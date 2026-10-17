#!/usr/bin/env python3
"""
Yugi SB Bot v2: a daily over/under sports betting board.

For every MLB, WNBA, NBA, NFL and NHL game on a given day it:
  1. finds the last 10 meetings between the two teams and takes the mean and
     median combined score (H2H Trends),
  2. pulls this season's scoring splits, defensive ranks, and the probable
     pitcher, goalie or quarterback, and builds a projected total (Matchup Edge),
  3. compares both to the sportsbook's over/under line,
  4. flags a Best Bet only when the H2H trend and the projection agree,
  5. tracks how the line moves between the morning and evening runs,
  6. grades every Best Bet the next day and keeps a running record in units.

All data comes from ESPN's public feed, updated daily. No logins or keys
needed. Runs on Python 3.9+ with the standard library only.

Usage:
  python yugi_sb_bot_v2.py                   today's board, opens in your browser
  python yugi_sb_bot_v2.py --date 2026-09-27 a specific day
  python yugi_sb_bot_v2.py --leagues NFL,NBA only some leagues
  python yugi_sb_bot_v2.py --demo            sample board with made-up numbers (no internet)
"""

import argparse
import base64
import csv
import datetime as dt
import hashlib
import html
import json
import random
import re
import statistics
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import math
import os
from pathlib import Path

# ---------------------------------------------------------------------------
# Settings you can change
# ---------------------------------------------------------------------------

APP_NAME = "Yugi SB Bot v2"
VERSION = "2.1"
TIMEZONE = "America/New_York"   # which calendar day counts as "today"
LAST_N = 10                     # how many past meetings to average
MIN_MEETINGS = 3                # fewer than this and no H2H averages are shown
BIG_GAP = 0.10                  # H2H "big gap": line 10%+ away from both averages
MIN_VENUE_GAMES = 3             # home/road splits need this many games, else season averages are used
RECENT_GAMES = 10               # "recent form" window
RECENT_WEIGHT = 0.30            # share of the projection that comes from recent form (0 turns it off)

# Bankroll and edge rules
UNIT_PCT = 0.025                # suggested stake per play as a share of your bankroll (2.5%)
MIN_EDGE = 0.04                 # model probability must beat the sportsbook's implied probability by this much
ODDS_FLOOR = None               # e.g. -300 to only allow prices that heavy. Standard totals are priced near -110,
                                # so this needs an odds feed with alternate lines; leave None with ESPN data.
# Typical game-to-game spread of a total, in points, used to turn a projection
# into a probability. These are estimates from past seasons; the Record tab
# shows whether they're too confident.
SIGMA = {"MLB": 3.9, "WNBA": 14.5, "NBA": 18.5, "NFL": 13.8, "NHL": 1.9,
         "NCAAF": 17.0, "NCAAB": 16.5, "NCAAW": 15.0}
# Leagues where the record has been weak: only Strong plays get through.
ONLY_STRONG = {"WNBA", "NHL", "NCAAF", "NCAAB", "NCAAW"}

# --- Odds providers (optional). Keys come from the environment, never this file. ---
# GitHub: Settings > Secrets and variables > Actions. Locally: set them in your shell.
ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "").strip()        # the-odds-api.com
SGO_API_KEY = os.environ.get("SGO_API_KEY", "").strip()          # sportsgameodds.com
DEFAULT_CREDIT_BUDGET = int(os.environ.get("ODDS_BUDGET", "40")) # credits one run may spend
PROP_GAMES_PER_LEAGUE = 6       # games per sport to pull props for (each costs credits)
PROP_MAX_ROWS = 40              # most prop plays to show
MIN_PROP_EDGE = 0.04            # a prop needs this much edge over the book's price
MIN_PROP_GAMES = 10             # fewest past games before a hit rate is trusted
PROP_CONF = 1.28                # how cautious a hit rate is: 1.28 = 90% confidence, 1.64 = 95%
MIN_ALT_EDGE = 0.04             # same edge test for alternate totals
ALT_MIN_PROB = 0.70             # alternate totals are the "high probability" play
ALT_MAX_LAY = -800              # never lay a price heavier than this
MIN_ARB_PROFIT = 0.005          # ignore arbs under 0.5%
# After the boards are priced, whatever is left is split between the two
# features so neither can starve the other. Change these to favour one.
ARB_SHARE = 0.5                 # share of the leftover budget for arbitrage
PROPS_SHARE = 0.5               # share of the leftover budget for player props
ARB_MARKETS = ["h2h", "spreads"]   # scanned for arbs on top of totals
TEAM_SHARE = 0.25               # share of the leftover budget for team totals
TEAM_TOTAL_GAMES_PER_LEAGUE = 4 # games per sport to price team totals for
TEAM_TOTAL_MAX_ROWS = 25
TEAM_TOTAL_MIN_PROB = 0.55      # a team total needs to be likelier than a coin flip

# UFC: fights the books expect to end early, between two finishers
UFC_ON = True
UFC_MAX_ROUND_LINE = 1.5        # the rounds total that signals an expected early finish
UFC_MIN_FINISH = 0.80           # both fighters must finish at least this often
UFC_MIN_FIGHTS = 6              # fewest recorded fights before a rate is trusted
UFC_PROB_CAP = 0.92             # never claim more certainty than this
UFC_MIN_PROB = 0.70             # below this the fight is not worth listing
UFC_ASSUMED_PRICE = "-600"      # the worst price the strategy stays profitable at
STEAM_POINTS = {"MLB": 1.0, "WNBA": 4.0, "NBA": 5.0, "NFL": 3.0, "NHL": 0.5,
                "NCAAF": 3.0, "NCAAB": 4.5, "NCAAW": 4.5}   # a move this big is a real signal

# on: include this league. seasons_back: how far to search for past meetings.
# season_ahead: ESPN labels NBA/NHL seasons by the year they end. halves: ESPN
# splits MLB schedules. min_games: games a team needs this season before it
# gets a projection. lean/strong: how far the projection must sit from the
# line, as a share of the line, for a Lean or Strong Best Bet.
LEAGUES = {
    "MLB":  {"on": True,  "sport": "baseball",   "league": "mlb",
              "toa": "baseball_mlb", "sgo": "MLB",
             "seasons_back": 4,
             "season_ahead": False, "halves": True,  "unit": "runs",
             "min_games": 10, "lean": 0.06, "strong": 0.10},
    "WNBA": {"on": True,  "sport": "basketball", "league": "wnba", "toa": "basketball_wnba", "sgo": "WNBA",
              "toa": "basketball_wnba", "sgo": "WNBA",
             "seasons_back": 5,
             "season_ahead": False, "halves": False, "unit": "points",
             "min_games": 5, "lean": 0.025, "strong": 0.05},
    "NBA":  {"on": True,  "sport": "basketball", "league": "nba", "toa": "basketball_nba", "sgo": "NBA",
              "toa": "basketball_nba", "sgo": "NBA",
             "seasons_back": 5,
             "season_ahead": True,  "halves": False, "unit": "points",
             "min_games": 5, "lean": 0.025, "strong": 0.05},
    "NFL":  {"on": True,  "sport": "football",   "league": "nfl", "toa": "americanfootball_nfl", "sgo": "NFL",
              "toa": "americanfootball_nfl", "sgo": "NFL",
             "seasons_back": 12,
             "season_ahead": False, "halves": False, "unit": "points",
             "min_games": 3, "lean": 0.04, "strong": 0.08},
    "NHL":  {"on": True,  "sport": "hockey",     "league": "nhl", "toa": "icehockey_nhl", "sgo": "NHL",
              "toa": "icehockey_nhl", "sgo": "NHL",
             "seasons_back": 5,
             "season_ahead": True,  "halves": False, "unit": "goals",
             "min_games": 8, "lean": 0.06, "strong": 0.10},
    # College: same metrics as the pros (NCAAF like NFL, NCAAB like NBA).
    # groups: which division ESPN returns (80 = FBS football, 50 = Division I
    # basketball). require_line: skip games no sportsbook has posted a total for,
    # which keeps the board and the run time manageable on busy college days.
    "NCAAF": {"on": True, "sport": "football",   "league": "college-football", "toa": "americanfootball_ncaaf", "sgo": "NCAAF",
             "seasons_back": 12,
              "season_ahead": False, "halves": False, "unit": "points",
              "min_games": 3, "lean": 0.04, "strong": 0.08,
              "groups": "80", "require_line": True},
    "NCAAB": {"on": True, "sport": "basketball", "league": "mens-college-basketball", "toa": "basketball_ncaab", "sgo": "NCAAB",
              "toa": "basketball_ncaab", "sgo": "NCAAB",
             "seasons_back": 6,
              "season_ahead": True,  "halves": False, "unit": "points",
              "min_games": 5, "lean": 0.025, "strong": 0.05,
              "groups": "50", "require_line": True},
    # UFC has no team scores, so it never appears on the totals board. It is
    # listed here only so the odds layer knows its provider keys.
    "UFC":  {"on": False, "sport": "mma", "league": "ufc",
             "toa": "mma_mixed_martial_arts", "sgo": "UFC", "seasons_back": 1,
             "season_ahead": False, "halves": False, "unit": "rounds",
             "min_games": 99, "lean": 0.05, "strong": 0.10},
    "NCAAW": {"on": True, "sport": "basketball", "league": "womens-college-basketball",
              "toa": "basketball_wncaab", "sgo": "NCAAW",
             "seasons_back": 6,
              "season_ahead": True,  "halves": False, "unit": "points",
              "min_games": 5, "lean": 0.025, "strong": 0.05,
              "groups": "50", "require_line": True},
}
FOOTBALL = ("nfl", "college-football")

ESPN = "https://site.api.espn.com/apis/site/v2/sports/{sport}/{league}"
ESPN_STANDINGS = "https://site.api.espn.com/apis/v2/sports/{sport}/{league}/standings"
# ESPN's network filters turn away requests that identify as a bot, so the
# bot introduces itself the way a regular Chrome browser would.
REQUEST_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"),
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip",
    "Referer": "https://www.espn.com/",
    "Origin": "https://www.espn.com",
}
# If ESPN's main address turns a request away, the same data is tried here.
ESPN_BACKUP_HOST = "site.web.api.espn.com"
HIST_FIELDS = ["date", "league", "event_id", "start_utc", "away", "home",
               "line", "over_price", "under_price", "book", "h2h_games",
               "mean", "median", "gap_mean", "gap_median", "proj", "first_line",
               "pick", "tier", "pick_price", "pick_line", "pick_time", "pick_prob",
               "pick_edge", "pick_result", "open_line", "alt_line", "alt_price", "alt_book",
               "final_total", "result"]

# App icons for the iPhone home screen (generated PNGs)
ICONS = {
    "apple-touch-icon.png": "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",
    "icon-192.png": "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",
    "icon-512.png": "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",
}


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

def utcnow():
    return dt.datetime.now(dt.timezone.utc)


_ZONE = None


def _zone():
    global _ZONE
    if _ZONE is None:
        try:
            from zoneinfo import ZoneInfo
            _ZONE = ZoneInfo(TIMEZONE)
        except Exception:          # Windows without the tzdata package
            _ZONE = False
    return _ZONE


def _us_eastern_offset(d):
    """Fallback when the time zone database is missing: US Eastern rules."""
    year = d.astimezone(dt.timezone.utc).year

    def nth_sunday(month, n):
        first = dt.date(year, month, 1)
        return first + dt.timedelta(days=(6 - first.weekday()) % 7 + 7 * (n - 1))

    start = dt.datetime.combine(nth_sunday(3, 2), dt.time(7), dt.timezone.utc)
    end = dt.datetime.combine(nth_sunday(11, 1), dt.time(6), dt.timezone.utc)
    return dt.timedelta(hours=-4 if start <= d < end else -5)


def to_local(d):
    zone = _zone()
    if zone:
        return d.astimezone(zone)
    return d.astimezone(dt.timezone(_us_eastern_offset(d)))


def parse_iso(value):
    if not value:
        return None
    text = str(value).strip().replace("Z", "+00:00")
    try:
        d = dt.datetime.fromisoformat(text)
    except ValueError:
        try:
            d = dt.datetime.strptime(text[:16], "%Y-%m-%dT%H:%M")
        except ValueError:
            return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=dt.timezone.utc)
    return d


def num(value):
    if value is None or value == "":
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def parse_score(value):
    if isinstance(value, dict):
        value = value.get("value", value.get("displayValue"))
    return num(value)


def fmt_num(x, places=1):
    if x is None:
        return ""
    if abs(x - round(x)) < 1e-9:
        return str(int(round(x)))
    return f"{x:.{places}f}"


def fmt_price(value):
    if value is None or value == "":
        return None
    n = num(value)
    if n is None:
        text = str(value).strip().upper()
        return "+100" if text in ("EVEN", "EV") else text
    n = int(round(n))
    return f"+{n}" if n > 0 else str(n)


def clock(d):
    return f"{d.hour % 12 or 12}:{d.minute:02d} {'AM' if d.hour < 12 else 'PM'}"


def lean(gap_mean, gap_median):
    """Which side the averages point to: line above both = under."""
    if gap_mean is None or gap_median is None:
        return None
    if gap_mean > 0 and gap_median > 0:
        return "under"
    if gap_mean < 0 and gap_median < 0:
        return "over"
    return None


def is_big_gap(line, gap_mean, gap_median):
    if not line or gap_mean is None or gap_median is None:
        return False
    return min(abs(gap_mean), abs(gap_median)) / abs(line) >= BIG_GAP


# ---------------------------------------------------------------------------
# Network
# ---------------------------------------------------------------------------

def _unzip(body):
    if body[:2] == b"\x1f\x8b":
        import gzip
        return gzip.decompress(body)
    return body


def http_get(url, timeout=25, retries=2):
    """Returns (status, headers, body). 4xx answers are returned, not raised."""
    last_error = None
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers=REQUEST_HEADERS)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.status, dict(resp.headers), _unzip(resp.read())
        except urllib.error.HTTPError as err:
            if 400 <= err.code < 500:
                try:
                    body = _unzip(err.read())
                except Exception:
                    body = b""
                return err.code, dict(err.headers or {}), body
            last_error = err
        except (urllib.error.URLError, TimeoutError, ConnectionError) as err:
            last_error = err
            if "CERTIFICATE_VERIFY_FAILED" in str(err):
                raise RuntimeError(
                    "Python can't verify web certificates. On a Mac, open "
                    "Applications > Python 3.x and double-click "
                    "'Install Certificates.command', then run again.") from err
        time.sleep(1.5 * (attempt + 1))
    raise RuntimeError(f"Couldn't reach {urllib.parse.urlparse(url).netloc}: {last_error}")


class Fetcher:
    """Fetches JSON, remembers it for this run, and keeps finished seasons on disk."""

    def __init__(self, cache_dir):
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self.memory = {}
        self.calls = 0
        self.last_status = None
        self.failures = 0

    def _get_json(self, url):
        status, _, body = http_get(url)
        self.calls += 1
        time.sleep(0.05)
        self.last_status = status
        if status == 200 and body:
            try:
                return json.loads(body)
            except ValueError:
                self.last_status = "unreadable reply"
        if self.failures < 3:       # show the first few problems in the run log
            self.failures += 1
            print(f"\n  ESPN answered {status} for {url}\n  {body[:160]!r}")
        return None

    def json(self, url):
        if url in self.memory:
            return self.memory[url]
        data = self._get_json(url)
        if data is None and "//site.api.espn.com/" in url:
            data = self._get_json(url.replace("//site.api.espn.com/", f"//{ESPN_BACKUP_HOST}/"))
        self.memory[url] = data
        return data

    def disk(self, key, build, keep):
        path = self.cache_dir / (hashlib.sha1(key.encode()).hexdigest() + ".json")
        if path.exists():
            try:
                return json.loads(path.read_text(encoding="utf-8"))
            except ValueError:
                pass
        value = build()
        if keep(value):
            path.write_text(json.dumps(value), encoding="utf-8")
        return value


# ---------------------------------------------------------------------------
# ESPN: schedules, scores and ESPN's own odds
# ---------------------------------------------------------------------------

def base_url(lg):
    return ESPN.format(sport=lg["sport"], league=lg["league"])


def compact_events(data):
    """Boils an ESPN schedule down to the few fields we need."""
    out = []
    for ev in (data or {}).get("events") or []:
        comps = ev.get("competitions") or []
        if not comps:
            continue
        comp = comps[0]
        state = ((comp.get("status") or ev.get("status") or {}).get("type") or {})
        teams = []
        for t in comp.get("competitors") or []:
            team = t.get("team") or {}
            teams.append({
                "id": str(team.get("id") or t.get("id") or ""),
                "ha": t.get("homeAway") or "",
                "name": team.get("displayName") or team.get("shortDisplayName")
                        or team.get("name") or "",
                "score": parse_score(t.get("score")),
            })
        out.append({
            "id": str(ev.get("id") or comp.get("id") or ""),
            "date": ev.get("date") or comp.get("date"),
            "completed": bool(state.get("completed")) or state.get("state") == "post",
            "detail": state.get("shortDetail") or state.get("detail") or "",
            "teams": teams,
        })
    return out


def team_schedule(fetch, lg, team_id, season, season_type):
    urls = [f"{base_url(lg)}/teams/{team_id}/schedule?season={season}&seasontype={season_type}"]
    if lg.get("halves"):
        urls = [urls[0] + "&half=1", urls[0] + "&half=2"]

    def build():
        merged = {}
        for url in urls:
            for ev in compact_events(fetch.json(url)):
                merged[ev["id"]] = ev
        return list(merged.values())

    def keep(events):   # only cache seasons that are over
        dates = [parse_iso(e["date"]) for e in events if e.get("date")]
        dates = [d for d in dates if d]
        return bool(dates) and max(dates) < utcnow() - dt.timedelta(days=21)

    return fetch.disk("|".join(urls), build, keep)


def parse_espn_odds(odds):
    if not odds:
        return None
    o = next((x for x in odds if x.get("overUnder") is not None or x.get("total")), odds[0])
    line = num(o.get("overUnder"))
    over, under = o.get("overOdds"), o.get("underOdds")
    total = o.get("total") or {}
    for side in ("over", "under"):
        block = total.get(side) or {}
        for when in ("close", "current", "open"):
            b = block.get(when)
            if not isinstance(b, dict) or not (b.get("odds") or b.get("line")):
                continue
            if side == "over" and over is None:
                over = b.get("odds")
            if side == "under" and under is None:
                under = b.get("odds")
            if line is None:
                line = num(str(b.get("line") or "").lstrip("ouOU "))
            break
    if line is None:
        return None
    book = (o.get("provider") or {}).get("name") or "ESPN feed"
    return {"line": line, "over": fmt_price(over), "under": fmt_price(under),
            "book": book}


def scoreboard(fetch, lg, day):
    plain = f"{base_url(lg)}/scoreboard?dates={day:%Y%m%d}"
    extra = "&limit=400" + (f"&groups={lg['groups']}" if lg.get("groups") else "")
    data = fetch.json(plain + extra)
    if data is None:
        data = fetch.json(plain + (f"&groups={lg['groups']}" if lg.get("groups") else ""))
    if data is None:
        raise RuntimeError(f"ESPN answered {fetch.last_status}")
    games = []
    for ev in data.get("events") or []:
        comps = ev.get("competitions") or []
        if not comps:
            continue
        comp = comps[0]
        start = parse_iso(ev.get("date") or comp.get("date"))
        if start is None or to_local(start).date() != day:
            continue
        state = ((comp.get("status") or ev.get("status") or {}).get("type") or {})
        sides = {}
        for t in comp.get("competitors") or []:
            team = t.get("team") or {}
            sides[t.get("homeAway")] = {
                "id": str(team.get("id") or t.get("id") or ""),
                "name": team.get("displayName") or team.get("name") or "",
                "nickname": team.get("name") or team.get("shortDisplayName") or "",
                "score": parse_score(t.get("score")),
                "starter": parse_starter(t) if lg["league"] in ("mlb", "nhl") else None,
                "passer": parse_passer(t) if lg["league"] in FOOTBALL else None,
                "location": team.get("location") or "",
            }
        if "home" not in sides or "away" not in sides:
            continue
        final_total = None
        if state.get("completed") and None not in (sides["home"]["score"], sides["away"]["score"]):
            final_total = sides["home"]["score"] + sides["away"]["score"]
        games.append({
            "id": str(ev.get("id")),
            "start": start,
            "home": sides["home"],
            "away": sides["away"],
            "state": state.get("state") or "pre",
            "status": state.get("shortDetail") or state.get("description") or "",
            "final_total": final_total,
            "espn_odds": parse_espn_odds(comp.get("odds")),
            "env": parse_env(ev, comp) if lg["league"] in ("mlb",) + FOOTBALL else None,
        })
    games.sort(key=lambda g: g["start"])
    return games


def last_meetings(fetch, lg, team_id, opp_id, before, today):
    first = today.year + (1 if lg["season_ahead"] else 0)
    found = {}
    for season in range(first, first - lg["seasons_back"] - 1, -1):
        for season_type in (2, 3):          # regular season, playoffs
            for ev in team_schedule(fetch, lg, team_id, season, season_type):
                ids = {t["id"] for t in ev["teams"]}
                if not ev["completed"] or opp_id not in ids or team_id not in ids:
                    continue
                if any(t["score"] is None for t in ev["teams"]):
                    continue
                if any(w in ev["detail"].lower() for w in ("postponed", "canceled", "cancelled")):
                    continue
                when = parse_iso(ev["date"])
                if when is None or when >= before:
                    continue
                found[ev["id"]] = ev
        if len(found) >= LAST_N:
            break
    games = sorted(found.values(), key=lambda e: e["date"], reverse=True)[:LAST_N]
    rows = []
    for ev in games:
        home = next((t for t in ev["teams"] if t["ha"] == "home"), ev["teams"][0])
        away = next((t for t in ev["teams"] if t is not home), ev["teams"][-1])
        rows.append({
            "date": to_local(parse_iso(ev["date"])).strftime("%b %d, %Y").replace(" 0", " "),
            "away": away["name"], "away_score": away["score"],
            "home": home["name"], "home_score": home["score"],
            "total": away["score"] + home["score"],
        })
    return rows


# ---------------------------------------------------------------------------
# Matchup factors: probable starters, quarterbacks, splits, defensive ranks
# ---------------------------------------------------------------------------

def _flatten_stats(node, out=None):
    """Collects {abbreviation or name: value} from any nested ESPN stat blocks."""
    out = {} if out is None else out
    if isinstance(node, dict):
        key = node.get("abbreviation") or node.get("name")
        value = node.get("displayValue", node.get("value"))
        if isinstance(key, str) and value is not None and not isinstance(value, (dict, list)):
            out.setdefault(key.lower(), value)
        for v in node.values():
            if isinstance(v, (dict, list)):
                _flatten_stats(v, out)
    elif isinstance(node, list):
        for v in node:
            _flatten_stats(v, out)
    return out


def parse_starter(competitor):
    """Probable starting pitcher (MLB) or goalie (NHL), when ESPN lists one."""
    for p in competitor.get("probables") or []:
        athlete = p.get("athlete") or {}
        name = athlete.get("shortName") or athlete.get("displayName") or p.get("displayName")
        if not name:
            continue
        stats = _flatten_stats(p.get("statistics") or [])
        stats.update({k: v for k, v in _flatten_stats(athlete.get("statistics") or []).items()
                      if k not in stats})
        record = str(p.get("record") or p.get("summary") or "")
        era = num(stats.get("era"))
        if era is None:
            m = re.search(r"(\d+\.\d+)\s*ERA", record, re.I)
            era = float(m.group(1)) if m else None
        gaa = num(stats.get("gaa") or stats.get("goalsagainstaverage"))
        svpct = num(stats.get("sv%") or stats.get("savepct") or stats.get("svpct")
                    or stats.get("savepercentage"))
        if svpct is not None and svpct > 1:
            svpct /= 100
        saves = num(stats.get("sv") or stats.get("saves"))
        games = num(stats.get("gp") or stats.get("gamesplayed") or stats.get("gs"))
        return {"name": name, "era": era, "gaa": gaa, "svpct": svpct, "whip": num(stats.get("whip")),
                "saves_pg": saves / games if saves is not None and games else None}
    return None


def games_played(competitor):
    for rec in competitor.get("records") or []:
        parts = [int(x) for x in re.findall(r"\d+", str(rec.get("summary") or ""))]
        if parts:
            return sum(parts)
    return None


def parse_passer(competitor):
    """Season passing leader (normally the starting QB) from ESPN's pregame leaders."""
    for cat in competitor.get("leaders") or []:
        if "passing" not in str(cat.get("name") or cat.get("displayName") or "").lower():
            continue
        for leader in cat.get("leaders") or []:
            athlete = leader.get("athlete") or {}
            yards = num(leader.get("value"))
            if yards is None:
                m = re.match(r"\s*([\d,]+)", str(leader.get("displayValue") or ""))
                yards = float(m.group(1).replace(",", "")) if m else None
            name = athlete.get("shortName") or athlete.get("displayName")
            if name:
                gp = games_played(competitor)
                return {"name": name, "ypg": yards / gp if yards is not None and gp else None}
    return None


def defense_ranks(fetch, lg):
    """Ranks every team by points (runs, goals) allowed per game, 1 = stingiest."""
    data = fetch.json(ESPN_STANDINGS.format(sport=lg["sport"], league=lg["league"]))
    entries = []

    def walk(node):
        if isinstance(node, dict):
            if isinstance(node.get("entries"), list):
                entries.extend(node["entries"])
            for v in node.values():
                if isinstance(v, (dict, list)):
                    walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(data or {})
    allowed = {}
    for e in entries:
        tid = str((e.get("team") or {}).get("id") or "")
        stats = {str(s.get("name") or s.get("type") or "").lower(): num(s.get("value"))
                 for s in e.get("stats") or []}
        per = stats.get("avgpointsagainst") or stats.get("avggoalsagainst")
        if per is None:
            total = next((stats[k] for k in ("goalsagainst", "pointsagainst", "runsallowed", "runsagainst")
                          if stats.get(k) is not None), None)
            gp = stats.get("gamesplayed") or sum(stats.get(k) or 0 for k in
                                                 ("wins", "losses", "ties", "otlosses", "overtimelosses"))
            per = total / gp if total is not None and gp else None
        if tid and per:
            allowed[tid] = per
    if len(allowed) < 5:
        return {}
    ranked = sorted(allowed.items(), key=lambda kv: kv[1])
    return {tid: {"rank": i + 1, "of": len(ranked)} for i, (tid, _) in enumerate(ranked)}


def current_season(fetch, lg, team_id, before, today):
    """Finds the newest season with games already played. Returns (label, events, is_prior)."""
    for season in (today.year + 1, today.year, today.year - 1):
        events = team_schedule(fetch, lg, team_id, season, 2)
        dates = [d for d in (parse_iso(e["date"]) for e in events) if d]
        if any(d < before for d in dates):
            prior = max(dates) < before - dt.timedelta(days=30)
            return season, prior
    return None, False


def team_splits(fetch, lg, team_id, season, before):
    if season is None:
        return None
    rows = {"home": ([], []), "away": ([], [])}
    played = []
    for ev in team_schedule(fetch, lg, team_id, season, 2):
        when = parse_iso(ev["date"])
        if not ev["completed"] or when is None or when >= before:
            continue
        if any(w in ev["detail"].lower() for w in ("postponed", "canceled", "cancelled")):
            continue
        me = next((t for t in ev["teams"] if t["id"] == team_id), None)
        opp = next((t for t in ev["teams"] if t["id"] != team_id), None)
        if not me or not opp or me["score"] is None or opp["score"] is None:
            continue
        where = "home" if me["ha"] == "home" else "away"
        rows[where][0].append(me["score"])
        rows[where][1].append(opp["score"])
        played.append((when, me["score"], opp["score"]))
    scored = rows["home"][0] + rows["away"][0]
    allowed = rows["home"][1] + rows["away"][1]
    if not scored:
        return None
    out = {"n": len(scored), "ppg": statistics.mean(scored), "papg": statistics.mean(allowed)}
    for where in ("home", "away"):
        s, a = rows[where]
        out[f"{where}_n"] = len(s)
        out[f"{where}_ppg"] = statistics.mean(s) if s else None
        out[f"{where}_papg"] = statistics.mean(a) if a else None
    played.sort(key=lambda r: r[0])
    recent = played[-RECENT_GAMES:]
    out["recent_n"] = len(recent)
    out["recent_ppg"] = statistics.mean(r[1] for r in recent)
    out["recent_papg"] = statistics.mean(r[2] for r in recent)
    out["last_game"] = played[-1][0].isoformat()
    return out


def venue_rate(split, where, key):
    """Home or road rate when there's enough sample, otherwise the season rate."""
    if split.get(f"{where}_n", 0) >= MIN_VENUE_GAMES and split.get(f"{where}_{key}") is not None:
        return split[f"{where}_{key}"], where
    return split[key], "season"


def with_form(split, rate, key):
    """Leans part of a season rate toward the team's last few games."""
    if RECENT_WEIGHT <= 0 or split.get("recent_n", 0) < RECENT_GAMES // 2:
        return rate
    return (1 - RECENT_WEIGHT) * rate + RECENT_WEIGHT * split[key]


def rest_days(split, start):
    """Days between a team's last game and this one (1 = back-to-back)."""
    last = parse_iso((split or {}).get("last_game"))
    if not last:
        return None
    return (to_local(start).date() - to_local(last).date()).days


def parse_env(event, comp):
    """Roof or weather at the venue, when ESPN lists it."""
    venue = comp.get("venue") or {}
    if venue.get("indoor") is True:
        return "Indoors (roof or dome)"
    w = event.get("weather") or comp.get("weather") or {}
    temp = num(w.get("temperature"))
    bits = []
    if temp is not None:
        bits.append(f"{temp:.0f}\u00b0F")
    if w.get("displayValue"):
        bits.append(str(w["displayValue"]))
    wind = w.get("windSpeed") or w.get("wind")
    if isinstance(wind, (int, float, str)) and str(wind).strip():
        bits.append(f"wind {wind}" + ("" if "mph" in str(wind).lower() else " mph"))
    return ", ".join(bits) or None


def _blend_pitcher(starter, team_allowed):
    # Starters cover roughly 55% of innings. ERA counts earned runs only, so it's
    # scaled up ~8% to runs of any kind. Extreme small-sample ERAs are capped.
    if not starter or starter.get("era") is None:
        return team_allowed
    era = min(max(starter["era"], 1.5), 8.0)
    return 0.55 * era * 1.08 + 0.45 * team_allowed


def _blend_goalie(starter, team_allowed):
    if not starter or starter.get("gaa") is None:
        return team_allowed
    gaa = min(max(starter["gaa"], 1.5), 4.5)
    return 0.5 * gaa + 0.5 * team_allowed


def project_total(league, lg, home, away):
    """Each side's expected score = average of its offense and the other side's defense."""
    hs, as_ = home.get("split"), away.get("split")
    if not hs or not as_ or hs["n"] < lg["min_games"] or as_["n"] < lg["min_games"]:
        return None
    home_off = with_form(hs, venue_rate(hs, "home", "ppg")[0], "recent_ppg")
    home_def = with_form(hs, venue_rate(hs, "home", "papg")[0], "recent_papg")
    away_off = with_form(as_, venue_rate(as_, "away", "ppg")[0], "recent_ppg")
    away_def = with_form(as_, venue_rate(as_, "away", "papg")[0], "recent_papg")
    if league == "MLB":
        home_def = _blend_pitcher(home.get("starter"), home_def)
        away_def = _blend_pitcher(away.get("starter"), away_def)
    elif league == "NHL":
        home_def = _blend_goalie(home.get("starter"), home_def)
        away_def = _blend_goalie(away.get("starter"), away_def)
    home_pts = (home_off + away_def) / 2
    away_pts = (away_off + home_def) / 2
    return {"total": home_pts + away_pts, "home": home_pts, "away": away_pts}


def price_for_prob(p):
    """The American price whose implied chance equals p: the break-even number."""
    p = min(max(p, 0.001), 0.999)
    return int(round(-100 * p / (1 - p))) if p > 0.5 else int(round(100 * (1 - p) / p))


def implied_prob(price):
    """What the sportsbook's price says the chance is (vig included)."""
    p = num(price)
    if p is None:
        p = -110
    return abs(p) / (abs(p) + 100) if p < 0 else 100 / (p + 100)


def norm_cdf(z):
    return 0.5 * (1 + math.erf(z / math.sqrt(2)))


def side_probs(league, proj_total, line):
    """Model chance of over and under, treating the total as a bell curve around the projection."""
    sigma = SIGMA.get(league, 15.0)
    p_over = 1 - norm_cdf((line - proj_total) / sigma)
    return {"over": p_over, "under": 1 - p_over}


def recommend(league, lg, line, h2h, proj, odds):
    """A Best Bet needs: projection off the line, the H2H trend pointing the same way,
    a model probability that beats the implied probability by MIN_EDGE, and (if set)
    a price at least as heavy as ODDS_FLOOR. Weak leagues need a Strong grade."""
    if line is None or not proj or not h2h:
        return None
    gap = line - proj["total"]
    size = abs(gap) / abs(line)
    if size < lg["lean"]:
        return None
    side = "under" if gap > 0 else "over"
    if lean(h2h["gap_mean"], h2h["gap_median"]) != side:
        return None
    strong = size >= lg["strong"] and is_big_gap(line, h2h["gap_mean"], h2h["gap_median"])
    if league in ONLY_STRONG and not strong:
        return None
    price = (odds or {}).get(side) or "-110"
    prob = side_probs(league, proj["total"], line)[side]
    implied = implied_prob(price)
    if prob - implied < MIN_EDGE:
        return None
    if ODDS_FLOOR is not None and (num(price) or -110) > ODDS_FLOOR:
        return None
    return {"side": side, "tier": "Strong" if strong else "Lean", "edge": size,
            "prob": prob, "implied": implied, "edge_prob": prob - implied, "price": price}


def payout(price):
    """Profit per 1 unit risked at American odds."""
    p = num(price)
    if p is None:
        p = -110
    return p / 100 if p > 0 else 100 / abs(p)


# ---------------------------------------------------------------------------
# Odds providers: multi-book prices, alternate lines, player props
#
# Keys come from the environment only, never from this file, so the code can
# live in a public repository safely:
#     ODDS_API_KEY   from the-odds-api.com
#     SGO_API_KEY    from sportsgameodds.com
# ---------------------------------------------------------------------------

TOA_BASE = "https://api.the-odds-api.com/v4"
SGO_BASE = "https://api.sportsgameodds.com/v2"

# Prop markets to ask for, by sport. The Odds API market keys.
PROP_MARKETS = {
    "MLB": ["pitcher_strikeouts", "batter_hits", "batter_total_bases", "batter_home_runs",
            "batter_rbis", "pitcher_outs"],
    "NBA": ["player_points", "player_rebounds", "player_assists", "player_threes",
            "player_points_rebounds_assists"],
    "WNBA": ["player_points", "player_rebounds", "player_assists"],
    "NFL": ["player_pass_yds", "player_rush_yds", "player_reception_yds", "player_receptions",
            "player_kicking_points", "player_anytime_td"],
    "NCAAF": ["player_pass_yds", "player_rush_yds", "player_reception_yds"],
    "NHL": ["player_points", "player_shots_on_goal", "player_assists"],
    "NCAAB": [],
    "NCAAW": [],
}
# How a prop market maps to a box-score stat the hit-rate engine can count.
PROP_STATS = {
    "pitcher_strikeouts": ("mlb_pitching", "strikeOuts", "strikeouts"),
    "pitcher_outs": ("mlb_pitching", "outs", "outs recorded"),
    "batter_hits": ("mlb_hitting", "hits", "hits"),
    "batter_total_bases": ("mlb_hitting", "totalBases", "total bases"),
    "batter_home_runs": ("mlb_hitting", "homeRuns", "home runs"),
    "batter_rbis": ("mlb_hitting", "rbi", "RBIs"),
    "player_points": ("espn", "points", "points"),
    "player_rebounds": ("espn", "rebounds", "rebounds"),
    "player_assists": ("espn", "assists", "assists"),
    "player_threes": ("espn", "threePointFieldGoalsMade", "threes"),
    "player_pass_yds": ("espn", "passingYards", "pass yards"),
    "player_rush_yds": ("espn", "rushingYards", "rush yards"),
    "player_reception_yds": ("espn", "receivingYards", "receiving yards"),
    "player_receptions": ("espn", "receptions", "receptions"),
    "player_shots_on_goal": ("espn", "shotsTotal", "shots on goal"),
}


def american(dec):
    """Decimal price to American."""
    if dec is None or dec <= 1:
        return None
    return round((dec - 1) * 100) if dec >= 2 else round(-100 / (dec - 1))


class OddsClient:
    """Talks to whichever odds provider has a key. Spends a daily credit budget
    in priority order and stops cleanly when it runs out."""

    def __init__(self, toa_key=None, sgo_key=None, budget=DEFAULT_CREDIT_BUDGET, log=print):
        self.toa, self.sgo = toa_key, sgo_key
        self.budget, self.spent, self.log = budget, 0, log
        self.remaining = None          # what the provider says is left this month
        self.errors = []
        self.calls = 0
        self.seen = {}                 # same request twice in a run costs one credit, not two
        self.skipped = []              # leagues we deliberately didn't price
        self.pools = {}                # name -> credits set aside for that feature
        self.used = {}                 # name -> credits actually spent on it
        self.pool = None               # which pool the current request draws from

    @property
    def on(self):
        return bool(self.toa or self.sgo)

    @property
    def left(self):
        return max(0, self.budget - self.spent)

    def split_rest(self, shares):
        """Divides whatever budget is left between the named features, so a long
        prop run can't eat the arbitrage allowance or the other way round."""
        rest = self.left
        total = sum(shares.values()) or 1
        self.pools = {k: int(rest * v / total) for k, v in shares.items()}
        return dict(self.pools)

    def room(self, pool):
        if pool not in self.pools:
            return self.left
        return max(0, min(self.pools[pool] - self.used.get(pool, 0), self.left))

    def using(self, pool):
        """Spend the next requests from this feature's share."""
        self.pool = pool
        return self

    def _get(self, url, cost=1):
        if url in self.seen:
            return self.seen[url]
        pool = self.pool
        if pool and self.room(pool) < cost:
            return None
        if self.left < cost:
            if "budget" not in " ".join(self.errors):
                self.note(f"stopped at the {self.budget}-credit budget for this run")
            return None
        status, headers, body = http_get(url, timeout=30, retries=1)
        self.calls += 1
        self.spent += cost
        if pool:
            self.used[pool] = self.used.get(pool, 0) + cost
        time.sleep(0.08)
        rem = None
        for k, v in (headers or {}).items():
            if k.lower() in ("x-requests-remaining", "x-ratelimit-remaining"):
                rem = num(v)
        if rem is not None:
            self.remaining = rem
        if status == 200 and body:
            try:
                data = json.loads(body)
                self.seen[url] = data
                return data
            except ValueError:
                pass
        if status in (401, 403):
            self.note(f"the odds key was rejected (status {status})")
        elif status == 429:
            self.note("the odds plan is out of requests for now")
        elif status != 200:
            self.note(f"odds provider answered {status}")
        return None

    def note(self, msg):
        if msg not in self.errors:
            self.errors.append(msg)
            self.log(f"  odds: {msg}")

    # -- The Odds API ------------------------------------------------------
    def _toa(self, path, params, cost):
        q = urllib.parse.urlencode(dict(params, apiKey=self.toa))
        return self._get(f"{TOA_BASE}{path}?{q}", cost=cost)

    def _toa_books(self, event):
        """Flattens one Odds API event into {market: [rows]}."""
        out = {}
        for b in event.get("bookmakers") or []:
            for m in b.get("markets") or []:
                key = m.get("key")
                for o in m.get("outcomes") or []:
                    out.setdefault(key, []).append({
                        "book": b.get("title") or b.get("key"), "book_key": b.get("key"),
                        "link": o.get("link") or m.get("link") or b.get("link"),
                        "name": o.get("name"), "player": o.get("description"),
                        "point": num(o.get("point")), "price": fmt_price(o.get("price")),
                    })
        return out

    # -- SportsGameOdds ----------------------------------------------------
    def _sgo(self, path, params):
        q = urllib.parse.urlencode(dict(params, apiKey=self.sgo))
        return self._get(f"{SGO_BASE}{path}?{q}", cost=1)

    @staticmethod
    def _sgo_rows(event):
        """SportsGameOdds keys each market as statID-playerID-periodID-betTypeID-sideID."""
        out = {}
        for odd_id, odd in (event.get("odds") or {}).items():
            parts = str(odd_id).split("-")
            if len(parts) < 5:
                continue
            stat_id, player_id, period, bet_type, side = parts[0], parts[1], parts[2], parts[3], parts[4]
            line = num(odd.get("bookOverUnder") or odd.get("fairOverUnder") or odd.get("overUnder"))
            books = odd.get("byBookmaker") or {}
            rows = []
            for bk, bo in books.items():
                if not isinstance(bo, dict) or bo.get("available") is False:
                    continue
                rows.append({"book": bk.replace("_", " ").title(), "book_key": bk,
                             "link": bo.get("deeplink") or bo.get("link"),
                             "point": num(bo.get("overUnder")) if num(bo.get("overUnder")) is not None else line,
                             "price": fmt_price(bo.get("odds")), "name": side.title(),
                             "player": None if player_id in ("all", "home", "away") else player_id})
            if not rows and odd.get("bookOdds"):
                rows.append({"book": "Consensus", "book_key": "consensus", "link": None,
                             "point": line, "price": fmt_price(odd.get("bookOdds")),
                             "name": side.title(),
                             "player": None if player_id in ("all", "home", "away") else player_id})
            if rows:
                out.setdefault((stat_id, period, bet_type), []).extend(rows)
        return out

    # -- public ------------------------------------------------------------
    def game_totals(self, league):
        """Multi-book game totals for a league, as a list of events we can match to ESPN."""
        lg = LEAGUES[league]
        if self.toa and lg.get("toa"):
            data = self._toa(f"/sports/{lg['toa']}/odds",
                             {"regions": "us", "markets": "totals", "oddsFormat": "american"}, cost=1)
            events = []
            for ev in data or []:
                rows = self._toa_books(ev).get("totals") or []
                if rows:
                    events.append({"id": ev.get("id"), "home": ev.get("home_team", ""),
                                   "away": ev.get("away_team", ""),
                                   "start": parse_iso(ev.get("commence_time")), "rows": rows})
            return events
        if self.sgo and lg.get("sgo"):
            data = self._sgo("/events", {"leagueID": lg["sgo"], "oddsAvailable": "true", "limit": 100})
            events = []
            for ev in (data or {}).get("data") or []:
                teams = ev.get("teams") or {}
                rows = self._sgo_rows(ev).get(("points", "game", "ou")) or []
                if rows:
                    events.append({"id": ev.get("eventID"),
                                   "home": ((teams.get("home") or {}).get("names") or {}).get("long", ""),
                                   "away": ((teams.get("away") or {}).get("names") or {}).get("long", ""),
                                   "start": parse_iso((ev.get("status") or {}).get("startsAt")), "rows": rows})
            return events
        return []

    def game_markets(self, league, markets):
        """Moneyline and spread prices for a whole league in one request."""
        lg = LEAGUES[league]
        if not (self.toa and lg.get("toa")) or not markets:
            return []
        data = self._toa(f"/sports/{lg['toa']}/odds",
                         {"regions": "us", "markets": ",".join(markets), "oddsFormat": "american"},
                         cost=len(markets))
        events = []
        for ev in data or []:
            books = self._toa_books(ev)
            rows = {m: books.get(m) or [] for m in markets if books.get(m)}
            if rows:
                events.append({"id": ev.get("id"), "home": ev.get("home_team", ""),
                               "away": ev.get("away_team", ""),
                               "start": parse_iso(ev.get("commence_time")), "markets": rows})
        return events

    def team_totals(self, league, event_id):
        """Each side's own total for one game."""
        lg = LEAGUES[league]
        if not (self.toa and lg.get("toa")) or not event_id:
            return []
        data = self._toa(f"/sports/{lg['toa']}/events/{event_id}/odds",
                         {"regions": "us", "markets": "team_totals", "oddsFormat": "american"}, cost=1)
        rows = self._toa_books(data or {}).get("team_totals") or []
        for r in rows:
            r["team"] = r.get("player") or r.get("team")
        return rows

    def alt_totals(self, league, event_id):
        """Every alternate total posted for one game."""
        lg = LEAGUES[league]
        if self.toa and lg.get("toa") and event_id:
            data = self._toa(f"/sports/{lg['toa']}/events/{event_id}/odds",
                             {"regions": "us", "markets": "alternate_totals", "oddsFormat": "american"}, cost=1)
            return self._toa_books(data or {}).get("alternate_totals") or []
        return []

    def props(self, league, event_id):
        """Player props for one game, one row per player/side/book."""
        lg = LEAGUES[league]
        markets = PROP_MARKETS.get(league) or []
        if not markets or not event_id:
            return []
        if self.toa and lg.get("toa"):
            data = self._toa(f"/sports/{lg['toa']}/events/{event_id}/odds",
                             {"regions": "us", "markets": ",".join(markets), "oddsFormat": "american"},
                             cost=len(markets))
            out = []
            for market, rows in self._toa_books(data or {}).items():
                for r in rows:
                    if r.get("player"):
                        out.append(dict(r, market=market))
            return out
        return []


# ---------------------------------------------------------------------------
# Matching a provider's game to an ESPN game, and shopping the best price
# ---------------------------------------------------------------------------

def _plain(text):
    return " ".join("".join(ch for ch in (text or "").lower()
                            if ch.isalnum() or ch == " ").split())


def _same_team(side, name):
    """The provider's team name against ESPN's. College shares nicknames, so the
    school has to match too when ESPN gives one."""
    n = _plain(name)
    if not n:
        return False
    if n == _plain(side["name"]):
        return True
    nick = _plain(side.get("nickname"))
    if not nick or not (n == nick or n.endswith(" " + nick)):
        return False
    place = _plain(side.get("location"))
    return not place or place in n or n == nick


def match_book_event(game, events):
    hits = [e for e in events if _same_team(game["home"], e["home"]) and _same_team(game["away"], e["away"])]
    if not hits:
        return None
    def gap(e):
        return abs((e["start"] - game["start"]).total_seconds()) if e.get("start") else 0
    best = min(hits, key=gap)
    return best if gap(best) <= 18 * 3600 else None


def best_book_total(rows):
    """The most common line across books, with the best price on each side of it."""
    lines = {}
    for r in rows:
        if r["point"] is None or not r["price"] or (r["name"] or "").lower() not in ("over", "under"):
            continue
        lines.setdefault(r["point"], []).append(r)
    if not lines:
        return None
    main = max(lines, key=lambda k: len({r["book_key"] for r in lines[k]}))
    overs = [r for r in lines[main] if r["name"].lower() == "over"]
    unders = [r for r in lines[main] if r["name"].lower() == "under"]
    if not overs or not unders:
        return None
    books = len({r["book_key"] for r in lines[main]})
    every = sorted(lines)
    return {"line": main, "over": max(overs, key=lambda r: payout(r["price"])),
            "under": max(unders, key=lambda r: payout(r["price"])),
            "books": books, "low": every[0], "high": every[-1],
            "consensus_book": f"{books} book{'s' if books != 1 else ''}"}


# ---------------------------------------------------------------------------
# Hit rates: how often a player has actually cleared a number
# ---------------------------------------------------------------------------

MLB_STATS = "https://statsapi.mlb.com/api/v1"


def _norm_name(name):
    text = "".join(ch for ch in (name or "").lower() if ch.isalpha() or ch in " .-")
    return " ".join(text.replace(".", " ").split())


def _last_name(name):
    parts = _norm_name(name).split()
    return parts[-1] if parts else ""


def mlb_player_id(fetch, name, season):
    """Finds an MLB player id by name from the free MLB Stats API."""
    key = f"mlb-roster-{season}"

    def build():
        data = fetch.json(f"{MLB_STATS}/sports/1/players?season={season}")
        return {_norm_name(p.get("fullName")): p.get("id") for p in (data or {}).get("people") or []}

    table = fetch.disk(key, build, lambda v: bool(v))
    if not table:
        return None
    want = _norm_name(name)
    if want in table:
        return table[want]
    # "E. Rodriguez" style: match on last name plus first initial
    parts = want.split()
    if len(parts) >= 2:
        initial, last = parts[0][0], parts[-1]
        hits = [v for k, v in table.items()
                if k.split()[-1] == last and k.split()[0].startswith(initial)]
        if len(hits) == 1:
            return hits[0]
    return None


def mlb_game_log(fetch, player_id, group, season):
    """Per-game numbers for one player this season."""
    data = fetch.json(f"{MLB_STATS}/people/{player_id}/stats"
                      f"?stats=gameLog&group={group}&season={season}&gameType=R")
    out = []
    for block in (data or {}).get("stats") or []:
        for split in block.get("splits") or []:
            stat, date = split.get("stat") or {}, split.get("date")
            if stat:
                out.append({"date": date, "home": (split.get("isHome") is True), "stat": stat})
    out.sort(key=lambda r: r["date"] or "")
    return out


def espn_athlete_ids(fetch, lg, team_id):
    """Name to ESPN athlete id for one team's roster."""
    data = fetch.json(f"{base_url(lg)}/teams/{team_id}/roster")
    out = {}

    def walk(node):
        if isinstance(node, dict):
            if node.get("id") and (node.get("fullName") or node.get("displayName")):
                out[_norm_name(node.get("fullName") or node.get("displayName"))] = str(node["id"])
            for v in node.values():
                if isinstance(v, (dict, list)):
                    walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(data or {})
    return out


def espn_game_log(fetch, lg, athlete_id):
    """Per-game stat lines for one athlete, as a list of {stat name: value}."""
    url = (f"https://site.web.api.espn.com/apis/common/v3/sports/{lg['sport']}/{lg['league']}"
           f"/athletes/{athlete_id}/gamelog")
    data = fetch.json(url)
    if not data:
        return []
    names = data.get("names") or data.get("labels") or []
    if not names:
        for cat in data.get("categories") or []:
            if cat.get("names"):
                names = cat["names"]
                break
    names = [str(n) for n in names]
    rows = []
    events = data.get("events") or {}
    items = events.values() if isinstance(events, dict) else events
    for ev in items:
        stats = ev.get("stats")
        if not isinstance(stats, list) or not names:
            continue
        row = {}
        for i, label in enumerate(names):
            if i < len(stats):
                v = num(str(stats[i]).split("-")[0])
                if v is not None:
                    row[label.lower()] = v
        if row:
            rows.append({"date": ev.get("gameDate") or ev.get("id"), "stat": row})
    rows.sort(key=lambda r: str(r["date"]))
    return rows


def _espn_value(stat_row, key):
    """ESPN labels vary by sport, so match a few spellings."""
    aliases = {
        "points": ["pts", "points"], "rebounds": ["reb", "rebounds", "totalrebounds"],
        "assists": ["ast", "assists"], "threePointFieldGoalsMade": ["3pm", "threepointfieldgoalsmade"],
        "passingYards": ["yds", "passingyards", "passyds"],
        "rushingYards": ["rushingyards", "rushyds"],
        "receivingYards": ["receivingyards", "recyds"],
        "receptions": ["rec", "receptions"], "shotsTotal": ["sog", "s", "shots", "shotstotal"],
    }
    for a in aliases.get(key, [key.lower()]):
        if a in stat_row:
            return stat_row[a]
    return None


def hit_rate(values, line, side):
    """How often a list of past results cleared the number."""
    if not values:
        return None
    if side == "over":
        hits = sum(1 for v in values if v > line)
    else:
        hits = sum(1 for v in values if v < line)
    return hits / len(values)


def prop_history(fetch, league, lg, game, player, market, season):
    """Past per-game values for this player and stat, newest last."""
    source, stat_key, _ = PROP_STATS.get(market, (None, None, None))
    if source == "mlb_pitching" or source == "mlb_hitting":
        pid = mlb_player_id(fetch, player, season)
        if not pid:
            return None
        group = "pitching" if source == "mlb_pitching" else "hitting"
        rows = mlb_game_log(fetch, pid, group, season)
        vals = [num(r["stat"].get(stat_key)) for r in rows]
        return [v for v in vals if v is not None]
    if source == "espn":
        for where in ("home", "away"):
            ids = game["sides"][where].get("roster") or {}
            aid = ids.get(_norm_name(player))
            if not aid:
                cands = [v for k, v in ids.items() if _last_name(k) == _last_name(player)]
                aid = cands[0] if len(cands) == 1 else None
            if aid:
                rows = espn_game_log(fetch, lg, aid)
                vals = [_espn_value(r["stat"], stat_key) for r in rows]
                return [v for v in vals if v is not None]
    return None


def wilson_low(hits, n, z=PROP_CONF):
    """The cautious end of a hit rate. With 25 of 26 it answers about 86%, not 96%,
    because a short record can't prove a high rate. Small samples get pulled down
    hard, which is exactly the protection we want before risking money."""
    if not n:
        return 0.0
    phat = hits / n
    denom = 1 + z * z / n
    centre = phat + z * z / (2 * n)
    margin = z * math.sqrt((phat * (1 - phat) + z * z / (4 * n)) / n)
    return max(0.0, (centre - margin) / denom)


def score_prop(values, line, side, price):
    """Turns a hit rate into an edge over the book's implied probability."""
    if not values or len(values) < MIN_PROP_GAMES:
        return None
    full = hit_rate(values, line, side)
    recent = hit_rate(values[-10:], line, side)
    if full is None or recent is None:
        return None
    n = len(values)
    hits = sum(1 for v in values if (v > line if side == "over" else v < line))
    prob = wilson_low(hits, n)
    # Recent form can only drag the number down, never inflate it.
    if recent < full:
        prob = min(prob, wilson_low(round(recent * min(n, 10)), min(n, 10)) * 0.5 + prob * 0.5)
    imp = implied_prob(price)
    return {"prob": prob, "implied": imp, "edge": prob - imp, "n": n,
            "full": full, "recent": recent, "last5": hit_rate(values[-5:], line, side),
            "avg": statistics.mean(values)}


def build_props(fetch, client, board, season, log=print):
    """Finds every player prop with a real edge, across the day's games."""
    out = []
    if not client.on:
        return out
    for entry in board["leagues"]:
        league = entry["name"]
        if not PROP_MARKETS.get(league):
            continue
        lg = LEAGUES[league]
        games = [g for g in entry["games"] if g["state"] == "pre" and g.get("odds_event_id")][:PROP_GAMES_PER_LEAGUE]
        for g in games:
            if client.room("props") < len(PROP_MARKETS[league]):
                break
            rows = client.props(league, g["odds_event_id"])
            if not rows:
                continue
            if PROP_STATS.get(rows[0]["market"], ("",))[0] == "espn":
                for where in ("home", "away"):
                    if g["sides"][where].get("roster") is None:
                        try:
                            g["sides"][where]["roster"] = espn_athlete_ids(fetch, lg, g["sides"][where]["id"])
                        except Exception:
                            g["sides"][where]["roster"] = {}
            # best price per player/market/line/side across books
            best = {}
            for r in rows:
                if r["point"] is None or not r["price"] or r["name"] not in ("Over", "Under"):
                    continue
                k = (r["player"], r["market"], r["point"], r["name"].lower())
                if k not in best or payout(r["price"]) > payout(best[k]["price"]):
                    best[k] = r
            seen = {}
            for (player, market, line, side), r in best.items():
                if ODDS_FLOOR is not None and (num(r["price"]) or -110) > ODDS_FLOOR:
                    continue
                key = (player, market)
                if key not in seen:
                    try:
                        seen[key] = prop_history(fetch, league, lg, g, player, market, season)
                    except Exception:
                        seen[key] = None
                vals = seen[key]
                if not vals:
                    continue
                sc = score_prop(vals, line, side, r["price"])
                if not sc or sc["edge"] < MIN_PROP_EDGE:
                    continue
                out.append({"league": league, "game": f'{g["away"]} @ {g["home"]}', "time": g["time"],
                            "player": player, "market": market,
                            "label": PROP_STATS.get(market, (None, None, market))[2],
                            "line": line, "side": side, "price": r["price"], "book": r["book"],
                            "link": r.get("link"), **sc})
        log(f"  {league}: {sum(1 for p in out if p['league'] == league)} prop edges")
    out.sort(key=lambda p: -p["edge"])
    return out[:PROP_MAX_ROWS]


# ---------------------------------------------------------------------------
# Alternate totals: buying down to a safer number
# ---------------------------------------------------------------------------

def alt_total_play(league, proj, rows, side):
    """Picks the alternate total with the best expected value on the side we like,
    which is how a heavy price at a high hit rate becomes the bet."""
    if not proj or not rows:
        return None
    best = None
    for r in rows:
        if r["point"] is None or not r["price"] or (r["name"] or "").lower() != side:
            continue
        price = num(r["price"])
        if price is None or (ODDS_FLOOR is not None and price > ODDS_FLOOR):
            continue
        if price < ALT_MAX_LAY:            # too expensive to risk a unit on
            continue
        prob = side_probs(league, proj["total"], r["point"])[side]
        imp = implied_prob(r["price"])
        edge = prob - imp
        ev = prob * payout(r["price"]) - (1 - prob)
        if edge < MIN_ALT_EDGE or prob < ALT_MIN_PROB:
            continue
        cand = {"line": r["point"], "price": r["price"], "book": r["book"], "link": r.get("link"),
                "prob": prob, "implied": imp, "edge": edge, "ev": ev, "side": side}
        if best is None or cand["ev"] > best["ev"]:
            best = cand
    return best


# ---------------------------------------------------------------------------
# Arbitrage scanner
# ---------------------------------------------------------------------------

def _best_cross_book(side_a, side_b):
    """Cheapest pair of prices from two different books. One book often leads on
    both sides, so every combination is tried, not just the top price on each."""
    best = None
    for a in side_a:
        for b in side_b:
            if a["book_key"] == b["book_key"]:
                continue
            total = implied_prob(a["price"]) + implied_prob(b["price"])
            if total >= 1:
                continue
            if best is None or total < best[0]:
                best = (total, a, b)
    return best


def _arb(ev, label, what, pair):
    total, a, b = pair
    return {"what": f"{label} {what}", "game": f'{ev["away"]} @ {ev["home"]}', "start": ev.get("start"),
            "total": total, "profit": (1 / total) - 1,
            "legs": [{"side": a.get("label") or a["name"], **a},
                     {"side": b.get("label") or b["name"], **b}]}


def find_arbs(events, label, market="totals"):
    """Both sides of one market priced at different books so the two prices
    together come to under 100%, which locks in a profit either way."""
    found = []
    for ev in events:
        rows = ev.get("rows") or []
        if market == "totals":
            by_line = {}
            for r in rows:
                if r["point"] is None or not r["price"] or (r["name"] or "").lower() not in ("over", "under"):
                    continue
                by_line.setdefault(r["point"], {}).setdefault(r["name"].lower(), []).append(r)
            for line, sides in by_line.items():
                if "over" in sides and "under" in sides:
                    pair = _best_cross_book(sides["over"], sides["under"])
                    if pair:
                        for leg, word in ((pair[1], "Over"), (pair[2], "Under")):
                            leg["label"] = f"{word} {fmt_num(line)}"
                        found.append(_arb(ev, label, f"total {fmt_num(line)}", pair))
        elif market == "h2h":
            sides = {}
            for r in rows:
                if r["price"] and r["name"]:
                    sides.setdefault(r["name"], []).append(r)
            names = [n for n in sides if n.lower() != "draw"]
            if len(names) == 2:
                pair = _best_cross_book(sides[names[0]], sides[names[1]])
                if pair:
                    for leg in (pair[1], pair[2]):
                        leg["label"] = leg["name"]
                    found.append(_arb(ev, label, "moneyline", pair))
        elif market == "spreads":
            by_point = {}
            for r in rows:
                if r["point"] is None or not r["price"] or not r["name"]:
                    continue
                by_point.setdefault(abs(r["point"]), []).append(r)
            for point, group in by_point.items():
                favs = [r for r in group if r["point"] < 0]
                dogs = [r for r in group if r["point"] > 0]
                if not favs or not dogs:
                    continue
                pair = _best_cross_book(favs, dogs)
                if pair:
                    for leg in (pair[1], pair[2]):
                        leg["label"] = f'{leg["name"]} {"+" if leg["point"] > 0 else ""}{fmt_num(leg["point"])}'
                    found.append(_arb(ev, label, f"spread {fmt_num(point)}", pair))
    found.sort(key=lambda a: -a["profit"])
    return found


def scan_arbs(board, client, log=print):
    """Scans every market we can afford. Totals come free because the board
    already paid for them; moneylines and spreads cost from the arb share."""
    arbs = []
    for entry in board["leagues"]:
        for ev in entry.get("book_rows") or []:
            arbs.extend(find_arbs([ev], entry["name"], "totals"))
    if client and client.on and ARB_MARKETS:
        for entry in board["leagues"]:
            if not entry.get("book_rows"):
                continue
            if client.room("arb") < len(ARB_MARKETS):
                client.skipped.append(f"{entry['name']} moneyline/spread arbs (arb share used up)")
                continue
            try:
                events = client.using("arb").game_markets(entry["name"], ARB_MARKETS)
            except Exception as err:
                client.note(f"{entry['name']} extra markets unavailable ({err})")
                events = []
            finally:
                client.pool = None
            for ev in events:
                for market, rows in ev["markets"].items():
                    arbs.extend(find_arbs([dict(ev, rows=rows)], entry["name"], market))
    seen, out = set(), []
    for a in sorted(arbs, key=lambda a: -a["profit"]):
        key = (a["game"], a["what"])
        if a["profit"] >= MIN_ARB_PROFIT and key not in seen:
            seen.add(key)
            out.append(a)
    return out[:25]


# ---------------------------------------------------------------------------
# Team totals: one side's score against its own number
# ---------------------------------------------------------------------------

def team_total_plays(league, proj, rows, home_name, away_name):
    """The projection already splits a game into each team's expected score, so
    a team total is the same test applied to one side."""
    if not proj or not rows:
        return []
    sigma = SIGMA.get(league, 15.0) / 1.414      # one side swings less than the game
    out = []
    for who, expect, name in (("home", proj["home"], home_name), ("away", proj["away"], away_name)):
        best = None
        for r in rows:
            if r["point"] is None or not r["price"] or (r["name"] or "").lower() not in ("over", "under"):
                continue
            # The provider labels team totals with the team's name; keep only this side's.
            label = (r.get("player") or r.get("team") or "").strip()
            if label and not _same_name(label, name):
                continue
            side = r["name"].lower()
            z = (r["point"] - expect) / sigma
            prob = norm_cdf(z) if side == "under" else 1 - norm_cdf(z)
            imp = implied_prob(r["price"])
            edge = prob - imp
            if edge < MIN_EDGE or prob < TEAM_TOTAL_MIN_PROB:
                continue
            if ODDS_FLOOR is not None and (num(r["price"]) or -110) > ODDS_FLOOR:
                continue
            cand = {"who": who, "team": name, "side": side, "line": r["point"], "price": r["price"],
                    "book": r["book"], "link": r.get("link"), "prob": prob, "implied": imp,
                    "edge": edge, "expect": expect}
            if best is None or cand["edge"] > best["edge"]:
                best = cand
        if best:
            out.append(best)
    return out


def _same_name(label, name):
    a, b = _plain(label), _plain(name)
    if not a or not b:
        return False
    return a == b or a in b or b in a or a.split()[-1] == b.split()[-1]


def build_team_totals(client, board, log=print):
    """Pulls team totals for the games most likely to matter and keeps the
    sides with a real edge."""
    out = []
    if not client or not client.on:
        return out
    for entry in board["leagues"]:
        games = [g for g in entry["games"]
                 if g["state"] == "pre" and g.get("odds_event_id") and g.get("proj")]
        games.sort(key=lambda g: 0 if play_of(g) else 1)      # Best Bet games first
        for g in games[:TEAM_TOTAL_GAMES_PER_LEAGUE]:
            if client.room("team") < 1:
                break
            try:
                rows = client.using("team").team_totals(entry["name"], g["odds_event_id"])
            except Exception:
                rows = []
            finally:
                client.pool = None
            for play in team_total_plays(entry["name"], g["proj"], rows, g["home"], g["away"]):
                out.append({"league": entry["name"], "game": f'{g["away"]} @ {g["home"]}',
                            "time": g["time"], **play})
    out.sort(key=lambda p: -p["edge"])
    return out[:TEAM_TOTAL_MAX_ROWS]


# ---------------------------------------------------------------------------
# UFC: fights that are unlikely to reach the judges
# ---------------------------------------------------------------------------

UFC_ESPN = "https://site.api.espn.com/apis/site/v2/sports/mma/ufc"


def ufc_card(fetch, day):
    """Today's UFC fights from ESPN, with each fighter's id and record."""
    data = fetch.json(f"{UFC_ESPN}/scoreboard?dates={day:%Y%m%d}")
    fights = []
    for ev in (data or {}).get("events") or []:
        for comp in ev.get("competitions") or []:
            start = parse_iso(comp.get("date") or ev.get("date"))
            if start is None or to_local(start).date() != day:
                continue
            state = ((comp.get("status") or {}).get("type") or {})
            people = []
            for c in comp.get("competitors") or []:
                ath = c.get("athlete") or {}
                people.append({"id": str(ath.get("id") or ""),
                               "name": ath.get("displayName") or ath.get("shortName") or "",
                               "record": next((str(r.get("summary") or "") for r in c.get("records") or []), "")})
            if len(people) != 2 or not all(p["name"] for p in people):
                continue
            fights.append({
                "id": str(comp.get("id") or ev.get("id")), "a": people[0], "b": people[1],
                "start": start, "time": clock(to_local(start)),
                "title": bool(comp.get("type", {}).get("abbreviation") == "Title"
                              or "title" in str(ev.get("name", "")).lower()),
                "rounds": num(comp.get("format", {}).get("regulation", {}).get("periods")) or 3,
                "state": state.get("state") or "pre",
                "card": (comp.get("type") or {}).get("text") or "",
            })
    fights.sort(key=lambda f: f["start"])
    return fights


def _scan_methods(node, found):
    """ESPN labels win methods differently by endpoint, so look for the words."""
    if isinstance(node, dict):
        label = str(node.get("displayName") or node.get("name") or node.get("abbreviation") or "").lower()
        value = node.get("value", node.get("displayValue"))
        v = num(value)
        if v is not None:
            if any(w in label for w in ("ko/tko", "knockout", "tko")):
                found["ko"] = found.get("ko", 0) + v
            elif "submission" in label or label == "sub":
                found["sub"] = found.get("sub", 0) + v
            elif "decision" in label:
                found["dec"] = found.get("dec", 0) + v
            elif label in ("fights", "totalfights", "bouts"):
                found["fights"] = max(found.get("fights", 0), v)
        for x in node.values():
            if isinstance(x, (dict, list)):
                _scan_methods(x, found)
    elif isinstance(node, list):
        for x in node:
            _scan_methods(x, found)
    return found


def fighter_finish_rate(fetch, athlete_id, record_text=""):
    """How often this fighter's bouts end before the judges score them.
    Counts wins and losses, because either ends the fight early."""
    if not athlete_id:
        return None
    data = fetch.json(f"https://site.web.api.espn.com/apis/common/v3/sports/mma/ufc/athletes/{athlete_id}")
    methods = _scan_methods(data or {}, {})
    ko, sub, dec = methods.get("ko", 0), methods.get("sub", 0), methods.get("dec", 0)
    inside = ko + sub
    total = inside + dec
    if total < UFC_MIN_FIGHTS:
        # Fall back on the win-loss-draw record only to size the sample, never
        # to invent a finish rate.
        return None
    return {"rate": inside / total, "inside": int(inside), "fights": int(total),
            "ko": int(ko), "sub": int(sub)}


def ufc_plays(fetch, client, day, log=print):
    """Fights where the books price an early finish and both fighters have a
    history of finishing. The bet is that it does not reach the judges."""
    try:
        card = ufc_card(fetch, day)
    except Exception as err:
        log(f"  UFC: card unavailable ({err})")
        return {"fights": [], "plays": [], "note": "ESPN didn't return a UFC card."}
    card = [f for f in card if f["state"] == "pre"]
    if not card:
        return {"fights": [], "plays": [], "note": None}
    totals = {}
    if client and client.on and client.room("props") >= 1:
        try:
            for ev in client.using("props").game_totals("UFC"):
                totals[(_plain(ev["home"]), _plain(ev["away"]))] = ev["rows"]
        except Exception as err:
            client.note(f"UFC prices unavailable ({err})")
        finally:
            client.pool = None
    plays = []
    for f in card:
        rows = None
        for (h, a), r in totals.items():
            names = {_plain(f["a"]["name"]), _plain(f["b"]["name"])}
            if {h, a} & names or any(n in h or n in a for n in names):
                rows = r
                break
        round_line = None
        if rows:
            points = [r["point"] for r in rows if r["point"] is not None]
            round_line = min(points) if points else None
        rates = []
        for who in ("a", "b"):
            try:
                rates.append(fighter_finish_rate(fetch, f[who]["id"], f[who]["record"]))
            except Exception:
                rates.append(None)
        f["rates"] = rates
        f["round_line"] = round_line
        if not all(rates):
            f["why"] = "Not enough fight history on ESPN to measure finish rates."
            continue
        if round_line is not None and round_line > UFC_MAX_ROUND_LINE:
            f["why"] = (f"Rounds total is {fmt_num(round_line)}; the strategy wants "
                        f"{fmt_num(UFC_MAX_ROUND_LINE)} or lower.")
            continue
        if min(r["rate"] for r in rates) < UFC_MIN_FINISH:
            low = min(rates, key=lambda r: r["rate"])
            f["why"] = f"One fighter finishes only {low['rate']:.0%} of the time."
            continue
        # Chance it ends early: either man can finish, but only one of them will.
        a, b = rates
        prob = 1 - (1 - a["rate"]) * (1 - b["rate"])
        prob = min(prob, UFC_PROB_CAP)      # never claim near-certainty
        n = min(a["fights"], b["fights"])
        prob = wilson_low(round(prob * n), n)
        f["prob"] = prob
        if prob < UFC_MIN_PROB:
            f["why"] = f"Model says only {prob:.0%} it ends early, below the {UFC_MIN_PROB:.0%} floor."
            continue
        # The strategy says this is playable up to -600. That only holds if the
        # fight really is better than the 85.7% -600 implies, so the break-even
        # price is published instead of assuming the ceiling is fine.
        max_price = price_for_prob(prob - MIN_EDGE)
        ceiling = implied_prob(UFC_ASSUMED_PRICE)
        plays.append({**f, "prob": prob, "max_price": max_price,
                      "ceiling_ok": prob - ceiling >= MIN_EDGE,
                      "implied": ceiling, "edge": prob - ceiling,
                      "distance": 5 if (f["title"] or f["rounds"] == 5) else 3})
    plays.sort(key=lambda p: -p["edge"])
    return {"fights": card, "plays": plays, "note": None}


# ---------------------------------------------------------------------------
# Line movement: where the number opened and where the money went
# ---------------------------------------------------------------------------

def steam_note(open_line, now_line, league):
    """Describes a big move off the opener. A move this size usually means
    sharp money, which is the half of the strategy we can actually measure."""
    if open_line is None or now_line is None:
        return None
    move = now_line - open_line
    big = STEAM_POINTS.get(league, 2.0)
    if abs(move) < big:
        return None
    return {"move": move, "side": "over" if move > 0 else "under",
            "text": f"Total moved {'up' if move > 0 else 'down'} {fmt_num(abs(move))} from the "
                    f"{fmt_num(open_line)} opener"}


# ---------------------------------------------------------------------------
# Building the day's board
# ---------------------------------------------------------------------------

def summarize(meetings, line):
    totals = [m["total"] for m in meetings]
    if len(totals) < MIN_MEETINGS:
        return None
    stats = {"n": len(totals), "mean": statistics.mean(totals),
             "median": statistics.median(totals), "totals": totals,
             "gap_mean": None, "gap_median": None}
    if line is not None:
        stats["gap_mean"] = line - stats["mean"]
        stats["gap_median"] = line - stats["median"]
    return stats


def build_board(fetch, day, league_names, client=None, log=print):
    board = {"date": day, "built": to_local(utcnow()), "leagues": [], "props": [], "arbs": [],
             "team_totals": [], "ufc": {"fights": [], "plays": [], "note": None}, "odds_note": None}
    for name in league_names:
        lg = LEAGUES[name]
        entry = {"name": name, "unit": lg["unit"], "games": [], "error": None,
                 "prior_season": False, "book_rows": []}
        board["leagues"].append(entry)
        try:
            games = scoreboard(fetch, lg, day)
        except Exception as err:
            entry["error"] = f"Couldn't load the {name} schedule from ESPN ({err})."
            log(f"{name}: schedule failed: {err}")
            continue
        if not games:
            log(f"{name}: no {name} games today.")
            continue
        log(f"{name}: {len(games)} game(s). Pulling trends and matchup factors...")
        entry["skipped"] = 0

        # Odds credits are only spent where they can change a bet: a league needs
        # at least one game that hasn't started. Out-of-season leagues never reach
        # here at all, because ESPN returns no games and we skip above.
        book_events = []
        upcoming = [g for g in games if g["state"] == "pre"]
        if client and client.on:
            if not upcoming:
                client.skipped.append(f"{name} (all {len(games)} games already started)")
                log(f"  {name}: every game has started, skipping the odds call")
            elif not PROP_MARKETS.get(name) and client.left < 1:
                client.skipped.append(f"{name} (out of credits)")
            else:
                try:
                    book_events = client.game_totals(name)
                    entry["book_rows"] = [{"home": e["home"], "away": e["away"],
                                           "start": e["start"], "rows": e["rows"]} for e in book_events]
                except Exception as err:
                    client.note(f"{name} prices unavailable ({err})")
        try:
            ranks = defense_ranks(fetch, lg)
        except Exception:
            ranks = {}
        season, prior = None, False
        for probe in games[:4]:            # try a few teams in case one schedule comes back empty
            try:
                season, prior = current_season(fetch, lg, probe["home"]["id"], probe["start"], day)
            except Exception:
                season = None
            if season is not None:
                break
        entry["prior_season"] = prior

        for g in games:
            odds = g["espn_odds"]
            match = match_book_event(g, book_events)
            if match:
                g["odds_event_id"] = match["id"]
                shopped = best_book_total(match["rows"])
                if shopped:
                    g["books"] = shopped
                    if odds is None or shopped.get("line") is not None:
                        odds = {"line": shopped["line"], "over": shopped["over"]["price"],
                                "under": shopped["under"]["price"], "book": shopped["consensus_book"]}
            line = odds["line"] if odds else None
            if line is None and lg.get("require_line"):
                entry["skipped"] = entry.get("skipped", 0) + 1
                continue
            note = None
            try:
                meetings = last_meetings(fetch, lg, g["home"]["id"], g["away"]["id"], g["start"], day)
            except Exception as err:
                meetings, note = [], f"Couldn't load past meetings ({err})."
            stats = summarize(meetings, line)
            if stats is None and note is None:
                span = f"in the last {lg['seasons_back']} seasons"
                note = (f"No past meetings found {span}." if not meetings else
                        f"Only {len(meetings)} past meeting{'s' if len(meetings) != 1 else ''} "
                        f"found {span}, not enough for averages.")
            sides = {}
            for where in ("home", "away"):
                team = g[where]
                try:
                    split = team_splits(fetch, lg, team["id"], season, g["start"])
                except Exception:
                    split = None
                sides[where] = {"name": team["name"], "nickname": team["nickname"] or team["name"],
                                "split": split, "starter": team.get("starter"),
                                "passer": team.get("passer"), "rank": ranks.get(team["id"]),
                                "rest": rest_days(split, g["start"])}
            proj = project_total(name, lg, sides["home"], sides["away"])
            pick = recommend(name, lg, line, stats, proj, odds)
            probs = side_probs(name, proj["total"], line) if proj and line is not None else None
            local = to_local(g["start"])
            entry["games"].append({
                "league": name, "id": g["id"], "start_utc": g["start"].isoformat(),
                "time": clock(local), "away": g["away"]["name"], "home": g["home"]["name"],
                "state": g["state"], "status": g["status"], "final_total": g["final_total"],
                "odds": odds, "meetings": meetings, "stats": stats,
                "note": note, "sides": sides, "proj": proj, "pick": pick, "probs": probs,
                "env": g.get("env"), "first_line": None, "locked": None,
                "odds_event_id": None, "books": None, "alt": None, "steam": None, "open_line": None,
            })
            print(".", end="", flush=True)
        print()
    return board


# ---------------------------------------------------------------------------
# History, grading and the record
# ---------------------------------------------------------------------------

def enrich_with_books(board, client, history, log=print):
    """Second pass once prices are in: opening-line movement, and the best
    alternate total to buy down to on each Best Bet."""
    board.setdefault("arbs", [])
    if not client or not client.on:
        return
    for entry in board["leagues"]:
        for g in entry["games"]:
            row = history.get((g["league"], g["id"])) or {}
            open_line = num(row.get("open_line"))
            if open_line is None and g["odds"]:
                open_line = g["first_line"] if g["first_line"] is not None else g["odds"]["line"]
            g["open_line"] = open_line
            if g["odds"]:
                g["steam"] = steam_note(open_line, g["odds"]["line"], g["league"])
            pl = play_of(g)
            if not pl or pl.get("result") or g["state"] != "pre" or not g["odds_event_id"]:
                continue
            if client.room("arb") < 1:
                continue
            try:
                rows = client.using("arb").alt_totals(g["league"], g["odds_event_id"])
            except Exception:
                rows = []
            finally:
                client.pool = None
            if rows:
                g["alt"] = alt_total_play(g["league"], g["proj"], rows, pl["side"])
                g["alt_rows"] = [{"home": g["home"], "away": g["away"], "start": g["start"], "rows": rows}]


def load_history(path):
    if not path.exists():
        return {}
    with open(path, newline="", encoding="utf-8") as fh:
        return {(r["league"], r["event_id"]): {f: r.get(f) or "" for f in HIST_FIELDS}
                for r in csv.DictReader(fh)}


def save_history(path, history):
    rows = sorted(history.values(), key=lambda r: (r["date"], r["league"], r.get("start_utc", "")))
    with open(path, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=HIST_FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def grade(line_text, total):
    line = num(line_text)
    if line is None:
        return "no line"
    if total > line:
        return "over"
    if total < line:
        return "under"
    return "push"


def record_board(history, board):
    day = board["date"].isoformat()
    for entry in board["leagues"]:
        for g in entry["games"]:
            key = (g["league"], g["id"])
            row = history.get(key) or {f: "" for f in HIST_FIELDS}
            if g["state"] == "pre" or not row.get("date"):
                row.update(date=day, league=g["league"], event_id=g["id"],
                           start_utc=g["start_utc"], away=g["away"], home=g["home"])
                if g["odds"]:
                    if not row.get("open_line"):
                        row["open_line"] = fmt_num(g["odds"]["line"])
                    if not row.get("first_line"):
                        row["first_line"] = row.get("line") or fmt_num(g["odds"]["line"])
                    row.update(line=fmt_num(g["odds"]["line"]), over_price=g["odds"]["over"] or "",
                               under_price=g["odds"]["under"] or "", book=g["odds"]["book"])
                s = g["stats"]
                if s:
                    row.update(h2h_games=str(s["n"]), mean=f"{s['mean']:.2f}",
                               median=f"{s['median']:.2f}")
                line, mean, median = num(row["line"]), num(row["mean"]), num(row["median"])
                if line is not None and mean is not None:
                    row.update(gap_mean=f"{line - mean:.2f}", gap_median=f"{line - median:.2f}")
                row["proj"] = f"{g['proj']['total']:.2f}" if g["proj"] else ""
                pick = g["pick"]
                if pick and not row.get("pick"):
                    # First time this game qualifies: lock the play at this line and price.
                    # Later line moves never remove it; it's graded at the locked line.
                    row.update(pick=pick["side"], tier=pick["tier"], pick_price=pick.get("price") or "",
                               pick_line=fmt_num(g["odds"]["line"]), pick_time=clock(board["built"]),
                               pick_prob=f"{pick['prob']:.3f}", pick_edge=f"{pick['edge_prob']:.3f}")
            if g.get("alt") and not row.get("alt_line"):
                row.update(alt_line=fmt_num(g["alt"]["line"]), alt_price=g["alt"]["price"],
                           alt_book=g["alt"]["book"])
            if g["final_total"] is not None and not row.get("result"):
                row.update(final_total=fmt_num(g["final_total"]),
                           result=grade(row.get("line"), g["final_total"]))
                if row.get("pick"):
                    row["pick_result"] = grade(row.get("pick_line") or row.get("line"), g["final_total"])
            history[key] = row
            g["first_line"] = num(row.get("first_line"))
            if row.get("pick"):
                g["locked"] = {"side": row["pick"], "tier": row["tier"], "price": row.get("pick_price") or "-110",
                               "line": num(row.get("pick_line")) if row.get("pick_line") else num(row.get("line")),
                               "time": row.get("pick_time") or "", "prob": num(row.get("pick_prob")),
                               "edge": num(row.get("pick_edge")), "still": bool(g["pick"]),
                               "result": row.get("pick_result") or ""}


def grade_past(history, fetch, today, log=print):
    pending = {}
    for row in history.values():
        if row.get("result"):
            continue
        try:
            day = dt.date.fromisoformat(row["date"])
        except ValueError:
            continue
        if today - dt.timedelta(days=14) <= day < today:
            pending.setdefault((row["league"], day), []).append(row)
    graded = 0
    for (league, day), rows in pending.items():
        lg = LEAGUES.get(league)
        if not lg:
            continue
        try:
            finals = {g["id"]: g["final_total"] for g in scoreboard(fetch, lg, day)
                      if g["final_total"] is not None}
        except Exception:
            continue
        for row in rows:
            total = finals.get(row["event_id"])
            if total is not None:
                row.update(final_total=fmt_num(total), result=grade(row.get("line"), total))
                if row.get("pick"):
                    row["pick_result"] = grade(row.get("pick_line") or row.get("line"), total)
                graded += 1
    if graded:
        log(f"Graded {graded} finished game(s) from earlier days.")


def _blank_record():
    return {"graded": 0, "over": 0, "under": 0, "push": 0, "trend_n": 0, "trend_w": 0,
            "bets": 0, "wins": 0, "losses": 0, "pushes": 0, "units": 0.0,
            "strong_n": 0, "strong_w": 0}


def track_record(history):
    table = {}
    for row in history.values():
        result = row.get("result")
        if result not in ("over", "under", "push"):
            continue
        side = lean(num(row.get("gap_mean")), num(row.get("gap_median")))
        pick, tier = row.get("pick"), row.get("tier")
        for bucket in (row["league"], "All"):
            s = table.setdefault(bucket, _blank_record())
            s["graded"] += 1
            s[result] += 1
            if side and result != "push":
                s["trend_n"] += 1
                s["trend_w"] += result == side
            pr = row.get("pick_result") or result     # older rows were graded at the closing line
            if pick:
                s["bets"] += 1
                if pr == "push":
                    s["pushes"] += 1
                elif pr == pick:
                    s["wins"] += 1
                    s["units"] += payout(row.get("pick_price"))
                else:
                    s["losses"] += 1
                    s["units"] -= 1
                if tier == "Strong" and pr != "push":
                    s["strong_n"] += 1
                    s["strong_w"] += pr == pick
    return table

# ---------------------------------------------------------------------------
# The page
# ---------------------------------------------------------------------------

CSS = """
:root{--font:"Rubik",system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif}
:root[data-theme="night"]{color-scheme:dark;--bg:#05070A;--card:#0B0F16;--tile:#111724;--border:#1D2637;--text:#EAF0FA;
--muted:#8E9AB3;--dim:#596580;--green:#34D399;--red:#FB7185;--amber:#FBBF24;--blue:#60A5FA;--violet:#A78BFA;--pink:#F472B6;
--cyan:#22D3EE;--line:#22D3EE;--grad:linear-gradient(135deg,#7C3AED 0%,#EC4899 100%);
--bar:linear-gradient(90deg,#8B5CF6,#EC4899);--glow:0 0 28px rgba(124,58,237,.22);--pillbg:#0B0F16}
:root[data-theme="day"]{color-scheme:light;--bg:#F2F5F9;--card:#FFFFFF;--tile:#F1F4F8;--border:#DAE1EA;--text:#141B26;
--muted:#5B6678;--dim:#8792A3;--green:#15803D;--red:#C2410C;--amber:#B45309;--blue:#2563EB;--violet:#6D28D9;--pink:#DB2777;
--cyan:#0E7490;--line:#B45309;--grad:linear-gradient(135deg,#1F9D7A 0%,#2563EB 100%);
--bar:linear-gradient(90deg,#1F9D7A,#2563EB);--glow:none;--pillbg:#E6EBF2}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%;scroll-behavior:smooth}
@media (prefers-reduced-motion:reduce){html{scroll-behavior:auto}.live-dot{animation:none}}
body{margin:0;min-height:100vh;color:var(--text);font:400 15px/1.5 var(--font);background:var(--bg)}
:root[data-theme="night"] body{background:radial-gradient(90% 40% at 50% 0%,rgba(124,58,237,.14) 0%,rgba(5,7,10,0) 60%),#05070A}
a{color:inherit}
button{font-family:inherit}
.topbar{position:sticky;top:0;z-index:20;background:var(--card);border-bottom:1px solid var(--border)}
:root[data-theme="night"] .topbar{background:rgba(11,15,22,.9);backdrop-filter:blur(14px);-webkit-backdrop-filter:blur(14px)}
.appbar{display:flex;align-items:center;justify-content:space-between;gap:10px;
padding:calc(env(safe-area-inset-top,0px) + 10px) max(14px,env(safe-area-inset-right,0px)) 10px max(14px,env(safe-area-inset-left,0px))}
.brand{display:flex;align-items:center;gap:10px;text-decoration:none}
.brand-word{display:flex;flex-direction:column;line-height:1}
.brand-word b{font-weight:600;letter-spacing:.32em;font-size:15px}
.brand-word small{margin-top:4px;color:var(--muted);letter-spacing:.34em;font-size:9px;white-space:nowrap}
.bar-right{display:flex;align-items:center;gap:8px}
.iconbtn{display:grid;place-items:center;width:38px;height:38px;border-radius:12px;border:1px solid var(--border);
background:var(--tile);color:var(--text);cursor:pointer;padding:0}
.iconbtn:focus-visible,.chip:focus-visible,.bottomnav a:focus-visible,summary:focus-visible,.btn:focus-visible{outline:2px solid var(--violet);outline-offset:2px}
.datepill{padding:8px 14px;border-radius:999px;background:var(--grad);color:#fff;font-weight:500;font-size:13.5px;white-space:nowrap;box-shadow:var(--glow)}
.ticker{display:flex;gap:8px;overflow-x:auto;padding:0 14px 10px;scrollbar-width:none}
.ticker::-webkit-scrollbar{display:none}
.ticker:empty{display:none}
.tick{flex:none;min-width:128px;padding:7px 10px;border-radius:12px;background:var(--tile);border:1px solid var(--border);
text-decoration:none;font-size:12px;line-height:1.35;color:var(--text)}
.tick .tk-lg{display:flex;justify-content:space-between;gap:8px;color:var(--muted);font-size:11px;margin-bottom:2px}
.tick .tk-row{display:flex;justify-content:space-between;gap:10px;font-variant-numeric:tabular-nums}
.tick .tk-row i{font-style:normal;font-weight:600}
.tick.is-live .tk-lg{color:var(--green)}
.tick.is-final{opacity:.75}
.tick-msg{flex:none;font-size:12px;color:var(--muted);padding:6px 2px}
.live-dot{display:inline-block;width:7px;height:7px;border-radius:50%;background:var(--green);margin-right:5px;animation:pulse 1.6s infinite}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.35}}
main{max-width:1120px;margin:0 auto;padding:16px max(14px,env(safe-area-inset-right,0px)) calc(120px + env(safe-area-inset-bottom,0px)) max(14px,env(safe-area-inset-left,0px))}
section{scroll-margin-top:120px}
.card{background:var(--card);border:1px solid var(--border);border-radius:20px}
.tiles{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
@media (min-width:760px){.tiles{grid-template-columns:repeat(3,minmax(0,1fr))}}
@media (min-width:1000px){.tiles{grid-template-columns:repeat(5,minmax(0,1fr))}}
.tile{display:flex;gap:14px;padding:16px;align-items:flex-start}
@media (max-width:520px){.tile{flex-direction:column;gap:8px;padding:14px}}
.icon{flex:none;display:grid;place-items:center;width:42px;height:42px;border-radius:13px;background:var(--tile);color:var(--violet)}
.label{display:block;font-size:11.5px;letter-spacing:.12em;text-transform:uppercase;color:var(--muted)}
:root[data-theme="night"] .label::before{content:"\\25C6  ";color:var(--violet);font-size:9px;vertical-align:1px}
.tile strong{display:block;margin-top:6px;font-size:28px;font-weight:600;line-height:1.05;font-variant-numeric:tabular-nums}
.tile small{display:block;margin-top:6px;font-size:13px;color:var(--green)}
.tile small.flat{color:var(--muted)}
.updated{margin:12px 4px 0;font-size:12.5px;color:var(--dim)}
.chips{display:flex;gap:8px;overflow-x:auto;margin:10px -2px 4px;padding:2px;scrollbar-width:none}
.chips::-webkit-scrollbar{display:none}
.chip{flex:none;border:1px solid var(--border);background:var(--card);color:var(--muted);border-radius:999px;
padding:8px 15px;font:500 14px var(--font);cursor:pointer}
.chip[aria-pressed="true"]{background:var(--grad);border-color:transparent;color:#fff}
.section-head{display:flex;align-items:baseline;justify-content:space-between;gap:12px;margin:30px 4px 12px}
.section-head h2{margin:0;font-size:22px;font-weight:600}
.section-head span{color:var(--muted);font-size:13.5px;text-align:right}
.top-play{padding:20px;margin-bottom:12px;position:relative;overflow:hidden;
background:radial-gradient(120% 140% at 100% 0%,rgba(124,58,237,.22) 0%,rgba(0,0,0,0) 55%),var(--card)}
.top-play .label{color:var(--violet)}
.top-play .side{margin-top:8px;font-size:32px;font-weight:600;line-height:1.05}
.top-play p{margin:8px 0 0;color:var(--muted)}
.bet-group{padding:6px 18px 8px;margin-bottom:12px}
.bet-group h3{display:flex;justify-content:space-between;align-items:baseline;margin:12px 0 4px;font-size:17px;font-weight:600}
.bet-group h3 span{font-size:13px;font-weight:400;color:var(--muted)}
.bet{display:grid;grid-template-columns:minmax(0,1.05fr) minmax(0,1.7fr) auto;gap:6px 16px;align-items:start;
padding:14px 0;border-top:1px solid var(--border)}
.bet:first-of-type{border-top:0}
@media (max-width:700px){.bet{grid-template-columns:minmax(0,1fr) auto}.bet .why{grid-column:1/-1}.bet .tier{grid-row:1;grid-column:2}}
.side{font-weight:600;font-size:19px;line-height:1.2;font-variant-numeric:tabular-nums}
.side small{display:block;font-size:12.5px;font-weight:400;color:var(--muted)}
.why{font-size:13.5px;color:var(--muted)}
.why b{color:var(--text);font-weight:500}
.why .st{display:block;margin-top:3px}
.why .ok{color:var(--green)}.why .warn{color:var(--amber)}.why .mv{color:var(--blue)}
.why .won{color:var(--green);font-weight:500}.why .lost{color:var(--red);font-weight:500}
.bet-actions{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin-top:8px}
.btn{border:1px solid var(--border);background:var(--tile);color:var(--text);border-radius:10px;padding:7px 12px;font-size:13px;cursor:pointer}
.btn.primary{background:var(--grad);border-color:transparent;color:#fff}
.btn.danger{color:var(--red)}
.stake{font-size:13px;color:var(--muted)}
.stake b{color:var(--text)}
.tier{justify-self:end;padding:5px 12px;border-radius:999px;font-size:12px;letter-spacing:.08em;text-transform:uppercase;white-space:nowrap}
.tier.Strong{background:rgba(52,211,153,.16);color:var(--green)}
.tier.Lean{border:1px solid var(--border);color:var(--muted)}
.over{color:var(--green)!important}.under{color:var(--red)!important}
.empty{margin:10px 0 14px;color:var(--muted)}
.error{margin:10px 0 14px;color:var(--red)}
.league-block{margin-bottom:26px}
.league-title{display:flex;align-items:baseline;gap:10px;margin:0 4px 10px}
.league-title h3{margin:0;font-size:18px;font-weight:600}
.league-title span{color:var(--muted);font-size:13.5px}
.game{padding:18px;margin-bottom:12px}
.game-top{display:flex;justify-content:space-between;align-items:center;gap:12px;min-height:30px}
.when{font-size:13px;color:var(--muted);font-variant-numeric:tabular-nums}
.teams{margin-top:4px;font-size:17px;font-weight:500;line-height:1.35}
.teams .at{color:var(--dim);font-weight:400;margin:0 6px}
.badge{flex:none;padding:6px 12px;border-radius:999px;font-size:12.5px;font-weight:500;white-space:nowrap}
.badge.over{background:rgba(52,211,153,.14)}.badge.under{background:rgba(251,113,133,.14)}
.badge.pass{border:1px solid var(--border);color:var(--dim)}
.linebox{display:flex;flex-wrap:wrap;align-items:center;gap:10px 18px;margin-top:14px;padding:14px 16px;border-radius:16px;background:var(--tile)}
.linebox .num{font-size:28px;font-weight:600;line-height:1;font-variant-numeric:tabular-nums}
.pills{display:flex;gap:6px}
.pill{padding:5px 10px;border-radius:10px;background:var(--pillbg);font-size:13px;font-variant-numeric:tabular-nums;white-space:nowrap}
.book{margin-left:auto;text-align:right;font-size:13px;color:var(--muted);line-height:1.35}
.move{flex-basis:100%;font-size:12.5px;color:var(--blue)}
.probs{flex-basis:100%;font-size:12.5px;color:var(--muted)}
.probs b{font-weight:500}
.split{display:grid;grid-template-columns:minmax(0,1fr);gap:12px;margin-top:12px}
@media (min-width:760px){.split{grid-template-columns:repeat(2,minmax(0,1fr))}}
.box{padding:16px;border-radius:16px;background:var(--tile)}
.box-head{display:flex;justify-content:space-between;gap:8px;margin-bottom:10px}
.box-head span{font-size:12.5px;color:var(--dim)}
.pair{display:grid;grid-template-columns:1fr 1fr;gap:10px}
.stat .v{display:block;font-size:24px;font-weight:600;line-height:1.1;font-variant-numeric:tabular-nums}
.stat small{display:block;font-size:12.5px;color:var(--muted)}
.strip{position:relative;height:98px;margin:14px 8px 0}
.strip span{position:absolute;display:block}
.st-axis{left:-8px;right:-8px;bottom:31px;height:2px;background:var(--border)}
.st-game{width:9px;height:9px;margin-left:-4.5px;border:1.6px solid var(--muted);border-radius:50%}
.st-line{top:20px;bottom:22px;width:4px;margin-left:-2px;border-radius:2px;background:var(--line)}
.st-line em{position:absolute;top:-20px;left:50%;transform:translateX(-50%);white-space:nowrap;font:600 13px/1 var(--font);font-style:normal;color:var(--line)}
.st-line.st-left em{left:0;transform:none}.st-line.st-right em{left:auto;right:0;transform:none}
.st-median{bottom:26px;width:12px;height:12px;margin-left:-6px;transform:rotate(45deg);background:var(--tile);border:2.2px solid var(--text)}
.st-mean{bottom:26px;width:12px;height:12px;margin-left:-6px;border-radius:50%;background:var(--text)}
.st-lo,.st-hi{bottom:0;font-size:12px;color:var(--dim);font-variant-numeric:tabular-nums}
.st-lo{left:-8px}.st-hi{right:-8px}
details{margin-top:4px}
summary{cursor:pointer;color:var(--muted);font-size:13px;width:max-content;max-width:100%}
.wrap{overflow-x:auto}
table{border-collapse:collapse;width:100%;font-size:13px;font-variant-numeric:tabular-nums}
th,td{padding:7px 12px 7px 0;border-bottom:1px solid var(--border);text-align:left;white-space:nowrap}
th{font-weight:500;color:var(--muted)}
td.n,th.n{text-align:right}
.team-f{padding:10px 0;border-top:1px solid var(--border)}
.box-head+.team-f{border-top:0;padding-top:0}
.team-f h5{margin:0 0 6px;font-size:14px;font-weight:500}
.team-f h5 span{color:var(--dim);font-weight:400}
.frow{display:flex;justify-content:space-between;gap:12px;font-size:13px;line-height:1.7}
.frow span:first-child{color:var(--muted)}
.frow span:last-child{text-align:right}
.proj{display:flex;justify-content:space-between;align-items:baseline;gap:10px;margin-top:8px;padding-top:12px;border-top:1px solid var(--border)}
.proj .v{font-size:22px;font-weight:600;font-variant-numeric:tabular-nums}
.proj small{display:block;font-size:12.5px;text-align:right}
.note{margin:8px 0 0;font-size:13px;color:var(--muted)}
.live-head{display:flex;flex-wrap:wrap;justify-content:space-between;align-items:center;gap:8px;margin:0 4px 10px;font-size:13px;color:var(--muted)}
.lv-group{padding:6px 18px 8px;margin-bottom:12px}
.lv-group h3{display:flex;justify-content:space-between;align-items:baseline;margin:12px 0 4px;font-size:17px;font-weight:600}
.lv-group h3 span{font-size:13px;font-weight:400;color:var(--muted)}
.lv{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:4px 14px;align-items:center;padding:11px 0;border-top:1px solid var(--border)}
.lv:first-of-type{border-top:0}
.lv .tm{display:flex;justify-content:space-between;gap:10px;font-variant-numeric:tabular-nums}
.lv .tm b{font-weight:500}
.lv .tm.win b{color:var(--text)}
.lv .stt{grid-row:1/3;text-align:right;font-size:13px;color:var(--muted);min-width:84px}
.lv.is-live .stt{color:var(--green)}
.record{display:grid;grid-template-columns:minmax(0,1fr);gap:12px}
@media (min-width:860px){.record{grid-template-columns:repeat(2,minmax(0,1fr))}}
.rec-card{padding:20px}
.rec-card h3{margin:0 0 14px;font-size:17px;font-weight:600}
.donut-wrap{display:flex;align-items:center;gap:22px;flex-wrap:wrap}
.donut{width:170px;height:170px}
@media (max-width:520px){.donut{width:132px;height:132px}.donut-legend{min-width:120px}.donut-wrap{gap:16px}}
.donut-legend{flex:1;min-width:150px}
.donut-legend div{padding:10px 0;border-bottom:1px solid var(--border)}
.donut-legend div:last-child{border-bottom:0}
.donut-legend strong{display:block;font-size:26px;font-weight:600;line-height:1.1}
.donut-legend small{color:var(--muted)}
.bar-row{display:grid;grid-template-columns:62px 1fr 64px;align-items:center;gap:12px;padding:9px 0}
.bar{position:relative;height:10px;border-radius:999px;background:var(--tile);overflow:visible}
.bar i{position:absolute;left:0;top:0;bottom:0;border-radius:999px;background:var(--bar)}
.bar b{position:absolute;top:-4px;bottom:-4px;width:2px;background:var(--amber);border-radius:1px}
.bar-row span{color:var(--muted)}
.bar-row strong{text-align:right;font-weight:600;font-variant-numeric:tabular-nums}
.bar-foot{display:flex;justify-content:space-between;margin-top:10px;padding-top:12px;border-top:1px solid var(--border);color:var(--muted)}
.bar-foot strong{color:var(--green);font-weight:500}
.rec-note{margin:12px 0 0;font-size:13px;color:var(--muted);max-width:68ch}
.wide{grid-column:1/-1}
.form{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px 12px}
@media (min-width:760px){.form{grid-template-columns:repeat(4,minmax(0,1fr))}}
.form label{display:flex;flex-direction:column;gap:4px;font-size:12px;color:var(--muted)}
.form label.wide2{grid-column:span 2}
.form input,.form select,.form textarea{width:100%;padding:9px 10px;border-radius:10px;border:1px solid var(--border);background:var(--tile);color:var(--text);font:400 14px var(--font)}
.form-actions{grid-column:1/-1;display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin-top:4px}
.jsum{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px;margin:14px 0 4px}
@media (min-width:760px){.jsum{grid-template-columns:repeat(4,minmax(0,1fr))}}
.jsum div{padding:12px 14px;border-radius:14px;background:var(--tile)}
.jsum strong{display:block;font-size:22px;font-weight:600;line-height:1.1;font-variant-numeric:tabular-nums}
.jsum small{font-size:12px;color:var(--muted)}
.jrow td select{padding:4px 6px;border-radius:8px;border:1px solid var(--border);background:var(--tile);color:var(--text);font:400 13px var(--font)}
.jrow .del{border:0;background:none;color:var(--red);cursor:pointer;font-size:13px;padding:0}
.pgroup{padding:6px 18px 10px;margin-bottom:12px}
.pgroup h3{display:flex;justify-content:space-between;align-items:baseline;margin:12px 0 4px;font-size:17px;font-weight:600}
.pgroup h3 span{font-size:13px;font-weight:400;color:var(--muted)}
.prop{display:grid;grid-template-columns:minmax(0,1.25fr) minmax(0,1.6fr) auto;gap:4px 16px;align-items:start;padding:13px 0;border-top:1px solid var(--border)}
.prop:first-of-type{border-top:0}
@media (max-width:700px){.prop{grid-template-columns:minmax(0,1fr) auto}.prop .pwhy{grid-column:1/-1}}
.prop .pname{font-weight:600;font-size:16px;line-height:1.25}
.prop .pname small{display:block;font-size:12.5px;font-weight:400;color:var(--muted)}
.pwhy{font-size:13.5px;color:var(--muted)}
.pwhy b{color:var(--text);font-weight:500}
.edge{justify-self:end;text-align:right;font-variant-numeric:tabular-nums}
.edge b{display:block;font-size:19px;font-weight:600;color:var(--green)}
.edge small{font-size:11.5px;color:var(--muted)}
.hits{display:flex;gap:5px;margin-top:5px;flex-wrap:wrap}
.hits i{font-style:normal;font-size:11.5px;padding:2px 7px;border-radius:7px;background:var(--pillbg);color:var(--muted)}
.arb{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:4px 14px;padding:13px 0;border-top:1px solid var(--border)}
.arb:first-of-type{border-top:0}
.arb .legs{font-size:13.5px;color:var(--muted);line-height:1.6}
.arb .legs a{color:var(--blue)}
.alt{flex-basis:100%;font-size:12.5px;color:var(--violet)}
.steam{flex-basis:100%;font-size:12.5px;color:var(--amber)}
.arb-out{margin-top:12px;padding:14px 16px;border-radius:14px;background:var(--tile);font-size:14px;line-height:1.6}
.arb-out b{font-weight:600}
.arb-out .yes{color:var(--green)}.arb-out .no{color:var(--red)}
footer{margin:30px 4px 0;font-size:12.5px;color:var(--dim);max-width:72ch}
.bottomnav{position:fixed;left:0;right:0;bottom:0;z-index:30;display:flex;justify-content:space-around;
padding:8px max(4px,env(safe-area-inset-right,0px)) calc(8px + env(safe-area-inset-bottom,0px)) max(4px,env(safe-area-inset-left,0px));
background:var(--card);border-top:1px solid var(--border);border-radius:24px 24px 0 0}
:root[data-theme="night"] .bottomnav{background:rgba(11,15,22,.94);backdrop-filter:blur(16px);-webkit-backdrop-filter:blur(16px)}
.bottomnav a{display:flex;flex-direction:column;align-items:center;gap:3px;min-width:44px;padding:4px 2px;text-decoration:none;color:var(--dim);font-size:10.5px;border-radius:12px}
.bottomnav a.active{color:var(--text)}
@media (min-width:1000px){.bottomnav{left:50%;right:auto;transform:translateX(-50%);width:700px;bottom:14px;border-radius:24px;border:1px solid var(--border);padding-bottom:8px}}
"""

JS = r"""
(function(){
  var D=window.YUGI||{}, $=function(s,r){return (r||document).querySelector(s)}, $$=function(s,r){return Array.prototype.slice.call((r||document).querySelectorAll(s))};
  function esc(t){return String(t==null?'':t).replace(/[&<>"']/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]})}
  function store(k,v){try{if(v===undefined){var x=localStorage.getItem(k);return x?JSON.parse(x):null}localStorage.setItem(k,JSON.stringify(v))}catch(e){return null}}
  function money(n){return (n<0?'-':'')+'$'+Math.abs(n).toLocaleString(undefined,{minimumFractionDigits:0,maximumFractionDigits:0})}
  function money2(n){return (n<0?'-':'')+'$'+Math.abs(n).toLocaleString(undefined,{minimumFractionDigits:2,maximumFractionDigits:2})}
  function payout(p){p=parseFloat(p);if(isNaN(p))p=-110;return p>0?p/100:100/Math.abs(p)}
  function implied(p){p=parseFloat(p);if(isNaN(p))return null;return p<0?Math.abs(p)/(Math.abs(p)+100):100/(p+100)}

  /* ---------- theme ---------- */
  var root=document.documentElement;
  function setTheme(t){root.setAttribute('data-theme',t);store('yugi.theme',t);var m=$('meta[name=theme-color]');if(m)m.setAttribute('content',t==='day'?'#F2F5F9':'#05070A');
    var b=$('#themeBtn');if(b)b.setAttribute('aria-label',t==='day'?'Switch to night mode':'Switch to day mode')}
  var tb=$('#themeBtn');if(tb)tb.addEventListener('click',function(){setTheme(root.getAttribute('data-theme')==='day'?'night':'day')});

  /* ---------- sport chips ---------- */
  var chips=$$('.chip');
  chips.forEach(function(c){c.addEventListener('click',function(){var f=c.getAttribute('data-f');
    chips.forEach(function(x){x.setAttribute('aria-pressed',x===c?'true':'false')});
    $$('[data-league]').forEach(function(el){el.hidden=(f!=='all'&&el.getAttribute('data-league')!==f)})})});

  /* ---------- bottom nav highlight ---------- */
  var links=$$('.bottomnav a');
  if('IntersectionObserver' in window){var obs=new IntersectionObserver(function(es){es.forEach(function(e){if(e.isIntersecting){
    links.forEach(function(a){a.classList.toggle('active',a.getAttribute('href')==='#'+e.target.id)})}})},{rootMargin:'-40% 0px -55% 0px'});
    ['top','bets','props','live','board','journal','arb'].forEach(function(id){var el=document.getElementById(id);if(el)obs.observe(el)})}

  /* ---------- bankroll + stakes ---------- */
  var BR=store('yugi.bankroll')||{bankroll:0,unitPct:(D.unitPct||0.025)*100};
  function unit(){return BR.bankroll*(BR.unitPct/100)}
  function paintStakes(){var u=unit();$$('.stake').forEach(function(el){var n=parseFloat(el.getAttribute('data-units')||'1');
    el.innerHTML=u>0?'Stake <b>'+money(u*n)+'</b> ('+n+' unit, '+BR.unitPct+'% of bankroll)':'Set your bankroll in Journal for a stake size'});
    var bi=$('#bankroll'),ui=$('#unitPct'),uo=$('#unitOut');if(bi&&bi.value===''&&BR.bankroll)bi.value=BR.bankroll;if(ui&&ui.value==='')ui.value=BR.unitPct;
    if(uo)uo.textContent=u>0?'1 unit = '+money(u):'Enter a bankroll'}
  var bf=$('#bankForm');if(bf)bf.addEventListener('submit',function(e){e.preventDefault();BR={bankroll:parseFloat($('#bankroll').value)||0,unitPct:parseFloat($('#unitPct').value)||2.5};store('yugi.bankroll',BR);paintStakes();renderJournal()});

  /* ---------- journal ---------- */
  var J=store('yugi.journal')||[];
  function saveJ(){store('yugi.journal',J);renderJournal()}
  function profit(b){var st=parseFloat(b.stake)||0;if(b.result==='Win')return st*payout(b.odds);if(b.result==='Loss')return -st;return 0}
  function renderJournal(){var tb=$('#jbody');if(!tb)return;
    var rows=J.slice().sort(function(a,b){return (b.date||'').localeCompare(a.date||'')||(b.id-a.id)});
    tb.innerHTML=rows.map(function(b){var pr=profit(b);return '<tr class="jrow"><td>'+esc(b.date)+'</td><td>'+esc(b.sport)+'</td><td>'+esc(b.play)+
      (b.source?' <small style="color:var(--muted)">(bot '+esc(b.tier||'')+')</small>':'')+'</td><td class="n">'+esc(b.odds)+'</td><td class="n">'+money(parseFloat(b.stake)||0)+'</td>'+
      '<td><select data-id="'+b.id+'">'+['Pending','Win','Loss','Push'].map(function(r){return '<option'+(b.result===r?' selected':'')+'>'+r+'</option>'}).join('')+'</select></td>'+
      '<td class="n '+(pr>0?'over':pr<0?'under':'')+'">'+(b.result==='Pending'?'&ndash;':money2(pr))+'</td><td><button class="del" data-id="'+b.id+'" aria-label="Delete">Delete</button></td></tr>'}).join('')||
      '<tr><td colspan="8" style="color:var(--muted)">No bets logged yet. Use Log this bet on any Best Bet, or add one below.</td></tr>';
    $$('#jbody select').forEach(function(s){s.addEventListener('change',function(){var b=J.find(function(x){return String(x.id)===s.getAttribute('data-id')});if(b){b.result=s.value;saveJ()}})});
    $$('#jbody .del').forEach(function(d){d.addEventListener('click',function(){J=J.filter(function(x){return String(x.id)!==d.getAttribute('data-id')});saveJ()})});
    var w=0,l=0,p=0,net=0,risk=0,units=0,strong=[0,0],lean=[0,0],stakes=[];
    J.forEach(function(b){var pr=profit(b),st=parseFloat(b.stake)||0;if(b.result==='Win'){w++}else if(b.result==='Loss'){l++}else if(b.result==='Push'){p++}
      if(b.result!=='Pending'){net+=pr;risk+=st;if(unit()>0)units+=pr/unit();stakes.push(st)}
      if(b.result==='Win'||b.result==='Loss'){var t=(b.tier==='Strong')?strong:(b.tier==='Lean')?lean:null;if(t){t[0]+=b.result==='Win'?1:0;t[1]++}}});
    var avgPct=(stakes.length&&BR.bankroll)?(stakes.reduce(function(a,b){return a+b},0)/stakes.length/BR.bankroll*100):null;
    var el=$('#jsum');if(el)el.innerHTML=[['Record',w+'-'+l+'-'+p,'win-loss-push'],['Net',money2(net),risk?('ROI '+(net/risk*100).toFixed(1)+'%'):'settled bets'],
      ['Units',(unit()>0?(units>=0?'+':'')+units.toFixed(1)+'u':'&ndash;'),unit()>0?'at your unit size':'set a bankroll'],
      ['Avg stake',avgPct!=null?avgPct.toFixed(1)+'%':'&ndash;','of bankroll (target '+BR.unitPct+'%)'],
      ['Strong plays',strong[1]?strong[0]+'-'+(strong[1]-strong[0]):'&ndash;','bot Strong bets you took'],
      ['Lean plays',lean[1]?lean[0]+'-'+(lean[1]-lean[0]):'&ndash;','bot Lean bets you took']].map(function(x){return '<div><small>'+x[0]+'</small><strong class="'+(x[0]==='Net'?(net>0?'over':net<0?'under':''):'')+'">'+x[1]+'</strong><small>'+x[2]+'</small></div>'}).join('');
    compareToBot()}
  function addBet(b){b.id=Date.now();J.push(b);saveJ()}
  var jf=$('#jform');if(jf)jf.addEventListener('submit',function(e){e.preventDefault();var f=e.target;
    addBet({date:f.date.value,sport:f.sport.value,play:f.play.value,odds:f.odds.value,stake:f.stake.value,tier:f.tier.value,result:f.result.value,source:f.source.value,notes:f.notes.value});
    f.reset();f.date.value=D.date||'';f.source.value='';var st=$('#jstake');if(st&&unit()>0)st.value=Math.round(unit())});
  $$('.logbet').forEach(function(btn){btn.addEventListener('click',function(){var b=JSON.parse(btn.getAttribute('data-log'));var f=$('#jform');if(!f)return;
    f.date.value=b.date;f.sport.value=b.sport;f.play.value=b.play;f.odds.value=b.odds;f.tier.value=b.tier;f.source.value=b.source;f.result.value='Pending';
    f.stake.value=unit()>0?Math.round(unit()):'';location.hash='#journal';f.play.focus()})});
  function csvEscape(v){v=String(v==null?'':v);return /[",\n]/.test(v)?'"'+v.replace(/"/g,'""')+'"':v}
  var ex=$('#jexport');if(ex)ex.addEventListener('click',function(){var cols=['date','sport','play','odds','stake','tier','result','source','notes'];
    var csv=cols.join(',')+'\n'+J.map(function(b){return cols.map(function(c){return csvEscape(b[c])}).join(',')}).join('\n');
    var a=document.createElement('a');a.href=URL.createObjectURL(new Blob([csv],{type:'text/csv'}));a.download='yugi-journal.csv';document.body.appendChild(a);a.click();a.remove()});
  function parseCSV(t){var rows=[],row=[],cur='',q=false;for(var i=0;i<t.length;i++){var ch=t[i];
    if(q){if(ch==='"'){if(t[i+1]==='"'){cur+='"';i++}else q=false}else cur+=ch}
    else if(ch==='"')q=true;else if(ch===','){row.push(cur);cur=''}else if(ch==='\n'||ch==='\r'){if(cur!==''||row.length){row.push(cur);rows.push(row)}row=[];cur='';if(ch==='\r'&&t[i+1]==='\n')i++}else cur+=ch}
    if(cur!==''||row.length){row.push(cur);rows.push(row)}return rows}
  var im=$('#jimport');if(im)im.addEventListener('change',function(){var file=im.files[0];if(!file)return;var r=new FileReader();r.onload=function(){
    var rows=parseCSV(r.result);if(rows.length<2)return;var h=rows[0].map(function(x){return x.trim().toLowerCase()});
    function col(names){for(var i=0;i<names.length;i++){var k=h.indexOf(names[i]);if(k>=0)return k}return -1}
    var c={date:col(['date','placed','placed at']),sport:col(['sport','league']),play:col(['play','bet','selection','description','name']),odds:col(['odds','price','american odds']),
      stake:col(['stake','wager','risk','amount','amount wagered']),tier:col(['tier']),result:col(['result','outcome','status']),source:col(['source']),notes:col(['notes','note'])};
    var n=0;rows.slice(1).forEach(function(rw){if(!rw.length||rw.join('')==='')return;function g(k){return c[k]>=0?rw[c[k]]:''}var res=g('result').toLowerCase();
      res=/^w/.test(res)?'Win':/^l/.test(res)?'Loss':/^p/.test(res)?'Push':'Pending';
      J.push({id:Date.now()+n,date:g('date').slice(0,10),sport:g('sport')||'Other',play:g('play'),odds:g('odds'),stake:String(g('stake')).replace(/[^0-9.\-]/g,''),tier:g('tier')||'Custom',result:res,source:g('source'),notes:g('notes')});n++});
    saveJ();alert('Imported '+n+' bets.');im.value=''};r.readAsText(file)});
  var clr=$('#jclear');if(clr)clr.addEventListener('click',function(){if(confirm('Delete every journal entry on this device?')){J=[];saveJ()}});

  /* ---------- journal vs. bot comparison (reads history.csv from the site) ---------- */
  function compareToBot(){var el=$('#jcompare');if(!el)return;
    fetch((D.historyUrl||'history.csv'),{cache:'no-store'}).then(function(r){if(!r.ok)throw 0;return r.text()}).then(function(t){
      var rows=parseCSV(t);if(rows.length<2)throw 0;var h=rows[0];var H=rows.slice(1).map(function(rw){var o={};h.forEach(function(k,i){o[k]=rw[i]});return o});
      var cutoff=new Date(Date.now()-30*864e5).toISOString().slice(0,10);
      var given=H.filter(function(r){return r.pick&&r.date>=cutoff});var taken=J.filter(function(b){return b.source});
      var takenIds={};taken.forEach(function(b){takenIds[b.source]=true});
      var took=given.filter(function(r){return takenIds[r.league+':'+r.event_id]});
      var skipped=given.filter(function(r){return !takenIds[r.league+':'+r.event_id]&&(r.pick_result||r.result)});
      var sw=0,sl=0;skipped.forEach(function(r){var pr=r.pick_result||r.result;if(pr===r.pick)sw++;else if(pr&&pr!=='push')sl++});
      el.innerHTML='<b>Last 30 days:</b> the bot gave '+given.length+' Best Bets. You logged '+took.length+' of them'+(given.length?' ('+Math.round(took.length/given.length*100)+'%)':'')+'.'+
        (skipped.length?' The ones you skipped went '+sw+'-'+sl+'.':'')+(taken.length-took.length>0?' '+(taken.length-took.length)+' logged bot plays are older than 30 days.':'')}).
      catch(function(){el.textContent='Open this page from the website (not a saved file) to compare your journal with the bot\u2019s Best Bets.'})}

  /* ---------- live scores (ESPN, read directly by your browser) ---------- */
  var LV={timer:null,failed:0};
  function espnUrl(lg){return 'https://site.api.espn.com/apis/site/v2/sports/'+lg.sport+'/'+lg.league+'/scoreboard?dates='+(D.date||'').replace(/-/g,'')+(lg.groups?'&groups='+lg.groups:'')+'&limit=400'}
  function parseEvents(lg,data){return (data.events||[]).map(function(ev){var c=(ev.competitions||[])[0]||{};var st=((c.status||ev.status||{}).type)||{};
    function side(w){var t=(c.competitors||[]).filter(function(x){return x.homeAway===w})[0]||{};var tm=t.team||{};return {name:tm.displayName||tm.name||'',abbr:tm.abbreviation||'',score:t.score!=null?String(t.score):''}}
    var when=new Date(ev.date||c.date||0);return {league:lg.name,id:String(ev.id),home:side('home'),away:side('away'),state:st.state||'pre',detail:st.shortDetail||st.description||'',
      time:isNaN(when)?'':when.toLocaleTimeString([],{hour:'numeric',minute:'2-digit'}),ts:isNaN(when)?0:when.getTime()}})}
  function loadLive(){var lgs=D.leagues||[];if(!lgs.length)return;
    Promise.all(lgs.map(function(lg){return fetch(espnUrl(lg)).then(function(r){return r.json()}).then(function(d){return parseEvents(lg,d)}).catch(function(){return null})})).then(function(res){
      var ok=res.filter(function(x){return x!==null});var games=[].concat.apply([],ok);
      var t=$('#ticker'),lvw=$('#liveWrap'),stamp=$('#liveStamp');
      if(!ok.length){if(t)t.innerHTML='<span class="tick-msg">Live scores couldn\u2019t load in this browser. Tap the refresh button for the latest board.</span>';if(lvw)lvw.innerHTML='<p class="empty">Live scores couldn\u2019t load. This works on the website and in the home-screen app; it can\u2019t run from a saved file.</p>';return}
      var order={in:0,pre:1,post:2};games.sort(function(a,b){return (order[a.state]-order[b.state])||(a.ts-b.ts)});
      var live=games.filter(function(g){return g.state==='in'}).length;
      if(t){t.innerHTML=games.slice(0,40).map(function(g){var cls=g.state==='in'?'is-live':g.state==='post'?'is-final':'';
        var lbl=g.state==='in'?'<span class="live-dot"></span>'+esc(g.detail):g.state==='post'?'Final':esc(g.time);
        return '<a class="tick '+cls+'" href="#live"><span class="tk-lg"><span>'+esc(g.league)+'</span><span>'+lbl+'</span></span>'+
          '<span class="tk-row"><b>'+esc(g.away.abbr||g.away.name)+'</b><i>'+esc(g.state==='pre'?'':g.away.score)+'</i></span>'+
          '<span class="tk-row"><b>'+esc(g.home.abbr||g.home.name)+'</b><i>'+esc(g.state==='pre'?'':g.home.score)+'</i></span></a>'}).join('')||'<span class="tick-msg">No games today.</span>'}
      if(lvw){lvw.innerHTML=lgs.map(function(lg){var mine=games.filter(function(g){return g.league===lg.name});if(!mine.length)return '';
        return '<div class="card lv-group" data-league="'+esc(lg.name)+'"><h3>'+esc(lg.name)+' <span>'+mine.filter(function(g){return g.state==='in'}).length+' live, '+mine.length+' games</span></h3>'+
          mine.map(function(g){var a=parseFloat(g.away.score),h=parseFloat(g.home.score);var pre=g.state==='pre';
            return '<div class="lv '+(g.state==='in'?'is-live':'')+'"><div class="tm '+(!pre&&a>h?'win':'')+'"><b>'+esc(g.away.name)+'</b><span>'+(pre?'':esc(g.away.score))+'</span></div>'+
              '<div class="tm '+(!pre&&h>a?'win':'')+'"><b>'+esc(g.home.name)+'</b><span>'+(pre?'':esc(g.home.score))+'</span></div>'+
              '<div class="stt">'+(g.state==='in'?'<span class="live-dot"></span>'+esc(g.detail):g.state==='post'?'Final':esc(g.time))+'</div></div>'}).join('')+'</div>'}).join('')||'<p class="empty">No games today.</p>';
        var f=$('.chip[aria-pressed="true"]');if(f&&f.getAttribute('data-f')!=='all'){$$('#liveWrap [data-league]').forEach(function(el){el.hidden=el.getAttribute('data-league')!==f.getAttribute('data-f')})}}
      if(stamp)stamp.textContent='Updated '+new Date().toLocaleTimeString([],{hour:'numeric',minute:'2-digit',second:'2-digit'})+(live?' \u00b7 '+live+' live':'')})}
  function schedule(){clearInterval(LV.timer);LV.timer=setInterval(function(){if(document.visibilityState==='visible')loadLive()},60000)}
  var lb=$('#liveBtn');if(lb)lb.addEventListener('click',loadLive);
  document.addEventListener('visibilitychange',function(){if(document.visibilityState==='visible')loadLive()});

  /* ---------- arbitrage calculator ---------- */
  var af=$('#arbForm');if(af){af.addEventListener('input',calcArb);af.addEventListener('submit',function(e){e.preventDefault();calcArb()})}
  function calcArb(){var o=$('#arbOut');if(!o)return;var a=parseFloat($('#arbA').value),b=parseFloat($('#arbB').value),c=parseFloat($('#arbC').value),T=parseFloat($('#arbStake').value)||100;
    var legs=[a,b,c].filter(function(x){return !isNaN(x)&&x!==0});if(legs.length<2){o.innerHTML='Enter the price on each side.';return}
    var ps=legs.map(implied),sum=ps.reduce(function(x,y){return x+y},0);var dec=legs.map(function(p){return 1+payout(p)});
    var stakes=dec.map(function(d){return T/d/sum*1});var ret=stakes[0]*dec[0];var prof=ret-T;
    var names=['Side A','Side B','Side C'];
    o.innerHTML='Market total: <b>'+(sum*100).toFixed(2)+'%</b> '+(sum<1?'<span class="yes">(under 100%, this is an arbitrage)</span>':'<span class="no">(100% or more, no guaranteed profit)</span>')+'<br>'+
      stakes.map(function(s,i){return names[i]+' at '+(legs[i]>0?'+':'')+legs[i]+': stake <b>'+money2(s)+'</b> to return '+money2(s*dec[i])}).join('<br>')+
      '<br>Total staked '+money2(T)+', return '+money2(ret)+', profit <b class="'+(prof>=0?'yes':'no')+'">'+money2(prof)+' ('+(prof/T*100).toFixed(2)+'%)</b> whichever side wins.'}

  /* ---------- start ---------- */
  var saved=store('yugi.theme');if(saved)setTheme(saved);
  var jd=$('#jform');if(jd){jd.date.value=D.date||''}
  paintStakes();renderJournal();calcArb();loadLive();schedule();
})();
"""

ICON_PATHS = {
    "slate": '<rect x="3.5" y="5" width="17" height="15" rx="3"/><path d="M3.5 10h17M8 3v4M16 3v4"/>',
    "bets": '<circle cx="12" cy="12" r="8.5"/><circle cx="12" cy="12" r="4.5"/><circle cx="12" cy="12" r="1"/>',
    "rate": '<path d="M3.5 16.5l5-5 4 4 7.5-7.5"/><path d="M15 8h5v5"/>',
    "units": '<rect x="3" y="6.5" width="18" height="12" rx="3"/><path d="M3 10.5h18"/><circle cx="16.5" cy="14.5" r="1.2"/>',
    "home": '<path d="M4 11l8-6.5 8 6.5v8.5a1 1 0 0 1-1 1h-4.5v-6h-5v6H5a1 1 0 0 1-1-1z"/>',
    "board": '<rect x="4" y="4" width="16" height="16" rx="3"/><path d="M4 9.5h16M4 14.5h16M10 4v16"/>',
    "record": '<path d="M8 4h8v5a4 4 0 0 1-8 0zM8 6H5a3 3 0 0 0 3 4M16 6h3a3 3 0 0 1-3 4M12 13v4M8.5 20h7"/>',
    "refresh": '<path d="M19.5 12a7.5 7.5 0 1 1-2.2-5.3"/><path d="M19.5 4.5v4.5H15"/>',
    "live": '<circle cx="12" cy="12" r="2.5"/><path d="M7.5 7.5a6.4 6.4 0 0 0 0 9M16.5 7.5a6.4 6.4 0 0 1 0 9M4.5 4.5a10.6 10.6 0 0 0 0 15M19.5 4.5a10.6 10.6 0 0 1 0 15"/>',
    "journal": '<path d="M6 3.5h9l4 4v13H6z"/><path d="M15 3.5v4h4M9 12h7M9 16h7"/>',
    "arb": '<path d="M4 7h16M4 17h16"/><path d="M15 3.5l4 3.5-4 3.5M9 13.5L5 17l4 3.5"/>',
    "sun": '<circle cx="12" cy="12" r="4"/><path d="M12 2.5v2.5M12 19v2.5M2.5 12H5M19 12h2.5M5.3 5.3l1.8 1.8M16.9 16.9l1.8 1.8M5.3 18.7l1.8-1.8M16.9 7.1l1.8-1.8"/>',
    "props": '<circle cx="9" cy="7.5" r="3"/><path d="M3.5 19.5a5.5 5.5 0 0 1 11 0"/><path d="M16 5.5h5M16 9h5M16 12.5h3"/>',
    "moon": '<path d="M20 14.5A8.5 8.5 0 0 1 9.5 4a8.5 8.5 0 1 0 10.5 10.5z"/>',
}


def icon(name, size=22):
    return (f'<svg width="{size}" height="{size}" viewBox="0 0 24 24" fill="none" stroke="currentColor" '
            f'stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">'
            f'{ICON_PATHS[name]}</svg>')


LOGO = ('<svg width="30" height="30" viewBox="0 0 32 32" aria-hidden="true">'
        '<path d="M4 14 L16 4 L28 14 L23 14 L16 8.4 L9 14Z" fill="#34D399"/>'
        '<path d="M4 18 L16 28 L28 18 L23 18 L16 23.6 L9 18Z" fill="#F472B6"/></svg>')


def esc(text):
    return html.escape(str(text if text is not None else ""))


def ordinal(n):
    suffix = "th" if 10 <= n % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suffix}"


def f1(x):
    return "" if x is None else f"{x:.1f}"


def gap_text(gap):
    if gap is None:
        return "", ""
    gap = round(gap, 1)
    if abs(gap) < 0.05:
        return "Line matches it", ""
    return (f"Line {fmt_num(abs(gap))} {'above' if gap > 0 else 'below'}",
            "under" if gap > 0 else "over")


def side_label(side, line):
    arrow = "&#9650;" if side == "over" else "&#9660;"
    return f'{arrow} {side.capitalize()} {esc(fmt_num(line))}'


def strip_html(stats, line):
    totals = stats["totals"]
    values = list(totals) + [stats["mean"], stats["median"]] + ([line] if line is not None else [])
    lo, hi = min(values), max(values)
    pad = (hi - lo) * 0.06 or 1
    lo, hi = lo - pad, hi + pad

    def pos(v):
        return (v - lo) / (hi - lo) * 100

    parts, stack = [], {}
    for t in sorted(totals):
        slot = round(pos(t) / 1.6)
        level = min(stack.get(slot, 0), 5)
        stack[slot] = stack.get(slot, 0) + 1
        parts.append(f'<span class="st-game" style="left:{pos(t):.2f}%;bottom:{38 + level * 10}px"></span>')
    if line is not None:
        lp = pos(line)
        edge = " st-left" if lp < 10 else " st-right" if lp > 90 else ""
        parts.append(f'<span class="st-line{edge}" style="left:{lp:.2f}%"><em>Line {esc(fmt_num(line))}</em></span>')
    parts.append(f'<span class="st-median" style="left:{pos(stats["median"]):.2f}%"></span>')
    parts.append(f'<span class="st-mean" style="left:{pos(stats["mean"]):.2f}%"></span>')
    parts.append(f'<span class="st-lo">{esc(fmt_num(min(totals)))}</span>'
                 f'<span class="st-hi">{esc(fmt_num(max(totals)))}</span>')
    label = (f"Past totals from {fmt_num(min(totals))} to {fmt_num(max(totals))}; mean {fmt_num(stats['mean'])}, "
             f"median {fmt_num(stats['median'])}" + (f"; line {fmt_num(line)}" if line is not None else ""))
    return f'<div class="strip" role="img" aria-label="{esc(label)}"><span class="st-axis"></span>{"".join(parts)}</div>'


def starter_text(league, side):
    st = side.get("starter")
    if league == "MLB":
        if not st:
            return "Starter", "Not announced"
        bits = [st["name"]]
        if st.get("era") is not None:
            bits.append(f"{st['era']:.2f} ERA")
        if st.get("whip") is not None:
            bits.append(f"{st['whip']:.2f} WHIP")
        return "Starter", ", ".join(bits)
    if league == "NHL":
        if not st:
            return "Goalie", "Not announced"
        bits = [st["name"]]
        if st.get("svpct") is not None:
            bits.append(f"{st['svpct']:.3f}".lstrip("0") + " SV%")
        if st.get("gaa") is not None:
            bits.append(f"{st['gaa']:.2f} GAA")
        if st.get("saves_pg") is not None:
            bits.append(f"{st['saves_pg']:.1f} saves/gm")
        return "Goalie", ", ".join(bits)
    if league in ("NFL", "NCAAF"):
        qb = side.get("passer")
        if not qb:
            return "QB", "Not listed"
        return "QB", qb["name"] + (f", {qb['ypg']:.0f} pass yds/gm" if qb.get("ypg") else "")
    return None


def render_factors(g):
    league = g["league"]
    unit = LEAGUES[league]["unit"]
    blocks = []
    for where in ("away", "home"):
        side = g["sides"][where]
        rows = []
        st = starter_text(league, side)
        if st:
            rows.append(st)
        s = side.get("split")
        venue_word = {"home": "at home", "away": "on road", "season": "season"}
        if s:
            off, used = venue_rate(s, where, "ppg")
            dfn, used2 = venue_rate(s, where, "papg")
            rows.append(("Scores", f"{f1(off)} {unit}/gm {venue_word[used]}"))
            rows.append(("Allows", f"{f1(dfn)} {unit}/gm {venue_word[used2]}"))
            if s.get("recent_n"):
                rows.append((f"Last {s['recent_n']}",
                             f"{f1(s['recent_ppg'])} scored, {f1(s['recent_papg'])} allowed"))
        else:
            rows.append(("Scoring", "Not enough games yet"))
        rest = side.get("rest")
        if league != "MLB" and rest is not None and 0 < rest < 30:
            rows.append(("Rest", "Back-to-back" if rest == 1 else f"{rest} days"))
        rank = side.get("rank")
        rows.append(("Defense rank", f"{ordinal(rank['rank'])} of {rank['of']}" if rank else "&ndash;"))
        body = "".join(f'<div class="frow"><span>{label}</span><span>{value if value == "&ndash;" else esc(value)}'
                       f'</span></div>' for label, value in rows)
        blocks.append(f'<div class="team-f"><h5>{esc(side["name"])} <span>{"away" if where == "away" else "home"}'
                      f'</span></h5>{body}</div>')
    if g.get("env"):
        blocks.append(f'<div class="team-f"><div class="frow"><span>Conditions</span>'
                      f'<span>{esc(g["env"])}</span></div></div>')
    line = g["odds"]["line"] if g["odds"] else None
    if g["proj"]:
        text, cls = gap_text(line - g["proj"]["total"]) if line is not None else ("No line to compare", "")
        proj = (f'<div class="proj"><span class="label">Projected total</span><span><span class="v">'
                f'{f1(g["proj"]["total"])}</span><small class="{cls}">{esc(text)}</small></span></div>')
    else:
        need = LEAGUES[league]["min_games"]
        proj = f'<p class="note">Projection needs {need}+ games this season from both teams.</p>'
    return ('<div class="box"><div class="box-head"><span class="label">Matchup edge</span>'
            '<span>This season</span></div>' + "".join(blocks) + proj + '</div>')


def render_h2h(g):
    stats = g["stats"]
    line = g["odds"]["line"] if g["odds"] else None
    head = ('<div class="box-head"><span class="label">H2H trends</span>'
            f'<span>{"Last " + str(stats["n"]) + " meetings" if stats else "Past meetings"}</span></div>')
    if not stats:
        return f'<div class="box">{head}<p class="note">{esc(g["note"])}</p></div>'
    pair = []
    for label, key, gkey in (("Mean", "mean", "gap_mean"), ("Median", "median", "gap_median")):
        text, cls = gap_text(stats[gkey])
        pair.append(f'<div class="stat"><span class="label">{label}</span><span class="v">'
                    f'{esc(fmt_num(stats[key]))}</span><small class="{cls}">{esc(text)}</small></div>')
    rows = "".join(
        f'<tr><td>{esc(m["date"])}</td><td>{esc(m["away"])} {esc(fmt_num(m["away_score"]))}</td>'
        f'<td>{esc(m["home"])} {esc(fmt_num(m["home_score"]))}</td><td class="n">{esc(fmt_num(m["total"]))}</td></tr>'
        for m in g["meetings"])
    meetings = (f'<details><summary>Show all {len(g["meetings"])} scores</summary><div class="wrap"><table>'
                '<thead><tr><th>Date</th><th>Away</th><th>Home</th><th class="n">Total</th></tr></thead>'
                f'<tbody>{rows}</tbody></table></div></details>')
    return f'<div class="box">{head}<div class="pair">{"".join(pair)}</div>{strip_html(stats, line)}{meetings}</div>'


def pct(w, n):
    return f"{w / n:.0%}" if n else "&ndash;"


def render_game(g, unit):
    odds, pick, locked = g["odds"], g["pick"], g.get("locked")
    when = g["time"]
    if g["state"] == "post":
        when = f"Final, {fmt_num(g['final_total'])} {unit}" if g["final_total"] is not None else "Final"
    elif g["state"] == "in":
        when = g["status"] or "Live"
    if locked:
        badge = (f'<span class="badge {locked["side"]}">{side_label(locked["side"], locked["line"])} '
                 f'&middot; {esc(locked["tier"])}</span>')
    elif pick:
        badge = f'<span class="badge {pick["side"]}">{side_label(pick["side"], odds["line"])} &middot; {pick["tier"]}</span>'
    elif odds and g["proj"] and g["stats"]:
        badge = '<span class="badge pass">No bet</span>'
    else:
        badge = ""
    if odds:
        pills = "".join(f'<span class="pill">{s}&nbsp;{esc(odds[k])}</span>'
                        for s, k in (("O", "over"), ("U", "under")) if odds.get(k))
        probs = ""
        if g.get("probs"):
            pr = g["probs"]
            probs = (f'<div class="probs">Model: <b class="over">Over {pr["over"]:.0%}</b>, '
                     f'<b class="under">Under {pr["under"]:.0%}</b>. Book implies '
                     f'{implied_prob(odds.get("over")):.0%} / {implied_prob(odds.get("under")):.0%}.</div>')
        extra = ""
        if g.get("steam"):
            extra += f'<div class="steam">{esc(g["steam"]["text"])}</div>'
        if g.get("alt"):
            a = g["alt"]
            extra += (f'<div class="alt">Safer number: {esc(a["side"].capitalize())} '
                      f'{esc(fmt_num(a["line"]))} at {esc(a["price"])} ({esc(a["book"])}), '
                      f'model {a["prob"]:.0%} vs. book {a["implied"]:.0%}</div>')
        linebox = (f'<div class="linebox"><div><span class="label">Total</span><div class="num">'
                   f'{esc(fmt_num(odds["line"]))}</div></div><div class="pills">{pills}</div>'
                   f'<div class="book">{esc(odds["book"])}</div>{move_html(g)}{probs}{extra}</div>')
    else:
        linebox = ('<div class="linebox"><div><span class="label">Total</span><div class="num">&ndash;</div></div>'
                   '<div class="book">Line not posted yet</div></div>')
    return (f'<article class="card game" id="g{esc(g["id"])}"><div class="game-top">'
            f'<span class="when">{esc(when)}</span>{badge}</div><div class="teams">{esc(g["away"])}'
            f'<span class="at">@</span>{esc(g["home"])}</div>{linebox}'
            f'<div class="split">{render_h2h(g)}{render_factors(g)}</div></article>')


def line_move(g):
    first, odds = g.get("first_line"), g.get("odds")
    if first is None or not odds or abs(odds["line"] - first) < 0.25:
        return None
    return odds["line"] - first


def move_html(g):
    move = line_move(g)
    if move is None:
        return ""
    word = "up" if move > 0 else "down"
    return (f'<div class="move">Line moved {word} {esc(fmt_num(abs(move)))} today, from '
            f'{esc(fmt_num(g["first_line"]))} to {esc(fmt_num(g["odds"]["line"]))}</div>')


def play_of(g):
    """The play to show: the locked one from history if there is one, else today's fresh pick."""
    lk = g.get("locked")
    if lk:
        return lk
    pk = g.get("pick")
    if pk:
        return {"side": pk["side"], "tier": pk["tier"], "price": pk.get("price") or "-110",
                "line": g["odds"]["line"], "time": "", "prob": pk.get("prob"), "edge": pk.get("edge_prob"),
                "still": True, "result": ""}
    return None


def bet_row(g, day):
    pl, odds, stats, proj = play_of(g), g["odds"], g["stats"], g["proj"]
    cur = odds["line"] if odds else None
    status = []
    if pl["result"]:
        word = {"over": "Over", "under": "Under", "push": "Push"}.get(pl["result"], pl["result"])
        if pl["result"] == "push":
            status.append('<span class="st">Final: push.</span>')
        else:
            won = pl["result"] == pl["side"]
            status.append(f'<span class="st {"won" if won else "lost"}">Final: {esc(fmt_num(g["final_total"]))} '
                          f'went {word}. {"Won" if won else "Lost"}.</span>')
    elif g["state"] == "in":
        status.append('<span class="st">In progress.</span>')
    elif cur is not None and abs(cur - (pl["line"] or cur)) >= 0.25:
        status.append(f'<span class="st {"ok" if pl["still"] else "warn"}">Line is now {esc(fmt_num(cur))}. '
                      + ("Still qualifies." if pl["still"] else "Wouldn\u2019t qualify at this number, but the play stands.")
                      + '</span>')
    elif not pl["still"] and g["state"] == "pre":
        status.append('<span class="st warn">No longer meets every rule after the latest update. The play stands.</span>')
    move = line_move(g)
    if move is not None and not pl["result"]:
        with_pick = (move > 0) == (pl["side"] == "over")
        status.append(f'<span class="st mv">Market moved {"with" if with_pick else "against"} this pick today '
                      f'({esc(fmt_num(g["first_line"]))} to {esc(fmt_num(cur))}).</span>')
    if g.get("alt") and not pl["result"]:
        a = g["alt"]
        status.append(f'<span class="st ok">Alternate: {esc(a["side"].capitalize())} '
                      f'{esc(fmt_num(a["line"]))} at {esc(a["price"])} ({esc(a["book"])}) clears more key '
                      f'numbers, model {a["prob"]:.0%} vs. book {a["implied"]:.0%}.</span>')
    if g.get("steam"):
        status.append(f'<span class="st warn">{esc(g["steam"]["text"])}; the move is toward the '
                      f'{esc(g["steam"]["side"])}.</span>')
    locked_at = f' Locked {esc(pl["time"])}.' if pl["time"] else ""
    edge = (f' Model {pl["prob"]:.0%} vs. book {implied_prob(pl["price"]):.0%}, edge '
            f'{"+" if (pl["edge"] or 0) >= 0 else ""}{(pl["edge"] or 0):.1%}.') if pl.get("prob") else ""
    play_text = f'{pl["side"].capitalize()} {fmt_num(pl["line"])} ({pl["price"]})'
    log = json.dumps({"date": day.isoformat(), "sport": g["league"], "play": f'{g["away"]} @ {g["home"]}: {play_text}',
                      "odds": pl["price"], "tier": pl["tier"], "source": f'{g["league"]}:{g["id"]}'})
    actions = "" if pl["result"] or g["state"] != "pre" else (
        f'<div class="bet-actions"><span class="stake" data-units="1"></span>'
        f'<button class="btn logbet" type="button" data-log=\'{esc(log)}\'>Log this bet</button></div>')
    return (f'<div class="bet"><div class="side {pl["side"]}">{side_label(pl["side"], pl["line"])}'
            f'<small>{esc(pl["price"])}, {esc(odds["book"] if odds else "ESPN")}{locked_at}</small></div>'
            f'<div class="why"><b>{esc(g["away"])} @ {esc(g["home"])}</b>, {esc(g["time"])}<br>'
            f'H2H mean {esc(fmt_num(stats["mean"]))}, median {esc(fmt_num(stats["median"]))}. '
            f'Projected {f1(proj["total"]) if proj else "&ndash;"}.{edge}{"".join(status)}{actions}</div>'
            f'<span class="tier {pl["tier"]}">{pl["tier"]}</span></div>')


def render_team_totals(board):
    rows = board.get("team_totals") or []
    if not rows:
        return ""
    by_league = {}
    for t in rows:
        by_league.setdefault(t["league"], []).append(t)
    parts = []
    for league, group in by_league.items():
        body = []
        for t in group:
            body.append(
                f'<div class="bet"><div class="side {t["side"]}">{side_label(t["side"], t["line"])}'
                f'<small>{esc(t["team"])} &middot; {esc(t["price"])}, {esc(t["book"])}</small></div>'
                f'<div class="why"><b>{esc(t["game"])}</b>, {esc(t["time"])}<br>'
                f'Projected {f1(t["expect"])} for {esc(t["team"])}. Model {t["prob"]:.0%} against a book '
                f'price of {t["implied"]:.0%}.</div>'
                f'<div class="edge"><b>+{t["edge"]:.1%}</b><small>edge</small></div></div>')
        parts.append(f'<div class="card bet-group" data-league="{esc(league)}">'
                     f'<h3>{esc(league)} team totals <span>{len(group)} '
                     f'play{"s" if len(group) != 1 else ""}</span></h3>{"".join(body)}</div>')
    return "".join(parts)


def render_ufc(board):
    data = board.get("ufc") or {}
    plays, fights = data.get("plays") or [], data.get("fights") or []
    if not fights and not plays:
        note = esc(data.get("note") or "No UFC card today.")
        return (f'<div class="card bet-group" data-league="UFC"><h3>UFC <span>no card</span></h3>'
                f'<p class="empty">{note}</p></div>')
    if not plays:
        reasons = [f for f in fights if f.get("why")][:3]
        detail = "".join(f'<div class="why" style="padding:6px 0">{esc(f["a"]["name"])} vs. '
                         f'{esc(f["b"]["name"])}: {esc(f["why"])}</div>' for f in reasons)
        return (f'<div class="card bet-group" data-league="UFC"><h3>UFC <span>{len(fights)} fights, '
                f'no plays</span></h3><p class="empty">No fight passed the test today.</p>{detail}</div>')
    body = []
    for f in plays:
        a, b = f["rates"]
        line = (f'Rounds total {fmt_num(f["round_line"])}. ' if f["round_line"] is not None else "")
        mp = f["max_price"]
        verdict = (f'<span class="st ok">Playable at the {esc(UFC_ASSUMED_PRICE)} ceiling.</span>'
                   if f["ceiling_ok"] else
                   f'<span class="st warn">Not worth {esc(UFC_ASSUMED_PRICE)}: that price needs '
                   f'{implied_prob(UFC_ASSUMED_PRICE):.0%} and the model says {f["prob"]:.0%}.</span>')
        body.append(
            f'<div class="bet"><div class="side over">Not to go the distance'
            f'<small>Ends inside {f["distance"]} rounds &middot; take {mp:+d} or better</small></div>'
            f'<div class="why"><b>{esc(f["a"]["name"])} vs. {esc(f["b"]["name"])}</b>, {esc(f["time"])}<br>'
            f'{esc(line)}{esc(f["a"]["name"])} finishes {a["rate"]:.0%} of {a["fights"]} fights, '
            f'{esc(f["b"]["name"])} {b["rate"]:.0%} of {b["fights"]}. '
            f'Model {f["prob"]:.0%} it ends early, so anything shorter than {mp:+d} is an overpay.'
            f'{verdict}'
            f'<span class="st">Price the fight-ends-inside-the-distance market at your book.</span></div>'
            f'<div class="edge"><b>{mp:+d}</b><small>max price</small></div></div>')
    return (f'<div class="card bet-group" data-league="UFC"><h3>UFC <span>{len(plays)} '
            f'play{"s" if len(plays) != 1 else ""}</span></h3>{"".join(body)}</div>')


def render_bets(board):
    day = board["date"]
    plays = [g for e in board["leagues"] for g in e["games"] if play_of(g)]
    parts = []
    open_plays = [g for g in plays if g["state"] == "pre" and not play_of(g)["result"]]
    if open_plays:
        top = max(open_plays, key=lambda g: (play_of(g)["tier"] == "Strong", play_of(g).get("edge") or 0))
        pl = play_of(top)
        parts.append(f'<div class="card top-play" data-league="{top["league"]}"><span class="label">Top play</span>'
                     f'<div class="side {pl["side"]}">{side_label(pl["side"], pl["line"])}</div>'
                     f'<p>{esc(top["away"])} @ {esc(top["home"])}, {esc(top["league"])}, {esc(top["time"])}. '
                     + (f'Model {pl["prob"]:.0%} against a book price of {implied_prob(pl["price"]):.0%}. '
                        if pl.get("prob") else "")
                     + 'The H2H trend and the projection agree.</p></div>')
    for e in board["leagues"]:
        mine = [g for g in e["games"] if play_of(g)]
        count = f'{len(mine)} play{"s" if len(mine) != 1 else ""}' if mine else ""
        body = []
        if e["error"]:
            body.append(f'<p class="error">{esc(e["error"])}</p>')
        elif not e["games"] and e.get("skipped"):
            body.append(f'<p class="empty">No {e["name"]} totals posted yet.</p>')
        elif not e["games"]:
            body.append(f'<p class="empty">No {e["name"]} games today.</p>')
        elif not mine:
            which = ("Today\u2019s only game didn\u2019t" if len(e["games"]) == 1
                     else f"None of today\u2019s {len(e['games'])} games")
            body.append(f'<p class="empty">No Best Bets on the {e["name"]} slate. {which} pass every rule'
                        + (" (this league needs a Strong grade)" if e["name"] in ONLY_STRONG else "") + '.</p>')
        else:
            mine.sort(key=lambda g: (bool(play_of(g)["result"]), play_of(g)["tier"] != "Strong",
                                     -(play_of(g).get("edge") or 0)))
            body.extend(bet_row(g, day) for g in mine)
        parts.append(f'<div class="card bet-group" data-league="{e["name"]}"><h3>{e["name"]} <span>{count}</span></h3>'
                     + "".join(body) + '</div>')
    return "".join(parts) + render_team_totals(board) + render_ufc(board)


def render_board(board):
    parts = []
    for e in board["leagues"]:
        n = len(e["games"])
        head = (f'<div class="league-title"><h3>{e["name"]}</h3>'
                f'<span>{str(n) + " game" + ("s" if n != 1 else "") if n else ""}</span></div>')
        if e["error"]:
            body = f'<p class="error">{esc(e["error"])} Check your connection and run it again.</p>'
        elif not n and e.get("skipped"):
            body = (f'<p class="empty">{e["skipped"]} {e["name"]} game{"s" if e["skipped"] != 1 else ""} today, '
                    'but none has a posted total yet. Check back after the evening update.</p>')
        elif not n:
            body = f'<p class="empty">No {e["name"]} games today.</p>'
        else:
            body = ""
            if e["prior_season"]:
                body += ('<p class="note">This season hasn\u2019t started yet for these teams, so matchup numbers '
                         'use last season.</p>')
            if e.get("skipped"):
                body += (f'<p class="note">{e["skipped"]} more {e["name"]} game{"s" if e["skipped"] != 1 else ""} '
                         'left off because no sportsbook has posted a total yet.</p>')
            body += "".join(render_game(g, e["unit"]) for g in e["games"])
        parts.append(f'<div class="league-block" data-league="{e["name"]}">{head}{body}</div>')
    if UFC_ON:
        fights = (board.get("ufc") or {}).get("fights") or []
        detail = (f'{len(fights)} fight{"s" if len(fights) != 1 else ""} on the card. '
                  'Fights are listed under Best Bets.' if fights else 'No UFC card today.')
        parts.append('<div class="league-block" data-league="UFC"><div class="league-title"><h3>UFC</h3>'
                     f'</div><p class="empty">{esc(detail)}</p></div>')
    return "".join(parts)


def render_record(record):
    all_ = record.get("All")
    if not all_ or not all_["bets"]:
        graded = all_["graded"] if all_ else 0
        return ('<div class="record"><div class="card rec-card wide"><h3>Bot record</h3>'
                '<p class="empty">Best Bets get graded the morning after they\u2019re played. '
                f'{"No graded games yet." if not graded else str(graded) + " games graded so far, none were Best Bets."}'
                '</p></div></div>')
    decided = all_["wins"] + all_["losses"]
    win_share = all_["wins"] / decided if decided else 0
    circ = 2 * 3.14159 * 70
    donut = (f'<svg class="donut" viewBox="0 0 180 180" role="img" aria-label="{all_["wins"]} wins, '
             f'{all_["losses"]} losses"><circle cx="90" cy="90" r="70" fill="none" stroke="#FB7185" '
             f'stroke-width="20"/><circle cx="90" cy="90" r="70" fill="none" stroke="#34D399" stroke-width="20" '
             f'stroke-dasharray="{circ * win_share:.1f} {circ:.1f}" transform="rotate(-90 90 90)"/>'
             f'<text x="90" y="92" text-anchor="middle" fill="currentColor" font-size="30" font-weight="600" '
             f'font-family="Rubik,system-ui,sans-serif">{win_share:.0%}</text><text x="90" y="116" '
             f'text-anchor="middle" fill="#8E9AB3" font-size="12" font-family="Rubik,system-ui,sans-serif">'
             f'hit rate</text></svg>')
    donut_card = (f'<div class="card rec-card"><h3>Bot record</h3><div class="donut-wrap">{donut}'
                  f'<div class="donut-legend"><div><span class="label over">Wins</span><strong>{all_["wins"]}</strong>'
                  f'</div><div><span class="label under">Losses</span><strong>{all_["losses"]}</strong>'
                  f'<small>{all_["pushes"]} push{"es" if all_["pushes"] != 1 else ""}</small></div>'
                  f'<div><span class="label">Units</span><strong class="{"over" if all_["units"] >= 0 else "under"}">'
                  f'{all_["units"]:+.1f}u</strong><small>1 unit per bet at the locked price</small></div></div></div></div>')
    bars = []
    for name in LEAGUES:
        s = record.get(name)
        if not s or not s["bets"]:
            continue
        d = s["wins"] + s["losses"]
        share = s["wins"] / d if d else 0
        bars.append(f'<div class="bar-row"><span>{name}</span><div class="bar"><i style="width:{share * 100:.0f}%">'
                    f'</i><b style="left:52.4%"></b></div><strong>{pct(s["wins"], d)}</strong></div>')
    bars_card = (f'<div class="card rec-card"><h3>Hit rate by sport</h3>{"".join(bars)}'
                 f'<div class="bar-foot"><span>Overall, {all_["wins"]}-{all_["losses"]}-{all_["pushes"]}</span>'
                 f'<strong>{pct(all_["wins"], decided)}</strong></div><p class="rec-note">The gold tick marks 52.4%, '
                 'the break-even rate at standard &minus;110 pricing.</p></div>')
    rows = []
    for name in list(LEAGUES) + ["All"]:
        s = record.get(name)
        if not s:
            continue
        d = s["wins"] + s["losses"]
        rows.append(f'<tr><td>{"All sports" if name == "All" else name}</td><td class="n">{s["graded"]}</td>'
                    f'<td class="n">{s["over"]}-{s["under"]}</td><td class="n">{pct(s["trend_w"], s["trend_n"])}'
                    f' <small>({s["trend_n"]})</small></td><td class="n">{pct(s["wins"], d)} <small>({d})</small></td>'
                    f'<td class="n">{pct(s["strong_w"], s["strong_n"])} <small>({s["strong_n"]})</small></td>'
                    f'<td class="n {"over" if s["units"] >= 0 else "under"}">{s["units"]:+.1f}u</td></tr>')
    table = ('<div class="card rec-card wide"><h3>Does the edge hold up?</h3><div class="wrap"><table><thead><tr>'
             '<th>Sport</th><th class="n">Graded</th><th class="n">Overs-Unders</th><th class="n">H2H trend alone</th>'
             '<th class="n">Best Bets</th><th class="n">Strong only</th><th class="n">Units</th></tr></thead><tbody>'
             + "".join(rows) + '</tbody></table></div><p class="rec-note">If Best Bets don\u2019t beat the H2H trend alone '
             'over a few hundred plays, the extra factors aren\u2019t adding an edge. Small samples swing a lot, so give '
             'it time before trusting any number here.</p></div>')
    return f'<div class="record">{donut_card}{bars_card}{table}</div>'


def render_journal(board, record):
    sports = "".join(f'<option>{e["name"]}</option>' for e in board["leagues"]) + \
             "".join(f"<option>{x}</option>" for x in ("UFC", "Props", "Parlay", "Other"))
    return (
        '<div class="card rec-card"><h3>Bankroll and unit size</h3>'
        '<form id="bankForm" class="form"><label>Bankroll ($)<input id="bankroll" type="number" min="0" step="1" '
        'placeholder="e.g. 2000"></label><label>Unit (% of bankroll)<input id="unitPct" type="number" min="0.1" '
        'max="100" step="0.1"></label><div class="form-actions"><button class="btn primary" type="submit">Save</button>'
        '<span id="unitOut" class="stake"></span></div></form>'
        '<p class="rec-note">Every Best Bet shows a stake at this unit size. 2.5% means a cold streak of ten losses '
        'costs a quarter of the bankroll, not all of it. Saved on this device only.</p></div>'
        '<div class="card rec-card" style="margin-top:12px"><h3>Your journal</h3><div id="jsum" class="jsum"></div>'
        '<p id="jcompare" class="rec-note"></p>'
        '<div class="wrap"><table><thead><tr><th>Date</th><th>Sport</th><th>Play</th><th class="n">Odds</th>'
        '<th class="n">Stake</th><th>Result</th><th class="n">P/L</th><th></th></tr></thead>'
        '<tbody id="jbody"></tbody></table></div>'
        '<h3 style="margin-top:18px">Add a bet</h3>'
        f'<form id="jform" class="form"><label>Date<input name="date" type="date" required></label>'
        f'<label>Sport<select name="sport">{sports}</select></label>'
        '<label class="wide2">Play<input name="play" placeholder="e.g. Jaguars @ Texans Under 41.5" required></label>'
        '<label>Odds (American)<input name="odds" placeholder="-110" required></label>'
        '<label>Stake ($)<input id="jstake" name="stake" type="number" min="0" step="0.01" required></label>'
        '<label>Tier<select name="tier"><option>Custom</option><option>Strong</option><option>Lean</option></select></label>'
        '<label>Result<select name="result"><option>Pending</option><option>Win</option><option>Loss</option>'
        '<option>Push</option></select></label>'
        '<label class="wide2">Notes<input name="notes" placeholder="optional"></label>'
        '<input type="hidden" name="source">'
        '<div class="form-actions"><button class="btn primary" type="submit">Add to journal</button>'
        '<button class="btn" type="button" id="jexport">Export CSV</button>'
        '<label class="btn" style="display:inline-block">Import CSV<input id="jimport" type="file" accept=".csv,text/csv" '
        'style="display:none"></label><button class="btn danger" type="button" id="jclear">Clear journal</button></div></form>'
        '<p class="rec-note">Entries stay in this browser. Export a CSV now and then as a backup, or to move them to '
        'another device. Imports also accept CSVs with date, sport, play, odds, stake and result columns.</p></div>'
        f'<div class="section-head" style="margin-top:26px"><h2>Bot record</h2><span>Graded the next morning</span></div>'
        + render_record(record))


def render_live(board):
    return ('<div class="live-head"><span>Scores come straight from ESPN to your browser and refresh every minute '
            'while this page is open. <span id="liveStamp"></span></span>'
            '<button class="btn" type="button" id="liveBtn">Refresh now</button></div>'
            '<div id="liveWrap"><p class="empty">Loading live scores\u2026</p></div>')


def render_props(board):
    props = board.get("props") or []
    if not props:
        if not (ODDS_API_KEY or SGO_API_KEY):
            return ('<div class="card bet-group"><p class="empty">Player props need an odds key. Add '
                    '<b>ODDS_API_KEY</b> or <b>SGO_API_KEY</b> in your repository secrets and the next run '
                    'will fill this tab.</p></div>')
        return ('<div class="card bet-group"><p class="empty">No props cleared the '
                f'{MIN_PROP_EDGE:.0%} edge test today. That is normal on a light slate, and it is the '
                'filter doing its job.</p></div>')
    by_league = {}
    for pr in props:
        by_league.setdefault(pr["league"], []).append(pr)
    parts = []
    for league, rows in by_league.items():
        body = []
        for pr in rows:
            link = (f' <a href="{esc(pr["link"])}" target="_blank" rel="noopener">open</a>'
                    if pr.get("link") else "")
            hits = "".join(f'<i>{label} {v:.0%}</i>' for label, v in
                           (("L5", pr["last5"]), ("L10", pr["recent"]), ("season", pr["full"])) if v is not None)
            body.append(
                f'<div class="prop"><div class="pname">{esc(pr["player"])} '
                f'{esc(pr["side"])} {esc(fmt_num(pr["line"]))} {esc(pr["label"])}'
                f'<small>{esc(pr["price"])} at {esc(pr["book"])}{link}</small></div>'
                f'<div class="pwhy"><b>{esc(pr["game"])}</b>, {esc(pr["time"])}<br>'
                f'Cleared it in {pr["full"]:.0%} of {pr["n"]} games, averaging {pr["avg"]:.1f}. '
                f'Model {pr["prob"]:.0%} against a book price of {pr["implied"]:.0%}.'
                f'<span class="hits">{hits}</span></div>'
                f'<div class="edge"><b>+{pr["edge"]:.1%}</b><small>edge</small></div></div>')
        parts.append(f'<div class="card pgroup"><h3>{esc(league)} <span>{len(rows)} '
                     f'play{"s" if len(rows) != 1 else ""}</span></h3>{"".join(body)}</div>')
    return "".join(parts)


def render_arb_list(board):
    arbs = board.get("arbs") or []
    if not arbs:
        return ('<p class="empty">No arbitrage found in today\u2019s totals, moneylines or spreads. '
                'These appear and vanish within minutes, so an empty list is the normal result.</p>')
    rows = []
    for a in arbs:
        legs = "<br>".join(
            f'{esc(l["side"])} at <b>{esc(l["book"])}</b> {esc(l["price"])}'
            + (f' <a href="{esc(l["link"])}" target="_blank" rel="noopener">open</a>' if l.get("link") else "")
            for l in a["legs"])
        rows.append(f'<div class="arb"><div><b>{esc(a["game"])}</b><div class="legs">{esc(a["what"])}<br>{legs}</div></div>'
                    f'<div class="edge"><b>{a["profit"]:.2%}</b><small>locked profit</small></div></div>')
    return f'<div class="card pgroup">{"".join(rows)}</div>'


def render_arb():
    return ('<div class="card rec-card"><h3>Calculator</h3>'
            '<p class="rec-note" style="margin:0 0 12px">Enter the best price on each side of the same market from '
            'different sportsbooks. If the market total comes in under 100%, the stakes below lock in the same profit '
            'no matter who wins. Prices move fast, so place both sides quickly and watch for limits.</p>'
            '<form id="arbForm" class="form"><label>Side A odds<input id="arbA" placeholder="-130" required></label>'
            '<label>Side B odds<input id="arbB" placeholder="+140" required></label>'
            '<label>Side C odds (3-way, optional)<input id="arbC" placeholder="e.g. draw +260"></label>'
            '<label>Total stake ($)<input id="arbStake" type="number" min="1" step="1" value="200"></label></form>'
            '<div id="arbOut" class="arb-out"></div>'
            '<p class="rec-note">Scanning every book automatically needs a multi-book odds feed; see the setup notes.</p>'
            '</div>')


def render_page(board, record, asset_prefix=""):
    day = board["date"]
    long_date = f"{day:%A}, {day:%B} {day.day}, {day.year}"
    short_date = f"{day:%a}, {day:%b} {day.day}"
    games = [g for e in board["leagues"] for g in e["games"]]
    playing = [e["name"] for e in board["leagues"] if e["games"]]
    plays = [g for g in games if play_of(g)]
    strong = sum(1 for g in plays if play_of(g)["tier"] == "Strong")
    extras = len(board.get("team_totals") or []) + len((board.get("ufc") or {}).get("plays") or [])
    all_ = record.get("All") or _blank_record()
    decided = all_["wins"] + all_["losses"]

    tiles = [
        ("slate", "On the slate", str(len(games)),
         f"games across {', '.join(playing)}" if playing else "No games today", bool(playing)),
        ("bets", "Best Bets", str(len(plays) + extras),
         (f"{strong} strong, {len(plays) - strong} lean"
          + (f", {extras} team/UFC" if extras else "")) if plays or extras else "No plays today",
         bool(plays or extras)),
        ("props", "Prop edges", str(len(board.get("props") or [])),
         f"{MIN_PROP_EDGE:.0%}+ edge, all sports" if board.get("props") else
         ("needs an odds key" if not (ODDS_API_KEY or SGO_API_KEY) else "none cleared today"),
         bool(board.get("props"))),
        ("rate", "Hit rate", pct(all_["wins"], decided) if decided else "&ndash;",
         f"{all_['wins']} of {decided} graded" if decided else "Grading starts tomorrow", bool(decided)),
        ("units", "Units", f"{all_['units']:+.1f}u" if all_["bets"] else "&ndash;",
         "All time at locked prices" if all_["bets"] else "Tracked per Best Bet", False),
    ]
    tile_html = "".join(
        f'<div class="card tile"><span class="icon">{icon(ic)}</span><div><span class="label">{label}</span>'
        f'<strong>{value}</strong><small class="{"" if green else "flat"}">{esc(sub)}</small></div></div>'
        for ic, label, value, sub, green in tiles)
    chip_names = [e["name"] for e in board["leagues"]] + (["UFC"] if UFC_ON else [])
    chips = ('<nav class="chips" aria-label="Filter by sport"><button class="chip" data-f="all" aria-pressed="true">All</button>'
             + "".join(f'<button class="chip" data-f="{n}" aria-pressed="false">{n}</button>'
                       for n in chip_names) + '</nav>')
    updated = f"Updated {board['built']:%b} {board['built'].day} at {clock(board['built'])} ET"
    footer = (f"{updated}. Scores, stats and lines from ESPN\u2019s public feed. Lines move, so confirm the number at "
              "your sportsbook before betting. Model probabilities are estimates and don\u2019t include the "
              "projection\u2019s own error. Research tool, not financial advice. Bet only what you can afford to lose."
              + (" " + board["odds_note"] if board.get("odds_note") else ""))
    nav = "".join(f'<a href="#{t}" class="{"active" if t == "top" else ""}">{icon(ic, 22)}{label}</a>'
                  for t, ic, label in (("top", "home", "Home"), ("bets", "bets", "Bets"),
                                       ("props", "props", "Props"), ("live", "live", "Live"),
                                       ("board", "board", "Board"), ("journal", "journal", "Journal"),
                                       ("arb", "arb", "Arb")))
    data = {"date": day.isoformat(), "unitPct": UNIT_PCT, "historyUrl": f"{asset_prefix}history.csv",
            "leagues": [{"name": e["name"], "sport": LEAGUES[e["name"]]["sport"], "league": LEAGUES[e["name"]]["league"],
                         "groups": LEAGUES[e["name"]].get("groups")} for e in board["leagues"] if not e["error"]]}
    pwa = (f'<link rel="manifest" href="{asset_prefix}manifest.webmanifest">'
           f'<link rel="apple-touch-icon" href="{asset_prefix}apple-touch-icon.png">'
           f'<link rel="icon" type="image/png" href="{asset_prefix}icon-192.png">')
    return f"""<!doctype html>
<html lang="en" data-theme="night"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#05070A">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="apple-mobile-web-app-title" content="{esc(APP_NAME)}">
{pwa}
<title>{esc(APP_NAME)}, {esc(long_date)}</title>
<script>try{{var t=JSON.parse(localStorage.getItem('yugi.theme'));if(t)document.documentElement.setAttribute('data-theme',t)}}catch(e){{}}</script>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Rubik:wght@400;500;600&display=swap" rel="stylesheet">
<style>{CSS}</style></head>
<body>
<div class="topbar"><header class="appbar"><a class="brand" href="#top">{LOGO}<span class="brand-word"><b>YUGI</b><small>&mdash; SB BOT V2 &mdash;</small></span></a>
<div class="bar-right"><button class="iconbtn" id="themeBtn" type="button" aria-label="Switch to day mode"><span class="sun">{icon("sun", 20)}</span><span class="moon">{icon("moon", 20)}</span></button>
<button class="iconbtn" type="button" onclick="location.reload()" aria-label="Refresh the board">{icon("refresh", 20)}</button>
<span class="datepill">{esc(short_date)}</span></div></header>
<div class="ticker" id="ticker" aria-label="Live scores"></div></div>
<main>
<section id="top"><div class="tiles">{tile_html}</div><p class="updated">{esc(updated)}</p>{chips}</section>
<section id="bets"><div class="section-head"><h2>Best Bets</h2><span>Locked when first flagged. Line moves don\u2019t remove them.</span></div>{render_bets(board)}</section>
<section id="props"><div class="section-head"><h2>Player Props</h2><span>Only plays with a real edge</span></div>{render_props(board)}</section>
<section id="live"><div class="section-head"><h2>Live</h2><span>Scores as they happen</span></div>{render_live(board)}</section>
<section id="board"><div class="section-head"><h2>The Board</h2><span>Every game, line and matchup</span></div>{render_board(board)}</section>
<section id="journal"><div class="section-head"><h2>Journal</h2><span>Your bets, your bankroll</span></div>{render_journal(board, record)}</section>
<section id="arb"><div class="section-head"><h2>Arb</h2><span>Totals, moneylines and spreads</span></div>{render_arb_list(board)}{render_arb()}</section>
<footer>{esc(footer)}</footer>
</main>
<nav class="bottomnav" aria-label="Sections">{nav}</nav>
<style>:root[data-theme="day"] .moon{{display:none}}:root[data-theme="night"] .sun{{display:none}}</style>
<script>window.YUGI={json.dumps(data)};</script>
<script>{JS}</script>
</body></html>"""


def write_app_files(out):
    """Home-screen app support: icon files and a web app manifest."""
    manifest = {"name": APP_NAME, "short_name": "Yugi v2", "start_url": "./", "scope": "./",
                "display": "standalone", "background_color": "#151C1F", "theme_color": "#151C1F",
                "icons": [{"src": "icon-192.png", "sizes": "192x192", "type": "image/png"},
                          {"src": "icon-512.png", "sizes": "512x512", "type": "image/png"}]}
    (out / "manifest.webmanifest").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    for name, data in ICONS.items():
        path = out / name
        if not path.exists():
            path.write_bytes(base64.b64decode(data))

# ---------------------------------------------------------------------------
# Demo data (no internet needed)
# ---------------------------------------------------------------------------

def demo_board(day):
    rng = random.Random(11)
    samples = {
        "MLB": [("Milwaukee Brewers", "Brewers", "Philadelphia Phillies", "Phillies", 8.5, 7.1, 2.4,
                 (4.6, 3.9), (4.4, 3.8), ("F. Peralta", 3.12), ("Z. Wheeler", 2.71)),
                ("Houston Astros", "Astros", "Athletics", "Athletics", 9.5, 11.2, 4.0,
                 (4.9, 4.6), (5.2, 5.4), ("H. Brown", 3.55), ("J. Springs", 4.88)),
                ("Los Angeles Angels", "Angels", "Seattle Mariners", "Mariners", 7.5, 7.4, 3.5,
                 (4.1, 4.9), (4.3, 3.7), ("J. Soriano", 3.91), ("B. Miller", 3.34))],
        "WNBA": [("Indiana Fever", "Fever", "Minnesota Lynx", "Lynx", 171.5, 182.0, 16.0,
                  (88.9, 84.1), (86.2, 79.0), None, None)],
        "NBA": [],
        "NFL": [("Chicago Bears", "Bears", "Detroit Lions", "Lions", 47.5, 41.0, 8.0,
                 (19.5, 21.0), (24.1, 20.4), ("C. Williams", 231.0), ("J. Goff", 262.0))],
        "NHL": [("Boston Bruins", "Bruins", "Toronto Maple Leafs", "Maple Leafs", 6.0, 6.2, 2.0,
                 (3.1, 2.8), (3.3, 3.0), ("J. Swayman", (0.912, 2.58, 26.4)), ("J. Woll", (0.905, 2.81, 25.1)))],
        "NCAAF": [("Ohio State Buckeyes", "Buckeyes", "Michigan Wolverines", "Wolverines", 44.5, 50.5, 9.0,
                   (38.2, 14.1), (31.5, 16.8), ("W. Howard", 268.0), ("B. Underwood", 221.0))],
        "NCAAB": [("Duke Blue Devils", "Blue Devils", "North Carolina Tar Heels", "Tar Heels", 151.5, 148.0, 12.0,
                   (80.1, 68.4), (79.3, 71.2), None, None)],
        "NCAAW": [("UConn Huskies", "Huskies", "South Carolina Gamecocks", "Gamecocks", 138.5, 131.0, 11.0,
                   (78.4, 55.2), (81.0, 54.6), None, None)],
    }
    board = {"date": day, "built": to_local(utcnow()), "leagues": [], "props": [], "arbs": [],
             "team_totals": [], "ufc": {"fights": [], "plays": [], "note": None}, "odds_note": None}
    for name, games in samples.items():
        lg = LEAGUES[name]
        entry = {"name": name, "unit": lg["unit"], "games": [], "error": None,
                 "prior_season": False, "skipped": 7 if name == "NCAAB" else 0}
        for i, (away, anick, home, hnick, line, center, spread, a_rates, h_rates, a_star, h_star) in enumerate(games):
            meetings = []
            for k in range(LAST_N):
                a = max(0, round(center / 2 + rng.gauss(0, spread / 2)))
                h = max(0, round(center / 2 + rng.gauss(0, spread / 2)))
                meetings.append({"date": f"Sample {k + 1}", "away": away, "away_score": a,
                                 "home": home, "home_score": h, "total": a + h})
            sides = {}
            for where, nm, nick, rates, star in (("away", away, anick, a_rates, a_star),
                                                 ("home", home, hnick, h_rates, h_star)):
                split = {"n": 40, "ppg": rates[0], "papg": rates[1], "home_n": 20, "away_n": 20,
                         "home_ppg": rates[0] * 1.03, "home_papg": rates[1] * 0.97,
                         "away_ppg": rates[0] * 0.97, "away_papg": rates[1] * 1.03,
                         "recent_n": 10, "recent_ppg": rates[0] * rng.uniform(0.9, 1.1),
                         "recent_papg": rates[1] * rng.uniform(0.9, 1.1)}
                starter = passer = None
                if name == "MLB":
                    starter = {"name": star[0], "era": star[1], "whip": round(0.9 + star[1] / 10, 2)}
                elif name == "NHL":
                    starter = {"name": star[0], "svpct": star[1][0], "gaa": star[1][1], "saves_pg": star[1][2]}
                elif name in ("NFL", "NCAAF"):
                    passer = {"name": star[0], "ypg": star[1]}
                sides[where] = {"name": nm, "nickname": nick, "split": split, "starter": starter,
                                "passer": passer, "rank": {"rank": rng.randint(1, 30), "of": 30},
                                "rest": {"NFL": 7, "NCAAF": 7, "NHL": 1 if where == "away" else 2}.get(name, 2)}
            odds = {"line": line, "over": "-110", "under": "-110", "book": "ESPN BET"}
            stats = summarize(meetings, line)
            proj = project_total(name, lg, sides["home"], sides["away"])
            pick = recommend(name, lg, line, stats, proj, odds)
            probs = side_probs(name, proj["total"], line) if proj else None
            locked = None
            if name == "MLB" and i == 1:       # a play locked this morning; the line has since moved
                locked = {"side": "over", "tier": "Lean", "price": "-110", "line": line - 0.5, "time": "8:09 AM",
                          "prob": 0.59, "edge": 0.066, "still": False, "result": ""}
            if name == "NFL":                  # a play that already finished
                locked = {"side": "under", "tier": "Strong", "price": "-110", "line": line, "time": "8:09 AM",
                          "prob": 0.64, "edge": 0.116, "still": True, "result": "under"}
            entry["games"].append({
                "league": name, "id": f"demo{name}{i}", "start_utc": "", "time": f"{1 + i * 3}:05 PM",
                "away": away, "home": home, "status": "",
                "odds": odds, "meetings": meetings, "stats": stats,
                "note": None, "sides": sides, "proj": proj, "pick": pick, "probs": probs, "locked": locked,
                "state": "post" if name == "NFL" else "pre", "final_total": 38 if name == "NFL" else None,
                "env": {"MLB": "71\u00b0F, Partly cloudy", "NFL": "Indoors (roof or dome)",
                        "NCAAF": "48\u00b0F, Cloudy"}.get(name),
                "first_line": line - 0.5 if i in (0, 1) else None})
        board["leagues"].append(entry)
    record = {"MLB": {**_blank_record(), "graded": 61, "over": 29, "under": 31, "push": 1, "trend_n": 44,
                      "trend_w": 23, "bets": 14, "wins": 8, "losses": 6, "units": 1.3, "strong_n": 4, "strong_w": 3},
              "NFL": {**_blank_record(), "graded": 16, "over": 7, "under": 9, "trend_n": 9, "trend_w": 4,
                      "bets": 5, "wins": 2, "losses": 3, "units": -1.2, "strong_n": 1, "strong_w": 0},
              "WNBA": {**_blank_record(), "graded": 22, "over": 12, "under": 10, "trend_n": 15, "trend_w": 8,
                       "bets": 6, "wins": 4, "losses": 2, "units": 1.6, "strong_n": 2, "strong_w": 1}}
    record["All"] = {k: sum(r[k] for r in record.values()) for k in _blank_record()}
    board["props"] = [
        {"league": "MLB", "game": "San Diego Padres @ Arizona Diamondbacks", "time": "7:05 PM",
         "player": "Eduardo Rodriguez", "market": "pitcher_strikeouts", "label": "strikeouts",
         "line": 2.5, "side": "over", "price": "-450", "book": "DraftKings", "link": None,
         "prob": 0.880, "implied": 0.818, "edge": 0.062, "n": 26, "full": 0.962, "recent": 0.90,
         "last5": 1.0, "avg": 4.6},
        {"league": "NFL", "game": "Chicago Bears @ Detroit Lions", "time": "1:05 PM",
         "player": "Jahmyr Gibbs", "market": "player_rush_yds", "label": "rush yards",
         "line": 39.5, "side": "over", "price": "-125", "book": "FanDuel", "link": None,
         "prob": 0.642, "implied": 0.556, "edge": 0.086, "n": 24, "full": 0.792, "recent": 0.80,
         "last5": 0.80, "avg": 61.4},
        {"league": "NBA", "game": "Boston Celtics @ Los Angeles Lakers", "time": "10:10 PM",
         "player": "Luka Doncic", "market": "player_points_rebounds_assists", "label": "points",
         "line": 24.5, "side": "over", "price": "-180", "book": "BetMGM", "link": None,
         "prob": 0.714, "implied": 0.643, "edge": 0.071, "n": 31, "full": 0.806, "recent": 0.70,
         "last5": 0.60, "avg": 29.8}]
    board["arbs"] = [{"what": "NFL moneyline", "game": "Chicago Bears @ Detroit Lions", "start": None,
                      "total": 0.9127, "profit": 0.0957,
                      "legs": [{"side": "Chicago Bears", "point": None, "price": "+180", "book": "DraftKings",
                                "book_key": "dk", "link": None},
                               {"side": "Detroit Lions", "point": None, "price": "-125", "book": "FanDuel",
                                "book_key": "fd", "link": None}]},
                     {"what": "MLB total 9.5", "game": "San Diego Padres @ Arizona Diamondbacks",
                      "start": None, "total": 0.9413, "profit": 0.0624,
                      "legs": [{"side": "Over", "point": 9.5, "price": "+115", "book": "BetMGM",
                                "book_key": "betmgm", "link": None},
                               {"side": "Under", "point": 9.5, "price": "+110", "book": "Caesars",
                                "book_key": "caesars", "link": None}]}]
    board["team_totals"] = [
        {"league": "NFL", "game": "Chicago Bears @ Detroit Lions", "time": "1:05 PM", "who": "away",
         "team": "Chicago Bears", "side": "under", "line": 23.5, "price": "-115", "book": "DraftKings",
         "link": None, "prob": 0.602, "implied": 0.535, "edge": 0.067, "expect": 21.0}]
    board["ufc"] = {"note": None, "fights": [], "plays": [{
        "a": {"name": "Blake Stone"}, "b": {"name": "Dmitri Volkov"}, "time": "10:00 PM",
        "round_line": 1.5, "distance": 3, "prob": 0.80, "max_price": -400, "ceiling_ok": False,
        "implied": 0.857, "edge": -0.057,
        "rates": [{"rate": 0.87, "fights": 15}, {"rate": 0.82, "fights": 17}]}]}
    board["odds_note"] = "Sample data. 8 odds credits used this run."
    return board, record


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def check_odds(today):
    """Pings the odds provider with your key and prints exactly what came back,
    so a problem shows up in seconds instead of inside a full run."""
    print(f"ODDS_API_KEY set: {'yes' if ODDS_API_KEY else 'no'}"
          f"   SGO_API_KEY set: {'yes' if SGO_API_KEY else 'no'}")
    if not (ODDS_API_KEY or SGO_API_KEY):
        print("\nNo key found. Set one and run again:")
        print("  Mac/Linux:  export ODDS_API_KEY=your-key-here")
        print("  Windows:    set ODDS_API_KEY=your-key-here")
        return 2
    client = OddsClient(ODDS_API_KEY or None, SGO_API_KEY or None, budget=12)
    ok = 0
    for league in ("MLB", "NFL", "NBA", "NCAAF"):
        try:
            events = client.game_totals(league)
        except Exception as err:
            print(f"{league:6} error: {err}")
            continue
        if not events:
            print(f"{league:6} no games with totals right now")
            continue
        ok += 1
        ev = events[0]
        shop = best_book_total(ev["rows"])
        books = sorted({r["book"] for r in ev["rows"]})
        print(f"{league:6} {len(events)} games. Sample: {ev['away']} @ {ev['home']}")
        if shop:
            print(f"       line {fmt_num(shop['line'])} across {shop['books']} books, "
                  f"best over {shop['over']['price']} ({shop['over']['book']}), "
                  f"best under {shop['under']['price']} ({shop['under']['book']})")
        print(f"       books seen: {', '.join(books[:8])}")
        if ok == 1 and ev.get("id"):
            alts = client.alt_totals(league, ev["id"])
            print(f"       alternate totals: {len(alts)} prices"
                  + (f", from {fmt_num(min(r['point'] for r in alts if r['point'] is not None))} "
                     f"to {fmt_num(max(r['point'] for r in alts if r['point'] is not None))}" if alts else ""))
            props = client.props(league, ev["id"])
            names = sorted({r["player"] for r in props if r.get("player")})
            print(f"       player props: {len(props)} prices for {len(names)} players"
                  + (f" (e.g. {names[0]})" if names else ""))
    print(f"\nCredits used: {client.spent}"
          + (f", {int(client.remaining)} left on the plan" if client.remaining is not None else ""))
    if client.errors:
        print("Problems: " + "; ".join(client.errors))
        return 1
    print("Key works." if ok else "Key reached the provider but no games came back.")
    return 0


def main():
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(errors="replace")
        except Exception:
            pass
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description="Yugi SB Bot v2: daily over/under betting board.")
    parser.add_argument("--date", help="day to build, YYYY-MM-DD (default: today)")
    parser.add_argument("--leagues", help="comma-separated, e.g. MLB,NFL (default: all turned on)")
    parser.add_argument("--out", default=str(here / "reports"), help="folder for the board and history")
    parser.add_argument("--no-open", action="store_true", help="don't open the browser")
    parser.add_argument("--demo", action="store_true", help="sample board, no internet needed")
    parser.add_argument("--no-odds", action="store_true",
                        help="skip the odds provider entirely and spend no credits")
    parser.add_argument("--check-odds", action="store_true",
                        help="test your odds key and show what came back, then stop")
    args = parser.parse_args()

    out = Path(args.out)
    (out / "archive").mkdir(parents=True, exist_ok=True)
    write_app_files(out)
    today = dt.date.fromisoformat(args.date) if args.date else to_local(utcnow()).date()

    if args.check_odds:
        return check_odds(today)

    if args.demo:
        board, record = demo_board(today)
        page = out / "demo.html"
        page.write_text(render_page(board, record), encoding="utf-8")
        print(f"Demo board saved to {page}")
        if not args.no_open:
            webbrowser.open(page.resolve().as_uri())
        return 0

    names = [n.strip().upper() for n in args.leagues.split(",")] if args.leagues \
        else [n for n, lg in LEAGUES.items() if lg["on"]]
    unknown = [n for n in names if n not in LEAGUES]
    if unknown:
        print(f"Unknown league(s): {', '.join(unknown)}. Choose from {', '.join(LEAGUES)}.")
        return 2

    print(f"Building {APP_NAME} for {today:%A, %B} {today.day}, {today.year}")
    fetch = Fetcher(out / ".cache")
    client = OddsClient(None, None) if args.no_odds else \
        OddsClient(ODDS_API_KEY or None, SGO_API_KEY or None)
    if args.no_odds:
        print("Odds provider: skipped by --no-odds, ESPN lines only")
    else:
        print("Odds provider: " + ("The Odds API" if ODDS_API_KEY else "SportsGameOdds"
              if SGO_API_KEY else "none set, ESPN lines only (no props or arbs)")
              + (f", budget {client.budget} credits" if client.on else ""))
    board = build_board(fetch, today, names, client)

    history_path = out / "history.csv"
    history = load_history(history_path)
    if client.on:
        pools = client.split_rest({"arb": ARB_SHARE, "props": PROPS_SHARE, "team": TEAM_SHARE})
        print(f"Boards priced with {client.spent} credits. Remaining split: "
              + ", ".join(f"{k} {v}" for k, v in pools.items()))
    enrich_with_books(board, client, history)
    record_board(history, board)
    board["arbs"] = scan_arbs(board, client) if client.on else []
    for entry in board["leagues"]:
        for g in entry["games"]:
            for ev in g.get("alt_rows") or []:
                board["arbs"].extend(find_arbs([ev], g["league"], "totals"))
    board["arbs"] = sorted({(a["game"], a["what"]): a for a in board["arbs"]}.values(),
                           key=lambda a: -a["profit"])[:25]
    board["team_totals"] = build_team_totals(client, board) if client.on else []
    board["props"] = (build_props(fetch, client.using("props"), board, to_local(utcnow()).year)
                      if client.on else [])
    client.pool = None
    board["ufc"] = ufc_plays(fetch, client, today) if UFC_ON else {"fights": [], "plays": [], "note": None}
    if client.on:
        bits = [f"{client.spent} odds credits used this run"
                + (f" ({client.used.get('arb', 0)} arbs, {client.used.get('props', 0)} props, "
                   f"{client.used.get('team', 0)} team totals)" if client.used else "")]
        if client.skipped:
            bits.append("skipped " + ", ".join(client.skipped))
        if client.remaining is not None:
            bits.append(f"{int(client.remaining)} left on the plan")
        if client.errors:
            bits.append("; ".join(client.errors))
        board["odds_note"] = ". ".join(bits) + "."
    grade_past(history, fetch, today)
    save_history(history_path, history)
    record = track_record(history)

    (out / "index.html").write_text(render_page(board, record), encoding="utf-8")
    (out / "archive" / f"{today.isoformat()}.html").write_text(
        render_page(board, record, asset_prefix="../"), encoding="utf-8")
    print(f"Done: {fetch.calls} requests. Board saved to {out / 'index.html'}")
    if not args.no_open:
        webbrowser.open((out / "index.html").resolve().as_uri())
    return 0


if __name__ == "__main__":
    sys.exit(main())
