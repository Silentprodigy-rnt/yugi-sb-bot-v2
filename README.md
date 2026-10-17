# Yugi SB Bot v2

A daily over/under betting board for MLB, WNBA, NBA, NFL, NHL, NCAAF, NCAAB and NCAAW. All data comes from ESPN's public feed. No logins, keys or paid services.

v2 runs beside v1 without touching it. See `Instructions/Yugi SB Bot v2 - What's New and Install.pdf`.

## What changed in v2

**Best Bets are locked.** The first time a game qualifies, the play is saved with that line, price and time. Later line moves never delete it. If the number moves, the play stays on the board and says so, and it is graded at the line you were given, not the closing line. This fixes the problem where seven lean plays vanished by 10 PM.

**Every play must clear a probability edge.** The projection is turned into a win probability for that side, which is compared with the price's implied probability. A play needs at least a **+4% edge** on top of the old rules. A line that merely sits near the projection no longer qualifies.

**Weak leagues require a Strong grade.** WNBA, NHL, NCAAF, NCAAB and NCAAW only produce a Best Bet on the top tier. Everything thinner is filtered out.

**Full team names.** "Arkansas Razorbacks", not "Razorbacks", everywhere on the board.

**Live scores.** A ticker across the top scrolls sideways through every game, and a **Live** tab lists them by sport. Both refresh every minute while the page is open, straight from ESPN to your browser, so they keep updating between the two daily builds.

**Day and night themes.** The sun/moon button in the top bar switches between a near-black night theme and a light day theme. Your choice is remembered.

**Journal tab.** Set your bankroll and unit size, and every Best Bet shows the dollar stake. Tap **Log this bet** on a play to pre-fill it, or add any bet by hand with sport, play, odds, stake, result and amount won or lost. It tracks record, net, ROI, units, your average stake against your target, and Strong vs. Lean separately. It also compares the plays you took with the bot's last 30 days of Best Bets, including how the ones you skipped did. Export and import CSV; entries live in your browser.

**Arb tab.** Enter the best price on each side from two or three books. It shows the market total, the stake for each side, and the locked profit.

## Your three rules, and how they're applied

1. **Unit size, 2.5%.** Set your bankroll in Journal and every play shows the dollar amount. The Journal flags your average stake against the target.
2. **Positive probability gap.** Enforced as a hard gate: model probability minus implied probability must be at least 4%. Every play shows both numbers.
3. **Odds of -300 or heavier.** The setting exists (`ODDS_FLOOR`) but ships **off**, because standard totals are priced near -110 and turning it on would produce zero plays every day. Heavy prices at a high hit rate live on **alternate lines**, which ESPN's feed doesn't carry. See "What an odds API would unlock" below.

**An honest note on the probabilities.** The model turns a projected total into a probability using a normal curve around the projection. That assumes the projection is correct on average, which it isn't yet. So the stated edge is an upper bound, not a promise. Treat the Record tab as the real test: if Best Bets don't clear 52.4% over a few hundred plays, the edge isn't there regardless of what the percentages say.

## Not built yet, and why

These need data ESPN's free feed doesn't publish. I didn't fake them, because a prop screen built on guessed numbers is how you lose money:

- **No-touchdown parlays.** Needs a full season of TD logs for every rostered player.
- **Halves and quarters.** The markets exist in the odds API; it is a credit-cost decision, not a technical one.
- **Player prop arbs.** Possible, but each game costs credits per market, so this waits until the paid plan is in place.
- **Pikkit sync.** Pikkit has no public API. If it can export a CSV, the Journal's CSV import reads it. Otherwise use Log this bet.

## Odds provider options

To build the list above, one of these is the missing piece. All have free tiers you can start on:

| API | Free tier | What it unlocks |
|---|---|---|
| **The Odds API** (the-odds-api.com) | 500 credits/month | Many books, alternate totals, team totals, halves and quarters, player props by event. Simplest to start with. |
| **SportsGameOdds** (sportsgameodds.com) | Free "Amateur" plan | 85+ books, player and team props, alternate lines, settlement data. Best coverage per dollar. |
| **OddsLink** (oddslink.app) | Free plan sees every book; props from $49/mo | Widest book list, deep alternate ladders. Best for arbitrage scanning. |

Start with a free key from any one of them and send it over. With multi-book prices I can build: true line shopping, the -300 alternate-line plays, automatic arb scanning, and the prop screens.

**Separately, for props you also need player game logs.** Best free options: MLB's own Stats API (free, no key, full game logs), nba_api (free Python package), and nflverse (free weekly data). I'd pair one of these with the odds API to compute hit rates the way your Eduardo Rodriguez example does.


## v2.1: odds providers, props, alternate lines and arbs

**Your keys never go in the code.** The bot reads them from the environment, so the file is safe in a public repository. On GitHub: **Settings > Secrets and variables > Actions > New repository secret**, named `ODDS_API_KEY` (the-odds-api.com) and/or `SGO_API_KEY` (sportsgameodds.com). Locally, `export ODDS_API_KEY=...` before running.

**Regenerate any key you have pasted into a chat, email or document.** Treat it like a password.

**Check a key in seconds:** `python yugi_sb_bot_v2.py --check-odds`. It prints the games, books, alternate totals and props it can see, plus credits remaining.

### What the odds key turns on

| Feature | What you get |
|---|---|
| **Line shopping** | Best price on each side across every book, on every total. |
| **Alternate totals** | The "buy down to a safer number" play. On each Best Bet the bot scans the alternate ladder and shows the number with the best expected value, which is where a -300 price at a high hit rate becomes the bet. |
| **Player Props tab** | Props from the book, hit rates from real game logs, sorted by edge across all sports. |
| **Arb tab** | Live arbitrage list with book names, prices and links, above the calculator. It pairs every book against every other, so it still finds the edge when one book leads on both sides. |
| **Line movement** | Opening number vs. now, with a steam flag when the move is big. |

### How props are scored

Props come from the odds API. Hit rates come from real game logs: **MLB Stats API** for baseball (free, no key) and **ESPN game logs** for the other sports. For each prop the bot counts how often the player actually cleared that number, then converts it to a **cautious probability** using a Wilson lower bound at 90% confidence.

That last step matters. A raw 25-for-26 reads as 96%, but 26 games can't prove 96%, so the bot calls it **88%**. A 5-for-5 record becomes 75%, not 100%. Only props clearing a **+4% edge** after that haircut are shown. On your Eduardo Rodriguez example the bot lands on 88% vs. the book's 82%, a +6.2% edge, which still makes the play.

### How the bot avoids wasting credits

Credits are only spent where they can change a bet. The order matters: **ESPN comes first and is free**, so the paid provider is never asked about a sport that isn't playing.

1. **The schedule is checked first, for free.** ESPN is asked what's on today. No WNBA games in December means the WNBA odds call never happens. Same for MLB in January or the NBA in July. This is automatic and needs no season calendar to maintain.
2. **A league needs a game that hasn't started.** If every game has already tipped or finished, there's nothing to bet, so that league is skipped and the page says so.
3. **The same request is never paid for twice** in one run.
4. **Alternate totals are fetched only for games that already produced a Best Bet**, not for the whole slate.
5. **Props are capped** at `PROP_GAMES_PER_LEAGUE` (default 6) games per sport.
6. **Arbitrage costs nothing extra.** The scan runs over prices already bought for the board.
7. **A hard budget stops the run.** `ODDS_BUDGET` (default 40) caps one run, and the page reports what was used and what was skipped.

A quiet December day with only NBA and NHL on the slate costs about 2 credits for the boards. A busy fall Saturday with props on costs the most, which is what the budget cap is for.

To spend nothing at all on a given run: `python yugi_sb_bot_v2.py --no-odds`.

### Splitting credits between arbs and props

After the boards are priced (the essential part), whatever budget is left is **split between arbitrage, player props and team totals**, so a long prop run can't eat the arb allowance or the other way round. The page reports the split, for example *"18 credits used (9 on arbs, 9 on props)"*.

To favour one, change these at the top of the file:

```
ARB_SHARE = 0.5      # arb scanning
PROPS_SHARE = 0.5    # player props
TEAM_SHARE = 0.25    # team totals
```

They're weights, not percentages, so 0.5 / 0.5 / 0.25 gives arbs and props 40% each and team totals 20%.

### What the Arb tab scans

Three markets, each paired across every book combination:

- **Totals** — free, because the board already paid for those prices.
- **Moneylines** and **spreads** — one request per sport covers every game, charged to the arb share.

These are **true arbitrage**, not Best Bets: both sides priced so the market totals under 100%, which profits either way. Each row shows the game, both legs with book and price, links where the provider supplies them, and the locked profit.

Two honest limits. Arbs vanish within minutes, so an empty list is normal and expected. And books limit or close accounts that only bet arbs, so treat it as a side feature rather than the main plan.

### UFC: fights that end early

The bot pulls the UFC card from ESPN and checks your three conditions:

1. **Rounds total of 1.5 or lower** (the books expect an early finish)
2. **Both fighters finish 80%+ of their fights**, counting wins and losses, since either ends the bout early
3. At least 6 recorded fights each, so the rate means something

What it publishes is the **break-even price**, not a blanket "-600 is fine". This matters: **-600 implies 85.7%**. A strategy that wins 85% of the time *loses money* at -600. So the bot shows the worst price worth paying for that specific fight, and warns when -600 is too expensive.

In testing, two fighters at 87% and 82% with a 1.5 rounds total produced a model estimate of 80% and a max price of **-400**, flagged as not worth -600. That is the protection, not a bug.

The finish-inside-the-distance market isn't in the odds feed, so price it at your book. Everything else is automatic.

### Team totals

The projection already splits each game into an expected score per side, so a team total is the same test on one team. The bot prices team totals for up to 4 games per sport (Best Bet games first), compares each side's projection against the posted number, and keeps the ones clearing the 4% edge.

### Credit budget

Each run spends credits: 1 per sport for game totals, 1 per game for alternate totals, and 1 per prop market per game. `ODDS_BUDGET` (default 40) caps one run, and the bot stops cleanly and says so on the page. The Odds API's free 500/month covers roughly one run a day with props on a few games. For full daily props across eight sports you'd want a paid tier or SportsGameOdds.

Tune `PROP_GAMES_PER_LEAGUE` and `PROP_MARKETS` at the top of the file to spend less.

### The NCAAF strategy: what's in and what's missing

Your Houston/Oklahoma State example has two halves:

- **Line movement (built).** The bot stores the opening total and flags a big move. 57.5 to 62.5 shows as "Total moved up 5 from the 57.5 opener."
- **Alternate total that clears key numbers (built).** With an odds key, each Best Bet shows the best buy-down on the alternate ladder, with the model's probability against the book's price.
- **Bet % vs. money % (not built).** No odds API publishes public betting splits. They come from sportsbook consensus feeds. Covers shows them but their terms bar reusing their content, and Outlier has no public API. If you want this, the realistic path is a paid feed such as Action Network or SportsInsights, or reading the splits yourself on Covers before placing a bet. The bot gives you the line movement half automatically.

### Still not built

UFC props (needs fighter finish rates and round totals), no-touchdown parlays (needs full season TD logs per player), and team totals by half or quarter (needs those markets pulled per game, which costs credits). Say the word and I'll add them in that order.

## Install

Two ways, both in the PDF:

- **New repository** (recommended): keeps v1 running at its own address while you compare.
- **Same repository**: replace the bot and workflow, and v2 takes over the address you already use.

## Settings

Everything you'd tune is at the top of `yugi_sb_bot_v2.py`:

- `UNIT_PCT` (2.5%), `MIN_EDGE` (4%), `ODDS_FLOOR` (off)
- `SIGMA`, how much a total normally swings per sport, which drives the probabilities
- `ONLY_STRONG`, the leagues restricted to top-tier plays
- Per-league Lean and Strong thresholds, and which leagues are on

## Good to know

- Journal entries and your theme live in **your browser**, not on the server. Clearing site data erases them, so export a CSV backup now and then.
- Live scores need the real website or home-screen app. They can't load from a file opened off your computer.
- **Every number here is a research aid, not advice.** Confirm each line at your book before betting, and never stake more than you can afford to lose.
