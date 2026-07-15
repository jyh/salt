# House-recorded executor token counts (primary data)

Recorded by the Fable house session from task-completion notifications,
2026-07-14 → 2026-07-15 (the Chen endgame + the exploration sprint's
opening). Output tokens per agent run (thousands, rounded); tool-use
counts and durations were also reported but are recorded here only where
notable. Earlier arcs' counts were not systematically retained — noted
as a gap for the method paper. All runs Opus-tier except where marked
(the Fable-inheritance mistake of 2026-07-14 affected runs before the
account switch: GBV3→GLU-2W-first ran ON FABLE unintentionally; see
flags/memory — the method paper's economics section must price those at
Fable rates).

## The Chen endgame (2026-07-14 → 07-15)

| Node | ktok | | Node | ktok |
|---|---|---|---|---|
| GBV3 | 256 | | fin5 | 221 |
| GBV4 | 347 | | fin6 | 259 |
| GBV5 | 425 | | fin7a | 341 |
| GLU-2 (#64) | 362 | | fin7b | 408 |
| H2-recon | 158 | | fin8 | 280 |
| H2-GATE | 250 | | fin8a | 288 |
| D0W | 303 | | fin8b | 281 |
| GLU-2b (#65) | 504 | | fin8c | 280 |
| W-SURG | 109 | | fin8d | 214 |
| H4C | 242 | | FIN-A3 | 381 |
| A1W | 285 | | FIN-A3b | 147 |
| A3W | 451 | | FIN-A3c | 289 |
| CNTW | 338 | | FIN-LED | 321 |
| A2W′ | 304 | | FIN-LED-2 | 340 |
| A3W2 | 345 | | FIN-LED-3 | 467 |
| GLU-2W-fin | 252 | | HCE | 188 |
| PRICE-GATE | 243 | | HDIAG | 248 |
| PRICE-0 | 210 | | HSUM | 329 |
| PRICE-1 | 286 | | SYMLOW | 394 |
| PRICE-2 | 241 | | PACK-A | 260 |
| PRICE-3 | 233 | | PACK-B | 158 |
| PRICE-3b | 254 | | HCOUNT | 203 |
| EDGE+fin3 | 262 | | HCOUNT-2 | 205 |
| fin4 | 198 | | HCOUNT-3 | 661 |
| A2WIN | 172 | | | |

Endgame executor total ≈ **13.0 M output tokens** across 49 runs
(median ≈ 270k; max HCOUNT-3 at 661k — the count-line composition;
min FIN-A3b at 147k — the mechanical restatements).

## The exploration pilot + sprint (2026-07-14 evening → 07-15)

| Run | ktok | Outcome class |
|---|---|---|
| PILOT-recon | 138 | recon |
| P-A (enlarged) | 201 | theorem + threshold |
| P-C (k=3) | 183 | sharp constant + conditional no-go |
| Q1-recon | 102 | reuse audit |
| Q6a-recon | 95 | honest-shape analysis |
| Q5a | 243 | obstruction theorem + no-go + numerics |
| Q3-recon | 97 | one-line-consumption finding |
| Q4 | 136 | statement + literature verdict |
| TAXONOMY | 348 | the 78-row dataset |
| Q6a-GATE | 128 | adversarial gate (3 tears + amendment) |
| Q6a-1 | 199 | witness pair + evaluations, first attempt |

Exploration total so far ≈ **1.54 M**; recon median ≈ 100k; probe
median ≈ 200k. (Q2-ASM in flight at recording time.)

## Known gaps

- Pre-endgame arcs (SW, BV, P0/P1, the Chen build phase to the razor):
  token counts not retained; only node/commit/attempt data (git + flags)
  survives. The method paper reports the endgame economics as measured
  and the earlier arcs as commit-count proxies.
- House-session (Fable) tokens: not separately metered; the session
  transcript is the only record.
- The 2026-07-14 Fable-inheritance window: GBV3 through GLU-2W-first
  (~4.8 M of the above) ran on Fable pricing by mistake; the fix and the
  user-ratified routing rule are in the ledger.
