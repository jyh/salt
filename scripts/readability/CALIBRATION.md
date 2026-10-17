# Layer-1 readability: calibration (O83 item 1)

The pair was chosen BEFORE the script was first run on either: `Salt/Brun/M2.lean`, a classical sieve
instantiation in ordinary mathlib style (the "readable" pole), and `SaltC1/Cert54/`, C1's generated
`k = 54` certificate (the control, which must score low). Regenerate the table with

    python3 scripts/readability/layer1.py Salt/Brun/M2.lean --json
    python3 scripts/readability/layer1.py SaltC1/Cert54 --json

Instrument receipts. The parser counts **493** theorems in Cert54, the number `Audit.lean`'s own header
states. On M2 it agrees with plain `grep` (18 theorems, 3 definitions, 14 docstrings, 2 `decide`). The
selftest has 15 mutation arms. Twelve fail against a zero stub (red first). The three invariance arms
(copyright excluded, module header excluded, tactic names in prose ignored) each fail against a mutant
that breaks the property they guard.

| field | `Salt/Brun/M2.lean` | `SaltC1/Cert54/` (9 files) |
|---|---:|---:|
| `files` | 1 | 9 |
| `decls` | 21 | 579 |
| `theorems` | 18 | 493 |
| `definitions` | 3 | 80 |
| `depth` | 6 | 10 |
| `fanout_max` | 6 | 131 |
| `fanout_mean` | 1.81 | 2.701 |
| `prose_chars` | 1703 | 14179 |
| `formal_chars` | 7779 | 130692 |
| `prose_formal` | 0.2189 | 0.1085 |
| `defs_documented` | 1.0 | 1.0 |
| `forward_prose_refs` | 1 | 2 |
| `role_lines` | 0.6111 | 0.0203 |
| `automation` | 60 | 596 |
| `automation_per_decl` | 2.857 | 1.029 |
| `kernel_comp` | 2 | 478 |
| `numeral_density` | 0.0 | 11.982 |
| `kernel_comp` per decl (derived) | 0.095 | 0.826 |

## Verdict per metric (the rule: a metric that cannot tell the pair apart is struck)

| metric | reading | verdict |
|---|---|---|
| depth | 6 vs 10, but Cert54's per-file maximum is also 6: the gap is population SIZE | **struck** |
| fan-out | the mean is HIGHER in M2 (1.81 vs 0.4–1.1 per Cert54 file); the max is one assembly theorem | **struck** as a discriminator |
| prose/formal | 0.219 vs 0.109 over the population (2.0×); per file it does NOT separate: Cert54's interface files run 0.44–1.7 and its row files 0.02–0.06 | **kept, population level only** |
| defs-first (a) definitions documented | 1.0 vs 1.0 | **struck** |
| defs-first (b) forward prose refs | 1 vs 2 | **struck** at this pair |
| role lines | 0.611 vs 0.020 (30×) | **kept**, the strongest |
| hidden steps, all automation per decl | 2.857 vs 1.029: INVERTED, it would rank the certificate the more readable | **struck** as a readability signal |
| hidden steps, kernel computation per decl | 0.095 vs 0.826 (8.7×) | **kept** |
| numeral density (the declared extra) | 0.0 vs 12.0 | **kept** |

Three survive: **role lines**, **kernel computation**, **numeral density**, plus prose/formal at population
level. All three are certificate DETECTORS. None of them measures whether a human proof explains itself,
and a pair of two points cannot validate one that does. The struck axes (depth, fan-out, automation) are
real readability questions this pair cannot speak to: for them, layer 2's non-author reader is the
instrument. Nothing here says the prose is true of the code.
