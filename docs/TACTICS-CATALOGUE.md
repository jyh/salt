# THE TACTICS CATALOGUE — by machine (O13 item 4)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/tactics_catalogue.py` · staleness gate: `python3 scripts/tactics_catalogue.py --check`.
> Base: last commit touching `Salt/` = `ec4ad6e6` · source digest `e0cbe906d0d8475f` (the same digest as items 1–3).
> Receipt: files 1388 · decls 23369 · with_body 23369 · tactic_lines 319634 · runs 37260 · blocks 1606.

## LIMITS (read before any number below)

- **Source-level, no Lean.** Names are resolved by item 1's namespace/`open` rules plus the `open … in` lines directly above a declaration; `export`, `alias`, notation, `simp` sets and macro expansion are NOT followed. A call that reaches a lemma through another lemma, a `simp [..]` set built elsewhere, or a local `have` alias is not a site.
- **Adoption counts proof-body TOKENS** (item 2's body: statement end → next command), comments and strings stripped, OUTSIDE `Salt/Tactic/`. A statement that merely mentions a name is not a site; two uses on one line are two sites (a `git grep -c` counts lines, so the two can differ).
- **A tactic line is a line whose first token is in the WHITELIST below** (data, a choice), from the first `by` of a body onward. Term-mode continuation lines, `⟨…⟩` pieces and tactics absent from the list are not counted, so Part 2 is a LOWER bound per keyword and says nothing about tactics it does not list.
- **Macro candidates are PRICED AS AN UPPER BOUND.** Lines saved = (block lines − 1) × occurrences assumes every occurrence collapses to ONE line. A macro call is ≥ 1 line, a block whose placeholders bind differently at two sites may not share one macro, and a block of generic tactics (`norm_num`, `linarith`) may be cheaper to leave than to name (the O15 lesson: span-2 sites saved nothing). Local-name detection is heuristic (binders, `have/obtain/intro/…` patterns, `h…` names, ≤ 2-char names); a missed local makes two equal blocks look different (under-count), a lemma mistaken for a local merges two different blocks (over-count).
- **Candidates OVERLAP and their savings are NOT additive:** a region repeated at several lengths yields several maximal blocks (a longer block with fewer occurrences is a different candidate); each entry names the earlier entries it shares source lines with. Many top candidates are `have`-chains that NAME facts used later; a hygienic macro cannot introduce those names, so their natural capture is a LEMMA returning the facts (still ≥ 1 line plus a destructuring), not a tactic macro.
- Per-family numbers use item 2's FAMILY map (a CHOICE, printed on `docs/METHODS-CATALOGUE.md`); a declaration in several families counts in each, and `(no family)` collects the rest.

## 1. The ledger's status, by machine

Ledger: `docs/blueprints/tactics.md`. Module claims come from three sources: the ledger section naming the path (`ledger`), the module's own header `ledger T<n>` (`header`), and `Salt/Tactic/All.lean`'s docstring (`All.lean`).

| id | ledger names | ledger says | ledger's paths | machine: modules claiming it (sources) | machine: header name(s) present in `Salt/`? |
|---|---|---|---|---|---|
| T1 | `CertEval` | PROBE RESULT | `CertEval.lean` | `CertEval.lean` (ledger) | `CertEval` yes |
| T2 | `eventually_budget` | LANDED · NOT USED | `EventuallyBudget.lean` | `EventuallyBudget.lean` (All.lean, header, ledger) | `eventually_budget` yes |
| T3 | `budget_num` | LANDED | `ExpLogNum.lean`, `NlinarithSuggest.lean`, `Numerals.lean` ⛔ NOT ON DISK | `ExpLogNum.lean` (All.lean, header, ledger); `LogNum.lean` (All.lean, header); `NlinarithSuggest.lean` (All.lean, header, ledger) | `budget_num` **no** |
| T4 | `salt_cast` | (no status word) | - | **none** | `salt_cast` **no** |
| T5 | `#audit_axioms` | LANDED | `AuditAxioms.lean` | `AuditAxioms.lean` (All.lean, ledger) | `#audit_axioms` yes |
| T6 | - | (no status word) | - | `DyadicRec.lean` (All.lean, header) | - |
| T7 | - | (no status word) | - | **none** | - |
| T8 | `slack_report` | (no status word) | - | **none** | `slack_report` **no** |
| T9 | `dyadicRec`, `regime_split`, `guard_collapse` | HARVESTED · NOT-YET | `DyadicRec.lean` | `DyadicRec.lean` (All.lean, ledger) | `dyadicRec` yes, `regime_split` **no**, `guard_collapse` **no** |
| T10 | `interval_log_exp` | (no status word) | - | **none** | `interval_log_exp` **no** |

⚠️ **Modules on disk that NO ledger section names by path:** `Salt/Tactic/LogNum.lean` — their T-id comes only from their own header or `All.lean`.

### Adoption per landed surface (call sites outside `Salt/Tactic/`)

| module | T | surface name | sites | forms | files |
|---|---|---|---:|---|---|
| `AuditAxioms.lean` | T5 | `#audit_axioms` | 463 | command 463 | `MR/All.lean` 203, `HB/All.lean` 133, `Entropy/All.lean` 34, `TwinBar/All.lean` 29 (+21 files) |
| `CertEval.lean` | T1 | `Salt.CertEval.CMono` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.CPoly` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.Exp5` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.FstarC` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.J_Fstar_0_reflective` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.cJD` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.cJD_eq` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.evalJcal` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.evalJcal_FstarC_0` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.evalJcal_eq` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.toE` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.toPoly` | 0 | - | - |
| `CertEval.lean` | T1 | `Salt.CertEval.toPoly_FstarC` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.dyadic_cover_sum_le` | 1 | qualified 1 | `HB/Lemma10Seal.lean` 1 |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.dyadic_cover_sum_le_range` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.dyadic_interval_rec` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_half_range_le` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_inv_sqrt_two_le` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_sqrt_two_pow_le` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_sum_le_bot` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_sum_le_bot_Icc` | 2 | qualified 2 | `HB/Lemma10Seal.lean` 1, `MR/TLegPreamble.lean` 1 |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_sum_le_top` | 0 | - | - |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_sum_le_top_Icc` | 1 | qualified 1 | `MR/TLegPreamble.lean` 1 |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.geom_two_pow_range_le` | 1 | qualified 1 | `HB/Lemma10Seal.lean` 1 |
| `DyadicRec.lean` | T6,T9 | `Salt.Tactic.mem_dyadic_block` | 1 | qualified 1 | `HB/Lemma10Seal.lean` 1 |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.eventually_add_le` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.eventually_finset_sum_le` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.eventually_ge_of_tendsto_gt` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.eventually_le_of_eventually_le_const` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.eventually_le_of_tendsto_zero` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.eventually_lt_of_eventually_le_const` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.eventually_sum_lt_of_pieces` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `Salt.Tactic.exists_forall_ge_of_eventually` | 0 | - | - |
| `EventuallyBudget.lean` | T2 | `eventually_budget` | 0 | - | - |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.exp_nat_eq_pow` | 0 | - | - |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.exp_nat_le_of_pow_le` | 27 | qualified 27 | `MR/FarStar.lean` 5, `MR/StrideDoorAllGrades.lean` 3, `Entropy/Chowla/Step.lean` 2, `Entropy/Chowla/StrideDecrement.lean` 2 (+13 files) |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.exp_nat_lt_of_pow_lt` | 9 | qualified 9 | `Entropy/Chowla/GoldbachEnergyKcH.lean` 3, `MR/MultShiu.lean` 2, `MR/S16ProducersH.lean` 2, `HB/L2cELT1.lean` 1 (+1 files) |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.le_exp_nat_of_le_pow` | 75 | qualified 75 | `MR/ThmA2Linear.lean` 18, `MR/StrideDoorAllGrades.lean` 8, `MR/ThmA2Rows.lean` 8, `MR/A3Middle.lean` 4 (+22 files) |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.log_le_nat_of_le_pow` | 34 | qualified 34 | `HB/CrownTheorem1.lean` 3, `Goldbach/RowsLive.lean` 2, `MR/LFunctionInvShallow.lean` 2, `MR/M4ClosureRepair.lean` 2 (+20 files) |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.lt_exp_nat_of_lt_pow` | 4 | qualified 4 | `MR/MRTPropA3.lean` 2, `MR/A4FMidRange.lean` 1, `MR/T0BandCapFree.lean` 1 |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.nat_le_log_of_pow_le` | 21 | qualified 21 | `HB/CrownTheorem1.lean` 4, `MR/M4ArithZeroLinear.lean` 4, `HB/L2cERT2.lean` 2, `Chen/WindowMembership.lean` 1 (+10 files) |
| `LogNum.lean` | T3 | `Salt.Tactic.LogNum.le_log_two_pow` | 0 | - | - |
| `LogNum.lean` | T3 | `Salt.Tactic.LogNum.log_eq_nat_mul_log` | 0 | - | - |
| `LogNum.lean` | T3 | `Salt.Tactic.LogNum.log_two_pow_le` | 0 | - | - |
| `LogNum.lean` | T3 | `Salt.Tactic.LogNum.log_two_pow_lt` | 0 | - | - |
| `LogNum.lean` | T3 | `Salt.Tactic.LogNum.lt_log_two_pow` | 0 | - | - |
| `NlinarithSuggest.lean` | T3 | `nlinarith?` | 0 | - | - |

`#audit_axioms` in detail: **463 commands auditing 9211 identifiers** across 25 files; in the `All.lean` ledgers **456 commands, 9204 identifiers**.

**Landed surface with ZERO call sites outside `Salt/Tactic/` (36) — each is a finding, not a defect of the count:** `Salt.CertEval.CMono`, `Salt.CertEval.CPoly`, `Salt.CertEval.Exp5`, `Salt.CertEval.FstarC`, `Salt.CertEval.J_Fstar_0_reflective`, `Salt.CertEval.cJD`, `Salt.CertEval.cJD_eq`, `Salt.CertEval.evalJcal`, `Salt.CertEval.evalJcal_FstarC_0`, `Salt.CertEval.evalJcal_eq`, `Salt.CertEval.toE`, `Salt.CertEval.toPoly`, `Salt.CertEval.toPoly_FstarC`, `Salt.Tactic.dyadic_cover_sum_le_range`, `Salt.Tactic.dyadic_interval_rec`, `Salt.Tactic.geom_half_range_le`, `Salt.Tactic.geom_inv_sqrt_two_le`, `Salt.Tactic.geom_sqrt_two_pow_le`, `Salt.Tactic.geom_sum_le_bot`, `Salt.Tactic.geom_sum_le_top`, `Salt.Tactic.eventually_add_le`, `Salt.Tactic.eventually_finset_sum_le`, `Salt.Tactic.eventually_ge_of_tendsto_gt`, `Salt.Tactic.eventually_le_of_eventually_le_const`, `Salt.Tactic.eventually_le_of_tendsto_zero`, `Salt.Tactic.eventually_lt_of_eventually_le_const`, `Salt.Tactic.eventually_sum_lt_of_pieces`, `Salt.Tactic.exists_forall_ge_of_eventually`, `eventually_budget`, `Salt.Tactic.exp_nat_eq_pow`, `Salt.Tactic.LogNum.le_log_two_pow`, `Salt.Tactic.LogNum.log_eq_nat_mul_log`, `Salt.Tactic.LogNum.log_two_pow_le`, `Salt.Tactic.LogNum.log_two_pow_lt`, `Salt.Tactic.LogNum.lt_log_two_pow`, `nlinarith?`

**Positive controls (the seat's measurement at main `1a5e85e1`: `git grep -c -F` per qualified name outside `Salt/Tactic`, summed = 24):**

| name | at base (seat, lines) | here: qualified tokens | here: all forms |
|---|---:|---:|---:|
| `Salt.Tactic.le_exp_nat_of_le_pow` | 11 | 75 | 75 |
| `Salt.Tactic.exp_nat_le_of_pow_le` | 4 | 27 | 27 |
| `Salt.Tactic.log_le_nat_of_le_pow` | 5 | 34 | 34 |
| `Salt.Tactic.nat_le_log_of_pow_le` | 4 | 21 | 21 |

## 2. Tactic usage (first token of each tactic line)

319634 tactic lines. Top 30:

| # | tactic | lines | share |
|---:|---|---:|---:|
| 1 | `have` | 141201 | 44.2% |
| 2 | `rw` | 51171 | 16.0% |
| 3 | `exact` | 18163 | 5.7% |
| 4 | `intro` | 14725 | 4.6% |
| 5 | `refine` | 13304 | 4.2% |
| 6 | `linarith` | 11271 | 3.5% |
| 7 | `obtain` | 9185 | 2.9% |
| 8 | `calc` | 8113 | 2.5% |
| 9 | `set` | 5762 | 1.8% |
| 10 | `simp` | 5256 | 1.6% |
| 11 | `apply` | 4607 | 1.4% |
| 12 | `nlinarith` | 3574 | 1.1% |
| 13 | `unfold` | 2706 | 0.8% |
| 14 | `exact_mod_cast` | 2617 | 0.8% |
| 15 | `ring` | 2269 | 0.7% |
| 16 | `rcases` | 2170 | 0.7% |
| 17 | `push_cast` | 2126 | 0.7% |
| 18 | `field_simp` | 1988 | 0.6% |
| 19 | `by_cases` | 1685 | 0.5% |
| 20 | `rwa` | 1667 | 0.5% |
| 21 | `omega` | 1523 | 0.5% |
| 22 | `norm_num` | 1486 | 0.5% |
| 23 | `show` | 1277 | 0.4% |
| 24 | `classical` | 1273 | 0.4% |
| 25 | `rintro` | 1170 | 0.4% |
| 26 | `congr` | 999 | 0.3% |
| 27 | `simpa` | 848 | 0.3% |
| 28 | `positivity` | 833 | 0.3% |
| 29 | `constructor` | 670 | 0.2% |
| 30 | `haveI` | 577 | 0.2% |

### Per method family (top 8 each)

| family | tactic lines | top tactics |
|---|---:|---|
| circle method / Fourier | 2728 | `have` 958, `rw` 598, `refine` 214, `exact` 153, `intro` 136, `ring` 79, `simp` 71, `calc` 68 |
| entropy decrement | 15933 | `have` 6491, `rw` 2800, `exact` 1023, `intro` 588, `refine` 564, `linarith` 479, `simp` 464, `calc` 391 |
| large sieve | 1719 | `have` 560, `rw` 379, `intro` 108, `refine` 104, `exact` 101, `simp` 56, `apply` 53, `calc` 48 |
| Selberg/Brun sieve | 70965 | `have` 30517, `rw` 12195, `exact` 3822, `intro` 3290, `calc` 2302, `apply` 2297, `refine` 1692, `linarith` 1505 |
| Bombieri-Vinogradov / Siegel-Walfisz | 35300 | `have` 15723, `rw` 6588, `exact` 1888, `intro` 1449, `refine` 1439, `linarith` 1109, `calc` 1107, `set` 888 |
| zero-density / zero-free regions | 13846 | `have` 6385, `rw` 2434, `exact` 702, `intro` 621, `linarith` 593, `refine` 443, `set` 408, `calc` 379 |
| character sums / L-functions | 66862 | `have` 28697, `rw` 10303, `exact` 4186, `refine` 3750, `intro` 3497, `obtain` 2422, `linarith` 2339, `calc` 1504 |
| exponential sums | 8307 | `have` 3163, `rw` 1697, `exact` 504, `intro` 410, `refine` 390, `linarith` 237, `set` 228, `simp` 209 |
| Mertens / PNT-type | 3298 | `have` 1530, `rw` 559, `exact` 173, `linarith` 147, `intro` 127, `refine` 103, `apply` 93, `simp` 73 |
| certificates / explicit numerics | 129 | `exact` 22, `rw` 22, `have` 13, `obtain` 10, `simp` 10, `refine` 8, `intro` 6, `rintro` 6 |
| explog/lognum numeral tactic | 106 | `have` 33, `rw` 20, `exact` 15, `intro` 6, `filter_upwards` 5, `refine` 5, `nlinarith` 4, `calc` 3 |
| Matomaki-Radziwill / Halasz (short intervals) | 128686 | `have` 60048, `rw` 17437, `exact` 7274, `refine` 7003, `intro` 6247, `linarith` 5994, `obtain` 4887, `calc` 2421 |
| (no family) | 29620 | `have` 11449, `rw` 5292, `exact` 1797, `intro` 1637, `obtain` 1013, `refine` 984, `set` 905, `calc` 888 |

## 3. Macro candidates (repeated normalised tactic blocks)

Blocks of 3–20 consecutive tactic lines, repeated ≥ 5 times (non-overlapping) in ≥ 3 files, maximal only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name (numbered by first appearance, so equal blocks bind alike), `#` = a numeral. 1606 candidates; top 25 by the UPPER-BOUND saving.

⚠️ **Lines saved is an UPPER bound, never a price:** a macro call is ≥ 1 line; sites whose placeholders bind differently may not share a macro; generic blocks may cost more to name than to repeat.

**1.** 14 lines × 25 occurrences in 17 files · lines saved ≤ **325** · e.g. `Salt/MR/DoorReceipt.lean:315` · `Salt/MR/FlatDoorEpsChain.lean:825`

```lean
· intro $1 $2 $3 $4 _ _
have $5 := $6 $1 $3 $4
have $7 : (# : ℝ) ≤ arcDen # $1 := one_le_arcDen_of_regime ($8 := $8) $3
have $9 : # ≤ $1 := by
have : (# : ℝ) ≤ ($1 : ℝ) := by nlinarith
exact_mod_cast this
exact blockLen_le $1 $2 $9
· intro $1 $2 $3 $4 _ _
exact blockLen_narrow ($8 := $8) $3 ($6 $1 $3 $4)
· intro $1 $2 $3 $4 $10 _
exact blockLen_drift ($8 := $8) $3 $10 ($6 $1 $3 $4)
· intro $1 $3 $4
have $11 := $12 $1 $3 $4
have $13 : (# : ℝ) ≤ strataResidual $1 :=
```

**2.** 12 lines × 27 occurrences in 14 files · lines saved ≤ **297** · e.g. `Salt/MR/DoorReceipt.lean:652` · `Salt/MR/FlatDoorEpsChain.lean:1031`

```lean
have $1 : s15Arm $2 $3 $4.Hhi $4.ω ≤ $4.x := by omega
have $5 : $6 $4.Hhi $4.ω ≤ $4.x := by omega
have $7 : $8 ≤ $9 := le_trans (le_max_left _ _) $10
have $11 : $4.Hlo = $9 := by
have : max $8 $9 = $9 := max_eq_right $7
omega
have $12 : loglogFloor50 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) $10
omega
have $13 : arcFloor36 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) $10
omega
```

**3.** 11 lines × 28 occurrences in 15 files · lines saved ≤ **280** · e.g. `Salt/MR/DoorReceipt.lean:653` · `Salt/MR/FlatDoorAllGradesBand.lean:1092` · ⚠️ shares source lines with #2

```lean
have $1 : $2 $3.Hhi $3.ω ≤ $3.x := by omega
have $4 : $5 ≤ $6 := le_trans (le_max_left _ _) $7
have $8 : $3.Hlo = $6 := by
have : max $5 $6 = $6 := max_eq_right $4
omega
have $9 : loglogFloor50 ≤ $3.Hlo := by
have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) $7
omega
have $10 : arcFloor36 ≤ $3.Hlo := by
have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) $7
omega
```

**4.** 13 lines × 22 occurrences in 9 files · lines saved ≤ **264** · e.g. `Salt/MR/S15Compose.lean:867` · `Salt/MR/S16Budget.lean:1735` · ⚠️ shares source lines with #2, #3

```lean
have $1 : s15Arm $2 $3 $4.Hhi $4.ω ≤ $4.x := by omega
have $5 : $6 $4.Hhi $4.ω ≤ $4.x := by omega
have $7 : $8 ≤ $9 := le_trans (le_max_left _ _) $10
have $11 : $4.Hlo = $9 := by
have : max $8 $9 = $9 := max_eq_right $7
omega
have $12 : loglogFloor50 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) $10
omega
have $13 : arcFloor36 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) $10
omega
refine ⟨$4, $14, $11, $5, $15, ?_⟩
```

**5.** 19 lines × 13 occurrences in 8 files · lines saved ≤ **234** · e.g. `Salt/MR/S15Compose.lean:1313` · `Salt/MR/S16Budget.lean:1735` · ⚠️ shares source lines with #2, #3, #4

```lean
have $1 : s15Arm $2 $3 $4.Hhi $4.ω ≤ $4.x := by omega
have $5 : $6 $4.Hhi $4.ω ≤ $4.x := by omega
have $7 : $8 ≤ $9 := le_trans (le_max_left _ _) $10
have $11 : $4.Hlo = $9 := by
have : max $8 $9 = $9 := max_eq_right $7
omega
have $12 : loglogFloor50 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) $10
omega
have $13 : arcFloor36 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) $10
omega
refine ⟨$4, $14, $11, $5, $15, ?_⟩
intro $16 $17
obtain ⟨$18, $19, $20, $21⟩ := $22 $16 $17.mfloor
intro $23
obtain ⟨-, $24⟩ := regime_Hfloor_of_loglogFloor50 $12
obtain ⟨-, $25⟩ := regime_Hfloor_of_loglogFloor50 (le_trans $12 $4.hHlohi)
have $26 : Real.log (Real.log (($4.Hhi : ℕ) : ℝ))
```

**6.** 8 lines × 33 occurrences in 17 files · lines saved ≤ **231** · e.g. `Salt/MR/DoorReceipt.lean:653` · `Salt/MR/FlatDoorAllGradesBand.lean:1092` · ⚠️ shares source lines with #2, #3, #4, #5

```lean
have $1 : $2 $3.Hhi $3.ω ≤ $3.x := by omega
have $4 : $5 ≤ $6 := le_trans (le_max_left _ _) $7
have $8 : $3.Hlo = $6 := by
have : max $5 $6 = $6 := max_eq_right $4
omega
have $9 : loglogFloor50 ≤ $3.Hlo := by
have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) $7
omega
```

**7.** 7 lines × 38 occurrences in 22 files · lines saved ≤ **228** · e.g. `Salt/MR/DoorReceipt.lean:654` · `Salt/MR/FlatDoorAllGradesBand.lean:1093` · ⚠️ shares source lines with #2, #3, #4, #5, #6

```lean
have $1 : $2 ≤ $3 := le_trans (le_max_left _ _) $4
have $5 : $6.Hlo = $3 := by
have : max $2 $3 = $3 := max_eq_right $1
omega
have $7 : loglogFloor50 ≤ $6.Hlo := by
have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) $4
omega
```

**8.** 6 lines × 45 occurrences in 24 files · lines saved ≤ **225** · e.g. `Salt/MR/DoorReceipt.lean:474` · `Salt/MR/FlatDoorAllGradesBand.lean:914`

```lean
set $1 : ℝ := s12DeltaSock $2 $3 with $4
have $5 : # < $1 := s12DeltaSock_pos $6 $7
have $8 : $1 ^ # = $2 / (# * $3) := s12DeltaSock_sq $6 $7
set $9 : ℝ := doorRhoOfDelta $1 with $10
have $11 : # < $9 := doorRhoOfDelta_pos $5.ne'
have $12 : $9 ≤ # := doorRhoOfDelta_le_one $1
```

**9.** 6 lines × 44 occurrences in 23 files · lines saved ≤ **220** · e.g. `Salt/MR/DoorReceipt.lean:552` · `Salt/MR/FlatDoorAllGradesBand.lean:1008`

```lean
have $1 : (# : ℝ) < # * $2 := by linarith
have $3 : # * $4 ^ # = $5 / (# * $2) := by
rw [$6]
field_simp
ring
linarith [$7, $8, $3.le, $3.ge]
```

**10.** 15 lines × 15 occurrences in 4 files · lines saved ≤ **210** · e.g. `Salt/MR/M4LadderLinear.lean:231` · `Salt/MR/M4MeanSq.lean:659`

```lean
have $1 : Real.exp # ≤ $2 := le_trans exp_one_le_exp_exp_one $3
have $4 : (# : ℝ) ≤ $2 := le_of_lt (lt_of_lt_of_le exp_exp_one_gt_three $3)
have $5 : (# : ℝ) < $2 := by linarith
have $6 : (# : ℝ) < $7 := by linarith
have $8 : (# : ℝ) < Real.log $2 := lt_of_lt_of_le (Real.exp_pos #) $9
have $10 : $2 ≤ ($11 : ℝ) := le_of_eq $12.symm
have $13 : (# : ℝ) ≤ ($11 : ℝ) := by rw [$12]; linarith
have $14 : # ≤ $11 := by exact_mod_cast $13
have $15 : ($16 : ℝ) = # * $2 := by rw [$17]; push_cast; rw [$12]
have $18 : # * $11 ≤ $16 := le_of_eq $17.symm
have $19 : ($16 : ℝ) ≤ # * ($11 : ℝ) := by rw [$15, $12]
have $20 : $2 ≤ ($16 : ℝ) := by rw [$15]; linarith
have $21 : ($16 : ℝ) ≤ # * $2 := le_of_eq $15
have $22 : ($16 : ℝ) ≤ # * ($11 : ℝ) := by rw [$15, $12]; linarith
have $23 : ∀ $24 ∈ ramI ($25 $2 theta293) $26 $27, # ≤ ramRbot ($25 $2 theta293) $11 $24 :=
```

**11.** 15 lines × 15 occurrences in 4 files · lines saved ≤ **210** · e.g. `Salt/MR/M4DoorClose.lean:424` · `Salt/MR/M4DoorClosePool.lean:275`

```lean
subst $1
subst $2
haveI : NeZero $3 := ⟨$4.ne'⟩
have $5 : (# : ℝ) < (($6 : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) $7
have $8 : (# : ℝ) ≤ Real.exp (Real.exp #) := by
have $9 := Real.add_one_le_exp (Real.exp #)
have $10 := Real.exp_pos #
linarith
have $11 : # ≤ $6 := by
have : (# : ℝ) ≤ (($6 : ℕ) : ℝ) := le_trans $8 $7
exact_mod_cast this
have $12 : (# : ℝ) ≤ Real.exp # := by
have := Real.add_one_le_exp (# : ℝ); linarith
have $13 : (# : ℝ) < Real.log (($6 : ℕ) : ℝ) := by linarith
have $14 : Real.exp # ≤ Real.log (($6 : ℕ) : ℝ) :=
```

**12.** 14 lines × 15 occurrences in 8 files · lines saved ≤ **195** · e.g. `Salt/MR/S15Compose.lean:867` · `Salt/MR/S16Budget.lean:1735` · ⚠️ shares source lines with #2, #3, #4, #5, #6, #7

```lean
have $1 : s15Arm $2 $3 $4.Hhi $4.ω ≤ $4.x := by omega
have $5 : $6 $4.Hhi $4.ω ≤ $4.x := by omega
have $7 : $8 ≤ $9 := le_trans (le_max_left _ _) $10
have $11 : $4.Hlo = $9 := by
have : max $8 $9 = $9 := max_eq_right $7
omega
have $12 : loglogFloor50 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) $10
omega
have $13 : arcFloor36 ≤ $4.Hlo := by
have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) $10
omega
refine ⟨$4, $14, $11, $5, $15, ?_⟩
intro $16 $17
```

**13.** 9 lines × 23 occurrences in 20 files · lines saved ≤ **184** · e.g. `Salt/MR/DoorReceipt.lean:928` · `Salt/MR/DoorReceiptSiegelFree.lean:117`

```lean
linarith
have $1 : $2 ≤ flatDesignBase $3 := by
have $4 : Real.exp (# * $3) + # ≤ Real.exp (Real.exp (# * $3)) := Real.add_one_le_exp _
have $5 : (($2 : ℕ) : ℝ) ≤ Real.exp (Real.exp (# * $3)) := by linarith
have $6 := le_trans $5 (Nat.le_ceil (Real.exp (Real.exp (# * $3))))
rw [flatDesignBase]; exact_mod_cast $6
have $7 : (# : ℝ) ≤ $3 := by linarith
have $8 : KlevF $3 ≤ # * flatDoorM $3 := KlevF_le_wideCeiling $7
obtain ⟨$9, $10, $11⟩ := $12 (KlevF $3)
```

**14.** 8 lines × 26 occurrences in 23 files · lines saved ≤ **182** · e.g. `Salt/MR/DoorReceipt.lean:928` · `Salt/MR/DoorReceiptSiegelFree.lean:117` · ⚠️ shares source lines with #13

```lean
linarith
have $1 : $2 ≤ flatDesignBase $3 := by
have $4 : Real.exp (# * $3) + # ≤ Real.exp (Real.exp (# * $3)) := Real.add_one_le_exp _
have $5 : (($2 : ℕ) : ℝ) ≤ Real.exp (Real.exp (# * $3)) := by linarith
have $6 := le_trans $5 (Nat.le_ceil (Real.exp (Real.exp (# * $3))))
rw [flatDesignBase]; exact_mod_cast $6
have $7 : (# : ℝ) ≤ $3 := by linarith
have $8 : KlevF $3 ≤ # * flatDoorM $3 := KlevF_le_wideCeiling $7
```

**15.** 5 lines × 45 occurrences in 24 files · lines saved ≤ **180** · e.g. `Salt/MR/DoorReceipt.lean:553` · `Salt/MR/FlatDoorAllGradesBand.lean:1009` · ⚠️ shares source lines with #9

```lean
have $1 : # * $2 ^ # = $3 / (# * $4) := by
rw [$5]
field_simp
ring
linarith [$6, $7, $1.le, $1.ge]
```

**16.** 10 lines × 19 occurrences in 16 files · lines saved ≤ **171** · e.g. `Salt/MR/DoorReceipt.lean:928` · `Salt/MR/DoorReceiptSiegelFree.lean:117` · ⚠️ shares source lines with #13, #14

```lean
linarith
have $1 : $2 ≤ flatDesignBase $3 := by
have $4 : Real.exp (# * $3) + # ≤ Real.exp (Real.exp (# * $3)) := Real.add_one_le_exp _
have $5 : (($2 : ℕ) : ℝ) ≤ Real.exp (Real.exp (# * $3)) := by linarith
have $6 := le_trans $5 (Nat.le_ceil (Real.exp (Real.exp (# * $3))))
rw [flatDesignBase]; exact_mod_cast $6
have $7 : (# : ℝ) ≤ $3 := by linarith
have $8 : KlevF $3 ≤ # * flatDoorM $3 := KlevF_le_wideCeiling $7
obtain ⟨$9, $10, $11⟩ := $12 (KlevF $3)
obtain ⟨$13, $14⟩ := $11 $3 $15 $16 $17 $8
```

**17.** 3 lines × 84 occurrences in 26 files · lines saved ≤ **168** · e.g. `Salt/MR/DoorReceipt.lean:477` · `Salt/MR/FlatDoorAllGradesBand.lean:917` · ⚠️ shares source lines with #8

```lean
set $1 : ℝ := doorRhoOfDelta $2 with $3
have $4 : # < $1 := doorRhoOfDelta_pos $5.ne'
have $6 : $1 ≤ # := doorRhoOfDelta_le_one $2
```

**18.** 15 lines × 12 occurrences in 5 files · lines saved ≤ **168** · e.g. `Salt/MR/M4BaseNarrow.lean:210` · `Salt/MR/M4ChiSummed.lean:340`

```lean
refine le_trans (Finset.sum_le_sum $1) ?_
rw [← Finset.mul_sum]
exact mul_le_mul_of_nonneg_left $2 (Nat.cast_nonneg _)
have $3 : ((($4 + $5 : ℕ)) : ℝ) ≤ # * ($6 : ℝ) + # := by
have $7 : $4 + $5 ≤ # * $6 + # := by omega
have := (Nat.cast_le ($8 := ℝ)).mpr $7
push_cast at this ⊢
linarith
have $9 : ((($4 + $5 : ℕ)) : ℝ) ≤ # * ((($6 + $5 : ℕ)) : ℝ) := by
have $7 : $4 + $5 ≤ # * ($6 + $5) := by omega
have := (Nat.cast_le ($8 := ℝ)).mpr $7
push_cast at this ⊢
linarith
have $10 : (# : ℝ) ≤ ((# ^ $11 : ℕ) : ℝ) ^ # := sq_nonneg _
have $12 : (# : ℝ) ≤ ((# ^ $11 : ℕ) : ℝ) ^ # / ((($6 + $5 : ℕ)) : ℝ) := by positivity
```

**19.** 5 lines × 40 occurrences in 24 files · lines saved ≤ **160** · e.g. `Salt/MR/DoorReceipt.lean:559` · `Salt/MR/FlatDoorAllGradesBand.lean:1015`

```lean
have $1 : # * $2 * ($3 / (# * $2)) = $3 / # := by
field_simp
ring
rw [$1]
linarith [$4]
```

**20.** 15 lines × 11 occurrences in 9 files · lines saved ≤ **154** · e.g. `Salt/MR/DoorReceipt.lean:946` · `Salt/MR/DoorReceiptSiegelFree.lean:135`

```lean
have $1 : (# : ℚ) / # ≤ $2.eps := by rw [$3]; exact hεpin
have $4 : Real.log (($2.x : ℕ) : ℝ) ≤ # / ($2.eps : ℝ) * (($2.Hhi : ℕ) : ℝ) := by
rw [$3]; exact $5
have $6 : # ≤ flatDoorM $7 := flatDoorM_one_le $8
have $9 : (# : ℝ) / # ≤ ($2.eps : ℝ) := by
rw [$3]
have $10 := (Rat.cast_le ($11 := ℝ)).mpr hεpin
rw [show (((# : ℚ) / # : ℚ) : ℝ) = # / # by norm_num] at $10
exact $10
have $12 : (# : ℝ) ≤ Real.log (Real.log ($2.Hlo : ℝ)) := by nlinarith [$13, $14]
have $15 : loglogFloor50 ≤ $2.Hlo := by rw [$16]; exact flatWitFloor_ll _ _ _ _
have $17 : Real.exp (# * $7) ≤ Real.log (($2.Hlo : ℕ) : ℝ) := by
rw [$16]; exact flatWitFloor_log_ge $14
have $18 : cofkRThr $19 $20 $21 $22 ≤ Real.log (($2.Hlo : ℕ) : ℝ) := by
linarith [$23, $17, $24]
```

**21.** 20 lines × 8 occurrences in 7 files · lines saved ≤ **152** · e.g. `Salt/Chen/ChenFinal2.lean:161` · `Salt/Chen/PriceOne.lean:367`

```lean
have $1 : # * # ^ (Nat.clog # $2 - #) = # ^ Nat.clog # $2 := by
rw [← pow_succ']
congr #
omega
rw [← $1]
exact Nat.mul_le_mul (le_refl #) (le_of_lt $3)
have $4 : $5 ^ ((# : ℝ)) ≤ ((# ^ $6 : ℕ) : ℝ) := by
refine le_trans $7 ?_
exact_mod_cast $8
have $9 : ((# ^ $6 : ℕ) : ℝ) ≤ # * $5 ^ ((# : ℝ)) := by
have $10 : ((# ^ $6 : ℕ) : ℝ) ≤ # * ($2 : ℝ) := by exact_mod_cast $11
linarith
have $12 : $5 ^ ((# : ℝ)) = $5 * $5 ^ ((# : ℝ)) := by
have $13 := Real.rpow_add $14 # #
rw [Real.rpow_one] at $13
rw [show (# : ℝ) = # + # by norm_num, $13]
have $15 : (# : ℝ) ≤ $5 ^ ((# : ℝ)) := Real.rpow_nonneg $16 _
have $17 : # * $5 ^ ((# : ℝ)) ≤ $18 ^ ((# : ℝ)) := by
have $19 : $5 ^ ((# : ℝ)) ≤ ((# : ℝ) / #) ^ ((# : ℝ)) * $18 ^ ((# : ℝ)) := by
calc $5 ^ ((# : ℝ)) ≤ (# / # * $18) ^ ((# : ℝ)) :=
```

**22.** 20 lines × 8 occurrences in 7 files · lines saved ≤ **152** · e.g. `Salt/Chen/ChenFinal2.lean:103` · `Salt/Chen/PriceOne.lean:309`

```lean
have $1 : ($2 : ℝ) < (($2 / # + # : ℕ) : ℝ) * # := by exact_mod_cast $3
have $4 : (($2 / # + # : ℕ) : ℝ) ≤ ($5 : ℝ) * ($6 : ℝ) := by exact_mod_cast $7
push_cast at $1 $4
have $8 : ($2 : ℝ) / # < ($5 : ℝ) * ($6 : ℝ) := by linarith
have $9 : Real.log (($2 : ℝ) / #) ≤ $10 := Real.log_le_log (by linarith) $8.le
rw [Real.log_div (ne_of_gt $11) (by norm_num : (# : ℝ) ≠ #)] at $9
have $12 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $13 : $10 ≤ Real.log $2 + # := by
have $3 : $10 ≤ Real.log (# * ($2 : ℝ)) := Real.log_le_log $14 $15
rw [Real.log_mul (by norm_num : (# : ℝ) ≠ #) (ne_of_gt $11)] at $3
have $16 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $17 : (# : ℝ) ≤ $10 := by linarith
have $18 : (# : ℝ) ≤ $10 := by linarith
have $19 : (# : ℝ) < $10 := by linarith
have $20 : (# : ℝ) ≤ $10 := by linarith
have $21 : (# : ℝ) ≤ $10 := by linarith
```

**23.** 4 lines × 50 occurrences in 17 files · lines saved ≤ **150** · e.g. `Salt/MR/DoorReceipt.lean:288` · `Salt/MR/FlatDoorEpsChain.lean:798`

```lean
have $1 : ∀ $2 : ℕ, $3.Hlo ≤ $2 → $2 ≤ $3.Hhi → # * arcDen # $2 ^ # ≤ ($2 : ℝ) := by
intro $2 $4 $5
have $6 := $7 $2 $4 $5
have $8 : (# : ℝ) ≤ arcDen # $2 := one_le_arcDen_of_regime ($3 := $3) $4
```

**24.** 6 lines × 30 occurrences in 26 files · lines saved ≤ **150** · e.g. `Salt/MR/DoorReceipt.lean:928` · `Salt/MR/DoorReceiptSiegelFree.lean:117` · ⚠️ shares source lines with #13, #14, #16

```lean
linarith
have $1 : $2 ≤ flatDesignBase $3 := by
have $4 : Real.exp (# * $3) + # ≤ Real.exp (Real.exp (# * $3)) := Real.add_one_le_exp _
have $5 : (($2 : ℕ) : ℝ) ≤ Real.exp (Real.exp (# * $3)) := by linarith
have $6 := le_trans $5 (Nat.le_ceil (Real.exp (Real.exp (# * $3))))
rw [flatDesignBase]; exact_mod_cast $6
```

**25.** 7 lines × 25 occurrences in 10 files · lines saved ≤ **150** · e.g. `Salt/MR/M4RowAssemblyLinear.lean:5070` · `Salt/MR/M4RowSpineLinear.lean:1356`

```lean
have $1 : # < $2 := $3.2.2.2.1
have $4 : # < $5 := $3.2.2.2.2.2.2.2.1
haveI : NeZero $2 := ⟨$1.ne'⟩
have $6 := $7 $8 $9 $2 $10 $5 $11 $3
have $12 : # < $5 + $11 := lt_of_lt_of_le $4 (Nat.le_add_right $5 $11)
have $13 : (# : ℝ) < ((($5 + $11 : ℕ)) : ℝ) := by exact_mod_cast $12
have $14 : (((# * ($5 + $11) : ℕ)) : ℝ) ≤ # * ((($5 + $11 : ℕ)) : ℝ) := by push_cast; linarith
```

## Whitelist (data)

`abel` `absurd` `aesop` `all_goals` `and_intros` `any_goals` `apply` `apply?` `apply_fun` `apply_rules` `assumption` `assumption_mod_cast` `bound` `bound?` `by_cases` `by_contra` `by_contra!` `calc` `calc?` `cancel_denoms` `case` `cases` `cases'` `change` `choose` `classical` `clear` `congr` `congr!` `congrm` `constructor` `continuity` `contradiction` `contrapose` `contrapose!` `conv` `conv_lhs` `conv_rhs` `convert` `convert_to` `decide` `delta` `done` `dsimp` `erw` `eventually_budget` `exact` `exact?` `exact_fun_prop` `exact_mod_cast` `exacts` `exfalso` `exists` `existsi` `ext` `field_simp` `field_simp?` `filter_upwards` `fin_cases` `first` `focus` `fun_prop` `funext` `gcongr` `gcongr?` `gcongr_discharger` `generalize` `group` `have` `haveI` `induction` `induction'` `infer_instance` `interval_cases` `intro` `intros` `iterate` `left` `let` `letI` `lift` `linarith` `linarith!` `linear_combination` `measurability` `mod_cast` `mono` `native_decide` `next` `nlinarith` `nlinarith!` `nlinarith?` `noncomm_ring` `norm_cast` `norm_num` `norm_num1` `norm_num?` `nth_rewrite` `nth_rw` `obtain` `omega` `on_goal` `pick_goal` `polyrith` `positivity` `positivity?` `push_cast` `push_neg` `qify` `rcases` `refine` `refine'` `refine_lift` `rel` `rename_i` `repeat` `rewrite` `rfl` `right` `ring` `ring1` `ring_nf` `rintro` `rotate_left` `rsuffices` `rw` `rw?` `rwa` `set` `show` `simp` `simp?` `simp_all` `simp_arith` `simp_rw` `simpa` `simpa?` `skip` `sorry` `specialize` `split` `split_ands` `split_ifs` `stop` `subst` `subst_vars` `suffices` `swap` `symm` `tauto` `trans` `trivial` `try` `unfold` `unfold?` `unfold_let` `use` `with_reducible` `wlog` `zify`

Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): `Salt/Tactic/AuditAxioms.lean`, `Salt/Tactic/NlinarithSuggest.lean`.
