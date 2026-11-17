# THE TACTICS CATALOGUE — by machine (O13 item 4)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/tactics_catalogue.py` · staleness gate: `python3 scripts/tactics_catalogue.py --check`.
> Base: last commit touching `Salt/` = `6b3cfc6c` · source digest `30033e42e90242cc` (the same digest as items 1–3).
> Receipt: files 1414 · decls 23441 · with_body 23441 · tactic_lines 303641 · runs 35658 · blocks 1264.

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
| T3 | `budget_num` | LANDED | `ExpLogNum.lean`, `NlinarithSuggest.lean` | `ExpLogNum.lean` (All.lean, header, ledger); `LogNum.lean` (All.lean, header); `NlinarithSuggest.lean` (All.lean, header, ledger) | `budget_num` **no** |
| T4 | `salt_cast` | NOT-YET | - | **none** | `salt_cast` **no** |
| T5 | `#audit_axioms` | LANDED | `AuditAxioms.lean` | `AuditAxioms.lean` (All.lean, ledger) | `#audit_axioms` yes |
| T6 | - | NOT-YET | - | `DyadicRec.lean` (All.lean, header) | - |
| T7 | - | NOT-YET | - | **none** | - |
| T8 | `slack_report` | NOT-YET | - | **none** | `slack_report` **no** |
| T9 | `dyadicRec`, `regime_split`, `guard_collapse` | HARVESTED · NOT-YET | `DyadicRec.lean` | `DyadicRec.lean` (All.lean, ledger) | `dyadicRec` yes, `regime_split` **no**, `guard_collapse` **no** |
| T10 | `interval_log_exp` | NOT-YET | - | **none** | `interval_log_exp` **no** |

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
| `ExpLogNum.lean` | T3 | `Salt.Tactic.le_exp_nat_of_le_pow` | 44 | qualified 44 | `MR/StrideDoorAllGrades.lean` 8, `MR/RegisterRepair.lean` 4, `MR/S13CapEps.lean` 4, `MR/S13CapGateLinearLH.lean` 4 (+19 files) |
| `ExpLogNum.lean` | T3 | `Salt.Tactic.log_le_nat_of_le_pow` | 33 | qualified 33 | `HB/CrownTheorem1.lean` 3, `Goldbach/RowsLive.lean` 2, `MR/LFunctionInvShallow.lean` 2, `MR/M4ClosureRepair.lean` 2 (+19 files) |
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
| `Salt.Tactic.le_exp_nat_of_le_pow` | 11 | 44 | 44 |
| `Salt.Tactic.exp_nat_le_of_pow_le` | 4 | 27 | 27 |
| `Salt.Tactic.log_le_nat_of_le_pow` | 5 | 33 | 33 |
| `Salt.Tactic.nat_le_log_of_pow_le` | 4 | 21 | 21 |

## 2. Tactic usage (first token of each tactic line)

303641 tactic lines. Top 30:

| # | tactic | lines | share |
|---:|---|---:|---:|
| 1 | `have` | 132442 | 43.6% |
| 2 | `rw` | 49088 | 16.2% |
| 3 | `exact` | 17462 | 5.8% |
| 4 | `intro` | 14057 | 4.6% |
| 5 | `refine` | 12779 | 4.2% |
| 6 | `linarith` | 10435 | 3.4% |
| 7 | `obtain` | 9159 | 3.0% |
| 8 | `calc` | 7809 | 2.6% |
| 9 | `set` | 5476 | 1.8% |
| 10 | `simp` | 5156 | 1.7% |
| 11 | `apply` | 4531 | 1.5% |
| 12 | `nlinarith` | 3341 | 1.1% |
| 13 | `unfold` | 2625 | 0.9% |
| 14 | `exact_mod_cast` | 2426 | 0.8% |
| 15 | `rcases` | 2129 | 0.7% |
| 16 | `ring` | 2065 | 0.7% |
| 17 | `push_cast` | 1961 | 0.6% |
| 18 | `field_simp` | 1864 | 0.6% |
| 19 | `by_cases` | 1635 | 0.5% |
| 20 | `rwa` | 1599 | 0.5% |
| 21 | `norm_num` | 1491 | 0.5% |
| 22 | `show` | 1268 | 0.4% |
| 23 | `omega` | 1266 | 0.4% |
| 24 | `classical` | 1247 | 0.4% |
| 25 | `rintro` | 1150 | 0.4% |
| 26 | `congr` | 930 | 0.3% |
| 27 | `simpa` | 921 | 0.3% |
| 28 | `positivity` | 792 | 0.3% |
| 29 | `constructor` | 654 | 0.2% |
| 30 | `ext` | 543 | 0.2% |

### Per method family (top 8 each)

| family | tactic lines | top tactics |
|---|---:|---|
| circle method / Fourier | 2726 | `have` 958, `rw` 597, `refine` 213, `exact` 153, `intro` 135, `ring` 79, `simp` 71, `calc` 68 |
| entropy decrement | 15149 | `have` 6100, `rw` 2662, `exact` 994, `intro` 565, `refine` 529, `simp` 462, `linarith` 447, `calc` 374 |
| large sieve | 1719 | `have` 560, `rw` 379, `intro` 108, `refine` 104, `exact` 101, `simp` 56, `apply` 53, `calc` 48 |
| Selberg/Brun sieve | 70444 | `have` 30316, `rw` 12099, `exact` 3801, `intro` 3244, `calc` 2288, `apply` 2287, `refine` 1691, `linarith` 1480 |
| Bombieri-Vinogradov / Siegel-Walfisz | 34755 | `have` 15480, `rw` 6455, `exact` 1868, `intro` 1433, `refine` 1418, `linarith` 1100, `calc` 1077, `set` 854 |
| zero-density / zero-free regions | 13609 | `have` 6263, `rw` 2384, `exact` 696, `intro` 614, `linarith` 576, `refine` 438, `set` 408, `calc` 379 |
| character sums / L-functions | 62535 | `have` 26239, `rw` 9881, `exact` 4058, `refine` 3590, `intro` 3337, `obtain` 2385, `linarith` 2136, `calc` 1437 |
| exponential sums | 8305 | `have` 3163, `rw` 1696, `exact` 504, `intro` 409, `refine` 391, `linarith` 237, `set` 228, `simp` 209 |
| Mertens / PNT-type | 3297 | `have` 1530, `rw` 557, `exact` 173, `linarith` 147, `intro` 127, `refine` 103, `apply` 93, `simp` 73 |
| certificates / explicit numerics | 129 | `exact` 22, `rw` 22, `have` 13, `obtain` 10, `simp` 10, `refine` 8, `intro` 6, `rintro` 6 |
| explog/lognum numeral tactic | 106 | `have` 33, `rw` 20, `exact` 15, `intro` 6, `filter_upwards` 5, `refine` 5, `nlinarith` 4, `calc` 3 |
| Matomaki-Radziwill / Halasz (short intervals) | 115548 | `have` 52489, `rw` 15922, `exact` 6701, `refine` 6555, `intro` 5745, `linarith` 5261, `obtain` 4978, `calc` 2200 |
| (no family) | 28822 | `have` 11183, `rw` 5141, `exact` 1746, `intro` 1562, `obtain` 972, `refine` 959, `set` 883, `calc` 866 |

## 3. Macro candidates (repeated normalised tactic blocks)

Blocks of 3–20 consecutive tactic lines, repeated ≥ 5 times (non-overlapping) in ≥ 3 files, maximal only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name (numbered by first appearance, so equal blocks bind alike), `#` = a numeral. 1264 candidates; top 25 by the UPPER-BOUND saving.

⚠️ **Lines saved is an UPPER bound, never a price:** a macro call is ≥ 1 line; sites whose placeholders bind differently may not share a macro; generic blocks may cost more to name than to repeat.

**1.** 3 lines × 54 occurrences in 47 files · lines saved ≤ **108** · e.g. `Salt/Entropy/Chowla/StrideCircle.lean:227` · `Salt/HB/Lemma10Chain.lean:358`

```lean
congr #
push_cast
ring
```

**2.** 6 lines × 19 occurrences in 7 files · lines saved ≤ **95** · e.g. `Salt/MR/M4SocketDischarge.lean:314` · `Salt/MR/M4SocketLinear.lean:256`

```lean
have $1 : # < $2 := $3.2.2.2.1
haveI : NeZero $2 := ⟨$1.ne'⟩
have $4 := $5 $6 $7 $2 $8 $9 $10 $3
have $11 : # ≤ $9 + $10 := by
exact_mod_cast (show (# : ℝ) ≤ ((($9 + $10 : ℕ)) : ℝ) by linarith [$4.X400])
exact $12 $2 $13 $14 ($9 + $10) (# * ($9 + $10)) rfl $4.X400 (by omega) le_rfl $4.C₁_one
```

**3.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:178` · `Salt/MR/M4SecondRoad.lean:555`

```lean
have $1 : # < # * $2.ω := by have := $2.hω; omega
have $3 : (# : ℝ) < ($2.ω : ℝ) := by
have $4 : # < $2.ω := by have := $2.hω; omega
exact_mod_cast $4
have $5 : $2.x / (# * $2.ω) ≤ $6 := by
rw [$7]
exact doorLadder_ge_x_div_four_omega ($8 := $8) $2.hω $9 (by omega)
have $10 : $6 ≤ $2.x := by
rw [$7]
exact doorLadder_le_start $11 ($12 + #)
have $13 : (# : ℝ) ≤ ($2.Hhi : ℝ) := by
have $4 : # ≤ $2.Hhi := le_trans $2.hHlo_floor $2.hHlohi
exact_mod_cast $4
have $14 : # * ($2.ω : ℝ) * ($2.Hhi : ℝ) ≤ ($2.x : ℝ) := regime_eight_omega_Hhi_le_x $2
have $15 : ($8 : ℝ) ≤ ($2.Hhi : ℝ) := by exact_mod_cast $16
have $17 : # * $2.ω * $8 ≤ $2.x := by
have $4 : (# : ℝ) * ($2.ω : ℝ) * ($8 : ℝ) ≤ ($2.x : ℝ) := by nlinarith [$14, $15, $3]
exact_mod_cast $4
have $18 : # * ($8 : ℝ) ≤ ($6 : ℝ) := by
have $19 : # * $8 ≤ $6 := by
```

**4.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:180` · `Salt/MR/M4SecondRoad.lean:557` · ⚠️ shares source lines with #3

```lean
have $1 : # < $2.ω := by have := $2.hω; omega
exact_mod_cast $1
have $3 : $2.x / (# * $2.ω) ≤ $4 := by
rw [$5]
exact doorLadder_ge_x_div_four_omega ($6 := $6) $2.hω $7 (by omega)
have $8 : $4 ≤ $2.x := by
rw [$5]
exact doorLadder_le_start $9 ($10 + #)
have $11 : (# : ℝ) ≤ ($2.Hhi : ℝ) := by
have $1 : # ≤ $2.Hhi := le_trans $2.hHlo_floor $2.hHlohi
exact_mod_cast $1
have $12 : # * ($2.ω : ℝ) * ($2.Hhi : ℝ) ≤ ($2.x : ℝ) := regime_eight_omega_Hhi_le_x $2
have $13 : ($6 : ℝ) ≤ ($2.Hhi : ℝ) := by exact_mod_cast $14
have $15 : # * $2.ω * $6 ≤ $2.x := by
have $1 : (# : ℝ) * ($2.ω : ℝ) * ($6 : ℝ) ≤ ($2.x : ℝ) := by nlinarith [$12, $13, $16]
exact_mod_cast $1
have $17 : # * ($6 : ℝ) ≤ ($4 : ℝ) := by
have $18 : # * $6 ≤ $4 := by
refine le_trans ((Nat.le_div_iff_mul_le $19).mpr ?_) $3
calc # * $6 * (# * $2.ω) = # * $2.ω * $6 := by ring
```

**5.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:179` · `Salt/MR/M4SecondRoad.lean:556` · ⚠️ shares source lines with #3, #4

```lean
have $1 : (# : ℝ) < ($2.ω : ℝ) := by
have $3 : # < $2.ω := by have := $2.hω; omega
exact_mod_cast $3
have $4 : $2.x / (# * $2.ω) ≤ $5 := by
rw [$6]
exact doorLadder_ge_x_div_four_omega ($7 := $7) $2.hω $8 (by omega)
have $9 : $5 ≤ $2.x := by
rw [$6]
exact doorLadder_le_start $10 ($11 + #)
have $12 : (# : ℝ) ≤ ($2.Hhi : ℝ) := by
have $3 : # ≤ $2.Hhi := le_trans $2.hHlo_floor $2.hHlohi
exact_mod_cast $3
have $13 : # * ($2.ω : ℝ) * ($2.Hhi : ℝ) ≤ ($2.x : ℝ) := regime_eight_omega_Hhi_le_x $2
have $14 : ($7 : ℝ) ≤ ($2.Hhi : ℝ) := by exact_mod_cast $15
have $16 : # * $2.ω * $7 ≤ $2.x := by
have $3 : (# : ℝ) * ($2.ω : ℝ) * ($7 : ℝ) ≤ ($2.x : ℝ) := by nlinarith [$13, $14, $1]
exact_mod_cast $3
have $17 : # * ($7 : ℝ) ≤ ($5 : ℝ) := by
have $18 : # * $7 ≤ $5 := by
refine le_trans ((Nat.le_div_iff_mul_le $19).mpr ?_) $4
```

**6.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:172` · `Salt/MR/M4SecondRoad.lean:549` · ⚠️ shares source lines with #3, #4, #5

```lean
linarith only [$1, (Nat.cast_nonneg _ : # ≤ ↑$2)]
have $3 : # < # * $4.ω := by have := $4.hω; omega
have $5 : (# : ℝ) < ($4.ω : ℝ) := by
have $6 : # < $4.ω := by have := $4.hω; omega
exact_mod_cast $6
have $7 : $4.x / (# * $4.ω) ≤ $8 := by
rw [$9]
exact doorLadder_ge_x_div_four_omega ($2 := $2) $4.hω $10 (by omega)
have $11 : $8 ≤ $4.x := by
rw [$9]
exact doorLadder_le_start $12 ($13 + #)
have $14 : (# : ℝ) ≤ ($4.Hhi : ℝ) := by
have $6 : # ≤ $4.Hhi := le_trans $4.hHlo_floor $4.hHlohi
exact_mod_cast $6
have $15 : # * ($4.ω : ℝ) * ($4.Hhi : ℝ) ≤ ($4.x : ℝ) := regime_eight_omega_Hhi_le_x $4
have $16 : ($2 : ℝ) ≤ ($4.Hhi : ℝ) := by exact_mod_cast $17
have $18 : # * $4.ω * $2 ≤ $4.x := by
have $6 : (# : ℝ) * ($4.ω : ℝ) * ($2 : ℝ) ≤ ($4.x : ℝ) := by nlinarith [$15, $16, $5]
exact_mod_cast $6
have $19 : # * ($2 : ℝ) ≤ ($8 : ℝ) := by
```

**7.** 18 lines × 5 occurrences in 3 files · lines saved ≤ **85** · e.g. `Salt/MR/BandRatedSocket.lean:106` · `Salt/MR/HDoorSupply.lean:1270`

```lean
have $1 : $2.Hlo ≤ $3 := $4.1
have $5 : $3 ≤ $2.Hhi := $4.2.1
have $6 : (# : ℝ) ≤ ($2.Hlo : ℝ) := by exact_mod_cast $2.hHlo_floor
have $7 : (# : ℝ) ≤ Real.log ($2.Hlo : ℝ) := cofk_log_big $6
have $8 : Real.exp (# : ℝ) ≤ Real.log ($2.Hlo : ℝ) := by
have $9 := Real.exp_le_exp.mpr $10
rwa [Real.exp_log (by linarith)] at $9
have $11 : (# : ℝ) ^ # ≤ Real.exp (# : ℝ) := by
have $9 := cofk_exp_quartic ($12 := (# : ℝ)) (by norm_num)
have $13 : (# : ℝ) ≤ (# + (# : ℝ) / #) ^ # := by norm_num
linarith
have $14 : (# : ℝ) ^ # ≤ Real.log ($2.Hlo : ℝ) := by linarith
have $15 : ($2.Hlo : ℝ) ≤ ($3 : ℝ) := by exact_mod_cast $1
have $16 : ($3 : ℝ) ≤ ($2.Hhi : ℝ) := by exact_mod_cast $5
have $17 : (# : ℝ) ≤ ($3 : ℝ) := by linarith
have $18 : (# : ℝ) < ($2.Hlo : ℝ) := by linarith
have $19 : Real.log ($2.Hlo : ℝ) ≤ Real.log ($3 : ℝ) := Real.log_le_log $18 $15
have $20 : Real.log ($3 : ℝ) ≤ Real.log ($2.Hhi : ℝ) :=
```

**8.** 13 lines × 7 occurrences in 6 files · lines saved ≤ **84** · e.g. `Salt/Chen/ChenFinal2.lean:112` · `Salt/Chen/PriceOne.lean:329`

```lean
have $1 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
rw [$2]
linarith
have $3 : (# : ℝ) < $4 := by rw [$2]; linarith
have $5 : (# : ℝ) ≤ $4 := by rw [$2]; linarith
have $6 : $7 ≤ # / # * $4 := by rw [$2]; linarith
have $8 : # * ((# : ℝ) / #) ^ ((# : ℝ)) ≤ $4 := by
have $9 : ((# : ℝ) / #) ^ ((# : ℝ)) = ((# : ℝ) / #) ^ (# : ℕ) := by
rw [show ((# : ℝ)) = ((# : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
have $10 : # * ((# : ℝ) / #) ^ (# : ℕ) ≤ # / # * # ^ # - # := by norm_num
rw [$9, $2]
linarith
```

**9.** 15 lines × 6 occurrences in 5 files · lines saved ≤ **84** · e.g. `Salt/Chen/ChenFinal2.lean:112` · `Salt/Chen/PriceOne.lean:329` · ⚠️ shares source lines with #8

```lean
have $1 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
rw [$2]
linarith
have $3 : (# : ℝ) < $4 := by rw [$2]; linarith
have $5 : (# : ℝ) ≤ $4 := by rw [$2]; linarith
have $6 : $7 ≤ # / # * $4 := by rw [$2]; linarith
have $8 : # * ((# : ℝ) / #) ^ ((# : ℝ)) ≤ $4 := by
have $9 : ((# : ℝ) / #) ^ ((# : ℝ)) = ((# : ℝ) / #) ^ (# : ℕ) := by
rw [show ((# : ℝ)) = ((# : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
have $10 : # * ((# : ℝ) / #) ^ (# : ℕ) ≤ # / # * # ^ # - # := by norm_num
rw [$9, $2]
linarith
have $11 : (# : ℝ) ≤ $7 ^ ((# : ℝ)) := by
calc (# : ℝ) ≤ $7 := by linarith
```

**10.** 6 lines × 16 occurrences in 13 files · lines saved ≤ **80** · e.g. `Salt/MR/DoorReceipt.lean:738` · `Salt/MR/DoorReceiptSiegelFree.lean:161`

```lean
have $1 : # * $2 ≤ Real.log (Real.log ($3.Hlo : ℝ)) := by
rw [$4]; exact flatWitFloor_design $5 $6 $2 $7
have $8 : Real.log (Real.log (($3.Hlo : ℕ) : ℝ)) ≤ # * $2 + Real.log # := by
rw [$4, flat_witFloor_eq_designBase $9 $10 $11 $12 $13 hεpin $14 $15]
exact flatDesignBase_loglog_le $9
have $16 : Real.log (Real.log (($3.Hhi : ℕ) : ℝ)) ≤ # * Real.exp (# * $2 / #) :=
```

**11.** 6 lines × 16 occurrences in 13 files · lines saved ≤ **80** · e.g. `Salt/MR/DoorReceipt.lean:748` · `Salt/MR/DoorReceiptSiegelFree.lean:171`

```lean
have $1 : (# : ℚ) / # ^ # ≤ $2.eps := by
rw [$3]
have : (# : ℚ) / # ^ # ≤ # / # := by norm_num
linarith [hεpin]
have $4 : Real.exp (# * $5) ≤ Real.log (($2.Hlo : ℕ) : ℝ) := by
rw [$6]; exact flatWitFloor_log_ge $7
```

**12.** 7 lines × 13 occurrences in 8 files · lines saved ≤ **78** · e.g. `Salt/MR/FlatDoorEpsRung2.lean:647` · `Salt/MR/S13CapEps.lean:437`

```lean
obtain ⟨-, $1⟩ := regime_Hfloor_of_loglogFloor50 (le_trans $2 $3)
have $4 : # ≤ $5 := le_trans $6.hHlo_floor $3
have $7 : (# : ℝ) ≤ ($5 : ℝ) := by exact_mod_cast $4
have $8 : (# : ℝ) < Real.log ($5 : ℝ) := Real.log_pos (by linarith)
have $9 : Real.exp # ≤ Real.log ($5 : ℝ) := by
have := Real.exp_le_exp.mpr $1
rwa [Real.exp_log $8] at this
```

**13.** 14 lines × 6 occurrences in 6 files · lines saved ≤ **78** · e.g. `Salt/MR/StrideDoorAllGrades.lean:5465` · `Salt/MR/StridePairReceipt.lean:2106`

```lean
have $1 : (# : ℝ) ≤ # / ($2.eps : ℝ) := by positivity
have $3 : (# : ℝ) ≤ # / ($2.eps : ℝ) := by
rw [le_div_iff₀ $4]; linarith
have $5 : (# : ℝ) ≤ Real.log (($2.ω : ℕ) : ℝ) := by
have $6 := $2.hωbig
nlinarith [mul_nonneg $1 $7]
have $8 : # ≤ $2.ω := $2.hω
have $9 : (# : ℝ) < (($2.ω : ℕ) : ℝ) := by
have $10 : (# : ℝ) ≤ (($2.ω : ℕ) : ℝ) := by exact_mod_cast $8
linarith
have $11 : # ≤ $2.ω := by
have $12 := Real.log_le_sub_one_of_pos $9
have $13 : (# : ℝ) ≤ (($2.ω : ℕ) : ℝ) := by linarith
exact_mod_cast $13
```

**14.** 8 lines × 11 occurrences in 7 files · lines saved ≤ **77** · e.g. `Salt/MaynardK/JMainSplit.lean:885` · `Salt/MaynardK/JSplit.lean:963`

```lean
have $1 : # < $2 := by
rcases Nat.eq_zero_or_pos $2 with $3 | $3
· rw [$3] at $4; simp at $4; linarith
· exact $3
have $5 : # ≤ $2 := by
have $6 : (#:ℝ) < ($2:ℝ) := by exact_mod_cast $1
have $7 : (#:ℝ) ≤ Real.exp (Real.log $2) := by
calc (#:ℝ) ≤ Real.exp # := by have := Real.add_one_le_exp (#:ℝ); linarith
```

**15.** 12 lines × 7 occurrences in 3 files · lines saved ≤ **77** · e.g. `Salt/MR/LFunctionInvShallow.lean:469` · `Salt/MR/MobiusChiRate.lean:406`

```lean
have $1 : (# : ℝ) ≤ Real.exp # := by linarith [Real.add_one_le_exp (# : ℝ)]
have $2 : (# : ℝ) ≤ Real.exp (Real.exp #) := by
have $3 : Real.exp # ≤ Real.exp (Real.exp #) := Real.exp_le_exp.mpr (by linarith)
linarith
have $4 : (# : ℝ) < $5 := by linarith
have $6 : Real.exp # ≤ Real.log $5 := by
rw [← Real.log_exp (Real.exp #)]
exact Real.log_le_log (Real.exp_pos _) (by linarith)
have $7 : (# : ℝ) < Real.log $5 := by linarith
have $8 : (# : ℝ) ≤ Real.log (Real.log $5) := by
rw [← Real.log_exp #]
exact Real.log_le_log (Real.exp_pos _) $6
```

**16.** 3 lines × 38 occurrences in 26 files · lines saved ≤ **76** · e.g. `Salt/BV/AbelCore.lean:578` · `Salt/Chen/A2Weighted.lean:523`

```lean
field_simp
ring
rw [$1]
```

**17.** 5 lines × 18 occurrences in 15 files · lines saved ≤ **72** · e.g. `Salt/MR/DoorReceipt.lean:714` · `Salt/MR/DoorReceiptSiegelFree.lean:137`

```lean
have $1 : XCeilRiderStrict $2 (fun _ _ : ℕ => #) := by
intro $3 $4 $5
obtain ⟨-, -, $6⟩ := $5
simp only [Nat.cast_zero, Real.log_zero]
linarith [Real.log_natCast_nonneg $4]
```

**18.** 9 lines × 9 occurrences in 8 files · lines saved ≤ **72** · e.g. `Salt/MR/DoorReceipt.lean:745` · `Salt/MR/DoorReceiptSiegelFree.lean:168` · ⚠️ shares source lines with #11

```lean
refine ⟨$1, $2, $3, $4, $5, $6, $7, $8, ?_⟩
intro $9 $10
have $11 : # ≤ flatDoorM $12 := flatDoorM_one_le (flat162_ge_26 $13)
have $14 : (# : ℚ) / # ^ # ≤ $1.eps := by
rw [$2]
have : (# : ℚ) / # ^ # ≤ # / # := by norm_num
linarith [hεpin]
have $15 : Real.exp (# * $12) ≤ Real.log (($1.Hlo : ℕ) : ℝ) := by
rw [$3]; exact flatWitFloor_log_ge $13
```

**19.** 9 lines × 9 occurrences in 9 files · lines saved ≤ **72** · e.g. `Salt/Brun/M5Assembly.lean:42` · `Salt/Chen/HeadlineW2.lean:187`

```lean
rw [Finset.prod_insert $1]
have $2 : $3.Prime := $4 $3 (Finset.mem_insert_self $3 $5)
have $6 : ∀ $7 ∈ $5, $7.Prime := fun $7 $8 => $4 $7 (Finset.mem_insert_of_mem $8)
have $9 : $3.Coprime (∏ $7 ∈ $5, $7) := by
apply Nat.Coprime.prod_right
intro $7 $8
exact (Nat.coprime_primes $2 ($6 $7 $8)).mpr (by rintro rfl; exact $1 $8)
rw [Nat.squarefree_mul_iff]
exact ⟨$9, $2.squarefree, $10 $6⟩
```

**20.** 10 lines × 8 occurrences in 7 files · lines saved ≤ **72** · e.g. `Salt/Chen/ChenFinal2.lean:154` · `Salt/Chen/PriceOne.lean:371`

```lean
have $1 : $2 ^ ((# : ℝ)) ≤ Real.exp $2 := by
have $3 : (# : ℝ) ≤ $2 / # := by linarith
have $4 : $2 ≤ ($2 / #) ^ ((# : ℝ)) := by
rw [show ((# : ℝ)) = ((# : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
have $5 : ($2 / #) ^ (# : ℕ) = $2 * $2 / # := by ring
rw [$5, le_div_iff₀ (by norm_num : (# : ℝ) < #)]
have $6 : (# : ℝ) ≤ ($2 - #) * $2 := mul_nonneg (by linarith) $7.le
linarith [$6]
have $8 : $2 / # ≤ Real.exp ($2 / #) := by linarith [Real.add_one_le_exp ($2 / #)]
calc $2 ^ ((# : ℝ))
```

**21.** 13 lines × 6 occurrences in 3 files · lines saved ≤ **72** · e.g. `Salt/MR/FlatConsumers.lean:124` · `Salt/MR/FlatDoorEpsRung2.lean:4047`

```lean
set $1 : ℝ := Real.log (Real.log (($2.Hlo : ℕ) : ℝ)) with $3
set $4 : ℝ := Real.log (Real.log (($2.Hhi : ℕ) : ℝ)) with $5
set $6 : ℝ := Real.log (Real.log ((($7 + $8 : ℕ)) : ℝ)) with $9
have $10 : # < $7 := $11.2.2.2.2.2.2.2.1
have $12 : (# : ℝ) < ($7 : ℝ) := by exact_mod_cast $10
have $13 : ($7 : ℝ) ≤ ((($7 + $8 : ℕ)) : ℝ) := by
push_cast; linarith [Nat.cast_nonneg ($14 := ℝ) $8]
obtain ⟨$15, -⟩ := s13_socketBase_loglogA $16 $11
have $17 : (# : ℝ) < Real.log ((($7 + $8 : ℕ)) : ℝ) := by
have := Real.log_le_log $12 $13; linarith
have $18 : (# : ℝ) < Real.log ((($7 + $8 : ℕ)) : ℝ) := by linarith
have $19 : constPool $20 $2.Hhi = Real.exp (Real.log $20 - Real.log # - # * $4) := by
rw [constPool_def, $5, Real.exp_sub, Real.exp_sub, Real.exp_log $21,
```

**22.** 3 lines × 35 occurrences in 25 files · lines saved ≤ **70** · e.g. `Salt/Chen/CountAtOp.lean:158` · `Salt/Chen/DyadicWindow.lean:92`

```lean
have $1 : (# : ℝ) < ($2 : ℝ) := by
have : (# : ℝ) ≤ ($2 : ℝ) := by exact_mod_cast $3
linarith
```

**23.** 6 lines × 14 occurrences in 9 files · lines saved ≤ **70** · e.g. `Salt/MR/FlatDoorEpsRung2.lean:762` · `Salt/MR/S13CapEps.lean:436` · ⚠️ shares source lines with #12

```lean
have $1 : $2.Hlo ≤ $3 := $4.1
obtain ⟨-, $5⟩ := regime_Hfloor_of_loglogFloor50 (le_trans $6 $1)
have $7 : # ≤ $3 := le_trans $2.hHlo_floor $1
have $8 : (# : ℝ) ≤ ($3 : ℝ) := by exact_mod_cast $7
have $9 : (# : ℝ) < Real.log ($3 : ℝ) := Real.log_pos (by linarith)
have $10 : Real.exp # ≤ Real.log ($3 : ℝ) := by
```

**24.** 6 lines × 14 occurrences in 13 files · lines saved ≤ **70** · e.g. `Salt/MR/DoorReceipt.lean:728` · `Salt/MR/DoorReceiptSiegelFree.lean:151`

```lean
intro $1
obtain ⟨$2, $3, $4, $5⟩ := $6 $1
have $7 := $8 $1
refine ⟨$2, $3, ?_⟩
intro $9 $10 $11 $12 $13
obtain ⟨$14, $15, $16⟩ := $5 $9 $10 $12
```

**25.** 6 lines × 14 occurrences in 12 files · lines saved ≤ **70** · e.g. `Salt/MR/FlatDoorStandoff.lean:941` · `Salt/MR/RegisterCompose.lean:184`

```lean
intro $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$13, $14, $15, $16, $17, $18, $19⟩ := $20 $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$21, $22, $23, $24, $25, $26⟩ := socketLogFrame_facts $6 $7 $19.logX_eight
have $27 : Real.exp (# * (Real.log ((($5 + $6 : ℕ)) : ℝ)) ^ ((# : ℝ) / #)) ≤ # * $8 := $11
have $28 : (# : ℝ) < # * $8 := by linarith
exact doorCapBundle_at_workingPoint_perBlock_L_gk $29 $30 $31 $23 $21 $19 $28 $10 $12
```

## Whitelist (data)

`abel` `absurd` `aesop` `all_goals` `and_intros` `any_goals` `apply` `apply?` `apply_fun` `apply_rules` `assumption` `assumption_mod_cast` `bound` `bound?` `by_cases` `by_contra` `by_contra!` `calc` `calc?` `cancel_denoms` `case` `cases` `cases'` `change` `choose` `classical` `clear` `congr` `congr!` `congrm` `constructor` `continuity` `contradiction` `contrapose` `contrapose!` `conv` `conv_lhs` `conv_rhs` `convert` `convert_to` `decide` `delta` `done` `dsimp` `erw` `eventually_budget` `exact` `exact?` `exact_fun_prop` `exact_mod_cast` `exacts` `exfalso` `exists` `existsi` `ext` `field_simp` `field_simp?` `filter_upwards` `fin_cases` `first` `focus` `fun_prop` `funext` `gcongr` `gcongr?` `gcongr_discharger` `generalize` `group` `have` `haveI` `induction` `induction'` `infer_instance` `interval_cases` `intro` `intros` `iterate` `left` `let` `letI` `lift` `linarith` `linarith!` `linear_combination` `measurability` `mod_cast` `mono` `native_decide` `next` `nlinarith` `nlinarith!` `nlinarith?` `noncomm_ring` `norm_cast` `norm_num` `norm_num1` `norm_num?` `nth_rewrite` `nth_rw` `obtain` `omega` `on_goal` `pick_goal` `polyrith` `positivity` `positivity?` `push_cast` `push_neg` `qify` `rcases` `refine` `refine'` `refine_lift` `rel` `rename_i` `repeat` `rewrite` `rfl` `right` `ring` `ring1` `ring_nf` `rintro` `rotate_left` `rsuffices` `rw` `rw?` `rwa` `set` `show` `simp` `simp?` `simp_all` `simp_arith` `simp_rw` `simpa` `simpa?` `skip` `sorry` `specialize` `split` `split_ands` `split_ifs` `stop` `subst` `subst_vars` `suffices` `swap` `symm` `tauto` `trans` `trivial` `try` `unfold` `unfold?` `unfold_let` `use` `with_reducible` `wlog` `zify`

Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): `Salt/Tactic/AuditAxioms.lean`, `Salt/Tactic/NlinarithSuggest.lean`.
