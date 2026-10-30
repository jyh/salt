# THE TACTICS CATALOGUE — by machine (O13 item 4)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/tactics_catalogue.py` · staleness gate: `python3 scripts/tactics_catalogue.py --check`.
> Base: last commit touching `Salt/` = `9689cb63` · source digest `f3c848d47d585286` (the same digest as items 1–3).
> Receipt: files 1395 · decls 23378 · with_body 23378 · tactic_lines 318095 · runs 37177 · blocks 1590.

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

318095 tactic lines. Top 30:

| # | tactic | lines | share |
|---:|---|---:|---:|
| 1 | `have` | 140100 | 44.0% |
| 2 | `rw` | 51012 | 16.0% |
| 3 | `exact` | 18061 | 5.7% |
| 4 | `intro` | 14657 | 4.6% |
| 5 | `refine` | 13306 | 4.2% |
| 6 | `linarith` | 11259 | 3.5% |
| 7 | `obtain` | 9320 | 2.9% |
| 8 | `calc` | 8113 | 2.6% |
| 9 | `set` | 5762 | 1.8% |
| 10 | `simp` | 5256 | 1.7% |
| 11 | `apply` | 4607 | 1.4% |
| 12 | `nlinarith` | 3545 | 1.1% |
| 13 | `unfold` | 2706 | 0.9% |
| 14 | `exact_mod_cast` | 2598 | 0.8% |
| 15 | `ring` | 2203 | 0.7% |
| 16 | `rcases` | 2170 | 0.7% |
| 17 | `push_cast` | 2109 | 0.7% |
| 18 | `field_simp` | 1922 | 0.6% |
| 19 | `by_cases` | 1685 | 0.5% |
| 20 | `rwa` | 1645 | 0.5% |
| 21 | `norm_num` | 1486 | 0.5% |
| 22 | `omega` | 1420 | 0.4% |
| 23 | `show` | 1277 | 0.4% |
| 24 | `classical` | 1273 | 0.4% |
| 25 | `rintro` | 1170 | 0.4% |
| 26 | `congr` | 999 | 0.3% |
| 27 | `simpa` | 936 | 0.3% |
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
| character sums / L-functions | 66344 | `have` 28287, `rw` 10258, `exact` 4186, `refine` 3750, `intro` 3497, `obtain` 2469, `linarith` 2329, `calc` 1504 |
| exponential sums | 8307 | `have` 3163, `rw` 1697, `exact` 504, `intro` 410, `refine` 390, `linarith` 237, `set` 228, `simp` 209 |
| Mertens / PNT-type | 3298 | `have` 1530, `rw` 559, `exact` 173, `linarith` 147, `intro` 127, `refine` 103, `apply` 93, `simp` 73 |
| certificates / explicit numerics | 129 | `exact` 22, `rw` 22, `have` 13, `obtain` 10, `simp` 10, `refine` 8, `intro` 6, `rintro` 6 |
| explog/lognum numeral tactic | 106 | `have` 33, `rw` 20, `exact` 15, `intro` 6, `filter_upwards` 5, `refine` 5, `nlinarith` 4, `calc` 3 |
| Matomaki-Radziwill / Halasz (short intervals) | 127147 | `have` 58947, `rw` 17278, `exact` 7172, `refine` 7005, `intro` 6179, `linarith` 5982, `obtain` 5022, `calc` 2421 |
| (no family) | 29620 | `have` 11449, `rw` 5292, `exact` 1797, `intro` 1637, `obtain` 1013, `refine` 984, `set` 905, `calc` 888 |

## 3. Macro candidates (repeated normalised tactic blocks)

Blocks of 3–20 consecutive tactic lines, repeated ≥ 5 times (non-overlapping) in ≥ 3 files, maximal only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name (numbered by first appearance, so equal blocks bind alike), `#` = a numeral. 1590 candidates; top 25 by the UPPER-BOUND saving.

⚠️ **Lines saved is an UPPER bound, never a price:** a macro call is ≥ 1 line; sites whose placeholders bind differently may not share a macro; generic blocks may cost more to name than to repeat.

**1.** 14 lines × 14 occurrences in 6 files · lines saved ≤ **182** · e.g. `Salt/MR/HloExportMR.lean:251` · `Salt/MR/HloExportMRFlatRoot.lean:304`

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

**2.** 15 lines × 12 occurrences in 5 files · lines saved ≤ **168** · e.g. `Salt/MR/M4BaseNarrow.lean:210` · `Salt/MR/M4ChiSummed.lean:340`

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

**3.** 20 lines × 8 occurrences in 7 files · lines saved ≤ **152** · e.g. `Salt/Chen/ChenFinal2.lean:161` · `Salt/Chen/PriceOne.lean:367`

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

**4.** 20 lines × 8 occurrences in 7 files · lines saved ≤ **152** · e.g. `Salt/Chen/ChenFinal2.lean:103` · `Salt/Chen/PriceOne.lean:309`

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

**5.** 7 lines × 25 occurrences in 10 files · lines saved ≤ **150** · e.g. `Salt/MR/M4RowAssemblyLinear.lean:5023` · `Salt/MR/M4RowSpineLinear.lean:1341`

```lean
have $1 : # < $2 := $3.2.2.2.1
have $4 : # < $5 := $3.2.2.2.2.2.2.2.1
haveI : NeZero $2 := ⟨$1.ne'⟩
have $6 := $7 $8 $9 $2 $10 $5 $11 $3
have $12 : # < $5 + $11 := lt_of_lt_of_le $4 (Nat.le_add_right $5 $11)
have $13 : (# : ℝ) < ((($5 + $11 : ℕ)) : ℝ) := by exact_mod_cast $12
have $14 : (((# * ($5 + $11) : ℕ)) : ℝ) ≤ # * ((($5 + $11 : ℕ)) : ℝ) := by push_cast; linarith
```

**6.** 8 lines × 21 occurrences in 7 files · lines saved ≤ **147** · e.g. `Salt/MR/M4SocketDischarge.lean:314` · `Salt/MR/M4SocketLinear.lean:256`

```lean
have $1 : # < $2 := $3.2.2.2.1
haveI : NeZero $2 := ⟨$1.ne'⟩
have $4 := $5 $6 $7 $2 $8 $9 $10 $3
have $11 : # ≤ $9 + $10 := by
have $12 : (# : ℝ) ≤ ((($9 + $10 : ℕ)) : ℝ) := $4.X400
have : (# : ℝ) ≤ ((($9 + $10 : ℕ)) : ℝ) := by linarith
exact_mod_cast this
exact $13 $2 $14 $15 ($9 + $10) (# * ($9 + $10)) rfl $4.X400 (by omega) le_rfl $4.C₁_one
```

**7.** 19 lines × 8 occurrences in 7 files · lines saved ≤ **144** · e.g. `Salt/MaynardK/ISplit.lean:192` · `Salt/MaynardK/JMainSplit.lean:687`

```lean
apply Finset.sum_le_sum_of_subset_of_nonneg
· intro $1 $2
rw [Finset.mem_filter] at $2
obtain ⟨$3, $4, $5⟩ := $2
simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at $3
obtain ⟨$6, $7, $8, _⟩ := $3
rw [Fintype.mem_piFinset]
intro $9
rw [$10, Finset.mem_filter, Finset.mem_range]
refine ⟨$6 $9, $7 $9, $8 $9, ?_⟩
simp only [$11]
split
· rename_i $12
rcases $12 with $13 | $14
· rw [$13]; exact $4
· rw [$14]; exact $5
· exact one_dvd _
· intro $1 _ _
exact Finset.prod_nonneg (fun $9 _ => by positivity)
```

**8.** 18 lines × 8 occurrences in 7 files · lines saved ≤ **136** · e.g. `Salt/MaynardK/ISplit.lean:504` · `Salt/MaynardK/JMainSplit.lean:801`

```lean
simp only [not_forall] at $1
obtain ⟨$2, $3, $4, $5⟩ := $1
have $6 : Nat.gcd ($7 $2) ($7 $3) ≠ # := $5
obtain ⟨$8, $9, $10⟩ := Nat.exists_prime_and_dvd $6
have $11 : $8 ∣ $7 $2 := $10.trans (Nat.gcd_dvd_left _ _)
have $12 : $8 ∣ $7 $3 := $10.trans (Nat.gcd_dvd_right _ _)
have $13 : ¬ $8 ∣ $14 := by
intro $15
have $16 : $8 ∣ (# : ℕ) := ($17 $2) ▸ Nat.dvd_gcd $11 $15
exact absurd (Nat.dvd_one.mp $16) $9.one_lt.ne'
have $18 : $19 < $8 := $20 $8 $9 $13
have $21 : # ≤ $7 $2 := Nat.pos_of_ne_zero ($22 $2).ne_zero
have $23 : $8 < $24 := lt_of_le_of_lt (Nat.le_of_dvd (by omega) $11) ($25 $2)
have $26 : $8 ∈ $27 := by
rw [$28, Finset.mem_filter, Finset.mem_range]; exact ⟨$23, $9, $18⟩
have $29 : ($2, $3) ∈ $30 := by
rw [$31, Finset.mem_filter]; exact ⟨Finset.mem_univ _, $4⟩
have $32 : (($2, $3), $8) ∈ $33 := by rw [$34]; exact Finset.mem_product.mpr ⟨$29, $26⟩
```

**9.** 10 lines × 15 occurrences in 12 files · lines saved ≤ **135** · e.g. `Salt/MR/CaseASocket.lean:97` · `Salt/MR/CenterSupply.lean:139`

```lean
have $1 : (# : ℝ) < $2 := by linarith
have $3 : (# : ℝ) < Real.sqrt $2 := Real.sqrt_pos.mpr $1
have $4 : (# : ℝ) ≤ Real.sqrt $2 := by
have $5 : Real.sqrt # = # := by
rw [show (# : ℝ) = # ^ # from by norm_num, Real.sqrt_sq (by norm_num)]
rw [← $5]
exact Real.sqrt_le_sqrt $6
have $7 : Real.log (Real.sqrt $2) ≤ Real.sqrt $2 - # := Real.log_le_sub_one_of_pos $3
have $8 : Real.log (Real.sqrt $2) = Real.log $2 / # := Real.log_sqrt $1.le
have $9 : Real.sqrt $2 * Real.sqrt $2 = $2 := Real.mul_self_sqrt $1.le
```

**10.** 20 lines × 7 occurrences in 6 files · lines saved ≤ **133** · e.g. `Salt/Chen/ChenFinal2.lean:106` · `Salt/Chen/PriceOne.lean:312` · ⚠️ shares source lines with #4

```lean
have $1 : ($2 : ℝ) / # < ($3 : ℝ) * ($4 : ℝ) := by linarith
have $5 : Real.log (($2 : ℝ) / #) ≤ $6 := Real.log_le_log (by linarith) $1.le
rw [Real.log_div (ne_of_gt $7) (by norm_num : (# : ℝ) ≠ #)] at $5
have $8 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $9 : $6 ≤ Real.log $2 + # := by
have $10 : $6 ≤ Real.log (# * ($2 : ℝ)) := Real.log_le_log $11 $12
rw [Real.log_mul (by norm_num : (# : ℝ) ≠ #) (ne_of_gt $7)] at $10
have $13 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $14 : (# : ℝ) ≤ $6 := by linarith
have $15 : (# : ℝ) ≤ $6 := by linarith
have $16 : (# : ℝ) < $6 := by linarith
have $17 : (# : ℝ) ≤ $6 := by linarith
have $18 : (# : ℝ) ≤ $6 := by linarith
set $19 : ℝ := # / # * Real.log $2 - # with $20
have $21 : $19 ≤ Real.log $22 := by
have $23 := Real.log_le_log (div_pos (Real.rpow_pos_of_pos $7 _) (by norm_num))
```

**11.** 20 lines × 7 occurrences in 6 files · lines saved ≤ **133** · e.g. `Salt/Chen/ChenFinal2.lean:104` · `Salt/Chen/PriceOne.lean:310` · ⚠️ shares source lines with #4, #10

```lean
have $1 : (($2 / # + # : ℕ) : ℝ) ≤ ($3 : ℝ) * ($4 : ℝ) := by exact_mod_cast $5
push_cast at $6 $1
have $7 : ($2 : ℝ) / # < ($3 : ℝ) * ($4 : ℝ) := by linarith
have $8 : Real.log (($2 : ℝ) / #) ≤ $9 := Real.log_le_log (by linarith) $7.le
rw [Real.log_div (ne_of_gt $10) (by norm_num : (# : ℝ) ≠ #)] at $8
have $11 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $12 : $9 ≤ Real.log $2 + # := by
have $13 : $9 ≤ Real.log (# * ($2 : ℝ)) := Real.log_le_log $14 $15
rw [Real.log_mul (by norm_num : (# : ℝ) ≠ #) (ne_of_gt $10)] at $13
have $16 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $17 : (# : ℝ) ≤ $9 := by linarith
have $18 : (# : ℝ) ≤ $9 := by linarith
have $19 : (# : ℝ) < $9 := by linarith
have $20 : (# : ℝ) ≤ $9 := by linarith
have $21 : (# : ℝ) ≤ $9 := by linarith
set $22 : ℝ := # / # * Real.log $2 - # with $23
```

**12.** 20 lines × 7 occurrences in 6 files · lines saved ≤ **133** · e.g. `Salt/Chen/ChenFinal2.lean:105` · `Salt/Chen/PriceOne.lean:311` · ⚠️ shares source lines with #4, #10, #11

```lean
push_cast at $1 $2
have $3 : ($4 : ℝ) / # < ($5 : ℝ) * ($6 : ℝ) := by linarith
have $7 : Real.log (($4 : ℝ) / #) ≤ $8 := Real.log_le_log (by linarith) $3.le
rw [Real.log_div (ne_of_gt $9) (by norm_num : (# : ℝ) ≠ #)] at $7
have $10 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $11 : $8 ≤ Real.log $4 + # := by
have $12 : $8 ≤ Real.log (# * ($4 : ℝ)) := Real.log_le_log $13 $14
rw [Real.log_mul (by norm_num : (# : ℝ) ≠ #) (ne_of_gt $9)] at $12
have $15 : Real.log # ≤ # := by
linarith [Real.log_le_sub_one_of_pos (show (# : ℝ) < # by norm_num)]
linarith
have $16 : (# : ℝ) ≤ $8 := by linarith
have $17 : (# : ℝ) ≤ $8 := by linarith
have $18 : (# : ℝ) < $8 := by linarith
have $19 : (# : ℝ) ≤ $8 := by linarith
have $20 : (# : ℝ) ≤ $8 := by linarith
set $21 : ℝ := # / # * Real.log $4 - # with $22
have $23 : $21 ≤ Real.log $24 := by
```

**13.** 6 lines × 26 occurrences in 19 files · lines saved ≤ **130** · e.g. `Salt/MR/DoorReceipt.lean:214` · `Salt/MR/FlatDoorAllGradesBand.lean:776`

```lean
have $1 : ∀ $2 : ℕ, $2 ≤ $3.Hhi → $2 + # ≤ $3.x := by
intro $2 $4
have $5 : $3.x / $3.ω ≤ $3.x / # := Nat.div_le_div_left $3.hω (by norm_num)
have $6 : $2 ≤ $3.x / # := le_trans (le_trans $4 $3.hheadroom) $5
have $7 : # ≤ $3.x := $3.hx
omega
```

**14.** 11 lines × 13 occurrences in 6 files · lines saved ≤ **130** · e.g. `Salt/MR/M4BaseNarrow.lean:304` · `Salt/MR/M4ChiSummed.lean:640`

```lean
exact mul_nonneg (mul_nonneg $1 (sq_nonneg _)) (Nat.cast_nonneg _)
rw [Nat.not_lt] at $2
have $3 : # ≤ $4 := by omega
have $5 : $6 ≤ # * $4 := by omega
have $7 : ($8 : ℝ) ≤ # * ($4 : ℝ) := by
have $9 : $8 ≤ # * $4 := by omega
have := (Nat.cast_le ($10 := ℝ)).mpr $9
push_cast at this ⊢
linarith
have $11 : (# : ℝ) ≤ ($4 : ℝ) := Nat.cast_nonneg _
set $12 := Nat.log # $8 with $13
```

**15.** 19 lines × 7 occurrences in 7 files · lines saved ≤ **126** · e.g. `Salt/Entropy/Chowla/HloExport.lean:537` · `Salt/Entropy/Chowla/HloExportFlat.lean:248`

```lean
have $1 : # < Real.log # := Real.log_pos (by norm_num)
have $2 : Real.log # < # := Real.log_two_lt_d9
have $3 : Real.log # = # * Real.log # := by
rw [show (# : ℝ) = # ^ # by norm_num, Real.log_pow]; norm_num
have $4 : $5 ≤ # / # := by
rw [$3] at $6; linarith
obtain ⟨$7, $8⟩ : ∃ $9 : ℚ, $9 = # / # := ⟨_, rfl⟩
have $10 : (($7 : ℚ) : ℝ) = # / # := by rw [$8]; norm_num
have $11 : (# : ℝ) < ($7 : ℝ) := by rw [$10]; norm_num
have $12 : # < $7 := by exact_mod_cast $11
have $13 : ($7 : ℝ) ≤ $14 / (# * Real.log #) := by
rw [$10, le_div_iff₀ (by positivity), $3]
linarith
have $15 : ($7 : ℝ) < # / # := by rw [$10]; norm_num
have $16 : ($7 : ℝ) ≤ $17 / # := by
rw [$10, le_div_iff₀ (by norm_num : (# : ℝ) < #)]; linarith
have $18 : ($7 : ℝ) ≤ $17 / (# * $5) := by
rw [$10, le_div_iff₀ (by positivity : (# : ℝ) < # * $5)]; linarith
have $19 : $7 ≤ # / # := by rw [$8]; norm_num
```

**16.** 4 lines × 41 occurrences in 11 files · lines saved ≤ **123** · e.g. `Salt/MR/M4ArithPrime.lean:244` · `Salt/MR/M4ArithZeroLinear.lean:800`

```lean
intro $1 $2 $3 $4 $5 $6 $7
have $8 : # ≤ $5 + $6 := by
have $9 : # < $5 := $7.2.2.2.2.2.2.2.1
omega
```

**17.** 5 lines × 30 occurrences in 3 files · lines saved ≤ **120** · e.g. `Salt/MR/A3Middle.lean:510` · `Salt/MR/ThmA2Linear.lean:1180`

```lean
have $1 : # * ($2 / $3) ≤ # * $4 := by linarith
have $5 : (# : ℝ) * $4 ≤ $2 := $6
have $7 : (# : ℝ) < # * $4 := by
have : (# : ℝ) < $2 / $3 := div_pos $8 (by linarith)
linarith
```

**18.** 7 lines × 20 occurrences in 18 files · lines saved ≤ **120** · e.g. `Salt/MR/DoorReceipt.lean:213` · `Salt/MR/FlatDoorAllGradesBand.lean:775` · ⚠️ shares source lines with #13

```lean
have $1 : # ≤ s13GK $2 $3 := one_le_s13GK $2 $4.hM
have $5 : ∀ $6 : ℕ, $6 ≤ $7.Hhi → $6 + # ≤ $7.x := by
intro $6 $8
have $9 : $7.x / $7.ω ≤ $7.x / # := Nat.div_le_div_left $7.hω (by norm_num)
have $10 : $6 ≤ $7.x / # := le_trans (le_trans $8 $7.hheadroom) $9
have $11 : # ≤ $7.x := $7.hx
omega
```

**19.** 11 lines × 12 occurrences in 4 files · lines saved ≤ **120** · e.g. `Salt/MR/M4BaseNarrow.lean:712` · `Salt/MR/M4NonCoprime.lean:405`

```lean
have $1 : # ≤ Nat.gcd $2 $3 := by omega
have $4 : Nat.gcd $2 $3 ≤ $3 := Nat.le_of_dvd $5 (Nat.gcd_dvd_right $2 $3)
have $6 : # * $3 ≤ $7 := by
have $8 : ((# * $3 : ℕ) : ℝ) ≤ ($7 : ℝ) := by
push_cast
have := $9 $7 $10 $11
linarith
exact_mod_cast $8
have $12 : Nat.gcd $2 $3 ≤ doorLadder $13.x $7 ($14 + #) := by omega
have $15 : # * Nat.gcd $2 $3 ≤ doorLadder $13.x $7 ($14 + #) := by omega
have $16 : # ≤ doorLadder $13.x $7 ($14 + #) / Nat.gcd $2 $3 :=
```

**20.** 13 lines × 10 occurrences in 8 files · lines saved ≤ **120** · e.g. `Salt/MR/DoorReceipt.lean:900` · `Salt/MR/DoorReceiptSiegelFree.lean:132`

```lean
have $1 : (# : ℚ) / # ≤ $2.eps := by rw [$3]; exact hεpin
have $4 : Real.log (($2.x : ℕ) : ℝ) ≤ # / ($2.eps : ℝ) * (($2.Hhi : ℕ) : ℝ) := by
rw [$3]; exact $5
have $6 : # ≤ flatDoorM $7 := flatDoorM_one_le $8
have $9 : (# : ℝ) / # ≤ ($2.eps : ℝ) := by
rw [$3]
simpa using (Rat.cast_le ($10 := ℝ)).mpr hεpin
have $11 : (# : ℝ) ≤ Real.log (Real.log ($2.Hlo : ℝ)) := by nlinarith [$12, $13]
have $14 : loglogFloor50 ≤ $2.Hlo := by rw [$15]; exact flatWitFloor_ll _ _ _ _
have $16 : Real.exp (# * $7) ≤ Real.log (($2.Hlo : ℕ) : ℝ) := by
rw [$15]; exact flatWitFloor_log_ge $13
have $17 : cofkRThr $18 $19 $20 $21 ≤ Real.log (($2.Hlo : ℕ) : ℝ) := by
linarith [$22, $16, $23]
```

**21.** 16 lines × 8 occurrences in 4 files · lines saved ≤ **120** · e.g. `Salt/MR/M4BaseNarrow.lean:210` · `Salt/MR/M4CoprimeSupply.lean:354` · ⚠️ shares source lines with #2

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
have $13 : ((($4 + $5 : ℕ)) : ℝ) * (((# ^ $11 : ℕ) : ℝ) ^ # * $14 $11 $15)
```

**22.** 10 lines × 13 occurrences in 8 files · lines saved ≤ **117** · e.g. `Salt/MR/S15Compose.lean:1291` · `Salt/MR/S16Budget.lean:1724`

```lean
have $1 : s15Arm $2 $3 $4.Hhi $4.ω ≤ $4.x := by omega
have $5 : $6 $4.Hhi $4.ω ≤ $4.x := by omega
obtain ⟨$7, $8, $9⟩ := regime_floors_of_U1 $10 $11 $12
refine ⟨$4, $13, $7, $5, $14, ?_⟩
intro $15 $16
obtain ⟨$17, $18, $19, $20⟩ := $21 $15 $16.mfloor
intro $22
obtain ⟨-, $23⟩ := regime_Hfloor_of_loglogFloor50 $8
obtain ⟨-, $24⟩ := regime_Hfloor_of_loglogFloor50 (le_trans $8 $4.hHlohi)
have $25 : Real.log (Real.log (($4.Hhi : ℕ) : ℝ))
```

**23.** 14 lines × 9 occurrences in 5 files · lines saved ≤ **117** · e.g. `Salt/MR/M4BridgeBlock.lean:430` · `Salt/MR/M4RowLinear.lean:1766`

```lean
rw [$1] at $2
exact le_trans $2 (mul_le_mul_of_nonneg_left $3 $4)
have $5 : $6 * $7 ≤ # * $8 := by
have $9 : $6 * $7 ≤ $8 + $7 := by rw [$10]; exact numBlocks_mul_le $8 $7
omega
have $11 : ($6 : ℝ) * ($7 : ℝ) ≤ # * ($8 : ℝ) := by
have : (($6 * $7 : ℕ) : ℝ) ≤ ((# * $8 : ℕ) : ℝ) := by exact_mod_cast $5
push_cast at this
linarith
have $12 : (# : ℝ) ≤ ($6 : ℝ) * ($7 : ℝ) := by positivity
have $13 : (($6 : ℝ) * ($7 : ℝ)) ^ # ≤ # * ($8 : ℝ) ^ # := by nlinarith
have $14 := $15 $8
have $16 : (# : ℝ) ≤ (# + # * Real.pi) ^ # := sq_nonneg _
have $17 : (# + # * Real.pi) ^ # * ($6 : ℝ) * ($18 $8 * ($6 : ℝ) * ($7 : ℝ) ^ #)
```

**24.** 5 lines × 29 occurrences in 16 files · lines saved ≤ **116** · e.g. `Salt/MR/DoorReceipt.lean:642` · `Salt/MR/FlatDoorAllGradesBand.lean:1115`

```lean
intro $1 $2 $3
refine le_trans (s15_gArmDoorRho_mono $4 ?_ $3) (s15Arm_rho $5)
have $6 := $7 $1 $2 $3
have := one_lt_log_of_loglog_ge $6.1 (by norm_num : (#:ℝ) < #) $6.2
linarith
```

**25.** 4 lines × 38 occurrences in 22 files · lines saved ≤ **114** · e.g. `Salt/MR/DoorReceipt.lean:510` · `Salt/MR/FlatDoorEpsChain.lean:920`

```lean
intro $1 $2 $3
have $4 : # < $1 := by
have := $5.hHlo_floor
omega
```

## Whitelist (data)

`abel` `absurd` `aesop` `all_goals` `and_intros` `any_goals` `apply` `apply?` `apply_fun` `apply_rules` `assumption` `assumption_mod_cast` `bound` `bound?` `by_cases` `by_contra` `by_contra!` `calc` `calc?` `cancel_denoms` `case` `cases` `cases'` `change` `choose` `classical` `clear` `congr` `congr!` `congrm` `constructor` `continuity` `contradiction` `contrapose` `contrapose!` `conv` `conv_lhs` `conv_rhs` `convert` `convert_to` `decide` `delta` `done` `dsimp` `erw` `eventually_budget` `exact` `exact?` `exact_fun_prop` `exact_mod_cast` `exacts` `exfalso` `exists` `existsi` `ext` `field_simp` `field_simp?` `filter_upwards` `fin_cases` `first` `focus` `fun_prop` `funext` `gcongr` `gcongr?` `gcongr_discharger` `generalize` `group` `have` `haveI` `induction` `induction'` `infer_instance` `interval_cases` `intro` `intros` `iterate` `left` `let` `letI` `lift` `linarith` `linarith!` `linear_combination` `measurability` `mod_cast` `mono` `native_decide` `next` `nlinarith` `nlinarith!` `nlinarith?` `noncomm_ring` `norm_cast` `norm_num` `norm_num1` `norm_num?` `nth_rewrite` `nth_rw` `obtain` `omega` `on_goal` `pick_goal` `polyrith` `positivity` `positivity?` `push_cast` `push_neg` `qify` `rcases` `refine` `refine'` `refine_lift` `rel` `rename_i` `repeat` `rewrite` `rfl` `right` `ring` `ring1` `ring_nf` `rintro` `rotate_left` `rsuffices` `rw` `rw?` `rwa` `set` `show` `simp` `simp?` `simp_all` `simp_arith` `simp_rw` `simpa` `simpa?` `skip` `sorry` `specialize` `split` `split_ands` `split_ifs` `stop` `subst` `subst_vars` `suffices` `swap` `symm` `tauto` `trans` `trivial` `try` `unfold` `unfold?` `unfold_let` `use` `with_reducible` `wlog` `zify`

Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): `Salt/Tactic/AuditAxioms.lean`, `Salt/Tactic/NlinarithSuggest.lean`.
