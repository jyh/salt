# THE TACTICS CATALOGUE — by machine (O13 item 4)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/tactics_catalogue.py` · staleness gate: `python3 scripts/tactics_catalogue.py --check`.
> Base: last commit touching `Salt/` = `67432a70` · source digest `cb454c87b809845a` (the same digest as items 1–3).
> Receipt: files 1414 · decls 23445 · with_body 23445 · tactic_lines 301972 · runs 35519 · blocks 1216.

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
| `ExpLogNum.lean` | T3 | `Salt.Tactic.le_exp_nat_of_le_pow` | 43 | qualified 43 | `MR/StrideDoorAllGrades.lean` 8, `MR/RegisterRepair.lean` 4, `MR/S13CapEps.lean` 4, `MR/S13CapGateLinearLH.lean` 4 (+19 files) |
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
| `Salt.Tactic.le_exp_nat_of_le_pow` | 11 | 43 | 43 |
| `Salt.Tactic.exp_nat_le_of_pow_le` | 4 | 27 | 27 |
| `Salt.Tactic.log_le_nat_of_le_pow` | 5 | 33 | 33 |
| `Salt.Tactic.nat_le_log_of_pow_le` | 4 | 21 | 21 |

## 2. Tactic usage (first token of each tactic line)

301972 tactic lines. Top 30:

| # | tactic | lines | share |
|---:|---|---:|---:|
| 1 | `have` | 131520 | 43.6% |
| 2 | `rw` | 48862 | 16.2% |
| 3 | `exact` | 17412 | 5.8% |
| 4 | `intro` | 14006 | 4.6% |
| 5 | `refine` | 12726 | 4.2% |
| 6 | `linarith` | 10358 | 3.4% |
| 7 | `obtain` | 9135 | 3.0% |
| 8 | `calc` | 7775 | 2.6% |
| 9 | `set` | 5444 | 1.8% |
| 10 | `simp` | 5149 | 1.7% |
| 11 | `apply` | 4520 | 1.5% |
| 12 | `nlinarith` | 3311 | 1.1% |
| 13 | `unfold` | 2623 | 0.9% |
| 14 | `exact_mod_cast` | 2384 | 0.8% |
| 15 | `rcases` | 2126 | 0.7% |
| 16 | `ring` | 2054 | 0.7% |
| 17 | `push_cast` | 1949 | 0.6% |
| 18 | `field_simp` | 1857 | 0.6% |
| 19 | `by_cases` | 1634 | 0.5% |
| 20 | `rwa` | 1570 | 0.5% |
| 21 | `norm_num` | 1487 | 0.5% |
| 22 | `show` | 1268 | 0.4% |
| 23 | `omega` | 1261 | 0.4% |
| 24 | `classical` | 1241 | 0.4% |
| 25 | `rintro` | 1150 | 0.4% |
| 26 | `simpa` | 925 | 0.3% |
| 27 | `congr` | 922 | 0.3% |
| 28 | `positivity` | 790 | 0.3% |
| 29 | `constructor` | 654 | 0.2% |
| 30 | `haveI` | 542 | 0.2% |

### Per method family (top 8 each)

| family | tactic lines | top tactics |
|---|---:|---|
| circle method / Fourier | 2670 | `have` 941, `rw` 582, `refine` 201, `exact` 153, `intro` 135, `ring` 79, `simp` 72, `calc` 62 |
| entropy decrement | 14939 | `have` 5996, `rw` 2622, `exact` 989, `intro` 565, `refine` 515, `simp` 463, `linarith` 438, `calc` 365 |
| large sieve | 1719 | `have` 560, `rw` 379, `intro` 108, `refine` 104, `exact` 101, `simp` 56, `apply` 53, `calc` 48 |
| Selberg/Brun sieve | 70161 | `have` 30175, `rw` 12048, `exact` 3793, `intro` 3238, `apply` 2283, `calc` 2277, `refine` 1686, `linarith` 1453 |
| Bombieri-Vinogradov / Siegel-Walfisz | 34728 | `have` 15469, `rw` 6451, `exact` 1867, `intro` 1431, `refine` 1416, `linarith` 1100, `calc` 1076, `set` 854 |
| zero-density / zero-free regions | 13596 | `have` 6255, `rw` 2382, `exact` 694, `intro` 614, `linarith` 575, `refine` 438, `set` 408, `calc` 379 |
| character sums / L-functions | 62463 | `have` 26196, `rw` 9869, `exact` 4046, `refine` 3588, `intro` 3335, `obtain` 2390, `linarith` 2130, `calc` 1437 |
| exponential sums | 8305 | `have` 3163, `rw` 1696, `exact` 504, `intro` 409, `refine` 391, `linarith` 237, `set` 228, `simp` 209 |
| Mertens / PNT-type | 3297 | `have` 1530, `rw` 557, `exact` 173, `linarith` 147, `intro` 127, `refine` 103, `apply` 93, `simp` 73 |
| certificates / explicit numerics | 129 | `exact` 22, `rw` 22, `have` 13, `obtain` 10, `simp` 10, `refine` 8, `intro` 6, `rintro` 6 |
| explog/lognum numeral tactic | 106 | `have` 33, `rw` 20, `exact` 15, `intro` 6, `filter_upwards` 5, `refine` 5, `nlinarith` 4, `calc` 3 |
| Matomaki-Radziwill / Halasz (short intervals) | 114488 | `have` 51850, `rw` 15812, `exact` 6676, `refine` 6523, `intro` 5710, `linarith` 5220, `obtain` 4962, `calc` 2188 |
| (no family) | 28735 | `have` 11157, `rw` 5120, `exact` 1735, `intro` 1554, `obtain` 970, `refine` 959, `set` 881, `calc` 865 |

## 3. Macro candidates (repeated normalised tactic blocks)

Blocks of 3–20 consecutive tactic lines, repeated ≥ 5 times (non-overlapping) in ≥ 3 files, maximal only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name (numbered by first appearance, so equal blocks bind alike), `#` = a numeral. 1216 candidates; top 25 by the UPPER-BOUND saving.

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

**3.** 6 lines × 16 occurrences in 13 files · lines saved ≤ **80** · e.g. `Salt/MR/DoorReceipt.lean:738` · `Salt/MR/DoorReceiptSiegelFree.lean:161`

```lean
have $1 : # * $2 ≤ Real.log (Real.log ($3.Hlo : ℝ)) := by
rw [$4]; exact flatWitFloor_design $5 $6 $2 $7
have $8 : Real.log (Real.log (($3.Hlo : ℕ) : ℝ)) ≤ # * $2 + Real.log # := by
rw [$4, flat_witFloor_eq_designBase $9 $10 $11 $12 $13 hεpin $14 $15]
exact flatDesignBase_loglog_le $9
have $16 : Real.log (Real.log (($3.Hhi : ℕ) : ℝ)) ≤ # * Real.exp (# * $2 / #) :=
```

**4.** 6 lines × 16 occurrences in 13 files · lines saved ≤ **80** · e.g. `Salt/MR/DoorReceipt.lean:748` · `Salt/MR/DoorReceiptSiegelFree.lean:171`

```lean
have $1 : (# : ℚ) / # ^ # ≤ $2.eps := by
rw [$3]
have : (# : ℚ) / # ^ # ≤ # / # := by norm_num
linarith [hεpin]
have $4 : Real.exp (# * $5) ≤ Real.log (($2.Hlo : ℕ) : ℝ) := by
rw [$6]; exact flatWitFloor_log_ge $7
```

**5.** 14 lines × 6 occurrences in 6 files · lines saved ≤ **78** · e.g. `Salt/MR/StrideDoorAllGrades.lean:5449` · `Salt/MR/StridePairReceipt.lean:2166`

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

**6.** 8 lines × 11 occurrences in 7 files · lines saved ≤ **77** · e.g. `Salt/MaynardK/JMainSplit.lean:885` · `Salt/MaynardK/JSplit.lean:963`

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

**7.** 3 lines × 38 occurrences in 26 files · lines saved ≤ **76** · e.g. `Salt/BV/AbelCore.lean:578` · `Salt/Chen/A2Weighted.lean:523`

```lean
field_simp
ring
rw [$1]
```

**8.** 5 lines × 18 occurrences in 15 files · lines saved ≤ **72** · e.g. `Salt/MR/DoorReceipt.lean:714` · `Salt/MR/DoorReceiptSiegelFree.lean:137`

```lean
have $1 : XCeilRiderStrict $2 (fun _ _ : ℕ => #) := by
intro $3 $4 $5
obtain ⟨-, -, $6⟩ := $5
simp only [Nat.cast_zero, Real.log_zero]
linarith [Real.log_natCast_nonneg $4]
```

**9.** 9 lines × 9 occurrences in 8 files · lines saved ≤ **72** · e.g. `Salt/MR/DoorReceipt.lean:745` · `Salt/MR/DoorReceiptSiegelFree.lean:168` · ⚠️ shares source lines with #4

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

**10.** 13 lines × 6 occurrences in 3 files · lines saved ≤ **72** · e.g. `Salt/MR/FlatConsumers.lean:124` · `Salt/MR/FlatDoorEpsRung2.lean:4029`

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

**11.** 3 lines × 35 occurrences in 25 files · lines saved ≤ **70** · e.g. `Salt/Chen/CountAtOp.lean:158` · `Salt/Chen/DyadicWindow.lean:92`

```lean
have $1 : (# : ℝ) < ($2 : ℝ) := by
have : (# : ℝ) ≤ ($2 : ℝ) := by exact_mod_cast $3
linarith
```

**12.** 6 lines × 14 occurrences in 13 files · lines saved ≤ **70** · e.g. `Salt/MR/DoorReceipt.lean:728` · `Salt/MR/DoorReceiptSiegelFree.lean:151`

```lean
intro $1
obtain ⟨$2, $3, $4, $5⟩ := $6 $1
have $7 := $8 $1
refine ⟨$2, $3, ?_⟩
intro $9 $10 $11 $12 $13
obtain ⟨$14, $15, $16⟩ := $5 $9 $10 $12
```

**13.** 6 lines × 14 occurrences in 12 files · lines saved ≤ **70** · e.g. `Salt/MR/FlatDoorStandoff.lean:941` · `Salt/MR/RegisterCompose.lean:184`

```lean
intro $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$13, $14, $15, $16, $17, $18, $19⟩ := $20 $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$21, $22, $23, $24, $25, $26⟩ := socketLogFrame_facts $6 $7 $19.logX_eight
have $27 : Real.exp (# * (Real.log ((($5 + $6 : ℕ)) : ℝ)) ^ ((# : ℝ) / #)) ≤ # * $8 := $11
have $28 : (# : ℝ) < # * $8 := by linarith
exact doorCapBundle_at_workingPoint_perBlock_L_gk $29 $30 $31 $23 $21 $19 $28 $10 $12
```

**14.** 6 lines × 14 occurrences in 8 files · lines saved ≤ **70** · e.g. `Salt/MR/HDoorClose.lean:345` · `Salt/MR/HDoorSupply.lean:871`

```lean
rw [Nat.card_Ioc]
have $1 := doorLadder_fit $2.x $3 $4
have $5 : doorLadder $2.x $3 $4 - doorLadder $2.x $3 ($4 + #) ≤ doorLadder $2.x $3 ($4 + #) := by
omega
exact_mod_cast $5
have $6 := doorLadder_pos $7 ($4 + #)
```

**15.** 8 lines × 10 occurrences in 9 files · lines saved ≤ **70** · e.g. `Salt/MR/DoorReceipt.lean:746` · `Salt/MR/DoorReceiptSiegelFree.lean:169` · ⚠️ shares source lines with #4, #9

```lean
intro $1 $2
have $3 : # ≤ flatDoorM $4 := flatDoorM_one_le (flat162_ge_26 $5)
have $6 : (# : ℚ) / # ^ # ≤ $7.eps := by
rw [$8]
have : (# : ℚ) / # ^ # ≤ # / # := by norm_num
linarith [hεpin]
have $9 : Real.exp (# * $4) ≤ Real.log (($7.Hlo : ℕ) : ℝ) := by
rw [$10]; exact flatWitFloor_log_ge $5
```

**16.** 15 lines × 5 occurrences in 5 files · lines saved ≤ **70** · e.g. `Salt/Goldbach/BandRows.lean:239` · `Salt/Goldbach/KerrY.lean:393`

```lean
have $1 : (# : ℝ) ≤ $2 := by linarith
have $3 : ((# ^ ($4 + #) - # : ℕ) : ℝ) * (pieceM $5 : ℝ) ≤ # * ($6 : ℝ) := by
have : ((# ^ ($4 + #) - #) * pieceM $5 : ℕ) ≤ # * $6 := $7
have $8 : (((# ^ ($4 + #) - #) * pieceM $5 : ℕ) : ℝ) ≤ ((# * $6 : ℕ) : ℝ) := by
exact_mod_cast this
push_cast at $8 ⊢; linarith [$8]
have $9 : $2 ≤ # * Real.log $6 := by
have $10 : ((# ^ ($4 + #) - # : ℕ) : ℝ) * (pieceM $5 : ℝ) ≤ # * ($6 : ℝ) := by linarith [$3]
have $11 : $2 ≤ Real.log (# * ($6 : ℝ)) := Real.log_le_log $12 $10
rw [Real.log_mul (by norm_num) (ne_of_gt $13)] at $11
linarith [$11, $14, $15]
have $16 : $2 ≤ Real.log (# * ($6 : ℝ)) := by
have $10 : ((# ^ ($4 + #) - # : ℕ) : ℝ) * (pieceM $5 : ℝ) ≤ # * ($6 : ℝ) := by linarith [$3]
exact Real.log_le_log $12 $10
have $17 : (# : ℝ) ≤ $2 := by linarith
```

**17.** 15 lines × 5 occurrences in 5 files · lines saved ≤ **70** · e.g. `Salt/Chen/ChenFinal2.lean:112` · `Salt/Chen/PriceOne.lean:331`

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

**18.** 15 lines × 5 occurrences in 5 files · lines saved ≤ **70** · e.g. `Salt/MR/M4RowsChiEnd.lean:271` · `Salt/MR/M4RowsChiEndPrime.lean:189`

```lean
have $1 := $2.eta_pos
have $3 := $2.eta_lt
have $4 := $2.one_le_Jb
have $5 := $2.one_le_G
have $6 := $2.one_le_M
have $7 : # ≤ $8 := le_trans (by norm_num) $2.A_floor
have $9 : # ≤ $10 := le_trans (one_le_calQK $8 $11 $12 $13) $2.Q_le_Xd
have $14 : calH $15 # = $15 := by simp [calH]
have $16 : (# : ℝ) ≤ calH $15 # := by rw [$14]; exact $2.H1_two
have $17 : # ≤ calP $8 $11 # := by simp only [calP]; exact Nat.one_le_two_pow
have $18 : (# : ℝ) < ((calP $8 $11 # : ℕ) : ℝ) := by
have : (# : ℝ) ≤ ((calP $8 $11 # : ℕ) : ℝ) := by exact_mod_cast $17
linarith
have $19 : calQK $8 $11 $12 # ≤ $10 := le_trans (calQK_mono $8 $5 $4) $2.Q_le_Xd
have $20 : ∀ $21 ∈ ramI (calH $15 #) (calP $8 $11 #) (calQK $8 $11 $12 #),
```

**19.** 5 lines × 17 occurrences in 15 files · lines saved ≤ **68** · e.g. `Salt/Entropy/Chowla/HloExport.lean:475` · `Salt/Entropy/Chowla/HloExportFlat.lean:314`

```lean
have $1 : $2 < $3 / (# * $4) * ($5.eps : ℝ) := by
rw [$6]
have $7 : (# : ℝ) < $3 / (# * $4) := div_pos $8 (mul_pos (by norm_num) $9)
have $10 : (# : ℝ) < $3 / (# * $4) * ($11 : ℝ) := mul_pos $7 $12
linarith [$13, $10]
```

**20.** 5 lines × 17 occurrences in 14 files · lines saved ≤ **68** · e.g. `Salt/MR/DoorReceipt.lean:823` · `Salt/MR/DoorReceiptSiegelFree.lean:81`

```lean
have $1 : $2 ≤ flatDesignBase $3 := le_flatDesignBase_of_le $4
have $5 : (# : ℝ) ≤ $3 := by linarith
have $6 : KlevF $3 ≤ # * flatDoorM $3 := KlevF_le_wideCeiling $5
obtain ⟨$7, $8, $9⟩ := $10 (KlevF $3)
obtain ⟨$11, $12⟩ := $9 $3 $13 $14 $15 $6
```

**21.** 5 lines × 17 occurrences in 13 files · lines saved ≤ **68** · e.g. `Salt/MR/FlatDoorStandoff.lean:941` · `Salt/MR/RegisterCompose.lean:184` · ⚠️ shares source lines with #13

```lean
intro $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$13, $14, $15, $16, $17, $18, $19⟩ := $20 $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$21, $22, $23, $24, $25, $26⟩ := socketLogFrame_facts $6 $7 $19.logX_eight
have $27 : Real.exp (# * (Real.log ((($5 + $6 : ℕ)) : ℝ)) ^ ((# : ℝ) / #)) ≤ # * $8 := $11
have $28 : (# : ℝ) < # * $8 := by linarith
```

**22.** 3 lines × 33 occurrences in 13 files · lines saved ≤ **66** · e.g. `Salt/MR/ArithPageLinear.lean:716` · `Salt/MR/FlatConsumers.lean:107` · ⚠️ shares source lines with #10

```lean
have $1 : (# : ℝ) < ($2 : ℝ) := by exact_mod_cast $3
have $4 : ($2 : ℝ) ≤ ((($2 + $5 : ℕ)) : ℝ) := by
push_cast; linarith [Nat.cast_nonneg ($6 := ℝ) $5]
```

**23.** 7 lines × 11 occurrences in 6 files · lines saved ≤ **66** · e.g. `Salt/Chen/ChenRows1.lean:345` · `Salt/Goldbach/BandRows.lean:274`

```lean
apply Real.sqrt_le_sqrt
have $1 : (($2 : ℝ) ^ ((# : ℝ) / #)) ^ (# : ℕ) = ($2 : ℝ) ^ ((# : ℝ) / #) := by
rw [← Real.rpow_natCast (($2 : ℝ) ^ ((# : ℝ) / #)) #, ← Real.rpow_mul $3.le,
show (# : ℝ) / # * ((# : ℕ) : ℝ) = # / # by push_cast; ring]
have $4 : (($2 : ℝ) ^ ((# : ℝ) / #) / #) ^ (# : ℕ) = ($2 : ℝ) ^ ((# : ℝ) / #) / # := by
rw [div_pow, $1]; norm_num
rw [$4]; exact $5
```

**24.** 6 lines × 13 occurrences in 5 files · lines saved ≤ **65** · e.g. `Salt/MR/FlatConsumers.lean:128` · `Salt/MR/FlatDoorEpsRung2.lean:4033` · ⚠️ shares source lines with #10, #22

```lean
have $1 : (# : ℝ) < ($2 : ℝ) := by exact_mod_cast $3
have $4 : ($2 : ℝ) ≤ ((($2 + $5 : ℕ)) : ℝ) := by
push_cast; linarith [Nat.cast_nonneg ($6 := ℝ) $5]
obtain ⟨$7, -⟩ := s13_socketBase_loglogA $8 $9
have $10 : (# : ℝ) < Real.log ((($2 + $5 : ℕ)) : ℝ) := by
have := Real.log_le_log $1 $4; linarith
```

**25.** 6 lines × 13 occurrences in 10 files · lines saved ≤ **65** · e.g. `Salt/MR/DoorReceipt.lean:561` · `Salt/MR/FlatDoorEpsChain.lean:933`

```lean
intro $1
obtain ⟨$2, $3, $4, $5⟩ := $6 $1
refine ⟨$2, $3, $4, ?_⟩
intro $7 $8 $9
obtain ⟨$10, $11, $12⟩ := $5 $7 $8 $9
refine ⟨$10, $11, ?_⟩
```

## Whitelist (data)

`abel` `absurd` `aesop` `all_goals` `and_intros` `any_goals` `apply` `apply?` `apply_fun` `apply_rules` `assumption` `assumption_mod_cast` `bound` `bound?` `by_cases` `by_contra` `by_contra!` `calc` `calc?` `cancel_denoms` `case` `cases` `cases'` `change` `choose` `classical` `clear` `congr` `congr!` `congrm` `constructor` `continuity` `contradiction` `contrapose` `contrapose!` `conv` `conv_lhs` `conv_rhs` `convert` `convert_to` `decide` `delta` `done` `dsimp` `erw` `eventually_budget` `exact` `exact?` `exact_fun_prop` `exact_mod_cast` `exacts` `exfalso` `exists` `existsi` `ext` `field_simp` `field_simp?` `filter_upwards` `fin_cases` `first` `focus` `fun_prop` `funext` `gcongr` `gcongr?` `gcongr_discharger` `generalize` `group` `have` `haveI` `induction` `induction'` `infer_instance` `interval_cases` `intro` `intros` `iterate` `left` `let` `letI` `lift` `linarith` `linarith!` `linear_combination` `measurability` `mod_cast` `mono` `native_decide` `next` `nlinarith` `nlinarith!` `nlinarith?` `noncomm_ring` `norm_cast` `norm_num` `norm_num1` `norm_num?` `nth_rewrite` `nth_rw` `obtain` `omega` `on_goal` `pick_goal` `polyrith` `positivity` `positivity?` `push_cast` `push_neg` `qify` `rcases` `refine` `refine'` `refine_lift` `rel` `rename_i` `repeat` `rewrite` `rfl` `right` `ring` `ring1` `ring_nf` `rintro` `rotate_left` `rsuffices` `rw` `rw?` `rwa` `set` `show` `simp` `simp?` `simp_all` `simp_arith` `simp_rw` `simpa` `simpa?` `skip` `sorry` `specialize` `split` `split_ands` `split_ifs` `stop` `subst` `subst_vars` `suffices` `swap` `symm` `tauto` `trans` `trivial` `try` `unfold` `unfold?` `unfold_let` `use` `with_reducible` `wlog` `zify`

Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): `Salt/Tactic/AuditAxioms.lean`, `Salt/Tactic/NlinarithSuggest.lean`.
