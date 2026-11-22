# THE TACTICS CATALOGUE — by machine (O13 item 4)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/tactics_catalogue.py` · staleness gate: `python3 scripts/tactics_catalogue.py --check`.
> Base: last commit touching `Salt/` = `5f50288f` · source digest `124f8ee20d5f7b85` (the same digest as items 1–3).
> Receipt: files 1415 · decls 23446 · with_body 23446 · tactic_lines 299194 · runs 35345 · blocks 1116.

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
| `ExpLogNum.lean` | T3 | `Salt.Tactic.exp_nat_le_of_pow_le` | 24 | qualified 24 | `MR/FarStar.lean` 4, `MR/StrideDoorAllGrades.lean` 3, `Entropy/Chowla/Step.lean` 2, `Entropy/Chowla/StrideDecrement.lean` 2 (+11 files) |
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
| `Salt.Tactic.exp_nat_le_of_pow_le` | 4 | 24 | 24 |
| `Salt.Tactic.log_le_nat_of_le_pow` | 5 | 33 | 33 |
| `Salt.Tactic.nat_le_log_of_pow_le` | 4 | 21 | 21 |

## 2. Tactic usage (first token of each tactic line)

299194 tactic lines. Top 30:

| # | tactic | lines | share |
|---:|---|---:|---:|
| 1 | `have` | 130059 | 43.5% |
| 2 | `rw` | 48445 | 16.2% |
| 3 | `exact` | 17316 | 5.8% |
| 4 | `intro` | 13906 | 4.6% |
| 5 | `refine` | 12711 | 4.2% |
| 6 | `linarith` | 10150 | 3.4% |
| 7 | `obtain` | 9195 | 3.1% |
| 8 | `calc` | 7705 | 2.6% |
| 9 | `set` | 5429 | 1.8% |
| 10 | `simp` | 5087 | 1.7% |
| 11 | `apply` | 4478 | 1.5% |
| 12 | `nlinarith` | 3261 | 1.1% |
| 13 | `unfold` | 2620 | 0.9% |
| 14 | `exact_mod_cast` | 2347 | 0.8% |
| 15 | `rcases` | 2099 | 0.7% |
| 16 | `ring` | 2045 | 0.7% |
| 17 | `push_cast` | 1917 | 0.6% |
| 18 | `field_simp` | 1853 | 0.6% |
| 19 | `by_cases` | 1632 | 0.5% |
| 20 | `rwa` | 1542 | 0.5% |
| 21 | `norm_num` | 1467 | 0.5% |
| 22 | `show` | 1254 | 0.4% |
| 23 | `classical` | 1238 | 0.4% |
| 24 | `omega` | 1230 | 0.4% |
| 25 | `rintro` | 1140 | 0.4% |
| 26 | `congr` | 917 | 0.3% |
| 27 | `simpa` | 872 | 0.3% |
| 28 | `positivity` | 785 | 0.3% |
| 29 | `constructor` | 649 | 0.2% |
| 30 | `haveI` | 542 | 0.2% |

### Per method family (top 8 each)

| family | tactic lines | top tactics |
|---|---:|---|
| circle method / Fourier | 2670 | `have` 941, `rw` 582, `refine` 201, `exact` 153, `intro` 135, `ring` 79, `simp` 72, `calc` 62 |
| entropy decrement | 14749 | `have` 5861, `rw` 2610, `exact` 977, `intro` 565, `refine` 511, `simp` 463, `linarith` 425, `obtain` 364 |
| large sieve | 1719 | `have` 560, `rw` 379, `intro` 108, `refine` 104, `exact` 101, `simp` 56, `apply` 53, `calc` 48 |
| Selberg/Brun sieve | 69895 | `have` 30035, `rw` 12017, `exact` 3780, `intro` 3236, `apply` 2283, `calc` 2267, `refine` 1685, `obtain` 1447 |
| Bombieri-Vinogradov / Siegel-Walfisz | 34726 | `have` 15468, `rw` 6451, `exact` 1867, `intro` 1431, `refine` 1416, `linarith` 1099, `calc` 1076, `set` 854 |
| zero-density / zero-free regions | 13545 | `have` 6218, `rw` 2378, `exact` 694, `intro` 612, `linarith` 569, `refine` 438, `set` 408, `calc` 379 |
| character sums / L-functions | 62361 | `have` 26119, `rw` 9861, `exact` 4046, `refine` 3588, `intro` 3331, `obtain` 2394, `linarith` 2121, `calc` 1437 |
| exponential sums | 8295 | `have` 3158, `rw` 1696, `exact` 504, `intro` 409, `refine` 391, `linarith` 232, `set` 228, `simp` 209 |
| Mertens / PNT-type | 3297 | `have` 1530, `rw` 557, `exact` 173, `linarith` 147, `intro` 127, `refine` 103, `apply` 93, `simp` 73 |
| certificates / explicit numerics | 129 | `exact` 22, `rw` 22, `have` 13, `obtain` 10, `simp` 10, `refine` 8, `intro` 6, `rintro` 6 |
| explog/lognum numeral tactic | 106 | `have` 33, `rw` 20, `exact` 15, `intro` 6, `filter_upwards` 5, `refine` 5, `nlinarith` 4, `calc` 3 |
| Matomaki-Radziwill / Halasz (short intervals) | 113118 | `have` 51096, `rw` 15625, `exact` 6635, `refine` 6519, `intro` 5636, `linarith` 5108, `obtain` 5005, `calc` 2184 |
| (no family) | 27799 | `have` 10733, `rw` 4933, `exact` 1705, `intro` 1530, `obtain` 972, `refine` 953, `set` 867, `calc` 814 |

## 3. Macro candidates (repeated normalised tactic blocks)

Blocks of 3–20 consecutive tactic lines, repeated ≥ 5 times (non-overlapping) in ≥ 3 files, maximal only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name (numbered by first appearance, so equal blocks bind alike), `#` = a numeral. 1116 candidates; top 25 by the UPPER-BOUND saving.

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

**3.** 3 lines × 38 occurrences in 26 files · lines saved ≤ **76** · e.g. `Salt/BV/AbelCore.lean:578` · `Salt/Chen/A2Weighted.lean:523`

```lean
field_simp
ring
rw [$1]
```

**4.** 5 lines × 18 occurrences in 15 files · lines saved ≤ **72** · e.g. `Salt/MR/DoorReceipt.lean:799` · `Salt/MR/DoorReceiptSiegelFree.lean:81`

```lean
have $1 : $2 ≤ flatDesignBase $3 := le_flatDesignBase_of_le $4
have $5 : (# : ℝ) ≤ $3 := by linarith
have $6 : KlevF $3 ≤ # * flatDoorM $3 := KlevF_le_wideCeiling $5
obtain ⟨$7, $8, $9⟩ := $10 (KlevF $3)
obtain ⟨$11, $12⟩ := $9 $3 $13 $14 $15 $6
```

**5.** 6 lines × 14 occurrences in 13 files · lines saved ≤ **70** · e.g. `Salt/MR/DoorReceipt.lean:716` · `Salt/MR/DoorReceiptSiegelFree.lean:144`

```lean
intro $1
obtain ⟨$2, $3, $4, $5⟩ := $6 $1
have $7 := $8 $1
refine ⟨$2, $3, ?_⟩
intro $9 $10 $11 $12 $13
obtain ⟨$14, $15, $16⟩ := $5 $9 $10 $12
```

**6.** 6 lines × 14 occurrences in 12 files · lines saved ≤ **70** · e.g. `Salt/MR/FlatDoorStandoff.lean:941` · `Salt/MR/RegisterCompose.lean:185`

```lean
intro $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$13, $14, $15, $16, $17, $18, $19⟩ := $20 $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$21, $22, $23, $24, $25, $26⟩ := socketLogFrame_facts $6 $7 $19.logX_eight
have $27 : Real.exp (# * (Real.log ((($5 + $6 : ℕ)) : ℝ)) ^ ((# : ℝ) / #)) ≤ # * $8 := $11
have $28 : (# : ℝ) < # * $8 := by linarith
exact doorCapBundle_at_workingPoint_perBlock_L_gk $29 $30 $31 $23 $21 $19 $28 $10 $12
```

**7.** 5 lines × 17 occurrences in 15 files · lines saved ≤ **68** · e.g. `Salt/Entropy/Chowla/HloExport.lean:419` · `Salt/Entropy/Chowla/HloExportFlat.lean:314`

```lean
have $1 : $2 < $3 / (# * $4) * ($5.eps : ℝ) := by
rw [$6]
have $7 : (# : ℝ) < $3 / (# * $4) := div_pos $8 (mul_pos (by norm_num) $9)
have $10 : (# : ℝ) < $3 / (# * $4) * ($11 : ℝ) := mul_pos $7 $12
linarith [$13, $10]
```

**8.** 5 lines × 17 occurrences in 13 files · lines saved ≤ **68** · e.g. `Salt/MR/FlatDoorStandoff.lean:941` · `Salt/MR/RegisterCompose.lean:185` · ⚠️ shares source lines with #6

```lean
intro $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$13, $14, $15, $16, $17, $18, $19⟩ := $20 $1 $2 $3 $4 $5 $6 $7 $8 $9 $10 $11 $12
obtain ⟨$21, $22, $23, $24, $25, $26⟩ := socketLogFrame_facts $6 $7 $19.logX_eight
have $27 : Real.exp (# * (Real.log ((($5 + $6 : ℕ)) : ℝ)) ^ ((# : ℝ) / #)) ≤ # * $8 := $11
have $28 : (# : ℝ) < # * $8 := by linarith
```

**9.** 4 lines × 22 occurrences in 19 files · lines saved ≤ **66** · e.g. `Salt/MR/DoorReceipt.lean:799` · `Salt/MR/DoorReceiptSiegelFree.lean:81` · ⚠️ shares source lines with #4

```lean
have $1 : $2 ≤ flatDesignBase $3 := le_flatDesignBase_of_le $4
have $5 : (# : ℝ) ≤ $3 := by linarith
have $6 : KlevF $3 ≤ # * flatDoorM $3 := KlevF_le_wideCeiling $5
obtain ⟨$7, $8, $9⟩ := $10 (KlevF $3)
```

**10.** 6 lines × 13 occurrences in 10 files · lines saved ≤ **65** · e.g. `Salt/MR/DoorReceipt.lean:556` · `Salt/MR/FlatDoorEpsChain.lean:933`

```lean
intro $1
obtain ⟨$2, $3, $4, $5⟩ := $6 $1
refine ⟨$2, $3, $4, ?_⟩
intro $7 $8 $9
obtain ⟨$10, $11, $12⟩ := $5 $7 $8 $9
refine ⟨$10, $11, ?_⟩
```

**11.** 9 lines × 8 occurrences in 6 files · lines saved ≤ **64** · e.g. `Salt/Entropy/Chowla/HloExport.lean:277` · `Salt/Entropy/Chowla/HloExportFlat.lean:152`

```lean
set $1 : ℝ := ∑ $2 ∈ $3 $4.eps $5, (# / ($2 : ℝ)) with $6
have $7 : $8 / Real.log ($5 : ℝ) ≤ $1 := $9 $4.eps $5 $10 $11 $12
have $13 : (# : ℝ) ≤ $1 := Finset.sum_nonneg (fun $2 _ => by positivity)
have $14 : (# : ℝ) < $1 := lt_of_lt_of_le (div_pos $15 $16) $7
have $17 : ($3 $4.eps $5).Nonempty := by
rcases ($3 $4.eps $5).$18 with $19 | $20
· exact absurd ($6.trans (by rw [$19, Finset.sum_empty])) (ne_of_gt $14)
· exact $20
set $21 : ℝ := |∫ $22, (ArithmeticFunction.liouville $22 : ℝ)
```

**12.** 8 lines × 9 occurrences in 5 files · lines saved ≤ **63** · e.g. `Salt/MR/M4BridgeBlock.lean:430` · `Salt/MR/M4RowLinear.lean:1711`

```lean
intro $1 $2 _ $3 $4 $5 $6
have $7 : # < $2 := Nat.pos_of_ne_zero (NeZero.ne $2)
obtain ⟨$8, $9, $10, $11, $12⟩ := $6
have $13 := $14 $2 $9 $3 $4 $10 $11
have $15 := $16 $2 $9 $3 $4 $10 $11
have $17 := $18 $2 $9 $3 $4 $10 $11
have $19 := $20 $2 $9 $3 $4 $10 $11
have $21 : # < $22 $2 $9 := $13
```

**13.** 8 lines × 9 occurrences in 7 files · lines saved ≤ **63** · e.g. `Salt/Entropy/Chowla/HloExport.lean:277` · `Salt/Entropy/Chowla/HloExportFlat.lean:152` · ⚠️ shares source lines with #11

```lean
set $1 : ℝ := ∑ $2 ∈ $3 $4.eps $5, (# / ($2 : ℝ)) with $6
have $7 : $8 / Real.log ($5 : ℝ) ≤ $1 := $9 $4.eps $5 $10 $11 $12
have $13 : (# : ℝ) ≤ $1 := Finset.sum_nonneg (fun $2 _ => by positivity)
have $14 : (# : ℝ) < $1 := lt_of_lt_of_le (div_pos $15 $16) $7
have $17 : ($3 $4.eps $5).Nonempty := by
rcases ($3 $4.eps $5).$18 with $19 | $20
· exact absurd ($6.trans (by rw [$19, Finset.sum_empty])) (ne_of_gt $14)
· exact $20
```

**14.** 4 lines × 20 occurrences in 11 files · lines saved ≤ **60** · e.g. `Salt/MR/FlatDoorStandoff.lean:828` · `Salt/MR/M4CapWire.lean:382`

```lean
haveI : NeZero $1 := ⟨$2.2.2.2.1.ne'⟩
have $3 : (# : ℝ) < Real.log ((($4 + $5 : ℕ)) : ℝ) := by
have := $6.logX_four
linarith
```

**15.** 6 lines × 12 occurrences in 3 files · lines saved ≤ **60** · e.g. `Salt/MR/S12Compose.lean:411` · `Salt/MR/S12ConstCompose.lean:608`

```lean
have $1 : (# : ℝ) < # * $2 := by linarith
have $3 : # * $4 ^ # = $5 / (# * $2) := by
rw [$6]
field_simp
ring
linarith [$7, $3.le, $3.ge]
```

**16.** 11 lines × 6 occurrences in 6 files · lines saved ≤ **60** · e.g. `Salt/Entropy/Chowla/HloExport.lean:243` · `Salt/Entropy/Chowla/HloExportFlat.lean:118`

```lean
have $1 : # ≤ $2 := le_trans $3.hHlo_floor $4
have $5 : # ≤ $2 := by omega
have $6 : $7 ≤ $2 := le_trans (le_max_left _ _) $8
have $9 : $10 ≤ $2 := le_trans (le_max_right _ _) $8
have $11 : (# : ℝ) ≤ ($2 : ℝ) := by exact_mod_cast $1
have $12 : (# : ℝ) < ($2 : ℝ) := by linarith
have $13 : # ≤ Real.log ($2 : ℝ) := by
rw [Real.le_log_iff_exp_le $12]
exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
have $14 : # < Real.log ($2 : ℝ) := by linarith
have $15 : Real.sqrt ($2 : ℝ) ≤ ($3.eps : ℝ) ^ # * ($2 : ℝ) / # :=
```

**17.** 11 lines × 6 occurrences in 6 files · lines saved ≤ **60** · e.g. `Salt/Entropy/Chowla/HloExport.lean:273` · `Salt/Entropy/Chowla/HloExportFlat.lean:148` · ⚠️ shares source lines with #11, #13

```lean
have $1 : (# : ℝ) ≤ # / ($2.eps : ℝ) := by
rw [le_div_iff₀ $3]; nlinarith [$4]
have $5 : # ≤ Real.log ($2.ω : ℝ) := by nlinarith [$6, $7, $1]
set $8 : ℝ := ∑ $9 ∈ $10 $2.eps $11, (# / ($9 : ℝ)) with $12
have $13 : $14 / Real.log ($11 : ℝ) ≤ $8 := $15 $2.eps $11 $16 $17 $18
have $19 : (# : ℝ) ≤ $8 := Finset.sum_nonneg (fun $9 _ => by positivity)
have $20 : (# : ℝ) < $8 := lt_of_lt_of_le (div_pos $21 $22) $13
have $23 : ($10 $2.eps $11).Nonempty := by
rcases ($10 $2.eps $11).$24 with $25 | $26
· exact absurd ($12.trans (by rw [$25, Finset.sum_empty])) (ne_of_gt $20)
· exact $26
```

**18.** 13 lines × 5 occurrences in 5 files · lines saved ≤ **60** · e.g. `Salt/SW/EFSharpMult.lean:480` · `Salt/SW/EFSharpZeros.lean:354`

```lean
set $1 : ℂ := ($2 : ℂ) - ($3 : ℂ) * $4 with $5
set $6 : ℂ := ($7 : ℂ) + ($3 : ℂ) * $4 with $8
have $9 : $1.re = $2 := by rw [$5]; simp
have $10 : $1.im = -$3 := by rw [$5]; simp
have $11 : $6.re = $7 := by rw [$8]; simp
have $12 : $6.im = $3 := by rw [$8]; simp
have $13 : DifferentiableOn ℂ $14 (closedRect $1 $6) := by
intro $15 $16
rw [closedRect, $9, $10, $11, $12, mem_reProdIm] at $16
rw [Set.uIcc_of_le $17.le] at $16
rw [Set.uIcc_of_le (by linarith : -$3 ≤ $3)] at $16
obtain ⟨$18, $19⟩ := $16
simp only [Set.mem_Icc] at $18 $19
```

**19.** 3 lines × 29 occurrences in 21 files · lines saved ≤ **58** · e.g. `Salt/MR/DoorReceipt.lean:300` · `Salt/MR/FlatDoorAllGradesBand.lean:768`

```lean
intro $1
have := $2 $1
positivity
```

**20.** 3 lines × 29 occurrences in 22 files · lines saved ≤ **58** · e.g. `Salt/MR/DoorReceipt.lean:456` · `Salt/MR/FlatDoorAllGradesBand.lean:833`

```lean
obtain ⟨$1, $2, $3, $4⟩ := door_socket_facts $5 $6
set $7 : ℝ := s12DeltaSock $8 $9 with $10
set $11 : ℝ := doorRhoOfDelta $7 with $12
```

**21.** 4 lines × 19 occurrences in 16 files · lines saved ≤ **57** · e.g. `Salt/MR/DoorReceipt.lean:800` · `Salt/MR/DoorReceiptSiegelFree.lean:82` · ⚠️ shares source lines with #4, #9

```lean
have $1 : (# : ℝ) ≤ $2 := by linarith
have $3 : KlevF $2 ≤ # * flatDoorM $2 := KlevF_le_wideCeiling $1
obtain ⟨$4, $5, $6⟩ := $7 (KlevF $2)
obtain ⟨$8, $9⟩ := $6 $2 $10 $11 $12 $3
```

**22.** 4 lines × 19 occurrences in 18 files · lines saved ≤ **57** · e.g. `Salt/MR/DoorReceipt.lean:716` · `Salt/MR/DoorReceiptSiegelFree.lean:144` · ⚠️ shares source lines with #5

```lean
intro $1
obtain ⟨$2, $3, $4, $5⟩ := $6 $1
have $7 := $8 $1
refine ⟨$2, $3, ?_⟩
```

**23.** 3 lines × 28 occurrences in 6 files · lines saved ≤ **56** · e.g. `Salt/MR/M4BridgeCover.lean:487` · `Salt/MR/M4Close.lean:562`

```lean
refine ⟨$1, $2, $3, $4, $5, $6, ?_⟩
intro $7 $8 $9 $10
obtain ⟨$11, $12, $13, $14, $15⟩ := $16 $7 $8 $9 $10
```

**24.** 6 lines × 11 occurrences in 11 files · lines saved ≤ **55** · e.g. `Salt/MR/DoorReceipt.lean:300` · `Salt/MR/FlatDoorEpsChain.lean:804` · ⚠️ shares source lines with #19

```lean
intro $1
have := $2 $1
positivity
have $3 := m4_cover_assembly_blk2_L_gk $4 $5 $6 $7
refine $8 $9 $10 $11 $12 $13 $5 $14 ?_ $15 $16
refine m4_sievedDoorSq_of_blk2_blockLen_L_gk $4
```

**25.** 12 lines × 5 occurrences in 5 files · lines saved ≤ **55** · e.g. `Salt/SW/EFSharpMult.lean:280` · `Salt/SW/EFSharpZeros.lean:151`

```lean
have $1 : (# : ℝ) < Real.log $2 := by linarith
set $3 : ℝ := # + # / Real.log $2 with $4
have $5 : # < $3 := by
have $6 : (# : ℝ) < # / Real.log $2 := by positivity
rw [$4]; linarith
have $7 : $3 < # := by
have $6 : # / Real.log $2 < # := by rw [div_lt_one $1]; linarith
rw [$4]; linarith
have $8 : (# : ℝ) < $3 := by linarith
have $9 : $3 - # = # / Real.log $2 := by rw [$4]; ring
have $10 : (# : ℝ) / # < $11 := by linarith
have $12 : (# : ℝ) < $11 := by linarith
```

## Whitelist (data)

`abel` `absurd` `aesop` `all_goals` `and_intros` `any_goals` `apply` `apply?` `apply_fun` `apply_rules` `assumption` `assumption_mod_cast` `bound` `bound?` `by_cases` `by_contra` `by_contra!` `calc` `calc?` `cancel_denoms` `case` `cases` `cases'` `change` `choose` `classical` `clear` `congr` `congr!` `congrm` `constructor` `continuity` `contradiction` `contrapose` `contrapose!` `conv` `conv_lhs` `conv_rhs` `convert` `convert_to` `decide` `delta` `done` `dsimp` `erw` `eventually_budget` `exact` `exact?` `exact_fun_prop` `exact_mod_cast` `exacts` `exfalso` `exists` `existsi` `ext` `field_simp` `field_simp?` `filter_upwards` `fin_cases` `first` `focus` `fun_prop` `funext` `gcongr` `gcongr?` `gcongr_discharger` `generalize` `group` `have` `haveI` `induction` `induction'` `infer_instance` `interval_cases` `intro` `intros` `iterate` `left` `let` `letI` `lift` `linarith` `linarith!` `linear_combination` `measurability` `mod_cast` `mono` `native_decide` `next` `nlinarith` `nlinarith!` `nlinarith?` `noncomm_ring` `norm_cast` `norm_num` `norm_num1` `norm_num?` `nth_rewrite` `nth_rw` `obtain` `omega` `on_goal` `pick_goal` `polyrith` `positivity` `positivity?` `push_cast` `push_neg` `qify` `rcases` `refine` `refine'` `refine_lift` `rel` `rename_i` `repeat` `rewrite` `rfl` `right` `ring` `ring1` `ring_nf` `rintro` `rotate_left` `rsuffices` `rw` `rw?` `rwa` `set` `show` `simp` `simp?` `simp_all` `simp_arith` `simp_rw` `simpa` `simpa?` `skip` `sorry` `specialize` `split` `split_ands` `split_ifs` `stop` `subst` `subst_vars` `suffices` `swap` `symm` `tauto` `trans` `trivial` `try` `unfold` `unfold?` `unfold_let` `use` `with_reducible` `wlog` `zify`

Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): `Salt/Tactic/AuditAxioms.lean`, `Salt/Tactic/NlinarithSuggest.lean`.
