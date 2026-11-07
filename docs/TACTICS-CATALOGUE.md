# THE TACTICS CATALOGUE — by machine (O13 item 4)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/tactics_catalogue.py` · staleness gate: `python3 scripts/tactics_catalogue.py --check`.
> Base: last commit touching `Salt/` = `698f8ede` · source digest `44f854b550989c5a` (the same digest as items 1–3).
> Receipt: files 1413 · decls 23380 · with_body 23380 · tactic_lines 313874 · runs 36898 · blocks 1448.

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

313874 tactic lines. Top 30:

| # | tactic | lines | share |
|---:|---|---:|---:|
| 1 | `have` | 137784 | 43.9% |
| 2 | `rw` | 50379 | 16.1% |
| 3 | `exact` | 17808 | 5.7% |
| 4 | `intro` | 14522 | 4.6% |
| 5 | `refine` | 13114 | 4.2% |
| 6 | `linarith` | 10930 | 3.5% |
| 7 | `obtain` | 9364 | 3.0% |
| 8 | `calc` | 8097 | 2.6% |
| 9 | `set` | 5740 | 1.8% |
| 10 | `simp` | 5237 | 1.7% |
| 11 | `apply` | 4594 | 1.5% |
| 12 | `nlinarith` | 3521 | 1.1% |
| 13 | `unfold` | 2697 | 0.9% |
| 14 | `exact_mod_cast` | 2610 | 0.8% |
| 15 | `ring` | 2188 | 0.7% |
| 16 | `rcases` | 2160 | 0.7% |
| 17 | `push_cast` | 2023 | 0.6% |
| 18 | `field_simp` | 1912 | 0.6% |
| 19 | `by_cases` | 1675 | 0.5% |
| 20 | `rwa` | 1638 | 0.5% |
| 21 | `norm_num` | 1486 | 0.5% |
| 22 | `omega` | 1307 | 0.4% |
| 23 | `show` | 1277 | 0.4% |
| 24 | `classical` | 1274 | 0.4% |
| 25 | `rintro` | 1170 | 0.4% |
| 26 | `congr` | 961 | 0.3% |
| 27 | `simpa` | 927 | 0.3% |
| 28 | `positivity` | 833 | 0.3% |
| 29 | `constructor` | 670 | 0.2% |
| 30 | `haveI` | 575 | 0.2% |

### Per method family (top 8 each)

| family | tactic lines | top tactics |
|---|---:|---|
| circle method / Fourier | 2728 | `have` 958, `rw` 598, `refine` 214, `exact` 153, `intro` 136, `ring` 79, `simp` 71, `calc` 68 |
| entropy decrement | 15686 | `have` 6354, `rw` 2749, `exact` 1008, `intro` 587, `refine` 550, `simp` 465, `linarith` 464, `calc` 391 |
| large sieve | 1719 | `have` 560, `rw` 379, `intro` 108, `refine` 104, `exact` 101, `simp` 56, `apply` 53, `calc` 48 |
| Selberg/Brun sieve | 70822 | `have` 30431, `rw` 12181, `exact` 3821, `intro` 3290, `calc` 2302, `apply` 2297, `refine` 1685, `linarith` 1486 |
| Bombieri-Vinogradov / Siegel-Walfisz | 35295 | `have` 15723, `rw` 6583, `exact` 1888, `intro` 1449, `refine` 1439, `linarith` 1109, `calc` 1107, `set` 888 |
| zero-density / zero-free regions | 13815 | `have` 6363, `rw` 2423, `exact` 702, `intro` 621, `linarith` 593, `refine` 443, `set` 408, `calc` 379 |
| character sums / L-functions | 65532 | `have` 27786, `rw` 10188, `exact` 4159, `refine` 3730, `intro` 3490, `obtain` 2494, `linarith` 2255, `calc` 1496 |
| exponential sums | 8307 | `have` 3163, `rw` 1697, `exact` 504, `intro` 410, `refine` 390, `linarith` 237, `set` 228, `simp` 209 |
| Mertens / PNT-type | 3296 | `have` 1530, `rw` 557, `exact` 173, `linarith` 147, `intro` 127, `refine` 103, `apply` 93, `simp` 73 |
| certificates / explicit numerics | 129 | `exact` 22, `rw` 22, `have` 13, `obtain` 10, `simp` 10, `refine` 8, `intro` 6, `rintro` 6 |
| explog/lognum numeral tactic | 106 | `have` 33, `rw` 20, `exact` 15, `intro` 6, `filter_upwards` 5, `refine` 5, `nlinarith` 4, `calc` 3 |
| Matomaki-Radziwill / Halasz (short intervals) | 123649 | `have` 56969, `rw` 16777, `exact` 6950, `refine` 6847, `intro` 6073, `linarith` 5702, `obtain` 5100, `calc` 2405 |
| (no family) | 29300 | `have` 11334, `rw` 5238, `exact` 1782, `intro` 1609, `obtain` 993, `refine` 971, `set` 907, `calc` 888 |

## 3. Macro candidates (repeated normalised tactic blocks)

Blocks of 3–20 consecutive tactic lines, repeated ≥ 5 times (non-overlapping) in ≥ 3 files, maximal only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name (numbered by first appearance, so equal blocks bind alike), `#` = a numeral. 1448 candidates; top 25 by the UPPER-BOUND saving.

⚠️ **Lines saved is an UPPER bound, never a price:** a macro call is ≥ 1 line; sites whose placeholders bind differently may not share a macro; generic blocks may cost more to name than to repeat.

**1.** 14 lines × 9 occurrences in 5 files · lines saved ≤ **117** · e.g. `Salt/MR/M4BridgeBlock.lean:430` · `Salt/MR/M4RowLinear.lean:1763`

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

**2.** 3 lines × 54 occurrences in 47 files · lines saved ≤ **108** · e.g. `Salt/Entropy/Chowla/StrideCircle.lean:226` · `Salt/HB/Lemma10Chain.lean:358`

```lean
congr #
push_cast
ring
```

**3.** 3 lines × 53 occurrences in 40 files · lines saved ≤ **106** · e.g. `Salt/Brun/M3Expansion.lean:159` · `Salt/BrunLower/BlockDecomp.lean:144`

```lean
intro $1 $2
rw [Finset.mem_image] at $2
obtain ⟨$3, $4, rfl⟩ := $2
```

**4.** 6 lines × 21 occurrences in 7 files · lines saved ≤ **105** · e.g. `Salt/MR/M4SocketDischarge.lean:314` · `Salt/MR/M4SocketLinear.lean:256`

```lean
have $1 : # < $2 := $3.2.2.2.1
haveI : NeZero $2 := ⟨$1.ne'⟩
have $4 := $5 $6 $7 $2 $8 $9 $10 $3
have $11 : # ≤ $9 + $10 := by
exact_mod_cast (show (# : ℝ) ≤ ((($9 + $10 : ℕ)) : ℝ) by linarith [$4.X400])
exact $12 $2 $13 $14 ($9 + $10) (# * ($9 + $10)) rfl $4.X400 (by omega) le_rfl $4.C₁_one
```

**5.** 5 lines × 26 occurrences in 6 files · lines saved ≤ **104** · e.g. `Salt/MR/M4BaseNarrow.lean:388` · `Salt/MR/M4ChiSummed.lean:787`

```lean
refine $1.trans (le_of_eq ?_)
simp only [$2]
push_cast
ring
calc (∑ $3 ∈ Finset.range ($4 / # ^ ($5 + #) + #), ∑ $6 ∈ Finset.Ioc $7 $8, $9 $5 $3 $6)
```

**6.** 4 lines × 34 occurrences in 17 files · lines saved ≤ **102** · e.g. `Salt/MR/DoorReceipt.lean:529` · `Salt/MR/FlatDoorAllGradesBand.lean:934`

```lean
unfold m4Cmax
ring
rw [$1] at $2
have $3 : # * (# * (# + # * Real.pi) ^ # * strataResidual $4 ^ #
```

**7.** 4 lines × 33 occurrences in 16 files · lines saved ≤ **99** · e.g. `Salt/MR/DoorReceipt.lean:516` · `Salt/MR/FlatDoorEpsChain.lean:917`

```lean
have $1 : (# : ℝ) ≤ arcDen # $2 := one_le_arcDen_of_regime ($3 := $3) $4
have $5 : (# : ℝ) ≤ # * (# + # * Real.pi) ^ # * strataResidual $2 ^ # := by positivity
have $6 := $7 $2 $4 $8
have $9 : # * (# + # * Real.pi) ^ # * strataResidual $2 ^ #
```

**8.** 9 lines × 12 occurrences in 5 files · lines saved ≤ **96** · e.g. `Salt/MR/M4BaseNarrow.lean:211` · `Salt/MR/M4ChiSummed.lean:341`

```lean
refine le_trans (Finset.sum_le_sum $1) ?_
rw [← Finset.mul_sum]
exact mul_le_mul_of_nonneg_left $2 (Nat.cast_nonneg _)
have $3 : ((($4 + $5 : ℕ)) : ℝ) ≤ # * ($6 : ℝ) + # := by
exact_mod_cast (show $4 + $5 ≤ # * $6 + # by omega)
have $7 : ((($4 + $5 : ℕ)) : ℝ) ≤ # * ((($6 + $5 : ℕ)) : ℝ) := by
exact_mod_cast (show $4 + $5 ≤ # * ($6 + $5) by omega)
have $8 : (# : ℝ) ≤ ((# ^ $9 : ℕ) : ℝ) ^ # := sq_nonneg _
have $10 : (# : ℝ) ≤ ((# ^ $9 : ℕ) : ℝ) ^ # / ((($6 + $5 : ℕ)) : ℝ) := by positivity
```

**9.** 17 lines × 6 occurrences in 3 files · lines saved ≤ **96** · e.g. `Salt/Chen/PieceDecomp.lean:304` · `Salt/Chen/SwitchW2.lean:261`

```lean
congr #
· rw [Finset.filter_filter]
refine congrArg Finset.card (Finset.filter_congr ?_)
intro $1 _
constructor
· rintro ⟨⟨$2, $3, $4, $5, $6, $7⟩, $8⟩
exact ⟨$2, $3, $4, $5, $6, $8⟩
· rintro ⟨$2, $3, $4, $5, $6, $8⟩
exact ⟨⟨$2, $3, $4, $5, $6, by omega⟩, $8⟩
· rw [Finset.filter_filter]
refine congrArg Finset.card (Finset.filter_congr ?_)
intro $1 _
constructor
· rintro ⟨⟨$2, $3, $4, $5, $9, $10⟩, $8⟩
exact ⟨$2, $3, $4, $5, by omega, $10⟩
· rintro ⟨$2, $3, $4, $5, $11, $10⟩
exact ⟨⟨$2, $3, $4, $5, by omega, $10⟩, by omega⟩
```

**10.** 17 lines × 6 occurrences in 6 files · lines saved ≤ **96** · e.g. `Salt/MR/CaseASocket.lean:130` · `Salt/MR/CenterSupply.lean:185`

```lean
have $1 : Real.exp # ≤ $2 := le_trans (le_max_right _ _) $3
have $4 : $5 + # ≤ $2 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) $3
have $6 : $7 ≤ $2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) $3
have $8 : (# : ℝ) ≤ $2 := le_trans twentyfive_le_exp_eight $1
have $9 : (# : ℝ) < $2 := by linarith
have $10 : $2 < (⌊$2⌋₊ : ℝ) + # := Nat.lt_floor_add_one $2
have $11 : $2 - # < ($12 : ℝ) := by
have $13 : ((⌊$2⌋₊ : ℕ) : ℝ) ≤ ($12 : ℝ) := Nat.cast_le.mpr $14
linarith
have $15 : ($12 : ℝ) ≤ # * $2 := le_trans (Nat.cast_le.mpr $16) $17
have $18 : $5 ≤ ($12 : ℝ) := by linarith
have $19 : (# : ℝ) < ($12 : ℝ) := by linarith
have $20 : (# : ℝ) ≤ ($12 : ℝ) := by linarith
have $21 : Real.log # < # := Real.log_two_lt_d9
have $22 : (# : ℝ) ≤ Real.log $2 := le_log_of_exp_le $1
have $23 : Real.log $2 - Real.log # ≤ Real.log ($12 : ℝ) := by
have $24 : Real.log ($2 / #) ≤ Real.log ($12 : ℝ) :=
```

**11.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:203` · `Salt/MR/M4SecondRoad.lean:542`

```lean
exact_mod_cast $1
have $2 : $3.x / (# * $3.ω) ≤ $4 := by
rw [$5]
exact doorLadder_ge_x_div_four_omega ($6 := $6) $3.hω $7 (by omega)
have $8 : $4 ≤ $3.x := by
rw [$5]
exact doorLadder_le_start $9 ($10 + #)
have $11 : (# : ℝ) ≤ ($3.Hhi : ℝ) := by
have $1 : # ≤ $3.Hhi := le_trans $3.hHlo_floor $3.hHlohi
exact_mod_cast $1
have $12 : (# : ℝ) ≤ Real.log ($3.Hhi : ℝ) := by
have $13 : Real.exp # ≤ ($3.Hhi : ℝ) := by linarith only [$11, Real.exp_one_lt_d9]
exact (Real.le_log_iff_exp_le (by linarith)).mpr $13
have $14 : # * ($3.ω : ℝ) * ($3.Hhi : ℝ) ≤ ($3.x : ℝ) := by
have $15 := $3.hheadroom'
have $16 : ((($3.x / $3.ω : ℕ)) : ℝ) ≤ ($3.x : ℝ) / ($3.ω : ℝ) := Nat.cast_div_le
have $17 : (# : ℝ) ≤ Real.log ($3.Hhi : ℝ) * Real.log ($3.Hhi : ℝ) := by
nlinarith only [$12]
have $18 : # * ($3.Hhi : ℝ) ≤ ($3.x : ℝ) / ($3.ω : ℝ) := by
calc # * ($3.Hhi : ℝ) = # * ($3.Hhi : ℝ) * # := by ring
```

**12.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:200` · `Salt/MR/M4SecondRoad.lean:539` · ⚠️ shares source lines with #11

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
have $14 : (# : ℝ) ≤ Real.log ($2.Hhi : ℝ) := by
have $15 : Real.exp # ≤ ($2.Hhi : ℝ) := by linarith only [$13, Real.exp_one_lt_d9]
exact (Real.le_log_iff_exp_le (by linarith)).mpr $15
have $16 : # * ($2.ω : ℝ) * ($2.Hhi : ℝ) ≤ ($2.x : ℝ) := by
have $17 := $2.hheadroom'
have $18 : ((($2.x / $2.ω : ℕ)) : ℝ) ≤ ($2.x : ℝ) / ($2.ω : ℝ) := Nat.cast_div_le
have $19 : (# : ℝ) ≤ Real.log ($2.Hhi : ℝ) * Real.log ($2.Hhi : ℝ) := by
```

**13.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:202` · `Salt/MR/M4SecondRoad.lean:541` · ⚠️ shares source lines with #11, #12

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
have $12 : (# : ℝ) ≤ Real.log ($2.Hhi : ℝ) := by
have $13 : Real.exp # ≤ ($2.Hhi : ℝ) := by linarith only [$11, Real.exp_one_lt_d9]
exact (Real.le_log_iff_exp_le (by linarith)).mpr $13
have $14 : # * ($2.ω : ℝ) * ($2.Hhi : ℝ) ≤ ($2.x : ℝ) := by
have $15 := $2.hheadroom'
have $16 : ((($2.x / $2.ω : ℕ)) : ℝ) ≤ ($2.x : ℝ) / ($2.ω : ℝ) := Nat.cast_div_le
have $17 : (# : ℝ) ≤ Real.log ($2.Hhi : ℝ) * Real.log ($2.Hhi : ℝ) := by
nlinarith only [$12]
have $18 : # * ($2.Hhi : ℝ) ≤ ($2.x : ℝ) / ($2.ω : ℝ) := by
```

**14.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:201` · `Salt/MR/M4SecondRoad.lean:540` · ⚠️ shares source lines with #11, #12, #13

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
have $13 : (# : ℝ) ≤ Real.log ($2.Hhi : ℝ) := by
have $14 : Real.exp # ≤ ($2.Hhi : ℝ) := by linarith only [$12, Real.exp_one_lt_d9]
exact (Real.le_log_iff_exp_le (by linarith)).mpr $14
have $15 : # * ($2.ω : ℝ) * ($2.Hhi : ℝ) ≤ ($2.x : ℝ) := by
have $16 := $2.hheadroom'
have $17 : ((($2.x / $2.ω : ℕ)) : ℝ) ≤ ($2.x : ℝ) / ($2.ω : ℝ) := Nat.cast_div_le
have $18 : (# : ℝ) ≤ Real.log ($2.Hhi : ℝ) * Real.log ($2.Hhi : ℝ) := by
nlinarith only [$13]
```

**15.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4Gauss.lean:877` · `Salt/MR/M4RowLinear.lean:9332`

```lean
linarith [$1]
have $2 : # ≤ $3 / $4 := (Nat.le_div_iff_mul_le $5).mpr (by omega)
have $6 : # < $3 / $4 - # := by omega
have $7 : # ≤ $3 / $4 := (Nat.le_div_iff_mul_le $5).mpr (by omega)
have $8 : (($3 / $4 - # : ℕ) : ℝ) = (($3 / $4 : ℕ) : ℝ) - # := by
have $9 : # ≤ $3 / $4 := by omega
rw [Nat.cast_sub $9, Nat.cast_one]
have $10 : ($3 : ℝ) ≤ ($4 : ℝ) * (($3 / $4 : ℕ) : ℝ) + ($4 : ℝ) := by
have $11 := (Nat.cast_le ($12 := ℝ)).mpr (le_mul_div_add ($3 := $3) ($4 := $4) $5)
push_cast at $11
linarith
have $13 : (# : ℝ) ≤ (($3 / $4 - # : ℕ) : ℝ) := Nat.cast_nonneg _
have $14 : (# : ℝ) ≤ (($3 / $4 - # : ℕ) : ℝ) := by
have $15 : (# : ℕ) ≤ $3 / $4 - # := by omega
exact_mod_cast $15
have $16 : capL $17 $4 ≤ $3 / $4 - # := capL_le_dilated_base $5 $18 $19
have $20 : Real.sqrt ($21 : ℝ) ≤ (($3 / $4 - # : ℕ) : ℝ) := by
rw [$8]
have $22 : # * ($4 : ℝ) ≤ Real.sqrt ($21 : ℝ) := by linarith
have $23 := mul_le_mul_of_nonneg_right $22
```

**16.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:194` · `Salt/MR/M4SecondRoad.lean:533` · ⚠️ shares source lines with #11, #12, #13, #14

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
have $15 : (# : ℝ) ≤ Real.log ($4.Hhi : ℝ) := by
have $16 : Real.exp # ≤ ($4.Hhi : ℝ) := by linarith only [$14, Real.exp_one_lt_d9]
exact (Real.le_log_iff_exp_le (by linarith)).mpr $16
have $17 : # * ($4.ω : ℝ) * ($4.Hhi : ℝ) ≤ ($4.x : ℝ) := by
have $18 := $4.hheadroom'
have $19 : ((($4.x / $4.ω : ℕ)) : ℝ) ≤ ($4.x : ℝ) / ($4.ω : ℝ) := Nat.cast_div_le
```

**17.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4Gauss.lean:876` · `Salt/MR/M4RowLinear.lean:9331` · ⚠️ shares source lines with #15

```lean
rw [$1] at $2
linarith [$3]
have $4 : # ≤ $5 / $6 := (Nat.le_div_iff_mul_le $7).mpr (by omega)
have $8 : # < $5 / $6 - # := by omega
have $9 : # ≤ $5 / $6 := (Nat.le_div_iff_mul_le $7).mpr (by omega)
have $10 : (($5 / $6 - # : ℕ) : ℝ) = (($5 / $6 : ℕ) : ℝ) - # := by
have $11 : # ≤ $5 / $6 := by omega
rw [Nat.cast_sub $11, Nat.cast_one]
have $12 : ($5 : ℝ) ≤ ($6 : ℝ) * (($5 / $6 : ℕ) : ℝ) + ($6 : ℝ) := by
have $13 := (Nat.cast_le ($14 := ℝ)).mpr (le_mul_div_add ($5 := $5) ($6 := $6) $7)
push_cast at $13
linarith
have $15 : (# : ℝ) ≤ (($5 / $6 - # : ℕ) : ℝ) := Nat.cast_nonneg _
have $16 : (# : ℝ) ≤ (($5 / $6 - # : ℕ) : ℝ) := by
have $17 : (# : ℕ) ≤ $5 / $6 - # := by omega
exact_mod_cast $17
have $18 : capL $19 $6 ≤ $5 / $6 - # := capL_le_dilated_base $7 $20 $21
have $22 : Real.sqrt ($23 : ℝ) ≤ (($5 / $6 - # : ℕ) : ℝ) := by
rw [$10]
have $24 : # * ($6 : ℝ) ≤ Real.sqrt ($23 : ℝ) := by linarith
```

**18.** 8 lines × 13 occurrences in 6 files · lines saved ≤ **91** · e.g. `Salt/MR/M4BaseNarrow.lean:299` · `Salt/MR/M4ChiSummed.lean:635`

```lean
exact mul_nonneg (mul_nonneg $1 (sq_nonneg _)) (Nat.cast_nonneg _)
rw [Nat.not_lt] at $2
have $3 : # ≤ $4 := by omega
have $5 : $6 ≤ # * $4 := by omega
have $7 : ($8 : ℝ) ≤ # * ($4 : ℝ) := by
exact_mod_cast (show $8 ≤ # * $4 by omega)
have $9 : (# : ℝ) ≤ ($4 : ℝ) := Nat.cast_nonneg _
set $10 := Nat.log # $8 with $11
```

**19.** 8 lines × 13 occurrences in 6 files · lines saved ≤ **91** · e.g. `Salt/MR/M4BaseNarrow.lean:358` · `Salt/MR/M4ChiSummed.lean:747`

```lean
nlinarith only [$1, $2, (Nat.cast_nonneg _ : # ≤ ↑(# ^ $3))]
refine le_trans (Finset.sum_le_sum $4) ?_
rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
have $5 : (($6 + # ^ ($3 + #) * $7 - ($8 + # ^ ($3 + #) * $7) : ℕ) : ℝ) ≤ ($8 : ℝ) := by
have $9 : $6 + # ^ ($3 + #) * $7 - ($8 + # ^ ($3 + #) * $7) ≤ $8 := by omega
exact_mod_cast $9
have $10 : (# : ℝ) ≤ ((# ^ $3 : ℕ) : ℝ) ^ # := by positivity
nlinarith only [$5, sq_nonneg ↑(# ^ $3)]
```

**20.** 3 lines × 45 occurrences in 24 files · lines saved ≤ **90** · e.g. `Salt/MR/DoorReceipt.lean:529` · `Salt/MR/FlatDoorAllGradesBand.lean:934` · ⚠️ shares source lines with #6

```lean
unfold m4Cmax
ring
rw [$1] at $2
```

**21.** 4 lines × 30 occurrences in 3 files · lines saved ≤ **90** · e.g. `Salt/MR/A3Middle.lean:497` · `Salt/MR/ThmA2Linear.lean:1165`

```lean
have $1 : (# : ℝ) < $2 := lt_of_lt_of_le (Real.exp_pos #) $3
have $4 : (# : ℝ) ≤ Real.exp # := by
exact_mod_cast Salt.Tactic.le_exp_nat_of_le_pow # (by norm_num)
have $5 : Real.exp # ≤ Real.log $2 :=
```

**22.** 4 lines × 30 occurrences in 7 files · lines saved ≤ **90** · e.g. `Salt/MR/M4BaseNarrow.lean:389` · `Salt/MR/M4ChiSummed.lean:788` · ⚠️ shares source lines with #5

```lean
simp only [$1]
push_cast
ring
calc (∑ $2 ∈ Finset.range ($3 / # ^ ($4 + #) + #), ∑ $5 ∈ Finset.Ioc $6 $7, $8 $4 $2 $5)
```

**23.** 10 lines × 10 occurrences in 8 files · lines saved ≤ **90** · e.g. `Salt/MR/CenterGrade.lean:36` · `Salt/MR/FarClose.lean:96`

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

**24.** 18 lines × 5 occurrences in 3 files · lines saved ≤ **85** · e.g. `Salt/MR/BandRatedSocket.lean:106` · `Salt/MR/HDoorSupply.lean:1270`

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

**25.** 18 lines × 5 occurrences in 3 files · lines saved ≤ **85** · e.g. `Salt/MR/M4Gauss.lean:790` · `Salt/MR/M4RowLinear.lean:9245`

```lean
have $1 : (# : ℝ) ≤ ($2 : ℝ) := by exact_mod_cast $3
have := Real.log_le_log (by linarith) $4
linarith
by_cases $5 : $6 < $7
· rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
positivity
rw [Nat.not_lt] at $5
have $8 : $9 ≤ $7 := by omega
have $10 : ($9 : ℝ) ≤ ($7 : ℝ) := by exact_mod_cast $8
have $11 : (# : ℝ) ≤ ($9 : ℝ) := by linarith only [$12, $13]
have $14 : # ≤ $9 := by
have : (# : ℝ) ≤ ($9 : ℝ) := by linarith
exact_mod_cast this
have $15 : # < $16 := by omega
have $17 : (# : ℝ) < ($16 : ℝ) := by exact_mod_cast $15
have $18 : ($9 : ℝ) ≤ ($16 : ℝ) := by exact_mod_cast $19
have $20 : (# : ℝ) ≤ Real.sqrt ($16 : ℝ) := Real.sqrt_nonneg _
have $21 : Real.sqrt ($16 : ℝ) ^ # = ($16 : ℝ) := Real.sq_sqrt $17.le
```

## Whitelist (data)

`abel` `absurd` `aesop` `all_goals` `and_intros` `any_goals` `apply` `apply?` `apply_fun` `apply_rules` `assumption` `assumption_mod_cast` `bound` `bound?` `by_cases` `by_contra` `by_contra!` `calc` `calc?` `cancel_denoms` `case` `cases` `cases'` `change` `choose` `classical` `clear` `congr` `congr!` `congrm` `constructor` `continuity` `contradiction` `contrapose` `contrapose!` `conv` `conv_lhs` `conv_rhs` `convert` `convert_to` `decide` `delta` `done` `dsimp` `erw` `eventually_budget` `exact` `exact?` `exact_fun_prop` `exact_mod_cast` `exacts` `exfalso` `exists` `existsi` `ext` `field_simp` `field_simp?` `filter_upwards` `fin_cases` `first` `focus` `fun_prop` `funext` `gcongr` `gcongr?` `gcongr_discharger` `generalize` `group` `have` `haveI` `induction` `induction'` `infer_instance` `interval_cases` `intro` `intros` `iterate` `left` `let` `letI` `lift` `linarith` `linarith!` `linear_combination` `measurability` `mod_cast` `mono` `native_decide` `next` `nlinarith` `nlinarith!` `nlinarith?` `noncomm_ring` `norm_cast` `norm_num` `norm_num1` `norm_num?` `nth_rewrite` `nth_rw` `obtain` `omega` `on_goal` `pick_goal` `polyrith` `positivity` `positivity?` `push_cast` `push_neg` `qify` `rcases` `refine` `refine'` `refine_lift` `rel` `rename_i` `repeat` `rewrite` `rfl` `right` `ring` `ring1` `ring_nf` `rintro` `rotate_left` `rsuffices` `rw` `rw?` `rwa` `set` `show` `simp` `simp?` `simp_all` `simp_arith` `simp_rw` `simpa` `simpa?` `skip` `sorry` `specialize` `split` `split_ands` `split_ifs` `stop` `subst` `subst_vars` `suffices` `swap` `symm` `tauto` `trans` `trivial` `try` `unfold` `unfold?` `unfold_let` `use` `with_reducible` `wlog` `zify`

Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): `Salt/Tactic/AuditAxioms.lean`, `Salt/Tactic/NlinarithSuggest.lean`.
