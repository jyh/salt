# THE TACTICS CATALOGUE — by machine (O13 item 4)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/tactics_catalogue.py` · staleness gate: `python3 scripts/tactics_catalogue.py --check`.
> Base: last commit touching `Salt/` = `35fae493` · source digest `b99d141a7baa2402` (the same digest as items 1–3).
> Receipt: files 1414 · decls 23420 · with_body 23420 · tactic_lines 310335 · runs 36397 · blocks 1377.

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
| `ExpLogNum.lean` | T3 | `Salt.Tactic.le_exp_nat_of_le_pow` | 45 | qualified 45 | `MR/StrideDoorAllGrades.lean` 8, `MR/RegisterRepair.lean` 4, `MR/S13CapEps.lean` 4, `MR/S13CapGateLinearLH.lean` 4 (+19 files) |
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
| `Salt.Tactic.le_exp_nat_of_le_pow` | 11 | 45 | 45 |
| `Salt.Tactic.exp_nat_le_of_pow_le` | 4 | 27 | 27 |
| `Salt.Tactic.log_le_nat_of_le_pow` | 5 | 34 | 34 |
| `Salt.Tactic.nat_le_log_of_pow_le` | 4 | 21 | 21 |

## 2. Tactic usage (first token of each tactic line)

310335 tactic lines. Top 30:

| # | tactic | lines | share |
|---:|---|---:|---:|
| 1 | `have` | 135802 | 43.8% |
| 2 | `rw` | 50031 | 16.1% |
| 3 | `exact` | 17711 | 5.7% |
| 4 | `intro` | 14324 | 4.6% |
| 5 | `refine` | 13069 | 4.2% |
| 6 | `linarith` | 10760 | 3.5% |
| 7 | `obtain` | 9328 | 3.0% |
| 8 | `calc` | 7988 | 2.6% |
| 9 | `set` | 5701 | 1.8% |
| 10 | `simp` | 5204 | 1.7% |
| 11 | `apply` | 4594 | 1.5% |
| 12 | `nlinarith` | 3448 | 1.1% |
| 13 | `unfold` | 2643 | 0.9% |
| 14 | `exact_mod_cast` | 2499 | 0.8% |
| 15 | `rcases` | 2154 | 0.7% |
| 16 | `ring` | 2099 | 0.7% |
| 17 | `push_cast` | 1997 | 0.6% |
| 18 | `field_simp` | 1883 | 0.6% |
| 19 | `by_cases` | 1657 | 0.5% |
| 20 | `rwa` | 1635 | 0.5% |
| 21 | `norm_num` | 1486 | 0.5% |
| 22 | `omega` | 1287 | 0.4% |
| 23 | `show` | 1277 | 0.4% |
| 24 | `classical` | 1265 | 0.4% |
| 25 | `rintro` | 1170 | 0.4% |
| 26 | `congr` | 955 | 0.3% |
| 27 | `simpa` | 915 | 0.3% |
| 28 | `positivity` | 815 | 0.3% |
| 29 | `constructor` | 670 | 0.2% |
| 30 | `haveI` | 566 | 0.2% |

### Per method family (top 8 each)

| family | tactic lines | top tactics |
|---|---:|---|
| circle method / Fourier | 2726 | `have` 958, `rw` 597, `refine` 215, `exact` 153, `intro` 135, `ring` 79, `simp` 71, `calc` 68 |
| entropy decrement | 15672 | `have` 6354, `rw` 2742, `exact` 1008, `intro` 580, `refine` 557, `simp` 465, `linarith` 464, `calc` 391 |
| large sieve | 1719 | `have` 560, `rw` 379, `intro` 108, `refine` 104, `exact` 101, `simp` 56, `apply` 53, `calc` 48 |
| Selberg/Brun sieve | 70764 | `have` 30431, `rw` 12152, `exact` 3821, `intro` 3261, `calc` 2302, `apply` 2297, `refine` 1714, `linarith` 1486 |
| Bombieri-Vinogradov / Siegel-Walfisz | 35295 | `have` 15723, `rw` 6583, `exact` 1888, `intro` 1449, `refine` 1439, `linarith` 1109, `calc` 1107, `set` 888 |
| zero-density / zero-free regions | 13811 | `have` 6363, `rw` 2421, `exact` 702, `intro` 619, `linarith` 593, `refine` 445, `set` 408, `calc` 379 |
| character sums / L-functions | 64099 | `have` 26975, `rw` 10060, `exact` 4109, `refine` 3694, `intro` 3436, `obtain` 2482, `linarith` 2190, `calc` 1463 |
| exponential sums | 8305 | `have` 3163, `rw` 1696, `exact` 504, `intro` 409, `refine` 391, `linarith` 237, `set` 228, `simp` 209 |
| Mertens / PNT-type | 3296 | `have` 1530, `rw` 557, `exact` 173, `linarith` 147, `intro` 127, `refine` 103, `apply` 93, `simp` 73 |
| certificates / explicit numerics | 129 | `exact` 22, `rw` 22, `have` 13, `obtain` 10, `simp` 10, `refine` 8, `intro` 6, `rintro` 6 |
| explog/lognum numeral tactic | 106 | `have` 33, `rw` 20, `exact` 15, `intro` 6, `filter_upwards` 5, `refine` 5, `nlinarith` 4, `calc` 3 |
| Matomaki-Radziwill / Halasz (short intervals) | 120202 | `have` 54987, `rw` 16475, `exact` 6853, `refine` 6756, `intro` 5921, `linarith` 5532, `obtain` 5110, `calc` 2296 |
| (no family) | 29290 | `have` 11334, `rw` 5233, `exact` 1782, `intro` 1604, `obtain` 988, `refine` 976, `set` 907, `calc` 888 |

## 3. Macro candidates (repeated normalised tactic blocks)

Blocks of 3–20 consecutive tactic lines, repeated ≥ 5 times (non-overlapping) in ≥ 3 files, maximal only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name (numbered by first appearance, so equal blocks bind alike), `#` = a numeral. 1377 candidates; top 25 by the UPPER-BOUND saving.

⚠️ **Lines saved is an UPPER bound, never a price:** a macro call is ≥ 1 line; sites whose placeholders bind differently may not share a macro; generic blocks may cost more to name than to repeat.

**1.** 3 lines × 54 occurrences in 47 files · lines saved ≤ **108** · e.g. `Salt/Entropy/Chowla/StrideCircle.lean:226` · `Salt/HB/Lemma10Chain.lean:358`

```lean
congr #
push_cast
ring
```

**2.** 6 lines × 21 occurrences in 7 files · lines saved ≤ **105** · e.g. `Salt/MR/M4SocketDischarge.lean:314` · `Salt/MR/M4SocketLinear.lean:256`

```lean
have $1 : # < $2 := $3.2.2.2.1
haveI : NeZero $2 := ⟨$1.ne'⟩
have $4 := $5 $6 $7 $2 $8 $9 $10 $3
have $11 : # ≤ $9 + $10 := by
exact_mod_cast (show (# : ℝ) ≤ ((($9 + $10 : ℕ)) : ℝ) by linarith [$4.X400])
exact $12 $2 $13 $14 ($9 + $10) (# * ($9 + $10)) rfl $4.X400 (by omega) le_rfl $4.C₁_one
```

**3.** 17 lines × 6 occurrences in 3 files · lines saved ≤ **96** · e.g. `Salt/Chen/PieceDecomp.lean:304` · `Salt/Chen/SwitchW2.lean:261`

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

**4.** 17 lines × 6 occurrences in 6 files · lines saved ≤ **96** · e.g. `Salt/MR/CaseASocket.lean:130` · `Salt/MR/CenterSupply.lean:185`

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

**5.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:181` · `Salt/MR/M4SecondRoad.lean:528`

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

**6.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:178` · `Salt/MR/M4SecondRoad.lean:525` · ⚠️ shares source lines with #5

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

**7.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:180` · `Salt/MR/M4SecondRoad.lean:527` · ⚠️ shares source lines with #5, #6

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

**8.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:179` · `Salt/MR/M4SecondRoad.lean:526` · ⚠️ shares source lines with #5, #6, #7

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

**9.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4Gauss.lean:900` · `Salt/MR/M4RowLinear.lean:7217`

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

**10.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4RowSpineLinear.lean:172` · `Salt/MR/M4SecondRoad.lean:519` · ⚠️ shares source lines with #5, #6, #7, #8

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

**11.** 20 lines × 5 occurrences in 3 files · lines saved ≤ **95** · e.g. `Salt/MR/M4Gauss.lean:899` · `Salt/MR/M4RowLinear.lean:7216` · ⚠️ shares source lines with #9

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

**12.** 10 lines × 10 occurrences in 8 files · lines saved ≤ **90** · e.g. `Salt/MR/CenterGrade.lean:36` · `Salt/MR/FarClose.lean:96`

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

**13.** 18 lines × 5 occurrences in 3 files · lines saved ≤ **85** · e.g. `Salt/MR/BandRatedSocket.lean:106` · `Salt/MR/HDoorSupply.lean:1270`

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

**14.** 18 lines × 5 occurrences in 3 files · lines saved ≤ **85** · e.g. `Salt/MR/M4Gauss.lean:813` · `Salt/MR/M4RowLinear.lean:7130`

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

**15.** 7 lines × 14 occurrences in 11 files · lines saved ≤ **84** · e.g. `Salt/MR/CenterGrade.lean:36` · `Salt/MR/FarClose.lean:96` · ⚠️ shares source lines with #12

```lean
have $1 : (# : ℝ) < $2 := by linarith
have $3 : (# : ℝ) < Real.sqrt $2 := Real.sqrt_pos.mpr $1
have $4 : (# : ℝ) ≤ Real.sqrt $2 := by
have $5 : Real.sqrt # = # := by
rw [show (# : ℝ) = # ^ # from by norm_num, Real.sqrt_sq (by norm_num)]
rw [← $5]
exact Real.sqrt_le_sqrt $6
```

**16.** 8 lines × 12 occurrences in 8 files · lines saved ≤ **84** · e.g. `Salt/MaynardK/ISplit.lean:303` · `Salt/MaynardK/JMainSplit.lean:885`

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

**17.** 13 lines × 7 occurrences in 6 files · lines saved ≤ **84** · e.g. `Salt/Chen/ChenFinal2.lean:112` · `Salt/Chen/PriceOne.lean:329`

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

**18.** 15 lines × 6 occurrences in 5 files · lines saved ≤ **84** · e.g. `Salt/Chen/ChenFinal2.lean:112` · `Salt/Chen/PriceOne.lean:329` · ⚠️ shares source lines with #17

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

**19.** 6 lines × 16 occurrences in 13 files · lines saved ≤ **80** · e.g. `Salt/MR/DoorReceipt.lean:738` · `Salt/MR/DoorReceiptSiegelFree.lean:161`

```lean
have $1 : # * $2 ≤ Real.log (Real.log ($3.Hlo : ℝ)) := by
rw [$4]; exact flatWitFloor_design $5 $6 $2 $7
have $8 : Real.log (Real.log (($3.Hlo : ℕ) : ℝ)) ≤ # * $2 + Real.log # := by
rw [$4, flat_witFloor_eq_designBase $9 $10 $11 $12 $13 hεpin $14 $15]
exact flatDesignBase_loglog_le $9
have $16 : Real.log (Real.log (($3.Hhi : ℕ) : ℝ)) ≤ # * Real.exp (# * $2 / #) :=
```

**20.** 6 lines × 16 occurrences in 13 files · lines saved ≤ **80** · e.g. `Salt/MR/DoorReceipt.lean:748` · `Salt/MR/DoorReceiptSiegelFree.lean:171`

```lean
have $1 : (# : ℚ) / # ^ # ≤ $2.eps := by
rw [$3]
have : (# : ℚ) / # ^ # ≤ # / # := by norm_num
linarith [hεpin]
have $4 : Real.exp (# * $5) ≤ Real.log (($2.Hlo : ℕ) : ℝ) := by
rw [$6]; exact flatWitFloor_log_ge $7
```

**21.** 7 lines × 13 occurrences in 8 files · lines saved ≤ **78** · e.g. `Salt/MR/S15Compose.lean:1297` · `Salt/MR/S16Budget.lean:1760`

```lean
have $1 : s15Arm $2 $3 $4.Hhi $4.ω ≤ $4.x := by omega
have $5 : $6 $4.Hhi $4.ω ≤ $4.x := by omega
obtain ⟨$7, $8, $9⟩ := regime_floors_of_U1 $10 $11 $12
refine ⟨$4, $13, $7, $5, $14, ?_⟩
intro $15 $16
obtain ⟨$17, $18, $19, $20⟩ := $21 $15 $16.mfloor
intro $22
```

**22.** 7 lines × 13 occurrences in 8 files · lines saved ≤ **78** · e.g. `Salt/MR/FlatDoorEpsRung2.lean:647` · `Salt/MR/S13CapEps.lean:437`

```lean
obtain ⟨-, $1⟩ := regime_Hfloor_of_loglogFloor50 (le_trans $2 $3)
have $4 : # ≤ $5 := le_trans $6.hHlo_floor $3
have $7 : (# : ℝ) ≤ ($5 : ℝ) := by exact_mod_cast $4
have $8 : (# : ℝ) < Real.log ($5 : ℝ) := Real.log_pos (by linarith)
have $9 : Real.exp # ≤ Real.log ($5 : ℝ) := by
have := Real.exp_le_exp.mpr $1
rwa [Real.exp_log $8] at this
```

**23.** 14 lines × 6 occurrences in 6 files · lines saved ≤ **78** · e.g. `Salt/MR/StrideDoorAllGrades.lean:5465` · `Salt/MR/StridePairReceipt.lean:2106`

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

**24.** 8 lines × 11 occurrences in 6 files · lines saved ≤ **77** · e.g. `Salt/MR/BandRatedSocket.lean:109` · `Salt/MR/CofactorBulk.lean:211` · ⚠️ shares source lines with #13

```lean
have $1 : (# : ℝ) ≤ Real.log ($2.Hlo : ℝ) := cofk_log_big $3
have $4 : Real.exp (# : ℝ) ≤ Real.log ($2.Hlo : ℝ) := by
have $5 := Real.exp_le_exp.mpr $6
rwa [Real.exp_log (by linarith)] at $5
have $7 : (# : ℝ) ^ # ≤ Real.exp (# : ℝ) := by
have $5 := cofk_exp_quartic ($8 := (# : ℝ)) (by norm_num)
have $9 : (# : ℝ) ≤ (# + (# : ℝ) / #) ^ # := by norm_num
linarith
```

**25.** 12 lines × 7 occurrences in 3 files · lines saved ≤ **77** · e.g. `Salt/MR/LFunctionInvShallow.lean:469` · `Salt/MR/MobiusChiRate.lean:406`

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

## Whitelist (data)

`abel` `absurd` `aesop` `all_goals` `and_intros` `any_goals` `apply` `apply?` `apply_fun` `apply_rules` `assumption` `assumption_mod_cast` `bound` `bound?` `by_cases` `by_contra` `by_contra!` `calc` `calc?` `cancel_denoms` `case` `cases` `cases'` `change` `choose` `classical` `clear` `congr` `congr!` `congrm` `constructor` `continuity` `contradiction` `contrapose` `contrapose!` `conv` `conv_lhs` `conv_rhs` `convert` `convert_to` `decide` `delta` `done` `dsimp` `erw` `eventually_budget` `exact` `exact?` `exact_fun_prop` `exact_mod_cast` `exacts` `exfalso` `exists` `existsi` `ext` `field_simp` `field_simp?` `filter_upwards` `fin_cases` `first` `focus` `fun_prop` `funext` `gcongr` `gcongr?` `gcongr_discharger` `generalize` `group` `have` `haveI` `induction` `induction'` `infer_instance` `interval_cases` `intro` `intros` `iterate` `left` `let` `letI` `lift` `linarith` `linarith!` `linear_combination` `measurability` `mod_cast` `mono` `native_decide` `next` `nlinarith` `nlinarith!` `nlinarith?` `noncomm_ring` `norm_cast` `norm_num` `norm_num1` `norm_num?` `nth_rewrite` `nth_rw` `obtain` `omega` `on_goal` `pick_goal` `polyrith` `positivity` `positivity?` `push_cast` `push_neg` `qify` `rcases` `refine` `refine'` `refine_lift` `rel` `rename_i` `repeat` `rewrite` `rfl` `right` `ring` `ring1` `ring_nf` `rintro` `rotate_left` `rsuffices` `rw` `rw?` `rwa` `set` `show` `simp` `simp?` `simp_all` `simp_arith` `simp_rw` `simpa` `simpa?` `skip` `sorry` `specialize` `split` `split_ands` `split_ifs` `stop` `subst` `subst_vars` `suffices` `swap` `symm` `tauto` `trans` `trivial` `try` `unfold` `unfold?` `unfold_let` `use` `with_reducible` `wlog` `zify`

Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): `Salt/Tactic/AuditAxioms.lean`, `Salt/Tactic/NlinarithSuggest.lean`.
