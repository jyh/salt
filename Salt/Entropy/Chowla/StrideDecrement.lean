/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F4a — THE DECREMENT AT THE STRIDE MEASURE (the D-block)

Tao arXiv:1509.05422 Lemma 3.1 (the entropy decrement along the tower) at the pushforward
measure `logMeasureAff a x ω := (logMeasure x ω).map (a * ·)` (`StrideFork.lean:75`): the twins
of `Step` / `InvarianceHead` / `Tower` / `Endpoints` / `Decrement`, stated at a plain
`ChowlaRegime` whose stride `R.a` is read INTO THE MEASURE.  The consumer is the affine shell
(`StrideShell.lean`), whose `hI` slot is this file's headline `entropy_decrementAff`.

THE DESIGN (price brief `2026-09-04-math-PRICE-lbv-w2S-F4-entropy-half.md` §3, D-block).  Of the
78 declarations of the nine landed files, 11 proofs touch a `logMeasure`-named lemma and 9 of
those only the probability instance (`isProbabilityMeasure_logMeasure` ↦
`isProbabilityMeasure_logMeasureAff`, `StrideFork.lean:104`); the two structural ones are
`base_l1_le` (`Step.lean:89`) and `joint_l1_le` (`Step.lean:255`).  ⭐ THE ONE DESIGN LEMMA:
`logMeasureAff_map_shift` — a shift by `t` with `a ∣ t` of the stride measure IS the plain
measure shifted by `t/a` and then pushed along `a * ·` (`a·(n + t/a) = a·n + t`).  So the joint
`ℓ¹` value at the stride measure is the generic pushforward contraction `map_real_l1_le`
(`Step.lean:70`, `P Q : Measure ℕ`-generic) at `g := jointWindow ∘ (a * ·)` composed with
`base_l1_le` VERBATIM at the shift `t/a` and `harmonic_shift_l1_le` verbatim: `base_l1_le` needs
NO twin, and the bound `8·(jH/a)·ω/x ≤ 8·jH·ω/x` lets `R.hheadroom'` discharge the Fannes
budget exactly as at stride `1`.  `R.a ∣ H` is CONSUMED here (F1's B7) where the landed lane
carries and discards it (`Step.lean:418` `_ha`, `Tower.lean:161`).  Everything else — the
concatenation `condEntropy_kwindow_le` (`liouvilleWindow_block` + chain rules), the reduction
spine, the tower arithmetic, the endpoints (`entropy_liouvilleWindow_le` is already `∀ μ`,
`Windows.lean:62`) — is a copy with the measure renamed.

⛔ Degenerate values (the W4 law): `a = 0` makes `logMeasureAff 0 x ω` the Dirac mass at `0`;
every statement below reads the stride as `R.a` with `R.ha : 1 ≤ R.a`, and the free-`a` lemmas
(`logMeasureAff_map_shift`, the instance) are true at `a = 0` as stated (`0 ∣ t ↔ t = 0`).
`H = 0` inherits the landed lane's degeneracy (the tower never produces it: `hHlo_floor`).
At `R.a = 1` every statement is the landed one through `logMeasureAff_one`
(`entropy_decrementAff_one` is the receipt).

HONEST LABEL.  Nothing here produces a door, proves an estimate about the affine correlation,
or bears on twin primes.  Every declaration below except the instance is statement-only at the
freeze (sorry-bodied, recipe in the docstring), built as a module through `../saltbuild.sh`; NO
executor fires before the helm's refuter verdict.  ⛔ MERGE FENCE (iron rule 2):
`math/lbv-w2s-f4a` never reaches `main` until every obligation in the four F4a files lands
sorry-free.
-/
import Salt.Entropy.Chowla.StridePair
import Salt.Entropy.Chowla.Decrement
import Mathlib

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## F4-D0 — the two plumbing facts every twin needs -/

/-- **F4-D0a (class A, LANDED AT THE FREEZE — an `instance`).**  The stride measure has finite
support: `finiteSupport_of_comp` (`Salt/Entropy/Measure.lean:150`, a LEMMA, not an instance —
so this declaration is mandatory: without it every `integrable_of_finiteSupport _` at
`logMeasureAff` fails to resolve) at the landed `instFiniteSupport (logMeasure x ω)`
(`LogMeasure.lean:80`).  ⛔ It gives `FiniteSupport` ONLY, not `IsFiniteMeasure`:
`integrable_of_finiteSupport _` demands BOTH, and the latter comes only through
`isProbabilityMeasure_logMeasureAff` under the ambient `hx hω` instance (v1.1, verdict A3). -/
instance finiteSupport_logMeasureAff (a x ω : ℕ) : FiniteSupport (logMeasureAff a x ω) := by
  unfold logMeasureAff
  exact finiteSupport_of_comp (measurable_from_nat)

/-- **F4-D0b (class B) — THE DESIGN LEMMA: a shift pulls through the pushforward.**  For
`a ∣ t`, shifting the stride measure by `t` is shifting the plain measure by `t / a` and then
pushing along `a * ·`, because `a * (n + t / a) = a * n + t` (`Nat.mul_add`,
`Nat.mul_div_cancel' hdvd`).  Recipe: `unfold logMeasureAff; rw [Measure.map_map
(measurable_of_countable _) measurable_from_nat, Measure.map_map measurable_from_nat
(measurable_of_countable _)]; congr 1; funext n; simp only [Function.comp]; rw [Nat.mul_add,
Nat.mul_div_cancel' hdvd]`.  True at `a = 0` (then `t = 0`). -/
theorem logMeasureAff_map_shift (a x ω t : ℕ) (hdvd : a ∣ t) :
    (logMeasureAff a x ω).map (fun n => n + t)
      = ((logMeasure x ω).map (fun n => n + t / a)).map (fun n => a * n) := by
  sorry

/-! ## F4-D1 — the joint-law `ℓ¹` value at the stride measure (the one twin with content) -/

/-- **F4-D1 (class B) — the joint `ℓ¹` estimate at the stride measure.**  The twin of
`joint_l1_le` (`Step.lean:255`) with the SAME bound `8·(jH)·ω/x`; `R.a ∣ H` is CONSUMED.
Recipe: set `t' := j * H / R.a` (so `R.a ∣ j * H` by `Dvd.dvd.mul_left`, and `t' ≤ j * H`);
rewrite the shifted joint law by `logMeasureAff_map_shift` and `Measure.map_map` into
`((logMeasure R.x R.ω).map (· + t')).map (jointWindow R.eps H 0 ∘ (R.a * ·))`, and the base
joint law into `(logMeasure R.x R.ω).map (jointWindow R.eps H 0 ∘ (R.a * ·))` (`unfold
logMeasureAff; Measure.map_map`); then the landed body of `joint_l1_le` VERBATIM with `g :=
jointWindow R.eps H 0 ∘ (R.a * ·)` (measurable by `measurable_of_countable`; its range sits in
`jointSupport` by `jointWindow_mem_jointSupport`), `A := Finset.Ioc 0 (R.x + t')`, the two
nullities from `logMeasure_apply` as at `Step.lean:266-284`; `map_real_l1_le` (`Step.lean:70`),
then `base_l1_le R.hx R.hω R.hωx` at `t'` and `harmonic_shift_l1_le R.hx R.hω R.hωx` at `t'`,
finally `8·t'·ω/x ≤ 8·(jH)·ω/x` by `Nat.div_le_self` and `gcongr`. -/
theorem joint_l1_le_aff (R : ChowlaRegime) (H j : ℕ) (hdvd : R.a ∣ H) :
    (∑ s ∈ jointSupport R.eps H,
      |(((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map
            (jointWindow R.eps H 0)).real {s}
        - ((logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
      ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by
  sorry

/-! ## F4-D2 — the reduction spine and the Fannes bridge at the stride measure -/

/-- **F4-D2a (class A).**  `condEntropy_shift_reduction` (`InvarianceHead.lean:108`) with the
measure renamed: its only `logMeasure` use is the probability instance (`:114`), supplied here
by `haveI : IsProbabilityMeasure (logMeasure R.x R.ω) := isProbabilityMeasure_logMeasure R.hx
R.hω` and the instance `isProbabilityMeasure_logMeasureAff`; the body (`chain_rule`,
`jointWindow_zero`, `entropy_comp_of_injective` + `jointRelabel_injective`,
`jointWindow_zero_comp_shift`, `entropy_def`, `Measure.map_map`) is measure-generic. -/
theorem condEntropy_shift_reduction_aff (R : ChowlaRegime) (H j : ℕ) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      - H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
    = Hm[((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)]
      - Hm[(logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)] := by
  sorry

/-- **F4-D2b (class A).**  `condEntropy_shift_le_of_l1` (`InvarianceHead.lean:150`) with the
measure renamed (in `hd` too): the two nullities from `jointWindow_mem_jointSupport` and
`Measure.map_apply`, the Fannes bridge `entropy_sub_le_of_l1` (`Fannes.lean:190`, `μ ν`-generic),
and `condEntropy_shift_reduction_aff`; the only `logMeasure` use was the instance (`:161`). -/
theorem condEntropy_shift_le_of_l1_aff (R : ChowlaRegime) (H j : ℕ) (d : ℝ)
    (hd : d = ∑ s ∈ jointSupport R.eps H,
      |(((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map
            (jointWindow R.eps H 0)).real {s}
        - ((logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
    (hd1 : d ≤ Real.exp (-1))
    (hbudget : d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
        ≤ (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        + (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  sorry

/-- **F4-D2c (class A) — the D-d headline at the stride measure.**  `condEntropy_shift_le`
(`Step.lean:417`) with `joint_l1_le_aff` (which CONSUMES `ha`) in place of `joint_l1_le` and
`condEntropy_shift_le_of_l1_aff` in place of `condEntropy_shift_le_of_l1`; the budget arithmetic
(`budget_real`, `log_jointSupport_card_le`, `R.hheadroom'`) is verbatim — the bound is the
landed `8·(jH)·ω/x`. -/
theorem condEntropy_shift_le_aff (R : ChowlaRegime) {H k j : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (hj : j < k) (ha : R.a ∣ H) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        + (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  sorry

/-- **F4-D2d (class A) — conditional concatenation subadditivity at the stride measure.**
`condEntropy_kwindow_le` (`Step.lean:641`): `liouvilleWindow_block` (a pointwise identity in the
sample), `condEntropy_comp_of_injective` and `condEntropy_finPi_le` (both `μ`-generic,
`Step.lean:513/566`); the only `logMeasure` use was the instance (`:647`). -/
theorem condEntropy_kwindow_le_aff (R : ChowlaRegime) (H k : ℕ) :
    H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ ∑ b ∈ Finset.range k,
          H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] := by
  sorry

/-- **F4-D2e (class A) — the (3.11) per-step inequality at the stride measure.**
`step_ineq_3_11` (`Step.lean:696`) with `condEntropy_kwindow_le_aff` and
`condEntropy_shift_le_aff` (`ha` forwarded, now consumed); the residue ceiling
`entropy_residueWindow_le_log_PH` (`PrimeWindow.lean:65`) is `∀ μ`. -/
theorem step_ineq_3_11_aff (R : ChowlaRegime) {H k : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (ha : R.a ∣ H) (hk : 1 ≤ k) :
    H[liouvilleWindow (k * H) ; logMeasureAff R.a R.x R.ω] / ((k : ℝ) * H)
      ≤ H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ)
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] / (H : ℝ)
        + ((R.eps : ℝ) ^ 2 * Real.log 4) / (k : ℝ)
        + 1 / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  sorry

/-! ## F4-D3 — the tower at the stride measure -/

/-- **F4-D3a (def).**  The per-symbol window entropy at tower level `j`, at the stride measure:
`towerEntropy` (`Tower.lean:137`) with the measure renamed. -/
noncomputable def towerEntropyAff (R : ChowlaRegime) (j : ℕ) : ℝ :=
  H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo j) ; logMeasureAff R.a R.x R.ω]
    / (chowlaTower R.C0 R.a R.Hlo j : ℝ)

/-- **F4-D3b (def).**  The mutual information at tower level `j`, at the stride measure:
`towerMI` (`Tower.lean:142`) with the measure renamed. -/
noncomputable def towerMIAff (R : ChowlaRegime) (j : ℕ) : ℝ :=
  I[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo j)
      : residueWindow R.eps (chowlaTower R.C0 R.a R.Hlo j) ; logMeasureAff R.a R.x R.ω]

/-- **F4-D3c (class A) — the abstract per-step drop.**  `tower_step_of` (`Tower.lean:152`) with
`step_ineq_3_11_aff`; the multiplier arithmetic is verbatim (measure-free). -/
lemma tower_step_of_aff (R : ChowlaRegime) {H m : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : m * H ≤ R.Hhi) (ha : R.a ∣ H) (hm : 2 ≤ m)
    (hmL : (R.C0 : ℝ) * Real.log H * Real.log (Real.log (Real.log H)) - 1 < (m : ℝ))
    (hdec : (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))
        < I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]) :
    H[liouvilleWindow (m * H) ; logMeasureAff R.a R.x R.ω] / ((m : ℝ) * H)
        - H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ)
      ≤ -(1 / (2 * Real.log H * Real.log (Real.log (Real.log H)))) := by
  sorry

/-- **F4-D3d (class A) — the telescope step.**  `tower_step` (`Tower.lean:210`) with
`tower_step_of_aff`; `dvd_chowlaTower R.C0 R.a R.Hlo j` supplies `ha` (`Tower.lean:234`),
`chowlaTower_ge`/`chowlaTower_le_Hhi`/`tower_mult_ge_two`/`chowlaTower_succ` verbatim. -/
lemma tower_step_aff (R : ChowlaRegime) {j : ℕ} (hj : j < R.J)
    (hdecj : (chowlaTower R.C0 R.a R.Hlo j : ℝ)
        / (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
      < towerMIAff R j) :
    towerEntropyAff R (j + 1) - towerEntropyAff R j
      ≤ -(1 / (2 * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))) := by
  sorry

/-- **F4-D3e (class A) — the conditional telescoped bound.**  `tower_telescope`
(`Tower.lean:246`) with `tower_step_aff`: `Finset.sum_range_sub`, `Finset.sum_le_sum`,
`towerDropSum` unfolded — measure-free. -/
theorem tower_telescope_aff (R : ChowlaRegime)
    (hdec : ∀ j, j < R.J →
      (chowlaTower R.C0 R.a R.Hlo j : ℝ)
          / (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
        < towerMIAff R j) :
    towerEntropyAff R R.J ≤ towerEntropyAff R 0 - towerDropSum R.C0 R.a R.Hlo R.J := by
  sorry

/-! ## F4-D4 — the endpoints at the stride measure -/

/-- **F4-D4a (class A).**  `entropy_per_symbol_le` (`Endpoints.lean:41`):
`entropy_liouvilleWindow_le H (logMeasureAff R.a R.x R.ω)` — the landed lemma is `∀ μ`
(`Windows.lean:62`). -/
theorem entropy_per_symbol_le_aff (R : ChowlaRegime) (H : ℕ) (hH : 1 ≤ H) :
    H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ) ≤ Real.log 2 := by
  sorry

/-- **F4-D4b (class A).**  `entropy_nonneg_per_symbol` (`Endpoints.lean:51`):
`div_nonneg (entropy_nonneg _ _) (Nat.cast_nonneg _)`. -/
theorem entropy_nonneg_per_symbol_aff (R : ChowlaRegime) (H : ℕ) :
    0 ≤ H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ) := by
  sorry

/-- **F4-D4c (class A).**  `mutualInfo_window_nonneg` (`Endpoints.lean:61`):
`mutualInfo_nonneg (measurable_liouvilleWindow H) (measurable_residueWindow R.eps H) _`. -/
theorem mutualInfo_window_nonneg_aff (R : ChowlaRegime) (H : ℕ) :
    0 ≤ I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] := by
  sorry

/-- **F4-D4d (class A) — the mutual information is symmetric at the stride measure.**  The
consumer (`StrideShell`) states `hI` with the residue window FIRST, as `outer_combine_h` does
(`OuterCombine.lean:632`), while the decrement produces it window-first; `mutualInfo_comm
(measurable_liouvilleWindow H) (measurable_residueWindow R.eps H) _` (the twin of the private
`mutualInfo_window_comm_flat`, `SpineFlat.lean:54`). -/
theorem mutualInfo_window_comm_aff (R : ChowlaRegime) (H : ℕ) :
    I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      = I[residueWindow R.eps H : liouvilleWindow H ; logMeasureAff R.a R.x R.ω] := by
  sorry

/-- The per-tower-level mutual-information bound predicate at the stride measure
(`Endpoints.lean:82`'s `MIbound` with the measure renamed); reducible, hence defeq to the
explicit inequality of `entropy_decrementAff`. -/
private abbrev MIboundAff (R : ChowlaRegime) (H : ℕ) : Prop :=
  I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
    ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))

/-- **F4-D4e (class A) — the contradiction assembly.**  `decrement_exists_of_tower`
(`Endpoints.lean:98`) with `entropy_per_symbol_le_aff`, `entropy_nonneg_per_symbol_aff`,
`R.hJcon`, `decrement_of_not_forall`, `dvd_chowlaTower` — the `towerEntropyAff`/`towerMIAff`
spellings unfold (defeq) to the raw `H[…]`/`I[…]` this statement uses, as at stride `1`.
⭐ The witness's range is exported at TAO'S RANGE `R.a * R.Hlo ≤ H` (the tower's base is
`a·Hlo`, `Regime.lean:38`; the affine seam `contradiction_of_mrtDoorXiL2AffW` reads
`R.a * R.Hlo ≤ H`, `StridePair.lean:390`), which the landed `R.Hlo ≤ H` does not give: `hmono`
carries it, from `chowlaTower_eq_base_one` + `chowlaTower_ge_base R.hC0 (4·10⁶ ≤ R.a * R.Hlo) j`
(the `StridePair.lean:150-156` script). -/
theorem decrement_exists_of_tower_aff (R : ChowlaRegime)
    (htele :
      (∀ j < R.J, ¬ MIboundAff R (chowlaTower R.C0 R.a R.Hlo j)) →
        H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo R.J); logMeasureAff R.a R.x R.ω]
            / (chowlaTower R.C0 R.a R.Hlo R.J : ℝ)
          ≤ H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo 0); logMeasureAff R.a R.x R.ω]
              / (chowlaTower R.C0 R.a R.Hlo 0 : ℝ)
            - towerDropSum R.C0 R.a R.Hlo R.J)
    (hmono : ∀ j, j < R.J →
      R.a * R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j ∧ chowlaTower R.C0 R.a R.Hlo j ≤ R.Hhi) :
    ∃ H, R.a * R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
  sorry

/-! ## F4-D5 — THE HEADLINE: Lemma 3.1 at the stride measure -/

/-- **F4-D5 (class A) — THE AFFINE DECREMENT (Tao Lemma 3.1 at the tuple `(λ(a·n + j))_j`).**
In any Chowla regime there is an admissible window width `H ∈ [H₋, H₊]` with `a ∣ H` at which
the window/residue mutual information UNDER THE STRIDE MEASURE is below the decrement
threshold.  Term-mode, as `entropy_decrement` (`Decrement.lean:49`):
`decrement_exists_of_tower_aff R (fun hfail => tower_telescope_aff R (fun j hj => not_le.mp
(hfail j hj))) (fun j hj => ⟨hbase j, chowlaTower_le_Hhi R (le_of_lt hj)⟩)` with `hbase j :
R.a * R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j` by `chowlaTower_eq_base_one` + `chowlaTower_ge_base`
(the range is TAO'S, `R.a * R.Hlo ≤ H`, not the landed `R.Hlo ≤ H` — see F4-D4e).
The regime is the crown's `Ra` (`StridePairReceipt.lean:2121`), a plain regime with a fitting,
crossing tower at stride `a` — nothing flat is read. -/
theorem entropy_decrementAff (R : ChowlaRegime) :
    ∃ H : ℕ, R.a * R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
  sorry

/-- **F4-D5a (class A) — the stride-`1` receipt, RESTATED v1.1 (verdict A2(d)) at the MEASURE
level.**  At `R.a = 1` the mutual information at the stride measure IS the landed one, at every
`H`: `rw [hR1, logMeasureAff_one]`.  The v1 form was an `Iff` between the two decrement theorems'
conclusions — two landed-or-frozen theorems, unable to fail; here `logMeasureAff_one` is
LOAD-BEARING and the receipt is the object the decrement's twin actually changes. -/
theorem entropy_decrementAff_one (R : ChowlaRegime) (hR1 : R.a = 1) (H : ℕ) :
    I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      = I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
  sorry

end Salt.Entropy.Chowla
