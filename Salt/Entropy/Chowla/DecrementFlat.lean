/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE FLAT ENTROPY-DECREMENT HEADLINE (freeze item F-2)

The flat twin of `entropy_decrement` (Tao 1509.05422 Lemma 3.1): in a
`ChowlaRegimeFlat` there is an admissible window width `H ∈ [H₋, H₊]` with
`a ∣ H` at which the Liouville/residue mutual information is below the FLAT
decrement threshold

    κ = H / (A · log H)          (in place of  H / (log H · logloglog H)).

The argument is the SAME Tao argument at a different threshold, exactly as
KAPPA-SCOPE said, and it composes out of three landed-shaped pieces:

* the flat telescope step (`tower_step_ofFlat`) — `step_ineq_3_11Flat` at
  `H = H_j`, `k = ⌊2·A·log H_j⌋₊`, fused with the failure hypothesis and the
  FLAT multiplier arithmetic `flat_hkey` (`TowerFlat.lean`): the two error terms
  `(ε²·log 4)/k` and `1/(4·A·L)` together fit inside HALF the flat per-step drop
  `1/(2·A·L)` — the flat tower funds its own threshold (FLAT-REF probe F4);
* the telescoped bound (`tower_telescopeFlat`) — summing over `j < Jf`;
* the endpoints — the per-symbol ceiling `e(H₀) ≤ log 2` and floor `0 ≤ e(H_J)`
  are the LANDED `entropy_per_symbol_le` / `entropy_nonneg_per_symbol`, reached
  through `R.toChowlaRegime`, and the crossing is the regime field `hJconF`.

Everything is ADDITIVE: `Tower.lean`, `Endpoints.lean` and `Decrement.lean` are
byte-untouched, and the landed `entropy_decrement` stays landed beside this.
-/
import Salt.Entropy.Chowla.StepFlat
import Salt.Entropy.Chowla.Endpoints

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### The per-symbol entropy and mutual information along the flat tower -/

/-- The per-symbol Liouville-window entropy at flat tower level `j`. -/
noncomputable def towerEntropyFlat (R : ChowlaRegimeFlat) (j : ℕ) : ℝ :=
  H[liouvilleWindow (chowlaTowerFlat R.A R.a R.Hlo j) ; logMeasure R.x R.ω]
    / (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)

/-- The mutual information `𝕀(X_{H_j} : Y_{H_j})` at flat tower level `j`. -/
noncomputable def towerMIFlat (R : ChowlaRegimeFlat) (j : ℕ) : ℝ :=
  I[liouvilleWindow (chowlaTowerFlat R.A R.a R.Hlo j)
      : residueWindow R.eps (chowlaTowerFlat R.A R.a R.Hlo j) ; logMeasure R.x R.ω]

/-! ### The flat telescope step -/

/-- **The abstract flat per-step drop.**  `step_ineq_3_11Flat` at `(H, k = m)`
    fused with the failure hypothesis and the FLAT multiplier arithmetic
    `flat_hkey` (`(ε²log4)/m ≤ 1/(4·A·L)` from `m > 2AL − 1`, `A ≥ 1`, `ε ≤ 1/2`,
    `L ≥ 15`).  The exchange closes with room to spare: the `ε`-term and the
    shift slot are each HALF the drop (FLAT-REF probe F4). -/
lemma tower_step_ofFlat (R : ChowlaRegimeFlat) {H m : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : m * H ≤ R.Hhi) (ha : R.a ∣ H) (hm : 2 ≤ m)
    (hmL : 2 * R.A * Real.log H - 1 < (m : ℝ))
    (hdec : (H : ℝ) / (R.A * Real.log H)
        < I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]) :
    H[liouvilleWindow (m * H) ; logMeasure R.x R.ω] / ((m : ℝ) * H)
        - H[liouvilleWindow H ; logMeasure R.x R.ω] / (H : ℝ)
      ≤ -(1 / (2 * R.A * Real.log H)) := by
  have hk1 : 1 ≤ m := le_trans (by norm_num) hm
  have hstep := step_ineq_3_11Flat R hH hcpl ha hk1
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHRle : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHfloor
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH15 : (15 : ℝ) ≤ Real.log (H : ℝ) := (tower_log_bounds hHfloor).1
  set lg := Real.log (H : ℝ) with hlgdef
  have hlgpos : (0 : ℝ) < lg := by linarith
  have hApos : (0 : ℝ) < R.A := R.hApos
  have hA1 : (1 : ℝ) ≤ R.A := R.hA1
  have hDpos : (0 : ℝ) < R.A * lg := mul_pos hApos hlgpos
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hepsR : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have heps1R : (R.eps : ℝ) ≤ 1 / 2 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr R.heps1
    push_cast at hc; linarith
  -- the FLAT multiplier arithmetic
  have hkey : (R.eps : ℝ) ^ 2 * Real.log 4 / (m : ℝ) ≤ 1 / (4 * R.A * lg) :=
    flat_hkey hepsR heps1R hA1 hlogH15 hmL
  -- the mutual-information decrement: `1/(A·L) < I/H`
  have hMH : 1 / (R.A * lg)
      < I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] / (H : ℝ) := by
    rw [div_lt_iff₀ hDpos] at hdec
    rw [div_lt_div_iff₀ hDpos hHpos, one_mul]; exact hdec
  have hAne : R.A ≠ 0 := ne_of_gt hApos
  have hlgne : lg ≠ 0 := ne_of_gt hlgpos
  have he1 : 1 / (R.A * lg) = 2 * (1 / (2 * R.A * lg)) := by field_simp
  have he2 : 1 / (4 * R.A * lg) = (1 / 2) * (1 / (2 * R.A * lg)) := by field_simp; norm_num
  linarith [hstep, hkey, hMH, he1, he2]

/-- **The flat telescope step**: the per-symbol entropy drops by at least the
    `towerDropSumFlat` summand `1/(2·A·log H_j)` at each level `j < Jf`, under the
    failure hypothesis at `H_j`. -/
lemma tower_stepFlat (R : ChowlaRegimeFlat) {j : ℕ} (hj : j < R.Jf)
    (hdecj : (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)
        / (R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)) < towerMIFlat R j) :
    towerEntropyFlat R (j + 1) - towerEntropyFlat R j
      ≤ -(1 / (2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ))) := by
  simp only [towerMIFlat] at hdecj
  have hHj : R.Hlo ≤ chowlaTowerFlat R.A R.a R.Hlo j := chowlaTowerFlat_ge R j
  have hfloor : 4000000 ≤ chowlaTowerFlat R.A R.a R.Hlo j := chowlaTowerFlat_floor R j
  have hmult := flatMul_ge_two R.hA1 hfloor
  have hrec : chowlaTowerFlat R.A R.a R.Hlo (j + 1)
      = (⌊2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)⌋₊)
        * chowlaTowerFlat R.A R.a R.Hlo j := by
    rw [chowlaTowerFlat_succ]; ring
  have hcpl : (⌊2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)⌋₊)
      * chowlaTowerFlat R.A R.a R.Hlo j ≤ R.Hhi := by
    rw [← hrec]; exact chowlaTowerFlat_le_Hhi R (by omega)
  have hmL := Nat.sub_one_lt_floor
      (2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ))
  have key := tower_step_ofFlat R hHj hcpl (dvd_chowlaTowerFlat R.A R.a R.Hlo j) hmult hmL hdecj
  simp only [towerEntropyFlat]
  rw [hrec, Nat.cast_mul]
  exact key

/-- **The flat conditional telescoped bound.**  If the flat headline fails at
    every tower level `j < Jf`, the top-level per-symbol entropy is below the base
    by the full flat telescoped decrement. -/
theorem tower_telescopeFlat (R : ChowlaRegimeFlat)
    (hdec : ∀ j, j < R.Jf →
      (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)
          / (R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)) < towerMIFlat R j) :
    towerEntropyFlat R R.Jf
      ≤ towerEntropyFlat R 0 - towerDropSumFlat R.A R.a R.Hlo R.Jf := by
  have hstep : ∀ j ∈ Finset.range R.Jf,
      towerEntropyFlat R (j + 1) - towerEntropyFlat R j
        ≤ -(1 / (2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ))) :=
    fun j hj => tower_stepFlat R (Finset.mem_range.mp hj) (hdec j (Finset.mem_range.mp hj))
  have htel := Finset.sum_range_sub (towerEntropyFlat R) R.Jf
  have hsum := Finset.sum_le_sum hstep
  have hneg : ∑ j ∈ Finset.range R.Jf,
        -(1 / (2 * R.A * Real.log (chowlaTowerFlat R.A R.a R.Hlo j : ℝ)))
      = - towerDropSumFlat R.A R.a R.Hlo R.Jf := by
    simp only [towerDropSumFlat, Finset.sum_neg_distrib]
  rw [htel, hneg] at hsum
  linarith [hsum]

/-! ### The flat contradiction assembly -/

/-- The per-flat-tower-level mutual-information bound predicate.  Reducible,
    hence defeq to the explicit inequality of the flat headline. -/
private abbrev MIboundFlat (R : ChowlaRegimeFlat) (H : ℕ) : Prop :=
  I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]
    ≤ (H : ℝ) / (R.A * Real.log H)

/-- **The flat contradiction assembly.**  Hypothesis-parametric on the flat
    telescope and the flat tower-range facts, exactly as the landed
    `decrement_exists_of_tower` is on wave III. -/
theorem decrement_exists_of_towerFlat (R : ChowlaRegimeFlat)
    (htele :
      (∀ j < R.Jf, ¬ MIboundFlat R (chowlaTowerFlat R.A R.a R.Hlo j)) →
        H[liouvilleWindow (chowlaTowerFlat R.A R.a R.Hlo R.Jf); logMeasure R.x R.ω]
            / (chowlaTowerFlat R.A R.a R.Hlo R.Jf : ℝ)
          ≤ H[liouvilleWindow (chowlaTowerFlat R.A R.a R.Hlo 0); logMeasure R.x R.ω]
              / (chowlaTowerFlat R.A R.a R.Hlo 0 : ℝ)
            - towerDropSumFlat R.A R.a R.Hlo R.Jf)
    (hmono : ∀ j, j < R.Jf →
      R.Hlo ≤ chowlaTowerFlat R.A R.a R.Hlo j ∧ chowlaTowerFlat R.A R.a R.Hlo j ≤ R.Hhi) :
    ∃ H, R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]
        ≤ (H : ℝ) / (R.A * Real.log H) := by
  have hbase : 1 ≤ chowlaTowerFlat R.A R.a R.Hlo 0 := by
    have ha := R.ha
    have hlo := R.hHlo_floor
    change 1 ≤ R.a * R.Hlo
    exact Nat.mul_pos (by omega) (by omega)
  have hnotall : ¬ ∀ j < R.Jf, ¬ MIboundFlat R (chowlaTowerFlat R.A R.a R.Hlo j) := by
    intro hall
    have hdrop := htele hall
    have hceil := entropy_per_symbol_le R.toChowlaRegime (chowlaTowerFlat R.A R.a R.Hlo 0) hbase
    have hfloor :=
      entropy_nonneg_per_symbol R.toChowlaRegime (chowlaTowerFlat R.A R.a R.Hlo R.Jf)
    have hcon := R.hJconF
    linarith
  obtain ⟨j, hjJ, hb⟩ := decrement_of_not_forall hnotall
  exact ⟨chowlaTowerFlat R.A R.a R.Hlo j, (hmono j hjJ).1, (hmono j hjJ).2,
    dvd_chowlaTowerFlat R.A R.a R.Hlo j, hb⟩

/-- **THE FLAT HEADLINE** (freeze F-2; Tao 1509.05422 Lemma 3.1 at the flat
    threshold).  In a flat Chowla regime there is an admissible window width
    `H ∈ [H₋, H₊]` with `a ∣ H` at which the Liouville/residue mutual information
    is below `H / (A · log H)`.

    The landed `entropy_decrement` is untouched and stays landed beside this. -/
theorem entropy_decrementFlat (R : ChowlaRegimeFlat) :
    ∃ H : ℕ, R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]
        ≤ (H : ℝ) / (R.A * Real.log H) :=
  decrement_exists_of_towerFlat R
    (fun hfail => tower_telescopeFlat R (fun j hj => not_le.mp (hfail j hj)))
    (fun j hj => ⟨chowlaTowerFlat_ge R j, chowlaTowerFlat_le_Hhi R (le_of_lt hj)⟩)

end Salt.Entropy.Chowla

