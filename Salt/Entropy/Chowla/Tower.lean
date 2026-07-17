/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The tower instantiation (Chowla / entropy-decrement spine, wave III)

Instantiates the concatenation step `step_ineq_3_11` along the regime's tower
`chowlaTower` (Tao 1509.05422 §3, p.19–20).  Three groups:

* **tower arithmetic** — the multiplier `⌊C₀ log H logloglog H⌋₊ ≥ 2` for
  `H ≥ 4·10⁶` (`tower_mult_ge_two`; `log H ≥ 15`, `logloglog H ≥ 1/2` from
  `tower_log_bounds`), whence `chowlaTower_ge` (every `H_j ≥ H₋`), the tower is
  monotone (`chowlaTower_monotone`), and `chowlaTower_le_Hhi` (every `H_j ≤ H₊`
  for `j ≤ J`, from `hfit`).
* **the telescope step** — `tower_step`: `step_ineq_3_11` at `H = H_j`,
  `k = ⌊C₀ log H_j logloglog H_j⌋₊` (so `k·H_j = H_{j+1}`), fused with the
  failure hypothesis and the multiplier arithmetic
  `(ε²log4)/k ≤ 1/(4 log H_j logloglog H_j)` into the clean per-step drop
  `e_{j+1} - e_j ≤ -1/(2 log H_j logloglog H_j)`.
* **the conditional telescoped bound** — `tower_telescope`: summing the step
  over `j < J` gives `e_J ≤ e_0 - towerDropSum` under the `∀ j < J` failure
  hypothesis (the all-`H`-failure branch of the eventual contradiction).
-/
import Salt.Entropy.Chowla.Step
import Salt.Entropy.Chowla.Regime

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### Numeric floor for the tower step -/

/-- For `H ≥ 4·10⁶`, `log H ≥ 15` and `logloglog H ≥ 1/2` (hence `> 0`).  The
    regime floor `hHlo_floor` is designed exactly so that `logloglog H₋ > 0`,
    forcing the tower step multiplier `≥ 2`. -/
lemma tower_log_bounds {H : ℕ} (hH : 4000000 ≤ H) :
    15 ≤ Real.log H ∧ (1 / 2 : ℝ) ≤ Real.log (Real.log (Real.log H)) := by
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hexp15 : Real.exp 15 ≤ 4000000 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have h15 : Real.exp 15 = (Real.exp 5) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h5b : Real.exp 5 ≤ 148.42 := by
      rw [h5]
      calc (Real.exp 1) ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := by gcongr
        _ ≤ 148.42 := by norm_num
    rw [h15]
    calc (Real.exp 5) ^ 3 ≤ (148.42 : ℝ) ^ 3 := by gcongr
      _ ≤ 4000000 := by norm_num
  have hlogH : 15 ≤ Real.log H := by
    rw [Real.le_log_iff_exp_le hHpos]; exact le_trans hexp15 hHR
  have hlogHpos : (0 : ℝ) < Real.log H := by linarith
  have hexp2 : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he2]; nlinarith [Real.exp_pos 1, h]
  have hloglogH : (2 : ℝ) ≤ Real.log (Real.log H) := by
    rw [Real.le_log_iff_exp_le hlogHpos]; linarith [hexp2, hlogH]
  have hloglogHpos : (0 : ℝ) < Real.log (Real.log H) := by linarith
  have hexphalf : Real.exp (1 / 2) ≤ 2 := by
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2), hsq, h1]
  have hlll : (1 / 2 : ℝ) ≤ Real.log (Real.log (Real.log H)) := by
    rw [Real.le_log_iff_exp_le hloglogHpos]; linarith [hexphalf, hloglogH]
  exact ⟨hlogH, hlll⟩

/-- The tower step multiplier is `≥ 2` for `H ≥ 4·10⁶` (with `C₀ ≥ 2`): strict
    growth of the tower. -/
lemma tower_mult_ge_two {C0 H : ℕ} (hC0 : 2 ≤ C0) (hH : 4000000 ≤ H) :
    2 ≤ ⌊(C0 : ℝ) * Real.log H * Real.log (Real.log (Real.log H))⌋₊ := by
  obtain ⟨hlogH, hlll⟩ := tower_log_bounds hH
  have hC0R : (2 : ℝ) ≤ (C0 : ℝ) := by exact_mod_cast hC0
  have h1 : (30 : ℝ) ≤ (C0 : ℝ) * Real.log H := by nlinarith [hlogH, hC0R]
  have hprod : (2 : ℝ) ≤ (C0 : ℝ) * Real.log H * Real.log (Real.log (Real.log H)) := by
    nlinarith [mul_le_mul h1 hlll (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : (0 : ℝ) ≤ (C0 : ℝ) * Real.log H)]
  exact Nat.le_floor (by exact_mod_cast hprod)

/-! ### Basic tower facts in the regime -/

/-- The tower's `succ`-step equation (Lemma 3.1, p.19). -/
lemma chowlaTower_succ (C0 a Hlo j : ℕ) :
    chowlaTower C0 a Hlo (j + 1)
      = chowlaTower C0 a Hlo j
        * ⌊(C0 : ℝ) * Real.log (chowlaTower C0 a Hlo j : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower C0 a Hlo j : ℝ)))⌋₊ := rfl

/-- Every tower value is `≥ H₋` (base `a·H₋ ≥ H₋`; each step multiplies by `≥ 1`). -/
lemma chowlaTower_ge (R : ChowlaRegime) (j : ℕ) :
    R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j := by
  induction j with
  | zero =>
    change R.Hlo ≤ R.a * R.Hlo
    calc R.Hlo = 1 * R.Hlo := (one_mul _).symm
      _ ≤ R.a * R.Hlo := by gcongr; exact R.ha
  | succ n ih =>
    have hfloor : 4000000 ≤ chowlaTower R.C0 R.a R.Hlo n := le_trans R.hHlo_floor ih
    have hmult := tower_mult_ge_two R.hC0 hfloor
    rw [chowlaTower_succ]
    calc R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo n := ih
      _ = chowlaTower R.C0 R.a R.Hlo n * 1 := (Nat.mul_one _).symm
      _ ≤ chowlaTower R.C0 R.a R.Hlo n
            * ⌊(R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo n : ℝ)
                * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo n : ℝ)))⌋₊ := by
          gcongr; omega

/-- The tower is non-decreasing (each step multiplies by `≥ 1`). -/
lemma chowlaTower_le_succ (R : ChowlaRegime) (j : ℕ) :
    chowlaTower R.C0 R.a R.Hlo j ≤ chowlaTower R.C0 R.a R.Hlo (j + 1) := by
  have hfloor : 4000000 ≤ chowlaTower R.C0 R.a R.Hlo j :=
    le_trans R.hHlo_floor (chowlaTower_ge R j)
  have hmult := tower_mult_ge_two R.hC0 hfloor
  rw [chowlaTower_succ]
  calc chowlaTower R.C0 R.a R.Hlo j
      = chowlaTower R.C0 R.a R.Hlo j * 1 := (Nat.mul_one _).symm
    _ ≤ chowlaTower R.C0 R.a R.Hlo j
          * ⌊(R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)))⌋₊ := by
        gcongr; omega

/-- The tower is monotone in the index. -/
lemma chowlaTower_monotone (R : ChowlaRegime) : Monotone (chowlaTower R.C0 R.a R.Hlo) :=
  monotone_nat_of_le_succ (chowlaTower_le_succ R)

/-- Every tower value up to index `J` fits below `H₊` (`hfit` + monotonicity). -/
lemma chowlaTower_le_Hhi (R : ChowlaRegime) {j : ℕ} (hj : j ≤ R.J) :
    chowlaTower R.C0 R.a R.Hlo j ≤ R.Hhi :=
  le_trans (chowlaTower_monotone R hj) R.hfit

/-! ### The per-symbol entropy and mutual information along the tower -/

/-- The per-symbol Liouville-window entropy at tower level `j`: `ℍ(X_{H_j})/H_j`. -/
noncomputable def towerEntropy (R : ChowlaRegime) (j : ℕ) : ℝ :=
  H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo j) ; logMeasure R.x R.ω]
    / (chowlaTower R.C0 R.a R.Hlo j : ℝ)

/-- The mutual information `𝕀(X_{H_j} : Y_{H_j})` at tower level `j`. -/
noncomputable def towerMI (R : ChowlaRegime) (j : ℕ) : ℝ :=
  I[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo j)
      : residueWindow R.eps (chowlaTower R.C0 R.a R.Hlo j) ; logMeasure R.x R.ω]

/-! ### The telescope step -/

/-- The abstract per-step drop: `step_ineq_3_11` at `(H, k = m)` fused with the
    failure hypothesis and the multiplier arithmetic
    `(ε²log4)/m ≤ 1/(4 log H logloglog H)` (from `m > C₀ log H logloglog H - 1`,
    `C₀ ≥ 2`, `ε ≤ 1/2`, and `log H · logloglog H ≥ 7.5`). -/
lemma tower_step_of (R : ChowlaRegime) {H m : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : m * H ≤ R.Hhi) (ha : R.a ∣ H) (hm : 2 ≤ m)
    (hmL : (R.C0 : ℝ) * Real.log H * Real.log (Real.log (Real.log H)) - 1 < (m : ℝ))
    (hdec : (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))
        < I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]) :
    H[liouvilleWindow (m * H) ; logMeasure R.x R.ω] / ((m : ℝ) * H)
        - H[liouvilleWindow H ; logMeasure R.x R.ω] / (H : ℝ)
      ≤ -(1 / (2 * Real.log H * Real.log (Real.log (Real.log H)))) := by
  have hk1 : 1 ≤ m := le_trans (by norm_num) hm
  have hstep := step_ineq_3_11 R hH hcpl ha hk1
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHRle : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHfloor
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  obtain ⟨hlogH15, hlll⟩ := tower_log_bounds hHfloor
  set L3 := Real.log (Real.log (Real.log (H : ℝ))) with hL3def
  set lg := Real.log (H : ℝ) with hlgdef
  have hlgpos : (0 : ℝ) < lg := by linarith [hlogH15]
  have hL3pos : (0 : ℝ) < L3 := by linarith [hlll]
  have hLpos : (0 : ℝ) < lg * L3 := mul_pos hlgpos hL3pos
  have hLge : (7.5 : ℝ) ≤ lg * L3 := by
    nlinarith [mul_le_mul hlogH15 hlll (by norm_num : (0 : ℝ) ≤ 1 / 2) hlgpos.le]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hC0R : (2 : ℝ) ≤ (R.C0 : ℝ) := by exact_mod_cast R.hC0
  have heps2 : (R.eps : ℝ) ^ 2 ≤ 1 / 4 := by
    have hq : R.eps ^ 2 ≤ 1 / 4 := by nlinarith [R.heps, R.heps1]
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc; linarith [hc]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the multiplier arithmetic: `(ε²log4)/m ≤ 1/(4 lg L3)`
  have h4e : (R.eps : ℝ) ^ 2 * Real.log 4 ≤ (1 / 2) * Real.log 2 := by
    rw [hlog4]
    nlinarith [heps2, hlog2pos, mul_le_mul_of_nonneg_right heps2 hlog2pos.le]
  have hprod : (lg * L3) * Real.log 2 ≤ (lg * L3) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hlog2.le hLpos.le
  have hlog2L : 2 * Real.log 2 * (lg * L3) ≤ 2 * (lg * L3) - 1 := by nlinarith [hprod, hLge]
  have h2lgm : 2 * (lg * L3) - 1 < (m : ℝ) := by nlinarith [hmL, hC0R, hLpos]
  have h4lgpos : (0 : ℝ) < 4 * lg * L3 := mul_pos (mul_pos (by norm_num) hlgpos) hL3pos
  have hkey : (R.eps : ℝ) ^ 2 * Real.log 4 / (m : ℝ) ≤ 1 / (4 * lg * L3) := by
    rw [div_le_div_iff₀ hmpos h4lgpos]
    nlinarith [mul_le_mul_of_nonneg_right h4e h4lgpos.le, hlog2L, h2lgm]
  -- the mutual-information decrement: `1/(lg L3) < I/H`
  have hMH : 1 / (lg * L3)
      < I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] / (H : ℝ) := by
    rw [div_lt_iff₀ hLpos] at hdec
    rw [div_lt_div_iff₀ hLpos hHpos, one_mul]; exact hdec
  -- reciprocal identities and the combination
  have hlgne : lg ≠ 0 := ne_of_gt hlgpos
  have hL3ne : L3 ≠ 0 := ne_of_gt hL3pos
  have he1 : 1 / (lg * L3) = 2 * (1 / (2 * lg * L3)) := by field_simp
  have he2 : 1 / (4 * lg * L3) = (1 / 2) * (1 / (2 * lg * L3)) := by field_simp; norm_num
  linarith [hstep, hkey, hMH, he1, he2]

/-- **The telescope step**: the per-symbol entropy drops by at least the
    `towerDropSum` summand `1/(2 log H_j logloglog H_j)` at each level `j < J`,
    under the failure hypothesis `hdecj` (the negation of the headline at `H_j`). -/
lemma tower_step (R : ChowlaRegime) {j : ℕ} (hj : j < R.J)
    (hdecj : (chowlaTower R.C0 R.a R.Hlo j : ℝ)
        / (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
      < towerMI R j) :
    towerEntropy R (j + 1) - towerEntropy R j
      ≤ -(1 / (2 * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))) := by
  simp only [towerMI] at hdecj
  have hHj : R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j := chowlaTower_ge R j
  have hfloor : 4000000 ≤ chowlaTower R.C0 R.a R.Hlo j := le_trans R.hHlo_floor hHj
  have hmult := tower_mult_ge_two R.hC0 hfloor
  have hrec : chowlaTower R.C0 R.a R.Hlo (j + 1)
      = (⌊(R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
          * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)))⌋₊)
        * chowlaTower R.C0 R.a R.Hlo j := by
    rw [chowlaTower_succ]; ring
  have hcpl : (⌊(R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)))⌋₊)
        * chowlaTower R.C0 R.a R.Hlo j ≤ R.Hhi := by
    rw [← hrec]; exact chowlaTower_le_Hhi R (by omega)
  have hmL := Nat.sub_one_lt_floor
      ((R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
  have key := tower_step_of R hHj hcpl (dvd_chowlaTower R.C0 R.a R.Hlo j) hmult hmL hdecj
  simp only [towerEntropy]
  rw [hrec, Nat.cast_mul]
  exact key

/-! ### The conditional telescoped bound -/

/-- **The conditional telescoped bound** (Tao 1509.05422 p.20).  If the headline
    fails at every tower level `j < J` (`hdec`, the all-`H`-failure branch), the
    top-level per-symbol entropy is below the base by the full telescoped
    decrement: `e_J ≤ e_0 - towerDropSum`.  Wave IV closes the contradiction with
    `e_0 ≤ log 2 < towerDropSum` (`hJcon`) and `e_J ≥ 0`. -/
theorem tower_telescope (R : ChowlaRegime)
    (hdec : ∀ j, j < R.J →
      (chowlaTower R.C0 R.a R.Hlo j : ℝ)
          / (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
        < towerMI R j) :
    towerEntropy R R.J ≤ towerEntropy R 0 - towerDropSum R.C0 R.a R.Hlo R.J := by
  have hstep : ∀ j ∈ Finset.range R.J,
      towerEntropy R (j + 1) - towerEntropy R j
        ≤ -(1 / (2 * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))) :=
    fun j hj => tower_step R (Finset.mem_range.mp hj) (hdec j (Finset.mem_range.mp hj))
  have htel := Finset.sum_range_sub (towerEntropy R) R.J
  have hsum := Finset.sum_le_sum hstep
  have hneg : ∑ j ∈ Finset.range R.J,
        -(1 / (2 * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)))))
      = - towerDropSum R.C0 R.a R.Hlo R.J := by
    simp only [towerDropSum, Finset.sum_neg_distrib]
  rw [htel, hneg] at hsum
  linarith [hsum]

end Salt.Entropy.Chowla
