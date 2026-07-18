/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Spacing
import Salt.Vk.BoxMeasure
import Salt.Vmvt.Summit2

/-!
# VMVT-VK rung R4 — the block bridge `vk_block_core` (`VK-POINTWISE`), the final stitch

`vk_block_core` closes R4-assembly: the ζ-phase block sum has a pointwise Weyl bound
`‖∑ eR(φ)‖ ≤ 8·P^{1−ρ}` derived from the machine-checked Vinogradov mean value theorem
`Salt.Vmvt.vmvt`.  This is the first pointwise Weyl bound from a machine-checked mean value
theorem.

The proof composes the landed analytic reduction
`vk_block_taylor_reduce → vk_shift_to_orbit → vk_pow_sum_le →
vk_box_disjoint_avg_of_centers → vmvt` with the two freeze residuals:

* **(b) spacing** — `vk_orbit_fract_sep` (`Salt/Vk/Spacing.lean`), the orbit `j*`-coordinate
  Diophantine separation feeding the box `hsep`;
* **(c) ledger** — the closing `rpow` bookkeeping (this file): the exponent split
  `2bρ = 1/8 | kρ ≤ 1/8 | η ≤ 1/8 | log_P D ≤ 1/8`, `(∏δ)⁻¹ = (16k)^k·P^{ρk+k(k+1)/2}`,
  `Slack = (π/8)·P^{1−ρ}`, collapsing to `8·P^{1−ρ}` after the `vmvt` application.
-/

namespace Salt.Vk

open Finset Real MeasureTheory Salt.ExpSum Salt.Vmvt
open scoped BigOperators

/-! ## Scalar ledger facts -/

/-- **`η ≤ 1/8`** (the `r`-choice budget).  With `r ≥ k·log(4k²)`, the exponent-decay term
`η(k,r) = ½k²(1−1/k)^r ≤ ½k²·(4k²)⁻¹ = 1/8` (via `(1−1/k)^r ≤ e^{−r/k} ≤ (4k²)⁻¹`). -/
lemma vk_eta_le {k r : ℕ} (hk : 1 ≤ k)
    (hr_ge : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (r : ℝ)) :
    vmvtEta k r ≤ 1 / 8 := by
  rw [vmvtEta]
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk2 : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by positivity
  have h01 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one hk0]; exact hkR
  have hexp1 : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / (k : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (k : ℝ))); linarith
  have hpow : (1 - 1 / (k : ℝ)) ^ r ≤ Real.exp (-((r : ℝ) / (k : ℝ))) := by
    calc (1 - 1 / (k : ℝ)) ^ r ≤ (Real.exp (-(1 / (k : ℝ)))) ^ r :=
          pow_le_pow_left₀ h01 hexp1 r
      _ = Real.exp (-((r : ℝ) / (k : ℝ))) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hlog : Real.log (4 * (k : ℝ) ^ 2) ≤ (r : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk0]; linarith [hr_ge]
  have hexp2 : Real.exp (-((r : ℝ) / (k : ℝ))) ≤ 1 / (4 * (k : ℝ) ^ 2) := by
    have h4k : Real.exp (-Real.log (4 * (k : ℝ) ^ 2)) = 1 / (4 * (k : ℝ) ^ 2) := by
      rw [Real.exp_neg, Real.exp_log hk2]; exact (one_div _).symm
    rw [← h4k]
    exact Real.exp_le_exp.mpr (by linarith [hlog])
  calc (1 / 2) * (k : ℝ) ^ 2 * (1 - 1 / (k : ℝ)) ^ r
      ≤ (1 / 2) * (k : ℝ) ^ 2 * (1 / (4 * (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_trans hpow hexp2) (by positivity)
    _ = 1 / 8 := by
        have hk2ne : (k : ℝ) ^ 2 ≠ 0 := by positivity
        field_simp; ring

/-- **`(16k)^k·D ≤ P^{1/8}`** (the `hD` P-floor budget).  With `D = k^{24k²r}` and the
log-floor `k·log(16k) + 24k²r·log k ≤ (log P)/8`, the constant is `≤ P^{1/8}`. -/
lemma vk_const_le {k r P : ℕ} (hk : 2 ≤ k) (hP : 1 ≤ P)
    (hlog : (k : ℝ) * Real.log (16 * (k : ℝ)) + 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log (k : ℝ)
      ≤ 1 / 8 * Real.log (P : ℝ)) :
    (16 * (k : ℝ)) ^ k * vmvtConst k r ≤ (P : ℝ) ^ ((1 : ℝ) / 8) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have h16k : (0 : ℝ) < 16 * (k : ℝ) := by positivity
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hP
  -- rewrite everything through `exp`
  have hD : vmvtConst k r = (k : ℝ) ^ (24 * k ^ 2 * r) := by
    rw [vmvtConst, vmvtC0, ← pow_mul]
  have e1 : (16 * (k : ℝ)) ^ k = Real.exp ((k : ℝ) * Real.log (16 * (k : ℝ))) := by
    rw [← Real.rpow_natCast (16 * (k : ℝ)) k, Real.rpow_def_of_pos h16k]; ring_nf
  have e2 : (k : ℝ) ^ (24 * k ^ 2 * r)
      = Real.exp (24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log (k : ℝ)) := by
    rw [← Real.rpow_natCast (k : ℝ) (24 * k ^ 2 * r), Real.rpow_def_of_pos hkpos]
    congr 1; push_cast; ring
  have e3 : (P : ℝ) ^ ((1 : ℝ) / 8) = Real.exp (1 / 8 * Real.log (P : ℝ)) := by
    rw [Real.rpow_def_of_pos hPpos]; ring_nf
  rw [hD, e1, e2, e3, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [hlog])

/-! ## The box half-widths `δ` -/

/-- The R4 box half-widths `δ_j = P^{−j−ρ}/(16k)`. -/
noncomputable def vkDelta (P k : ℕ) (ρbl : ℝ) : Deg k → ℝ :=
  fun j => (P : ℝ) ^ (-((j : ℕ) : ℝ) - ρbl) / (16 * (k : ℝ))

lemma vkDelta_nonneg {P k : ℕ} (hk : 1 ≤ k) (ρbl : ℝ) (j : Deg k) : 0 ≤ vkDelta P k ρbl j := by
  rw [vkDelta]; positivity

lemma vkDelta_le_one {P k : ℕ} (hP : 1 ≤ P) (hk : 1 ≤ k) {ρbl : ℝ} (hρ0 : 0 ≤ ρbl)
    (j : Deg k) : vkDelta P k ρbl j ≤ 1 := by
  rw [vkDelta]
  have hPR : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hj1 : 1 ≤ (j : ℕ) := (Finset.mem_Icc.mp j.2).1
  have hexp : (P : ℝ) ^ (-((j : ℕ) : ℝ) - ρbl) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hPR
    have : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj1
    linarith
  rw [div_le_one (by positivity)]
  nlinarith [hexp, hkR]

lemma vkDelta_prod_pos {P k : ℕ} (hP : 0 < P) (hk : 1 ≤ k) (ρbl : ℝ) :
    0 < ∏ j : Deg k, vkDelta P k ρbl j := by
  apply Finset.prod_pos
  intro j _
  rw [vkDelta]
  have : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  positivity

/-- **The `(∏δ)⁻¹` closed form** (ledger).  `(∏_j δ_j)⁻¹ = (16k)^k·P^{½k(k+1)+kρ}` (the
Gauss sum `∑_{j=1}^k j = ½k(k+1)` and the `rpow` product-to-sum). -/
lemma vkDelta_prod_inv {P k : ℕ} (hP : 0 < P) (hk : 1 ≤ k) (ρbl : ℝ) :
    (∏ j : Deg k, vkDelta P k ρbl j)⁻¹
      = (16 * (k : ℝ)) ^ k * (P : ℝ) ^ (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl) := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hcard : (Finset.Icc 1 k).card = k := by rw [Nat.card_Icc]; omega
  have hGauss : ∀ m : ℕ, ∑ j ∈ Finset.Icc 1 m, (j : ℝ) = 1 / 2 * (m : ℝ) * ((m : ℝ) + 1) := by
    intro m; induction m with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]; push_cast; ring
  have hconv : ∏ j : Deg k, vkDelta P k ρbl j
      = (∏ j ∈ Finset.Icc 1 k, (P : ℝ) ^ (-(j : ℝ) - ρbl)) / (16 * (k : ℝ)) ^ k := by
    simp only [vkDelta]
    rw [Finset.prod_coe_sort (Finset.Icc 1 k)
      (fun j => (P : ℝ) ^ (-(j : ℝ) - ρbl) / (16 * (k : ℝ)))]
    rw [Finset.prod_div_distrib, Finset.prod_const, hcard]
  have hsum : ∑ j ∈ Finset.Icc 1 k, (-(j : ℝ) - ρbl)
      = -(1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl) := by
    have h1 : ∑ j ∈ Finset.Icc 1 k, (-(j : ℝ) - ρbl)
        = -(∑ j ∈ Finset.Icc 1 k, (j : ℝ)) - (∑ _j ∈ Finset.Icc 1 k, ρbl) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    rw [h1, hGauss k, Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hnum : ∏ j ∈ Finset.Icc 1 k, (P : ℝ) ^ (-(j : ℝ) - ρbl)
      = (P : ℝ) ^ (-(1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl)) := by
    rw [← Real.rpow_sum_of_pos hPpos, hsum]
  have h16 : (0 : ℝ) < (16 * (k : ℝ)) ^ k := by positivity
  refine inv_eq_of_mul_eq_one_left ?_
  rw [hconv, hnum]
  have hrw : (16 * (k : ℝ)) ^ k * (P : ℝ) ^ (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl)
      * ((P : ℝ) ^ (-(1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl)) / (16 * (k : ℝ)) ^ k)
      = ((P : ℝ) ^ (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl)
          * (P : ℝ) ^ (-(1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl)))
        * ((16 * (k : ℝ)) ^ k / (16 * (k : ℝ)) ^ k) := by ring
  rw [hrw, ← Real.rpow_add hPpos, add_neg_cancel, Real.rpow_zero, div_self (ne_of_gt h16),
    one_mul]

/-- **The Slack bound** (ledger).  `Slack = 2π·P'·∑_j δ_j·(P')^j ≤ (π/8)·P^{1−ρ} ≤ P^{1−ρ}`
(each term `δ_j·(P')^j ≤ P^{−ρ}/(16k)`, so `∑ ≤ P^{−ρ}/16`). -/
lemma vkDelta_slack_le {P P' k : ℕ} (hP'P : P' ≤ P) (hP : 1 ≤ P) (hk : 1 ≤ k) (ρbl : ℝ) :
    2 * π * ((P' : ℝ) * ∑ j : Deg k, vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ))
      ≤ (P : ℝ) ^ (1 - ρbl) := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hP
  have hP'0 : (0 : ℝ) ≤ (P' : ℝ) := by positivity
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcardD : Fintype.card (Deg k) = k := by rw [Fintype.card_coe, Nat.card_Icc]; omega
  have hterm : ∀ j : Deg k,
      vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ) ≤ (P : ℝ) ^ (-ρbl) / (16 * (k : ℝ)) := by
    intro j
    have hPj : (P' : ℝ) ^ ((j : ℕ)) ≤ (P : ℝ) ^ ((j : ℕ)) :=
      pow_le_pow_left₀ hP'0 (by exact_mod_cast hP'P) _
    have hbound : (P : ℝ) ^ (-((j : ℕ) : ℝ) - ρbl) * (P' : ℝ) ^ ((j : ℕ)) ≤ (P : ℝ) ^ (-ρbl) := by
      calc (P : ℝ) ^ (-((j : ℕ) : ℝ) - ρbl) * (P' : ℝ) ^ ((j : ℕ))
          ≤ (P : ℝ) ^ (-((j : ℕ) : ℝ) - ρbl) * (P : ℝ) ^ ((j : ℕ)) :=
            mul_le_mul_of_nonneg_left hPj (Real.rpow_nonneg hPpos.le _)
        _ = (P : ℝ) ^ (-ρbl) := by
            have hnp : (P : ℝ) ^ ((j : ℕ)) = (P : ℝ) ^ (((j : ℕ) : ℝ)) :=
              (Real.rpow_natCast (P : ℝ) (j : ℕ)).symm
            rw [hnp, ← Real.rpow_add hPpos]
            congr 1; ring
    rw [vkDelta, div_mul_eq_mul_div]
    gcongr
  have hsum : ∑ j : Deg k, vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ) ≤ (P : ℝ) ^ (-ρbl) / 16 := by
    calc ∑ j : Deg k, vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ)
        ≤ ∑ _j : Deg k, (P : ℝ) ^ (-ρbl) / (16 * (k : ℝ)) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (P : ℝ) ^ (-ρbl) / 16 := by
          rw [Finset.sum_const, Finset.card_univ, hcardD, nsmul_eq_mul]
          field_simp
  have hP'P_R : (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP'P
  have hPρ : (0 : ℝ) ≤ (P : ℝ) ^ (-ρbl) := Real.rpow_nonneg hPpos.le _
  have hPρ1 : (0 : ℝ) ≤ (P : ℝ) ^ (1 - ρbl) := Real.rpow_nonneg hPpos.le _
  have hkey : (P' : ℝ) * (P : ℝ) ^ (-ρbl) ≤ (P : ℝ) ^ (1 - ρbl) := by
    calc (P' : ℝ) * (P : ℝ) ^ (-ρbl) ≤ (P : ℝ) * (P : ℝ) ^ (-ρbl) :=
          mul_le_mul_of_nonneg_right hP'P_R hPρ
      _ = (P : ℝ) ^ (1 - ρbl) := by
          rw [sub_eq_add_neg, Real.rpow_add hPpos, Real.rpow_one]
  have hπ8 : π / 8 ≤ 1 := by linarith [Real.pi_le_four]
  calc 2 * π * ((P' : ℝ) * ∑ j : Deg k, vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ))
      ≤ 2 * π * ((P' : ℝ) * ((P : ℝ) ^ (-ρbl) / 16)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsum hP'0
    _ = π / 8 * ((P' : ℝ) * (P : ℝ) ^ (-ρbl)) := by ring
    _ ≤ π / 8 * (P : ℝ) ^ (1 - ρbl) := by apply mul_le_mul_of_nonneg_left hkey; positivity
    _ ≤ 1 * (P : ℝ) ^ (1 - ρbl) := mul_le_mul_of_nonneg_right hπ8 hPρ1
    _ = (P : ℝ) ^ (1 - ρbl) := one_mul _

/-! ## Two boundary `rpow` facts -/

/-- `P^{1/2} ≤ P^{1−ρ}` for `0 ≤ ρ ≤ 1/2` and `1 ≤ P`. -/
lemma rpow_half_le_one_sub {P : ℕ} (hP : 1 ≤ P) {ρbl : ℝ} (hρ : ρbl ≤ 1 / 2) :
    (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (P : ℝ) ^ (1 - ρbl) := by
  have hPR : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  exact Real.rpow_le_rpow_of_exponent_le hPR (by linarith)

/-- **`2Y ≤ 5·P^{1−ρ}`** (the boundary term budget).  `2⌈P^{1/2}⌉ ≤ 2(P^{1/2}+1) ≤ 5P^{1/2}`
(since `P^{1/2} ≥ 1`) `≤ 5P^{1−ρ}`. -/
lemma vk_two_Y_le {P Y : ℕ} (hP : 1 ≤ P) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    {ρbl : ℝ} (hρ : ρbl ≤ 1 / 2) : 2 * (Y : ℝ) ≤ 5 * (P : ℝ) ^ (1 - ρbl) := by
  have hPR : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hhalf1 : (1 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hPR (by norm_num)
  have hYceil : (Y : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) + 1 := by
    rw [hY]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hle := rpow_half_le_one_sub hP hρ
  linarith

/-- **The ledger exponent inequality** (the `2bρ|kρ|η|log_P D` split, `Σ=1/2`).  The `P`-power
of `(∏δ)⁻¹·Jk` is `≤` that of `P^{(1−ρ)·2b}·P^{1/2}` (the `Y·(P^{1−ρ})^{2b}` floor); the
`½k(k+1)` cancels and it reduces to `kρ + η ≤ 1/4` (`kρ = 1/(16r) ≤ 1/16`, `η ≤ 1/8`). -/
lemma vk_exp_ineq {k r : ℕ} {ρbl : ℝ} (hk1 : 1 ≤ k) (hr1 : 1 ≤ r)
    (hρ : ρbl = 1 / (16 * (k : ℝ) * r)) (hr_ge : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (r : ℝ)) :
    1 / 8 + (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl) + vmvtExp k r
      ≤ (1 - ρbl) * (2 * ((k * r : ℕ) : ℝ)) + 1 / 2 := by
  have hkne : (k : ℝ) ≠ 0 := by positivity
  have hrne : (r : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    positivity
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hη := vk_eta_le hk1 hr_ge
  have hkρ : (k : ℝ) * ρbl = 1 / (16 * (r : ℝ)) := by rw [hρ]; field_simp
  have h2bρ : ρbl * (2 * ((k * r : ℕ) : ℝ)) = 1 / 8 := by rw [hρ]; push_cast; field_simp; ring
  have h16r : 1 / (16 * (r : ℝ)) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hr1R]
  rw [vmvtExp, show (1 - ρbl) * (2 * ((k * r : ℕ) : ℝ))
      = 2 * ((k * r : ℕ) : ℝ) - ρbl * (2 * ((k * r : ℕ) : ℝ)) from by ring, h2bρ, hkρ]
  push_cast
  nlinarith [hη, h16r]

/-! ## The bridge complete -/

set_option maxHeartbeats 2000000 in
-- The bridge assembles the full analytic chain (Taylor → shift → Jensen → box → vmvt) with the
-- closing `rpow` ledger in one theorem; the default heartbeat budget is insufficient.
/-- **`vk_block_core` — THE BRIDGE.**  The ζ-phase block sum has a pointwise Weyl bound
`‖∑ eR(φ)‖ ≤ 8·P^{1−ρ}` derived from the machine-checked Vinogradov mean value theorem
`Salt.Vmvt.vmvt`.  The first pointwise Weyl bound from a machine-checked mean value theorem. -/
theorem vk_block_core {k r N₀ P P' Y : ℕ} {t ρbl : ℝ} (hk : 19 ≤ k)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊) (hρ : ρbl = 1 / (16 * (k : ℝ) * r))
    (hP' : P' ≤ P) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ) / N₀) ^ (k + 1) ≤ ((N₀ : ℝ))⁻¹)
    (hW2 : ∃ js ∈ Finset.Icc 2 (k - 1), VkSpaced t N₀ P Y js ρbl k) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖ ≤ 8 * (P : ℝ) ^ (1 - ρbl) := by
  obtain ⟨js, hjs_mem, hspaced⟩ := hW2
  rw [Finset.mem_Icc] at hjs_mem
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hjsk : js + 1 ≤ k := by omega
  have hkR : (19 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0R : (0 : ℝ) < (k : ℝ) := by linarith
  -- r-facts
  have hr_ge : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (r : ℝ) := by rw [hr]; exact Nat.le_ceil _
  have hlog4k2 : 0 < Real.log (4 * (k : ℝ) ^ 2) := Real.log_pos (by nlinarith [hkR])
  have hr1 : 1 ≤ r := by
    have h0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le (by positivity) hr_ge
    have : 0 < r := by exact_mod_cast h0
    omega
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  -- P ≥ 2
  have hlogP : 0 < Real.log (P : ℝ) := by
    have hA : 0 < (k : ℝ) * Real.log (16 * (k : ℝ)) :=
      mul_pos hk0R (Real.log_pos (by nlinarith [hkR]))
    have hB : 0 ≤ 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log (k : ℝ) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hk1))
    nlinarith [hD, hA, hB]
  have hP2 : 2 ≤ P := by
    by_contra h; rw [not_le] at h; interval_cases P <;> simp_all
  have hP1' : 1 ≤ P := by omega
  have hPR : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  -- Y ≥ 1, N₀ > 0
  have hY1 : 1 ≤ Y := by rw [hY, Nat.one_le_ceil_iff]; positivity
  have hYR1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have hY0R : (0 : ℝ) < (Y : ℝ) := by linarith
  have hW2c := hspaced.2.2
  have hN0R : (0 : ℝ) < (N₀ : ℝ) := by nlinarith [hW2c, hk0R, hY0R]
  have hN0 : 0 < N₀ := by exact_mod_cast hN0R
  -- ρ facts
  have hkr1R : (1 : ℝ) ≤ (k : ℝ) * (r : ℝ) := by nlinarith [hk0R, hr1R, hkR]
  have hρ0 : 0 ≤ ρbl := by rw [hρ]; positivity
  have hρhalf : ρbl ≤ 1 / 2 := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hkr1R]
  -- 0 ≤ t
  have hW2a := hspaced.1
  have ht : 0 ≤ t := by
    have hlhs : (0 : ℝ) < (P : ℝ) ^ (-(js : ℝ) - ρbl) / (4 * (k : ℝ)) := by positivity
    have hpos := lt_of_lt_of_le hlhs hW2a
    by_contra h; rw [not_le] at h
    have : t / (2 * π * (N₀ : ℝ) ^ (js + 1)) < 0 := div_neg_of_neg_of_pos h (by positivity)
    linarith
  set c : ℕ → ℝ := vkCoef t N₀ with hc
  set bb : ℕ := k * r with hbb
  set Pρ : ℝ := (P : ℝ) ^ (1 - ρbl) with hPρ
  have hPρpos : 0 < Pρ := Real.rpow_pos_of_pos hPpos _
  have hbb1 : 1 ≤ bb := by rw [hbb]; simpa using Nat.mul_le_mul hk1 hr1
  -- the two boundary rpow bounds
  have h2Y : 2 * (Y : ℝ) ≤ 5 * Pρ := vk_two_Y_le hP1' hY hρhalf
  rcases (by omega : Y ≤ P' ∨ P' < Y) with hYP' | hlt
  · -- MAIN branch
    have hP'1 : 1 ≤ P' := le_trans hY1 hYP'
    have hP'PR : (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP'
    -- Taylor cost bound
    have hTaylor : 2 * π * ((P' : ℝ) * (2 * (t / (2 * π))
        * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))) ≤ Pρ := by
      have hXeq : (((P + Y : ℕ) : ℝ) / N₀) = ((P : ℝ) + (Y : ℝ)) / N₀ := by push_cast; ring
      have hcost : 2 * π * ((P' : ℝ) * (2 * (t / (2 * π))
          * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))) = 2 * (P' : ℝ)
          * (t * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1)) := by
        field_simp
      rw [hcost]
      have hbnd : t * (((P + Y : ℕ) : ℝ) / N₀) ^ (k + 1)
          ≤ (P : ℝ) ^ ((1 : ℝ) / 2) / (2 * (P' : ℝ)) := by
        refine le_trans hW1 ?_
        rw [le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hN0R]
        have hNhalf : 4 * (k : ℝ) ^ 2 * (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (N₀ : ℝ) := by
          have hYhalf : (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (Y : ℝ) := by rw [hY]; exact Nat.le_ceil _
          nlinarith [hW2c, hYhalf, hk0R]
        have hPsq : (P : ℝ) ^ ((1 : ℝ) / 2) * (P : ℝ) ^ ((1 : ℝ) / 2) = (P : ℝ) := by
          rw [← Real.rpow_add hPpos]; norm_num
        have hhalf_nn : (0 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hPpos.le _
        have hprod := mul_le_mul_of_nonneg_right hNhalf hhalf_nn
        have hmid : 4 * (k : ℝ) ^ 2 * (P : ℝ) ≤ (N₀ : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 2) := by
          nlinarith [hprod, hPsq]
        have hk4 : (2 : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by nlinarith [hkR]
        nlinarith [hmid, hP'PR, hPpos, hk4]
      calc 2 * (P' : ℝ) * (t * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))
          = 2 * (P' : ℝ) * (t * (((P + Y : ℕ) : ℝ) / N₀) ^ (k + 1)) := by rw [hXeq]
        _ ≤ 2 * (P' : ℝ) * ((P : ℝ) ^ ((1 : ℝ) / 2) / (2 * (P' : ℝ))) :=
            mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = (P : ℝ) ^ ((1 : ℝ) / 2) := by field_simp
        _ ≤ Pρ := rpow_half_le_one_sub hP1' hρhalf
    -- centers, moments
    set centers : Fin Y → Deg k → ℝ :=
      fun y j => Int.fract (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ) j) with hcenters
    set a : Fin Y → ℝ :=
      fun y => ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ)) (centers y)‖ with ha
    have ha_nn : ∀ y, 0 ≤ a y := fun y => norm_nonneg _
    have ha_eq : ∀ y : Fin Y,
        ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ)) (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ))‖ = a y := by
      intro y; rw [ha]; simp only [hcenters]
      exact (congrArg norm (genFun_fract k _ (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ)))).symm
    -- the box hsep from the spacing lemma
    set j₀ : Deg k := ⟨js, by rw [Finset.mem_Icc]; omega⟩ with hj0
    have hsep : ∀ y y' : Fin Y, y ≠ y' →
        2 * vkDelta P k ρbl j₀ ≤ |centers y j₀ - centers y' j₀| := by
      intro y y' hyy'
      have hwY : ((y : ℕ) + 1 : ℝ) ≤ (Y : ℝ) := by
        have : (y : ℕ) + 1 ≤ Y := by have := y.2; omega
        exact_mod_cast this
      have hw'Y : ((y' : ℕ) + 1 : ℝ) ≤ (Y : ℝ) := by
        have : (y' : ℕ) + 1 ≤ Y := by have := y'.2; omega
        exact_mod_cast this
      have hne : (1 : ℝ) ≤ |((y : ℕ) + 1 : ℝ) - ((y' : ℕ) + 1 : ℝ)| := by
        have hyy'n : (y : ℕ) ≠ (y' : ℕ) := fun h => hyy' (Fin.ext h)
        have hred : ((y : ℕ) + 1 : ℝ) - ((y' : ℕ) + 1 : ℝ) = ((y : ℕ) : ℝ) - ((y' : ℕ) : ℝ) := by
          ring
        rw [hred]
        rcases (by omega : (y : ℕ) + 1 ≤ (y' : ℕ) ∨ (y' : ℕ) + 1 ≤ (y : ℕ)) with h | h
        · have hc1 : ((y : ℕ) : ℝ) + 1 ≤ ((y' : ℕ) : ℝ) := by exact_mod_cast h
          rw [abs_of_nonpos (by linarith)]; linarith
        · have hc1 : ((y' : ℕ) : ℝ) + 1 ≤ ((y : ℕ) : ℝ) := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]; linarith
      have key := vk_orbit_fract_sep hk1 hjsk hspaced
        (by have : (0 : ℝ) ≤ ((y : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hwY
        (by have : (0 : ℝ) ≤ ((y' : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hw'Y hne
      simpa only [hcenters, vkDelta, vkOrbitPoint] using key
    -- Taylor front + shift + fract
    have hstep0 := vk_block_taylor_reduce k N₀ P P' Y t ht hN0 hP'
    rw [← hc] at hstep0
    have hshift := vk_shift_to_orbit k P' Y c hYP'
    rw [Finset.sum_congr rfl (fun y _ => ha_eq y)] at hshift
    -- Icc-vs-range phase
    have hc0 : c 0 = 0 := by rw [hc, vkCoef]; simp
    have hpoly : ∀ m : ℤ, ∑ j ∈ Finset.Icc 1 k, c j * (m : ℝ) ^ j
        = ∑ j ∈ Finset.range (k + 1), c j * (m : ℝ) ^ j := by
      intro m
      rw [show Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) from by
            ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hc0, zero_mul, zero_add]
    have hWiWr : ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (∑ j ∈ Finset.Icc 1 k, c j * (m : ℝ) ^ j)‖
        = ‖∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j)‖ :=
      congrArg norm (Finset.sum_congr rfl (fun m _ => by rw [hpoly m]))
    rw [hWiWr] at hstep0
    -- box + vmvt + ledger
    have hbox := vk_box_disjoint_avg_of_centers k bb P' Y centers (vkDelta P k ρbl) j₀
      (fun y j => fract_mem_Icc _) (fun j => vkDelta_nonneg hk1 ρbl j)
      (fun j => vkDelta_le_one hP1' hk1 hρ0 j) (vkDelta_prod_pos (by omega) hk1 ρbl) hsep
    have hvmvt : (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ)
        ≤ vmvtConst k r * (P' : ℝ) ^ (vmvtExp k r) := vmvt k r P' hk2 hr1 hP'1
    have hClaimB := vkDelta_slack_le hP' hP1' hk1 ρbl
    have hClaimA : (∏ j : Deg k, vkDelta P k ρbl j)⁻¹
        * (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ) ≤ Pρ ^ (2 * bb) * (Y : ℝ) := by
      have hEnn : 0 ≤ vmvtExp k r := vmvtExp_nonneg hk2 hr1
      have hvc_nn : 0 ≤ vmvtConst k r := by rw [vmvtConst, vmvtC0]; positivity
      have hD_div : (k : ℝ) * Real.log (16 * (k : ℝ))
          + 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log (k : ℝ) ≤ 1 / 8 * Real.log P := by linarith [hD]
      have hconst := vk_const_le hk2 hP1' hD_div
      have hdinv := vkDelta_prod_inv (P := P) (by omega) hk1 ρbl
      have hJk_le : (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ)
          ≤ vmvtConst k r * (P : ℝ) ^ (vmvtExp k r) :=
        le_trans hvmvt (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hP'PR hEnn) hvc_nn)
      have hdinv_nn : 0 ≤ (∏ j : Deg k, vkDelta P k ρbl j)⁻¹ :=
        le_of_lt (inv_pos.mpr (vkDelta_prod_pos (by omega) hk1 ρbl))
      have hYhalf : (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (Y : ℝ) := by rw [hY]; exact Nat.le_ceil _
      calc (∏ j : Deg k, vkDelta P k ρbl j)⁻¹ * (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ)
          ≤ (∏ j : Deg k, vkDelta P k ρbl j)⁻¹ * (vmvtConst k r * (P : ℝ) ^ (vmvtExp k r)) :=
            mul_le_mul_of_nonneg_left hJk_le hdinv_nn
        _ = ((16 * (k : ℝ)) ^ k * vmvtConst k r)
              * (P : ℝ) ^ (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl + vmvtExp k r) := by
            rw [hdinv]
            conv_rhs => rw [Real.rpow_add hPpos]
            ring
        _ ≤ (P : ℝ) ^ ((1 : ℝ) / 8)
              * (P : ℝ) ^ (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl + vmvtExp k r) :=
            mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hPpos.le _)
        _ = (P : ℝ) ^ ((1 : ℝ) / 8
              + (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl + vmvtExp k r)) := by
            rw [← Real.rpow_add hPpos]
        _ ≤ (P : ℝ) ^ ((1 - ρbl) * (2 * ((k * r : ℕ) : ℝ)) + 1 / 2) :=
            Real.rpow_le_rpow_of_exponent_le (le_of_lt hPR) (by
              have := vk_exp_ineq hk1 hr1 hρ hr_ge; linarith)
        _ = Pρ ^ (2 * bb) * (P : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_add hPpos, hPρ, ← Real.rpow_natCast ((P : ℝ) ^ (1 - ρbl)) (2 * bb),
              ← Real.rpow_mul hPpos.le]
            congr 2; rw [hbb]; push_cast; ring
        _ ≤ Pρ ^ (2 * bb) * (Y : ℝ) := mul_le_mul_of_nonneg_left hYhalf (by positivity)
    -- combine: ∑ a ≤ 2 Pρ Y
    have hsumroot : (∑ y : Fin Y, a y) ≤ 2 * Pρ * (Y : ℝ) := by
      have hSlk_nn : 0 ≤ 2 * π
          * ((P' : ℝ) * ∑ j : Deg k, vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ)) := by
        have := vkDelta_prod_pos (by omega : 0 < P) hk1 ρbl
        refine mul_nonneg (by positivity) (mul_nonneg (by positivity) (Finset.sum_nonneg ?_))
        intro j _; exact mul_nonneg (vkDelta_nonneg hk1 ρbl j) (by positivity)
      have hpow : (∑ y : Fin Y, a y) ^ (2 * bb)
          ≤ (2 : ℝ) ^ (2 * bb) * Pρ ^ (2 * bb) * (Y : ℝ) ^ (2 * bb) := by
        have hjen := vk_pow_sum_le bb Y a ha_nn (by omega : 1 ≤ 2 * bb)
        calc (∑ y : Fin Y, a y) ^ (2 * bb)
            ≤ (Y : ℝ) ^ (2 * bb - 1) * ∑ y : Fin Y, a y ^ (2 * bb) := hjen
          _ ≤ (Y : ℝ) ^ (2 * bb - 1) * (2 ^ (2 * bb - 1) * (2 * (Pρ ^ (2 * bb) * (Y : ℝ)))) := by
              refine mul_le_mul_of_nonneg_left (le_trans hbox
                (mul_le_mul_of_nonneg_left ?_ (by positivity))) (by positivity)
              have hB : (Y : ℝ) * (2 * π * ((P' : ℝ) * ∑ j : Deg k,
                    vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ))) ^ (2 * bb)
                  ≤ Pρ ^ (2 * bb) * (Y : ℝ) := by
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ hSlk_nn hClaimB (2 * bb)) (by positivity)
              nlinarith [hClaimA, hB]
          _ = (2 : ℝ) ^ (2 * bb) * Pρ ^ (2 * bb) * (Y : ℝ) ^ (2 * bb) := by
              have hY2 : (Y : ℝ) ^ (2 * bb - 1) * (Y : ℝ) = (Y : ℝ) ^ (2 * bb) := by
                rw [← pow_succ]; congr 1; omega
              have h22 : (2 : ℝ) ^ (2 * bb - 1) * 2 = (2 : ℝ) ^ (2 * bb) := by
                rw [← pow_succ]; congr 1; omega
              rw [← hY2, ← h22]; ring
      have hrhs : (2 : ℝ) ^ (2 * bb) * Pρ ^ (2 * bb) * (Y : ℝ) ^ (2 * bb)
          = (2 * Pρ * (Y : ℝ)) ^ (2 * bb) := by rw [mul_pow, mul_pow]
      rw [hrhs] at hpow
      exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow
    -- Wr ≤ 2Pρ + 2Y, then final
    have hWr_le : ‖∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
        eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j)‖ ≤ 2 * Pρ + 2 * (Y : ℝ) := by
      have hYWr : (Y : ℝ) * ‖∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j)‖
          ≤ (Y : ℝ) * (2 * Pρ + 2 * (Y : ℝ)) := by nlinarith [hshift, hsumroot, hY0R]
      exact le_of_mul_le_mul_left hYWr hY0R
    calc ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖
        ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
            eR (∑ j ∈ Finset.range (k + 1), c j * (m : ℝ) ^ j)‖
          + 2 * π * ((P' : ℝ) * (2 * (t / (2 * π))
            * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))) := hstep0
      _ ≤ (2 * Pρ + 2 * (Y : ℝ)) + Pρ := add_le_add hWr_le hTaylor
      _ ≤ 8 * Pρ := by linarith [h2Y]
  · -- TRIVIAL branch: P' < Y
    have htriv : ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖ ≤ (P' : ℝ) := by
      calc ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖
          ≤ ∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), ‖eR (phi t n)‖ := norm_sum_le _ _
        _ = ∑ _n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), (1 : ℝ) :=
            Finset.sum_congr rfl (fun n _ => by rw [norm_eR])
        _ = (P' : ℝ) := by
            rw [Finset.sum_const, Int.card_Ioc]
            simp only [nsmul_eq_mul, mul_one]
            rw [show (N₀ : ℤ) + (P' : ℤ) - N₀ = (P' : ℤ) from by ring]
            simp
    have hP'YR : (P' : ℝ) < (Y : ℝ) := by exact_mod_cast hlt
    have hhalf1 : (1 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.one_le_rpow (by exact_mod_cast hP1') (by norm_num)
    have hYceil : (Y : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) + 1 := by
      rw [hY]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have hle := rpow_half_le_one_sub hP1' hρhalf
    calc ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖ ≤ (P' : ℝ) := htriv
      _ ≤ 8 * Pρ := by rw [hPρ]; linarith [hPρpos]

end Salt.Vk
