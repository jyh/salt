/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.GrowthPow

/-!
# S8 MR-CORE rung H1.0 — `one_line_pow_growth` (the σ = 1 power-growth stone)

The near-1-line growth bound

  `‖ζ(1+d'+it)‖ ≤ C·(log|t|)^{3/4}·(loglog|t|)^4`  for `0 ≤ d' ≤ 1`, `|t| ≥ T₀`.

This is the missing `σ = 1` upper bound flagged by all four S8 verdicts.  It closes the D3
compression consumed by wave-2 R1.2 (`dist_one_floor_pow`).

## Route (freeze PRIMARY, dyadic-block form)

The proof reuses the VK dyadic machinery already landed in `Salt/Vk/GrowthPow.lean`.  Truncate
`ζ(σ+it)` (`σ = 1+d' ∈ [1,2]`) at `N = ⌈t²⌉` via `zeta_sub_dirichlet_bound` (error `≤ 4`).  Bound
the length-`N` partial sum by a **geometric dyadic ladder**:

* every dyadic block `(M, x']` (`M < x' ≤ 2M`, `M ≤ t²`) obeys `‖∑ n^{−s}‖ ≤ 1348·M^{−Θ/2}`
  (`Θ = vkTheta t`).  This comes from `vk_dirichlet_block_le` run at the sub-unit line
  `σ₀ = 1−Θ/2 ∈ [1−Θ,1)` (which routes low/mid/high internally, giving `≤ 1348` for **every**
  prefix), followed by one Abel weighting (`abel_antitone_prefix`) that folds the residual antitone
  weight `n^{−(σ−1+Θ/2)}`, leaving the decay `M^{−Θ/2}`.
* summing the block bounds over the dyadic ladder gives the geometric series
  `1348·∑_j (2^{−Θ/2})^j ≤ 1348/(1−2^{−Θ/2}) ≤ C·(log|t|)^{3/4}(loglog|t|)²`, since
  `1/Θ = 1000·(log t)^{3/4}(loglog t)²`.

Combined with the truncation error and the `n = 1` term, `‖ζ(1+d'+it)‖ ≤ C·L^{3/4}ℓ² ≤ C·L^{3/4}ℓ⁴`.

No new analysis, no `native_decide`, no new axioms — pure reuse of the landed VK block tools.
-/

namespace Salt.MR

open Complex Salt.Vk Salt.ExpSum

/-- **Residual-weight merge.**  Splits `n^{−(σ+it)}` as the real residual weight
`n^{−(σ−1+Θ/2)}` (folded by Abel) times the sub-unit Dirichlet term `n^{−((1−Θ/2)+it)}`. -/
private lemma cpow_resid_merge (σ t Θ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (((n : ℝ) ^ (-(σ - 1 + Θ / 2)) : ℝ) : ℂ)
        * (n : ℂ) ^ (-(((1 - Θ / 2 : ℝ) : ℂ) + (t : ℂ) * I))
      = (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.ofReal_cpow hn0, Complex.ofReal_natCast,
    ← Complex.cpow_add _ _ hnC]
  congr 1
  push_cast
  ring

/-- **The geometric dyadic block bound.**  On `σ ≥ 1`, `log t ≥ e^100`, every dyadic block
`(M, x']` (`1 ≤ M`, `M < x' ≤ 2M`, `M ≤ t²`) of the `n^{−s}` sum obeys
`‖∑_{(M,x']} n^{−s}‖ ≤ 1348·M^{−Θ/2}` where `Θ = vkTheta t`.  `vk_dirichlet_block_le` at
`σ₀ = 1−Θ/2` gives the uniform prefix bound `≤ 1348`; `abel_antitone_prefix` folds the residual
weight `n^{−(σ−1+Θ/2)}`, leaving the decay `M^{−Θ/2}`. -/
lemma onelinepow_block_le {σ t : ℝ} {M x' : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσ1 : 1 ≤ σ) (hM1 : 1 ≤ M) (hMx' : M < x') (hx'2 : x' ≤ 2 * M)
    (hMt2 : (M : ℝ) ≤ t ^ 2) :
    ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ 1348 * (M : ℝ) ^ (-(vkTheta t / 2)) := by
  have hlogt1 : 1 < Real.log t := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith [hL100]
  set Θ : ℝ := vkTheta t with hΘdef
  have hΘpos : 0 < Θ := vkTheta_pos hlogt1
  set σ₀ : ℝ := 1 - Θ / 2 with hσ₀def
  have hσ₀lo : 1 - Θ ≤ σ₀ := by rw [hσ₀def]; linarith
  have hσ₀hi : σ₀ < 1 := by rw [hσ₀def]; linarith
  set a : ℝ := σ - 1 + Θ / 2 with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  set w : ℕ → ℝ := fun n => (n : ℝ) ^ (-a) with hwdef
  set z : ℕ → ℂ := fun n => (n : ℂ) ^ (-((σ₀ : ℂ) + (t : ℂ) * I)) with hzdef
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  -- prefix bound via `vk_dirichlet_block_le` at `σ₀`
  have hpref : ∀ k : ℕ, M < k → k ≤ x' → ‖∑ n ∈ Finset.Ioc M k, z n‖ ≤ 1348 := by
    intro k hMk hkx'
    rw [hzdef]
    exact vk_dirichlet_block_le ht0 hL100 hσ₀lo hσ₀hi hM1 hMk (le_trans hkx' hx'2) hMt2
  have hwnn : ∀ n, M < n → n ≤ x' → 0 ≤ w n := fun n _ _ => by
    rw [hwdef]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hwanti : ∀ n, M < n → n < x' → w (n + 1) ≤ w n := fun n hn _ => by
    rw [hwdef]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    exact Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast Nat.le_succ n) (by linarith)
  have habel := abel_antitone_prefix M x' hMx' w z 1348 (by norm_num) hwnn hwanti hpref
  -- rewrite the weighted sum as the σ-Dirichlet block
  have hmerge : ∑ n ∈ Finset.Ioc M x', ((w n : ℝ) : ℂ) * z n
      = ∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
    apply Finset.sum_congr rfl
    intro n hn; rw [Finset.mem_Ioc] at hn
    rw [hwdef, hzdef]
    exact cpow_resid_merge σ t Θ (by omega)
  rw [hmerge] at habel
  refine le_trans habel ?_
  -- `w(M+1)·1348 ≤ 1348·M^{−Θ/2}`
  have hstep : w (M + 1) ≤ (M : ℝ) ^ (-(Θ / 2)) := by
    rw [hwdef]
    calc ((M + 1 : ℕ) : ℝ) ^ (-a) ≤ (M : ℝ) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos hMpos (by push_cast; linarith) (by linarith)
      _ = (M : ℝ) ^ (-(σ - 1)) * (M : ℝ) ^ (-(Θ / 2)) := by
          rw [← Real.rpow_add hMpos]; congr 1; rw [hadef]; ring
      _ ≤ 1 * (M : ℝ) ^ (-(Θ / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hMpos.le _)
          exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hM1) (by linarith)
      _ = (M : ℝ) ^ (-(Θ / 2)) := by ring
  calc w (M + 1) * 1348 ≤ (M : ℝ) ^ (-(Θ / 2)) * 1348 :=
        mul_le_mul_of_nonneg_right hstep (by norm_num)
    _ = 1348 * (M : ℝ) ^ (-(Θ / 2)) := by ring

/-- `((2^J)^{−Θ/2}) = (2^{−Θ/2})^J` — bridges the dyadic block base `M = 2^J` to the geometric
ratio `r = 2^{−Θ/2}`. -/
private lemma pow2_rpow_eq (Θ : ℝ) (J : ℕ) :
    ((2 ^ J : ℕ) : ℝ) ^ (-(Θ / 2)) = ((2 : ℝ) ^ (-(Θ / 2))) ^ J := by
  rw [show ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J from by push_cast; ring,
    ← Real.rpow_natCast ((2 : ℝ) ^ (-(Θ / 2))) J, ← Real.rpow_natCast (2 : ℝ) J,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- **The geometric dyadic ladder.**  Given the per-block bound
`‖∑_{(M,x']} n^{−s}‖ ≤ 1348·M^{−Θ/2}` for every dyadic block within `(1, N]`, the whole
length-`N` tail obeys the geometric bound `‖∑_{(1,N]} n^{−s}‖ ≤ 1348/(1 − 2^{−Θ/2})`. -/
private lemma onelinepow_ladder {s : ℂ} {N : ℕ} {Θ : ℝ} (hΘ0 : 0 < Θ) (hN1 : 1 ≤ N)
    (hblock : ∀ M x' : ℕ, 1 ≤ M → M < x' → x' ≤ 2 * M → x' ≤ N →
        ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-s)‖ ≤ 1348 * (M : ℝ) ^ (-(Θ / 2))) :
    ‖∑ n ∈ Finset.Ioc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1348 * (1 - (2 : ℝ) ^ (-(Θ / 2)))⁻¹ := by
  set r : ℝ := (2 : ℝ) ^ (-(Θ / 2)) with hrdef
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    have h : (2 : ℝ) ^ (-(Θ / 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    rw [hrdef]; exact h
  -- ladder induction on the number of doublings
  have hlad : ∀ (J Y : ℕ), 1 ≤ Y → Y ≤ 2 ^ J → Y ≤ N →
      ‖∑ n ∈ Finset.Ioc 1 Y, (n : ℂ) ^ (-s)‖ ≤ 1348 * ∑ j ∈ Finset.range J, r ^ j := by
    intro J
    induction J with
    | zero =>
        intro Y hY0 hY1 _
        simp only [pow_zero] at hY1
        have : Y = 1 := le_antisymm hY1 hY0
        subst this; simp
    | succ J ih =>
        intro Y hY0 hY1 hYN
        by_cases hc : Y ≤ 2 ^ J
        · refine le_trans (ih Y hY0 hc hYN) ?_
          rw [Finset.sum_range_succ]
          have hrJ : (0 : ℝ) ≤ r ^ J := pow_nonneg hr0.le J
          have hmono : ∑ j ∈ Finset.range J, r ^ j
              ≤ ∑ j ∈ Finset.range J, r ^ j + r ^ J := by linarith
          exact mul_le_mul_of_nonneg_left hmono (by norm_num)
        · replace hc : 2 ^ J < Y := not_le.mp hc
          have hmid : 1 ≤ 2 ^ J := Nat.one_le_pow J 2 (by norm_num)
          have hsplit : ∑ n ∈ Finset.Ioc 1 Y, (n : ℂ) ^ (-s)
              = ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ J), (n : ℂ) ^ (-s)
                + ∑ n ∈ Finset.Ioc (2 ^ J) Y, (n : ℂ) ^ (-s) :=
            (Finset.sum_Ioc_consecutive _ hmid (le_of_lt hc)).symm
          rw [hsplit]
          refine le_trans (norm_add_le _ _) ?_
          have hb1 := ih (2 ^ J) hmid (le_refl _) (le_trans (le_of_lt hc) hYN)
          have hY2M : Y ≤ 2 * 2 ^ J := by
            rw [show 2 * 2 ^ J = 2 ^ (J + 1) from by rw [pow_succ]; ring]; exact hY1
          have hb2 := hblock (2 ^ J) Y hmid hc hY2M hYN
          rw [pow2_rpow_eq Θ J, ← hrdef] at hb2
          calc _ ≤ 1348 * ∑ j ∈ Finset.range J, r ^ j + 1348 * r ^ J := add_le_add hb1 hb2
            _ = 1348 * ∑ j ∈ Finset.range (J + 1), r ^ j := by
                rw [Finset.sum_range_succ]; ring
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, N ≤ 2 ^ J := ⟨N, le_of_lt Nat.lt_two_pow_self⟩
  have hmain := hlad J N hN1 hJ (le_refl N)
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hgeom : ∑ j ∈ Finset.range J, r ^ j ≤ (1 - r)⁻¹ := by
    have key : (∑ j ∈ Finset.range J, r ^ j) * (1 - r) = 1 - r ^ J := by
      have hgm := geom_sum_mul r J
      have hneg : (1 - r) = -(r - 1) := by ring
      rw [hneg, mul_neg, hgm]; ring
    have hval : ∑ j ∈ Finset.range J, r ^ j = (1 - r ^ J) / (1 - r) := by
      rw [eq_div_iff (ne_of_gt h1r)]; exact key
    rw [hval, div_le_iff₀ h1r, inv_mul_cancel₀ (ne_of_gt h1r)]
    linarith [pow_nonneg hr0.le J]
  exact le_trans hmain (mul_le_mul_of_nonneg_left hgeom (by norm_num))

/-- **The geometric tail, evaluated.**  `1348/(1 − 2^{−Θ/2}) ≤ 8·10⁶·(log t)^{3/4}(loglog t)²`,
using `1/Θ = 1000·(log t)^{3/4}(loglog t)²` and `1 − 2^{−Θ/2} ≥ Θ·log 2/4`. -/
private lemma tail_geom_bound {t : ℝ} (hL1 : 1 ≤ Real.log t)
    (hℓ1 : 1 ≤ Real.log (Real.log t)) :
    1348 * (1 - (2 : ℝ) ^ (-(vkTheta t / 2)))⁻¹
      ≤ 8000000 * ((Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ)) := by
  set D : ℝ := (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) with hDdef
  have hLpow1 : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hL1 (by norm_num)
  have hℓpow1 : (1 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := one_le_pow₀ hℓ1
  have hD1 : (1 : ℝ) ≤ D := by rw [hDdef]; nlinarith [hLpow1, hℓpow1]
  have hDpos : (0 : ℝ) < D := by linarith
  have hΘeq : vkTheta t = (1 / 1000) / D := by rw [hDdef, vkTheta]
  set Θ : ℝ := vkTheta t with hΘdef
  have hΘpos : 0 < Θ := by rw [hΘeq]; positivity
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  -- x := (Θ/2)·log 2 and r := 2^{−Θ/2} = exp(−x)
  set x : ℝ := (Θ / 2) * Real.log 2 with hxdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hΘle : Θ ≤ 1 / 1000 := by
    rw [hΘeq, div_le_iff₀ hDpos]; nlinarith [hD1]
  have hx1 : x ≤ 1 := by rw [hxdef]; nlinarith [hΘle, hlog2le, hΘpos.le, hlog2pos.le]
  have hrx : (2 : ℝ) ^ (-(Θ / 2)) = Real.exp (-x) := by
    have hlx : Real.log 2 * (-(Θ / 2)) = -x := by rw [hxdef]; ring
    rw [Real.rpow_def_of_pos (by norm_num), hlx]
  -- 1 − 2^{−Θ/2} ≥ x/2
  have hexpx : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp x])
  have h1xpos : (0 : ℝ) < 1 + x := by linarith
  have h2 : (1 : ℝ) / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ h1xpos]; nlinarith [hx1, hxpos.le]
  have hden : x / 2 ≤ 1 - (2 : ℝ) ^ (-(Θ / 2)) := by rw [hrx]; linarith [hexpx, h2]
  -- invert: (1 − 2^{−Θ/2})⁻¹ ≤ 2/x
  have hx2pos : (0 : ℝ) < x / 2 := by linarith
  have hinv : (1 - (2 : ℝ) ^ (-(Θ / 2)))⁻¹ ≤ 2 / x := by
    rw [← one_div]
    calc (1 : ℝ) / (1 - (2 : ℝ) ^ (-(Θ / 2))) ≤ 1 / (x / 2) :=
          one_div_le_one_div_of_le hx2pos hden
      _ = 2 / x := by rw [one_div_div]
  -- 2/x ≤ 5772·D  (since x = log2/(2000 D) and log2 > 0.693)
  have hxval : x = Real.log 2 / (2000 * D) := by
    rw [hxdef, hΘeq]; field_simp; ring
  have h2overx : 2 / x ≤ 5772 * D := by
    rw [hxval, div_div_eq_mul_div, div_le_iff₀ hlog2pos]
    nlinarith [hlog2gt, hDpos]
  calc 1348 * (1 - (2 : ℝ) ^ (-(Θ / 2)))⁻¹
      ≤ 1348 * (2 / x) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ ≤ 1348 * (5772 * D) := mul_le_mul_of_nonneg_left h2overx (by norm_num)
    _ ≤ 8000000 * D := by nlinarith [hDpos]

/-- **Positive-height core.**  For `t ≥ exp(exp 100)` and `0 ≤ d' ≤ 1`,
`‖ζ(1+d'+it)‖ ≤ 8000005·(log t)^{3/4}(loglog t)^4`.  Truncate at `⌈t²⌉` (`zeta_sub_dirichlet_bound`,
error `≤ 4`), peel the `n = 1` term (`≤ 1`), and bound the length-`N` tail by the geometric ladder
`onelinepow_ladder` + `tail_geom_bound`. -/
private lemma one_line_pow_growth_pos {d' t : ℝ} (hd0 : 0 ≤ d') (hd1 : d' ≤ 1)
    (ht : Real.exp (Real.exp 100) ≤ t) :
    ‖riemannZeta (((1 + d' : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ 8000005 * ((Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (4 : ℕ)) := by
  set σ : ℝ := 1 + d' with hσdef
  have hσ1 : 1 ≤ σ := by rw [hσdef]; linarith
  have hσ34 : (3 : ℝ) / 4 ≤ σ := by rw [hσdef]; linarith
  have hσ3 : σ ≤ 3 := by rw [hσdef]; linarith
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hL100 : Real.exp 100 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos _) ht
    rwa [Real.log_exp] at h
  have hlogt1 : 1 < Real.log t := by linarith [hL100, hexp100]
  have hL1 : (1 : ℝ) ≤ Real.log t := le_of_lt hlogt1
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log t) := by
    have h100 : (100 : ℝ) ≤ Real.log (Real.log t) := by
      rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hL100
    linarith
  have ht100 : (100 : ℝ) ≤ t := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) :=
      Real.exp_le_exp.mpr (by linarith [hexp100])
    linarith [ht, hexp100, h2]
  set N : ℕ := ⌈t ^ 2⌉₊ with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef, Nat.one_le_ceil_iff]; positivity
  have hΘpos : 0 < vkTheta t := vkTheta_pos hlogt1
  -- per-block bound over the ladder
  have hblock : ∀ M x' : ℕ, 1 ≤ M → M < x' → x' ≤ 2 * M → x' ≤ N →
      ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
        ≤ 1348 * (M : ℝ) ^ (-(vkTheta t / 2)) := by
    intro M x' hM1 hMx' _hx'2 hx'N
    have hMt2 : (M : ℝ) ≤ t ^ 2 := by
      have hMN : M + 1 ≤ N := by omega
      have hNle : (N : ℝ) ≤ t ^ 2 + 1 := by
        rw [hNdef]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
      have hMNR : (M : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hMN
      linarith
    exact onelinepow_block_le ht0 hL100 hσ1 hM1 hMx' _hx'2 hMt2
  have htail := onelinepow_ladder (s := (σ : ℂ) + (t : ℂ) * I) (N := N) (Θ := vkTheta t)
    hΘpos hN1 hblock
  have hgeom := tail_geom_bound (t := t) hL1 hℓ1
  -- peel the `n = 1` term
  have hins : Finset.Icc 1 N = insert 1 (Finset.Ioc 1 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Ioc 1 N := by simp
  have hDnorm : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ 1 + 1348 * (1 - (2 : ℝ) ^ (-(vkTheta t / 2)))⁻¹ := by
    rw [hins, Finset.sum_insert h1notin]
    refine le_trans (norm_add_le _ _) ?_
    have h1n : ‖((1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = 1 := by
      rw [Nat.cast_one, Complex.one_cpow, norm_one]
    rw [h1n]; linarith [htail]
  -- assemble
  have hζle : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ 4 + (1 + 1348 * (1 - (2 : ℝ) ^ (-(vkTheta t / 2)))⁻¹) := by
    have happrox := zeta_sub_dirichlet_bound (σ := σ) hσ34 hσ3 ht100
    have htri := norm_le_norm_add_norm_sub' (riemannZeta ((σ : ℂ) + (t : ℂ) * I))
      (∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))
    rw [← hNdef] at htri happrox
    linarith [htri, happrox, hDnorm]
  -- ℓ² ≤ ℓ⁴ and the constant absorption
  have hLp : (0 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have hℓ2 : (Real.log (Real.log t)) ^ (2 : ℕ) ≤ (Real.log (Real.log t)) ^ (4 : ℕ) :=
    pow_le_pow_right₀ hℓ1 (by norm_num)
  have hℓ4 : (1 : ℝ) ≤ (Real.log (Real.log t)) ^ (4 : ℕ) := one_le_pow₀ hℓ1
  have hLp1 : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hL1 (by norm_num)
  have hbig : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (4 : ℕ) := by
    nlinarith [hLp1, hℓ4]
  have hprod : (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ)
      ≤ (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (4 : ℕ) :=
    mul_le_mul_of_nonneg_left hℓ2 hLp
  calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ 5 + 8000000 * ((Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ)) := by
        linarith [hζle, hgeom]
    _ ≤ 8000005 * ((Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (4 : ℕ)) := by
        nlinarith [hprod, hbig]

/-- **`one_line_pow_growth` (S8 rung H1.0).**  The near-1-line power growth of ζ:
`‖ζ(1+d'+it)‖ ≤ C·(log|t|)^{3/4}(loglog|t|)^4` for `0 ≤ d' ≤ 1`, `|t| ≥ T₀`.  The `σ = 1` upper
bound flagged by all four S8 verdicts; witnesses `C = 8000005`, `T₀ = exp(exp 100)`. -/
theorem one_line_pow_growth :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ d' t : ℝ, 0 ≤ d' → d' ≤ 1 → T₀ ≤ |t| →
      ‖riemannZeta (((1 + d' : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ C * ((Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ)) := by
  refine ⟨8000005, Real.exp (Real.exp 100), by norm_num, Real.exp_pos _, ?_⟩
  intro d' t hd0 hd1 ht
  rcases le_or_gt 0 t with htpos | htneg
  · rw [abs_of_nonneg htpos] at ht ⊢
    exact one_line_pow_growth_pos hd0 hd1 ht
  · rw [abs_of_neg htneg] at ht ⊢
    have hs1 : (((1 + d' : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, Complex.one_im] at him
      linarith
    have hconjpt : (starRingEnd ℂ) (((1 + d' : ℝ) : ℂ) + (t : ℂ) * I)
        = ((1 + d' : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
      ring
    have hz : riemannZeta (((1 + d' : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
        = (starRingEnd ℂ) (riemannZeta (((1 + d' : ℝ) : ℂ) + (t : ℂ) * I)) := by
      rw [← hconjpt]; exact riemannZeta_conj hs1
    have hconj : ‖riemannZeta (((1 + d' : ℝ) : ℂ) + (t : ℂ) * I)‖
        = ‖riemannZeta (((1 + d' : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ := by
      rw [hz, Complex.norm_conj]
    rw [hconj]
    exact one_line_pow_growth_pos hd0 hd1 ht

end Salt.MR
