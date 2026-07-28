/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.TwistHigh
import Salt.MR.VkTwistClose
import Salt.SW.StripConvergence

/-!
# VK-TWIST VT-4 — the socket `VkTwistUB`, discharged

`Salt/MR/VkTwistClose.lean` (VT-5/VT-6) built the whole consumer side of the campaign
against the socket

  `VkTwistUB C ψ X t : ‖L((1 + 1/log X) − it, ψ)‖ ≤ C·√q·(log|t|)^{3/4}·(loglog|t|)⁴`.

This file supplies it.  Four moves:

* **§1 — the twisted ladder.**  `Salt/Vk/TwistHigh.lean` gives the unconditional twisted
  per-block bound `‖∑_{(M,x']} e(βn)·n^{−(σ+it)}‖ ≤ 1348` on the sub-unit line.  Running
  the blocks at `σ₀ = 1 − Θ/2` and folding the residual weight `n^{−(σ−1+Θ/2)}` by one
  Abel step converts that into the per-block decay `1348·M^{−Θ/2}`, whose dyadic geometric
  sum is `≤ 1348/(1 − 2^{−Θ/2}) ≍ (log t)^{3/4}(loglog t)²`.  This is
  `OneLinePowGrowth`'s ladder with the twist carried through, verbatim.

* **§2 — the finite Fourier completion.**  `χ mod q` is a periodic function, so
  `q·χ(n) = ∑_{a<q} c_a·e(an/q)` with `|c_a| ≤ q`, by the *elementary* orthogonality
  `∑_{a<q} e(ad/q) = q·[q ∣ d]` (a geometric sum — no Gauss sum, no primitivity, and in
  particular no appeal to `|τ(χ)| = √q`, which mathlib does not have).  This converts the
  character sum into `q` twisted sums at `β = a/q` and pays a factor `q`.

* **§3 — the truncation.**  `SW.norm_LFunction_sub_partial_le` at Pólya–Vinogradov's
  `M = √q(1+log q)` — its gate is `0 < Re s`, so the bridge point `Re s = 1 + 1/log X > 1`
  is comfortably inside — with `N = ⌈t²⌉`, whose tail is `O(√q(1+log q)·(1+|t|)/t²)`.

* **§4 — the socket, and the campaign capstone.**  `vkTwistUB_holds` discharges
  `VkTwistUB`, and `capFreeFloor3_lamChi_unconditional` composes it with VT-6's
  `capFreeFloor3_lamChi_vk`: `CapFreeFloor3 (lamChi χ) X` for non-real `χ` under a scale
  threshold *alone*.  No socket remains.

## The honest `q`-exponent

The profile's `√q` slot is **not** what the proof spends.  §2 costs a full `q` (the crude
Fourier completion, `|c_a| ≤ q`), and §3 costs `√q(1+log q)`.  The total is `q^{3/2}`-grade,
NOT `q^{1/2}`.  This costs the campaign nothing, because `vkProfile`'s constant `C` is
quantified *after* `q` everywhere downstream (`chi_floor_vk_pointwise`,
`capFreeFloor3_lamChi_vk`): the discharge below is stated at

  `C = vkTwistConst q = 10^7·q·(1 + log q)`,

so `vkProfile (vkTwistConst q) q t = 10^7·q^{3/2}(1+log q)·(log|t|)^{3/4}(loglog|t|)⁴`, and
the extra `q` lands in `vkDebitConst C`'s `(1/4)·log C` — a term VT-6 already carries
symbolically in its threshold.  `vkProfile` itself is untouched; nothing upstream re-pins.
-/

namespace Salt.MR

open Complex Salt.Vk Salt.ExpSum

/-! ## §1 — the twisted dyadic ladder -/

/-- **Residual-weight merge, twisted.**  Splits `e(βn)·n^{−(σ+it)}` as the real residual
weight `n^{−(σ−1+Θ/2)}` (folded by Abel) times the sub-unit twisted term.  The twist is
unimodular and rides through untouched. -/
private lemma twist_resid_merge (σ t Θ β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (((n : ℝ) ^ (-(σ - 1 + Θ / 2)) : ℝ) : ℂ)
        * (eR (β * (n : ℝ)) * (n : ℂ) ^ (-(((1 - Θ / 2 : ℝ) : ℂ) + (t : ℂ) * I)))
      = eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hmerge : (((n : ℝ) ^ (-(σ - 1 + Θ / 2)) : ℝ) : ℂ)
      * (n : ℂ) ^ (-(((1 - Θ / 2 : ℝ) : ℂ) + (t : ℂ) * I))
    = (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
    rw [Complex.ofReal_cpow hn0, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hnC]
    congr 1
    push_cast
    ring
  calc (((n : ℝ) ^ (-(σ - 1 + Θ / 2)) : ℝ) : ℂ)
        * (eR (β * (n : ℝ)) * (n : ℂ) ^ (-(((1 - Θ / 2 : ℝ) : ℂ) + (t : ℂ) * I)))
      = eR (β * (n : ℝ)) * ((((n : ℝ) ^ (-(σ - 1 + Θ / 2)) : ℝ) : ℂ)
          * (n : ℂ) ^ (-(((1 - Θ / 2 : ℝ) : ℂ) + (t : ℂ) * I))) := by ring
    _ = eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by rw [hmerge]

/-- **The twisted geometric dyadic block bound.**  On `σ ≥ 1`, `log t ≥ e^100`, every dyadic
block `(M, x']` (`1 ≤ M`, `M < x' ≤ 2M`, `M ≤ t²`) of the twisted sum obeys
`‖∑_{(M,x']} e(βn)·n^{−s}‖ ≤ 1348·M^{−Θ/2}`, `Θ = vkTheta t`.

`vk_dirichlet_block_twist_all` at `σ₀ = 1 − Θ/2` gives the uniform prefix bound `≤ 1348`;
`abel_antitone_prefix` folds the residual weight, leaving the decay `M^{−Θ/2}`. -/
lemma vk_twist_block_le {σ t β : ℝ} {M x' : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσ1 : 1 ≤ σ) (hM1 : 1 ≤ M) (hMx' : M < x') (hx'2 : x' ≤ 2 * M)
    (hMt2 : (M : ℝ) ≤ t ^ 2) :
    ‖∑ n ∈ Finset.Ioc M x', eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ 1348 * (M : ℝ) ^ (-(vkTheta t / 2)) := by
  have hlogt1 : 1 < Real.log t := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith [hL100]
  set Θ : ℝ := vkTheta t with hΘdef
  have hΘpos : 0 < Θ := vkTheta_pos hlogt1
  set σ₀ : ℝ := 1 - Θ / 2 with hσ₀def
  have hσ₀lo : 1 - Θ ≤ σ₀ := by rw [hσ₀def]; linarith
  set a : ℝ := σ - 1 + Θ / 2 with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  set w : ℕ → ℝ := fun n => (n : ℝ) ^ (-a) with hwdef
  set z : ℕ → ℂ := fun n => eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ₀ : ℂ) + (t : ℂ) * I)) with hzdef
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hpref : ∀ k : ℕ, M < k → k ≤ x' → ‖∑ n ∈ Finset.Ioc M k, z n‖ ≤ 1348 := by
    intro k hMk hkx'
    rw [hzdef]
    exact vk_dirichlet_block_twist_all ht0 hL100 hσ₀lo hM1 hMk (le_trans hkx' hx'2) hMt2
  have hwnn : ∀ n, M < n → n ≤ x' → 0 ≤ w n := fun n _ _ => by
    rw [hwdef]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hwanti : ∀ n, M < n → n < x' → w (n + 1) ≤ w n := fun n hn _ => by
    rw [hwdef]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    exact Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast Nat.le_succ n) (by linarith)
  have habel := abel_antitone_prefix M x' hMx' w z 1348 (by norm_num) hwnn hwanti hpref
  have hmerge : ∑ n ∈ Finset.Ioc M x', ((w n : ℝ) : ℂ) * z n
      = ∑ n ∈ Finset.Ioc M x', eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
    apply Finset.sum_congr rfl
    intro n hn; rw [Finset.mem_Ioc] at hn
    rw [hwdef, hzdef]
    exact twist_resid_merge σ t Θ β (by omega)
  rw [hmerge] at habel
  refine le_trans habel ?_
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

/-- `((2^J)^{−Θ/2}) = (2^{−Θ/2})^J`. -/
private lemma vk_pow2_rpow_eq (Θ : ℝ) (J : ℕ) :
    ((2 ^ J : ℕ) : ℝ) ^ (-(Θ / 2)) = ((2 : ℝ) ^ (-(Θ / 2))) ^ J := by
  rw [show ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J from by push_cast; ring,
    ← Real.rpow_natCast ((2 : ℝ) ^ (-(Θ / 2))) J, ← Real.rpow_natCast (2 : ℝ) J,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- **The geometric dyadic ladder, summand-generic.**  Given the per-block bound
`1348·M^{−Θ/2}` for every dyadic block inside `(1, N]`, the whole tail obeys
`1348/(1 − 2^{−Θ/2})`.  The proof never inspects the summand — this is
`OneLinePowGrowth`'s ladder with the `(n : ℂ)^{−s}` specialisation removed. -/
private lemma vk_twist_ladder {g : ℕ → ℂ} {N : ℕ} {Θ : ℝ} (hΘ0 : 0 < Θ) (hN1 : 1 ≤ N)
    (hblock : ∀ M x' : ℕ, 1 ≤ M → M < x' → x' ≤ 2 * M → x' ≤ N →
        ‖∑ n ∈ Finset.Ioc M x', g n‖ ≤ 1348 * (M : ℝ) ^ (-(Θ / 2))) :
    ‖∑ n ∈ Finset.Ioc 1 N, g n‖ ≤ 1348 * (1 - (2 : ℝ) ^ (-(Θ / 2)))⁻¹ := by
  set r : ℝ := (2 : ℝ) ^ (-(Θ / 2)) with hrdef
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    have h : (2 : ℝ) ^ (-(Θ / 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    rw [hrdef]; exact h
  have hlad : ∀ (J Y : ℕ), 1 ≤ Y → Y ≤ 2 ^ J → Y ≤ N →
      ‖∑ n ∈ Finset.Ioc 1 Y, g n‖ ≤ 1348 * ∑ j ∈ Finset.range J, r ^ j := by
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
          have hsplit : ∑ n ∈ Finset.Ioc 1 Y, g n
              = ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ J), g n
                + ∑ n ∈ Finset.Ioc (2 ^ J) Y, g n :=
            (Finset.sum_Ioc_consecutive _ hmid (le_of_lt hc)).symm
          rw [hsplit]
          refine le_trans (norm_add_le _ _) ?_
          have hb1 := ih (2 ^ J) hmid (le_refl _) (le_trans (le_of_lt hc) hYN)
          have hY2M : Y ≤ 2 * 2 ^ J := by
            rw [show 2 * 2 ^ J = 2 ^ (J + 1) from by rw [pow_succ]; ring]; exact hY1
          have hb2 := hblock (2 ^ J) Y hmid hc hY2M hYN
          rw [vk_pow2_rpow_eq Θ J, ← hrdef] at hb2
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

/-- **The geometric tail, evaluated.**  `1348/(1 − 2^{−Θ/2}) ≤ 8·10⁶·(log t)^{3/4}(loglog t)²`
(the twin of `OneLinePowGrowth`'s private `tail_geom_bound`, same constant). -/
private lemma vk_twist_tail_geom {t : ℝ} (hL1 : 1 ≤ Real.log t)
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
  set x : ℝ := (Θ / 2) * Real.log 2 with hxdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hΘle : Θ ≤ 1 / 1000 := by
    rw [hΘeq, div_le_iff₀ hDpos]; nlinarith [hD1]
  have hx1 : x ≤ 1 := by rw [hxdef]; nlinarith [hΘle, hlog2le, hΘpos.le, hlog2pos.le]
  have hrx : (2 : ℝ) ^ (-(Θ / 2)) = Real.exp (-x) := by
    have hlx : Real.log 2 * (-(Θ / 2)) = -x := by rw [hxdef]; ring
    rw [Real.rpow_def_of_pos (by norm_num), hlx]
  have hexpx : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp x])
  have h1xpos : (0 : ℝ) < 1 + x := by linarith
  have h2 : (1 : ℝ) / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ h1xpos]; nlinarith [hx1, hxpos.le]
  have hden : x / 2 ≤ 1 - (2 : ℝ) ^ (-(Θ / 2)) := by rw [hrx]; linarith [hexpx, h2]
  have hx2pos : (0 : ℝ) < x / 2 := by linarith
  have hinv : (1 - (2 : ℝ) ^ (-(Θ / 2)))⁻¹ ≤ 2 / x := by
    rw [← one_div]
    calc (1 : ℝ) / (1 - (2 : ℝ) ^ (-(Θ / 2))) ≤ 1 / (x / 2) :=
          one_div_le_one_div_of_le hx2pos hden
      _ = 2 / x := by rw [one_div_div]
  have hxval : x = Real.log 2 / (2000 * D) := by
    rw [hxdef, hΘeq]; field_simp; ring
  have h2overx : 2 / x ≤ 5772 * D := by
    rw [hxval, div_div_eq_mul_div, div_le_iff₀ hlog2pos]
    nlinarith [hlog2gt, hDpos]
  calc 1348 * (1 - (2 : ℝ) ^ (-(Θ / 2)))⁻¹
      ≤ 1348 * (2 / x) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ ≤ 1348 * (5772 * D) := mul_le_mul_of_nonneg_left h2overx (by norm_num)
    _ ≤ 8000000 * D := by nlinarith [hDpos]

/-- **§1's EXIT — the twisted Dirichlet head bound.**  For `t ≥ exp(exp 100)`, `σ ≥ 1`,
every twist `β` and every `N` with `N ≤ t² + 1`,

  `‖∑_{n ≤ N} e(βn)·n^{−(σ+it)}‖ ≤ 1 + 8·10⁶·(log t)^{3/4}(loglog t)²`.

The `1` is the `n = 1` term; everything else is the geometric ladder. -/
theorem vk_twist_head_le {σ t β : ℝ} {N : ℕ}
    (ht : Real.exp (Real.exp 100) ≤ t) (hσ1 : 1 ≤ σ) (hN1 : 1 ≤ N)
    (hNle : (N : ℝ) ≤ t ^ 2 + 1) :
    ‖∑ n ∈ Finset.Icc 1 N, eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
      ≤ 1 + 8000000 * ((Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ)) := by
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
  have hΘpos : 0 < vkTheta t := vkTheta_pos hlogt1
  have hblock : ∀ M x' : ℕ, 1 ≤ M → M < x' → x' ≤ 2 * M → x' ≤ N →
      ‖∑ n ∈ Finset.Ioc M x', eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖
        ≤ 1348 * (M : ℝ) ^ (-(vkTheta t / 2)) := by
    intro M x' hM1 hMx' hx'2 hx'N
    have hMt2 : (M : ℝ) ≤ t ^ 2 := by
      have hMN : M + 1 ≤ N := by omega
      have hMNR : (M : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hMN
      linarith
    exact vk_twist_block_le ht0 hL100 hσ1 hM1 hMx' hx'2 hMt2
  have htail := vk_twist_ladder (g := fun n : ℕ =>
      eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))
    (N := N) (Θ := vkTheta t) hΘpos hN1 hblock
  have hgeom := vk_twist_tail_geom (t := t) hL1 hℓ1
  have hins : Finset.Icc 1 N = insert 1 (Finset.Ioc 1 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  have h1notin : (1 : ℕ) ∉ Finset.Ioc 1 N := by simp
  rw [hins, Finset.sum_insert h1notin]
  refine le_trans (norm_add_le _ _) ?_
  have h1n : ‖eR (β * ((1 : ℕ) : ℝ)) * ((1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = 1 := by
    rw [norm_mul, norm_eR, Nat.cast_one, Complex.one_cpow, norm_one, one_mul]
  rw [h1n]
  linarith [htail, hgeom]

/-! ## §2 — the finite Fourier completion (elementary, no Gauss sum) -/

/-- `e(a·x) = e(x)^a` for a natural multiplier. -/
private lemma eR_natCast_mul (a : ℕ) (x : ℝ) : eR ((a : ℝ) * x) = (eR x) ^ a := by
  induction a with
  | zero => simp [eR]
  | succ a ih =>
      have hstep : ((a + 1 : ℕ) : ℝ) * x = (a : ℝ) * x + x := by push_cast; ring
      rw [hstep, eR_add, ih, pow_succ]

/-- `e(m) = 1` at every integer. -/
private lemma eR_intCast (m : ℤ) : eR ((m : ℝ)) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I m
  simp only [eR]
  rw [show (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (((m : ℝ)) : ℂ))
        = (m : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) from by push_cast; ring]
  exact h

/-- `e(y) = 1` forces `y` to be an integer. -/
private lemma eR_eq_one_imp {y : ℝ} (h : eR y = 1) : ∃ m : ℤ, y = (m : ℝ) := by
  simp only [eR] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2πI : (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hkey : (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) * ((y : ℝ) : ℂ)
      = (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) * (n : ℂ) := by
    rw [hn]; ring
  have := mul_left_cancel₀ h2πI hkey
  exact_mod_cast this

/-- **The elementary orthogonality relation.**  `∑_{a<q} e(a·d/q) = q·[q ∣ d]`, by the
geometric sum: the ratio `e(d/q)` has `q`-th power `e(d) = 1`, and equals `1` exactly when
`q ∣ d`.  No Gauss sum, no character, no primitivity. -/
private lemma eR_geom_delta {q : ℕ} (hq : 0 < q) (d : ℤ) :
    ∑ a ∈ Finset.range q, eR ((a : ℝ) * ((d : ℝ) / (q : ℝ)))
      = if ((q : ℤ) ∣ d) then (q : ℂ) else 0 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hterm : ∀ a ∈ Finset.range q,
      eR ((a : ℝ) * ((d : ℝ) / (q : ℝ))) = (eR ((d : ℝ) / (q : ℝ))) ^ a :=
    fun a _ => eR_natCast_mul a _
  rw [Finset.sum_congr rfl hterm]
  have hwq : (eR ((d : ℝ) / (q : ℝ))) ^ q = 1 := by
    rw [← eR_natCast_mul q ((d : ℝ) / (q : ℝ)),
      show (q : ℝ) * ((d : ℝ) / (q : ℝ)) = ((d : ℤ) : ℝ) from by field_simp]
    exact eR_intCast d
  by_cases hdvd : (q : ℤ) ∣ d
  · obtain ⟨k, hk⟩ := hdvd
    have hval : ((d : ℝ) / (q : ℝ)) = ((k : ℤ) : ℝ) := by
      rw [hk]; push_cast; field_simp
    rw [hval, eR_intCast, if_pos ⟨k, hk⟩]
    simp
  · rw [if_neg hdvd]
    have hwne : eR ((d : ℝ) / (q : ℝ)) ≠ 1 := by
      intro hcon
      obtain ⟨m, hm⟩ := eR_eq_one_imp hcon
      refine hdvd ⟨m, ?_⟩
      have : (d : ℝ) = (q : ℝ) * (m : ℝ) := by
        field_simp at hm; linarith [hm]
      exact_mod_cast this
    rw [geom_sum_eq hwne q, hwq]
    simp

/-- **THE COMPLETION.**  For any `χ mod q`, any finite `S ⊆ ℕ` and any weights `f`, a
uniform bound `B` on the `q` *additively twisted* sums `∑_{n∈S} e(an/q)·f n` (`a < q`) gives

  `‖∑_{n∈S} χ(n)·f n‖ ≤ q·B`.

The factor `q` (not `√q`) is the crude price of the elementary route: the Fourier
coefficients `c_a = ∑_r χ(r)e(−ar/q)` are bounded only by `q`, since mathlib has no
`|τ(χ)| = √q`.  §4 shows the campaign has room for it. -/
theorem char_sum_fourier_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (f : ℕ → ℂ) {B : ℝ}
    (hbd : ∀ a : ℕ, a < q →
      ‖∑ n ∈ S, eR ((a : ℝ) / (q : ℝ) * (n : ℝ)) * f n‖ ≤ B) :
    ‖∑ n ∈ S, χ (n : ZMod q) * f n‖ ≤ (q : ℝ) * B := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  -- the divisibility condition, read in `ZMod q`
  have hdvd_iff : ∀ (n : ℕ) (r : ZMod q),
      ((q : ℤ) ∣ ((n : ℤ) - ((r.val : ℕ) : ℤ))) ↔ ((n : ℕ) : ZMod q) = r := by
    intro n r
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [show (((r.val : ℕ) : ZMod q)) = r from by simp]
    exact sub_eq_zero
  -- the pointwise Fourier expansion
  have hpt : ∀ n : ℕ, (q : ℂ) * χ ((n : ℕ) : ZMod q)
      = ∑ a ∈ Finset.range q, ∑ r : ZMod q,
          χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ)) * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ))) := by
    intro n
    rw [Finset.sum_comm]
    have hrow : ∀ r : ZMod q,
        (∑ a ∈ Finset.range q,
            χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
              * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ))))
          = if ((n : ℕ) : ZMod q) = r then χ r * (q : ℂ) else 0 := by
      intro r
      set d : ℤ := (n : ℤ) - ((r.val : ℕ) : ℤ) with hddef
      have hcollapse : ∀ a ∈ Finset.range q,
          χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
              * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))
            = χ r * eR ((a : ℝ) * ((d : ℝ) / (q : ℝ))) := by
        intro a _
        rw [mul_assoc, ← eR_add]
        congr 2
        rw [hddef]
        push_cast
        ring
      rw [Finset.sum_congr rfl hcollapse, ← Finset.mul_sum, eR_geom_delta hq0 d]
      by_cases hc : ((n : ℕ) : ZMod q) = r
      · rw [if_pos ((hdvd_iff n r).mpr hc), if_pos hc]
      · rw [if_neg (fun hd => hc ((hdvd_iff n r).mp hd)), if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl (fun r _ => hrow r), Finset.sum_ite_eq Finset.univ
      (((n : ℕ) : ZMod q)) (fun r => χ r * (q : ℂ)), if_pos (Finset.mem_univ _), mul_comm]
  -- expand, swap, and bound each of the `q²` inner sums by `B`
  have hexpand : (q : ℂ) * ∑ n ∈ S, χ ((n : ℕ) : ZMod q) * f n
      = ∑ a ∈ Finset.range q, ∑ r : ZMod q, ∑ n ∈ S,
          (χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
            * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))) * f n := by
    rw [Finset.mul_sum]
    have hstep : ∀ n ∈ S, (q : ℂ) * (χ ((n : ℕ) : ZMod q) * f n)
        = ∑ a ∈ Finset.range q, ∑ r : ZMod q,
            (χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
              * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))) * f n := by
      intro n _
      rw [show (q : ℂ) * (χ ((n : ℕ) : ZMod q) * f n)
            = ((q : ℂ) * χ ((n : ℕ) : ZMod q)) * f n from by ring, hpt n,
        Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_mul _ _ _)
    rw [Finset.sum_congr rfl hstep]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  have hinner : ∀ a ∈ Finset.range q, ∀ r : ZMod q,
      ‖∑ n ∈ S, (χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
          * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))) * f n‖ ≤ B := by
    intro a ha r
    rw [Finset.mem_range] at ha
    have heq : (∑ n ∈ S, (χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
          * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))) * f n)
        = (χ r * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ))))
            * ∑ n ∈ S, eR ((a : ℝ) / (q : ℝ) * (n : ℝ)) * f n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [heq, norm_mul]
    have h1 : ‖χ r * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))‖ ≤ 1 := by
      rw [norm_mul, norm_eR, mul_one]
      exact χ.norm_le_one r
    have h2 := hbd a ha
    have hnn : (0 : ℝ) ≤ ‖∑ n ∈ S, eR ((a : ℝ) / (q : ℝ) * (n : ℝ)) * f n‖ := norm_nonneg _
    nlinarith [h1, h2, hnn, norm_nonneg (χ r * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ))))]
  have hbig : ‖(q : ℂ) * ∑ n ∈ S, χ ((n : ℕ) : ZMod q) * f n‖ ≤ (q : ℝ) * ((q : ℝ) * B) := by
    rw [hexpand]
    refine le_trans (norm_sum_le _ _) ?_
    have hrow : ∀ a ∈ Finset.range q,
        ‖∑ r : ZMod q, ∑ n ∈ S, (χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
            * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))) * f n‖ ≤ (q : ℝ) * B := by
      intro a ha
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ r : ZMod q, ‖∑ n ∈ S, (χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
              * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))) * f n‖
          ≤ ∑ _r : ZMod q, B := Finset.sum_le_sum (fun r _ => hinner a ha r)
        _ = (q : ℝ) * B := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card q, nsmul_eq_mul]
    calc ∑ a ∈ Finset.range q, ‖∑ r : ZMod q, ∑ n ∈ S,
            (χ r * eR ((a : ℝ) / (q : ℝ) * (n : ℝ))
              * eR (-((a : ℝ) * (r.val : ℝ) / (q : ℝ)))) * f n‖
        ≤ ∑ _a ∈ Finset.range q, (q : ℝ) * B := Finset.sum_le_sum hrow
      _ = (q : ℝ) * ((q : ℝ) * B) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [norm_mul, Complex.norm_natCast] at hbig
  exact le_of_mul_le_mul_left hbig hqR

/-! ## §3 — sign symmetry and the truncation -/

/-- Conjugation passes through a positive-integer cpow. -/
private lemma conj_natCast_cpow {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ w) = (n : ℂ) ^ ((starRingEnd ℂ) w) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj,
    map_mul, hlog, Complex.conj_ofReal]

/-- **The twisted head bound at either sign of the frequency.**  The twist family is closed
under `β ↦ −β`, so conjugating the whole sum turns `(β, T)` into `(−β, −T)` and the positive
branch covers both. -/
theorem vk_twist_head_abs_le {σ T β : ℝ} {N : ℕ}
    (hT : Real.exp (Real.exp 100) ≤ |T|) (hσ1 : 1 ≤ σ) (hN1 : 1 ≤ N)
    (hNle : (N : ℝ) ≤ T ^ 2 + 1) :
    ‖∑ n ∈ Finset.Icc 1 N, eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))‖
      ≤ 1 + 8000000
          * ((Real.log |T|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |T|)) ^ (2 : ℕ)) := by
  rcases le_or_gt 0 T with hTpos | hTneg
  · rw [abs_of_nonneg hTpos] at hT ⊢
    exact vk_twist_head_le hT hσ1 hN1 hNle
  · rw [abs_of_neg hTneg] at hT ⊢
    have hswap : ∑ n ∈ Finset.Icc 1 N,
          eR ((-β) * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I))
        = (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 N,
            eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_Icc] at hn
      rw [map_mul, conj_eR, conj_natCast_cpow hn.1, neg_mul]
      congr 1
      congr 1
      simp only [map_neg, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    have hnorm : ‖∑ n ∈ Finset.Icc 1 N,
          eR ((-β) * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I))‖
        = ‖∑ n ∈ Finset.Icc 1 N,
            eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))‖ := by
      rw [hswap, RCLike.norm_conj]
    rw [← hnorm]
    exact vk_twist_head_le hT hσ1 hN1 (by rw [show (-T) ^ 2 = T ^ 2 from by ring]; exact hNle)

/-- **The character head bound.**  Fourier completion (§2) applied to the twisted ladder
(§1): the length-`N` head of `L(s, χ)` at `s = σ + iT`, `σ ≥ 1`, is `≤ q·(1 + 8·10⁶·L^{3/4}ℓ²)`. -/
theorem vk_char_head_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ T : ℝ} {N : ℕ}
    (hT : Real.exp (Real.exp 100) ≤ |T|) (hσ1 : 1 ≤ σ) (hN1 : 1 ≤ N)
    (hNle : (N : ℝ) ≤ T ^ 2 + 1) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I))‖
      ≤ (q : ℝ) * (1 + 8000000
          * ((Real.log |T|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |T|)) ^ (2 : ℕ))) :=
  char_sum_fourier_le χ (Finset.Icc 1 N)
    (fun n => (n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * I)))
    (fun _a _ => vk_twist_head_abs_le hT hσ1 hN1 hNle)

/-! ## §4 — the socket, and the campaign capstone -/

/-- **The VT-4 constant.**  `10⁷·q·(1 + log q)` — the crude Fourier completion's `q`, the
Pólya–Vinogradov truncation's `√q(1+log q)`, and the ladder's `8·10⁶`, all in one place.
Against `vkProfile`'s own `√q` this is the honest `q^{3/2}(1+log q)` grade; see the module
docstring on why the campaign has room for it. -/
noncomputable def vkTwistConst (q : ℕ) : ℝ := 10000000 * (q : ℝ) * (1 + Real.log q)

lemma one_le_vkTwistConst {q : ℕ} [NeZero q] : 1 ≤ vkTwistConst q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  unfold vkTwistConst
  nlinarith [hq1, hlq]

lemma vkTwistConst_mono {f q : ℕ} (hf : 1 ≤ f) (hfq : f ≤ q) :
    vkTwistConst f ≤ vkTwistConst q := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hfqR : (f : ℝ) ≤ (q : ℝ) := by exact_mod_cast hfq
  have hlf : (0 : ℝ) ≤ Real.log f := Real.log_nonneg hf1
  have hlog : Real.log f ≤ Real.log q := Real.log_le_log (by linarith) hfqR
  unfold vkTwistConst
  nlinarith [hf1, hfqR, hlf, hlog]

/-- `vkProfile` is monotone in the constant and in the level. -/
lemma vkProfile_mono {C C' : ℝ} {f q : ℕ} {t : ℝ} (hC0 : 0 ≤ C) (hCC' : C ≤ C')
    (hfq : f ≤ q) (hL : 0 ≤ Real.log |t|) : vkProfile C f t ≤ vkProfile C' q t := by
  have hsq : Real.sqrt f ≤ Real.sqrt q := Real.sqrt_le_sqrt (by exact_mod_cast hfq)
  have hs0 : (0 : ℝ) ≤ Real.sqrt f := Real.sqrt_nonneg _
  have hA : (0 : ℝ) ≤ (Real.log |t|) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hL _
  have hB : (0 : ℝ) ≤ (Real.log (Real.log |t|)) ^ (4 : ℕ) := by positivity
  unfold vkProfile
  have h1 : C * Real.sqrt f ≤ C' * Real.sqrt q :=
    mul_le_mul hCC' hsq hs0 (le_trans hC0 hCC')
  have h2 : C * Real.sqrt f * (Real.log |t|) ^ ((3 : ℝ) / 4)
      ≤ C' * Real.sqrt q * (Real.log |t|) ^ ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_right h1 hA
  exact mul_le_mul_of_nonneg_right h2 hB

set_option maxHeartbeats 1000000 in
-- The bridge-point bookkeeping stages many rpow/log facts through `nlinarith`.
/-- **THE SOCKET, PRIMITIVE CASE.**  For a primitive `ψ mod q` (`q ≥ 2`), `X ≥ e` and
`|t| ≥ exp(exp 100)`,

  `‖L((1 + 1/log X) − it, ψ)‖ ≤ vkProfile (vkTwistConst q) q t`.

Truncate at `N = ⌈t²⌉` (`SW.norm_LFunction_sub_partial_le_primitive`, error `≤ √q(1+log q)`),
then bound the head by `vk_char_head_le`. -/
theorem vk_LFunction_bridge_le_primitive {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hprim : ψ.IsPrimitive) (hq2 : 2 ≤ q) {X t : ℝ}
    (hX : Real.exp 1 ≤ X) (ht : Real.exp (Real.exp 100) ≤ |t|) :
    ‖DirichletCharacter.LFunction ψ
        (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖
      ≤ vkProfile (vkTwistConst q) q t := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hsq1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hq1
  have hsqq : Real.sqrt q ≤ (q : ℝ) := by
    nlinarith [Real.sq_sqrt (le_trans zero_le_one hq1), Real.sqrt_nonneg ((q : ℝ))]
  -- the bridge point
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  set σ : ℝ := 1 + 1 / Real.log X with hσdef
  have hσ1 : 1 ≤ σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  set T : ℝ := -t with hTdef
  have hTeq : ((σ : ℝ) : ℂ) + (T : ℂ) * Complex.I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I := by
    rw [hσdef, hTdef]; push_cast; ring
  have habsT : |T| = |t| := by rw [hTdef, abs_neg]
  have hT2 : T ^ 2 = t ^ 2 := by rw [hTdef]; ring
  -- height facts
  have habs0 : (0 : ℝ) < |t| := lt_of_lt_of_le (Real.exp_pos _) ht
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hbig : (101 : ℝ) ≤ |t| := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) :=
      Real.exp_le_exp.mpr (by linarith [hexp100])
    linarith [ht, hexp100, h2]
  obtain ⟨hL100, hℓ100⟩ := vk_height_facts ht
  have hLpos : (0 : ℝ) < Real.log |t| := lt_of_lt_of_le (Real.exp_pos _) hL100
  have hLp1 : (1 : ℝ) ≤ (Real.log |t|) ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith [hexp100]) (by norm_num)
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log |t|) := by linarith
  have hℓ2 : (Real.log (Real.log |t|)) ^ (2 : ℕ) ≤ (Real.log (Real.log |t|)) ^ (4 : ℕ) :=
    pow_le_pow_right₀ hℓ1 (by norm_num)
  have hℓ4 : (1 : ℝ) ≤ (Real.log (Real.log |t|)) ^ (4 : ℕ) := one_le_pow₀ hℓ1
  have hDbig : (1 : ℝ) ≤ (Real.log |t|) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log |t|)) ^ (4 : ℕ) := by nlinarith [hLp1, hℓ4]
  -- the truncation length
  set N : ℕ := ⌈t ^ 2⌉₊ with hNdef
  have ht2pos : (0 : ℝ) < t ^ 2 := by nlinarith [habs0, abs_nonneg t, sq_abs t]
  have hN1 : 1 ≤ N := by rw [hNdef]; exact Nat.one_le_ceil_iff.mpr ht2pos
  have hNge : t ^ 2 ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ t ^ 2 + 1 := by
    rw [hNdef]; exact le_of_lt (Nat.ceil_lt_add_one ht2pos.le)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- the truncation error
  have hsre : ((((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I).re = σ := by
    simp [hσdef]
  have hsnorm : ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I‖ ≤ 2 + |t| := by
    have h1 : ‖(((1 + 1 / Real.log X : ℝ) : ℂ))‖ = |1 + 1 / Real.log X| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖((t : ℝ) : ℂ) * Complex.I‖ = |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I‖
        ≤ ‖(((1 + 1 / Real.log X : ℝ) : ℂ))‖ + ‖((t : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ = |1 + 1 / Real.log X| + |t| := by rw [h1, h2]
      _ ≤ 2 + |t| := by
          have habs : |1 + 1 / Real.log X| = 1 + 1 / Real.log X :=
            abs_of_nonneg (by linarith)
          rw [habs]; linarith
  have htrunc := Salt.SW.norm_LFunction_sub_partial_le_primitive ψ hprim hq2
    (s := (((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I)
    (by rw [hsre]; linarith) hN1
  rw [hsre] at htrunc
  have herr : Real.sqrt q * (1 + Real.log q)
        * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I‖ * (1 + 1 / σ))
        * (N : ℝ) ^ (-σ)
      ≤ Real.sqrt q * (1 + Real.log q) := by
    have hinv : (1 : ℝ) + 1 / σ ≤ 2 := by
      have : 1 / σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hfac : (1 : ℝ) + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I‖ * (1 + 1 / σ)
        ≤ 5 + 2 * |t| := by
      have hnn : (0 : ℝ) ≤ ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I‖ :=
        norm_nonneg _
      nlinarith [hsnorm, hinv, hnn, habs0]
    have hNσ : (N : ℝ) ^ (-σ) ≤ 1 / (t ^ 2) := by
      have h1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
      have h2 : (N : ℝ) ^ (-1 : ℝ) = 1 / (N : ℝ) := by rw [Real.rpow_neg_one, one_div]
      rw [h2] at h1
      have h3 : (1 : ℝ) / (N : ℝ) ≤ 1 / (t ^ 2) := by
        apply one_div_le_one_div_of_le ht2pos hNge
      linarith
    have hratio : (5 + 2 * |t|) * (1 / (t ^ 2)) ≤ 1 := by
      have hsqt : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      rw [hsqt, mul_one_div, div_le_one (by positivity)]
      nlinarith [hbig, mul_le_mul_of_nonneg_right hbig (abs_nonneg t)]
    have hNσ0 : (0 : ℝ) ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg hNpos.le _
    have hs0 : (0 : ℝ) ≤ Real.sqrt q * (1 + Real.log q) := by positivity
    calc Real.sqrt q * (1 + Real.log q)
            * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I‖ * (1 + 1 / σ))
            * (N : ℝ) ^ (-σ)
        ≤ Real.sqrt q * (1 + Real.log q) * (5 + 2 * |t|) * (N : ℝ) ^ (-σ) := by
          apply mul_le_mul_of_nonneg_right _ hNσ0
          exact mul_le_mul_of_nonneg_left hfac hs0
      _ ≤ Real.sqrt q * (1 + Real.log q) * (5 + 2 * |t|) * (1 / (t ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hNσ _
          positivity
      _ = Real.sqrt q * (1 + Real.log q) * ((5 + 2 * |t|) * (1 / (t ^ 2))) := by ring
      _ ≤ Real.sqrt q * (1 + Real.log q) * 1 := mul_le_mul_of_nonneg_left hratio hs0
      _ = Real.sqrt q * (1 + Real.log q) := by ring
  -- the head
  have hhead := vk_char_head_le (q := q) ψ (σ := σ) (T := T) (N := N)
    (by rw [habsT]; exact ht) hσ1 hN1 (by rw [hT2]; exact hNle)
  rw [habsT, hTeq] at hhead
  -- assemble
  have htri := norm_le_norm_add_norm_sub' (DirichletCharacter.LFunction ψ
      ((((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I))
    (∑ n ∈ Finset.Icc 1 N, ψ (n : ZMod q)
      * (n : ℂ) ^ (-((((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I)))
  have htot : ‖DirichletCharacter.LFunction ψ
        ((((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I)‖
      ≤ Real.sqrt q * (1 + Real.log q)
        + (q : ℝ) * (1 + 8000000 * ((Real.log |t|) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log |t|)) ^ (2 : ℕ))) := by
    linarith [htri, htrunc, herr, hhead]
  refine le_trans htot ?_
  -- `√q(1+log q) + q(1 + 8·10⁶·L^{3/4}ℓ²) ≤ 10⁷·q·(1+log q)·√q·L^{3/4}·ℓ⁴`
  set D : ℝ := (Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ) with hDdef
  set D2 : ℝ := (Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (2 : ℕ) with hD2def
  have hD2D : D2 ≤ D := by
    rw [hD2def, hDdef]
    exact mul_le_mul_of_nonneg_left hℓ2 (by linarith [hLp1])
  have hD1 : (1 : ℝ) ≤ D := hDbig
  have hA0 : (0 : ℝ) ≤ Real.sqrt q * (1 + Real.log q) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hstep : Real.sqrt q * (1 + Real.log q) + (q : ℝ) * (1 + 8000000 * D2)
      ≤ (Real.sqrt q * (1 + Real.log q) + (q : ℝ) + 8000000 * (q : ℝ)) * D := by
    have h1 : Real.sqrt q * (1 + Real.log q) ≤ Real.sqrt q * (1 + Real.log q) * D := by
      nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hD1)]
    have h2 : (q : ℝ) ≤ (q : ℝ) * D := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ)) (sub_nonneg.mpr hD1)]
    have h3 : 8000000 * (q : ℝ) * D2 ≤ 8000000 * (q : ℝ) * D :=
      mul_le_mul_of_nonneg_left hD2D (by linarith)
    linarith [h1, h2, h3]
  refine le_trans hstep ?_
  unfold vkProfile vkTwistConst
  have hR0 : (0 : ℝ) ≤ (q : ℝ) * (1 + Real.log q) * Real.sqrt q :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Real.sqrt_nonneg _)
  have hcoef : Real.sqrt q * (1 + Real.log q) + (q : ℝ) + 8000000 * (q : ℝ)
      ≤ 10000000 * (q : ℝ) * (1 + Real.log q) * Real.sqrt q := by
    have e1 : Real.sqrt q * (1 + Real.log q)
        ≤ (q : ℝ) * (1 + Real.log q) * Real.sqrt q := by
      nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hq1)]
    have e2 : (q : ℝ) ≤ (q : ℝ) * (1 + Real.log q) * Real.sqrt q := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ)) hlq)
        (Real.sqrt_nonneg ((q : ℝ))),
        mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ)) (sub_nonneg.mpr hsq1)]
    have e3 : 8000000 * (q : ℝ)
        ≤ 8000000 * ((q : ℝ) * (1 + Real.log q) * Real.sqrt q) := by linarith [e2]
    linarith [e1, e2, e3, hR0]
  have hDpos : (0 : ℝ) ≤ D := by linarith
  calc (Real.sqrt q * (1 + Real.log q) + (q : ℝ) + 8000000 * (q : ℝ)) * D
      ≤ (10000000 * (q : ℝ) * (1 + Real.log q) * Real.sqrt q) * D :=
        mul_le_mul_of_nonneg_right hcoef hDpos
    _ = 10000000 * (q : ℝ) * (1 + Real.log q) * Real.sqrt q
          * (Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ) := by
        rw [hDdef]; ring

/-- **THE VT-4 SOCKET, DISCHARGED.**  For every nonprincipal `ψ mod q`, every `X ≥ e` and
every `|t| ≥ exp(exp 100)`,

  `VkTwistUB (vkEulerCorr q * vkTwistConst q) ψ X t`.

The primitive core is `vk_LFunction_bridge_le_primitive` at the conductor; VT-5's
`vkTwistUB_of_primitive` carries it to `ψ` itself, and `vkProfile_mono` absorbs the
conductor's level into `q`. -/
theorem vkTwistUB_holds {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {X t : ℝ} (hX : Real.exp 1 ≤ X) (ht : Real.exp (Real.exp 100) ≤ |t|) :
    VkTwistUB (vkEulerCorr q * vkTwistConst q) ψ X t := by
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have hf1 : ψ.conductor ≠ 1 := fun h =>
    hψ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have hf2 : 2 ≤ ψ.conductor := by
    have := ψ.conductor_ne_zero
    omega
  have hfq : ψ.conductor ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
    ψ.conductor_dvd_level
  have hcore := vk_LFunction_bridge_le_primitive ψ.primitiveCharacter
    ψ.primitiveCharacter_isPrimitive hf2 hX ht
  refine vkTwistUB_of_primitive ψ hψ hX (le_trans hcore ?_)
  have hLt : (0 : ℝ) ≤ Real.log |t| :=
    le_trans (Real.exp_pos 100).le (vk_height_facts ht).1
  exact vkProfile_mono (by linarith [one_le_vkTwistConst (q := ψ.conductor)])
    (vkTwistConst_mono (by omega) hfq) hfq hLt

/-- **THE CAMPAIGN CAPSTONE — the D1 wall's death certificate.**  For every non-real `χ`
(`χ² ≠ 1`) and every `X` past an explicit symbolic threshold on `loglog X`, the twisted
datum `λ·χ̄` satisfies `CapFreeArm3.CapFreeFloor3`.

**No socket remains.**  VT-6's `capFreeFloor3_lamChi_vk` demanded `VkTwistUB` on the whole
contour box; `vkTwistUB_holds` supplies it, at `C = vkEulerCorr q · vkTwistConst q`.  The
only hypotheses left are `χ² ≠ 1`, the scale floor `X ≥ exp(exp 1)`, and the threshold —
whose every constant is named. -/
theorem capFreeFloor3_lamChi_unconditional :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ),
      χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X →
      32 * (Real.log (Real.log (Real.log X)) + (1 / 8) * Real.log q
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + K + 25)
        < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X := by
  obtain ⟨K, hK⟩ := capFreeFloor3_lamChi_vk
  refine ⟨K, ?_⟩
  intro q _ χ X hχ2 hX hthr
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
    have h1 := one_le_vkEulerCorr q
    have h2 := one_le_vkTwistConst (q := q)
    nlinarith [h1, h2]
  refine hK q χ (vkEulerCorr q * vkTwistConst q) X hC1 hχ2 hX (fun v _hv hbig => ?_) hthr
  have h2v : Real.exp (Real.exp 100) ≤ |2 * v| := by
    have : |v| ≤ |2 * v| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg v]
    linarith
  exact vkTwistUB_holds (χ ^ 2) hχ2 hXe h2v

end Salt.MR
