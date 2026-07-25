/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.VanDerCorput
import Salt.MR.HalaszIntegers

/-!
# The van der Corput socket, middle band — `hZ` discharged, L9 unconditional

`Salt/MR/VanDerCorput.lean` lands the honest-log socket

  `‖∑_{n=1}^N n^{iu}‖ ≤ Cvdc·(N/√(1+u²) + √(1+|u|)·(1+log(2+|u|)))`

on the two frequency **corners** `|u| ≤ 1` (`halasz_socket_small`) and `|u| ≥ N²`
(`halasz_socket_large`), both by the trivial bound.  This file closes the middle
band — in fact **all** of `|u| ≥ 1`, uniformly in `N` — and therefore supplies the
`hZ` hypothesis of `Salt.MR.halasz_integers_of_vanDerCorput` unconditionally.

## The route (Montgomery, *Ten Lectures*, p. 141 (33)–(34))

Two all-`t` block stones, then a single three-range assembly:

* `block_strip_all_t` — the **second-derivative** prefix block.  The proof of
  `Salt.Vk.zeta_block_strip` never uses its `t ≤ 27π·N` hypothesis before the final
  numeric collapse: the second-difference window `[μ, 4μ]` with `μ = A/(4U²)`,
  `A = t/2π`, is valid for *every* `t > 0` on *every* prefix `(U, X]` of a dyadic
  block (`X ≤ 2U`).  Stopping before the collapse leaves the honest all-`t` shape
  `‖∑_{U<n≤X} n^{−it}‖ ≤ 16√A + 16U/√A`.
* `range_kusmin_all` — the **Kušmin–Landau** range bound, generalising
  `Salt.ExpSum.zeta_block_kusmin` off the dyadic block: once `t ≤ M`, the whole
  range `(M, X]` (no dyadic subdivision!) has its consecutive phase differences in
  the single unit window `[−1+δ, −δ]` with `δ = t/(2π(X+1))`, so Kušmin–Landau
  gives `‖∑_{M<n≤X} n^{−it}‖ ≤ 2π(X+1)/t` in one shot.  This is what turns the
  `U ≥ t` regime into an `N/t`-grade term with **no** dyadic geometric series.
* `socket_head` — the dyadic induction on `N ≤ 2u+1`.  Splitting at `U = ⌈N/2⌉`
  (so `U < N ≤ 2U`) and feeding the block stone, the harmonic increment
  `log N − log U ≥ log(3/2) ≥ 1/3` absorbs the constant `100√u` per halving,
  landing `‖∑_{n≤N}‖ ≤ 320√u·(1+log N)`.  The `log` here **is** the source's
  `√t·log t` — the `≈ ½log₂ t` dyadic blocks of *Ten Lectures* (33).
* `socket_mid` / `socket_hZ` — the assembly: head up to `M = ⌈2u⌉₊`, Kušmin tail
  beyond, then the two corners and the `u ↦ −u` conjugation.  Absolute constant
  `640`.

## What lands

* `socket_hZ` — the honest-log socket for **all** `u : ℝ` and all `N`, `Cvdc = 640`.
* `halasz_integers_unconditional` — `halasz_integers_of_vanDerCorput` with `hZ`
  supplied: L9 (Halász for integers) with **no** analytic hypothesis.
-/

noncomputable section

open Finset
open scoped Real

namespace Salt.MR

open Salt.ExpSum (eR eK phi)

/-! ### STONE 0 — small bridges -/

/-- `Icc 1 k = Ioc 0 k` in `ℕ`: lets the head sums feed `Finset.sum_Ioc_consecutive`. -/
lemma vdc_Icc_one_eq_Ioc_zero (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- The socket sum in the `eK` character (the one the van der Corput engine speaks). -/
lemma norm_socketSum_eq_eK (u : ℝ) (S : Finset ℕ) :
    ‖∑ n ∈ S, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      = ‖∑ n ∈ S, eK (phi u (n : ℤ))‖ := by
  rw [norm_socketSum_eq_eR u S]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => Salt.ExpSum.eR_eq_eK _)

/-- The socket sum is `u ↦ −u` symmetric in norm (conjugation). -/
lemma vdc_norm_socketSum_neg (u : ℝ) (S : Finset ℕ) :
    ‖∑ n ∈ S, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      = ‖∑ n ∈ S, Complex.exp (Complex.I * ((-u : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖ := by
  have h : ∀ n : ℕ,
      Complex.exp (Complex.I * ((-u : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))
        = (starRingEnd ℂ) (Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))) := by
    intro n
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun n (_ : n ∈ S) => h n), ← map_sum, Complex.norm_conj]

/-! ### STONE 1 — the all-`t` second-derivative prefix block -/

/-- **V1 — the all-`t` second-derivative prefix block.**  For every `t > 0` and every
prefix `(U, X]` of a dyadic block (`1 ≤ U < X ≤ 2U`),
`‖∑_{U<n≤X} eR(phi t n)‖ ≤ 16√A + 16U/√A` with `A = t/2π`.  This is
`Salt.Vk.zeta_block_strip`'s proof stopped **before** its final collapse: the
second-difference window `μ ≤ d² ≤ 4μ` with `μ = A/(4U²)` never sees the strip
restriction `t ≤ 27πU`. -/
theorem block_strip_all_t (t : ℝ) (ht : 0 < t) (U X : ℕ) (hU1 : 1 ≤ U)
    (hUX : U < X) (hX2U : X ≤ 2 * U) :
    ‖∑ n ∈ Finset.Ioc U X, eK (phi t (n : ℤ))‖
      ≤ 16 * Real.sqrt (t / (2 * Real.pi))
          + 16 * (U : ℝ) / Real.sqrt (t / (2 * Real.pi)) := by
  have hURpos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU1
  set A : ℝ := t / (2 * Real.pi) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set μ : ℝ := A / (4 * (U : ℝ) ^ 2) with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  -- the second-difference identity for the ζ-phase (ℕ-indexed)
  have hd2 : ∀ n : ℕ,
      (phi t ((n + 1 + 1 : ℕ) : ℤ) - phi t ((n + 1 : ℕ) : ℤ))
          - (phi t ((n + 1 : ℕ) : ℤ) - phi t ((n : ℕ) : ℤ))
        = A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
    intro n
    simp only [Salt.ExpSum.phi, ← hA]
    push_cast
    ring_nf
  have hlb : ∀ n : ℕ, U < n → n < X →
      μ ≤ (phi t ((n + 1 + 1 : ℕ) : ℤ) - phi t ((n + 1 : ℕ) : ℤ))
            - (phi t ((n + 1 : ℕ) : ℤ) - phi t ((n : ℕ) : ℤ)) := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (U : ℝ) + 1 ≤ (n : ℝ) := by
      have : U + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hll := Salt.Vk.log_2diff_lower hmpos
    have hnu : (n : ℝ) + 1 ≤ 2 * (U : ℝ) := by
      have : n + 1 ≤ 2 * U := by omega
      exact_mod_cast this
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ 4 * (U : ℝ) ^ 2 := by nlinarith [hnu, hURpos]
    have hstep1 : μ ≤ A / ((n : ℝ) + 1) ^ 2 := by
      rw [hμ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hsq, hA0.le]
    have heq2 : A / ((n : ℝ) + 1) ^ 2 = A * (1 / ((n : ℝ) + 1) ^ 2) := by ring
    have hstep2 : A / ((n : ℝ) + 1) ^ 2
        ≤ A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hll hA0.le
    linarith [hstep1, hstep2]
  have hub : ∀ n : ℕ, U < n → n < X →
      (phi t ((n + 1 + 1 : ℕ) : ℤ) - phi t ((n + 1 : ℕ) : ℤ))
          - (phi t ((n + 1 : ℕ) : ℤ) - phi t ((n : ℕ) : ℤ)) ≤ 4 * μ := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (U : ℝ) + 1 ≤ (n : ℝ) := by
      have : U + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlu := Salt.Vk.log_2diff_upper hmpos
    have hUsq : (U : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 2) := by nlinarith [hnR1, hURpos]
    have heq2 : A / ((n : ℝ) * ((n : ℝ) + 2)) = A * (1 / ((n : ℝ) * ((n : ℝ) + 2))) := by ring
    have hstep1 : A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ))
        ≤ A / ((n : ℝ) * ((n : ℝ) + 2)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hlu hA0.le
    have h4μ : 4 * μ = A / (U : ℝ) ^ 2 := by rw [hμ]; ring
    have hstep2 : A / ((n : ℝ) * ((n : ℝ) + 2)) ≤ 4 * μ := by
      rw [h4μ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hUsq, hA0.le]
    linarith [hstep1, hstep2]
  have hkey := Salt.ExpSum.vdC_second_derivative (f := fun j : ℕ => phi t (j : ℤ))
    (a := U) (b := X) (lam := μ) (c := 4) (le_of_lt hUX) hμ0 (by norm_num) hlb hub
  refine le_trans hkey ?_
  -- 8(4(X−U)√μ + 1/√μ) ≤ 16√A + 16U/√A
  have hsm : Real.sqrt μ = Real.sqrt A / (2 * (U : ℝ)) := by
    rw [hμ, show A / (4 * (U : ℝ) ^ 2) = A * (1 / (2 * (U : ℝ))) ^ 2 from by field_simp; ring,
      Real.sqrt_mul hA0.le, Real.sqrt_sq (by positivity)]
    ring
  have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hXU : (X : ℝ) - (U : ℝ) ≤ (U : ℝ) := by
    have : (X : ℝ) ≤ 2 * (U : ℝ) := by exact_mod_cast hX2U
    linarith
  have hterm1 : 4 * ((X : ℝ) - (U : ℝ)) * Real.sqrt μ ≤ 2 * Real.sqrt A := by
    have he : 4 * ((X : ℝ) - (U : ℝ)) * (Real.sqrt A / (2 * (U : ℝ)))
        = 2 * ((X : ℝ) - (U : ℝ)) * Real.sqrt A / (U : ℝ) := by
      field_simp; ring
    rw [hsm, he, div_le_iff₀ hURpos]
    nlinarith [mul_le_mul_of_nonneg_right hXU hsApos.le]
  have hterm2 : 1 / Real.sqrt μ = 2 * (U : ℝ) / Real.sqrt A := by
    rw [hsm, one_div, inv_div]
  rw [hterm2]
  have hfrac : 8 * (2 * (U : ℝ) / Real.sqrt A) = 16 * (U : ℝ) / Real.sqrt A := by
    field_simp; ring
  linarith [hterm1, hfrac]

/-! ### STONE 2 — the all-range Kušmin–Landau bound -/

/-- **V1′ — the Kušmin–Landau range bound (no dyadic subdivision).**  Once `t ≤ M`,
the *whole* range `(M, X]` has consecutive ζ-phase differences inside the single unit
window `[−1+δ, −δ]` with `δ = t/(2π(X+1))`, so Kušmin–Landau gives
`‖∑_{M<n≤X} eR(phi t n)‖ ≤ 2π(X+1)/t` in one application.  This generalises
`Salt.ExpSum.zeta_block_kusmin` (`X = 2M`) off the dyadic block. -/
theorem range_kusmin_all (t : ℝ) (ht : 0 < t) (M X : ℕ) (hM1 : 1 ≤ M)
    (htM : t ≤ (M : ℝ)) (hMX : M ≤ X) :
    ‖∑ n ∈ Finset.Ioc M X, eK (phi t (n : ℤ))‖
      ≤ 2 * Real.pi * ((X : ℝ) + 1) / t := by
  set f : ℕ → ℝ := fun j => phi t (j : ℤ) with hf
  set δ : ℝ := t / (2 * Real.pi * ((X : ℝ) + 1)) with hδ
  have hXR : (M : ℝ) ≤ (X : ℝ) := by exact_mod_cast hMX
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hfval : ∀ j : ℕ, f j = -(t / (2 * Real.pi)) * Real.log (j : ℝ) := by
    intro j; simp only [hf, Salt.ExpSum.phi, Int.cast_natCast]
  have hgval : ∀ m : ℕ, f (m + 1) - f m
      = -(t / (2 * Real.pi)) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by
    intro m; rw [hfval (m + 1), hfval m]; push_cast; ring
  have hApos : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hpi1 : (1 : ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
  have hδ2π : δ ≤ 1 / (2 * Real.pi) := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by positivity)]
    have htX1 : t ≤ (X : ℝ) + 1 := by linarith
    nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr htX1)]
  have hδ12 : δ ≤ 1 / 2 := by
    have h : 1 / (2 * Real.pi) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hpi1]
    linarith [hδ2π]
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos ht (by positivity)
  have hg_ub : ∀ n : ℕ, M < n → n ≤ X → f (n + 1) - f n ≤ ((-1 : ℤ) : ℝ) + 1 - δ := by
    intro n hlt hle
    have hn1 : 1 ≤ n := by omega
    have hLlb := Salt.ExpSum.log_succ_sub_ge n hn1
    have hn1X : (n : ℝ) + 1 ≤ (X : ℝ) + 1 := by
      have : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hle
      linarith
    have hstep1 : t / (2 * Real.pi) * (1 / ((n : ℝ) + 1))
        ≤ t / (2 * Real.pi) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLlb (le_of_lt hApos)
    have hstep2 : δ ≤ t / (2 * Real.pi) * (1 / ((n : ℝ) + 1)) := by
      rw [mul_one_div, hδ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hn1X
        (mul_nonneg (le_of_lt ht) (le_of_lt (show (0 : ℝ) < 2 * Real.pi by positivity)))]
    have hcomb : δ ≤ t / (2 * Real.pi) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      le_trans hstep2 hstep1
    rw [hgval n, neg_mul]; push_cast; linarith [hcomb]
  have hg_lb : ∀ n : ℕ, M < n → n ≤ X → ((-1 : ℤ) : ℝ) + δ ≤ f (n + 1) - f n := by
    intro n hlt hle
    have hn1 : 1 ≤ n := by omega
    have hLub := Salt.ExpSum.log_succ_sub_le n hn1
    have htn : t ≤ (n : ℝ) := by
      have : (M : ℝ) < (n : ℝ) := by exact_mod_cast hlt
      linarith
    have hstep1 : t / (2 * Real.pi) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ t / (2 * Real.pi) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLub (le_of_lt hApos)
    have hbound : t / (2 * Real.pi) * (1 / (n : ℝ)) ≤ 1 - δ := by
      rw [mul_one_div, div_div]
      have h1 : t / (2 * Real.pi * (n : ℝ)) ≤ 1 / (2 * Real.pi) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr htn)]
      have h3 : 1 / (2 * Real.pi) + 1 / (2 * Real.pi) ≤ 1 := by
        rw [← add_div, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
      linarith [h1, hδ2π, h3]
    have hcomb : t / (2 * Real.pi) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 - δ :=
      le_trans hstep1 hbound
    rw [hgval n, neg_mul]; push_cast; linarith [hcomb]
  have hmono : ∀ n : ℕ, M < n → n < X → f (n + 1) - f n ≤ f (n + 1 + 1) - f (n + 1) := by
    intro n hlt hlt2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hratio : ((n : ℝ) + 2) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / (n : ℝ) := by
      rw [div_le_div_iff₀ hn1 hn0]; nlinarith
    have hlogle :=
      Real.log_le_log (show (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1) by positivity) hratio
    rw [Real.log_div (by positivity) (ne_of_gt hn1),
      Real.log_div (ne_of_gt hn1) (ne_of_gt hn0)] at hlogle
    have he2 : f (n + 1 + 1) - f (n + 1)
        = -(t / (2 * Real.pi)) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
      rw [hfval (n + 1 + 1), hfval (n + 1)]; push_cast; ring_nf
    rw [hgval n, he2, neg_mul, neg_mul]
    linarith [mul_le_mul_of_nonneg_left hlogle (le_of_lt hApos)]
  have hkl := Salt.ExpSum.kusmin_landau (f := f) (a := M) (b := X) (δ := δ) (m := -1)
    hδ0 hδ12 hg_lb hg_ub hmono
  refine le_trans hkl (le_of_eq ?_)
  rw [hδ, one_div_div]

/-! ### STONE 3 — the two block stones in socket form -/

/-- `2π ≤ 441/64`, the constant behind `16√(2π) ≤ 42`. -/
lemma two_pi_le_441_div_64 : 2 * Real.pi ≤ 441 / 64 := by
  linarith [Real.pi_lt_d6]

/-- **The second-derivative prefix block, socket form.**  `‖∑_{U<n≤X} n^{iu}‖ ≤
16√u + 42U/√u` for `u ≥ 1` and `1 ≤ U < X ≤ 2U`. -/
theorem socket_block_strip (u : ℝ) (hu : 1 ≤ u) (U X : ℕ) (hU1 : 1 ≤ U)
    (hUX : U < X) (hX2U : X ≤ 2 * U) :
    ‖∑ n ∈ Finset.Ioc U X, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 16 * Real.sqrt u + 42 * (U : ℝ) / Real.sqrt u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hURnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  rw [norm_socketSum_eq_eK]
  refine le_trans (block_strip_all_t u hu0 U X hU1 hUX hX2U) ?_
  set A : ℝ := u / (2 * Real.pi) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hsupos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  -- `√A ≤ √u`
  have h1 : Real.sqrt A ≤ Real.sqrt u := by
    apply Real.sqrt_le_sqrt
    rw [hA]
    exact div_le_self hu0.le (by nlinarith [Real.pi_gt_three])
  -- `√u ≤ (21/8)·√A`
  have h2 : Real.sqrt u ≤ 21 / 8 * Real.sqrt A := by
    have he : (21 : ℝ) / 8 * Real.sqrt A = Real.sqrt (441 / 64 * A) := by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt (441 / 64 : ℝ) = 21 / 8 from by
        rw [show (441 / 64 : ℝ) = (21 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [he]
    apply Real.sqrt_le_sqrt
    rw [hA, mul_div_assoc', le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [two_pi_le_441_div_64, hu0]
  have h3 : 16 * (U : ℝ) / Real.sqrt A ≤ 42 * (U : ℝ) / Real.sqrt u := by
    rw [div_le_div_iff₀ hsApos hsupos]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 16 * (U : ℝ))]
  linarith [h1, h3]

/-- **The Kušmin–Landau range bound, socket form.**  `‖∑_{M<n≤X} n^{iu}‖ ≤ 7(X+1)/u`
whenever `u ≤ M`. -/
theorem socket_range_kusmin (u : ℝ) (hu : 1 ≤ u) (M X : ℕ) (hM1 : 1 ≤ M)
    (huM : u ≤ (M : ℝ)) (hMX : M ≤ X) :
    ‖∑ n ∈ Finset.Ioc M X, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 7 * ((X : ℝ) + 1) / u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  rw [norm_socketSum_eq_eK]
  refine le_trans (range_kusmin_all u hu0 M X hM1 huM hMX) ?_
  rw [div_le_div_iff₀ hu0 hu0]
  have h2pi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d6]
  have hpos : (0 : ℝ) ≤ ((X : ℝ) + 1) * u := by positivity
  linarith [mul_le_mul_of_nonneg_right h2pi hpos]

/-! ### STONE 4 — the dyadic head induction -/

/-- `log(3/2) ≥ 1/3`: the harmonic increment bought by one halving. -/
lemma one_third_le_log_three_halves : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
  have h4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
  have h5 : Real.log ((2 : ℝ) / 3) = -Real.log (3 / 2) := by
    rw [show (2 : ℝ) / 3 = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
  rw [h5] at h4
  linarith

/-- **V2a — the dyadic head induction.**  For `u ≥ 1` and `N ≤ 2u+1`,
`‖∑_{n≤N} n^{iu}‖ ≤ 320√u·(1+log N)`.  Splitting at `U = ⌈N/2⌉` gives a prefix
block `(U, N]` with `U < N ≤ 2U`, on which `socket_block_strip` costs `100√u`
(using `U ≤ 2u`); the harmonic increment `log N − log U ≥ log(3/2) ≥ 1/3` pays for
it out of `320√u`.  This `log` is exactly *Ten Lectures* (33)'s `≈ ½log₂ t` blocks. -/
theorem socket_head (u : ℝ) (hu : 1 ≤ u) :
    ∀ N : ℕ, (N : ℝ) ≤ 2 * u + 1 →
      ‖∑ n ∈ Finset.Icc 1 N,
          Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
        ≤ 320 * Real.sqrt u * (1 + Real.log (N : ℝ)) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hsu1 : (1 : ℝ) ≤ Real.sqrt u := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hu
  have hsupos : (0 : ℝ) < Real.sqrt u := by linarith
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rcases Nat.lt_or_ge N 2 with hN2 | hN2
    · have hcase : N = 0 ∨ N = 1 := by omega
      rcases hcase with rfl | rfl
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        simp only [Nat.cast_zero, Real.log_zero, add_zero]
        positivity
      · refine le_trans (norm_socketSum_le_card u 1) ?_
        simp only [Nat.cast_one, Real.log_one, add_zero, mul_one]
        linarith
    · set U : ℕ := (N + 1) / 2 with hUdef
      have hU1 : 1 ≤ U := by omega
      have hUN : U < N := by omega
      have hN2U : N ≤ 2 * U := by omega
      have h3U : 3 * U ≤ 2 * N := by omega
      have h2U : 2 * U ≤ N + 1 := by omega
      have hUpos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU1
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have hNz : 0 < N := by omega
        exact_mod_cast hNz
      have hsplit : ∑ n ∈ Finset.Icc 1 N,
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))
          = (∑ n ∈ Finset.Icc 1 U,
              Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ)))
            + ∑ n ∈ Finset.Ioc U N,
              Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
        rw [vdc_Icc_one_eq_Ioc_zero N, vdc_Icc_one_eq_Ioc_zero U]
        exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le U) (le_of_lt hUN)).symm
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hhead := ih U hUN (by
        have hUR : (U : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_of_lt hUN
        linarith)
      have hblk := socket_block_strip u hu U N hU1 hUN hN2U
      have hUu : (U : ℝ) ≤ 2 * u := by
        have h : (2 : ℝ) * (U : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast h2U
        linarith
      have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
      have hdiv : 42 * (U : ℝ) / Real.sqrt u ≤ 84 * Real.sqrt u := by
        rw [div_le_iff₀ hsupos]
        nlinarith [hUu, hss]
      have hratio : (3 : ℝ) / 2 ≤ (N : ℝ) / (U : ℝ) := by
        rw [le_div_iff₀ hUpos]
        have h : (3 : ℝ) * (U : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h3U
        linarith
      have hlogd : (1 : ℝ) / 3 ≤ Real.log (N : ℝ) - Real.log (U : ℝ) := by
        have hA1 : Real.log ((3 : ℝ) / 2) ≤ Real.log ((N : ℝ) / (U : ℝ)) :=
          Real.log_le_log (by norm_num) hratio
        have hA2 : Real.log ((N : ℝ) / (U : ℝ)) = Real.log (N : ℝ) - Real.log (U : ℝ) :=
          Real.log_div (ne_of_gt hNpos) (ne_of_gt hUpos)
        linarith [one_third_le_log_three_halves]
      have hkey : 100 * Real.sqrt u
          ≤ 320 * Real.sqrt u * Real.log (N : ℝ) - 320 * Real.sqrt u * Real.log (U : ℝ) := by
        have hA1 : (0 : ℝ)
            ≤ Real.sqrt u * (320 * (Real.log (N : ℝ) - Real.log (U : ℝ)) - 100) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hA1]
      linarith [hhead, hblk, hdiv, hkey]

/-- The head grade `320√u·(1+log K)` sits inside the socket's tail term whenever
`K ≤ 2u+1` (there `log K ≤ 2·log(2+u)`, since `2u+1 ≤ (2+u)²`). -/
lemma head_le_target (u : ℝ) (hu : 1 ≤ u) (K : ℕ) (hK : (K : ℝ) ≤ 2 * u + 1) :
    320 * Real.sqrt u * (1 + Real.log (K : ℝ))
      ≤ 640 * (Real.sqrt (1 + u) * (1 + Real.log (2 + u))) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlognn : (0 : ℝ) ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  have hlogK : Real.log (K : ℝ) ≤ 2 * Real.log (2 + u) := by
    rcases Nat.eq_zero_or_pos K with rfl | hKpos
    · simp only [Nat.cast_zero, Real.log_zero]; linarith
    · have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
      have hle : (K : ℝ) ≤ (2 + u) ^ 2 := by nlinarith [hK, hu0, sq_nonneg u]
      have h := Real.log_le_log hKR hle
      rw [Real.log_pow] at h
      push_cast at h
      exact h
  have h1 : 1 + Real.log (K : ℝ) ≤ 2 * (1 + Real.log (2 + u)) := by linarith
  have hsq : Real.sqrt u ≤ Real.sqrt (1 + u) := Real.sqrt_le_sqrt (by linarith)
  calc 320 * Real.sqrt u * (1 + Real.log (K : ℝ))
      ≤ 320 * Real.sqrt u * (2 * (1 + Real.log (2 + u))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 640 * (Real.sqrt u * (1 + Real.log (2 + u))) := by ring
    _ ≤ 640 * (Real.sqrt (1 + u) * (1 + Real.log (2 + u))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 640)
        exact mul_le_mul_of_nonneg_right hsq (by linarith)

/-! ### STONE 5 — the middle band and the socket -/

/-- **V2b — the middle band, all `N`.**  For `u ≥ 1` the honest-log socket holds
unconditionally with the absolute constant `640`: head up to `M = ⌈2u⌉₊`
(`socket_head` + `head_le_target`), Kušmin–Landau on `(M, N]` in one shot
(`socket_range_kusmin`), and `√(1+u²) ≤ 2u` to convert `N/u` into `N/√(1+u²)`. -/
theorem socket_mid (u : ℝ) (hu : 1 ≤ u) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 640 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + u) * (1 + Real.log (2 + u))) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hsp : (0 : ℝ) < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hheadnn : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (1 + u ^ 2) := by positivity
  set M : ℕ := ⌈2 * u⌉₊ with hMdef
  have hMge : 2 * u ≤ (M : ℝ) := Nat.le_ceil _
  have hMlt : (M : ℝ) < 2 * u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · rw [h0] at hMge; norm_num at hMge; linarith
    · omega
  have huM : u ≤ (M : ℝ) := by linarith
  rcases le_or_gt N M with hNM | hNM
  · have hNle : (N : ℝ) ≤ 2 * u + 1 := by
      have hNR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
      linarith
    refine le_trans (socket_head u hu N hNle) ?_
    refine le_trans (head_le_target u hu N hNle) ?_
    linarith [hheadnn]
  · have hMN : M ≤ N := le_of_lt hNM
    have hN1 : 1 ≤ N := by omega
    have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hsplit : ∑ n ∈ Finset.Icc 1 N,
          Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))
        = (∑ n ∈ Finset.Icc 1 M,
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ)))
          + ∑ n ∈ Finset.Ioc M N,
            Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
      rw [vdc_Icc_one_eq_Ioc_zero N, vdc_Icc_one_eq_Ioc_zero M]
      exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN).symm
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hMle : (M : ℝ) ≤ 2 * u + 1 := le_of_lt hMlt
    have hhead := le_trans (socket_head u hu M hMle) (head_le_target u hu M hMle)
    have htail := socket_range_kusmin u hu M N hM1 huM hMN
    have hb : Real.sqrt (1 + u ^ 2) ≤ 2 * u := by
      rw [show (2 : ℝ) * u = Real.sqrt ((2 * u) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have htail2 : 7 * ((N : ℝ) + 1) / u ≤ 640 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hu0 hsp]
      have h1 : 7 * ((N : ℝ) + 1) * Real.sqrt (1 + u ^ 2) ≤ 7 * ((N : ℝ) + 1) * (2 * u) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      have h2 : 7 * ((N : ℝ) + 1) * (2 * u) ≤ 640 * (N : ℝ) * u := by
        have h3 : (0 : ℝ) ≤ u * (626 * (N : ℝ) - 14) := mul_nonneg hu0.le (by linarith)
        linarith [h3]
      linarith [h1, h2]
    linarith [hhead, htail, htail2]

/-- **V3 — the `hZ` socket, discharged for every frequency.**  The honest-log socket
`‖∑_{n≤N} n^{iu}‖ ≤ 640·(N/√(1+u²) + √(1+|u|)·(1+log(2+|u|)))` holds for **all**
`u : ℝ` and all `N`: `|u| ≤ 1` by `halasz_socket_small`, `u ≥ 1` by `socket_mid`,
`u ≤ −1` by conjugation (`vdc_norm_socketSum_neg`). -/
theorem socket_hZ (N : ℕ) (u : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N,
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 640 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|))) := by
  have hbr : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (1 + u ^ 2)
      + Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (1 + u ^ 2) := by positivity
    have h2 : (0 : ℝ) ≤ 1 + Real.log (2 + |u|) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 + |u| by linarith [abs_nonneg u])
      linarith
    have h3 : (0 : ℝ) ≤ Real.sqrt (1 + |u|) * (1 + Real.log (2 + |u|)) :=
      mul_nonneg (Real.sqrt_nonneg _) h2
    linarith
  rcases le_or_gt |u| 1 with h1 | h1
  · refine le_trans (halasz_socket_small N u h1) ?_
    have h2 : Real.sqrt 2 ≤ 640 := by
      rw [show (640 : ℝ) = Real.sqrt (640 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact mul_le_mul_of_nonneg_right h2 hbr
  · rcases le_or_gt 0 u with hpos | hneg
    · have habs : |u| = u := abs_of_nonneg hpos
      have hu : 1 ≤ u := by rw [habs] at h1; linarith
      rw [habs]
      exact socket_mid u hu N
    · have habs : |u| = -u := abs_of_neg hneg
      have hu : 1 ≤ -u := by rw [habs] at h1; linarith
      have key := socket_mid (-u) hu N
      rw [show ((-u : ℝ)) ^ 2 = u ^ 2 from by ring] at key
      rw [vdc_norm_socketSum_neg u, habs]
      exact key

/-! ### THE CAPSTONE — L9 unconditional -/

/-- **L9 (Halász for integers), UNCONDITIONAL.**  `halasz_integers_of_vanDerCorput`
with its sole analytic hypothesis `hZ` supplied by `socket_hZ` (`Cvdc = 640`):
`Σ_{t∈𝒯} ‖A(it)‖² ≤ 4·641·(N + |𝒯|√T)·(1 + log 2T)·Σ‖aₙ‖²` for well-spaced
`𝒯 ⊆ [−T,T]`, `T ≥ 1`. -/
theorem halasz_integers_unconditional (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ 4 * (640 + 1) * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
  halasz_integers_of_vanDerCorput N a T hT 𝒯 hws hsub 640 (by norm_num) (socket_hZ N)

/-- The capstone with the absolute constant collapsed: `4·(640+1) = 2564`. -/
theorem halasz_integers_unconditional_const (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ 2564 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := halasz_integers_unconditional N a T hT 𝒯 hws hsub
  have e : (4 : ℝ) * (640 + 1) = 2564 := by norm_num
  rwa [e] at h

end Salt.MR
