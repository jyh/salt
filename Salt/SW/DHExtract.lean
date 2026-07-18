/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.SelAlgebra
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The pole-cancelled extraction toolkit (`T-BAL` R2) — the kernel-Abel + power-sum stones

Design: the JYH-ratified **T-BAL S₀ synthesis freeze**
(`docs/exploration/tbal-s0-freeze.md`, the 5th design). The freeze's R2/R6 rung card MANDATES
the *kernel-Abel exact form* for the linear detector kernel `(1 − n/y)`: a bare `ζ(β₀)` or
`1/(1−s)` box "re-breaks the u^{−9} ledger". This module lands the two exact, weight-generic
stones the extraction rests on, with no analysis beyond finite summation-by-parts and the
mathlib monotone sum↔integral comparison:

* **`kernel_abel_sum`** — the exact discrete kernel-Abel identity
  `Σ_{1≤n≤y} a_n·(1 − n/y) = (1/y)·Σ_{1≤t≤y−1} A(t)`, `A(t) = Σ_{1≤n≤t} a_n`
  (summation by parts against the linear kernel; the `(2−β₀)` double-`∫` structure lives in the
  OUTER `Σ_t` here, so the inner sum never touches a positive-power EM).

* **`sum_rpow_le_integral`** — the exact power-sum cap
  `Σ_{1≤t≤y} t^a ≤ ((y+1)^{a+1} − 1)/(a+1)` for `a ≥ 0` (the outer `t^{1−β₀}` bound giving the
  `1/(2−β₀)` factor, via `MonotoneOn.sum_le_integral`).

The full extraction `unmoll_extraction_real` (R2) assembles these with the landed `zeta_partial_em`
(inner `β₀`-power sum, `1/2 ≤ β₀ < 1`) and `partial_sum_at_zero_small` (the `L(β₀,χ)=0`
pole-cancellation); see `docs/blueprints/flags.md` (T-BAL wave 2).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Finset

noncomputable section

namespace Salt.SW

/-! ## §1 — the exact discrete kernel-Abel identity -/

/-- **Abel identity (weighted).** `Σ_{1≤n≤y} n·a_n = y·A(y) − Σ_{1≤t≤y−1} A(t)` with
`A(t) = Σ_{1≤n≤t} a_n`. Pure summation by parts, by induction on `y ≥ 1`. -/
lemma sum_mul_index_eq (a : ℕ → ℝ) {y : ℕ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 1 y, (n : ℝ) * a n
      = (y : ℝ) * (∑ n ∈ Finset.Icc 1 y, a n)
        - ∑ t ∈ Finset.Icc 1 (y - 1), ∑ n ∈ Finset.Icc 1 t, a n := by
  induction y, hy using Nat.le_induction with
  | base => simp
  | succ y hy ih =>
    have hsucc : y + 1 - 1 = y := by omega
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ y + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ y + 1), hsucc]
    rw [ih]
    have hAsplit : ∑ t ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 t, a n
        = (∑ t ∈ Finset.Icc 1 (y - 1), ∑ n ∈ Finset.Icc 1 t, a n)
          + ∑ n ∈ Finset.Icc 1 y, a n := by
      rcases Nat.lt_or_ge 1 (y + 1) with hy1 | hy1
      · have : y = (y - 1) + 1 := by omega
        rw [this, Finset.sum_Icc_succ_top (by omega : 1 ≤ (y - 1) + 1)]
        congr 1
      · -- y = 0 impossible since hy : 1 ≤ y, but keep total
        omega
    rw [hAsplit]
    push_cast
    ring

/-- **The exact discrete kernel-Abel identity.** For `y ≥ 1`,
`Σ_{1≤n≤y} a_n·(1 − n/y) = (1/y)·Σ_{1≤t≤y−1} A(t)`, `A(t) = Σ_{1≤n≤t} a_n`.
Summation by parts against the linear kernel `(1 − n/y)`; the `n = y` term contributes `0`. -/
theorem kernel_abel_sum (a : ℕ → ℝ) {y : ℕ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 1 y, a n * (1 - (n : ℝ) / (y : ℝ))
      = (1 / (y : ℝ)) * ∑ t ∈ Finset.Icc 1 (y - 1), ∑ n ∈ Finset.Icc 1 t, a n := by
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hkey := sum_mul_index_eq a hy
  have hexpand : ∑ n ∈ Finset.Icc 1 y, a n * (1 - (n : ℝ) / (y : ℝ))
      = (∑ n ∈ Finset.Icc 1 y, a n) - (1 / (y : ℝ)) * ∑ n ∈ Finset.Icc 1 y, (n : ℝ) * a n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    field_simp
  rw [hexpand, hkey]
  field_simp
  ring

/-! ## §2 — the exact power-sum cap via the monotone sum↔integral comparison -/

/-- Reindex `Icc 1 y` to `range y` by `t = i + 1`. -/
lemma sum_Icc_one_shift (f : ℕ → ℝ) (y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y, f t = ∑ i ∈ Finset.range y, f (i + 1) := by
  induction y with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_range_succ, ih]

/-- **The outer power-sum cap.** For `r ≥ 0` and every `y`,
`Σ_{1≤t≤y} t^r ≤ ((y+1)^{r+1} − 1)/(r+1)`. The integrand `x ↦ x^r` is monotone on `[1, y+1]`,
so `Σ_{i<y} (1+i)^r ≤ ∫_1^{y+1} x^r dx` (`MonotoneOn.sum_le_integral`); the integral evaluates by
`integral_rpow` to `((y+1)^{r+1} − 1)/(r+1)`. Gives the `1/(2−β₀)` factor at `r = 1−β₀`. -/
theorem sum_rpow_le_integral {r : ℝ} (hr : 0 ≤ r) (y : ℕ) :
    ∑ t ∈ Finset.Icc 1 y, (t : ℝ) ^ r ≤ (((y : ℝ) + 1) ^ (r + 1) - 1) / (r + 1) := by
  have hmono : MonotoneOn (fun x : ℝ => x ^ r) (Set.Icc (1 : ℝ) (1 + (y : ℝ))) := by
    intro u hu v _ huv
    simp only [Set.mem_Icc] at hu
    exact Real.rpow_le_rpow (by linarith [hu.1]) huv hr
  have hle := hmono.sum_le_integral (x₀ := 1) (a := y)
  -- Reindex the LHS `Icc 1 y` to `range y` (`t = i + 1`).
  have hreindex : ∑ t ∈ Finset.Icc 1 y, (t : ℝ) ^ r
      = ∑ i ∈ Finset.range y, ((1 : ℝ) + (i : ℝ)) ^ r := by
    rw [sum_Icc_one_shift (fun t => (t : ℝ) ^ r) y]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast; ring_nf
  -- Evaluate the integral.
  have hint : (∫ x in (1 : ℝ)..(1 + (y : ℝ)), x ^ r)
      = (((y : ℝ) + 1) ^ (r + 1) - 1) / (r + 1) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < r))]
    rw [Real.one_rpow]
    congr 2
    ring
  rw [hreindex]
  calc ∑ i ∈ Finset.range y, ((1 : ℝ) + (i : ℝ)) ^ r
      ≤ ∫ x in (1 : ℝ)..(1 + (y : ℝ)), x ^ r := hle
    _ = (((y : ℝ) + 1) ^ (r + 1) - 1) / (r + 1) := hint

/-! ## §3 — the zero-killed stream (the `L(β₀,χ)=0` pole-cancellation, pointwise) -/

/-- **The zero-killed stream (real form).** For a real primitive `χ` and a REAL zero `β₀`
(`L(β₀,χ)=0`, `0<β₀≤1`), the `β₀`-twisted `χ_ℝ` partial sum is small:
`|Σ_{1≤d≤m} χ_ℝ(d)·d^{−β₀}| ≤ 6·√q(1+log q)·m^{−β₀}`. The real `chiRe`-sum is the real cast of the
complex `Σ χ(d)d^{−ρ}` at `ρ = β₀`, bounded by the landed `partial_sum_at_zero_small`
(`1+‖β₀‖/β₀ = 2`). The pointwise pole-cancellation the extraction rests on. -/
lemma chiRe_partial_at_zero_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hβ0 : 0 < β₀) (hβ1 : β₀ ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    |∑ d ∈ Finset.Icc 1 m, chiRe χ d * (d : ℝ) ^ (-β₀)|
      ≤ 6 * (Real.sqrt q * (1 + Real.log q)) * (m : ℝ) ^ (-β₀) := by
  have hcast : ((∑ d ∈ Finset.Icc 1 m, chiRe χ d * (d : ℝ) ^ (-β₀) : ℝ) : ℂ)
      = ∑ d ∈ Finset.Icc 1 m, χ (d : ZMod q) * (d : ℂ) ^ (-(β₀ : ℂ)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Complex.ofReal_mul, chiRe_ofReal χ hsq d,
      Complex.ofReal_cpow (show (0:ℝ) ≤ (d:ℝ) by positivity), Complex.ofReal_neg,
      Complex.ofReal_natCast]
  have hbound := partial_sum_at_zero_small χ hχ hq (ρ := (β₀ : ℂ)) hzero
    (by rw [Complex.ofReal_re]; exact hβ0) (by rw [Complex.ofReal_re]; exact hβ1) hm
  have hnorm : ‖((∑ d ∈ Finset.Icc 1 m, chiRe χ d * (d : ℝ) ^ (-β₀) : ℝ) : ℂ)‖
      = |∑ d ∈ Finset.Icc 1 m, chiRe χ d * (d : ℝ) ^ (-β₀)| :=
    (Complex.norm_real _).trans (Real.norm_eq_abs _)
  have heq : |∑ d ∈ Finset.Icc 1 m, chiRe χ d * (d : ℝ) ^ (-β₀)|
      = ‖∑ d ∈ Finset.Icc 1 m, χ (d : ZMod q) * (d : ℂ) ^ (-(β₀ : ℂ))‖ :=
    hnorm.symm.trans (congrArg (‖·‖) hcast)
  rw [heq]
  calc ‖∑ d ∈ Finset.Icc 1 m, χ (d : ZMod q) * (d : ℂ) ^ (-(β₀ : ℂ))‖
      ≤ 3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖(β₀ : ℂ)‖ / (β₀ : ℂ).re)
          * (m : ℝ) ^ (-(β₀ : ℂ).re) := hbound
    _ = 6 * (Real.sqrt q * (1 + Real.log q)) * (m : ℝ) ^ (-β₀) := by
        rw [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0,
          div_self hβ0.ne']; ring

end Salt.SW

end
