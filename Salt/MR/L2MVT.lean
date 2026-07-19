/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.AnalyticLS

/-!
# MR-gate campaign, wave 1, node S6a (MR-A): the Dirichlet-polynomial L² mean value

Blueprint / freeze: `docs/exploration/mr-freeze.md` (S6a `dirichlet_poly_l2_mvt`).

The classical mean-value theorem for Dirichlet polynomials asks for a constant `C`
with, for `F(t) = ∑_{1≤n≤N} aₙ · nⁱᵗ = ∑_{1≤n≤N} aₙ · exp(i·t·log n)`,

  `∫_{-T}^{T} ‖F(t)‖² dt ≤ C·(T + N)·∑ ‖aₙ‖²`.

**Status: PARTIAL.** This file lands the honest *reduction*: the exact expansion of
the L² integral into its diagonal and off-diagonal pieces (`dirichlet_poly_l2_expand`,
`dirichlet_poly_l2_diagonal`). The diagonal is exactly `2T·∑‖aₙ‖²`. The remaining
`(T+N)` closing requires bounding the off-diagonal
`∑_{m≠n} conj(aₙ)·aₘ · ∫_{-T}^T exp(i·t·(log m − log n)) dt` by `C·N·∑‖aₙ‖²`.

That off-diagonal bound is the Montgomery–Vaughan generalized Hilbert inequality
(`|∑_{m≠n} bₘ conj(bₙ)/(λₘ−λₙ)| ≤ (3/2)π ∑ ‖bₙ‖²/δₙ` with `δₙ` the local spacing of
`λₙ = log n`, so `δₙ ≈ 1/n` gives `∑‖aₙ‖²·n ≤ N·∑‖aₙ‖²`). The naive triangle bound
`|∑| ≤ ∑ |bₘ||bₙ|/|λₘ−λₙ|` loses a `log N` factor (its Schur norm is `≍ N log N`), so
the sharp shape genuinely needs bilinear cancellation. mathlib has **no** Hilbert /
Montgomery–Vaughan inequality, and the frozen suppliers
(`Salt.LS.gallagher_pointwise`, `Salt.LS.analytic_LS`) cannot supply it: `analytic_LS`
is the discrete large sieve for *integer* frequencies at well-spaced points, whereas
this is a *continuous* integral over *log-spaced* frequencies. See the executor report
for the precise flag.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral Complex

/-- The Dirichlet polynomial `F(t) = ∑_{1 ≤ n ≤ N} aₙ · exp(i·t·log n)`. Since
`n^{it} = exp(i·t·log n)` for `n ≥ 1`, indexing from `1` avoids `0^{it}`. -/
noncomputable def dpoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (Complex.I * (t : ℂ) * Real.log n)

/-- `dpoly N a` is continuous (a finite sum of continuous terms). -/
lemma continuous_dpoly (N : ℕ) (a : ℕ → ℂ) : Continuous (dpoly N a) := by
  unfold dpoly
  apply continuous_finsetSum
  intro n _
  fun_prop

/-- **Pointwise expansion.** `‖F(t)‖²`, as a complex number, is the double sum
`∑ₙ ∑ₘ conj(aₙ)·aₘ · exp(i·t·(log m − log n))`. -/
lemma sq_norm_dpoly_eq (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ((‖dpoly N a t‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (starRingEnd ℂ) (a n) * a m
            * Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
  have hcm : ((‖dpoly N a t‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (dpoly N a t) * dpoly N a t := by
    rw [Complex.sq_norm]; exact Complex.normSq_eq_conj_mul_self
  rw [hcm]
  have hconj : (starRingEnd ℂ) (dpoly N a t)
      = ∑ n ∈ Finset.Icc 1 N,
          (starRingEnd ℂ) (a n)
            * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
    unfold dpoly
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj]
  unfold dpoly
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  have hexp :
      Complex.exp (Complex.I * (t : ℂ) * (Real.log m : ℂ))
          * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))
        = Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [show (starRingEnd ℂ) (a n)
          * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))
          * (a m * Complex.exp (Complex.I * (t : ℂ) * (Real.log m : ℂ)))
        = (starRingEnd ℂ) (a n) * a m
            * (Complex.exp (Complex.I * (t : ℂ) * (Real.log m : ℂ))
                * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) from by ring,
      hexp]

/-- **S6a expansion (landed).** The L² mean-value integral of the Dirichlet
polynomial expands as the diagonal + off-diagonal double sum. This is the honest
reduction: all that remains for the `(T+N)` mean-value bound is an off-diagonal
estimate (the Montgomery–Vaughan / Hilbert inequality). -/
theorem dirichlet_poly_l2_expand (N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    ((∫ t in (-T)..T, ‖dpoly N a t‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (starRingEnd ℂ) (a n) * a m
            * ∫ t in (-T)..T,
                Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
  have hInt1 : ∀ n m : ℕ, IntervalIntegrable
      (fun t => (starRingEnd ℂ) (a n) * a m
        * Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
      volume (-T) T := by
    intro n m; apply Continuous.intervalIntegrable; fun_prop
  have hInt2 : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun t => ∑ m ∈ Finset.Icc 1 N, (starRingEnd ℂ) (a n) * a m
        * Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
      volume (-T) T := by
    intro n _; apply Continuous.intervalIntegrable
    apply continuous_finsetSum; intro m _; fun_prop
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [sq_norm_dpoly_eq N a]
  rw [intervalIntegral.integral_finsetSum hInt2]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun m _ => hInt1 n m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul]

/-- **S6a diagonal split (landed).** The L² integral equals its diagonal
`2T·∑‖aₙ‖²` plus the off-diagonal remainder. This makes the exact gap to the
`(T+N)` mean-value bound explicit: it is the Montgomery–Vaughan / Hilbert
estimate `‖∑_{m≠n} conj(aₙ)·aₘ·Jₘₙ‖ ≤ C·N·∑‖aₙ‖²`, where `Jₘₙ = 2 sin(Tθ)/θ`
with `θ = log m − log n`, so `‖Jₘₙ‖ ≤ 2/|log(m/n)|`. -/
theorem dirichlet_poly_l2_diagonal (N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    ((∫ t in (-T)..T, ‖dpoly N a t‖ ^ 2 : ℝ) : ℂ)
      = ((2 * T : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, ((‖a n‖ ^ 2 : ℝ) : ℂ)
        + ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).erase n,
            (starRingEnd ℂ) (a n) * a m
              * ∫ t in (-T)..T,
                  Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
  rw [dirichlet_poly_l2_expand]
  have hdiag : ∀ n : ℕ, (∫ t in (-T)..T,
      Complex.exp (Complex.I * (t : ℂ) * ((Real.log n : ℂ) - (Real.log n : ℂ))))
      = ((2 * T : ℝ) : ℂ) := by
    intro n
    simp only [sub_self, mul_zero, Complex.exp_zero]
    rw [intervalIntegral.integral_const, Complex.real_smul, mul_one]
    push_cast; ring
  have hconjsq : ∀ n : ℕ, (starRingEnd ℂ) (a n) * a n = ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
    intro n; rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  have hsplit : ∀ n ∈ Finset.Icc 1 N,
      (∑ m ∈ Finset.Icc 1 N, (starRingEnd ℂ) (a n) * a m
          * ∫ t in (-T)..T,
              Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))))
        = ((‖a n‖ ^ 2 : ℝ) : ℂ) * ((2 * T : ℝ) : ℂ)
          + ∑ m ∈ (Finset.Icc 1 N).erase n, (starRingEnd ℂ) (a n) * a m
              * ∫ t in (-T)..T,
                  Complex.exp (Complex.I * (t : ℂ) * ((Real.log m : ℂ) - (Real.log n : ℂ))) := by
    intro n hn
    rw [← Finset.add_sum_erase _ _ hn]
    congr 1
    rw [hdiag n, hconjsq n]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

end Salt.MR
