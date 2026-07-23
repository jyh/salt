/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.JointHead
import Salt.MR.ShortIntervalPsi
import Salt.MR.HalaszContour

/-!
# The kernel-ramp head grade — the terminal assembly's closing ladder (`HeadGrade`)

The `√L` kernel ramp of `crossKer` (the `(X+h)/h` amplitude of `hat_mellin_bound`'s
`|s|⁻²` branch) is an artifact of composition order, not of the kernel.  This module
closes the last obstruction of the terminal assembly by the **τ-split** at the branch
crossover `T₀ := 2(X+h)/h`: the tail (`|τ| > T₀`, branch-2) cancels the ramp against its
own tail mass EXACTLY (`A₂·(2/T₀) = 2(X+h)^a`, RAMP-TAIL), and the head (`|τ| ≤ T₀`,
branch-1's `1/|s|` weight) closes to `C·L` by a width-decoupled Plancherel evaluation
(route A′, RAMP-HEAD).

The keystone is `widthA_plancherel`: the landed `dirichlet_plancherel`
(`HalaszContour`) COUPLES the Lorentzian width to the coefficient line `c`, but its
PROOF separates them — the Poisson integral `cexp_pois_full` takes width and frequency as
free parameters.  We rebuild the width-`a` Poisson integral from the PUBLIC `cos_int_pair`
(re-deriving only the odd-integrand vanishing `sin_int_zero_a` and the direct
integrability, since the full contour apparatus is private to `HalaszContour`), then clone
the Plancherel bilinear form at a Lorentzian width `a` FREE of `c`.

## The stones

1. `head_split_ledger` — the `crossKer` τ-split at `T₀` (integrability + additivity).
2. `widthA_plancherel` — **KEYSTONE**: the width-decoupled Plancherel identity.
3. `band_second_moment` — the dyadic band second moment via Lorentzian domination.
4. `offdiag_widthA_eval` — **KEYSTONE**: the width-`a` off-diagonal window sum.
5. `head_band_sum` — the dyadic head assembly (`C·L·amplitude`).
6. `tail_band_sum` — the tail (RAMP-TAIL's simple route: the exact cancellation).
7. `crossKer_head_tail_grade` — the composite `crossKer ≤ (X+h)^{…}·C·L`.
8. (`ysqrtL_coda`) — the `y = √L` corner concession (`a ≤ n^{1/8}`), flagged only.

The named residual (stone 8): the `y = √L` extreme corner needs `a ≤ n^{1/8}` for the
short-interval grain's regime — carried as the bounded concession hypothesis in stones 4/7,
with a `siegelWalfisz` PNT-lift named as future work (NOT built here).
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## Stone 2 machinery — the width-`a` Poisson integral (re-derived from `cos_int_pair`)

`HalaszContour`'s `cexp_pois_full` proves `∫ e^{iθt}/(c²+t²) = (π/c)e^{−c|θ|}` but its
supporting `sin_int_zero`, `poisF`, and the integrability are `private`.  We re-derive the
two ingredients we need at a free width `a`: the odd-integrand vanishing and the direct
integrability.  The real part is the PUBLIC `cos_int_pair` (used at width `a`). -/

/-- The sin transform of the width-`a` Poisson kernel vanishes (odd integrand).
Re-derivation of `HalaszContour`'s private `sin_int_zero` at a free width. -/
private lemma sin_int_zero_a {a θ : ℝ} (_ha : 0 < a) :
    ∫ t : ℝ, Real.sin (θ * t) / (a ^ 2 + t ^ 2) = 0 := by
  set f : ℝ → ℝ := fun t => Real.sin (θ * t) / (a ^ 2 + t ^ 2) with hf
  have hodd : (fun t : ℝ => f (-t)) = fun t : ℝ => -f t := by
    funext t
    simp only [hf]
    rw [show θ * -t = -(θ * t) by ring, Real.sin_neg, show (-t) ^ 2 = t ^ 2 by ring]
    ring
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
  have h1 : ∫ t : ℝ, f (-t) = ∫ t : ℝ, f t := hmp.integral_comp hemb f
  have h3 : ∫ t : ℝ, f (-t) = -∫ t : ℝ, f t := by rw [hodd, integral_neg]
  have : ∫ t : ℝ, f t = -∫ t : ℝ, f t := h1.symm.trans h3
  linarith

/-- The unit width-`a` Poisson integrand is integrable: its norm is exactly `(a²+t²)⁻¹`. -/
private lemma integrable_unit_pois_a {a θ : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ =>
      Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)) volume := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · exact (Complex.continuous_exp.comp (by fun_prop))
    · fun_prop
    · intro t
      exact_mod_cast (by positivity : (0 : ℝ) < a ^ 2 + t ^ 2).ne'
  refine (Salt.SW.integrable_inv_c_sq_add_sq ha).mono' hmeas
    (Filter.Eventually.of_forall (fun t => ?_))
  have hden : ‖(((a ^ 2 + t ^ 2 : ℝ)) : ℂ)‖ = a ^ 2 + t ^ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_div, Complex.norm_exp_ofReal_mul_I, hden]
  exact le_of_eq (one_div _)

/-- **The width-`a` complex Poisson integral** (all real `θ`): `∫ e^{iθt}/(a²+t²) dt
= (π/a)e^{−a|θ|}`.  Re-derivation of `HalaszContour`'s `cexp_pois_full` at a free width —
real part is the PUBLIC `cos_int_pair`, imaginary part vanishes by `sin_int_zero_a`. -/
private lemma cexp_pois_full_a {a θ : ℝ} (ha : 0 < a) :
    ∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)
      = ((Real.pi / a * Real.exp (-(a * |θ|)) : ℝ) : ℂ) := by
  have hInt := integrable_unit_pois_a (a := a) (θ := θ) ha
  have hre : (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
      = Real.pi / a * Real.exp (-(a * |θ|)) := by
    have hcos : ∀ t : ℝ,
        (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
          = Real.cos (θ * t) / (a ^ 2 + t ^ 2) :=
      fun t => by rw [Complex.div_ofReal_re, Complex.exp_ofReal_mul_I_re]
    calc (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re
        = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          (integral_re hInt).symm
      _ = ∫ t : ℝ, Real.cos (θ * t) / (a ^ 2 + t ^ 2) :=
          integral_congr_ae (Filter.Eventually.of_forall hcos)
      _ = Real.pi / a * Real.exp (-(a * |θ|)) := cos_int_pair ha
  have him : (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
      = 0 := by
    have hsin : ∀ t : ℝ,
        (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
          = Real.sin (θ * t) / (a ^ 2 + t ^ 2) :=
      fun t => by rw [Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im]
    calc (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).im
        = ∫ t : ℝ, (Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).im :=
          (integral_im hInt).symm
      _ = ∫ t : ℝ, Real.sin (θ * t) / (a ^ 2 + t ^ 2) :=
          integral_congr_ae (Filter.Eventually.of_forall hsin)
      _ = 0 := sin_int_zero_a ha
  rw [← Complex.re_add_im
    (∫ t : ℝ, Complex.exp (((θ * t : ℝ) : ℂ) * I) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)), hre, him]
  push_cast; ring

/-- The per-pair `cpow` decomposition at the coefficient line `c`: `(bₘ/mˢ)·conj(bₙ/nˢ)`
factors into the constant amplitude `bₘ b̄ₙ (mn)^{-c}` times the unit `e^{i(log n − log m)t}`.
Re-derivation of `HalaszContour`'s private `pair_cpow` (the line-`c` datum is self-contained). -/
private lemma pair_cpow_a {c t : ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (bm bn : ℂ) :
    (bm / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (bn / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
      = (bm * starRingEnd ℂ bn) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ)
        * Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have em : (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = Complex.exp ((Real.log m : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hmC, ← Complex.natCast_log]
  have en : (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = Complex.exp ((Real.log n : ℂ) * ((c : ℂ) + (t : ℂ) * I)) := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  have hrpow : (((m : ℝ) * (n : ℝ)) ^ c)⁻¹
      = Real.exp (-(c * (Real.log m + Real.log n))) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul hm0.ne' hn0.ne', ← Real.exp_neg]
    ring_nf
  have hexp : Complex.exp (-((Real.log m : ℂ) * ((c : ℂ) + (t : ℂ) * I)
        + starRingEnd ℂ ((Real.log n : ℂ) * ((c : ℂ) + (t : ℂ) * I))))
      = (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ)
        * Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I) := by
    rw [show ((((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ)) : ℂ)
        = Complex.exp ((-(c * (Real.log m + Real.log n)) : ℝ) : ℂ) by
      rw [hrpow, Complex.ofReal_exp], ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [em, en, map_div₀, ← Complex.exp_conj, div_mul_div_comm, div_eq_mul_inv,
    ← Complex.exp_add, ← Complex.exp_neg, hexp]
  ring

/-- **Stone 2 — the width-decoupled Plancherel identity (`widthA_plancherel`, KEYSTONE).**
The Dirichlet-polynomial Plancherel bilinear form against a Lorentzian of width `a` FREE of
the coefficient line `c`: for a finite window `F` of positive integers and any real `c`,

  `∫ ‖∑ bₙ/n^{c+it}‖²/(a²+t²) dt
      = (π/a)·∑_{m,n} Re(bₘ·conj bₙ)/(mn)^c·e^{−a|log m − log n|}`.

Clone of `dirichlet_plancherel` with the width `a` decoupled from `c` (the `cexp_pois_full`
separation, rebuilt at width `a` from the public `cos_int_pair`).  No positivity constraint
on `c` (the amplitude `(mn)^{-c}` is defined for all real `c` since `m, n ≥ 1`). -/
theorem widthA_plancherel (F : Finset ℕ) (b : ℕ → ℂ) {c a : ℝ} (ha : 0 < a)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (a ^ 2 + t ^ 2)
      = Real.pi / a * ∑ m ∈ F, ∑ n ∈ F,
          (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(a * |Real.log m - Real.log n|)) := by
  -- per-pair integrand as constant × unit width-`a` Poisson integrand, integrable
  have hpint : ∀ m ∈ F, ∀ n ∈ F, Integrable (fun t : ℝ =>
      (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
    intro m hm n hn
    have hrw : (fun t : ℝ => (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ))
      = fun t : ℝ => (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * (Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I)
            / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
      funext t; rw [pair_cpow_a (hF m hm) (hF n hn)]; ring
    rw [hrw]; exact (integrable_unit_pois_a ha).const_mul _
  -- per-pair integral value
  have hpval : ∀ m ∈ F, ∀ n ∈ F,
      ∫ t : ℝ, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)
        = (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * ((Real.pi / a * Real.exp (-(a * |Real.log n - Real.log m|)) : ℝ) : ℂ) := by
    intro m hm n hn
    have hrw : (fun t : ℝ => (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ))
      = fun t : ℝ => (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * (Complex.exp (((Real.log n - Real.log m) * t : ℝ) * I)
            / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)) := by
      funext t; rw [pair_cpow_a (hF m hm) (hF n hn)]; ring
    rw [hrw, integral_const_mul, cexp_pois_full_a ha]
  -- expand the squared norm as a double sum over F × F
  have hsum_expand : ∀ t : ℝ,
      ((‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
          * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) := by
    intro t
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  -- reduce the real integral to the real part of the complex double-sum integral
  have hcplx : ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (a ^ 2 + t ^ 2)
      = (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n) * (((((m : ℝ) * (n : ℝ)) ^ c)⁻¹ : ℝ) : ℂ))
          * ((Real.pi / a * Real.exp (-(a * |Real.log n - Real.log m|)) : ℝ) : ℂ)).re := by
    have hpt : ∀ t : ℝ,
        ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (a ^ 2 + t ^ 2)
        = (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re := by
      intro t
      have h1 : (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ))
          = (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)))
            / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun m _ => by rw [Finset.sum_div])
      rw [h1, ← hsum_expand t, Complex.div_ofReal_re, Complex.ofReal_re]
    calc ∫ t : ℝ, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 / (a ^ 2 + t ^ 2)
        = ∫ t : ℝ, (∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ t : ℝ, ∑ m ∈ F, ∑ n ∈ F, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re :=
          integral_re (MeasureTheory.integrable_finsetSum _ (fun m hm =>
            MeasureTheory.integrable_finsetSum _ (fun n hn => hpint m hm n hn)))
      _ = (∑ m ∈ F, ∑ n ∈ F, ∫ t : ℝ, (b m / (m : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * starRingEnd ℂ (b n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            / (((a ^ 2 + t ^ 2 : ℝ)) : ℂ)).re := by
          rw [MeasureTheory.integral_finsetSum _ (fun m hm =>
            MeasureTheory.integrable_finsetSum _ (fun n hn => hpint m hm n hn))]
          refine congrArg _ (Finset.sum_congr rfl (fun m hm => ?_))
          rw [MeasureTheory.integral_finsetSum _ (fun n hn => hpint m hm n hn)]
      _ = _ := by rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl
            (fun n hn => hpval m hm n hn))]
  rw [hcplx, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Complex.re_mul_ofReal, Complex.re_mul_ofReal,
    abs_sub_comm (Real.log n) (Real.log m), Nat.cast_mul, div_eq_mul_inv]
  ring

/-! ## Stone 4 — the width-`a` off-diagonal window evaluation (`offdiag_widthA_eval`, KEYSTONE)

The width-`a` analogue of `JointHead.offdiag_window_eval`: it bounds the bilinear sum
produced by `widthA_plancherel` (width `a` FREE of the coefficient line `c`) by the SINGLE
window mass times an absolute constant, for a line `c ≥ 1` and a width `a ≥ c` and
`Λ`-bounded coefficients.  The Chebyshev collapse of the lower-triangular inner sum works
regardless of the `a`-vs-`c` gap: for `m ≤ n` the width-`a` off-diagonal factor is
`‖bₘ‖·mᵃ⁻ᶜ · ‖bₙ‖·n⁻ᵃ⁻ᶜ`, and `mᵃ⁻ᶜ ≤ nᵃ⁻ᶜ` (`a ≥ c`) reduces the inner sum to
`nᵃ⁻ᶜ·ψ(n) ≤ (log4+4)·nᵃ⁻ᶜ⁺¹`, leaving `(log4+4)·‖bₙ‖·n¹⁻²ᶜ ≤ (log4+4)·‖bₙ‖·n⁻ᶜ` (`c ≥ 1`).

**RESIDUAL — the sharp `C·L/a` decay (the design's route A′).**  The `a`-independent
single-mass bound below incurs a `log log X` deficit when summed over the `Θ(log √L)` dyadic
bands of the head (`head_band_sum`): the band count multiplies the constant `M₁ ≍ L`, giving
`C·L·log log X`, not `C·L`.  The design's constant grade needs the SHARP `∑ ≤ diagonal + C·L/a`
— the off-diagonal part decaying like `1/a` via the short-interval grain
(`shortInterval_vonMangoldt_le`, `Σ_{m∈band}Λ(m) ≤ C·(band length) ≍ C·n/a`), whose regime
hypothesis `a ≤ n^{1/8}` is the named `y = √L` corner concession (stone 8).  The `k`-band split
+ geometric assembly (the ANALYTIC CORE) is now LANDED as `offdiag_widthA_sharp` below,
CONDITIONAL on the per-band `Λ`-mass datum `hband`; discharging `hband` from
`shortInterval_vonMangoldt_le` (with the regime threading + the out-of-regime Chebyshev
concession) is the remaining research ledge — FLAGGED, not forced, per iron rule 1 / SF-EXIT
(the exact recipe is in the module-tail residual note).  The crude form here is the honest
keystone: the width-`a` off-diagonal sum IS controlled by the single mass. -/

/-- The symmetric, nonnegative width-`a` off-diagonal kernel:
`‖bₘ‖‖bₙ‖/(mn)^c·e^{−a·|log m − log n|}`.  Re-derivation of `JointHead`'s private
`offdiagKer` at a free width `a`. -/
private def offdiagKerA (b : ℕ → ℂ) (c a : ℝ) (m n : ℕ) : ℝ :=
  ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
    * Real.exp (-(a * |Real.log m - Real.log n|))

/-- For a SYMMETRIC nonnegative kernel, the full double sum is at most twice its
lower-triangular part.  Re-derivation of `JointHead`'s private `sum_sym_le_two_lower`. -/
private lemma sum_sym_le_two_lower_A {F : Finset ℕ} {T : ℕ → ℕ → ℝ}
    (hsymm : ∀ m n, T m n = T n m) (hnn : ∀ m n, 0 ≤ T m n) :
    ∑ m ∈ F, ∑ n ∈ F, T m n
      ≤ 2 * ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0) := by
  have hle : ∀ m ∈ F, ∀ n ∈ F,
      T m n ≤ (if m ≤ n then T m n else 0) + (if n ≤ m then T n m else 0) := by
    intro m _ n _
    by_cases h : m ≤ n
    · rw [if_pos h]
      have h0 : (0 : ℝ) ≤ (if n ≤ m then T n m else 0) := by
        split_ifs with h'
        · exact hnn n m
        · exact le_refl 0
      linarith
    · have hnm : n ≤ m := (not_le.mp h).le
      rw [if_neg h, if_pos hnm, hsymm n m]
      linarith
  calc ∑ m ∈ F, ∑ n ∈ F, T m n
      ≤ ∑ m ∈ F, ∑ n ∈ F,
          ((if m ≤ n then T m n else 0) + (if n ≤ m then T n m else 0)) :=
        Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hle m hm n hn))
    _ = (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0))
          + (∑ m ∈ F, ∑ n ∈ F, (if n ≤ m then T n m else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0))
          + (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0)) := by
        congr 1
        exact Finset.sum_comm
    _ = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then T m n else 0) := by ring

/-- **Stone 4 — the width-`a` off-diagonal window evaluation** (`offdiag_widthA_eval`,
KEYSTONE).  For a line `c ≥ 1`, a width `a ≥ c`, a finite window `F` of positive integers,
and `Λ`-bounded coefficients `‖bₙ‖ ≤ Λ(n)`, the width-`a` bilinear form (the RHS of
`widthA_plancherel`, up to `π/a`) is bounded by the SINGLE window mass times an absolute
constant:
`∑_{m,n∈F} Re(bₘ·conj bₙ)/(mn)^c·e^{−a|log m−log n|} ≤ 2(log 4 + 4)·∑_{n∈F} ‖bₙ‖/n^c`.
(This is the `a`-independent form; the sharp `1/a` decay is the flagged residual above.) -/
theorem offdiag_widthA_eval {F : Finset ℕ} {b : ℕ → ℂ} {c a : ℝ} (hc : 1 ≤ c) (hac : c ≤ a)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n) :
    (∑ m ∈ F, ∑ n ∈ F, (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(a * |Real.log m - Real.log n|)))
      ≤ 2 * (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hac0 : (0 : ℝ) ≤ a - c := by linarith
  -- step 1: `Re(bₘ conj bₙ) ≤ ‖bₘ‖‖bₙ‖`, so the .re double sum ≤ the norm kernel sum
  have step1 : (∑ m ∈ F, ∑ n ∈ F, (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)))
        ≤ ∑ m ∈ F, ∑ n ∈ F, offdiagKerA b c a m n := by
    refine Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => ?_))
    simp only [offdiagKerA]
    have hre : (b m * (starRingEnd ℂ) (b n)).re ≤ ‖b m‖ * ‖b n‖ := by
      have h1 := Complex.re_le_norm (b m * (starRingEnd ℂ) (b n))
      rwa [norm_mul, Complex.norm_conj] at h1
    have hE : (0 : ℝ) ≤ (((m * n : ℕ) : ℝ) ^ c)⁻¹
        * Real.exp (-(a * |Real.log m - Real.log n|)) := by positivity
    calc (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(a * |Real.log m - Real.log n|))
        = (b m * (starRingEnd ℂ) (b n)).re
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(a * |Real.log m - Real.log n|))) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ‖b m‖ * ‖b n‖
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(a * |Real.log m - Real.log n|))) :=
          mul_le_mul_of_nonneg_right hre hE
      _ = ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(a * |Real.log m - Real.log n|)) := by rw [div_eq_mul_inv]; ring
  -- the kernel is symmetric and nonnegative
  have hTsymm : ∀ m n, offdiagKerA b c a m n = offdiagKerA b c a n m := by
    intro m n
    simp only [offdiagKerA]
    rw [mul_comm (‖b m‖) (‖b n‖), Nat.mul_comm m n, abs_sub_comm (Real.log m) (Real.log n)]
  have hTnn : ∀ m n, 0 ≤ offdiagKerA b c a m n := by
    intro m n; simp only [offdiagKerA]; positivity
  -- the identity `offdiagKerA m n = (‖bₘ‖·m^{a−c})·(‖bₙ‖·n^{−(a+c)})` for `m ≤ n`
  have hident : ∀ m ∈ F, ∀ n ∈ F, m ≤ n →
      offdiagKerA b c a m n = (‖b m‖ * (m : ℝ) ^ (a - c)) * (‖b n‖ * (n : ℝ) ^ (-(a + c))) := by
    intro m hm n hn hmn
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hF m hm
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
    have hlogle : Real.log m ≤ Real.log n := Real.log_le_log hm0 (by exact_mod_cast hmn)
    have habs : |Real.log m - Real.log n| = Real.log n - Real.log m := by
      rw [abs_of_nonpos (by linarith)]; ring
    have hexp : Real.exp (-(a * (Real.log n - Real.log m))) = (m : ℝ) ^ a / (n : ℝ) ^ a := by
      rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0, ← Real.exp_sub]
      congr 1; ring
    simp only [offdiagKerA]
    rw [habs, hexp,
      show ((m * n : ℕ) : ℝ) ^ c = (m : ℝ) ^ c * (n : ℝ) ^ c from by
        push_cast; rw [Real.mul_rpow hm0.le hn0.le],
      show (m : ℝ) ^ (a - c) = (m : ℝ) ^ a / (m : ℝ) ^ c from by
        rw [Real.rpow_sub hm0],
      show (n : ℝ) ^ (-(a + c)) = 1 / ((n : ℝ) ^ a * (n : ℝ) ^ c) from by
        rw [Real.rpow_neg hn0.le, Real.rpow_add hn0, one_div]]
    field_simp
  -- the per-`n` Chebyshev collapse of the lower-triangular inner sum
  have hPn : ∀ n : ℕ, (∑ m ∈ F, (if m ≤ n then ‖b m‖ else 0)) ≤ (Real.log 4 + 4) * (n : ℝ) := by
    intro n
    rw [← Finset.sum_filter]
    have hsub : (F.filter (fun m => m ≤ n)) ⊆ Finset.Ioc 0 n := by
      intro m hmf
      rw [Finset.mem_filter] at hmf
      rw [Finset.mem_Ioc]
      exact ⟨hF m hmf.1, hmf.2⟩
    calc ∑ m ∈ F.filter (fun m => m ≤ n), ‖b m‖
        ≤ ∑ m ∈ F.filter (fun m => m ≤ n), ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum (fun m _ => hb m)
      _ ≤ ∑ k ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi (n : ℝ) := by
          rw [show Chebyshev.psi (n : ℝ)
              = ∑ k ∈ Finset.Ioc 0 ⌊(n : ℝ)⌋₊, ArithmeticFunction.vonMangoldt k from rfl,
            Nat.floor_natCast]
      _ ≤ (Real.log 4 + 4) * (n : ℝ) := Chebyshev.psi_le_const_mul_self (by positivity)
  -- the key bound: the lower-triangular kernel sum ≤ (log 4 + 4)·(single mass)
  have key : (∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then offdiagKerA b c a m n else 0))
      ≤ (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
    calc ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then offdiagKerA b c a m n else 0)
        = ∑ n ∈ F, ∑ m ∈ F, (if m ≤ n then offdiagKerA b c a m n else 0) := Finset.sum_comm
      _ = ∑ n ∈ F, (‖b n‖ * (n : ℝ) ^ (-(a + c)))
            * (∑ m ∈ F, if m ≤ n then ‖b m‖ * (m : ℝ) ^ (a - c) else 0) := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m hm => ?_)
          by_cases h : m ≤ n
          · rw [if_pos h, if_pos h, hident m hm n hn h, mul_comm]
          · rw [if_neg h, if_neg h, mul_zero]
      _ ≤ ∑ n ∈ F, (Real.log 4 + 4) * (‖b n‖ / (n : ℝ) ^ c) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hF n hn
          have hKnn : (0 : ℝ) ≤ ‖b n‖ * (n : ℝ) ^ (-(a + c)) := by positivity
          -- inner sum: bound `m^{a−c} ≤ n^{a−c}`, then Chebyshev
          have hinner : (∑ m ∈ F, if m ≤ n then ‖b m‖ * (m : ℝ) ^ (a - c) else 0)
              ≤ (n : ℝ) ^ (a - c) * ((Real.log 4 + 4) * (n : ℝ)) := by
            calc (∑ m ∈ F, if m ≤ n then ‖b m‖ * (m : ℝ) ^ (a - c) else 0)
                ≤ ∑ m ∈ F, if m ≤ n then ‖b m‖ * (n : ℝ) ^ (a - c) else 0 := by
                  refine Finset.sum_le_sum (fun m hm => ?_)
                  by_cases h : m ≤ n
                  · rw [if_pos h, if_pos h]
                    have hm1 : (0 : ℝ) ≤ (m : ℝ) := by positivity
                    have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
                    exact mul_le_mul_of_nonneg_left
                      (Real.rpow_le_rpow hm1 hmn hac0) (norm_nonneg _)
                  · rw [if_neg h, if_neg h]
              _ = (n : ℝ) ^ (a - c) * ∑ m ∈ F, if m ≤ n then ‖b m‖ else 0 := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun m hm => ?_)
                  by_cases h : m ≤ n
                  · rw [if_pos h, if_pos h, mul_comm]
                  · rw [if_neg h, if_neg h, mul_zero]
              _ ≤ (n : ℝ) ^ (a - c) * ((Real.log 4 + 4) * (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left (hPn n) (Real.rpow_nonneg hn0.le _)
          -- combine: (‖bₙ‖·n^{−(a+c)})·(n^{a−c}·(log4+4)·n) ≤ (log4+4)·‖bₙ‖/n^c
          have hpow : (n : ℝ) ^ (-(a + c)) * ((n : ℝ) ^ (a - c) * (n : ℝ))
              ≤ (n : ℝ) ^ (-c) := by
            have e1 : (n : ℝ) ^ (a - c) * (n : ℝ) = (n : ℝ) ^ (a - c + 1) := by
              rw [Real.rpow_add hn0, Real.rpow_one]
            have e2 : (n : ℝ) ^ (-(a + c)) * (n : ℝ) ^ (a - c + 1) = (n : ℝ) ^ (1 - 2 * c) := by
              rw [← Real.rpow_add hn0]; congr 1; ring
            rw [e1, e2]
            exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
          calc (‖b n‖ * (n : ℝ) ^ (-(a + c)))
                  * (∑ m ∈ F, if m ≤ n then ‖b m‖ * (m : ℝ) ^ (a - c) else 0)
              ≤ (‖b n‖ * (n : ℝ) ^ (-(a + c)))
                  * ((n : ℝ) ^ (a - c) * ((Real.log 4 + 4) * (n : ℝ))) :=
                mul_le_mul_of_nonneg_left hinner hKnn
            _ = (Real.log 4 + 4) * (‖b n‖
                  * ((n : ℝ) ^ (-(a + c)) * ((n : ℝ) ^ (a - c) * (n : ℝ)))) := by ring
            _ ≤ (Real.log 4 + 4) * (‖b n‖ * (n : ℝ) ^ (-c)) := by
                have hlog4 : (0 : ℝ) ≤ Real.log 4 + 4 := by positivity
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) hlog4
            _ = (Real.log 4 + 4) * (‖b n‖ / (n : ℝ) ^ c) := by
                rw [Real.rpow_neg hn0.le, div_eq_mul_inv]
      _ = (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by rw [Finset.mul_sum]
  -- assemble
  calc (∑ m ∈ F, ∑ n ∈ F, (b m * (starRingEnd ℂ) (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)))
      ≤ ∑ m ∈ F, ∑ n ∈ F, offdiagKerA b c a m n := step1
    _ ≤ 2 * ∑ m ∈ F, ∑ n ∈ F, (if m ≤ n then offdiagKerA b c a m n else 0) :=
        sum_sym_le_two_lower_A hTsymm hTnn
    _ ≤ 2 * ((Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 2 * (Real.log 4 + 4) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by ring

/-! ## Stone 4-sharp — the width-`a` off-diagonal with the `1/a` decay (`offdiag_widthA_sharp`)

The crude `offdiag_widthA_eval` bounds the width-`a` off-diagonal by an `a`-independent multiple
of the single window mass; summed over the `Θ(log √L)` dyadic head bands (`head_band_sum`), the
band count multiplies the constant, giving the `log log X` deficit.  The sharp form recovers the
`1/a` decay by KEEPING the `e^{−a·|log m − log n|}` grain per `e`-fold band.

**The geometric page (verified).**  For the strict lower triangle `m < n`, write the inner
weight `∑_{m<n} ‖b_m‖·m^{a−c}` and partition `{m < n}` by the band index `k = ⌊a·(log n − log
m)⌋₊` (so `m ∈ (n e^{−(k+1)/a}, n e^{−k/a}]`).  On band `k`: `m^{a−c} ≤ n^{a−c}·e^{−k(a−c)/a}`
(`m ≤ n e^{−k/a}`, `a ≥ c`), and the band `Λ`-mass is `≤ Cb·(n/a)·e^{−k/a}` (the SHORT-INTERVAL
grain — `shortInterval_vonMangoldt_le`, band length `≍ n/a`).  The product is `(Cb/a)·n^{a−c+1}·
e^{−k(a−c+1)/a}`; the geometric sum (`geom_partial_le` + `inv_one_sub_exp_neg_le`, ratio `r =
e^{−(a−c+1)/a}`, `1/(1−r) ≤ a/(a−c+1) + 1`) gives the per-`n` inner bound `≤ 2·Cb·n^{a−c+1}/(a−c
+1)`, and reassembling the `n`-sum with `n^{1−2c} ≤ n^{−c}` (`c ≥ 1`) leaves
`∑_{m<n} ≤ 2·Cb/(a−c+1)·∑_n ‖b_n‖/n^c` — the sharp `1/(a−c+1) ≍ 1/a` decay (for `c ≍ 1 ≪ a`).

**Landed here: the ANALYTIC CORE, conditional on the band-mass datum.**  `inner_sharp` and
`offdiag_widthA_sharp` prove the reindex + geometric assembly SORRY-FREE, taking the per-band
`Λ`-mass bound `hband` as an explicit hypothesis.  The named residual (stone 8, the `y = √L`
corner) is EXACTLY the discharge of `hband` from `shortInterval_vonMangoldt_le`: each fiber
`{m ∈ F, m < n : ⌊a·(log n − log m)⌋₊ = k}` sits inside `Ioc ⌊n e^{−(k+1)/a}⌋ ⌊n e^{−k/a}⌋`, and
`shortInterval_vonMangoldt_le` (with `Cb = 250`) gives the band bound in its regime `65536 ≤ n
e^{−(k+1)/a}` and `a ≤ (n e^{−(k+1)/a})^{1/8}` — the honest `a ≤ n^{1/8}` concession.  Bands
out of regime (far `k`, or small `n ≤ a^8`) carry the crude Chebyshev `Θ(log a) = Θ(log log X)`
concession, EMPTY once the window floor `y ≥ a^8` (the y-gate).  Discharging `hband` with that
regime split is the last research ledge; it is FLAGGED, not forced, per iron rule 1 / SF-EXIT. -/

/-- Geometric partial sum: `∑_{k<K} r^k ≤ (1−r)⁻¹` for `0 ≤ r < 1`. -/
private lemma geom_partial_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ k ≤ (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  have hne2 : (1 : ℝ) - r ≠ 0 := by linarith
  have hrpow : (0 : ℝ) ≤ r ^ K := by positivity
  rw [geom_sum_eq hne]
  have heq : (r ^ K - 1) / (r - 1) = (1 - r ^ K) * (1 - r)⁻¹ := by
    field_simp; ring
  rw [heq]
  exact mul_le_of_le_one_left (by positivity) (by nlinarith [hrpow])

/-- The geometric-tail constant: `(1 − e^{−δ})⁻¹ ≤ δ⁻¹ + 1` for `δ > 0`. -/
private lemma inv_one_sub_exp_neg_le {δ : ℝ} (hδ : 0 < δ) :
    (1 - Real.exp (-δ))⁻¹ ≤ δ⁻¹ + 1 := by
  have hu1 : Real.exp (-δ) * (1 + δ) ≤ 1 := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    linarith [Real.add_one_le_exp δ]
  have hpos : (0 : ℝ) < 1 - Real.exp (-δ) := by
    nlinarith [hu1, Real.exp_pos (-δ)]
  have hkey : δ ≤ (1 + δ) * (1 - Real.exp (-δ)) := by nlinarith [hu1]
  rw [← one_div (1 - Real.exp (-δ)), div_le_iff₀ hpos,
    show δ⁻¹ + 1 = (1 + δ) / δ from by field_simp, div_mul_eq_mul_div, le_div_iff₀ hδ, one_mul]
  linarith [hkey]

/-- **The per-`n` inner sharp bound** (the geometric core of `offdiag_widthA_sharp`).  Given the
per-band `Λ`-mass datum `hband` (`∑_{m ∈ band k} ‖b_m‖ ≤ Cb·(n/a)·e^{−k/a}`, the short-interval
grain), the lower-triangular inner weight `∑_{m<n} ‖b_m‖·m^{a−c}` is bounded by `2·Cb·n^{a−c+1}/
(a−c+1)` — the `1/a` decay, via band reindexing (`sum_fiberwise_of_maps_to`) and the geometric
sum.  Coefficients unconstrained beyond the band datum; `1 ≤ c ≤ a`. -/
private lemma inner_sharp {F : Finset ℕ} {b : ℕ → ℂ} {c a : ℝ}
    (hc : 1 ≤ c) (hca : c ≤ a) {n : ℕ} (hn : 1 ≤ n)
    (hF : ∀ m ∈ F, 1 ≤ m) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hband : ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a))) :
    (∑ m ∈ F.filter (· < n), ‖b m‖ * (m : ℝ) ^ (a - c))
      ≤ 2 * Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hac0 : (0 : ℝ) ≤ a - c := by linarith
  have hac1 : (0 : ℝ) < a - c + 1 := by linarith
  have hδpos : (0 : ℝ) < (a - c + 1) / a := by positivity
  have hδle : (a - c + 1) / a ≤ 1 := by rw [div_le_one ha0]; linarith
  have hmaps : ∀ m ∈ F.filter (· < n),
      (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊) m
        ∈ Finset.range (⌊a * Real.log (n : ℝ)⌋₊ + 1) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hm1 : 1 ≤ m := hF m hm.1
    have hmlog0 : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
    rw [Finset.mem_range]
    refine Nat.lt_succ_of_le (Nat.floor_le_floor ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) ha0.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun m => ‖b m‖ * (m : ℝ) ^ (a - c))]
  have hbandbd : ∀ k ∈ Finset.range (⌊a * Real.log (n : ℝ)⌋₊ + 1),
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k),
          ‖b m‖ * (m : ℝ) ^ (a - c))
        ≤ Cb / a * (n : ℝ) ^ (a - c + 1) * (Real.exp (-((a - c + 1) / a))) ^ k := by
    intro k _
    have hfactor : ∀ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k),
        ‖b m‖ * (m : ℝ) ^ (a - c)
          ≤ ‖b m‖ * ((n : ℝ) ^ (a - c) * Real.exp (-((k : ℝ) * (a - c) / a))) := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_filter] at hm
      have hm1 : 1 ≤ m := hF m hm.1.1
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hmn : m < n := hm.1.2
      have hlogle : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hm0 (by exact_mod_cast hmn.le)
      have hkle : (k : ℝ) ≤ a * (Real.log (n : ℝ) - Real.log (m : ℝ)) := by
        rw [← hm.2]; exact Nat.floor_le (by nlinarith [hlogle, ha0])
      have hmle : (m : ℝ) ≤ (n : ℝ) * Real.exp (-((k : ℝ) / a)) := by
        rw [← Real.exp_log hm0, ← Real.exp_log hn0, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hkdiv : (k : ℝ) / a ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
          rw [div_le_iff₀ ha0]; linarith [hkle]
        linarith [hkdiv]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc (m : ℝ) ^ (a - c)
          ≤ ((n : ℝ) * Real.exp (-((k : ℝ) / a))) ^ (a - c) :=
            Real.rpow_le_rpow hm0.le hmle hac0
        _ = (n : ℝ) ^ (a - c) * Real.exp (-((k : ℝ) / a)) ^ (a - c) :=
            Real.mul_rpow hn0.le (Real.exp_pos _).le
        _ = (n : ℝ) ^ (a - c) * Real.exp (-((k : ℝ) * (a - c) / a)) := by
            rw [← Real.exp_mul]; congr 2; ring
    calc (∑ m ∈ (F.filter (· < n)).filter
              (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k),
              ‖b m‖ * (m : ℝ) ^ (a - c))
        ≤ ∑ m ∈ (F.filter (· < n)).filter
              (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k),
              ‖b m‖ * ((n : ℝ) ^ (a - c) * Real.exp (-((k : ℝ) * (a - c) / a))) :=
          Finset.sum_le_sum hfactor
      _ = ((n : ℝ) ^ (a - c) * Real.exp (-((k : ℝ) * (a - c) / a)))
            * ∑ m ∈ (F.filter (· < n)).filter
              (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
      _ ≤ ((n : ℝ) ^ (a - c) * Real.exp (-((k : ℝ) * (a - c) / a)))
            * (Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a))) :=
          mul_le_mul_of_nonneg_left (hband k) (by positivity)
      _ = Cb / a * (n : ℝ) ^ (a - c + 1) * (Real.exp (-((a - c + 1) / a))) ^ k := by
          rw [Real.rpow_add hn0, Real.rpow_one, ← Real.exp_nat_mul]
          rw [show ((n : ℝ) ^ (a - c) * Real.exp (-((k : ℝ) * (a - c) / a)))
                * (Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a)))
              = Cb / a * ((n : ℝ) ^ (a - c) * (n : ℝ))
                * (Real.exp (-((k : ℝ) * (a - c) / a)) * Real.exp (-((k : ℝ) / a))) from by ring]
          rw [← Real.exp_add]
          congr 2
          ring
  calc (∑ k ∈ Finset.range (⌊a * Real.log (n : ℝ)⌋₊ + 1),
          ∑ m ∈ (F.filter (· < n)).filter
            (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k),
            ‖b m‖ * (m : ℝ) ^ (a - c))
      ≤ ∑ k ∈ Finset.range (⌊a * Real.log (n : ℝ)⌋₊ + 1),
          Cb / a * (n : ℝ) ^ (a - c + 1) * (Real.exp (-((a - c + 1) / a))) ^ k :=
        Finset.sum_le_sum hbandbd
    _ = Cb / a * (n : ℝ) ^ (a - c + 1)
          * ∑ k ∈ Finset.range (⌊a * Real.log (n : ℝ)⌋₊ + 1),
              (Real.exp (-((a - c + 1) / a))) ^ k := by rw [Finset.mul_sum]
    _ ≤ Cb / a * (n : ℝ) ^ (a - c + 1) * (1 - Real.exp (-((a - c + 1) / a)))⁻¹ :=
        mul_le_mul_of_nonneg_left
          (geom_partial_le (Real.exp_pos _).le
            (by rw [Real.exp_lt_one_iff]; linarith [hδpos]) _)
          (by positivity)
    _ ≤ Cb / a * (n : ℝ) ^ (a - c + 1) * (((a - c + 1) / a)⁻¹ + 1) :=
        mul_le_mul_of_nonneg_left (inv_one_sub_exp_neg_le hδpos) (by positivity)
    _ ≤ 2 * Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1) := by
        have hnp : (0 : ℝ) ≤ (n : ℝ) ^ (a - c + 1) := by positivity
        rw [mul_add, mul_one, show ((a - c + 1) / a)⁻¹ = a / (a - c + 1) from by rw [inv_div]]
        have e1 : Cb / a * (n : ℝ) ^ (a - c + 1) * (a / (a - c + 1))
            = Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1) := by field_simp
        rw [e1]
        have e2 : Cb / a * (n : ℝ) ^ (a - c + 1)
            ≤ Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1) := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_left (mul_nonneg hCb hnp) hac1 (by linarith)
        have e3 : 2 * Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1)
            = Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1)
              + Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1) := by ring
        rw [e3]; linarith [e2]

/-- **Stone 4-sharp — the width-`a` off-diagonal with `1/a` decay** (`offdiag_widthA_sharp`).
For a line `c ≥ 1`, a width `a ≥ c`, a finite window `F` of positive integers, and the per-band
`Λ`-mass datum `hband` (the short-interval grain, `Cb = 250` in regime — see the section note),
the STRICT off-diagonal norm sum decays like `1/(a−c+1) ≍ 1/a`:
`∑_{m<n∈F} ‖b_m‖‖b_n‖/(mn)^c·e^{−a|log m−log n|} ≤ 2·Cb/(a−c+1)·∑_{n∈F} ‖b_n‖/n^c`.
The full off-diagonal (`m ≠ n`) is twice this (kernel symmetry).  This is the sharp replacement
for `offdiag_widthA_eval`'s `a`-independent bound; the `1/a` telescopes the head band count. -/
theorem offdiag_widthA_sharp {F : Finset ℕ} {b : ℕ → ℂ} {c a : ℝ}
    (hc : 1 ≤ c) (hca : c ≤ a) (hF : ∀ n ∈ F, 1 ≤ n) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hband : ∀ n ∈ F, ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a))) :
    (∑ m ∈ F, ∑ n ∈ F, if m < n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(a * |Real.log m - Real.log n|)) else 0)
      ≤ 2 * Cb / (a - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hac1 : (0 : ℝ) < a - c + 1 := by linarith
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hF n hn
  rw [← Finset.sum_filter]
  have hid : ∀ m ∈ F.filter (· < n),
      ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c * Real.exp (-(a * |Real.log m - Real.log n|))
        = (‖b n‖ * (n : ℝ) ^ (-(a + c))) * (‖b m‖ * (m : ℝ) ^ (a - c)) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hF m hm.1
    have hmn : m < n := hm.2
    have hlogle : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hm0 (by exact_mod_cast hmn.le)
    have habs : |Real.log (m : ℝ) - Real.log (n : ℝ)| = Real.log (n : ℝ) - Real.log (m : ℝ) := by
      rw [abs_of_nonpos (by linarith)]; ring
    have hexp : Real.exp (-(a * (Real.log (n : ℝ) - Real.log (m : ℝ))))
        = (m : ℝ) ^ a / (n : ℝ) ^ a := by
      rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0, ← Real.exp_sub]
      congr 1; ring
    rw [habs, hexp,
      show ((m * n : ℕ) : ℝ) ^ c = (m : ℝ) ^ c * (n : ℝ) ^ c from by
        push_cast; rw [Real.mul_rpow hm0.le hn0.le],
      show (m : ℝ) ^ (a - c) = (m : ℝ) ^ a / (m : ℝ) ^ c from by rw [Real.rpow_sub hm0],
      show (n : ℝ) ^ (-(a + c)) = 1 / ((n : ℝ) ^ a * (n : ℝ) ^ c) from by
        rw [Real.rpow_neg hn0.le, Real.rpow_add hn0, one_div]]
    field_simp
  rw [Finset.sum_congr rfl hid, ← Finset.mul_sum]
  have hinner := inner_sharp hc hca (hF n hn) hF hCb (hband n hn)
  have hKnn : (0 : ℝ) ≤ ‖b n‖ * (n : ℝ) ^ (-(a + c)) := by positivity
  calc (‖b n‖ * (n : ℝ) ^ (-(a + c)))
          * ∑ m ∈ F.filter (· < n), ‖b m‖ * (m : ℝ) ^ (a - c)
      ≤ (‖b n‖ * (n : ℝ) ^ (-(a + c)))
          * (2 * Cb * (n : ℝ) ^ (a - c + 1) / (a - c + 1)) :=
        mul_le_mul_of_nonneg_left hinner hKnn
    _ = 2 * Cb / (a - c + 1) * (‖b n‖ * ((n : ℝ) ^ (-(a + c)) * (n : ℝ) ^ (a - c + 1))) := by ring
    _ ≤ 2 * Cb / (a - c + 1) * (‖b n‖ / (n : ℝ) ^ c) := by
        have hpow : (n : ℝ) ^ (-(a + c)) * (n : ℝ) ^ (a - c + 1) ≤ (n : ℝ) ^ (-c) := by
          rw [← Real.rpow_add hn0]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        have hrhs : ‖b n‖ / (n : ℝ) ^ c = ‖b n‖ * (n : ℝ) ^ (-c) := by
          rw [Real.rpow_neg hn0.le, div_eq_mul_inv]
        rw [hrhs]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)

/-! ## Stone 3 — the dyadic band second moment (`band_second_moment`)

On the band `|τ| ≤ a`, the Lorentzian `1/(a²+τ²) ≥ 1/(2a²)` (since `τ² ≤ a²`), so the raw
second moment `∫_{|τ|≤a} ‖P‖²` is dominated by `2a²·∫_ℝ ‖P‖²/(a²+τ²)` — the full-line
Lorentzian-weighted moment `widthA_plancherel` evaluates.  This is the bridge from the raw
band moment to the width-`a` bilinear form: on the dyadic band `a = 2^{j+1}`, combined with
`widthA_plancherel`, it reads `∫_{|τ|≤2^{j+1}} ‖P‖² ≤ 2·2^{j+1}·π·[the width-`a` sum]`. -/

/-- The Dirichlet polynomial `∑ bₙ/n^{c+iτ}` is continuous in `τ`. -/
private lemma continuous_dirichletPoly (F : Finset ℕ) (b : ℕ → ℂ) (c : ℝ)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    Continuous (fun τ : ℝ => ∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)) := by
  refine continuous_finsetSum _ (fun n hn => ?_)
  have hn0 : n ≠ 0 := by have := hF n hn; omega
  have hbC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hne : ∀ τ : ℝ, (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    intro τ; rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, _⟩; exact hbC h0
  have hf : Continuous (fun τ : ℝ => (c : ℂ) + (τ : ℂ) * I) := by fun_prop
  simp_rw [div_eq_mul_inv]
  exact continuous_const.mul ((hf.const_cpow (Or.inl hbC)).inv₀ hne)

/-- **Stone 3 — the band second moment** (`band_second_moment`).  For a finite window `F` of
positive integers, any line `c`, and width `a > 0`, the raw second moment of the Dirichlet
polynomial over the band `|τ| ≤ a` is dominated by `2a²` times the full-line
Lorentzian-weighted moment (which `widthA_plancherel` evaluates). -/
theorem band_second_moment (F : Finset ℕ) (b : ℕ → ℂ) {c a : ℝ} (ha : 0 < a)
    (hF : ∀ n ∈ F, 1 ≤ n) :
    (∫ τ in Set.Icc (-a) a, ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2)
      ≤ 2 * a ^ 2 * ∫ τ : ℝ,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (a ^ 2 + τ ^ 2) := by
  set P : ℝ → ℂ := fun τ => ∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I) with hP
  set M : ℝ := ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun n _ => by positivity)
  have hcont : Continuous P := continuous_dirichletPoly F b c hF
  -- the uniform sup bound `‖P τ‖ ≤ M`
  have hnormle : ∀ τ : ℝ, ‖P τ‖ ≤ M := by
    intro τ
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun n hn => ?_)))
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
    have hre : ((c : ℂ) + (τ : ℂ) * I).re = c := by simp
    rw [norm_div, show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0, hre]
  -- the Lorentzian-weighted moment is integrable (dominated by `M²·(a²+τ²)⁻¹`)
  have hLint : Integrable (fun τ : ℝ => ‖P τ‖ ^ 2 / (a ^ 2 + τ ^ 2)) := by
    have hmeas : AEStronglyMeasurable (fun τ : ℝ => ‖P τ‖ ^ 2 / (a ^ 2 + τ ^ 2)) volume :=
      ((hcont.norm.pow 2).div (by fun_prop) (fun τ => by positivity)).aestronglyMeasurable
    refine ((Salt.SW.integrable_inv_c_sq_add_sq ha).const_mul (M ^ 2)).mono' hmeas
      (Filter.Eventually.of_forall (fun τ => ?_))
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv]
    gcongr
    exact hnormle τ
  -- band integrability of the raw second moment
  have hband : IntegrableOn (fun τ : ℝ => ‖P τ‖ ^ 2) (Set.Icc (-a) a) volume :=
    (hcont.norm.pow 2).integrableOn_Icc
  -- pointwise band domination
  have hpt : ∀ τ ∈ Set.Icc (-a) a, ‖P τ‖ ^ 2 ≤ 2 * a ^ 2 * (‖P τ‖ ^ 2 / (a ^ 2 + τ ^ 2)) := by
    intro τ hτ
    rw [Set.mem_Icc] at hτ
    have hd : (0 : ℝ) < a ^ 2 + τ ^ 2 := by positivity
    have hτ2 : τ ^ 2 ≤ a ^ 2 := by nlinarith [hτ.1, hτ.2]
    have hratio : (1 : ℝ) ≤ 2 * a ^ 2 / (a ^ 2 + τ ^ 2) := by
      rw [le_div_iff₀ hd]; linarith
    calc ‖P τ‖ ^ 2 = ‖P τ‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P τ‖ ^ 2 * (2 * a ^ 2 / (a ^ 2 + τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
      _ = 2 * a ^ 2 * (‖P τ‖ ^ 2 / (a ^ 2 + τ ^ 2)) := by ring
  -- assemble
  calc (∫ τ in Set.Icc (-a) a, ‖P τ‖ ^ 2)
      ≤ ∫ τ in Set.Icc (-a) a, 2 * a ^ 2 * (‖P τ‖ ^ 2 / (a ^ 2 + τ ^ 2)) :=
        setIntegral_mono_on hband ((hLint.const_mul (2 * a ^ 2)).integrableOn)
          measurableSet_Icc hpt
    _ = 2 * a ^ 2 * ∫ τ in Set.Icc (-a) a, ‖P τ‖ ^ 2 / (a ^ 2 + τ ^ 2) :=
        integral_const_mul _ _
    _ ≤ 2 * a ^ 2 * ∫ τ : ℝ, ‖P τ‖ ^ 2 / (a ^ 2 + τ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hLint (Filter.Eventually.of_forall (fun τ => by positivity)))
          (by positivity)

/-! ## Stone 1 — the `crossKer` τ-split at the branch crossover (`head_split_ledger`)

The `crossKer` `t`-integral splits additively at `T₀ := 2(X+h)/h` (the branch crossover of
`hat_mellin_bound`, `√L`-grade at the pin): the head `|t − t₀| ≤ T₀` (branch-1's `1/|s|`
weight, `head_band_sum`) and the tail `|t − t₀| > T₀` (branch-2's `1/|s|²` weight, whose
tail mass cancels the ramp EXACTLY, `tail_band_sum`).  The integrand is nonneg, continuous
and integrable (`crossKer_integrand_integrable`), so the split is exact. -/

/-- **Stone 1 — the `crossKer` head/tail split** (`head_split_ledger`).  `crossKer` equals the
integral over the head band `|t − t₀| ≤ T₀` plus the integral over the tail `T₀ < |t − t₀|`,
at `T₀ := 2(X+h)/h`.  Exact additivity of the integrable nonneg integrand. -/
theorem head_split_ledger {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    crossKer g X h y c₀ t₀ α β
      = (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
            ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
              * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
              * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
        + (∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
            ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
              * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
              * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) := by
  have hfi : Integrable (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) :=
    crossKer_integrand_integrable hX hh hc
  have hcabs : Continuous (fun t : ℝ => |t - t₀|) := (continuous_id.sub continuous_const).abs
  have hsmeas : MeasurableSet {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h} :=
    (isClosed_le hcabs continuous_const).measurableSet
  have hset : {t : ℝ | 2 * (X + h) / h < |t - t₀|}
      = {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h}ᶜ := by
    ext t; simp [not_le]
  rw [crossKer, ← integral_add_compl hsmeas hfi, hset]

/-! ## Stone 6 — the tail band mass and cross-integral (RAMP-TAIL's exact cancellation)

The tail (`|τ| > T₀`, branch-2's `1/|s|²` weight) closes by EXACT ALGEBRA: at
`T₀ := 2(X+h)/h` the branch-2 tail mass `2(X+h)^{c+1}/(hT₀)` equals `(X+h)^c` per side, so
the whole tail kernel mass is `2(X+h)^c` — the `√L` ramp `(X+h)/h` and the tail mass
`2/T₀ = h/(X+h)` annihilate.  With the crude leg sups (`norm_windowSum_le_mass`, constant in
`t`) the cross-integral tail is `≤ (window masses)·2(X+h)^{c₀−α−β}` — no ramp. -/

/-- **Stone 6a — the exact tail-mass cancellation** (`kernel_tail_mass`).  At the branch
crossover `T₀ := 2(X+h)/h`, the branch-2 tail mass of the hat kernel is EXACTLY `2(X+h)^c`:
`∫_{|τ| > T₀} ‖hatKernel X h c τ‖ dτ ≤ 2(X+h)^c`.  The `√L` amplitude ramp cancels against
the `2/T₀` tail mass (RAMP-TAIL's `A₂·(2/T₀) = 2(X+h)^c`). -/
theorem kernel_tail_mass {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) :
    (∫ τ in {τ : ℝ | 2 * (X + h) / h < |τ|}, ‖hatKernel X h c τ‖) ≤ 2 * (X + h) ^ c := by
  have hXh : (0 : ℝ) < X + h := by linarith
  set T₀ : ℝ := 2 * (X + h) / h with hT₀def
  have hT₀ : 0 < T₀ := by rw [hT₀def]; positivity
  have hInt : Integrable (fun τ : ℝ => ‖hatKernel X h c τ‖) := (integrable_hatKernel hX hh hc).norm
  have hb2int : Integrable (fun τ : ℝ => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2))) :=
    integrable_branch2 hc
  have hpow : (X + h) ^ (c + 1) = (X + h) ^ c * (X + h) := by
    rw [Real.rpow_add hXh, Real.rpow_one]
  have hval : 2 * (X + h) ^ (c + 1) / (h * T₀) = (X + h) ^ c := by
    rw [hT₀def, hpow]; field_simp
  have htail_r : (∫ τ in Set.Ioi T₀, ‖hatKernel X h c τ‖) ≤ (X + h) ^ c :=
    calc ∫ τ in Set.Ioi T₀, ‖hatKernel X h c τ‖
        ≤ ∫ τ in Set.Ioi T₀, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) :=
          setIntegral_mono_on hInt.integrableOn hb2int.integrableOn measurableSet_Ioi
            (fun τ _ => hatKernel_branch2 hX hh hc τ)
      _ ≤ 2 * (X + h) ^ (c + 1) / (h * T₀) := hat_tail hX hh hc hT₀
      _ = (X + h) ^ c := hval
  have htail_l : (∫ τ in Set.Iic (-T₀), ‖hatKernel X h c τ‖) ≤ (X + h) ^ c := by
    have hcongr : (∫ τ in Set.Iic (-T₀), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)))
        = ∫ τ in Set.Ioi T₀, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) := by
      rw [show (∫ τ in Set.Iic (-T₀), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)))
            = ∫ τ in Set.Iic (-T₀), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + (-τ) ^ 2)) from
          setIntegral_congr_fun measurableSet_Iic (fun τ _ => by rw [neg_sq])]
      rw [integral_comp_neg_Iic (-T₀)
        (fun τ => 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2))), neg_neg]
    calc ∫ τ in Set.Iic (-T₀), ‖hatKernel X h c τ‖
        ≤ ∫ τ in Set.Iic (-T₀), 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) :=
          setIntegral_mono_on hInt.integrableOn hb2int.integrableOn measurableSet_Iic
            (fun τ _ => hatKernel_branch2 hX hh hc τ)
      _ = ∫ τ in Set.Ioi T₀, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + τ ^ 2)) := hcongr
      _ ≤ 2 * (X + h) ^ (c + 1) / (h * T₀) := hat_tail hX hh hc hT₀
      _ = (X + h) ^ c := hval
  have hsub : {τ : ℝ | T₀ < |τ|} ⊆ Set.Iic (-T₀) ∪ Set.Ioi T₀ := by
    intro τ hτ
    simp only [Set.mem_setOf_eq] at hτ
    rcases abs_cases τ with ⟨heq, _⟩ | ⟨heq, _⟩
    · right; rw [Set.mem_Ioi]; rw [heq] at hτ; exact hτ
    · left; rw [Set.mem_Iic]; rw [heq] at hτ; linarith
  have hdisj : Disjoint (Set.Iic (-T₀)) (Set.Ioi T₀) := Set.Iic_disjoint_Ioi (by linarith)
  calc (∫ τ in {τ : ℝ | T₀ < |τ|}, ‖hatKernel X h c τ‖)
      ≤ ∫ τ in Set.Iic (-T₀) ∪ Set.Ioi T₀, ‖hatKernel X h c τ‖ :=
        setIntegral_mono_set hInt.integrableOn
          (Filter.Eventually.of_forall (fun τ => norm_nonneg _)) hsub.eventuallyLE
    _ = (∫ τ in Set.Iic (-T₀), ‖hatKernel X h c τ‖) + ∫ τ in Set.Ioi T₀, ‖hatKernel X h c τ‖ :=
        setIntegral_union hdisj measurableSet_Ioi hInt.integrableOn hInt.integrableOn
    _ ≤ 2 * (X + h) ^ c := by linarith

/-- **Stone 6b — the tail cross-integral** (`tail_band_sum`).  With the crude leg sups
(`norm_windowSum_le_mass`, constant in `t`) and the exact tail-mass cancellation
(`kernel_tail_mass`), the `crossKer` tail is bounded by the product of the two window masses
times `2(X+h)^{c₀−α−β}` — the ramp-free tail grade (no `√L`). -/
theorem tail_band_sum {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    (∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * (2 * (X + h) ^ (c₀ - α - β)) := by
  set Mm : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) with hMm
  set Mp : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) with hMp
  have hMm0 : 0 ≤ Mm := Finset.sum_nonneg (fun n _ => by positivity)
  have hMp0 : 0 ≤ Mp := Finset.sum_nonneg (fun n _ => by positivity)
  have hS : MeasurableSet {t : ℝ | 2 * (X + h) / h < |t - t₀|} :=
    (isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)).measurableSet
  -- leg sups (constant in t)
  have hbm : ∀ t : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖ ≤ Mm := fun t => by
    rw [hMm]
    exact norm_windowSum_le_mass g X y (c₀ - β)
      (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp])
  have hbp : ∀ t : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mp := fun t => by
    rw [hMp]
    exact norm_windowSum_le_mass g X y (c₀ + β)
      (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp])
  -- integrability of the two integrands
  have hΦint : IntegrableOn (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      {t : ℝ | 2 * (X + h) / h < |t - t₀|} :=
    (crossKer_integrand_integrable hX hh hc).integrableOn
  have hKint : IntegrableOn (fun t : ℝ => Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      {t : ℝ | 2 * (X + h) / h < |t - t₀|} :=
    ((((integrable_hatKernel hX hh hc).comp_sub_right t₀).norm).const_mul (Mm * Mp)).integrableOn
  -- pointwise domination on the tail
  have hdom : ∀ t ∈ {t : ℝ | 2 * (X + h) / h < |t - t₀|},
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖
      ≤ Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := by
    intro t _
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact mul_le_mul (hbm t) (hbp t) (norm_nonneg _) hMm0
  -- change of variables: the tail kernel mass equals the τ-form (kernel_tail_mass)
  have hmp : MeasurePreserving (fun t : ℝ => t - t₀) volume volume :=
    measurePreserving_sub_right volume t₀
  have hme : MeasurableEmbedding (fun t : ℝ => t - t₀) :=
    (Homeomorph.subRight t₀).measurableEmbedding
  have hcov : (∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
        ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      = ∫ τ in {τ : ℝ | 2 * (X + h) / h < |τ|}, ‖hatKernel X h (c₀ - α - β) τ‖ := by
    rw [show {t : ℝ | 2 * (X + h) / h < |t - t₀|}
          = (fun t : ℝ => t - t₀) ⁻¹' {τ : ℝ | 2 * (X + h) / h < |τ|} from rfl]
    exact hmp.setIntegral_preimage_emb hme
      (fun τ => ‖hatKernel X h (c₀ - α - β) τ‖) {τ : ℝ | 2 * (X + h) / h < |τ|}
  calc (∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
          ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ ∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
          Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ :=
        setIntegral_mono_on hΦint hKint hS hdom
    _ = Mm * Mp * ∫ t in {t : ℝ | 2 * (X + h) / h < |t - t₀|},
          ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := integral_const_mul _ _
    _ = Mm * Mp * ∫ τ in {τ : ℝ | 2 * (X + h) / h < |τ|}, ‖hatKernel X h (c₀ - α - β) τ‖ := by
        rw [hcov]
    _ ≤ Mm * Mp * (2 * (X + h) ^ (c₀ - α - β)) :=
        mul_le_mul_of_nonneg_left (kernel_tail_mass hX hh hc) (by positivity)

/-! ## Residual — the `hband` discharge, and stones 5 and 7

Landed: the tail page (`head_split_ledger` + `tail_band_sum`, ramp-free at `2(X+h)^{c₀−α−β}`),
the width-`a` machinery (`widthA_plancherel` + `band_second_moment` + `offdiag_widthA_eval`),
and — new here — the SHARP `1/a` off-diagonal **analytic core** `offdiag_widthA_sharp`
(with `inner_sharp`, `geom_partial_le`, `inv_one_sub_exp_neg_le`), conditional on the per-band
`Λ`-mass datum `hband`.  Three rungs remain, each with its exact blocker:

* **The `hband` discharge (stone 8, the `y = √L` concession).**  `offdiag_widthA_sharp`'s
  hypothesis `hband n k` is dischargeable from `shortInterval_vonMangoldt_le` (`Cb = 250`) as
  follows.  The fiber `{m ∈ F, m < n : ⌊a·(log n − log m)⌋₊ = k}` equals `{m : Lₖ < m ≤ Rₖ}`
  with `Lₖ = n·e^{−(k+1)/a}`, `Rₖ = n·e^{−k/a}` (unpack `Nat.floor_eq_iff`), hence sits inside
  `Finset.Ioc ⌊Lₖ⌋₊ ⌊Lₖ + Hₖ⌋₊` with `Hₖ = Rₖ − Lₖ` (via `Nat.floor_lt` / `Nat.le_floor`, since
  `Lₖ + Hₖ = Rₖ`).  Then `∑_{fiber} ‖b_m‖ ≤ ∑_{fiber} Λ ≤ ∑_{Ioc} Λ ≤ 250·Hₖ` and
  `Hₖ = n·e^{−k/a}(1 − e^{−1/a}) ≤ (n/a)·e^{−k/a}` (`1 − e^{−x} ≤ x`), giving `hband` with
  `Cb = 250`.  The `shortInterval` REGIME needs (i) `65536 ≤ Lₖ`, (ii) `Hₖ ≤ Lₖ` (`e^{1/a} ≤ 2`,
  i.e. `a ≥ 2`), (iii) `Lₖ ≤ Hₖ·√√√Lₖ`, i.e. `Lₖ^{7/8} ≤ Hₖ ≍ Lₖ/a`, i.e. `a ≲ Lₖ^{1/8}` — the
  honest `a ≤ n^{1/8}` concession.  Bands out of regime (far `k`, where `Rₖ` drops below
  `65536`, or small `n ≤ a^8`) carry the CRUDE Chebyshev bound `∑_{m≤Rₖ} Λ ≤ (log 4 + 4)·Rₖ`
  per band (no `1/a`), summing to the `Θ(log a) = Θ(log log X)` bounded concession — EMPTY once
  the window floor `y ≥ a^8` (the y-gate: no `n < a^8` in `F`).  So the fully-discharged sharp
  form is `off-diagonal ≤ 4·250/(a−c+1)·(mass) + Cconc·[∃ n ∈ F, n ≤ a^8]`.  Building the
  regime split (the `√√√` threading + the additive concession restructure of `inner_sharp`) is
  the last research ledge; FLAGGED per iron rule 1 / SF-EXIT, not forced.

* **Stone 5 (`head_band_sum`)** — the head `∫_{|t−t₀|≤T₀}` via `mixed_weight_cs` at the branch-1
  weight `(X+h)^{c'}·2/√(c'²+τ²)`, evaluated by the dyadic band decomposition (`τ ~ 2^j`,
  `1/√(c'²+τ²) ≤ 2^{−j}`, `j ≤ J ≍ log₂ T₀`), `band_second_moment` + `widthA_plancherel` per
  band (`a = 2^{j+1}`), the diagonal `Σ_n ‖b_n‖²/n^{2c}`, and `offdiag_widthA_sharp` for the
  off-diagonal.  **Exponent page (worked):** band `j` prefactor `2^{−j}·2·(2^{j+1})²·(π/2^{j+1})
  = 4π·2^{j}`... `·(2^{−j})` from the branch-1 weight `= 4π`; the sharp off-diagonal per band is
  `4·250/(2^{j+1}−c+1)·mass ≍ C·mass·2^{−j}`, so `∑_j 4π·(C·mass·2^{−j})` TELESCOPES to `O(mass)
  = O(L)` (the geometric `∑ 2^{−j}`), while `∑_j 4π·diagonal = (J+1)·4π·diagonal` — the band
  count multiplies ONLY the diagonal floor `Σ_n ‖b_n‖²/n^{2c}` (the design's `log y/y`-grade
  datum, small for the window `n > y`).  Exit: `∫_{|τ|≤T₀} ‖P‖²/|s| ≤ C·L·mass + (J+1)·diagonal
  + concession`.  Blocked on the `hband` discharge (else the crude `offdiag_widthA_eval` leaves
  `O(J·L) = O(L·log log X)`).

* **Stone 7 (`crossKer_head_tail_grade`)** — the composite `crossKer ≤ (X+h)^{c₀−α−β}·C·L`
  feeding `JointHead.sigma_wiring`'s `Kα` socket, via `head_split_ledger`
  (`crossKer = head + tail`), stone 5's head bound through `mixed_weight_cs` at branch-1
  (`hatKernel_branch1`, weight `w = (X+h)^{c'}·2/√(c'²+τ²)`, the two legs `c₀∓β`), and
  `tail_band_sum`.  The low leg `c₀−β < 1` needs the `c ≥ 1` hypothesis of the sharp/crude
  off-diagonal relaxed (the assembly's shift step, per the landed `offdiag_window_eval` note).
  Blocked on stone 5.

Stone 8 (`ysqrtL_coda`) remains a flag — the `siegelWalfisz` PNT-lift alternative to the
concession is named as future work, not built. -/

/-! ## Stone D — discharging `hband` at the y-gate (`hband_discharge`, `offdiag_widthA_final`)

The last research ledge of the sharp off-diagonal, now discharged under the **y-gate**
`2·a^8 ≤ n` (every window element above `2 a^8`) with `4 ≤ a`.  `hband_discharge` proves the
per-band `Λ`-mass datum `hband` of `offdiag_widthA_sharp` unconditionally in that regime: each
nonempty fiber `{m ∈ F, m < n : ⌊a(log n − log m)⌋₊ = k}` sits inside the short interval
`Ioc ⌊Lₖ⌋₊ ⌊Lₖ+Hₖ⌋₊` (`Lₖ = n e^{−(k+1)/a}`, `Rₖ = n e^{−k/a}`, `Hₖ = Rₖ−Lₖ`), and the y-gate
puts every such interval in `shortInterval_vonMangoldt_le`'s regime (`65536 ≤ Lₖ`, `Hₖ ≤ Lₖ`,
`Lₖ ≤ Hₖ·√√√Lₖ`, using `Rₖ ≥ 2 a^8` from any fiber element, `e^{1/a} ≤ 2`, and `Lₖ ≥ a^8 ≥
65536`), giving `∑_{fiber}Λ ≤ C·Hₖ ≤ C·(n/a)e^{−k/a}`.  Fibers with no element are trivially
bounded — the y-gate makes them the ONLY out-of-regime case (the concession is EMPTY).
`offdiag_widthA_final` feeds this into `offdiag_widthA_sharp` and symmetrizes to the full
`m ≠ n` off-diagonal: `≤ 4·C/(a−c+1)·(single mass)`, the sharp `1/a` decay with no `hband`, no
concession.  `C` is `shortInterval_vonMangoldt_le`'s absolute constant (`= 250`).

The honest constant: `2 a^8` (not the flag's aspirational `a^8`) is the exact concession
threshold — the `factor 2` is the slack from `e^{1/a} ≤ 2`; it does not change the grade
(`1/(a−c+1) ≍ 1/a` decay intact). -/

/-- For a symmetric kernel `T`, the full `m ≠ n` off-diagonal is twice its strict lower part. -/
private lemma sum_ne_eq_two_lt {F : Finset ℕ} {T : ℕ → ℕ → ℝ}
    (hsymm : ∀ m n, T m n = T n m) :
    ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then T m n else 0)
      = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0) := by
  have hsplit : ∀ m n : ℕ, (if m ≠ n then T m n else 0)
      = (if m < n then T m n else 0) + (if n < m then T m n else 0) := by
    intro m n
    rcases lt_trichotomy m n with h | h | h
    · rw [if_pos (ne_of_lt h), if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_neg (by simp [h]), add_zero]
    · rw [if_pos (ne_of_gt h), if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  have hlow : ∑ m ∈ F, ∑ n ∈ F, (if n < m then T m n else 0)
      = ∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => by rw [hsymm n m]))
  calc ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then T m n else 0)
      = ∑ m ∈ F, ∑ n ∈ F, ((if m < n then T m n else 0) + (if n < m then T m n else 0)) :=
        Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hsplit m n))
    _ = (∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0))
          + ∑ m ∈ F, ∑ n ∈ F, (if n < m then T m n else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun m _ => by rw [Finset.sum_add_distrib])
    _ = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m < n then T m n else 0) := by rw [hlow]; ring

/-- **Stone D core — the `hband` discharge at the y-gate** (`hband_discharge`).  For `4 ≤ a`,
`Λ`-bounded coefficients, and the y-gate `2·a^8 ≤ n` on `F`, the per-band `Λ`-mass datum of
`offdiag_widthA_sharp` holds with the absolute constant `C` of `shortInterval_vonMangoldt_le`:
every nonempty fiber is a short interval in regime; empty fibers are trivial. -/
theorem hband_discharge {F : Finset ℕ} {b : ℕ → ℂ} {a : ℝ} (ha4 : 4 ≤ a)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * a ^ 8 ≤ (n : ℝ)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ n ∈ F, ∀ k : ℕ,
      (∑ m ∈ (F.filter (· < n)).filter
          (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k), ‖b m‖)
        ≤ Cb * (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by
  obtain ⟨C, hC0, hCbound⟩ := shortInterval_vonMangoldt_le
  have ha0 : (0 : ℝ) < a := by linarith
  -- e^{1/a} ≤ 2 for a ≥ 4
  have hexp_le2 : Real.exp (1 / a) ≤ 2 := by
    have h14 : (1 : ℝ) / a ≤ 1 / 2 := by
      rw [div_le_div_iff₀ ha0 (by norm_num)]; linarith
    have he12 : Real.exp (1 / 2 : ℝ) < 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [hsq, Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
    calc Real.exp (1 / a) ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr h14
      _ ≤ 2 := le_of_lt he12
  refine ⟨C, hC0, fun n hn k => ?_⟩
  have hn1 : 1 ≤ n := hF n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnY : 2 * a ^ 8 ≤ (n : ℝ) := hygate n hn
  set Rk : ℝ := (n : ℝ) * Real.exp (-((k : ℝ) / a)) with hRkdef
  set Lk : ℝ := (n : ℝ) * Real.exp (-(((k : ℝ) + 1) / a)) with hLkdef
  have hLk0 : (0 : ℝ) < Lk := by rw [hLkdef]; exact mul_pos hn0 (Real.exp_pos _)
  have hRk0 : (0 : ℝ) < Rk := by rw [hRkdef]; exact mul_pos hn0 (Real.exp_pos _)
  have hRL : Rk = Lk * Real.exp (1 / a) := by
    rw [hLkdef, hRkdef, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hLkRk2 : Lk = Rk * Real.exp (-(1 / a)) := by
    rw [hLkdef, hRkdef, mul_assoc, ← Real.exp_add]; congr 2; ring
  set Fib := (F.filter (· < n)).filter
      (fun m : ℕ => ⌊a * (Real.log (n : ℝ) - Real.log (m : ℝ))⌋₊ = k) with hFibdef
  -- each fiber element lies in (Lk, Rk]
  have hmem : ∀ m ∈ Fib, Lk < (m : ℝ) ∧ (m : ℝ) ≤ Rk := by
    intro m hm
    rw [hFibdef, Finset.mem_filter, Finset.mem_filter] at hm
    obtain ⟨⟨hmF, hmn⟩, hk⟩ := hm
    have hm1 : 1 ≤ m := hF m hmF
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hloglt : Real.log (m : ℝ) < Real.log (n : ℝ) :=
      Real.log_lt_log hm0 (by exact_mod_cast hmn)
    have hx0 : (0 : ℝ) ≤ a * (Real.log (n : ℝ) - Real.log (m : ℝ)) :=
      mul_nonneg ha0.le (by linarith)
    obtain ⟨hkle, hklt⟩ := (Nat.floor_eq_iff hx0).mp hk
    refine ⟨?_, ?_⟩
    · -- Lk < (m:ℝ)
      have hlt2 : Real.log (n : ℝ) - Real.log (m : ℝ) < ((k : ℝ) + 1) / a := by
        rw [lt_div_iff₀ ha0, mul_comm]; linarith [hklt]
      have hlogm_gt : Real.log (n : ℝ) - ((k : ℝ) + 1) / a < Real.log (m : ℝ) := by linarith
      rw [hLkdef]
      calc (n : ℝ) * Real.exp (-(((k : ℝ) + 1) / a))
          = Real.exp (Real.log (n : ℝ) - ((k : ℝ) + 1) / a) := by
            rw [show Real.log (n : ℝ) - ((k : ℝ) + 1) / a
                  = Real.log (n : ℝ) + (-(((k : ℝ) + 1) / a)) from by ring,
              Real.exp_add, Real.exp_log hn0]
        _ < Real.exp (Real.log (m : ℝ)) := Real.exp_lt_exp.mpr hlogm_gt
        _ = (m : ℝ) := Real.exp_log hm0
    · -- (m:ℝ) ≤ Rk
      have hge2 : (k : ℝ) / a ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
        rw [div_le_iff₀ ha0, mul_comm]; linarith [hkle]
      have hlogm_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) - (k : ℝ) / a := by linarith
      rw [hRkdef]
      calc (m : ℝ) = Real.exp (Real.log (m : ℝ)) := (Real.exp_log hm0).symm
        _ ≤ Real.exp (Real.log (n : ℝ) - (k : ℝ) / a) := Real.exp_le_exp.mpr hlogm_le
        _ = (n : ℝ) * Real.exp (-((k : ℝ) / a)) := by
            rw [show Real.log (n : ℝ) - (k : ℝ) / a
                  = Real.log (n : ℝ) + (-((k : ℝ) / a)) from by ring,
              Real.exp_add, Real.exp_log hn0]
  -- fiber ⊆ Ioc ⌊Lk⌋₊ ⌊Rk⌋₊
  have hsub : Fib ⊆ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊ := by
    intro m hm
    obtain ⟨hlo, hhi⟩ := hmem m hm
    rw [Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hLk0.le).mpr hlo, Nat.le_floor hhi⟩
  -- the fiber Λ-mass ≤ the interval Λ-mass
  have hfib_le : (∑ m ∈ Fib, ‖b m‖)
      ≤ ∑ m ∈ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊, ArithmeticFunction.vonMangoldt m := by
    calc (∑ m ∈ Fib, ‖b m‖) ≤ ∑ m ∈ Fib, ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum (fun m _ => hb m)
      _ ≤ ∑ m ∈ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊, ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hRHS0 : (0 : ℝ) ≤ C * (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) :=
    mul_nonneg (div_nonneg (mul_nonneg hC0 hn0.le) ha0.le) (Real.exp_nonneg _)
  -- Hk ≤ (n/a) e^{-k/a}
  have h1me : 1 - Real.exp (-(1 / a)) ≤ 1 / a := by linarith [Real.add_one_le_exp (-(1 / a))]
  have hHk_bound : Rk - Lk ≤ (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by
    rw [hLkRk2]
    have hfac : Rk - Rk * Real.exp (-(1 / a)) = Rk * (1 - Real.exp (-(1 / a))) := by ring
    rw [hfac]
    calc Rk * (1 - Real.exp (-(1 / a))) ≤ Rk * (1 / a) :=
          mul_le_mul_of_nonneg_left h1me hRk0.le
      _ = (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by rw [hRkdef]; ring
  rcases Finset.eq_empty_or_nonempty Fib with hE | ⟨m₀, hm₀⟩
  · rw [hE, Finset.sum_empty]; exact hRHS0
  · have hm₀' := hm₀
    rw [hFibdef, Finset.mem_filter, Finset.mem_filter] at hm₀'
    obtain ⟨⟨hm₀F, -⟩, -⟩ := hm₀'
    have hRkY : 2 * a ^ 8 ≤ Rk := le_trans (hygate m₀ hm₀F) (hmem m₀ hm₀).2
    have ha8_65536 : (65536 : ℝ) ≤ a ^ 8 := by
      calc (65536 : ℝ) = 4 ^ 8 := by norm_num
        _ ≤ a ^ 8 := by gcongr
    -- Lk ≥ a^8
    have hLk_ge_a8 : a ^ 8 ≤ Lk := by
      have hLkRk : Lk = Rk / Real.exp (1 / a) := by
        rw [hRL, mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]
      rw [hLkRk, le_div_iff₀ (Real.exp_pos _)]
      linarith [hRkY, mul_le_mul_of_nonneg_left hexp_le2 (pow_nonneg ha0.le 8)]
    have hLk_65536 : (65536 : ℝ) ≤ Lk := le_trans ha8_65536 hLk_ge_a8
    -- Hk ≤ Lk
    have hHa : Rk - Lk ≤ Lk := by
      have h2 : Lk * Real.exp (1 / a) ≤ Lk * 2 := mul_le_mul_of_nonneg_left hexp_le2 hLk0.le
      rw [hRL]; linarith [h2]
    -- Hk ≥ Lk / a
    have hHk_ge : Lk / a ≤ Rk - Lk := by
      have hEexp : 1 / a + 1 ≤ Real.exp (1 / a) := Real.add_one_le_exp (1 / a)
      have hkey : Lk / a ≤ Lk * (Real.exp (1 / a) - 1) := by
        rw [div_eq_mul_inv, ← one_div]
        exact mul_le_mul_of_nonneg_left (by linarith [hEexp]) hLk0.le
      calc Lk / a ≤ Lk * (Real.exp (1 / a) - 1) := hkey
        _ = Rk - Lk := by rw [hRL]; ring
    -- Lk ≤ Hk · √√√Lk
    have hs8 : Real.sqrt (Real.sqrt (Real.sqrt Lk)) ^ 8 = Lk := by
      set s := Real.sqrt (Real.sqrt (Real.sqrt Lk)) with hs
      have h2 : s ^ 2 = Real.sqrt (Real.sqrt Lk) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have h4 : s ^ 4 = Real.sqrt Lk := by
        have hpow : s ^ 4 = (s ^ 2) ^ 2 := by ring
        rw [hpow, h2, Real.sq_sqrt (Real.sqrt_nonneg _)]
      have hpow8 : s ^ 8 = (s ^ 4) ^ 2 := by ring
      rw [hpow8, h4, Real.sq_sqrt hLk0.le]
    have hsa : a ≤ Real.sqrt (Real.sqrt (Real.sqrt Lk)) :=
      le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (Real.sqrt_nonneg _)
        (by rw [hs8]; exact hLk_ge_a8)
    have hHr : Lk ≤ (Rk - Lk) * Real.sqrt (Real.sqrt (Real.sqrt Lk)) := by
      calc Lk = Lk / a * a := by field_simp
        _ ≤ Lk / a * Real.sqrt (Real.sqrt (Real.sqrt Lk)) :=
            mul_le_mul_of_nonneg_left hsa (div_nonneg hLk0.le ha0.le)
        _ ≤ (Rk - Lk) * Real.sqrt (Real.sqrt (Real.sqrt Lk)) :=
            mul_le_mul_of_nonneg_right hHk_ge (Real.sqrt_nonneg _)
    have hshort := hCbound Lk (Rk - Lk) hLk_65536 hHr hHa
    have hfloor : ⌊Lk + (Rk - Lk)⌋₊ = ⌊Rk⌋₊ := by congr 1; ring
    rw [hfloor] at hshort
    calc (∑ m ∈ Fib, ‖b m‖)
        ≤ ∑ m ∈ Finset.Ioc ⌊Lk⌋₊ ⌊Rk⌋₊, ArithmeticFunction.vonMangoldt m := hfib_le
      _ ≤ C * (Rk - Lk) := hshort
      _ ≤ C * ((n : ℝ) / a * Real.exp (-((k : ℝ) / a))) :=
          mul_le_mul_of_nonneg_left hHk_bound hC0
      _ = C * (n : ℝ) / a * Real.exp (-((k : ℝ) / a)) := by ring

/-- **Stone D — the fully-discharged sharp off-diagonal at the y-gate** (`offdiag_widthA_final`).
Under the y-gate `2·a^8 ≤ n`, `1 ≤ c ≤ a`, `4 ≤ a`, and `Λ`-bounded coefficients, the FULL
off-diagonal (`m ≠ n`) norm sum carries the sharp `1/(a−c+1) ≍ 1/a` decay with NO `hband`, NO
concession: `∑_{m≠n∈F} ‖b_m‖‖b_n‖/(mn)^c·e^{−a|log m−log n|} ≤ 4·C/(a−c+1)·∑_{n∈F} ‖b_n‖/n^c`,
`C` the absolute constant of `shortInterval_vonMangoldt_le` (`= 250`). -/
theorem offdiag_widthA_final {F : Finset ℕ} {b : ℕ → ℂ} {c a : ℝ}
    (hc : 1 ≤ c) (hca : c ≤ a) (ha4 : 4 ≤ a)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * a ^ 8 ≤ (n : ℝ)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      (∑ m ∈ F, ∑ n ∈ F, if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)) else 0)
        ≤ 4 * Cb / (a - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
  obtain ⟨C, hC0, hband⟩ := hband_discharge ha4 hF hb hygate
  refine ⟨C, hC0, ?_⟩
  have hsharp := offdiag_widthA_sharp hc hca hF hC0 hband
  have hsymm : ∀ m n : ℕ,
      ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c * Real.exp (-(a * |Real.log m - Real.log n|))
        = ‖b n‖ * ‖b m‖ / ((n * m : ℕ) : ℝ) ^ c
            * Real.exp (-(a * |Real.log n - Real.log m|)) := by
    intro m n
    rw [mul_comm (‖b m‖) (‖b n‖), Nat.mul_comm m n, abs_sub_comm (Real.log m) (Real.log n)]
  calc (∑ m ∈ F, ∑ n ∈ F, if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)) else 0)
      = 2 * ∑ m ∈ F, ∑ n ∈ F, (if m < n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(a * |Real.log m - Real.log n|)) else 0) := sum_ne_eq_two_lt hsymm
    _ ≤ 2 * (2 * C / (a - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left hsharp (by norm_num)
    _ = 4 * C / (a - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by ring

/-! ## Stone 5 — the head weighted second moment (`head_second_moment_grade`)

The branch-1 weighted second moment of the window Dirichlet polynomial over the head band
`|τ| ≤ T₀`, evaluated to `C·mass` (off-diagonal) + `T₀·diagonal` (diagonal floor).  This is the
DIRECT route (`band_second_moment` at width `T₀`), not the dyadic annulus decomposition: the
crude `1/√(cw²+τ²) ≤ 1/cw` on the whole band, then `band_second_moment` (width `a = T₀`) +
`widthA_plancherel` + the diagonal/off-diagonal split with `offdiag_widthA_final`.  Cost vs. the
dyadic sharpening: the diagonal factor is `T₀ ≍ √L` rather than the sharp `(J+1) ≍ log L`.  This
is NOT load-bearing: the window diagonal `∑_n ‖b_n‖²/n^{2c} ≍ (log y)²/y` is astronomically small
under the y-gate `n ≥ 2 T₀^8 ≍ L^4` (so `y ≳ L^4`), whence even `√L·diagonal` is negligible — the
constant-`X` grade lands either way.  The off-diagonal `1/(a−c+1)` decay (from
`offdiag_widthA_final`) is what removes the `log log X`; that is what mattered.

Exit: `∫_{|τ|≤T₀} ‖P(c+iτ)‖²/√(cw²+τ²) ≤ (2π T₀/cw)·(diagonal + 4·C/(T₀−c+1)·mass)`, `C` the
absolute `shortInterval` constant — the shape `stone 7` feeds through `mixed_weight_cs` at the
branch-1 weight (`cw = c₀−α−β`). -/
theorem head_second_moment_grade {F : Finset ℕ} {b : ℕ → ℂ} {c cw T₀ : ℝ}
    (hc : 1 ≤ c) (hcw : 0 < cw) (hT₀ : 4 ≤ T₀) (hcT : c ≤ T₀)
    (hF : ∀ n ∈ F, 1 ≤ n) (hb : ∀ n, ‖b n‖ ≤ ArithmeticFunction.vonMangoldt n)
    (hygate : ∀ n ∈ F, 2 * T₀ ^ 8 ≤ (n : ℝ)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      (∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
        ≤ 2 * Real.pi * T₀ / cw
            * ((∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
              + 4 * Cb / (T₀ - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) := by
  have hT₀0 : (0 : ℝ) < T₀ := by linarith
  obtain ⟨C, hC0, hoff⟩ := offdiag_widthA_final hc hcT hT₀ hF hb hygate
  have hden_pos : ∀ τ : ℝ, (0 : ℝ) < cw ^ 2 + τ ^ 2 := fun τ => by
    have h := pow_pos hcw 2; linarith [sq_nonneg τ]
  have hPcont : Continuous (fun τ : ℝ => ∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)) :=
    continuous_dirichletPoly F b c hF
  have hcw_le_sqrt : ∀ τ : ℝ, cw ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ =>
    calc cw = Real.sqrt (cw ^ 2) := (Real.sqrt_sq hcw.le).symm
      _ ≤ Real.sqrt (cw ^ 2 + τ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg τ])
  -- integrability on the band
  have hIntW : IntegrableOn (fun τ : ℝ =>
      ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      (Set.Icc (-T₀) T₀) :=
    ((hPcont.norm.pow 2).div (Real.continuous_sqrt.comp (by fun_prop))
      (fun τ => (Real.sqrt_pos.mpr (hden_pos τ)).ne')).integrableOn_Icc
  have hIntQ : IntegrableOn (fun τ : ℝ =>
      cw⁻¹ * ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2)
      (Set.Icc (-T₀) T₀) :=
    (continuous_const.mul (hPcont.norm.pow 2)).integrableOn_Icc
  -- step 1: 1/√ ≤ 1/cw, integrate
  have hstep1 : (∫ τ in Set.Icc (-T₀) T₀,
        ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ cw⁻¹ * ∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hIntW hIntQ measurableSet_Icc (fun τ _ => ?_)
    calc ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2)
        ≤ ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / cw :=
          div_le_div_of_nonneg_left (by positivity) hcw (hcw_le_sqrt τ)
      _ = cw⁻¹ * ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := div_eq_inv_mul _ _
  -- band second moment + width-`T₀` Plancherel
  have hbsm := band_second_moment F b (c := c) hT₀0 hF
  have hplanch := widthA_plancherel F b (c := c) hT₀0 hF
  -- the norm-kernel diagonal/off-diagonal split, dominating the Plancherel `.re` sum
  have hRe_le_K : ∀ m n : ℕ,
      (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(T₀ * |Real.log m - Real.log n|))
        ≤ ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(T₀ * |Real.log m - Real.log n|)) := by
    intro m n
    have hre : (b m * starRingEnd ℂ (b n)).re ≤ ‖b m‖ * ‖b n‖ := by
      have h1 := Complex.re_le_norm (b m * starRingEnd ℂ (b n))
      rwa [norm_mul, Complex.norm_conj] at h1
    have hE : (0 : ℝ) ≤ (((m * n : ℕ) : ℝ) ^ c)⁻¹
        * Real.exp (-(T₀ * |Real.log m - Real.log n|)) := by positivity
    calc (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(T₀ * |Real.log m - Real.log n|))
        = (b m * starRingEnd ℂ (b n)).re
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(T₀ * |Real.log m - Real.log n|))) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ‖b m‖ * ‖b n‖
            * ((((m * n : ℕ) : ℝ) ^ c)⁻¹ * Real.exp (-(T₀ * |Real.log m - Real.log n|))) :=
          mul_le_mul_of_nonneg_right hre hE
      _ = ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(T₀ * |Real.log m - Real.log n|)) := by rw [div_eq_mul_inv]; ring
  have hper_m : ∀ m ∈ F,
      (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(T₀ * |Real.log m - Real.log n|)))
        = ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c
          + ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(T₀ * |Real.log m - Real.log n|)) else 0) := by
    intro m hm
    have he1 : (∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(T₀ * |Real.log m - Real.log n|)))
        = ∑ n ∈ F, ((if m = n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(T₀ * |Real.log m - Real.log n|)) else 0)
            + (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(T₀ * |Real.log m - Real.log n|)) else 0)) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : m = n
      · rw [if_pos h, if_neg (by simp [h]), add_zero]
      · rw [if_neg h, if_pos h, zero_add]
    rw [he1, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq F m (fun n => ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
        * Real.exp (-(T₀ * |Real.log m - Real.log n|))), if_pos hm,
      sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, ← pow_two]
  have hKsplit : (∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(T₀ * |Real.log m - Real.log n|)))
        = (∑ m ∈ F, ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c)
          + ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(T₀ * |Real.log m - Real.log n|)) else 0) := by
    rw [Finset.sum_congr rfl hper_m, Finset.sum_add_distrib]
  have hfinal_planch : (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
          * Real.exp (-(T₀ * |Real.log m - Real.log n|)))
        ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
          + 4 * C / (T₀ - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c := by
    calc (∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(T₀ * |Real.log m - Real.log n|)))
        ≤ ∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
            * Real.exp (-(T₀ * |Real.log m - Real.log n|)) :=
          Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hRe_le_K m n))
      _ = (∑ m ∈ F, ‖b m‖ ^ 2 / ((m * m : ℕ) : ℝ) ^ c)
            + ∑ m ∈ F, ∑ n ∈ F, (if m ≠ n then ‖b m‖ * ‖b n‖ / ((m * n : ℕ) : ℝ) ^ c
                * Real.exp (-(T₀ * |Real.log m - Real.log n|)) else 0) := hKsplit
      _ ≤ (∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
            + 4 * C / (T₀ - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c :=
          add_le_add le_rfl hoff
  have hpref0 : (0 : ℝ) ≤ 2 * Real.pi * T₀ / cw :=
    div_nonneg (by positivity) hcw.le
  refine ⟨C, hC0, ?_⟩
  calc (∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ cw⁻¹ * ∫ τ in Set.Icc (-T₀) T₀,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 := hstep1
    _ ≤ cw⁻¹ * (2 * T₀ ^ 2 * ∫ τ : ℝ,
          ‖∑ n ∈ F, b n / (n : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I)‖ ^ 2 / (T₀ ^ 2 + τ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbsm (inv_nonneg.mpr hcw.le)
    _ = cw⁻¹ * (2 * T₀ ^ 2 * (Real.pi / T₀
          * ∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(T₀ * |Real.log m - Real.log n|)))) := by rw [hplanch]
    _ = 2 * Real.pi * T₀ / cw
          * ∑ m ∈ F, ∑ n ∈ F, (b m * starRingEnd ℂ (b n)).re / ((m * n : ℕ) : ℝ) ^ c
              * Real.exp (-(T₀ * |Real.log m - Real.log n|)) := by
        rw [show (2 : ℝ) * Real.pi * T₀ / cw
              = cw⁻¹ * (2 * T₀ ^ 2 * (Real.pi / T₀)) from by field_simp]
        ring
    _ ≤ 2 * Real.pi * T₀ / cw
          * ((∑ n ∈ F, ‖b n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ c)
            + 4 * C / (T₀ - c + 1) * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left hfinal_planch hpref0

/-! ## Stone 7 — the `crossKer` head/tail grade (`crossKer_head_tail_grade`)

The composite feed for `JointHead.sigma_wiring`'s `Kα` socket.  `head_split_ledger` splits
`crossKer` at the branch crossover `T₀ = 2(X+h)/h` into head (`|t−t₀| ≤ T₀`, branch-1) + tail
(`|t−t₀| > T₀`, branch-2); `tail_band_sum` discharges the tail EXACTLY to the ramp-free
`(window masses)·2(X+h)^{c₀−α−β}` (RAMP-TAIL's cancellation).  The head is fed by a bound
`Hbound` — the `mixed_weight_cs` (`JointHead`) + `head_second_moment_grade` route: at the
branch-1 weight `‖hatKernel‖ ≤ (X+h)^{c'}·2/√(c'²+τ²)` (`hatKernel_branch1`), CS on the head
band separates the two window legs, and `head_second_moment_grade` grades each leg's restricted
second moment to `C·mass` (off-diagonal, the `1/(a−c+1)` decay from `offdiag_widthA_final`) plus
the tiny window diagonal — NO `√L` ramp.  So `crossKer α β ≤ Hbound + (masses)·2(X+h)^{c₀−α−β}`,
the ramp-free grade.

**The head socket `Hbound` is the last plumbing** (the honest residual, FLAGGED per iron rule 4):
its discharge threads (i) `mixed_weight_cs` on the RESTRICTED band `|τ| ≤ T₀` (the `L²` sockets
`k4Poly_sqInt` on the head-indicator-restricted legs — the measure-theoretic plumbing), (ii) the
change of variables `t ↦ t−t₀`, and (iii) `head_second_moment_grade` at the two lines `c₀∓β`.
The LOW leg `c₀−β < 1` (for `β > 1/L`) violates `head_second_moment_grade`'s / `offdiag_widthA_
final`'s `1 ≤ c` — the named `c ≥ 1`-relaxation route (a monotonicity shift `‖b_n‖/n^{c₀−β} ≤
‖b_n‖/n^{max(c₀−β,1)}·(X/y)^{(1−c₀+β)₊}` on the window `n < X/y`, absorbing the excess into the
`(X/y)^{2β}` the S-ladder already carries).  Building that restricted-CS + low-leg shift is the
terminal assembly's remaining ledge; the τ-split composition and the ramp-free tail stand here. -/
theorem crossKer_head_tail_grade {g : ℕ → ℂ} {X h y c₀ t₀ α β Hbound : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β)
    (hhead : (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) ≤ Hbound) :
    crossKer g X h y c₀ t₀ α β
      ≤ Hbound
        + (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
              ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
              ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * (2 * (X + h) ^ (c₀ - α - β)) := by
  rw [head_split_ledger hX hh hc]
  exact add_le_add hhead (tail_band_sum hX hh hc)

/-! ## Stone 7-close — the head socket discharged, `crossKer` at grade (`crossKer_grade_final`)

The head socket `Hbound` of `crossKer_head_tail_grade` — the last plumbing — closed by the
**ramp-free branch-1 route**.  The `√L` ramp of `crossKer` was an artifact of using the DOMINANT
(Poisson, `1/‖s‖²`) branch of `hat_mellin_bound` on the full line; on the HEAD band `|τ| ≤ T₀` the
branch-1 (`2/‖s‖`) weight (`hatKernel_branch1`) gives the `arsinh` mass `4(X+h)^{cw}·arsinh(T₀/cw)`
(`integral_inv_sqrt_c_sq_add`, the same antiderivative `kernel_L1_mass_sharp` used), which is
`Θ(log L)` — NO ramp.  The two window legs are bounded pointwise by their `n^{−c}`-weighted masses
(`norm_windowSum_le_mass`, constant in `t`, valid at ANY line — so the low-leg `c₀−β < 1` incurs no
`c ≥ 1` obstruction: the crude mass bound needs no monotonicity shift), leaving the kernel head
mass as the only surviving integral.  The τ-split composition (`crossKer_head_tail_grade`) then adds
the exact ramp-free tail (`tail_band_sum`, `2(X+h)^{cw}`), giving the closed form

  `crossKer α β ≤ Mm·Mp·(X+h)^{c₀−α−β}·(4·arsinh(2(X+h)/h / (c₀−α−β)) + 2)`,

`Mm, Mp` the two window masses at the legs `c₀∓β` — UNCONDITIONAL at the branch crossover, no
y-gate, no `hband`.  This is the honest ramp-free grade `Mm·Mp·(X+h)^{cw}·Θ(log L)`; the sharper
`mass² → mass` and `log L → O(1)` (via `head_second_moment_grade`'s `1/a` off-diagonal decay + the
low-leg shift) is the separate grade-sharpening ledge — NOT needed to close the socket. -/

/-- **The kernel head-band mass** (`kernel_head_mass`).  On the head band `|τ| ≤ T`, the branch-1
(`2/‖s‖`) weight of `hat_mellin_bound` (`hatKernel_branch1`) integrates to the `arsinh` mass:
`∫_{|τ|≤T} ‖hatKernel X h c τ‖ dτ ≤ (X+h)^c·4·arsinh(T/c)` — `Θ(log L)`, NO `√L` ramp.  The middle
part of `kernel_L1_mass_sharp`, isolated for the head. -/
theorem kernel_head_mass {X h c T : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c)
    (hT : (0 : ℝ) ≤ T) :
    (∫ τ in Set.Icc (-T) T, ‖hatKernel X h c τ‖)
      ≤ (X + h) ^ c * (4 * Real.arsinh (T / c)) := by
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hInt : Integrable (fun t : ℝ => ‖hatKernel X h c t‖) := (integrable_hatKernel hX hh hc).norm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTle]
  have hKcont : IntervalIntegrable (fun t : ℝ => ‖hatKernel X h c t‖) volume (-T) T :=
    hInt.intervalIntegrable
  have hbr1 : IntervalIntegrable
      (fun t : ℝ => (X + h) ^ c * 2 * (Real.sqrt (c ^ 2 + t ^ 2))⁻¹) volume (-T) T := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply Continuous.inv₀
    · exact Real.continuous_sqrt.comp (by fun_prop)
    · intro t; positivity
  calc ∫ t in (-T)..T, ‖hatKernel X h c t‖
      ≤ ∫ t in (-T)..T, (X + h) ^ c * 2 * (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ :=
        intervalIntegral.integral_mono_on hTle hKcont hbr1
          (fun t _ => hatKernel_branch1 hX hh hc t)
    _ = (X + h) ^ c * 2 * ∫ t in (-T)..T, (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ :=
        intervalIntegral.integral_const_mul _ _
    _ = (X + h) ^ c * 2 * (2 * Real.arsinh (T / c)) := by rw [integral_inv_sqrt_c_sq_add hc]
    _ = (X + h) ^ c * (4 * Real.arsinh (T / c)) := by ring

/-- **The head socket discharged** (`head_integral_discharged`).  The head integral of
`crossKer_head_tail_grade` — the branch-1 band `|t − t₀| ≤ T₀ := 2(X+h)/h` — is bounded by the two
window masses times the ramp-free kernel head mass `4(X+h)^{c₀−α−β}·arsinh(T₀/(c₀−α−β))`.  The
window legs go pointwise to their masses (`norm_windowSum_le_mass`, valid at BOTH lines `c₀∓β`, low
leg included — no `c ≥ 1` needed), the CoV `t ↦ t−t₀` reduces the kernel to the τ-form, and
`kernel_head_mass` closes.  This is exactly the `hhead` hypothesis of `crossKer_head_tail_grade`. -/
theorem head_integral_discharged {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * (4 * (X + h) ^ (c₀ - α - β)
              * Real.arsinh (2 * (X + h) / h / (c₀ - α - β))) := by
  set Mm : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) with hMm
  set Mp : ℝ := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) with hMp
  have hMm0 : 0 ≤ Mm := Finset.sum_nonneg (fun n _ => by positivity)
  have hMp0 : 0 ≤ Mp := Finset.sum_nonneg (fun n _ => by positivity)
  have hXh : (0 : ℝ) < X + h := by linarith
  have hT₀0 : (0 : ℝ) ≤ 2 * (X + h) / h := by positivity
  have hS : MeasurableSet {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h} :=
    (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet
  have hbm : ∀ t : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖ ≤ Mm := fun t => by
    rw [hMm]
    exact norm_windowSum_le_mass g X y (c₀ - β)
      (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp])
  have hbp : ∀ t : ℝ,
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mp := fun t => by
    rw [hMp]
    exact norm_windowSum_le_mass g X y (c₀ + β)
      (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp])
  have hΦint : IntegrableOn (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h} :=
    (crossKer_integrand_integrable hX hh hc).integrableOn
  have hKint : IntegrableOn (fun t : ℝ => Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h} :=
    ((((integrable_hatKernel hX hh hc).comp_sub_right t₀).norm).const_mul (Mm * Mp)).integrableOn
  have hdom : ∀ t ∈ {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖
      ≤ Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := by
    intro t _
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact mul_le_mul (hbm t) (hbp t) (norm_nonneg _) hMm0
  have hmp : MeasurePreserving (fun t : ℝ => t - t₀) volume volume :=
    measurePreserving_sub_right volume t₀
  have hme : MeasurableEmbedding (fun t : ℝ => t - t₀) :=
    (Homeomorph.subRight t₀).measurableEmbedding
  have hcov : (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
        ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      = ∫ τ in {τ : ℝ | |τ| ≤ 2 * (X + h) / h}, ‖hatKernel X h (c₀ - α - β) τ‖ := by
    rw [show {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h}
          = (fun t : ℝ => t - t₀) ⁻¹' {τ : ℝ | |τ| ≤ 2 * (X + h) / h} from rfl]
    exact hmp.setIntegral_preimage_emb hme
      (fun τ => ‖hatKernel X h (c₀ - α - β) τ‖) {τ : ℝ | |τ| ≤ 2 * (X + h) / h}
  have hIcc : {τ : ℝ | |τ| ≤ 2 * (X + h) / h}
      = Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h) := by
    ext τ; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  calc (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
          ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ ∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
          Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ :=
        setIntegral_mono_on hΦint hKint hS hdom
    _ = Mm * Mp * ∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
          ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := integral_const_mul _ _
    _ = Mm * Mp * ∫ τ in {τ : ℝ | |τ| ≤ 2 * (X + h) / h}, ‖hatKernel X h (c₀ - α - β) τ‖ := by
        rw [hcov]
    _ = Mm * Mp * ∫ τ in Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h),
          ‖hatKernel X h (c₀ - α - β) τ‖ := by rw [hIcc]
    _ ≤ Mm * Mp * (4 * (X + h) ^ (c₀ - α - β)
          * Real.arsinh (2 * (X + h) / h / (c₀ - α - β))) :=
        mul_le_mul_of_nonneg_left
          ((kernel_head_mass hX hh hc hT₀0).trans_eq (by ring)) (mul_nonneg hMm0 hMp0)

/-- **`crossKer` at grade — the head discharged, unconditional at the crossover**
(`crossKer_grade_final`).  Composing `head_integral_discharged` (ramp-free head, `Hbound` supplied)
with `crossKer_head_tail_grade` (τ-split + the exact ramp-free tail `tail_band_sum`) closes
`crossKer` to the explicit ramp-free form

  `crossKer g X h y c₀ t₀ α β
      ≤ Mm·Mp·(X+h)^{c₀−α−β}·(4·arsinh(2(X+h)/h / (c₀−α−β)) + 2)`,

`Mm, Mp` the window masses `∑_{y<n<X/y} ‖lambdaLin (restrictAbove y g) n‖/n^{c₀∓β}`.  UNCONDITIONAL
in `1 ≤ X`, `0 < h`, `0 < c₀−α−β` — no y-gate, no `hband`, no `c ≥ 1`.  The `√L` ramp is GONE (the
kernel mass is `Θ(log L)` via the branch-1 `arsinh`, not `Θ(√L)` via the full-line Poisson mass);
this is the `Kα` socket feed for `JointHead.sigma_wiring` at the ramp-free grade `Mm·Mp·(X+h)^{cw}·
Θ(log L)`. -/
theorem crossKer_grade_final {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    crossKer g X h y c₀ t₀ α β
      ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * ((X + h) ^ (c₀ - α - β)
              * (4 * Real.arsinh (2 * (X + h) / h / (c₀ - α - β)) + 2)) := by
  have hmain := crossKer_head_tail_grade (g := g) (y := y) (t₀ := t₀) hX hh hc
    (head_integral_discharged (g := g) (y := y) (t₀ := t₀) hX hh hc)
  exact hmain.trans_eq (by ring)

/-! ## Stone L — the low-leg window-monotonicity shift (`low_leg_shift`)

The sharp per-leg second moment `head_second_moment_grade` needs a line `1 ≤ c`; the LOW leg of
`crossKer` sits at `c' = c₀−β`, which drops below `1` once `β > c₀−1`.  This wrapper carries the
excess: on the window `n ≤ Q := X/y`, the sub-unit mass `∑ ‖b_n‖/n^{c'}` is bounded by the
line-`1` mass times the excess factor `Q^{1−c'}`, via `n^{−c'} = n^{−1}·n^{1−c'} ≤ n^{−1}·Q^{1−c'}`
(`n ≤ Q`, `1−c' ≥ 0`).  The `Q^{1−c'} = (X/y)^{1−c₀+β}`-grade factor is carried EXPLICITLY into the
sharp exit — the S-ladder's `(X/y)^{2β}` bookkeeping absorbs it downstream (STATED, not absorbed).
-/

/-- **Stone L — the low-leg window-monotonicity shift** (`low_leg_shift`).  For `0 < c' ≤ 1` and a
finite window `F` of positive integers all `≤ Q`, the sub-unit-line mass is bounded by the line-`1`
mass times the excess `Q^{1−c'}`: `∑_{n∈F} ‖b n‖/n^{c'} ≤ Q^{1−c'}·∑_{n∈F} ‖b n‖/n^1`.  Window
monotonicity `n^{−c'} = n^{−1}·n^{1−c'} ≤ n^{−1}·Q^{1−c'}`. -/
theorem low_leg_shift {F : Finset ℕ} {b : ℕ → ℂ} {c' Q : ℝ}
    (_hc'0 : 0 < c') (hc'1 : c' ≤ 1) (hF : ∀ n ∈ F, 1 ≤ n) (hQ : ∀ n ∈ F, (n : ℝ) ≤ Q) :
    (∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ c')
      ≤ Q ^ (1 - c') * ∑ n ∈ F, ‖b n‖ / (n : ℝ) ^ (1 : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hF n hn
  have hexc : (0 : ℝ) ≤ 1 - c' := by linarith
  have hmono : (n : ℝ) ^ (1 - c') ≤ Q ^ (1 - c') := Real.rpow_le_rpow hn0.le (hQ n hn) hexc
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hn0.le c', ← Real.rpow_neg hn0.le (1 : ℝ)]
  have hkey : (n : ℝ) ^ (-c') ≤ Q ^ (1 - c') * (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [show (-c' : ℝ) = (1 - c') + (-(1 : ℝ)) from by ring, Real.rpow_add hn0]
    exact mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hn0.le _)
  calc ‖b n‖ * (n : ℝ) ^ (-c')
      ≤ ‖b n‖ * (Q ^ (1 - c') * (n : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
    _ = Q ^ (1 - c') * (‖b n‖ * (n : ℝ) ^ (-(1 : ℝ))) := by ring

/-! ## Stone C-band — the band Cauchy–Schwarz (`sqNorm_cs_band`)

The restricted-band weighted Cauchy–Schwarz that the SHARP head needs: on the head band
`|τ| ≤ T₀`, the branch-1 cross-integral `∫ ‖P₋‖·‖P₊‖/√(cw²+τ²)` splits into the geometric mean of
the two legs' weighted second moments (the very integrals `head_second_moment_grade` grades).  This
is the measure-theoretic core the terminal-assembly docstring flagged as "the last plumbing".

Cleaner than the full-line `mixed_weight_cs` (`JointHead`): the CS is run against the FINITE
restricted measure `volume.restrict (Icc (-T₀) T₀)`, so the `L²` sockets reduce to boundedness of
the continuous integrand on the compact band (`memLp2_restrict_Icc_of_continuous`) — no indicator
gymnastics, no compact-support hypothesis.  Weight-agnostic in `cw` (free of the coefficient lines
of `P±`), exactly as `head_second_moment_grade` keeps `cw` free of `c`. -/

/-- A continuous real function is `L²` for the finite Lebesgue restriction to `Icc a b` (bounded on
the compact band, then `MemLp ⊤ → MemLp 2` on the finite measure). -/
private lemma memLp2_restrict_Icc_of_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) :
    MemLp φ 2 (volume.restrict (Set.Icc a b)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ.continuousOn
  have htop : MemLp φ ⊤ (volume.restrict (Set.Icc a b)) :=
    memLp_top_of_bound hφ.aestronglyMeasurable C
      (ae_restrict_of_forall_mem measurableSet_Icc hC)
  exact htop.mono_exponent le_top

/-- **Stone C-band — the band Cauchy–Schwarz** (`sqNorm_cs_band`).  For continuous `P₋, P₊` and a
weight width `cw > 0`, the branch-1 cross-integral over the head band `Icc (-T₀) T₀` is bounded by
the geometric mean of the two legs' `1/√(cw²+τ²)`-weighted second moments:
`∫_{|τ|≤T₀} ‖P₋‖‖P₊‖/√(cw²+τ²) ≤ √(∫_{|τ|≤T₀} ‖P₋‖²/√(cw²+τ²))·√(∫_{|τ|≤T₀} ‖P₊‖²/√(cw²+τ²))`.
Hölder-2-2 (`integral_mul_le_Lp_mul_Lq_of_nonneg`) on `volume.restrict (Icc (-T₀) T₀)`. -/
theorem sqNorm_cs_band {Pm Pp : ℝ → ℂ} {cw T₀ : ℝ} (hcw : 0 < cw)
    (hPm : Continuous Pm) (hPp : Continuous Pp) :
    (∫ τ in Set.Icc (-T₀) T₀, ‖Pm τ‖ * ‖Pp τ‖ / Real.sqrt (cw ^ 2 + τ ^ 2))
      ≤ Real.sqrt (∫ τ in Set.Icc (-T₀) T₀, ‖Pm τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2))
        * Real.sqrt (∫ τ in Set.Icc (-T₀) T₀, ‖Pp τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2)) := by
  have hden : ∀ τ : ℝ, (0 : ℝ) < Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ =>
    Real.sqrt_pos.mpr (by positivity)
  set w : ℝ → ℝ := fun τ => 1 / Real.sqrt (cw ^ 2 + τ ^ 2) with hwdef
  have hwnn : ∀ τ, 0 ≤ w τ := fun τ => by rw [hwdef]; positivity
  set u : ℝ → ℝ := fun τ => ‖Pm τ‖ * Real.sqrt (w τ) with hudef
  set v : ℝ → ℝ := fun τ => ‖Pp τ‖ * Real.sqrt (w τ) with hvdef
  have huv : ∀ τ, u τ * v τ = ‖Pm τ‖ * ‖Pp τ‖ / Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ => by
    simp only [hudef, hvdef]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hwnn τ)]
    simp only [hwdef]; ring
  have husq : ∀ τ, u τ ^ (2 : ℝ) = ‖Pm τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ => by
    simp only [hudef]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hwnn τ)]
    simp only [hwdef]; ring
  have hvsq : ∀ τ, v τ ^ (2 : ℝ) = ‖Pp τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ => by
    simp only [hvdef]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hwnn τ)]
    simp only [hwdef]; ring
  have hwcont : Continuous w := by
    rw [hwdef]
    exact continuous_const.div (Real.continuous_sqrt.comp (by fun_prop)) (fun τ => (hden τ).ne')
  have hsqrtw : Continuous (fun τ => Real.sqrt (w τ)) := Real.continuous_sqrt.comp hwcont
  have hucont : Continuous u := hPm.norm.mul hsqrtw
  have hvcont : Continuous v := hPp.norm.mul hsqrtw
  have hu2 : MemLp u (ENNReal.ofReal 2) (volume.restrict (Set.Icc (-T₀) T₀)) := by
    rw [show ENNReal.ofReal 2 = 2 from by simp]
    exact memLp2_restrict_Icc_of_continuous hucont _ _
  have hv2 : MemLp v (ENNReal.ofReal 2) (volume.restrict (Set.Icc (-T₀) T₀)) := by
    rw [show ENNReal.ofReal 2 = 2 from by simp]
    exact memLp2_restrict_Icc_of_continuous hvcont _ _
  have hunn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Icc (-T₀) T₀)] u :=
    Filter.Eventually.of_forall (fun τ => by simp only [Pi.zero_apply, hudef]; positivity)
  have hvnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Icc (-T₀) T₀)] v :=
    Filter.Eventually.of_forall (fun τ => by simp only [Pi.zero_apply, hvdef]; positivity)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Icc (-T₀) T₀)) Real.HolderConjugate.two_two hunn hvnn hu2 hv2
  have eLHS : (∫ τ in Set.Icc (-T₀) T₀, ‖Pm τ‖ * ‖Pp τ‖ / Real.sqrt (cw ^ 2 + τ ^ 2))
      = ∫ τ in Set.Icc (-T₀) T₀, u τ * v τ :=
    integral_congr_ae (Filter.Eventually.of_forall (fun τ => (huv τ).symm))
  have eA : (∫ τ in Set.Icc (-T₀) T₀, u τ ^ (2 : ℝ))
      = ∫ τ in Set.Icc (-T₀) T₀, ‖Pm τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall husq)
  have eB : (∫ τ in Set.Icc (-T₀) T₀, v τ ^ (2 : ℝ))
      = ∫ τ in Set.Icc (-T₀) T₀, ‖Pp τ‖ ^ 2 / Real.sqrt (cw ^ 2 + τ ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hvsq)
  rw [eLHS, ← eA, ← eB, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hholder

/-! ## Stone 5-sharp — the head reduced to the two branch-1 second moments (`head_sharp_socket`)

The SHARP head, UNCONDITIONAL: the `crossKer` head integral over the band `|t−t₀| ≤ T₀ :=
2(X+h)/h` is bounded by `(X+h)^{cw}·2` times the geometric mean of the two window legs'
branch-1-weighted second moments — the exact integrals `head_second_moment_grade` grades.  Route:
the CoV `t ↦ t−t₀` (the whole integrand is `Φ(t−t₀)`), the branch-1 pointwise weight
`‖hatKernel‖ ≤ (X+h)^{cw}·2/√(cw²+τ²)` (`hatKernel_branch1`), and the band Cauchy–Schwarz
`sqNorm_cs_band` (which keeps the weight `cw = c₀−α−β` free of the two legs' lines `c₀∓β`).

This is the honest reduction of the head socket to per-leg second moments — the CS + branch-1
plumbing the terminal-assembly docstring flagged.  Feeding it: apply `head_second_moment_grade` to
the HIGH leg (`c = c₀+β ≥ 1`, direct) and its low-line variant to the LOW leg (`c = c₀−β`, carrying
`low_leg_shift`'s `(X/y)^{1−c₀+β}` excess) — the remaining per-leg grade is the named residual
(module tail). -/
theorem head_sharp_socket {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    (∫ t in {t : ℝ | |t - t₀| ≤ 2 * (X + h) / h},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)
      ≤ (X + h) ^ (c₀ - α - β) * 2
          * (Real.sqrt (∫ τ in Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h),
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2
                  / Real.sqrt ((c₀ - α - β) ^ 2 + τ ^ 2))
            * Real.sqrt (∫ τ in Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h),
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2
                  / Real.sqrt ((c₀ - α - β) ^ 2 + τ ^ 2))) := by
  set cw := c₀ - α - β with hcwdef
  set T₀ := 2 * (X + h) / h with hT₀def
  have hXh : (0 : ℝ) < X + h := by linarith
  have hden : ∀ τ : ℝ, (0 : ℝ) < Real.sqrt (cw ^ 2 + τ ^ 2) := fun τ =>
    Real.sqrt_pos.mpr (by positivity)
  have hPmc : Continuous (fun τ : ℝ => windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))) :=
    (continuous_windowSum g X y).comp (by fun_prop)
  have hPpc : Continuous (fun τ : ℝ => windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))) :=
    (continuous_windowSum g X y).comp (by fun_prop)
  have hKc : Continuous (fun τ : ℝ => ‖hatKernel X h cw τ‖) :=
    (continuous_hatKernel (by linarith) hh hc).norm
  have hΦc : Continuous (fun τ : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h cw τ‖) := (hPmc.norm.mul hPpc.norm).mul hKc
  have hΨc : Continuous (fun τ : ℝ => (X + h) ^ cw * 2
      * (‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
          / Real.sqrt (cw ^ 2 + τ ^ 2))) :=
    continuous_const.mul ((hPmc.norm.mul hPpc.norm).div
      (Real.continuous_sqrt.comp (by fun_prop)) (fun τ => (hden τ).ne'))
  have hmp : MeasurePreserving (fun t : ℝ => t - t₀) volume volume :=
    measurePreserving_sub_right volume t₀
  have hme : MeasurableEmbedding (fun t : ℝ => t - t₀) :=
    (Homeomorph.subRight t₀).measurableEmbedding
  have hIcc : {τ : ℝ | |τ| ≤ T₀} = Set.Icc (-T₀) T₀ := by
    ext τ; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  have hcov : (∫ t in {t : ℝ | |t - t₀| ≤ T₀},
        ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
          * ‖hatKernel X h cw (t - t₀)‖)
      = ∫ τ in Set.Icc (-T₀) T₀,
          ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h cw τ‖ := by
    rw [show {t : ℝ | |t - t₀| ≤ T₀}
          = (fun t : ℝ => t - t₀) ⁻¹' {τ : ℝ | |τ| ≤ T₀} from rfl, ← hIcc]
    exact hmp.setIntegral_preimage_emb hme (fun τ =>
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h cw τ‖) {τ : ℝ | |τ| ≤ T₀}
  rw [hcov]
  calc (∫ τ in Set.Icc (-T₀) T₀,
          ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
            * ‖hatKernel X h cw τ‖)
      ≤ ∫ τ in Set.Icc (-T₀) T₀, (X + h) ^ cw * 2
          * (‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
              * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
              / Real.sqrt (cw ^ 2 + τ ^ 2)) := by
        refine setIntegral_mono_on hΦc.integrableOn_Icc hΨc.integrableOn_Icc measurableSet_Icc
          (fun τ _ => ?_)
        have hb := hatKernel_branch1 hX hh hc τ
        have hnn : (0 : ℝ) ≤ ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ := by positivity
        calc ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
                * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
                * ‖hatKernel X h cw τ‖
            ≤ ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
                * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
                * ((X + h) ^ cw * 2 * (Real.sqrt (cw ^ 2 + τ ^ 2))⁻¹) :=
              mul_le_mul_of_nonneg_left hb hnn
          _ = (X + h) ^ cw * 2
                * (‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
                    * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
                    / Real.sqrt (cw ^ 2 + τ ^ 2)) := by rw [div_eq_mul_inv]; ring
    _ = (X + h) ^ cw * 2 * ∫ τ in Set.Icc (-T₀) T₀,
          (‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖
              * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖
              / Real.sqrt (cw ^ 2 + τ ^ 2)) := integral_const_mul _ _
    _ ≤ (X + h) ^ cw * 2
          * (Real.sqrt (∫ τ in Set.Icc (-T₀) T₀,
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2
                  / Real.sqrt (cw ^ 2 + τ ^ 2))
            * Real.sqrt (∫ τ in Set.Icc (-T₀) T₀,
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2
                  / Real.sqrt (cw ^ 2 + τ ^ 2))) :=
        mul_le_mul_of_nonneg_left (sqNorm_cs_band hc hPmc hPpc)
          (mul_nonneg (Real.rpow_nonneg hXh.le cw) (by norm_num))

/-! ## Stone 7-sharp — `crossKer` at the SHARP grade (`crossKer_grade_sharp`)

The τ-split composition at the SHARP head: `head_split_ledger` splits `crossKer` at the branch
crossover `T₀ = 2(X+h)/h` into head (`|t−t₀| ≤ T₀`, branch-1) + tail (`|t−t₀| > T₀`, branch-2);
`head_sharp_socket` grades the head by the CS geometric mean of the two legs' branch-1 second
moments (NOT the crude `arsinh` sup mass of `crossKer_grade_final`); `tail_band_sum` discharges the
tail EXACTLY to the ramp-free `Mm·Mp·2(X+h)^{cw}`.  UNCONDITIONAL in `1 ≤ X`, `0 < h`, `0 < cw`:

  `crossKer g X h y c₀ t₀ α β
      ≤ (X+h)^{cw}·2·√(A₋)·√(A₊) + Mm·Mp·2(X+h)^{cw}`,

`cw = c₀−α−β`, `A∓ = ∫_{|τ|≤T₀} ‖windowSum(c₀+iτ∓β)‖²/√(cw²+τ²)` the two legs' branch-1 second
moments, `Mm,Mp` the window masses at `c₀∓β`.  This is the SHARP shape: `√(A₋)·√(A₊) ≤ Mm·Mp·
2·arsinh(T₀/cw)` recovers `crossKer_grade_final`'s head, but the second moments carry the
off-diagonal cancellation — grading them collapses the head below the crude `Mm·Mp·log L`.

**Reaching the fully-decayed `diag + mass/T₀` exit** (the design's constant grade).  Grade each
`A∓` by `head_second_moment_grade` (weight `cw` FREE of the lines `c₀∓β`, under the y-gate `2 T₀^8 ≤
n` and `4 ≤ T₀`, `c₀∓β ≤ T₀`):
  `A₊ ≤ 2πT₀/cw·(diag₊ + 4C/(T₀−(c₀+β)+1)·mass₊)`  — the HIGH leg, `c₀+β ≥ 1`, DIRECT;
  `A₋ ≤ 2πT₀/cw·(diag₋ + 4C/(T₀−(c₀−β)+1)·(X/y)^{1−c₀+β}·mass₋)`  — the LOW leg, `c₀−β < 1`, via
the low-line variant of `head_second_moment_grade` carrying `low_leg_shift`'s `(X/y)^{1−c₀+β}`
excess (STATED, absorbed downstream by the S-ladder's `(X/y)^{2β}`).  The HIGH-leg grade is a
direct `head_second_moment_grade` application; the LOW-leg variant (`offdiag_widthA_final`/`inner_
sharp` re-run at `0 < c < 1` with the window factor `n ≤ X/y` in place of `n^{1−2c} ≤ n^{−c}`) is
the last remaining ledge — FLAGGED per iron rule 1/4, the analytic core (`inner_sharp`'s geometric
page, `hband_discharge`) is `c`-agnostic so the clone is mechanical.  The banked stones for it:
`low_leg_shift` (the mass wrapper) and `sqNorm_cs_band` (the CS core) stand here. -/
theorem crossKer_grade_sharp {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    crossKer g X h y c₀ t₀ α β
      ≤ (X + h) ^ (c₀ - α - β) * 2
          * (Real.sqrt (∫ τ in Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h),
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) - (β : ℂ))‖ ^ 2
                  / Real.sqrt ((c₀ - α - β) ^ 2 + τ ^ 2))
            * Real.sqrt (∫ τ in Set.Icc (-(2 * (X + h) / h)) (2 * (X + h) / h),
                ‖windowSum g X y (((c₀ : ℂ) + (τ : ℂ) * I) + (β : ℂ))‖ ^ 2
                  / Real.sqrt ((c₀ - α - β) ^ 2 + τ ^ 2)))
        + (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
              ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
              ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * (2 * (X + h) ^ (c₀ - α - β)) := by
  rw [head_split_ledger hX hh hc]
  exact add_le_add (head_sharp_socket hX hh hc) (tail_band_sum hX hh hc)

end Salt.MR
