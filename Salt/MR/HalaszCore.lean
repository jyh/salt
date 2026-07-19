/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.L2MVT
import Salt.MR.Dist

/-!
# MR-gate S8/MR-CORE wave 1, stone H2 — the Halász core (`HalaszCore`)

Rung card (S8 MR-CORE FREEZE v2, H2 `HalaszCore`, THE keystone): the pointwise
Granville–Harper–Soundararajan Halász engine underneath Matomäki–Radziwiłł–Tao
Proposition A.3.  Source: MRT arXiv `1503.05121v3` App. A pp. 22–28 (v3 pin: the
corrected slow-`M` route).  Frozen grade everywhere: `E(M) := exp(-M/2)`.

Internal order (FIXED by the freeze; only the exit stone `halasz_ball_decay` is a
frozen interface — internal lemma shapes are the executor's to adjust):
* `R2.2` `halasz_cosh_ineq` — Lemma A.8, the warm-up cosh inequality
  `eᵃ + e⁻ᵃ − 2cos t ≤ e^{√(a²+t²)}` (day-1 stone; pure real analysis).
* `R2.3` `lambda_ell_decomp` — the `s_𝒥/ℓ/Λ_ℓ` Plancherel decomposition of
  pp. 24–25 (D-class, FAIL-FAST kill-check K1).
* `R2.1` `ball_mvt` — the short-ball L² mean value from `L2MVT`.
* `R2.4` — the A.6/A.7 iterated moment/decay chain.
* `R2.5` `halasz_ball_decay` — DEFERRED (needs H1's `R1.1` triangle).

D5 source pins: MRT v3 ONLY (corrected slow-`M` Prop A.3); consumes only LANDED
corpus surfaces (`L2MVT`, `Dist`).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## R2.2 — the Halász cosh inequality (Lemma A.8, `halasz_cosh_ineq`)

MRT Lemma A.8 (p. 27): for real `α, θ`,
`eᵃ + e⁻ᵃ − 2 cos θ ≤ e^{√(α²+θ²)}`.
The paper's proof is a two-line mean value theorem argument: the function
`x ↦ e^{√x}` has derivative `≥ e/2` on `(0,∞)` (which reduces to `e·u ≤ eᵘ`),
so `e^{√(b²+t²)} ≥ e^b + (e/2) t²`, and then `cos θ ≥ 1 − θ²/2` closes it. -/

/-- The elementary inequality `e·u ≤ eᵘ` for all real `u` (equality at `u = 1`).
Restated from `Real.add_one_le_exp` at the shifted point `u − 1`: this is exactly
the derivative-lower-bound `e^{√x}' = e^{√x}/(2√x) ≥ e/2` after clearing `2√x`. -/
theorem exp_one_mul_le_exp (u : ℝ) : Real.exp 1 * u ≤ Real.exp u := by
  have h : u ≤ Real.exp (u - 1) := by
    have := Real.add_one_le_exp (u - 1); linarith
  calc Real.exp 1 * u
      ≤ Real.exp 1 * Real.exp (u - 1) :=
        mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos 1))
    _ = Real.exp u := by rw [← Real.exp_add]; congr 1; ring

/-- The mean value theorem core of Lemma A.8: for `b ≥ 0` and any `t`,
`e^b + (e/2) t² ≤ e^{√(b²+t²)}`.  Proof: `H(x) := e^{√x} − (e/2) x` is monotone
on `[0,∞)` because `H'(x) = e^{√x}/(2√x) − e/2 ≥ 0` on `(0,∞)`
(⟺ `e·√x ≤ e^{√x}`), so `H(b²+t²) ≥ H(b²)`. -/
theorem exp_sqrt_lower (b t : ℝ) (hb : 0 ≤ b) :
    Real.exp b + Real.exp 1 / 2 * t ^ 2 ≤ Real.exp (Real.sqrt (b ^ 2 + t ^ 2)) := by
  set H : ℝ → ℝ := fun x => Real.exp (Real.sqrt x) - Real.exp 1 / 2 * x with hHdef
  have hcont : ContinuousOn H (Set.Ici 0) := by
    apply Continuous.continuousOn; rw [hHdef]; fun_prop
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt H (Real.exp (Real.sqrt x) * (1 / (2 * Real.sqrt x)) - Real.exp 1 / 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx0
    have hexp : HasDerivAt (fun x => Real.exp (Real.sqrt x))
        (Real.exp (Real.sqrt x) * (1 / (2 * Real.sqrt x))) x := hsqrt.exp
    have hlin : HasDerivAt (fun x : ℝ => Real.exp 1 / 2 * x) (Real.exp 1 / 2) x := by
      simpa using (hasDerivAt_id x).const_mul (Real.exp 1 / 2)
    exact hexp.sub hlin
  have hmono : MonotoneOn H (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
    · rw [interior_Ici]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(hderiv x hx).deriv]
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
      have h2s : 0 < 2 * Real.sqrt x := by positivity
      have hes : Real.exp 1 * Real.sqrt x ≤ Real.exp (Real.sqrt x) := exp_one_mul_le_exp _
      rw [sub_nonneg, mul_one_div, le_div_iff₀ h2s]
      nlinarith [hes]
  have hb2 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
  have hbt : (0 : ℝ) ≤ b ^ 2 + t ^ 2 := by positivity
  have hle : b ^ 2 ≤ b ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hstep := hmono (Set.mem_Ici.mpr hb2) (Set.mem_Ici.mpr hbt) hle
  simp only [hHdef] at hstep
  rw [Real.sqrt_sq hb] at hstep
  have hexpand : Real.exp 1 / 2 * (b ^ 2 + t ^ 2)
      = Real.exp 1 / 2 * b ^ 2 + Real.exp 1 / 2 * t ^ 2 := by ring
  linarith [hstep, hexpand.le, hexpand.ge]

/-- **R2.2 — Halász's cosh inequality (MRT Lemma A.8).**  For real `a, t`,
`eᵃ + e⁻ᵃ − 2 cos t ≤ e^{√(a²+t²)}`.  The `√(a²+t²)` on the right is exactly the
modulus of the complex number `a + i t`; this is the seed of the Euler-product
`≤ 1` step (A.12) in the `Λ_ℓ` decomposition. -/
theorem halasz_cosh_ineq (a t : ℝ) :
    Real.exp a + Real.exp (-a) - 2 * Real.cos t ≤ Real.exp (Real.sqrt (a ^ 2 + t ^ 2)) := by
  have hb : 0 ≤ |a| := abs_nonneg a
  have hab : Real.exp a + Real.exp (-a) = Real.exp |a| + Real.exp (-|a|) := by
    rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, neg_neg]; ring
  have hb2 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have hcos : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
  have hexpnb : Real.exp (-|a|) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hmvt : Real.exp |a| + Real.exp 1 / 2 * t ^ 2 ≤ Real.exp (Real.sqrt (|a| ^ 2 + t ^ 2)) :=
    exp_sqrt_lower |a| t hb
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  rw [hab, hb2]
  nlinarith [hmvt, hcos, hexpnb,
    mul_nonneg (by linarith [he2] : (0 : ℝ) ≤ Real.exp 1 - 2) (sq_nonneg t)]

/-! ## R2.3 (attempt 1) — the complex Halász inequality (A.11)/(A.12)

The Euler-product `≤ 1` step of the `Λ_ℓ` decomposition (MRT (A.11)–(A.12),
p. 26) reduces, by the law of cosines, to the *complex* form of Lemma A.8:
`‖exp u − exp(−u)‖ ≤ exp‖u‖`.  This is the one component of R2.3 provable
outright from `halasz_cosh_ineq`: the law of cosines gives
`‖exp u − exp(−u)‖² = e^{2Re u}+e^{−2Re u}−2cos(2Im u)`, with `‖u‖ = √(Re u² + Im u²)`.
The remaining machinery of
R2.3 — the Perron/Plancherel representation (A.10) and the contour bound
(A.13)–(A.14)⇒(A.9) — is not reachable from the current corpus (see the FAIL-FAST
note below). -/

/-- The complex Halász inequality: `‖exp u − exp(−u)‖ ≤ exp‖u‖`.  The law-of-cosines
face of Lemma A.8 (`halasz_cosh_ineq`) and the algebraic heart of MRT (A.11)–(A.12). -/
theorem halasz_sinh_bound (u : ℂ) :
    ‖Complex.exp u - Complex.exp (-u)‖ ≤ Real.exp ‖u‖ := by
  have hnu : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hre : (Complex.exp u - Complex.exp (-u)).re
      = Real.cos u.im * (Real.exp u.re - Real.exp (-u.re)) := by
    rw [Complex.sub_re, Complex.exp_re, Complex.exp_re, Complex.neg_re, Complex.neg_im,
      Real.cos_neg]; ring
  have him : (Complex.exp u - Complex.exp (-u)).im
      = Real.sin u.im * (Real.exp u.re + Real.exp (-u.re)) := by
    rw [Complex.sub_im, Complex.exp_im, Complex.exp_im, Complex.neg_re, Complex.neg_im,
      Real.sin_neg]; ring
  have hpyth : Real.sin u.im ^ 2 + Real.cos u.im ^ 2 = 1 := Real.sin_sq_add_cos_sq u.im
  have hpq : Real.exp u.re * Real.exp (-u.re) = 1 := by rw [← Real.exp_add]; simp
  have hp2 : Real.exp u.re * Real.exp u.re = Real.exp (2 * u.re) := by
    rw [← Real.exp_add]; congr 1; ring
  have hq2 : Real.exp (-u.re) * Real.exp (-u.re) = Real.exp (-(2 * u.re)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcos2 : Real.cos (2 * u.im) = Real.cos u.im ^ 2 - Real.sin u.im ^ 2 := by
    rw [Real.cos_two_mul]; linear_combination hpyth
  have hsq : Complex.normSq (Complex.exp u - Complex.exp (-u))
      = Real.exp (2 * u.re) + Real.exp (-(2 * u.re)) - 2 * Real.cos (2 * u.im) := by
    rw [Complex.normSq_apply, hre, him, ← hp2, ← hq2, hcos2]
    linear_combination
      (Real.exp u.re ^ 2 + Real.exp (-u.re) ^ 2) * hpyth
      + (2 * (Real.sin u.im ^ 2 - Real.cos u.im ^ 2)) * hpq
  have hsqle : ‖Complex.exp u - Complex.exp (-u)‖ ^ 2 ≤ (Real.exp ‖u‖) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hsq]
    have hcosh := halasz_cosh_ineq (2 * u.re) (2 * u.im)
    have hstep : (2 * u.re) ^ 2 + (2 * u.im) ^ 2 = (2 * ‖u‖) ^ 2 := by
      linear_combination -4 * hnu
    have hnorm2 : Real.sqrt ((2 * u.re) ^ 2 + (2 * u.im) ^ 2) = 2 * ‖u‖ := by
      rw [hstep]; exact Real.sqrt_sq (by positivity)
    rw [hnorm2] at hcosh
    have hexpsq : (Real.exp ‖u‖) ^ 2 = Real.exp (2 * ‖u‖) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hexpsq]; exact hcosh
  calc ‖Complex.exp u - Complex.exp (-u)‖
      = Real.sqrt (‖Complex.exp u - Complex.exp (-u)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.exp ‖u‖) ^ 2) := Real.sqrt_le_sqrt hsqle
    _ = Real.exp ‖u‖ := Real.sqrt_sq (Real.exp_pos _).le

/-- MRT (A.12) (p. 26): `‖exp(w/2) − exp(−w/2)‖ ≤ exp(‖w‖/2)`, the Cauchy–Schwarz
form used to establish that the Euler-product factor of (A.11) is `≤ 1`.  Immediate
from `halasz_sinh_bound` at `u = w/2` (with `‖w/2‖ = ‖w‖/2`). -/
theorem halasz_cosh_ineq_complex (w : ℂ) :
    ‖Complex.exp (w / 2) - Complex.exp (-(w / 2))‖ ≤ Real.exp (‖w‖ / 2) := by
  have h := halasz_sinh_bound (w / 2)
  rwa [show ‖w / 2‖ = ‖w‖ / 2 by rw [norm_div]; simp] at h

/-! ## R2.1 (piece) — the off-diagonal oscillatory integral bound

The `L²` mean value of a Dirichlet polynomial expands (via `L2MVT`'s
`dirichlet_poly_l2_diagonal`) into a diagonal `2T·∑‖aₙ‖²` plus off-diagonal terms
each carrying the oscillatory integral `∫_{-T}^{T} exp(i t (log m − log n)) dt`.
This lemma is the per-pair magnitude bound `≤ 2/|log m − log n|` — the elementary
kernel of the `T + N log N` mean value estimate (the remaining `∑_{m≠n} 1/|log(m/n)|
≪ N log N` harmonic bound is the residual of `ball_mvt`). -/

/-- The oscillatory-integral kernel bound: for `θ ≠ 0`,
`‖∫_{-T}^{T} exp(i t θ) dt‖ ≤ 2/|θ|` (the integral is `2 sin(Tθ)/θ`). -/
theorem offdiag_int_bound (θ T : ℝ) (hθ : θ ≠ 0) :
    ‖∫ t in (-T)..T, Complex.exp (Complex.I * (t : ℂ) * (θ : ℂ))‖ ≤ 2 / |θ| := by
  have hc : Complex.I * (θ : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hθ)
  have hθpos : 0 < |θ| := abs_pos.mpr hθ
  have hrw : (∫ t in (-T)..T, Complex.exp (Complex.I * (t : ℂ) * (θ : ℂ)))
      = ∫ t in (-T)..T, Complex.exp ((Complex.I * (θ : ℂ)) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_); congr 1; ring
  have hnorm : ‖Complex.I * (θ : ℂ)‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hrw, integral_exp_mul_complex hc, norm_div, hnorm]
  have hnum : ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ))
      - Complex.exp (Complex.I * (θ : ℂ) * ((-T : ℝ) : ℂ))‖ ≤ 2 := by
    have e1 : ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      norm_num [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have e2 : ‖Complex.exp (Complex.I * (θ : ℂ) * ((-T : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      norm_num [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    calc ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ))
            - Complex.exp (Complex.I * (θ : ℂ) * ((-T : ℝ) : ℂ))‖
        ≤ ‖Complex.exp (Complex.I * (θ : ℂ) * (T : ℂ))‖
            + ‖Complex.exp (Complex.I * (θ : ℂ) * ((-T : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [e1, e2]; norm_num
  gcongr

end Salt.MR
