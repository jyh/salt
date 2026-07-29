/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.L2MVT
import Salt.MR.MVCore2
import Salt.MR.Dist
import Salt.MR.PretentiousTriangle
import Salt.MR.DistHalasz

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

/-! ## R2.4 grade — the `E(M)` collapse (`grade_EM`, DES-A graft)

The frozen grade of the whole A-chain is `E(M) := exp(-M/2)` (S8 freeze).  The
raw output of the Halász moment bound is `(1 + M)·exp(-M)` (the `1 + M` from the
`∫₀^η (1/σ) dσ ≍ M` accumulation of the `Λ`-window integral, per the S2' head
ledger).  This lemma is the DES-A stone certifying `(1 + M)·exp(-M) ≤ 2·exp(-M/2)`
for `M ≥ 0` — a genuine constant `2` (the interior maximum of
`M ↦ (1 + M)·exp(-M/2)` is `≈ 1.213` at `M = 1`, comfortably `≤ 2`), NOT an
`o(1)`.  It buys the `√`-slack consumed at each Cauchy–Schwarz downstream. -/

/-- **R2.4 grade collapse (`grade_EM`, DES-A graft).**  For `M ≥ 0`,
`(1 + M)·exp(-M) ≤ 2·exp(-M/2)`.  Route: `Real.add_one_le_exp` at `M/2` gives
`1 + M/2 ≤ exp(M/2)`, whence `1 + M ≤ 2·exp(M/2)`; multiplying by `exp(-M) > 0`
and folding `exp(M/2)·exp(-M) = exp(-M/2)` closes it.  (The paper's `interior
max 1.213` is a fortiori `≤ 2`.)

**AMENDMENT B4 (JYH-ratified 2026-07-23).**  This collapse is now VESTIGIAL on the
elementary B-route: the B-ladder's pretentious cutoff delivers the head already in the
`C·e^{−cM}` shape (`c = 1/e`), so there is no `(1 + M)` to collapse — `halasz_ball_decay`
no longer invokes `grade_EM`.  Kept LANDED as heritage (the `(1+M)e^{−M} → 2e^{−M/2}`
identity remains true and is the artifact of the superseded max-modulus route). -/
theorem grade_EM {M : ℝ} (_hM : 0 ≤ M) :
    (1 + M) * Real.exp (-M) ≤ 2 * Real.exp (-M / 2) := by
  have hkey : 1 + M ≤ 2 * Real.exp (M / 2) := by
    have := Real.add_one_le_exp (M / 2); linarith
  have hpos : (0 : ℝ) ≤ Real.exp (-M) := (Real.exp_pos _).le
  calc (1 + M) * Real.exp (-M)
      ≤ (2 * Real.exp (M / 2)) * Real.exp (-M) := mul_le_mul_of_nonneg_right hkey hpos
    _ = 2 * Real.exp (-M / 2) := by
        rw [mul_assoc, ← Real.exp_add, show M / 2 + -M = -M / 2 by ring]

/-! ## R2.1 — the short-ball L² mean value (`ball_mvt`)

The Halász ball contribution is an L² mean value of a Dirichlet polynomial over
the ball `|t − t₀| ≤ T₀` (here `T₀ = (log X)^{1/46}`, the frozen ball radius).

**Anchor observation (ANCHOR DRIFT, recorded):** the freeze priced R2.1 as the
harmonic `(T + N log N)` route over `offdiag_int_bound` + `dirichlet_poly_l2_diagonal`.
Since the freeze was written, `dirichlet_poly_l2_mvt_final` (`MVCore2`) has landed
the SHARP `(2T + 20N)·∑‖aₙ‖²` mean value UNCONDITIONALLY (the Montgomery–Vaughan /
Hilbert route, `mvHilbertUniform_holds` discharged).  This strictly supersedes the
harmonic route (no `log N` factor).  `ball_mvt` therefore recenters the sharp bound
to the ball; the elementary harmonic kernel `offdiag_int_bound` (landed above) and
the per-pair log lower bound (`log_diff_ge`, below) remain the honest grains of the
superseded route. -/

/-- The center-twisted coefficient `n ↦ a n · exp(i·t₀·log n)` (the ball-center
twist `n^{it₀}` folded into the Dirichlet-polynomial coefficient). -/
private noncomputable def twistCoeff (a : ℕ → ℂ) (t₀ : ℝ) : ℕ → ℂ :=
  fun n => a n * Complex.exp (Complex.I * (t₀ : ℂ) * (Real.log n : ℂ))

/-- The center twist is modulus-preserving: `‖twistCoeff a t₀ n‖ = ‖a n‖` (the
twist `exp(i·t₀·log n)` is unimodular, its exponent being purely imaginary). -/
private lemma norm_twistCoeff (a : ℕ → ℂ) (t₀ : ℝ) (n : ℕ) :
    ‖twistCoeff a t₀ n‖ = ‖a n‖ := by
  rw [twistCoeff, norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (t₀ : ℂ) * (Real.log n : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hre, Real.exp_zero, mul_one]

/-- Recentering the Dirichlet polynomial: `F_a(u + t₀) = F_{twistCoeff a t₀}(u)`. -/
private lemma dpoly_shift (N : ℕ) (a : ℕ → ℂ) (t₀ u : ℝ) :
    dpoly N a (u + t₀) = dpoly N (twistCoeff a t₀) u := by
  unfold dpoly twistCoeff
  refine Finset.sum_congr rfl fun n _ => ?_
  have hexp : Complex.exp (Complex.I * ((u + t₀ : ℝ) : ℂ) * (Real.log n : ℂ))
      = Complex.exp (Complex.I * (t₀ : ℂ) * (Real.log n : ℂ))
        * Complex.exp (Complex.I * (u : ℂ) * (Real.log n : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hexp]; ring

/-- **R2.1 — the short-ball L² mean value (`ball_mvt`).**  For the ball
`|t − t₀| ≤ T₀`, the L² mean value of the Dirichlet polynomial `dpoly N a` is
bounded by `(2 T₀ + 20 N)·∑_{1≤n≤N} ‖aₙ‖²` — the sharp `(T + N)` grade, recentered
from `dirichlet_poly_l2_mvt_final` by the change of variables `t = u + t₀` (the
center twist `n^{it₀}` is modulus-free, so the coefficient `ℓ²`-mass is unchanged). -/
theorem ball_mvt (N : ℕ) (a : ℕ → ℂ) (t₀ T₀ : ℝ) :
    (∫ t in (t₀ - T₀)..(t₀ + T₀), ‖dpoly N a t‖ ^ 2)
      ≤ (2 * T₀ + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hshift : (∫ t in (t₀ - T₀)..(t₀ + T₀), ‖dpoly N a t‖ ^ 2)
      = ∫ u in (-T₀)..(T₀), ‖dpoly N (twistCoeff a t₀) u‖ ^ 2 := by
    rw [show t₀ - T₀ = -T₀ + t₀ by ring, show t₀ + T₀ = T₀ + t₀ by ring,
      ← intervalIntegral.integral_comp_add_right (fun t => ‖dpoly N a t‖ ^ 2) t₀]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [dpoly_shift N a t₀ u]
  rw [hshift]
  refine (dirichlet_poly_l2_mvt_final N (twistCoeff a t₀) T₀).trans ?_
  have hnorms : (∑ n ∈ Finset.Icc 1 N, ‖twistCoeff a t₀ n‖ ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_congr rfl fun n _ => by rw [norm_twistCoeff a t₀ n]
  rw [hnorms]

/-- **The spacing kernel** (step 1 of the harmonic `ball_mvt` remainder, the honest
grain of the superseded route).  For `1 ≤ n, m ≤ N`, the log-spacing dominates the
scaled linear spacing: `|m − n|/N ≤ |log m − log n|`.  This is the elementary
`|log(m/n)| ≥ (m−n)/N` kernel (companion to the oscillatory kernel
`offdiag_int_bound`); the harmonic double sum `∑_{m≠n} 1/|log(m/n)| ≪ N log N`
follows by summing `N/|m−n|` over the two harmonic tails.  Route: for `b ≤ a`,
`log(a/b) ≥ 1 − b/a = (a−b)/a ≥ (a−b)/N` (`Real.one_sub_inv_le_log_of_pos`).
Not consumed downstream — `ball_mvt` uses the sharp `(2T+20N)` route; landed as the
elementary residual kernel the freeze names. -/
theorem log_diff_ge {n m N : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnN : n ≤ N) (hmN : m ≤ N) :
    |(m : ℝ) - (n : ℝ)| / (N : ℝ) ≤ |Real.log m - Real.log n| := by
  have hord : ∀ a b : ℕ, 1 ≤ b → b ≤ a → a ≤ N →
      ((a : ℝ) - (b : ℝ)) / (N : ℝ) ≤ Real.log a - Real.log b := by
    intro a b hb hba haN
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast lt_of_lt_of_le hb hba
    have haNr : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast haN
    have hbar : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    have hab_nn : (0 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by linarith
    have hlb : 1 - ((a : ℝ) / (b : ℝ))⁻¹ ≤ Real.log ((a : ℝ) / (b : ℝ)) :=
      Real.one_sub_inv_le_log_of_pos (div_pos ha0 hb0)
    have hrw : 1 - ((a : ℝ) / (b : ℝ))⁻¹ = ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
      rw [inv_div]; field_simp
    rw [Real.log_div (ne_of_gt ha0) (ne_of_gt hb0), hrw] at hlb
    exact le_trans (div_le_div_of_nonneg_left hab_nn ha0 haNr) hlb
  rcases le_total m n with hmn | hnm
  · have hmnr : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hlogle : Real.log m ≤ Real.log n := Real.log_le_log (by exact_mod_cast hm) hmnr
    rw [abs_of_nonpos (show (m : ℝ) - (n : ℝ) ≤ 0 by linarith),
      abs_of_nonpos (show Real.log m - Real.log n ≤ 0 by linarith), neg_sub, neg_sub]
    exact hord n m hm hmn hnN
  · have hnmr : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hlogle : Real.log n ≤ Real.log m := Real.log_le_log (by exact_mod_cast hn) hnmr
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) by linarith),
      abs_of_nonneg (show (0 : ℝ) ≤ Real.log m - Real.log n by linarith)]
    exact hord m n hn hnm hmN

/-! ## R2.4 / R2.5 — the exit stone `halasz_ball_decay` (the frozen interface)

**R2.4 GATE-CHECK VERDICT — HELD (GS[10] Lemma-7.1 NOT needed; no staging debt).**
The freeze (`halasz-infra-freeze.md`, scope-diff (2); OPEN_RISK #5) flagged a latent
dependency on Granville–Soundararajan [10] Lemma 7.1 — the Lipschitz /
renormalization step that MRT (A.8) uses to control the variation of
`M(t) = 𝔻(f, p^{it}; X)²` across the ball — with a DECLARED replacement:
"center-`t₀` exit + `R1.1` triangle recentering", and a STOP-and-flag if the
replacement proved irreplaceable.  Examining the assembly need:

* The seam (S1'/S2', `HalaszSeam`) is CONSTRUCTED centered at `t₀`: the represented
  sum is twisted by `n^{-it₀}` (`seamCoeff`) and the contour kernel is
  `hatKernel X h c₀ (t − t₀)` (centered at `t₀`).  Hence the S2' head main term
  `X·(1+M)·e^{-M}` carries `M = 𝔻(f, p^{it₀}; X)²` at the CENTER directly — the
  `exp(-M(t₀)/2)` grade emerges from the centered Euler/`F` factor, NOT from a
  sup-over-ball argument that would require `M(t) ≥ M(t₀) − o(1)` uniformly.
* The exit stone is verified center-`t₀`/infimum-free (`s8-freeze.md:25`), so no
  `inf_{ball} M` machinery ("Wall 3") and no continuity-of-`M` estimate is invoked.
* The only distance-recentering the ladder needs (windowed `f·g_J → f`) is exactly
  `dist_mul_half` / `pretDist_triangle` (`R1.1`, `PretentiousTriangle`, LANDED),
  applied by H3's `R3.1`, not a Lipschitz bound.

CONCLUSION: the declared replacement holds; GS[10] Lemma 7.1 is dissolved by the
seam's centered construction plus the landed R1.1 triangle.  GS[10] does NOT join
staging debt; there is NO second named residual `R2.4-Lipschitz`.

**R2.5 conditionality.**  The full A.6/A.7 → exit-stone assembly consumes the S1'
`α,β` Perron representation (the campaign's single NAMED RESIDUAL — a multi-thousand
line formalization, `HalaszSeam` module docstring) and the S2' head
(`contour_A13_A14_head`), itself CONDITIONAL on the K4' Plancherel leg
(`dirichlet_plancherel`, the wave-I-1 named residual, mathlib-absent contour).
Per the freeze ("the K4'-conditional exit form is a legitimate landing"),
`halasz_ball_decay` therefore lands as the ASSEMBLY of the seam contributions into
the frozen shape, carrying those two analytic inputs as EXPLICIT hypotheses
(`hhead` — the S1'/S2'-produced centered head, K4'-conditional; `htail` — the S2'
tail ledger, `s2_tail_ledger`; `hsplit` — the S1' head/tail decomposition of the
ball contribution `U`).  The frozen CONCLUSION shape (`s8-freeze.md:25`) is served
verbatim; `grade_EM` performs the `(1+M)e^{-M} → 2e^{-M/2}` collapse; the tail
`ε`-bump uses `Real.rpow_le_rpow_of_exponent_le`. -/

/-- **`M_range` nonnegativity.**  The range-minimum `M_range f X T` is a distance-square
infimum, hence `≥ 0`: every element of the range image is `pretDistSq f (costwist t) X ≥ 0`
(`pretDistSq_nonneg`, using `‖costwist t n‖ = 1`), so `Real.sInf_nonneg` applies.  Supplies
`halasz_ball_decay`'s `hM0` after the J0 restatement (the `M`-nonneg the old proof drew from
`pretDistSq_nonneg f g X`). -/
theorem Mrange_nonneg (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (X T : ℝ) :
    0 ≤ M_range f X T := by
  unfold M_range
  refine Real.sInf_nonneg ?_
  rintro v ⟨t, -, rfl⟩
  refine pretDistSq_nonneg f (costwist t) X hf (fun n => ?_)
  have hct : ‖costwist t n‖ = 1 := by unfold costwist; exact Complex.norm_exp_ofReal_mul_I _
  exact hct.le

/-- **R2.5 — the exit stone `halasz_ball_decay`** (frozen interface,
`s8-freeze.md:25`, served in K4'/S1'-conditional assembly form).  For a 1-bounded
`f` and center `t₀` (carried through `g`, the character `n ↦ n^{it₀}` restricted to
primes), with `M = M_range f X T` GHS Lemma 1's RANGE-MINIMUM squared-distance, the
ball `|t − t₀| ≤ (log X)^{1/46}` contributes
`U ≪ X·(e^{-cM} + (log X)^{-1/2+ε})`  (`c = 1/e`).

The heavy analytic inputs are the hypotheses: `hsplit` is the S1' representation's
head/tail split of `U`; `hhead` is the S2' head (centered at `t₀`, K4'-conditional
via `contour_A13_A14_head`) in its `C·e^{−cM}` grade (the B-route delivers `e^{−cM}`
directly — no `(1+M)` accumulation); `htail` is the S2' tail ledger (`s2_tail_ledger`).
The frozen shape assembles by adding the tail `ε`-bump.  See the section GATE-CHECK
verdict above (R1.1 replaces GS[10]).

**AMENDMENT B4 (JYH-ratified 2026-07-23; D4's tolerance clause exercised).**  The head
grade is re-frozen from `(1+M)e^{−M}` to the elementary-route `C·e^{−cM}` shape with
`c = 1/Real.exp 1` (the sigma-uniform pretentious bound `C(1/σ)exp(−cD²)` integrating to
`≤ 3.78·e^{−cM}·L` — HPRET-SCOPE).  No collapse survives: the conclusion carries the raw
`e^{−cM}` decay (not `e^{−M/2}`), and the coefficient drops to `C₁ + C₂` (the `grade_EM`
factor `2` is gone with the collapse).  The price is the fully-elementary B-ladder route
to the last frontier stone (max-modulus was ruled out mathematically — a boundary-sup
principle destroys the pointwise-in-`t` decay).  Downstream the floor delivers the final
grade `(log X)^{−c/32} = (log X)^{−1/(32e)}`, a fixed positive delta.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  The head distance `M` is GHS Lemma 1's
range-minimum `M_range f X T` (the `sInf` of `𝔻(f, ·^{it}; X)²` over the offset window),
NOT the center value `pretDistSq f g X`.  The center-M deviation was the drift problem's
source (center-M is unsatisfiable on the joint route); `M_range` never drifts below the
landed floor (`Mrange_one_floor` = GHS Lemmas 1+2, both landed) and restores the frozen
`prop_A3'` semantics.  The exit stone uses `M` only via the decreasing
`e^{−cM}` shape (`Real.exp_pos`, B4) — `M_range`-satisfied; the `g`
slot (the ball-center character) is retained for interface symmetry with the twins. -/
theorem halasz_ball_decay
    {f g : ℕ → ℂ} (_hf : ∀ n, ‖f n‖ ≤ 1) (_hg : ∀ n, ‖g n‖ ≤ 1)
    {X ε U Uhead Utail C₁ C₂ T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X * Real.exp (-(1 / Real.exp 1) * M_range f X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2)) :
    U ≤ (C₁ + C₂) * X
        * (Real.exp (-(1 / Real.exp 1) * M_range f X T)
          + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hX0' : 0 ≤ X := hX0.le
  have hlogX : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).mpr hX
  set M := M_range f X T with hMdef
  have hE : (0 : ℝ) ≤ Real.exp (-(1 / Real.exp 1) * M) := (Real.exp_pos _).le
  have hT : (0 : ℝ) ≤ (Real.log X) ^ (-(1 : ℝ) / 2 + ε) :=
    Real.rpow_nonneg (by linarith) _
  have htail' : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2 + ε) := by
    refine htail.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_exponent_le hlogX (by linarith)
  rw [hsplit]
  calc Uhead + Utail
      ≤ C₁ * X * Real.exp (-(1 / Real.exp 1) * M)
          + C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2 + ε) :=
        add_le_add hhead htail'
    _ ≤ (C₁ + C₂) * X * (Real.exp (-(1 / Real.exp 1) * M)
          + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
        nlinarith [mul_nonneg (mul_nonneg hC₁ hX0') hT, mul_nonneg (mul_nonneg hC₂ hX0') hE]

end Salt.MR
