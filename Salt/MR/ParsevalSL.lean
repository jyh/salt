/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MVCore2

/-!
# S8 MR-CORE, node A3a (ParsevalSL): the continuous Perron / Saffari–Vaughan layer

Source pin (freeze D5): **MR arXiv v4 only** (`docs/sources/1501.04585v4.pdf`).

## The frozen statement — Lemma 14 (MR v4, §7 "Parseval bound", pp. 21–23)

*Verbatim transcription (frozen at dispatch).*  Let `|aₘ| ≤ 1`.  Assume
`1 ≤ h₁ ≤ h₂ = X/(log X)^{1/5}`.  For `X ≤ x ≤ 2X` set
`Sⱼ(x) = ∑_{x ≤ m ≤ x+hⱼ} aₘ` and `A(s) := ∑_{X ≤ m ≤ 4X} aₘ/mˢ`.  Then

`(1/X) ∫_X^{2X} |(1/h₁)S₁(x) − (1/h₂)S₂(x)|² dx`
`  ≪ 1/(log X)^{2/15} + ∫_{1+i(log X)^{1/45}}^{1+iX/h₁} |A(s)|² |ds|`
`      + max_{T ≥ X/h₁} ((X/h₁)/T) ∫_{1+iT}^{1+i2T} |A(s)|² |ds|.`

*Transcription correction (2026-07-24, Fable tier, iron-rule-1 procedure):* the
original transcription dropped the `(X/h₁)/T` weight on the max-term.  Both corpus
copies of the source carry it (`docs/sources/mr_extract.md` §2.6 and the §8 table),
and it is load-bearing: without the weight the `max` over `T ≥ X/h₁` diverges
(`∫_{1+iT}^{1+i2T} |A|² ~ (4T+20N)·Σ|aₘ/m|²` grows with `T`), and the weight is what
produces Prop 1's `(T/(X/Q₁)+1)` grade.  Corrected to match MR v4 verbatim.

## Proof skeleton (MR v4 pp. 21–23) and where each ingredient lives

1. **Continuous Perron** (p. 21): `Sⱼ(x) = (1/2πi) ∫_{1−i∞}^{1+i∞} A(s)·((x+hⱼ)ˢ−xˢ)/s ds`.
   *Named residual* `A3a-R1` — a critical-line Perron representation (conditionally
   convergent); mathlib-absent, un-landed here.
2. **U/V split at `T₀ = (log X)^{1/45}`** (p. 22): on `|t| ≤ T₀` a Taylor expansion
   of `(x+hⱼ)ˢ−xˢ` gives the `1/(log X)^{2/15}` main term.  *Named residual* `A3a-R2`.
3. **Saffari–Vaughan smoothing** ([35, p. 25]) for the `Vⱼ` tail — the averaging
   identity that replaces `((x+h)ˢ−xˢ)/s`.  **LANDED here** as `sv_average_kernel`
   (abstract) and `sv_average_identity` (the concrete cpow instance).
4. **Parseval / mean value** — expand the square, exchange order, integrate over `x`,
   and apply the mean-value theorem (MR Lemma 6 = the `(T+O(N))` MVT).  The MVT is
   the landed `dirichlet_poly_l2_mvt_final` (`Salt/MR/MVCore2.lean`); the critical-line
   `|A(1+it)|²` form it consumes is **LANDED here** as `lpoly_mean_sq_bound`.

`[35] = B. Saffari and R. C. Vaughan, "On the fractional parts of x/n and related
sequences II", Ann. Inst. Fourier` (MR references).

## Warning honoured (freeze A3a line)

`Salt/LS/Parseval.lean:76` (`parseval`) is the *integer-frequency* identity
`∫₀¹ ‖expSum N a α‖² dα = ∑ ‖aₙ‖²` — a **pattern only**.  The continuous-frequency
core is the mean value on the critical line (`lpoly_mean_sq_bound`), which is genuinely
different analytic content and consumes the Montgomery–Vaughan `(2T+20N)` bound.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory Complex

/-! ## Grain (ii) — the Saffari–Vaughan averaging identity -/

/-- **The Saffari–Vaughan averaging kernel (abstract).**  If two integrands `F, G`
on `[h, 3h]` differ by the *constant* `K` (i.e. `F w − G w = K` for all `w`), then
`K` is recovered as `(1/2h)·(∫_h^{3h} F − ∫_h^{3h} G)`.  This is the exact mechanism
of MR's `(x+h)ˢ−xˢ = (1/2h)∫(…)` step (v4 p. 22, following Saffari–Vaughan [35, p. 25]):
the shared `(x+w)ˢ` cancels in the difference, leaving the constant `((x+h)ˢ−xˢ)/s`. -/
theorem sv_average_kernel {h : ℝ} (hh : 0 < h) (K : ℂ) (F G : ℝ → ℂ)
    (hFG : ∀ w, F w - G w = K)
    (hF : IntervalIntegrable F volume h (3 * h))
    (hG : IntervalIntegrable G volume h (3 * h)) :
    K = (1 / (2 * h)) • ((∫ w in h..(3 * h), F w) - ∫ w in h..(3 * h), G w) := by
  have hsub : (∫ w in h..(3 * h), F w) - (∫ w in h..(3 * h), G w)
      = ∫ w in h..(3 * h), (F w - G w) := (intervalIntegral.integral_sub hF hG).symm
  rw [hsub]
  have hK : (∫ w in h..(3 * h), (F w - G w)) = (2 * h) • K := by
    have hcong : (∫ w in h..(3 * h), (F w - G w)) = ∫ _w in h..(3 * h), K :=
      intervalIntegral.integral_congr (fun w _ => hFG w)
    rw [hcong, intervalIntegral.integral_const]
    congr 1
    ring
  rw [hK, smul_smul, one_div, inv_mul_cancel₀ (by positivity : (2 * h : ℝ) ≠ 0), one_smul]

/-- Interval integrability of `w ↦ (x+w)ˢ` on `[h, 3h]` for `0 < x`, `0 < h`
(the base `x+w ≥ x+h > 0` stays off the branch cut). -/
private lemma cpow_shift_intervalIntegrable {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (s : ℂ) :
    IntervalIntegrable (fun w : ℝ => ((x + w : ℝ) : ℂ) ^ s) volume h (3 * h) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : h ≤ 3 * h)]
  intro w hw
  rw [Set.mem_Icc] at hw
  have hxw : (0 : ℝ) < x + w := by linarith [hw.1]
  have hca : ContinuousAt (fun w : ℝ => ((x + w : ℝ) : ℂ) ^ s) w :=
    (continuousAt_ofReal_cpow_const (x + w) s (Or.inr hxw.ne')).comp
      (by fun_prop : ContinuousAt (fun w : ℝ => x + w) w)
  exact hca.continuousWithinAt

/-- **The Saffari–Vaughan averaging identity (concrete).**  The exact MR v4 p. 22
replacement: for `0 < x`, `0 < h` and any `s : ℂ`,
`((x+h)ˢ−xˢ)/s = (1/2h)·(∫_h^{3h} ((x+w)ˢ−xˢ)/s dw − ∫_h^{3h} ((x+w)ˢ−(x+h)ˢ)/s dw)`. -/
theorem sv_average_identity {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (s : ℂ) :
    (((x + h : ℝ) : ℂ) ^ s - ((x : ℝ) : ℂ) ^ s) / s
      = (1 / (2 * h)) • (
          (∫ w in h..(3 * h), (((x + w : ℝ) : ℂ) ^ s - ((x : ℝ) : ℂ) ^ s) / s)
          - ∫ w in h..(3 * h), (((x + w : ℝ) : ℂ) ^ s - ((x + h : ℝ) : ℂ) ^ s) / s) := by
  have hcpow := cpow_shift_intervalIntegrable hx hh s
  have hF : IntervalIntegrable
      (fun w : ℝ => (((x + w : ℝ) : ℂ) ^ s - ((x : ℝ) : ℂ) ^ s) / s) volume h (3 * h) := by
    simp_rw [sub_div]
    exact (hcpow.div_const s).sub intervalIntegrable_const
  have hG : IntervalIntegrable
      (fun w : ℝ => (((x + w : ℝ) : ℂ) ^ s - ((x + h : ℝ) : ℂ) ^ s) / s) volume h (3 * h) := by
    simp_rw [sub_div]
    exact (hcpow.div_const s).sub intervalIntegrable_const
  have hFG : ∀ w : ℝ, (((x + w : ℝ) : ℂ) ^ s - ((x : ℝ) : ℂ) ^ s) / s
      - (((x + w : ℝ) : ℂ) ^ s - ((x + h : ℝ) : ℂ) ^ s) / s
      = (((x + h : ℝ) : ℂ) ^ s - ((x : ℝ) : ℂ) ^ s) / s := by
    intro w; rw [div_sub_div_same]; congr 1; ring
  exact sv_average_kernel hh _ _ _ hFG hF hG

/-! ## Grain (i) — the continuous-frequency critical-line mean-value bound

`A(1+it) = ∑_{X≤m≤4X} aₘ m^{-1} e^{-it log m}`.  With `cₘ = aₘ/m` this is a
Dirichlet polynomial in the negated frequency; its mean square on `[-T,T]` is the
`|A(1+it)|²` integral that Lemma 14's RHS controls.  This IS the continuous-frequency
Parseval core; it consumes `dirichlet_poly_l2_mvt_final` (MR Lemma 6) directly. -/

/-- The critical-line Dirichlet polynomial `∑_{1≤m≤N} cₘ e^{-it log m}` (`= A(1+it)`
after `cₘ = aₘ/m`). -/
noncomputable def lpoly (N : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, c m * Complex.exp (-(Complex.I * (t : ℂ) * Real.log m))

/-- `lpoly N c t = dpoly N c (-t)`: the negated-frequency bridge to the landed L² MVT. -/
lemma lpoly_eq_dpoly_neg (N : ℕ) (c : ℕ → ℂ) (t : ℝ) : lpoly N c t = dpoly N c (-t) := by
  unfold lpoly dpoly
  refine Finset.sum_congr rfl fun n _ => ?_
  have hexp : (-(Complex.I * (t : ℂ) * Real.log n))
      = Complex.I * ((-t : ℝ) : ℂ) * Real.log n := by push_cast; ring
  rw [hexp]

/-- **Grain (i) — the continuous-frequency Parseval / mean-value bound.**  The mean
square of `A(1+it)` (as `lpoly`) over `[-T,T]` is bounded by the Montgomery–Vaughan
`(2T+20N)` factor times the coefficient `L²` mass — the critical-line form of MR's
Lemma 6, consumed by the Parseval step of Lemma 14.  Unconditional. -/
theorem lpoly_mean_sq_bound (N : ℕ) (c : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖lpoly N c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  have h1 : (∫ t in (-T)..T, ‖lpoly N c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖dpoly N c (-t)‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => by rw [lpoly_eq_dpoly_neg])
  have h2 : (∫ t in (-T)..T, ‖dpoly N c (-t)‖ ^ 2)
      = ∫ t in (-T)..T, ‖dpoly N c t‖ ^ 2 := by
    simpa using
      intervalIntegral.integral_comp_neg (f := fun t : ℝ => ‖dpoly N c t‖ ^ 2) (a := -T) (b := T)
  rw [h1, h2]
  exact dirichlet_poly_l2_mvt_final N c T

end Salt.MR
