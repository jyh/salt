/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.MeasureTheory.Group.Integral
import Salt.MR.HalaszFactor

/-!
# HALASZ-IDENTITY — PART 1 opening stones (`HalaszIdentity`)

The three opening stones of the TERMINAL ASSEMBLY FREEZE, PART 1
(`docs/exploration/terminal-assembly-freeze.md`):

* **H-0** `seam_carrier_audit` — the exact relation between the seam coefficient
  `seamCoeff f (windowIndicator y (X/y)) t₀` (`= fgJ f t₀ y (X/y)`) and the
  `g`-built four-factor carriers (`𝒮 = smoothSeries`, `𝓛 = largeSeries`).  The
  audit isolates *what is TRUE unconditionally* (the LARGE carrier
  `ellLin (restrictAbove y g)` is shared exactly, for ANY `f`; the smooth carrier
  is the `f`-dependent `smoothPart y g (fgJ …)`) and the *route-(i) exactness*
  (`smoothPart y g (ellLin g) = ellLin (restrictBelow y g)`, the linearized datum
  makes `𝒮` exact), and delivers the *linearization defect as an explicit
  coefficient sequence*.  The H-EXIT statement shape is PROPOSED to the maestro
  (final message), never stated here (statement-layer law).

* **H-1** `seam_centering` — the `n^{-it₀}` centering change-of-variables (a
  full-line `t`-translation, SOUND) + the `β → 2β` substitution with the Jacobian
  tracked EXPLICITLY (`∫₀^{2η} F = 2 • ∫₀^η F(2·)`).  **THE FACTOR-2 MANDATE**:
  the honest GHS chain reproducing `(2.4) = Σf(n) − secondary` from the symmetric
  four-factor form requires a factor `2` that the frozen `prop21RHS` LACKS — see
  the module note below and the executor's final report.  Per the mandate, the
  substitution lemmas are LANDED and the full composition STOPS pending the
  maestro's `prop21RHS` amendment.

* **H-2** `seam_double_ftc` — the `(α,β)` collapse on the ALIGNED GHS-(2.3) form
  (`𝒮` genuinely fixed at `s`, a bare constant): the β-leg via
  `largeSeries_ftc_double_beta`, the α-leg via `shifted_dirichlet_ftc`, the
  `𝒮`-prefactor pulled out where constant.  The window truncation (the mismatched
  `+η` endpoint term) is NOT collapsed here — it routes to H-5.

## ⟦THE FACTOR-2 VERDICT (H-1, iron-rule-1 tier) — CONFIRMED⟧

GHS (`docs/sources/1706.03749v1.pdf`) derives, in Lemma 2.2 (p.8), the identity
`(2.3) = (2.4)` with the inner integral's `β` ranging over `[0, 2η]` and, after
the `c_{α,β} = c₀ − α − β/2` realignment (p.10, (2.5)), the symmetric shifts
`∓β/2`.  The Prop 2.1 proof (p.11) then says *"finally replace β by 2β"*: the
substitution `β = 2β′` sends `∫_{β=0}^{2η} G(β/2) dβ = 2 ∫_{β′=0}^{η} G(β′) dβ′`
— a **Jacobian factor of 2**.  Hence the TRUE identity is
`Σ_{n≤x} f(n) − secondary = 2 · (symmetric [0,η]² four-factor integral)`, i.e.
GHS's *printed* Prop 2.1 (2.1)=(2.2), which omits the `2`, is off by a factor 2.
This is immaterial to GHS (an upper bound absorbs the `2` into `≪`) but MATERIAL
to the two-sided `hfactor`.  The frozen `prop21RHS` (`HalaszRepAsm`) transcribes
the printed (2.1) faithfully and therefore **LACKS the factor 2**.  The mandate:
do NOT absorb it into `E`; the maestro amends `prop21RHS` before H-EXIT is stated.
See `beta_double_jacobian` (the factor made visible) and the final report.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators LSeries.notation
open ArithmeticFunction

/-! ## H-0 — `seam_carrier_audit`

The seam coefficient `seamCoeff f (windowIndicator y Y) t₀` is, by definition, the
concrete GHS window decomposition `fgJ f t₀ y Y` (`HalaszSeam`).  The audit derives
its exact factorization into the `g`-built carriers, starting from
`fgJ_factorization` (the L3' split) and `smoothPart` (`HalaszLambda`). -/

/-- **H-0 (a) — the seam coefficient IS `fgJ`.**  Definitional: the seam Dirichlet
coefficient integrated by `prop21_contour_leg` is exactly the concrete window
decomposition `fgJ` of `HalaszSeam`. -/
lemma seamCoeff_windowIndicator_eq_fgJ (f : ℕ → ℂ) (t₀ y Y : ℝ) :
    seamCoeff f (windowIndicator y Y) t₀ = fgJ f t₀ y Y := rfl

/-- **H-0 (b) — the LARGE carrier is shared exactly (ANY `f`).**  The seam
coefficient factors as `sPart_f ⍟ ℓ_above`, where the large factor
`ℓ_above = ellLin (restrictAbove y g)` is built purely from the prime datum `g`
and is the coefficient function of `𝓛 = largeSeries y g` — the SAME for every `f`.
The smooth factor `sPart_f = smoothPart y g (fgJ f t₀ y Y)` is `f`-dependent.
Restatement of `fgJ_factorization` (GHS `f = s ⋆ ℓ`, p.7). -/
lemma seam_carrier_factorization (f g : ℕ → ℂ) (t₀ y Y : ℝ) :
    fgJ f t₀ y Y
      = smoothPart y g (fgJ f t₀ y Y) ⍟ ellLin (restrictAbove y g) :=
  (fgJ_factorization f g t₀ y Y).symm

/-- **H-0 (c) — the smooth carrier, explicit.**  The seam's smooth part is the
seam coefficient deconvolved by the large-part Dirichlet inverse.  Definitional
(`smoothPart y g fg = fg ⍟ ℓ⁻¹_above`). -/
lemma seam_smoothCarrier_eq (f g : ℕ → ℂ) (t₀ y Y : ℝ) :
    smoothPart y g (fgJ f t₀ y Y)
      = fgJ f t₀ y Y ⍟ ellLinInv (restrictAbove y g) := rfl

/-- **H-0 (d) — the windowed-vs-full coefficient decomposition.**  The seam
coefficient is the `{0,1}` window times the un-windowed twisted `f`.  (The
main-mass out-of-window defect at the CARRIER level routes to H-5; this is the
coefficient-level factorization.) -/
lemma fgJ_eq_window_mul (f : ℕ → ℂ) (t₀ y Y : ℝ) (n : ℕ) :
    fgJ f t₀ y Y n = windowIndicator y Y n * seamCoeff f (fun _ => 1) t₀ n := by
  unfold fgJ seamCoeff
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]; ring

/-- **H-0 (e) — route-(i) exactness at the linearized datum.**  When the seam
coefficient IS the fully linearized `g`-twist `ellLin g`, the smooth carrier
recovers `ellLin (restrictBelow y g)` EXACTLY — so `LSeries (smoothPart …)`
becomes `smoothSeries y g` (`= 𝒮`), i.e. the `g`-built `𝒮` of `prop21RHS` is
exact.  Route: the split product law `ellLin_split_toAF` + the Dirichlet-inverse
unit `ellLin_toAF_mul_inv` at the LARGE datum.  (`f = ellLin g` is the route-(i)
hypothesis; see the H-EXIT proposal.) -/
theorem smoothPart_ellLin_eq_restrictBelow (y : ℝ) (g : ℕ → ℂ) :
    smoothPart y g (ellLin g) = ellLin (restrictBelow y g) := by
  change ⇑(toArithmeticFunction (ellLin g)
      * toArithmeticFunction (ellLinInv (restrictAbove y g)))
    = ellLin (restrictBelow y g)
  rw [ellLin_split_toAF y g, mul_assoc, ellLin_toAF_mul_inv (restrictAbove y g), mul_one]
  funext n
  rw [toAF_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl]; simp [ellLin]
  · rw [if_neg hn]

/-- Bilinearity (left) of Dirichlet convolution: `(A − B) ⍟ c = A ⍟ c − B ⍟ c`,
pointwise.  The mechanism turning the seam-datum defect into the smooth-carrier
defect. -/
lemma convolution_sub_left (A B c : ℕ → ℂ) :
    ((fun n => A n - B n) ⍟ c) = fun n => (A ⍟ c) n - (B ⍟ c) n := by
  funext n
  simp only [LSeries.convolution_def]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun p _ => by rw [sub_mul])

/-- **H-0 (f) — THE LINEARIZATION DEFECT as an explicit coefficient sequence.**
For a GENERIC `f`, the smooth carrier splits as the exact `g`-built coefficient
`ellLin (restrictBelow y g)` PLUS the defect
`(fgJ f t₀ y Y − ellLin g) ⍟ ellLinInv (restrictAbove y g)` — the seam-datum
defect `fgJ − ellLin g` deconvolved by the large-part inverse.  This is GHS's
`Λ_f / log n` prime-power linearization defect, made a concrete coefficient
sequence: the route-(ii) term that would be bounded and added to `E`. -/
theorem seam_linearization_defect (f g : ℕ → ℂ) (t₀ y Y : ℝ) (n : ℕ) :
    smoothPart y g (fgJ f t₀ y Y) n
      = ellLin (restrictBelow y g) n
        + ((fun k => fgJ f t₀ y Y k - ellLin g k) ⍟ ellLinInv (restrictAbove y g)) n := by
  have hbelow : ellLin (restrictBelow y g) n
      = (ellLin g ⍟ ellLinInv (restrictAbove y g)) n := by
    rw [← smoothPart_ellLin_eq_restrictBelow y g]; rfl
  rw [hbelow, convolution_sub_left]
  change (fgJ f t₀ y Y ⍟ ellLinInv (restrictAbove y g)) n
      = (ellLin g ⍟ ellLinInv (restrictAbove y g)) n
        + ((fgJ f t₀ y Y ⍟ ellLinInv (restrictAbove y g)) n
            - (ellLin g ⍟ ellLinInv (restrictAbove y g)) n)
  ring

/-! ## H-1 — `seam_centering` (the centering c-o-v + the β→2β Jacobian)

The two SOUND substitution lemmas of H-1.  The full composition against the frozen
`prop21RHS` is STOPPED per THE FACTOR-2 MANDATE (module note): the honest chain
needs a factor `2` that `prop21RHS` lacks. -/

/-- **H-1 (a) — the `n^{-it₀}` centering identity.**  The `t₀`-twisted seam
Dirichlet series at `s` equals the UN-twisted series at the recentered point
`s + t₀·i`: the twist `n^{-it₀}` is absorbed by shifting the imaginary part of the
argument.  Termwise `n^{-it₀}/n^s = 1/n^{s+it₀}`; SOUND (HF-REF-A's twist
verdict). -/
lemma seamDirichlet_twist (f gJ : ℕ → ℂ) (t₀ : ℝ) (s : ℂ) :
    seamDirichlet f gJ t₀ s = seamDirichlet f gJ 0 (s + (t₀ : ℂ) * I) := by
  unfold seamDirichlet
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [seamCoeff]
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [seamCoeff, seamCoeff, if_neg hn, if_neg hn]
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one]
    rw [Complex.cpow_add _ _ hnC, show -(t₀ : ℂ) * I = -((t₀ : ℂ) * I) by ring,
      Complex.cpow_neg, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

/-- **H-1 (a′) — the centering under the contour integral.**  The `t₀`-twisted
seam contour integral (kernel at `t`) equals the UN-twisted seam contour integral
with the kernel CENTERED at `t − t₀` (matching `prop21RHS`'s `hatKernel … (t−t₀)`).
Route: the twist identity `seamDirichlet_twist` recenters the argument to
`c₀ + (t+t₀)i`, then the full-line translation invariance
`integral_add_right_eq_self` slides `t ↦ t − t₀`. -/
theorem seam_centering (f gJ : ℕ → ℂ) (t₀ X h c₀ : ℝ) :
    (∫ t : ℝ, seamDirichlet f gJ t₀ ((c₀ : ℂ) + (t : ℂ) * I) * hatKernel X h c₀ t)
      = ∫ t : ℝ,
          seamDirichlet f gJ 0 ((c₀ : ℂ) + (t : ℂ) * I) * hatKernel X h c₀ (t - t₀) := by
  have hcong : ∀ t : ℝ,
      seamDirichlet f gJ t₀ ((c₀ : ℂ) + (t : ℂ) * I) * hatKernel X h c₀ t
        = (fun u : ℝ => seamDirichlet f gJ 0 ((c₀ : ℂ) + (u : ℂ) * I)
              * hatKernel X h c₀ (u - t₀)) (t + t₀) := by
    intro t
    change seamDirichlet f gJ t₀ ((c₀ : ℂ) + (t : ℂ) * I) * hatKernel X h c₀ t
        = seamDirichlet f gJ 0 ((c₀ : ℂ) + ((t + t₀ : ℝ) : ℂ) * I)
            * hatKernel X h c₀ (t + t₀ - t₀)
    rw [seamDirichlet_twist f gJ t₀ ((c₀ : ℂ) + (t : ℂ) * I)]
    congr 1
    · congr 1; push_cast; ring
    · congr 1; ring
  calc (∫ t : ℝ, seamDirichlet f gJ t₀ ((c₀ : ℂ) + (t : ℂ) * I) * hatKernel X h c₀ t)
      = ∫ t : ℝ, (fun u : ℝ => seamDirichlet f gJ 0 ((c₀ : ℂ) + (u : ℂ) * I)
              * hatKernel X h c₀ (u - t₀)) (t + t₀) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcong)
    _ = ∫ u : ℝ, seamDirichlet f gJ 0 ((c₀ : ℂ) + (u : ℂ) * I) * hatKernel X h c₀ (u - t₀) :=
        integral_add_right_eq_self (μ := volume)
          (fun u : ℝ => seamDirichlet f gJ 0 ((c₀ : ℂ) + (u : ℂ) * I)
            * hatKernel X h c₀ (u - t₀)) t₀

/-- **H-1 (b) — THE β→2β JACOBIAN, made visible (THE FACTOR-2 MANDATE).**  GHS's
"replace β by 2β" (Prop 2.1 proof, p.11) is the substitution `β = 2β′` on the
`[0, 2η]` β-range: it produces an EXPLICIT factor of `2`.
`∫_{0}^{2η} F(β) dβ = 2 • ∫_{0}^{η} F(2β′) dβ′`.  This is the factor the frozen
`prop21RHS`'s symmetric `[0,η]²` form omits — see the module note and the report.
A direct instance of `intervalIntegral.smul_integral_comp_mul_left` at `c = 2`. -/
theorem beta_double_jacobian (F : ℝ → ℂ) (η : ℝ) :
    (∫ β in (0 : ℝ)..(2 * η), F β) = (2 : ℝ) • ∫ β in (0 : ℝ)..η, F (2 * β) := by
  have hsmul := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := η)
    (f := F) (2 : ℝ)
  rw [mul_zero] at hsmul
  exact hsmul.symm

/-! ## H-2 — `seam_double_ftc` (the (α,β) collapse on the ALIGNED (2.3)-form)

The collapse runs on the ALIGNED GHS-(2.3) form, `𝒮` genuinely fixed at `s` (a bare
constant `𝒮val`), NEVER on `prop21RHS`'s mixed `𝒮(s−α−β)` argument.  The β-leg
rides `largeSeries_ftc_double_beta` (the LANDED witness); the α-leg rides
`shifted_dirichlet_ftc`; the constant `𝒮`-prefactor is pulled out via
`integral_const_mul`.  The window truncation — the mismatched endpoint term
`largeSeries ((s+α)+η)` — is NOT collapsed here; it is the H-5 residual. -/

/-- **H-2 (α-leg) — the α-FTC with the `𝒮`-prefactor pulled out.**  With `𝒮` fixed
at the constant `𝒮val`, the α-integral of `𝒮val · Λ_ℓ·𝓛` at base `s` collapses to
the `𝓛` endpoint difference: `shifted_dirichlet_ftc` at the large datum with the
constant pulled through `integral_const_mul`.  (GHS's `∫₀^η 𝓛'(s+α) dα = 𝓛(s+η) − 𝓛(s)`
half, p.9, the term that closes the first two terms of (2.4).) -/
theorem seam_alpha_collapse (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (𝒮val : ℂ) {s : ℂ} (hs : 1 < s.re) {η : ℝ} (hη : 0 ≤ η) :
    (∫ α in (0 : ℝ)..η, 𝒮val
        * (LSeries (lambdaLin (restrictAbove y g)) (s + (α : ℂ))
            * largeSeries y g (s + (α : ℂ))))
      = 𝒮val * (largeSeries y g s - largeSeries y g (s + (η : ℂ))) := by
  rw [intervalIntegral.integral_const_mul]
  congr 1
  simpa only [largeSeries] using
    shifted_dirichlet_ftc (restrictAbove y g) (restrictAbove_norm_le hg) hs hη

/-- **H-2 (β-leg) — the β-collapse with the `𝒮`-prefactor pulled out.**  The inner
β-integral of the `(α,β)` double integral collapses to the `𝓛` endpoint difference
under the outer α-integral, with the constant `𝒮val` pulled through both integrals:
`largeSeries_ftc_double_beta` (the LANDED spine witness) prefixed by `𝒮val`.  (GHS's
`∫₀^{2η} 𝓛'(s+α+β) dβ = 𝓛(s+α+2η) − 𝓛(s+α)` β-half, p.8, here at the `[0,η]`
range of the landed witness.) -/
theorem seam_beta_collapse (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (𝒮val : ℂ) {w : ℂ} (hw : 1 < w.re) {η : ℝ} (hη : 0 ≤ η) :
    (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        𝒮val * (LSeries (lambdaLin (restrictAbove y g)) ((w + (α : ℂ)) + (β : ℂ))
            * largeSeries y g ((w + (α : ℂ)) + (β : ℂ))))
      = 𝒮val * ∫ α in (0 : ℝ)..η,
          (largeSeries y g (w + (α : ℂ)) - largeSeries y g ((w + (α : ℂ)) + (η : ℂ))) := by
  have hpull : ∀ α : ℝ,
      (∫ β in (0 : ℝ)..η,
          𝒮val * (LSeries (lambdaLin (restrictAbove y g)) ((w + (α : ℂ)) + (β : ℂ))
              * largeSeries y g ((w + (α : ℂ)) + (β : ℂ))))
        = 𝒮val * ∫ β in (0 : ℝ)..η,
            (LSeries (lambdaLin (restrictAbove y g)) ((w + (α : ℂ)) + (β : ℂ))
              * largeSeries y g ((w + (α : ℂ)) + (β : ℂ))) :=
    fun α => intervalIntegral.integral_const_mul _ _
  rw [intervalIntegral.integral_congr (fun α _ => hpull α),
    intervalIntegral.integral_const_mul, largeSeries_ftc_double_beta y g hg hw hη]

/-- **H-2 (the aligned collapse) — `seam_double_ftc`.**  The FULL β-collapse of the
aligned GHS-(2.3) integrand
`𝒮val · Λ_ℓ(s+α) · (Λ_ℓ((s+α)+β) · 𝓛((s+α)+β))` (product form, `𝒮` fixed): the
inner β-integral collapses via `shifted_dirichlet_ftc` at base `s+α`, carrying the
α-dependent prefactor `Λ_ℓ(s+α)`, to `𝓛(s+α) − 𝓛((s+α)+η)`.  The outer α-integral is
LEFT in GHS's post-β form `∫₀^η 𝒮val·Λ_ℓ(s+α)·(𝓛(s+α) − 𝓛((s+α)+η)) dα` (GHS p.8);
its FTC-collapsible half `𝓛(s+α)` closes via `seam_alpha_collapse`, and the
mismatched half `𝓛((s+α)+η)` is the H-5 window-truncation residual (NOT collapsed
here). -/
theorem seam_double_ftc (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (𝒮val : ℂ) {s : ℂ} (hs : 1 < s.re) {η : ℝ} (hη : 0 ≤ η) :
    (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        𝒮val * (LSeries (lambdaLin (restrictAbove y g)) (s + (α : ℂ))
            * (LSeries (lambdaLin (restrictAbove y g)) ((s + (α : ℂ)) + (β : ℂ))
                * largeSeries y g ((s + (α : ℂ)) + (β : ℂ)))))
      = ∫ α in (0 : ℝ)..η,
          𝒮val * (LSeries (lambdaLin (restrictAbove y g)) (s + (α : ℂ))
            * (largeSeries y g (s + (α : ℂ)) - largeSeries y g ((s + (α : ℂ)) + (η : ℂ)))) := by
  refine intervalIntegral.integral_congr (fun α hα => ?_)
  have hα0 : 0 ≤ α := by
    rcases Set.mem_uIcc.mp hα with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hsα : 1 < (s + (α : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_const_mul]
  congr 1
  simpa only [largeSeries] using
    shifted_dirichlet_ftc (restrictAbove y g) (restrictAbove_norm_le hg) hsα hη


/-! ## H-4 — `four_factor_hat_rep` (THE RISK STONE)

The exact coefficient representation of `prop21RHS`'s inner `t`-integral.  The design
insight (freeze §H-4) realized: the `(α,β)`-shifted four-factor product
`𝒮(s-α-β)·𝓛(s+β)·P(s-β)·P(s+β)` is ONE Dirichlet series with the four-fold *convolved*
coefficients `fourFactorCoeff` (three finite legs — the `y`-smooth `𝒮` and the two window
polynomials `P` — convolved first, the infinite `𝓛` leg last, on the `LSeries_convolution'`
rail, never `kconv`/`dpoly_pow`); `hat_contour_rep` applied in REVERSE reads the inner
integral off as the hat-smoothed sum of those coefficients.  No sharp Perron, no
multivariable analysis: Finset convolution algebra + the landed hat kernel.

The five anticipated helper layers (freeze-enumerated): (1) shifted-coefficient
`LSeriesSummable` at `c₀` via FINITE SUPPORT for the `𝒮·P·P` legs (`𝒮` is supported on the
`y`-smooth squarefree numbers — a divisor set of `primorial ⌊y⌋₊`; `smoothSeries_summable`
restated off `re > 1`); (2) iterated `LSeries_convolution'`; (3) the norm-convolution
summability gate (via absolute `LSeriesSummable` of the convolution — no crude `n^{2η}`);
(4) reverse `hat_contour_rep`; (5) the `t₀`-centering compatibility
(`integral_add_right_eq_self`). -/


/-- Shift a coefficient sequence: `a(n)·n^w`; makes `L(shiftCoeff w a) s = L a (s-w)`. -/
def shiftCoeff (w : ℂ) (a : ℕ → ℂ) : ℕ → ℂ := fun n => a n * (n : ℂ) ^ w

@[simp] lemma shiftCoeff_zero (w : ℂ) (a : ℕ → ℂ) (ha : a 0 = 0) : shiftCoeff w a 0 = 0 := by
  simp [shiftCoeff, ha]

/-- Termwise, the shifted coefficient at `s` matches the original at the shifted point `s - w`. -/
lemma term_shiftCoeff (w : ℂ) (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (shiftCoeff w a) s n = LSeries.term a (s - w) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, shiftCoeff,
      Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn)]
    field_simp

lemma LSeries_shiftCoeff (w : ℂ) (a : ℕ → ℂ) (s : ℂ) :
    LSeries (shiftCoeff w a) s = LSeries a (s - w) :=
  tsum_congr (term_shiftCoeff w a s)

lemma LSeriesSummable_shiftCoeff {w : ℂ} {a : ℕ → ℂ} {s : ℂ}
    (h : LSeriesSummable a (s - w)) : LSeriesSummable (shiftCoeff w a) s := by
  rw [LSeriesSummable, funext (term_shiftCoeff w a s)]; exact h

/-- Finite support of a sequence lifts to `LSeriesSummable` at every `s`. -/
lemma LSeriesSummable_of_finite_support {a : ℕ → ℂ}
    (h : (Function.support a).Finite) (s : ℂ) : LSeriesSummable a s := by
  refine summable_of_hasFiniteSupport (h.subset ?_)
  intro n hn
  rw [Function.mem_support] at hn ⊢
  intro ha
  apply hn
  rcases eq_or_ne n 0 with rfl | hne
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hne, ha, zero_div]

/-- The smooth (`p ≤ y`) linearized twist has FINITE support: every nonzero value is at a
squarefree number whose prime factors are all `≤ y`, hence a divisor of `primorial ⌊y⌋₊`. -/
lemma finite_support_ellLin_restrictBelow (y : ℝ) (g : ℕ → ℂ) :
    (Function.support (ellLin (restrictBelow y g))).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (primorial ⌊y⌋₊).divisors)
  intro n hn
  rw [Function.mem_support] at hn
  -- unpack `ellLin (restrictBelow y g) n ≠ 0`
  have hn0 : n ≠ 0 := by rintro rfl; simp [ellLin] at hn
  have hsq : Squarefree n := by
    by_contra hsq
    simp only [ellLin, if_neg hn0, if_neg hsq, ne_eq, not_true_eq_false] at hn
  have hprod : ∏ p ∈ n.primeFactors, restrictBelow y g p ≠ 0 := by
    simpa only [ellLin, if_neg hn0, if_pos hsq] using hn
  have hple : ∀ p ∈ n.primeFactors, p ≤ ⌊y⌋₊ := by
    intro p hp
    have hpne : restrictBelow y g p ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) p hp
    have : (p : ℝ) ≤ y := by
      by_contra hlt
      simp only [restrictBelow, if_neg hlt] at hpne; exact hpne rfl
    exact Nat.le_floor this
  -- membership in the primorial's divisor set
  have hsub : n.primeFactors ⊆ (Finset.range (⌊y⌋₊ + 1)).filter (fun p => Nat.Prime p) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hple p hp), Nat.prime_of_mem_primeFactors hp⟩
  have hdvd : n ∣ primorial ⌊y⌋₊ := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, primorial]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  rw [Finset.mem_coe, Nat.mem_divisors]
  exact ⟨hdvd, (primorial_pos _).ne'⟩

/-- The window Dirichlet-polynomial coefficient: the windowed large von Mangoldt analog. -/
def winCoeff (g : ℕ → ℂ) (X y : ℝ) : ℕ → ℂ :=
  fun n => if n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ then lambdaLin (restrictAbove y g) n else 0

@[simp] lemma winCoeff_zero (g : ℕ → ℂ) (X y : ℝ) : winCoeff g X y 0 = 0 := by
  simp only [winCoeff, Finset.mem_Ioo]
  rw [if_neg]; rintro ⟨h, _⟩; exact absurd h (by omega)

lemma finite_support_winCoeff (g : ℕ → ℂ) (X y : ℝ) :
    (Function.support (winCoeff g X y)).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊))
  intro n hn
  rw [Function.mem_support] at hn
  by_contra hmem
  rw [Finset.mem_coe] at hmem
  simp only [winCoeff, if_neg hmem] at hn
  exact hn rfl

/-- The window Dirichlet polynomial is the L-series of its (finite-support) coefficient. -/
lemma windowSum_eq_LSeries (g : ℕ → ℂ) (X y : ℝ) (s : ℂ) :
    windowSum g X y s = LSeries (winCoeff g X y) s := by
  rw [windowSum, LSeries]
  rw [tsum_eq_sum (s := Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) (fun n hn => ?_)]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : n ≠ 0 := by rw [Finset.mem_Ioo] at hn; omega
    rw [LSeries.term_of_ne_zero hn0, winCoeff, if_pos hn]
  · rcases eq_or_ne n 0 with rfl | hne
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hne, winCoeff, if_neg hn, zero_div]

/-- `shiftCoeff` preserves finite support. -/
lemma finite_support_shiftCoeff (w : ℂ) {a : ℕ → ℂ} (h : (Function.support a).Finite) :
    (Function.support (shiftCoeff w a)).Finite := by
  refine h.subset (fun n hn => ?_)
  rw [Function.mem_support] at hn ⊢
  intro ha; exact hn (by simp [shiftCoeff, ha])

/-- The large (`p > y`) shifted coefficient is `1`-bounded at each `n ≥ 1` (for `β ≥ 0`). -/
lemma largeC_norm_le {y : ℝ} {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {β : ℝ}
    (hβ : 0 ≤ β) {n : ℕ} (hn : 1 ≤ n) :
    ‖shiftCoeff (-(β : ℂ)) (ellLin (restrictAbove y g)) n‖ ≤ 1 := by
  have hn0 : 0 < n := hn
  rw [shiftCoeff, norm_mul, Complex.norm_natCast_cpow_of_pos hn0]
  have hre : (-(β : ℂ)).re = -β := by simp
  rw [hre]
  have h1 : ‖ellLin (restrictAbove y g) n‖ ≤ 1 :=
    ellLin_norm_le_one (restrictAbove y g) (restrictAbove_norm_le hg) n
  have h2 : (n : ℝ) ^ (-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  calc ‖ellLin (restrictAbove y g) n‖ * (n : ℝ) ^ (-β)
      ≤ 1 * 1 := mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) zero_le_one
    _ = 1 := mul_one 1

/-- The four-fold convolution coefficient of the `(α,β)`-shifted four-factor product.
The three finite legs (smooth `𝒮`, both windows `P`) are convolved first; the infinite
`𝓛` leg is convolved last (matching the freeze's "finite×infinite" instruction). -/
def fourFactorCoeff (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) : ℕ → ℂ :=
  ((shiftCoeff ((α : ℂ) + (β : ℂ)) (ellLin (restrictBelow y g))
      ⍟ shiftCoeff (β : ℂ) (winCoeff g X y))
      ⍟ shiftCoeff (-(β : ℂ)) (winCoeff g X y))
      ⍟ shiftCoeff (-(β : ℂ)) (ellLin (restrictAbove y g))

/-- **H-4 layer (2) — the four-factor product IS a single Dirichlet series.**  On `1 < re s`
(and `β ≥ 0`), the `(α,β)`-shifted four-factor product `𝒮(s-α-β)·𝓛(s+β)·P(s-β)·P(s+β)`
equals the L-series of the four-fold convolution `fourFactorCoeff`.  Route: each factor is
the L-series of a shifted coefficient (`LSeries_shiftCoeff`); the three finite legs are
`LSeriesSummable` everywhere (finite support), the `𝓛` leg on `re > 1` (bounded); the
product factors by `LSeries_convolution'`. -/
theorem four_factor_LSeries (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (X α : ℝ) {β : ℝ} (hβ : 0 ≤ β) {s : ℂ} (hs : 1 < s.re) :
    smoothSeries y g (s - (α : ℂ) - (β : ℂ)) * largeSeries y g (s + (β : ℂ))
        * windowSum g X y (s - (β : ℂ)) * windowSum g X y (s + (β : ℂ))
      = LSeries (fourFactorCoeff y g X α β) s := by
  -- the four shifted coefficient legs
  set A := shiftCoeff ((α : ℂ) + (β : ℂ)) (ellLin (restrictBelow y g)) with hA
  set Cc := shiftCoeff (β : ℂ) (winCoeff g X y) with hCc
  set D := shiftCoeff (-(β : ℂ)) (winCoeff g X y) with hD
  set B := shiftCoeff (-(β : ℂ)) (ellLin (restrictAbove y g)) with hB
  -- summabilities
  have hAsum : ∀ z, LSeriesSummable A z := fun z =>
    LSeriesSummable_of_finite_support
      (finite_support_shiftCoeff _ (finite_support_ellLin_restrictBelow y g)) z
  have hCsum : ∀ z, LSeriesSummable Cc z := fun z =>
    LSeriesSummable_of_finite_support
      (finite_support_shiftCoeff _ (finite_support_winCoeff g X y)) z
  have hDsum : ∀ z, LSeriesSummable D z := fun z =>
    LSeriesSummable_of_finite_support
      (finite_support_shiftCoeff _ (finite_support_winCoeff g X y)) z
  have hBsum : LSeriesSummable B s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn => largeC_norm_le hg hβ (Nat.one_le_iff_ne_zero.mpr hn)) hs
  -- the convolution product
  rw [fourFactorCoeff, ← hA, ← hCc, ← hD, ← hB,
    LSeries_convolution' ((hAsum s).convolution (hCsum s) |>.convolution (hDsum s)) hBsum,
    LSeries_convolution' ((hAsum s).convolution (hCsum s)) (hDsum s),
    LSeries_convolution' (hAsum s) (hCsum s)]
  -- identify each leg
  rw [hA, LSeries_shiftCoeff, hCc, LSeries_shiftCoeff, hD, LSeries_shiftCoeff,
    hB, LSeries_shiftCoeff]
  rw [← windowSum_eq_LSeries, ← windowSum_eq_LSeries]
  simp only [smoothSeries, largeSeries]
  rw [show s - ((α : ℂ) + (β : ℂ)) = s - (α : ℂ) - (β : ℂ) by ring,
    show s - -(β : ℂ) = s + (β : ℂ) by ring]
  ring

@[simp] lemma fourFactorCoeff_zero (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) :
    fourFactorCoeff y g X α β 0 = 0 := by
  rw [fourFactorCoeff, LSeries.convolution_def]; simp

/-- `fourFactorCoeff` is `LSeriesSummable` on `1 < re s` (three finite legs + the bounded
`𝓛` leg). -/
lemma LSeriesSummable_fourFactorCoeff (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (X α : ℝ) {β : ℝ} (hβ : 0 ≤ β) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fourFactorCoeff y g X α β) s := by
  have hAsum : LSeriesSummable (shiftCoeff ((α : ℂ) + (β : ℂ)) (ellLin (restrictBelow y g))) s :=
    LSeriesSummable_of_finite_support
      (finite_support_shiftCoeff _ (finite_support_ellLin_restrictBelow y g)) s
  have hCsum : LSeriesSummable (shiftCoeff (β : ℂ) (winCoeff g X y)) s :=
    LSeriesSummable_of_finite_support
      (finite_support_shiftCoeff _ (finite_support_winCoeff g X y)) s
  have hDsum : LSeriesSummable (shiftCoeff (-(β : ℂ)) (winCoeff g X y)) s :=
    LSeriesSummable_of_finite_support
      (finite_support_shiftCoeff _ (finite_support_winCoeff g X y)) s
  have hBsum : LSeriesSummable (shiftCoeff (-(β : ℂ)) (ellLin (restrictAbove y g))) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn => largeC_norm_le hg hβ (Nat.one_le_iff_ne_zero.mpr hn)) hs
  exact (((hAsum.convolution hCsum).convolution hDsum).convolution hBsum)

/-- **H-4 layer (3) — the `hat_contour_rep` summability gate.**  The weighted coefficient
sum `∑ ‖C_N‖((X+h)/N)^c` converges: it equals `(X+h)^c` times the *absolute* L-series
summability of `fourFactorCoeff` at `c` (a convolution of summable legs — no crude
`n^{2η}` absorption). -/
theorem fourFactor_weight_summable (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (X α : ℝ) {β : ℝ} (hβ : 0 ≤ β) {h c : ℝ} (hXh : 0 < X + h) (hc : 1 < c) :
    Summable (fun N => ‖fourFactorCoeff y g X α β N‖ * ((X + h) / (N : ℝ)) ^ c) := by
  have hCsum : LSeriesSummable (fourFactorCoeff y g X α β) (c : ℂ) :=
    LSeriesSummable_fourFactorCoeff y g hg X α hβ (by simpa using hc)
  have hnorm : Summable (fun N => ‖LSeries.term (fourFactorCoeff y g X α β) (c : ℂ) N‖) :=
    hCsum.norm
  refine (hnorm.mul_left ((X + h) ^ c)).congr (fun N => ?_)
  rcases eq_or_ne N 0 with rfl | hN
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hN, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN), Complex.ofReal_re,
      Real.div_rpow hXh.le (Nat.cast_nonneg N)]
    have hNc : (0 : ℝ) < (N : ℝ) ^ c :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hN) c
    field_simp

/-- Convert the naive tsum `∑ a(n)/n^s` (with `a 0 = 0`) into the mathlib `LSeries`. -/
lemma tsum_div_eq_LSeries {a : ℕ → ℂ} (ha0 : a 0 = 0) (s : ℂ) :
    (∑' n, a n / (n : ℂ) ^ s) = LSeries a s := by
  rw [LSeries]; refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, ha0]
  · rw [LSeries.term_of_ne_zero hn]

/-- **H-4 — `four_factor_hat_rep` (THE RISK STONE).**  `prop21RHS`'s inner `t`-integral
(per `(α,β)`, `β ≥ 0`) equals `2π` times the hat-smoothed sum of the four-fold convolved
coefficients `fourFactorCoeff`.  Route: the `t₀`-centering change-of-variables
(`integral_add_right_eq_self`, layer 5) aligns the kernel; `four_factor_LSeries` (layer 2)
turns the product into one Dirichlet series; `hat_contour_rep` applied in REVERSE (layer 4),
with the summability gate `fourFactor_weight_summable` (layer 3), reads off the coefficient
sum. -/
theorem four_factor_hat_rep (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) {t₀ X h c₀ : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc₀ : 1 < c₀) :
    (∫ t : ℝ,
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h c₀ (t - t₀))
      = (2 * Real.pi) • ∑' N, fourFactorCoeff y g X α β N * (hatK X h N : ℂ) := by
  set C := fourFactorCoeff y g X α β with hCdef
  have hC0 : C 0 = 0 := fourFactorCoeff_zero y g X α β
  -- centering: the integrand is `Ψ (t - t₀)`
  set Ψ : ℝ → ℂ := fun u =>
      smoothSeries y g (((c₀ : ℂ) + (u : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y g (((c₀ : ℂ) + (u : ℂ) * I) + (β : ℂ))
        * windowSum g X y (((c₀ : ℂ) + (u : ℂ) * I) - (β : ℂ))
        * windowSum g X y (((c₀ : ℂ) + (u : ℂ) * I) + (β : ℂ))
        * hatKernel X h c₀ u with hΨdef
  have hcenter : (∫ t : ℝ,
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h c₀ (t - t₀))
      = ∫ u : ℝ, Ψ u := by
    have h1 : (fun t : ℝ =>
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h c₀ (t - t₀)) = fun t : ℝ => Ψ (t - t₀) := rfl
    rw [h1]
    have := integral_add_right_eq_self (μ := volume) Ψ (-t₀)
    simpa [sub_eq_add_neg] using this
  rw [hcenter]
  -- align the four-factor product to the single Dirichlet series `LSeries C`
  have halign : (∫ u : ℝ, Ψ u)
      = ∫ u : ℝ, LSeries C ((c₀ : ℂ) + (u : ℂ) * I) * hatKernel X h c₀ u := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    rw [hΨdef]
    dsimp only
    rw [four_factor_LSeries y g hg X α hβ (s := (c₀ : ℂ) + (u : ℂ) * I) (by simpa using hc₀)]
  rw [halign]
  -- reverse hat_contour_rep
  have hgate : Summable (fun N => ‖C N‖ * ((X + h) / (N : ℝ)) ^ c₀) :=
    fourFactor_weight_summable y g hg X α hβ (by linarith : (0 : ℝ) < X + h) hc₀
  have hrep := hat_contour_rep C hC0 hX hh (by linarith : (0 : ℝ) < c₀) hgate
  -- rewrite hrep's inner tsum as `LSeries C` and its kernel expression as `hatKernel`
  have hrep' : (∑' N, C N * (hatK X h N : ℂ))
      = (1 / (2 * Real.pi)) •
          ∫ u : ℝ, LSeries C ((c₀ : ℂ) + (u : ℂ) * I) * hatKernel X h c₀ u := by
    rw [hrep]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    dsimp only
    rw [tsum_div_eq_LSeries hC0]
    rfl
  rw [hrep', smul_smul]
  rw [show (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 by
    field_simp, one_smul]

/-- **H-4 corollary — `prop21RHS` AS a coefficient sum.**  The frozen `prop21RHS`
(the `(α,β)` double integral of the four-factor product, with its leading `2`-Jacobian
and the centered hat kernel) equals `2·∫∫` of the hat-smoothed four-fold convolution
coefficient sum.  This is the exact object H-5's bridge reconciles against the seam
coefficient sum `∑ fgJ·hatK`. -/
theorem prop21RHS_hat_rep (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ X h c₀ y η : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc₀ : 1 < c₀) (hη : 0 ≤ η) :
    prop21RHS g t₀ X h c₀ y η
      = (2 : ℝ) • ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          ∑' N, fourFactorCoeff y g X α β N * (hatK X h N : ℂ) := by
  rw [prop21RHS]
  congr 1
  refine intervalIntegral.integral_congr (fun α _ => ?_)
  refine intervalIntegral.integral_congr (fun β hβmem => ?_)
  have hβ0 : 0 ≤ β := by
    rw [Set.uIcc_of_le hη] at hβmem; exact (Set.mem_Icc.mp hβmem).1
  rw [four_factor_hat_rep y g hg α hβ0 hX hh hc₀, smul_smul,
    show (1 / (2 * Real.pi)) * (2 * Real.pi) = 1 by field_simp, one_smul]

end Salt.MR
