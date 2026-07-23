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

/-! ## P21-3K — the mismatched-line hat rep (the amendment's cone repair)

AMENDMENT P21-3K (`docs/exploration/terminal-assembly-freeze.md`, `⟦A — AMENDMENT
P21-3K⟧`) centered the hat kernel's line on the four-factor argument shift:
`prop21RHS` now integrates against `hatKernel X h (c₀−α−β) (t−t₀)`, so its inner
integral pairs a Dirichlet series on the line `c₀` with a kernel on the line
`c₀−α−β`.  `hat_contour_rep` (`HalaszKernel`) requires a MATCHED line; this block
generalizes it — the line-gap `N^{c₀−(c₀−α−β)} = N^{α+β}` is absorbed into the
coefficient as `shiftCoeff (c'−c)`, depositing exactly the `N^{−(α+β)}`
compensation the audit demands (NUM-REF's standing tripwire). -/

/-- **P21-3K step 1 — the mismatched-line hat rep.**  Generalizes `hat_contour_rep`
to a kernel whose line `c'` differs from the series line `c`.  The gap is carried
by `shiftCoeff (c'−c)` (weight `N^{c'−c}`); the summability at `c'` reduces to the
ORIGINAL `c`-line gate because `‖shiftCoeff (c'−c) a N‖·((X+h)/N)^{c'} =
(X+h)^{c'−c}·(‖a N‖·((X+h)/N)^c)` (the shift and the kernel-line change cancel to a
constant).  Gate `0 < c'` is the regime `c₀−2η > 0` (the `y ≥ 10` floor) carried,
not proved, here. -/
theorem hat_contour_rep_mismatch (a : ℕ → ℂ) (ha0 : a 0 = 0) {X h c c' : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc' : 0 < c')
    (hsum : Summable fun n => ‖a n‖ * ((X + h) / (n : ℝ)) ^ c) :
    (∑' N, shiftCoeff ((c' : ℂ) - (c : ℂ)) a N * (hatK X h N : ℂ))
      = (1 / (2 * Real.pi)) •
          ∫ u : ℝ, LSeries a ((c : ℂ) + (u : ℂ) * I) * hatKernel X h c' u := by
  have hb0 : shiftCoeff ((c' : ℂ) - (c : ℂ)) a 0 = 0 := shiftCoeff_zero _ a ha0
  have hXh0 : (0 : ℝ) < X + h := by linarith
  -- the shifted summability at line `c'` reduces to the original `c`-line gate
  have hsum' : Summable
      (fun n => ‖shiftCoeff ((c' : ℂ) - (c : ℂ)) a n‖ * ((X + h) / (n : ℝ)) ^ c') := by
    refine (hsum.mul_left ((X + h) ^ (c' - c))).congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [shiftCoeff, ha0]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hXhc := (Real.rpow_pos_of_pos hXh0 c).ne'
      have hnc := (Real.rpow_pos_of_pos hn0 c).ne'
      have hnc' := (Real.rpow_pos_of_pos hn0 c').ne'
      rw [shiftCoeff, norm_mul, Complex.norm_natCast_cpow_of_pos hn,
        show ((c' : ℂ) - (c : ℂ)).re = c' - c by simp,
        Real.div_rpow hXh0.le hn0.le, Real.div_rpow hXh0.le hn0.le,
        Real.rpow_sub hXh0, Real.rpow_sub hn0]
      field_simp
  have hrep := hat_contour_rep (shiftCoeff ((c' : ℂ) - (c : ℂ)) a) hb0 hX hh hc' hsum'
  rw [hrep]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  dsimp only
  rw [tsum_div_eq_LSeries hb0, LSeries_shiftCoeff,
    show ((c' : ℂ) + (u : ℂ) * I) - ((c' : ℂ) - (c : ℂ)) = (c : ℂ) + (u : ℂ) * I by ring]
  rfl

/-- **P21-3K step 2 — the shifted four-factor hat rep.**  The amended `prop21RHS`
inner `t`-integral (kernel on the line `c₀−α−β`) equals `2π` times the hat-smoothed
sum of `fourFactorCoeff` carrying the `N^{−(α+β)}` line-compensation.  Route: the
`t₀`-centering (`integral_add_right_eq_self`) + `four_factor_LSeries` (the product is
one Dirichlet series on `c₀`) + `hat_contour_rep_mismatch` (the `c₀ → c₀−α−β`
line-gap deposits `N^{−(α+β)}`).  The gate `0 < c₀−α−β` is the carried regime. -/
theorem four_factor_hat_rep_shifted (y : ℝ) (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) {t₀ X h c₀ : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc₀ : 1 < c₀) (hc' : 0 < c₀ - α - β) :
    (∫ t : ℝ,
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀))
      = (2 * Real.pi) • ∑' N, fourFactorCoeff y g X α β N
          * (N : ℂ) ^ (-(α : ℂ) - (β : ℂ)) * (hatK X h N : ℂ) := by
  set C := fourFactorCoeff y g X α β with hCdef
  have hC0 : C 0 = 0 := fourFactorCoeff_zero y g X α β
  -- centering: the integrand is `Ψ (t - t₀)`
  set Ψ : ℝ → ℂ := fun u =>
      smoothSeries y g (((c₀ : ℂ) + (u : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y g (((c₀ : ℂ) + (u : ℂ) * I) + (β : ℂ))
        * windowSum g X y (((c₀ : ℂ) + (u : ℂ) * I) - (β : ℂ))
        * windowSum g X y (((c₀ : ℂ) + (u : ℂ) * I) + (β : ℂ))
        * hatKernel X h (c₀ - α - β) u with hΨdef
  have hcenter : (∫ t : ℝ,
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀))
      = ∫ u : ℝ, Ψ u := by
    have h1 : (fun t : ℝ =>
        smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀)) = fun t : ℝ => Ψ (t - t₀) := rfl
    rw [h1]
    have := integral_add_right_eq_self (μ := volume) Ψ (-t₀)
    simpa [sub_eq_add_neg] using this
  rw [hcenter]
  -- align the four-factor product to the single Dirichlet series `LSeries C`
  have halign : (∫ u : ℝ, Ψ u)
      = ∫ u : ℝ, LSeries C ((c₀ : ℂ) + (u : ℂ) * I) * hatKernel X h (c₀ - α - β) u := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    rw [hΨdef]
    dsimp only
    rw [four_factor_LSeries y g hg X α hβ (s := (c₀ : ℂ) + (u : ℂ) * I) (by simpa using hc₀)]
  rw [halign]
  -- the mismatched-line rep at series line `c₀`, kernel line `c₀−α−β`
  have hgate : Summable (fun N => ‖C N‖ * ((X + h) / (N : ℝ)) ^ c₀) :=
    fourFactor_weight_summable y g hg X α hβ (by linarith : (0 : ℝ) < X + h) hc₀
  have hmm := hat_contour_rep_mismatch C hC0 (c := c₀) (c' := c₀ - α - β) hX hh hc' hgate
  have hSeq : (∑' N, shiftCoeff (((c₀ - α - β : ℝ) : ℂ) - ((c₀ : ℝ) : ℂ)) C N * (hatK X h N : ℂ))
      = ∑' N, C N * (N : ℂ) ^ (-(α : ℂ) - (β : ℂ)) * (hatK X h N : ℂ) := by
    refine tsum_congr (fun N => ?_)
    rw [shiftCoeff,
      show (((c₀ - α - β : ℝ) : ℂ) - ((c₀ : ℝ) : ℂ)) = -(α : ℂ) - (β : ℂ) by push_cast; ring]
  have hI : (∫ u : ℝ, LSeries C ((c₀ : ℂ) + (u : ℂ) * I) * hatKernel X h (c₀ - α - β) u)
      = (2 * Real.pi) •
          (∑' N, shiftCoeff (((c₀ - α - β : ℝ) : ℂ) - ((c₀ : ℝ) : ℂ)) C N * (hatK X h N : ℂ)) := by
    rw [hmm, smul_smul, show (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 by field_simp, one_smul]
  rw [hI, hSeq]

/-- **H-4 corollary — `prop21RHS` AS a coefficient sum (P21-3K, the COMPENSATED
form).**  The amended `prop21RHS` (the `(α,β)` double integral of the four-factor
product, with its leading `2`-Jacobian and the LINE-CENTERED hat kernel
`hatKernel X h (c₀−α−β)`) equals `2·∫∫` of the hat-smoothed four-fold convolution
coefficient sum, EACH coefficient carrying the `N^{−(α+β)}` line-compensation the
amendment deposits (P21-3K).  NUM-REF's standing tripwire is manifest here: the
`(N:ℂ)^{−(α+β)}` factor is the audit's required compensation.  Re-proved at the
corrected definition via `four_factor_hat_rep_shifted`.  The regime gate
`0 < c₀−2η` (the `y ≥ 10` floor; `c₀−2η ≥ ~0.13`) is carried, not proved. -/
theorem prop21RHS_hat_rep (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ X h c₀ y η : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc₀ : 1 < c₀) (hη : 0 ≤ η)
    (hc' : 0 < c₀ - 2 * η) :
    prop21RHS g t₀ X h c₀ y η
      = (2 : ℝ) • ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          ∑' N, fourFactorCoeff y g X α β N * (N : ℂ) ^ (-(α : ℂ) - (β : ℂ))
            * (hatK X h N : ℂ) := by
  rw [prop21RHS]
  congr 1
  refine intervalIntegral.integral_congr (fun α hαmem => ?_)
  have hαη : α ≤ η := by rw [Set.uIcc_of_le hη] at hαmem; exact (Set.mem_Icc.mp hαmem).2
  refine intervalIntegral.integral_congr (fun β hβmem => ?_)
  have hβ0 : 0 ≤ β := by rw [Set.uIcc_of_le hη] at hβmem; exact (Set.mem_Icc.mp hβmem).1
  have hβη : β ≤ η := by rw [Set.uIcc_of_le hη] at hβmem; exact (Set.mem_Icc.mp hβmem).2
  have hc'αβ : 0 < c₀ - α - β := by linarith
  rw [four_factor_hat_rep_shifted y g hg α hβ0 hX hh hc₀ hc'αβ, smul_smul,
    show (1 / (2 * Real.pi)) * (2 * Real.pi) = 1 by field_simp, one_smul]

/-! ## H-1b — `seam_realignment` (THE HAT-REP SANDWICH — validated)

The amendment's design (freeze §⟦A⟧): `prop21RHS`'s symmetric four-factor form and the
ALIGNED GHS-(2.3) form (`𝒮` fixed, the shifts on the log-derivative/large legs) differ by
multiplicative reweightings `n^{±α}, n^{±β}` of the convolved coefficients.  This block
lands the SHIFTCOEFF ALGEBRA that is the sandwich's provable core: two reusable
distribution laws (`shiftCoeff_convolution`, `shiftCoeff_shiftCoeff`) and the regrouping
`fourFactorCoeff = shiftCoeff (α+β) alignedCoeff`.

### ⟦SANDWICH VALIDATION OUTCOME — the tripwire, reported (iron-rule-1 tier)⟧

The regrouping is EXACT and pure algebra (zero analysis), exactly as the design predicted.
But the validation also PINS the residual precisely: the global reweighting is
`shiftCoeff (α+β)`, and `α+β` is *not* zero, so under the hat-smoothed sum it does NOT
collapse:
`∑_N fourFactorCoeff·hatK = ∑_N alignedCoeff_N · N^{α+β} · hatK`  (`seam_realignment_hat`).
The `N^{α+β}` factor is `LSeries alignedCoeff` read on the SHIFTED argument `c₀−(α+β)+it`
(= GHS's `c_{α,β} = c₀−α−β/2` contour, with our `β↔2β` convention).  Consequently the
downstream stone H-5 (fire `seam_double_ftc` on the aligned form) is BLOCKED as designed:

* `seam_double_ftc` consumes the FULL log-derivative `LSeries (lambdaLin (restrictAbove))`,
  which converges only on `re > 1`; but `alignedCoeff`'s windowed `winCoeff` legs sit at
  arguments `w+α` with `re = c₀−β < 1` on the shifted line, where the window→full
  replacement (H-5a) is INVALID (the full log-derivative diverges there).
* Equivalently: after regrouping, `seam_double_ftc`'s FIXED base `s` is replaced by the
  `(α,β)`-DEPENDENT base `s−(α+β)`; the fixed-base FTC cannot fire, and removing the
  `(α,β)`-dependence is precisely the CONTOUR SHIFT the amendment forbade ("do NOT shift
  contours, do NOT touch Cauchy").
* The coefficient-level shortcut is also closed (BETA's wall, re-confirmed): the `β`-integral
  `∫₀^η (mk/(jn))^β dβ = ((mk/(jn))^η−1)/log(mk/(jn))` couples the four convolution indices —
  no telescoping.  The main term telescopes ONLY through the analytic FTC, which needs the
  convergent line.

The bridge from `∑_N alignedCoeff_N N^{α+β} hatK` to the telescoped main term is therefore
GHS's Lemma 2.5 (truncate the integral at height `T`, move the line, price the Perron
truncation error) — the multivariable-Perron / line-moving analytic core, i.e. the
CAMPAIGN-GATE fallback the brief instructs never to attempt in an executor loop.  H-1b lands
here (the sandwich's algebra + the explicit residual); H-5/H-EXIT are STOPPED at this wall
per the fail-fast mandate.  See the executor's final report.

### ⟦P21-3K CODA (2026-07-22, maestro-ruled) — THE WALL IS DISSOLVED⟧

The wall this note records is DISSOLVED by AMENDMENT P21-3K (`HalaszRepAsm`'s `prop21RHS`
docstring; `docs/exploration/terminal-assembly-freeze.md`, `⟦A — AMENDMENT P21-3K⟧`).  The
`N^{α+β}` residual `seam_realignment_hat` pins was an artifact of the frozen HYBRID object
(post-line-move FACTORS against a pre-move, `(α,β)`-free kernel).  The amended definition
centers the kernel line on the shift — `hatKernel X h (c₀−α−β)` — so the kernel deposits
`N^{−(α+β)}` per coefficient, cancelling the `N^{α+β}` EXACTLY.  There is no shifted-line
residual and no line-moving fallback: `prop21RHS = 2·∫∫ Σ_N alignedCoeff·hatK` UNCONDITIONALLY
(`prop21RHS_hat_rep_aligned`, the H-5 v4 foundation, below).  This note STANDS as the
historical record of the pre-amendment wall — it is NOT rewritten (additive supersession). -/

/-- `shiftCoeff` distributes over Dirichlet convolution: the shift weight `n^w` splits along
the antidiagonal `p.1·p.2 = n` by base multiplicativity of `cpow`. -/
lemma shiftCoeff_convolution (w : ℂ) (a b : ℕ → ℂ) :
    shiftCoeff w (a ⍟ b) = shiftCoeff w a ⍟ shiftCoeff w b := by
  funext n
  simp only [shiftCoeff, LSeries.convolution_def]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have hbase : ((p.1 : ℂ)) ^ w * ((p.2 : ℂ)) ^ w = (n : ℂ) ^ w := by
    rw [← Complex.natCast_mul_natCast_cpow, ← Nat.cast_mul, hp.1]
  calc a p.1 * b p.2 * (n : ℂ) ^ w
      = a p.1 * b p.2 * (((p.1 : ℂ)) ^ w * ((p.2 : ℂ)) ^ w) := by rw [hbase]
    _ = a p.1 * (p.1 : ℂ) ^ w * (b p.2 * (p.2 : ℂ) ^ w) := by ring

/-- `shiftCoeff` is additive in the shift (for a sequence vanishing at `0`, which every
carrier here satisfies — the `n=0` term is `0` on both sides). -/
lemma shiftCoeff_shiftCoeff (w v : ℂ) {a : ℕ → ℂ} (ha0 : a 0 = 0) :
    shiftCoeff w (shiftCoeff v a) = shiftCoeff (w + v) a := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [shiftCoeff, ha0]
  · simp only [shiftCoeff]
    rw [mul_assoc, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), add_comm v w]

/-- `ellLin` vanishes at `0` (the linearized twist has no constant term). -/
lemma ellLin_zero (g : ℕ → ℂ) : ellLin g 0 = 0 := by simp [ellLin]

/-- **The ALIGNED four-fold coefficient** (GHS-(2.3) form).  The smooth carrier `𝒮 = ℓ_below`
is UNSHIFTED (fixed at `s`); the two window legs and the large leg carry the `−α`, `−α−2β`
shifts (the `2β` is GHS's `β→2β` doubling in our post-Jacobian convention).  This is the
coefficient `seam_double_ftc` would consume — with `winCoeff` first replaced by the full
`lambdaLin (restrictAbove)` (the H-5a defect) and on a line where that replacement is valid. -/
def alignedCoeff (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) : ℕ → ℂ :=
  ((ellLin (restrictBelow y g)
      ⍟ shiftCoeff (-(α : ℂ)) (winCoeff g X y))
      ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y))
      ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (ellLin (restrictAbove y g))

/-- **H-1b — `seam_realignment` (THE HAT-REP SANDWICH).**  The symmetric-form convolved
coefficient `fourFactorCoeff` equals the ALIGNED coefficient globally reweighted by
`shiftCoeff (α+β)`.  Pure `shiftCoeff` algebra: push the global shift through the three
convolutions (`shiftCoeff_convolution`) and fuse it into each leg (`shiftCoeff_shiftCoeff`);
the four resulting shifts `(α+β, β, −β, −β)` match `fourFactorCoeff`'s by `ring`.  The
`α+β` reweighting is the residual the design must (and, at H-5, cannot algebraically)
remove — see the module note. -/
theorem seam_realignment (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) :
    fourFactorCoeff y g X α β
      = shiftCoeff ((α : ℂ) + (β : ℂ)) (alignedCoeff y g X α β) := by
  rw [fourFactorCoeff, alignedCoeff]
  rw [shiftCoeff_convolution, shiftCoeff_convolution, shiftCoeff_convolution]
  rw [shiftCoeff_shiftCoeff _ _ (winCoeff_zero g X y),
      shiftCoeff_shiftCoeff _ _ (winCoeff_zero g X y),
      shiftCoeff_shiftCoeff _ _ (ellLin_zero (restrictAbove y g))]
  congr 1
  · congr 1
    · congr 1
      · congr 1; ring
    · congr 1; ring
  · congr 1; ring

/-- **H-1b corollary — the residual made explicit.**  The symmetric hat-smoothed coefficient
sum equals the ALIGNED sum reweighted by `N^{α+β}`.  This is the exact object H-5 would feed
to `seam_double_ftc`; the visible `N^{α+β}` is the shifted-line factor that walls the
fixed-base FTC (module note). -/
theorem seam_realignment_hat (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) {h : ℝ} :
    (∑' N, fourFactorCoeff y g X α β N * (hatK X h N : ℂ))
      = ∑' N, alignedCoeff y g X α β N * (N : ℂ) ^ ((α : ℂ) + (β : ℂ)) * (hatK X h N : ℂ) := by
  rw [seam_realignment]
  refine tsum_congr (fun N => ?_)
  simp only [shiftCoeff, mul_assoc]

/-! ## H-5a — `window_truncation_defect` (the coefficient-level defect, routed to MS-B)

The window polynomial `windowSum = P` truncates the full log-derivative
`𝓛(λ_ℓ) = LSeries (lambdaLin (restrictAbove y g))` to the open window `(⌊y⌋, ⌈X/y⌉)`.  At the
COEFFICIENT level the defect is the full coefficient supported OFF the window; its norm is
dominated by the full coefficient's, so its mass is `≤` the full `lambdaLin (restrictAbove)`
mass — exactly the shape `mult_shiu_MS_B` bounds (`MS-B`'s triple sum carries
`‖lambdaLin (restrictAbove y g) q.2.1‖` with the shifted exponents; `MultShiu:2214`).  This is
the freeze's woven-truncation ruling landed at the coefficient level.  (Its analytic consumer
is H-5, walled above; the defect object is banked for the campaign-gate continuation.) -/

/-- **H-5a (a) — the defect decomposition.**  `𝓛(λ_ℓ) − P` at the coefficient level is the
full `lambdaLin (restrictAbove y g)` coefficient restricted to the complement of the window. -/
theorem window_truncation_defect (g : ℕ → ℂ) (X y : ℝ) (n : ℕ) :
    lambdaLin (restrictAbove y g) n - winCoeff g X y n
      = if n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ then 0 else lambdaLin (restrictAbove y g) n := by
  rw [winCoeff]; split_ifs with h <;> ring

/-- **H-5a (b) — the defect is dominated by the full coefficient.**  Each defect coefficient
has norm `≤ ‖lambdaLin (restrictAbove y g) n‖`, so the truncation mass is bounded by the full
`𝓛(λ_ℓ)` mass — the `MS-B` budget shape (freeze corner ledger: the defect carries exactly the
`2η+α` shifted exponents `MS-B` already bounds). -/
lemma norm_window_truncation_defect_le (g : ℕ → ℂ) (X y : ℝ) (n : ℕ) :
    ‖lambdaLin (restrictAbove y g) n - winCoeff g X y n‖ ≤ ‖lambdaLin (restrictAbove y g) n‖ := by
  rw [window_truncation_defect]; split_ifs with h
  · simp
  · exact le_refl _

/-! ## P21-3K — the aligned foundation (`prop21RHS_hat_rep_aligned`, H-5 v4)

The amendment's CONSEQUENCE, landed: the `N^{−(α+β)}` line-compensation the amended
`prop21RHS` deposits (`prop21RHS_hat_rep`) cancels `seam_realignment`'s `N^{α+β}` reweighting
EXACTLY, collapsing the object to the CLEAN aligned coefficient sum.  This is GHS's genuine
Prop-2.1 object and the foundation the H-5 v4 design block consumes. -/

/-- The aligned four-fold coefficient vanishes at `0` (convolution over the empty
antidiagonal). -/
@[simp] lemma alignedCoeff_zero (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) :
    alignedCoeff y g X α β 0 = 0 := by
  rw [alignedCoeff, LSeries.convolution_def]; simp

/-- **P21-3K — `prop21RHS_hat_rep_aligned` (THE H-5 v4 FOUNDATION).**  The amended
`prop21RHS` equals `2·∫∫` of the hat-smoothed ALIGNED coefficient sum — GHS's genuine
Prop-2.1 object, with `𝒮` fixed and the shifts on the log-derivative/large legs.  Route:
`prop21RHS_hat_rep` (the compensated `N^{−(α+β)}` form) composed with `seam_realignment`
(`fourFactorCoeff = shiftCoeff (α+β) alignedCoeff`), whose `N^{α+β}` reweighting the
amendment's `N^{−(α+β)}` compensation cancels EXACTLY (the audit's verified centerpiece;
NUM-REF's tripwire satisfied).  The pre-amendment wall (`seam_realignment_hat`'s `N^{α+β}`
residual, the H-1b module note) is thereby DISSOLVED: the main term is the clean aligned sum,
unconditionally, no line-moving fallback.  H-5 v4 fires `seam_double_ftc` on THIS object.  The
regime gate `0 < c₀−2η` (the `y ≥ 10` floor) is carried, not proved. -/
theorem prop21RHS_hat_rep_aligned (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ X h c₀ y η : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc₀ : 1 < c₀) (hη : 0 ≤ η)
    (hc' : 0 < c₀ - 2 * η) :
    prop21RHS g t₀ X h c₀ y η
      = (2 : ℝ) • ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          ∑' N, alignedCoeff y g X α β N * (hatK X h N : ℂ) := by
  rw [prop21RHS_hat_rep g hg hX hh hc₀ hη hc']
  congr 1
  refine intervalIntegral.integral_congr (fun α _ => ?_)
  refine intervalIntegral.integral_congr (fun β _ => ?_)
  refine tsum_congr (fun N => ?_)
  have hrel : fourFactorCoeff y g X α β N
      = alignedCoeff y g X α β N * (N : ℂ) ^ ((α : ℂ) + (β : ℂ)) := by
    have := congrFun (seam_realignment y g X α β) N
    simpa [shiftCoeff] using this
  rw [hrel]
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · have hcancel : (N : ℂ) ^ ((α : ℂ) + (β : ℂ)) * (N : ℂ) ^ (-(α : ℂ) - (β : ℂ)) = 1 := by
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hN),
        show ((α : ℂ) + (β : ℂ)) + (-(α : ℂ) - (β : ℂ)) = 0 by ring, Complex.cpow_zero]
    rw [mul_assoc (alignedCoeff y g X α β N), hcancel, mul_one]

/-! ## THE S1′ REPRESENTATION — the v5 collapse chain (V5-3 → V5-2 → V5-4 → V5-6)

The core chain of the H-5 v5 wave (`docs/exploration/h5-v5-design.md`, the AMENDMENT
V5-0 seam un-windowing).  On the landed foundation `prop21RHS_hat_rep_aligned`
(`prop21RHS = 2·∫∫ Σ_N alignedCoeff·hatK`, GHS's genuine Prop-2.1 object) the chain
telescopes the `(α,β)` double integral to the GHS-(2.4) endpoint form, with every
defect priced against the `MultShiu` budget shapes (MS-A/MS-B/MS-EXIT).

The collapse is realized at the COEFFICIENT level (not the analytic FTC on L-series):
after multiplication by the hat kernel `hatK` — which vanishes past `X+h` — every sum
over `N` is a FINITE Finset sum, so the `∫α ∫β ↔ Σ_N` interchanges are plain
`integral_finset_sum`, no measure-theoretic Fubini.  The FTC content is the per-`N`
identity `lambdaLin (restrictAbove) ⍟ ellLin (restrictAbove) = log · ellLin
(restrictAbove)` (`lambdaLin_convolution`) composed with the scalar exponential
integrals `∫₀^η N^{-2β} dβ` (the `β→2β` Jacobian ½, `beta_double_jacobian`) and
`∫₀^η N^{-α} dα` — the "constant chain": the leading `2` meets the `½`, and the
`log N` from the convolution cancels the `1/log N` from the scalar integral. -/

/-- Dirichlet convolution is commutative (via the `ArithmeticFunction` ring). -/
lemma conv_comm (a b : ℕ → ℂ) : a ⍟ b = b ⍟ a := by
  simp only [LSeries.convolution]
  rw [mul_comm]

/-- Dirichlet convolution is associative (via the `ArithmeticFunction` ring). -/
lemma conv_assoc (a b c : ℕ → ℂ) : (a ⍟ b) ⍟ c = a ⍟ (b ⍟ c) := by
  simp only [LSeries.convolution]
  rw [ArithmeticFunction.toArithmeticFunction_eq_self,
      ArithmeticFunction.toArithmeticFunction_eq_self, mul_assoc]

/-- **V5-3 support fact.**  If the large log-derivative coefficient `lambdaLin
(restrictAbove y g) n` is nonzero, then `n > y`: it is a prime power whose least prime
factor exceeds `y` (`restrictAbove`), so `n ≥ minFac n > y`. -/
lemma lambdaLin_restrictAbove_gt {y : ℝ} {g : ℕ → ℂ} {n : ℕ}
    (hn : lambdaLin (restrictAbove y g) n ≠ 0) : y < (n : ℝ) := by
  by_contra hle
  have hle : (n : ℝ) ≤ y := not_lt.mp hle
  apply hn
  unfold lambdaLin
  by_cases hpp : IsPrimePow n
  · rw [if_pos hpp]
    have hn0 : n ≠ 1 := by rintro rfl; exact not_isPrimePow_one hpp
    have hp : (n.minFac).Prime := Nat.minFac_prime hn0
    have hnpos : 0 < n := hpp.pos
    have hmfle : (n.minFac : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.minFac_le hnpos
    have hmfy : ¬ (y < (n.minFac : ℝ)) := by linarith
    have hra0 : restrictAbove y g n.minFac = 0 := by
      unfold restrictAbove; rw [if_neg hmfy]
    have hk1 : 1 ≤ n.factorization n.minFac :=
      Nat.Prime.factorization_pos_of_dvd hp hnpos.ne' (Nat.minFac_dvd n)
    rw [hra0, zero_pow (by omega : n.factorization n.minFac ≠ 0), mul_zero, zero_mul]
  · rw [if_neg hpp]

/-- Convolution congruence when the right factors agree on every divisor of `u`. -/
lemma conv_eq_on_dvd {A B B' : ℕ → ℂ} {u : ℕ}
    (hBB' : ∀ d : ℕ, d ∣ u → B d = B' d) :
    (A ⍟ B) u = (A ⍟ B') u := by
  simp only [LSeries.convolution_def]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have hdvd : p.2 ∣ u := ⟨p.1, by rw [← hp.1]; ring⟩
  rw [hBB' p.2 hdvd]

/-- `winCoeff` equals the full log-derivative coefficient at an in-window index. -/
lemma winCoeff_eq_of_window {y : ℝ} {g : ℕ → ℂ} {X : ℝ} {k : ℕ}
    (hlo : ⌊y⌋₊ < k) (hhi : (k : ℝ) < X / y) :
    winCoeff g X y k = lambdaLin (restrictAbove y g) k := by
  unfold winCoeff
  rw [if_pos (Finset.mem_Ioo.mpr ⟨hlo, Nat.lt_ceil.mpr hhi⟩)]

/-- **V5-3 pair lemma — the joint-support untruncation of the two window legs.**  On
`j ≤ X`, the convolution of the two window Dirichlet-polynomial coefficient legs
`winCoeff` equals that of the full log-derivative `lambdaLin (restrictAbove)`.  GHS §2.2:
on a nonzero term `k·l = j`, both partners are prime powers `> y` (`lambdaLin
(restrictAbove)` support), so each forces the other `< X/y` STRICTLY (`k·y < k·l = j ≤
X`), landing both in the window `(⌊y⌋, ⌈X/y⌉)` (`Nat.lt_ceil`; the lower bound is free,
`> y > ⌊y⌋`).  Terms with a vanishing leg agree trivially (`winCoeff` support ⊆
`lambdaLin`). -/
lemma window_pair_untrunc (y : ℝ) (g : ℕ → ℂ) (hy : 0 < y) (X α β : ℝ) :
    ∀ j : ℕ, (j : ℝ) ≤ X →
      (shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g))
          ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g))) j
      = (shiftCoeff (-(α : ℂ)) (winCoeff g X y)
          ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y)) j := by
  intro j hj
  simp only [LSeries.convolution_def]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨hprod, hj0⟩ := hp
  set k := p.1 with hk
  set l := p.2 with hl
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at hprod; omega)
  have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at hprod; omega)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl1
  have hklR : (k : ℝ) * (l : ℝ) = (j : ℝ) := by exact_mod_cast hprod
  simp only [shiftCoeff]
  by_cases hΛk : lambdaLin (restrictAbove y g) k = 0
  · have hwk : winCoeff g X y k = 0 := by
      unfold winCoeff; split_ifs with h
      · exact hΛk
      · rfl
    rw [hΛk, hwk]; ring
  · by_cases hΛl : lambdaLin (restrictAbove y g) l = 0
    · have hwl : winCoeff g X y l = 0 := by
        unfold winCoeff; split_ifs with h
        · exact hΛl
        · rfl
      rw [hΛl, hwl]; ring
    · have hky : y < (k : ℝ) := lambdaLin_restrictAbove_gt hΛk
      have hly : y < (l : ℝ) := lambdaLin_restrictAbove_gt hΛl
      have hfloor : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy.le
      have hklo : ⌊y⌋₊ < k := by exact_mod_cast (lt_of_le_of_lt hfloor hky)
      have hllo : ⌊y⌋₊ < l := by exact_mod_cast (lt_of_le_of_lt hfloor hly)
      have hkhi : (k : ℝ) < X / y := by
        rw [lt_div_iff₀ hy]
        calc (k : ℝ) * y < (k : ℝ) * (l : ℝ) :=
              mul_lt_mul_of_pos_left hly (by linarith)
          _ = (j : ℝ) := hklR
          _ ≤ X := hj
      have hlhi : (l : ℝ) < X / y := by
        rw [lt_div_iff₀ hy]
        calc (l : ℝ) * y < (l : ℝ) * (k : ℝ) :=
              mul_lt_mul_of_pos_left hky (by linarith)
          _ = (k : ℝ) * (l : ℝ) := by ring
          _ = (j : ℝ) := hklR
          _ ≤ X := hj
      rw [winCoeff_eq_of_window hklo hkhi, winCoeff_eq_of_window hllo hlhi]

/-- **The UN-truncated aligned coefficient** (V5-3).  `alignedCoeff` with both window
Dirichlet-polynomial legs (`winCoeff`) promoted to the FULL log-derivative
`lambdaLin (restrictAbove y g)` — the object the FTC collapse consumes.  Independent of
the window cutoff `X`. -/
def alignedCoeffFull (y : ℝ) (g : ℕ → ℂ) (α β : ℝ) : ℕ → ℂ :=
  ((ellLin (restrictBelow y g)
      ⍟ shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)))
      ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g)))
      ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (ellLin (restrictAbove y g))

@[simp] lemma alignedCoeffFull_zero (y : ℝ) (g : ℕ → ℂ) (α β : ℝ) :
    alignedCoeffFull y g α β 0 = 0 := by
  rw [alignedCoeffFull, LSeries.convolution_map_zero]

/-- **V5-3 — `joint_support_untruncation`.**  On `N ≤ X` the aligned coefficient equals
its un-truncated version `alignedCoeffFull` (both window legs promoted to the full
log-derivative).  Route: reassociate so the two window legs are adjacent
(`conv_assoc`/`conv_comm`), then `conv_eq_on_dvd` lifts the pair lemma
`window_pair_untrunc` (agreement on `j ≤ X`) through the outer smooth/large legs (every
divisor of `N ≤ X` is `≤ X`).  The ramp complement `X < N ≤ X+h` is the residual
(`rampTerm`, priced in V5-6). -/
theorem joint_support_untruncation (y : ℝ) (g : ℕ → ℂ) (hy : 0 < y) (X α β : ℝ)
    {N : ℕ} (hN : (N : ℝ) ≤ X) :
    alignedCoeff y g X α β N = alignedCoeffFull y g α β N := by
  rw [alignedCoeff, alignedCoeffFull]
  set S := ellLin (restrictBelow y g) with hS
  set E := shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (ellLin (restrictAbove y g)) with hE
  set Pf := shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)) with hPf
  set Qf := shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g)) with hQf
  set Pw := shiftCoeff (-(α : ℂ)) (winCoeff g X y) with hPw
  set Qw := shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y) with hQw
  have hpair : ∀ j : ℕ, (j : ℝ) ≤ X → (Pf ⍟ Qf) j = (Pw ⍟ Qw) j :=
    window_pair_untrunc y g hy X α β
  have hinner : ∀ u : ℕ, (u : ℝ) ≤ X → (S ⍟ (Pf ⍟ Qf)) u = (S ⍟ (Pw ⍟ Qw)) u := by
    intro u hu
    rcases Nat.eq_zero_or_pos u with rfl | hupos
    · simp only [LSeries.convolution_map_zero]
    · refine conv_eq_on_dvd (fun d hd => hpair d ?_)
      have : (d : ℝ) ≤ (u : ℝ) := by exact_mod_cast Nat.le_of_dvd hupos hd
      linarith
  have houter : (E ⍟ (S ⍟ (Pf ⍟ Qf))) N = (E ⍟ (S ⍟ (Pw ⍟ Qw))) N := by
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp only [LSeries.convolution_map_zero]
    · refine conv_eq_on_dvd (A := E) (fun d hd => ?_)
      have hdN : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_dvd hNpos hd
      exact hinner d (le_trans hdN hN)
  rw [conv_assoc S Pw Qw, conv_assoc S Pf Qf,
    conv_comm (S ⍟ (Pw ⍟ Qw)) E, conv_comm (S ⍟ (Pf ⍟ Qf)) E]
  exact houter.symm

/-! ## V5-2 — `coeff_collapse` (the per-`N` FTC collapse)

The scalar `cpow` FTCs (`scalar_cpow_ftc`, `cpow_beta_ftc` at `κ=-2`, `cpow_alpha_ftc`
at `κ=-1`) and the per-`N` collapse of `alignedCoeffFull`.  The β-leg telescopes with the
β→2β Jacobian `½` (`cpow_beta_ftc`), the two β-legs having convolved into `log·E` via
`lambdaLin_convolution`; the leading `2` meets the `½`; the α-leg's main half telescopes
(`cpow_alpha_ftc`) to `𝒮·𝓛 − η`-endpoint while the `2η`-endpoint survives as an α-integral
(the α-shifts `−α` vs `−α−2η` prevent its telescoping).  Every `Σ_N`/`∫` interchange is a
finite `Finset` operation (the summands are finite convolutions), no Fubini. -/

/-- The scalar FTC for `(j)^(w0 + κ·t)`.  `∫ₐᵇ c·log(j)·(j)^(w0+κt) dt =
(c/κ)·((j)^(w0+κb) − (j)^(w0+κa))`. -/
lemma scalar_cpow_ftc {j : ℕ} (hj : 1 ≤ j) (c w0 : ℂ) {κ : ℝ} (hκ : κ ≠ 0) (a b : ℝ) :
    (∫ t in a..b, c * Complex.log (j : ℂ) * (j : ℂ) ^ (w0 + (κ : ℂ) * (t : ℂ)))
      = (c / (κ : ℂ)) * ((j : ℂ) ^ (w0 + (κ : ℂ) * (b : ℂ))
          - (j : ℂ) ^ (w0 + (κ : ℂ) * (a : ℂ))) := by
  have hj0 : (j : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  -- the ℂ→ℂ antiderivative and its derivative (all differentiation over ℂ)
  have hGe : ∀ z : ℂ, HasDerivAt (fun z : ℂ => (c / (κ : ℂ)) * (j : ℂ) ^ (w0 + (κ : ℂ) * z))
      (c * Complex.log (j : ℂ) * (j : ℂ) ^ (w0 + (κ : ℂ) * z)) z := by
    intro z
    have hq : HasDerivAt (fun z : ℂ => w0 + (κ : ℂ) * z) ((κ : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (κ : ℂ)).const_add w0
    have hcomp : HasDerivAt (fun z : ℂ => (j : ℂ) ^ (w0 + (κ : ℂ) * z))
        ((j : ℂ) ^ (w0 + (κ : ℂ) * z) * Complex.log (j : ℂ) * (κ : ℂ)) z :=
      hq.const_cpow (Or.inl hj0)
    have h3 := hcomp.const_mul (c / (κ : ℂ))
    have hcancel : c / (κ : ℂ) * ((j : ℂ) ^ (w0 + (κ : ℂ) * z) * Complex.log (j : ℂ) * (κ : ℂ))
        = c * Complex.log (j : ℂ) * (j : ℂ) ^ (w0 + (κ : ℂ) * z) := by
      field_simp
    rw [hcancel] at h3
    exact h3
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (c / (κ : ℂ)) * (j : ℂ) ^ (w0 + (κ : ℂ) * (t : ℂ)))
      (c * Complex.log (j : ℂ) * (j : ℂ) ^ (w0 + (κ : ℂ) * (t : ℂ))) t :=
    fun t => (hGe (t : ℂ)).comp_ofReal
  have hcont : Continuous
      (fun t : ℝ => c * Complex.log (j : ℂ) * (j : ℂ) ^ (w0 + (κ : ℂ) * (t : ℂ))) := by
    apply Continuous.mul continuous_const
    apply Continuous.const_cpow (by fun_prop) (Or.inl hj0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable a b)]
  ring

/-- The β-leg scalar FTC (`κ = -2`, endpoints at `2β ∈ {0, 2η}`). -/
lemma cpow_beta_ftc {j : ℕ} (hj : 1 ≤ j) (e : ℂ) (α η : ℝ) :
    (∫ β in (0 : ℝ)..η, e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ) - 2 * (β : ℂ)))
      = (1 / 2 : ℂ) * (e * (j : ℂ) ^ (-(α : ℂ))
          - e * (j : ℂ) ^ (-(α : ℂ) - 2 * (η : ℂ))) := by
  have key := scalar_cpow_ftc hj e (-(α : ℂ)) (κ := -2) (by norm_num) 0 η
  have hint : (∫ β in (0 : ℝ)..η, e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ) - 2 * (β : ℂ)))
      = ∫ β in (0 : ℝ)..η,
          e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ) + ((-2 : ℝ) : ℂ) * (β : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro β _
    change e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ) - 2 * (β : ℂ))
        = e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ) + ((-2 : ℝ) : ℂ) * (β : ℂ))
    rw [show (-(α : ℂ) - 2 * (β : ℂ)) = (-(α : ℂ) + ((-2 : ℝ) : ℂ) * (β : ℂ)) by push_cast; ring]
  rw [hint, key,
    show (-(α : ℂ) + ((-2 : ℝ) : ℂ) * ((η : ℝ) : ℂ)) = (-(α : ℂ) - 2 * (η : ℂ)) by push_cast; ring,
    show (-(α : ℂ) + ((-2 : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) = (-(α : ℂ)) by push_cast; ring]
  push_cast; ring

/-- The α-leg scalar FTC (`κ = -1`). -/
lemma cpow_alpha_ftc {j : ℕ} (hj : 1 ≤ j) (e : ℂ) (η : ℝ) :
    (∫ α in (0 : ℝ)..η, e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ)))
      = e * (j : ℂ) ^ (0 : ℂ) - e * (j : ℂ) ^ (-(η : ℂ)) := by
  have key := scalar_cpow_ftc hj e (0 : ℂ) (κ := -1) (by norm_num) 0 η
  have hint : (∫ α in (0 : ℝ)..η, e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ)))
      = ∫ α in (0 : ℝ)..η,
          e * Complex.log (j : ℂ) * (j : ℂ) ^ ((0 : ℂ) + ((-1 : ℝ) : ℂ) * (α : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro α _
    change e * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ))
        = e * Complex.log (j : ℂ) * (j : ℂ) ^ ((0 : ℂ) + ((-1 : ℝ) : ℂ) * (α : ℂ))
    rw [show (-(α : ℂ)) = ((0 : ℂ) + ((-1 : ℝ) : ℂ) * (α : ℂ)) by push_cast; ring]
  rw [hint, key,
    show ((0 : ℂ) + ((-1 : ℝ) : ℂ) * ((η : ℝ) : ℂ)) = (-(η : ℂ)) by push_cast; ring,
    show ((0 : ℂ) + ((-1 : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) = (0 : ℂ) by push_cast; ring]
  push_cast; ring

/-- Factor `alignedCoeffFull` so the two β-dependent legs are convolved into one
shifted `Λ⍟E` leg. -/
lemma alignedCoeffFull_factor (y : ℝ) (g : ℕ → ℂ) (α β : ℝ) :
    alignedCoeffFull y g α β
      = (ellLin (restrictBelow y g) ⍟ shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)))
          ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ))
              (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) := by
  rw [alignedCoeffFull, conv_assoc, shiftCoeff_convolution]

/-- Push a `β`-integral through a convolution whose left leg is `β`-independent. -/
lemma conv_integral_push (P : ℕ → ℂ) (c : ℝ → ℕ → ℂ) (N : ℕ) {a b : ℝ}
    (hc : ∀ j, IntervalIntegrable (fun β => c β j) volume a b) :
    (∫ β in a..b, (P ⍟ fun n => c β n) N)
      = (P ⍟ fun n => ∫ β in a..b, c β n) N := by
  simp only [LSeries.convolution_def]
  rw [intervalIntegral.integral_finsetSum (fun p _ => (hc p.2).const_mul (P p.1))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [intervalIntegral.integral_const_mul]

/-- The β-leg is interval-integrable. -/
lemma betaLeg_intervalIntegrable (y : ℝ) (g : ℕ → ℂ) (α η : ℝ) (j : ℕ) :
    IntervalIntegrable (fun β : ℝ => shiftCoeff (-(α : ℂ) - 2 * (β : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j) volume 0 η := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : (fun β : ℝ => shiftCoeff (-(α : ℂ) - 2 * (β : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) 0) = fun _ => 0 := by
      funext β; simp [shiftCoeff, LSeries.convolution_map_zero]
    rw [h0]; exact intervalIntegrable_const
  · apply Continuous.intervalIntegrable
    unfold shiftCoeff
    exact Continuous.mul continuous_const
      (Continuous.const_cpow (by fun_prop) (Or.inl (Nat.cast_ne_zero.mpr hj.ne')))

/-- The per-`j` β-integral: `∫₀^η (Λ⍟E)(j)·j^{-α-2β} dβ = ½(E(j)·j^{-α} − E(j)·j^{-α-2η})`. -/
lemma betaLeg_integral (y : ℝ) (g : ℕ → ℂ) (α η : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    (∫ β in (0 : ℝ)..η, shiftCoeff (-(α : ℂ) - 2 * (β : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j)
      = (1 / 2 : ℂ) * (shiftCoeff (-(α : ℂ)) (ellLin (restrictAbove y g)) j
          - shiftCoeff (-(α : ℂ) - 2 * (η : ℂ)) (ellLin (restrictAbove y g)) j) := by
  have hconv : (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j
      = (Real.log j : ℂ) * ellLin (restrictAbove y g) j :=
    (lambdaLin_convolution (restrictAbove y g) j).symm
  have hint : (∫ β in (0 : ℝ)..η, shiftCoeff (-(α : ℂ) - 2 * (β : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j)
      = ∫ β in (0 : ℝ)..η,
          ellLin (restrictAbove y g) j * Complex.log (j : ℂ)
            * (j : ℂ) ^ (-(α : ℂ) - 2 * (β : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro β _
    change shiftCoeff (-(α : ℂ) - 2 * (β : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j = _
    rw [shiftCoeff, hconv, Complex.natCast_log]; ring
  rw [hint, cpow_beta_ftc hj (ellLin (restrictAbove y g) j) α η, shiftCoeff, shiftCoeff]

/-- **V5-2 (β-leg) — the per-`N` β-collapse.**  The inner β-integral of
`alignedCoeffFull` telescopes to a ½-scaled endpoint difference (the β→2β Jacobian ½
of `cpow_beta_ftc`). -/
lemma beta_collapse (y : ℝ) (g : ℕ → ℂ) (α η : ℝ) (N : ℕ) :
    (∫ β in (0 : ℝ)..η, alignedCoeffFull y g α β N)
      = (1 / 2 : ℂ) *
        (((ellLin (restrictBelow y g) ⍟ shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)))
              ⍟ shiftCoeff (-(α : ℂ)) (ellLin (restrictAbove y g))) N
          - ((ellLin (restrictBelow y g) ⍟ shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)))
              ⍟ shiftCoeff (-(α : ℂ) - 2 * (η : ℂ)) (ellLin (restrictAbove y g))) N) := by
  set A := ellLin (restrictBelow y g)
      ⍟ shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)) with hA
  set E := ellLin (restrictAbove y g) with hE
  set Lam := lambdaLin (restrictAbove y g) with hLam
  -- rewrite the integrand via the factorization
  have hfac : (fun β : ℝ => alignedCoeffFull y g α β N)
      = fun β : ℝ => (A ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (Lam ⍟ E)) N := by
    funext β; rw [alignedCoeffFull_factor]
  rw [show (∫ β in (0 : ℝ)..η, alignedCoeffFull y g α β N)
      = ∫ β in (0 : ℝ)..η, (A ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (Lam ⍟ E)) N from by
    rw [hfac]]
  -- push the integral through the convolution
  rw [conv_integral_push A (fun β => shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (Lam ⍟ E)) N
      (fun j => betaLeg_intervalIntegrable y g α η j)]
  -- the per-j integral, as a sequence identity
  have hseq : (fun n => ∫ β in (0 : ℝ)..η, shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (Lam ⍟ E) n)
      = fun n => (1 / 2 : ℂ)
          * (shiftCoeff (-(α : ℂ)) E n - shiftCoeff (-(α : ℂ) - 2 * (η : ℂ)) E n) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hE0 : E 0 = 0 := by rw [hE]; exact ellLin_zero (restrictAbove y g)
      simp [shiftCoeff, LSeries.convolution_map_zero, hE0]
    · exact betaLeg_integral y g α η hn
  rw [hseq]
  -- bilinearity: A ⍟ (½·(u − v)) = ½·(A⍟u − A⍟v)
  simp only [LSeries.convolution_def]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

/-! ### The α-collapse -/

/-- Continuity of a convolution of two `α`-continuous coefficient families. -/
lemma continuous_conv2 (a b : ℝ → ℕ → ℂ) (N : ℕ)
    (ha : ∀ k, Continuous (fun α => a α k)) (hb : ∀ m, Continuous (fun α => b α m)) :
    Continuous (fun α => (a α ⍟ b α) N) := by
  simp only [LSeries.convolution_def]
  exact continuous_finsetSum _ (fun p _ => (ha p.1).mul (hb p.2))

/-- Continuity in `α` of a shifted coefficient applied at a fixed index (for a `0`-vanishing
sequence and a continuous exponent). -/
lemma continuous_shiftCoeff_apply {e : ℕ → ℂ} (he0 : e 0 = 0) (w : ℝ → ℂ) (hw : Continuous w)
    (j : ℕ) : Continuous (fun α : ℝ => shiftCoeff (w α) e j) := by
  unfold shiftCoeff
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [he0, zero_mul]; exact continuous_const
  · exact Continuous.mul continuous_const
      (Continuous.const_cpow hw (Or.inl (Nat.cast_ne_zero.mpr (by omega))))

/-- The α-leg is interval-integrable. -/
lemma alphaLeg_intervalIntegrable (y : ℝ) (g : ℕ → ℂ) (η : ℝ) (j : ℕ) :
    IntervalIntegrable (fun α : ℝ => shiftCoeff (-(α : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j) volume 0 η :=
  (continuous_shiftCoeff_apply (by rw [LSeries.convolution_map_zero]) (fun α => -(α : ℂ))
    (by fun_prop) j).intervalIntegrable 0 η

/-- The per-`j` α-integral: `∫₀^η (Λ⍟E)(j)·j^{-α} dα = E(j) − E(j)·j^{-η}`. -/
lemma alphaLeg_integral (y : ℝ) (g : ℕ → ℂ) (η : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    (∫ α in (0 : ℝ)..η, shiftCoeff (-(α : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j)
      = ellLin (restrictAbove y g) j - shiftCoeff (-(η : ℂ)) (ellLin (restrictAbove y g)) j := by
  have hconv : (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j
      = (Real.log j : ℂ) * ellLin (restrictAbove y g) j :=
    (lambdaLin_convolution (restrictAbove y g) j).symm
  have hint : (∫ α in (0 : ℝ)..η, shiftCoeff (-(α : ℂ))
        (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j)
      = ∫ α in (0 : ℝ)..η,
          ellLin (restrictAbove y g) j * Complex.log (j : ℂ) * (j : ℂ) ^ (-(α : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro α _
    change shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g) ⍟ ellLin (restrictAbove y g)) j = _
    rw [shiftCoeff, hconv, Complex.natCast_log]; ring
  rw [hint, cpow_alpha_ftc hj (ellLin (restrictAbove y g) j) η, Complex.cpow_zero, mul_one,
    shiftCoeff]

/-- **V5-2 (the per-`N` full collapse) — `coeff_collapse`.**  The `(α,β)` double integral
of `alignedCoeffFull` telescopes (with the leading `2` meeting the β-Jacobian `½` and the
`Λ⍟E = log·E` cancellation) to the main term minus the `η`-endpoint minus the `2η`-endpoint
(the surviving `α`-integral, which the α-shifts prevent from telescoping). -/
lemma coeff_collapse (y : ℝ) (g : ℕ → ℂ) (η : ℝ) (N : ℕ) :
    (2 : ℝ) • (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, alignedCoeffFull y g α β N)
      = (ellLin (restrictBelow y g) ⍟ ellLin (restrictAbove y g)) N
        - (ellLin (restrictBelow y g) ⍟ shiftCoeff (-(η : ℂ)) (ellLin (restrictAbove y g))) N
        - ∫ α in (0 : ℝ)..η,
            ((ellLin (restrictBelow y g) ⍟ shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)))
              ⍟ shiftCoeff (-(α : ℂ) - 2 * (η : ℂ)) (ellLin (restrictAbove y g))) N := by
  set S := ellLin (restrictBelow y g) with hS
  set E := ellLin (restrictAbove y g) with hE
  set Lam := lambdaLin (restrictAbove y g) with hLam
  -- F1, F2 as α-families
  set F1 : ℝ → ℂ := fun α => ((S ⍟ shiftCoeff (-(α : ℂ)) Lam) ⍟ shiftCoeff (-(α : ℂ)) E) N with hF1
  set F2 : ℝ → ℂ := fun α =>
    ((S ⍟ shiftCoeff (-(α : ℂ)) Lam) ⍟ shiftCoeff (-(α : ℂ) - 2 * (η : ℂ)) E) N with hF2
  -- inner β via beta_collapse
  have hβ : (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, alignedCoeffFull y g α β N)
      = ∫ α in (0 : ℝ)..η, (1 / 2 : ℂ) * (F1 α - F2 α) := by
    apply intervalIntegral.integral_congr
    intro α _
    exact beta_collapse y g α η N
  -- F1, F2 continuity ⇒ integrability
  have hF1cont : Continuous F1 := by
    rw [hF1]
    exact continuous_conv2 _ _ N
      (fun k => continuous_conv2 _ _ k (fun _ => continuous_const)
        (fun m => continuous_shiftCoeff_apply
          (by rw [hLam]; unfold lambdaLin; rw [if_neg not_isPrimePow_zero])
          (fun α => -(α : ℂ)) (by fun_prop) m))
      (fun m => continuous_shiftCoeff_apply (by rw [hE]; exact ellLin_zero _)
        (fun α => -(α : ℂ)) (by fun_prop) m)
  have hF2cont : Continuous F2 := by
    rw [hF2]
    exact continuous_conv2 _ _ N
      (fun k => continuous_conv2 _ _ k (fun _ => continuous_const)
        (fun m => continuous_shiftCoeff_apply
          (by rw [hLam]; unfold lambdaLin; rw [if_neg not_isPrimePow_zero])
          (fun α => -(α : ℂ)) (by fun_prop) m))
      (fun m => continuous_shiftCoeff_apply (by rw [hE]; exact ellLin_zero _)
        (fun α => -(α : ℂ) - 2 * (η : ℂ)) (by fun_prop) m)
  -- collapse the scalar prefactor: 2 • ∫ ½(F1−F2) = ∫ (F1−F2)
  rw [hβ, ← intervalIntegral.integral_smul,
    show (fun α => (2 : ℝ) • ((1 / 2 : ℂ) * (F1 α - F2 α))) = fun α => F1 α - F2 α from by
      funext α; rw [Complex.real_smul]; push_cast; ring,
    intervalIntegral.integral_sub (hF1cont.intervalIntegrable 0 η) (hF2cont.intervalIntegrable 0 η)]
  -- ∫ F2 is the RHS 2η-term verbatim; ∫ F1 telescopes to main − eta
  have hF1int : (∫ α in (0 : ℝ)..η, F1 α)
      = (S ⍟ E) N - (S ⍟ shiftCoeff (-(η : ℂ)) E) N := by
    -- F1 α = (S ⍟ shiftCoeff (-α) (Lam ⍟ E)) N
    rw [show (∫ α in (0 : ℝ)..η, F1 α)
          = ∫ α in (0 : ℝ)..η, (S ⍟ shiftCoeff (-(α : ℂ)) (Lam ⍟ E)) N from by
        apply intervalIntegral.integral_congr; intro α _
        rw [hF1]
        change ((S ⍟ shiftCoeff (-(α : ℂ)) Lam) ⍟ shiftCoeff (-(α : ℂ)) E) N
            = (S ⍟ shiftCoeff (-(α : ℂ)) (Lam ⍟ E)) N
        rw [conv_assoc, ← shiftCoeff_convolution]]
    rw [conv_integral_push S (fun α => shiftCoeff (-(α : ℂ)) (Lam ⍟ E)) N
        (fun j => by rw [hLam, hE]; exact alphaLeg_intervalIntegrable y g η j)]
    have hseq : (fun n => ∫ α in (0 : ℝ)..η, shiftCoeff (-(α : ℂ)) (Lam ⍟ E) n)
        = fun n => E n - shiftCoeff (-(η : ℂ)) E n := by
      funext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hE0 : E 0 = 0 := by rw [hE]; exact ellLin_zero _
        simp [shiftCoeff, LSeries.convolution_map_zero, hE0]
      · rw [hLam, hE]; exact alphaLeg_integral y g η hn
    rw [hseq]
    simp only [LSeries.convolution_def]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [hF1int]

end Salt.MR
