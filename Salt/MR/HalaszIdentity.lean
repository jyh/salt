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

end Salt.MR
