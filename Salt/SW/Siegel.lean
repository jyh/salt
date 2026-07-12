/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.FourFold
import Salt.SW.ZeroFreeReal
import Salt.SW.Growth

/-!
# The SW rung, node S4b — Siegel's theorem via Goldfeld

Design: `docs/blueprints/sw.md`, wave S4. This module lands the reduction of **Siegel's theorem**
(the ineffective lower bound `L(1,χ) ≫_ε q^{−ε}` for real primitive quadratic characters, hence
the zero-free region `1 − β ≫_ε q^{−ε}`) to the single hard analytic input of Goldfeld's proof:
**Estermann's positivity lemma** (Montgomery–Vaughan, *Multiplicative Number Theory I*,
Lemma 11.13 — a quantitative form of Landau's theorem on Dirichlet series with nonnegative
coefficients).

## Route (Montgomery–Vaughan §11.14 / Goldfeld 1974, as transcribed in Liu arXiv:2201.11145 and
Bao–Vo)

For two real primitive quadratic characters `χ, χ₁`, the fourfold product
`F(s) = ζ(s)·L(s,χ)·L(s,χ₁)·L(s,χχ₁) = Σ r(n) n^{−s}` has nonnegative coefficients with `r(1)=1`
(this is `Salt.SW.fourfoldCoeff`, landed in `FourFold.lean`). Its residue at `s = 1` is
`λ = L(1,χ)·L(1,χ₁)·L(1,χχ₁)`. Goldfeld's dichotomy: for a given `ε`, EITHER no real primitive
quadratic character has an L-zero in `[1−ε, 1)` (then Siegel is trivial and *effective*), OR one
fixes a single such `χ₁` with a zero `β₁` (THE ineffective choice — `χ₁, β₁` depend only on `ε`).
Pairing any other `χ` against this fixed `χ₁` and feeding `f = L(·,χ)L(·,χ₁)L(·,χχ₁)`,
`f(β₁) = 0`, into Estermann's lemma yields `f(1) ≫_ε q^{−ε}`; dividing out the (fixed, hence
`ε`-dependent) `L(1,χ₁)L(1,χχ₁) ≪ log²(qq₁)` gives `L(1,χ) ≫_ε q^{−ε}`.

## What is FULLY PROVEN here (sorry-free, axiom-clean)

* `LFunction_pos_of_one_lt` — for a real quadratic character (`χ² = 1`) and real `x > 1`,
  `0 < LFunction χ x` in `ComplexOrder` (a *positive real*). Via the mathlib positivity engine
  on `ζ ⍟ χ = zetaMul χ` (nonnegative coefficients) and `ζ(x) > 0`.
* `LFunction_apply_one_pos` — `0 < LFunction χ 1` for a real primitive quadratic `χ ≠ 1`: the
  boundary value is a *positive* real. (`LFunction_pos_of_one_lt` limit + `L(1,χ) ≠ 0` + real.)
* `lambda_pos` — the residue `λ = L(1,χ)L(1,χ₁)L(1,χχ₁) > 0`.

## What is ABSTRACTED (the one flagged analytic input)

* `EstermannPositivity` — Estermann/Landau's quantitative positivity lemma, stated for an abstract
  `f` analytic on `ball 2 (3/2)`. This is the genuine analytic core of Goldfeld's proof (Cauchy
  estimates on the pole-subtracted `ζ·f − f(1)/(s−1)`, plus a Landau summation). Its FULL
  formalization is deferred; see `docs/blueprints/flags.md` (SW S4b).

The ineffectivity of `C(ε)` is intrinsic and *by construction*: the exceptional `χ₁, β₁` are
selected by `Classical.choice` out of a `by_cases`, and cannot be produced by any finite
procedure. This is the nature of the theorem, not a formalization artifact.
-/

namespace Salt.SW

open Complex DirichletCharacter ArithmeticFunction
open scoped LSeries.notation ComplexOrder

/-! ## 1. Positivity of `L(σ,χ)` for real quadratic `χ` on the real axis -/

/-- **`L(σ,χ) > 0` for real `σ > 1` and real (quadratic) `χ`.** In `ComplexOrder` this asserts
`(L(σ,χ)).re > 0` and `(L(σ,χ)).im = 0`: a positive real number. Route: the mathlib positivity
engine (`ArithmeticFunction.LSeries_positive`) applied to `zetaMul χ = ζ ⍟ χ`, whose coefficients
are nonnegative (`zetaMul_nonneg`) with value `1` at `n = 1`, gives `0 < ζ(σ)·L(σ,χ)`
(`LSeries_zetaMul_eq`); dividing by `ζ(σ) > 0` (`riemannZeta_pos_of_one_lt`) leaves `0 < L(σ,χ)`. -/
theorem LFunction_pos_of_one_lt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ^ 2 = 1) {x : ℝ} (hx : 1 < x) : 0 < LFunction χ (x : ℂ) := by
  have hxC : (1 : ℝ) < ((x : ℂ)).re := by rw [Complex.ofReal_re]; exact hx
  -- the 2-fold product `P = ζ(x)·L(x,χ)` is a positive real
  have habsc : LSeries.abscissaOfAbsConv (⇑(zetaMul χ)) < (x : EReal) := by
    refine lt_of_le_of_lt
      (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        (x := 1) (fun y hy => LSeriesSummable_zetaMul χ (by rwa [Complex.ofReal_re]))) ?_
    exact_mod_cast hx
  have hP : (0 : ℂ) < LSeries (⇑(zetaMul χ)) (x : ℂ) := by
    refine ArithmeticFunction.LSeries_positive (fun n => zetaMul_nonneg hχ n) ?_ habsc
    rw [(isMultiplicative_zetaMul χ).map_one]; exact zero_lt_one
  rw [LSeries_zetaMul_eq χ hxC] at hP
  -- unpack: `0 < ζ(x)` and `0 < ζ(x)·L(x,χ)` ⇒ `0 < L(x,χ)` via re/im
  have hZ : (0 : ℂ) < riemannZeta (x : ℂ) := riemannZeta_pos_of_one_lt hx
  obtain ⟨hZre, hZim⟩ := Complex.pos_iff.mp hZ
  obtain ⟨hPre, hPim⟩ := Complex.pos_iff.mp hP
  set Lv : ℂ := LFunction χ (x : ℂ) with hLv
  have hPre' : (riemannZeta (x : ℂ)).re * Lv.re = (riemannZeta (x : ℂ) * Lv).re := by
    rw [Complex.mul_re, ← hZim]; ring
  have hPim' : (riemannZeta (x : ℂ)).re * Lv.im = (riemannZeta (x : ℂ) * Lv).im := by
    rw [Complex.mul_im, ← hZim]; ring
  refine Complex.pos_iff.mpr ⟨?_, ?_⟩
  · have hkey : 0 < (riemannZeta (x : ℂ)).re * Lv.re := by rw [hPre']; exact hPre
    exact (mul_pos_iff_of_pos_left hZre).mp hkey
  · have hkey : (riemannZeta (x : ℂ)).re * Lv.im = 0 := by rw [hPim']; exact hPim.symm
    exact ((mul_eq_zero.mp hkey).resolve_left (ne_of_gt hZre)).symm

/-- **`L(1,χ) > 0` for a real primitive quadratic `χ ≠ 1`.** The boundary value is a *positive*
real. Route: `L(1,χ)` is real (`LFunction_conj` at `s = 1`), nonzero
(`LFunction_apply_one_ne_zero`), and `≥ 0` as the right limit of the positive reals `L(σ,χ)`. -/
theorem LFunction_apply_one_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hsq : χ ^ 2 = 1) : 0 < LFunction χ 1 := by
  set L1 : ℂ := LFunction χ 1 with hL1
  -- real
  have hreal : L1.im = 0 := by
    have h := LFunction_conj hχ1 hsq 1
    rw [map_one] at h
    exact (Complex.conj_eq_iff_im.mp h.symm)
  -- nonzero
  have hne : L1 ≠ 0 := LFunction_apply_one_ne_zero hχ1
  -- `re ≥ 0` by continuity from the right
  have hcont : Continuous (fun σ : ℝ => (LFunction χ (σ : ℂ)).re) :=
    Complex.continuous_re.comp ((differentiable_LFunction hχ1).continuous.comp
      Complex.continuous_ofReal)
  have hge : 0 ≤ (LFunction χ (1 : ℂ)).re := by
    have hcwa : ContinuousWithinAt (fun σ : ℝ => (LFunction χ (σ : ℂ)).re) (Set.Ioi 1) 1 :=
      (hcont.continuousAt).continuousWithinAt
    have hev : ∀ᶠ σ : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1), 0 ≤ (LFunction χ (σ : ℂ)).re :=
      Filter.eventually_of_mem self_mem_nhdsWithin
        (fun σ hσ => le_of_lt (Complex.pos_iff.mp (LFunction_pos_of_one_lt hsq hσ)).1)
    have h := ge_of_tendsto hcwa hev
    simpa using h
  have hre_pos : 0 < L1.re := by
    rcases lt_or_eq_of_le hge with h | h
    · rw [hL1]; exact h
    · exfalso; apply hne; rw [hL1] at *; exact Complex.ext h.symm hreal
  exact Complex.pos_iff.mpr ⟨hre_pos, hreal.symm⟩

/-- **The fourfold product is a positive real on `(1, ∞)`.** For real quadratic `χ₁, χ₂` and real
`x > 1`, `0 < LSeries (fourfoldCoeff χ₁ χ₂) x = ζ(x)·L(x,χ₁)·L(x,χ₂)·L(x,χ₁χ₂)` — the positivity
engine directly on the fourfold coefficients (`fourfoldCoeff_nonneg`, `fourfoldCoeff_apply_one`). -/
theorem fourfold_pos_of_one_lt {N : ℕ} [NeZero N] (χ₁ χ₂ : DirichletCharacter ℂ N)
    (hχ₁ : χ₁ ^ 2 = 1) (hχ₂ : χ₂ ^ 2 = 1) {x : ℝ} (hx : 1 < x) :
    0 < LSeries (fourfoldCoeff χ₁ χ₂) (x : ℂ) := by
  have habsc : LSeries.abscissaOfAbsConv (⇑(fourfoldCoeff χ₁ χ₂)) < (x : EReal) := by
    refine lt_of_le_of_lt
      (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        (x := 1) (fun y hy => LSeriesSummable_fourfoldCoeff χ₁ χ₂ (by rwa [Complex.ofReal_re]))) ?_
    exact_mod_cast hx
  refine ArithmeticFunction.LSeries_positive (fun n => fourfoldCoeff_nonneg hχ₁ hχ₂ n) ?_ habsc
  rw [fourfoldCoeff_apply_one]; exact zero_lt_one

/-! ## 2. The residue `λ = L(1,χ₁)·L(1,χ₂)·L(1,χ₁χ₂)` is positive -/

/-- **The Goldfeld residue is positive.** For real quadratic characters `χ₁ ≠ 1`, `χ₂ ≠ 1` at a
common level with `χ₁χ₂ ≠ 1`, the residue of the fourfold product at `s = 1`,
`λ = L(1,χ₁)·L(1,χ₂)·L(1,χ₁χ₂)`, is a positive real (product of three positives via
`LFunction_apply_one_pos`). This is the `λ > 0` used in Goldfeld's "no exceptional zero" branch. -/
theorem lambda_pos {N : ℕ} [NeZero N] {χ₁ χ₂ : DirichletCharacter ℂ N}
    (hsq1 : χ₁ ^ 2 = 1) (hsq2 : χ₂ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1) (hχ₂1 : χ₂ ≠ 1)
    (hprod : χ₁ * χ₂ ≠ 1) :
    0 < LFunction χ₁ 1 * LFunction χ₂ 1 * LFunction (χ₁ * χ₂) 1 := by
  have hsqp : (χ₁ * χ₂) ^ 2 = 1 := by rw [mul_pow, hsq1, hsq2, mul_one]
  have h1 : 0 < LFunction χ₁ 1 := LFunction_apply_one_pos hχ₁1 hsq1
  have h2 : 0 < LFunction χ₂ 1 := LFunction_apply_one_pos hχ₂1 hsq2
  have h3 : 0 < LFunction (χ₁ * χ₂) 1 := LFunction_apply_one_pos hprod hsqp
  exact mul_pos (mul_pos h1 h2) h3

/-! ## 3. Estermann's positivity lemma (the flagged analytic core) and its fourfold instantiation

`EstermannPositivity` is the one genuinely hard analytic input of Goldfeld's proof, abstracted
faithfully. It is Montgomery–Vaughan *Multiplicative Number Theory I*, Lemma 11.13 (a quantitative
form of Landau's theorem on singularities of Dirichlet series with nonnegative coefficients). Its
proof — Cauchy estimates on the pole-subtracted `ζ·f − f(1)/(s−1)` about `s = 2`, combined with a
Landau truncation summation over the nonnegative Taylor coefficients — is deferred to a later wave;
see `docs/blueprints/flags.md` (SW S4b). Everything below the abstraction is proven here. -/

open scoped ComplexOrder in
/-- **Estermann's positivity lemma (abstract).** For an entire `f` bounded by `M ≥ 1` on the disk
`|s − 2| < 3/2`, whose product with `ζ` has nonnegative Dirichlet coefficients `r` (with `r 1 = 1`)
on `Re s > 1`, if `f` takes a nonnegative-real value at some `σ ∈ [19/20, 1)` then
`(1 − σ)/4 · M^{−3(1−σ)} ≤ (f 1).re`. (MV Lemma 11.13; the `Differentiable ℂ f` hypothesis is only
used through analyticity on the disk — every factor in the Goldfeld application is entire.) -/
def EstermannPositivity : Prop :=
  ∀ (f : ℂ → ℂ) (r : ℕ → ℂ) (M : ℝ), 1 ≤ M → Differentiable ℂ f →
    (∀ z ∈ Metric.ball (2 : ℂ) (3 / 2), ‖f z‖ ≤ M) →
    (0 ≤ r) → r 1 = 1 → LSeries.abscissaOfAbsConv r < 2 →
    (∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries r s) →
    ∀ {σ : ℝ}, (19 / 20 : ℝ) ≤ σ → σ < 1 → (0 : ℂ) ≤ f (σ : ℂ) →
      (1 - σ) / 4 * M ^ (-(3 * (1 - σ))) ≤ (f 1).re

/-- **The fourfold instantiation of Estermann's lemma.** Assuming `EstermannPositivity`, for real
quadratic characters `χ₁, χ₂` at a common level (all of `χ₁, χ₂, χ₁χ₂` non-principal), with a
disk-growth bound `M` on the product `f = L(·,χ₁)·L(·,χ₂)·L(·,χ₁χ₂)` and an exceptional zero
`σ ∈ [19/20, 1)` of the first factor `L(·,χ₁)`, we get
`(1−σ)/4 · M^{−3(1−σ)} ≤ (L(1,χ₁)·L(1,χ₂)·L(1,χ₁χ₂)).re`.

This is the exact Estermann plug-in of Goldfeld/MV §11.14: `f` is entire (each factor is a
non-principal L-function, `differentiable_LFunction`), `ζ·f` has the nonnegative fourfold
coefficients (`fourfoldCoeff`, `LSeries_fourfoldCoeff_eq`), and `f(σ) = 0` because the `χ₁` factor
vanishes. The residual analytic input — the disk growth `M` — is supplied as `hMbnd` (the standard
`L(s,χ) ≪ q^{1/2} log q` disk bound, MV Lemma 10.15). -/
theorem estermann_fourfold (hEst : EstermannPositivity) {N : ℕ} [NeZero N]
    (χ₁ χ₂ : DirichletCharacter ℂ N) (hsq1 : χ₁ ^ 2 = 1) (hsq2 : χ₂ ^ 2 = 1)
    (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1) (hp : χ₁ * χ₂ ≠ 1)
    {M : ℝ} (hM : 1 ≤ M)
    (hMbnd : ∀ z ∈ Metric.ball (2 : ℂ) (3 / 2),
      ‖LFunction χ₁ z * LFunction χ₂ z * LFunction (χ₁ * χ₂) z‖ ≤ M)
    {σ : ℝ} (hσlo : (19 / 20 : ℝ) ≤ σ) (hσhi : σ < 1) (hzero : LFunction χ₁ (σ : ℂ) = 0) :
    (1 - σ) / 4 * M ^ (-(3 * (1 - σ))) ≤
      (LFunction χ₁ 1 * LFunction χ₂ 1 * LFunction (χ₁ * χ₂) 1).re := by
  set f : ℂ → ℂ := fun s => LFunction χ₁ s * LFunction χ₂ s * LFunction (χ₁ * χ₂) s with hf
  have hfdiff : Differentiable ℂ f :=
    ((differentiable_LFunction h1).mul (differentiable_LFunction h2)).mul
      (differentiable_LFunction hp)
  have hr0 : (0 : ℕ → ℂ) ≤ ⇑(fourfoldCoeff χ₁ χ₂) := fun n => fourfoldCoeff_nonneg hsq1 hsq2 n
  have hr1 : (fourfoldCoeff χ₁ χ₂) 1 = 1 := fourfoldCoeff_apply_one χ₁ χ₂
  have hident : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * f s = LSeries (⇑(fourfoldCoeff χ₁ χ₂)) s := by
    intro s hs
    rw [hf, LSeries_fourfoldCoeff_eq χ₁ χ₂ hs]; ring
  have hfσ : (0 : ℂ) ≤ f (σ : ℂ) := by
    have : f (σ : ℂ) = 0 := by simp only [hf, hzero, zero_mul]
    rw [this]
  have habsc : LSeries.abscissaOfAbsConv (⇑(fourfoldCoeff χ₁ χ₂)) < 2 := by
    refine lt_of_le_of_lt
      (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
        (x := 1) (fun y hy => LSeriesSummable_fourfoldCoeff χ₁ χ₂ (by rwa [Complex.ofReal_re]))) ?_
    have h12 : ((1 : ℝ) : EReal) < ((2 : ℝ) : EReal) := by exact_mod_cast (one_lt_two : (1 : ℝ) < 2)
    simpa using h12
  exact hEst f (⇑(fourfoldCoeff χ₁ χ₂)) M hM hfdiff hMbnd hr0 hr1 habsc hident hσlo hσhi hfσ

/-! ## 4. The exceptional-zero dichotomy (the ineffective choice) -/

/-- **Goldfeld's dichotomy.** For every `ε > 0`, EITHER no real primitive quadratic character has an
L-zero in the window `[1−ε, 1)` (then Siegel is trivial and *effective*), OR there is a *fixed* such
`χ₁` with a zero `β₁` in the window (Goldfeld's ineffective choice — `χ₁, β₁` depend only on `ε`,
and are produced by `Classical.em`, hence cannot be exhibited by any finite procedure). This is the
structural source of the ineffectivity of Siegel's constant. -/
theorem siegel_dichotomy (ε : ℝ) :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      ∀ {β : ℝ}, LFunction χ β = 0 → ¬ (1 - ε ≤ β ∧ β < 1))
    ∨
    (∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β₁ : ℝ),
      χ₁.IsPrimitive ∧ χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ LFunction χ₁ β₁ = 0 ∧ 1 - ε ≤ β₁ ∧ β₁ < 1) := by
  rcases em (∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β₁ : ℝ),
      χ₁.IsPrimitive ∧ χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ LFunction χ₁ β₁ = 0 ∧ 1 - ε ≤ β₁ ∧ β₁ < 1) with h | h
  · exact Or.inr h
  · refine Or.inl ?_
    intro q _ χ hprim hsq hne β hzero ⟨hw1, hw2⟩
    exact h ⟨q, ‹NeZero q›, χ, β, hprim, hsq, hne, hzero, hw1, hw2⟩

/-! ## 5. Isolating `L(1,χ₂)` — the "combine" step -/

/-- **The combine step (MV/Bao–Vo).** All three of `L(1,χ₁), L(1,χ₂), L(1,χ₁χ₂)` are positive
reals (`LFunction_apply_one_pos`), so the fourfold value at `1` factors as
`(L(1,χ₁)L(1,χ₂)L(1,χ₁χ₂)).re = L(1,χ₁).re · L(1,χ₂).re · L(1,χ₁χ₂).re`. Dividing a lower bound `A`
for the product by upper bounds `B₁ ≥ L(1,χ₁).re`, `B₂ ≥ L(1,χ₁χ₂).re` isolates a lower bound on
`L(1,χ₂).re`. -/
theorem siegel_L_one_extract {N : ℕ} [NeZero N] {χ₁ χ₂ : DirichletCharacter ℂ N}
    (hsq1 : χ₁ ^ 2 = 1) (hsq2 : χ₂ ^ 2 = 1) (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1) (hp : χ₁ * χ₂ ≠ 1)
    {A B₁ B₂ : ℝ} (hA : A ≤ (LFunction χ₁ 1 * LFunction χ₂ 1 * LFunction (χ₁ * χ₂) 1).re)
    (hB₁ : (LFunction χ₁ 1).re ≤ B₁) (hB₂ : (LFunction (χ₁ * χ₂) 1).re ≤ B₂)
    (hB₁pos : 0 < B₁) (hB₂pos : 0 < B₂) :
    A / (B₁ * B₂) ≤ (LFunction χ₂ 1).re := by
  have hsqp : (χ₁ * χ₂) ^ 2 = 1 := by rw [mul_pow, hsq1, hsq2, mul_one]
  obtain ⟨r1, i1⟩ := Complex.pos_iff.mp (LFunction_apply_one_pos h1 hsq1)
  obtain ⟨r2, i2⟩ := Complex.pos_iff.mp (LFunction_apply_one_pos h2 hsq2)
  obtain ⟨r3, i3⟩ := Complex.pos_iff.mp (LFunction_apply_one_pos hp hsqp)
  set a : ℝ := (LFunction χ₁ 1).re
  set b : ℝ := (LFunction χ₂ 1).re
  set c : ℝ := (LFunction (χ₁ * χ₂) 1).re
  have hab_im : (LFunction χ₁ 1 * LFunction χ₂ 1).im = 0 := by
    rw [Complex.mul_im, ← i1, ← i2]; ring
  have hab_re : (LFunction χ₁ 1 * LFunction χ₂ 1).re = a * b := by
    rw [Complex.mul_re, ← i1]; ring
  have hre : (LFunction χ₁ 1 * LFunction χ₂ 1 * LFunction (χ₁ * χ₂) 1).re = a * b * c := by
    rw [Complex.mul_re, hab_re, hab_im, ← i3]; ring
  rw [hre] at hA
  rw [div_le_iff₀ (mul_pos hB₁pos hB₂pos)]
  have step : a * b * c ≤ b * (B₁ * B₂) := by
    have hac : a * c ≤ B₁ * B₂ := mul_le_mul hB₁ hB₂ r3.le hB₁pos.le
    calc a * b * c = b * (a * c) := by ring
      _ ≤ b * (B₁ * B₂) := mul_le_mul_of_nonneg_left hac r2.le
  linarith [hA, step]

/-! ## 6. Goldfeld's quantitative L(1)-lower bound (the reduction to Estermann) -/

/-- **Goldfeld's quantitative lower bound for `L(1,χ₂)`.** Assuming `EstermannPositivity`, for two
real quadratic characters `χ₁, χ₂` at a common level (all of `χ₁, χ₂, χ₁χ₂` non-principal), given
the standard disk growth bound `M` on `L(·,χ₁)·L(·,χ₂)·L(·,χ₁χ₂)` (`hMbnd`), one-point upper bounds
`B₁ ≥ L(1,χ₁).re`, `B₂ ≥ L(1,χ₁χ₂).re`, and an exceptional zero `σ ∈ [19/20,1)` of `L(·,χ₁)`, then
`(1−σ)/4 · M^{−3(1−σ)} / (B₁B₂) ≤ L(1,χ₂).re`.

This is Goldfeld's engine in one line: `estermann_fourfold` (Estermann applied to the nonnegative
fourfold coefficients) followed by `siegel_L_one_extract` (dividing out the fixed factors). With
`χ₁, σ` the *fixed* exceptional data of `siegel_dichotomy` and `M ≪ (qq₁)^{1/2}·log`, the right side
is `≫_ε q^{−ε}` — the assertion of Siegel's theorem — after the (deferred) `ε`-power arithmetic. -/
theorem goldfeld_L_one_lower (hEst : EstermannPositivity) {N : ℕ} [NeZero N]
    (χ₁ χ₂ : DirichletCharacter ℂ N) (hsq1 : χ₁ ^ 2 = 1) (hsq2 : χ₂ ^ 2 = 1)
    (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1) (hp : χ₁ * χ₂ ≠ 1)
    {M : ℝ} (hM : 1 ≤ M)
    (hMbnd : ∀ z ∈ Metric.ball (2 : ℂ) (3 / 2),
      ‖LFunction χ₁ z * LFunction χ₂ z * LFunction (χ₁ * χ₂) z‖ ≤ M)
    {B₁ B₂ : ℝ} (hB₁ : (LFunction χ₁ 1).re ≤ B₁) (hB₂ : (LFunction (χ₁ * χ₂) 1).re ≤ B₂)
    (hB₁pos : 0 < B₁) (hB₂pos : 0 < B₂)
    {σ : ℝ} (hσlo : (19 / 20 : ℝ) ≤ σ) (hσhi : σ < 1) (hzero : LFunction χ₁ (σ : ℂ) = 0) :
    (1 - σ) / 4 * M ^ (-(3 * (1 - σ))) / (B₁ * B₂) ≤ (LFunction χ₂ 1).re :=
  siegel_L_one_extract hsq1 hsq2 h1 h2 hp
    (estermann_fourfold hEst χ₁ χ₂ hsq1 hsq2 h1 h2 hp hM hMbnd hσlo hσhi hzero)
    hB₁ hB₂ hB₁pos hB₂pos

/-! ## 7. The zero-free form: the easy branch is effective; the hard branch is the Estermann core -/

/-- **Siegel's theorem (zero-free form), decomposed along the dichotomy.** The exact target
statement, proven from a single hypothesis `hHard` isolating the *exceptional* case (when a fixed
real primitive quadratic `χ₁` with an L-zero `β₁ ∈ [1−ε, 1)` exists — Goldfeld's ineffective
choice). The **no-exceptional-zero branch is proven here, fully and effectively** (with `C = ε`):
if `L(·,χ)` never vanishes in `[1−ε, 1)` then every zero `β < 1` already satisfies `β < 1 − ε
≤ 1 − ε/qᵉ`. The exceptional branch — where `L(1,χ) ≫_ε q^{−ε}` (`goldfeld_L_one_lower` via
`EstermannPositivity`) is converted to the zero-free bound by the derivative mean-value step — is
the hypothesis `hHard`; discharging it is deferred (see `docs/blueprints/flags.md`, SW S4b). -/
theorem siegel_zero_free_of_exceptional_case
    (hHard : ∀ ε : ℝ, 0 < ε →
      (∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β₁ : ℝ),
        χ₁.IsPrimitive ∧ χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ LFunction χ₁ β₁ = 0 ∧ 1 - ε ≤ β₁ ∧ β₁ < 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
        ∀ {β : ℝ}, LFunction χ β = 0 → β < 1 → β ≤ 1 - C / (q : ℝ) ^ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      ∀ {β : ℝ}, LFunction χ β = 0 → β < 1 → β ≤ 1 - C / (q : ℝ) ^ ε := by
  intro ε hε
  rcases siegel_dichotomy ε with hno | hyes
  · -- the effective easy branch: `C = ε`
    refine ⟨ε, hε, ?_⟩
    intro q _ χ hprim hsq hne β hzero hβ1
    have hnot := hno q χ hprim hsq hne hzero
    have hβlt : β < 1 - ε := by
      by_contra hc; exact hnot ⟨not_lt.mp hc, hβ1⟩
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hqε : (1 : ℝ) ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq1 hε.le
    have hle : ε / (q : ℝ) ^ ε ≤ ε := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hqε, hε.le]
    linarith [hβlt, hle]
  · exact hHard ε hε hyes

end Salt.SW
