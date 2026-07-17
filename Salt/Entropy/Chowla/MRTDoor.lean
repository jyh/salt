/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The MRT door (Tao 1509.05422, Prop 2.4 = Matomäki–Radziwiłł–Tao), spine node W3-e

The `L¹`-uniformity door that discharges the log-Chowla-failure branch. Tao's
Proposition 2.4 (arXiv:1509.05422, p. 12) is a THEOREM, proven from [17] =
Matomäki–Radziwiłł–Tao, arXiv:1503.05121 ("An averaged form of Chowla's
conjecture"). The OPEN object is Tao's (4.1) (§4, p. 26): the sup-INSIDE-the-
integral variant, "not currently covered by the existing literature".

This module lands two pieces of the MRT-DOOR-R0 freeze
(`docs/exploration/s3-a3-design.md`):

* `windowExpSum` / `MRTUniformity` (W3-e-door): the exponential-sum window and
  the `∀ α`-OUTSIDE-the-integral uniformity predicate. The quantifier position
  is the whole game — see the warning on `MRTUniformity`.
* `contradiction_of_mrtDoor` (W3-e-seam): the door fires once at `α = −ξ/H`
  across `ξ ∈ Ξ_H`, and the circle-method mass lower bound `c₀ε ≤ …` collides
  with the door's smallness `card·δ ≤ K·δ < c₀ε`. The chain is
  `c₀ε ≤ Σ_{ξ∈Ξ}(1/H)∫‖…‖ ≤ Σ_{ξ∈Ξ}(1/H)(δH) = card·δ ≤ K·δ < c₀ε`.
-/
import Salt.Entropy.Chowla.CircleMethod
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **The window exponential sum** (Tao 1509.05422, the `e(αj)`-twisted window
sum). For the Liouville window `liouvilleWindow H n : Fin H → ℤ`, the finite
exponential sum `∑_{i<H} x_i e(α(i+1))` whose `L¹(logMeasure)` size the MRT door
controls. `liouvilleWindow` is top-level (root namespace), referenced here
unqualified. -/
noncomputable def windowExpSum (H n : ℕ) (α : ℝ) : ℂ :=
  ∑ i : Fin H, (liouvilleWindow H n i : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (((i : ℕ) : ℂ) + 1))

/-- **The MRT uniformity door** (Tao 1509.05422, Prop 2.4, p. 12).

THE `∀ α` STAYS OUTSIDE THE INTEGRAL. The sup-inside form is Tao 1509.05422
(4.1), which is OPEN — moving this quantifier silently downgrades a theorem-door
(Prop 2.4, PROVEN in Matomäki–Radziwiłł–Tao, arXiv:1503.05121) into an open
conjecture. Any edit must preserve the quantifier position; the kernel cannot
police this. Fires once in the spine, at α := −ξ.val/H (Tao p. 24). -/
noncomputable def MRTUniformity (R : ChowlaRegime) (δ : ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
    (∫ n, ‖windowExpSum H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)

/-- **The MRT seam** (W3-e-seam, MRT-DOOR-R0 freeze). The door fires at
`α = −ξ/H` across `ξ ∈ Ξ_H`; its smallness `card·δ ≤ K·δ < c₀ε` collides with
the circle-method mass lower bound `c₀ε ≤ Σ_{ξ∈Ξ}(1/H)∫‖…‖`. Nonnegativity of
`δ` is DERIVED (the door bounds a nonnegative integral by `δH`, and `H > 0`), so
no extra hypothesis is needed. -/
theorem contradiction_of_mrtDoor (R : ChowlaRegime) {δ c₀ ε K : ℝ} {H : ℕ} [NeZero H]
    (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) (hH : 0 < H)
    (hdoor : MRTUniformity R δ)
    (hXi : ((bigXi R.eps H).card : ℝ) ≤ K)
    (hsmall : K * δ < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXi R.eps H,
        (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
          ∂(logMeasure R.x R.ω)) :
    False := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  -- δ ≥ 0: the door bounds a nonnegative integral by `δH`, and `H > 0`.
  have hδ : 0 ≤ δ := by
    have h0 : (0 : ℝ) ≤ ∫ n, ‖windowExpSum H n 0‖ ∂(logMeasure R.x R.ω) :=
      integral_nonneg (fun n => norm_nonneg _)
    have hb := hdoor H hlo hhi 0
    nlinarith [le_trans h0 hb, hHR]
  -- Termwise: (1/H)∫‖…‖ ≤ (1/H)(δH) = δ.
  have hsum : (∑ ξ ∈ bigXi R.eps H,
      (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
        ∂(logMeasure R.x R.ω)) ≤ ∑ _ξ ∈ bigXi R.eps H, δ := by
    apply Finset.sum_le_sum
    intro ξ _
    have hb := hdoor H hlo hhi (-(ξ.val : ℝ) / (H : ℝ))
    calc (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
            ∂(logMeasure R.x R.ω)
        ≤ (1 / (H : ℝ)) * (δ * (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = δ * ((H : ℝ) / (H : ℝ)) := by ring
      _ = δ := by rw [div_self hHR.ne', mul_one]
  -- Σ_{ξ∈Ξ} δ = card·δ ≤ K·δ (δ ≥ 0).
  have hconst : (∑ _ξ ∈ bigXi R.eps H, δ) = ((bigXi R.eps H).card : ℝ) * δ := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((bigXi R.eps H).card : ℝ) * δ ≤ K * δ :=
    mul_le_mul_of_nonneg_right hXi hδ
  have h1 : c₀ * ε ≤ ((bigXi R.eps H).card : ℝ) * δ :=
    le_trans hlower (le_trans hsum (le_of_eq hconst))
  linarith [h1, hcard, hsmall]

/-- **The weakened MRT uniformity door** (Tao 1509.05422, Prop 2.4, p. 12; the
Tao-faithful Ξ_H-restricted surface).

THE `∀ ξ ∈ Ξ_H` STAYS OUTSIDE THE INTEGRAL. The sup-inside form is Tao
1509.05422 (4.1), which is OPEN — moving this quantifier silently downgrades a
theorem-door (Prop 2.4, PROVEN in Matomäki–Radziwiłł–Tao, arXiv:1503.05121) into
an open conjecture. Any edit must preserve the quantifier position; the kernel
cannot police this. Fires once in the spine, at α := −ξ.val/H (Tao p. 24).

This is the weakened, Tao-faithful surface: Tao's proof (p. 24) fires Prop 2.4
only at the finitely many large-spectrum frequencies ξ ∈ Ξ_H; |Ξ_H| ≤ C is
Lemma 3.5 (landed as `bigXi_bounded`). Note ξ = 0 ∈ Ξ_H always, and its instance
is already full Matomäki–Radziwiłł short-interval strength — the weakening
shrinks the door's surface, not its depth (see the W4-MAJOR-R0 RED verdict). -/
noncomputable def MRTUniformityXi (R : ChowlaRegime) (δ : ℝ) : Prop :=
  ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ ξ ∈ bigXi R.eps H,
    (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)

/-- **The door weakening** (W3-e-door, SALVAGE): the full `∀ α`-outside door
implies its Ξ_H-restricted form. Trivial — instantiate at `α := −ξ.val/H` for
each `ξ ∈ Ξ_H`; the frequency restriction only discards instances. -/
theorem mrtUniformity_implies_xi (R : ChowlaRegime) (δ : ℝ) :
    MRTUniformity R δ → MRTUniformityXi R δ := by
  intro h H _ hlo hhi ξ _
  exact h H hlo hhi (-(ξ.val : ℝ) / (H : ℝ))

/-- **The weakened MRT seam** (W3-e-seam, SALVAGE variant). Identical collision to
`contradiction_of_mrtDoor`, but consuming the Ξ_H-restricted door `MRTUniformityXi`.
Because the weakened door no longer speaks at `α = 0`, nonnegativity of `δ` can no
longer be derived from the door (that derivation fired Prop 2.4 at `α = 0`); it is
taken as the explicit hypothesis `hδ : 0 ≤ δ`, per the SALVAGE ruling. The chain is
unchanged: `c₀ε ≤ Σ_{ξ∈Ξ}(1/H)∫‖…‖ ≤ Σ_{ξ∈Ξ}(1/H)(δH) = card·δ ≤ K·δ < c₀ε`. -/
theorem contradiction_of_mrtDoorXi (R : ChowlaRegime) {δ c₀ ε K : ℝ} {H : ℕ} [NeZero H]
    (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) (hH : 0 < H) (hδ : 0 ≤ δ)
    (hdoor : MRTUniformityXi R δ)
    (hXi : ((bigXi R.eps H).card : ℝ) ≤ K)
    (hsmall : K * δ < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXi R.eps H,
        (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
          ∂(logMeasure R.x R.ω)) :
    False := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  -- Termwise: (1/H)∫‖…‖ ≤ (1/H)(δH) = δ, now firing the door at each ξ ∈ Ξ_H.
  have hsum : (∑ ξ ∈ bigXi R.eps H,
      (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
        ∂(logMeasure R.x R.ω)) ≤ ∑ _ξ ∈ bigXi R.eps H, δ := by
    apply Finset.sum_le_sum
    intro ξ hξ
    have hb := hdoor H hlo hhi ξ hξ
    calc (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
            ∂(logMeasure R.x R.ω)
        ≤ (1 / (H : ℝ)) * (δ * (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = δ * ((H : ℝ) / (H : ℝ)) := by ring
      _ = δ := by rw [div_self hHR.ne', mul_one]
  -- Σ_{ξ∈Ξ} δ = card·δ ≤ K·δ (δ ≥ 0).
  have hconst : (∑ _ξ ∈ bigXi R.eps H, δ) = ((bigXi R.eps H).card : ℝ) * δ := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((bigXi R.eps H).card : ℝ) * δ ≤ K * δ :=
    mul_le_mul_of_nonneg_right hXi hδ
  have h1 : c₀ * ε ≤ ((bigXi R.eps H).card : ℝ) * δ :=
    le_trans hlower (le_trans hsum (le_of_eq hconst))
  linarith [h1, hcard, hsmall]

end Salt.Entropy.Chowla
