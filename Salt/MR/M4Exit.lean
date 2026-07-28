/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Window
import Salt.MR.M4Residue
import Salt.MR.DoorFloor

/-!
# M4-9 — the three-step exit into `MRTUniformityXi`

The last stone of the MRT §4 port (`docs/exploration/s9-freeze-0726.md`,
⟦AMENDMENT B⟧ row `M4-9`).  Three steps, and only these three:

1. **`δ := doorGrade R.Hlo`, PINNED** (§2).  The head consumes ONE `δ` for the
   whole window range `[R.Hlo, R.Hhi]`; MRT delivers a per-`H` grade.  The pin
   is the grade at the FLOOR, and `doorGrade_anti` (`DoorFloor.lean:125`) is the
   transfer: `doorGrade H ≤ doorGrade R.Hlo` for every `H ≥ R.Hlo`.  Positivity
   comes off the regime's own `hHlo_floor` (`4·10⁶ ≤ R.Hlo`, so `2 ≤ R.Hlo`),
   never off a numeral chosen to fit.

2. **The `C_MRT` gate** (§3).  MRT's delivered grade is
   `C_MRT·(log H)^{−11/4}·loglog H` (`mrtDeliveredGrade`), which beats the door
   grade `(log H)^{−5/4}` (`doorGrade`) exactly past the freeze's in-statement
   gate

   `C_MRT · loglog H ≤ (log H)^{3/2}`   (`mrtGate`).

   The gate is stated SYMBOLICALLY — `C_MRT` is a parameter, never a numeral —
   and is discharged from a plain scale demand `C_MRT² ≤ log H`
   (`mrtGate_of_sq_le`, the genre of `log_scale_threshold`/`regime_hthr_of_scale`
   at `DoorFloor.lean:180/200`: `log L ≤ L` absorbed by one half-power of `L`).
   The scale demand transfers UP the window range for free (`log` is monotone),
   which is `mrtGate_transfer`; a floor `H0scale C_MRT = ⌈exp(C_MRT²)⌉₊`, in the
   `H0door` genre, makes it a regime-floor demand.

3. **The `∀ξ`-outside preservation** (§4–§5).  The per-`(H, α)` bound is
   weakened to the pin (`absWindowBound_le_pin`) and handed to M4-0's adapter
   `mrtUniformityXi_of_absWindowBound_twelve` (`M4Window.lean:267`) unchanged.
   The `∀ ξ` of `MRTUniformityXi` (`MRTDoor.lean:109–111`) stays OUTSIDE the
   integral throughout: nothing in this file introduces a `sup`, and the only
   `intro` over `ξ` is the adapter's own.  `MRTDoor` lives in
   `Salt/Entropy/Chowla/`, not `Salt/MR/`.

## The socket

`m4_exit_socket` is the row's deliverable: `ε`/`δ₀` fixed first, then for every
`C_MRT ≥ 0` and every extra floor/outer-scale demand a regime `R` at which the
ONLY open binder is

```
hbd : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
        NearRatTight (arcDen 12 H) H α →
          (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
            ≤ mrtDeliveredGrade C_MRT H * (H : ℝ)
```

**M4-7 supplies this** (the arithmetic close of the mean-square chain,
`≪ HX/(dW^{1/4})` reassembled at the door normalisation).  Everything else on
the exit path is closed here.

## Two seams recorded

* **The coefficient spelling.**  M4-0's adapter speaks `lamCoeff`
  (`M4Window.lean:73`); the M4 sieve/mean-square chain speaks `liouvilleC`
  (`M4Residue.lean:91`).  Both are the `ℤ→ℂ` cast of
  `ArithmeticFunction.liouville`, so they are `rfl`-equal —
  `lamCoeff_eq_liouvilleC` — and `integral_absWindowSum_lamCoeff_eq` transports
  the door integrand.  No `congr` gymnastics is needed; the bridge is recorded
  so the two names are never re-derived apart.
* **Binder order at the head.**  `budget_head_grade_closed_g`
  (`DoorFloor.lean:276`) takes `U1floor`/`g` BEFORE its `∃ ε`, but the arc floor
  `H₀` of `mrtUniformityXi_of_absWindowBound_twelve` is produced FROM `ε`.  The
  socket therefore fires `log_chowla_two_budget_head_g` directly (whose
  `∀ extraFloor U1floor g` sits after `∃ ε δ₀`, exactly the acyclic shape the
  head was built for) and re-derives the grade payoff through
  `doorGrade_le_of_H0door_le` — the same four lines
  `budget_head_grade_closed_g` uses.  All three floor demands (the door floor
  `H0door δ₀`, the arc floor `H₀`, the gate floor `H0scale C_MRT`) plus the
  caller's own `U1floor` ride the head's two floor slots.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the coefficient bridge (`lamCoeff` vs `liouvilleC`) -/

/-- **The spelling bridge.**  `lamCoeff` (`M4Window.lean:73`, the adapter's
coefficient) and `liouvilleC` (`M4Residue.lean:91`, the mean-square chain's) are
the same `ℤ→ℂ` cast of `ArithmeticFunction.liouville`; the type ascription in
`liouvilleC` is a no-op, so the two elaborate to the same term. -/
theorem lamCoeff_eq_liouvilleC : lamCoeff = liouvilleC := rfl

/-- The window sum is spelling-blind. -/
theorem absWindowSum_lamCoeff_eq (H n : ℕ) (α : ℝ) :
    absWindowSum lamCoeff H n α = absWindowSum liouvilleC H n α := by
  rw [lamCoeff_eq_liouvilleC]

/-- The door integrand is spelling-blind: M4-7 may deliver its bound at either
name. -/
theorem integral_absWindowSum_lamCoeff_eq (x ω H : ℕ) (α : ℝ) :
    (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure x ω))
      = ∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure x ω) := by
  simp only [absWindowSum_lamCoeff_eq]

/-! ## §2 — `δ := doorGrade R.Hlo`, PINNED -/

/-- Every regime clears the `doorGrade` API's `2 ≤ H` side condition, off
`hHlo_floor` (`4·10⁶ ≤ R.Hlo`) — never off a fitted numeral. -/
theorem two_le_regime_Hlo (R : ChowlaRegime) : 2 ≤ R.Hlo := by
  have h := R.hHlo_floor; omega

/-- Inside the regime's window range the log is positive — the side condition
every `rpow` step below needs. -/
theorem log_pos_of_regime_le (R : ChowlaRegime) {H : ℕ} (h : R.Hlo ≤ H) :
    0 < Real.log (H : ℝ) := by
  have h2 : 2 ≤ H := le_trans (two_le_regime_Hlo R) h
  have h1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
  exact Real.log_pos h1

/-- **THE PIN IS POSITIVE.**  `0 < doorGrade R.Hlo`, the `0 < δ` arm of the
budget head's door quantifier, at the raised floor. -/
theorem doorGrade_regime_pos (R : ChowlaRegime) : 0 < doorGrade R.Hlo :=
  doorGrade_pos (two_le_regime_Hlo R)

/-- **THE ANTITONE-IN-`H` TRANSFER.**  The grade at the floor serves the whole
window range: `doorGrade H ≤ doorGrade R.Hlo` for every `H ≥ R.Hlo`.  This is
what makes ONE `δ` legal for the head's `∀ H ∈ [R.Hlo, R.Hhi]` door. -/
theorem doorGrade_le_regime_floor (R : ChowlaRegime) {H : ℕ} (h : R.Hlo ≤ H) :
    doorGrade H ≤ doorGrade R.Hlo :=
  doorGrade_anti (two_le_regime_Hlo R) h

/-- **The pin is admissible at the head.**  Once the regime's floor clears
`H0door δ₀`, the pinned grade is a legal `δ` for `log_chowla_two_budget_head(_g)`:
`0 < doorGrade R.Hlo ≤ δ₀`. -/
theorem doorGrade_regime_pin (R : ChowlaRegime) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hfloor : H0door δ₀ ≤ R.Hlo) :
    0 < doorGrade R.Hlo ∧ doorGrade R.Hlo ≤ δ₀ :=
  ⟨doorGrade_regime_pos R, doorGrade_le_of_H0door_le hδ₀ hfloor⟩

/-! ## §3 — the `C_MRT` gate -/

/-- **MRT's delivered grade**: `C_MRT·(log H)^{−11/4}·loglog H`.  `C_MRT` is a
NAMED PARAMETER — the freeze's constant-absorption margin is what the gate below
buys, so no numeral is ever formed here. -/
def mrtDeliveredGrade (C : ℝ) (H : ℕ) : ℝ :=
  C * Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) * Real.log (Real.log (H : ℝ))

/-- **THE `C_MRT` GATE**, in-statement (freeze ⟦AMENDMENT B⟧, row M4-9):
`C_MRT · loglog H ≤ (log H)^{3/2}`.  Exactly the crossing at which the delivered
grade `C_MRT(log H)^{−11/4}loglog H` falls under the door grade
`(log H)^{−5/4}`: the exponent gap is `−5/4 − (−11/4) = 3/2`. -/
def mrtGate (C : ℝ) (H : ℕ) : Prop :=
  C * Real.log (Real.log (H : ℝ)) ≤ Real.log (H : ℝ) ^ (3 / 2 : ℝ)

/-- The half-power split, once: `L^{3/2} = L·√L` for `L > 0`. -/
private lemma rpow_three_halves {L : ℝ} (hL : 0 < L) : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
  have h : L ^ (3 / 2 : ℝ) = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hL]; norm_num
  rw [h, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- **The gate's arithmetic, at the raised floor** (genre: `log_scale_threshold`,
`DoorFloor.lean:180`).  A plain scale demand `C² ≤ log H` discharges the gate:
`log L ≤ L` costs nothing, and the remaining `C·L ≤ L^{3/2} = L·√L` is
`C ≤ √L`. -/
theorem mrtGate_of_sq_le {C : ℝ} {H : ℕ} (hC : 0 ≤ C) (hL : 0 < Real.log (H : ℝ))
    (hCL : C ^ 2 ≤ Real.log (H : ℝ)) : mrtGate C H := by
  have hlog : Real.log (Real.log (H : ℝ)) ≤ Real.log (H : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hL
    linarith
  have hCs : C ≤ Real.sqrt (Real.log (H : ℝ)) := by
    have h := Real.sqrt_le_sqrt hCL
    rwa [Real.sqrt_sq hC] at h
  have h1 : C * Real.log (Real.log (H : ℝ)) ≤ C * Real.log (H : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hC
  have h2 : C * Real.log (H : ℝ)
      ≤ Real.log (H : ℝ) * Real.sqrt (Real.log (H : ℝ)) := by
    have h3 := mul_le_mul_of_nonneg_right hCs hL.le
    linarith [h3, mul_comm (Real.sqrt (Real.log (H : ℝ))) (Real.log (H : ℝ))]
  change C * Real.log (Real.log (H : ℝ)) ≤ Real.log (H : ℝ) ^ (3 / 2 : ℝ)
  rw [rpow_three_halves hL]
  linarith

/-- **The gate floor** `⌈exp(C²)⌉₊`, in the `H0door` genre (`DoorFloor.lean:86`):
the least window length at which the scale demand `C² ≤ log H` holds.  SHAPE, NOT
NUMERAL — it is never evaluated, only compared. -/
def H0scale (C : ℝ) : ℕ := ⌈Real.exp (C ^ 2)⌉₊

/-- The gate floor is a genuine (positive) floor demand. -/
theorem H0scale_pos (C : ℝ) : 0 < H0scale C :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

/-- **The defining property of `H0scale`**: above the floor the scale demand
holds (mirrors `log_ge_of_H0door_le`, `DoorFloor.lean:136`). -/
theorem sq_le_log_of_H0scale_le {C : ℝ} {H : ℕ} (h : H0scale C ≤ H) :
    C ^ 2 ≤ Real.log (H : ℝ) := by
  have hcast : ((H0scale C : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h
  have h1 : Real.exp (C ^ 2) ≤ (H : ℝ) := le_trans (Nat.le_ceil _) hcast
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rwa [Real.log_exp] at h2

/-- **THE GATE TRANSFERS UP THE WINDOW RANGE.**  Stated at the raised floor
`R.Hlo`, the scale demand `C² ≤ log R.Hlo` gives the gate at EVERY `H ≥ R.Hlo` —
`log` is monotone, so the gate is never re-proved per window length. -/
theorem mrtGate_transfer (R : ChowlaRegime) {C : ℝ} {H : ℕ} (hC : 0 ≤ C)
    (hgate : C ^ 2 ≤ Real.log (R.Hlo : ℝ)) (hH : R.Hlo ≤ H) : mrtGate C H := by
  refine mrtGate_of_sq_le hC (log_pos_of_regime_le R hH) (le_trans hgate ?_)
  have h0 : (0 : ℝ) < (R.Hlo : ℝ) := by
    have := two_le_regime_Hlo R
    exact_mod_cast (by omega : 0 < R.Hlo)
  exact Real.log_le_log h0 (by exact_mod_cast hH)

/-! ## §4 — the delivered grade beats the pin -/

/-- **The gate, cashed**: past the gate the delivered grade is below the door
grade at the SAME window length.  Multiply the gate by `(log H)^{−11/4} > 0` and
read `3/2 + (−11/4) = −5/4`. -/
theorem mrtDeliveredGrade_le_doorGrade {C : ℝ} {H : ℕ} (hL : 0 < Real.log (H : ℝ))
    (hgate : mrtGate C H) : mrtDeliveredGrade C H ≤ doorGrade H := by
  have hgate' : C * Real.log (Real.log (H : ℝ)) ≤ Real.log (H : ℝ) ^ (3 / 2 : ℝ) := hgate
  have hpow : (0 : ℝ) < Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) := Real.rpow_pos_of_pos hL _
  have hid : Real.log (H : ℝ) ^ (3 / 2 : ℝ) * Real.log (H : ℝ) ^ (-(11 / 4 : ℝ))
      = doorGrade H := by
    rw [← Real.rpow_add hL, doorGrade]
    norm_num
  have h := mul_le_mul_of_nonneg_right hgate' hpow.le
  rw [hid] at h
  calc mrtDeliveredGrade C H
      = C * Real.log (Real.log (H : ℝ)) * Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) := by
        rw [mrtDeliveredGrade]; ring
    _ ≤ doorGrade H := h

/-- **THE PIN DOMINATES THE WHOLE RANGE.**  Steps 1 and 2 composed: past the gate
at the floor, `mrtDeliveredGrade C H ≤ doorGrade R.Hlo` for every `H ≥ R.Hlo`. -/
theorem mrtDeliveredGrade_le_pin (R : ChowlaRegime) {C : ℝ} {H : ℕ} (hC : 0 ≤ C)
    (hgate : C ^ 2 ≤ Real.log (R.Hlo : ℝ)) (hH : R.Hlo ≤ H) :
    mrtDeliveredGrade C H ≤ doorGrade R.Hlo :=
  le_trans
    (mrtDeliveredGrade_le_doorGrade (log_pos_of_regime_le R hH)
      (mrtGate_transfer R hC hgate hH))
    (doorGrade_le_regime_floor R hH)

/-! ## §5 — the `∀ξ`-outside preservation -/

/-- **The `hbd` weakening.**  The per-`(H, α)` M4 bound, delivered at MRT's own
per-`H` grade, weakened to the single pinned `δ = doorGrade R.Hlo`.  Binder shape
is byte-matched to `mrtUniformityXi_of_absWindowBound`'s `hbd`
(`M4Window.lean:246–248`): `∀ H, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α, …`,
with `α` OUTSIDE the integral and no `sup` anywhere. -/
theorem absWindowBound_le_pin (R : ChowlaRegime) (C : ℝ) {B₅ : ℝ} (hC : 0 ≤ C)
    (hgate : C ^ 2 ≤ Real.log (R.Hlo : ℝ))
    (hbd : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
          ≤ mrtDeliveredGrade C H * (H : ℝ)) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
          ≤ doorGrade R.Hlo * (H : ℝ) := by
  intro H _ hlo hhi α harc
  refine le_trans (hbd H hlo hhi α harc) ?_
  exact mul_le_mul_of_nonneg_right (mrtDeliveredGrade_le_pin R hC hgate hlo)
    (Nat.cast_nonneg H)

/-- **THE THREE-STEP COMPOSE.**  From

* (i) the `hbd`-shaped hypothesis at MRT's per-`H` delivered grade (M4-7's
  eventual output),
* (ii) the `C_MRT` gate at the raised floor (`C_MRT² ≤ log R.Hlo`), and
* (iii) M4-0's arc adapter `hadapt` (the `∀δ` form of
  `mrtUniformityXi_of_absWindowBound_twelve` at this `R`),

the `Ξ_H`-restricted door at the pinned grade.  The `∀ ξ` of `MRTUniformityXi`
is produced ONLY by `hadapt`; this file never intros it, so the quantifier stays
outside the integral by construction. -/
theorem m4_exit_of_hbd (R : ChowlaRegime) (C : ℝ) (hC : 0 ≤ C)
    (hgate : C ^ 2 ≤ Real.log (R.Hlo : ℝ))
    (hadapt : ∀ δ : ℝ,
      (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
        NearRatTight (arcDen 12 H) H α →
          (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)) →
      MRTUniformityXi R δ)
    (hbd : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen 12 H) H α →
        (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
          ≤ mrtDeliveredGrade C H * (H : ℝ)) :
    MRTUniformityXi R (doorGrade R.Hlo) :=
  hadapt (doorGrade R.Hlo) (absWindowBound_le_pin R C hC hgate hbd)

/-- **The collision at the pinned grade.**  `contradiction_of_mrtDoorXi`
(`MRTDoor.lean:127`) fired at `δ := doorGrade R.Hlo`; its `0 ≤ δ` binder — the
one obligation the `Ξ_H`-weakened door cannot derive for itself — is discharged
by `doorGrade_regime_pos`. -/
theorem m4_exit_collision (R : ChowlaRegime) {c₀ ε K : ℝ} {H : ℕ} [NeZero H]
    (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) (hH : 0 < H)
    (hdoor : MRTUniformityXi R (doorGrade R.Hlo))
    (hXi : ((bigXi R.eps H).card : ℝ) ≤ K)
    (hsmall : K * doorGrade R.Hlo < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXi R.eps H,
        (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
          ∂(logMeasure R.x R.ω)) :
    False :=
  contradiction_of_mrtDoorXi R hlo hhi hH (doorGrade_regime_pos R).le hdoor hXi hsmall hlower

/-! ## §6 — the socket -/

/-- **THE M4 EXIT SOCKET** — the M4-9 deliverable.

`ε` and `δ₀` are fixed FIRST (the head's own honest choice); then, for every
constant `C_MRT ≥ 0` and every extra floor / outer-scale demand `(U1floor, g)`,
a regime `R` at that `ε` whose floor absorbs all three of the exit's floor
demands — the door floor `H0door δ₀`, M4-0's arc floor `H₀`, and the gate floor
`H0scale C_MRT` — and at which log-Chowla-2 does not fail, conditional on the
SINGLE open binder

```
∀ H, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α, NearRatTight (arcDen 12 H) H α →
  (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
    ≤ mrtDeliveredGrade C_MRT H * (H : ℝ)
```

**M4-7 supplies this** (the arithmetic close of the mean-square chain at the door
normalisation).  `integral_absWindowSum_lamCoeff_eq` lets it be delivered at
`liouvilleC` instead, at zero cost.

Non-circularity: `C_MRT`, `U1floor` and `g` are all fixed BEFORE the regime, and
`ε`/`δ₀` before them, so every floor demand fed to the head's two floor slots is
a legal argument.  The `g`-lever and the `U1floor` slot are carried through
verbatim from `log_chowla_two_budget_head_g`. -/
theorem m4_exit_socket :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          H0door δ₀ ≤ R.Hlo ∧ 0 < doorGrade R.Hlo ∧ doorGrade R.Hlo ≤ δ₀ ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                  ≤ mrtDeliveredGrade C H * (H : ℝ)) →
            ¬ logChowla2Fails R.eps R.x R.ω) := by
  obtain ⟨ε, δ₀, hε, hδ₀, hhead⟩ := log_chowla_two_budget_head_g
  refine ⟨ε, δ₀, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨H₀, hH₀⟩ := mrtUniformityXi_of_absWindowBound_twelve ε hε
  obtain ⟨R, hReps, hRdoor, hRU1, hRg, hR⟩ :=
    hhead (H0door δ₀) (max U1floor (max H₀ (H0scale C))) g
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRU1
  have hscale : H0scale C ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRU1
  obtain ⟨hpos, hle⟩ := doorGrade_regime_pin R hδ₀ hRdoor
  refine ⟨R, hReps, hU1, hRg, hRdoor, hpos, hle, fun hbd => ?_⟩
  exact hR (doorGrade R.Hlo) hpos hle
    (m4_exit_of_hbd R C hC (sq_le_log_of_H0scale_le hscale) (hH₀ R hReps harc) hbd)

/-- **The socket's collision form.**  With the failure branch `logChowla2Fails`
assumed at the socket's regime — the head's own negation shape — the exit closes
to `False`.  (The seam itself is `contradiction_of_mrtDoorXi`, fired inside the
head; `m4_exit_collision` above is the same collision exposed directly at the
pinned grade.) -/
theorem m4_exit_socket_False :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                  ≤ mrtDeliveredGrade C H * (H : ℝ)) →
            logChowla2Fails R.eps R.x R.ω → False) := by
  obtain ⟨ε, δ₀, hε, hδ₀, h⟩ := m4_exit_socket
  refine ⟨ε, δ₀, hε, hδ₀, fun C hC U1floor g => ?_⟩
  obtain ⟨R, hReps, hU1, hRg, _, _, _, hR⟩ := h C hC U1floor g
  exact ⟨R, hReps, hU1, hRg, fun hbd hfail => hR hbd hfail⟩

end Salt.MR
