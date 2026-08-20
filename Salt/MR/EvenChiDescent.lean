/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.EvenChiEta
import Salt.MR.LandauDescent

/-!
# E6 — the even descent: the `ℂ → ℝ` restriction, and the even floor in the corpus's shape

`Salt/MR/EvenChiEta.lean` lands the even-χ floor `e4a_L1_lower_even` over a **real-valued**
character (`χ : DirichletCharacter ℝ q`), concluding about `(e4a_toC χ)⁻¹`.  The corpus's
consumer — `LandauL1.L1LowerEffective` — quantifies over **ℂ-valued** `χ` with `χ ^ 2 = 1`.
This file supplies the missing leg.

## Why this leg exists at all, and why it was not free

The helm ruled **ℝ-UP** on 2026-08-19: state the even lane over `ℝ` and push up through
`MulChar.ringHomComp Complex.ofRealHom` (`e4a_toC`), because the up-transport is cheap and
constructive while *pulling `ℂ` down needs an inverse of `ringHomComp`, which is not free*.
That ruling was right and it bought the whole E4a/E5a spine; it also **deferred exactly one
cost to this node**.  The odd lane never paid it because `Salt/MR/LandauOdd.lean` is
ℂ-native from the start.

⛔ **Neither salt nor mathlib has the down-leg.**  Mathlib's `MulChar.IsQuadratic` API is
up-only (`IsQuadratic.comp`), and `Salt/HB/RealPrimStructure.lean` states the convention
explicitly: *"a `ℂ`-valued consumer composes with `MulChar.ringHomComp (Int.castRingHom ℂ)`"*.
So the restriction is built here, once, and is reusable by any lane that needs it.

## The construction

A quadratic character takes values in `{0, 1, -1}`, and is nonzero exactly at units
(`MulChar.apply_ne_zero_iff`).  So at a unit its value is `±1` — already real — and the
restriction is assembled on the unit group, where it is a genuine `MonoidHom`, and extended
by `MulChar.ofUnitHom`.  `e4a_toC_toR` then identifies the round trip **on the nose**.

## Main results

* `e4a_unit_val_pm` — a quadratic ℂ-character takes value `±1` at every unit.
* `e4a_toR` — the real-valued restriction of a quadratic ℂ-valued Dirichlet character.
* `e4a_toC_toR` — `e4a_toC (e4a_toR χ hQ) = χ`.  The round trip is the identity.
* `e4a_eInt` / `e4a_eInt_spec` — the `ℕ`-indexed integer coefficient map the floor consumes.
-/

namespace Salt.MR

open Complex DirichletCharacter

variable {q : ℕ}

/-! ## §1 — values at units -/

/-- A quadratic `ℂ`-valued character takes the value `±1` at every unit: the third branch of
`IsQuadratic` (`χ a = 0`) is excluded there by `MulChar.apply_ne_zero_iff`. -/
theorem e4a_unit_val_pm (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) (a : (ZMod q)ˣ) :
    χ (a : ZMod q) = 1 ∨ χ (a : ZMod q) = -1 := by
  rcases hQ (a : ZMod q) with h | h | h
  · exact absurd h (MulChar.apply_ne_zero_iff.mpr a.isUnit)
  · exact Or.inl h
  · exact Or.inr h

/-- The `±1` value of a quadratic `ℂ`-character at a unit, as a **unit of `ℝ`**. -/
noncomputable def e4a_signRu (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) : ℝˣ := by
  classical exact if χ (a : ZMod q) = 1 then 1 else -1

/-- The defining property: complexifying the real sign returns the character's value. -/
theorem e4a_signRu_coe (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) (a : (ZMod q)ˣ) :
    ((e4a_signRu χ a : ℝ) : ℂ) = χ (a : ZMod q) := by
  classical
  unfold e4a_signRu
  split_ifs with h
  · simp [h]
  · rcases e4a_unit_val_pm χ hQ a with h1 | h1
    · exact absurd h1 h
    · simp [h1]

/-! ## §2 — the restriction -/

/-- The unit-group homomorphism underlying the real restriction.  Multiplicativity is proved
by pushing both sides up to `ℂ` through `e4a_signRu_coe`, where it is `map_mul` for `χ`. -/
noncomputable def e4a_toRHom (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) :
    (ZMod q)ˣ →* ℝˣ where
  toFun := e4a_signRu χ
  map_one' := by
    classical
    unfold e4a_signRu
    simp
  map_mul' x y := by
    apply Units.ext
    apply Complex.ofReal_injective
    push_cast
    rw [e4a_signRu_coe χ hQ, e4a_signRu_coe χ hQ, e4a_signRu_coe χ hQ]
    push_cast
    exact map_mul _ _ _

/-- ⭐ **THE DOWN-LEG.**  The real-valued restriction of a quadratic `ℂ`-valued Dirichlet
character.  This is the inverse of `e4a_toC` on the quadratic locus. -/
noncomputable def e4a_toR (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) :
    DirichletCharacter ℝ q :=
  MulChar.ofUnitHom (e4a_toRHom χ hQ)

/-- ⭐⭐ **THE ROUND TRIP IS THE IDENTITY.**  Complexifying the restriction returns `χ`.
Proved by `MulChar.ext`, which only asks for agreement on units — exactly where the
restriction was built. -/
theorem e4a_toC_toR (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) :
    e4a_toC (e4a_toR χ hQ) = χ := by
  ext a
  rw [e4a_toC_apply]
  change ((e4a_toR χ hQ (a : ZMod q) : ℝ) : ℂ) = χ (a : ZMod q)
  rw [e4a_toR, MulChar.ofUnitHom_coe]
  exact e4a_signRu_coe χ hQ a

/-! ## §3 — the integer coefficient map -/

/-- The `ℕ`-indexed integer coefficients `e` with `(e a : ℝ) = -χ a`, which
`e4a_L1_lower_even` takes as data.  Off the units both sides are `0`. -/
noncomputable def e4a_eInt (χ : DirichletCharacter ℝ q) (a : ℕ) : ℤ := by
  classical exact if χ (a : ZMod q) = 1 then -1 else if χ (a : ZMod q) = -1 then 1 else 0

/-- `e4a_eInt` meets the floor's coefficient hypothesis, for any quadratic real character. -/
theorem e4a_eInt_spec {χ : DirichletCharacter ℝ q} (hQ : χ.IsQuadratic) (a : ℕ) :
    ((e4a_eInt χ a : ℤ) : ℝ) = -χ (a : ZMod q) := by
  classical
  unfold e4a_eInt
  split_ifs with h1 h2
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rcases hQ ((a : ZMod q)) with h | h | h
    · rw [h]; norm_num
    · exact absurd h h1
    · exact absurd h h2

/-! ## §4 — the hypotheses come back down, and E6 -/

/-- Quadraticity descends: `ofReal` is injective, so the `{0, 1, -1}` trichotomy transports. -/
theorem e4a_toR_isQuadratic (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) :
    (e4a_toR χ hQ).IsQuadratic := by
  intro a
  have h := hQ a
  rw [← e4a_toC_toR χ hQ, e4a_toC_apply] at h
  rcases h with h | h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (Or.inl (by exact_mod_cast h))
  · exact Or.inr (Or.inr (by exact_mod_cast h))

/-- Evenness descends. -/
theorem e4a_toR_even (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) (heven : χ (-1) = 1) :
    (e4a_toR χ hQ) (-1) = 1 := by
  have h : e4a_toC (e4a_toR χ hQ) (-1) = 1 := by rw [e4a_toC_toR]; exact heven
  rw [e4a_toC_apply] at h
  exact_mod_cast h

/-- Non-principality descends, by `MulChar.ringHomComp_one`. -/
theorem e4a_toR_ne_one (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic) (hne : χ ≠ 1) :
    e4a_toR χ hQ ≠ 1 := by
  intro h
  apply hne
  calc χ = e4a_toC (e4a_toR χ hQ) := (e4a_toC_toR χ hQ).symm
    _ = e4a_toC 1 := by rw [h]
    _ = 1 := by unfold e4a_toC; exact MulChar.ringHomComp_one _

/-- Primitivity descends, through the `↔` already landed in `EvenChiRingBridge`. -/
theorem e4a_toR_isPrimitive [NeZero q] (χ : DirichletCharacter ℂ q) (hQ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) : (e4a_toR χ hQ).IsPrimitive :=
  (e4a_toC_isPrimitive_iff (e4a_toR χ hQ)).mp (by rw [e4a_toC_toR]; exact hprim)

/-- ⭐⭐⭐ **E6 — THE EVEN FLOOR IN THE CORPUS'S SHAPE.**  The even-χ floor
`log((3+√5)/2)/√q = 2 log φ / √q`, stated over a **ℂ-valued** primitive even quadratic
character and about `L(χ, 1)` itself — the form `LandauL1.L1LowerEffective` consumes.

Every hypothesis is descended through `e4a_toR`; the character's own inverse disappears by
mathlib's `MulChar.IsQuadratic.inv` (`χ⁻¹ = χ`), which is what lets the real-side conclusion
about `(e4a_toC χ_ℝ)⁻¹` land on `χ`. -/
theorem e4a_L1_lower_even_complex [NeZero q] (hq1 : 1 < q) (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) (hprim : χ.IsPrimitive) (heven : χ (-1) = 1) (hne : χ ≠ 1) :
    Real.log ((3 + Real.sqrt 5) / 2) / Real.sqrt q
      ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  have hid : e4a_toC (e4a_toR χ hQ) = χ := e4a_toC_toR χ hQ
  have hQR : (e4a_toR χ hQ).IsQuadratic := e4a_toR_isQuadratic χ hQ
  have hsumR : ∑ a : ZMod q, (e4a_toR χ hQ) a = 0 :=
    MulChar.sum_eq_zero_of_ne_one (e4a_toR_ne_one χ hQ hne)
  have key := e4a_L1_lower_even hq1 (e4a_toR χ hQ) (e4a_toR_isPrimitive χ hQ hprim)
    (e4a_toR_even χ hQ heven) hsumR (e4a_eInt (e4a_toR χ hQ)) (e4a_eInt_spec hQR)
  rwa [hid, hQ.inv] at key

/-! ## §5 — E7: the effective floor at BOTH parities, and the descent -/

/-- `2 log φ ≤ π`.  Via `Real.log_le_sub_one_of_pos`: `log((3+√5)/2) ≤ (1+√5)/2 < 3 < π`. -/
theorem e4a_log_golden_le_pi : Real.log ((3 + Real.sqrt 5) / 2) ≤ Real.pi := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5 : Real.sqrt 5 < 2.24 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hx : (0 : ℝ) < (3 + Real.sqrt 5) / 2 := by linarith
  have h1 := Real.log_le_sub_one_of_pos hx
  have h3 := Real.pi_gt_three
  linarith

/-- `0 < 2 log φ`. -/
theorem e4a_log_golden_pos : 0 < Real.log ((3 + Real.sqrt 5) / 2) := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  exact Real.log_pos (by linarith)

/-- ⭐⭐ **THE PRIMITIVE PRODUCTION AT BOTH PARITIES, grade `3/2`.**  The even half is this
campaign's floor (`e4a_L1_lower_even_complex`, grade `1/2`, weakened one grade); the odd half
is the landed Gauss-sum lane (`L1_lower_odd_primitive_of_sawtooth` at the discharged
`sawtoothOdd`, grade `3/2`, constant `π ≥ 2 log φ`).  `DirichletCharacter.even_or_odd` splits. -/
theorem e4a_L1_lower_primitive_both {f : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f)
    (hprim : ψ.IsPrimitive) (hne : ψ ≠ 1) (hsq : ψ ^ 2 = 1) :
    Real.log ((3 + Real.sqrt 5) / 2) / (f : ℝ) ^ (3 / 2 : ℝ)
      ≤ (DirichletCharacter.LFunction ψ 1).re := by
  have hf1 : 1 < f := by
    rcases Nat.lt_or_ge 1 f with h | h
    · exact h
    · have hfe : f = 1 := le_antisymm h (Nat.one_le_iff_ne_zero.mpr (NeZero.ne f))
      subst hfe
      exact absurd (DirichletCharacter.level_one ψ) hne
  have hf1R : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf1.le
  have hcpos := e4a_log_golden_pos
  rcases DirichletCharacter.even_or_odd ψ with hev | hodd
  · -- EVEN: the campaign floor at grade 1/2, weakened to 3/2
    have h6 := e4a_L1_lower_even_complex hf1 ψ hsq hprim hev hne
    refine le_trans ?_ h6
    have hsr : Real.sqrt (f : ℝ) = (f : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    rw [hsr]
    have hle : (f : ℝ) ^ (1 / 2 : ℝ) ≤ (f : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hf1R (by norm_num)
    have hpos : (0 : ℝ) < (f : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_le_div_of_nonneg_left hcpos.le hpos hle
  · -- ODD: the landed Gauss-sum lane at grade 3/2, constant π
    have hoddfloor := L1_lower_odd_primitive_of_sawtooth sawtoothOdd hprim hodd hsq hne
    refine le_trans ?_ hoddfloor
    have hpos : (0 : ℝ) < (f : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_le_div_of_nonneg_right e4a_log_golden_le_pi hpos.le

/-- ⭐⭐⭐ **E7 — `L1LowerEffective (log((3+√5)/2)) (5/2)`.**  The effective `L(1,χ)` lower bound
at grade `5/2` with the golden constant `2 log φ`, for **every** real nonprincipal `χ`,
primitive or not — the `Prop` that `LandauL1` states as its target.

⛔ **SCOPE FENCE (carried verbatim from the refuter's struck-and-replaced claim).**  This
closes the register's paper-completeness item and retires the `L1_lower_real_effective` Zeno.
It does **NOT** discharge `K_vt`: the live ineffectivity is `siegelBandB`'s EVT **band**
minimum, which a **point** floor at `s = 1` does not reach.  Point→band is a separate,
unpriced campaign; nothing here claims past the point floor. -/
theorem l1LowerEffective_goldenGate :
    L1LowerEffective (Real.log ((3 + Real.sqrt 5) / 2)) (5 / 2) := by
  have h := L1LowerEffective_descend (c := Real.log ((3 + Real.sqrt 5) / 2)) (A := 3 / 2)
    e4a_log_golden_pos (by norm_num)
    (fun f _ ψ hprim hne hsq => e4a_L1_lower_primitive_both ψ hprim hne hsq)
  norm_num at h
  exact h

end Salt.MR
