/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.RealPrimitive
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The real primitive structure theorem (node WEIL-TRIO-W4-a)

`Salt/HB/RealPrimitive.lean` proves Heath-Brown's p.217 composite two-forms bound
*conditionally on a structure hypothesis*: the character has to be presented as a CRT product
of an admissible `2`-part with the Jacobi character of an odd squarefree modulus.  This file
supplies that hypothesis, i.e. the classical structure theorem for real primitive characters.

Over the value ring `ℤ` the "real" hypothesis is automatic: `ℤˣ = {1, -1}`, so **every**
`MulChar R ℤ` is quadratic (`isQuadratic_of_int`).  Only primitivity is assumed.

## Main results

* `crtFactor₁` / `crtFactor₂`, `crtFactor_apply` (S1) — the Chinese-Remainder splitting of a
  Dirichlet character across a coprime factorisation of the modulus, with uniqueness
  (`crtFactor₁_unique`).
* `crtFactor₁_isPrimitive` / `crtFactor₂_isPrimitive` (S2) — primitivity is componentwise.
* `not_isPrimitive_of_odd_prime_pow` (S3) — a character mod `p ^ k`, `p` odd, `k ≥ 2`, is never
  primitive.
* `eq_quadraticChar_of_isPrimitive` (S3) — mod an odd prime `p`, the only primitive character
  is the Legendre character.
* `not_isPrimitive_two`, `not_isPrimitive_two_pow` (S4) — no primitive character mod `2`, none
  mod `2 ^ a` for `a ≥ 4`.
* `eq_chi4_of_isPrimitive`, `eq_chi8_or_chi8'_of_isPrimitive` (S4) — the classification mod `4`
  and mod `8`.
* `isPrimitive_chi4`, `isPrimitive_chi8`, `isPrimitive_chi8'` (S4) — the primitivity of
  `χ₄`, `χ₈`, `χ₈'`, which mathlib asserts only in prose.
* `eq_jacobiChar_of_isPrimitive` (S5) — the odd part: a primitive character to an odd modulus
  `m` forces `m` squarefree and the character to be `J(· | m)`.
* `structure_of_isPrimitive` (S5) — **the structure theorem**: `q = 2 ^ a * m` with
  `a ∈ {0, 2, 3}`, `m` odd squarefree, and `χ n = χ₂ n * J(n | m)` for all `n : ℕ`.
* `sum_two_forms_le_gcd_of_isPrimitive` (S5) — **the discharge**: the p.217 bound
  `|∑_{t mod q} χ (u t + u') χ (v t + v')| ≤ (q, u v' - v u')` for *every* primitive
  `ℤ`-valued (equivalently: real) character mod `q`, with no structure hypothesis left.
-/

namespace Salt.HB

open Finset

/-! ### S0: `ℤ`-valued characters are automatically quadratic -/

/-- Every `ℤ`-valued multiplicative character is quadratic — `ℤˣ = {1, -1}` leaves no room.
This is why the theorems below need no "real" hypothesis. -/
theorem isQuadratic_of_int {R : Type*} [CommMonoidWithZero R] (χ : MulChar R ℤ) :
    χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rcases Int.units_eq_one_or (χ.toUnitHom u) with h | h
    · exact Or.inr (Or.inl (by rw [← MulChar.coe_toUnitHom, h]; rfl))
    · exact Or.inr (Or.inr (by rw [← MulChar.coe_toUnitHom, h]; rfl))
  · exact Or.inl (χ.map_nonunit ha)

/-- A `ℤ`-valued character takes the value `1` or `-1` at a unit. -/
theorem int_apply_unit {R : Type*} [CommMonoidWithZero R] (χ : MulChar R ℤ) {a : R}
    (ha : IsUnit a) : χ a = 1 ∨ χ a = -1 := by
  rcases isQuadratic_of_int χ a with h | h | h
  · exact absurd h (by
      obtain ⟨u, rfl⟩ := ha
      simpa using (Units.ne_zero (χ.toUnitHom u)) ∘ (fun hh => by
        rw [← MulChar.coe_toUnitHom] at hh; exact_mod_cast hh))
  · exact Or.inl h
  · exact Or.inr h

/-! ### S1: the Chinese-Remainder splitting of a Dirichlet character -/

section CRT

variable {R : Type*} [CommMonoidWithZero R] {q₁ q₂ : ℕ}

/-- The CRT description of the reduction maps: modulo `q₁ q₂` the Chinese-Remainder isomorphism
is the pair of the two reductions.  (Any two ring homomorphisms out of `ZMod n` agree.) -/
theorem chineseRemainder_apply (hcop : Nat.Coprime q₁ q₂) (n : ZMod (q₁ * q₂)) :
    (ZMod.chineseRemainder hcop) n = ((ZMod.cast n : ZMod q₁), (ZMod.cast n : ZMod q₂)) := by
  have h : ((ZMod.chineseRemainder hcop : ZMod (q₁ * q₂) ≃+* ZMod q₁ × ZMod q₂) :
      ZMod (q₁ * q₂) →+* ZMod q₁ × ZMod q₂)
      = RingHom.prod (ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁))
          (ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂)) := RingHom.ext_zmod _ _
  have := congrArg (fun r : ZMod (q₁ * q₂) →+* ZMod q₁ × ZMod q₂ => r n) h
  simpa [RingHom.prod_apply, ZMod.castHom_apply] using this

/-- The first CRT injection `ZMod q₁ →* ZMod (q₁ q₂)`: `x ↦ (x, 1)`.  Multiplicative but not
additive; that is all a multiplicative character needs. -/
def crtIn₁ (hcop : Nat.Coprime q₁ q₂) (x : ZMod q₁) : ZMod (q₁ * q₂) :=
  (ZMod.chineseRemainder hcop).symm (x, 1)

/-- The second CRT injection `ZMod q₂ →* ZMod (q₁ q₂)`: `x ↦ (1, x)`. -/
def crtIn₂ (hcop : Nat.Coprime q₁ q₂) (x : ZMod q₂) : ZMod (q₁ * q₂) :=
  (ZMod.chineseRemainder hcop).symm (1, x)

theorem crtIn₁_one (hcop : Nat.Coprime q₁ q₂) : crtIn₁ hcop (1 : ZMod q₁) = 1 := by
  simp [crtIn₁, show ((1 : ZMod q₁), (1 : ZMod q₂)) = 1 from rfl]

theorem crtIn₂_one (hcop : Nat.Coprime q₁ q₂) : crtIn₂ hcop (1 : ZMod q₂) = 1 := by
  simp [crtIn₂, show ((1 : ZMod q₁), (1 : ZMod q₂)) = 1 from rfl]

theorem crtIn₁_mul (hcop : Nat.Coprime q₁ q₂) (x y : ZMod q₁) :
    crtIn₁ hcop (x * y) = crtIn₁ hcop x * crtIn₁ hcop y := by
  simp only [crtIn₁, ← map_mul]
  congr 1
  simp

theorem crtIn₂_mul (hcop : Nat.Coprime q₁ q₂) (x y : ZMod q₂) :
    crtIn₂ hcop (x * y) = crtIn₂ hcop x * crtIn₂ hcop y := by
  simp only [crtIn₂, ← map_mul]
  congr 1
  simp

theorem isUnit_crtIn₁_iff (hcop : Nat.Coprime q₁ q₂) (x : ZMod q₁) :
    IsUnit (crtIn₁ hcop x) ↔ IsUnit x := by
  constructor
  · intro h
    have h2 := h.map (ZMod.chineseRemainder hcop)
    rw [crtIn₁, RingEquiv.apply_symm_apply] at h2
    exact (Prod.isUnit_iff.mp h2).1
  · intro h
    have h2 : IsUnit ((x, (1 : ZMod q₂))) := Prod.isUnit_iff.mpr ⟨h, isUnit_one⟩
    exact h2.map (ZMod.chineseRemainder hcop).symm

theorem isUnit_crtIn₂_iff (hcop : Nat.Coprime q₁ q₂) (x : ZMod q₂) :
    IsUnit (crtIn₂ hcop x) ↔ IsUnit x := by
  constructor
  · intro h
    have h2 := h.map (ZMod.chineseRemainder hcop)
    rw [crtIn₂, RingEquiv.apply_symm_apply] at h2
    exact (Prod.isUnit_iff.mp h2).2
  · intro h
    have h2 : IsUnit (((1 : ZMod q₁), x)) := Prod.isUnit_iff.mpr ⟨isUnit_one, h⟩
    exact h2.map (ZMod.chineseRemainder hcop).symm

/-- **S1: the `q₁`-part of a character mod `q₁ q₂`** (`(q₁, q₂) = 1`). -/
def crtFactor₁ (hcop : Nat.Coprime q₁ q₂) (χ : DirichletCharacter R (q₁ * q₂)) :
    DirichletCharacter R q₁ where
  toFun x := χ (crtIn₁ hcop x)
  map_one' := by simp [crtIn₁_one]
  map_mul' x y := by simp [crtIn₁_mul]
  map_nonunit' x hx := χ.map_nonunit (fun h => hx ((isUnit_crtIn₁_iff hcop x).mp h))

/-- **S1: the `q₂`-part of a character mod `q₁ q₂`** (`(q₁, q₂) = 1`). -/
def crtFactor₂ (hcop : Nat.Coprime q₁ q₂) (χ : DirichletCharacter R (q₁ * q₂)) :
    DirichletCharacter R q₂ where
  toFun x := χ (crtIn₂ hcop x)
  map_one' := by simp [crtIn₂_one]
  map_mul' x y := by simp [crtIn₂_mul]
  map_nonunit' x hx := χ.map_nonunit (fun h => hx ((isUnit_crtIn₂_iff hcop x).mp h))

@[simp] theorem crtFactor₁_apply (hcop : Nat.Coprime q₁ q₂) (χ : DirichletCharacter R (q₁ * q₂))
    (x : ZMod q₁) : crtFactor₁ hcop χ x = χ (crtIn₁ hcop x) := rfl

@[simp] theorem crtFactor₂_apply (hcop : Nat.Coprime q₁ q₂) (χ : DirichletCharacter R (q₁ * q₂))
    (x : ZMod q₂) : crtFactor₂ hcop χ x = χ (crtIn₂ hcop x) := rfl

/-- **S1: the splitting.**  A Dirichlet character mod `q₁ q₂` with `(q₁, q₂) = 1` is the
product of its two CRT parts.  This is exactly the `hsplit` shape consumed by
`sum_two_forms_le_gcd_of_split`. -/
theorem crtFactor_apply (hcop : Nat.Coprime q₁ q₂) (χ : DirichletCharacter R (q₁ * q₂))
    (n : ZMod (q₁ * q₂)) :
    χ n = crtFactor₁ hcop χ (ZMod.cast n) * crtFactor₂ hcop χ (ZMod.cast n) := by
  rw [crtFactor₁_apply, crtFactor₂_apply, ← map_mul, crtIn₁, crtIn₂, ← map_mul]
  congr 1
  rw [show ((ZMod.cast n : ZMod q₁), (1 : ZMod q₂)) * ((1 : ZMod q₁), (ZMod.cast n : ZMod q₂))
      = ((ZMod.cast n : ZMod q₁), (ZMod.cast n : ZMod q₂)) by simp,
    ← chineseRemainder_apply hcop n]
  simp

/-- **S1: uniqueness.**  A factorisation of `χ` into a `q₁`-part and a `q₂`-part determines the
`q₁`-part. -/
theorem crtFactor₁_unique (hcop : Nat.Coprime q₁ q₂) (χ : DirichletCharacter R (q₁ * q₂))
    (ψ₁ : DirichletCharacter R q₁) (ψ₂ : DirichletCharacter R q₂)
    (hψ : ∀ n : ZMod (q₁ * q₂), χ n = ψ₁ (ZMod.cast n) * ψ₂ (ZMod.cast n)) :
    crtFactor₁ hcop χ = ψ₁ := by
  refine MulChar.ext' fun x => ?_
  rw [crtFactor₁_apply, hψ]
  have h := chineseRemainder_apply hcop (crtIn₁ hcop x)
  rw [crtIn₁, RingEquiv.apply_symm_apply] at h
  rw [show (ZMod.cast (crtIn₁ hcop x) : ZMod q₁) = x from (Prod.ext_iff.mp h).1.symm,
    show (ZMod.cast (crtIn₁ hcop x) : ZMod q₂) = 1 from (Prod.ext_iff.mp h).2.symm,
    MulChar.map_one, mul_one]

/-- **S1: uniqueness** (the `q₂`-part). -/
theorem crtFactor₂_unique (hcop : Nat.Coprime q₁ q₂) (χ : DirichletCharacter R (q₁ * q₂))
    (ψ₁ : DirichletCharacter R q₁) (ψ₂ : DirichletCharacter R q₂)
    (hψ : ∀ n : ZMod (q₁ * q₂), χ n = ψ₁ (ZMod.cast n) * ψ₂ (ZMod.cast n)) :
    crtFactor₂ hcop χ = ψ₂ := by
  refine MulChar.ext' fun x => ?_
  rw [crtFactor₂_apply, hψ]
  have h := chineseRemainder_apply hcop (crtIn₂ hcop x)
  rw [crtIn₂, RingEquiv.apply_symm_apply] at h
  rw [show (ZMod.cast (crtIn₂ hcop x) : ZMod q₁) = 1 from (Prod.ext_iff.mp h).1.symm,
    show (ZMod.cast (crtIn₂ hcop x) : ZMod q₂) = x from (Prod.ext_iff.mp h).2.symm,
    MulChar.map_one, one_mul]

end CRT

/-! ### S2: primitivity is componentwise -/

section Componentwise

variable {R : Type*} [CommMonoidWithZero R] {q₁ q₂ : ℕ}

/-- **S2 (the `q₁`-part).**  If `χ` is primitive mod `q₁ q₂` then its `q₁`-part is primitive.

Contrapositive: if the `q₁`-part factored through a proper divisor `d ∣ q₁`, then `χ` itself
would factor through `d q₂`, a proper divisor of `q₁ q₂`. -/
theorem crtFactor₁_isPrimitive [NeZero q₁] [NeZero q₂] (hcop : Nat.Coprime q₁ q₂)
    (χ : DirichletCharacter R (q₁ * q₂)) (hprim : χ.IsPrimitive) :
    (crtFactor₁ hcop χ).IsPrimitive := by
  haveI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  rw [DirichletCharacter.isPrimitive_def]
  set χ₁ := crtFactor₁ hcop χ with hχ₁
  set d := χ₁.conductor with hd
  have hdvd : d ∣ q₁ := DirichletCharacter.conductor_dvd_level χ₁
  have hdq : d * q₂ ∣ q₁ * q₂ := mul_dvd_mul_right hdvd q₂
  have hker₁ : (ZMod.unitsMap hdvd).ker ≤ χ₁.toUnitHom.ker :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).mp
      (DirichletCharacter.factorsThrough_conductor χ₁)
  have hft : χ.FactorsThrough (d * q₂) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdq]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hU₂ : ZMod.unitsMap (dvd_mul_left q₂ q₁) u = 1 := by
      have h2 := congrArg (ZMod.unitsMap (dvd_mul_left q₂ d)) hu
      rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp, map_one] at h2
      exact h2
    have hU₁ : ZMod.unitsMap hdvd (ZMod.unitsMap (dvd_mul_right q₁ q₂) u) = 1 := by
      have h1 := DFunLike.congr_fun (ZMod.unitsMap_comp hdvd (dvd_mul_right q₁ q₂)) u
      rw [MonoidHom.comp_apply] at h1
      have h2 := congrArg (ZMod.unitsMap (dvd_mul_right d q₂)) hu
      rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp, map_one] at h2
      rw [h1]; exact h2
    have hval₁ : χ₁.toUnitHom (ZMod.unitsMap (dvd_mul_right q₁ q₂) u) = 1 :=
      hker₁ (MonoidHom.mem_ker.mpr hU₁)
    refine Units.ext ?_
    rw [MulChar.coe_toUnitHom, Units.val_one, crtFactor_apply hcop χ,
      ← ZMod.unitsMap_val (dvd_mul_right q₁ q₂) u, ← ZMod.unitsMap_val (dvd_mul_left q₂ q₁) u,
      hU₂, Units.val_one, ← hχ₁, MulChar.map_one, mul_one, ← MulChar.coe_toUnitHom, hval₁,
      Units.val_one]
  have hle : χ.conductor ≤ d * q₂ :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
  rw [DirichletCharacter.isPrimitive_def] at hprim
  rw [hprim] at hle
  refine Nat.le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q₁)) hdvd) ?_
  by_contra hlt
  have hlt' : d < q₁ := Nat.lt_of_not_le hlt
  exact absurd (lt_of_lt_of_le
    (mul_lt_mul_of_pos_right hlt' (Nat.pos_of_ne_zero (NeZero.ne q₂))) hle) (lt_irrefl _)

/-- **S2 (the `q₂`-part).**  If `χ` is primitive mod `q₁ q₂` then its `q₂`-part is primitive. -/
theorem crtFactor₂_isPrimitive [NeZero q₁] [NeZero q₂] (hcop : Nat.Coprime q₁ q₂)
    (χ : DirichletCharacter R (q₁ * q₂)) (hprim : χ.IsPrimitive) :
    (crtFactor₂ hcop χ).IsPrimitive := by
  haveI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  rw [DirichletCharacter.isPrimitive_def]
  set χ₂ := crtFactor₂ hcop χ with hχ₂
  set d := χ₂.conductor with hd
  have hdvd : d ∣ q₂ := DirichletCharacter.conductor_dvd_level χ₂
  have hdq : q₁ * d ∣ q₁ * q₂ := mul_dvd_mul_left q₁ hdvd
  have hker₂ : (ZMod.unitsMap hdvd).ker ≤ χ₂.toUnitHom.ker :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).mp
      (DirichletCharacter.factorsThrough_conductor χ₂)
  have hft : χ.FactorsThrough (q₁ * d) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdq]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hU₁ : ZMod.unitsMap (dvd_mul_right q₁ q₂) u = 1 := by
      have h2 := congrArg (ZMod.unitsMap (dvd_mul_right q₁ d)) hu
      rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp, map_one] at h2
      exact h2
    have hU₂ : ZMod.unitsMap hdvd (ZMod.unitsMap (dvd_mul_left q₂ q₁) u) = 1 := by
      have h1 := DFunLike.congr_fun (ZMod.unitsMap_comp hdvd (dvd_mul_left q₂ q₁)) u
      rw [MonoidHom.comp_apply] at h1
      have h2 := congrArg (ZMod.unitsMap (dvd_mul_left d q₁)) hu
      rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp, map_one] at h2
      rw [h1]; exact h2
    have hval₂ : χ₂.toUnitHom (ZMod.unitsMap (dvd_mul_left q₂ q₁) u) = 1 :=
      hker₂ (MonoidHom.mem_ker.mpr hU₂)
    refine Units.ext ?_
    rw [MulChar.coe_toUnitHom, Units.val_one, crtFactor_apply hcop χ,
      ← ZMod.unitsMap_val (dvd_mul_right q₁ q₂) u, ← ZMod.unitsMap_val (dvd_mul_left q₂ q₁) u,
      hU₁, Units.val_one, MulChar.map_one, one_mul, ← hχ₂, ← MulChar.coe_toUnitHom, hval₂,
      Units.val_one]
  have hle : χ.conductor ≤ q₁ * d :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
  rw [DirichletCharacter.isPrimitive_def] at hprim
  rw [hprim] at hle
  refine Nat.le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q₂)) hdvd) ?_
  by_contra hlt
  have hlt' : d < q₂ := Nat.lt_of_not_le hlt
  exact absurd (lt_of_lt_of_le
    (mul_lt_mul_of_pos_left hlt' (Nat.pos_of_ne_zero (NeZero.ne q₁))) hle) (lt_irrefl _)

end Componentwise

end Salt.HB
