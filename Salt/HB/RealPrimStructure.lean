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

* `isQuadratic_of_int` (S0) — every `MulChar R ℤ` is quadratic; the "real" hypothesis is free.
* `crtFactor₁` / `crtFactor₂`, `crtFactor_apply` (S1) — the Chinese-Remainder splitting of a
  Dirichlet character across a coprime factorisation of the modulus, with uniqueness
  (`crtFactor₁_unique`, `crtFactor₂_unique`).
* `crtFactor₁_isPrimitive` / `crtFactor₂_isPrimitive` (S2) — primitivity is componentwise.
* `not_isPrimitive_of_odd_prime_pow` (S3) — a character mod `p ^ k`, `p` odd, `k ≥ 2`, is never
  primitive.
* `eq_quadraticChar_of_isPrimitive` (S3) — mod an odd prime `p`, the only primitive character
  is the Legendre character.
* `not_isPrimitive_two`, `exists_odd_sq_sub_dvd`, `not_isPrimitive_two_pow` (S4) — no primitive
  character mod `2`, none mod `2 ^ a` for `a ≥ 4` (via Hensel lifting of square roots at `2`).
* `eq_chi4_of_isPrimitive`, `eq_chi8_or_chi8'_of_isPrimitive` (S4) — the classification mod `4`
  and mod `8`.
* `isPrimitive_chi4`, `isPrimitive_chi8`, `isPrimitive_chi8'` (S4) — the primitivity of
  `χ₄`, `χ₈`, `χ₈'`, which mathlib asserts only in prose.
* `squarefree_and_eq_jacobiChar_of_isPrimitive` (S5) — the odd part: a primitive character to an
  odd modulus `m` forces `m` squarefree and the character to be `J(· | m)`.
* `exists_split_of_isPrimitive` (S5) — the decomposition in the exact shape consumed by
  `sum_two_forms_le_gcd_of_split`, and `exists_split_of_isPrimitive_enumerated` with the `2`-part
  named (`1`, `χ₄`, `χ₈`, `χ₈'`).
* `structure_of_isPrimitive` (S5) — **the structure theorem**: `q = 2 ^ a * m` with
  `a ∈ {0, 2, 3}`, `m` odd squarefree, and `χ n = χ₂ n * J(n | m)` for all `n : ℕ`.
* `sum_two_forms_le_gcd_of_isPrimitive` (S5) — **the discharge**: the p.217 bound
  `|∑_{t mod q} χ (u t + u') χ (v t + v')| ≤ (q, u v' - v u')` for *every* primitive
  `ℤ`-valued (equivalently: real) character mod `q`, with no structure hypothesis left.

## Value ring

`ℤ`-valued throughout, matching `Salt/HB/RealPrimitive.lean` and `Salt/HB/QuadCharSum.lean`.
A `ℂ`-valued consumer composes with `MulChar.ringHomComp (Int.castRingHom ℂ)`.

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

/-! ### S3: the local classification at an odd prime -/

section OddLocal

/-- **S3 (odd prime, exponent `≥ 2`).**  There is no primitive `ℤ`-valued character modulo
`p ^ k` for `p` an odd prime and `k ≥ 2`.

The kernel `K` of the reduction `(ZMod p^k)ˣ → (ZMod p)ˣ` has order `p ^ (k-1)`, which is **odd**;
a character into `ℤˣ = {±1}` is therefore trivial on `K` (a `±1` value raised to an odd power
returns itself), so `χ` factors through `p < p ^ k`. -/
theorem not_isPrimitive_of_odd_prime_pow {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (χ : DirichletCharacter ℤ (p ^ k)) : ¬ χ.IsPrimitive := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  have hple : 2 ≤ p := hp.two_le
  have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
  set K := (ZMod.unitsMap hpk).ker with hK
  have hcard : Nat.card K = p ^ (k - 1) := by
    have h2 : (ZMod.unitsMap hpk).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective hpk)
    have h3 : Nat.card K * Nat.card ((ZMod p)ˣ) = Nat.card ((ZMod (p ^ k))ˣ) := by
      rw [← Subgroup.card_mul_index K, hK, Subgroup.index_ker, h2, Subgroup.card_top]
    rw [Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units_eq_totient,
      Nat.totient_prime hp, Nat.card_eq_fintype_card (α := (ZMod (p ^ k))ˣ),
      ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega)] at h3
    exact Nat.eq_of_mul_eq_mul_right (by omega) h3
  have hoddK : Odd (Nat.card K) := by rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  have hft : χ.FactorsThrough p := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hpk]
    intro u hu
    rw [MonoidHom.mem_ker]
    have hu1 : u ^ Nat.card K = 1 := by
      have h := pow_card_eq_one' (G := K) (x := (⟨u, hu⟩ : K))
      have h' : (((⟨u, hu⟩ : K) ^ Nat.card K : K) : (ZMod (p ^ k))ˣ)
          = ((1 : K) : (ZMod (p ^ k))ˣ) := congrArg (fun x : K => (x : (ZMod (p ^ k))ˣ)) h
      rw [Subgroup.coe_pow, OneMemClass.coe_one] at h'
      exact h'
    rcases Int.units_eq_one_or (χ.toUnitHom u) with h | h
    · exact h
    · exfalso
      have h2 := congrArg χ.toUnitHom hu1
      rw [map_pow, map_one, h, hoddK.neg_one_pow] at h2
      have h3 : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg Units.val h2
      norm_num at h3
  intro hprim
  have hle : χ.conductor ≤ p := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
  rw [DirichletCharacter.isPrimitive_def] at hprim
  rw [hprim] at hle
  have hlt : p < p ^ k := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

/-- **S3 (odd prime, exponent `1`).**  Modulo an odd prime `p` the *only* primitive `ℤ`-valued
character is the Legendre (quadratic) character.

`(ZMod p)ˣ` is cyclic; a `±1`-valued character is determined by its value at a generator `g`,
and a nontrivial one must send `g` to `-1`.  Both `χ` and `quadraticChar` are nontrivial. -/
theorem eq_quadraticChar_of_isPrimitive {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℤ p) (hprim : χ.IsPrimitive) : χ = quadraticChar (ZMod p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hrc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hne : χ ≠ 1 := by
    intro h
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hprim
    exact hp.ne_one hprim.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have key : ∀ ψ : DirichletCharacter ℤ p, ψ ≠ 1 → ψ.toUnitHom g = -1 := by
    intro ψ hψ
    rcases Int.units_eq_one_or (ψ.toUnitHom g) with h | h
    · refine absurd (MulChar.ext fun a => ?_) hψ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
      rw [← MulChar.coe_toUnitHom, map_zpow, h, one_zpow, Units.val_one, MulChar.one_apply_coe]
    · exact h
  have h1 := key χ hne
  have h2 := key (quadraticChar (ZMod p)) (quadraticChar_ne_one hrc)
  refine MulChar.ext fun a => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  rw [← MulChar.coe_toUnitHom, ← MulChar.coe_toUnitHom (quadraticChar (ZMod p)), map_zpow,
    map_zpow, h1, h2]

end OddLocal

/-! ### S4: the local classification at `2` -/

section TwoLocal

/-- **S4 (`a = 1`).**  There is no primitive character modulo `2`: `(ZMod 2)ˣ` is trivial, so
every character mod `2` is the trivial one, of conductor `1`. -/
theorem not_isPrimitive_two (χ : DirichletCharacter ℤ 2) : ¬ χ.IsPrimitive := by
  have htriv : ∀ a : (ZMod 2)ˣ, a = 1 := by decide
  have h1 : χ = 1 := MulChar.ext fun a => by
    rw [htriv a, Units.val_one, MulChar.map_one, MulChar.map_one]
  intro hprim
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hprim
  exact absurd hprim (by norm_num)

/-- **Hensel at `2`.**  An integer `≡ 1 (mod 8)` is a square modulo every power of `2`, with an
odd square root.  The lift `y ↦ y - 2 ^ (j-1) c` gains one `2`-adic digit as soon as `j ≥ 3`
(that is where `2 j - 2 ≥ j + 1` bites) — the arithmetic reason the `2`-part of a real primitive
modulus never exceeds `8`. -/
theorem exists_odd_sq_sub_dvd (k : ℕ) {n : ℤ} (h8 : (8 : ℤ) ∣ n - 1) :
    ∃ y : ℤ, Odd y ∧ (2 : ℤ) ^ k ∣ y ^ 2 - n := by
  induction k with
  | zero => exact ⟨1, odd_one, by simp⟩
  | succ j ih =>
      rcases le_or_gt (j + 1) 3 with hj | hj
      · refine ⟨1, odd_one, ?_⟩
        have h1 : (2 : ℤ) ^ (j + 1) ∣ 8 := by
          have : (8 : ℤ) = 2 ^ 3 := by norm_num
          rw [this]; exact pow_dvd_pow 2 hj
        have h2 : (8 : ℤ) ∣ 1 ^ 2 - n := by
          obtain ⟨c, hc⟩ := h8; exact ⟨-c, by rw [one_pow]; omega⟩
        exact h1.trans h2
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
        obtain ⟨y, hyodd, c, hc⟩ := ih
        obtain ⟨e, he⟩ := hyodd
        refine ⟨y - 2 ^ (i + 2) * c, ⟨e - 2 ^ (i + 1) * c, by rw [he]; ring⟩,
          ⟨-(c * e) + 2 ^ i * c ^ 2, ?_⟩⟩
        linear_combination hc - 2 ^ (i + 3) * c * he

/-- **S4 (`a ≥ 4`).**  There is no primitive character modulo `2 ^ a` for `a ≥ 4`.

A unit `≡ 1 (mod 8)` is a square (`exists_odd_sq_sub_dvd`), and a `ℤ`-valued character kills
squares; so `χ` factors through `8 < 2 ^ a`. -/
theorem not_isPrimitive_two_pow {a : ℕ} (ha : 4 ≤ a) (χ : DirichletCharacter ℤ (2 ^ a)) :
    ¬ χ.IsPrimitive := by
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  have h8 : (8 : ℕ) ∣ 2 ^ a := by
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this]; exact pow_dvd_pow 2 (by omega)
  have hft : χ.FactorsThrough 8 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h8]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    -- the value of `u`, as an integer `≡ 1 (mod 8)`
    set n : ℤ := ((u : ZMod (2 ^ a)).val : ℤ) with hn
    have hcast : ((n : ℤ) : ZMod (2 ^ a)) = (u : ZMod (2 ^ a)) := by
      rw [hn]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
    have h8n : (8 : ℤ) ∣ n - 1 := by
      have h1 : ((u : ZMod (2 ^ a)).cast : ZMod 8) = 1 := by
        have := congrArg Units.val hu
        rwa [ZMod.unitsMap_val, Units.val_one] at this
      have h2 : ((n : ℤ) : ZMod 8) = 1 := by
        rw [hn]; push_cast; rw [ZMod.natCast_val]; exact h1
      have h3 : ((n - 1 : ℤ) : ZMod 8) = 0 := by rw [Int.cast_sub, h2, Int.cast_one, sub_self]
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n - 1) 8).mp h3
    obtain ⟨y, _, hy⟩ := exists_odd_sq_sub_dvd a h8n
    -- `u` is a square, so `χ u = (χ y) ^ 2 = 1`
    have hsq : ((y : ℤ) : ZMod (2 ^ a)) * ((y : ℤ) : ZMod (2 ^ a)) = (u : ZMod (2 ^ a)) := by
      have h4 : (((y ^ 2 - n : ℤ)) : ZMod (2 ^ a)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast hy
      rw [Int.cast_sub, sub_eq_zero, Int.cast_pow, sq] at h4
      rw [h4, hcast]
    have hyu : IsUnit ((y : ℤ) : ZMod (2 ^ a)) :=
      isUnit_of_mul_isUnit_left (y := ((y : ℤ) : ZMod (2 ^ a))) (by rw [hsq]; exact Units.isUnit u)
    refine Units.ext ?_
    rw [MulChar.coe_toUnitHom, Units.val_one, ← hsq, map_mul]
    rcases int_apply_unit χ hyu with h | h <;> rw [h] <;> norm_num
  intro hprim
  have hle : χ.conductor ≤ 8 := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
  rw [DirichletCharacter.isPrimitive_def] at hprim
  rw [hprim] at hle
  have hlt : (8 : ℕ) < 2 ^ a := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ < 2 ^ a := Nat.pow_lt_pow_right one_lt_two (by omega)
  omega

/-- Divisor bookkeeping at a prime power: to be primitive mod `2 ^ a` it suffices not to factor
through `2 ^ (a - 1)`, since every proper divisor of `2 ^ a` divides `2 ^ (a - 1)`. -/
theorem isPrimitive_two_pow_of_not_factorsThrough {a : ℕ} (ha : 1 ≤ a)
    (χ : DirichletCharacter ℤ (2 ^ a)) (h : ¬ χ.FactorsThrough (2 ^ (a - 1))) : χ.IsPrimitive := by
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  obtain ⟨j, hj, hcj⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (DirichletCharacter.conductor_dvd_level χ)
  have hjlt : j < a := by
    rcases Nat.eq_or_lt_of_le hj with rfl | h1
    · exact absurd hcj hne
    · exact h1
  have hdvd1 : χ.conductor ∣ 2 ^ (a - 1) := by rw [hcj]; exact pow_dvd_pow 2 (by omega)
  have hdvd2 : (2 : ℕ) ^ (a - 1) ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
  exact h (DirichletCharacter.FactorsThrough.mono
    (hχ := DirichletCharacter.factorsThrough_conductor χ) (hd := hdvd1) (hm := hdvd2))

/-- **S4: `χ₄` is primitive.**  mathlib names `χ₄` "the primitive quadratic character on
`ZMod 4`" in prose only; this is the proof.  The unit `3 ≡ 1 (mod 2)` is in the kernel of
`(ZMod 4)ˣ → (ZMod 2)ˣ` but not in the kernel of `χ₄`. -/
theorem isPrimitive_chi4 :
    DirichletCharacter.IsPrimitive (ZMod.χ₄ : DirichletCharacter ℤ 4) := by
  refine isPrimitive_two_pow_of_not_factorsThrough (a := 2) (by norm_num) ZMod.χ₄ ?_
  change ¬ DirichletCharacter.FactorsThrough (ZMod.χ₄ : DirichletCharacter ℤ 4) 2
  intro hft
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show (2 : ℕ) ∣ 4 by norm_num)] at hft
  obtain ⟨u, hu3⟩ : ∃ u : (ZMod 4)ˣ, (u : ZMod 4) = 3 := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have hmem : u ∈ (ZMod.unitsMap (show (2 : ℕ) ∣ 4 by norm_num)).ker := by
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [ZMod.unitsMap_val, Units.val_one, hu3]
    decide
  have hk := congrArg Units.val (MonoidHom.mem_ker.mp (hft hmem))
  rw [MulChar.coe_toUnitHom, Units.val_one, hu3] at hk
  exact absurd hk (by decide)

/-- **S4: `χ₈` is primitive.**  The unit `5 ≡ 1 (mod 4)` separates `χ₈` from level `4`. -/
theorem isPrimitive_chi8 :
    DirichletCharacter.IsPrimitive (ZMod.χ₈ : DirichletCharacter ℤ 8) := by
  refine isPrimitive_two_pow_of_not_factorsThrough (a := 3) (by norm_num) ZMod.χ₈ ?_
  change ¬ DirichletCharacter.FactorsThrough (ZMod.χ₈ : DirichletCharacter ℤ 8) 4
  intro hft
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show (4 : ℕ) ∣ 8 by norm_num)] at hft
  obtain ⟨u, hu5⟩ : ∃ u : (ZMod 8)ˣ, (u : ZMod 8) = 5 := ⟨⟨5, 5, by decide, by decide⟩, rfl⟩
  have hmem : u ∈ (ZMod.unitsMap (show (4 : ℕ) ∣ 8 by norm_num)).ker := by
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [ZMod.unitsMap_val, Units.val_one, hu5]
    decide
  have hk := congrArg Units.val (MonoidHom.mem_ker.mp (hft hmem))
  rw [MulChar.coe_toUnitHom, Units.val_one, hu5] at hk
  exact absurd hk (by decide)

/-- **S4: `χ₈'` is primitive.** -/
theorem isPrimitive_chi8' :
    DirichletCharacter.IsPrimitive (ZMod.χ₈' : DirichletCharacter ℤ 8) := by
  refine isPrimitive_two_pow_of_not_factorsThrough (a := 3) (by norm_num) ZMod.χ₈' ?_
  change ¬ DirichletCharacter.FactorsThrough (ZMod.χ₈' : DirichletCharacter ℤ 8) 4
  intro hft
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show (4 : ℕ) ∣ 8 by norm_num)] at hft
  obtain ⟨u, hu5⟩ : ∃ u : (ZMod 8)ˣ, (u : ZMod 8) = 5 := ⟨⟨5, 5, by decide, by decide⟩, rfl⟩
  have hmem : u ∈ (ZMod.unitsMap (show (4 : ℕ) ∣ 8 by norm_num)).ker := by
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [ZMod.unitsMap_val, Units.val_one, hu5]
    decide
  have hk := congrArg Units.val (MonoidHom.mem_ker.mp (hft hmem))
  rw [MulChar.coe_toUnitHom, Units.val_one, hu5] at hk
  exact absurd hk (by decide)

/-- **S4 (`a = 2`).**  The only primitive character modulo `4` is `χ₄`. -/
theorem eq_chi4_of_isPrimitive (χ : DirichletCharacter ℤ 4) (hprim : χ.IsPrimitive) :
    χ = ZMod.χ₄ := by
  have hunits : ∀ v : (ZMod 4)ˣ, (v : ZMod 4) = 1 ∨ (v : ZMod 4) = 3 := by decide
  have hne : χ ≠ 1 := by
    intro h
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hprim
    exact absurd hprim (by norm_num)
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
  have hu3 : (u : ZMod 4) = 3 := by
    rcases hunits u with h | h
    · exact absurd (by rw [h]; exact MulChar.map_one χ) hu
    · exact h
  rw [hu3] at hu
  have h3 : χ (3 : ZMod 4) = -1 :=
    (int_apply_unit χ (⟨⟨3, 3, by decide, by decide⟩, rfl⟩ : IsUnit (3 : ZMod 4))).resolve_left hu
  refine MulChar.ext fun a => ?_
  rcases hunits a with h | h
  · rw [h, MulChar.map_one, MulChar.map_one]
  · rw [h, h3]; decide

/-- **S4 (`a = 3`).**  The primitive characters modulo `8` are exactly `χ₈` and `χ₈'`.

Primitivity means `χ` does not factor through `4`, i.e. `χ 5 = -1`; the remaining freedom is the
sign of `χ 3`, and `χ 7 = χ 3 · χ 5` is then forced. -/
theorem eq_chi8_or_chi8'_of_isPrimitive (χ : DirichletCharacter ℤ 8) (hprim : χ.IsPrimitive) :
    χ = ZMod.χ₈ ∨ χ = ZMod.χ₈' := by
  have h48 : (4 : ℕ) ∣ 8 := by norm_num
  have hnft : ¬ χ.FactorsThrough 4 := by
    intro hft
    have hle : χ.conductor ≤ 4 :=
      Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
    rw [DirichletCharacter.isPrimitive_def] at hprim
    rw [hprim] at hle
    omega
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h48] at hnft
  obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.mp hnft
  have hcast : ((u : ZMod 8).cast : ZMod 4) = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.mp hu1)
    rwa [ZMod.unitsMap_val, Units.val_one] at h
  have hker : ∀ v : (ZMod 8)ˣ, ((v : ZMod 8).cast : ZMod 4) = 1 →
      (v : ZMod 8) = 1 ∨ (v : ZMod 8) = 5 := by decide
  have hu5 : (u : ZMod 8) = 5 := by
    rcases hker u hcast with h | h
    · refine absurd (MonoidHom.mem_ker.mpr (Units.ext ?_)) hu2
      rw [MulChar.coe_toUnitHom, Units.val_one, h, MulChar.map_one]
    · exact h
  have h5 : χ (5 : ZMod 8) = -1 := by
    refine (int_apply_unit χ
      (⟨⟨5, 5, by decide, by decide⟩, rfl⟩ : IsUnit (5 : ZMod 8))).resolve_left ?_
    intro h
    refine absurd (MonoidHom.mem_ker.mpr (Units.ext ?_)) hu2
    rw [MulChar.coe_toUnitHom, Units.val_one, hu5, h]
  have h7 : χ (7 : ZMod 8) = χ 3 * χ 5 := by
    rw [show (7 : ZMod 8) = 3 * 5 by decide, map_mul]
  have hunits : ∀ v : (ZMod 8)ˣ, (v : ZMod 8) = 1 ∨ (v : ZMod 8) = 3 ∨ (v : ZMod 8) = 5 ∨
      (v : ZMod 8) = 7 := by decide
  rcases int_apply_unit χ
    (⟨⟨3, 3, by decide, by decide⟩, rfl⟩ : IsUnit (3 : ZMod 8)) with h3 | h3
  · refine Or.inr (MulChar.ext fun a => ?_)
    rcases hunits a with h | h | h | h
    · rw [h, MulChar.map_one, MulChar.map_one]
    · rw [h, h3]; decide
    · rw [h, h5]; decide
    · rw [h, h7, h3, h5]; decide
  · refine Or.inl (MulChar.ext fun a => ?_)
    rcases hunits a with h | h | h | h
    · rw [h, MulChar.map_one, MulChar.map_one]
    · rw [h, h3]; decide
    · rw [h, h5]; decide
    · rw [h, h7, h3, h5]; decide

end TwoLocal

/-! ### S5: the assembly -/

section Assembly

/-- **S5 (the odd part), by induction over the prime factorisation.**  The modulus is carried as
a *variable* `q` with `q = m`, so that the exponent-one collapse `p ^ 1 = p` can be discharged by
`subst` instead of a dependent rewrite of the character's type (the transport trap).

`not_isPrimitive_of_odd_prime_pow` collapses every prime power to a single prime,
`eq_quadraticChar_of_isPrimitive` identifies the local factor with the Legendre symbol, and the
coprime step is `crtFactor_apply` fed by the multiplicativity of `jacobiSym` in its modulus. -/
theorem squarefree_and_eq_jacobiChar_aux : ∀ m : ℕ, ¬ 2 ∣ m →
    ∀ q : ℕ, q = m → ∀ χ : DirichletCharacter ℤ q, χ.IsPrimitive →
      Squarefree q ∧ ∀ n : ZMod q, χ n = jacobiChar q n := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => exact fun h => absurd (dvd_zero 2) h
  | one =>
      rintro _ q rfl χ _
      refine ⟨squarefree_one, fun n => ?_⟩
      rw [show n = 1 from Subsingleton.elim n 1, MulChar.map_one, jacobiChar, jacobiSym.one_right]
  | prime_pow p k hp hk =>
      intro hodd
      have hp2 : p ≠ 2 := by rintro rfl; exact hodd (dvd_pow_self 2 hk.ne')
      haveI : Fact p.Prime := ⟨hp⟩
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · obtain rfl : k = 1 := by omega
        intro q hq
        rw [pow_one] at hq
        subst hq
        intro χ hprim
        refine ⟨hp.squarefree, fun n => ?_⟩
        rw [eq_quadraticChar_of_isPrimitive hp2 χ hprim]
        exact (jacobiChar_prime n).symm
      · rintro q rfl χ hprim
        exact absurd hprim (not_isPrimitive_of_odd_prime_pow hp hp2 hk2 χ)
  | coprime a b ha hb hcop iha ihb =>
      rintro hodd q rfl χ hprim
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      have hodda : ¬ 2 ∣ a := fun h => hodd (h.mul_right b)
      have hoddb : ¬ 2 ∣ b := fun h => hodd (h.mul_left a)
      obtain ⟨hsqa, hea⟩ :=
        iha hodda a rfl (crtFactor₁ hcop χ) (crtFactor₁_isPrimitive hcop χ hprim)
      obtain ⟨hsqb, heb⟩ :=
        ihb hoddb b rfl (crtFactor₂ hcop χ) (crtFactor₂_isPrimitive hcop χ hprim)
      refine ⟨Nat.squarefree_mul_iff.mpr ⟨hcop, hsqa, hsqb⟩, fun n => ?_⟩
      have key : jacobiChar (a * b) n
          = jacobiChar a (ZMod.cast n) * jacobiChar b (ZMod.cast n) := by
        have hcast₁ : ((ZMod.cast n : ZMod a).val : ℤ) = (n.val : ℤ) % (a : ℤ) := by
          rw [← ZMod.natCast_val n, ZMod.val_natCast]
          push_cast
          ring
        have hcast₂ : ((ZMod.cast n : ZMod b).val : ℤ) = (n.val : ℤ) % (b : ℤ) := by
          rw [← ZMod.natCast_val n, ZMod.val_natCast]
          push_cast
          ring
        rw [jacobiChar, jacobiChar, jacobiChar, hcast₁, hcast₂, ← jacobiSym.mod_left,
          ← jacobiSym.mod_left, jacobiSym.mul_right]
      rw [crtFactor_apply hcop χ, hea, heb, key]

/-- **S5 (the odd part).**  A primitive `ℤ`-valued character to an *odd* modulus `m` forces `m`
to be squarefree, and the character to be the Jacobi symbol `J(· | m)`. -/
theorem squarefree_and_eq_jacobiChar_of_isPrimitive (m : ℕ) (hodd : ¬ 2 ∣ m)
    (χ : DirichletCharacter ℤ m) (hprim : χ.IsPrimitive) :
    Squarefree m ∧ ∀ n : ZMod m, χ n = jacobiChar m n :=
  squarefree_and_eq_jacobiChar_aux m hodd m rfl χ hprim

/-- **S5 (the local shape at a factored modulus).**  For `q = 2 ^ a · m` with `m` odd, a
primitive character mod `q` forces `a ∈ {0, 2, 3}`, `m` squarefree, and the D9 exit shape:
`χ n = χ₂ (cast n) · J(cast n | m)` with the `2`-part `χ₂` carrying the two-forms bound. -/
theorem exists_split_of_isPrimitive {a m : ℕ} [NeZero m] (hodd : ¬ 2 ∣ m)
    (hcop : Nat.Coprime (2 ^ a) m) (χ : DirichletCharacter ℤ (2 ^ a * m)) (hprim : χ.IsPrimitive) :
    (a = 0 ∨ a = 2 ∨ a = 3) ∧ Squarefree m ∧
      ∃ χ₂ : ZMod (2 ^ a) → ℤ, HasTwoFormGcdBound (2 ^ a) χ₂ ∧
        ∀ n : ZMod (2 ^ a * m), χ n = χ₂ (ZMod.cast n) * jacobiChar m (ZMod.cast n) := by
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  have h2prim := crtFactor₁_isPrimitive hcop χ hprim
  have hmprim := crtFactor₂_isPrimitive hcop χ hprim
  obtain ⟨hsq, hem⟩ := squarefree_and_eq_jacobiChar_of_isPrimitive m hodd _ hmprim
  have hsplit : ∀ n : ZMod (2 ^ a * m),
      χ n = crtFactor₁ hcop χ (ZMod.cast n) * jacobiChar m (ZMod.cast n) := fun n => by
    rw [crtFactor_apply hcop χ, hem]
  rcases a with _ | _ | _ | _ | a4
  · exact ⟨Or.inl rfl, hsq, _, hasTwoFormGcdBound_of_modulus_one _ (by
      rw [show (0 : ZMod 1) = 1 from Subsingleton.elim _ _, MulChar.map_one]; norm_num), hsplit⟩
  · exact absurd h2prim (not_isPrimitive_two _)
  · refine ⟨Or.inr (Or.inl rfl), hsq, _, ?_, hsplit⟩
    rw [eq_chi4_of_isPrimitive _ h2prim]
    exact hasTwoFormGcdBound_chi4
  · rcases eq_chi8_or_chi8'_of_isPrimitive _ h2prim with h8 | h8
    · refine ⟨Or.inr (Or.inr rfl), hsq, _, ?_, hsplit⟩
      rw [h8]; exact hasTwoFormGcdBound_chi8
    · refine ⟨Or.inr (Or.inr rfl), hsq, _, ?_, hsplit⟩
      rw [h8]; exact hasTwoFormGcdBound_chi8'
  · exact absurd h2prim (not_isPrimitive_two_pow (by omega) _)

/-- **S5: THE STRUCTURE THEOREM (node WEIL-TRIO-W4-a).**  Let `χ` be a primitive `ℤ`-valued —
equivalently, real — Dirichlet character modulo `q ≥ 1`.  Then

* `q = 2 ^ a · m` with `a ∈ {0, 2, 3}` and `m` odd squarefree, and
* `χ n = χ₂ n · J(n | m)` for every natural `n`,

where the `2`-part `χ₂` is one of the four admissible characters (trivial, `χ₄`, `χ₈`, `χ₈'`) —
recorded here through the property that actually matters downstream, namely that `χ₂` satisfies
the two-forms bound at the sharp constant `1`.

The `ℕ`-indexed form of the decomposition avoids all dependent transport; the `ZMod`-indexed
form fixed by design note D9 is `exists_split_of_isPrimitive`. -/
theorem structure_of_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℤ q)
    (hprim : χ.IsPrimitive) :
    ∃ (a m : ℕ) (χ₂ : ZMod (2 ^ a) → ℤ), q = 2 ^ a * m ∧ (a = 0 ∨ a = 2 ∨ a = 3) ∧
      Squarefree m ∧ ¬ 2 ∣ m ∧ HasTwoFormGcdBound (2 ^ a) χ₂ ∧
      ∀ n : ℕ, χ n = χ₂ n * jacobiChar m n := by
  obtain ⟨a, m, hodd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne q) 2 (by norm_num)
  haveI : NeZero m := ⟨by rintro rfl; exact hodd (dvd_zero 2)⟩
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  obtain ⟨ha, hsq, χ₂, hb, hs⟩ := exists_split_of_isPrimitive hodd hcop χ hprim
  refine ⟨a, m, χ₂, rfl, ha, hsq, hodd, hb, fun n => ?_⟩
  have e1 : (ZMod.cast ((n : ℕ) : ZMod (2 ^ a * m)) : ZMod (2 ^ a)) = ((n : ℕ) : ZMod (2 ^ a)) := by
    rw [← ZMod.castHom_apply (h := dvd_mul_right (2 ^ a) m), map_natCast]
  have e2 : (ZMod.cast ((n : ℕ) : ZMod (2 ^ a * m)) : ZMod m) = ((n : ℕ) : ZMod m) := by
    rw [← ZMod.castHom_apply (h := dvd_mul_left m (2 ^ a)), map_natCast]
  rw [hs, e1, e2]

/-- **S5: THE DISCHARGE (Heath-Brown p.217, unconditional form).**  For **every** primitive
`ℤ`-valued (equivalently: real) character `χ` modulo `q` and arbitrary coefficients,

`|∑_{t mod q} χ (u t + u') χ (v t + v')| ≤ (q, u v' - v u')`.

This is `sum_two_forms_le_gcd_of_split` with its structure hypothesis discharged by the structure
theorem: nothing is assumed about the shape of `q` or of `χ` beyond primitivity.  A `ℂ`-valued
consumer composes with `MulChar.ringHomComp (Int.castRingHom ℂ)`. -/
theorem sum_two_forms_le_gcd_of_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℤ q)
    (hprim : χ.IsPrimitive) (u u' v v' : ZMod q) :
    |∑ t : ZMod q, χ (u * t + u') * χ (v * t + v')|
      ≤ (Nat.gcd q (u * v' - v * u').val : ℤ) := by
  obtain ⟨a, m, hodd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne q) 2 (by norm_num)
  haveI : NeZero m := ⟨by rintro rfl; exact hodd (dvd_zero 2)⟩
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  obtain ⟨_, hsq, χ₂, hb, hs⟩ := exists_split_of_isPrimitive hodd hcop χ hprim
  exact sum_two_forms_le_gcd_of_split hcop hsq hodd hb hs u u' v v'

/-- **S5 (ii) in enumerated form.**  The same decomposition as `exists_split_of_isPrimitive`, but
with the `2`-part named: the admissible characters are the trivial one (`a = 0`), `χ₄` (`a = 2`),
and `χ₈` or `χ₈'` (`a = 3`) — precisely the list of `2`-parts enumerated in
`Salt/HB/RealPrimitive.lean`.  (Recall `χ₈' = χ₄ · χ₈`, mathlib's `ZMod.χ₈'_eq_χ₄_mul_χ₈`.) -/
theorem exists_split_of_isPrimitive_enumerated {a m : ℕ} [NeZero m] (hodd : ¬ 2 ∣ m)
    (hcop : Nat.Coprime (2 ^ a) m) (χ : DirichletCharacter ℤ (2 ^ a * m)) (hprim : χ.IsPrimitive) :
    Squarefree m ∧
      ((a = 0 ∧ ∀ n : ZMod (2 ^ a * m), χ n = jacobiChar m (ZMod.cast n)) ∨
       (a = 2 ∧ ∀ n : ZMod (2 ^ a * m),
          χ n = ZMod.χ₄ (ZMod.cast n) * jacobiChar m (ZMod.cast n)) ∨
       (a = 3 ∧ ∀ n : ZMod (2 ^ a * m),
          χ n = ZMod.χ₈ (ZMod.cast n) * jacobiChar m (ZMod.cast n)) ∨
       (a = 3 ∧ ∀ n : ZMod (2 ^ a * m),
          χ n = ZMod.χ₈' (ZMod.cast n) * jacobiChar m (ZMod.cast n))) := by
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  have h2prim := crtFactor₁_isPrimitive hcop χ hprim
  have hmprim := crtFactor₂_isPrimitive hcop χ hprim
  obtain ⟨hsq, hem⟩ := squarefree_and_eq_jacobiChar_of_isPrimitive m hodd _ hmprim
  have hsplit : ∀ n : ZMod (2 ^ a * m),
      χ n = crtFactor₁ hcop χ (ZMod.cast n) * jacobiChar m (ZMod.cast n) := fun n => by
    rw [crtFactor_apply hcop χ, hem]
  rcases a with _ | _ | _ | _ | a4
  · refine ⟨hsq, Or.inl ⟨rfl, fun n => ?_⟩⟩
    rw [hsplit n, show (ZMod.cast n : ZMod (2 ^ 0)) = 1 from
      (Subsingleton.elim (α := ZMod 1) _ _), MulChar.map_one, one_mul]
  · exact absurd h2prim (not_isPrimitive_two _)
  · exact ⟨hsq, Or.inr (Or.inl ⟨rfl, fun n => by rw [hsplit n, eq_chi4_of_isPrimitive _ h2prim]⟩)⟩
  · rcases eq_chi8_or_chi8'_of_isPrimitive _ h2prim with h8 | h8
    · exact ⟨hsq, Or.inr (Or.inr (Or.inl ⟨rfl, fun n => by rw [hsplit n, h8]⟩))⟩
    · exact ⟨hsq, Or.inr (Or.inr (Or.inr ⟨rfl, fun n => by rw [hsplit n, h8]⟩))⟩
  · exact absurd h2prim (not_isPrimitive_two_pow (by omega) _)

end Assembly

end Salt.HB
