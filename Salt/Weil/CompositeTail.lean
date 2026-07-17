/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.PrimePower
import Salt.Weil.Composite
import Mathlib

/-!
# Weil track, W6.3 — the composite tail: odd exponents, `p = 2`, and the unit-threaded recursion

This module closes the "consumer tail" of the Kloosterman bound by assembling three pieces on
top of the even prime-power bound (`norm_kloosterman_prime_pow_even`, `Salt.Weil.PrimePower`)
and the twisted multiplicativity (`kloosterman_mul_of_coprime`, `Salt.Weil.Composite`).

## (1) Odd prime-power exponents — *noted, even case landed*

The even case `‖S(a, b; p^{2m})‖ ≤ 2·p^m` (Salié, no Gauss sum) is
`norm_kloosterman_prime_pow_even`.
For odd exponents `k = 2m+1` (`m ≥ 1`, `p` odd) the SAME averaging machinery applies with the shift
family `u z = 1 + p^{m+1}·z` (`(p^{m+1})² = p^{2m+2} = 0` in `ZMod (p^{2m+1})`): the critical
condition `p^{m+1}·w t = 0` reduces (multiplying by the unit `t`) to `ā·ρ(t)² = b̄` in the cyclic
group `(ZMod p^m)ˣ`, with `≤ 2` roots, and each fibre of the reduction
`(ZMod p^{2m+1})ˣ → (ZMod p^m)ˣ` has size `φ(p^{2m+1})/φ(p^m) = p^{m+1}`. This gives the **crude**
bound `‖S(a, b; p^{2m+1})‖ ≤ 2·p^{m+1}` (a factor `√p` above the true `2·p^{m+1/2}`; the missing
`√p` is a one-variable quadratic Gauss sum mod `p`, `‖gaussSum χ ψ‖² = p`, cf.
`Salt.LS.gaussSum_normSq`). The crude bound is proof-identical to the even case with
`p^m ↦ p^{m+1}`; it is TOO LOSSY for a general `τ(c)√c` target but adequate for the squarefull
R4-dispersion consumer, which absorbs a per-odd-prime-power `√p`. The Lean proof is deferred:
it duplicates the ~250-line even-exponent development with the shift exponent bumped by one.
The prime case `k = 1` is the Weil summit and is explicitly OUT of this node (the main line).

## (2) `p = 2` — the crude placeholder

`‖S(a, b; c)‖ ≤ #(ZMod c)ˣ = φ(c) ≤ c` (`norm_kloosterman_le_modulus`), specialised to
`‖S(a, b; 2^k)‖ ≤ 2^k` (`norm_kloosterman_two_pow`). The 2-adic Salié evaluation is fussy; the
consumers absorb a `2^{O(1)}` constant, so the trivial bound is the honest placeholder here.

## (3) The factorization recursion — unit-threaded

`kloosterman_mul_of_coprime` reduces `‖S(a, b; c₁c₂)‖` to the two coprime factors, but the
per-prime-power Salié bound needs `IsUnit` of the first argument. We thread that through the CRT:
* `exists_split_stdAddChar_unit` upgrades the additive-character split to assert the twists
  `l₁, l₂` are **units** (the split constant of a faithful character is a non-zero-divisor, hence
  a unit in the finite ring `ZMod cᵢ`).
* `kloosterman_mul_of_coprime_unit` — the twisted multiplicativity carrying `IsUnit` of both
  first arguments `l₁·(e a).1`, `l₂·(e a).2` (projections of a unit under the CRT iso are units,
  and the Bézout twists `lᵢ` are units, so their product is).
* `norm_kloosterman_le_mul_of_coprime_unit` — the reduction: bounds `M₁, M₂` that hold merely at
  **unit** first arguments give `‖S(a, b; c₁c₂)‖ ≤ M₁·M₂` whenever `a` is a unit. Iterating this
  over `Nat.factorization` (each pair of prime-power factors is coprime, and `a` a unit keeps every
  CRT projection a unit) is the recursion that plugs the per-prime-power Weil bounds into an
  arbitrary modulus.
-/

namespace Salt.Weil

open scoped BigOperators

/-! ### (2) The trivial modulus bound and the `p = 2` placeholder -/

/-- **Trivial modulus bound.** `‖S(a, b; c)‖ ≤ c` for any modulus `c`, from
`‖S‖ ≤ #(ZMod c)ˣ = φ(c) ≤ c`. -/
theorem norm_kloosterman_le_modulus {c : ℕ} [NeZero c] (a b : ZMod c) :
    ‖kloosterman a b‖ ≤ (c : ℝ) := by
  refine (norm_kloosterman_le a b).trans ?_
  rw [ZMod.card_units_eq_totient]
  exact_mod_cast Nat.totient_le c

/-- **(2) The `p = 2` placeholder.** `‖S(a, b; 2^k)‖ ≤ 2^k` (the crude trivial bound; the
consumers absorb the `2^{O(1)}` loss). -/
theorem norm_kloosterman_two_pow {k : ℕ} [NeZero (2 ^ k)] (a b : ZMod (2 ^ k)) :
    ‖kloosterman a b‖ ≤ (2 : ℝ) ^ k := by
  refine (norm_kloosterman_le_modulus a b).trans (le_of_eq ?_)
  push_cast
  ring

/-! ### (3) The unit-threaded factorization recursion -/

/-- The split constant of a faithful additive character is a unit: if `y ↦ ψ(l·y)` is injective
on the finite ring `ZMod n` then `l` is a non-zero-divisor, hence a unit. -/
theorem isUnit_of_stdAddChar_mul_injective {n : ℕ} [NeZero n] {l : ZMod n}
    (hinj : Function.Injective (fun y : ZMod n => ZMod.stdAddChar (l * y))) : IsUnit l := by
  have hmul : Function.Injective (fun y : ZMod n => l * y) := by
    intro y y' hyy; exact hinj (by simp only [hyy])
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hmul) 1
  exact IsUnit.of_mul_eq_one y hy

/-- **Unit-carrying character split.** Strengthens `exists_split_stdAddChar`: for coprime `c₁, c₂`
the twists `l₁, l₂` in the additive-character factorization are **units**. Each `lᵢ` is the split
constant of the faithful character `y ↦ stdAddChar (e.symm (…))`, so the injective-split lemma
applies. -/
theorem exists_split_stdAddChar_unit {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : Nat.Coprime c₁ c₂) :
    ∃ (l₁ : ZMod c₁) (l₂ : ZMod c₂), IsUnit l₁ ∧ IsUnit l₂ ∧ ∀ x : ZMod (c₁ * c₂),
      ZMod.stdAddChar (N := c₁ * c₂) x
        = ZMod.stdAddChar (l₁ * (ZMod.chineseRemainder h x).1)
          * ZMod.stdAddChar (l₂ * (ZMod.chineseRemainder h x).2) := by
  haveI : NeZero (c₁ * c₂) := ⟨mul_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  obtain ⟨l₁, l₂, hsplit⟩ := exists_split_stdAddChar h
  set e := ZMod.chineseRemainder h with he
  refine ⟨l₁, l₂, ?_, ?_, hsplit⟩
  · -- `stdAddChar (l₁ * y) = stdAddChar (e.symm (y, 0))`, a faithful character in `y`.
    have hΨ₁ : ∀ y : ZMod c₁,
        ZMod.stdAddChar (l₁ * y) = ZMod.stdAddChar (e.symm (y, 0)) := by
      intro y
      have hx := hsplit (e.symm (y, 0))
      rw [e.apply_symm_apply] at hx
      simp only at hx
      rw [mul_zero, AddChar.map_zero_eq_one, mul_one] at hx
      exact hx.symm
    refine isUnit_of_stdAddChar_mul_injective ?_
    have hfe : (fun y : ZMod c₁ => ZMod.stdAddChar (l₁ * y))
        = fun y => ZMod.stdAddChar (e.symm (y, 0)) := funext hΨ₁
    rw [hfe]
    intro y y' hyy
    exact (Prod.ext_iff.mp (e.symm.injective (ZMod.injective_stdAddChar hyy))).1
  · have hΨ₂ : ∀ z : ZMod c₂,
        ZMod.stdAddChar (l₂ * z) = ZMod.stdAddChar (e.symm (0, z)) := by
      intro z
      have hx := hsplit (e.symm (0, z))
      rw [e.apply_symm_apply] at hx
      simp only at hx
      rw [mul_zero, AddChar.map_zero_eq_one, one_mul] at hx
      exact hx.symm
    refine isUnit_of_stdAddChar_mul_injective ?_
    have hfe : (fun z : ZMod c₂ => ZMod.stdAddChar (l₂ * z))
        = fun z => ZMod.stdAddChar (e.symm (0, z)) := funext hΨ₂
    rw [hfe]
    intro z z' hzz
    exact (Prod.ext_iff.mp (e.symm.injective (ZMod.injective_stdAddChar hzz))).2

/-- **Unit-carrying twisted multiplicativity.** For coprime `c₁, c₂` and a **unit** `a`,
`S(a, b; c₁c₂) = S(A₁, B₁; c₁) · S(A₂, B₂; c₂)` with `A₁ = l₁·(e a).1`, `A₂ = l₂·(e a).2` both
units (`l₁, l₂` the unit twists of `exists_split_stdAddChar_unit`, `(e a).ᵢ` the unit CRT
projections). This is `kloosterman_mul_of_coprime` with `IsUnit` of both first arguments threaded
through — exactly what the per-prime-power Salié bound needs. -/
theorem kloosterman_mul_of_coprime_unit {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : Nat.Coprime c₁ c₂) (a b : ZMod (c₁ * c₂)) (ha : IsUnit a) :
    ∃ (l₁ : ZMod c₁) (l₂ : ZMod c₂),
      IsUnit (l₁ * (ZMod.chineseRemainder h a).1)
      ∧ IsUnit (l₂ * (ZMod.chineseRemainder h a).2)
      ∧ kloosterman a b
        = kloosterman (l₁ * (ZMod.chineseRemainder h a).1) (l₁ * (ZMod.chineseRemainder h b).1)
          * kloosterman (l₂ * (ZMod.chineseRemainder h a).2)
              (l₂ * (ZMod.chineseRemainder h b).2) := by
  haveI : NeZero (c₁ * c₂) := ⟨mul_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  obtain ⟨l₁, l₂, hu₁, hu₂, hsplit⟩ := exists_split_stdAddChar_unit h
  set e := ZMod.chineseRemainder h with he
  have hp1 : IsUnit (e a).1 :=
    (ha.map (e : ZMod (c₁ * c₂) →+* ZMod c₁ × ZMod c₂)).map (MonoidHom.fst (ZMod c₁) (ZMod c₂))
  have hp2 : IsUnit (e a).2 :=
    (ha.map (e : ZMod (c₁ * c₂) →+* ZMod c₁ × ZMod c₂)).map (MonoidHom.snd (ZMod c₁) (ZMod c₂))
  refine ⟨l₁, l₂, hu₁.mul hp1, hu₂.mul hp2, ?_⟩
  let ue : (ZMod (c₁ * c₂))ˣ ≃* (ZMod c₁)ˣ × (ZMod c₂)ˣ :=
    (Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits
  have hval1 : ∀ s : (ZMod (c₁ * c₂))ˣ,
      (e (s : ZMod (c₁ * c₂))).1 = ((ue s).1 : ZMod c₁) := by
    intro s
    rw [show ((ue s).1 : ZMod c₁)
        = ((Units.map (MonoidHom.fst (ZMod c₁) (ZMod c₂)) (Units.mapEquiv e.toMulEquiv s) :
            (ZMod c₁)ˣ) : ZMod c₁) from rfl,
      Units.coe_map, MonoidHom.coe_fst, Units.coe_mapEquiv]
    rfl
  have hval2 : ∀ s : (ZMod (c₁ * c₂))ˣ,
      (e (s : ZMod (c₁ * c₂))).2 = ((ue s).2 : ZMod c₂) := by
    intro s
    rw [show ((ue s).2 : ZMod c₂)
        = ((Units.map (MonoidHom.snd (ZMod c₁) (ZMod c₂)) (Units.mapEquiv e.toMulEquiv s) :
            (ZMod c₂)ˣ) : ZMod c₂) from rfl,
      Units.coe_map, MonoidHom.coe_snd, Units.coe_mapEquiv]
    rfl
  set A₁ := l₁ * (e a).1 with hA₁
  set B₁ := l₁ * (e b).1 with hB₁
  set A₂ := l₂ * (e a).2 with hA₂
  set B₂ := l₂ * (e b).2 with hB₂
  have hLHS : kloosterman a b
      = ∑ t : (ZMod (c₁ * c₂))ˣ,
          ZMod.stdAddChar
              (A₁ * ((ue t).1 : ZMod c₁) + B₁ * (((ue t).1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁))
            * ZMod.stdAddChar
                (A₂ * ((ue t).2 : ZMod c₂) + B₂ * (((ue t).2⁻¹ : (ZMod c₂)ˣ) : ZMod c₂)) := by
    unfold kloosterman
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have hinv1 : (e ((t⁻¹ : (ZMod (c₁ * c₂))ˣ) : ZMod (c₁ * c₂))).1
        = (((ue t).1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁) := by
      rw [hval1 t⁻¹, map_inv ue t]; rfl
    have hinv2 : (e ((t⁻¹ : (ZMod (c₁ * c₂))ˣ) : ZMod (c₁ * c₂))).2
        = (((ue t).2⁻¹ : (ZMod c₂)ˣ) : ZMod c₂) := by
      rw [hval2 t⁻¹, map_inv ue t]; rfl
    have arg1 : l₁ * (e (a * (t : ZMod (c₁ * c₂))
          + b * ((t⁻¹ : (ZMod (c₁ * c₂))ˣ) : ZMod (c₁ * c₂)))).1
        = A₁ * ((ue t).1 : ZMod c₁) + B₁ * (((ue t).1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁) := by
      rw [map_add, map_mul, map_mul, Prod.fst_add, Prod.fst_mul, Prod.fst_mul, hval1 t, hinv1,
        hA₁, hB₁]; ring
    have arg2 : l₂ * (e (a * (t : ZMod (c₁ * c₂))
          + b * ((t⁻¹ : (ZMod (c₁ * c₂))ˣ) : ZMod (c₁ * c₂)))).2
        = A₂ * ((ue t).2 : ZMod c₂) + B₂ * (((ue t).2⁻¹ : (ZMod c₂)ˣ) : ZMod c₂) := by
      rw [map_add, map_mul, map_mul, Prod.snd_add, Prod.snd_mul, Prod.snd_mul, hval2 t, hinv2,
        hA₂, hB₂]; ring
    rw [hsplit, arg1, arg2]
  rw [hLHS]
  rw [Fintype.sum_equiv ue.toEquiv
    (fun t =>
      ZMod.stdAddChar
          (A₁ * ((ue t).1 : ZMod c₁) + B₁ * (((ue t).1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁))
        * ZMod.stdAddChar
          (A₂ * ((ue t).2 : ZMod c₂) + B₂ * (((ue t).2⁻¹ : (ZMod c₂)ˣ) : ZMod c₂)))
    (fun p =>
      ZMod.stdAddChar (A₁ * (p.1 : ZMod c₁) + B₁ * ((p.1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁))
        * ZMod.stdAddChar (A₂ * (p.2 : ZMod c₂) + B₂ * ((p.2⁻¹ : (ZMod c₂)ˣ) : ZMod c₂)))
    (fun t => rfl)]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum]
  rfl

/-- **(3) The unit-threaded reduction step.** For coprime `c₁, c₂` and a **unit** `a`, bounds
`M₁, M₂` that hold merely at *unit* first arguments already control the composite:
`‖S(a, b; c₁c₂)‖ ≤ M₁·M₂`. This is the composable two-factor core of the factorization recursion —
iterate over `Nat.factorization` (coprime prime-power factors; `a` a unit keeps each CRT
projection a unit) to feed the per-prime-power Weil/Salié bounds into an arbitrary modulus. -/
theorem norm_kloosterman_le_mul_of_coprime_unit {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : Nat.Coprime c₁ c₂) (a b : ZMod (c₁ * c₂)) (ha : IsUnit a) {M₁ M₂ : ℝ} (hM₁0 : 0 ≤ M₁)
    (hM₁ : ∀ a₁ b₁ : ZMod c₁, IsUnit a₁ → ‖kloosterman a₁ b₁‖ ≤ M₁)
    (hM₂ : ∀ a₂ b₂ : ZMod c₂, IsUnit a₂ → ‖kloosterman a₂ b₂‖ ≤ M₂) :
    ‖kloosterman a b‖ ≤ M₁ * M₂ := by
  obtain ⟨l₁, l₂, hua, hub, hmul⟩ := kloosterman_mul_of_coprime_unit h a b ha
  rw [hmul, norm_mul]
  exact mul_le_mul (hM₁ _ _ hua) (hM₂ _ _ hub) (norm_nonneg _) hM₁0

end Salt.Weil
