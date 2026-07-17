/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Kloosterman
import Mathlib

/-!
# Weil track, W6.1 — composite Kloosterman multiplicativity

The **twisted multiplicativity** of Kloosterman sums (Iwaniec–Kowalski (1.59)): for
coprime moduli `c₁, c₂` the sum `S(a, b; c₁c₂)` factors as a product of a `c₁`-sum and a
`c₂`-sum, each with the arguments twisted by the Bézout inverse of the other modulus. This
is the "consumer tail" rung: it reduces `‖S(a, b; c)‖` over an arbitrary modulus to the
prime-power case, where a future node supplies the Weil / Salié bound `‖S‖ ≤ 2 √(p^k)`.

The derivation is intrinsic to the CRT reindex rather than pinned to explicit idempotents:

* **`exists_mulShift_stdAddChar`** — every complex-valued additive character of `ZMod n`
  equals `stdAddChar.mulShift l` for some `l`. Injectivity of `l ↦ stdAddChar.mulShift l`
  (primitivity of `stdAddChar`, `AddChar.to_mulShift_inj_of_isPrimitive`) plus the Pontryagin
  count `#(AddChar (ZMod n) ℂ) = #(ZMod n)` (`AddChar.card_eq`) forces surjectivity.

* **`exists_split_stdAddChar`** — the character split. Under the CRT ring iso
  `e = ZMod.chineseRemainder h`, the standard character factors as
  `stdAddChar x = stdAddChar (l₁ · (e x).1) · stdAddChar (l₂ · (e x).2)`, where `l₁, l₂` are
  the mulShift constants of the two restricted characters `y ↦ stdAddChar (e.symm (y, 0))`
  and `z ↦ stdAddChar (e.symm (0, z))`. The proof writes `x = e.symm (e x).1‑part +
  e.symm (e x).2‑part` and uses additivity of `stdAddChar`.

* **`kloosterman_mul_of_coprime`** — the multiplicativity itself. Reindexing the unit sum
  through `(ZMod (c₁c₂))ˣ ≃* (ZMod c₁)ˣ × (ZMod c₂)ˣ` (`Units.mapEquiv e` composed with
  `MulEquiv.prodUnits`) and applying the character split summand-by-summand yields
  `S(a, b; c₁c₂) = S(l₁·a₁, l₁·b₁; c₁) · S(l₂·a₂, l₂·b₂; c₂)`, with `aᵢ = (e a)ᵢ`, `bᵢ = (e b)ᵢ`
  the CRT projections and `l₁, l₂` the (existential) unit twists — the honest form of the
  Bézout inverses `c̄₂, c̄₁`.

* **`norm_kloosterman_mul_of_coprime`** / **`norm_kloosterman_le_mul_of_coprime`** — the norm
  factorisation `‖S(a,b;c₁c₂)‖ = ‖S(a₁,b₁;c₁)‖·‖S(a₂,b₂;c₂)‖` and the reduction step: uniform
  bounds `M₁, M₂` on the two factor moduli give `‖S(a,b;c₁c₂)‖ ≤ M₁·M₂`. Iterating this over
  `Nat.factorization` is the future node that plugs in the per-prime-power Weil bounds.
-/

namespace Salt.Weil

open scoped BigOperators

/-- **Character representation.** Every complex-valued additive character of `ZMod n` is
`stdAddChar.mulShift l` for some `l : ZMod n`. The map `l ↦ stdAddChar.mulShift l` is injective
by primitivity of `stdAddChar`, and `#(AddChar (ZMod n) ℂ) = #(ZMod n)`, so it is bijective. -/
theorem exists_mulShift_stdAddChar {n : ℕ} [NeZero n] (χ : AddChar (ZMod n) ℂ) :
    ∃ l : ZMod n, χ = (ZMod.stdAddChar (N := n)).mulShift l := by
  have hbij : Function.Bijective
      (fun a : ZMod n => (ZMod.stdAddChar (N := n)).mulShift a) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨AddChar.to_mulShift_inj_of_isPrimitive (ZMod.isPrimitive_stdAddChar n),
      AddChar.card_eq.symm⟩
  obtain ⟨l, hl⟩ := hbij.surjective χ
  exact ⟨l, hl.symm⟩

/-- **Character split.** For coprime `c₁, c₂`, writing `e = ZMod.chineseRemainder h`, there exist
twists `l₁ : ZMod c₁`, `l₂ : ZMod c₂` with
`stdAddChar x = stdAddChar (l₁ · (e x).1) · stdAddChar (l₂ · (e x).2)` for all `x`. The `lᵢ` are
the mulShift constants of the restricted characters `stdAddChar ∘ (e.symm ∘ inlᵢ)`. -/
theorem exists_split_stdAddChar {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : Nat.Coprime c₁ c₂) :
    ∃ (l₁ : ZMod c₁) (l₂ : ZMod c₂), ∀ x : ZMod (c₁ * c₂),
      ZMod.stdAddChar (N := c₁ * c₂) x
        = ZMod.stdAddChar (l₁ * (ZMod.chineseRemainder h x).1)
          * ZMod.stdAddChar (l₂ * (ZMod.chineseRemainder h x).2) := by
  haveI : NeZero (c₁ * c₂) := ⟨mul_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  set e := ZMod.chineseRemainder h with he
  let φ₁ : ZMod c₁ →+ ZMod (c₁ * c₂) :=
    { toFun := fun y => e.symm (y, 0)
      map_zero' := by simp
      map_add' := fun y y' => by rw [← map_add]; congr 1; ext <;> simp }
  let φ₂ : ZMod c₂ →+ ZMod (c₁ * c₂) :=
    { toFun := fun z => e.symm (0, z)
      map_zero' := by simp
      map_add' := fun z z' => by rw [← map_add]; congr 1; ext <;> simp }
  let Ψ₁ : AddChar (ZMod c₁) ℂ := ZMod.stdAddChar.compAddMonoidHom φ₁
  let Ψ₂ : AddChar (ZMod c₂) ℂ := ZMod.stdAddChar.compAddMonoidHom φ₂
  obtain ⟨l₁, hl₁⟩ := exists_mulShift_stdAddChar Ψ₁
  obtain ⟨l₂, hl₂⟩ := exists_mulShift_stdAddChar Ψ₂
  refine ⟨l₁, l₂, fun x => ?_⟩
  have key : x = e.symm ((e x).1, 0) + e.symm ((0 : ZMod c₁), (e x).2) := by
    rw [← map_add,
      show (((e x).1, (0 : ZMod c₂)) + ((0 : ZMod c₁), (e x).2)) = e x from by ext <;> simp,
      e.symm_apply_apply]
  calc ZMod.stdAddChar (N := c₁ * c₂) x
      = ZMod.stdAddChar (e.symm ((e x).1, 0) + e.symm ((0 : ZMod c₁), (e x).2)) := by
          conv_lhs => rw [key]
    _ = ZMod.stdAddChar (e.symm ((e x).1, 0)) * ZMod.stdAddChar (e.symm ((0 : ZMod c₁), (e x).2)) :=
          AddChar.map_add_eq_mul _ _ _
    _ = Ψ₁ (e x).1 * Ψ₂ (e x).2 := rfl
    _ = (ZMod.stdAddChar.mulShift l₁) (e x).1 * (ZMod.stdAddChar.mulShift l₂) (e x).2 := by
          rw [hl₁, hl₂]
    _ = ZMod.stdAddChar (l₁ * (e x).1) * ZMod.stdAddChar (l₂ * (e x).2) := by
          rw [AddChar.mulShift_apply, AddChar.mulShift_apply]

/-- **Twisted multiplicativity (Iwaniec–Kowalski (1.59)).** For coprime `c₁, c₂`,
`S(a, b; c₁c₂) = S(l₁·a₁, l₁·b₁; c₁) · S(l₂·a₂, l₂·b₂; c₂)`, where `a₁ = (e a).1`, `b₁ = (e b).1`
(resp. `.2`) are the CRT projections of `a, b` and `l₁ : ZMod c₁`, `l₂ : ZMod c₂` are the unit
twists (the Bézout inverses `c̄₂, c̄₁`, existentially quantified). Proof: reindex the unit sum via
`(ZMod (c₁c₂))ˣ ≃* (ZMod c₁)ˣ × (ZMod c₂)ˣ` and apply `exists_split_stdAddChar` termwise. -/
theorem kloosterman_mul_of_coprime {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : Nat.Coprime c₁ c₂) (a b : ZMod (c₁ * c₂)) :
    ∃ (l₁ : ZMod c₁) (l₂ : ZMod c₂),
      kloosterman a b
        = kloosterman (l₁ * (ZMod.chineseRemainder h a).1) (l₁ * (ZMod.chineseRemainder h b).1)
          * kloosterman (l₂ * (ZMod.chineseRemainder h a).2)
              (l₂ * (ZMod.chineseRemainder h b).2) := by
  haveI : NeZero (c₁ * c₂) := ⟨mul_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  obtain ⟨l₁, l₂, hsplit⟩ := exists_split_stdAddChar h
  refine ⟨l₁, l₂, ?_⟩
  set e := ZMod.chineseRemainder h with he
  let ue : (ZMod (c₁ * c₂))ˣ ≃* (ZMod c₁)ˣ × (ZMod c₂)ˣ :=
    (Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits
  have hval1 : ∀ s : (ZMod (c₁ * c₂))ˣ, (e (s : ZMod (c₁ * c₂))).1 = ((ue s).1 : ZMod c₁) := by
    intro s
    rw [show ((ue s).1 : ZMod c₁)
        = ((Units.map (MonoidHom.fst (ZMod c₁) (ZMod c₂)) (Units.mapEquiv e.toMulEquiv s) :
            (ZMod c₁)ˣ) : ZMod c₁) from rfl,
      Units.coe_map, MonoidHom.coe_fst, Units.coe_mapEquiv]
    rfl
  have hval2 : ∀ s : (ZMod (c₁ * c₂))ˣ, (e (s : ZMod (c₁ * c₂))).2 = ((ue s).2 : ZMod c₂) := by
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
          ZMod.stdAddChar (A₁ * ((ue t).1 : ZMod c₁) + B₁ * (((ue t).1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁))
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
      ZMod.stdAddChar (A₁ * ((ue t).1 : ZMod c₁) + B₁ * (((ue t).1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁))
        * ZMod.stdAddChar (A₂ * ((ue t).2 : ZMod c₂) + B₂ * (((ue t).2⁻¹ : (ZMod c₂)ˣ) : ZMod c₂)))
    (fun p => ZMod.stdAddChar (A₁ * (p.1 : ZMod c₁) + B₁ * ((p.1⁻¹ : (ZMod c₁)ˣ) : ZMod c₁))
        * ZMod.stdAddChar (A₂ * (p.2 : ZMod c₂) + B₂ * ((p.2⁻¹ : (ZMod c₂)ˣ) : ZMod c₂)))
    (fun t => rfl)]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum]
  rfl

/-- **Norm multiplicativity.** The absolute value of a composite Kloosterman sum factors over
coprime moduli: `‖S(a,b;c₁c₂)‖ = ‖S(a₁,b₁;c₁)‖ · ‖S(a₂,b₂;c₂)‖` for suitable twisted arguments.
Direct consequence of `kloosterman_mul_of_coprime` and `norm_mul`. -/
theorem norm_kloosterman_mul_of_coprime {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : Nat.Coprime c₁ c₂) (a b : ZMod (c₁ * c₂)) :
    ∃ (a₁ b₁ : ZMod c₁) (a₂ b₂ : ZMod c₂),
      ‖kloosterman a b‖ = ‖kloosterman a₁ b₁‖ * ‖kloosterman a₂ b₂‖ := by
  obtain ⟨l₁, l₂, hmul⟩ := kloosterman_mul_of_coprime h a b
  exact ⟨_, _, _, _, by rw [hmul, norm_mul]⟩

/-- **Reduction step.** Given uniform bounds `M₁, M₂` on the Kloosterman norms at the two coprime
factor moduli, the composite norm obeys `‖S(a,b;c₁c₂)‖ ≤ M₁ · M₂`. Iterating this over the prime
powers in `Nat.factorization` (each pair of prime-power factors is coprime) is the future node
that assembles the global bound `‖S(a,b;c)‖ ≤ ∏_{p^k ∥ c} ‖bound‖` from per-prime-power Weil
estimates. -/
theorem norm_kloosterman_le_mul_of_coprime {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (h : Nat.Coprime c₁ c₂) (a b : ZMod (c₁ * c₂)) {M₁ M₂ : ℝ}
    (hM₁ : ∀ a₁ b₁ : ZMod c₁, ‖kloosterman a₁ b₁‖ ≤ M₁) (hM₁0 : 0 ≤ M₁)
    (hM₂ : ∀ a₂ b₂ : ZMod c₂, ‖kloosterman a₂ b₂‖ ≤ M₂) :
    ‖kloosterman a b‖ ≤ M₁ * M₂ := by
  obtain ⟨a₁, b₁, a₂, b₂, hnorm⟩ := norm_kloosterman_mul_of_coprime h a b
  rw [hnorm]
  exact mul_le_mul (hM₁ a₁ b₁) (hM₂ a₂ b₂) (norm_nonneg _) hM₁0

end Salt.Weil
