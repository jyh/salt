/-
# The ℝ→ℂ complexification of a real Dirichlet character

Module 7 of the even-χ port (2026-08-19), executing the helm's **ℝ-UP** ruling.

## The direction, and why it is not arbitrary

The ladder's ANALYTIC half (E3's Fourier identity, Gauss sums, `LFunction`) is stated at
`DirichletCharacter ℂ`; its ARITHMETIC half (the `ℤ` sign map, the fibre swap) is stated at
`DirichletCharacter ℝ`.  Nothing joined them.  Pushing the ℝ side UP is constructive and
cheap — `MulChar.ringHomComp`; pulling the ℂ side DOWN would need an INVERSE of
`ringHomComp`, and although a ℂ-valued quadratic χ does take values in `{0,±1} ⊆ ℝ`,
exhibiting its real avatar is work, not a coercion.

## Main results

* `e4a_toC` — the complexification, and `e4a_toC_eq_signOf`: **at a unit the complexified
  value IS the integer sign map**, which is what turns a ℂ-coefficient character sum into an
  ℤ-coefficient one.
* `e4a_toC_isQuadratic` / `_even` / `_ne_one` — the hypotheses transport.
* `e4a_sum_units_of_vanishing` / `e4a_toC_sum_eq_signOf_sum` — a unit-supported sum over
  `ZMod q` IS a sum over the units, with integer weights.
* `e4a_toC_isPrimitive_iff` — **PRIMITIVITY TRANSPORTS, both ways, and it collapses to ONE
  observation: the KERNELS ARE EQUAL.**  `ofReal` is injective and sends `1` to `1`, and
  mathlib characterises `FactorsThrough` purely by a kernel containment
  (`factorsThrough_iff_ker_unitsMap`) — so conductor sets, conductors and `IsPrimitive` are
  all bookkeeping on that single fact.  *Priced as a conductor argument, it is an `sInf` over
  levels; stated through the kernel, the conductor is never computed at all.*
-/
import Salt.MR.EvenChiSign

namespace Salt.MR

/-- **The complexification of a real Dirichlet character.** -/
noncomputable def e4a_toC {q : ℕ} (χ : DirichletCharacter ℝ q) : DirichletCharacter ℂ q :=
  χ.ringHomComp Complex.ofRealHom

@[simp] theorem e4a_toC_apply {q : ℕ} (χ : DirichletCharacter ℝ q) (a : ZMod q) :
    e4a_toC χ a = ((χ a : ℝ) : ℂ) := rfl

/-- Quadraticity transports — straight off mathlib's `IsQuadratic.comp`. -/
theorem e4a_toC_isQuadratic {q : ℕ} {χ : DirichletCharacter ℝ q} (hχ : χ.IsQuadratic) :
    (e4a_toC χ).IsQuadratic := hχ.comp _

/-- Evenness transports: a ring hom sends `1` to `1`. -/
theorem e4a_toC_even {q : ℕ} {χ : DirichletCharacter ℝ q} (hev : χ (-1) = 1) :
    (e4a_toC χ) (-1) = 1 := by
  rw [e4a_toC_apply, hev, Complex.ofReal_one]

/-- Non-principality transports, because `ofReal` is injective. -/
theorem e4a_toC_ne_one {q : ℕ} {χ : DirichletCharacter ℝ q} (hχ : χ ≠ 1) :
    e4a_toC χ ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff Complex.ofReal_injective).mpr hχ

/-- ⭐ **THE COEFFICIENT BRIDGE — THE PAYLOAD.**  At a unit, the complexified character's
value IS the integer sign map, cast to `ℂ`.  This is what turns the ℂ-coefficient sum of
E3's Fourier identity into the ℤ-coefficient sum that `e4a_sum_clog_re` consumes. -/
theorem e4a_toC_eq_signOf {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) (a : (ZMod q)ˣ) :
    e4a_toC χ (a : ZMod q) = ((E4aChiBridge.e4a_signOf χ a : ℤ) : ℂ) := by
  rw [e4a_toC_apply, ← E4aChiBridge.e4a_signOf_cast' χ a]
  push_cast
  ring

/-- ⭐ **THE SUM COLLAPSE** — a character-weighted sum over ALL of `ZMod q` is a sum over
the UNITS, because the character vanishes off them.  Stated for an arbitrary unit-supported
weight so it is reusable and says nothing about η. -/
theorem e4a_sum_units_of_vanishing {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M]
    (g : ZMod q → M) (hg : ∀ j : ZMod q, ¬ IsUnit j → g j = 0) :
    ∑ j : ZMod q, g j = ∑ a : (ZMod q)ˣ, g (a : ZMod q) := by
  classical
  have hsub : (Finset.univ.image (fun a : (ZMod q)ˣ => (a : ZMod q))) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hoff : ∀ x ∈ Finset.univ,
      x ∉ (Finset.univ.image (fun a : (ZMod q)ˣ => (a : ZMod q))) → g x = 0 := by
    intro x _ hx
    refine hg x ?_
    intro hu
    exact hx (Finset.mem_image.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩)
  rw [← Finset.sum_subset hsub hoff]
  exact Finset.sum_image (fun a _ b _ h => Units.ext h)

/-- ⭐ **THE TWO JOINED** — the ℂ-valued character sum over `ZMod q` IS an ℤ-coefficient
sum over the units.  This is exactly the shape `e4a_sum_clog_re` takes. -/
theorem e4a_toC_sum_eq_signOf_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    (f : ZMod q → ℂ) :
    ∑ j : ZMod q, e4a_toC χ j * f j
      = ∑ a : (ZMod q)ˣ, ((E4aChiBridge.e4a_signOf χ a : ℤ) : ℂ) * f (a : ZMod q) := by
  rw [e4a_sum_units_of_vanishing (fun j => e4a_toC χ j * f j) ?_]
  · exact Finset.sum_congr rfl fun a _ => by rw [e4a_toC_eq_signOf]
  · intro j hj
    rw [e4a_toC_apply, MulChar.map_nonunit χ hj, Complex.ofReal_zero, zero_mul]

/-! ### MUTATION CONTROL — the restriction to units is LOAD-BEARING, not decorative.

The mutant drops `IsUnit` from the coefficient bridge and claims the sign map's two values
everywhere.  It is FALSE, not merely unreachable: off the units the complexified value is
`0`, and `0` is neither `1` nor `-1`. -/

/-- The complexification has the SAME unit-hom kernel: `ofReal` is injective. -/
theorem e4a_toC_toUnitHom_ker {q : ℕ} (χ : DirichletCharacter ℝ q) :
    (e4a_toC χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker]
  rw [← Units.val_eq_one, ← Units.val_eq_one, MulChar.coe_toUnitHom, MulChar.coe_toUnitHom,
    e4a_toC_apply, Complex.ofReal_eq_one]

/-- Factoring through a level is preserved and reflected. -/
theorem e4a_toC_factorsThrough_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    {d : ℕ} (hd : d ∣ q) :
    (e4a_toC χ).FactorsThrough d ↔ χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, e4a_toC_toUnitHom_ker]

/-- Hence the conductor SETS coincide. -/
theorem e4a_toC_conductorSet_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    (e4a_toC χ).conductorSet = χ.conductorSet := by
  ext d
  constructor
  · intro hd
    exact (e4a_toC_factorsThrough_iff χ (DirichletCharacter.FactorsThrough.dvd hd)).mp hd
  · intro hd
    exact (e4a_toC_factorsThrough_iff χ (DirichletCharacter.FactorsThrough.dvd hd)).mpr hd

/-- Hence the conductors are equal. -/
theorem e4a_toC_conductor_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    (e4a_toC χ).conductor = χ.conductor := by
  unfold DirichletCharacter.conductor
  rw [e4a_toC_conductorSet_eq]

/-- ⭐ **PRIMITIVITY TRANSPORTS, BOTH WAYS.** -/
theorem e4a_toC_isPrimitive_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    (e4a_toC χ).IsPrimitive ↔ χ.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive
  rw [e4a_toC_conductor_eq]

/-- The direction the assembly needs: a primitive REAL character complexifies to a
primitive one, so `e4a_fourier_signOf_form` can be fed from the real side. -/
theorem e4a_toC_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℝ q}
    (hprim : χ.IsPrimitive) : (e4a_toC χ).IsPrimitive :=
  (e4a_toC_isPrimitive_iff χ).mpr hprim

end Salt.MR
