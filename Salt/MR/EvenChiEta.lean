/-
# η in `𝓞_K`, and the ground: `L(1,χ) ≥ 2·log φ / √q`

The final module of the even-χ port (2026-08-19).  **This is the one that terminates at the
objective**, and it is a single dependency chain: `e4aK → e4aZetaO → e4aEta →
e4a_eta_sum_integer_final → exists_int_add_inv_sin_prod → e4a_L1_lower_even`.  Guide rows
3b, 5 and 9 are not separable deliverables; they are this file.

⚠️ **FIVE OF THESE DECLARATIONS ARE INVISIBLE TO A TEXTUAL DEPENDENCY SCAN.**
`e4aK_cyclotomic`, `e4aK_numberField`, `e4a_route_b_isCyclotomicExtension`,
`e4a_ringOfIntegers_isIntegral` and `e4a_zeta_isAlgebraic` are reached by TYPECLASS
INSTANCE RESOLUTION, not by name, so no scan over proof text can find them.  They are here
because the port's cone measurement was labelled a LOWER BOUND from the start, for exactly
this reason.

## The two results

* `exists_int_add_inv_sin_prod` — **the Captain-ratified statement**: for an even real
  primitive χ mod q with `∑χ = 0`, the sine product `∏ (2 sin(πa/q))^{e a}` and its inverse
  sum to an INTEGER.
* `e4a_L1_lower_even` — **the ground**: `L(1,χ) ≥ log((3+√5)/2) / √q = 2·log φ / √q`.

## Why the integer exists at all

η is a ratio of cyclotomic units, so it is a unit of `𝓞_K`; it is fixed by every Galois
automorphism up to inversion (`e4a_eta_gal`), so `η + η⁻¹` is rational AND integral, hence an
integer.  `e4a_card_eq_of_sum_zero` (in `EvenChiAlgebra`) is what makes the two fibres equal
in size, which is what cancels the signs in that ratio — and it is exactly the R1 amendment
`∑χ = 0` doing the work, which is why that hypothesis is IN the ruled statement.
-/
import Salt.MR.EvenChiAlgebra
import Salt.MR.EvenChiCosh
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

namespace Salt.MR

open IsPrimitiveRoot
open scoped ComplexOrder

section

variable {q a : ℕ}

/-- `ζ_q ^ q = 1`. -/
theorem e4a_zeta_pow_q (hq : 0 < q) :
    (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ q = 1 := by
  rw [← Complex.exp_nat_mul]
  have hqR : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have : (q : ℂ) * (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast; field_simp
  rw [this]
  simp

end


theorem e4a_zeta_isAlgebraic {q : ℕ} (hq : 0 < q) :
    IsAlgebraic ℚ (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) := by
  refine ⟨Polynomial.X ^ q - Polynomial.C 1, ?_, ?_⟩
  · intro h
    have hd : (Polynomial.X ^ q - Polynomial.C 1 : Polynomial ℚ).natDegree = q :=
      Polynomial.natDegree_X_pow_sub_C
    rw [h] at hd
    simp at hd
    omega
  · have h := e4a_zeta_pow_q (q := q) hq
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero]
    exact h

/-- **THE PREAMBLE** — `ℚ⟮ζ⟯` is a cyclotomic extension of `ℚ` of order `q`. -/
theorem e4a_route_b_isCyclotomicExtension {q : ℕ} [NeZero q] :
    IsCyclotomicExtension {q} ℚ
      (IntermediateField.adjoin ℚ
        ({Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)} : Set ℂ)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hζ := e4a_zeta_isPrimitiveRoot (q := q) hq
  change IsCyclotomicExtension {q} ℚ
    (IntermediateField.adjoin ℚ
      ({Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)} : Set ℂ)).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (e4a_zeta_isAlgebraic hq)]
  exact hζ.adjoin_isCyclotomicExtension ℚ

#print axioms e4a_zeta_isAlgebraic
#print axioms e4a_route_b_isCyclotomicExtension

/-! ## PROBE 18 — THE RING/FIELD JOIN

With the preamble, `K := ℚ⟮ζ⟯` is a cyclotomic extension, hence a `NumberField`, hence has
a ring of integers `𝓞 K` where UNIT-NESS IS NON-VACUOUS.  Carrying ζ there closes the gap
I named at tick 6: probes 1/2/4/14 are stated for any `CommRing`+`IsDomain`, so they apply
verbatim in `𝓞 K` once ζ is a primitive root THERE. -/

noncomputable abbrev e4aK (q : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({e4aZeta q} : Set ℂ)

instance e4aK_cyclotomic (q : ℕ) [NeZero q] : IsCyclotomicExtension {q} ℚ (e4aK q) :=
  e4a_route_b_isCyclotomicExtension

instance e4aK_numberField (q : ℕ) [NeZero q] : NumberField (e4aK q) :=
  IsCyclotomicExtension.numberField {q} ℚ _

/-- ζ, as an element of `K`. -/
noncomputable def e4aZetaK (q : ℕ) : e4aK q :=
  ⟨e4aZeta q, IntermediateField.subset_adjoin ℚ _ rfl⟩

theorem e4aZetaK_isPrimitiveRoot {q : ℕ} [NeZero q] :
    IsPrimitiveRoot (e4aZetaK q) q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine IsPrimitiveRoot.of_map_of_injective (f := (algebraMap (e4aK q) ℂ)) ?_ ?_
  · exact e4a_zeta_isPrimitiveRoot hq
  · exact (algebraMap (e4aK q) ℂ).injective

/-- ζ, as an algebraic INTEGER of `K`. -/
noncomputable def e4aZetaO (q : ℕ) [NeZero q] : NumberField.RingOfIntegers (e4aK q) :=
  (e4aZetaK_isPrimitiveRoot (q := q)).toInteger

theorem e4aZetaO_isPrimitiveRoot {q : ℕ} [NeZero q] :
    IsPrimitiveRoot (e4aZetaO q) q :=
  (e4aZetaK_isPrimitiveRoot (q := q)).toInteger_isPrimitiveRoot

section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]

/-- And the unit form: an element of `𝓞 K` and its inverse-in-`𝓞 K` both being integral is
exactly what a unit of the ring of integers gives. -/
theorem e4a_ringOfIntegers_isIntegral {K : Type*} [Field K] [NumberField K]
    (y : NumberField.RingOfIntegers K) :
    IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K y) :=
  NumberField.RingOfIntegers.isIntegral_coe y

#print axioms e4a_sum_isIntegral_of_both
#print axioms e4a_spine
#print axioms e4a_ringOfIntegers_isIntegral

/-! ## PROBE 31 — THE χ BRIDGE, grafted from the helm's executor, and JOINTLY VERIFIED

⭐⭐ IT DELETED A HYPOTHESIS FROM MY SPINE.  My brief instructed that "χ real" be carried
as a hypothesis, on the ground that mathlib has no `IsReal` for `DirichletCharacter ℝ`.
That was accurate about the NAME and WRONG ON THE SUBSTANCE: at `[NeZero q]` the unit group
is FINITE, so χ's values on units are torsion in `ℝˣ`, and the only roots of unity in a
linearly ordered ring are `±1`.  The rider is FREE, not assumed.

⛔ AND THE MISS IS THE SHAPE I ALREADY BANKED TODAY: mathlib's name for my predicate is
`MulChar.IsQuadratic`, and **salt itself already consumes it** — measured just now, 14
occurrences across 8 files (`HB/RealPrimStructure.lean:64`, `SW/DHDetector.lean:91`, …),
with `Salt.HB.isQuadratic_of_int` as the ℤ-valued precedent I had walked past.  I searched
for `IsReal`, hedged the claim to "that I found", and the hedge was true while the search
was aimed at the wrong name.  Same failure as `cyclotomicUnit` this morning, twelve hours
apart, in the same file.

The executor's own interface control used `example`s with my lemmas TRANSCRIBED as
hypotheses.  That is a proxy.  The real test is below: the ACTUAL lemmas, applied. -/

/-! ## The definition

`e4a_signOf χ a = if χ a = 1 then 1 else -1`.

**Why the decidable test and not `Real.sign`.**  Two reasons, both about `_mul`:

1. `Real.sign` is a THREE-valued object (`-1/0/1`) whose multiplicativity is not a
   `simp` lemma in mathlib and would have to be proved by a nine-way case split.
   The two-valued test collapses that to a cast argument: `_mul` and `_one` are
   proved by pushing `Int.cast` and using `map_mul`/`map_one` on the underlying
   `MulChar`, never touching the `if` at all.
2. `Real.sign` would make `_cast` FALSE at a non-unit (`Real.sign 0 = 0` casts to
   `0 = χ a` correctly, but the domain here is `(ZMod q)ˣ` where the value is never
   `0`, so the third branch is dead weight).  The test makes `e4a_signOf` total on
   units with the `0` case impossible — which is exactly the fibre lemmas' setting.

The price is that `_cast` needs the "χ real" hypothesis (the `else` branch has to be
identified with `-1`, which is only true because the value set is `{1,-1}` on units).
`_mul` inherits that need through `_cast`.  `_one` needs nothing.
-/

theorem e4a_sigma_to_b {q : ℕ} [NeZero q] (σ : e4aK q ≃ₐ[ℚ] e4aK q) :
    ∃ b : (ZMod q)ˣ, σ (e4aZetaK q) = (e4aZetaK q) ^ ((b : ZMod q)).val :=
  ⟨IsCyclotomicExtension.Rat.galEquivZMod q (e4aK q) σ,
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq q (e4aK q) σ
      (e4aZetaK_isPrimitiveRoot (q := q)).pow_eq_one⟩

/-! ### PROBE 34 — the bridge lemmas, GENERALISED off ℂ

Math's `e4a_zeta_pow_mod` / `e4a_zeta_pow_val_mul` are stated at the CONCRETE complex ζ.
The spine acts on `K = ℚ⟮ζ⟯`, so the same two facts are needed there.  Rather than restate
them at `e4aZetaK`, they are proved once for an arbitrary monoid element with `ζ ^ q = 1`
— the ℂ versions are then the special case, and nothing is q-specific. -/

theorem e4a_sigma_prod_reindex {q : ℕ} [NeZero q] (σ : e4aK q ≃ₐ[ℚ] e4aK q)
    {b : (ZMod q)ˣ} (hb : σ (e4aZetaK q) = (e4aZetaK q) ^ ((b : ZMod q)).val)
    (S : Finset (ZMod q)ˣ) :
    σ (∏ a ∈ S, ((e4aZetaK q) ^ ((a : ZMod q)).val - 1))
      = ∏ a ∈ S, ((e4aZetaK q) ^ (((a * b : (ZMod q)ˣ) : ZMod q)).val - 1) := by
  have hζq : (e4aZetaK q) ^ q = 1 := (e4aZetaK_isPrimitiveRoot (q := q)).pow_eq_one
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_sub, map_pow, map_one, hb, ← pow_mul, Units.val_mul, e4a_pow_val_mul_gen hζq,
    Nat.mul_comm ((b : ZMod q)).val ((a : ZMod q)).val]

/-! ### PROBE 36 — ⛔ GAP 6, FOUND WHILE WIRING THE FIX ARM

The mirror of math's own probe-26 finding, one arm over.  Probe 24/25 prove the `χ(b) = +1`
case for the `+1` FIBRE (`e4a_fibre_fix`, `e4a_prod_fibre_fix`); probe 26 proves both
directions for `χ(b) = −1` (`e4a_fibre_swap`, `e4a_fibre_swap'`) and concludes
`e4a_eta_inverts`.  **There is no `e4a_fibre_fix'`** — the `−1` fibre at `χ(b) = +1` — and
consequently no `e4a_eta_fixed`.  So the FIX arm's quotient was never established: probe 25
fixes the numerator and says nothing about the denominator.

Same shape as GAP 4/5: a green half whose partner nobody stated.  Repaired here, in math's
own style, because the `hgal` disjunction needs BOTH arms. -/

noncomputable def e4aEta {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) : e4aK q :=
  (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1),
      ((e4aZetaK q) ^ ((a : ZMod q)).val - 1))
    / (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
      ((e4aZetaK q) ^ ((a : ZMod q)).val - 1))

theorem e4aEta_def {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    e4aEta χ =
      (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1),
          ((e4aZetaK q) ^ ((a : ZMod q)).val - 1))
        / (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
          ((e4aZetaK q) ^ ((a : ZMod q)).val - 1)) := rfl

/-- ⭐⭐ **GAP 4 CLOSED** — `hgal`, for the real η, at every element of `Gal(K/ℚ)`.
`σ` is turned into a `b : (ZMod q)ˣ` by probe 33, the `b` is pushed through η's two products
by probe 35, and the fibre apparatus then fixes or inverts according to `χ(b)`. -/
theorem e4a_eta_gal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    (σ : e4aK q ≃ₐ[ℚ] e4aK q) :
    σ (e4aEta χ) = e4aEta χ ∨ σ (e4aEta χ) = (e4aEta χ)⁻¹ := by
  obtain ⟨b, hb⟩ := e4a_sigma_to_b (q := q) σ
  have hnum := e4a_sigma_prod_reindex σ hb
      (Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1))
  have hden := e4a_sigma_prod_reindex σ hb
      (Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1))
  have hsplit : σ (e4aEta χ)
      = (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1),
            ((e4aZetaK q) ^ (((a * b : (ZMod q)ˣ) : ZMod q)).val - 1))
        / (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
            ((e4aZetaK q) ^ (((a * b : (ZMod q)ˣ) : ZMod q)).val - 1)) := by
    rw [e4aEta_def, map_div₀, hnum, hden]
  rcases E4aChiBridge.e4a_signOf_eq_one_or_neg_one χ b with hbχ | hbχ
  · left
    rw [hsplit, e4aEta_def]
    exact e4a_eta_fixed (E4aChiBridge.e4a_signOf χ) (E4aChiBridge.e4a_signOf_mul' χ)
      (E4aChiBridge.e4a_signOf_one χ) b hbχ
      (fun a => (e4aZetaK q) ^ ((a : ZMod q)).val - 1)
  · right
    rw [hsplit, e4aEta_def]
    exact e4a_eta_inverts (E4aChiBridge.e4a_signOf χ) (E4aChiBridge.e4a_signOf_mul' χ)
      (E4aChiBridge.e4a_signOf_one χ) b hbχ
      (fun a => (e4aZetaK q) ^ ((a : ZMod q)).val - 1)

/-! ### PROBE 38 — THE INTERFACE CONTROL: `e4a_spine` APPLIED, `hgal` DISCHARGED BY PROBE 37

Not a transcription — math's OWN `e4a_spine` (line ~1021 above), instantiated at
`K = ℚ⟮ζ⟯` and at the real η, with `hgal` supplied by `e4a_eta_gal`.  Only the two
integrality hypotheses remain open, and those are the unit-ness leg's job (probes 14/18/30),
not the link's. -/

theorem e4a_eta_sum_is_integer_concrete {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    (hx : IsIntegral ℤ (e4aEta χ)) (hxinv : IsIntegral ℤ (e4aEta χ)⁻¹) :
    ∃ z : ℤ, algebraMap ℤ (e4aK q) z = e4aEta χ + (e4aEta χ)⁻¹ := by
  haveI : IsGalois ℚ (e4aK q) := IsCyclotomicExtension.isGalois {q} ℚ _
  exact e4a_spine (e4aEta χ) hx hxinv (fun σ => e4a_eta_gal χ σ)

/-! ### PROBE 39 — NON-DEGENERACY CERTIFICATE

⚠️ At `χ = 1` the `−1` fibre is EMPTY, η is a bare product over the whole unit group, and
both arms of `e4a_eta_gal` collapse to the fix arm — the swap arm is never exercised.  A
demonstration that did not say which χ it meant would be that degenerate one.

At `χ ≠ 1` neither fibre is empty: the `+1` fibre contains `1` outright, and the `−1` fibre
has the SAME cardinality by math's own `e4a_dirichlet_card_eq` fed by `e4a_signOf_sum_eq_zero`
(probe 32's repair).  So the index chosen for the interface control is non-degenerate exactly
when χ is non-principal — which is the only case E4a is stated for. -/

/-- ⭐ **GAP 3 CLOSED** — if the two fibre products are `Associated` in `𝓞 K`, then η (their
quotient in `K`) and `η⁻¹` are BOTH integral over ℤ, which is exactly the pair of
hypotheses `e4a_spine` carries. -/
theorem e4a_eta_isIntegral_of_associated {K : Type*} [Field K] [NumberField K]
    {x y : NumberField.RingOfIntegers K} (hx : x ≠ 0)
    (h : Associated x y) :
    ∃ u : (NumberField.RingOfIntegers K)ˣ,
      (algebraMap _ K y) / (algebraMap _ K x)
        = algebraMap (NumberField.RingOfIntegers K) K (u : NumberField.RingOfIntegers K) :=
  e4a_associated_quotient_eq
    (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers K) K) hx h

/-- ⭐ **THE UNITS-INDEXED ASSOCIATE RELATION** — the ninth interface fully closed.
`ZMod.val_coe_unit_coprime` (`Data/ZMod/Basic.lean:798`) supplies the coprimality for every
unit outright, so the generic chain instantiates at η's own index with no side condition
beyond `χ ≠ 1` (which `e4a_signOf_sum_eq_zero` turns into the equal-cardinality fact). -/
theorem e4a_eta_products_associated {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) :
    Associated
      (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1),
        ((e4aZetaO q) ^ ((a : ZMod q)).val - 1))
      (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
        ((e4aZetaO q) ^ ((a : ZMod q)).val - 1)) := by
  classical
  refine e4a_assoc_of_card_eq_gen (e4aZetaO_isPrimitiveRoot (q := q)) _ _
    (fun a : (ZMod q)ˣ => ((a : ZMod q)).val)
    (fun a _ => ZMod.val_coe_unit_coprime a) (fun a _ => ZMod.val_coe_unit_coprime a) ?_
  exact e4a_dirichlet_card_eq χ (e4a_signOf_sum_eq_zero χ hχ)

#print axioms e4a_eta_products_associated

/-! ## PROBE 42 — THE `𝓞_K → K` IMAGE LINK: the one step I named last tick

Last tick I said the associate relation was at the right index but in `𝓞_K`, while `e4aEta`
lives in the FIELD over `e4aZetaK` — and that the image step was the remaining link.  Doing
it in the same turn as naming it would have been better; doing it in the next is the rule. -/

end


section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]
variable {q : ℕ} [NeZero q]

/-- ζ-in-`𝓞_K` maps to ζ-in-`K`.  `toInteger` is the subtype constructor, so this is `rfl`. -/
theorem e4a_zetaO_image : algebraMap (NumberField.RingOfIntegers (e4aK q)) (e4aK q)
    (e4aZetaO q) = e4aZetaK q := rfl

/-- The fibre products map across intact. -/
theorem e4a_prod_image (S : Finset ((ZMod q)ˣ)) :
    algebraMap (NumberField.RingOfIntegers (e4aK q)) (e4aK q)
        (∏ a ∈ S, ((e4aZetaO q) ^ ((a : ZMod q)).val - 1))
      = ∏ a ∈ S, ((e4aZetaK q) ^ ((a : ZMod q)).val - 1) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_sub, map_pow, map_one, e4a_zetaO_image]

/-- ⭐ **THE LINK CLOSED** — `e4aEta` IS the image of a unit of `𝓞_K`, hence itself and its
inverse are integral.  This is the pair of hypotheses `e4a_eta_sum_is_integer_concrete`
still carries, now supplied — modulo the numerator being nonzero, which is stated rather
than assumed silently. -/
theorem e4a_eta_is_unit_image (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1)
    (hne : (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
              ((e4aZetaO q) ^ ((a : ZMod q)).val - 1)) ≠ 0) :
    ∃ u : (NumberField.RingOfIntegers (e4aK q))ˣ,
      e4aEta χ = algebraMap (NumberField.RingOfIntegers (e4aK q)) (e4aK q)
        (u : NumberField.RingOfIntegers (e4aK q)) := by
  classical
  -- ORIENTATION: gap 3 gives y/x from `Associated x y`; e4aEta is num/den, so take the
  -- SYMMETRIC associate (den ~ num) and the nonzero hypothesis on the DENOMINATOR.
  obtain ⟨u, hu⟩ := e4a_eta_isIntegral_of_associated hne
    (e4a_eta_products_associated χ hχ).symm
  refine ⟨u, ?_⟩
  rw [e4aEta, ← e4a_prod_image, ← e4a_prod_image, hu]


#print axioms e4a_zetaO_image
#print axioms e4a_prod_image
#print axioms e4a_eta_is_unit_image

/-! ## PROBE 43 — ⭐ THE CULMINATION: the integrality pair DISCHARGED, and the assembled
  theorem applied with no open hypothesis beyond `χ ≠ 1` and one nonvanishing side condition -/

/-- η's inverse is the image of the inverse unit. -/
theorem e4a_eta_inv_is_unit_image (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1)
    (hne : (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
              ((e4aZetaO q) ^ ((a : ZMod q)).val - 1)) ≠ 0) :
    ∃ u : (NumberField.RingOfIntegers (e4aK q))ˣ,
      (e4aEta χ)⁻¹ = algebraMap (NumberField.RingOfIntegers (e4aK q)) (e4aK q)
        ((u⁻¹ : (NumberField.RingOfIntegers (e4aK q))ˣ)
          : NumberField.RingOfIntegers (e4aK q)) := by
  obtain ⟨u, hu⟩ := e4a_eta_is_unit_image χ hχ hne
  refine ⟨u, ?_⟩
  rw [hu, ← map_units_inv]

/-- ⭐⭐ **E4a's SPINE, FULLY DISCHARGED** — `∃ T : ℤ, η + η⁻¹ = T` for a real Dirichlet
character, with NO integrality hypothesis left open.  What remains outside is only `χ ≠ 1`
(the amendment, equivalent to non-principality) and the denominator's nonvanishing. -/
theorem e4a_eta_sum_integer_final (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1)
    (hne : (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
              ((e4aZetaO q) ^ ((a : ZMod q)).val - 1)) ≠ 0) :
    ∃ z : ℤ, algebraMap ℤ (e4aK q) z = e4aEta χ + (e4aEta χ)⁻¹ := by
  obtain ⟨u, hu⟩ := e4a_eta_is_unit_image χ hχ hne
  obtain ⟨u', hu'⟩ := e4a_eta_inv_is_unit_image χ hχ hne
  refine e4a_eta_sum_is_integer_concrete χ ?_ ?_
  · rw [hu]; exact NumberField.RingOfIntegers.isIntegral_coe _
  · rw [hu']; exact NumberField.RingOfIntegers.isIntegral_coe _


#print axioms e4a_eta_inv_is_unit_image
#print axioms e4a_eta_sum_integer_final

/-! ## PROBE 44 — E5a's CONNECTIVE: `x + x⁻¹ = 2 cosh (log x)`

E5a is `∃ T : ℤ, 2·cosh(√q · L(1,χ).re) = T` — the SIGN-FREE form, which dodges the Gauss
sign theorem.  My spine delivers `∃ T : ℤ` for `η + η⁻¹`.  The join is the elementary
identity below, and proving it beneath E5a is the same move that served all night: the
statement is someone else's tier, the ground under it is not.

⭐ Note WHY the cosh form is sign-free, since it is the node's whole reason for existing:
`cosh` is EVEN, so it cannot distinguish `log η` from `−log η` — i.e. it does not care which
of `η, η⁻¹` you named.  That is exactly the ambiguity the Gauss sign theorem would have had
to resolve, and the statement sidesteps it by asking a question whose answer is the same
either way.  Same shape as the descent taking a DISJUNCTION rather than a determination. -/

end


section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]

/-- The `χ = −1` fibre product is nonzero in `𝓞_K`: each `ζ^v − 1` with `0 < v < q` is. -/
theorem e4a_fibre_prod_ne_zero {q : ℕ} [NeZero q] (hq : 1 < q)
    (S : Finset ((ZMod q)ˣ)) :
    (∏ a ∈ S, ((e4aZetaO q) ^ ((a : ZMod q)).val - 1)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  intro hzero
  have hone : (e4aZetaO q) ^ ((a : ZMod q)).val = 1 := by
    have := sub_eq_zero.mp hzero
    exact this
  have hdvd : q ∣ ((a : ZMod q)).val :=
    (e4aZetaO_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp hone
  have hpos : 0 < ((a : ZMod q)).val := ZMod.val_pos.mpr (e4a_unit_ne_zero_aux hq a)
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr (ZMod.val_lt _))


/-! ### η's IMAGE IN ℂ, AND ITS NORM

`e4aK q` is an `IntermediateField ℚ ℂ`, so η already lives over ℂ — the "bridge" is the
structure map, and it is a field hom, so it commutes with the quotient and the products. -/

theorem e4a_eta_image {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    (algebraMap (e4aK q) ℂ) (e4aEta χ)
      = (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1),
          ((e4aZeta q) ^ ((a : ZMod q)).val - 1))
        / (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
          ((e4aZeta q) ^ ((a : ZMod q)).val - 1)) := by
  classical
  rw [e4aEta_def, map_div₀, map_prod, map_prod]
  congr 1

theorem e4a_eta_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    ‖(algebraMap (e4aK q) ℂ) (e4aEta χ)‖
      = (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = 1),
          ‖(e4aZeta q) ^ ((a : ZMod q)).val - 1‖)
        / (∏ a ∈ Finset.univ.filter (fun a : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ a = -1),
          ‖(e4aZeta q) ^ ((a : ZMod q)).val - 1‖) := by
  classical
  rw [e4a_eta_image, norm_div, norm_prod, norm_prod]


#print axioms e4a_eta_image
#print axioms e4a_eta_norm

/-! ### ⭐⭐ THE STATEMENT'S REAL PRODUCT IS `‖η‖⁻¹`

Four moves, each already built: the sine bridge factor-by-factor · the units↔`Ioo` transport
(the weight is `1` off the coprimes because `χ` vanishes there) · the exponent at a unit is
`−signOf` · and the fibre split by the sign.  `norm_sub_rev` absorbs `1 − ζ^v` vs `ζ^v − 1`,
so NO sign bookkeeping is needed anywhere — working in norms kills it. -/

theorem e4a_sin_prod_eq_eta_norm_inv {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℝ q) (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a))
      = ‖(algebraMap (e4aK q) ℂ) (e4aEta χ)‖⁻¹ := by
  classical
  set g : ℕ → ℝ := fun a => ‖1 - (e4aZeta q) ^ a‖ with hgdef
  have hstep : ∀ a ∈ Finset.Ioo 0 q,
      (2 * Real.sin (Real.pi * a / q)) ^ (e a) = (g a) ^ (e a) := by
    intro a ha
    obtain ⟨h0, hlt⟩ := Finset.mem_Ioo.mp ha
    rw [hgdef, mul_div_assoc, ← e4a_step3_sin_bridge h0 hlt]
  rw [Finset.prod_congr rfl hstep]
  have hoff : ∀ a ∈ Finset.Ioo 0 q, ¬ Nat.Coprime a q → (g a) ^ (e a) = 1 := by
    intro a _ hnc
    have hz : ((e a : ℤ) : ℝ) = 0 := by
      rw [he a, e4a_char_vanishes_off_units χ hnc, neg_zero]
    have hz0 : e a = 0 := by exact_mod_cast hz
    rw [hz0, zpow_zero]
  rw [← e4a_prod_units_eq_prod_Ioo hq (fun a => (g a) ^ (e a)) hoff]
  have hexp : ∀ u : (ZMod q)ˣ, e ((u : ZMod q).val) = - E4aChiBridge.e4a_signOf χ u := by
    intro u
    have h1 := he ((u : ZMod q).val)
    have h2 : (((u : ZMod q).val : ℕ) : ZMod q) = (u : ZMod q) := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [h2, ← E4aChiBridge.e4a_signOf_cast' χ u] at h1
    exact_mod_cast h1
  have hfilt : Finset.univ.filter (fun u : (ZMod q)ˣ =>
        ¬ (E4aChiBridge.e4a_signOf χ u = 1))
      = Finset.univ.filter (fun u : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ u = -1) := by
    refine Finset.filter_congr fun u _ => ?_
    rcases E4aChiBridge.e4a_signOf_eq_one_or_neg_one χ u with h | h <;>
      simp [h]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun u : (ZMod q)ˣ => E4aChiBridge.e4a_signOf χ u = 1)
      (fun u => (g ((u : ZMod q).val)) ^ (e ((u : ZMod q).val))),
    hfilt, e4a_eta_norm]
  have hone : ∀ u ∈ Finset.univ.filter (fun u : (ZMod q)ˣ =>
      E4aChiBridge.e4a_signOf χ u = 1),
      (g ((u : ZMod q).val)) ^ (e ((u : ZMod q).val))
        = ‖(e4aZeta q) ^ ((u : ZMod q)).val - 1‖⁻¹ := by
    intro u hu
    rw [hexp u, (Finset.mem_filter.mp hu).2, hgdef]
    simp [norm_sub_rev]
  have hneg : ∀ u ∈ Finset.univ.filter (fun u : (ZMod q)ˣ =>
      E4aChiBridge.e4a_signOf χ u = -1),
      (g ((u : ZMod q).val)) ^ (e ((u : ZMod q).val))
        = ‖(e4aZeta q) ^ ((u : ZMod q)).val - 1‖ := by
    intro u hu
    rw [hexp u, (Finset.mem_filter.mp hu).2, hgdef]
    simp [norm_sub_rev]
  rw [Finset.prod_congr rfl hone, Finset.prod_congr rfl hneg, Finset.prod_inv_distrib]
  field_simp


#print axioms e4a_sin_prod_eq_eta_norm_inv

/-! ############################################################################
## ⚖️⭐⭐⭐ THE RULED STATEMENT, PROVED

Captain-ratified 08/19 WITH `(hprim : χ.IsPrimitive)`; statement text VERBATIM as handed
down, not one token altered.

⚠️ NOTE THE ABSENT `1 < q`: the ruling carries only `[NeZero q]`, so `q = 1` is IN SCOPE and
is handled as a case rather than assumed away — there `Finset.Ioo 0 1 = ∅`, the product is
the empty product `1`, and `1 + 1⁻¹ = 2`.  *I did not add a hypothesis to make this go away;
statement edits are not mine.* -/

theorem e4a_fibre_prod_K_ne_zero {q : ℕ} [NeZero q] (hq : 1 < q)
    (S : Finset ((ZMod q)ˣ)) :
    (∏ a ∈ S, ((e4aZetaK q) ^ ((a : ZMod q)).val - 1)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  intro hzero
  have hone : (e4aZetaK q) ^ ((a : ZMod q)).val = 1 := sub_eq_zero.mp hzero
  have hdvd : q ∣ ((a : ZMod q)).val :=
    (e4aZetaK_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp hone
  have hpos : 0 < ((a : ZMod q)).val := ZMod.val_pos.mpr (e4a_unit_ne_zero_aux hq a)
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr (ZMod.val_lt _))

theorem e4a_eta_ne_zero {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℝ q) :
    e4aEta χ ≠ 0 := by
  classical
  rw [e4aEta_def]
  exact div_ne_zero (e4a_fibre_prod_K_ne_zero hq _) (e4a_fibre_prod_K_ne_zero hq _)

/-- ⭐⭐⭐ **E4a — THE RULED STATEMENT.** -/
theorem exists_int_add_inv_sin_prod {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q)
    (hprim : χ.IsPrimitive)
    (heven : χ (-1) = 1)
    (hsum : ∑ a : ZMod q, χ a = 0)
    (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    ∃ T : ℤ, (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a))
           + (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a))⁻¹ = T := by
  classical
  by_cases hq : 1 < q
  · -- the substantive case
    set w : ℂ := (algebraMap (e4aK q) ℂ) (e4aEta χ) with hw
    have hwne : w ≠ 0 := by
      rw [hw]
      exact (map_ne_zero_iff _ (algebraMap (e4aK q) ℂ).injective).mpr
        (e4a_eta_ne_zero hq χ)
    obtain ⟨z, hz⟩ :=
      e4a_eta_sum_integer_final χ (e4a_ne_one_of_sum_zero χ hsum)
        (e4a_fibre_prod_ne_zero hq _)
    have hzC : w + w⁻¹ = (z : ℂ) := by
      have := congrArg (algebraMap (e4aK q) ℂ) hz
      rw [map_add, map_inv₀] at this
      rw [hw, ← this]
      simp
    obtain ⟨T, hT⟩ := e4a_norm_add_inv_int hwne hzC
    refine ⟨T, ?_⟩
    rw [e4a_sin_prod_eq_eta_norm_inv hq χ e he, ← hw, inv_inv, add_comm]
    exact hT
  · -- `q = 1`: the index set is empty and the product is the empty product
    have hq1 : q = 1 := by
      have := Nat.pos_of_ne_zero (NeZero.ne q)
      omega
    subst hq1
    have hempty : Finset.Ioo 0 1 = (∅ : Finset ℕ) := by decide
    refine ⟨2, ?_⟩
    rw [hempty, Finset.prod_empty]
    norm_num


#print axioms e4a_fibre_prod_K_ne_zero
#print axioms e4a_eta_ne_zero
#print axioms exists_int_add_inv_sin_prod

/-! ### 🧪 A MEASUREMENT, NOT A PROPOSAL — which ruled hypotheses did the proof CONSUME?

The ruled statement stands exactly as ratified and is proved above.  This probe asks a
different question and answers it in the kernel rather than by my reading: drop `hprim` and
`heven` and see whether the SAME proof still closes.  If it does, the E4a route consumes
neither — which is a fact about MY ROUTE, not an argument about the ruling.

⚠️ THIS IS NOT A REQUEST TO AMEND ANYTHING.  `hprim` is free at every intended call site and
E5 needs it twice (piece (1) carries `IsPrimitive`; `|τ|² = q` is `gaussSum_normSq_of_primitive`).
The point is only that the record should say what was USED, not what was AVAILABLE. -/

/-- ⭐⭐⭐ **E5a** — the integrality of `η + η⁻¹` IS the integrality of `2 cosh(Re(τ·L))`.
The hypothesis `e4a_cosh_integer_of_sum` was carrying since the morning is now SUPPLIED. -/
theorem e4a_E5a_cosh_integer {q : ℕ} [NeZero q] (hq1 : 1 < q)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (heven : χ (-1) = 1)
    (hsum : ∑ a : ZMod q, χ a = 0) (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    ∃ z : ℤ, (z : ℝ) = 2 * Real.cosh ((gaussSum (e4a_toC χ) ZMod.stdAddChar *
        DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re) := by
  have hPpos : 0 < (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a)) := by
    rw [e4a_sin_prod_eq_eta_norm_inv hq1 χ e he]
    refine inv_pos.mpr (norm_pos_iff.mpr ?_)
    exact (map_ne_zero_iff _ (algebraMap (e4aK q) ℂ).injective).mpr (e4a_eta_ne_zero hq1 χ)
  obtain ⟨T, hT⟩ := exists_int_add_inv_sin_prod χ hprim heven hsum e he
  exact e4a_cosh_integer_of_sum hPpos
    (e4a_log_P_eq_middle hq1 χ hprim heven e he) ⟨T, hT.symm⟩

/-- ⭐⭐⭐ **E5's FLOOR, AT THE ANALYTIC QUANTITY, SIGN-FREE.**  `2 log φ ≤ |Re(τ·L)|`.

⭐ THE ONLY OPEN INPUT IS `Re(τ·L) ≠ 0`, and it is `≠ 0` rather than `> 0` BECAUSE COSH IS
EVEN — `e4a_cosh_of_pm` absorbs the sign, exactly as the 08/19 reprice predicted it would.
*Stating the weaker hypothesis is not a convenience: `> 0` would be an unproved positivity
claim about `‖η‖ < 1`, and nothing in the ladder supplies it.*

⛔ NAMED, NOT HIDDEN: this is E5 CONDITIONAL ON A NONVANISHING. Do not read it as E5 closed. -/
theorem e4a_E5_floor_at_middle {q : ℕ} [NeZero q] (hq1 : 1 < q)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (heven : χ (-1) = 1)
    (hsum : ∑ a : ZMod q, χ a = 0) (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a)
    (hne : (gaussSum (e4a_toC χ) ZMod.stdAddChar *
        DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re ≠ 0) :
    Real.log ((3 + Real.sqrt 5) / 2)
      ≤ |(gaussSum (e4a_toC χ) ZMod.stdAddChar *
          DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re| := by
  obtain ⟨z, hz⟩ := e4a_E5a_cosh_integer hq1 χ hprim heven hsum e he
  refine e4a_E5_floor (z := z) (abs_pos.mpr hne) ?_
  rw [hz]
  refine e4a_cosh_of_pm ?_
  rcases abs_choice ((gaussSum (e4a_toC χ) ZMod.stdAddChar *
      DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re) with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

#print axioms e4a_E5_floor_at_middle

/-! ############################################################################
## ⭐⭐⭐ THE NONVANISHING — E5's FLOOR GOES UNCONDITIONAL

`e4a_E5_floor_at_middle` carried ONE open input: `Re(τ·L) ≠ 0`.  It splits, because τ is
REAL (piece 2), so `Re(τ·L) = τ.re · Re(L)` and BOTH factors are already available:

  τ.re ≠ 0   from `τ.re² = q > 0`                        (e4a_gaussSum_re_sq)
  L(1,χ) > 0 from `Salt.SW.LFunction_apply_one_pos`      ⟵ ALREADY IN THE CORPUS

⭐ THE SECOND IS THE DEEP ONE AND IT WAS LANDED MONTHS AGO. The bank's §2 pre-flight recorded
`LFunction_apply_one_pos` as "parity- and primitivity-free, confirmed exact" and I read that
line at boot this morning — this is that pre-flight paying. *The summit map's lesson: check
what the corpus already holds before pricing a nonvanishing.* -/

/-- ⭐⭐⭐ **E5's FLOOR, UNCONDITIONAL.**  `2 log φ ≤ |Re(τ·L)|` with no open input. -/
theorem e4a_E5_floor_unconditional {q : ℕ} [NeZero q] (hq1 : 1 < q)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (heven : χ (-1) = 1)
    (hsum : ∑ a : ZMod q, χ a = 0) (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    Real.log ((3 + Real.sqrt 5) / 2)
      ≤ |(gaussSum (e4a_toC χ) ZMod.stdAddChar *
          DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re| :=
  e4a_E5_floor_at_middle hq1 χ hprim heven hsum e he
    (e4a_middle_ne_zero χ hprim heven hsum)


#print axioms e4a_gaussSum_re_ne_zero
#print axioms e4a_middle_ne_zero
#print axioms e4a_E5_floor_unconditional

/-! ############################################################################
## ⭐⭐⭐ THE GROUND — AN EFFECTIVE q-UNIFORM `L(1,χ)` LOWER BOUND AT EVEN REAL χ

This is the objective the whole ladder was built for, and it is now one division away:
the floor `2 log φ ≤ |Re(τ·L)|` factors as `|τ.re| · L(1,χ)` with `|τ.re| = √q`.

  ***L(1,χ)  ≥  2 log φ / √q  =  0.96242… / √q***

⛔ TIER NOTE: this is a COMPOSITION of landed results, not a statement I am inventing —
`2 log φ` has been the ladder's unified constant since the R1 ratification (08/15) and the
`c/√q` shape is what the ground was defined to produce.  **If a CANONICAL statement text for
the ground is to be ruled, that is Captain/Fable tier and I am not writing it here.**  This
  lemma reports the inequality; the naming is not mine to fix. -/

/-- ⭐⭐⭐ **THE EVEN-χ FLOOR.** -/
theorem e4a_L1_lower_even {q : ℕ} [NeZero q] (hq1 : 1 < q)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (heven : χ (-1) = 1)
    (hsum : ∑ a : ZMod q, χ a = 0) (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    Real.log ((3 + Real.sqrt 5) / 2) / Real.sqrt q
      ≤ (DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re := by
  classical
  have hquadR : χ.IsQuadratic := by
    intro a
    rcases E4aChiBridge.e4a_dirichletReal_values χ a with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  have hquad : (e4a_toC χ).IsQuadratic := e4a_toC_isQuadratic hquadR
  have hne1 : e4a_toC χ ≠ 1 := e4a_toC_ne_one (e4a_ne_one_of_sum_zero χ hsum)
  have hevC : (e4a_toC χ) (-1) = 1 := e4a_toC_even heven
  have hLpos : 0 < DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1 := by
    rw [hquad.inv]
    exact Salt.SW.LFunction_apply_one_pos hne1 hquad.sq_eq_one
  have hLre : 0 < (DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re :=
    (Complex.lt_def.mp hLpos).1
  have hτim : (gaussSum (e4a_toC χ) (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).im = 0 :=
    e4a_gaussSum_real (e4a_toC χ) hevC hquad
  have hsplit : (gaussSum (e4a_toC χ) ZMod.stdAddChar *
      DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re
      = (gaussSum (e4a_toC χ) ZMod.stdAddChar).re *
        (DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re := by
    rw [Complex.mul_re, hτim, zero_mul, sub_zero]
  have habs := e4a_abs_gaussSum_re (e4a_toC χ)
    ((e4a_toC_isPrimitive_iff χ).mpr hprim) hevC hquad
  have hfloor := e4a_E5_floor_unconditional hq1 χ hprim heven hsum e he
  rw [hsplit, abs_mul, habs, abs_of_pos hLre] at hfloor
  have hsq : (0 : ℝ) < Real.sqrt q := by
    refine Real.sqrt_pos.mpr ?_
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [div_le_iff₀ hsq, mul_comm]
  exact hfloor

end


end Salt.MR
