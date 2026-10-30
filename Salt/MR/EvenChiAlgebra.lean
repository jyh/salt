/-
# The generic algebra beneath η — fibre swaps, the spine, associates, descent

Module 3a of the even-χ port (2026-08-19).  Dependency-CLOSED and LIGHT by measurement: no
cyclotomic field and no ring of integers appears anywhere in these twenty-three declarations,
even though every one of them exists to serve the η that lives in one.

⭐ **PORTING THIS BEFORE THE `𝓞_K` LAYER IS FORCED, NOT PREFERRED.** Measured: the remaining
heavy set's dependency closure contains ALL TWENTY-THREE of these — the η layer cannot compile
without them.

## What it contains

* The **fibre swap / fibre fix** family, in both the abstract (`χ : G → ℤ` multiplicative) and
  the ZMod-indexed forms.  These are what let a Galois twist be absorbed by a reindexing of
  the `χ = +1` and `χ = −1` fibres.
* `e4a_spine` — the abstract shape of the whole descent: a Galois-stable element whose orbit
  sum is rational and integral is an integer.  Stated for an arbitrary field extension, which
  is why it costs nothing to instantiate later.
* `e4a_fixed_isRational` / `e4a_descent_to_int` / `e4a_sum_inv_fixed[_alg]` — the descent's
  three steps, each free of the number field they will eventually be used in.
* `e4a_prod_associated_gen` / `e4a_assoc_of_card_eq_gen` / `e4a_associated_quotient_eq` —
  associate-hood of weighted products, at `CommRing` + `IsDomain`.  **The generality here was
  chosen at the start of the campaign and it is why the 𝓞_K instantiation needs NO re-proof.**
* `e4a_pow_mod_gen` / `e4a_pow_val_mul_gen` — the exponent arithmetic of a primitive root,
  stated generically.
-/
import Salt.MR.EvenChiMiddle

namespace Salt.MR

open IsPrimitiveRoot

/-- `ζ_q := exp(2πi/q)` is a primitive `q`-th root of unity in `ℂ` at `hq : 0 < q`: the exponent
is rewritten to `2πi · (1/q)` and `Complex.isPrimitiveRoot_exp_of_coprime` at `1` applies.
Consumed by `e4a_route_b_isCyclotomicExtension` and `e4aZetaK_isPrimitiveRoot` (`EvenChiEta`)
and by `EvenChiCyclotomic`. -/
theorem e4a_zeta_isPrimitiveRoot {q : ℕ} (hq : 0 < q) :
    IsPrimitiveRoot (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) q := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have heq : ((2 * Real.pi / q : ℝ) : ℂ) * Complex.I
      = 2 * (Real.pi : ℂ) * Complex.I * (((1 : ℕ) : ℂ) / ((q : ℕ) : ℂ)) := by
    push_cast
    field_simp
  rw [heq]
  exact Complex.isPrimitiveRoot_exp_of_coprime 1 q hq.ne' (Nat.coprime_one_left q)

/-- `e4aZeta q = exp(2πi/q)`, the concrete complex root the port adjoins; an `abbrev`, so
`e4a_zeta_isPrimitiveRoot` applies to it by unfolding. It generates `e4aK q` and is the image of
`e4aZetaK q` in `ℂ` (`EvenChiEta`). -/
noncomputable abbrev e4aZeta (q : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)

/-- The descent's first step: an element `x` of a finite Galois extension `E/ℚ` fixed by every
`f : Gal(E/ℚ)` (`hfix`) is in the image of `ℚ` — `IsGalois.mem_range_algebraMap_iff_fixed`.
Consumed by `e4a_descent_to_int`. -/
theorem e4a_fixed_isRational {E : Type*} [Field E] [Algebra ℚ E] [IsGalois ℚ E]
    [FiniteDimensional ℚ E] (x : E) (hfix : ∀ f : Gal(E/ℚ), f x = x) :
    ∃ r : ℚ, algebraMap ℚ E r = x :=
  (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfix

/-- **THE DESCENT** — Galois-fixed AND an algebraic integer ⇒ literally an integer. -/
theorem e4a_descent_to_int {E : Type*} [Field E] [Algebra ℚ E] [IsGalois ℚ E]
    [FiniteDimensional ℚ E] (x : E) (hfix : ∀ f : Gal(E/ℚ), f x = x)
    (hint : IsIntegral ℤ x) :
    ∃ z : ℤ, algebraMap ℤ E z = x := by
  obtain ⟨r, hr⟩ := e4a_fixed_isRational x hfix
  have hinj : Function.Injective (algebraMap ℚ E) := (algebraMap ℚ E).injective
  have hrint : IsIntegral ℤ r := by
    refine IsIntegral.tower_bot hinj ?_
    rw [hr]; exact hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hrint
  exact ⟨z, by rw [IsScalarTower.algebraMap_apply ℤ ℚ E, hz, hr]⟩

#print axioms e4a_fixed_isRational
#print axioms e4a_descent_to_int

/-! ## PROBE 23 — COMPOSITE-q SAFETY, the recon's finding 3 answered in Lean

The 08/18 mathlib recon flagged: `range n` with exponents `1..q−1` coincides with `(ZMod q)ˣ`
ONLY at prime `q`, and asked whether my `q` is composite.  **It is: E4a is stated for a
general modulus `q` with `χ : DirichletCharacter ℝ q`, composite included.**

But the mismatch does not bite, and here is why as a theorem rather than as prose: the
weighted product's exponent is `−χ(a)`, and **χ VANISHES off the units** — so every
non-coprime factor is `g a ^ 0 = 1` and drops out.  The two index sets in this file serve
different masters and neither is wrong:
* `range (q−1)` carries the UNWEIGHTED identity `∏(1−ζ^a) = q` (probe 9) — true at every
  `q`, and the source of the `√q` in `2 log φ / √q`.
* the COPRIME set carries the χ-weighted η — because that is where χ is nonzero.

This lemma is what lets a caller at composite `q` discharge the `hcop` hypothesis my
unit-route lemmas carry, instead of assuming it. -/

section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G]

/-- The `χ(b) = +1` arm: each fibre maps to ITSELF.  **Both arms driven** — the law says a
check is validated only when its good and bad cases give different output, and here the two
arms give genuinely different conclusions (fix vs swap). -/
theorem e4a_fibre_fix (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : G) (hb : χ b = 1) :
    (Finset.univ.filter (fun a => χ a = 1)).image (fun a => a * b)
      = Finset.univ.filter (fun a => χ a = 1) := by
  classical
  have hinv : χ b⁻¹ = 1 := by
    have h1 : χ b * χ b⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    rw [hb] at h1; omega
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hmul, ha, hb]; norm_num
  · intro hx
    refine ⟨x * b⁻¹, ?_, by group⟩
    rw [hmul, hx, hinv]; norm_num


#print axioms e4a_fibre_swap
#print axioms e4a_fibre_fix

/-! ## PROBE 25 — THE KC4 ASSEMBLY at the fibre level

The fibre lemmas are set equalities; the assembly needs them as PRODUCT equalities, because
that is the form `σ` applied to η's numerator actually produces.  Both arms again, and they
are the two halves of `η^{χ(b)}`:
* `χ(b) = −1` — the twisted numerator IS the untwisted DENOMINATOR (⇒ η inverts);
* `χ(b) = +1` — the twisted numerator IS the untwisted numerator (⇒ η is fixed).

⚠️ The recon warned that `Equiv.prod_comp` is `univ`-indexed and cannot be used on a
FILTERED index set.  Correct — so this goes through `Finset.prod_image` with right-
multiplication's injectivity, not through the transport lemma. -/

end


section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]

omit [DecidableEq G] in
/-- The product form of `e4a_fibre_swap` (`EvenChiSign`): at `hb : χ b = -1` the `+1` fibre of
`χ` translated by `b` is the `-1` fibre, so the product of `F (a * b)` over the `+1` fibre is
the product of `F` over the `-1` fibre — `Finset.prod_image` with right multiplication
injective. Consumed by `e4a_eta_inverts` and `EvenChiCyclotomic`. -/
theorem e4a_prod_fibre_swap (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : G) (hb : χ b = -1) (F : G → M) :
    ∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F (a * b)
      = ∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F a := by
  classical
  rw [← e4a_fibre_swap χ hmul hone b hb,
    Finset.prod_image (fun x _ y _ h => mul_right_cancel h)]

omit [DecidableEq G] in
/-- The product form of `e4a_fibre_fix`: at `hb : χ b = 1` the `+1` fibre of `χ` translated by
`b` is itself, so the product of `F (a * b)` over it equals the product of `F` —
`Finset.prod_image` with right multiplication injective. Consumed by `e4a_eta_fixed` and
`EvenChiCyclotomic`. -/
theorem e4a_prod_fibre_fix (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : G) (hb : χ b = 1) (F : G → M) :
    ∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F (a * b)
      = ∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F a := by
  classical
  conv_rhs => rw [← e4a_fibre_fix χ hmul hone b hb]
  rw [Finset.prod_image (fun x _ y _ h => mul_right_cancel h)]


#print axioms e4a_prod_fibre_swap
#print axioms e4a_prod_fibre_fix

/-! ## PROBE 26 — THE MIRROR SWAP, without which the quotient does NOT invert

η = P₊ / P₋.  Probe 25 shows the twisted NUMERATOR becomes P₋.  To conclude
`σ_b(η) = η⁻¹` the twisted DENOMINATOR must become P₊ — a second, genuinely different set
equality, and one I would have skipped had I stopped at "the swap is proved".
At `χ(b) = −1` and `χ(a) = −1`: `χ(ab) = (−1)(−1) = +1`, so the `−1` fibre lands in the
`+1` fibre.  **Only with both directions is the quotient inverted rather than merely
scrambled.** -/

/-- The mirror of `e4a_fibre_swap`: at `hb : χ b = -1` the `-1` fibre of `χ` translated by `b`
is the `+1` fibre, since `χ (a * b) = (-1) * (-1) = 1` by `hmul`; the converse direction uses
`χ b⁻¹ = -1`, derived from `hb`, `hone` and `hmul`. Without it `e4a_eta_inverts` would move only
η's numerator. Consumed by `e4a_prod_fibre_swap'`. -/
theorem e4a_fibre_swap' (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : G) (hb : χ b = -1) :
    (Finset.univ.filter (fun a => χ a = -1)).image (fun a => a * b)
      = Finset.univ.filter (fun a => χ a = 1) := by
  classical
  have hinv : χ b⁻¹ = -1 := by
    have h1 : χ b * χ b⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    rw [hb] at h1; omega
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hmul, ha, hb]; norm_num
  · intro hx
    refine ⟨x * b⁻¹, ?_, by group⟩
    rw [hmul, hx, hinv]; norm_num

omit [DecidableEq G] in
/-- The product form of `e4a_fibre_swap'`: at `hb : χ b = -1` the product of `F (a * b)` over
the `-1` fibre of `χ` is the product of `F` over the `+1` fibre. With `e4a_prod_fibre_swap` it
is what `e4a_eta_inverts` rewrites. -/
theorem e4a_prod_fibre_swap' (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : G) (hb : χ b = -1) (F : G → M) :
    ∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F (a * b)
      = ∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F a := by
  classical
  rw [← e4a_fibre_swap' χ hmul hone b hb,
    Finset.prod_image (fun x _ y _ h => mul_right_cancel h)]

omit [DecidableEq G] in
/-- ⭐ **THE QUOTIENT INVERTS** — `σ_b(η) = η⁻¹` at `χ(b) = −1`, in a field. Both swap
directions consumed; this is the statement KC4 exists to produce. -/
theorem e4a_eta_inverts {K : Type*} [Field K] (χ : G → ℤ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1) (b : G) (hb : χ b = -1) (F : G → K) :
    (∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F (a * b))
      / (∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F (a * b))
      = ((∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F a)
          / (∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F a))⁻¹ := by
  rw [e4a_prod_fibre_swap χ hmul hone b hb F, e4a_prod_fibre_swap' χ hmul hone b hb F,
    inv_div]

#print axioms e4a_fibre_swap'
#print axioms e4a_prod_fibre_swap'
#print axioms e4a_eta_inverts

/-! ## PROBE 27 — THE ZMod-INDEX HALF, grafted from the helm's executor (jason pools)

Delivered in ONE attempt against my brief.  ⭐ AND IT REFUTED MY OWN ANALYSIS: my brief
called the `ZMod.val_mul`/`ζ^q = 1` bridge "the only real content" of the deliverable.
It is not consumed by that statement at all — the statement carries `(a * b)` as a UNITS
product, so `.val` is applied ONCE, after the multiplication, and never distributed.  The
deliverable is `e4a_units_reindex` at one instantiation, by beta.

**The bridge is needed one step EARLIER, at the caller**: `σ_b : ζ ↦ ζ^(b.val)` pushed
through by probe 21 yields exponents `b.val * a.val` — an ℕ product, not a `ZMod` one.
The executor proved that leg too, in `EvenChiCyclotomic.e4a_zeta_pow_val_mul`, not a stub.

⇒ NET: `σ_b` FIXES the full units-indexed product.  No χ-twist here — the twist appears
only once the product is SPLIT INTO FIBRES, which is probe 24/26's territory.

Grafted with the two restated givens dropped.  ⚠️ Their caveat said both sat in the fenced
`GivenByMath` section; measured, `e4a_units_reindex` sat OUTSIDE it, so deleting the fence
alone would have collided.  Extracted `section E4aUnitsIndex` only. -/

/-- A ring hom `σ` that sends `x` to `x` or to `x⁻¹` (`h`) fixes `x + x⁻¹`: `map_add`,
`map_inv₀`, and in the second arm `inv_inv` and `add_comm`. The ring-hom form behind
`e4a_sum_inv_fixed_alg`. -/
theorem e4a_sum_inv_fixed {K : Type*} [Field K] (σ : K →+* K) (x : K)
    (h : σ x = x ∨ σ x = x⁻¹) : σ (x + x⁻¹) = x + x⁻¹ := by
  rw [map_add, map_inv₀]
  rcases h with h | h
  · rw [h]
  · rw [h, inv_inv, add_comm]

/-- The same for an algebra equivalence, which is the shape `Gal(E/ℚ)` actually provides. -/
theorem e4a_sum_inv_fixed_alg {E : Type*} [Field E] [Algebra ℚ E] (σ : E ≃ₐ[ℚ] E) (x : E)
    (h : σ x = x ∨ σ x = x⁻¹) : σ (x + x⁻¹) = x + x⁻¹ := by
  have := e4a_sum_inv_fixed (σ : E →+* E) x (by simpa using h)
  simpa using this

/-- ⭐⭐ **E4a's CONCLUSION SHAPE** — if every Galois conjugate of `η` is `η` or `η⁻¹`, and
`η + η⁻¹` is an algebraic integer, then `η + η⁻¹` IS an integer.  This is
`∃ T : ℤ, η + η⁻¹ = T`. -/
theorem e4a_eta_sum_is_integer {E : Type*} [Field E] [Algebra ℚ E] [IsGalois ℚ E]
    [FiniteDimensional ℚ E] (η : E)
    (hgal : ∀ σ : E ≃ₐ[ℚ] E, σ η = η ∨ σ η = η⁻¹)
    (hint : IsIntegral ℤ (η + η⁻¹)) :
    ∃ z : ℤ, algebraMap ℤ E z = η + η⁻¹ :=
  e4a_descent_to_int (η + η⁻¹) (fun σ => e4a_sum_inv_fixed_alg σ η (hgal σ)) hint

#print axioms e4a_sum_inv_fixed
#print axioms e4a_sum_inv_fixed_alg
#print axioms e4a_eta_sum_is_integer


/-! ## PROBE 30 — ⛔ THE GAP THE COMPOSITION CONTROL FOUND, and its repair

Ran the control I had no reason to expect would fire: **does the spine actually compose?**
Audited `IsIntegral ℤ (η + η⁻¹)` across the file — it occurs ONLY as a HYPOTHESIS (the
descent, the glue). **Nothing supplied it.**

That is the THIRD disjoint-halves gap in this file today, after probe 8's abstract/concrete
ζ and probe 18's ring/field, and it is the same shape every time: two green pieces whose
interface nobody stated.  The unit-ness leg proves η is a UNIT; the descent CONSUMES
integrality of `η + η⁻¹`; no lemma joined them.

The join is that a unit contributes BOTH `x` and `x⁻¹` as integers, so the sum is integral
by `IsIntegral.add`.  Stated for `x` and `x⁻¹` integral rather than for a `(𝓞 K)ˣ` — more
general, and it avoids the units-group plumbing entirely (attempt 1 tried `u + u⁻¹` inside
the UNIT GROUP, which has no addition at all). -/

/-- The join the composition control (probe 30) found missing: if `x` and `x⁻¹` are both
integral over `ℤ` (`hx`, `hxinv`), so is `x + x⁻¹` — `IsIntegral.add`. Stated for the two
elements rather than for a unit of `𝓞 K`, which has no addition. Consumed by `e4a_spine`. -/
theorem e4a_sum_isIntegral_of_both {K : Type*} [Field K] (x : K)
    (hx : IsIntegral ℤ x) (hxinv : IsIntegral ℤ x⁻¹) :
    IsIntegral ℤ (x + x⁻¹) := hx.add hxinv

/-- ⭐ **THE SPINE, COMPOSED — every hypothesis now supplied, none dangling.** -/
theorem e4a_spine {K : Type*} [Field K] [Algebra ℚ K] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (x : K) (hx : IsIntegral ℤ x) (hxinv : IsIntegral ℤ x⁻¹)
    (hgal : ∀ σ : K ≃ₐ[ℚ] K, σ x = x ∨ σ x = x⁻¹) :
    ∃ z : ℤ, algebraMap ℤ K z = x + x⁻¹ :=
  e4a_eta_sum_is_integer x hgal (e4a_sum_isIntegral_of_both x hx hxinv)

/-- For `ζ` with `hζ : ζ ^ q = 1` in any monoid, an exponent may be reduced mod `q`: write
`n = q * (n / q) + n % q` (`Nat.div_add_mod`) and the `q`-multiple part contributes `1`.
Consumed by `e4a_pow_val_mul_gen`. -/
theorem e4a_pow_mod_gen {M : Type*} [Monoid M] {q : ℕ} {ζ : M} (hζ : ζ ^ q = 1) (n : ℕ) :
    ζ ^ (n % q) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

/-- The exponent bridge off `ℂ`: for `ζ` with `hζ : ζ ^ q = 1`, the `val` of a `ZMod q` product
and the product of the `val`s give the same power, since `ZMod.val_mul` differs by a reduction
mod `q` that `e4a_pow_mod_gen` absorbs. Consumed by `e4a_sigma_prod_reindex` (`EvenChiEta`),
where `σ_b : ζ ↦ ζ ^ b.val` is pushed through η's products. -/
theorem e4a_pow_val_mul_gen {M : Type*} [Monoid M] {q : ℕ} {ζ : M} (hζ : ζ ^ q = 1)
    (x y : ZMod q) : ζ ^ ((x * y).val) = ζ ^ (x.val * y.val) := by
  rw [ZMod.val_mul, e4a_pow_mod_gen hζ]

/-! ### PROBE 35 — ⭐ THE TRANSPORT: σ applied to a `(ZMod q)ˣ`-indexed cyclotomic product

This is where the link is CONSUMED.  `e4a_map_prod_sub_one_pow` (probe 21) is ℕ-indexed;
η's products are `(ZMod q)ˣ`-indexed with exponent `(a : ZMod q).val`, so the same three
`map_*` rewrites are redone at that index type.  The output is exactly the translated index
`a ↦ a * b` that the fibre apparatus (probes 24–26) eats. -/

end


section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]
variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]

/-- The partner of `e4a_fibre_fix` for the `-1` fibre: at `hb : χ b = 1` the `-1` fibre of `χ`
translated by `b` is itself, since `χ (a * b) = χ a` by `hmul`; the converse direction uses
`χ b⁻¹ = 1`. The gap probe 36 (`EvenChiEta`) found: without it the fix arm fixed η's numerator
and said nothing of its denominator. Consumed by `e4a_prod_fibre_fix'`. -/
theorem e4a_fibre_fix' (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : G) (hb : χ b = 1) :
    (Finset.univ.filter (fun a => χ a = -1)).image (fun a => a * b)
      = Finset.univ.filter (fun a => χ a = -1) := by
  classical
  have hinv : χ b⁻¹ = 1 := by
    have h1 : χ b * χ b⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    rw [hb] at h1; omega
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hmul, ha, hb]; norm_num
  · intro hx
    refine ⟨x * b⁻¹, ?_, by group⟩
    rw [hmul, hx, hinv]; norm_num

omit [DecidableEq G] in
/-- The product form of `e4a_fibre_fix'`: at `hb : χ b = 1` the product of `F (a * b)` over the
`-1` fibre of `χ` is the product of `F` over it. With `e4a_prod_fibre_fix` it is what
`e4a_eta_fixed` rewrites. -/
theorem e4a_prod_fibre_fix' (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1)
    (b : G) (hb : χ b = 1) (F : G → M) :
    ∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F (a * b)
      = ∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F a := by
  classical
  conv_rhs => rw [← e4a_fibre_fix' χ hmul hone b hb]
  rw [Finset.prod_image (fun x _ y _ h => mul_right_cancel h)]

end


section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]

/-- ⭐ **THE QUOTIENT IS FIXED**
⚠️ **PORT DIVERGENCE, DELIBERATE AND RECORDED:** the out-of-tree source states this with an
explicit `[DecidableEq G]` binder.  Here that binder is DROPPED — the enclosing section still
supplies the instance to the PROOF, while the TYPE does not need it, so `lake build`'s linter
is satisfied.  **The scratch cannot take the same edit** (its `e4a_eta_fixed` sits where no
section supplies the instance, and removing the binder breaks its proof), so the two forms
differ by exactly this one binder.  *Stated here because an undocumented divergence between a
source of truth and its port is the trap this port exists to avoid.*

⭐ **THE QUOTIENT IS FIXED** — `σ_b(η) = η` at `χ(b) = +1`.  The partner of math's
`e4a_eta_inverts`; without it the `hgal` disjunction has only one arm. -/
theorem e4a_eta_fixed {G : Type*} [Fintype G] [Group G] {K : Type*} [Field K]
    (χ : G → ℤ) (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1) (b : G) (hb : χ b = 1)
    (F : G → K) :
    (∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F (a * b))
      / (∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F (a * b))
      = (∏ a ∈ Finset.univ.filter (fun a => χ a = 1), F a)
        / (∏ a ∈ Finset.univ.filter (fun a => χ a = -1), F a) := by
  rw [e4a_prod_fibre_fix χ hmul hone b hb F, e4a_prod_fibre_fix' χ hmul hone b hb F]

/-! ### PROBE 37 — ⭐⭐ η IN `K`, AND `hgal` DISCHARGED

η is written where the spine lives: in `K = ℚ⟮ζ⟯`, indexed by `(ZMod q)ˣ`, with the χ-fibres
supplied by the landed `E4aChiBridge.e4a_signOf`.  Then the disjunction `σ η = η ∨ σ η = η⁻¹`
— `e4a_spine`'s `hgal`, once unsupplied — is proved for EVERY `σ` (`EvenChiEta.e4a_eta_gal`). -/

end


section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

omit [IsDomain R] in
/-- Two associated elements `x`, `y` of `R` (`h`), with `x ≠ 0` (`hx`) and `algebraMap R K`
injective (`hinj`), have a quotient `y / x` in `K` that is the image of a unit `u : Rˣ`:
`y = x * u` and the nonzero image of `x` cancels. Instantiated at `R = 𝓞 K` by
`e4a_eta_isIntegral_of_associated` (`EvenChiEta`). -/
theorem e4a_associated_quotient_eq (hinj : Function.Injective (algebraMap R K))
    {x y : R} (hx : x ≠ 0) (h : Associated x y) :
    ∃ u : Rˣ, (algebraMap R K y) / (algebraMap R K x) = algebraMap R K (u : R) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have hx0 : algebraMap R K x ≠ 0 := by
    simpa using fun hc => hx (hinj (by simpa using hc))
  rw [← hu, map_mul]
  field_simp

end


section

variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {M : Type*} [CommMonoid M]
variable {A : Type*} [CommRing A] [IsDomain A] {ζ : A} {n : ℕ}

/-- For a primitive `n`-th root `ζ` of a domain (`hζ`) and exponents `e a` coprime to `n` on `S`
(`hS`), the product of `ζ ^ (e a) - 1` over `S` is associated to `(ζ - 1) ^ S.card`: induction
on `S`, each factor associated to `ζ - 1` by
`IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`. Consumed by
`e4a_assoc_of_card_eq_gen`. -/
theorem e4a_prod_associated_gen {ι : Type*} (hζ : IsPrimitiveRoot ζ n) (S : Finset ι)
    (e : ι → ℕ) (hS : ∀ a ∈ S, Nat.Coprime (e a) n) :
    Associated (∏ a ∈ S, (ζ ^ (e a) - 1)) ((ζ - 1) ^ S.card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      have h1 : Associated (ζ ^ (e a) - 1) (ζ - 1) :=
        (hζ.associated_sub_one_pow_sub_one_of_coprime
          (hS a (Finset.mem_insert_self a S))).symm
      have h2 : Associated (∏ b ∈ S, (ζ ^ (e b) - 1)) ((ζ - 1) ^ S.card) :=
        ih (fun b hb => hS b (Finset.mem_insert_of_mem hb))
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ,
        mul_comm ((ζ - 1) ^ S.card) (ζ - 1)]
      exact h1.mul_mul h2

/-- Equal cardinality ⇒ the two index-generic products are associated. -/
theorem e4a_assoc_of_card_eq_gen {ι : Type*} (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset ι) (e : ι → ℕ)
    (hS : ∀ a ∈ S, Nat.Coprime (e a) n) (hT : ∀ a ∈ T, Nat.Coprime (e a) n)
    (hcard : S.card = T.card) :
    Associated (∏ a ∈ S, (ζ ^ (e a) - 1)) (∏ a ∈ T, (ζ ^ (e a) - 1)) := by
  have h1 := e4a_prod_associated_gen hζ S e hS
  have h2 := e4a_prod_associated_gen hζ T e hT
  rw [hcard] at h1
  exact h1.trans h2.symm

end


end Salt.MR
