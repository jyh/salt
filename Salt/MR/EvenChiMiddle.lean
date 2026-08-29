/-
# The middle — E3's Fourier identity reaching the real sine product

Module 8 of the even-χ port (2026-08-19).  Dependency-CLOSED and LIGHT by measurement: no
cyclotomic field and no ring of integers appears anywhere in these fourteen declarations.

## What it does

E3 gives an identity at `s = 1` between `τ(χ)·L(χ⁻¹,1)` and a sum of complex logarithms over
`ZMod q`.  This module carries that all the way down to a REAL statement about a product of
sines with INTEGER exponents, indexed by the units:

    Re( τ · L(χ⁻¹,1) )  =  − log ∏_{a ∈ (ZMod q)ˣ} ( 2 sin(π·(−a).val / q) ) ^ χ(a)

## Two things here are worth reading before using it

* ⭐ `e4a_norm_add_inv_int` — **if `w + w⁻¹` is an integer then so is `‖w‖ + ‖w‖⁻¹`, with NO
  assumption that `w` is real.** Taking imaginary parts gives `w.im · (normSq w − 1) = 0`, so
  either `w` is real (and `w = ±‖w‖`) or `‖w‖ = 1` — and BOTH branches land an integer.
  *This is what makes the descent to the real statement possible without ever proving that η
  is real, which is a Galois question the target never asks.*
* ⭐ `e4a_signOf_neg` / `e4a_middle_reindex` — **this is where EVENNESS is load-bearing.**
  E3's identity indexes by `(−j).val`; η's products index by `val`; the two agree ONLY because
  `χ(−a) = χ(a)`.  *The hypothesis E4a's own proof does not consume is the one this join
  cannot do without.*

## Also here

`e4a_prod_units_eq_prod_Ioo` (the one index transport the ruled statement forces — both
indices are fixed by objects the port does not own), `e4a_ne_one_of_sum_zero` (`χ ≠ 1` is a
CONSEQUENCE of the R1 amendment, not an extra hypothesis), and `e4a_middle_ne_zero`
(`Re(τ·L) ≠ 0`, which splits because τ is real and `L(1,χ) > 0` was already in the corpus).
-/
import Salt.MR.EvenChiTau
import Salt.MR.EvenChiFourier
import Salt.SW.Siegel

namespace Salt.MR

open scoped ComplexOrder

/-- ⭐⭐ **THE CRUX.**  If `w + w⁻¹` is an integer, so is `‖w‖ + ‖w‖⁻¹` — with NO assumption
that `w` is real.  The two branches are "w is real" and "w is on the unit circle". -/
theorem e4a_norm_add_inv_int {w : ℂ} (hw : w ≠ 0) {z : ℤ} (h : w + w⁻¹ = (z : ℂ)) :
    ∃ T : ℤ, ‖w‖ + ‖w‖⁻¹ = (T : ℝ) := by
  have hns : Complex.normSq w ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hw
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsq : ‖w‖ ^ 2 = Complex.normSq w := Complex.sq_norm w
  have him : w.im + -w.im / Complex.normSq w = 0 := by
    have hh := congrArg Complex.im h
    simpa [Complex.add_im, Complex.inv_im] using hh
  have hfac : w.im * (Complex.normSq w - 1) = 0 := by
    field_simp at him
    nlinarith [him]
  rcases mul_eq_zero.mp hfac with hzero | hone
  · -- `w` is real: `w = ±‖w‖`, and the sign only flips the integer
    have hre : w = ((w.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hzero])
    have hrene : w.re ≠ 0 := by
      intro hh; exact hw (by rw [hre, hh]; simp)
    have hz : w.re + (w.re)⁻¹ = (z : ℝ) := by
      have hh : ((w.re + (w.re)⁻¹ : ℝ) : ℂ) = (((z : ℝ)) : ℂ) := by
        push_cast
        rw [← hre]
        exact h
      exact_mod_cast hh
    have hn : ‖w‖ = |w.re| := by
      conv_lhs => rw [hre]
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hflip : -w.re + (-w.re)⁻¹ = -(w.re + (w.re)⁻¹) := by field_simp; ring
    rcases abs_cases w.re with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ⟨z, by rw [hn, ha]; exact hz⟩
    · refine ⟨-z, ?_⟩
      rw [hn, ha, hflip, hz]
      push_cast
      ring
  · -- `w` is on the unit circle
    have h1 : Complex.normSq w = 1 := by linarith [sub_eq_zero.mp hone]
    have hn1 : ‖w‖ = 1 := by nlinarith [hsq, norm_nonneg w, h1]
    exact ⟨2, by rw [hn1]; norm_num⟩


#print axioms e4a_norm_add_inv_int

/-! ### THE ONE TRANSPORT THE STATEMENT GENUINELY FORCES

Three times today the coordinates law saved a transport because the consuming lemma was
already index-agnostic.  ⛔ NOT HERE, and the difference is worth naming: the RULED statement
fixes `Finset.Ioo 0 q` (ℕ) and `e4aEta` is defined over `(ZMod q)ˣ`.  BOTH INDICES ARE FIXED
BY OBJECTS I DO NOT OWN, so there is no generic statement to reach for — the bijection has to
be built.  *That is the honest test of the law: it saves you when a coordinate is FREE, and
this one is not.* -/

/-- `val` is a bijection from the units of `ZMod q` onto the coprime residues in `Ioo 0 q`;
weights supported on the units therefore see the whole of `Ioo 0 q`. -/
theorem e4a_prod_units_eq_prod_Ioo {q : ℕ} [NeZero q] (hq : 1 < q) {M : Type*} [CommMonoid M]
    (F : ℕ → M) (hF : ∀ a ∈ Finset.Ioo 0 q, ¬ Nat.Coprime a q → F a = 1) :
    ∏ u : (ZMod q)ˣ, F ((u : ZMod q).val) = ∏ a ∈ Finset.Ioo 0 q, F a := by
  classical
  have hmem : ∀ u : (ZMod q)ˣ, ((u : ZMod q)).val ∈
      (Finset.Ioo 0 q).filter (fun a => Nat.Coprime a q) := by
    intro u
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨?_, ZMod.val_lt _⟩,
      ZMod.val_coe_unit_coprime u⟩
    exact ZMod.val_pos.mpr (by
      intro h
      have hu : IsUnit (0 : ZMod q) := h ▸ u.isUnit
      haveI : Fact (1 < q) := ⟨hq⟩
      rw [isUnit_zero_iff] at hu
      exact zero_ne_one hu)
  have hbij : ∏ u : (ZMod q)ˣ, F ((u : ZMod q).val)
      = ∏ a ∈ (Finset.Ioo 0 q).filter (fun a => Nat.Coprime a q), F a := by
    refine Finset.prod_nbij' (fun u : (ZMod q)ˣ => ((u : ZMod q)).val)
      (fun a : ℕ => if h : Nat.Coprime a q then ZMod.unitOfCoprime a h else 1)
      (fun u _ => hmem u) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro u _
      rw [dif_pos (ZMod.val_coe_unit_coprime u)]
      refine Units.ext ?_
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_val, ZMod.cast_id]
    · intro a ha
      obtain ⟨haI, hac⟩ := Finset.mem_filter.mp ha
      rw [dif_pos hac, ZMod.coe_unitOfCoprime,
        ZMod.val_natCast_of_lt (Finset.mem_Ioo.mp haI).2]
  rw [hbij]
  refine Finset.prod_subset (Finset.filter_subset _ _) ?_
  intro a ha hnot
  exact hF a ha (fun hc => hnot (Finset.mem_filter.mpr ⟨ha, hc⟩))

/-- `χ ≠ 1` is a CONSEQUENCE of the R1 amendment, not an extra hypothesis: at the principal
character the sum counts the units, and there is at least one. -/
theorem e4a_ne_one_of_sum_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    (hsum : ∑ a : ZMod q, χ a = 0) : χ ≠ 1 := by
  classical
  intro h
  rw [h, MulChar.sum_one_eq_card_units] at hsum
  have hpos : 0 < Fintype.card ((ZMod q)ˣ) := Fintype.card_pos
  have : (0 : ℝ) < (Fintype.card ((ZMod q)ˣ) : ℝ) := by exact_mod_cast hpos
  rw [hsum] at this
  exact lt_irrefl _ this

theorem e4a_fourier_signOf_form {q : ℕ} [NeZero q] (hq : q ≠ 1)
    (χ : DirichletCharacter ℝ q) (hprim : (e4a_toC χ).IsPrimitive) (hev : χ (-1) = 1) :
    gaussSum (e4a_toC χ) ZMod.stdAddChar * DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1
      = ∑ a : (ZMod q)ˣ, ((E4aChiBridge.e4a_signOf χ a : ℤ) : ℂ) *
          (-(Complex.log (1 - Complex.exp
            (((2 * Real.pi * (((-(a : ZMod q)).val : ℝ) / q) : ℝ) : ℂ) * Complex.I)))) := by
  rw [Salt.MR.LFunction_one_even_fourier hq hprim (e4a_toC_even hev)]
  exact e4a_toC_sum_eq_signOf_sum χ _

#print axioms e4a_fourier_signOf_form

/-! ### ⭐ PRIMITIVITY TRANSPORTS — the item my own Gap-B landing left unpriced

`e4a_fourier_signOf_form` takes `hprim` AT THE COMPLEXIFIED character and passes it through;
it does not prove primitivity moves.  If the assembled statement quantifies over a REAL χ,
that lemma is owed.  Here it is, both directions, from ONE observation:

  ⭐ THE KERNELS ARE EQUAL.  `ofReal` is injective and sends `1` to `1`, so `χ_ℂ u = 1` iff
  `χ_ℝ u = 1` — and mathlib characterises `FactorsThrough` purely by a KERNEL containment
  (`factorsThrough_iff_ker_unitsMap`).  Everything above is bookkeeping on that one fact.

⚠️ STILL PROOF-INTERNAL AND STILL SILENT ABOUT THE HELD STATEMENT: this says primitivity is
preserved by complexification.  It does NOT decide whether the assembled E4a statement should
CARRY `hprim` — that is the Captain's, and this lemma is neutral between the two rulings.
It makes the `hprim`-carrying form STATABLE OVER A REAL χ, which is the only reason it is owed. -/

/-- ⭐⭐ **THE WITNESS, NOW STATABLE OVER A REAL CHARACTER.**  `e4a_fourier_signOf_form` had to
take primitivity at the COMPLEXIFIED character because nothing said primitivity transports.
It does (`e4a_toC_isPrimitive`), so the hypothesis can be stated where the campaign actually
has it: on the real χ.  Same conclusion, hypothesis moved to the side that supplies it. -/
theorem e4a_fourier_signOf_form_real {q : ℕ} [NeZero q] (hq : q ≠ 1)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (hev : χ (-1) = 1) :
    gaussSum (e4a_toC χ) ZMod.stdAddChar * DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1
      = ∑ a : (ZMod q)ˣ, ((E4aChiBridge.e4a_signOf χ a : ℤ) : ℂ) *
          (-(Complex.log (1 - Complex.exp
            (((2 * Real.pi * (((-(a : ZMod q)).val : ℝ) / q) : ℝ) : ℂ) * Complex.I)))) :=
  e4a_fourier_signOf_form hq χ (e4a_toC_isPrimitive hprim) hev

#print axioms e4a_fourier_signOf_form_real

/-! ### ⭐ GAP C + THE INDEX — the last connective between the witness and the sin form

The witness's right-hand side carries `exp((2π·v/q)·I)` at `v = (−a).val` for a UNIT `a`;
the landed sin bridge is stated for `(exp((2π/q)·I))^a` at `a : ℕ`.  Two shape differences,
both mechanical once named.

⭐ AND THE INDEX IS *NOT* TRANSPORTED, deliberately.  The banked law is that the cost lives
in the coordinates — stated over the object's OWN index there is nothing to move.  I do not
push the units-indexed sum across a bijection into `Finset ℕ`; I note that
`e4a_sum_clog_re` was ALREADY generic in `ι`, and supply the numeric coordinate through
`ZMod.val` where the sine actually needs one.  The ℕ-specific `_sin` variant is bypassed,
not ported.  (Third sighting of this seat's ℕ-vs-own-index habit; first time it costs nothing.) -/

/-- ⭐⭐ **THE CONNECTIVE** — the real part of the witness's right-hand side IS the negated
`ℤ`-weighted sum of `log (2 sin(π·v/q))`, indexed by the units, with no transport. -/
theorem e4a_witness_rhs_re {q : ℕ} [NeZero q] (hq : 1 < q) (c : (ZMod q)ˣ → ℤ) :
    (∑ a : (ZMod q)ˣ, ((c a : ℂ) *
        (-(Complex.log (1 - Complex.exp
          ((((2 * Real.pi * (((-(a : ZMod q)).val : ℝ) / q)) : ℝ) : ℂ) * Complex.I)))))).re
      = ∑ a : (ZMod q)ˣ, (c a : ℝ) *
          (-Real.log (2 * Real.sin (Real.pi * (((-(a : ZMod q)).val : ℝ) / q)))) := by
  rw [e4a_sum_clog_re]
  exact Finset.sum_congr rfl fun a _ => by
    rw [e4a_sin_bridge_zmod (e4a_unit_neg_ne_zero hq a)]

/-- ⭐⭐⭐ **THE MIDDLE'S ANALYTIC-TO-REAL JOIN.**  Taking real parts of the Fourier identity
at `s = 1` lands the negated `ℤ`-weighted sum of `log (2 sin(π·v/q))` — the sum that
`e4a_log_eta_eq_sum` identifies with `−log η`.

This is the composition the whole ring-bridge section existed to make possible: E3's analytic
identity (ℂ, primitive, even) reaching the real sine sum with INTEGER weights, stated over a
REAL character and over the units' own index.  Three lines, because every piece beneath it
was made to fit first.

⛔ NOT the tier-locked statement, and not the final `log η = √q·Re L`: the `√q` still needs
`|τ|² = q` and the identification of the sine sum with `log η`.  This is the join, not the
conclusion. -/
theorem e4a_middle_re_join {q : ℕ} [NeZero q] (hq1 : 1 < q)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (hev : χ (-1) = 1) :
    (gaussSum (e4a_toC χ) ZMod.stdAddChar *
        DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re
      = ∑ a : (ZMod q)ˣ, ((E4aChiBridge.e4a_signOf χ a : ℤ) : ℝ) *
          (-Real.log (2 * Real.sin (Real.pi * (((-(a : ZMod q)).val : ℝ) / q)))) := by
  have hq : q ≠ 1 := by omega
  rw [e4a_fourier_signOf_form_real hq χ hprim hev]
  exact e4a_witness_rhs_re hq1 (fun a => E4aChiBridge.e4a_signOf χ a)

#print axioms e4a_middle_re_join

/-! ### ⭐ THE τ MAGNITUDE — the only source of the √q in `log η = √q·Re L`

Reality alone (piece 2) does not produce a `√q`; it produces `τ.re`.  The `√q` comes from
`|τ|² = q`, which is PRIMITIVE-BOUND by name (`Salt.LS.gaussSum_normSq`).  Recording that
here rather than at assembly time, because "the sign is free" is true and has been quoted in
a way that can hide WHERE the magnitude comes from. -/

/-- Evenness moves through the sign map: `signOf χ (−u) = signOf χ u`. -/
theorem e4a_signOf_neg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) (heven : χ (-1) = 1)
    (u : (ZMod q)ˣ) :
    E4aChiBridge.e4a_signOf χ (u * (-1)) = E4aChiBridge.e4a_signOf χ u := by
  have hval : ((u * (-1) : (ZMod q)ˣ) : ZMod q) = -(u : ZMod q) := by
    push_cast; ring
  unfold E4aChiBridge.e4a_signOf
  rw [hval, show (-(u : ZMod q)) = (-1 : ZMod q) * (u : ZMod q) by ring, map_mul, heven,
    one_mul]

/-- The `(−a)`-indexed product of E3's identity IS the `val`-indexed product of η —
by the units reindex `a ↦ a·(−1)`, with evenness supplying the exponent. -/
theorem e4a_middle_reindex {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    (heven : χ (-1) = 1) :
    (∏ a : (ZMod q)ˣ, (2 * Real.sin (Real.pi * (((-(a : ZMod q)).val : ℝ) / q)))
        ^ (E4aChiBridge.e4a_signOf χ a))
      = ∏ a : (ZMod q)ˣ, (2 * Real.sin (Real.pi * ((((a : ZMod q)).val : ℝ) / q)))
        ^ (E4aChiBridge.e4a_signOf χ a) := by
  have hkey := e4a_units_reindex
    (fun u : (ZMod q)ˣ => (2 * Real.sin (Real.pi * ((((u : ZMod q)).val : ℝ) / q)))
      ^ (E4aChiBridge.e4a_signOf χ u)) (-1)
  rw [← hkey]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hval : ((a * (-1) : (ZMod q)ˣ) : ZMod q) = -(a : ZMod q) := by push_cast; ring
  rw [hval, e4a_signOf_neg χ heven a]

/-- `log` of the units-indexed sine product, with no generalisation: the landed
`e4a_log_zpow_prod` was already index-agnostic. -/
theorem e4a_log_eta_units {q : ℕ} [NeZero q] (hq : 1 < q) (e : (ZMod q)ˣ → ℤ) :
    Real.log (∏ a : (ZMod q)ˣ,
        (2 * Real.sin (Real.pi * (((-(a : ZMod q)).val : ℝ) / q))) ^ (e a))
      = ∑ a : (ZMod q)ˣ, (e a : ℝ) *
          Real.log (2 * Real.sin (Real.pi * (((-(a : ZMod q)).val : ℝ) / q))) :=
  e4a_log_zpow_prod _ _ e (fun a _ => e4a_sin_ne_zero_at_unit hq a)

/-- ⭐⭐⭐ **THE MIDDLE.**  The real part of `τ·L(χ⁻¹,1)` IS `−log` of the χ-weighted sine
product.  Every hypothesis is on the REAL character; the index is the units' own. -/
theorem e4a_middle_closed {q : ℕ} [NeZero q] (hq1 : 1 < q)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (hev : χ (-1) = 1) :
    (gaussSum (e4a_toC χ) ZMod.stdAddChar *
        DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re
      = -Real.log (∏ a : (ZMod q)ˣ,
          (2 * Real.sin (Real.pi * (((-(a : ZMod q)).val : ℝ) / q)))
            ^ (E4aChiBridge.e4a_signOf χ a)) := by
  rw [e4a_middle_re_join hq1 χ hprim hev,
    e4a_log_eta_units hq1 (fun a => E4aChiBridge.e4a_signOf χ a)]
  simp [mul_neg]


#print axioms e4a_unit_val_div_mem
#print axioms e4a_sin_ne_zero_at_unit
#print axioms e4a_log_eta_units
#print axioms e4a_middle_closed

/-! ############################################################################
## ⚖️⭐ THE RULED STATEMENT — tier-lock OPENED by the Captain 08/19, WITH `hprim`

⭐⭐ THE CRUX DISSOLVED BEFORE IT WAS PRICED.  I was about to pay for "is η REAL?" — a
Galois-descent question (complex conjugation is a `σ`, and η's `hgal` gives only the
DISJUNCTION `σ η = η ∨ σ η = η⁻¹`).  Computing it, `conj η = ζ^{-S} · η`: η is real only if
`q ∣ S`, which is NOT free.

⇒ BUT THE STATEMENT NEVER ASKS.  Stated over ℂ instead of over K there is no descent:
for ANY `w ≠ 0` with `w + w⁻¹` REAL, taking imaginary parts gives
`w.im · (normSq w − 1) = 0`, so EITHER `w` is real (and `w = ±‖w‖`, so `‖w‖ + ‖w‖⁻¹ = ±z`)
OR `‖w‖ = 1` (and `‖w‖ + ‖w‖⁻¹ = 2`).  ***BOTH BRANCHES LAND AN INTEGER.***

🔑 THE COST WAS IN THE COORDINATES, for the fourth time today: the descent I was pricing
belongs to a question the target does not ask.  `η + η⁻¹ ∈ ℤ ⊆ ℝ` is the ENTIRE input. -/

/-- The statement's product, in η's own units index. -/
theorem e4a_P_eq_units_prod_inv {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℝ q) (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a))
      = (∏ u : (ZMod q)ˣ, (2 * Real.sin (Real.pi * ((((u : ZMod q)).val : ℝ) / q)))
          ^ (E4aChiBridge.e4a_signOf χ u))⁻¹ := by
  classical
  have hstep : ∀ a ∈ Finset.Ioo 0 q,
      (2 * Real.sin (Real.pi * a / q)) ^ (e a)
        = (2 * Real.sin (Real.pi * ((a : ℝ) / q))) ^ (e a) := by
    intro a _; rw [mul_div_assoc]
  rw [Finset.prod_congr rfl hstep]
  have hoff : ∀ a ∈ Finset.Ioo 0 q, ¬ Nat.Coprime a q →
      (2 * Real.sin (Real.pi * ((a : ℝ) / q))) ^ (e a) = 1 := by
    intro a _ hnc
    have hz : ((e a : ℤ) : ℝ) = 0 := by
      rw [he a, e4a_char_vanishes_off_units χ hnc, neg_zero]
    have hz0 : e a = 0 := by exact_mod_cast hz
    rw [hz0, zpow_zero]
  rw [← e4a_prod_units_eq_prod_Ioo hq _ hoff]
  have hexp : ∀ u : (ZMod q)ˣ, e ((u : ZMod q).val) = - E4aChiBridge.e4a_signOf χ u := by
    intro u
    have h1 := he ((u : ZMod q).val)
    have h2 : (((u : ZMod q).val : ℕ) : ZMod q) = (u : ZMod q) := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [h2, ← E4aChiBridge.e4a_signOf_cast' χ u] at h1
    exact_mod_cast h1
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun u _ => by rw [hexp u, zpow_neg]

/-- ⭐⭐⭐ **E5a's JOIN** — `log` of the statement's product IS the real part E3 produces. -/
theorem e4a_log_P_eq_middle {q : ℕ} [NeZero q] (hq1 : 1 < q)
    (χ : DirichletCharacter ℝ q) (hprim : χ.IsPrimitive) (heven : χ (-1) = 1)
    (e : ℕ → ℤ) (he : ∀ a, (e a : ℝ) = -χ a) :
    Real.log (∏ a ∈ Finset.Ioo 0 q, (2 * Real.sin (Real.pi * a / q)) ^ (e a))
      = (gaussSum (e4a_toC χ) ZMod.stdAddChar *
          DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re := by
  rw [e4a_middle_closed hq1 χ hprim heven, e4a_middle_reindex χ heven,
    e4a_P_eq_units_prod_inv hq1 χ e he, Real.log_inv]

/-- ⭐⭐ **THE NONVANISHING.** -/
theorem e4a_middle_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q)
    (hprim : χ.IsPrimitive) (heven : χ (-1) = 1) (hsum : ∑ a : ZMod q, χ a = 0) :
    (gaussSum (e4a_toC χ) ZMod.stdAddChar *
      DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re ≠ 0 := by
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
  have hinv : (e4a_toC χ)⁻¹ = e4a_toC χ := hquad.inv
  -- the L-value is a positive real
  have hLpos : 0 < DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1 := by
    rw [hinv]
    exact Salt.SW.LFunction_apply_one_pos hne1 hquad.sq_eq_one
  have hLre : 0 < (DirichletCharacter.LFunction (e4a_toC χ)⁻¹ 1).re :=
    Complex.lt_def.mp hLpos |>.1
  -- τ is real, so the real part is the product of the real parts
  have hτim : (gaussSum (e4a_toC χ) (ZMod.stdAddChar : AddChar (ZMod q) ℂ)).im = 0 :=
    e4a_gaussSum_real (e4a_toC χ) hevC hquad
  have hτre := e4a_gaussSum_re_ne_zero (e4a_toC χ)
    ((e4a_toC_isPrimitive_iff χ).mpr hprim) hevC hquad
  rw [Complex.mul_re, hτim, zero_mul, sub_zero]
  exact mul_ne_zero hτre (ne_of_gt hLre)

end Salt.MR
