/-
# The sine bridge — `2 sin(πa/q)` is `‖1 − ζ^a‖`, and its logarithms

Second module of the even-χ port (2026-08-19).  Like `EvenChiCosh` this is a
DEPENDENCY-CLOSED unit — measured, not asserted: the code-only cone of these fourteen
declarations pulls in nothing beyond itself, and **no cyclotomic field, ring of integers or
Dirichlet character appears anywhere in it.**

## What it is for

The even-χ ladder has an ANALYTIC side (an `L`-value, a Gauss sum, complex logarithms) and an
ARITHMETIC side (a real product of sines with integer exponents).  **This module is the joint**:
`‖1 − ζ^a‖ = 2 sin(πa/q)` for `0 < a < q`, together with the bookkeeping that carries it
through products, `zpow` weights, norms and real parts.

## Main results

* `e4a_step3_sin_bridge` — the bridge itself, at a natural-number index.
* `e4a_exp_pow_eq_exp` / `e4a_sin_bridge_zmod` — the same bridge at a `ZMod q` coordinate,
  which is where the character sums actually live.
* `e4a_norm_zpow_prod` / `e4a_sin_prod_eq_norm` — the bridge carried through a weighted product.
* `e4a_neg_clog_re` / `e4a_sum_clog_re` — real parts of `−log` sums; **stated over an ARBITRARY
  index type**, which is why the ladder never has to transport a sum across a bijection.
* `e4a_log_zpow_prod` / `e4a_log_eta_eq_sum` — `log` of a `zpow`-weighted product is the
  weighted sum of `log`s, again index-agnostic.
* `e4a_unit_val_div_mem` / `e4a_sin_ne_zero_at_unit` — the sine does not vanish at a unit's
  coordinate, which is the side condition every product identity above needs.
-/
import Salt.MR.Sawtooth

namespace Salt.MR

theorem e4a_step3_sin_bridge {q a : ℕ} (ha : 0 < a) (haq : a < q) :
    ‖1 - (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a‖
      = 2 * Real.sin (Real.pi * ((a : ℝ) / q)) := by
  have hq : 0 < (q : ℝ) := by
    have : 0 < q := lt_of_le_of_lt (Nat.zero_le a) haq
    exact_mod_cast this
  have hmem : ((a : ℝ) / q) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (by exact_mod_cast ha) hq
    · rw [div_lt_one hq]; exact_mod_cast haq
  have hpow : (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a
      = Complex.exp (((2 * Real.pi * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow]
  exact Salt.MR.norm_one_sub_exp hmem

#print axioms e4a_step3_sin_bridge

/-! ## PROBE 4 — THE UNIT-NESS CONTENT OF E4a, stated with no division at all

`η = ∏_{χ(a)=−1}(ζ^a−1) / ∏_{χ(a)=+1}(ζ^a−1)`.  For real χ, `Σ_a χ(a) = 0` says
EXACTLY that the two index sets have EQUAL CARDINALITY.  By probe 2 each product is
associated to the SAME power `(ζ−1)^m`, so the two products are associated to each
other — and `Associated x y` is precisely "`x` and `y` differ by a unit".

⭐ That is η's unit-ness, obtained WITHOUT forming a quotient, WITHOUT a norm
computation, and UNIFORMLY IN q — no prime-power branch.  v1 sought this through
`Norm = 1 ⇒ unit`, which is false off the integers because η is a quotient; the
associate route never leaves the ring. -/

theorem e4a_norm_zpow_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ) (e : ι → ℤ) :
    ‖∏ a ∈ S, (f a) ^ (e a)‖ = ∏ a ∈ S, ‖f a‖ ^ (e a) := by
  rw [norm_prod]
  exact Finset.prod_congr rfl fun a _ => norm_zpow _ _

/-- ⭐ **THE BRIDGE THE STATEMENT ASSEMBLY NEEDS** — the REAL sine product IS the norm of
the ALGEBRAIC product, weight for weight.  This is the join between v2 §1's statement
(real sines, ℤ exponents) and everything proved above it (cyclotomic units in `𝓞_K`). -/
theorem e4a_sin_prod_eq_norm {q : ℕ} (S : Finset ℕ) (e : ℕ → ℤ)
    (hS : ∀ a ∈ S, 0 < a ∧ a < q) :
    ∏ a ∈ S, (2 * Real.sin (Real.pi * ((a : ℝ) / q))) ^ (e a)
      = ‖∏ a ∈ S, (1 - (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a) ^ (e a)‖ := by
  rw [e4a_norm_zpow_prod]
  refine (Finset.prod_congr rfl fun a ha => ?_).symm
  obtain ⟨ha0, haq⟩ := hS a ha
  rw [e4a_step3_sin_bridge ha0 haq]

#print axioms e4a_norm_zpow_prod
#print axioms e4a_sin_prod_eq_norm

/-! ## PROBE 36 — GAP 4 CLOSED, grafted from the helm's executor, and JOINTLY VERIFIED

⭐ It went past the ask and INTO my spine: not just `σζ = ζ^{b.val}` but `hgal` itself, and
then `e4a_spine` APPLIED with `hgal` discharged.  Its mutation control deleted the swap arm
and got a type mismatch AT THE `e4a_spine` CALL SITE — proving the spine genuinely CONSUMES
the lemma rather than elaborating past it.

⛔ AND IT FOUND AN EIGHTH INTERFACE ON THE WAY IN: there was no `e4a_fibre_fix'` (the −1
fibre at `χ(b) = +1`), hence no fixed-arm quotient — probe 25 fixed the NUMERATOR and said
nothing about the denominator.  ***That is probe 26's own finding, one arm over, and I did
not run probe 26's lesson against probe 25's other arm.***

⚠️ Grafted against my CURRENT file after verifying their base (seat `7d2fd48`, 1266 lines)
is a strict PREFIX of it — checked by `diff`, not assumed, because they built on a file
three commits behind. -/

/-! ### PROBE 33 — ⭐ THE σ ↔ b LINK

`IsCyclotomicExtension.Rat.galEquivZMod` (`NumberField/Cyclotomic/Galois.lean:60`) is the
isomorphism `Gal(K/ℚ) ≃* (ZMod n)ˣ`; `galEquivZMod_apply_of_pow_eq` (:63) is the statement
that it does what its name says — `σ x = x ^ (galEquivZMod n K σ).val.val` for any `x` with
`x ^ n = 1`.  ζ is such an `x` by `IsPrimitiveRoot.pow_eq_one`.

⚠️ Note what the hypothesis `x ^ n = 1` costs and does NOT cost: math's probe-20 docstring
is right that it forbids applying this lemma to η.  It does not forbid applying it to ζ,
which is all the link needs — the transport to η goes through the product, below. -/

theorem e4a_neg_clog_re (z : ℂ) : (-(Complex.log z)).re = -Real.log ‖z‖ := by
  rw [Complex.neg_re, Complex.log_re]

/-- The real part of a real-coefficient sum of `−log`s IS the negated weighted sum of
`log ‖·‖` — the shape E3's right-hand side has once χ is ℤ-valued through the sign map. -/
theorem e4a_sum_clog_re {ι : Type*} (S : Finset ι) (c : ι → ℤ) (w : ι → ℂ) :
    (∑ a ∈ S, ((c a : ℂ) * (-(Complex.log (w a))))).re
      = ∑ a ∈ S, (c a : ℝ) * (-Real.log ‖w a‖) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ((c a : ℂ)) = (((c a : ℝ) : ℂ)) by push_cast; ring,
    Complex.re_ofReal_mul, e4a_neg_clog_re]

/-- ⭐ **PIECE (3), AT η's FACTORS** — the real part of the character sum is the negated
weighted sum of `log (2 sin(πa/q))`, which `e4a_log_eta_eq_sum` identifies with `−log η`. -/
theorem e4a_sum_clog_re_sin {q : ℕ} (S : Finset ℕ) (c : ℕ → ℤ)
    (hS : ∀ a ∈ S, 0 < a ∧ a < q) :
    (∑ a ∈ S, ((c a : ℂ) *
        (-(Complex.log (1 - (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ a))))).re
      = ∑ a ∈ S, (c a : ℝ) * (-Real.log (2 * Real.sin (Real.pi * ((a : ℝ) / q)))) := by
  rw [e4a_sum_clog_re]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha0, haq⟩ := hS a ha
  rw [e4a_step3_sin_bridge ha0 haq]

#print axioms e4a_neg_clog_re
#print axioms e4a_sum_clog_re
#print axioms e4a_sum_clog_re_sin

/-! ############################################################################
## ⭐ E5a MIDDLE, PIECE (2) — τ(χ) IS REAL AT AN EVEN QUADRATIC χ
GRAFTED 2026-08-19 from `salt/ScratchE4aTauReal-exec.lean` (untracked, mortal),
proved by an Opus executor in 2 attempts.  The exec file was STANDALONE — its own
imports, no shared body with this file — so the graft is a pure append and the
"their base may lag mine" prefix hazard does not arise here.  Verified before the
graft: 0 name collisions on all 7 theorems.

REPRICE HONOURED: only REALITY is proved.  The SIGN (τ = ±√q) is deliberately NOT
proved and is NOT needed — `cosh` is even, so `e4a_cosh_of_pm` /
`e4a_cosh_integer_of_pm` absorb it downstream.  NO √q appears below.

⭐ CONSUME `e4a_gaussSum_real` (even + quadratic).  `hprim` IS NOT NEEDED — the
brief's `_of_primitive` variant is kept only so the requested name exists, and is
the WEAKER-HYPOTHESIS rule pointing the other way: take the one that asks less.

📌 KEY SURFACE: `star_gaussSum_eq` (Mathlib/NumberTheory/GaussSum.lean:89) —
zero call sites in mathlib or salt before this.
⚠ MATHLIB GAP: `mul_gaussSum_inv_eq_gaussSum` (GaussSum.lean:123) packages exactly
`χ(-1) * gaussSum χ ψ⁻¹ = gaussSum χ ψ` but sits under `[Field R]` GRATUITOUSLY —
its proof uses no field structure — so it is UNAVAILABLE at `ZMod q` for composite
`q`.  Re-derived below at `[CommRing R] [Fintype R]`.  A 1-line upstream PR.
############################################################################ -/


open Complex

theorem e4a_log_zpow_prod {ι : Type*} (S : Finset ι) (g : ι → ℝ) (e : ι → ℤ)
    (hg : ∀ a ∈ S, g a ≠ 0) :
    Real.log (∏ a ∈ S, (g a) ^ (e a)) = ∑ a ∈ S, (e a : ℝ) * Real.log (g a) := by
  rw [Real.log_prod (fun a ha => zpow_ne_zero _ (hg a ha))]
  exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _

/-- ⭐ **AT η** — with the exponent `e a = −χ(a)`, `log η` IS the negated character sum of
`log (2 sin(πa/q))`.  That is precisely the real part of E3's right-hand side, so this is
the join between the ANALYTIC identity and the REAL product the statement names. -/
theorem e4a_log_eta_eq_sum {q : ℕ} (S : Finset ℕ) (e : ℕ → ℤ)
    (hS : ∀ a ∈ S, 0 < a ∧ a < q) :
    Real.log (∏ a ∈ S, (2 * Real.sin (Real.pi * ((a : ℝ) / q))) ^ (e a))
      = ∑ a ∈ S, (e a : ℝ) * Real.log (2 * Real.sin (Real.pi * ((a : ℝ) / q))) := by
  refine e4a_log_zpow_prod S _ e (fun a ha => ?_)
  obtain ⟨ha0, haq⟩ := hS a ha
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := lt_trans ha0 haq
    exact_mod_cast this
  have h0 : 0 < Real.pi * ((a : ℝ) / (q : ℝ)) := by
    have hA : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
    have : (0 : ℝ) < (a : ℝ) / (q : ℝ) := div_pos hA hqR
    positivity
  have h1 : Real.pi * ((a : ℝ) / (q : ℝ)) < Real.pi := by
    have hlt : ((a : ℝ) / (q : ℝ)) < 1 := by rw [div_lt_one hqR]; exact_mod_cast haq
    nlinarith [Real.pi_pos]
  have := Real.sin_pos_of_pos_of_lt_pi h0 h1
  positivity

#print axioms e4a_log_zpow_prod
#print axioms e4a_log_eta_eq_sum

/-! ## PROBE 48 — ⭐ E3b REPRICED: the Gauss sum's SIGN is absorbed, only its REALITY is needed

Composition control on the decomposition I named last tick.  Piece (2) was "τ(χ) = √q at
even real primitive χ" — the ladder's E3b — and I measured it: **NOT LANDED** (0 files).
Only the MODULUS is landed (`gaussSum_normSq_of_primitive`, 1 file).

⭐ BUT E3b SPLITS, AND ONLY HALF OF IT IS NEEDED.  `τ = ±√q` propagates to
`√q · Re L = ±(−log η)`, and **`cosh` is EVEN**, so `2 cosh(√q · Re L) = η + η⁻¹` **either
way**.  ⇒ ***The SIGN of the Gauss sum is FREE — absorbed by the same evenness that makes
E5a sign-free.  What E3b must still supply is that τ is REAL (so `Re(S/τ) = ±Re(S)/√q`),
not WHICH real it is.***

That is the ladder's own claim ("sign-free — dodges the Gauss sign theorem") sharpened from
a slogan into a decomposition: the theorem it dodges is the SIGN theorem specifically, and
the modulus + reality it still needs are cheaper and one of them is landed. -/

/-- **GAP C** — a power of the primitive root IS the exponential of the scaled angle. -/
theorem e4a_exp_pow_eq_exp {q : ℕ} (v : ℕ) :
    (Complex.exp (((2 * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ v
      = Complex.exp ((((2 * Real.pi * ((v : ℝ) / q)) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A unit of `ZMod q` is nonzero when `q > 1` (the un-negated companion of
`e4a_unit_neg_ne_zero`). -/
theorem e4a_unit_ne_zero_aux {q : ℕ} (hq : 1 < q) (a : (ZMod q)ˣ) : (a : ZMod q) ≠ 0 := by
  haveI : Fact (1 < q) := ⟨hq⟩
  intro h
  have hu : IsUnit (0 : ZMod q) := h ▸ a.isUnit
  rw [isUnit_zero_iff] at hu
  exact zero_ne_one hu

/-! ### DISCHARGING `e4a_eta_sum_integer_final`'s TWO HYPOTHESES from the ruled statement

The ruled statement supplies `hsum` and `hprim`; the culmination lemma wants `χ ≠ 1` and a
nonvanishing product.  Both come out of what the statement already carries. -/


/-- A unit of `ZMod q` is nonzero, hence so is its negative — `q > 1` is the whole content
(at `q = 1` the ring is trivial and every `val` is `0`). -/
theorem e4a_unit_neg_ne_zero {q : ℕ} (hq : 1 < q) (a : (ZMod q)ˣ) : (-(a : ZMod q)) ≠ 0 := by
  haveI : Fact (1 < q) := ⟨hq⟩
  rw [neg_ne_zero]
  intro h
  have hu : IsUnit (0 : ZMod q) := h ▸ a.isUnit
  rw [isUnit_zero_iff] at hu
  exact zero_ne_one hu

/-- A unit's negated coordinate lands strictly inside `(0,1)` after division by `q`. -/
theorem e4a_unit_val_div_mem {q : ℕ} [NeZero q] (hq : 1 < q) (a : (ZMod q)ˣ) :
    (((-(a : ZMod q)).val : ℝ) / q) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos : 0 < (-(a : ZMod q)).val := ZMod.val_pos.mpr (e4a_unit_neg_ne_zero hq a)
  have hlt : (-(a : ZMod q)).val < q := ZMod.val_lt _
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : (0 : ℝ) < ((-(a : ZMod q)).val : ℝ) := by exact_mod_cast hpos
  have h2 : (((-(a : ZMod q)).val : ℝ)) < (q : ℝ) := by exact_mod_cast hlt
  exact ⟨by positivity, (div_lt_one hqR).mpr h2⟩

/-- Hence `2 sin(π·v/q) ≠ 0` — the side condition `e4a_log_zpow_prod` asks for. -/
theorem e4a_sin_ne_zero_at_unit {q : ℕ} [NeZero q] (hq : 1 < q) (a : (ZMod q)ˣ) :
    2 * Real.sin (Real.pi * (((-(a : ZMod q)).val : ℝ) / q)) ≠ 0 := by
  have := Salt.MR.sin_pi_mul_pos (e4a_unit_val_div_mem hq a)
  positivity

/-- The sin bridge, stated at a `ZMod q` coordinate instead of a raw `ℕ`. -/
theorem e4a_sin_bridge_zmod {q : ℕ} [NeZero q] {x : ZMod q} (hx : x ≠ 0) :
    ‖1 - Complex.exp ((((2 * Real.pi * ((x.val : ℝ) / q)) : ℝ) : ℂ) * Complex.I)‖
      = 2 * Real.sin (Real.pi * ((x.val : ℝ) / q)) := by
  rw [← e4a_exp_pow_eq_exp]
  exact e4a_step3_sin_bridge (ZMod.val_pos.mpr hx) (ZMod.val_lt x)

end Salt.MR
