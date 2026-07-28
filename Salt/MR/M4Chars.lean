/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ChiFloor
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# M4-3 — the character expansion and THE CONJUGATION BRIDGE (`M4Chars`)

The M4 ladder's residue-class leg (`M4-2`) hands the chain a sum restricted to a single
residue class `m ≡ b₀ (mod q₀)` with `b₀` a unit; the quality leg (`M4-6`, and behind it
`ChiFloor`'s H1 exit) speaks only the datum

`lamChi χ = fun n => lam n * conj (χ n)`   (`ChiFloor.lean`, the `λ·χ̄` datum)

— the **`χ̄`-twisted** `λ`.  Character expansion of the indicator therefore has to land in
that orientation, or the two legs speak opposite conjugations and nothing composes.  This
file fixes the orientation ONCE.

## The orientation, stated plainly

mathlib's orthogonality relation (`DirichletCharacter.sum_char_inv_mul_char_eq`) reads

`∑_χ χ(a⁻¹)·χ(b) = if a = b then φ(n) else 0`   (`a` a unit),

whose textbook reading `1_{m ≡ b₀} = (1/φ)·∑_χ χ̄(b₀)·χ(m)` puts the conjugate on the
COEFFICIENT and leaves the per-`χ` datum as `λ·χ` — the WRONG twist for `lamChi`.  Taking
complex conjugates of the whole relation (legitimate: the right-hand side is a real
natural-number cast) flips it to

`∑_χ χ(a)·conj (χ b) = if a = b then φ(n) else 0`,

and THIS is the orientation the corpus needs.  The landed decomposition is therefore

`λ(m)·1_{m ≡ b₀ (mod q₀)} = (1/φ(q₀))·∑_χ χ(b₀)·lamChi χ m`,

with the coefficient `χ(b₀)` **unconjugated** and the per-`χ` object exactly `lamChi χ`
(`= λ·χ̄`).  The coefficient is unimodular (`norm_chi_of_isUnit`), which is all the
downstream trivial bound needs.

## Contents

* `conj_chi_eq_inv`, `conj_chi_eq_invChar` — `conj (χ a) = (χ a)⁻¹ = χ⁻¹ a`, at EVERY `a`
  (no unit hypothesis: at a non-unit both sides are `0`).
* `chi_inv_eq_conj_chi` — **THE CONJUGATION BRIDGE**: `χ (a⁻¹) = conj (χ a)` for `a` a unit
  of `ZMod q`.  Fixed here once; `Salt.SW.Defs.psi1_fold` and `Salt.BV.MaxReduction` each
  re-derive this inline, and future consumers should cite this name instead.
* `sum_conj_chi_mul_chi` — orthogonality with the conjugate on the COEFFICIENT (the
  textbook orientation; recorded for completeness, NOT the one the M4 chain consumes).
* `sum_chi_mul_conj_chi` — orthogonality with the conjugate on the DATUM: the
  `lamChi` orientation.
* `indicator_eq_inv_totient_sum` — the indicator extraction, valid at EVERY `m : ℕ` with no
  coprimality hypothesis (see "the non-unit branch" below).
* `weight_indicator_eq_inv_totient_sum` — the same at a general arithmetic weight `w`.
* `lam_indicator_eq_lamChi_sum` / `lam_modEq_indicator_eq_lamChi_sum` — **the M4-3
  decomposition**, in `ZMod q` and in `Nat.ModEq` form.
* `sum_weight_residue_eq`, `sum_lam_residue_eq` — the `Finset`-summed consumer shape:
  a residue-class sum becomes `(1/φ(q))·∑_χ χ(b₀)·(the `lamChi χ` sum)`.
* `norm_sum_lam_residue_le` — the trivial bound that the M4-4 dyadic cut applies to the
  decomposition, with the unimodular coefficient discharged.
* `norm_chi_of_isUnit`, `totient_cast_ne_zero` — the side facts (`‖χ b₀‖ = 1`, `φ(q) ≠ 0`).

## The non-unit branch (the honest statement)

The extraction needs NO `Nat.Coprime q m` hypothesis.  If `(m : ZMod q)` is not a unit then
every character kills it (`MulChar.map_nonunit`, which applies to the principal character
too), so the character side is `0`; and the arithmetic side is `0` as well, because
`b₀` IS a unit and hence `(m : ZMod q) ≠ b₀`.  The two branches agree, so the identity is
stated for all `m` at once — the `if` is over `(m : ZMod q) = b₀`, a test that lives in
`ZMod q`, not in `ℕ`.
-/

namespace Salt.MR

open scoped BigOperators

section Bridge

variable {q : ℕ}

/-! ## 1. The conjugation bridge -/

/-- Conjugation of a character value is inversion of that value, at EVERY `a : ZMod q`.
At a non-unit `a` both sides are `0` (`MulChar.map_nonunit`, `inv_zero`), so no unit
hypothesis is needed.  Route: `MulChar.star_apply'` (the values are roots of unity) followed
by `MulChar.inv_apply_eq_inv'`. -/
theorem conj_chi_eq_inv (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    (starRingEnd ℂ) (χ a) = (χ a)⁻¹ := by
  rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply_eq_inv']

/-- The character-level form of `conj_chi_eq_inv`: conjugating values is applying the
inverse character. -/
theorem conj_chi_eq_invChar (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    (starRingEnd ℂ) (χ a) = (χ⁻¹ : DirichletCharacter ℂ q) a := by
  rw [starRingEnd_apply, MulChar.star_apply']

/-- **THE CONJUGATION BRIDGE.**  For `a` a unit of `ZMod q` and any Dirichlet character `χ`
mod `q` over `ℂ`, `χ (a⁻¹) = conj (χ a)`.

Route: `χ(a⁻¹)·χ(a) = χ(a⁻¹·a) = χ(1) = 1` (`ZMod.inv_mul_eq_one_of_isUnit`), so `χ(a⁻¹)` is
the multiplicative inverse of `χ(a)` in `ℂ`; and `conj (χ a)` is that same inverse because
`χ(a)` is a root of unity (`conj_chi_eq_inv`).  This is the identity that
`Salt.SW.Defs.psi1_fold` derives inline as `conj_a`; it is fixed here once. -/
theorem chi_inv_eq_conj_chi {a : ZMod q} (ha : IsUnit a) (χ : DirichletCharacter ℂ q) :
    χ a⁻¹ = (starRingEnd ℂ) (χ a) := by
  have hmul : χ a⁻¹ * χ a = 1 := by
    rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl, map_one]
  rw [conj_chi_eq_inv]
  exact eq_inv_of_mul_eq_one_left hmul

/-- The values of a Dirichlet character at a unit are unimodular — the `IsUnit`-hypothesis
repackaging of `DirichletCharacter.unit_norm_eq_one`.  This is what makes the coefficient
`χ b₀` of the M4-3 decomposition harmless in the trivial bound. -/
theorem norm_chi_of_isUnit {a : ZMod q} (ha : IsUnit a) (χ : DirichletCharacter ℂ q) :
    ‖χ a‖ = 1 := by
  have h := χ.unit_norm_eq_one ha.unit
  rwa [IsUnit.unit_spec] at h

/-! ## 2. Totient positivity (the divisor in the extraction) -/

variable (q) in
/-- `φ(q) ≠ 0` as a complex number, for `q ≠ 0` — the side condition for dividing by the
number of characters. -/
theorem totient_cast_ne_zero [NeZero q] : (q.totient : ℂ) ≠ 0 := by
  have hpos : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  exact_mod_cast hpos.ne'

variable (q) in
/-- `φ(q) > 0` as a real number, for `q ≠ 0`. -/
theorem totient_cast_pos [NeZero q] : (0 : ℝ) < (q.totient : ℝ) := by
  have hpos : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  exact_mod_cast hpos

/-! ## 3. Orthogonality in both orientations -/

variable [NeZero q]

/-- Orthogonality with the conjugate on the COEFFICIENT — mathlib's
`DirichletCharacter.sum_char_inv_mul_char_eq` rewritten through the bridge.  This is the
textbook orientation `1_{m ≡ b} = (1/φ)·∑_χ χ̄(b)·χ(m)`; its per-`χ` datum is `λ·χ`, the
WRONG twist for `lamChi`.  Recorded for completeness and as the input to
`sum_chi_mul_conj_chi`. -/
theorem sum_conj_chi_mul_chi {a : ZMod q} (ha : IsUnit a) (b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) * χ b
      = if a = b then (q.totient : ℂ) else 0 := by
  calc ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) * χ b
      = ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ b :=
        Finset.sum_congr rfl fun χ _ => by rw [chi_inv_eq_conj_chi ha χ]
    _ = if a = b then (q.totient : ℂ) else 0 :=
        DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) ha b

/-- **Orthogonality in the `lamChi` orientation.**  For `a` a unit of `ZMod q` and any
`b : ZMod q`,

`∑_χ χ(a)·conj (χ b) = if a = b then φ(q) else 0`.

The conjugate sits on the DATUM slot `b`, which is where `lamChi χ = λ·χ̄` needs it.  Route:
conjugate `sum_conj_chi_mul_chi` termwise — the right-hand side is a cast of a natural
number, hence fixed by conjugation. -/
theorem sum_chi_mul_conj_chi {a : ZMod q} (ha : IsUnit a) (b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a * (starRingEnd ℂ) (χ b)
      = if a = b then (q.totient : ℂ) else 0 := by
  have key : (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ a) * χ b)
      = ∑ χ : DirichletCharacter ℂ q, χ a * (starRingEnd ℂ) (χ b) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun χ _ => by rw [map_mul, Complex.conj_conj]
  rw [← key, sum_conj_chi_mul_chi ha b]
  by_cases hab : a = b
  · rw [if_pos hab]
    exact map_natCast (starRingEnd ℂ) q.totient
  · rw [if_neg hab, map_zero]

/-! ## 4. The indicator extraction -/

/-- **The indicator extraction.**  For `b₀` a unit of `ZMod q` and ANY `m : ℕ`,

`1_{(m : ZMod q) = b₀} = (1/φ(q))·∑_χ χ(b₀)·conj (χ m)`.

No coprimality hypothesis on `m`: at a non-unit `m` every character vanishes
(`MulChar.map_nonunit`) and the indicator is `0` as well, since `b₀` is a unit.  The
equality test lives in `ZMod q`. -/
theorem indicator_eq_inv_totient_sum {b₀ : ZMod q} (hb : IsUnit b₀) (m : ℕ) :
    (if (m : ZMod q) = b₀ then (1 : ℂ) else 0)
      = (q.totient : ℂ)⁻¹
          * ∑ χ : DirichletCharacter ℂ q, χ b₀ * (starRingEnd ℂ) (χ (m : ZMod q)) := by
  rw [sum_chi_mul_conj_chi hb ((m : ℕ) : ZMod q)]
  by_cases hab : b₀ = ((m : ℕ) : ZMod q)
  · rw [if_pos hab, if_pos hab.symm, inv_mul_cancel₀ (totient_cast_ne_zero q)]
  · rw [if_neg hab, if_neg fun h => hab h.symm, mul_zero]

/-- **The indicator extraction at a general arithmetic weight.**  For `b₀` a unit and any
`w : ℕ → ℂ`, `m : ℕ`,

`w(m)·1_{(m : ZMod q) = b₀} = (1/φ(q))·∑_χ χ(b₀)·(w(m)·conj (χ m))`.

The per-`χ` object is `w·χ̄` — the `χ̄`-twisted weight, i.e. the `lamChi` shape at `w := lam`. -/
theorem weight_indicator_eq_inv_totient_sum {b₀ : ZMod q} (hb : IsUnit b₀) (w : ℕ → ℂ)
    (m : ℕ) :
    (if (m : ZMod q) = b₀ then w m else 0)
      = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ b₀ * (w m * (starRingEnd ℂ) (χ (m : ZMod q))) := by
  have hsplit : (if (m : ZMod q) = b₀ then w m else 0)
      = w m * (if (m : ZMod q) = b₀ then (1 : ℂ) else 0) := by
    by_cases hab : ((m : ℕ) : ZMod q) = b₀
    · rw [if_pos hab, if_pos hab, mul_one]
    · rw [if_neg hab, if_neg hab, mul_zero]
  rw [hsplit, indicator_eq_inv_totient_sum hb m, mul_comm (w m), mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun χ _ => by ring

/-! ## 5. The M4-3 decomposition, in `lamChi`'s orientation -/

/-- **THE M4-3 DECOMPOSITION.**  For `b₀` a unit of `ZMod q` and any `m : ℕ`,

`λ(m)·1_{(m : ZMod q) = b₀} = (1/φ(q))·∑_χ χ(b₀)·lamChi χ m`.

The per-`χ` object is `lamChi χ = λ·χ̄` EXACTLY as `ChiFloor` defines it, and the coefficient
`χ(b₀)` is UNCONJUGATED (unimodular, by `norm_chi_of_isUnit`).  This is the orientation the
M4-6 quality leg must speak. -/
theorem lam_indicator_eq_lamChi_sum {b₀ : ZMod q} (hb : IsUnit b₀) (m : ℕ) :
    (if (m : ZMod q) = b₀ then lam m else 0)
      = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ b₀ * lamChi χ m := by
  rw [weight_indicator_eq_inv_totient_sum hb lam m]
  congr 1

/-- The M4-3 decomposition with the residue test written in `ℕ` (`Nat.ModEq`) rather than in
`ZMod q` — the shape the arithmetic legs of the chain hand over.  `b` is a natural
representative whose residue is a unit. -/
theorem lam_modEq_indicator_eq_lamChi_sum {b : ℕ} (hb : IsUnit ((b : ℕ) : ZMod q)) (m : ℕ) :
    (if m ≡ b [MOD q] then lam m else 0)
      = (q.totient : ℂ)⁻¹
          * ∑ χ : DirichletCharacter ℂ q, χ ((b : ℕ) : ZMod q) * lamChi χ m := by
  have hiff : (m ≡ b [MOD q]) ↔ ((m : ℕ) : ZMod q) = ((b : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff m b q).symm
  rw [← lam_indicator_eq_lamChi_sum hb m]
  by_cases hmb : m ≡ b [MOD q]
  · rw [if_pos hmb, if_pos (hiff.mp hmb)]
  · rw [if_neg hmb, if_neg fun h => hmb (hiff.mpr h)]

/-! ## 6. The summed consumer shape -/

/-- **The residue-class sum, folded into character sums** (general weight).  For `b₀` a unit
and `S : Finset ℕ`,

`∑_{m ∈ S, m ≡ b₀} w(m) = (1/φ(q))·∑_χ χ(b₀)·∑_{m ∈ S} w(m)·conj (χ m)`.

The inner object is the `χ̄`-twisted weight sum — at `w := lam` it is literally
`∑_{m ∈ S} lamChi χ m`. -/
theorem sum_weight_residue_eq {b₀ : ZMod q} (hb : IsUnit b₀) (w : ℕ → ℂ) (S : Finset ℕ) :
    ∑ m ∈ S.filter (fun m => ((m : ℕ) : ZMod q) = b₀), w m
      = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ b₀ * ∑ m ∈ S, w m * (starRingEnd ℂ) (χ ((m : ℕ) : ZMod q)) := by
  rw [Finset.sum_filter]
  calc ∑ m ∈ S, (if ((m : ℕ) : ZMod q) = b₀ then w m else 0)
      = ∑ m ∈ S, (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ b₀ * (w m * (starRingEnd ℂ) (χ ((m : ℕ) : ZMod q))) :=
        Finset.sum_congr rfl fun m _ => weight_indicator_eq_inv_totient_sum hb w m
    _ = (q.totient : ℂ)⁻¹ * ∑ m ∈ S, ∑ χ : DirichletCharacter ℂ q,
          χ b₀ * (w m * (starRingEnd ℂ) (χ ((m : ℕ) : ZMod q))) := by
        rw [Finset.mul_sum]
    _ = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ∑ m ∈ S,
          χ b₀ * (w m * (starRingEnd ℂ) (χ ((m : ℕ) : ZMod q))) := by
        rw [Finset.sum_comm]
    _ = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ b₀ * ∑ m ∈ S, w m * (starRingEnd ℂ) (χ ((m : ℕ) : ZMod q)) := by
        congr 1
        exact Finset.sum_congr rfl fun χ _ => (Finset.mul_sum _ _ _).symm

/-- **The M4 consumer shape.**  The `λ`-sum over a residue class becomes `(1/φ(q))` times a
character-indexed sum whose inner objects are the `lamChi χ` sums — exactly the quantities
the `M4-6` quality leg bounds. -/
theorem sum_lam_residue_eq {b₀ : ZMod q} (hb : IsUnit b₀) (S : Finset ℕ) :
    ∑ m ∈ S.filter (fun m => ((m : ℕ) : ZMod q) = b₀), lam m
      = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ b₀ * ∑ m ∈ S, lamChi χ m := by
  rw [sum_weight_residue_eq hb lam S]
  congr 1

/-! ## 7. The trivial bound on the decomposition -/

/-- **The trivial bound.**  The coefficient `χ(b₀)` is unimodular, so the residue-class
`λ`-sum is at most `(1/φ(q))·∑_χ ‖∑_{m ∈ S} lamChi χ m‖`.  This is the form the M4-4 dyadic
cut applies to the decomposition. -/
theorem norm_sum_lam_residue_le {b₀ : ZMod q} (hb : IsUnit b₀) (S : Finset ℕ) :
    ‖∑ m ∈ S.filter (fun m => ((m : ℕ) : ZMod q) = b₀), lam m‖
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖∑ m ∈ S, lamChi χ m‖ := by
  rw [sum_lam_residue_eq hb S, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [norm_mul, norm_chi_of_isUnit hb χ, one_mul]

/-! ## 8. The `ℕ`-facing handoff (`Nat.Coprime` / `Nat.ModEq`) -/

omit [NeZero q] in
/-- The unit hypothesis from the arithmetic side's `Nat.Coprime`.  `Salt.SW.Defs` and
`Salt.BV.MaxReduction` each re-derive this inline; it is named here so the M4 legs, which
carry `Nat.Coprime q b`, can hand it over directly. -/
theorem isUnit_natCast_of_coprime {b : ℕ} (hcop : Nat.Coprime q b) :
    IsUnit ((b : ℕ) : ZMod q) :=
  (ZMod.isUnit_iff_coprime b q).mpr hcop.symm

/-- **The M4-2 → M4-3 handoff.**  A `λ`-sum over the residue class `m ≡ b (mod q)`,
with `b` coprime to `q`, becomes `(1/φ(q))·∑_χ χ(b)·(the `lamChi χ` sum over `S`)`.  Same
orientation as `sum_lam_residue_eq`; the residue test is written in `ℕ`. -/
theorem sum_lam_modEq_residue_eq {b : ℕ} (hcop : Nat.Coprime q b) (S : Finset ℕ) :
    ∑ m ∈ S.filter (fun m => m ≡ b [MOD q]), lam m
      = (q.totient : ℂ)⁻¹
          * ∑ χ : DirichletCharacter ℂ q, χ ((b : ℕ) : ZMod q) * ∑ m ∈ S, lamChi χ m := by
  have hfil : S.filter (fun m => m ≡ b [MOD q])
      = S.filter (fun m => ((m : ℕ) : ZMod q) = ((b : ℕ) : ZMod q)) :=
    Finset.filter_congr fun m _ => (ZMod.natCast_eq_natCast_iff m b q).symm
  rw [hfil, sum_lam_residue_eq (isUnit_natCast_of_coprime hcop) S]

/-- The trivial bound in the `ℕ`-facing shape — `norm_sum_lam_residue_le` with the residue
test written as `Nat.ModEq` and the unit hypothesis supplied by `Nat.Coprime`. -/
theorem norm_sum_lam_modEq_residue_le {b : ℕ} (hcop : Nat.Coprime q b) (S : Finset ℕ) :
    ‖∑ m ∈ S.filter (fun m => m ≡ b [MOD q]), lam m‖
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖∑ m ∈ S, lamChi χ m‖ := by
  have hfil : S.filter (fun m => m ≡ b [MOD q])
      = S.filter (fun m => ((m : ℕ) : ZMod q) = ((b : ℕ) : ZMod q)) :=
    Finset.filter_congr fun m _ => (ZMod.natCast_eq_natCast_iff m b q).symm
  rw [hfil]
  exact norm_sum_lam_residue_le (isUnit_natCast_of_coprime hcop) S

end Bridge

end Salt.MR
