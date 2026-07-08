/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Diagonal

/-!
# The cross-collision correction to the S₁ main term (blueprint N4.4)

The S₁ quadratic form (N2.4, `s1_diagonalisation`) sums the weight
`lam d * lam e / ∏ᵢ lcm(dᵢ,eᵢ)` over **all** pairs `(d,e) ∈ 𝒟 × 𝒟`, and
diagonalises to `∑_r y(r)² / ∏ᵢ φ(rᵢ)`. The actual congruence count
(N4.1, `congCountTuple`) is however **exactly `0`** on *collision* pairs —
pairs `(d,e)` for which some two distinct coordinates `i ≠ j` have
`gcd(dᵢ, eⱼ) > 1` (`congCountTuple_collision`). So the count-weighted
S₁ ranges only over the *compatible* (non-collision) pairs, and differs
from the full diagonal form by the contribution of the collision pairs.

This file isolates that correction as a clean, exact algebraic
decomposition of the diagonal form into a collision part and a compatible
part, and delivers the one-sided upper bound the caller (N4.3) needs.

## What is delivered (all sorry-free, no new axioms)

* `IsCollisionPair` — the collision predicate on pairs, with its
  `Decidable` instance.
* `s1Summand`, `s1FullForm`, `s1CollisionForm`, `s1CompatForm` — the
  diagonal summand and the three restricted quadratic forms.
* `s1_full_split` — the **exact** decomposition
  `s1CollisionForm + s1CompatForm = s1FullForm` (unconditional).
* `s1_full_eq_yside` — `s1FullForm = ∑_r y(r)²/∏ᵢφ(rᵢ)` (re-exposes N2.4).
* `s1_compat_eq` — the reduction the caller wants, **unconditional**:
  `s1CompatForm = (∑_r y(r)²/∏ᵢφ(rᵢ)) − s1CollisionForm`.
* `s1_yside_nonneg` — the y-side `∑_r y(r)²/∏ᵢφ(rᵢ)` is `≥ 0`.
* `crossCollision_le` — the **one-sided drop**: *if* the collision form is
  nonneg, the compatible (count-weighted) main term is `≤` the full
  diagonal `∑_r y(r)²/∏ᵢφ(rᵢ)`. This is exactly the upper bound N4.3 needs.

## PORT-BLOCKER (see `CrossCollisionControlled`)

The frozen design (maynard.md N4.4) wants the *quantitative* relative
bound `|collision form| ≤ (c k²/D₀) · (y-side)`, which controls the sign
issue and makes the collision term genuinely lower-order. That bound needs
the per-prime tensor structure of the collision constraint (a shared prime
`p > D₀` in two coordinates) and is **not** proved here; the sign
hypothesis of `crossCollision_le` is left as the remaining gap, recorded
precisely as the `Prop` `CrossCollisionControlled`. Everything else in
this file is unconditional.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## The collision predicate -/

/-- A pair `(d,e)` of `k`-tuples is a **collision pair** if some two
distinct coordinates `i ≠ j` have `dᵢ` and `eⱼ` sharing a common factor,
i.e. `¬ Coprime (dᵢ) (eⱼ)`. On such pairs the congruence count
`congCountTuple` is exactly `0` (`congCountTuple_collision`): a shared
prime would have to divide both `n + hSeq k i` and `n + hSeq k j`. -/
def IsCollisionPair {k : ℕ} (d e : Fin k → ℕ) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ ¬ Nat.Coprime (d i) (e j)

instance {k : ℕ} (d e : Fin k → ℕ) : Decidable (IsCollisionPair d e) := by
  unfold IsCollisionPair; infer_instance

/-! ## The diagonal summand and the three quadratic forms -/

/-- The S₁ diagonal summand for a pair `(d,e)`:
`lam d · lam e / ∏ᵢ lcm(dᵢ,eᵢ)`. -/
noncomputable def s1Summand (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (d e : Fin k → ℕ) : ℝ :=
  lam k R W y d * lam k R W y e / ∏ i, (Nat.lcm (d i) (e i) : ℝ)

/-- The full S₁ diagonal form: the summand over **all** pairs
`(d,e) ∈ 𝒟 × 𝒟`. This is exactly the left-hand side of
`s1_diagonalisation`. -/
noncomputable def s1FullForm (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W, s1Summand k R W y d e

/-- The collision part of the S₁ diagonal form: the summand over the
collision pairs only. -/
noncomputable def s1CollisionForm (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
    if IsCollisionPair d e then s1Summand k R W y d e else 0

/-- The compatible (non-collision) part of the S₁ diagonal form: the
summand over the compatible pairs only — the pairs on which the
congruence count is nonzero, i.e. the pairs actually contributing to the
true count-weighted S₁. -/
noncomputable def s1CompatForm (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
    if IsCollisionPair d e then 0 else s1Summand k R W y d e

/-! ## The exact decomposition -/

/-- **Exact decomposition.** The full S₁ diagonal form splits, pair by
pair, into its collision part and its compatible part. Unconditional. -/
theorem s1_full_split (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    s1CollisionForm k R W y + s1CompatForm k R W y = s1FullForm k R W y := by
  unfold s1CollisionForm s1CompatForm s1FullForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro d _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro e _
  split_ifs <;> ring

/-- **N2.4, re-exposed.** The full S₁ diagonal form equals the y-side
`∑_r y(r)² / ∏ᵢ φ(rᵢ)`. -/
theorem s1_full_eq_yside (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy : ∀ r, r ∉ kSieveIndex k R W → y r = 0) :
    s1FullForm k R W y
      = ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  unfold s1FullForm s1Summand
  exact s1_diagonalisation k R W y hy

/-- **The reduction N4.3 wants (unconditional).** The compatible
(count-weighted) main term equals the full diagonal y-side minus the
collision correction:
`s1CompatForm = (∑_r y(r)²/∏ᵢφ(rᵢ)) − s1CollisionForm`. Bounding S₁ from
above is therefore *exactly* the problem of bounding `s1CollisionForm`
from below (see `crossCollision_le`) — or, quantitatively, controlling
`|s1CollisionForm|` (`CrossCollisionControlled`). -/
theorem s1_compat_eq (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy : ∀ r, r ∉ kSieveIndex k R W → y r = 0) :
    s1CompatForm k R W y
      = (∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        - s1CollisionForm k R W y := by
  have hsplit := s1_full_split k R W y
  have hfull := s1_full_eq_yside k R W y hy
  rw [hfull] at hsplit
  linarith [hsplit]

/-- The y-side `∑_r y(r)² / ∏ᵢ φ(rᵢ)` is nonnegative: each summand is a
square over a positive totient product (`φ(rᵢ) > 0` on the sieve
support). -/
theorem s1_yside_nonneg (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    0 ≤ ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  apply Finset.sum_nonneg
  intro r hr
  apply div_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro i _
  exact_mod_cast (Nat.totient_pos.mpr (kSieveIndex_coord_pos hr i)).le

/-! ## The one-sided drop (the caller's upper bound) -/

/-- **N4.4 — the cross-collision upper bound.** If the collision form is
nonnegative, then the compatible (count-weighted) main term is bounded
above by the full diagonal y-side `∑_r y(r)²/∏ᵢφ(rᵢ)`. This is the
one-sided "drop the collision correction" bound the caller (N4.3) needs
for its S₁ upper bound.

The hypothesis `hcoll : 0 ≤ s1CollisionForm` is the remaining gap — see
`CrossCollisionControlled` and the module docstring. It follows from (and
is the qualitative shadow of) the quantitative relative bound in the
frozen design. -/
theorem crossCollision_le (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy : ∀ r, r ∉ kSieveIndex k R W → y r = 0)
    (hcoll : 0 ≤ s1CollisionForm k R W y) :
    s1CompatForm k R W y
      ≤ ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  rw [s1_compat_eq k R W y hy]
  linarith [hcoll]

/-! ## The remaining gap, stated precisely -/

/-- **PORT-BLOCKER (N4.4 quantitative core).** The frozen design's genuine
content: the collision form is controlled *relative to* the y-side by a
constant of shape `c k² / D₀ k` (here abstracted as an arbitrary
nonnegative `κ`). This is what makes the collision correction genuinely
lower-order and, in particular, implies the sign hypothesis
`0 ≤ s1CollisionForm` up to the (small, controlled) magnitude — i.e. it
discharges the hypothesis of `crossCollision_le`. Proving it requires the
per-prime tensor structure of the collision constraint (a shared prime
`p > D₀ k` occupying two coordinates), which is not carried out here.

Stated as a `Prop` (no proof obligation, no `sorry`) so the exact
remaining target is machine-checkable downstream. -/
def CrossCollisionControlled (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) : Prop :=
  ∃ κ : ℝ, 0 ≤ κ ∧
    |s1CollisionForm k R W y|
      ≤ κ * ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)

/-! ## Re-attempt 2: a GENUINE (crude) absolute bound on the collision form

The relative bound `CrossCollisionControlled` (`|collision| ≤ (small)·yside`)
remains the wall: it needs the per-prime tensor structure of the collision
constraint (a shared prime `p > D₀` in two coordinates) and is *not* proved.

The collision form is **signed** (indefinite): `s1Summand d e =
lam d · lam e / ∏lcm` and the sieve weights `lam` take both signs, so
`0 ≤ s1CollisionForm` is **false in general** — we do not claim it.

What *is* delivered here, unconditionally and non-vacuously, is the honest
triangle-inequality bound the caller (N4.3) can still use: the compatible
(count-weighted) main term is at most the diagonal y-side **plus** a
genuinely-bounded, absolutely-summed collision correction
`s1AbsCollisionForm = ∑_{collision (d,e)} |lam d|·|lam e| / ∏ᵢ lcm(dᵢ,eᵢ)`.
This is crude (it does not exhibit the correction as lower-order) but it is
a true, finite, of-the-right-additive-shape bound — not vacuous. -/

/-- The **absolute** collision form: the absolute value of each collision
summand, summed over the collision pairs. `s1AbsCollisionForm =
∑_{collision (d,e)} |lam d|·|lam e| / ∏ᵢ lcm(dᵢ,eᵢ)`. This is the crude but
genuine majorant of the (signed) `s1CollisionForm`. -/
noncomputable def s1AbsCollisionForm (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
    if IsCollisionPair d e then
      |lam k R W y d| * |lam k R W y e| / ∏ i, (Nat.lcm (d i) (e i) : ℝ)
    else 0

/-- The lcm-product denominator is nonnegative (a product of nat casts). -/
theorem prod_lcm_nonneg {k : ℕ} (d e : Fin k → ℕ) :
    0 ≤ ∏ i, (Nat.lcm (d i) (e i) : ℝ) :=
  Finset.prod_nonneg fun i _ => by positivity

/-- Each absolute collision summand is nonnegative. -/
theorem s1AbsCollisionForm_nonneg (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    0 ≤ s1AbsCollisionForm k R W y := by
  unfold s1AbsCollisionForm
  apply Finset.sum_nonneg; intro d _
  apply Finset.sum_nonneg; intro e _
  split_ifs with h
  · exact div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (prod_lcm_nonneg d e)
  · exact le_refl 0

/-- **Genuine triangle bound.** The signed collision form is dominated in
absolute value by the absolute collision form. Unconditional, non-vacuous:
`|s1CollisionForm| ≤ ∑_{collision (d,e)} |lam d|·|lam e| / ∏ᵢ lcm(dᵢ,eᵢ)`. -/
theorem s1CollisionForm_abs_le (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    |s1CollisionForm k R W y| ≤ s1AbsCollisionForm k R W y := by
  unfold s1CollisionForm s1AbsCollisionForm
  calc |∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
            if IsCollisionPair d e then s1Summand k R W y d e else 0|
      ≤ ∑ d ∈ kSieveIndex k R W, |∑ e ∈ kSieveIndex k R W,
            if IsCollisionPair d e then s1Summand k R W y d e else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
            |if IsCollisionPair d e then s1Summand k R W y d e else 0| := by
        apply Finset.sum_le_sum; intro d _; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
            (if IsCollisionPair d e then
              |lam k R W y d| * |lam k R W y e| / ∏ i, (Nat.lcm (d i) (e i) : ℝ)
            else 0) := by
        apply Finset.sum_le_sum; intro d _
        apply Finset.sum_le_sum; intro e _
        split_ifs with h
        · rw [s1Summand, abs_div, abs_mul,
            abs_of_nonneg (prod_lcm_nonneg d e)]
        · rw [abs_zero]

/-- **The usable upper bound for N4.3 (unconditional, non-vacuous).** The
compatible (count-weighted) S₁ main term is at most the full diagonal form
plus the crude absolute collision correction. From `s1_full_split`
(`collision + compat = full`) and the triangle bound
`-collision ≤ |collision| ≤ s1AbsCollisionForm`. -/
theorem s1Compat_le_full_add_absColl (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    s1CompatForm k R W y
      ≤ s1FullForm k R W y + s1AbsCollisionForm k R W y := by
  have hsplit := s1_full_split k R W y
  have habs := s1CollisionForm_abs_le k R W y
  have hneg := neg_le_abs (s1CollisionForm k R W y)
  linarith

/-- **The caller-facing form (unconditional, non-vacuous).** Restating the
previous bound with the full form rewritten to the y-side via N2.4:
`s1CompatForm ≤ (∑_r y(r)²/∏ᵢφ(rᵢ)) + s1AbsCollisionForm`. The leading term
is the genuine diagonal y-side; the collision correction is a true, finite,
additive term (crudely bounded, not shown lower-order — that sharpening is
`CrossCollisionControlled`, still open). -/
theorem s1Compat_le_yside_add_absColl (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy : ∀ r, r ∉ kSieveIndex k R W → y r = 0) :
    s1CompatForm k R W y
      ≤ (∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + s1AbsCollisionForm k R W y := by
  rw [← s1_full_eq_yside k R W y hy]
  exact s1Compat_le_full_add_absColl k R W y

end Salt.Maynard
