/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# A kernel-certified counterexample to the Jacobian conjecture

This file gives a fully kernel-checked verification of the two central algebraic
claims of the counterexample announced 2026-07-20 by L. Alpöge (crediting
A. Mathew and the Fable model), preprint *"A counterexample to the Jacobian
conjecture"*, Theorem 3.1.

The polynomial map `F = (P, Q, R) : 𝔸³ → 𝔸³` is defined over `ℚ` by
```
P = (1 + xy)³·z + y²·(1 + xy)·(4 + 3xy)
Q = y + 3x·(1 + xy)²·z + 3x·y²·(4 + 3xy)
R = 2x − 3x²·y − x³·z
```
where `x = X 0`, `y = X 1`, `z = X 2`.

**What is verified here (both to the Lean kernel, no `native_decide`, no new axioms):**
* `jacobian_det` : the formal Jacobian determinant `det (pderiv j (F i)) = C (-2)`
  as an identity of multivariate polynomials over `ℚ` — hence over every field of
  characteristic zero, since all coefficients are rational.
* `keller_not_injective` : the induced evaluation map on `ℚ³` is not injective;
  concretely the three *distinct* rational points `(0,0,-1/4)`, `(1,-3/2,13/2)`,
  `(-1,3/2,13/2)` all map to `(-1/4,0,0)` (`eval_point0/1/2`, `points_pairwise_distinct`).
* `keller_not_injective_C` : the same collision over `ℂ` (transfer via `algebraMap ℚ ℂ`).

A nonzero constant Jacobian together with a non-injective map is exactly a Keller
map that is not a polynomial automorphism: a counterexample to the Jacobian
conjecture in dimension 3.

**What is NOT verified here:** the preprint's global-geometry sections
(Propositions 4.x, the incidence variety `𝓘`), the properness/behaviour-at-infinity
analysis (Theorem 2.2, Corollary 2.3), the stabilization to dimensions `n > 3`, and
any analytic or properness claims. This file certifies precisely the algebraic
identity of Theorem 3.1 and the rational (hence characteristic-zero) fiber collision.
-/

open MvPolynomial

namespace Keller

/-! ## Stone 1 — the polynomials `P`, `Q`, `R` over `ℚ` -/

/-- First coordinate `P = (1 + xy)³·z + y²·(1 + xy)·(4 + 3xy)`. -/
noncomputable def P : MvPolynomial (Fin 3) ℚ :=
  (1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) * (4 + 3 * (X 0 * X 1))

/-- Second coordinate `Q = y + 3x·(1 + xy)²·z + 3x·y²·(4 + 3xy)`. -/
noncomputable def Q : MvPolynomial (Fin 3) ℚ :=
  X 1 + 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 + 3 * X 0 * X 1 ^ 2 * (4 + 3 * (X 0 * X 1))

/-- Third coordinate `R = 2x − 3x²·y − x³·z`. -/
noncomputable def R : MvPolynomial (Fin 3) ℚ :=
  2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2

/-- The map `F = (P, Q, R)` as a vector of polynomials. -/
noncomputable def F : Fin 3 → MvPolynomial (Fin 3) ℚ := ![P, Q, R]

/-! ## Stone 2 — the formal Jacobian and `det = -2` -/

/-- The formal Jacobian matrix `J i j = ∂ F i / ∂ x_j = pderiv j (F i)`. -/
noncomputable def J : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℚ) :=
  fun i j => pderiv j (F i)

/-- A derivation annihilates a numeral `≥ 2`: numerals appear as `OfNat.ofNat n`, not as
`Nat.cast n`, so `Derivation.map_natCast` needs the `Nat.cast_ofNat` bridge to apply. -/
private theorem pderiv_ofNat (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (OfNat.ofNat n : MvPolynomial (Fin 3) ℚ) = 0 := by
  rw [← Nat.cast_ofNat (R := MvPolynomial (Fin 3) ℚ) (n := n)]
  exact (pderiv i).map_natCast _

-- The `3×3` determinant of cubic entries expands to a large polynomial; the default
-- `maxRecDepth` (512) is exhausted while `simp` distributes `pderiv` over it.
set_option maxRecDepth 8000 in
/-- **Theorem 3.1, first identity.** The formal Jacobian determinant of `F` is the
constant polynomial `-2`. This is an identity in `MvPolynomial (Fin 3) ℚ`, verified
by expanding the nine partial derivatives and normalizing with `ring`. -/
theorem jacobian_det : J.det = C (-2) := by
  have hC : (C (-2 : ℚ) : MvPolynomial (Fin 3) ℚ) = -2 := by
    rw [map_neg, _root_.map_ofNat]
  -- The six off-diagonal partials `∂ x_i / ∂ x_j` (`i ≠ j`) vanish; supplied explicitly
  -- so `simp` need not discharge the `Fin` inequality side-goals of `pderiv_X_of_ne`.
  have h01 : pderiv 0 (X 1 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h02 : pderiv 0 (X 2 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h10 : pderiv 1 (X 0 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h12 : pderiv 1 (X 2 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h20 : pderiv 2 (X 0 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h21 : pderiv 2 (X 1 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  -- The scalar constants `2, 3, 4` occurring in `P, Q, R` also have zero derivative
  -- (instantiated at the literals so `simp` keys on them, unlike the generic `pderiv_ofNat`).
  have n2 : ∀ i : Fin 3, pderiv i (2 : MvPolynomial (Fin 3) ℚ) = 0 := fun i => pderiv_ofNat i 2
  have n3 : ∀ i : Fin 3, pderiv i (3 : MvPolynomial (Fin 3) ℚ) = 0 := fun i => pderiv_ofNat i 3
  have n4 : ∀ i : Fin 3, pderiv i (4 : MvPolynomial (Fin 3) ℚ) = 0 := fun i => pderiv_ofNat i 4
  rw [hC, Matrix.det_fin_three]
  -- Reduce each matrix entry `J i j` to `pderiv j` of the concrete coordinate, then push
  -- every `pderiv` through the ring structure down to `pderiv _ (X _)`.
  simp only [J, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, P, Q, R,
    map_add, map_sub, pderiv_mul, pderiv_pow, pderiv_one,
    pderiv_X_self, h01, h02, h10, h12, h20, h21, n2, n3, n4]
  ring

/-! ## Stone 3 — the fiber collision over `ℚ` -/

/-- The evaluation map `ℚ³ → ℚ³` induced by `F`. -/
noncomputable def Fmap (p : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => eval p (F i)

/-- `F(0, 0, -1/4) = (-1/4, 0, 0)`. -/
theorem eval_point0 : Fmap ![0, 0, -1/4] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [Fmap, F, P, Q, R]

/-- `F(1, -3/2, 13/2) = (-1/4, 0, 0)`. -/
theorem eval_point1 : Fmap ![1, -3/2, 13/2] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [Fmap, F, P, Q, R] <;> norm_num

/-- `F(-1, 3/2, 13/2) = (-1/4, 0, 0)`. -/
theorem eval_point2 : Fmap ![-1, 3/2, 13/2] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [Fmap, F, P, Q, R] <;> norm_num

/-- The three witness points are pairwise distinct (they already differ in the
`x`-coordinate: `0`, `1`, `-1`). -/
theorem points_pairwise_distinct :
    (![0, 0, -1/4] : Fin 3 → ℚ) ≠ ![1, -3/2, 13/2] ∧
    (![0, 0, -1/4] : Fin 3 → ℚ) ≠ ![-1, 3/2, 13/2] ∧
    (![1, -3/2, 13/2] : Fin 3 → ℚ) ≠ ![-1, 3/2, 13/2] := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd (congrFun h 0) (by norm_num)

/-! ## Stone 4 — packaging: not injective, and the headline statement -/

/-- **Theorem 3.1, second identity (consequence).** The map `F` is not injective on
`ℚ³`: the two distinct points `(0,0,-1/4)` and `(1,-3/2,13/2)` share the image
`(-1/4,0,0)`. -/
theorem keller_not_injective : ¬ Function.Injective Fmap := by
  intro h
  have hEq : Fmap ![0, 0, -1/4] = Fmap ![1, -3/2, 13/2] := by
    rw [eval_point0, eval_point1]
  have hpts := h hEq
  have := congrFun hpts 0
  norm_num at this

/-- **The counterexample to the Jacobian conjecture (Theorem 3.1).**

`F` has constant nonzero formal Jacobian determinant (`= C (-2)`) yet is not
injective as a map `ℚ³ → ℚ³` — hence not a polynomial automorphism. Since all data
is rational, the same statement holds over every field of characteristic zero.

Announced 2026-07-20 by L. Alpöge (crediting A. Mathew and the Fable model),
preprint *"A counterexample to the Jacobian conjecture"*, Theorem 3.1. See the
module docstring for the exact scope of what is and is not machine-verified here. -/
theorem jacobian_conjecture_counterexample :
    J.det = C (-2) ∧ ¬ Function.Injective Fmap :=
  ⟨jacobian_det, keller_not_injective⟩

/-! ## Stone 5 (bonus) — the same counterexample over `ℂ` -/

/-- The coordinates of `F` pushed to `ℂ` coefficients via `algebraMap ℚ ℂ` and
`MvPolynomial.map`. -/
noncomputable def Fℂ : Fin 3 → MvPolynomial (Fin 3) ℂ := fun i => map (algebraMap ℚ ℂ) (F i)

/-- The induced evaluation map `ℂ³ → ℂ³`. -/
noncomputable def FmapC (p : Fin 3 → ℂ) : Fin 3 → ℂ := fun i => eval p (Fℂ i)

/-- `F(0, 0, -1/4) = (-1/4, 0, 0)` over `ℂ`. -/
theorem evalC_point0 : FmapC ![0, 0, -1/4] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [FmapC, Fℂ, F, P, Q, R]

/-- `F(1, -3/2, 13/2) = (-1/4, 0, 0)` over `ℂ`. -/
theorem evalC_point1 : FmapC ![1, -3/2, 13/2] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [FmapC, Fℂ, F, P, Q, R] <;> norm_num

/-- The `ℂ`-map is not injective: the two distinct points `(0,0,-1/4)` and
`(1,-3/2,13/2)` in `ℂ³` share the image `(-1/4,0,0)`. This transfers the
characteristic-zero counterexample to the algebraically closed field `ℂ`. -/
theorem keller_not_injective_C : ¬ Function.Injective FmapC := by
  intro h
  have hEq : FmapC ![0, 0, -1/4] = FmapC ![1, -3/2, 13/2] := by
    rw [evalC_point0, evalC_point1]
  have hpts := h hEq
  have := congrFun hpts 0
  norm_num at this

end Keller
