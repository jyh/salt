/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard
import Salt.Maynard.Tuple

/-!
# Rung 4a — explicit gaps ≤ 12: parameter pack (card C3, blueprint P0)

Statement stubs for the explicit-gaps track (`docs/blueprints/explicit12-design.md`,
§1) and the concrete evaluation of the `k = 5` admissible tuple `H 5`
(landed `Salt.Maynard.H`/`hSeq`) needed to sharpen the pigeonhole gap bound
from `D₀ 5` to `diam (H 5) = 12`.
-/

open Salt.Maynard

/-! ## §1 — statement stubs (frozen; copied verbatim from the design doc) -/

/-- PNT-quality prime supply in the (N, 64N] window: for every ε there is a
threshold past which Δπ ≥ (63−ε)·N/log N.  A trivial consequence of PNT;
stated as an interface (like `HasLevel`) because mathlib has no PNT — the
PrimeNumberTheoremAnd project can discharge it the day we take the dep. -/
def WindowPNT : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    (63 - ε) * (N : ℝ) / Real.log N
      ≤ (Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)

/-- The full Elliott–Halberstam conjecture: every level θ < 1. -/
def EHall : Prop := ∀ θ : ℝ, 0 < θ → θ < 1 → EH θ

/-- Unfold helper: `EHall` instantiated at a particular level `θ ∈ (0,1)`. -/
theorem EHall_hasEH {θ : ℝ} (h : EHall) (hθ0 : 0 < θ) (hθ1 : θ < 1) : EH θ :=
  h θ hθ0 hθ1

/-! ## §6-C3(ii) — evaluating the `k = 5` tuple

`H 5 = {7, 11, 13, 17, 19}`, the first 5 primes strictly greater than 5.
`firstIdxAboveK 5 = Nat.count Nat.Prime 6 = 3` (primes `< 6`: `2, 3, 5`), so
`hSeq 5 i = Nat.nth Nat.Prime (3 + i)`. Mathlib already supplies
`Nat.nth Nat.Prime 3 = 7` and `Nat.nth Nat.Prime 4 = 11`
(`Nat.nth_prime_three_eq_seven`, `Nat.nth_prime_four_eq_eleven`,
`Mathlib.Data.Nat.Prime.Nth`); we supply the remaining three instances of
the same `Nat.nth_count` pattern for indices `5, 6, 7`. -/

namespace Salt.Twelve

theorem firstIdxAboveK_five : firstIdxAboveK 5 = 3 := by decide

/-- `Nat.nth Nat.Prime 5 = 13`, same pattern as mathlib's
`Nat.nth_prime_four_eq_eleven`. -/
theorem nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 :=
  Nat.nth_count (show Nat.Prime 13 by norm_num)

/-- `Nat.nth Nat.Prime 6 = 17`. -/
theorem nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 :=
  Nat.nth_count (show Nat.Prime 17 by norm_num)

/-- `Nat.nth Nat.Prime 7 = 19`. -/
theorem nth_prime_seven_eq_nineteen : Nat.nth Nat.Prime 7 = 19 :=
  Nat.nth_count (show Nat.Prime 19 by norm_num)

theorem hSeq_five_zero : hSeq 5 ⟨0, by omega⟩ = 7 := by
  unfold hSeq
  rw [firstIdxAboveK_five]
  exact Nat.nth_prime_three_eq_seven

theorem hSeq_five_one : hSeq 5 ⟨1, by omega⟩ = 11 := by
  unfold hSeq
  rw [firstIdxAboveK_five]
  exact Nat.nth_prime_four_eq_eleven

theorem hSeq_five_two : hSeq 5 ⟨2, by omega⟩ = 13 := by
  unfold hSeq
  rw [firstIdxAboveK_five]
  exact nth_prime_five_eq_thirteen

theorem hSeq_five_three : hSeq 5 ⟨3, by omega⟩ = 17 := by
  unfold hSeq
  rw [firstIdxAboveK_five]
  exact nth_prime_six_eq_seventeen

theorem hSeq_five_four : hSeq 5 ⟨4, by omega⟩ = 19 := by
  unfold hSeq
  rw [firstIdxAboveK_five]
  exact nth_prime_seven_eq_nineteen

/-- The pigeonhole-sharpening fact: every pair of values of the concrete
`k = 5` tuple `hSeq 5` differs by at most `12` (max − min = 19 − 7 = 12,
the diameter of the optimal admissible 5-tuple `H 5`). -/
theorem hSeq_diam_le_twelve (i j : Fin 5) :
    (hSeq 5 i : ℤ) - (hSeq 5 j : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  fin_cases i <;> fin_cases j <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

end Salt.Twelve
