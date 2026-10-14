/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.InnerS1

/-!
# C1 · B4.3a — the S₁ collision bound for any bounded weight, at any `k`

`Salt.Twelve.collision_yF_M` (k = 5, `Qabs F ≤ 1`) with its only k = 5 content — the route to
`|y| ≤ 1` — replaced by the hypothesis itself; both lemmas it composes (`s1_inner_bounded`,
`collision_lower_orderW_ofM`) are already k-generic.
-/

open Finset Salt.Twelve Salt.Maynard

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

omit [Salt.Maynard.TupleChoice] in
theorem collision_y_M (k R W' D : ℕ) (y : (Fin k → ℕ) → ℝ) (hk : 1 ≤ k)
    (hy1 : ∀ r, |y r| ≤ 1) (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hDlt : ∀ p, p.Prime → ¬p ∣ W' → D < p) (hDk : 12 * k ^ 2 ≤ D) :
    |s1CollisionForm k R W' y|
      ≤ 12 * (k : ℝ) ^ 2 / D * ∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) := by
  have hInner : S1InnerBoundM k R W' y
      (∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ)) :=
    Salt.Twelve.s1_inner_bounded k R W' y hy1 hy0
  have hM : 0 ≤ ∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) :=
    Finset.sum_nonneg fun r _ => by positivity
  exact Salt.Twelve.collision_lower_orderW_ofM k R W' D y _ hM hy0 hInner hDlt hk hDk

end Salt.MaynardK
