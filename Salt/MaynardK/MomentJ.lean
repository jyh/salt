/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.JMain

/-!
# C1 bridge B4b — the sieve's contracted second moment of Maynard's `F` at `k = 105`

Its main term is the certificate's `Jform`: `mv_J_gen` (B3) at `n + 1 = 105` on `Fpoly 105 F`,
rewritten by `Jform_eq` (B4a), at every coordinate `m`.
-/

open Finset Salt.Twelve Salt.Maynard

namespace Salt.MaynardK

theorem mv_J_105 (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (hUpper : PhiUpperAtom W')
    (m : Fin 105) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ (kSieveIndex 105 R W').filter (fun r => r m = 1),
            (∑ u ∈ Finset.range R,
                yFg R W' (Fpoly 105 F) (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 106 * ((Jform : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 106 * (1 / Real.log R + 1 / D) := by
  obtain ⟨c, hc, h⟩ := mv_J_gen W' hW' hpos hUpper 104 (by norm_num) (Fpoly 105 F) m
  refine ⟨c, hc, fun D R hD hDW hR => ?_⟩
  rw [Jform_eq m]
  exact h D R hD hDW hR

end Salt.MaynardK
