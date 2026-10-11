/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Square
import Salt.MaynardK.MvIGen

/-!
# C1 — the sieve's first moment of Maynard's `F²` at `k = 105`

Its main term is the certificate's `Iform`.

`mv_I_gen` (B2) applied to `Fsq 105 F`, rewritten by `eval_Fsq` and `Iform_eq`.
-/

open Finset Salt.Twelve Salt.Maynard

namespace Salt.MaynardK

theorem mv_I_105 (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (hUpper : PhiUpperAtom W') :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ kSieveIndex 105 R W',
            eval (Fpoly 105 F) (fun i => Real.log (r i) / Real.log R) ^ 2
              / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 105 * ((Iform : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 105 * (1 / Real.log R + 1 / D) := by
  obtain ⟨c, hc, h⟩ := mv_I_gen W' hW' hpos hUpper 105 (by norm_num) (Fsq 105 F)
  refine ⟨c, hc, fun D R hD hDW hR => ?_⟩
  simpa only [eval_Fsq, ← Iform_eq] using h D R hD hDW hR

end Salt.MaynardK
