/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16

/-! # HL-3c node M2b — `2^Ω = β ∗ τ` on odd `n` (statement frozen at salt `66fd0d0d`). -/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-- **M2b.** The convolution identity on odd `n`. -/
theorem pow2Omega_eq_sum (n : ℕ) (hn : Odd n) :
    pow2Omega n = ∑ m ∈ n.divisors, betaT m * ((n / m).divisors.card : ℝ) := by
  sorry

end Salt.HardyLittlewood.Sel
