/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16

/-! # HL-3c node M4 — the finite Euler product reaches `1/Π₂` (statement frozen at salt `66fd0d0d`). -/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-! ## M4 — the finite Euler product reaches `1/Π₂` -/

/-- **M4.** -/
theorem betaSum_ge {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ, Odd R ∧ (1 - η) / Pi2 ≤ ∑ m ∈ R.divisors, betaT m / m := by
  sorry

end Salt.HardyLittlewood.Sel
