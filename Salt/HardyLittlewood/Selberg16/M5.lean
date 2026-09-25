/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16.M2
import Salt.HardyLittlewood.Selberg16.M3
import Salt.HardyLittlewood.Selberg16.M4

/-! # HL-3c nodes M5a, M5 — the dimension-2 mean value (statements frozen at salt `66fd0d0d`). -/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-! ## M5a — the convolution lower bound (M1 · M2 · a finite `m`-range) -/

/-- **M5a.** For odd `R`, `Σ_{n<x odd} 2^Ω(n)/n ≥ Σ_{m ∣ R} β(m)/m · oddDivSum((x−1)/m)`. -/
theorem oddOmegaSum_ge_conv (R x : ℕ) (hR : Odd R) :
    ∑ m ∈ R.divisors, betaT m / m * oddDivSum ((x - 1) / m) ≤ oddOmegaSum x := by
  sorry

/-! ## M5 — the dimension-2 mean value -/

/-- **M5. The mean value.** `mainTermSum z ≥ (1−η)·(log z)²/(8·Π₂)` for all large `z`. -/
theorem mainTermSum_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ z : ℕ in atTop, (1 - η) * (Real.log z) ^ 2 / (8 * Pi2) ≤ Salt.M3Assembly.mainTermSum z := by
  sorry

end Salt.HardyLittlewood.Sel
