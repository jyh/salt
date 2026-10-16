/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.MomentJ54

/-!
# C1 · A2d (f) — the two forms and the ratio certificate at `k = 54`

`Iform54 = IformM 13 54 cs54`, `Jform54 = JformM 13 54 cs54`. With `Iint = 100!·Iform54`
(`Iint_eq_IformM`) and `Jint = (24!)²·101!·Jform54` (`Jint_eq_JformM`), the certificate's integer
inequality `cert54` divides out to `ratio_cert_54`: `M₅₄ > 4.0015`; and `0 < Iint` is `Iform54_pos`.
Nothing here bears on twin primes.
-/

open scoped Nat

namespace SaltC1.MaynardK

open Salt.MaynardK SaltC1.Cert54

/-- `I = ∫ F²` at `k = 54`. -/
noncomputable def Iform54 : ℚ := IformM 13 54 cs54

/-- `J = ∫ (∫ F dt₅₄)²` at `k = 54`. -/
noncomputable def Jform54 : ℚ := JformM 13 54 cs54

/-- **`M₅₄ > 4.0015`.** -/
theorem ratio_cert_54 : (40015 : ℚ) * Iform54 < 10000 * (54 * Jform54) := by
  have h : ((40015 * Iint * (Dconst : ℤ) : ℤ) : ℚ) < ((10000 * 54 * Jint * (F100 : ℤ) : ℤ) : ℚ) :=
    Int.cast_lt.mpr cert54.2
  push_cast at h
  rw [Iint_eq_IformM, Jint_eq_JformM, F100_eq, Dconst_eq] at h
  push_cast at h
  have hP : (0 : ℚ) < ((100 ! : ℕ) : ℚ) * (((24 ! : ℕ) : ℚ) ^ 2 * ((101 ! : ℕ) : ℚ)) := by
    positivity
  unfold Iform54 Jform54
  refine lt_of_mul_lt_mul_right ?_ hP.le
  linarith

/-- `0 < Iform54`. -/
theorem Iform54_pos : 0 < Iform54 := by
  have h : ((0 : ℤ) : ℚ) < (Iint : ℚ) := Int.cast_lt.mpr cert54.1
  rw [Iint_eq_IformM, Int.cast_zero] at h
  have h100 : (0 : ℚ) < ((100 ! : ℕ) : ℚ) := by positivity
  exact (mul_pos_iff_of_pos_left h100).mp h

end SaltC1.MaynardK
