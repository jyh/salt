/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Cert105
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# C1 · B4.5a — the ratio certificate at `k = 105` and its real-algebra core

`ratio_cert_105`: `M₁₀₅ > 4.0015`, i.e. `40015·Iform < 10000·(105·Jform)`, by kernel reduction.
`win_ratio_core_105`: the window-PNT slack algebra at `ε = 1/1000` and window exponent `4999/20000`
(blueprint 2026-10-11 §2: the needed ratio is `4.000904`, the certificate gives `4.0015`).
-/

namespace Salt.MaynardK

theorem ratio_cert_105 : (40015 : ℚ) * Iform < 10000 * (105 * Jform) := by decide +kernel

theorem win_ratio_core_105 (Nr δ logR I SJ eps : ℝ)
    (hIpos : 0 < I) (hSJcert : (40015 : ℝ) * I < 10000 * SJ)
    (hDL : (63 - 1 / 1000 : ℝ) * (4999 / 20000) * Nr ≤ δ * logR)
    (hNr : 0 < Nr) (hepsle : eps ≤ 1 / 100000) :
    63 * Nr * (1 + eps) * I < δ * logR * SJ := by
  have hSJpos : 0 < SJ := by nlinarith [hSJcert, hIpos]
  have h1 : (δ * logR - (63 - 1 / 1000) * (4999 / 20000) * Nr) * SJ ≥ 0 :=
    mul_nonneg (by linarith) hSJpos.le
  have h2 : Nr * (10000 * SJ - 40015 * I) ≥ 0 := mul_nonneg hNr.le (by linarith)
  have h3 : eps * (Nr * I) ≤ (1 / 100000) * (Nr * I) :=
    mul_le_mul_of_nonneg_right hepsle (mul_nonneg hNr.le hIpos.le)
  have hC : 0 < Nr * I := mul_pos hNr hIpos
  nlinarith [h1, h2, h3, hC, hIpos, hNr, hSJpos]

end Salt.MaynardK
