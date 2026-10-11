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
`win_ratio_core_105`: the window-PNT slack algebra at `c_DL = 15746/1000` (blueprint v2 §2, option
(ii): the log-R pin `4999/20000` times `63 − 1/1000`, lowered into the window that absorbs the
δ-shift); the needed ratio is `4.0010561`, the certificate gives `4.0015`. `Iform_pos`: `0 < Iform`.
-/

namespace Salt.MaynardK

theorem ratio_cert_105 : (40015 : ℚ) * Iform < 10000 * (105 * Jform) := by decide +kernel

theorem Iform_pos : 0 < Iform := by decide +kernel

theorem win_ratio_core_105 (Nr δ logR I SJ eps : ℝ)
    (hIpos : 0 < I) (hSJcert : (40015 : ℝ) * I < 10000 * SJ)
    (hDL : (15746 / 1000 : ℝ) * Nr ≤ δ * logR)
    (hNr : 0 < Nr) (hepsle : eps ≤ 1 / 100000) :
    63 * Nr * (1 + eps) * I < δ * logR * SJ := by
  have hSJpos : 0 < SJ := by nlinarith [hSJcert, hIpos]
  have h1 : (δ * logR - 15746 / 1000 * Nr) * SJ ≥ 0 :=
    mul_nonneg (by linarith) hSJpos.le
  have h2 : Nr * (10000 * SJ - 40015 * I) ≥ 0 := mul_nonneg hNr.le (by linarith)
  have h3 : eps * (Nr * I) ≤ (1 / 100000) * (Nr * I) :=
    mul_le_mul_of_nonneg_right hepsle (mul_nonneg hNr.le hIpos.le)
  have hC : 0 < Nr * I := mul_pos hNr hIpos
  nlinarith [h1, h2, h3, hC, hIpos, hNr, hSJpos]

end Salt.MaynardK
