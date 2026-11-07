/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A lower bound on `log x` from an exponential floor

`exp c ≤ x` gives `c ≤ log x`. Mathlib states this as the iff `Real.le_log_iff_exp_le`, which
needs `0 < x` as an argument; here the floor supplies it. The corpus wrote the two-step
`rw [← Real.log_exp c]; exact Real.log_le_log (Real.exp_pos _) h` at 157 sites (the tactics
catalogue's candidate #45); this module states it once.

It is imported by `Salt.SW.ZetaPole`, a base module that every one of those sites already
imports, so no site file takes a new import.
-/

namespace Salt

/-- **An exponential floor bounds the log from below:** `exp c ≤ x → c ≤ log x`. -/
theorem le_log_of_exp_le {c x : ℝ} (h : Real.exp c ≤ x) : c ≤ Real.log x :=
  (Real.le_log_iff_exp_le ((Real.exp_pos c).trans_le h)).2 h

end Salt
