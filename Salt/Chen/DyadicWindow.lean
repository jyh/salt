/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# A power of two in `[y, 4y]`, and the scale window `x/2 < X·M ≤ 4x`

For a real `y ≥ 2` there is a `k` with `y ≤ 2^k ≤ 4y`: round `y` up to the natural `n = ⌈y⌉`
(so `n ≤ y + 1 ≤ 2y`), then take the least power of two at or above `n`, which is at most `2n`.

This is the dyadic-window step that the Chen and Goldbach band assemblies took inline
(`ChenFinal2`, `PriceOne`, `PriceTwo` ×2, `BandWin`, `D0Win`, `D0Win2`), each time at
`y = L ^ 17`. The first conjunct `2 ≤ 2^k` is what those assemblies pass on as the window's
floor. `k` is returned by an existential, so `Nat.clog` and `Nat.ceil` stay out of reach of
defeq at the call site.

## Main result
* `exists_two_pow_window` — for `2 ≤ y`, some `k` has `2 ≤ 2^k`, `y ≤ 2^k` and `2^k ≤ 4·y`.
* `xm_log_bounds_of_le` — `log x − 1 ≤ log(X·M) ≤ log x + 3` from `x/2 + 1 ≤ X·M ≤ 4x`, `x ≥ 2`;
  `xm_log_bounds` is its strict form, and `xm_real_bounds(_of_le)` the real window under it.
-/

namespace Salt.Chen

/-- **A dyadic point in `[y, 4y]`.** For `2 ≤ y` there is `k` with `2 ≤ 2^k`, `y ≤ 2^k` and
`2^k ≤ 4·y`. Proof: `n = ⌈y⌉₊` satisfies `y ≤ n ≤ y + 1` and `1 < n`; `k = Nat.clog 2 n` gives
`n ≤ 2^k ≤ 2n`. -/
theorem exists_two_pow_window {y : ℝ} (hy : 2 ≤ y) :
    ∃ k : ℕ, 2 ≤ 2 ^ k ∧ y ≤ ((2 ^ k : ℕ) : ℝ) ∧ ((2 ^ k : ℕ) : ℝ) ≤ 4 * y := by
  obtain ⟨n, hn_ge, hn_le⟩ : ∃ n : ℕ, y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y + 1 :=
    ⟨⌈y⌉₊, Nat.le_ceil _, le_of_lt (Nat.ceil_lt_add_one (by linarith))⟩
  have hn1 : 1 < n := by
    have h1R : (1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h1R
  refine ⟨Nat.clog 2 n, ?_, ?_, ?_⟩
  · exact le_trans (by omega : 2 ≤ n) (Nat.le_pow_clog (by norm_num) n)
  · exact le_trans hn_ge (by exact_mod_cast Nat.le_pow_clog (by norm_num) n)
  · have hpow_lt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) hn1
    have hsplit : 2 * 2 ^ (Nat.clog 2 n - 1) = 2 ^ Nat.clog 2 n := by
      rw [← pow_succ']
      congr 1
      have := Nat.clog_pos (b := 2) (by norm_num) hn1
      omega
    have h2n : 2 ^ Nat.clog 2 n ≤ 2 * n := by
      rw [← hsplit]
      exact Nat.mul_le_mul (le_refl 2) (le_of_lt hpow_lt)
    have h2nR : ((2 ^ Nat.clog 2 n : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast h2n
    linarith

/-! ## The scale window `x/2 < X·M ≤ 4x` and its logarithm

From the raw Nat window `x/2 + 1 ≤ X·M ≤ 4x`, `X·M ≍ x` in `ℝ` and
`log(X·M) ∈ [log x − 1, log x + 3]`; the `−1` and `+3` are `log 2 ≤ 1` and `log 4 ≤ 3`. The
Chen and Goldbach band assemblies (`ChenFinal2`, `PriceOne`, `PriceTwo` ×2, `BandWin`, `D0Win`,
`D0Win2`) each derived the logarithmic pair inline. The `≤` forms serve the Goldbach annuli,
whose cut gives `x/2 + 1 ≤ X·M`; the strict forms are the box rows' original statements. -/

/-- **`xm_real_bounds_of_le`.** The real window from the raw Nat window: `0 < X·M`,
`x/2 < X·M`, `X·M ≤ 4x`. -/
theorem xm_real_bounds_of_le {x X M : ℕ} (hlo : x / 2 + 1 ≤ X * M) (hhi : X * M ≤ 4 * x) :
    (0 : ℝ) < (X : ℝ) * (M : ℝ)
      ∧ (x : ℝ) / 2 < (X : ℝ) * (M : ℝ)
      ∧ (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hhiR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hhi
  refine ⟨hXMposR, ?_, hhiR⟩
  have h1 : x < (x / 2 + 1) * 2 := by omega
  have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
  have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (M : ℝ) := by exact_mod_cast hlo
  push_cast at h1R h2R
  linarith

/-- **`xm_real_bounds` (F1-rows(a)).** `xm_real_bounds_of_le` from the strict window
`x/2 + 1 < X·M`. -/
theorem xm_real_bounds {x X M : ℕ} (hlo : x / 2 + 1 < X * M) (hhi : X * M ≤ 4 * x) :
    (0 : ℝ) < (X : ℝ) * (M : ℝ)
      ∧ (x : ℝ) / 2 < (X : ℝ) * (M : ℝ)
      ∧ (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) :=
  xm_real_bounds_of_le hlo.le hhi

/-- **`xm_log_bounds_of_le`.** `log x − 1 ≤ log(X·M) ≤ log x + 3` from the raw Nat window
(`x ≥ 2`). The `−1`/`+3` come from `log 2 ≤ 1` and `log 4 ≤ 3`. -/
theorem xm_log_bounds_of_le {x X M : ℕ} (hx : 2 ≤ x)
    (hlo : x / 2 + 1 ≤ X * M) (hhi : X * M ≤ 4 * x) :
    Real.log x - 1 ≤ Real.log ((X : ℝ) * (M : ℝ))
      ∧ Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log x + 3 := by
  obtain ⟨hXMposR, hhalf, hhiR⟩ := xm_real_bounds_of_le hlo hhi
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  constructor
  · have hlog : Real.log ((x : ℝ) / 2) ≤ Real.log ((X : ℝ) * (M : ℝ)) :=
      Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    have h2log : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  · have h1 : Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log (4 * (x : ℝ)) :=
      Real.log_le_log hXMposR hhiR
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h1
    have h4log : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith

/-- **`xm_log_bounds` (F1-rows(a)).** `xm_log_bounds_of_le` from the strict window
`x/2 + 1 < X·M`. -/
theorem xm_log_bounds {x X M : ℕ} (hx : 2 ≤ x)
    (hlo : x / 2 + 1 < X * M) (hhi : X * M ≤ 4 * x) :
    Real.log x - 1 ≤ Real.log ((X : ℝ) * (M : ℝ))
      ∧ Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log x + 3 :=
  xm_log_bounds_of_le hx hlo.le hhi

end Salt.Chen
