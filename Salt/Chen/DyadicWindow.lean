/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# A power of two in `[y, 4y]`

For a real `y ≥ 2` there is a `k` with `y ≤ 2^k ≤ 4y`: round `y` up to the natural `n = ⌈y⌉`
(so `n ≤ y + 1 ≤ 2y`), then take the least power of two at or above `n`, which is at most `2n`.

This is the dyadic-window step that the Chen and Goldbach band assemblies took inline
(`ChenFinal2`, `PriceOne`, `PriceTwo` ×2, `BandWin`, `D0Win`, `D0Win2`), each time at
`y = L ^ 17`. The first conjunct `2 ≤ 2^k` is what those assemblies pass on as the window's
floor. `k` is returned by an existential, so `Nat.clog` and `Nat.ceil` stay out of reach of
defeq at the call site.

## Main result
* `exists_two_pow_window` — for `2 ≤ y`, some `k` has `2 ≤ 2^k`, `y ≤ 2^k` and `2^k ≤ 4·y`.
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

end Salt.Chen
