/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.RosserChain

/-!
# AF1 — the Rosser-chain iterate `fseq n` is antitone on its operating range

The helper node `E₁c-hf` needs each iterate `fₙ = fseq n` to be **antitone** on the
range where it is the active window: odd levels live on `[1,∞)`, even levels on `[2,∞)`.

## Route (per-level, no induction)

Both parities reduce `fseq n` to a single global product `(1/s)·G(s)` on their range:

* **odd `n ≥ 3`** — the `max`-collapse of `fseq_odd_{tail,flat}_window` gives, for *all* `s ≥ 1`,
  `fseq n s = (1/s)·∫_{max s 3}^{(n-1)+3} fseq (n-1)(t-1) dt` (flat for `s ≤ 3`, tail for
  `s ≥ 3`, agreeing at the `s = 3` junction — the idiom of `MassCert.fseq_odd_continuousOn`,
  which never uses the upper endpoint of its domain, so the same equation holds on all of `[1,∞)`);
* **even `n ≥ 2`** — `fseq_even_window` already gives, for *all* `s ≥ 2`,
  `fseq n s = (1/s)·∫_s^{(n-1)+3} fseq (n-1)(t-1) dt` (globally on `[2,∞)`, no junction split);
* **`n = 1`** — the explicit `(3−s)/s` on `[1,3]`, `0` beyond, handled directly.

In each case `1/s` is positive antitone and `s ↦ ∫_{L s}^{c} (nonneg)` is antitone (`L` monotone,
integral antitone in its lower limit via interval additivity + nonnegativity of the integrand); the
product of two nonnegative antitone factors is antitone.  Nonnegativity of the integral factor is
read off `fseq_nonneg` (`∫ = s·fseq n s ≥ 0`), sidestepping the reversed-orientation region `s > c`.
-/

open intervalIntegral MeasureTheory Set

namespace Salt.Chen

/-! ### The two reusable ingredients -/

/-- The integral `a ↦ ∫_a^c h` is **antitone** when `h ≥ 0` is interval-integrable: raising the
lower limit `a₁ ≤ a₂` removes the nonnegative slab `∫_{a₁}^{a₂} h ≥ 0` (interval additivity). -/
theorem antitone_integral_lower {c : ℝ} {h : ℝ → ℝ}
    (hnn : ∀ t, 0 ≤ h t)
    (hint : ∀ a b : ℝ, IntervalIntegrable h volume a b) :
    Antitone (fun a => ∫ t in a..c, h t) := by
  intro a1 a2 ha
  change (∫ t in a2..c, h t) ≤ ∫ t in a1..c, h t
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hint a1 a2) (hint a2 c)
  have hpos : 0 ≤ ∫ t in a1..a2, h t := intervalIntegral.integral_nonneg ha (fun u _ => hnn u)
  linarith [hadd, hpos]

/-! ### `n = 1`: the explicit base level -/

/-- `fseq 1` is antitone on `[1,∞)`: `(3−s)/s` decreasing on `[1,3]`, then flat `0`. -/
theorem fseq_one_antitoneOn_Ici : AntitoneOn (fseq 1) (Set.Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  rcases le_or_gt y 3 with hy3 | hy3
  · -- both in the window `[1,3]`
    have hx3 : x ≤ 3 := le_trans hxy hy3
    rw [fseq_one_window hx hx3, fseq_one_window hy hy3]
    have hx0 : (0 : ℝ) < x := by linarith
    have hy0 : (0 : ℝ) < y := by linarith
    have expand : (3 - x) / x - (3 - y) / y = 3 * (y - x) / (x * y) := by field_simp; ring
    have hge : 0 ≤ (3 - x) / x - (3 - y) / y := by
      rw [expand]; exact div_nonneg (by nlinarith) (mul_pos hx0 hy0).le
    linarith
  · -- `y > 3`: `fseq 1 y = 0 ≤ fseq 1 x`
    rw [fseq_eq_zero_of_ge 1 y (by push_cast; linarith)]
    exact fseq_nonneg 1 x

/-! ### The frozen targets -/

/-- **AF1, odd.**  For odd `n`, `fseq n` is antitone on `[1,∞)`. -/
theorem fseq_antitoneOn_odd {n : ℕ} (hodd : Odd n) : AntitoneOn (fseq n) (Set.Ici (1 : ℝ)) := by
  have hpos : 1 ≤ n := by rcases hodd with ⟨j, hj⟩; omega
  rcases eq_or_lt_of_le hpos with hn1 | hn3
  · -- `n = 1`
    subst hn1
    exact fseq_one_antitoneOn_Ici
  · -- `n ≥ 3` odd: the `max`-collapse product on `[1,∞)`
    have hn0 : (n - 1) ≠ 0 := by omega
    have hmrw : (n - 1) + 1 = n := by omega
    have hpred_odd : ¬ Even ((n - 1) + 1) := by
      rw [hmrw]; exact Nat.not_even_iff_odd.mpr hodd
    -- the single formula, valid on all of `[1,∞)` (upper endpoint is never used)
    have key : ∀ s, 1 ≤ s →
        fseq n s = (1 / s) * ∫ t in (max s 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1) := by
      intro s hs1
      rcases le_or_gt s 3 with h3 | h3
      · rw [max_eq_right h3]
        rcases eq_or_lt_of_le h3 with heq | hlt
        · -- `s = 3`: tail window at 3
          have ht := fseq_odd_tail_window (n := n - 1) hn0 hpred_odd (s := s) heq.ge
          rw [hmrw] at ht; rw [ht, heq]
        · -- `s < 3`: flat window
          have hf := fseq_odd_flat_window (n := n - 1) hn0 hpred_odd (s := s) hs1 hlt
          rw [hmrw] at hf; exact hf
      · rw [max_eq_left h3.le]
        have ht := fseq_odd_tail_window (n := n - 1) hn0 hpred_odd (s := s) h3.le
        rw [hmrw] at ht; exact ht
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hx0 : (0 : ℝ) < x := by linarith
    have hy0 : (0 : ℝ) < y := by linarith
    rw [key x hx, key y hy]
    -- the integral factor is antitone (`max` monotone ∘ integral-in-lower-limit antitone)
    have hmaxle : max x 3 ≤ max y 3 := max_le_max hxy le_rfl
    have hGanti : (∫ t in (max y 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1))
        ≤ ∫ t in (max x 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1) :=
      antitone_integral_lower (fun t => fseq_nonneg (n - 1) (t - 1))
        (fun a b => fseq_shift_intervalIntegrable (n - 1) a b) hmaxle
    -- the integral factor at `y` is nonnegative (`= y · fseq n y`)
    have hGy0 : 0 ≤ ∫ t in (max y 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1) := by
      have heqy : (∫ t in (max y 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1))
          = y * fseq n y := by
        rw [key y hy, ← mul_assoc, mul_one_div, div_self (ne_of_gt hy0), one_mul]
      rw [heqy]; exact mul_nonneg hy0.le (fseq_nonneg _ _)
    have h1x0 : (0 : ℝ) ≤ 1 / x := (one_div_pos.mpr hx0).le
    have h1xy : (1 : ℝ) / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy
    calc (1 / y) * ∫ t in (max y 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1)
        ≤ (1 / x) * ∫ t in (max y 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1) :=
          mul_le_mul_of_nonneg_right h1xy hGy0
      _ ≤ (1 / x) * ∫ t in (max x 3)..(((n - 1 : ℕ) : ℝ) + 3), fseq (n - 1) (t - 1) :=
          mul_le_mul_of_nonneg_left hGanti h1x0

/-- **AF1, even.**  For even `n ≠ 0`, `fseq n` is antitone on `[2,∞)`. -/
theorem fseq_antitoneOn_even {n : ℕ} (hne : n ≠ 0) (heven : Even n) :
    AntitoneOn (fseq n) (Set.Ici (2 : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  rw [fseq_even_window heven hx, fseq_even_window heven hy]
  -- the integral factor is antitone in its lower limit
  have hGanti : (∫ t in y..((m : ℝ) + 3), fseq m (t - 1))
      ≤ ∫ t in x..((m : ℝ) + 3), fseq m (t - 1) :=
    antitone_integral_lower (fun t => fseq_nonneg m (t - 1))
      (fun a b => fseq_shift_intervalIntegrable m a b) hxy
  -- the integral factor at `y` is nonnegative (`= y · fseq (m+1) y`)
  have hGy0 : 0 ≤ ∫ t in y..((m : ℝ) + 3), fseq m (t - 1) := by
    have heqy : (∫ t in y..((m : ℝ) + 3), fseq m (t - 1)) = y * fseq (m + 1) y := by
      rw [fseq_even_window heven hy, ← mul_assoc, mul_one_div, div_self (ne_of_gt hy0), one_mul]
    rw [heqy]; exact mul_nonneg hy0.le (fseq_nonneg _ _)
  have h1x0 : (0 : ℝ) ≤ 1 / x := (one_div_pos.mpr hx0).le
  have h1xy : (1 : ℝ) / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy
  calc (1 / y) * ∫ t in y..((m : ℝ) + 3), fseq m (t - 1)
      ≤ (1 / x) * ∫ t in y..((m : ℝ) + 3), fseq m (t - 1) :=
        mul_le_mul_of_nonneg_right h1xy hGy0
    _ ≤ (1 / x) * ∫ t in x..((m : ℝ) + 3), fseq m (t - 1) :=
        mul_le_mul_of_nonneg_left hGanti h1x0

end Salt.Chen
