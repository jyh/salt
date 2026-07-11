/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.LS.Dist

/-!
# L6.1 — Farey spacing

Design: `docs/blueprints/largesieve.md`, "Carrier choices" and node `L6.1`.
Two distinct Farey-type fractions `a/q ≠ a'/q'` with denominators `q, q' ≤ Q`
are `dist₁`-separated by at least `1/Q²`. Coprimality of `a` with `q` (and
`a'` with `q'`) is NOT needed; the argument only uses `0 ≤ a < q`,
`0 ≤ a' < q'`, and `a/q ≠ a'/q'`.

The denominator-sharp core estimate `1/(q q') ≤ dist₁ (a/q) (a'/q')` is
proved first (`farey_spacing_core`); the `Q`-uniform corollary
(`farey_spacing`) follows from `q, q' ≤ Q ⇒ q q' ≤ Q²`.

Proof idea for the core estimate: writing `x = a/q`, `y = a'/q'`, for every
integer `n` the difference `x - y - n` equals `(k : ℝ) / (q q')` where
`k = a q' - a' q - n q q' : ℤ`. If `k = 0` then `x - y = n`; but
`x, y ∈ [0, 1)` forces `x - y ∈ (-1, 1)`, so `n = 0` and `x = y`,
contradicting `x ≠ y`. Hence `k ≠ 0`, so `|k| ≥ 1` (`Int.one_le_abs`) and
`|x - y - n| ≥ 1/(q q')` for every integer `n`; take `n = round (x - y)`,
which is exactly `dist₁ x y`.
-/

namespace Salt.LS

/-- **L6.1 core.** Denominator-sharp Farey spacing: two distinct fractions
`a/q ≠ a'/q'` with `a < q`, `a' < q'` are `dist₁`-separated by at least
`1/(q q')`. Coprimality is not required. -/
theorem farey_spacing_core {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (ha : a < q) (ha' : a' < q') (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / ((q : ℝ) * q') ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  set x : ℝ := (a : ℝ) / q with hxdef
  set y : ℝ := (a' : ℝ) / q' with hydef
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg a) hqR.le
  have hx1 : x < 1 := by
    rw [hxdef, div_lt_one hqR]
    exact_mod_cast ha
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg a') hq'R.le
  have hy1 : y < 1 := by
    rw [hydef, div_lt_one hq'R]
    exact_mod_cast ha'
  -- For every integer `n`, `|x - y - n| ≥ 1/(q q')`.
  have key : ∀ n : ℤ, 1 / ((q : ℝ) * q') ≤ |x - y - (n : ℝ)| := by
    intro n
    set k : ℤ := (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - n * (q : ℤ) * (q' : ℤ)
      with hkdef
    have hxy : x - y - (n : ℝ) = (k : ℝ) / ((q : ℝ) * q') := by
      rw [hxdef, hydef, hkdef]
      push_cast
      field_simp
    have hk0 : k ≠ 0 := by
      intro h0
      apply hne
      have hz : (k : ℝ) = 0 := by exact_mod_cast h0
      have hxyn : x - y - (n : ℝ) = 0 := by rw [hxy, hz, zero_div]
      have hnlt : (n : ℝ) < 1 := by linarith
      have hngt : (-1 : ℝ) < (n : ℝ) := by linarith
      have hn0 : n = 0 := by
        have h1 : n < 1 := by exact_mod_cast hnlt
        have h2 : -1 < n := by exact_mod_cast hngt
        omega
      have hn0R : (n : ℝ) = 0 := by exact_mod_cast hn0
      linarith
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hZ : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast hZ
    rw [hxy, abs_div, abs_of_pos (mul_pos hqR hq'R)]
    gcongr
  have := key (round (x - y))
  unfold dist₁
  exact this

/-- **L6.1.** Farey spacing, `Q`-uniform form: two distinct fractions
`a/q ≠ a'/q'` with denominators bounded by a common `Q` are `dist₁`-separated
by at least `1/Q²`. Coprimality is not required. -/
theorem farey_spacing {q q' Q a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hqQ : q ≤ Q) (hq'Q : q' ≤ Q) (ha : a < q) (ha' : a' < q')
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / (Q : ℝ) ^ 2 ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hq'QR : (q' : ℝ) ≤ Q := by exact_mod_cast hq'Q
  have hcore := farey_spacing_core hq hq' ha ha' hne
  have hQR : (0 : ℝ) ≤ (Q : ℝ) := hqR.le.trans hqQR
  have hQQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have hmul : (q : ℝ) * q' ≤ (Q : ℝ) * Q := mul_le_mul hqQR hq'QR hq'R.le hQR
    nlinarith [hmul]
  have hstep : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') :=
    one_div_le_one_div_of_le (mul_pos hqR hq'R) hQQ
  exact hstep.trans hcore

end Salt.LS
