/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SharpFuncbound

/-!
# E₁a-flat — the odd-flat funcbound `∫_2^c h ≤ (97/100)·s·h(s)` on `1 ≤ s ≤ 3`

The odd-flat companion of `SharpFuncbound.hBJS_funcbound_sharp`.  Where E₁a bounds the
*shifting* integral `∫_{s−1}^c h` on the operating window `s ≥ 2`, BJS's odd-level Lemma 10
also needs the **fixed** integral `H(3) = ∫_3^∞ h(t−1)dt = ∫_2^∞ h(u)du` (after the `t−1`
shift) bounded by `κ̃·s·h(s)` down to `s = 1`, where E₁a's `κ₃ = 49/50` window does not
reach.  Here we land **`κ̃B = 97/100`** on the odd-flat window `1 ≤ s ≤ 3`.

## What is proved (sorry-free, axiom-clean)

* **The odd-flat functional bound** (`hBJS_funcbound_flat`): for `1 ≤ s ≤ 3` and any upper
  limit `c`, `∫_2^c h(u) du ≤ (97/100)·s·h(s)`.  The lower limit is the FIXED `2` (the shifted
  `H(3)`), not the moving `s−1` of E₁a.  Route: the sharp fixed-integral value
  `SharpFuncbound.hBJS_intbound_from2_sharp` gives `∫_2^c h ≤ e⁻² − (1/9)e⁻³` for **all** `c`
  (the same nonnegativity-handled arbitrary-`c` treatment as E₁a), while the window minimum of
  `s·h(s)` over `[1,3]` is `e⁻²` (attained at `s = 1`; the `[2,3]` branch stays `≥ e⁻²` since
  `e^{s−2} ≤ s` there, via the same Padé panel `(4−s)e^{s−2} ≤ s`).  Closing:
  `e⁻² − (1/9)e⁻³ ≤ (97/100)e⁻²` ⟺ `(3/100)e⁻² ≤ (1/9)e⁻³` ⟺ `27e ≤ 100`
  (`e ≤ 100/27 ≈ 3.7037`), which holds with room since `e < 2.7182818286`.

* **The consumption corollary** (`flat_h_contract`, mirroring `TauSharp.sharp_h_contract`):
  `(1/s)·∫_2^c h ≤ (97/100)·h(s)` on `1 ≤ s ≤ 3` — dividing through by `s > 0`.

## The constant

`κ̃B = 97/100 < 49/50 = κ₃` (E₁a), so the odd-flat plug does not disturb the sharp
`chSharpB` contraction (which requires `κ̃B < 49/50`).  The freeze margin is `1.1 %` at the
worst point `s = 1` (true value `H(3) ≈ 0.12469`, bound `≈ 0.1298`, target `0.97e⁻² ≈ 0.13127`).
-/

open MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-- The odd-flat window minimum: `e⁻² ≤ s·h(s)` for `1 ≤ s ≤ 3` (attained at `s = 1`).
On `[1,2]` the flat branch gives `s·e⁻² ≥ e⁻²` (since `s ≥ 1`); on `[2,3]` the decay branch
gives `s·e⁻ˢ ≥ e⁻²` because `e^{s−2} ≤ (4−s)e^{s−2} ≤ s` (the Padé panel with `4−s ≥ 1`). -/
theorem hBJS_window_min {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : Real.exp (-2) ≤ s * hBJS s := by
  rcases le_total s 2 with h2 | h2
  · -- flat branch `s ≤ 2`: `s·e⁻² ≥ e⁻²`
    rw [hBJS_le2 h2]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ s - 1) (Real.exp_pos (-2 : ℝ)).le]
  · -- decay branch `2 ≤ s ≤ 3`: `s·e⁻ˢ ≥ e⁻²` via `e^{s−2} ≤ s`
    rw [hBJS_mid h2 hs3]
    have hpade : (4 - s) * Real.exp (s - 2) ≤ s := by
      have h := exp_pade_upper (x := s - 2) (by linarith) (by linarith)
      have e1 : (2 - (s - 2)) = 4 - s := by ring
      have e2 : (2 + (s - 2)) = s := by ring
      rw [e1, e2] at h; exact h
    have hexp_le : Real.exp (s - 2) ≤ s := by
      have h1 : Real.exp (s - 2) ≤ (4 - s) * Real.exp (s - 2) := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - s) (Real.exp_pos (s - 2)).le]
      linarith [hpade, h1]
    have eid : Real.exp (-2) = Real.exp (s - 2) * Real.exp (-s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [eid]
    exact mul_le_mul_of_nonneg_right hexp_le (Real.exp_pos _).le

/-- **E₁a-flat — the odd-flat `hBJS` functional integral bound** (BJS Lemma 10's fixed-`H(3)`
`κ̃`-bound).  For `1 ≤ s ≤ 3` and any upper limit `c`, `∫_2^c h(u) du ≤ (97/100)·s·h(s)`.
The lower limit is the FIXED `2` (the shifted `H(3) = ∫_3^∞ h(t−1)dt`); `c` is arbitrary, as
in E₁a (the sharp fixed-integral bound handles `c ≤ 2` by nonnegativity).  Closes at `97/100`
because `e ≤ 100/27`; the constant `97/100 < 49/50` leaves the sharp contraction intact. -/
theorem hBJS_funcbound_flat (s c : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    (∫ u in (2 : ℝ)..c, hBJS u) ≤ (97 / 100) * s * hBJS s := by
  -- fixed-integral value (all `c`, via the sharp parts-twice tail bound)
  have hLHS : (∫ u in (2 : ℝ)..c, hBJS u) ≤ Real.exp (-2) - (1 / 9) * Real.exp (-3) :=
    hBJS_intbound_from2_sharp c
  -- `e⁻² − (1/9)e⁻³ ≤ (97/100)e⁻²`  ⟺  `27e ≤ 100`
  have hclose : Real.exp (-2) - (1 / 9) * Real.exp (-3) ≤ (97 / 100) * Real.exp (-2) := by
    have e2id : Real.exp (-2) = Real.exp 1 * Real.exp (-3) := by rw [← Real.exp_add]; norm_num
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h3pos : (0 : ℝ) < Real.exp (-3) := Real.exp_pos _
    rw [e2id]
    nlinarith [he, h3pos, mul_pos (by linarith : (0 : ℝ) < 2.7182818286 - Real.exp 1) h3pos]
  -- window minimum `e⁻² ≤ s·h(s)` lifts the constant target to the general `s`
  have key_min : Real.exp (-2) ≤ s * hBJS s := hBJS_window_min hs1 hs3
  have hassoc : (97 / 100) * (s * hBJS s) = (97 / 100) * s * hBJS s := by ring
  have hRHS : (97 / 100) * Real.exp (-2) ≤ (97 / 100) * s * hBJS s := by
    rw [← hassoc]; exact mul_le_mul_of_nonneg_left key_min (by norm_num)
  linarith [hLHS, hclose, hRHS]

/-- **E₁a-flat consumption** (the τ-relative odd-flat `h`-contraction, mirroring
`TauSharp.sharp_h_contract`).  For `1 ≤ s ≤ 3`, the fixed loglog-integral of `h` over `[2, c]`,
scaled by the density factor `1/s`, is `≤ (97/100)·h(s)`.  Directly consumes
`hBJS_funcbound_flat`: dividing by `s > 0` cancels the `s`. -/
theorem flat_h_contract (s c : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    (1 / s) * (∫ u in (2 : ℝ)..c, hBJS u) ≤ (97 / 100) * hBJS s := by
  have hs0 : 0 < s := by linarith
  have hsne : s ≠ 0 := ne_of_gt hs0
  have h := hBJS_funcbound_flat s c hs1 hs3
  have hinv : (0 : ℝ) ≤ 1 / s := by positivity
  calc (1 / s) * (∫ u in (2 : ℝ)..c, hBJS u)
      ≤ (1 / s) * ((97 / 100) * s * hBJS s) := mul_le_mul_of_nonneg_left h hinv
    _ = (97 / 100) * hBJS s := by field_simp
end Salt.Chen
