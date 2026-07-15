/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.ChainValues

/-!
# C1b″ — the per-level value cascade (propagation engine + the first level past the anchor)

Design: `docs/blueprints/chen.md`, the C1b′/C1cσ rows; flags `2026-07-13 C1b′` and `C1cσ`.

C1b′ (`ChainValues.lean`) landed the value-certification **interface**
(`fchain_lower_of_evenSum_le`/`Fchain_upper_of_oddSum_le`), the sharp **leading** per-level bound
`fseq_two_le_sq` (`f₂(s) ≤ (4−s)²/(s(s−1))` on `[2,4]`, the one-integration `fseq_two_window`
template), and the sharp truncation tail (`fchain_trunc_close`), and isolated the remaining sharp
head (the even/odd levels `4 ≤ n ≲ 2048` at the operating point) as the **C1cσ debt**.

This file supplies the **reusable propagation engine** that a sharp cascade runs on
(`fseq_next_le_of_shift_majorant` — the single integral-comparison step, extracted from the
`fseq_le` `windowbd` pattern into a general lemma keyed on the recursion's window equation) and the
**first genuine level past the `f₂` anchor** — `f₃` — worked in the exact `fseq_two_le_sq`
one-integration style on both its regions (`fseq_three_tail_le` on the tail window `[3,5]`,
`fseq_three_flat_le` on the flat window `[1,3]`), via the propagated `f₂`-majorant integral
`integral_M3`.

## The certification arithmetic (computed pre-code; the honest cascade design and its wall)

`fchain N s = 1 − Σ_{n even ≤ N} fₙ(s)`; `Fchain N s = 1 + Σ_{n odd ≤ N} fₙ(s)`.  Numeric
DDE-integration (rational-arithmetic verified against the C1b′ table) gives the two operating sums:

* **A₁ even sum** (worst point `s = 39/10`, sup): `Σ_{even} = 0.027525` (`fchain = 0.972475`); at
  `s = 4`: `0.021646` (`fchain = 0.978354`).  Per-two-level ratio `→ 0.5224`.
* **A₂ odd sum** (worst point `s = 4/3`, sup): `Σ_{odd} = 1.671609` (`Fchain = 2.671609`); at
  `s = 3/2`: `1.374764`.

**Which target is closable.**  The A₂ ledger target `supF ≤ 2.68` (odd-sum `≤ 1.68`) has the true
sup `2.671609 < 2.68` — **closable with `0.5%` headroom** by a sharp uniform-on-`[4/3,3]` bound.
The A₁ ledger target `fchain ≥ 0.9779` (even-sum `≤ 0.0221`) is the value **at `s = 4`**; the
worst-case-on-`[39/10,4]` even sum is `0.027525` (`fchain = 0.9725`), so **no uniform bound on
`[39/10,4]` reaches `0.9779`** — the ledger's A₁ target is pinned to `s ≈ 4`, an adjudication left
to C5/Fable (the C0 margins may absorb the `0.972 → 0.978` gap).

**The sharpness wall (machine-relevant finding, per Iron Rule 4).**  Both targets have `≤ 0.5%`
headroom, so the per-level majorants must be within a few `%` of the truth *summed*.  The
closed-form `fseq_two_window`-style route (a rational majorant + `log x ≤ x−1`) is **`2.3–3.1×`
too loose** — the `log`-linearization is crude near each iterate's left endpoint (`M₂(2) = 2` vs
`f₂(2) = 0.648`), and this factor *compounds* per level (`∫₂⁴ M₂ = 0.797` vs true `0.294`;
`f₃`-bound `= 2.71×` truth at every point — see `fseq_three_tail_le`).  So the closed-form cascade
is **not load-bearing**, and grinding it to `n = 8` (each further level's antiderivative acquiring
`log/u` terms ⇒ dilogarithms) is both compute-infeasible in budget and provably non-load-bearing.
A **load-bearing** cascade needs **fine-knot piecewise-linear majorants integrated exactly** (no
`log`-linearization): the genuine C1cσ artifact.  The engine here is exactly its per-level step
(`fseq n ≤ (piecewise-linear) ⇒ fseq (n+1) ≤ (1/s)∫ (piecewise-linear)`), and `f₃` is the honest
first level demonstrating composition.

**What is certified here (sorry-free, axiom-clean).**  The propagation engine and the genuine
`f₃` majorant on both regions.  These are `2.71×`-loose (non-load-bearing), which is honest: the
sharp constants remain the C1cσ debt (see the flags).
-/

open intervalIntegral MeasureTheory Set

namespace Salt.Chen

/-! ## Part A — the propagation engine (the per-level step of any `fₙ`-majorant cascade)

The Rosser recursion on its window is `fseq (n+1) s = (1/s)·∫ fseq n (t−1)` (BJS (16)/(17), the
`fseq_even_window`/`fseq_odd_tail_window`/`fseq_odd_flat_window` unfoldings).  Given any upper
bound `g` on the shifted integrand `t ↦ fseq n (t−1)` over the integration range, monotonicity of
the integral propagates it one level.  This is the `windowbd` core of `fseq_le` (`Tail.lean`)
extracted as a general lemma: pass the window equation as `hform` and it serves the even window
(`lo = s`), the odd tail (`lo = s`), and the odd flattening (`lo = 3`) uniformly. -/

/-- **The cascade's per-level step.**  If the shifted iterate `t ↦ fseq n (t−1)` is dominated on
`[lo, up]` by an integrable `g`, then the next iterate is dominated by `(1/s)·∫ g`.  `hform` is the
recursion's window equation (any of `fseq_even_window`, `fseq_odd_tail_window`,
`fseq_odd_flat_window`); `s > 0` and `lo ≤ up` orient the `(1/s)·` factor and the integral. -/
theorem fseq_next_le_of_shift_majorant {n : ℕ} {s lo up : ℝ} {g : ℝ → ℝ}
    (hform : fseq (n + 1) s = (1 / s) * ∫ t in lo..up, fseq n (t - 1))
    (hs0 : 0 < s) (hlo : lo ≤ up)
    (hg : ∀ t ∈ Set.Icc lo up, fseq n (t - 1) ≤ g t)
    (hgii : IntervalIntegrable g volume lo up) :
    fseq (n + 1) s ≤ (1 / s) * ∫ t in lo..up, g t := by
  rw [hform]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 1 / s)
  exact intervalIntegral.integral_mono_on hlo
    (fseq_shift_intervalIntegrable n lo up) hgii hg

/-! ## Part B — the level-3 machinery: the propagated `f₂`-majorant and its exact integral

The `f₂` majorant of C1b′ is `f₂(u) ≤ (4−u)²/(u(u−1))` on `[2,4]` (`fseq_two_le_sq`).  Its shift
`u = t−1` is `M₃(t) := (5−t)²/((t−1)(t−2))`, the integrand of the `f₃` recursion; its exact
antiderivative is `t − 16·log(t−1) + 9·log(t−2)` (partial fractions
`(5−t)²/((t−1)(t−2)) = 1 − 16/(t−1) + 9/(t−2)`). -/

/-- **The exact `M₃`-integral.**  `∫_a^b (5−t)²/((t−1)(t−2)) dt = G(b) − G(a)` with
`G(u) = u − 16·log(u−1) + 9·log(u−2)`, for `2 < a ≤ b` (the region where both logs' arguments are
positive).  The `fseq_two_window` one-integration step, propagated to level 3. -/
theorem integral_M3 {a b : ℝ} (ha : 2 < a) (hab : a ≤ b) :
    (∫ t in a..b, (5 - t) ^ 2 / ((t - 1) * (t - 2)))
      = (b - 16 * Real.log (b - 1) + 9 * Real.log (b - 2))
        - (a - 16 * Real.log (a - 1) + 9 * Real.log (a - 2)) := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u => u - 16 * Real.log (u - 1) + 9 * Real.log (u - 2))
        ((5 - t) ^ 2 / ((t - 1) * (t - 2))) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht2 : 2 < t := lt_of_lt_of_le ha ht.1
    have h1 : (t - 1) ≠ 0 := by linarith
    have h2 : (t - 2) ≠ 0 := by linarith
    have hlog1 : HasDerivAt (fun u : ℝ => Real.log (u - 1)) (1 / (t - 1)) t := by
      simpa using ((hasDerivAt_id t).sub_const 1).log h1
    have hlog2 : HasDerivAt (fun u : ℝ => Real.log (u - 2)) (1 / (t - 2)) t := by
      simpa using ((hasDerivAt_id t).sub_const 2).log h2
    have hcomb : HasDerivAt (fun u => u - 16 * Real.log (u - 1) + 9 * Real.log (u - 2))
        (1 - 16 * (1 / (t - 1)) + 9 * (1 / (t - 2))) t :=
      (((hasDerivAt_id t).sub (hlog1.const_mul 16)).add (hlog2.const_mul 9))
    have hval : (1 - 16 * (1 / (t - 1)) + 9 * (1 / (t - 2)))
        = (5 - t) ^ 2 / ((t - 1) * (t - 2)) := by
      field_simp; ring
    rwa [hval] at hcomb
  have hint : IntervalIntegrable (fun t => (5 - t) ^ 2 / ((t - 1) * (t - 2))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact ((continuous_const.sub continuous_id).pow 2).continuousOn
    · exact ((continuous_id.sub continuous_const).mul
        (continuous_id.sub continuous_const)).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht2 : 2 < t := lt_of_lt_of_le ha ht.1
      have : (0 : ℝ) < (t - 1) * (t - 2) := by nlinarith
      exact ne_of_gt this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- The shifted `f₂` majorant on the `f₃`-integrand range `[3,5]`:
`f₂(t−1) ≤ (5−t)²/((t−1)(t−2))` (`fseq_two_le_sq` at argument `t−1 ∈ [2,4]`). -/
theorem fseq2_shift_le_M3 {t : ℝ} (ht3 : 3 ≤ t) (ht5 : t ≤ 5) :
    fseq 2 (t - 1) ≤ (5 - t) ^ 2 / ((t - 1) * (t - 2)) := by
  have h := fseq_two_le_sq (s := t - 1) (by linarith) (by linarith)
  calc fseq 2 (t - 1) ≤ (4 - (t - 1)) ^ 2 / ((t - 1) * ((t - 1) - 1)) := h
    _ = (5 - t) ^ 2 / ((t - 1) * (t - 2)) := by ring

/-- `M₃` is interval integrable on `[a,b]` for `2 < a ≤ b` (continuous, denominator nonzero). -/
theorem M3_intble {a b : ℝ} (ha : 2 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (5 - t) ^ 2 / ((t - 1) * (t - 2))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · exact ((continuous_const.sub continuous_id).pow 2).continuousOn
  · exact ((continuous_id.sub continuous_const).mul
      (continuous_id.sub continuous_const)).continuousOn
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht2 : 2 < t := lt_of_lt_of_le ha ht.1
    have : (0 : ℝ) < (t - 1) * (t - 2) := by nlinarith
    exact ne_of_gt this

/-! ## Part C — the first level past the anchor: `f₃` on both regions

`f₃` is the leading **odd** iterate past `f₁`; on `[4/3,3]` it is the largest odd-sum term after
`f₁`.  Here is its certified majorant by one propagation of the `f₂` bound through the engine — the
exact `fseq_two_le_sq` template at level 3.  (NB: `2.71×`-loose, inherited from `M₂`'s
`log`-linearization; genuine but non-load-bearing, per the module note.) -/

/-- **`f₃` on the tail window `[3,5]`.**  `f₃(s) ≤ [G(5) − G(s)]/s` with
`G(u) = u − 16·log(u−1) + 9·log(u−2)`, i.e.
`f₃(s) ≤ ((5 − 16·log 4 + 9·log 3) − (s − 16·log(s−1) + 9·log(s−2)))/s`.  One integration of the
`f₂` majorant (BJS (16), odd-tail branch). -/
theorem fseq_three_tail_le {s : ℝ} (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    fseq 3 s ≤ ((5 - 16 * Real.log 4 + 9 * Real.log 3)
      - (s - 16 * Real.log (s - 1) + 9 * Real.log (s - 2))) / s := by
  have hs0 : 0 < s := by linarith
  have hform : fseq (2 + 1) s = (1 / s) * ∫ t in s..((2 : ℕ) : ℝ) + 3, fseq 2 (t - 1) :=
    fseq_odd_tail_window (n := 2) (by norm_num) (by decide) hs3
  have hup : ((2 : ℕ) : ℝ) + 3 = 5 := by norm_num
  rw [hup] at hform
  have hstep := fseq_next_le_of_shift_majorant (n := 2) (s := s) (lo := s) (up := 5)
    (g := fun t => (5 - t) ^ 2 / ((t - 1) * (t - 2))) hform hs0 (by linarith)
    (fun t ht => fseq2_shift_le_M3 (by linarith [ht.1]) ht.2)
    (M3_intble (by linarith) (by linarith))
  rw [integral_M3 (by linarith) (by linarith)] at hstep
  have a1 : Real.log ((5 : ℝ) - 1) = Real.log 4 := by norm_num
  have a2 : Real.log ((5 : ℝ) - 2) = Real.log 3 := by norm_num
  rw [a1, a2, one_div, ← div_eq_inv_mul] at hstep
  exact hstep

/-- **`f₃` on the flat window `[1,3]`.**  The (17) flattening makes `f₃` constant-over-`s`:
`f₃(s) ≤ (2 − 16·log 2 + 9·log 3)/s` (the bracket `= ∫₂⁴ M₂ = G(5) − G(3)`, numerically
`≈ 0.797`).  On `[4/3,3]` this is the leading odd-sum term after `f₁`. -/
theorem fseq_three_flat_le {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    fseq 3 s ≤ (2 - 16 * Real.log 2 + 9 * Real.log 3) / s := by
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rcases eq_or_lt_of_le hs3 with h | hlt
  · -- s = 3: the tail lemma at s = 3 (tail and flat agree at the junction)
    subst h
    have hval := fseq_three_tail_le (s := 3) (by norm_num) (by norm_num)
    have e : ((5 - 16 * Real.log 4 + 9 * Real.log 3)
        - (3 - 16 * Real.log (3 - 1) + 9 * Real.log (3 - 2))) / 3
        = (2 - 16 * Real.log 2 + 9 * Real.log 3) / 3 := by
      have h31 : Real.log ((3 : ℝ) - 1) = Real.log 2 := by norm_num
      have h32 : Real.log ((3 : ℝ) - 2) = Real.log 1 := by norm_num
      rw [h31, h32, Real.log_one, hl4]; ring
    rwa [e] at hval
  · have hs0 : 0 < s := by linarith
    have hform : fseq (2 + 1) s = (1 / s) * ∫ t in (3 : ℝ)..((2 : ℕ) : ℝ) + 3, fseq 2 (t - 1) :=
      fseq_odd_flat_window (n := 2) (by norm_num) (by decide) hs1 hlt
    have hup : ((2 : ℕ) : ℝ) + 3 = 5 := by norm_num
    rw [hup] at hform
    have hstep := fseq_next_le_of_shift_majorant (n := 2) (s := s) (lo := 3) (up := 5)
      (g := fun t => (5 - t) ^ 2 / ((t - 1) * (t - 2))) hform hs0 (by norm_num)
      (fun t ht => fseq2_shift_le_M3 ht.1 ht.2)
      (M3_intble (by norm_num) (by norm_num))
    rw [integral_M3 (by norm_num) (by norm_num)] at hstep
    have e : ((5 - 16 * Real.log ((5 : ℝ) - 1) + 9 * Real.log ((5 : ℝ) - 2))
        - (3 - 16 * Real.log ((3 : ℝ) - 1) + 9 * Real.log ((3 : ℝ) - 2)))
        = (2 - 16 * Real.log 2 + 9 * Real.log 3) := by
      have a1 : Real.log ((5 : ℝ) - 1) = Real.log 4 := by norm_num
      have a2 : Real.log ((5 : ℝ) - 2) = Real.log 3 := by norm_num
      have a3 : Real.log ((3 : ℝ) - 1) = Real.log 2 := by norm_num
      have a4 : Real.log ((3 : ℝ) - 2) = Real.log 1 := by norm_num
      rw [a1, a2, a3, a4, Real.log_one, hl4]; ring
    rw [e, one_div, ← div_eq_inv_mul] at hstep
    exact hstep

end Salt.Chen
