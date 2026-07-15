/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.FinLed
import Salt.Chen.A2Window

/-!
# FIN-LED-2 — the yR-top window A₂ certificate (catch #78 repair) + the shares + `hL_bundle`

Design: `docs/blueprints/flags.md`, the `2026-07-15 FIN-LED … ★ CATCH #78 ★` entry (the
adjudication: the A2WIN pattern at the top; the honest top deviation
`log(opY) − (8/3)·log(opZ) = O(x^{-1/8})`, exponentially inside a fixed tiny `δ′ = 1/1000`)
and the `2026-07-15 A2WIN` entry (`A2Window.lean` — the Dtot-window template).

## The top-window relaxation (this file, Part 1)

`A2Window.A2grid_window_le` relaxes only the **Dtot** geometry (`log Dtot ∈ [(4−8/10000)·log z,
4·log z]`) but still demands the **exact top** `log yR = (8/3)·log z` (via `agg_at_zpow4` →
`applicationA2` → `A2weight_integral_eq`).  The independently-floored `opY = ⌊x^{1/3}⌋` misses
that identity by the floor loss.  We relax the top to the window

  `(8/3)·log z ≤ log yR ≤ (8/3 + 1/1000)·log z`   (`δ′ = 1/1000`)

by the SAME reference route A2WIN uses for `Dtot`:

* **the integral** (`a2weight_integral_topwindow_le`): split `∫_z^{yR} = ∫_z^{yR0} + ∫_{yR0}^{yR}`
  at the exact reference `yR0 = exp((8/3)·log z)`.  The first is `(log 6)/4` verbatim
  (`A2weight_integral_eq`); the second is bounded by the elementary crumb `∫_{yR0}^{yR} w/(t log t)
  ≤ (1125/3997)·(log yR − (8/3)log z)/log z ≤ 1125/3997000` (constant `1/((4/3 − δ′)(8/3))`, the
  denominators frozen on the window).
* **the pointwise domination** (`A2weight_topwindow_dom`): the COMBINED Dtot+top window worsens the
  A2WIN constant `5000/4997` only to `1250/1249` (`κ_combined = δ/(4/3 − δ − δ′) = 24/39946`,
  vs A2WIN's `24/39976`); the razor cost stays within the allowance (`razor_topwindow_cost`).

## The at-op membership (Part 2)

Take `yR := (opY x : ℝ) + 1`.  Then every prime `p ≤ opY x` has `p < yR`; the LOWER edge is
CLEAN — `opY + 1 > x^{1/3}` gives `log(opY+1) ≥ (1/3)log x ≥ (8/3)·log(opZ)` (no floor subtlety);
the UPPER edge uses the floor loss on `opZ` (`opf_window_floor_bounds`, giving the `δ′` room).

No `sorry`, no `native_decide`, no new axioms.  Lean notes (FinLed): `maxRecDepth 8000`,
`linarith` over `nlinarith` in the heavy op context, explicit-`≠0` `field_simp`.
-/

namespace Salt.Chen

open Real

/-! ## Part 1a — the combined Dtot+top pointwise weight domination

Mirror of `A2Window.A2weight_window_dom` with the top filter relaxed from `log t ≤ (8/3)·log z` to
`log t ≤ (8/3 + 1/1000)·log z`.  The combined window worsens the honest `1 + κ` from `5000/4997`
to `1250/1249` (`κ = 24/39946 ≤ 1/1249`); after clearing denominators the claim reduces to the two
window filters (rational, with `~0.33·log z` margin). -/
theorem A2weight_topwindow_dom {z Dtot : ℕ} {t : ℝ} (hz2 : 2 ≤ z) (_ht0 : 0 < t)
    (htyR : Real.log t ≤ (8 / 3 + 1 / 1000) * Real.log z)
    (hLD_lo : (4 - 8 / 10000) * Real.log z ≤ Real.log Dtot) :
    A2weight z Dtot t ≤ (1250 / 1249) * A2weight z (z ^ 4) t := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hLD0 : Real.log ((z ^ 4 : ℕ) : ℝ) = 4 * Real.log z := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hden_e : 0 < 4 * Real.log z - Real.log t := by nlinarith [htyR, hL]
  have hden_a : 0 < Real.log Dtot - Real.log t := by nlinarith [hLD_lo, htyR, hL]
  have hkey : 4 * Real.log z - Real.log t
      ≤ 1250 / 1249 * (Real.log Dtot - Real.log t) := by
    nlinarith [hLD_lo, htyR, hL]
  rw [A2weight, A2weight, hLD0, ← mul_div_assoc, div_le_div_iff₀ hden_a hden_e]
  calc Real.log z * (4 * Real.log z - Real.log t)
      ≤ Real.log z * (1250 / 1249 * (Real.log Dtot - Real.log t)) :=
        mul_le_mul_of_nonneg_left hkey hL.le
    _ = 1250 / 1249 * Real.log z * (Real.log Dtot - Real.log t) := by ring

/-! ## Part 1b — the top-window integral bound (the reference split) -/

/-- **The top-window A₂ integral bound.**  On the top window `(8/3)·log z ≤ log yR ≤
(8/3 + 1/1000)·log z`, the reference-`z⁴` A₂ integrand integrates to at most `(log 6)/4` plus the
frozen crumb `1125/3997000`.  Split at the exact reference `yR0 = exp((8/3)·log z)`: the lower part
is `(log 6)/4` (`A2weight_integral_eq`); the upper part is `∫_{yR0}^{yR} w/(t log t)`, dominated by
`(1125/3997)·(1/log z)·(1/t)` on the window (frozen denominators) whose integral is
`(1125/3997)·(log yR − (8/3)log z)/log z ≤ 1125/3997000`. -/
theorem a2weight_integral_topwindow_le {z : ℕ} {yR : ℝ} (hz2 : 2 ≤ z)
    (_hzy : (z : ℝ) ≤ yR) (_hyR0 : 0 < yR)
    (hLy_lo : 8 / 3 * Real.log z ≤ Real.log yR)
    (hLy_hi : Real.log yR ≤ (8 / 3 + 1 / 1000) * Real.log z) :
    (∫ t in (z : ℝ)..yR, A2weight z (z ^ 4) t / (t * Real.log t))
      ≤ Real.log 6 / 4 + 1125 / 3997000 := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  have hlogz4 : Real.log ((z ^ 4 : ℕ) : ℝ) = 4 * Real.log z := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  -- the exact reference top `yR0 = exp((8/3)·log z)`
  set yR0 : ℝ := Real.exp (8 / 3 * Real.log z) with hyR0def
  have hyR0pos : 0 < yR0 := Real.exp_pos _
  have hlogyR0 : Real.log yR0 = 8 / 3 * Real.log z := Real.log_exp _
  have hz_yR0 : (z : ℝ) ≤ yR0 := by
    have h : Real.exp (Real.log z) ≤ Real.exp (8 / 3 * Real.log z) :=
      Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_log hzpos] at h
  have hyR0_yR : yR0 ≤ yR := by
    have h : Real.exp (8 / 3 * Real.log z) ≤ Real.exp (Real.log yR) := Real.exp_le_exp.mpr hLy_lo
    rwa [Real.exp_log _hyR0] at h
  -- the integrand is continuous on `[z, yR]`
  have hmem : ∀ t ∈ Set.Icc (z : ℝ) yR,
      0 < t ∧ 0 < Real.log ((z ^ 4 : ℕ) : ℝ) - Real.log t ∧ 0 < Real.log t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hzpos ht.1
    have htlt : (1 : ℝ) < t := lt_of_lt_of_le hz1 ht.1
    have htlog : 0 < Real.log t := Real.log_pos htlt
    refine ⟨ht0, ?_, htlog⟩
    rw [hlogz4]
    have : Real.log t ≤ Real.log yR := Real.log_le_log ht0 ht.2
    nlinarith [this, hLy_hi, hL]
  have hcont : ContinuousOn (fun t => A2weight z (z ^ 4) t / (t * Real.log t))
      (Set.Icc (z : ℝ) yR) := by
    apply ContinuousOn.div
    · apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.sub
          (Real.continuousOn_log.mono (fun t ht => (hmem t ht).1.ne'))
      · exact fun t ht => (hmem t ht).2.1.ne'
    · exact continuousOn_id.mul (Real.continuousOn_log.mono (fun t ht => (hmem t ht).1.ne'))
    · exact fun t ht => mul_ne_zero (hmem t ht).1.ne' (hmem t ht).2.2.ne'
  -- integrability on the two sub-intervals
  have hII : ∀ a b : ℝ, (z : ℝ) ≤ a → b ≤ yR → a ≤ b →
      IntervalIntegrable (fun t => A2weight z (z ^ 4) t / (t * Real.log t))
        MeasureTheory.volume a b := by
    intro a b ha hb hab
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hcont.mono (Set.Icc_subset_Icc ha hb)
  have hInt1 := hII (z : ℝ) yR0 le_rfl hyR0_yR hz_yR0
  have hInt2 := hII yR0 yR hz_yR0 le_rfl hyR0_yR
  -- the split
  have hsplit : (∫ t in (z : ℝ)..yR, A2weight z (z ^ 4) t / (t * Real.log t))
      = (∫ t in (z : ℝ)..yR0, A2weight z (z ^ 4) t / (t * Real.log t))
        + (∫ t in yR0..yR, A2weight z (z ^ 4) t / (t * Real.log t)) :=
    (intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2).symm
  -- the main part is exactly `(log 6)/4`
  have hmain : (∫ t in (z : ℝ)..yR0, A2weight z (z ^ 4) t / (t * Real.log t)) = Real.log 6 / 4 :=
    A2weight_integral_eq hz1 hyR0pos hlogz4 hlogyR0
  -- the crumb: bound the upper integral by the frozen constant
  set g : ℝ → ℝ := fun t => 1125 / 3997 / Real.log z * (1 / t) with hgdef
  have hg_int : IntervalIntegrable g MeasureTheory.volume yR0 yR := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hyR0_yR]
    apply continuousOn_const.mul
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.mem_Icc] at ht
    exact (lt_of_lt_of_le hyR0pos ht.1).ne'
  -- pointwise `w/(t log t) ≤ g` on `[yR0, yR]`
  have hptwise : ∀ t ∈ Set.Icc yR0 yR,
      A2weight z (z ^ 4) t / (t * Real.log t) ≤ g t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hyR0pos ht.1
    have htloglo : 8 / 3 * Real.log z ≤ Real.log t := by
      calc 8 / 3 * Real.log z = Real.log yR0 := hlogyR0.symm
        _ ≤ Real.log t := Real.log_le_log hyR0pos ht.1
    have htloghi : Real.log t ≤ (8 / 3 + 1 / 1000) * Real.log z := by
      calc Real.log t ≤ Real.log yR := Real.log_le_log ht0 ht.2
        _ ≤ (8 / 3 + 1 / 1000) * Real.log z := hLy_hi
    have htlogpos : 0 < Real.log t := by nlinarith [htloglo, hL]
    have hden : 0 < 4 * Real.log z - Real.log t := by nlinarith [htloghi, hL]
    -- the t-free product bound `(log z)^2 ≤ (1125/3997)·(4 log z − log t)·log t`
    have hf1 : 3997 / 3000 * Real.log z ≤ 4 * Real.log z - Real.log t := by linarith [htloghi]
    have hprod : 3997 / 3000 * Real.log z * (8 / 3 * Real.log z)
        ≤ (4 * Real.log z - Real.log t) * Real.log t :=
      mul_le_mul hf1 htloglo (by positivity) hden.le
    have hkey : Real.log z * Real.log z
        ≤ 1125 / 3997 * ((4 * Real.log z - Real.log t) * Real.log t) := by nlinarith [hprod]
    -- assemble the fraction inequality
    simp only [hgdef]
    rw [A2weight, hlogz4, div_div]
    rw [show 1125 / 3997 / Real.log z * (1 / t) = 1125 / 3997 / (Real.log z * t) by
      rw [div_mul_eq_div_div]; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, ht0, mul_pos ht0 htlogpos, hL, htlogpos]
  have hmono : (∫ t in yR0..yR, A2weight z (z ^ 4) t / (t * Real.log t))
      ≤ ∫ t in yR0..yR, g t :=
    intervalIntegral.integral_mono_on hyR0_yR hInt2 hg_int hptwise
  have hgval : (∫ t in yR0..yR, g t)
      = 1125 / 3997 / Real.log z * (Real.log yR - 8 / 3 * Real.log z) := by
    rw [hgdef, intervalIntegral.integral_const_mul,
      integral_one_div_of_pos hyR0pos _hyR0,
      Real.log_div _hyR0.ne' hyR0pos.ne', hlogyR0]
  have hgval_le : (∫ t in yR0..yR, g t) ≤ 1125 / 3997000 := by
    rw [hgval]
    have hdev : Real.log yR - 8 / 3 * Real.log z ≤ 1 / 1000 * Real.log z := by linarith [hLy_hi]
    have hcoef_nn : (0 : ℝ) ≤ 1125 / 3997 / Real.log z := by positivity
    calc 1125 / 3997 / Real.log z * (Real.log yR - 8 / 3 * Real.log z)
        ≤ 1125 / 3997 / Real.log z * (1 / 1000 * Real.log z) :=
          mul_le_mul_of_nonneg_left hdev hcoef_nn
      _ = 1125 / 3997000 := by field_simp; ring
  rw [hsplit, hmain]
  linarith [hmono, hgval_le]

/-! ## Part 1c — the top-window Abel pass and aggregation -/

/-- **The top-window monotone Abel pass at the reference `Dtot0 = z⁴`.**  The `applicationA2`
route with the exact integral replaced by `a2weight_integral_topwindow_le` (the reference split);
the four calculus hypotheses need only `log yR < 4 log z`, so the window suffices. -/
theorem applicationA2_topwindow {z : ℕ} {yR : ℝ} (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR)
    (hyR0 : 0 < yR) (hLy_lo : 8 / 3 * Real.log z ≤ Real.log yR)
    (hLy_hi : Real.log yR ≤ (8 / 3 + 1 / 1000) * Real.log z) :
    ∑ p ∈ Salt.BrunLower.primesInWindow (z : ℝ) yR, A2weight z (z ^ 4) p / p
      ≤ Real.log 6 / 4 + 1125 / 3997000 + (21 / Real.log z) * A2weight z (z ^ 4) yR := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  have hlogz4 : Real.log ((z ^ 4 : ℕ) : ℝ) = 4 * Real.log z := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hyD : Real.log yR < Real.log ((z ^ 4 : ℕ) : ℝ) := by
    rw [hlogz4]; nlinarith [hLy_hi, hL]
  have hbounds : ∀ t ∈ Set.Icc (z : ℝ) yR, 0 < t ∧ Real.log t < Real.log ((z ^ 4 : ℕ) : ℝ) := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact ⟨ht0, lt_of_le_of_lt (Real.log_le_log ht0 ht.2) hyD⟩
  have habel := prime_sum_abel_monotone (w := (z : ℝ)) (z := yR) hz2R hzy
    (f := A2weight z (z ^ 4)) (f' := A2weight_deriv z (z ^ 4))
    (fun t ht => A2weight_hasDerivAt (hbounds t ht).1 (hbounds t ht).2)
    (A2weight_deriv_intervalIntegrable hzpos hzy hyD)
    (fun t ht => A2weight_nonneg hz2 (hbounds t ht).2)
    (fun t ht => A2weight_deriv_nonneg (by omega : 1 ≤ z) (hbounds t ht).1)
  have hint := a2weight_integral_topwindow_le hz2 hzy hyR0 hLy_lo hLy_hi
  linarith [habel, hint]

/-- **The top-window exact-reference A₂ aggregation.**  Mirror of `A2Window.agg_at_zpow4` with the
exact top `log yR = (8/3)·log z` relaxed to the window; the extra `1125/3997000` is the reference
split's crumb (`a2weight_integral_topwindow_le`). -/
theorem agg_at_zpow4_topwindow (P : Finset ℕ) (z : ℕ) (yR : ℝ)
    (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR) (hyR0 : 0 < yR)
    (hLy_lo : 8 / 3 * Real.log z ≤ Real.log yR)
    (hLy_hi : Real.log yR ≤ (8 / 3 + 1 / 1000) * Real.log z)
    (hP : ∀ p ∈ P, p.Prime ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < yR) :
    ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p
      ≤ Real.log 6 / 4 + 1125 / 3997000
        + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)) := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hlogz4 : Real.log ((z ^ 4 : ℕ) : ℝ) = 4 * Real.log z := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hyD0 : Real.log yR < Real.log ((z ^ 4 : ℕ) : ℝ) := by
    rw [hlogz4]; nlinarith [hLy_hi, hL]
  have hWyR_nn : 0 ≤ A2weight z (z ^ 4) yR := A2weight_nonneg hz2 hyD0
  -- split 1/(p-1) = 1/p + 1/(p(p-1))
  have hsplit : ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p
      = (∑ p ∈ P, A2weight z (z ^ 4) p / p)
        + ∑ p ∈ P, A2weight z (z ^ 4) p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpp, _, _⟩ := hP p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    field_simp
    ring
  rw [hsplit]
  have hPsub : P ⊆ Salt.BrunLower.primesInWindow (z : ℝ) yR := by
    intro p hp
    obtain ⟨hpp, hzp, hpy⟩ := hP p hp
    rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_ceil.mpr hpy, hpp, hzp⟩
  have hwinnn : ∀ q ∈ Salt.BrunLower.primesInWindow (z : ℝ) yR,
      q ∉ P → 0 ≤ A2weight z (z ^ 4) q / q := by
    intro q hq _
    rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqc, hqp, hzq⟩ := hq
    have hqy : (q : ℝ) < yR := Nat.lt_ceil.mp hqc
    have hqD : Real.log q < Real.log ((z ^ 4 : ℕ) : ℝ) :=
      lt_of_le_of_lt (Real.log_le_log (by exact_mod_cast hqp.pos) hqy.le) hyD0
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
    exact div_nonneg (A2weight_nonneg hz2 hqD) hqpos.le
  have hmain : ∑ p ∈ P, A2weight z (z ^ 4) p / p
      ≤ Real.log 6 / 4 + 1125 / 3997000 + 21 / Real.log z * A2weight z (z ^ 4) yR := by
    calc ∑ p ∈ P, A2weight z (z ^ 4) p / p
        ≤ ∑ p ∈ Salt.BrunLower.primesInWindow (z : ℝ) yR, A2weight z (z ^ 4) p / p :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub hwinnn
      _ ≤ Real.log 6 / 4 + 1125 / 3997000 + 21 / Real.log z * A2weight z (z ^ 4) yR :=
          applicationA2_topwindow hz2 hzy hyR0 hLy_lo hLy_hi
  have hcrumb : ∑ p ∈ P, A2weight z (z ^ 4) p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ A2weight z (z ^ 4) yR * (2 / ((z : ℝ) - 1)) := by
    have hstep : ∀ p ∈ P, A2weight z (z ^ 4) p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ A2weight z (z ^ 4) yR * (2 / (p : ℝ) ^ 2) := by
      intro p hp
      obtain ⟨hpp, _, hpy⟩ := hP p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hpprod : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by positivity
      have hwp : A2weight z (z ^ 4) p ≤ A2weight z (z ^ 4) yR :=
        A2weight_le_of_log_le (by omega : 1 ≤ z) (Real.log_le_log hp0 hpy.le) hyD0
      rw [show A2weight z (z ^ 4) yR * (2 / (p : ℝ) ^ 2)
            = (2 * A2weight z (z ^ 4) yR) / (p : ℝ) ^ 2 by ring,
        div_le_div_iff₀ hpprod (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hwp (sq_nonneg (p : ℝ)),
        mul_nonneg hWyR_nn (by nlinarith [hp2] : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 2))]
    calc ∑ p ∈ P, A2weight z (z ^ 4) p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ p ∈ P, A2weight z (z ^ 4) yR * (2 / (p : ℝ) ^ 2) := Finset.sum_le_sum hstep
      _ = A2weight z (z ^ 4) yR * (2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ A2weight z (z ^ 4) yR * (2 * (1 / ((z : ℝ) - 1))) := by
          apply mul_le_mul_of_nonneg_left _ hWyR_nn
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          have hPsub2 : P ⊆ Finset.Icc z ⌊yR⌋₊ := by
            intro p hp
            obtain ⟨hpp, hzp, hpy⟩ := hP p hp
            rw [Finset.mem_Icc]
            refine ⟨by exact_mod_cast hzp, Nat.le_floor hpy.le⟩
          calc ∑ p ∈ P, 1 / (p : ℝ) ^ 2
              ≤ ∑ p ∈ Finset.Icc z ⌊yR⌋₊, 1 / (p : ℝ) ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg hPsub2 (fun p _ _ => by positivity)
            _ ≤ 1 / ((z : ℝ) - 1) := Salt.BrunLower.sum_one_div_sq_le hz2
      _ = A2weight z (z ^ 4) yR * (2 / ((z : ℝ) - 1)) := by ring
  have hcomb := add_le_add hmain hcrumb
  calc (∑ p ∈ P, A2weight z (z ^ 4) p / p)
        + ∑ p ∈ P, A2weight z (z ^ 4) p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ (Real.log 6 / 4 + 1125 / 3997000 + 21 / Real.log z * A2weight z (z ^ 4) yR)
        + A2weight z (z ^ 4) yR * (2 / ((z : ℝ) - 1)) := hcomb
    _ = Real.log 6 / 4 + 1125 / 3997000
        + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)) := by ring

/-! ## Part 1d — the top-window A₂ certificate -/

/-- **`A2grid_topwindow_le` — the combined Dtot+top window A₂ cert (catch #78 repair).**  The
`A2Window.A2grid_window_le` bound with the top hypothesis relaxed from the exact `log yR =
(8/3)·log z` to the window `[(8/3)·log z, (8/3 + 1/1000)·log z]`.  The combined domination constant
is `1250/1249` (`A2weight_topwindow_dom`); the extra `1125/3997000` is the reference-split crumb. -/
theorem A2grid_topwindow_le {Cmass : ℝ} (P : Finset ℕ) (z Dtot : ℕ) (yR : ℝ) (Nf : ℕ → ℕ)
    (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR) (hyR0 : 0 < yR) (hCmass : ∀ N, A2massSum N ≤ Cmass)
    (hLD_lo : (4 - 8 / 10000) * Real.log z ≤ Real.log Dtot)
    (hLy_lo : 8 / 3 * Real.log z ≤ Real.log yR)
    (hLy_hi : Real.log yR ≤ (8 / 3 + 1 / 1000) * Real.log z)
    (hP : ∀ p ∈ P, p.Prime ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < yR)
    (hN : ∀ p ∈ P, 1 ≤ Nf p)
    (hsrange : ∀ p ∈ P, 1 ≤ logRatio z (cdiv Dtot p) ∧ logRatio z (cdiv Dtot p) ≤ 3) :
    A2grid P z Dtot Nf
      ≤ (1250 / 1249) * ((3 + Cmass) * (Real.log 6 / 4 + 1125 / 3997000
          + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by
  have hCmass_nn : (0 : ℝ) ≤ Cmass := by have := hCmass 0; simpa [A2massSum] using this
  have h3C : (0 : ℝ) ≤ 3 + Cmass := by linarith
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  -- window ⟹ log yR < log Dtot ⟹ yR < Dtot ⟹ every p < Dtot
  have hyD : Real.log yR < Real.log Dtot := by
    have hlt : (8 / 3 + 1 / 1000 : ℝ) * Real.log z < (4 - 8 / 10000) * Real.log z :=
      mul_lt_mul_of_pos_right (by norm_num) hL
    linarith [hLD_lo, hLy_hi]
  have hDlogpos : 0 < Real.log Dtot := lt_of_le_of_lt (by nlinarith [hLy_lo, hL]) hyD
  have hDpos : (0 : ℝ) < (Dtot : ℝ) := by
    rcases Nat.eq_zero_or_pos Dtot with h0 | hpos
    · exfalso; rw [h0, Nat.cast_zero, Real.log_zero] at hDlogpos; exact lt_irrefl 0 hDlogpos
    · exact_mod_cast hpos
  have hyR_lt_D : yR < (Dtot : ℝ) := by
    have h := Real.exp_lt_exp.mpr hyD
    rwa [Real.exp_log hyR0, Real.exp_log hDpos] at h
  have hpDtot : ∀ p ∈ P, (p : ℝ) < (Dtot : ℝ) := fun p hp => lt_trans (hP p hp).2.2 hyR_lt_D
  -- FLOOR A (actual Dtot): geometry-free
  have hfloorA : A2grid P z Dtot Nf
      ≤ (3 + Cmass) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p :=
    A2grid_le_weighted P z Dtot Nf hz2 hCmass
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, hpDtot p hp⟩) hN hsrange
  -- pointwise combined domination lifted to the sum
  have hdom : ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p
      ≤ (1250 / 1249) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpp, _, hpy⟩ := hP p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp1nn : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
    have hlogp : Real.log p ≤ (8 / 3 + 1 / 1000) * Real.log z := by
      calc Real.log p ≤ Real.log yR := Real.log_le_log hp0 hpy.le
        _ ≤ (8 / 3 + 1 / 1000) * Real.log z := hLy_hi
    have hwdom : A2weight z Dtot p ≤ (1250 / 1249) * A2weight z (z ^ 4) p :=
      A2weight_topwindow_dom hz2 hp0 hlogp hLD_lo
    calc (1 / ((p : ℝ) - 1)) * A2weight z Dtot p
        ≤ (1 / ((p : ℝ) - 1)) * ((1250 / 1249) * A2weight z (z ^ 4) p) :=
          mul_le_mul_of_nonneg_left hwdom hp1nn
      _ = (1250 / 1249) * ((1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p) := by ring
  -- the top-window aggregation at the reference point
  have hagg0 := agg_at_zpow4_topwindow P z yR hz2 hzy hyR0 hLy_lo hLy_hi hP
  calc A2grid P z Dtot Nf
      ≤ (3 + Cmass) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p := hfloorA
    _ ≤ (3 + Cmass) * ((1250 / 1249) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p) :=
        mul_le_mul_of_nonneg_left hdom h3C
    _ ≤ (3 + Cmass) * ((1250 / 1249) * (Real.log 6 / 4 + 1125 / 3997000
          + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by
        apply mul_le_mul_of_nonneg_left _ h3C
        exact mul_le_mul_of_nonneg_left hagg0 (by norm_num : (0 : ℝ) ≤ 1250 / 1249)
    _ = (1250 / 1249) * ((3 + Cmass) * (Real.log 6 / 4 + 1125 / 3997000
          + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by ring

/-! ## Part 1e — the razor-compatibility numeric check (combined with catch #75)

The combined top+Dtot deviation folds into the A₂ `wtail` slot as

  `wtail_fixed = (1/1249)·(log 6/4) + (1250/1249)·(1125/3997000)`

(the multiplicative `1250/1249 − 1 = 1/1249` on `log 6/4`, plus the reference-split crumb scaled by
the domination constant).  Halved into the razor's `mainA2/2` share with the frozen mass
`Cmass = 43/75`, this stays below the error-bundle allowance `M − 1/100 = 0.002151`. -/

/-- **`razor_topwindow_cost` — the combined deviation fits the razor.**  At `Cmass = 43/75`,

  `(3 + 43/75)·((1/1249)·(log 6/4) + (1250/1249)·(1125/3997000))/2 ≤ 2151/1000000  (≈ 0.001144)`.

This is the whole catch-#78 top-window cost (it SUPERSEDES `A2Window.razor_window_cost` — the
`1250/1249` factor already absorbs the `5000/4997` Dtot deviation), sitting at ~53% of the
allowance. -/
theorem razor_topwindow_cost :
    (3 + 43 / 75 : ℝ) * ((1 / 1249) * (Real.log 6 / 4) + (1250 / 1249) * (1125 / 3997000)) / 2
      ≤ 2151 / 1000000 := by
  have hlog6 : Real.log 6 ≤ 17917596 / 10000000 := by
    have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [h6]; linarith [log_two_le, log_three_le]
  nlinarith [hlog6]

/-! ## Part 2 — the at-op top-window membership (`yR := opY x + 1`)

Taking the summation top at `(opY x : ℝ) + 1` makes every prime `p ≤ opY x` strictly below it and
discharges BOTH window edges cleanly.  The LOWER edge is exact-free: `opY + 1 > x^{1/3}` gives
`log(opY+1) ≥ (1/3)·log x ≥ (8/3)·log(opZ)`.  The UPPER edge uses the floor loss on `opZ`
(`opf_window_floor_bounds`), with the `opY → opY+1` gap `≤ 1/opY ≤ 10^{-6}` absorbed. -/

/-- **`logRatio_A2_topwindow_mem` — the top-window at op.**  For `x ≥ 10^48`,

  `(8/3)·log(opZ x) ≤ log(opY x + 1) ≤ (8/3 + 1/1000)·log(opZ x)`. -/
theorem logRatio_A2_topwindow_mem : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    8 / 3 * Real.log (opZ x) ≤ Real.log ((opY x : ℝ) + 1)
    ∧ Real.log ((opY x : ℝ) + 1) ≤ (8 / 3 + 1 / 1000) * Real.log (opZ x) := by
  refine ⟨10 ^ 48, fun x hx => ?_⟩
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hxR
  have hL96 : (96 : ℝ) ≤ Real.log (x : ℝ) := opf_log_ge_96 x hxR
  obtain ⟨-, -, hz_le, hz_ge⟩ := opf_window_floor_bounds x hxR (γ := (1 : ℝ) / 8) (by norm_num)
  obtain ⟨-, hy6, hy_le, -⟩ := opf_window_floor_bounds x hxR (γ := (1 : ℝ) / 3) (by norm_num)
  -- expose the floors
  rw [opZ, opY]
  set Z : ℝ := (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℝ) with hZdef
  set Y : ℝ := (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) with hYdef
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by norm_num) hy6
  have hlogx3 : Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) = 1 / 3 * Real.log (x : ℝ) :=
    Real.log_rpow hxpos _
  constructor
  · -- LOWER: (8/3)·log Z ≤ (1/3)·log x = log(x^{1/3}) ≤ log(Y+1)
    have hx13 : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ Y + 1 := by
      rw [hYdef]; exact (Nat.lt_floor_add_one _).le
    have hx13pos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hxpos _
    have hlog_le : Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) ≤ Real.log (Y + 1) :=
      Real.log_le_log hx13pos hx13
    rw [hlogx3] at hlog_le
    linarith [hz_le, hlog_le]
  · -- UPPER: log(Y+1) ≤ log Y + 1/Y ≤ (1/3)log x + 1/10^6 ≤ (8/3+1/1000)·log Z
    have hY6 : (10 : ℝ) ^ 6 ≤ Y := hy6
    have hgap : Real.log (Y + 1) - Real.log Y ≤ 1 / Y := by
      have hlogdiv : Real.log ((Y + 1) / Y) = Real.log (Y + 1) - Real.log Y :=
        Real.log_div (by positivity) hYpos.ne'
      have hle : Real.log ((Y + 1) / Y) ≤ (Y + 1) / Y - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hid : (Y + 1) / Y - 1 = 1 / Y := by field_simp; ring
      rw [hlogdiv, hid] at hle
      linarith [hle]
    have hinvY : 1 / Y ≤ 1 / 1000000 := by
      rw [div_le_div_iff₀ hYpos (by norm_num)]; nlinarith [hY6]
    -- (8/3+1/1000)·log Z ≥ (8/3+1/1000)·((1/8)log x − 1/999999)
    have hZlow : (8 / 3 + 1 / 1000) * ((1 / 8) * Real.log (x : ℝ) - 1 / 999999)
        ≤ (8 / 3 + 1 / 1000) * Real.log Z :=
      mul_le_mul_of_nonneg_left (by rw [hZdef]; linarith [hz_ge]) (by norm_num)
    -- log(Y+1) ≤ log Y + 1/Y ≤ (1/3)log x + 1/10^6
    have hupper : Real.log (Y + 1) ≤ 1 / 3 * Real.log (x : ℝ) + 1 / 1000000 := by
      have : Real.log Y ≤ 1 / 3 * Real.log (x : ℝ) := hy_le
      linarith [hgap, hinvY, this]
    nlinarith [hupper, hZlow, hL96]

/-! ## Part 2b — the per-prime `A2grid_le_weighted` hypotheses at op

`A2grid_topwindow_le` consumes, for each `p ∈ [opZ, opY]` prime: `1 ≤ Nf p` (the sub-sieve depth)
and `logRatio (opZ x)(cdiv (opD x) p) ∈ [1, 3]`.  The depth is `maxDepth`, blind to the extra `p`
(`twinA2SieveW_prodPrimes = opP x`), so it equals the `A₁` depth (`≥ 2`).  The operating point's
lower edge is the landed `a12_cdivStop`; the upper edge needs `cdiv (opD x) p ≤ (opZ x)^3`, from the
nat fact `cdiv·opZ ≤ opD + opZ` (`p ≥ opZ`) over the rpow bound `opD + opZ ≤ (opZ)^4`. -/

/-- **`1 ≤ maxDepth (twinA2SieveW …)`.**  Its `prodPrimes = opP x` is shared with `twinA1SieveW`, so
its `maxDepth` equals the `A₁` one (`≥ 2` by `two_le_maxDepth_A1`). -/
theorem one_le_maxDepth_A2 (x : ℕ) (p : ℕ) (hx : (4 * opW' + 1) ^ 8 ≤ x) :
    1 ≤ maxDepth (twinA2SieveW opQ opA x (opP x) p (opf_P_sq x) (opf_Podd x)) := by
  have h2 := two_le_maxDepth_A1 x hx
  have heq : maxDepth (twinA2SieveW opQ opA x (opP x) p (opf_P_sq x) (opf_Podd x))
      = maxDepth (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)) := by
    unfold maxDepth
    rw [twinA1SieveW_prodPrimes, twinA2SieveW_prodPrimes]
  omega

/-- **The `cdiv·opZ` nat bound.**  For `opZ x ≤ p`, `cdiv (opD x) p · opZ x ≤ opD x + opZ x`
(`⌈opD/p⌉·opZ ≤ (⌊(opD−1)/p⌋·p) + opZ ≤ (opD−1) + opZ`). -/
theorem cdiv_opD_mul_opZ_le (x p : ℕ) (hzp : opZ x ≤ p) :
    cdiv (opD x) p * opZ x ≤ opD x + opZ x := by
  have hcd : cdiv (opD x) p = (opD x - 1) / p + 1 := rfl
  have h1 : (opD x - 1) / p * opZ x ≤ (opD x - 1) / p * p :=
    Nat.mul_le_mul (le_refl _) hzp
  have h2 : (opD x - 1) / p * p ≤ opD x - 1 := Nat.div_mul_le_self _ _
  rw [hcd, Nat.add_mul, one_mul]
  omega

/-- **The rpow bound `opD x + opZ x ≤ (opZ x)^4`.**  With `C = x^{1/8}`, `opD ≤ x^{1/2−9/100000}=B`
(floor), `opZ ∈ [C−1, C]`; `A := x^{1/2} = C^4`, `B ≥ C^3`, and `A − B ≥ B·(9/100000)·log x ≥
36·C^3 ≥ 4C^3 + C` (once `log x ≥ 400000`), giving `B + C ≤ A − 4C^3 ≤ (C−1)^4 ≤ (opZ)^4`. -/
theorem opD_add_opZ_le_opZ_pow4 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (opD x : ℝ) + (opZ x : ℝ) ≤ (opZ x : ℝ) ^ 4 := by
  obtain ⟨xL, hLog⟩ := a12_log_ge 400000
  refine ⟨max xL (10 ^ 48), fun x hx => ?_⟩
  have hxL : xL ≤ x := le_trans (le_max_left _ _) hx
  have hx48 : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx48
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48
  have hlnx : (400000 : ℝ) ≤ Real.log x := (hLog x hxL).2
  set C : ℝ := (x : ℝ) ^ ((1 : ℝ) / 8) with hCdef
  set B : ℝ := (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) with hBdef
  have hCpos : 0 < C := Real.rpow_pos_of_pos hxpos _
  have hC6 : (10 : ℝ) ^ 6 ≤ C := by
    obtain ⟨hApow, _, _, _⟩ := opf_window_floor_bounds x hx48 (γ := (1 : ℝ) / 8) (by norm_num)
    exact hApow
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC6
  have hopZ_hi : (opZ x : ℝ) ≤ C := by rw [opZ, hCdef]; exact Nat.floor_le hCpos.le
  have hopZ_lo : C - 1 ≤ (opZ x : ℝ) := by
    rw [opZ, hCdef]; linarith [Nat.lt_floor_add_one C]
  have hopD_hi : (opD x : ℝ) ≤ B := by
    rw [opD, hBdef]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hC4 : C ^ 4 = (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [hCdef, ← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 8)) 4, ← Real.rpow_mul hxpos.le]
    norm_num
  have hC3le : C ^ 3 ≤ B := by
    have hC3 : C ^ 3 = (x : ℝ) ^ ((3 : ℝ) / 8) := by
      rw [hCdef, ← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 8)) 3, ← Real.rpow_mul hxpos.le]
      norm_num
    rw [hC3, hBdef]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hBnn : 0 ≤ B := le_trans (by positivity) hC3le
  -- A − B ≥ B·(9/100000)·log x
  have hAeq : (x : ℝ) ^ ((9 : ℝ) / 100000) * B = (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [hBdef, ← Real.rpow_add hxpos]; norm_num
  have hexpge : 1 + 9 / 100000 * Real.log x ≤ (x : ℝ) ^ ((9 : ℝ) / 100000) := by
    rw [Real.rpow_def_of_pos hxpos]
    have := Real.add_one_le_exp (Real.log x * (9 / 100000))
    linarith [this]
  have hABlb : B * (9 / 100000) * Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 2) - B := by
    have hmul : B * (1 + 9 / 100000 * Real.log x) ≤ B * (x : ℝ) ^ ((9 : ℝ) / 100000) :=
      mul_le_mul_of_nonneg_left hexpge hBnn
    rw [mul_comm ((x : ℝ) ^ ((9 : ℝ) / 100000)) B] at hAeq
    nlinarith [hmul, hAeq]
  -- 36·C^3 ≤ A − B
  have h36 : 36 * C ^ 3 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) - B := by
    have hstep : C ^ 3 * (9 / 100000) * 400000 ≤ B * (9 / 100000) * Real.log x :=
      mul_le_mul (mul_le_mul_of_nonneg_right hC3le (by norm_num)) hlnx (by norm_num)
        (by positivity)
    nlinarith [hstep, hABlb]
  -- assemble
  have hfinal2 : B + (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) - 4 * C ^ 3 := by
    have hC2 : (10 : ℝ) ^ 12 ≤ C ^ 2 := by nlinarith [hC6, hCpos]
    have h32 : 4 * C ^ 3 + C ≤ 36 * C ^ 3 := by nlinarith [hC2, hCpos]
    linarith [h36, h32, hopZ_hi]
  have hfinal3 : (x : ℝ) ^ ((1 : ℝ) / 2) - 4 * C ^ 3 ≤ (C - 1) ^ 4 := by
    nlinarith [hC4, sq_nonneg (3 * C - 1)]
  have hfinal4 : (C - 1) ^ 4 ≤ (opZ x : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by linarith [hC6]) hopZ_lo 4
  linarith [hopD_hi, hfinal2, hfinal3, hfinal4]

/-- **`logRatio_cdiv_le_three` — the `s_p ≤ 3` operating range at op.**  For `p ∈ [opZ, opY]` prime,
`logRatio (opZ x)(cdiv (opD x) p) ≤ 3` via `cdiv (opD x) p ≤ (opZ x)^3`. -/
theorem logRatio_cdiv_le_three : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
      logRatio (opZ x) (cdiv (opD x) p) ≤ 3 := by
  obtain ⟨x₁, hpow⟩ := opD_add_opZ_le_opZ_pow4
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max x₁ xt, fun x hx p hp => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxt : xt ≤ x := le_trans (le_max_right _ _) hx
  have hz3 : 3 ≤ opZ x := (htower x hxt).2.2.2.1
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hzp, _⟩, _⟩ := hp
  have hzR1 : (1 : ℝ) < (opZ x : ℝ) := by exact_mod_cast (by omega : 1 < opZ x)
  have hlogz : 0 < Real.log (opZ x) := Real.log_pos hzR1
  have hzpos : (0 : ℝ) < (opZ x : ℝ) := by linarith
  have hnat := cdiv_opD_mul_opZ_le x p hzp
  have hpow' := hpow x hx1
  have hcdivR : (cdiv (opD x) p : ℝ) * (opZ x : ℝ) ≤ (opZ x : ℝ) ^ 4 := by
    have h1 : ((cdiv (opD x) p * opZ x : ℕ) : ℝ) ≤ ((opD x + opZ x : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at h1
    linarith [h1, hpow']
  have hcdiv3 : (cdiv (opD x) p : ℝ) ≤ (opZ x : ℝ) ^ 3 := by
    have h4 : (cdiv (opD x) p : ℝ) * (opZ x : ℝ) ≤ (opZ x : ℝ) ^ 3 * (opZ x : ℝ) := by
      rw [show (opZ x : ℝ) ^ 3 * (opZ x : ℝ) = (opZ x : ℝ) ^ 4 by ring]; exact hcdivR
    exact le_of_mul_le_mul_right h4 hzpos
  have hcdivpos : (0 : ℝ) < (cdiv (opD x) p : ℝ) := by
    have : 1 ≤ cdiv (opD x) p := Nat.le_add_left 1 _
    exact_mod_cast lt_of_lt_of_le (by norm_num) this
  have hlogcdiv : Real.log (cdiv (opD x) p) ≤ 3 * Real.log (opZ x) := by
    calc Real.log (cdiv (opD x) p)
        ≤ Real.log ((opZ x : ℝ) ^ 3) := Real.log_le_log hcdivpos hcdiv3
      _ = 3 * Real.log (opZ x) := by rw [Real.log_pow]; push_cast; ring
  rw [logRatio, div_le_iff₀ hlogz]
  linarith [hlogcdiv]

/-! ## Part 2c — `hcertA2_at_op`: the A₂ grid cert at the operating point -/

/-- **`hcertA2_at_op` — the `M2` A₂ grid bounded at op** (catch #78 repair, wired).  The `M2`
carrier's `A2grid` symbol is bounded by `A2grid_topwindow_le` at `z = opZ x`, `Dtot = opD x`,
`yR = opY x + 1`, `Cmass = 43/75`, with all per-prime and window hypotheses discharged: the Dtot
window via `logRatio_A2_window_mem`, the TOP window via `logRatio_A2_topwindow_mem`, the depth via
`one_le_maxDepth_A2`, and the operating range via `a12_cdivStop` (lower) / `logRatio_cdiv_le_three`
(upper). -/
theorem hcertA2_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    A2grid ((Finset.Icc (opZ x) (opY x)).filter Nat.Prime) (opZ x) (opD x)
        (fun p => maxDepth (twinA2SieveW opQ opA x (opP x) p (opf_P_sq x) (opf_Podd x)))
      ≤ (1250 / 1249) * ((3 + 43 / 75) * (Real.log 6 / 4 + 1125 / 3997000
          + A2weight (opZ x) ((opZ x) ^ 4) ((opY x : ℝ) + 1)
              * (21 / Real.log (opZ x) + 2 / ((opZ x : ℝ) - 1)))) := by
  obtain ⟨xW, hW⟩ := logRatio_A2_window_mem
  obtain ⟨xT, hT⟩ := logRatio_A2_topwindow_mem
  obtain ⟨xS, hS⟩ := a12_cdivStop
  obtain ⟨xU, hU⟩ := logRatio_cdiv_le_three
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max (max xW xT) (max xS xU)) (max xt ((4 * opW' + 1) ^ 8)), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hxW, hxT⟩, hxS, hxU⟩, hxt, hx8⟩ := hx
  obtain ⟨_, _, _, hz3, _, _, hzy, _, _, _, _, _, _, _, _, _, _⟩ := htower x hxt
  have hz2 : 2 ≤ opZ x := by omega
  have hzyR : (opZ x : ℝ) ≤ (opY x : ℝ) + 1 := by
    have : (opZ x : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hzy
    linarith
  -- the Dtot window (opD = ⌊x^{1/2−9/100000}⌋)
  obtain ⟨hLD_lo, _⟩ := hW x hxW
  have hLDlo' : (4 - 8 / 10000) * Real.log (opZ x) ≤ Real.log (opD x) := by
    rw [opZ, opD]; exact hLD_lo
  -- the top window (yR = opY + 1)
  obtain ⟨hLy_lo, hLy_hi⟩ := hT x hxT
  apply A2grid_topwindow_le _ (opZ x) (opD x) ((opY x : ℝ) + 1) _ hz2 hzyR (by positivity)
    A2massSum_le_final hLDlo' hLy_lo hLy_hi
  · -- hP
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hzp, hpy⟩, hpp⟩ := hp
    refine ⟨hpp, by exact_mod_cast hzp, ?_⟩
    have : (p : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hpy
    linarith
  · -- hN
    intro p _; exact one_le_maxDepth_A2 x p hx8
  · -- hsrange
    intro p hp
    exact ⟨hS x hxS p hp, hU x hxU p hp⟩

end Salt.Chen
