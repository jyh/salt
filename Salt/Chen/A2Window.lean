/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.A2Weighted
import Salt.Chen.WindowMembership
import Salt.Chen.LogToolkit

/-!
# A2WIN — the window-perturbed A₂ certificate (catch #75 repair, additive)

Design: `docs/blueprints/flags.md`, the `2026-07-15 PACK-A ✅ … ★ CATCH #75 ★` entry (the
adjudicated repair) and the `2026-07-14 A2W` entry (the landed cert's structure).  The landed
`A2Weighted.A2grid_sharp_le` demands the **exact** geometry `Real.log Dtot = 4·Real.log z` (ℕ
args).  Catch #75 records that this is unreachable at any operating point: `Dtot = z⁴` gives
exactness but breaks the A₂ BV level row by polylog factors, while the realistic operating
`Dtot = QD ≈ x^{1/2−ε′}·polylog` lands *inside* a window around `4·log z` but never *on* it.

## The use-site map (where the exact identity is consumed in `A2grid_sharp_le`, and its cost)

| use site (`A2Weighted.lean`)              | what needs the identity | cost at the window |
|-------------------------------------------|-------------------------|--------------------|
| `hyD : log yR < log Dtot` (:477)          | strict `<`              | none (window keeps it) |
| `hDge2 : 2 ≤ Dtot` (:478)                 | `log Dtot > 0`          | none |
| `hyR_lt_D : yR < Dtot` (:484)             | via `hyD`               | none |
| **`applicationA2`→`A2weight_integral_eq`**| `∫ = (log 6)/4` EXACT   | **relative `(1+κ)`** |
| crumb `A2weight_le_of_log_le` (:549)      | via `hyD`               | none |
| `A2weight_top_eq` (:443)                  | not used in the bound   | none |

So the entire perturbation localizes to the integral evaluation.  We handle it with a **reference
point** `Dtot0 := z⁴`, which is a genuine `ℕ` with `Real.log ((z⁴ : ℕ)) = 4·Real.log z` *exactly*
(`Real.log_pow`), so the landed exact aggregation applies to it verbatim (`agg_at_zpow4`); the
actual perturbed weights are routed to it through the single pointwise domination
`A2weight_window_dom`.

## The deviation constant (honest)

On the window `log t ≤ (8/3)·log z` (the A₂ window top `yR = x^{1/3}`, geometry fixed) with
`Real.log Dtot ≥ (4 − δ)·log z`, the perturbed weight `w(t) = log z/(log Dtot − log t)` is
dominated by the exact-geometry weight `w₀(t) = log z/(4·log z − log t)`:

  `w(t) ≤ (1 + κ)·w₀(t)`,   `κ = δ/(4/3 − δ)`.

Derivation: the denominator shrinks by at most `δ·log z`; the exact denominator on the window is at
least `(4 − 8/3)·log z = (4/3)·log z`, so the relative growth is `≤ δ·log z/((4/3 − δ)·log z) =
κ`.  With the frozen window `δ = 8/10000` (matching the A₁ certs' frozen `[3.9992, 4]` window —
`39992/10000 = 4 − 8/10000`), the arithmetic collapses exactly:

  `κ = (8/10000)/(4/3 − 8/10000) = 3/4997`,   `1 + κ = 5000/4997`.

The pointwise bound reduces (after clearing denominators) to precisely `log t ≤ (8/3)·log z` — the
window hypothesis — so it is a tight, rational-arithmetic inequality.

## The razor-compatibility number

The A₂ constant the razor consumes is `½·(3 + 43/75)·(log 6/4) = 0.800319` (`RazorClose`).  The
`(1 + κ)` factor adds `κ·(3 + 43/75)·(log 6/4)` to the un-halved A₂ value; halved, the extra cost is

  `(3/4997)·(3 + 43/75)·(log 6/4)/2 ≈ 0.000480`,

verified `≤ 2151/1000000` in `razor_window_cost`.  The razor's certified margin is `M = 0.012151`
(`RazorClose.razor_scalar_margin`); the error bundle allowance beyond the `1/100` floor is
`M − 1/100 = 0.002151`.  The deviation `0.000480` sits at ~22% of that allowance — INSIDE, with
~4.5× headroom.  It folds into the `e2` error-bundle share of `hledger_at_certs`, leaving the
frozen `a2hi = (3 + 43/75)·(log 6/4)` untouched (so `razor_scalar_margin` is unaffected).

## The at-op geometry discharge (for fin8d)

`A2grid_window_le` consumes the window as two hypotheses `hLD_lo`/`hLD_hi`.  For the recommended
operating convention `Dtot := ⌊x^{1/2−ε′}⌋₊` (the A₁ level `D` itself — it centers at
`log D/log z = 4 − 8ε′ = 3.99928 ∈ [3.9992, 4]` and satisfies the W2-LEVEL row, since
`D = √x/x^{ε′} ≤ √x/(log x)^{B+2}`), the landed A₁ membership `WindowMembership.logRatio_A1_mem`
discharges the window *directly*: `logRatio_A2_window_mem` is that bridge.  If fin8d instead uses
`Dtot = QD`, the lower bound `hLD_lo` is automatic (`Dtot ≥ D`), and only the upper bound
`hLD_hi` needs the standard `log Q ≤ 8ε′·log z` control at the operating threshold.

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Salt.Chen

/-! ## Part A — the pointwise weight domination (the entire deviation cost) -/

/-- **The window-perturbed weight domination.**  For `z ≥ 2`, `t > 0` with `log t ≤ (8/3)·log z`,
and `Real.log Dtot ≥ (4 − 8/10000)·log z`, the perturbed carrier is within a factor `5000/4997 =
1 + 3/4997` of the exact-geometry carrier at `Dtot0 = z⁴`:

  `A2weight z Dtot t ≤ (5000/4997)·A2weight z (z⁴) t`.

After clearing denominators the claim is exactly `log t ≤ (8/3)·log z` (rational, tight); the
`5000/4997` is the honest `1 + κ` with `κ = (8/10000)/(4/3 − 8/10000) = 3/4997`. -/
theorem A2weight_window_dom {z Dtot : ℕ} {t : ℝ} (hz2 : 2 ≤ z) (_ht0 : 0 < t)
    (htyR : Real.log t ≤ 8 / 3 * Real.log z)
    (hLD_lo : (4 - 8 / 10000) * Real.log z ≤ Real.log Dtot) :
    A2weight z Dtot t ≤ (5000 / 4997) * A2weight z (z ^ 4) t := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hLD0 : Real.log ((z ^ 4 : ℕ) : ℝ) = 4 * Real.log z := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  -- both denominators are positive on the window
  have hden_e : 0 < 4 * Real.log z - Real.log t := by nlinarith [htyR, hL]
  have hden_a : 0 < Real.log Dtot - Real.log t := by nlinarith [hLD_lo, htyR, hL]
  -- the key rational inequality: exact denom ≤ (1+κ)·actual denom, tight iff log t ≤ (8/3)log z
  have hkey : 4 * Real.log z - Real.log t
      ≤ 5000 / 4997 * (Real.log Dtot - Real.log t) := by
    nlinarith [hLD_lo, htyR, hL]
  rw [A2weight, A2weight, hLD0, ← mul_div_assoc, div_le_div_iff₀ hden_a hden_e]
  calc Real.log z * (4 * Real.log z - Real.log t)
      ≤ Real.log z * (5000 / 4997 * (Real.log Dtot - Real.log t)) :=
        mul_le_mul_of_nonneg_left hkey hL.le
    _ = 5000 / 4997 * Real.log z * (Real.log Dtot - Real.log t) := by ring

/-! ## Part B — the exact aggregation at the reference point `Dtot0 = z⁴`

A verbatim replay of `A2grid_sharp_le`'s internal `hagg` block at `Dtot0 = z⁴`, where the exact
geometry `Real.log ((z⁴ : ℕ)) = 4·log z` holds by `Real.log_pow`, so `applicationA2` (hence the
partial-fraction integral `(log 6)/4` and the monotone Abel pass) applies unchanged. -/

/-- **The exact A₂ aggregation at `Dtot0 = z⁴`.**  For each `p ∈ P` a prime in `[z, yR)` with the
window top `Real.log yR = (8/3)·log z`,

  `∑_{p∈P} (1/(p−1))·A2weight z (z⁴) p ≤ (log 6)/4 + A2weight z (z⁴) yR·(21/log z + 2/(z−1))`.

This is the `hagg` half of `A2grid_sharp_le` instantiated at the reference `Dtot0 = z⁴`. -/
theorem agg_at_zpow4 (P : Finset ℕ) (z : ℕ) (yR : ℝ)
    (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR) (hyR0 : 0 < yR)
    (hLy : Real.log yR = 8 / 3 * Real.log z)
    (hP : ∀ p ∈ P, p.Prime ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < yR) :
    ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p
      ≤ Real.log 6 / 4 + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)) := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hLD0 : Real.log ((z ^ 4 : ℕ) : ℝ) = 4 * Real.log z := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hyD0 : Real.log yR < Real.log ((z ^ 4 : ℕ) : ℝ) := by rw [hLD0, hLy]; linarith
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
      ≤ Real.log 6 / 4 + 21 / Real.log z * A2weight z (z ^ 4) yR := by
    calc ∑ p ∈ P, A2weight z (z ^ 4) p / p
        ≤ ∑ p ∈ Salt.BrunLower.primesInWindow (z : ℝ) yR, A2weight z (z ^ 4) p / p :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub hwinnn
      _ ≤ Real.log 6 / 4 + 21 / Real.log z * A2weight z (z ^ 4) yR :=
          applicationA2 (Dtot := z ^ 4) hz2 hzy hyR0 hLD0 hLy
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
      ≤ (Real.log 6 / 4 + 21 / Real.log z * A2weight z (z ^ 4) yR)
        + A2weight z (z ^ 4) yR * (2 / ((z : ℝ) - 1)) := hcomb
    _ = Real.log 6 / 4 + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)) := by ring

/-! ## Part C — the window-perturbed A₂ certificate -/

/-- **`A2grid_window_le` — the window-perturbed A₂ cert (catch #75 repair).**  The restatement of
`A2Weighted.A2grid_sharp_le` with the exact geometry `Real.log Dtot = 4·log z` relaxed to the
frozen window `[(4 − 8/10000)·log z, 4·log z]`.  Under the same operating hypotheses (each `p ∈ P`
prime in `[z, yR)`, its operating point `logRatio z (cdiv Dtot p) ∈ [1,3]`, `Nf p ≥ 1`) and the
fixed window top `Real.log yR = (8/3)·log z`,

  `A2grid ≤ (5000/4997)·((3 + Cmass)·((log 6)/4 + A2weight z (z⁴) yR·(21/log z + 2/(z−1))))`.

The `5000/4997 = 1 + 3/4997` factor is the honest window deviation (Part A).  The bracket is the
landed exact bound (`A2grid_sharp_le`) at the reference `Dtot0 = z⁴`.  Route to the razor:
`A2grid_window_additive` splits the factor off `a2hi`.  (The window's upper edge `_hLD_hi` is kept
in the interface for symmetry with `logRatio_A2_window_mem` but is not load-bearing: an upper bound
on `A2grid` only ever wants the *smallest* `Dtot`, i.e. the lower window edge — a larger `Dtot`
merely shrinks the weights.) -/
theorem A2grid_window_le {Cmass : ℝ} (P : Finset ℕ) (z Dtot : ℕ) (yR : ℝ) (Nf : ℕ → ℕ)
    (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR) (hyR0 : 0 < yR) (hCmass : ∀ N, A2massSum N ≤ Cmass)
    (hLD_lo : (4 - 8 / 10000) * Real.log z ≤ Real.log Dtot)
    (_hLD_hi : Real.log Dtot ≤ 4 * Real.log z)
    (hLy : Real.log yR = 8 / 3 * Real.log z)
    (hP : ∀ p ∈ P, p.Prime ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < yR)
    (hN : ∀ p ∈ P, 1 ≤ Nf p)
    (hsrange : ∀ p ∈ P, 1 ≤ logRatio z (cdiv Dtot p) ∧ logRatio z (cdiv Dtot p) ≤ 3) :
    A2grid P z Dtot Nf
      ≤ (5000 / 4997) * ((3 + Cmass) * (Real.log 6 / 4
          + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by
  have hCmass_nn : (0 : ℝ) ≤ Cmass := by have := hCmass 0; simpa [A2massSum] using this
  have h3C : (0 : ℝ) ≤ 3 + Cmass := by linarith
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  -- window ⟹ log yR < log Dtot ⟹ yR < Dtot ⟹ every p < Dtot
  have hyD : Real.log yR < Real.log Dtot := by
    rw [hLy]
    have hlt : (8 / 3 : ℝ) * Real.log z < (4 - 8 / 10000) * Real.log z :=
      mul_lt_mul_of_pos_right (by norm_num) hL
    linarith [hLD_lo]
  have hDlogpos : 0 < Real.log Dtot := lt_of_le_of_lt (by nlinarith [hLy, hL]) hyD
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
  -- pointwise (1+κ)-domination lifted to the sum
  have hdom : ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p
      ≤ (5000 / 4997) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpp, _, hpy⟩ := hP p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp1nn : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
    have hlogp : Real.log p ≤ 8 / 3 * Real.log z := by
      calc Real.log p ≤ Real.log yR := Real.log_le_log hp0 hpy.le
        _ = 8 / 3 * Real.log z := hLy
    have hwdom : A2weight z Dtot p ≤ (5000 / 4997) * A2weight z (z ^ 4) p :=
      A2weight_window_dom hz2 hp0 hlogp hLD_lo
    calc (1 / ((p : ℝ) - 1)) * A2weight z Dtot p
        ≤ (1 / ((p : ℝ) - 1)) * ((5000 / 4997) * A2weight z (z ^ 4) p) :=
          mul_le_mul_of_nonneg_left hwdom hp1nn
      _ = (5000 / 4997) * ((1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p) := by ring
  -- exact aggregation at the reference point
  have hagg0 := agg_at_zpow4 P z yR hz2 hzy hyR0 hLy hP
  calc A2grid P z Dtot Nf
      ≤ (3 + Cmass) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p := hfloorA
    _ ≤ (3 + Cmass) * ((5000 / 4997) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z (z ^ 4) p) :=
        mul_le_mul_of_nonneg_left hdom h3C
    _ ≤ (3 + Cmass) * ((5000 / 4997) * (Real.log 6 / 4
          + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by
        apply mul_le_mul_of_nonneg_left _ h3C
        exact mul_le_mul_of_nonneg_left hagg0 (by norm_num : (0 : ℝ) ≤ 5000 / 4997)
    _ = (5000 / 4997) * ((3 + Cmass) * (Real.log 6 / 4
          + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by ring

/-- **`A2grid_window_additive` — the razor-slot form.**  The same bound rearranged so the frozen
razor constant `a2hi = (3 + Cmass)·(log 6/4)` appears untouched, with the window deviation and the
`O(1/log z)` tail collected into a single additive error term (the razor's `e2` share):

  `A2grid ≤ (3 + Cmass)·(log 6/4)
            + [ (3/4997)·(3 + Cmass)·(log 6/4)
                + (5000/4997)·(3 + Cmass)·(A2weight z (z⁴) yR·(21/log z + 2/(z−1))) ]`.

The bracket's first summand is the honest window cost (bounded by `razor_window_cost` at
`Cmass = 43/75`); the second is the landed `O(1/log z)` tail (`A2weight z (z⁴) yR = 3/4` at op). -/
theorem A2grid_window_additive {Cmass : ℝ} (P : Finset ℕ) (z Dtot : ℕ) (yR : ℝ) (Nf : ℕ → ℕ)
    (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR) (hyR0 : 0 < yR) (hCmass : ∀ N, A2massSum N ≤ Cmass)
    (hLD_lo : (4 - 8 / 10000) * Real.log z ≤ Real.log Dtot)
    (hLD_hi : Real.log Dtot ≤ 4 * Real.log z)
    (hLy : Real.log yR = 8 / 3 * Real.log z)
    (hP : ∀ p ∈ P, p.Prime ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < yR)
    (hN : ∀ p ∈ P, 1 ≤ Nf p)
    (hsrange : ∀ p ∈ P, 1 ≤ logRatio z (cdiv Dtot p) ∧ logRatio z (cdiv Dtot p) ≤ 3) :
    A2grid P z Dtot Nf
      ≤ (3 + Cmass) * (Real.log 6 / 4)
        + ((3 / 4997) * (3 + Cmass) * (Real.log 6 / 4)
            + (5000 / 4997) * (3 + Cmass)
                * (A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by
  have h := A2grid_window_le P z Dtot yR Nf hz2 hzy hyR0 hCmass hLD_lo hLD_hi hLy hP hN hsrange
  -- pure algebra: (5000/4997)·((3+C)·(L + T)) = (3+C)·L + (3/4997)(3+C)·L + (5000/4997)(3+C)·T
  have hexpand : (5000 / 4997 : ℝ) * ((3 + Cmass) * (Real.log 6 / 4
        + A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1))))
      = (3 + Cmass) * (Real.log 6 / 4)
        + ((3 / 4997) * (3 + Cmass) * (Real.log 6 / 4)
            + (5000 / 4997) * (3 + Cmass)
                * (A2weight z (z ^ 4) yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)))) := by ring
  linarith [h, hexpand.ge, hexpand.le]

/-! ## Part D — the razor-compatibility numeric check (mandatory) -/

/-- **`razor_window_cost` — the deviation fits the razor.**  At the frozen mass `Cmass = 43/75`,
the window deviation's contribution to the halved A₂ razor share is below the error-bundle
allowance `M − 1/100 = 0.002151`:

  `(3/4997)·(3 + 43/75)·(log 6/4)/2 ≤ 2151/1000000  (≈ 0.000480)`.

Consumes `log 6 ≤ 17917596/10⁷` (from `LogToolkit.log_two_le + log_three_le`), matching
`RazorClose.razor_scalar_margin`'s `M = 0.012151`. -/
theorem razor_window_cost :
    (3 / 4997 : ℝ) * (3 + 43 / 75) * (Real.log 6 / 4) / 2 ≤ 2151 / 1000000 := by
  have hlog6 : Real.log 6 ≤ 17917596 / 10000000 := by
    have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [h6]; linarith [log_two_le, log_three_le]
  nlinarith [hlog6]

/-! ## Part E — the at-op geometry membership (for fin8d) -/

/-- **The `logRatio`-to-window bridge.**  A membership `logRatio z Dtot ∈ [39992/10000, 4]`
(with `39992/10000 = 4 − 8/10000`) is exactly the A₂ geometry window `A2grid_window_le` consumes.
Pure real arithmetic (multiply through by `log z > 0`). -/
theorem window_of_logRatio_mem {z Dtot : ℕ} (hz : (1 : ℝ) < z)
    (hmem : logRatio z Dtot ∈ Set.Icc (39992 / 10000 : ℝ) 4) :
    (4 - 8 / 10000) * Real.log z ≤ Real.log Dtot ∧ Real.log Dtot ≤ 4 * Real.log z := by
  have hlz : 0 < Real.log z := Real.log_pos hz
  rw [Set.mem_Icc, logRatio] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  rw [le_div_iff₀ hlz] at hlo
  rw [div_le_iff₀ hlz] at hhi
  exact ⟨by linarith [hlo], hhi⟩

/-- **`logRatio_A2_window_mem` — the at-op discharge for `Dtot = ⌊x^{1/2−ε′}⌋₊`.**  The recommended
operating convention takes the A₂ total level to be the A₁ divisor level `D = ⌊x^{1/2−9/100000}⌋₊`
itself (it centers at `4 − 8ε′ = 3.99928 ∈ [3.9992, 4]` and satisfies the W2-LEVEL row).  Then the
landed A₁ membership `WindowMembership.logRatio_A1_mem` discharges `A2grid_window_le`'s window
hypotheses verbatim:

  `(4 − 8/10000)·log⌊x^{1/8}⌋₊ ≤ log⌊x^{1/2−9/100000}⌋₊ ≤ 4·log⌊x^{1/8}⌋₊`   for all large `x`.

fin8d instantiates `A2grid_window_le` with `z = ⌊x^{1/8}⌋₊`, `Dtot = ⌊x^{1/2−9/100000}⌋₊`; if it
instead runs `Dtot = QD`, the lower bound is automatic (`Dtot ≥ D`) and only the upper bound needs
the `log Q ≤ 8ε′·log z` control. -/
theorem logRatio_A2_window_mem :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
      (4 - 8 / 10000) * Real.log (⌊(x : ℝ) ^ (1 / 8 : ℝ)⌋₊ : ℕ)
          ≤ Real.log (⌊(x : ℝ) ^ (1 / 2 - 9 / 100000 : ℝ)⌋₊ : ℕ)
      ∧ Real.log (⌊(x : ℝ) ^ (1 / 2 - 9 / 100000 : ℝ)⌋₊ : ℕ)
          ≤ 4 * Real.log (⌊(x : ℝ) ^ (1 / 8 : ℝ)⌋₊ : ℕ) := by
  obtain ⟨x₁, hmem⟩ := logRatio_A1_mem
  refine ⟨max x₁ (10 ^ 48), fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx48 : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hx
  -- z = ⌊x^{1/8}⌋₊ ≥ 10^6 > 1
  have hpow48 : ((10 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 8) = (10 : ℝ) ^ 6 := by
    have h6 : ((48 : ℕ) : ℝ) * (1 / 8) = ((6 : ℕ) : ℝ) := by norm_num
    rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10), h6,
      Real.rpow_natCast]
  have hstep1 : (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← hpow48]; exact Real.rpow_le_rpow (by positivity) hx48 (by norm_num)
  have hfloor6 : (1000000 : ℕ) ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ := by
    apply Nat.le_floor
    rw [show ((1000000 : ℕ) : ℝ) = (10 : ℝ) ^ 6 by norm_num]; exact hstep1
  have hz1 : (1 : ℝ) < (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℝ) := by
    have h : (1000000 : ℝ) ≤ (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℝ) := by exact_mod_cast hfloor6
    linarith
  exact window_of_logRatio_mem hz1 (hmem x hx1)

end Salt.Chen
