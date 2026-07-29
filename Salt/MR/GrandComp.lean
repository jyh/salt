/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HeadGrade
import Salt.MR.HalaszHead
import Salt.Maynard.Mertens

/-!
# GRAND-COMP — the terminal composition of the joint head (`GrandComp`)

The final composition wave of the terminal-assembly campaign.  It consumes the LANDED
kernel-ramp grade (`crossKer_grade_decayed`, `HeadGrade`), the joint CS factoring
(`joint_cs_factoring`, `JointHead`), the pointwise Euler layer (`head_sigma_bound`,
`SupF`), and the pretentious σ-cutoff (`sigma_cutoff_pretentious`, `SupF`), and drives
toward `T1_head_wire`'s `hRHS` binder (`HExit`).

* **G1 (`window_mass_eval`)** — LANDED.  The two window coefficient-mass sums (linear
  and diagonal, at the two legs `c₀∓β`) that `crossKer_grade_decayed` emits, evaluated
  to the honest `(log⌈X/y⌉ + (log 4 + 4))` Mertens grade via `sum_vonMangoldt_div_le`
  (`Salt.Maynard.Mertens`) — the exact page gate-b (`BRIDGE-EXEC`, 09:44) verifies:
  `‖lambdaLin‖ ≤ Λ`, `n^{−c}`-weighting on the two legs, `Λ² ≤ (log(X/y))·Λ` for the
  diagonals, the low-leg window-excess `(X/y)^{1−(c₀−β)}` carried EXPLICIT.

The higher stones G2–G4 (the per-`(α,β)` `supF` supply, the `β`/`α`-integral assembly,
the `T1` supply) are recorded with their precise residuals in the campaign notes: the
`joint_cs_factoring` socket is `∀ t : ℝ`, and the pointwise `head_sigma_bound` decay
`e^{−(1/e)𝔻²(t)}` is `≥ e^{−(1/e)M_range}` only for `t` inside the `M_range` annular
window — outside it (notably at the twist-trivial frequency) the four-factor does not
decay, so the ∀-`t` sup cannot carry `M_range` decay.  This is the corpus-flagged
`supF`-pretentious wall (`T1_decay_conditional_final`'s residual set).
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open ArithmeticFunction

/-! ## G1 — the window coefficient-mass evaluation (`window_mass_eval`)

`crossKer_grade_decayed` (`HeadGrade`) emits four coefficient-mass sums over the window
`F = Ioo ⌊y⌋₊ ⌈X/y⌉₊`:

* two LINEAR sums `∑ ‖λ_lin(restrictAbove y g)‖ / n^{c₀∓β}` (high leg `c₀+β ≥ 1`, low leg
  `0 < c₀−β ≤ 1`);
* two DIAGONAL sums `∑ ‖λ_lin(restrictAbove y g)‖² / (n·n)^{c₀∓β}`.

This stone evaluates all four to the Mertens grade.  Its route is partial-summation-free:
`‖λ_lin g‖ ≤ Λ` at every `n` (`lambdaLin_norm_le`, κ=1 disarmed), the `n^{−c}` weighting
collapsed to `Λ n / n` by the leg regime, and `∑_{n≤⌈X/y⌉} Λ n / n ≤ log⌈X/y⌉ + (log 4+4)`
(`sum_vonMangoldt_div_le`).  The diagonals use `Λ² ≤ (log(X/y))·Λ` (`vonMangoldt_le_log`,
`n ≤ X/y`) and a second `1/n ≤ 1/y` weight (window floor `n > y`); the low legs carry the
explicit window-excess `(X/y)^{1−(c₀−β)}` / `(X/y)^{2(1−(c₀−β))}`. -/

/-- **G1 — the window-mass evaluation** (`window_mass_eval`).  For a globally 1-bounded `g`
at primes, `1 ≤ X`, `0 < y ≤ X`, the leg regimes `0 < c₀−β ≤ 1 ≤ c₀+β`, and the window
membership `n ≤ X/y` (`hQ`, exactly `crossKer_grade_decayed`'s), the four coefficient-mass
sums obey the Mertens grade `L' := log⌈X/y⌉ + (log 4 + 4)`:

* high linear `≤ L'`;
* low linear `≤ (X/y)^{1−(c₀−β)}·L'`;
* high diagonal `≤ (log(X/y)/y)·L'`;
* low diagonal `≤ (X/y)^{2(1−(c₀−β))}·(log(X/y)/y)·L'`. -/
theorem window_mass_eval {g : ℕ → ℂ} {X y c₀ β : ℝ}
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (_hX : 1 ≤ X) (hy0 : 0 < y) (hyX : y ≤ X)
    (_hclow0 : 0 < c₀ - β) (hclow1 : c₀ - β ≤ 1) (hchigh : 1 ≤ c₀ + β)
    (hQ : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (n : ℝ) ≤ X / y) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
      ≤ Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)
  ∧ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
      ≤ (X / y) ^ (1 - (c₀ - β)) * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4))
  ∧ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ (c₀ + β))
      ≤ Real.log (X / y) / y * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4))
  ∧ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ (c₀ - β))
      ≤ (X / y) ^ (2 * (1 - (c₀ - β))) * (Real.log (X / y) / y)
          * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) := by
  -- abbreviations and shared facts
  have hb : ∀ n, ‖lambdaLin (restrictAbove y g) n‖ ≤ ArithmeticFunction.vonMangoldt n :=
    fun n => lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) n
  have hXy1 : (1 : ℝ) ≤ X / y := (one_le_div hy0).mpr hyX
  have hXypos : (0 : ℝ) < X / y := by linarith
  have hlogQ0 : (0 : ℝ) ≤ Real.log (X / y) := Real.log_nonneg hXy1
  have hceil1 : 1 ≤ ⌈X / y⌉₊ := Nat.one_le_ceil_iff.mpr hXypos
  -- per-n window facts
  have hn1 : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (1 : ℝ) ≤ (n : ℝ) := by
    intro n hn; rw [Finset.mem_Ioo] at hn
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hny : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, y < (n : ℝ) := by
    intro n hn; rw [Finset.mem_Ioo] at hn
    have h1 : (⌊y⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn.1
    linarith [Nat.lt_floor_add_one y]
  -- the Mertens base sum over the window
  have hsub : Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ ⊆ Finset.Ioc 0 ⌈X / y⌉₊ := by
    intro n hn; rw [Finset.mem_Ioo] at hn; rw [Finset.mem_Ioc]; omega
  have hbase : ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
      ≤ Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))).trans ?_
    exact Salt.Maynard.sum_vonMangoldt_div_le hceil1
  -- the squared numerator bound Λ² ≤ log(X/y)·Λ, per window n
  have hsqbound : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
      ‖lambdaLin (restrictAbove y g) n‖ ^ 2
        ≤ Real.log (X / y) * ArithmeticFunction.vonMangoldt n := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith [hn1 n hn]
    have hblogQ : ‖lambdaLin (restrictAbove y g) n‖ ≤ Real.log (X / y) :=
      le_trans (hb n) (le_trans vonMangoldt_le_log (Real.log_le_log hnpos (hQ n hn)))
    have := mul_le_mul hblogQ (hb n) (norm_nonneg _) hlogQ0
    rwa [← sq] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- G1.1 — high linear: `‖b n‖/n^{c₀+β} ≤ Λ n / n`, then `hbase`
    refine (Finset.sum_le_sum (fun n hn => ?_)).trans hbase
    have h1n := hn1 n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ (c₀ + β) := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ (c₀ + β) := Real.rpow_le_rpow_of_exponent_le h1n hchigh
    calc ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β)
        ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (c₀ + β) := by
          gcongr; exact hb n
      _ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
          div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hnpos hpow
  · -- G1.2 — low linear: carries the window-excess `(X/y)^{1−(c₀−β)}`
    calc (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
        ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            (X / y) ^ (1 - (c₀ - β)) * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have h1n := hn1 n hn
          have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
          have hden : (0 : ℝ) < (n : ℝ) ^ (c₀ - β) := Real.rpow_pos_of_pos hnpos _
          have hpid : (n : ℝ) ^ (1 - (c₀ - β)) * (n : ℝ) ^ (c₀ - β) = (n : ℝ) := by
            rw [← Real.rpow_add hnpos, sub_add_cancel, Real.rpow_one]
          have hkey : (n : ℝ) ≤ (X / y) ^ (1 - (c₀ - β)) * (n : ℝ) ^ (c₀ - β) := by
            calc (n : ℝ) = (n : ℝ) ^ (1 - (c₀ - β)) * (n : ℝ) ^ (c₀ - β) := hpid.symm
              _ ≤ (X / y) ^ (1 - (c₀ - β)) * (n : ℝ) ^ (c₀ - β) :=
                  mul_le_mul_of_nonneg_right
                    (Real.rpow_le_rpow hnpos.le (hQ n hn) (by linarith))
                    (Real.rpow_nonneg hnpos.le _)
          rw [← mul_div_assoc, div_le_div_iff₀ hden hnpos]
          calc ‖lambdaLin (restrictAbove y g) n‖ * (n : ℝ)
              ≤ ArithmeticFunction.vonMangoldt n
                  * ((X / y) ^ (1 - (c₀ - β)) * (n : ℝ) ^ (c₀ - β)) :=
                mul_le_mul (hb n) hkey hnpos.le ArithmeticFunction.vonMangoldt_nonneg
            _ = (X / y) ^ (1 - (c₀ - β)) * ArithmeticFunction.vonMangoldt n
                  * (n : ℝ) ^ (c₀ - β) := by ring
      _ = (X / y) ^ (1 - (c₀ - β)) * ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ArithmeticFunction.vonMangoldt n / (n : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ (X / y) ^ (1 - (c₀ - β)) * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) :=
          mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hXypos.le _)
  · -- G1.3 — high diagonal: `Λ² ≤ log(X/y)·Λ`, then `1/n ≤ 1/y`
    calc (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ (c₀ + β))
        ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            Real.log (X / y) / y * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have h1n := hn1 n hn
          have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
          have hyn := hny n hn
          have hcast : ((n * n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) := by push_cast; ring
          have hnn1 : (1 : ℝ) ≤ (n : ℝ) * (n : ℝ) := by nlinarith [h1n]
          have hnnpos : (0 : ℝ) < (n : ℝ) * (n : ℝ) := by positivity
          have hpow2 : (n : ℝ) * (n : ℝ) ≤ ((n : ℝ) * (n : ℝ)) ^ (c₀ + β) := by
            calc (n : ℝ) * (n : ℝ) = ((n : ℝ) * (n : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ ((n : ℝ) * (n : ℝ)) ^ (c₀ + β) :=
                  Real.rpow_le_rpow_of_exponent_le hnn1 hchigh
          rw [hcast]
          calc ‖lambdaLin (restrictAbove y g) n‖ ^ 2 / ((n : ℝ) * (n : ℝ)) ^ (c₀ + β)
              ≤ (Real.log (X / y) * ArithmeticFunction.vonMangoldt n)
                  / ((n : ℝ) * (n : ℝ)) ^ (c₀ + β) := by
                gcongr; exact hsqbound n hn
            _ ≤ (Real.log (X / y) * ArithmeticFunction.vonMangoldt n)
                  / ((n : ℝ) * (n : ℝ)) :=
                div_le_div_of_nonneg_left
                  (mul_nonneg hlogQ0 ArithmeticFunction.vonMangoldt_nonneg) hnnpos hpow2
            _ ≤ Real.log (X / y) / y * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
                rw [div_mul_div_comm]
                exact div_le_div_of_nonneg_left
                  (mul_nonneg hlogQ0 ArithmeticFunction.vonMangoldt_nonneg)
                  (mul_pos hy0 hnpos)
                  (mul_le_mul_of_nonneg_right hyn.le hnpos.le)
      _ = Real.log (X / y) / y * ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ArithmeticFunction.vonMangoldt n / (n : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ Real.log (X / y) / y * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) :=
          mul_le_mul_of_nonneg_left hbase (div_nonneg hlogQ0 hy0.le)
  · -- G1.4 — low diagonal: carries `(X/y)^{2(1−(c₀−β))}`
    calc (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ ^ 2 / ((n * n : ℕ) : ℝ) ^ (c₀ - β))
        ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            (X / y) ^ (2 * (1 - (c₀ - β))) * (Real.log (X / y) / y)
              * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have h1n := hn1 n hn
          have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
          have hyn := hny n hn
          have hcast : ((n * n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) := by push_cast; ring
          have hnnpos : (0 : ℝ) < (n : ℝ) * (n : ℝ) := by positivity
          have hden : (0 : ℝ) < ((n : ℝ) * (n : ℝ)) ^ (c₀ - β) := Real.rpow_pos_of_pos hnnpos _
          have hpid2 : ((n : ℝ) * (n : ℝ)) ^ (1 - (c₀ - β))
                * ((n : ℝ) * (n : ℝ)) ^ (c₀ - β) = (n : ℝ) * (n : ℝ) := by
            rw [← Real.rpow_add hnnpos, sub_add_cancel, Real.rpow_one]
          have hmono2 : ((n : ℝ) * (n : ℝ)) ^ (1 - (c₀ - β))
              ≤ (X / y) ^ (2 * (1 - (c₀ - β))) := by
            calc ((n : ℝ) * (n : ℝ)) ^ (1 - (c₀ - β))
                ≤ ((X / y) * (X / y)) ^ (1 - (c₀ - β)) :=
                  Real.rpow_le_rpow (by positivity)
                    (mul_le_mul (hQ n hn) (hQ n hn) hnpos.le hXypos.le) (by linarith)
              _ = (X / y) ^ (2 * (1 - (c₀ - β))) := by
                  rw [Real.mul_rpow hXypos.le hXypos.le, ← Real.rpow_add hXypos,
                    show (1 - (c₀ - β)) + (1 - (c₀ - β)) = 2 * (1 - (c₀ - β)) from by ring]
          have hkey2 : (n : ℝ) * (n : ℝ)
              ≤ (X / y) ^ (2 * (1 - (c₀ - β))) * ((n : ℝ) * (n : ℝ)) ^ (c₀ - β) := by
            calc (n : ℝ) * (n : ℝ)
                = ((n : ℝ) * (n : ℝ)) ^ (1 - (c₀ - β)) * ((n : ℝ) * (n : ℝ)) ^ (c₀ - β) :=
                  hpid2.symm
              _ ≤ (X / y) ^ (2 * (1 - (c₀ - β))) * ((n : ℝ) * (n : ℝ)) ^ (c₀ - β) :=
                  mul_le_mul_of_nonneg_right hmono2 (Real.rpow_nonneg hnnpos.le _)
          rw [hcast]
          have hstep : ‖lambdaLin (restrictAbove y g) n‖ ^ 2 / ((n : ℝ) * (n : ℝ)) ^ (c₀ - β)
              ≤ (X / y) ^ (2 * (1 - (c₀ - β)))
                  * (Real.log (X / y) * ArithmeticFunction.vonMangoldt n)
                  / ((n : ℝ) * (n : ℝ)) := by
            rw [div_le_div_iff₀ hden hnnpos]
            calc ‖lambdaLin (restrictAbove y g) n‖ ^ 2 * ((n : ℝ) * (n : ℝ))
                ≤ (Real.log (X / y) * ArithmeticFunction.vonMangoldt n)
                    * ((X / y) ^ (2 * (1 - (c₀ - β))) * ((n : ℝ) * (n : ℝ)) ^ (c₀ - β)) :=
                  mul_le_mul (hsqbound n hn) hkey2 (by positivity)
                    (mul_nonneg hlogQ0 ArithmeticFunction.vonMangoldt_nonneg)
              _ = (X / y) ^ (2 * (1 - (c₀ - β)))
                    * (Real.log (X / y) * ArithmeticFunction.vonMangoldt n)
                    * ((n : ℝ) * (n : ℝ)) ^ (c₀ - β) := by ring
          refine hstep.trans ?_
          rw [mul_div_assoc, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hXypos.le _)
          rw [div_mul_div_comm]
          exact div_le_div_of_nonneg_left
            (mul_nonneg hlogQ0 ArithmeticFunction.vonMangoldt_nonneg)
            (mul_pos hy0 hnpos)
            (mul_le_mul_of_nonneg_right hyn.le hnpos.le)
      _ = (X / y) ^ (2 * (1 - (c₀ - β))) * (Real.log (X / y) / y)
            * ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
                ArithmeticFunction.vonMangoldt n / (n : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ (X / y) ^ (2 * (1 - (c₀ - β))) * (Real.log (X / y) / y)
            * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) :=
          mul_le_mul_of_nonneg_left hbase
            (mul_nonneg (Real.rpow_nonneg hXypos.le _) (div_nonneg hlogQ0 hy0.le))

/-! ## S1/S2 (`WINDOW-COMP`) — the window head decay and its σ-cutoff

The two terminal composition stones of `UHEAD-SCOPE`'s ladder (`docs/exploration/pilot.md`,
16:21).  Pure compositions of the LANDED decay atoms — `head_sigma_bound` (`SupF`, the
σ-uniform pointwise Euler majorant), `scale_floor_Mrange_seam` (`SupF`, the seam-datum
`M_range` floor), and `sigma_cutoff_pretentious` (`SupF`, the `c = 1/e` flat-regime
σ-integral).  No new analysis: the decay lives on `M_range`'s annular window (the corpus's
`hhead`/moment frontier), and these stones fire the atoms there.

The seam head is `LSeries (ellLin (seamCoeff (ellLin g) 1 t₀))` — the L-series of the
linearized seam coefficient.  `head_sigma_bound` at datum `seamCoeff (ellLin g) 1 t₀` and
frequency `t` emits the pointwise decay at distance
`𝔻(1, (seamCoeff (ellLin g) 1 t₀)·costwist(−t); e^{1/σ})²`, which the twist algebra
(`dist_triv_left_eq` below + the public `seamCoeff_trivial_dist_eq`, `HalaszHead`) rewrites to
the bare `ℓ`-datum shifted-center form `𝔻(ellLin g, costwist(t+t₀); e^{1/σ})²` that
`scale_floor_Mrange_seam` floors by `M_range(seamCoeff (ellLin g) 1 t₀) − 2log(σL) − 48`. -/

/-- Twist algebra: the trivial-left-datum distance `𝔻(1, f·costwist(−t); X)²` equals the
`𝔻(f, costwist t; X)²` form.  Per prime, `Re(1·conj(f·costwist(−t))) = Re(f·conj(costwist t))`
via `conj (costwist t) = costwist (−t)` (`costwist_conj`) and `Re(conj z) = Re z`
(`Complex.conj_re`). -/
private lemma dist_triv_left_eq (f : ℕ → ℂ) (t X : ℝ) :
    pretDistSq (fun _ => 1) (fun n => f n * costwist (-t) n) X
      = pretDistSq f (costwist t) X := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hre : ((fun _ => (1 : ℂ)) p
        * (starRingEnd ℂ) ((fun n => f n * costwist (-t) n) p)).re
      = (f p * (starRingEnd ℂ) (costwist t p)).re := by
    simp only [one_mul, Complex.conj_re, costwist_conj]
  rw [hre]

/-- **S1 — the window head-sup decay** (`window_sup_decay`).  For a globally 1-bounded (at
primes) `g`, `σ ∈ (0, 1]` with `e^{1/σ} ≤ X`, and a frequency `t` in the `M_range` window, the
seam head on the line `(1+σ)+it` obeys the honest window decay

  `‖F_seam(1+σ+it)‖ ≤ C_F·(1/σ)·exp(−(1/e)·(M_range(seamCoeff (ellLin g) 1 t₀; X,T)
    − 2·log(σ·logX) − 48))`,

with `C_F = exp(cpeel + (log 4 + cpeel))`.  The composition `head_sigma_bound ∘
scale_floor_Mrange_seam`: the pointwise Euler majorant at the seam datum, its distance
rewritten (`dist_triv_left_eq` + `seamCoeff_trivial_dist_eq`) to the bare `ℓ`-datum
shifted-center form and floored by the seam `M_range`. -/
theorem window_sup_decay {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X T σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X)
    (hmem : (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X) :
    ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
        (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
        * Real.exp (-(1 / Real.exp 1)
            * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                - 2 * Real.log (σ * Real.log X) - 48)) := by
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hEllOne (fun _ => le_of_eq norm_one) t₀ n
  have hHead := head_sigma_bound (g := seamCoeff (ellLin g) (fun _ => 1) t₀) hSeamOne hσ0 hσ1 t
  have hdist_eq :
      pretDistSq (fun _ => 1)
          (fun n => seamCoeff (ellLin g) (fun _ => 1) t₀ n * costwist (-t) n) (Real.exp (1 / σ))
        = pretDistSq (ellLin g) (costwist (t + t₀)) (Real.exp (1 / σ)) :=
    (dist_triv_left_eq (seamCoeff (ellLin g) (fun _ => 1) t₀) t (Real.exp (1 / σ))).trans
      (seamCoeff_trivial_dist_eq t₀ t (Real.exp (1 / σ)))
  rw [hdist_eq] at hHead
  refine hHead.trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Real.exp_nonneg _) (div_nonneg zero_le_one hσ0.le))
  apply Real.exp_le_exp.mpr
  rw [neg_mul, neg_mul]
  have hd := scale_floor_Mrange_seam (t₀ := t₀) hg hσ0 hσ1 hYX hmem
  have hepos : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
  exact neg_le_neg (mul_le_mul_of_nonneg_left hd hepos)

/-- **S1 squared** (`window_sup_decay_sq`).  The `S3`-consumer shape: squaring
`window_sup_decay` gives
`‖F_seam‖² ≤ C_F²·(1/σ²)·exp(−(2/e)·(M_range(...) − 2·log(σ·logX) − 48))`. -/
theorem window_sup_decay_sq {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X T σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X)
    (hmem : (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X) :
    ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
        (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
        * Real.exp (-(2 / Real.exp 1)
            * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                - 2 * Real.log (σ * Real.log X) - 48)) := by
  have h1 := window_sup_decay hg hσ0 hσ1 hYX hmem (t₀ := t₀)
  have hE2 : Real.exp (-(1 / Real.exp 1)
        * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
            - 2 * Real.log (σ * Real.log X) - 48)) ^ 2
      = Real.exp (-(2 / Real.exp 1)
        * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
            - 2 * Real.log (σ * Real.log X) - 48)) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  calc ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
            (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
        * ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
            (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ := by rw [pow_two]
    _ ≤ (Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
            * Real.exp (-(1 / Real.exp 1)
                * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                    - 2 * Real.log (σ * Real.log X) - 48)))
          * (Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
            * Real.exp (-(1 / Real.exp 1)
                * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                    - 2 * Real.log (σ * Real.log X) - 48))) :=
        mul_self_le_mul_self (norm_nonneg _) h1
    _ = Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
          * Real.exp (-(2 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                  - 2 * Real.log (σ * Real.log X) - 48)) := by
        rw [← hE2]; ring

/-- **S2 — the σ-cutoff of the window head decay** (`sigma_cutoff_seam`).  The σ-integral of
`window_sup_decay`'s majorant over the flat regime `[1/logX, 2η]`: for `logX ≥ 3` and
`1/logX ≤ 2η`, with `M_range(...) ≥ 0`,

  `∫_{1/logX}^{2η} (S1-majorant σ)/σ dσ
    ≤ C_F·(exp(48/e)/(1 − 2/e))·exp(−(1/e)·M_range(seamCoeff (ellLin g) 1 t₀)) · logX`,

via `sigma_cutoff_pretentious` (the `c = 1/e` flat-regime integral; `L := logX`, `C := 48`)
after `integral_congr` collapses `(1/σ)·(1/σ) = 1/σ²` and `integral_const_mul` pulls out the
constant `C_F = exp(cpeel + (log 4 + cpeel))`.  `sigma_cutoff_pretentious` is the directly
matching socket: the S1 majorant/σ is exactly `C_F ×` its integrand (no `Fbound`/`htriv`
plumbing, unlike `HExit.sigma_cutoff`'s `(1+M)` arm). -/
theorem sigma_cutoff_seam {g : ℕ → ℂ} {t₀ X T η : ℝ}
    (hL : 3 ≤ Real.log X) (hη : 1 / Real.log X ≤ 2 * η)
    (hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) :
    (∫ σ in (1 / Real.log X)..(2 * η),
        Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
          * Real.exp (-(1 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                  - 2 * Real.log (σ * Real.log X) - 48)) / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(1 / Real.exp 1) * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X := by
  have hCFnn : (0 : ℝ) ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) := Real.exp_nonneg _
  have hcong : Set.EqOn
      (fun σ => Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
          * Real.exp (-(1 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                  - 2 * Real.log (σ * Real.log X) - 48)) / σ)
      (fun σ => Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                  - 2 * Real.log (σ * Real.log X) - 48))))
      (Set.uIcc (1 / Real.log X) (2 * η)) := by
    intro σ _
    dsimp only
    ring
  rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const_mul]
  have hsc := sigma_cutoff_pretentious (L := Real.log X)
      (M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) (C := 48) (b := 2 * η)
      hL hM0 (by norm_num) hη
  have hconv : -(M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T / Real.exp 1)
      = -(1 / Real.exp 1) * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T := by ring
  rw [hconv] at hsc
  calc Real.exp (cpeel + (Real.log 4 + cpeel))
        * (∫ σ in (1 / Real.log X)..(2 * η),
            (1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1)
                * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                    - 2 * Real.log (σ * Real.log X) - 48)))
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
              * Real.exp (-(1 / Real.exp 1)
                  * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
              * Real.log X) := mul_le_mul_of_nonneg_left hsc hCFnn
    _ = Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(1 / Real.exp 1)
              * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X := by ring

end Salt.MR
