/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Twist
import Salt.Vk.GrowthPow

/-!
# VK-TWIST VT-3 — the β-thread through the VK ladder

VT-1/VT-2 (`Salt/ExpSum/Twist.lean`, `Salt/Vk/Twist.lean`) landed the two facts the whole
campaign rests on: the `k`-th difference (`k ≥ 2`) is blind to an affine phase, and the
twist `e(βn)` moves only the degree-1 Taylor coefficient of the block polynomial
(`twistCoef`).  This file threads that twist through the *aggregation* ladder, layer by
layer, up to the interface `Salt/MR/OneLinePowGrowth.lean` consumes.

## The thread

| layer | untwisted | twisted (here) |
|---|---|---|
| block bridge | `Core.vk_block_core` | `vk_block_core_twist` |
| per-block, interior | `Window.vk_block_at` (private) | `vk_block_at_twist` |
| dyadic ladder | `Windows.vk_ladder_bound` | *reused verbatim* (generic in `f`) |
| prefix ladder | `GrowthPow.vk_ladder_prefix` | *reused verbatim* (generic in `f`) |
| window | `Window.vk_window_bound` | `vk_window_bound_twist` |
| window, prefix | `GrowthPow.vk_window_prefix` | `vk_window_prefix_twist` |
| per-scale | `Window.vk_window_scale` | `vk_window_scale_twist` |
| per-scale, prefix | `GrowthPow.vk_window_scale_prefix` | `vk_window_scale_prefix_twist` |
| schedule (mid) | `Mid.vk_window_mid` | `vk_window_mid_twist` |
| schedule, prefix | `GrowthPow.vk_window_mid_prefix` | `vk_window_mid_prefix_twist` |
| weighted block | `ExpSum.zeta_weighted_block` | `vk_weighted_block_twist` |
| **the exit** | `GrowthPow.vk_dirichlet_block_le` | **`vk_dirichlet_block_twist_le`** |

`β` is a *single* real, fixed for the whole ladder (it comes from one Gauss completion at a
fixed `a/q`), threaded as a plain binder and never re-quantified per block.

## Two structural savings

* **The ladders are generic.**  `vk_ladder_bound` and `vk_ladder_prefix` are stated for an
  arbitrary `f : ℤ → E` in a normed group; the twisted phase is just another `f`.  No twin
  is needed, and none is written.
* **The margins are phase-independent.**  Everything between the window-select witness and
  the five `vk_block_core` hypotheses (`vk_window_scale`'s ~130-line margin grind, and
  `vk_window_mid`'s ~200-line schedule bookkeeping) never mentions the phase.  It is
  extracted here **once** — `vk_scale_margins`, `vk_mid_schedule` — and consumed by the
  full-window and prefix twins alike.

## Where the twist stops (a finding, recorded)

`vk_dirichlet_block_le` routes each dyadic block by `j = log M` into **three** branches.
Two of them twist:

* **low** (`Θ·j < log 2`): trivial — `‖e(βn)·n^{−s}‖ = ‖n^{−s}‖`, the twist is unimodular;
* **mid** (`log 2 ≤ Θ·j`, `10j < log t`): the VK ladder, twisted here.

The **high** branch (`10·log M ≥ log t`) runs `ExpSum.zeta_block_dispatch`, whose first
sub-case is *Kusmin* — a **first**-derivative test.  The twist shifts `φ'(n) = −t/(2πn)` to
`φ'(n) + β`, and `dk 1` is **not** affine-blind: the affine-blindness of VT-1 begins at
order 2.  So the high branch does not transcribe; it needs a Diophantine hypothesis on `β`
(the classical `√q` cost).  Accordingly:

* `vk_dirichlet_block_twist_le` — unconditional on the **non-high** range
  (`10·log M < log t`), with the *sharper* constant `10` (the `1348` was the high branch's);
* `vk_dirichlet_block_twist_le_of_high` — the total interface, with the high branch as an
  explicit socket binder (the `VkTwistUB` pattern of `Salt/MR/VkTwistClose.lean`).

Conventions unchanged: `eR x = exp(2πi·x)` (the `2π` inside), `phi t n = −(t/2π)·log n`, so
the twisted summand is `eR (phi t n + β·n)` on the phase side and
`eR (β·n) · n^{−s}` on the Dirichlet side.  No numeral is introduced anywhere: every
constant is the landed one.
-/

namespace Salt.Vk

open Finset Real MeasureTheory Salt.ExpSum Salt.Vmvt
open scoped BigOperators

/-! ## Section 1 — the twisted block bridge (`vk_block_core` twin) -/

set_option maxHeartbeats 2000000 in
-- Mirrors `vk_block_core`'s budget: the same analytic chain plus the same closing ledger.
/-- **`vk_block_core_twist` — THE BRIDGE, twisted.**  The *twisted* ζ-phase block sum has the
same pointwise Weyl bound `‖∑ eR(φ + β·id)‖ ≤ 8·P^{1−ρ}` as the untwisted one, from the same
machine-checked Vinogradov mean value theorem, with the same hypotheses — `VkSpaced` and the
`hW1` Taylor window are read only through degrees `≥ 2`, which the twist does not move.

The proof is `vk_block_core`'s with three edits: the front end is
`vk_block_taylor_reduce_twist` (same Taylor cost `R`), the coefficient vector is
`twistCoef β (vkCoef t N₀)`, and the box centers are re-based at the `j₀` site by
`vkOrbit_twistCoef` (`j₀ = js ≥ 2`).  Nothing else in the bridge reads degree 1. -/
theorem vk_block_core_twist {k r N₀ P P' Y : ℕ} {t ρbl β : ℝ} (hk : 19 ≤ k)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊) (hρ : ρbl = 1 / (16 * (k : ℝ) * r))
    (hP' : P' ≤ P) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ) / N₀) ^ (k + 1) ≤ ((N₀ : ℝ))⁻¹)
    (hW2 : ∃ js ∈ Finset.Icc 2 (k - 1), VkSpaced t N₀ P Y js ρbl k) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n + β * (n : ℝ))‖
      ≤ 8 * (P : ℝ) ^ (1 - ρbl) := by
  obtain ⟨js, hjs_mem, hspaced⟩ := hW2
  rw [Finset.mem_Icc] at hjs_mem
  have hjs2 : 2 ≤ js := hjs_mem.1
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hjsk : js + 1 ≤ k := by omega
  have hkR : (19 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0R : (0 : ℝ) < (k : ℝ) := by linarith
  -- r-facts
  have hr_ge : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (r : ℝ) := by rw [hr]; exact Nat.le_ceil _
  have hlog4k2 : 0 < Real.log (4 * (k : ℝ) ^ 2) := Real.log_pos (by nlinarith [hkR])
  have hr1 : 1 ≤ r := by
    have h0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le (by positivity) hr_ge
    have : 0 < r := by exact_mod_cast h0
    omega
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  -- P ≥ 2
  have hlogP : 0 < Real.log (P : ℝ) := by
    have hA : 0 < (k : ℝ) * Real.log (16 * (k : ℝ)) :=
      mul_pos hk0R (Real.log_pos (by nlinarith [hkR]))
    have hB : 0 ≤ 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log (k : ℝ) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hk1))
    nlinarith [hD, hA, hB]
  have hP2 : 2 ≤ P := by
    by_contra h; rw [not_le] at h; interval_cases P <;> simp_all
  have hP1' : 1 ≤ P := by omega
  have hPR : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  -- Y ≥ 1, N₀ > 0
  have hY1 : 1 ≤ Y := by rw [hY, Nat.one_le_ceil_iff]; positivity
  have hYR1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have hY0R : (0 : ℝ) < (Y : ℝ) := by linarith
  have hW2c := hspaced.2.2
  have hN0R : (0 : ℝ) < (N₀ : ℝ) := by nlinarith [hW2c, hk0R, hY0R]
  have hN0 : 0 < N₀ := by exact_mod_cast hN0R
  -- ρ facts
  have hkr1R : (1 : ℝ) ≤ (k : ℝ) * (r : ℝ) := by nlinarith [hk0R, hr1R, hkR]
  have hρ0 : 0 ≤ ρbl := by rw [hρ]; positivity
  have hρhalf : ρbl ≤ 1 / 2 := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hkr1R]
  -- 0 ≤ t
  have hW2a := hspaced.1
  have ht : 0 ≤ t := by
    have hlhs : (0 : ℝ) < (P : ℝ) ^ (-(js : ℝ) - ρbl) / (4 * (k : ℝ)) := by positivity
    have hpos := lt_of_lt_of_le hlhs hW2a
    by_contra h; rw [not_le] at h
    have : t / (2 * π * (N₀ : ℝ) ^ (js + 1)) < 0 := div_neg_of_neg_of_pos h (by positivity)
    linarith
  set c : ℕ → ℝ := twistCoef β (vkCoef t N₀) with hc
  set bb : ℕ := k * r with hbb
  set Pρ : ℝ := (P : ℝ) ^ (1 - ρbl) with hPρ
  have hPρpos : 0 < Pρ := Real.rpow_pos_of_pos hPpos _
  have hbb1 : 1 ≤ bb := by rw [hbb]; simpa using Nat.mul_le_mul hk1 hr1
  -- the two boundary rpow bounds
  have h2Y : 2 * (Y : ℝ) ≤ 5 * Pρ := vk_two_Y_le hP1' hY hρhalf
  rcases (by omega : Y ≤ P' ∨ P' < Y) with hYP' | hlt
  · -- MAIN branch
    have hP'1 : 1 ≤ P' := le_trans hY1 hYP'
    have hP'PR : (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP'
    -- Taylor cost bound (byte-identical to the untwisted one: same `R`)
    have hTaylor : 2 * π * ((P' : ℝ) * (2 * (t / (2 * π))
        * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))) ≤ Pρ := by
      have hXeq : (((P + Y : ℕ) : ℝ) / N₀) = ((P : ℝ) + (Y : ℝ)) / N₀ := by push_cast; ring
      have hcost : 2 * π * ((P' : ℝ) * (2 * (t / (2 * π))
          * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))) = 2 * (P' : ℝ)
          * (t * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1)) := by
        field_simp
      rw [hcost]
      have hbnd : t * (((P + Y : ℕ) : ℝ) / N₀) ^ (k + 1)
          ≤ (P : ℝ) ^ ((1 : ℝ) / 2) / (2 * (P' : ℝ)) := by
        refine le_trans hW1 ?_
        rw [le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hN0R]
        have hNhalf : 4 * (k : ℝ) ^ 2 * (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (N₀ : ℝ) := by
          have hYhalf : (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (Y : ℝ) := by rw [hY]; exact Nat.le_ceil _
          nlinarith [hW2c, hYhalf, hk0R]
        have hPsq : (P : ℝ) ^ ((1 : ℝ) / 2) * (P : ℝ) ^ ((1 : ℝ) / 2) = (P : ℝ) := by
          rw [← Real.rpow_add hPpos]; norm_num
        have hhalf_nn : (0 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hPpos.le _
        have hprod := mul_le_mul_of_nonneg_right hNhalf hhalf_nn
        have hmid : 4 * (k : ℝ) ^ 2 * (P : ℝ) ≤ (N₀ : ℝ) * (P : ℝ) ^ ((1 : ℝ) / 2) := by
          nlinarith [hprod, hPsq]
        have hk4 : (2 : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by nlinarith [hkR]
        nlinarith [hmid, hP'PR, hPpos, hk4]
      calc 2 * (P' : ℝ) * (t * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))
          = 2 * (P' : ℝ) * (t * (((P + Y : ℕ) : ℝ) / N₀) ^ (k + 1)) := by rw [hXeq]
        _ ≤ 2 * (P' : ℝ) * ((P : ℝ) ^ ((1 : ℝ) / 2) / (2 * (P' : ℝ))) :=
            mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = (P : ℝ) ^ ((1 : ℝ) / 2) := by field_simp
        _ ≤ Pρ := rpow_half_le_one_sub hP1' hρhalf
    -- centers, moments (in the TWISTED coefficients)
    set centers : Fin Y → Deg k → ℝ :=
      fun y j => Int.fract (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ) j) with hcenters
    set a : Fin Y → ℝ :=
      fun y => ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ)) (centers y)‖ with ha
    have ha_nn : ∀ y, 0 ≤ a y := fun y => norm_nonneg _
    have ha_eq : ∀ y : Fin Y,
        ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ)) (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ))‖ = a y := by
      intro y; rw [ha]; simp only [hcenters]
      exact (congrArg norm (genFun_fract k _ (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ)))).symm
    -- the box `hsep` — the ONLY site where the twist has to be undone (degree `js ≥ 2`)
    set j₀ : Deg k := ⟨js, by rw [Finset.mem_Icc]; omega⟩ with hj0
    have htworb : ∀ w : ℝ, vkOrbit k c w js = vkOrbit k (vkCoef t (N₀ : ℝ)) w js := by
      intro w; rw [hc]; exact vkOrbit_twistCoef k β (vkCoef t (N₀ : ℝ)) w hjs2
    have hsep : ∀ y y' : Fin Y, y ≠ y' →
        2 * vkDelta P k ρbl j₀ ≤ |centers y j₀ - centers y' j₀| := by
      intro y y' hyy'
      have hwY : ((y : ℕ) + 1 : ℝ) ≤ (Y : ℝ) := by
        have : (y : ℕ) + 1 ≤ Y := by have := y.2; omega
        exact_mod_cast this
      have hw'Y : ((y' : ℕ) + 1 : ℝ) ≤ (Y : ℝ) := by
        have : (y' : ℕ) + 1 ≤ Y := by have := y'.2; omega
        exact_mod_cast this
      have hne : (1 : ℝ) ≤ |((y : ℕ) + 1 : ℝ) - ((y' : ℕ) + 1 : ℝ)| := by
        have hyy'n : (y : ℕ) ≠ (y' : ℕ) := fun h => hyy' (Fin.ext h)
        have hred : ((y : ℕ) + 1 : ℝ) - ((y' : ℕ) + 1 : ℝ) = ((y : ℕ) : ℝ) - ((y' : ℕ) : ℝ) := by
          ring
        rw [hred]
        rcases (by omega : (y : ℕ) + 1 ≤ (y' : ℕ) ∨ (y' : ℕ) + 1 ≤ (y : ℕ)) with h | h
        · have hc1 : ((y : ℕ) : ℝ) + 1 ≤ ((y' : ℕ) : ℝ) := by exact_mod_cast h
          rw [abs_of_nonpos (by linarith)]; linarith
        · have hc1 : ((y' : ℕ) : ℝ) + 1 ≤ ((y : ℕ) : ℝ) := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]; linarith
      have key := vk_orbit_fract_sep hk1 hjsk hspaced
        (by have : (0 : ℝ) ≤ ((y : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hwY
        (by have : (0 : ℝ) ≤ ((y' : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hw'Y hne
      have keytw : 2 * ((P : ℝ) ^ (-(js : ℝ) - ρbl) / (16 * (k : ℝ)))
          ≤ |Int.fract (vkOrbit k c ((y : ℕ) + 1 : ℝ) js)
              - Int.fract (vkOrbit k c ((y' : ℕ) + 1 : ℝ) js)| := by
        simp only [htworb]; exact key
      simpa only [hcenters, vkDelta, vkOrbitPoint] using keytw
    -- Taylor front (TWISTED) + shift + fract
    have hstep0 := vk_block_taylor_reduce_twist k N₀ P P' Y t β ht hk1 hN0 hP'
    rw [← hc] at hstep0
    have hshift := vk_shift_to_orbit k P' Y c hYP'
    rw [Finset.sum_congr rfl (fun y _ => ha_eq y)] at hshift
    -- Icc-vs-range phase (the twist leaves the degree-0 slot at 0)
    have hc0 : c 0 = 0 := by rw [hc, twistCoef_zero, vkCoef]; simp
    have hpoly : ∀ m : ℤ, ∑ j ∈ Finset.Icc 1 k, c j * (m : ℝ) ^ j
        = ∑ j ∈ Finset.range (k + 1), c j * (m : ℝ) ^ j := by
      intro m
      rw [show Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) from by
            ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hc0, zero_mul, zero_add]
    have hWiWr : ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (∑ j ∈ Finset.Icc 1 k, c j * (m : ℝ) ^ j)‖
        = ‖∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j)‖ :=
      congrArg norm (Finset.sum_congr rfl (fun m _ => by rw [hpoly m]))
    rw [hWiWr] at hstep0
    -- box + vmvt + ledger (all phase-independent)
    have hbox := vk_box_disjoint_avg_of_centers k bb P' Y centers (vkDelta P k ρbl) j₀
      (fun y j => fract_mem_Icc _) (fun j => vkDelta_nonneg hk1 ρbl j)
      (fun j => vkDelta_le_one hP1' hk1 hρ0 j) (vkDelta_prod_pos (by omega) hk1 ρbl) hsep
    have hvmvt : (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ)
        ≤ vmvtConst k r * (P' : ℝ) ^ (vmvtExp k r) := vmvt k r P' hk2 hr1 hP'1
    have hClaimB := vkDelta_slack_le hP' hP1' hk1 ρbl
    have hClaimA : (∏ j : Deg k, vkDelta P k ρbl j)⁻¹
        * (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ) ≤ Pρ ^ (2 * bb) * (Y : ℝ) := by
      have hEnn : 0 ≤ vmvtExp k r := vmvtExp_nonneg hk2 hr1
      have hvc_nn : 0 ≤ vmvtConst k r := by rw [vmvtConst, vmvtC0]; positivity
      have hD_div : (k : ℝ) * Real.log (16 * (k : ℝ))
          + 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log (k : ℝ) ≤ 1 / 8 * Real.log P := by linarith [hD]
      have hconst := vk_const_le hk2 hP1' hD_div
      have hdinv := vkDelta_prod_inv (P := P) (by omega) hk1 ρbl
      have hJk_le : (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ)
          ≤ vmvtConst k r * (P : ℝ) ^ (vmvtExp k r) :=
        le_trans hvmvt (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hP'PR hEnn) hvc_nn)
      have hdinv_nn : 0 ≤ (∏ j : Deg k, vkDelta P k ρbl j)⁻¹ :=
        le_of_lt (inv_pos.mpr (vkDelta_prod_pos (by omega) hk1 ρbl))
      have hYhalf : (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (Y : ℝ) := by rw [hY]; exact Nat.le_ceil _
      calc (∏ j : Deg k, vkDelta P k ρbl j)⁻¹ * (Jk k bb (Finset.Ioc (0 : ℤ) (P' : ℤ)) : ℝ)
          ≤ (∏ j : Deg k, vkDelta P k ρbl j)⁻¹ * (vmvtConst k r * (P : ℝ) ^ (vmvtExp k r)) :=
            mul_le_mul_of_nonneg_left hJk_le hdinv_nn
        _ = ((16 * (k : ℝ)) ^ k * vmvtConst k r)
              * (P : ℝ) ^ (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl + vmvtExp k r) := by
            rw [hdinv]
            conv_rhs => rw [Real.rpow_add hPpos]
            ring
        _ ≤ (P : ℝ) ^ ((1 : ℝ) / 8)
              * (P : ℝ) ^ (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl + vmvtExp k r) :=
            mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hPpos.le _)
        _ = (P : ℝ) ^ ((1 : ℝ) / 8
              + (1 / 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ρbl + vmvtExp k r)) := by
            rw [← Real.rpow_add hPpos]
        _ ≤ (P : ℝ) ^ ((1 - ρbl) * (2 * ((k * r : ℕ) : ℝ)) + 1 / 2) :=
            Real.rpow_le_rpow_of_exponent_le (le_of_lt hPR) (by
              have := vk_exp_ineq hk1 hr1 hρ hr_ge; linarith)
        _ = Pρ ^ (2 * bb) * (P : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_add hPpos, hPρ, ← Real.rpow_natCast ((P : ℝ) ^ (1 - ρbl)) (2 * bb),
              ← Real.rpow_mul hPpos.le]
            congr 2; rw [hbb]; push_cast; ring
        _ ≤ Pρ ^ (2 * bb) * (Y : ℝ) := mul_le_mul_of_nonneg_left hYhalf (by positivity)
    -- combine: ∑ a ≤ 2 Pρ Y
    have hsumroot : (∑ y : Fin Y, a y) ≤ 2 * Pρ * (Y : ℝ) := by
      have hSlk_nn : 0 ≤ 2 * π
          * ((P' : ℝ) * ∑ j : Deg k, vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ)) := by
        have := vkDelta_prod_pos (by omega : 0 < P) hk1 ρbl
        refine mul_nonneg (by positivity) (mul_nonneg (by positivity) (Finset.sum_nonneg ?_))
        intro j _; exact mul_nonneg (vkDelta_nonneg hk1 ρbl j) (by positivity)
      have hpow : (∑ y : Fin Y, a y) ^ (2 * bb)
          ≤ (2 : ℝ) ^ (2 * bb) * Pρ ^ (2 * bb) * (Y : ℝ) ^ (2 * bb) := by
        have hjen := vk_pow_sum_le bb Y a ha_nn (by omega : 1 ≤ 2 * bb)
        calc (∑ y : Fin Y, a y) ^ (2 * bb)
            ≤ (Y : ℝ) ^ (2 * bb - 1) * ∑ y : Fin Y, a y ^ (2 * bb) := hjen
          _ ≤ (Y : ℝ) ^ (2 * bb - 1) * (2 ^ (2 * bb - 1) * (2 * (Pρ ^ (2 * bb) * (Y : ℝ)))) := by
              refine mul_le_mul_of_nonneg_left (le_trans hbox
                (mul_le_mul_of_nonneg_left ?_ (by positivity))) (by positivity)
              have hB : (Y : ℝ) * (2 * π * ((P' : ℝ) * ∑ j : Deg k,
                    vkDelta P k ρbl j * (P' : ℝ) ^ (j : ℕ))) ^ (2 * bb)
                  ≤ Pρ ^ (2 * bb) * (Y : ℝ) := by
                rw [mul_comm]
                exact mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ hSlk_nn hClaimB (2 * bb)) (by positivity)
              nlinarith [hClaimA, hB]
          _ = (2 : ℝ) ^ (2 * bb) * Pρ ^ (2 * bb) * (Y : ℝ) ^ (2 * bb) := by
              have hY2 : (Y : ℝ) ^ (2 * bb - 1) * (Y : ℝ) = (Y : ℝ) ^ (2 * bb) := by
                rw [← pow_succ]; congr 1; omega
              have h22 : (2 : ℝ) ^ (2 * bb - 1) * 2 = (2 : ℝ) ^ (2 * bb) := by
                rw [← pow_succ]; congr 1; omega
              rw [← hY2, ← h22]; ring
      have hrhs : (2 : ℝ) ^ (2 * bb) * Pρ ^ (2 * bb) * (Y : ℝ) ^ (2 * bb)
          = (2 * Pρ * (Y : ℝ)) ^ (2 * bb) := by rw [mul_pow, mul_pow]
      rw [hrhs] at hpow
      exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow
    -- Wr ≤ 2Pρ + 2Y, then final
    have hWr_le : ‖∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
        eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j)‖ ≤ 2 * Pρ + 2 * (Y : ℝ) := by
      have hYWr : (Y : ℝ) * ‖∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j)‖
          ≤ (Y : ℝ) * (2 * Pρ + 2 * (Y : ℝ)) := by nlinarith [hshift, hsumroot, hY0R]
      exact le_of_mul_le_mul_left hYWr hY0R
    calc ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n + β * (n : ℝ))‖
        ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
            eR (∑ j ∈ Finset.range (k + 1), c j * (m : ℝ) ^ j)‖
          + 2 * π * ((P' : ℝ) * (2 * (t / (2 * π))
            * (((P : ℝ) + (Y : ℝ)) / N₀) ^ (k + 1))) := hstep0
      _ ≤ (2 * Pρ + 2 * (Y : ℝ)) + Pρ := add_le_add hWr_le hTaylor
      _ ≤ 8 * Pρ := by linarith [h2Y]
  · -- TRIVIAL branch: P' < Y (the twist is unimodular, so the count bound is unchanged)
    have htriv : ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n + β * (n : ℝ))‖
        ≤ (P' : ℝ) := by
      calc ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n + β * (n : ℝ))‖
          ≤ ∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), ‖eR (phi t n + β * (n : ℝ))‖ := norm_sum_le _ _
        _ = ∑ _n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), (1 : ℝ) :=
            Finset.sum_congr rfl (fun n _ => by rw [norm_eR])
        _ = (P' : ℝ) := by
            rw [Finset.sum_const, Int.card_Ioc]
            simp only [nsmul_eq_mul, mul_one]
            rw [show (N₀ : ℤ) + (P' : ℤ) - N₀ = (P' : ℤ) from by ring]
            simp
    have hP'YR : (P' : ℝ) < (Y : ℝ) := by exact_mod_cast hlt
    have hhalf1 : (1 : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.one_le_rpow (by exact_mod_cast hP1') (by norm_num)
    have hYceil : (Y : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 2) + 1 := by
      rw [hY]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have hle := rpow_half_le_one_sub hP1' hρhalf
    calc ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n + β * (n : ℝ))‖ ≤ (P' : ℝ) := htriv
      _ ≤ 8 * Pρ := by rw [hPρ]; linarith [hPρpos]

/-! ## Section 2 — the per-block interior bound and the two window twins

`vk_ladder_bound` (`Salt/Vk/Windows.lean`) and `vk_ladder_prefix` (`Salt/Vk/GrowthPow.lean`)
are stated for an arbitrary `f : ℤ → E`; the twisted phase is just another `f`, so both are
reused **verbatim** and no ladder twin is written.  Only the per-block feed changes. -/

/-- **Per-block `vk_block_core_twist` at an interior block `N₀ ∈ [N, 2N]`.**  Twisted twin of
`Window.vk_block_at` (private there, hence re-derived here): the per-scale worst-case
hypotheses (`hW1` at `N`, `hW2a` at `2N`, `hW2b`/`hW2c` at `N`) recover the block-specific
`vk_block_core_twist` hypotheses by monotonicity in `N₀`.  Every hypothesis is the untwisted
one — the twist never enters. -/
private lemma vk_block_at_twist {k r P P' Y N N₀ : ℕ} {t ρ β : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hP' : P' ≤ P)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hNle : N ≤ N₀) (hN₀le : N₀ ≤ 2 * N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ)) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n + β * (n : ℝ))‖
      ≤ 8 * (P : ℝ) ^ (1 - ρ) := by
  have hN0pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hN₀0 : (0 : ℝ) < (N₀ : ℝ) := lt_of_lt_of_le hN0pos (by exact_mod_cast hNle)
  have hNleR : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hNle
  have hN₀leR : (N₀ : ℝ) ≤ (2 * N : ℝ) := by exact_mod_cast hN₀le
  have hπ : (0 : ℝ) < 2 * π := by positivity
  refine vk_block_core_twist hk hr hρ hP' hY hD ?_ ⟨js, ?_, ?_, ?_, ?_⟩
  · -- hW1 at N₀
    have hkey : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k :=
      le_trans hW1 (by gcongr)
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    calc t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k := hkey
      _ = ((N₀ : ℝ))⁻¹ * (N₀ : ℝ) ^ (k + 1) := by
          rw [pow_succ, mul_comm ((N₀ : ℝ) ^ k) (N₀ : ℝ), ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hN₀0), one_mul]
  · rw [Finset.mem_Icc]; exact ⟨hjs2, hjsk⟩
  · -- W2a at N₀
    have hpow : ((N₀ : ℝ)) ^ (js + 1) ≤ ((2 * N : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN₀0.le hN₀leR _
    calc (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
        ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)) := hW2a
      _ ≤ t / (2 * π * ((N₀ : ℝ)) ^ (js + 1)) := by gcongr
  · -- W2b at N₀
    have hpow : ((N : ℝ)) ^ (js + 1) ≤ ((N₀ : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN0pos.le hNleR _
    calc t * (Y : ℝ) / (2 * π * ((N₀ : ℝ)) ^ (js + 1))
        ≤ t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) := by gcongr
      _ ≤ 1 / 6 := hW2b
  · -- W2c at N₀
    calc 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ) := hW2c
      _ ≤ (N₀ : ℝ) := hNleR

/-- **R5b window bound, twisted.**  Twin of `Window.vk_window_bound`: the full dyadic window
`(N, 2N]` of the *twisted* ζ-phase Weyl sum obeys `≤ 10·N·P^{−ρ}`, from the same five
per-scale worst-case hypotheses.  Assembled by the generic `vk_ladder_bound`. -/
theorem vk_window_bound_twist {k r P Y N : ℕ} {t ρ β : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hP : 1 ≤ P) (h4P : 4 * P ≤ N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ)) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n + β * (n : ℝ))‖
      ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  apply vk_ladder_bound (fun n => eR (phi t n + β * (n : ℝ))) hP h4P
  intro i hi
  have hP0Z : (0 : ℤ) ≤ (P : ℤ) := by positivity
  have hiP0 : (0 : ℤ) ≤ (i : ℤ) * (P : ℤ) := by positivity
  have hN0Z : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have hstep : ((i : ℤ) + 1) * (P : ℤ) = (i : ℤ) * (P : ℤ) + (P : ℤ) := by ring
  have hage : (N : ℤ) ≤ min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    le_min (by linarith) (by linarith)
  have hab : min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)
      ≤ min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) :=
    min_le_min (by linarith [hstep, hP0Z]) (le_refl _)
  have hale : min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) ≤ 2 * N := min_le_right _ _
  have hbma : min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) ≤ (P : ℤ) := by
    omega
  set N₀ : ℕ := (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hN₀def
  set P' : ℕ := (min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hP'def
  have haN₀ : (N₀ : ℤ) = min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (le_trans hN0Z hage)
  have hP'val : (P' : ℤ) = min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (by linarith [hab])
  have hbval : min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) = (N₀ : ℤ) + (P' : ℤ) := by
    rw [haN₀, hP'val]; ring
  have hNleN₀ : N ≤ N₀ := by
    have : (N : ℤ) ≤ (N₀ : ℤ) := by rw [haN₀]; exact hage
    exact_mod_cast this
  have hN₀le2N : N₀ ≤ 2 * N := by
    have : (N₀ : ℤ) ≤ 2 * N := by rw [haN₀]; exact hale
    exact_mod_cast this
  have hP'le : P' ≤ P := by
    have : (P' : ℤ) ≤ (P : ℤ) := by rw [hP'val]; exact hbma
    exact_mod_cast this
  rw [haN₀.symm, hbval]
  exact vk_block_at_twist hk hr hρ hP'le hY hNleN₀ hN₀le2N hN1 hjs2 hjsk htpos hD hW1 hW2a hW2b hW2c

/-- **Prefix window bound, twisted.**  Twin of `GrowthPow.vk_window_prefix`: every prefix
`(N, y]` (`N < y ≤ 2N`) of the twisted window obeys `≤ 10·N·P^{−ρ}`.  Assembled by the
generic `vk_ladder_prefix` (the min-trick), fed by `vk_block_at_twist`. -/
theorem vk_window_prefix_twist {k r P Y N : ℕ} {t ρ β : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hP : 1 ≤ P) (h4P : 4 * P ≤ N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ))
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n + β * (n : ℝ))‖
      ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  apply vk_ladder_prefix (fun n => eR (phi t n + β * (n : ℝ))) hP h4P ?_ y hy1 hy2
  intro i hi z hz1 hz2
  have hN0Z : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have hiP0 : (0 : ℤ) ≤ (i : ℤ) * (P : ℤ) := by positivity
  have hage : (N : ℤ) ≤ min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    le_min (by linarith) (by linarith)
  have hbma : min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) ≤ (P : ℤ) := by
    have hstep : ((i : ℤ) + 1) * (P : ℤ) = (i : ℤ) * (P : ℤ) + (P : ℤ) := by ring
    have hP0Z : (0 : ℤ) ≤ (P : ℤ) := by positivity
    omega
  set N₀ : ℕ := (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hN₀def
  set P' : ℕ := (z - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hP'def
  have haN₀ : (N₀ : ℤ) = min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (le_trans hN0Z hage)
  have hP'val : (P' : ℤ) = z - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (by linarith [hz1])
  have hzval : z = (N₀ : ℤ) + (P' : ℤ) := by rw [haN₀, hP'val]; ring
  have hNleN₀ : N ≤ N₀ := by
    have : (N : ℤ) ≤ (N₀ : ℤ) := by rw [haN₀]; exact hage
    exact_mod_cast this
  have hN₀le2N : N₀ ≤ 2 * N := by
    have : (N₀ : ℤ) ≤ 2 * N := by rw [haN₀]; exact min_le_right _ _
    exact_mod_cast this
  have hP'le : P' ≤ P := by
    have : (P' : ℤ) ≤ (P : ℤ) := by rw [hP'val]; linarith [hz2, hbma]
    exact_mod_cast this
  rw [haN₀.symm, hzval]
  exact vk_block_at_twist hk hr hρ hP'le hY hNleN₀ hN₀le2N hN1 hjs2 hjsk htpos hD hW1 hW2a hW2b hW2c

/-! ## Section 3 — the per-scale discharge (WALL 1), phase-independent

`vk_window_scale`'s ~130-line margin grind never mentions the phase: it converts the
window-select witness `P = ⌈N^{1−(m+2)/(k+1)}⌉`, `Y = ⌈P^{1/2}⌉`, `js = m+2` into exactly
the eight facts `vk_window_bound`/`vk_window_prefix` consume.  It is extracted once here and
fed to both twisted twins. -/

/-- Exp-monotone (copy of `Window.vk_exp_mono_le`, private there). -/
private lemma vk_exp_mono_le' {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : Real.log A ≤ Real.log B) : A ≤ B := by
  have := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hA, Real.exp_log hB] at this

set_option maxHeartbeats 1600000 in
-- The five margin discharges thread ~40 shared log-atom facts through staged `nlinarith` calls;
-- the default budget times out in the W2a corner arithmetic (as in `vk_window_scale`).
/-- **WALL 1 margins, extracted.**  At the (VK-8-amended) window-select witness
`P = ⌈N^{1−(m+2)/(k+1)}⌉`, `Y = ⌈P^{1/2}⌉`, `js = m+2` on the band `11 ≤ m`, `m+8 ≤ k`, with
the `hD` P-floor and the `j`-floor, the eight inputs of the window bound all hold.  This is
the body of `vk_window_scale` up to (but not including) its final `vk_window_bound` call —
phase-independent, hence shared by the full-window and prefix twisted twins. -/
private lemma vk_scale_margins {k r m N P Y : ℕ} {t ρ : ℝ}
    (hk : 19 ≤ k) (hρ : ρ = 1 / (16 * (k : ℝ) * r))
    (hm11 : 11 ≤ m) (hmk : m + 8 ≤ k) (hN1 : 1 ≤ N)
    (hP : P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (htlo : (N : ℝ) ^ (m - 1) < t) (hthi : t ≤ (N : ℝ) ^ m)
    (hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N)
    (hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N) :
    1 ≤ P ∧ 4 * P ≤ N ∧ 0 < t
      ∧ 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P
      ∧ t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k
      ∧ (P : ℝ) ^ (-((m + 2 : ℕ) : ℝ) - ρ) / (4 * k)
          ≤ t / (2 * π * ((2 * N : ℝ)) ^ (m + 2 + 1))
      ∧ t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (m + 2 + 1)) ≤ 1 / 6
      ∧ 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ) := by
  -- ## Setup: positivity and the basic cast facts (`q` opaque to avoid defeq storms)
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hqdef] at hP hDf
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmR11 : (11 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm11
  have hmkR : (m : ℝ) + 8 ≤ (k : ℝ) := by exact_mod_cast hmk
  have humc : (0 : ℝ) ≤ (m : ℝ) - 11 := by linarith
  have hvmc : (0 : ℝ) ≤ (k : ℝ) - (m : ℝ) - 8 := by linarith
  have hq0 : 0 ≤ q := by
    rw [hqdef, sub_nonneg, div_le_one hk1R]; linarith
  have hq1 : q ≤ 1 := by
    rw [hqdef]
    have : 0 ≤ ((m : ℝ) + 2) / ((k : ℝ) + 1) := by positivity
    linarith
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hj0 : 0 ≤ Real.log N := Real.log_nonneg hNR1
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlk0 : 0 ≤ Real.log (k : ℝ) := by
    apply Real.log_nonneg; exact_mod_cast (show 1 ≤ k by omega)
  have hkl2nn : 0 ≤ ((k : ℝ) + 1) * Real.log 2 := by positivity
  have hj8 : 8 ≤ Real.log N := by linarith [hjf, hkl2nn, hlk0]
  have hP1 : 1 ≤ P := by
    rw [hP, Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hNpos _
  have hPR1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  have hlP0 : 0 ≤ Real.log P := Real.log_nonneg hPR1
  have hY1 : 1 ≤ Y := by
    rw [hY, Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hPpos _
  have htpos : 0 < t :=
    lt_trans (show (0 : ℝ) < (N : ℝ) ^ (m - 1) by positivity) htlo
  -- ## Log bounds for P, Y, t
  have hlPlo : q * Real.log N ≤ Real.log P := vk_logP_ge hN1 hP
  have hlPub : Real.log P ≤ Real.log 2 + q * Real.log N := vk_logP_ub hN1 hq0 hP
  have hlYub : Real.log Y ≤ Real.log 2 + 1 / 2 * Real.log P := by
    have h := vk_logP_ub hP1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hY
    linarith [h]
  have hltub : Real.log t ≤ (m : ℝ) * Real.log N := by
    calc Real.log t ≤ Real.log ((N : ℝ) ^ m) := Real.log_le_log htpos hthi
      _ = (m : ℝ) * Real.log N := by rw [Real.log_pow]
  have hltlo : ((m : ℝ) - 1) * Real.log N ≤ Real.log t := by
    have h1 : Real.log ((N : ℝ) ^ (m - 1)) ≤ Real.log t :=
      Real.log_le_log (by positivity) htlo.le
    rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h1
    exact h1
  -- ## The guard 4P ≤ N
  have h2kl2 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ Real.log N := by linarith [hjf, hlk0]
  have h13 : 3 * Real.log 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * Real.log N := by
    nlinarith [h2kl2, mul_nonneg humc hj0, mul_nonneg hl20 hk1R.le]
  have h1mq : (1 - q) * Real.log N = ((m : ℝ) + 2) * Real.log N / ((k : ℝ) + 1) := by
    rw [hqdef]; field_simp; ring
  have h3l2q : 3 * Real.log 2 ≤ (1 - q) * Real.log N := by
    rw [h1mq, le_div_iff₀ hk1R]; linarith [h13]
  have hguardR : (4 : ℝ) * (P : ℝ) ≤ (N : ℝ) := by
    apply vk_exp_mono_le' (by positivity) hNpos
    have h4P : Real.log (4 * (P : ℝ)) = 2 * Real.log 2 + Real.log P := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hPpos),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [h4P]; linarith [hlPub, h3l2q]
  have h4PN : 4 * P ≤ N := by exact_mod_cast hguardR
  -- ## hD: the P-floor
  have hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ Real.log P := le_trans hDf hlPlo
  -- ## The W1 margin
  have hYP : Y ≤ P := by
    rw [hY]
    apply Nat.ceil_le.mpr
    calc (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (P : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hPR1 (by norm_num)
      _ = (P : ℝ) := Real.rpow_one _
  have hlogPY : Real.log ((P + Y : ℕ) : ℝ) ≤ 2 * Real.log 2 + q * Real.log N := by
    have hYR : (Y : ℝ) ≤ (P : ℝ) := by exact_mod_cast hYP
    calc Real.log ((P + Y : ℕ) : ℝ) ≤ Real.log (2 * (P : ℝ)) := by
          apply Real.log_le_log (by push_cast; positivity)
          push_cast; linarith
      _ = Real.log 2 + Real.log P := Real.log_mul (by norm_num) (ne_of_gt hPpos)
      _ ≤ 2 * Real.log 2 + q * Real.log N := by linarith [hlPub]
  have hW1m : Real.log t + ((k + 1 : ℕ) : ℝ) * Real.log ((P + Y : ℕ) : ℝ)
      ≤ (k : ℝ) * Real.log N := by
    have hexp : ((k : ℝ) + 1) * (2 * Real.log 2 + q * Real.log N)
        = 2 * ((k : ℝ) + 1) * Real.log 2 + ((k : ℝ) - (m : ℝ) - 1) * Real.log N := by
      rw [hqdef]; field_simp; ring
    have h2 : ((k : ℝ) + 1) * Real.log ((P + Y : ℕ) : ℝ)
        ≤ 2 * ((k : ℝ) + 1) * Real.log 2 + ((k : ℝ) - (m : ℝ) - 1) * Real.log N := by
      rw [← hexp]; exact mul_le_mul_of_nonneg_left hlogPY (by positivity)
    have hkcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hkcast]
    nlinarith [hltub, h2, hjf, hlk0]
  -- ## The W2c margin
  have hW2cm : Real.log 8 + 2 * Real.log k + 1 / 2 * Real.log P ≤ Real.log N := by
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by nlinarith [hq1, hj0]
    have hkl2 : 3 * Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl20
      exact_mod_cast (show 3 ≤ k by omega)
    rw [hl8]
    linarith [hjf, hlPub, hqj_le, hkl2, hlk0, hl20]
  -- ## The W2b margin
  have hW2bm : Real.log t + Real.log Y ≤ ((m + 2 + 1 : ℕ) : ℝ) * Real.log N := by
    have hc : ((m + 2 + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by nlinarith [hq1, hj0]
    rw [hc]
    nlinarith [hltub, hlYub, hlPub, hqj_le, hj8, hl21, hl20]
  -- ## The W2a margin (the corner: (m+2)(k−m−1) ≥ (9/2)(k+1) on the band)
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hf : 9 / 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * ((k : ℝ) - (m : ℝ) - 1) := by
    nlinarith [mul_nonneg humc hvmc]
  have hqj : 9 / 2 * Real.log N ≤ ((m : ℝ) + 2) * (q * Real.log N) := by
    have hqeq : q * Real.log N = ((k : ℝ) - (m : ℝ) - 1) * Real.log N / ((k : ℝ) + 1) := by
      rw [hqdef]; field_simp; ring
    rw [hqeq, mul_div_assoc', le_div_iff₀ hk1R]
    nlinarith [mul_le_mul_of_nonneg_right hf hj0]
  have hlPq : ((m : ℝ) + 2) * (q * Real.log N) ≤ ((m : ℝ) + 2) * Real.log P :=
    mul_le_mul_of_nonneg_left hlPlo (by linarith)
  have hl2π : Real.log (2 * π) ≤ 7 := by
    have hπ4 : π ≤ 4 := Real.pi_le_four
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * π by positivity)
    linarith
  have hl2lb : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hl4k : 0 ≤ Real.log (4 * (k : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  have hW2am : (-((m + 2 : ℕ) : ℝ) - ρ) * Real.log P - Real.log (4 * (k : ℝ))
      ≤ Real.log t - Real.log (2 * π) - ((m + 2 + 1 : ℕ) : ℝ) * Real.log (2 * (N : ℝ)) := by
    have hcjs : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    have hcjs1 : ((m + 2 + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
    have hl2N : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) (ne_of_gt hNpos)
    have hml2 : ((m : ℝ) + 9) * Real.log 2 ≤ ((k : ℝ) + 1) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl20; linarith
    have hkey : 9 / 2 * Real.log N ≤ ((m : ℝ) + 2) * Real.log P := le_trans hqj hlPq
    rw [hcjs, hcjs1, hl2N]
    nlinarith [hltlo, hkey, hl2π, hl4k, hjf, hml2, mul_nonneg hρ0 hlP0, hlk0, hl2lb]
  -- ## Bundle
  exact ⟨hP1, h4PN, htpos, hD,
    vk_hW1_form htpos hP1 hN1 hW1m,
    vk_hW2a_form (by omega) hP1 hN1 htpos hW2am,
    vk_hW2b_form htpos hY1 hN1 hW2bm,
    vk_hW2c_form (by omega) hP1 hN1 hY hW2cm⟩

/-- **WALL 1 per-scale theorem, twisted.**  Twin of `Window.vk_window_scale`: at the amended
window-select witness the *twisted* dyadic window obeys the freeze's `≤ 10·N·P^{−ρ}`. -/
theorem vk_window_scale_twist {k r m N P Y : ℕ} {t ρ β : ℝ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r))
    (hm11 : 11 ≤ m) (hmk : m + 8 ≤ k) (hN1 : 1 ≤ N)
    (hP : P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (htlo : (N : ℝ) ^ (m - 1) < t) (hthi : t ≤ (N : ℝ) ^ m)
    (hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N)
    (hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n + β * (n : ℝ))‖
      ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  obtain ⟨hP1, h4PN, htpos, hD, hW1, hW2a, hW2b, hW2c⟩ :=
    vk_scale_margins hk hρ hm11 hmk hN1 hP hY htlo hthi hDf hjf
  exact vk_window_bound_twist (js := m + 2) hk hr hρ hY hP1 h4PN hN1 (by omega) (by omega)
    htpos hD hW1 hW2a hW2b hW2c

/-- **Prefix per-scale theorem, twisted.**  Twin of `GrowthPow.vk_window_scale_prefix`: the
same witness, concluding the *prefix* bound for every `N < y ≤ 2N`. -/
theorem vk_window_scale_prefix_twist {k r m N P Y : ℕ} {t ρ β : ℝ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r))
    (hm11 : 11 ≤ m) (hmk : m + 8 ≤ k) (hN1 : 1 ≤ N)
    (hP : P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (htlo : (N : ℝ) ^ (m - 1) < t) (hthi : t ≤ (N : ℝ) ^ m)
    (hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N)
    (hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N)
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n + β * (n : ℝ))‖
      ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  obtain ⟨hP1, h4PN, htpos, hD, hW1, hW2a, hW2b, hW2c⟩ :=
    vk_scale_margins hk hρ hm11 hmk hN1 hP hY htlo hthi hDf hjf
  exact vk_window_prefix_twist (js := m + 2) hk hr hρ hY hP1 h4PN hN1 (by omega) (by omega)
    htpos hD hW1 hW2a hW2b hW2c y hy1 hy2

/-! ## Section 4 — the `k(t)`-schedule (mid branch), phase-independent

`vk_window_mid`'s ~200-line schedule bookkeeping is likewise phase-free: it manufactures the
internal `P`, `Y`, `ρ` and discharges every `vk_window_scale` input, plus the `P^{−ρ} →
exp(−Θ·log N)` fold.  Extracted once as `vk_mid_schedule`. -/

/-- Copy of `Mid.vk_lnD_budget` (private there). -/
private lemma vk_lnD_budget' {k r : ℕ} {A ℓ : ℝ}
    (hkR_lo : A ≤ (k : ℝ)) (hkR_ub : (k : ℝ) ≤ 11 / 10 * A) (hr_ub : (r : ℝ) ≤ 6 / 10 * (k : ℝ) * ℓ)
    (hlnk_ub : Real.log k ≤ 28 / 100 * ℓ) (hlnk0 : 0 ≤ Real.log k) (hr0R : (0 : ℝ) < (r : ℝ))
    (hk0R : (0 : ℝ) < (k : ℝ)) (hl21 : Real.log 2 ≤ 1) (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hA0 : (0 : ℝ) < A) (hℓ0 : (0 : ℝ) < ℓ) :
    8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ 52 * A ^ 3 * ℓ ^ 2 := by
  have hlog16k : Real.log (16 * (k : ℝ)) ≤ 4 + 28 / 100 * ℓ := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hk0R)]
    have h16 : Real.log 16 ≤ 4 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith [hl21]
    linarith [hlnk_ub]
  have hT1 : (k : ℝ) * Real.log (16 * k) ≤ 4 / 10 * A * ℓ := by
    have h1 : (k : ℝ) * Real.log (16 * k) ≤ (11 / 10 * A) * (4 + 28 / 100 * ℓ) := by
      apply mul_le_mul hkR_ub hlog16k _ (by positivity)
      apply Real.log_nonneg; nlinarith [hkR_lo, hA26]
    nlinarith [h1, hA0, hℓ100, mul_nonneg hA0.le (show (0 : ℝ) ≤ ℓ by linarith)]
  have hk2 : (k : ℝ) ^ 2 ≤ (11 / 10 * A) ^ 2 := by nlinarith [hkR_ub, hkR_lo, hA0]
  have hrk : (r : ℝ) ≤ 6 / 10 * (11 / 10 * A) * ℓ := by
    apply le_trans hr_ub; nlinarith [hkR_ub, hℓ100]
  have hkr_lnk : (k : ℝ) ^ 2 * (r : ℝ) * Real.log k
      ≤ (11 / 10 * A) ^ 2 * (6 / 10 * (11 / 10 * A) * ℓ) * (28 / 100 * ℓ) :=
    mul_le_mul (mul_le_mul hk2 hrk hr0R.le (by positivity)) hlnk_ub hlnk0 (by positivity)
  have hT2 : 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log k ≤ 6 * A ^ 3 * ℓ ^ 2 := by
    nlinarith [hkr_lnk, hA0, hℓ0, mul_pos (pow_pos hA0 3) (pow_pos hℓ0 2)]
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have hAℓ : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
    have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith [hA2, hℓ100, hℓ0]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]
  linarith [hT1, hT2, hAℓ]

/-- Copy of `Mid.vk_Aℓ_cube` (private there). -/
private lemma vk_Aℓ_cube' {A ℓ : ℝ} (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hA0 : (0 : ℝ) < A) (hℓ0 : (0 : ℝ) < ℓ) : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith [hA2, hℓ100, hℓ0]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]

/-- Copy of `Mid.vk_theta_saving` (private there). -/
private lemma vk_theta_saving' {A ℓ j ρ LP : ℝ} (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hj0 : (0 : ℝ) < j) (hρpos : (0 : ℝ) < ρ)
    (hρlo : 1 / (12 * A ^ 2 * ℓ) ≤ ρ) (hLP : j / 2 ≤ LP) :
    (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j ≤ ρ * LP := by
  have hD0 : (0 : ℝ) < A ^ 3 * ℓ ^ 2 := by positivity
  have hstep2 : (1 / (12 * A ^ 2 * ℓ)) * (j / 2) ≤ ρ * LP :=
    mul_le_mul hρlo hLP (by positivity) hρpos.le
  have hcompare : (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j ≤ (1 / (12 * A ^ 2 * ℓ)) * (j / 2) := by
    have hAℓ2600 : (2600 : ℝ) ≤ A * ℓ := by nlinarith [hA26, hℓ100]
    have hden : 24 * (A ^ 2 * ℓ) ≤ 1000 * (A ^ 3 * ℓ ^ 2) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ A ^ 2 * ℓ by positivity)
        (show (0 : ℝ) ≤ 1000 * (A * ℓ) - 24 by linarith [hAℓ2600])]
    have hL : (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j = j / (1000 * (A ^ 3 * ℓ ^ 2)) := by
      field_simp
    have hR : (1 / (12 * A ^ 2 * ℓ)) * (j / 2) = j / (24 * (A ^ 2 * ℓ)) := by field_simp; ring
    rw [hL, hR]
    gcongr
  linarith [hstep2, hcompare]

set_option maxHeartbeats 4000000 in
-- The ~55-hypothesis schedule bookkeeping (as in `vk_window_mid`) exceeds the default budget.
/-- **The mid-branch schedule, extracted.**  For `log t ≥ e^100`, `N ≥ 2` in the mid routing
band, the freeze schedule `k = max(19, ⌈L^{1/4}⌉)`, `r = ⌈k·log 4k²⌉`, `m = ⌈L/j⌉` produces
window-select parameters `P = ⌈N^{1−(m+2)/(k+1)}⌉`, `Y = ⌈P^{1/2}⌉`, `ρ = 1/(16kr)` meeting
every `vk_window_scale` input, and the saving folds: `P^{−ρ} ≤ exp(−Θ·log N)`.

This is `vk_window_mid`'s body up to (but not including) its `vk_window_scale` call and the
closing `exp`-fold — phase-independent, hence shared by both twisted mid twins. -/
private lemma vk_mid_schedule {t : ℝ} {N k r m : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t) (hN2 : 2 ≤ N)
    (hk : k = max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hm : m = ⌈Real.log t / Real.log N⌉₊)
    (hroute : Real.log 2 ≤ vkTheta t * Real.log N)
    (hjhi : 10 * Real.log N < Real.log t) :
    ∃ P Y : ℕ, ∃ ρ : ℝ,
      19 ≤ k ∧ 11 ≤ m ∧ m + 8 ≤ k ∧ 1 ≤ N
      ∧ P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊
      ∧ Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊
      ∧ ρ = 1 / (16 * (k : ℝ) * r)
      ∧ (N : ℝ) ^ (m - 1) < t ∧ t ≤ (N : ℝ) ^ m
      ∧ 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
          ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N
      ∧ 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N
      ∧ (P : ℝ) ^ (-ρ) ≤ Real.exp (-(vkTheta t * Real.log N)) := by
  -- ## Opaque scalars (defeq-storm avoidance)
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log t := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ x : ℝ, x = Real.log N := ⟨_, rfl⟩
  rw [← hLdef] at hL100 hk hm hjhi
  rw [← hjdef] at hm hjhi hroute
  obtain ⟨ℓ, hℓdef⟩ : ∃ x : ℝ, x = Real.log L := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ x : ℝ, x = L ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hAdef] at hk
  -- ## Base positivity
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hL1 : (1 : ℝ) < L := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith
  have hℓ100 : (100 : ℝ) ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hL100
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hN1R : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN0R : (0 : ℝ) < (N : ℝ) := by linarith
  have hj0 : (0 : ℝ) < j := by rw [hjdef]; exact Real.log_pos hN1R
  have hN1 : 1 ≤ N := by omega
  -- ## A bounds
  have hAexp : A = Real.exp (ℓ * (1 / 4)) := by
    rw [hAdef, Real.rpow_def_of_pos hL0, hℓdef]
  have hA25 : Real.exp 25 ≤ A := by
    rw [hAexp]
    exact Real.exp_le_exp.mpr (by linarith)
  have hA26 : (26 : ℝ) ≤ A := by
    have : (26 : ℝ) ≤ Real.exp 25 := by linarith [Real.add_one_le_exp (25 : ℝ)]
    linarith
  have hA0 : (0 : ℝ) < A := by linarith
  -- ## k = ⌈A⌉ and its bounds
  have hkA : k = ⌈A⌉₊ := by
    rw [hk, max_eq_right]
    have h1 : (19 : ℝ) ≤ (⌈A⌉₊ : ℝ) := le_trans (by linarith) (Nat.le_ceil A)
    exact_mod_cast h1
  have hkR_lo : A ≤ (k : ℝ) := by rw [hkA]; exact Nat.le_ceil A
  have hkR_ub : (k : ℝ) ≤ 11 / 10 * A := by
    rw [hkA]
    have h1 : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0.le
    linarith [hA26]
  have hk19 : 19 ≤ k := by rw [hk]; exact le_max_left _ _
  have hk0R : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hA0 hkR_lo
  have hl20 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  -- ## log k ≤ (28/100)·ℓ
  have hlogA : Real.log A = ℓ / 4 := by
    rw [hAdef, Real.log_rpow hL0, ← hℓdef]; ring
  have hlnk_ub : Real.log k ≤ 28 / 100 * ℓ := by
    have h1 : Real.log k ≤ Real.log (11 / 10 * A) := Real.log_le_log hk0R hkR_ub
    rw [Real.log_mul (by norm_num) (ne_of_gt hA0), hlogA] at h1
    have h2 : Real.log (11 / 10) ≤ 1 / 10 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 10 by norm_num)]
    linarith [hℓ100]
  have hlnk0 : (0 : ℝ) ≤ Real.log k := by
    apply Real.log_nonneg; exact_mod_cast (show 1 ≤ k by omega)
  -- ## r ≤ (6/10)·k·ℓ
  have hlog4k2 : Real.log (4 * (k : ℝ) ^ 2) ≤ 2 + 56 / 100 * ℓ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [hl21]
    push_cast; linarith [hlnk_ub]
  have hr_ub : (r : ℝ) ≤ 6 / 10 * (k : ℝ) * ℓ := by
    rw [hr]
    have h0 : (0 : ℝ) ≤ (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) := by
      apply mul_nonneg hk0R.le
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
      nlinarith
    have h1 : (⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊ : ℝ)
        < (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) + 1 := Nat.ceil_lt_add_one h0
    have h2 : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (k : ℝ) * (2 + 56 / 100 * ℓ) :=
      mul_le_mul_of_nonneg_left hlog4k2 hk0R.le
    have h3 : (k : ℝ) * 100 ≤ (k : ℝ) * ℓ := mul_le_mul_of_nonneg_left hℓ100 hk0R.le
    nlinarith [h1, h2, h3, hk0R]
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_ceil_iff]
    apply mul_pos hk0R
    apply Real.log_pos
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
    nlinarith
  have hr0R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  -- ## Θ in A/ℓ form and the j floor
  have hA3eq : L ^ ((3 : ℝ) / 4) = A ^ 3 := by
    rw [hAdef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hL0.le]
    norm_num
  have hΘval : vkTheta t = 1 / 1000 / (A ^ 3 * ℓ ^ 2) := by
    rw [vkTheta, ← hLdef, ← hℓdef, hA3eq]
  have hD0 : (0 : ℝ) < A ^ 3 * ℓ ^ 2 := by positivity
  have hjlo : 693 * (A ^ 3 * ℓ ^ 2) ≤ j := by
    have h1 := hroute
    rw [hΘval] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hD0] at h1
    nlinarith [Real.log_two_gt_d9, hD0.le, h1]
  -- ## The m band
  have hLj10 : (10 : ℝ) < L / j := by rw [lt_div_iff₀ hj0]; linarith
  have hm11 : 11 ≤ m := by
    have h1 : 10 < m := by
      rw [hm]
      exact_mod_cast Nat.lt_ceil.mpr (by exact_mod_cast hLj10)
    omega
  have hLj0 : (0 : ℝ) ≤ L / j := by positivity
  have hm_ub : (m : ℝ) < L / j + 1 := by
    rw [hm]; exact Nat.ceil_lt_add_one hLj0
  have hL_A4 : L = A ^ 4 := by
    rw [hAdef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hL0.le]
    norm_num
  have hℓ2ge : (10000 : ℝ) ≤ ℓ ^ 2 := by nlinarith [hℓ100]
  have hA2ge : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have hLj_ub : L / j ≤ A / 693 := by
    have hstep : L * 693 ≤ A * j := by
      have h1 : A * (693 * (A ^ 3 * ℓ ^ 2)) ≤ A * j := mul_le_mul_of_nonneg_left hjlo hA0.le
      have h2 : A * (693 * (A ^ 3 * ℓ ^ 2)) = 693 * L * ℓ ^ 2 := by rw [hL_A4]; ring
      rw [h2] at h1
      nlinarith [h1, hℓ2ge, hL0.le]
    rw [div_le_div_iff₀ hj0 (by norm_num)]
    linarith [hstep]
  have hmA : (m : ℝ) ≤ A / 693 + 1 := le_trans hm_ub.le (by linarith [hLj_ub])
  have hmk : m + 8 ≤ k := by
    have h1 : (m : ℝ) + 8 ≤ (k : ℝ) := by nlinarith [hmA, hA26, hkR_lo]
    exact_mod_cast h1
  -- ## The scale window N^{m−1} < t ≤ N^m
  have hNexp : ∀ n : ℕ, (N : ℝ) ^ n = Real.exp ((n : ℝ) * j) := by
    intro n
    rw [Real.exp_nat_mul, hjdef, Real.exp_log hN0R]
  have htexp : t = Real.exp L := by rw [hLdef, Real.exp_log ht0]
  have hthi : t ≤ (N : ℝ) ^ m := by
    have h1 : L / j ≤ (m : ℝ) := by rw [hm]; exact Nat.le_ceil _
    have h2 : L ≤ (m : ℝ) * j := by rw [div_le_iff₀ hj0] at h1; linarith
    rw [htexp, hNexp m]
    exact Real.exp_le_exp.mpr h2
  have htlo : (N : ℝ) ^ (m - 1) < t := by
    have h1 : (m : ℝ) - 1 < L / j := by linarith [hm_ub]
    have h2 : ((m : ℝ) - 1) * j < L := by rw [lt_div_iff₀ hj0] at h1; linarith
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [htexp, hNexp (m - 1), hcast]
    exact Real.exp_lt_exp.mpr h2
  -- ## `P`, `Y`, `ρ`
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ, Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊ := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 1 / (16 * (k : ℝ) * r) := ⟨_, rfl⟩
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hβ0 : (0 : ℝ) ≤ 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one hk1R]
    have : (m : ℝ) + 2 ≤ (k : ℝ) := by
      have : (m : ℝ) + 8 ≤ (k : ℝ) := by exact_mod_cast hmk
      linarith
    linarith
  -- ## The `hD` P-floor:  8·lnD ≤ (1−β)·j
  have hlnD_ub : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ 52 * A ^ 3 * ℓ ^ 2 :=
    vk_lnD_budget' hkR_lo hkR_ub hr_ub hlnk_ub hlnk0 hr0R hk0R hl21 hA26 hℓ100 hA0 hℓ0
  have hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N := by
    rw [← hjdef]
    have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 654 / 1000 := by
      rw [div_le_iff₀ hk1R]
      nlinarith [hmA, hkR_lo, hA26]
    have hβj : (346 / 1000) * j ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * j := by
      apply mul_le_mul_of_nonneg_right _ hj0.le
      linarith [hle]
    have hfloor : 52 * A ^ 3 * ℓ ^ 2 ≤ (346 / 1000) * j := by
      have h : (346 / 1000) * (693 * (A ^ 3 * ℓ ^ 2)) ≤ (346 / 1000) * j :=
        mul_le_mul_of_nonneg_left hjlo (by norm_num)
      nlinarith [h, hD0.le]
    linarith only [hlnD_ub, hfloor, hβj]
  -- ## The `j`-floor
  have hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N := by
    rw [← hjdef]
    have hkℓ : 2 * ((k : ℝ) + 1) + 4 * (28 / 100) * ℓ + 8 ≤ (346 / 1000) * j := by
      have hbig : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := vk_Aℓ_cube' hA26 hℓ100 hA0 hℓ0
      have hjge : 693 * (A * ℓ) ≤ j := le_trans (by nlinarith [hbig, hD0.le]) hjlo
      nlinarith [hjge, hkR_ub, hA0, hℓ100, hA26]
    have h1 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ 2 * ((k : ℝ) + 1) := by nlinarith [hl21, hk0R]
    have h2 : 4 * Real.log k ≤ 4 * (28 / 100) * ℓ := by linarith [hlnk_ub]
    have hj346 : (346 / 1000) * j ≤ j := by nlinarith [hj0]
    linarith only [h1, h2, hkℓ, hj346]
  -- ## Fold `P^{−ρ}` into `exp(−Θ·j)`
  have hlPlo : (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N ≤ Real.log P :=
    vk_logP_ge hN1 hPdef
  have hlogN0 : (0 : ℝ) ≤ Real.log N := by rw [← hjdef]; exact hj0.le
  have hlP_half : j / 2 ≤ Real.log P := by
    have hβle : (1 : ℝ) / 2 ≤ 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := by
      have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hk1R]; nlinarith [hmA, hkR_lo, hA26]
      linarith [hle]
    have hstep : (1 : ℝ) / 2 * Real.log N ≤ Real.log P :=
      le_trans (mul_le_mul_of_nonneg_right hβle hlogN0) hlPlo
    rw [hjdef]; linarith only [hstep]
  have hρpos : (0 : ℝ) < ρ := by rw [hρdef]; positivity
  have hr_ub2 : (16 * (k : ℝ) * r) ≤ 16 * (11 / 10 * A) * (6 / 10 * (11 / 10 * A) * ℓ) := by
    apply mul_le_mul (by nlinarith [hkR_ub, hA0]) _ hr0R.le (by positivity)
    apply le_trans hr_ub; nlinarith [hkR_ub, hℓ100]
  have h16kr : (0 : ℝ) < 16 * (k : ℝ) * r := mul_pos (mul_pos (by norm_num) hk0R) hr0R
  have hρlo : 1 / (12 * A ^ 2 * ℓ) ≤ ρ := by
    rw [hρdef, div_le_div_iff₀ (by positivity) h16kr]
    nlinarith [hr_ub2, hA0, hℓ0]
  have hΘlogN : vkTheta t * j ≤ ρ * Real.log P := by
    rw [hΘval]
    exact vk_theta_saving' hA26 hℓ100 hj0 hρpos hρlo hlP_half
  have hfold : (P : ℝ) ^ (-ρ) ≤ Real.exp (-(vkTheta t * Real.log N)) := by
    have hPpos : (0 : ℝ) < (P : ℝ) := by
      rw [hPdef]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one
        (by rw [Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hN0R _)
    have hPρ : (P : ℝ) ^ (-ρ) = Real.exp (-(ρ * Real.log P)) := by
      rw [Real.rpow_def_of_pos hPpos]; congr 1; ring
    rw [hPρ, ← hjdef]
    exact Real.exp_le_exp.mpr (by linarith [hΘlogN])
  exact ⟨P, Y, ρ, hk19, hm11, hmk, hN1, hPdef, hYdef, hρdef, htlo, hthi, hDf, hjf, hfold⟩

/-- **WALL 1 end-to-end (mid branch), twisted.**  Twin of `Mid.vk_window_mid`: at the
`k(t)`-schedule and in the mid routing band, the *twisted* dyadic ζ-phase window at `N` saves
the full `exp(−vkTheta t · log N)` factor. -/
theorem vk_window_mid_twist {t β : ℝ} {N k r m : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t) (hN2 : 2 ≤ N)
    (hk : k = max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hm : m = ⌈Real.log t / Real.log N⌉₊)
    (hroute : Real.log 2 ≤ vkTheta t * Real.log N)
    (hjhi : 10 * Real.log N < Real.log t) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n + β * (n : ℝ))‖
      ≤ 10 * (N : ℝ) * Real.exp (-(vkTheta t * Real.log N)) := by
  obtain ⟨P, Y, ρ, hk19, hm11, hmk, hN1, hPdef, hYdef, hρdef, htlo, hthi, hDf, hjf, hfold⟩ :=
    vk_mid_schedule ht0 hL100 hN2 hk hr hm hroute hjhi
  refine le_trans (vk_window_scale_twist (β := β) hk19 hr hρdef hm11 hmk hN1 hPdef hYdef
    htlo hthi hDf hjf) ?_
  exact mul_le_mul_of_nonneg_left hfold (by positivity)

/-- **Mid-branch prefix window, twisted.**  Twin of `GrowthPow.vk_window_mid_prefix`: the same
schedule and routing predicates, concluding the *prefix* bound for every `N < y ≤ 2N`.  This
is the shape `zeta_weighted_block`'s Abel fold consumes. -/
theorem vk_window_mid_prefix_twist {t β : ℝ} {N k r m : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t) (hN2 : 2 ≤ N)
    (hk : k = max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hm : m = ⌈Real.log t / Real.log N⌉₊)
    (hroute : Real.log 2 ≤ vkTheta t * Real.log N)
    (hjhi : 10 * Real.log N < Real.log t)
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n + β * (n : ℝ))‖
      ≤ 10 * (N : ℝ) * Real.exp (-(vkTheta t * Real.log N)) := by
  obtain ⟨P, Y, ρ, hk19, hm11, hmk, hN1, hPdef, hYdef, hρdef, htlo, hthi, hDf, hjf, hfold⟩ :=
    vk_mid_schedule ht0 hL100 hN2 hk hr hm hroute hjhi
  refine le_trans (vk_window_scale_prefix_twist (β := β) hk19 hr hρdef hm11 hmk hN1 hPdef hYdef
    htlo hthi hDf hjf y hy1 hy2) ?_
  exact mul_le_mul_of_nonneg_left hfold (by positivity)

/-! ## Section 5 — the exit: the twisted per-block Dirichlet bound

The twist crosses from the phase side to the Dirichlet side through one Abel fold: the
weight `n^{−σ}` is real and antitone, so `ExpSum.abel_antitone_prefix` applies verbatim and
the twisted phase-prefix bound becomes a bound on `∑ e(βn)·n^{−s}`. -/

/-- **The weighted block bound, twisted.**  Twin of `ExpSum.zeta_weighted_block`: a uniform
prefix bound `B` on the *twisted* phase sums over `(M, x]` gives
`‖∑_{M<n≤x} e(βn)·n^{−s}‖ ≤ M^{−σ}·B`.  The weight `n^{−σ}` is the untwisted one — the twist
is unimodular and rides inside the phase. -/
lemma vk_weighted_block_twist (σ t β : ℝ) (hσ : 0 < σ) (M x : ℕ) (hM1 : 1 ≤ M) (hMx : M < x)
    (B : ℝ) (hB : 0 ≤ B)
    (hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x : ℤ) →
      ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n + β * (n : ℝ))‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc M x, eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (M : ℝ) ^ (-σ) * B := by
  have hσle : -σ ≤ 0 := by linarith
  -- ℤ → ℕ reindex for the twisted phase prefix sums
  have hreindex : ∀ k : ℕ, ∑ n ∈ Finset.Ioc (M : ℤ) (k : ℤ), eR (phi t n + β * (n : ℝ))
      = ∑ n ∈ Finset.Ioc M k, eR (phi t (n : ℤ) + β * ((n : ℤ) : ℝ)) := by
    intro k
    apply Finset.sum_nbij' (i := fun n : ℤ => n.toNat) (j := fun m : ℕ => (m : ℤ))
    · intro n hn; rw [Finset.mem_Ioc] at hn ⊢; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm ⊢; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn; rw [show ((n.toNat : ℤ)) = n from by omega]
  -- split the twisted summand:  e(βn)·n^{−s} = n^{−σ}·e(φ(n) + βn)
  have hcong : ∑ n ∈ Finset.Ioc M x,
        eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = ∑ n ∈ Finset.Ioc M x,
        (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * eR (phi t (n : ℤ) + β * ((n : ℤ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn; rw [Finset.mem_Ioc] at hn
    have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
    rw [cpow_weight_split σ t (by omega : 1 ≤ n), eR_add, hcast]
    ring
  rw [hcong]
  -- Abel weighting (the weight is untouched by the twist)
  have habel := abel_antitone_prefix M x hMx (fun n => (n : ℝ) ^ (-σ))
    (fun n => eR (phi t (n : ℤ) + β * ((n : ℤ) : ℝ))) B hB
    (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (fun n hn _ => by
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast Nat.le_succ n) hσle)
    (fun k hk hkx => by
      show ‖∑ n ∈ Finset.Ioc M k, eR (phi t (n : ℤ) + β * ((n : ℤ) : ℝ))‖ ≤ B
      rw [← hreindex k]
      exact hpref (k : ℤ) (by exact_mod_cast hk) (by exact_mod_cast hkx))
  refine le_trans habel ?_
  have hstep : ((M + 1 : ℕ) : ℝ) ^ (-σ) ≤ (M : ℝ) ^ (-σ) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    exact Real.rpow_le_rpow_of_nonpos hM0 (by push_cast; linarith) hσle
  exact mul_le_mul_of_nonneg_right hstep hB

set_option maxHeartbeats 1000000 in
-- The two-way routing threads staged rpow/exp/log facts through `nlinarith` (as in
-- `vk_dirichlet_block_le`, minus its third branch).
/-- **THE EXIT — the twisted per-block Dirichlet bound.  VT-4 consumes exactly this.**

On the sub-unit strip `σ ≥ 1 − vkTheta t`, above the schedule floor `log t ≥ e^100`, every
dyadic block `(M, x']` (`1 ≤ M`, `M < x' ≤ 2M`) **below the high boundary**
(`10·log M < log t`) obeys, for **every** twist `β : ℝ`,

  `‖∑_{M<n≤x'} e(βn)·n^{−(σ+it)}‖ ≤ 10`.

Same grades as the untwisted `vk_dirichlet_block_le` — same `M`, `x'`, `σ`, `t` binders, same
weights, the twist living only in the `eR` phase — with the **sharper** constant `10` (the
untwisted `1348` is the high branch's; that branch is excluded here, see
`vk_dirichlet_block_twist_le_of_high` and the module docstring).

Routing, exactly as untwisted: `Θ·log M < log 2` is trivial (the twist is unimodular, so the
`n^{−σ}` majorant is unchanged); `log 2 ≤ Θ·log M` runs the twisted mid window
`vk_window_mid_prefix_twist` through the twisted Abel fold `vk_weighted_block_twist`. -/
theorem vk_dirichlet_block_twist_le {σ t β : ℝ} {M x' : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσlo : 1 - vkTheta t ≤ σ)
    (hM1 : 1 ≤ M) (hMx' : M < x') (hx'2 : x' ≤ 2 * M)
    (hjhiM : 10 * Real.log M < Real.log t) :
    ‖∑ n ∈ Finset.Ioc M x',
        eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 10 := by
  have hlogtpos : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hlogt1 : 1 < Real.log t := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith [hL100]
  have hΘpos : 0 < vkTheta t := vkTheta_pos hlogt1
  -- Θ ≤ 1/2^14 (so in particular Θ < 1, giving σ > 0)
  have hΘ14 : vkTheta t ≤ 1 / (2 : ℝ) ^ 14 := by
    rw [vkTheta]
    have h1 : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have h2 : (100 : ℝ) ≤ Real.log (Real.log t) := by
      rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hL100
    have h3 : (10000 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := by nlinarith [h2]
    have hDpos : 0 < (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) := by
      positivity
    rw [div_le_iff₀ hDpos]
    nlinarith [h1, h3, mul_le_mul h1 h3 (by norm_num) (by positivity)]
  have hσpos : 0 < σ := by
    have : (1 : ℝ) / (2 : ℝ) ^ 14 < 1 := by norm_num
    linarith [hσlo, hΘ14]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hlogM0 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1R
  have hx'2Z : (x' : ℤ) ≤ 2 * (M : ℤ) := by exact_mod_cast hx'2
  rcases le_or_gt (Real.log 2) (vkTheta t * Real.log M) with hmid | hlow
  · -- MID: the twisted dyadic window through the twisted Abel fold
    have hM2 : 2 ≤ M := by
      rcases Nat.lt_or_ge M 2 with h | h
      · exfalso
        have hM1' : M = 1 := by omega
        rw [hM1', Nat.cast_one, Real.log_one, mul_zero] at hmid
        linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
      · exact h
    set k : ℕ := max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊ with hkdef
    set r : ℕ := ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊ with hrdef
    set m : ℕ := ⌈Real.log t / Real.log M⌉₊ with hmdef
    have hBnn : (0 : ℝ) ≤ 10 * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M)) := by positivity
    have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
        ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n + β * (n : ℝ))‖
          ≤ 10 * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M)) := by
      intro y hy1 hy2
      exact vk_window_mid_prefix_twist ht0 hL100 hM2 hkdef hrdef hmdef hmid hjhiM y hy1
        (le_trans hy2 hx'2Z)
    refine le_trans (vk_weighted_block_twist σ t β hσpos M x' hM1 hMx' _ hBnn hpref) ?_
    -- M^{−σ}·(10 M exp(−Θ logM)) = 10·exp((1−σ−Θ)·logM) ≤ 10
    have hcollapse : (M : ℝ) ^ (-σ) * (M : ℝ) = Real.exp ((1 - σ) * Real.log M) := by
      rw [← Real.rpow_add_one (ne_of_gt hMpos) (-σ), Real.rpow_def_of_pos hMpos]
      congr 1; ring
    have hexpprod : Real.exp ((1 - σ) * Real.log M) * Real.exp (-(vkTheta t * Real.log M))
        = Real.exp ((1 - σ - vkTheta t) * Real.log M) := by
      rw [← Real.exp_add]; congr 1; ring
    have harg : (1 - σ - vkTheta t) * Real.log M ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hlogM0
      linarith [hσlo]
    calc (M : ℝ) ^ (-σ) * (10 * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M)))
        = 10 * ((M : ℝ) ^ (-σ) * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M))) := by ring
      _ = 10 * Real.exp ((1 - σ - vkTheta t) * Real.log M) := by rw [hcollapse, hexpprod]
      _ ≤ 10 * Real.exp 0 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.exp_le_exp.mpr harg
      _ = 10 := by rw [Real.exp_zero]; ring
  · -- LOW: trivial — the twist is unimodular, so the majorant is the untwisted one
    have hnorm : ‖∑ n ∈ Finset.Ioc M x',
          eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ) := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : 0 < n := by omega
      rw [norm_mul, norm_eR, one_mul, Complex.norm_natCast_cpow_of_pos hn0]
      apply le_of_eq
      congr 1
      simp [Complex.add_re, Complex.mul_re]
    have hsum : ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ) ≤ (M : ℝ) ^ (1 - σ) := by
      have hbound : ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ)
          ≤ ∑ _n ∈ Finset.Ioc M x', (M : ℝ) ^ (-σ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Ioc] at hn
        exact Real.rpow_le_rpow_of_nonpos hMpos (by exact_mod_cast (by omega : M ≤ n))
          (by linarith)
      rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul] at hbound
      have hcard : ((x' - M : ℕ) : ℝ) ≤ (M : ℝ) := by
        have : x' - M ≤ M := by omega
        exact_mod_cast this
      have hMσnn : (0 : ℝ) ≤ (M : ℝ) ^ (-σ) := Real.rpow_nonneg hMpos.le _
      refine le_trans hbound ?_
      calc ((x' - M : ℕ) : ℝ) * (M : ℝ) ^ (-σ) ≤ (M : ℝ) * (M : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right hcard hMσnn
        _ = (M : ℝ) ^ (1 - σ) := by
            rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hMpos) (-σ)]
            congr 1; ring
    have hlt2 : (M : ℝ) ^ (1 - σ) < 2 := by
      have hle : (M : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (vkTheta t) :=
        Real.rpow_le_rpow_of_exponent_le hM1R (by linarith [hσlo])
      have heq : (M : ℝ) ^ (vkTheta t) = Real.exp (vkTheta t * Real.log M) := by
        rw [Real.rpow_def_of_pos hMpos, mul_comm]
      rw [heq] at hle
      have : Real.exp (vkTheta t * Real.log M) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlow
      rw [Real.exp_log (by norm_num)] at this
      linarith [hle]
    calc ‖∑ n ∈ Finset.Ioc M x',
          eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ) := hnorm
      _ ≤ (M : ℝ) ^ (1 - σ) := hsum
      _ ≤ 10 := by linarith [hlt2]

/-- **The total twisted per-block interface (socket form).**  Byte-identical to
`GrowthPow.vk_dirichlet_block_le` — same hypotheses, same `1348` — with the one branch the
twist cannot cross taken as an explicit binder.

The residual `hhigh` is exactly the twisted `ExpSum.zeta_block_dispatch` on `log t ≤ 10·log M`.
Its first sub-case is Kusmin's **first**-derivative test, and VT-1's affine blindness starts
at order 2: `dk 1 (φ + β·id) = dk 1 φ + β`.  Discharging it needs a Diophantine hypothesis on
`β` (for `β = a/q`, the classical `√q`), which is VT-4's business, not the ladder's. -/
theorem vk_dirichlet_block_twist_le_of_high {σ t β : ℝ} {M x' : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσlo : 1 - vkTheta t ≤ σ)
    (hM1 : 1 ≤ M) (hMx' : M < x') (hx'2 : x' ≤ 2 * M)
    (hhigh : Real.log t ≤ 10 * Real.log M →
      ‖∑ n ∈ Finset.Ioc M x',
          eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348) :
    ‖∑ n ∈ Finset.Ioc M x',
        eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 := by
  rcases le_or_gt (Real.log t) (10 * Real.log M) with hhi | hlo
  · exact hhigh hhi
  · exact le_trans (vk_dirichlet_block_twist_le ht0 hL100 hσlo hM1 hMx' hx'2 hlo) (by norm_num)

end Salt.Vk
