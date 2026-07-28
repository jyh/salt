/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ChiLLower
import Salt.MR.CapFreeArm3

/-!
# VK-TWIST, the consumer side — the height-extended 3-4-1 and the close into the floor

`ChiLLower.chi_Llower_341` is the sharp `L`-lower bound at the bridge point
`1 + 1/log X − it` for a non-real `χ`, and it is gated `|t| ≤ 1`.  The gate is not the
3-4-1 device: it is the ONE growth input the device needs at the doubled frequency, namely
an upper bound for `‖L(1 + 1/log X − 2it, χ²)‖`.  The corpus supplies that input through
`ChiLLower.LFunction_norm_le_level`, whose Pólya–Vinogradov shape is LINEAR in `‖s‖`, hence
linear in `|t|` — useless past a bounded band.

The VK-TWIST campaign's VT-4 will replace exactly that input by the twisted
Vinogradov–Korobov bound (the χ-analogue of `OneLinePowGrowth.one_line_pow_growth`)

  `‖L((1 + 1/log X) − it, χ)‖ ≤ C·√q·(log|t|)^{3/4}·(loglog|t|)⁴`,  `|t| ≥ exp(exp 100)`.

**This file is the CONSUMER SIDE, built against that bound as a HYPOTHESIS.**  Every
statement below carries the pinned bound as a binder (`VkTwistUB`, §1), so the kernel checks
the whole chain TODAY and VT-4 plugs into the socket later — the pattern of
`ChiFloorLow.chi_floor_low_of_Llower`.

## The three frequency branches, and how they cover `ℝ`

| branch | range | growth input | debit's `loglog X` weight |
|---|---|---|---|
| mid | `\|t\| ≤ T₀` | `LFunction_norm_le_level` (linear; CONSTANT on a bounded window) | `3/4` |
| VK | `exp(exp 100) ≤ \|t\|` | `VkTwistUB` (the VT-4 socket) | `3/4 + 3/16 = 15/16` |

At `T₀ := exp(exp 100)` the two ranges COVER `ℝ`, with no gap: `chi_Llower_341_height`
generalises `chi_Llower_341` from the landed `T₀ = 1` (where its `15 = 3·(3 + 2·1)` is
recovered on the nose) to any height cap, and the window being BOUNDED is the entire reason
the linear input still gives an `X`-independent constant there.

## Contents

* §1 — `vkProfile`, `VkTwistUB`: the pinned VK-TWIST growth profile and its socket;
  `log_vkProfile`, the exact log-expansion under the honest height gate.
* §2 — `chi_Llower_341_of_ub` (VT-5 CORE): the 3-4-1 lower bound with its ONE height-sensitive
  input abstracted to a slot `U`, debit `2log4 + (3/4)log(1+log X) + (1/4)log U`.
* §3 — the two suppliers of `U`: `chi_Llower_341_height` (mid branch, `|t| ≤ T₀`, from
  `LFunction_norm_le_level`, `U = 3(3+2T₀)q²(1+log q)`) and `chi_Llower_341_vk` (VK branch,
  from the socket, `U = vkProfile C q (2t)`).
* §4 — the imprimitivity adapter: `norm_LFunction_le_vkEulerCorr` (the `LFunction_changeLevel`
  Euler-factor correction, priced by `vkEulerCorr q = ∏_{p|q}(1 + 1/p)` rather than the
  corpus's crude `q`), `vkTwistUB_of_primitive`, and `vkDebitConst_vkEulerCorr` — which says
  the whole imprimitivity cost is `(1/4)·log(vkEulerCorr q)`, i.e. `O(loglog q)`.
* §5 — VT-6, the close: `chi_floor_vk_pointwise`, the constant-expanded floor

    `𝔻²(λχ̄, n^{iv}; X) ≥ (1/16)loglog X − logloglog X − (1/8)log q − D_C − D_q − K`,

  and the margin lemmas `vk_capfree_threshold` / `capFreeFloor_lamChi_vk` /
  `capFreeFloor3_lamChi_vk` landing `CapFreeArm.CapFreeFloor` (and the `3X` box's
  `CapFreeArm3.CapFreeFloor3`) at an explicit symbolic threshold on `loglog X`.

## THE CONSTANT EXPANSION (the number VT-6 exists to produce)

The debit `(1/4)·log(vkProfile C q (2t))` expands EXACTLY as

  `(1/4)log C + (1/8)log q + (3/16)·loglog|2t| + logloglog|2t|`

(the `(loglog)⁴` costs `(1/4)·4 = 1` copy of `logloglog`, not four).  On the contour box
`|t| ≤ 3X` the two height terms are `≤ (3/16)loglog X` and `≤ logloglog X` up to `log 2`'s,
and `(3/4)log(1 + log X) ≤ (3/4)loglog X + (3/4)log 2`.  So against `chi_dist_bridge`'s
coefficient-`1` `loglog X` the surviving weight is

  `1 − 3/4 − 3/16 = 1/16`,

DOUBLE the `CapFreeFloor` demand `1/32`, with `logloglog X + (1/8)log q` and the named
constants `vkDebitConst C`, `vkMidDebit q`, `K` to be cleared by the threshold.

## Traps observed

* **The three log-scales.**  Every threshold here speaks `loglog X` (the pretentious scale).
  Nothing in this file speaks `loglog H`; a W-gate consumer must re-pin the scale.
* **The shifted variable.**  Floors are stated in the BARE frequency `v`.  The seam station
  minimises the `t₀`-shifted datum; `HalaszHead.seamCoeff_trivial_dist_eq` is the adapter,
  and it is NOT applied here.
* **Strict vs non-strict.**  `CapFreeFloor` demands a STRICT `<`; the threshold hypotheses
  below are strict for exactly that reason.
* **The `T₀`-corner.**  `(log|t|)^{3/4}` is only sane past the socket's own floor; the VK
  branch therefore never fires below `exp(exp 100)`, and the mid branch — whose input is
  `X`-independent precisely because the window is bounded — covers everything below.
-/

namespace Salt.MR

open Complex DirichletCharacter Salt.SW
open scoped BigOperators

/-! ## §1 — the pinned VK-TWIST profile and its socket -/

/-- **The pinned VK-TWIST growth profile.**  `C·√q·(log|t|)^{3/4}·(loglog|t|)⁴` — the χ-twist
of `OneLinePowGrowth.one_line_pow_growth`'s ζ-profile, with the `√q` the Gauss-completion
step contributes. -/
noncomputable def vkProfile (C : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  C * Real.sqrt q * (Real.log |t|) ^ ((3 : ℝ) / 4) * (Real.log (Real.log |t|)) ^ (4 : ℕ)

/-- **THE VT-4 SOCKET.**  The pinned bound at the bridge point `1 + 1/log X − it`, stated as
a `Prop` so every consumer below takes it as one binder.  Its honest range is
`exp(exp 100) ≤ |t|`; the range does not appear here because the range lives in the
SUPPLIER — a consumer that never asserts the socket outside the range is what §5 arranges. -/
def VkTwistUB (C : ℝ) {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (X t : ℝ) : Prop :=
  ‖DirichletCharacter.LFunction ψ
      (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ ≤ vkProfile C q t

/-- The two standing height facts past the socket's floor: `log|t| ≥ exp 100` and
`loglog|t| ≥ 100`.  This is what keeps every logarithm below away from its corner. -/
lemma vk_height_facts {t : ℝ} (ht : Real.exp (Real.exp 100) ≤ |t|) :
    Real.exp 100 ≤ Real.log |t| ∧ (100 : ℝ) ≤ Real.log (Real.log |t|) := by
  have h0 : (0 : ℝ) < |t| := lt_of_lt_of_le (Real.exp_pos _) ht
  have h1 : Real.exp 100 ≤ Real.log |t| := (Real.le_log_iff_exp_le h0).mpr ht
  have h2 : (0 : ℝ) < Real.log |t| := lt_of_lt_of_le (Real.exp_pos _) h1
  exact ⟨h1, (Real.le_log_iff_exp_le h2).mpr h1⟩

/-- **The exact log-expansion of the profile.**  Past the socket's height floor,

  `log(vkProfile C q t) = log C + (1/2)log q + (3/4)·loglog|t| + 4·logloglog|t|`.

Every term is a genuine equality — this is the arithmetic §5's leading coefficient reads
off, so no inequality is allowed to hide here. -/
lemma log_vkProfile {C : ℝ} (hC : 0 < C) {q : ℕ} [NeZero q] {t : ℝ}
    (ht : Real.exp (Real.exp 100) ≤ |t|) :
    Real.log (vkProfile C q t)
      = Real.log C + Real.log q / 2 + (3 / 4) * Real.log (Real.log |t|)
          + 4 * Real.log (Real.log (Real.log |t|)) := by
  obtain ⟨h1, h2⟩ := vk_height_facts ht
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsq : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hL : (0 : ℝ) < Real.log |t| := lt_of_lt_of_le (Real.exp_pos _) h1
  have hA : (0 : ℝ) < (Real.log |t|) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL _
  have hLL : (0 : ℝ) < Real.log (Real.log |t|) := by linarith
  have hB : (0 : ℝ) < (Real.log (Real.log |t|)) ^ (4 : ℕ) := pow_pos hLL 4
  unfold vkProfile
  rw [Real.log_mul (by positivity) (ne_of_gt hB), Real.log_mul (by positivity) (ne_of_gt hA),
    Real.log_mul (ne_of_gt hC) (ne_of_gt hsq), Real.log_sqrt (by linarith), Real.log_rpow hL,
    Real.log_pow]
  push_cast
  ring

/-- Standing facts at any point of `Re s > 1` (a local copy of `ChiLLower`'s `private`
`pt_facts`, which is not exported). -/
private lemma vk_pt_facts {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    (s ≠ 1) ∧ DifferentiableAt ℂ (LFunction χ) s ∧ LFunction χ s ≠ 0 := by
  have hne1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl 1 hs
  exact ⟨hne1, differentiableAt_LFunction χ _ (Or.inl hne1),
    χ.LFunction_ne_zero_of_one_le_re (Or.inr hne1) hs.le⟩

/-! ## §2 — VT-5 CORE: the 3-4-1 against ANY χ²-at-`2t` upper bound -/

/-- **VT-5 CORE — the 3-4-1 `L`-lower bound with its growth input as a SOCKET.**  For `X ≥ e`
and EVERY real `t`, ANY upper bound `U` for the χ²-factor at the DOUBLED frequency yields

  `−[2log4 + (3/4)log(1+log X) + (1/4)log U] ≤ log‖L(1 + 1/log X − it, χ)‖`.

This is `ChiLLower.chi_Llower_341` with its single `|t| ≤ 1`-gated step abstracted: the
`3 log‖L(v,χ₀)‖` leg still pays `(3/4)log(1 + log X)` (the ζ pole, unavoidable on the
horizontal route), the three `Re = 2` anchors still pay `8·log 4` over `4`, and everything
that depends on the HEIGHT is now `U`.

**`U` IS THE ONLY IMPROVABLE SLOT IN THE WHOLE CHAIN.**  §3 supplies it from the corpus's
`LFunction_norm_le_level` (linear in `|t|`, so honest only on a bounded window); the VK
branch supplies it from the VT-4 socket.  A future sharper 1-line bound — e.g. the classical
`‖L(1+δ+it,χ)‖ ≪ log(q(|t|+2))` — plugs in here and NOWHERE else. -/
theorem chi_Llower_341_of_ub {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X t U : ℝ)
    (hX : Real.exp 1 ≤ X)
    (hUB : ‖DirichletCharacter.LFunction (χ ^ 2)
        (((1 + 1 / Real.log X : ℝ) : ℂ) - ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤ U) :
    -(2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X) + (1 / 4) * Real.log U)
      ≤ Real.log ‖DirichletCharacter.LFunction χ
          (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  have hu1 : (1 : ℝ) < 1 + 1 / Real.log X := by linarith
  have hu2 : 1 + 1 / Real.log X ≤ 2 := by linarith
  have hlog4 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have h341 := LFunction_341_horiz χ (u := 1 + 1 / Real.log X) (t := -t) hu1 hu2
  have hpt : ((1 + 1 / Real.log X : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I := by push_cast; ring
  rw [hpt] at h341
  have a0 : -Real.log 4 ≤ Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((2 : ℝ) : ℂ)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by norm_num))
  have a1 : -Real.log 4
      ≤ Real.log ‖LFunction χ (((2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by simp))
  have a2 : -Real.log 4
      ≤ Real.log ‖LFunction (χ ^ 2) (((2 : ℝ) : ℂ) + 2 * ((-t : ℝ) : ℂ) * I)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by simp))
  have hb0 : Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((1 + 1 / Real.log X : ℝ) : ℂ)‖
      ≤ Real.log (1 + Real.log X) := by
    have hpos : (0 : ℝ) < ‖LFunction (1 : DirichletCharacter ℂ q)
        (((1 + 1 / Real.log X : ℝ) : ℂ))‖ := by
      rw [norm_pos_iff]
      exact (vk_pt_facts (1 : DirichletCharacter ℂ q)
        (s := (((1 + 1 / Real.log X : ℝ) : ℂ))) (by simpa using hu1)).2.2
    refine Real.log_le_log hpos ?_
    have hbnd := LFunction_one_real_upper (q := q) (u := 1 + 1 / Real.log X) hu1
    have heq : (1 : ℝ) + 1 / ((1 + 1 / Real.log X) - 1) = 1 + Real.log X := by
      rw [show (1 + 1 / Real.log X) - 1 = 1 / Real.log X by ring, one_div_one_div]
    linarith [hbnd, heq.symm.le, heq.le]
  -- THE ONE STEP THE CAMPAIGN CHANGES: the χ²-at-`2t` factor, taken from `U`
  have hs2re : ((((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I).re
      = 1 + 1 / Real.log X := by simp
  have hs2 : (((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) - ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hb2 : Real.log ‖LFunction (χ ^ 2)
        ((((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I)‖ ≤ Real.log U := by
    have hpos : (0 : ℝ) < ‖LFunction (χ ^ 2)
        ((((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I)‖ := by
      rw [norm_pos_iff]
      exact (vk_pt_facts (χ ^ 2) (by rw [hs2re]; linarith)).2.2
    refine Real.log_le_log hpos ?_
    rw [hs2]
    exact hUB
  linarith [h341, a0, a1, a2, hb0, hb2]

/-! ## §3 — the two suppliers of `U`: the MID branch and the VK branch -/

/-- **VT-5 (mid branch) — the 3-4-1 `L`-lower bound on a BOUNDED height window.**
For `X ≥ e`, a height cap `T₀ ≥ 1`, `|t| ≤ T₀` and `χ² ≠ 1`,

  `−[2log4 + (3/4)log(1+log X) + (1/4)log(3(3+2T₀)q²(1+log q))]
      ≤ log‖L(1 + 1/log X − it, χ)‖`.

`ChiLLower.chi_Llower_341` is the case `T₀ = 1`, and its constant `15` is recovered exactly
(`3·(3 + 2·1) = 15`).  The point of the generalisation: `LFunction_norm_le_level`'s
`3(1 + ‖s‖)` is LINEAR in the frequency, so on a BOUNDED window it is still an
`X`-independent constant — and only the `T₀`-dependence of that constant is paid.  This is
the branch that covers everything below the VK socket's height floor.

**⚠ THE PRICE.**  The dependence on `T₀` is `log T₀`, so at the socket's floor
`T₀ = exp(exp 100)` this debit is about `(1/4)·e^100` — an `X`-free constant, but an
astronomical one.  It is the mid window, NOT the VK branch, that sets §5's threshold; see
`chi_Llower_341_of_ub`'s improvable slot. -/
theorem chi_Llower_341_height {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 ≠ 1)
    (X t T₀ : ℝ) (hX : Real.exp 1 ≤ X) (hT₀ : 1 ≤ T₀) (ht : |t| ≤ T₀) :
    -(2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (3 * (3 + 2 * T₀) * (q : ℝ) ^ 2 * (1 + Real.log q)))
      ≤ Real.log ‖DirichletCharacter.LFunction χ
          (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  have hu2 : 1 + 1 / Real.log X ≤ 2 := by linarith
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  refine chi_Llower_341_of_ub χ X t _ hX ?_
  have hs2re : ((((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I).re
      = 1 + 1 / Real.log X := by simp
  have hnorms : ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I‖
      ≤ 2 + 2 * T₀ := by
    have h1 : ‖(((1 + 1 / Real.log X : ℝ) : ℂ))‖ = |1 + 1 / Real.log X| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖((2 * t : ℝ) : ℂ) * Complex.I‖ = 2 * |t| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I‖
        ≤ ‖(((1 + 1 / Real.log X : ℝ) : ℂ))‖ + ‖((2 * t : ℝ) : ℂ) * Complex.I‖ :=
          norm_sub_le _ _
      _ = |1 + 1 / Real.log X| + 2 * |t| := by rw [h1, h2]
      _ ≤ 2 + 2 * T₀ := by
          have habs : |1 + 1 / Real.log X| = 1 + 1 / Real.log X :=
            abs_of_nonneg (by linarith)
          rw [habs]; linarith
  have hbnd := LFunction_norm_le_level (χ ^ 2) hχ2
    (s := (((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I)
    (by rw [hs2re]; linarith) (by rw [hs2re]; linarith)
  refine le_trans hbnd ?_
  have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
    nlinarith [Real.sq_sqrt (le_trans zero_le_one hq1R), Real.sqrt_nonneg ((q : ℝ))]
  have hMnn : (0 : ℝ) ≤ 3 * (3 + 2 * T₀) := by linarith
  have h15 : 3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I‖)
      ≤ 3 * (3 + 2 * T₀) := by linarith [hnorms]
  have ha : 3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I‖)
      * Real.sqrt q ≤ 3 * (3 + 2 * T₀) * (q : ℝ) := by
    calc 3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I‖)
            * Real.sqrt q
        ≤ 3 * (3 + 2 * T₀) * Real.sqrt q :=
          mul_le_mul_of_nonneg_right h15 (Real.sqrt_nonneg _)
      _ ≤ 3 * (3 + 2 * T₀) * (q : ℝ) := mul_le_mul_of_nonneg_left hsq hMnn
  have e1 : 3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) - ((2 * t : ℝ) : ℂ) * Complex.I‖)
        * Real.sqrt q * (1 + Real.log q)
      ≤ 3 * (3 + 2 * T₀) * (q : ℝ) * (1 + Real.log q) :=
    mul_le_mul_of_nonneg_right ha (by linarith)
  calc (q : ℝ) * (3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ))
          - ((2 * t : ℝ) : ℂ) * Complex.I‖) * Real.sqrt q * (1 + Real.log q))
      ≤ (q : ℝ) * (3 * (3 + 2 * T₀) * (q : ℝ) * (1 + Real.log q)) :=
        mul_le_mul_of_nonneg_left e1 (by linarith)
    _ = 3 * (3 + 2 * T₀) * (q : ℝ) ^ 2 * (1 + Real.log q) := by ring

/-- **VT-5 (VK branch) — THE HEIGHT-EXTENDED 3-4-1.**  Given the VT-4 socket at the SQUARE
character and the DOUBLED frequency (`VkTwistUB C (χ²) X (2t)` — the factor `2` on `t` is
why §5 states its height gates in `|2t|`),

  `−[2log4 + (3/4)log(1+log X) + (1/4)log(vkProfile C q (2t))] ≤ log‖L(1 + 1/log X − it, χ)‖`

for every `X ≥ e` and EVERY real `t`.

Note what is NOT a hypothesis: neither `χ² ≠ 1` nor a height floor appears — the honest range
`exp(exp 100) ≤ |t|` lives entirely in the TRUTH of the socket, so a consumer that only ever
asserts `VkTwistUB` inside that range (as §5 does) pays nothing extra here. -/
theorem chi_Llower_341_vk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (C X t : ℝ)
    (hX : Real.exp 1 ≤ X) (hUB : VkTwistUB C (χ ^ 2) X (2 * t)) :
    -(2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (vkProfile C q (2 * t)))
      ≤ Real.log ‖DirichletCharacter.LFunction χ
          (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  unfold VkTwistUB at hUB
  exact chi_Llower_341_of_ub χ X t (vkProfile C q (2 * t)) hX hUB

/-! ## §4 — the imprimitivity adapter

VT-4 delivers the socket for a character; `χ²` need not be primitive, and mathlib's
`LFunction_changeLevel` is the exact bridge.  `ChiLLower.LFunction_norm_le_level` already
walks this road but prices each Euler factor by `‖1 − ψ'(p)p^{−s}‖ ≤ p`, i.e. the whole
correction by `q`.  On the 1-line that is far too crude: `‖p^{−s}‖ ≤ 1/p` there, so the
honest price is `∏_{p|q}(1 + 1/p)` — whose LOGARITHM is `O(loglog q)`. -/

/-- The Euler-factor correction incurred by passing from the primitive character inducing
`ψ` to `ψ` itself, on the closed half-plane `Re s ≥ 1`. -/
noncomputable def vkEulerCorr (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, (1 + 1 / (p : ℝ))

lemma one_le_vkEulerCorr (q : ℕ) : 1 ≤ vkEulerCorr q := by
  unfold vkEulerCorr
  calc (1 : ℝ) = ∏ _p ∈ q.primeFactors, (1 : ℝ) := by simp
    _ ≤ ∏ p ∈ q.primeFactors, (1 + 1 / (p : ℝ)) := by
        refine Finset.prod_le_prod (fun p _ => zero_le_one) (fun p hp => ?_)
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith

lemma vkEulerCorr_pos (q : ℕ) : 0 < vkEulerCorr q :=
  lt_of_lt_of_le zero_lt_one (one_le_vkEulerCorr q)

/-- **The imprimitivity price, honestly.**  For a nonprincipal `ψ mod q` and `Re s ≥ 1`,

  `‖L(s,ψ)‖ ≤ (∏_{p|q}(1 + 1/p))·‖L(s, ψ*)‖`

with `ψ*` the inducing primitive character.  `LFunction_changeLevel` re-attaches the finitely
many Euler factors at `p | q`; on `Re s ≥ 1` each has norm `≤ 1 + p^{−Re s} ≤ 1 + 1/p`. -/
theorem norm_LFunction_le_vkEulerCorr {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖LFunction ψ s‖ ≤ vkEulerCorr q * ‖LFunction ψ.primitiveCharacter s‖ := by
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have hf1 : ψ.conductor ≠ 1 := fun h => hψ (eq_one_iff_conductor_eq_one.mpr h)
  have hpne : ψ.primitiveCharacter ≠ 1 := by
    intro h
    exact hf1 (by rw [← ψ.primitiveCharacter_isPrimitive]; exact eq_one_iff_conductor_eq_one.mp h)
  have hLfac : LFunction ψ s
      = LFunction ψ.primitiveCharacter s
        * ∏ p ∈ q.primeFactors, (1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
    conv_lhs => rw [← ψ.changeLevel_primitiveCharacter]
    exact LFunction_changeLevel ψ.conductor_dvd_level ψ.primitiveCharacter (Or.inl hpne)
  have hprodle : ‖∏ p ∈ q.primeFactors,
      (1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s))‖ ≤ vkEulerCorr q := by
    rw [norm_prod]
    unfold vkEulerCorr
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p hp => ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hcast : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s).re := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have hexp : (p : ℝ) ^ (-s).re ≤ (p : ℝ) ^ (-1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
      rw [Complex.neg_re]; linarith
    have hinv : (p : ℝ) ^ (-1 : ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    have hchi : ‖ψ.primitiveCharacter p‖ ≤ 1 := ψ.primitiveCharacter.norm_le_one _
    calc ‖1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s)‖
        ≤ ‖(1 : ℂ)‖ + ‖ψ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ = 1 + ‖ψ.primitiveCharacter p‖ * ‖(p : ℂ) ^ (-s)‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + 1 / (p : ℝ) := by
          rw [hcast]
          have h1 : ‖ψ.primitiveCharacter p‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re :=
            mul_le_mul_of_nonneg_right hchi (Real.rpow_nonneg hp0.le _)
          rw [one_mul] at h1
          rw [← hinv]
          linarith
  rw [hLfac, norm_mul]
  calc ‖LFunction ψ.primitiveCharacter s‖
        * ‖∏ p ∈ q.primeFactors, (1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s))‖
      ≤ ‖LFunction ψ.primitiveCharacter s‖ * vkEulerCorr q :=
        mul_le_mul_of_nonneg_left hprodle (norm_nonneg _)
    _ = vkEulerCorr q * ‖LFunction ψ.primitiveCharacter s‖ := by ring

/-- `vkProfile` is linear in its constant, so an Euler correction is absorbed by rescaling
`C`. -/
lemma vkProfile_const_mul (a C : ℝ) (q : ℕ) (t : ℝ) :
    vkProfile (a * C) q t = a * vkProfile C q t := by
  unfold vkProfile; ring

/-- **§4 — THE IMPRIMITIVITY SOCKET ADAPTER.**  If VT-4's bound is delivered only for the
PRIMITIVE character inducing `ψ`, the socket at `ψ` itself holds with `C` rescaled by
`vkEulerCorr q`.  Nothing else moves. -/
theorem vkTwistUB_of_primitive {C : ℝ} {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) {X t : ℝ} (hX : Real.exp 1 ≤ X)
    (hprim : ‖LFunction ψ.primitiveCharacter
        (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ ≤ vkProfile C q t) :
    VkTwistUB (vkEulerCorr q * C) ψ X t := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hre0 : ((((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I).re
      = 1 + 1 / Real.log X := by simp
  have hre : (1 : ℝ) ≤ ((((1 + 1 / Real.log X : ℝ) : ℂ)) - (t : ℝ) * Complex.I).re := by
    rw [hre0]; linarith [one_div_pos.mpr hlogXpos]
  have h := norm_LFunction_le_vkEulerCorr ψ hψ hre
  unfold VkTwistUB
  rw [vkProfile_const_mul]
  refine le_trans h ?_
  exact mul_le_mul_of_nonneg_left hprim (vkEulerCorr_pos q).le

/-! ## §5 — VT-6: the close into `CapFreeFloor` -/

/-- The `X`-free part of the VK-branch debit:
`2log4 + (31/16)log2 + (1/4)log C`.  The `(31/16)log2` is the sum of the three `log 2`'s the
three rounding steps `1 + log X ≤ 2log X`, `log|2v| ≤ 2log X`, `log2 + loglog X ≤ 2loglog X`
cost (`3/4 + 3/16 + 1`). -/
noncomputable def vkDebitConst (C : ℝ) : ℝ :=
  2 * Real.log 4 + (31 / 16) * Real.log 2 + (1 / 4) * Real.log C

/-- The `X`-free MID-branch debit, at the socket's own height floor `T₀ = exp(exp 100)`.
Kept symbolic: it is a fixed (astronomically large, but `X`-free) number times `q`-content. -/
noncomputable def vkMidDebit (q : ℕ) : ℝ :=
  2 * Real.log 4 + (3 / 4) * Real.log 2
    + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2
        * (1 + Real.log q))

lemma vkDebitConst_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ vkDebitConst C := by
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC' : (0 : ℝ) ≤ Real.log C := Real.log_nonneg hC
  unfold vkDebitConst; linarith

lemma vkMidDebit_nonneg (q : ℕ) [NeZero q] : 0 ≤ vkMidDebit q := by
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hE : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have harg : (1 : ℝ) ≤ 3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2
      * (1 + Real.log q) := by
    have h1 : (9 : ℝ) ≤ 3 * (3 + 2 * Real.exp (Real.exp 100)) := by linarith
    have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hlq : (1 : ℝ) ≤ 1 + Real.log q := by linarith
    have s1 : (9 : ℝ) ≤ 3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2 := by
      nlinarith [h1, hq2]
    nlinarith [s1, hlq]
  have := Real.log_nonneg harg
  unfold vkMidDebit; linarith

/-- **The imprimitivity cost, isolated.**  Rescaling `C` by `vkEulerCorr q` (the §4 adapter)
moves the debit by exactly `(1/4)·log(vkEulerCorr q)` — an `O(loglog q)` quantity, and the only
trace imprimitivity leaves anywhere in the close. -/
lemma vkDebitConst_vkEulerCorr {C : ℝ} (hC : 0 < C) (q : ℕ) :
    vkDebitConst (vkEulerCorr q * C)
      = vkDebitConst C + (1 / 4) * Real.log (vkEulerCorr q) := by
  unfold vkDebitConst
  rw [Real.log_mul (ne_of_gt (vkEulerCorr_pos q)) (ne_of_gt hC)]
  ring

private lemma vk_log_one_add_log_le {X : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.log (1 + Real.log X) ≤ Real.log 2 + Real.log (Real.log X) := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have h1 : (0 : ℝ) < 1 + Real.log X := by linarith
  have h2 : 1 + Real.log X ≤ 2 * Real.log X := by linarith
  calc Real.log (1 + Real.log X) ≤ Real.log (2 * Real.log X) := Real.log_le_log h1 h2
    _ = Real.log 2 + Real.log (Real.log X) :=
        Real.log_mul (by norm_num) (by linarith)

/-- The contour box `|v| ≤ 3X` never lets `log|2v|` exceed `2·log X`, once `X ≥ exp(exp 1)`
(which already forces `X > 6`).  This is the ONE place the box radius enters, and it enters
identically for the `X` box and the `3X` box. -/
private lemma vk_log_two_abs_le {X v : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hv : |v| ≤ 3 * X) :
    Real.log |2 * v| ≤ 2 * Real.log X := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h6e : (6 : ℝ) < Real.exp 2 := by rw [hsq]; nlinarith [Real.exp_one_gt_d9]
  have hmono : Real.exp 2 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr he2
  have h6X : (6 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hlog6 : Real.log 6 ≤ Real.log X := Real.log_le_log (by norm_num) h6X
  have hlog6pos : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  rcases eq_or_lt_of_le (abs_nonneg (2 * v)) with h0 | h0
  · rw [← h0, Real.log_zero]; linarith
  · have habs : |2 * v| ≤ 6 * X := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
    calc Real.log |2 * v| ≤ Real.log (6 * X) := Real.log_le_log h0 habs
      _ = Real.log 6 + Real.log X := Real.log_mul (by norm_num) (ne_of_gt hXpos)
      _ ≤ 2 * Real.log X := by linarith

/-- **THE CONSTANT EXPANSION (VT-6's arithmetic core).**  On the contour box the VK-branch
debit is bounded by

  `(15/16)·loglog X + logloglog X + (1/8)·log q + vkDebitConst C`.

The `15/16` is `3/4` (the ζ-pole factor, `chi_Llower_341`'s own cost) plus `3/16` (the
socket's `(log|2t|)^{3/4}`, quartered by the 3-4-1's `4`), and the `(loglog)⁴` costs exactly
ONE `logloglog X`, not four. -/
lemma vk_debit_le {C : ℝ} (hC : 1 ≤ C) {q : ℕ} [NeZero q] {X t : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X) (ht : Real.exp (Real.exp 100) ≤ |t|)
    (h2t : Real.log |2 * t| ≤ 2 * Real.log X) :
    2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (vkProfile C q (2 * t))
      ≤ (15 / 16) * Real.log (Real.log X) + Real.log (Real.log (Real.log X))
          + (1 / 8) * Real.log q + vkDebitConst C := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hL : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hL1 : (2 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have := (Real.le_log_iff_exp_le hLpos).mpr hL
    linarith
  have hLLpos : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  -- the socket's height floor transfers to `|2t|`
  have ht2 : Real.exp (Real.exp 100) ≤ |2 * t| := by
    have : |t| ≤ |2 * t| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg t]
    linarith
  obtain ⟨hg1, hg2⟩ := vk_height_facts ht2
  have hlt : (0 : ℝ) < Real.log |2 * t| := lt_of_lt_of_le (Real.exp_pos _) hg1
  have hllt : (0 : ℝ) < Real.log (Real.log |2 * t|) := by linarith
  -- `loglog|2t| ≤ log 2 + loglog X`
  have hA : Real.log (Real.log |2 * t|) ≤ Real.log 2 + Real.log (Real.log X) := by
    calc Real.log (Real.log |2 * t|) ≤ Real.log (2 * Real.log X) := Real.log_le_log hlt h2t
      _ = Real.log 2 + Real.log (Real.log X) :=
          Real.log_mul (by norm_num) (ne_of_gt hLpos)
  -- `logloglog|2t| ≤ log 2 + logloglog X`
  have hB : Real.log (Real.log (Real.log |2 * t|))
      ≤ Real.log 2 + Real.log (Real.log (Real.log X)) := by
    have hstep : Real.log 2 + Real.log (Real.log X) ≤ 2 * Real.log (Real.log X) := by linarith
    calc Real.log (Real.log (Real.log |2 * t|))
        ≤ Real.log (2 * Real.log (Real.log X)) :=
          Real.log_le_log hllt (le_trans hA hstep)
      _ = Real.log 2 + Real.log (Real.log (Real.log X)) :=
          Real.log_mul (by norm_num) (ne_of_gt hLLpos)
  have hexp := log_vkProfile (C := C) (by linarith) (q := q) (t := 2 * t) ht2
  have hone := vk_log_one_add_log_le hXe
  rw [hexp]
  unfold vkDebitConst
  linarith

/-- **VT-6, THE POINTWISE FLOOR.**  With `K` the (uniform, `q`/`χ`/`X`/`t`-free)
`chi_dist_bridge` constant: for `1 ≤ C`, `χ² ≠ 1`, `X ≥ exp(exp 1)` and any `v` on the
contour box `|v| ≤ 3X`, GIVEN the VT-4 socket wherever it is honest
(`exp(exp 100) ≤ |v|` — below that the mid branch of §2 fires and the socket is never
asserted),

  `(1/16)·loglog X − logloglog X − (1/8)·log q − vkDebitConst C − vkMidDebit q − K
      ≤ 𝔻(λ·χ̄, n^{iv}; X)²`.

Coefficient `1/16` on the nose, with NO `k²` division: this goes through
`chi_floor_low_of_Llower` (coefficient `1`, all frequencies) and never touches the
`orderOf χ` join.  The two branches are joined by subtracting BOTH `X`-free debits, which is
legitimate because both are nonnegative. -/
theorem chi_floor_vk_pointwise :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (C X v : ℝ),
      1 ≤ C → χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X → |v| ≤ 3 * X →
      (Real.exp (Real.exp 100) ≤ |v| → VkTwistUB C (χ ^ 2) X (2 * v)) →
        (1 / 16) * Real.log (Real.log X) - Real.log (Real.log (Real.log X))
            - (1 / 8) * Real.log q - vkDebitConst C - vkMidDebit q - K
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨K, hK⟩ := chi_floor_low_of_Llower
  refine ⟨K, ?_⟩
  intro q _ χ C X v hC hχ2 hX hv hsock
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hL : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : (0 : ℝ) < Real.log X := by linarith [Real.exp_pos (1 : ℝ)]
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have := (Real.le_log_iff_exp_le hLpos).mpr hL
    linarith
  have hlll : (0 : ℝ) ≤ Real.log (Real.log (Real.log X)) := Real.log_nonneg hLL1
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hDC : (0 : ℝ) ≤ vkDebitConst C := vkDebitConst_nonneg hC
  have hDM : (0 : ℝ) ≤ vkMidDebit q := vkMidDebit_nonneg q
  by_cases hbig : Real.exp (Real.exp 100) ≤ |v|
  · -- the VK branch
    have hlow := chi_Llower_341_vk χ C X v hXe (hsock hbig)
    have hfl := hK q χ X v (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (vkProfile C q (2 * v))) hXe hlow
    have hexp := vk_debit_le (C := C) hC (q := q) (X := X) (t := v) hX hbig
      (vk_log_two_abs_le hX hv)
    linarith
  · -- the MID branch
    have hvT : |v| ≤ Real.exp (Real.exp 100) := (not_le.mp hbig).le
    have hT₀ : (1 : ℝ) ≤ Real.exp (Real.exp 100) := by
      have : (0 : ℝ) ≤ Real.exp 100 := (Real.exp_pos 100).le
      calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr this
    have hlow := chi_Llower_341_height χ hχ2 X v (Real.exp (Real.exp 100)) hXe hT₀ hvT
    have hfl := hK q χ X v (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2
            * (1 + Real.log q))) hXe hlow
    have hone := vk_log_one_add_log_le hXe
    have hmid : 2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2
            * (1 + Real.log q))
        ≤ (3 / 4) * Real.log (Real.log X) + vkMidDebit q := by
      unfold vkMidDebit; linarith
    linarith

/-- **D3-3a for the VK floor — the cap-free gate.**  The `(1/16)`-floor beats the
`CapFreeFloor` demand `(1/32)·L + 25` once `L` clears `32·(everything else)`.  The whole
content is `1/16 − 1/32 = 1/32`: the margin is exactly the floor's own excess coefficient.
Genre match: `SiegelBand.capfree_threshold_lt`. -/
theorem vk_capfree_threshold (L ℓ Lq D E K : ℝ)
    (hthr : 32 * (ℓ + (1 / 8) * Lq + D + E + K + 25) < L) :
    (1 / 32) * L + 25 < (1 / 16) * L - ℓ - (1 / 8) * Lq - D - E - K := by linarith

/-- **VT-6, THE CLOSE (the `3X` box).**  Under the VT-4 socket on the whole contour box and
an explicit symbolic threshold on `loglog X`, the twisted datum `λ·χ̄` satisfies
`CapFreeArm3.CapFreeFloor3` — the cap-free arm's hypothesis at the widened box.

Every constant is named (`vkDebitConst C`, `vkMidDebit q`, `K`); there is no hidden `X₀`
(law #253).  Numerically the threshold is `loglog X > 32·(logloglog X + (1/8)log q + …)`,
which for the campaign's `C ≈ 8·10⁶` and door-range `q` sits at `loglog X` of order a few
thousand — subsumed by the ε-window's `6412.6`. -/
theorem capFreeFloor3_lamChi_vk :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (C X : ℝ),
      1 ≤ C → χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X →
      (∀ v : ℝ, |v| ≤ 3 * X → Real.exp (Real.exp 100) ≤ |v| → VkTwistUB C (χ ^ 2) X (2 * v)) →
      32 * (Real.log (Real.log (Real.log X)) + (1 / 8) * Real.log q
            + vkDebitConst C + vkMidDebit q + K + 25) < Real.log (Real.log X) →
        CapFreeFloor3 (lamChi χ) X := by
  obtain ⟨K, hK⟩ := chi_floor_vk_pointwise
  refine ⟨K, ?_⟩
  intro q _ χ C X hC hχ2 hX hsock hthr v hv
  have hfl := hK q χ C X v hC hχ2 hX hv (fun hb => hsock v hv hb)
  have hmar := vk_capfree_threshold (Real.log (Real.log X))
    (Real.log (Real.log (Real.log X))) (Real.log q) (vkDebitConst C) (vkMidDebit q) K hthr
  linarith

/-- **VT-6, THE CLOSE (the `X` box).**  The same at `CapFreeArm.CapFreeFloor`, with the
socket demanded only on `|v| ≤ X`.  The pointwise statements are box-blind, so this is a
wrapper; it is stated separately because its HYPOTHESIS is genuinely weaker. -/
theorem capFreeFloor_lamChi_vk :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (C X : ℝ),
      1 ≤ C → χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X →
      (∀ v : ℝ, |v| ≤ X → Real.exp (Real.exp 100) ≤ |v| → VkTwistUB C (χ ^ 2) X (2 * v)) →
      32 * (Real.log (Real.log (Real.log X)) + (1 / 8) * Real.log q
            + vkDebitConst C + vkMidDebit q + K + 25) < Real.log (Real.log X) →
        CapFreeFloor (lamChi χ) X := by
  obtain ⟨K, hK⟩ := chi_floor_vk_pointwise
  refine ⟨K, ?_⟩
  intro q _ χ C X hC hχ2 hX hsock hthr v hv
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hv3 : |v| ≤ 3 * X := by linarith
  have hfl := hK q χ C X v hC hχ2 hX hv3 (fun hb => hsock v hv hb)
  have hmar := vk_capfree_threshold (Real.log (Real.log X))
    (Real.log (Real.log (Real.log X))) (Real.log q) (vkDebitConst C) (vkMidDebit q) K hthr
  linarith

end Salt.MR
