/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SiegelBand
import Salt.MR.EvenChiDescent

/-!
# POINT→BAND, step 1 — the band `L`-lower with a STATED RATE in `q` (`BandRated`)

`QUEUE.md` P2 item 6, commissioned at WORKER tier by helm ruling 2026-08-26 06:0x.
**Standing instruction, adopted verbatim: SPEND NOTHING ON GRADE.**

## What this file is for

`SiegelBand.chi_Llower_band_uniform` produces a band constant `B(Q)` by a bare induction-max over
the characters of every modulus `q ≤ Q`, and its own header records the consequence: *"it has no
known growth rate in `Q`"*.  That is the ineffectivity the `K_vt` cushion inherits — and the
cushion evaluates it at `Qm = ⌈(log H₊)^12⌉₊`, i.e. at an argument that grows with the same `H₊`
that funds the budget, so **an unrated constant there is not slack, it is a demanded exponent**
(`arc.md` §4's struck R-1; measured `Qm^0.083 → 1/12`).

This file starts the repair at the one seam that needs it.  `chi_floor_band_uniform` composes
`chi_Llower_band_uniform` into `ChiFloorLow.chi_floor_low_of_Llower`; **replacing only the first
factor** with a RATED band lower bound carries the composition through.

## The rate, and where it comes from

`SiegelArm` §6 already built the uniform arm conditional on ONE input — a lower bound for
`(L(1,χ)).re` — in `chi_Llower_real_of_L1`.  `EvenChiDescent.l1LowerEffective_goldenGate` supplies
exactly that input, **effectively**, for every real nonprincipal `χ`:
`L1LowerEffective (log((3+√5)/2)) (5/2)`.  Instantiating one at the other is this file's content.

⭐ **THE POINT OF THE STATEMENT BELOW: its only existential is `Z`, and `Z` is `q`-FREE and
`χ`-FREE** (a compact maximum over the fixed box `[1,2] × [−1,1]`, `SiegelArm.zeta_upper_band`).
Every `q`-dependence is on the page: `−log L₁ = (5/2)·log q + log(1/c)` and
`diskConst q = 27/2·√q·(1+log q)·q` (`Salt/SW/SiegelFinal.lean:53`), both explicit.  **That is the
whole difference from `chi_Llower_band_uniform`, whose `B(Q)` has no stated growth at all.**

⚠️ **AND IT IS WHY THE COEFFICIENT DROPS.**  The bound carries `(3/4)·log(1 + log X)`, which is
`X`-DEPENDENT, so through `chi_floor_low_of_Llower` the floor becomes `(1/4)·loglog X − …` where the
landed band arm gives coefficient `1`.  **That trade is structural and unrecoverable** — every
effective arm in this corpus pays that term (32 sites, 7 files), and the only arm that avoids it is
the compact-minimum one, i.e. the ineffective route.  *Coefficient 1 was the ineffectivity wearing
a better coefficient.*  The consumer demand is `(1/32)·loglog X + 25 + D` and `1/32 < 1/4`, so the
shape survives; re-deriving `capFreeFloor3_margin_all_chi_vt`'s threshold at `1/4` is the
commission's remaining content and is NOT attempted here.

⛔ **SCOPE.**  Real nonprincipal `χ` only (`χ ≠ 1`, `χ² = 1`).  That is not a gap: the cushion's band
arm is consumed **only** at `χ² = 1` with `|v| ≤ 1/2` (`VkMidSharp.capFreeFloor3_margin_all_chi_vt`
splits on `χ² = 1` first, sending `χ² ≠ 1` to the VK pointwise arm, which Wave K's numeral stones
already made effective).  The principal character's own band bound is separately EXPLICIT
(`SiegelArm.LFunction_band_lower_principal`, `δ/q`).
-/

namespace Salt.MR

open Complex DirichletCharacter Salt.SW

/-! ## §1 — the golden `L₁`, as a named function of `q` -/

/-- **The effective `L(1,χ)` floor as a function of the modulus** — `goldenGate`'s value at `q`.
`c/q^{5/2}` with `c = log((3+√5)/2) = 2·log φ`, the constant `EvenChiDescent` lands at both
parities.  Named so the rate is readable at every call site rather than inlined. -/
noncomputable def goldenL1 (q : ℕ) : ℝ :=
  Real.log ((3 + Real.sqrt 5) / 2) / (q : ℝ) ^ (5 / 2 : ℝ)

/-- `√5 < 2.3`, by squaring.  Local because it is used twice and mathlib has no numeral form. -/
private lemma sqrt_five_lt : Real.sqrt 5 < 2.3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

/-- `c = log((3+√5)/2) ≤ 1`: the argument is `≈ 2.618 < e`. -/
lemma log_golden_le_one : Real.log ((3 + Real.sqrt 5) / 2) ≤ 1 := by
  have hlt : (3 + Real.sqrt 5) / 2 < Real.exp 1 := by
    have := sqrt_five_lt
    nlinarith [Real.exp_one_gt_d9]
  have hpos : (0 : ℝ) < (3 + Real.sqrt 5) / 2 := by
    have := Real.sqrt_nonneg 5; linarith
  have hlog := Real.log_lt_log hpos hlt
  rw [Real.log_exp] at hlog
  linarith

/-- `0 < goldenL1 q` at every nonzero modulus. -/
lemma goldenL1_pos (q : ℕ) [NeZero q] : 0 < goldenL1 q := by
  have hq : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  exact div_pos e4a_log_golden_pos (Real.rpow_pos_of_pos hq _)

/-- `goldenL1 q ≤ 1`: the numerator is `≤ 1` and the denominator is `≥ 1`. -/
lemma goldenL1_le_one (q : ℕ) [NeZero q] : goldenL1 q ≤ 1 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hden : (1 : ℝ) ≤ (q : ℝ) ^ (5 / 2 : ℝ) :=
    Real.one_le_rpow hq1 (by norm_num)
  rw [goldenL1, div_le_one (by linarith : (0:ℝ) < (q : ℝ) ^ (5 / 2 : ℝ))]
  linarith [log_golden_le_one]

/-- **`goldenGate`, unfolded at `goldenL1`** — the hypothesis `chi_Llower_real_of_L1` asks for. -/
lemma goldenL1_le_LFunction_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hsq : χ ^ 2 = 1) :
    goldenL1 q ≤ (DirichletCharacter.LFunction χ 1).re :=
  l1LowerEffective_goldenGate q χ hne hsq

/-! ## §2 — the rated band `L`-lower at real nonprincipal `χ` -/

/-- ⭐ **POINT→BAND STEP 1** (`chi_Llower_band_real_rated`).  `SiegelArm.chi_Llower_real_of_L1` with
its `L₁` slot filled by the LANDED effective floor `goldenL1 q`, so the bound's entire
`q`-dependence is explicit:

`−(log 2 − log L₁ + 2log4 + (3/4)log(1+log X) + (1/4)log(16·q·Z·diskConst q / L₁))`
  `  ≤ log‖L(1+1/log X − it, χ)‖`

at `L₁ = c/q^{5/2}`, so `−log L₁ = (5/2)log q + log(1/c)`.

**The only existential is `Z`, and it is `q`-free and `χ`-free** — the compact maximum of
`SiegelArm.zeta_upper_band` over the fixed box.  Contrast `chi_Llower_band_uniform`, whose `B(Q)`
is a bare induction-max with no stated growth: *that* is the difference the `K_vt` cushion needs,
because the cushion evaluates its constant at an argument growing with `H₊`.

The scale gate `32·diskConst q / goldenL1 q ≤ log X` is `chi_Llower_real_of_L1`'s own and is
CARRIED, not discharged — at the door's range it clears with enormous room (`loglog X ≥ log H₊ − 14`
against a demand polynomial in `q`), but that discharge belongs to the consumer, not here. -/
theorem chi_Llower_band_real_rated :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 / 2 →
        32 * diskConst q / goldenL1 q ≤ Real.log X →
          -(Real.log 2 - Real.log (goldenL1 q)
              + (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
                + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q)))
            ≤ Real.log ‖DirichletCharacter.LFunction χ
                (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨Z, hZ1, hL⟩ := chi_Llower_real_of_L1
  refine ⟨Z, hZ1, ?_⟩
  intro q _ χ hne hsq X t hX ht hgate
  exact hL q χ hne hsq X t (goldenL1 q) hX ht (goldenL1_pos q) (goldenL1_le_one q)
    (goldenL1_le_LFunction_one χ hne hsq) hgate

end Salt.MR
