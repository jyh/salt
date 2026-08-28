/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FarL2
import Salt.MR.CofactorSupply

/-!
# `A2Wall` — THE `seamT0` RE-CUT WINDOW, IN THE KERNEL

The GEOMEAN-SCOPE fallback re-cuts the seam floor `seamT0 X` from `(log X)^{1/15}` to
`(log X)^{1/n}` with `n ≈ 45`, paying the crude fold's `√(seamT0 X)` out of the CONTOUR-BOX
floor (`FarL2.box_floor_M0`, coefficient `1/16`) instead of the band floor's `7/30`.  The
window it lands in was priced on paper only.  This file is the arithmetic, checked.

## §1–§2 — THE FLOOR (the gate side, a lower bound on `n`)

`T0BandCapFree.cfb_gate_decay`'s identity, freed of its two numerals: with
`T₀ = (log X)^ν` and the gate `M₀ ≥ c·e·loglog X`,

  `(log X)^ν · e^{−M₀/e} ≤ (log X)^{ν−c}`     (`a2wall_gate_general`),

so the first exit summand of `ThmA2.thm_a2'_of_rows` decays at rate `δ := c − ν`.  At the
box floor the largest available `c` is `1/16/e`, whence

  `ν ≤ 1/(16e) − δ`,    i.e.   `n ≥ 1/(1/(16e) − δ)`.

The PRE-RE-CUT configuration was `ν = 1/15`, `c = 103/1500`, `δ = 1/500`, paid by the BAND
floor `7/30`; `a2wall_box_fails_gate_15` is why that gate cannot be met at box strength, i.e.
why the re-cut exists at all.  (The re-cut `(n, m) = (45, 46)`, `δ = 1/5000` is LANDED as of
2026-07-28: `SeamSplit.seamT0`/`seamRad` carry it, and `T0BandCapFree.cfb_gate_decay` is
stated at `1009/45000`.)  The thresholds, exactly:

| `δ` | critical `n` | least integer | stone |
|---|---|---|---|
| `0` | `16e = 43.4925…` | `44` | `a2wall_critical_n` |
| `1/5000` | `43.8742…` | `44` | `a2wall_floor_44` / `a2wall_floor_43_fails` |
| `1/500` | `47.6357…` | `48` | `a2wall_floor_48_at_500` / `a2wall_floor_47_fails_at_500` |

## §3 — THE CEILING (the ball side, an upper bound on `n`)

⚠ **THE `§8.3` FIRST-TERM WALL IS NOT IN THE LANDED CHAIN.**  `s8-freeze.md:11`'s
`1 − 1/n − (1−θ)` is the MR-paper bookkeeping — the term `log Q₈₃/(T₀·log P₈₃)` at MR's own
pin `θ = 1/48` (from MR's Halász grade `ρ = 1/16`).  The corpus replaced that page with the
⟦V5e⟧ BALANCE pin: `USetPrice.hU_fully_priced` prices `∫_𝒰` as the main leg
`(log X)^{5θ−2ρ}` against the remainder leg `(log X)^{−θ}`, met at `θ = ρ/3`, with `1/log P₈₃`
entering ONLY through the floor page `H₈₃·log P₈₃ ≥ log X` — and `seamT0` appears nowhere in
it (`a2Mrow` is `seamT0`-free).  At the landed pin `θ₂₉₃ = 1/(32(3e+1))` the freeze's own
formula would read `n < 1/θ₂₉₃ = 292.96`, not `48`; but the term it names does not exist here.

The ceiling that IS in the landed statements sits on the BALL radius, not the seam floor.
`CofactorSupply.cofactorRbd`'s CASE-B half is `farSupS = 2√2/R + farErr` at `R = Rrad ≤
seamRad X`, and `USetPrice.hU_fully_priced` pins `cofactorRbd ≤ CR·(log X)^{−ρ₂₉₃}`.  So the
pin FORCES `6√2/Rrad ≤ CR·(log X)^{−ρ₂₉₃}` (`a2wall_ballrad_forced`), i.e. at
`seamRad X = (log X)^{1/m}`

  `6√2 ≤ CR·(log X)^{1/m − ρ₂₉₃}`     (`a2wall_ballrad_pin_exponent`),

which at a constant `CR` demands `1/m > ρ₂₉₃ = 3/(32(3e+1))`, i.e. `m < 97.6516…`
(`a2wall_ceiling_97` / `a2wall_ceiling_98_fails`).  Since the ball must sit strictly inside
the annulus (`CenterCore.seamRad_lt_seamT0`, `n < m`), the seam floor's own ceiling is the
same number.  At the working re-cut `(n, m) = (45, 46)` the pin clears with a `2.12×` margin
(`a2wall_ballrad_46_clears`).

**THE VERIFIED WINDOW:** `n ∈ [44, 97]`, not `(43.9, 48)` — the floor is confirmed, the
ceiling moves up by a factor `2.03`.
-/

namespace Salt.MR

open Real

/-! ## §1 — THE GATE, PARAMETRIC -/

/-- **THE GATE IDENTITY, FREE OF ITS NUMERALS** (`a2wall_gate_general`).
`T0BandCapFree.cfb_gate_decay` with `1/15` replaced by a free `ν` and `103/1500` by a free
`c`: under `M₀ ≥ c·e·loglog X`,

  `(log X)^ν · e^{−M₀/e} ≤ (log X)^{ν−c}`.

Nothing is estimated — `e^{−M₀/e} ≤ (log X)^{−c}` is the gate read through
`Real.rpow_def_of_pos`, and the exponents then add. -/
theorem a2wall_gate_general {X M₀ ν c : ℝ} (hL : 1 ≤ Real.log X)
    (hgate : c * Real.exp 1 * Real.log (Real.log X) ≤ M₀) :
    Real.log X ^ ν * Real.exp (-(1 / Real.exp 1) * M₀) ≤ Real.log X ^ (ν - c) := by
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le zero_lt_one hL
  have hstep : Real.exp (-(1 / Real.exp 1) * M₀) ≤ Real.log X ^ (-c) := by
    rw [Real.rpow_def_of_pos hL0]
    refine Real.exp_le_exp.mpr ?_
    have hinv : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgate hinv
    have hid : (1 / Real.exp 1) * (c * Real.exp 1 * Real.log (Real.log X))
        = c * Real.log (Real.log X) := by
      field_simp
    rw [hid] at hmul
    nlinarith [hmul]
  have hν : (0 : ℝ) ≤ Real.log X ^ ν := Real.rpow_nonneg hL0.le _
  calc Real.log X ^ ν * Real.exp (-(1 / Real.exp 1) * M₀)
      ≤ Real.log X ^ ν * Real.log X ^ (-c) := mul_le_mul_of_nonneg_left hstep hν
    _ = Real.log X ^ (ν - c) := by
        rw [← Real.rpow_add hL0]; ring_nf

/-- **THE RE-CUT GATE AT `n = 45`, `δ = 1/5000`** (`a2wall_gate_45`).  The exponent
arithmetic is EXACT, exactly as at `n = 15`: `1/45 − 1009/45000 = 1000/45000 − 1009/45000 =
−9/45000 = −1/5000`.  This is the re-cut's twin of `T0BandCapFree.cfb_gate_decay`. -/
theorem a2wall_gate_45 {X M₀ : ℝ} (hL : 1 ≤ Real.log X)
    (hgate : 1009 / 45000 * Real.exp 1 * Real.log (Real.log X) ≤ M₀) :
    Real.log X ^ ((1 : ℝ) / 45) * Real.exp (-(1 / Real.exp 1) * M₀)
      ≤ Real.log X ^ (-(1 : ℝ) / 5000) := by
  have h := a2wall_gate_general (ν := (1 : ℝ) / 45) (c := 1009 / 45000) hL hgate
  rwa [show (1 : ℝ) / 45 - 1009 / 45000 = -(1 : ℝ) / 5000 by norm_num] at h

/-! ## §2 — THE BOX FLOOR PAYS IT (the floor half of the window) -/

/-- **THE MARGIN** (`a2wall_box_clears_45`).  `(1009/45000)·e ≤ 0.0609500` against the box
floor's `1/16 = 0.0625`: the re-cut gate clears with `1/16 − (1009/45000)e ≥ 1/700`
(the true margin is `0.00155008…`, i.e. `1/645.1`). -/
theorem a2wall_box_clears_45 : 1009 / 45000 * Real.exp 1 ≤ 1 / 16 - 1 / 700 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  linarith

/-- **THE BOX FLOOR CLEARS THE RE-CUT GATE** (`a2wall_box_floor_clears_gate_45`).  The
`T0BandCapFree.cfb_floor_clears_gate` twin at `FarL2.boxM0`'s coefficient `1/16` and the
re-cut gate `(1009/45000)·e`: with `L := loglog X`, `ℓ := logloglog X` and the box floor's
own debits `D := (5/4)ℓ + (3/4)log q + q + K`,

  `700·D ≤ L  ⟹  (1009/45000)·e·L ≤ boxM0 K q X`.

The threshold constant is `700` (against `cfb_floor_clears_gate`'s `22` at `7/30` and
`FarL2.plog_floor_clears_gate`'s `16` at `1/4`) — the whole price of dropping to box
strength. -/
theorem a2wall_box_floor_clears_gate_45 {K : ℝ} {q : ℕ} {X : ℝ}
    (hLL : 0 ≤ Real.log (Real.log X))
    (hthr : 700 * ((5 / 4) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log q
              + (q : ℝ) + K) ≤ Real.log (Real.log X)) :
    1009 / 45000 * Real.exp 1 * Real.log (Real.log X) ≤ boxM0 K q X := by
  have hmar := a2wall_box_clears_45
  have hmul : 1009 / 45000 * Real.exp 1 * Real.log (Real.log X)
      ≤ (1 / 16 - 1 / 700) * Real.log (Real.log X) :=
    mul_le_mul_of_nonneg_right hmar hLL
  unfold boxM0
  linarith

/-- **THE STRICT NEGATIVITY AT THE BOX FLOOR** (`a2wall_exponent_neg_45`) — the twin of
`M4ClassPrice.m4_decay_exponent_neg` (`1/15 − 7/(30e) < 0`) with the band floor's `7/30`
replaced by the box floor's `1/16` and the seam floor re-cut to `1/45`:

  `1/45 − 1/(16e) < 0`,   equivalently `16e < 45`.

This is the ONE fact that makes the re-cut's decay-retaining pricing work at all. -/
theorem a2wall_exponent_neg_45 : (1 : ℝ) / 45 - 1 / (16 * Real.exp 1) < 0 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < 16 * Real.exp 1 := by positivity
  have hlt : (1 : ℝ) / 45 < 1 / (16 * Real.exp 1) := by
    rw [div_lt_div_iff₀ (by norm_num) h0]
    linarith
  linarith

/-- **THE FLOOR IS SHARP** (`a2wall_critical_n`).  `43 < 16e < 44`: the bare convergence
demand `1/n < 1/(16e)` fails at `n = 43` and holds at `n = 44`.  `16e = 43.4925…`. -/
theorem a2wall_critical_n : (43 : ℝ) < 16 * Real.exp 1 ∧ 16 * Real.exp 1 < 44 := by
  constructor
  · linarith [Real.exp_one_gt_d9]
  · linarith [Real.exp_one_lt_d9]

/-- **THE FLOOR AT `δ = 1/5000`** (`a2wall_floor_44`).  `1/44 ≤ 1/(16e) − 1/5000`: `n = 44`
already meets the re-cut gate at the relaxed decay demand (`n ≥ 43.8742…`).  `n = 45` is the
working choice; this is the sharp integer. -/
theorem a2wall_floor_44 : (1 : ℝ) / 44 ≤ 1 / (16 * Real.exp 1) - 1 / 5000 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < 16 * Real.exp 1 := by positivity
  have hkey : (5044 : ℝ) / 220000 ≤ 1 / (16 * Real.exp 1) := by
    rw [div_le_div_iff₀ (by norm_num) h0]
    linarith
  have hsplit : (1 : ℝ) / 44 + 1 / 5000 = 5044 / 220000 := by norm_num
  linarith

/-- **AND IT IS SHARP** (`a2wall_floor_43_fails`).  `1/(16e) − 1/5000 < 1/43`: at the relaxed
decay demand `n = 43` still fails. -/
theorem a2wall_floor_43_fails : 1 / (16 * Real.exp 1) - 1 / 5000 < (1 : ℝ) / 43 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h0 : (0 : ℝ) < 16 * Real.exp 1 := by positivity
  have hkey : 1 / (16 * Real.exp 1) < (5043 : ℝ) / 215000 := by
    rw [div_lt_div_iff₀ h0 (by norm_num)]
    linarith
  have hsplit : (1 : ℝ) / 43 + 1 / 5000 = 5043 / 215000 := by norm_num
  linarith

/-- **THE δ-COUPLING, PRICED** (`a2wall_floor_48_at_500`).  KEEPING the landed decay demand
`δ = 1/500` moves the floor to `n ≥ 47.6357…`: `1/48 ≤ 1/(16e) − 1/500`.  This is why the
fallback relaxes `δ` — at `δ = 1/500` the floor collides with the freeze's (nonexistent)
`48` ceiling. -/
theorem a2wall_floor_48_at_500 : (1 : ℝ) / 48 ≤ 1 / (16 * Real.exp 1) - 1 / 500 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < 16 * Real.exp 1 := by positivity
  have hkey : (137 : ℝ) / 6000 ≤ 1 / (16 * Real.exp 1) := by
    rw [div_le_div_iff₀ (by norm_num) h0]
    linarith
  have hsplit : (1 : ℝ) / 48 + 1 / 500 = 137 / 6000 := by norm_num
  linarith

/-- `1/(16e) − 1/500 < 1/47` — at `δ = 1/500` even `n = 47` fails. -/
theorem a2wall_floor_47_fails_at_500 : 1 / (16 * Real.exp 1) - 1 / 500 < (1 : ℝ) / 47 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h0 : (0 : ℝ) < 16 * Real.exp 1 := by positivity
  have hkey : 1 / (16 * Real.exp 1) < (547 : ℝ) / 23500 := by
    rw [div_lt_div_iff₀ h0 (by norm_num)]
    linarith
  have hsplit : (1 : ℝ) / 47 + 1 / 500 = 547 / 23500 := by norm_num
  linarith

/-- **THE FALLBACK'S FALLBACK** (`a2wall_floor32_89`).  If the `1/16` box floor cannot be
transported to the door's masked piece and only `CapFreeArm`'s `1/32` is available
(`M4T0Datum`'s table, row `box`), the floor moves to `n ≥ 88.525…`: `1/89 ≤ 1/(32e) − 1/5000`.
Under the freeze's claimed `48` ceiling that route was DEAD; under the landed ceiling
(§3, `97.6516…`) the window `n ∈ [89, 96]` is still non-empty. -/
theorem a2wall_floor32_89 : (1 : ℝ) / 89 ≤ 1 / (32 * Real.exp 1) - 1 / 5000 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < 32 * Real.exp 1 := by positivity
  have hkey : (5089 : ℝ) / 445000 ≤ 1 / (32 * Real.exp 1) := by
    rw [div_le_div_iff₀ (by norm_num) h0]
    linarith
  have hsplit : (1 : ℝ) / 89 + 1 / 5000 = 5089 / 445000 := by norm_num
  linarith

/-! ### ⭐ THE SAME FLOOR AT THE θ-LIFTED HALÁSZ GRADE (A6 wave, node 9)

`USetPins.rhoB4` is `1/(32e)`, and its own docstring names it **the B4 Halász grade** — `ρ = c/32`
at the head constant `c = 1/e`.  The A6 wave freed that head constant to `e^{−θ}`
(`SeamBallWeighted.head_sigma_bound_theta`, `HalaszDirect.window_sup_decay_theta`), so the same
page at `θ = log 2` — the `c = 1/2` point — reads `ρ = (1/2)/32 = 1/64`.

⭐⭐ **THIS IS WHY THE HEAD CONSTANT IS WORTH MORE THAN A CONSTANT.**  `ρ` is not a multiplier: it
is `theta83 ρ = ρ/3`, which is the EXPONENT in `H83 X θ = (log X)^θ`.  A factor `e/2 ≈ 1.359` on
`ρ` is a factor on a RATE, not on a coefficient.

⛔ **THESE TWO THEOREMS ARE ARITHMETIC AT A HYPOTHETICAL GRADE, AND NOTHING CONSUMES THEM.**  They
say what the `1/32`-floor fallback becomes IF the balance page is re-run at `ρ = 1/64`; the balance
page has NOT been re-run, `rhoB4` is UNCHANGED, and re-deriving it is a design act.  They are here
so the wave's claimed benefit is CHECKABLE rather than asserted in a bus post.
⇒ 🔑 ***WHEN A CLAIM ABOUT A NUMBER IS THE DELIVERABLE, THE NUMBER IS A NODE.*** -/

/-- **The `1/32`-floor fallback at the θ-lifted grade** (`a2wall_floor64_65`):
`1/65 ≤ 1/64 − 1/5000`.
Compare `a2wall_floor32_89` — the sharp integer moves **89 → 65**, and against §3's landed ceiling
`97.6516…` the admissible window widens from `n ∈ [89, 96]` to `n ∈ [65, 96]`.
📌 The direction is the favourable one and that is not an accident: `1/64 > 1/(32e)`, and the floor
is an `≤` against `ρ`, so a LARGER grade can only admit MORE `n`. -/
theorem a2wall_floor64_65 : (1 : ℝ) / 65 ≤ 1 / 64 - 1 / 5000 := by norm_num

/-- `1/64 − 1/5000 < 1/64` — `65` is the sharp integer at the θ-lifted grade, exactly as `89` is at
`1/(32e)`.  (Stated against `1/64` rather than `1/n` for `n = 64`: they are the same numeral, and
this is the form that exhibits the `1/5000` slack as the whole of the gap.) -/
theorem a2wall_floor64_64_fails : 1 / 64 - 1 / 5000 < (1 : ℝ) / 64 := by norm_num

/-- `1/(32e) − 1/5000 < 1/88` — `89` is the sharp integer at the `1/32` floor. -/
theorem a2wall_floor32_88_fails : 1 / (32 * Real.exp 1) - 1 / 5000 < (1 : ℝ) / 88 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h0 : (0 : ℝ) < 32 * Real.exp 1 := by positivity
  have hkey : 1 / (32 * Real.exp 1) < (5088 : ℝ) / 440000 := by
    rw [div_lt_div_iff₀ h0 (by norm_num)]
    linarith
  have hsplit : (1 : ℝ) / 88 + 1 / 5000 = 5088 / 440000 := by norm_num
  linarith

/-- **WHY THE RE-CUT EXISTS** (`a2wall_box_fails_gate_15`).  The LANDED gate coefficient
`(103/1500)·e ≈ 0.18665` is `2.99×` above the box floor's `1/16 = 0.0625`: at `n = 15` the
first exit summand cannot be paid out of the contour box at all.  (`T0BandCapFree`'s header
records the same fact against `CapFreeFloor`'s `1/32`, at `6×`.) -/
theorem a2wall_box_fails_gate_15 : (1 : ℝ) / 16 < 103 / 1500 * Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

/-! ## §3 — THE CEILING: the ball radius against the U-7 exit grade -/

/-- **THE PIN FORCES A BALL RADIUS** (`a2wall_ballrad_forced`).  `CofactorSupply.cofactorRbd`
is `3·max(2·caseAS, farSupS)` and `farSupS W Y Rmax R = 2√2/R + farErr W Y Rmax` with
`farErr ≥ 0`, so ANY upper bound `B` on `cofactorRbd` is an upper bound on `6√2/R`.  This is
the only place the ball radius is bounded BELOW in the whole §8.3 chain, and it is what caps
the re-cut. -/
theorem a2wall_ballrad_forced {c Cb X θ W Y Rmax R B : ℝ}
    (hY : 0 ≤ Real.log Y) (hRmax : 0 ≤ Rmax)
    (hpin : cofactorRbd c Cb X θ W Y Rmax R ≤ B) :
    6 * Real.sqrt 2 / R ≤ B := by
  have hfe : (0 : ℝ) ≤ farErr W Y Rmax := farErr_nonneg hY hRmax
  have hlow : 2 * Real.sqrt 2 / R ≤ farSupS W Y Rmax R := by
    unfold farSupS; linarith
  have hmax : farSupS W Y Rmax R
      ≤ max (2 * caseAS c Cb (cofactorMfl X θ W) W) (farSupS W Y Rmax R) := le_max_right _ _
  unfold cofactorRbd at hpin
  have h6 : 6 * Real.sqrt 2 / R = 3 * (2 * Real.sqrt 2 / R) := by ring
  rw [h6]
  linarith

/-- **THE CEILING, AS AN EXPONENT INEQUALITY** (`a2wall_ballrad_pin_exponent`).  At the ball
radius `R = (log X)^m` the U-7 pin `cofactorRbd ≤ CR·(log X)^{−ρ₂₉₃}` (the `hRgrade` binder of
`USetPrice.hU_fully_priced`) forces

  `6√2 ≤ CR·(log X)^{m − ρ₂₉₃}`.

At a constant `CR` this is possible only for `m > ρ₂₉₃`; at `seamRad X = (log X)^{1/m'}` that
reads `m' < 1/ρ₂₉₃ = 32(3e+1)/3 = 97.6516…`.  **This — not the `§8.3` first term — is the
landed ceiling on the re-cut.** -/
theorem a2wall_ballrad_pin_exponent {c Cb X θ W Y Rmax CR m : ℝ}
    (hL : 0 < Real.log X) (hY : 0 ≤ Real.log Y) (hRmax : 0 ≤ Rmax)
    (hpin : cofactorRbd c Cb X θ W Y Rmax (Real.log X ^ m)
      ≤ CR * Real.log X ^ (-rho293)) :
    6 * Real.sqrt 2 ≤ CR * Real.log X ^ (m - rho293) := by
  have hforced := a2wall_ballrad_forced (R := Real.log X ^ m) hY hRmax hpin
  have hRpos : (0 : ℝ) < Real.log X ^ m := Real.rpow_pos_of_pos hL m
  rw [div_le_iff₀ hRpos] at hforced
  have hcomb : Real.log X ^ (-rho293) * Real.log X ^ m = Real.log X ^ (m - rho293) := by
    rw [← Real.rpow_add hL, neg_add_eq_sub]
  rw [mul_assoc, hcomb] at hforced
  exact hforced

/-- **THE CEILING'S EXACT LOCATION** (`a2wall_ceiling_97`).  `ρ₂₉₃ < 1/97`: a ball radius
`(log X)^{1/97}` still clears the U-7 exit grade. -/
theorem a2wall_ceiling_97 : rho293 < 1 / 97 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h0 : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by positivity
  rw [rho293, theta293, show (3 : ℝ) * (1 / (32 * (3 * Real.exp 1 + 1)))
      = 3 / (32 * (3 * Real.exp 1 + 1)) by ring,
    div_lt_div_iff₀ h0 (by norm_num)]
  linarith

/-- **AND IT IS SHARP** (`a2wall_ceiling_98_fails`).  `1/98 < ρ₂₉₃`: at `(log X)^{1/98}` the
CASE-B half of `cofactorRbd` no longer decays fast enough for the pin.  `1/ρ₂₉₃ =
32(3e+1)/3 = 97.6516…`. -/
theorem a2wall_ceiling_98_fails : (1 : ℝ) / 98 < rho293 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by positivity
  rw [rho293, theta293, show (3 : ℝ) * (1 / (32 * (3 * Real.exp 1 + 1)))
      = 3 / (32 * (3 * Real.exp 1 + 1)) by ring,
    div_lt_div_iff₀ (by norm_num) h0]
  linarith

/-- **THE WORKING RE-CUT CLEARS IT** (`a2wall_ballrad_46_clears`).  At `(n, m) = (45, 46)` —
the seam floor `(log X)^{1/45}` with the ball radius re-pinned to `(log X)^{1/46}` so that
`seamRad < seamT0` survives — the U-7 pin clears with `1/46 = 0.02174` against
`ρ₂₉₃ = 0.01024`, a `2.12×` margin. -/
theorem a2wall_ballrad_46_clears : rho293 < 1 / 46 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h0 : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by positivity
  rw [rho293, theta293, show (3 : ℝ) * (1 / (32 * (3 * Real.exp 1 + 1)))
      = 3 / (32 * (3 * Real.exp 1 + 1)) by ring,
    div_lt_div_iff₀ h0 (by norm_num)]
  linarith

/-- **THE WINDOW, IN ONE LINE** (`a2wall_window_45_46`).  The re-cut `(n, m) = (45, 46)` is
inhabited: the seam floor's exponent `1/45` sits under the box floor's gate budget
`1/(16e) − 1/5000` (the FLOOR), and the ball radius' exponent `1/46` sits above `ρ₂₉₃`
(the CEILING), with `1/46 < 1/45` (the ball inside the annulus). -/
theorem a2wall_window_45_46 :
    (1 : ℝ) / 45 ≤ 1 / (16 * Real.exp 1) - 1 / 5000 ∧ rho293 < 1 / 46
      ∧ (1 : ℝ) / 46 < 1 / 45 := by
  refine ⟨?_, a2wall_ballrad_46_clears, by norm_num⟩
  have h44 := a2wall_floor_44
  have : (1 : ℝ) / 45 ≤ 1 / 44 := by norm_num
  linarith

end Salt.MR
