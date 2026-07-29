/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4T0Datum
import Salt.MR.FarStar
import Salt.MR.GradeWindowC
import Salt.MR.MVCore2

/-!
# `FarL2` — THE PRICING-SCOPE R1 PAGE: the poly-log floor and the ℓ²-mass far kernel

Two independent pages, both aimed at ⟦THE PRICING RESIDUE⟧ — the fact that the truncation
height that the far arm can afford (`FarStar.Tstar k L = L⁴·k^{1/(4 log L)}`) is EXACTLY the
height at which the χ-floor's coefficient collapses from `1/4` to `1/16`.

* **§1–§7 — THE POLY-LOG FLOOR (P3).**  `plogM0` / `polylog_floor_M0` — the height-
  parameterized band floor at coefficient **`1/4`** on `|v| ≤ (log X)^A`, for EVERY `A ≥ 1`,
  with the height debit doubly-logarithmic (`log(3A) + logloglog X`) rather than the box's
  `(3/16)·loglog X`.  Three arms, exactly as `T0BandCapFree.band_floor_M0`, but the non-real
  arm is taken through the **VK branch** (`VkTwistClose.chi_Llower_341_vk`, socket discharged
  by `VkTwistLadder.vkTwistUB_holds`) above the absolute height `exp(exp 100)` and through
  `chi_Llower_341_height` AT that absolute height below — so no `(1/4)·log(3 + 2T)` height
  price is ever paid against `loglog X`.  Coefficient `1/4`, versus the `T₀`-band's `7/30`
  and the contour box's `1/16`.
* **§8 — the master check.**  `plog_floor_clears_gate`: the assembled coefficient beats the
  `T0BandCapFree` gate `(1009/45000)·e = 0.0609500…` with the margin `1/4 − 1/16 = 0.1875`,
  i.e. the threshold constant is **`16`** (against `band_floor_M0`'s `22`).
* **§9 — the transports.**  `polylog_floor_M0_liouChi` / `polylog_floor_M0_pieceDatum` —
  the `band_floor_M0_pieceDatum` pattern verbatim, through `pretDistSq_liouChi_eq` and
  `CofactorSupplier.pretDistSq_pieceDatum_ge`.
* **§10 — the free wins.**  `band_floor_M0_vk` (w2: the `T₀`-band floor lifted `7/30 → 1/4`,
  an instance of §7 at `A := 2`) and `boxM0` / `box_floor_M0` (w1: the plain
  `M₀ ≤ 𝔻²` pointwise form on the whole `3X` box at coefficient `1/16`, no threshold margin
  spent — `capFreeFloor3_margin_all_chi` without the `CapFreeFloor3` wrapper).
* **§11–§13 — THE ℓ²-MASS FAR KERNEL (P2).**  `winL2Coeff` / `windowSum_eq_dpoly` /
  `winL2Mass` — the window Dirichlet polynomial identified with `L2MVT.dpoly`, so
  `MVCore2.dirichlet_poly_l2_mvt_final` applies to it, together with the far-region
  reduction `crossKerFar_le_weighted_l2` which replaces the two ℓ¹ masses
  (`HExit.norm_windowSum_le_mass`, which carry `k^{1/(4 log L)}`) by the two `1/τ²`-weighted
  ℓ² tails.  See ⟦THE N-TERM REFUTATION⟧ below for what this page does and does NOT close.

## ⟦THE N-TERM REFUTATION⟧ (P2, the design finding)

The scope's P2 route — "dyadic Cauchy–Schwarz in `τ` + the landed L² mean value against the
kernel's `1/(c²+τ²)` weight" — does NOT reach a poly-log `H` as stated.  The landed mean
value is `dirichlet_poly_l2_mvt_final`:

  `∫_{−R}^{R} ‖dpoly N a‖² ≤ (2R + 20N)·∑_{n≤N}‖aₙ‖²`,

and the `τ`-dyadic sum of the kernel weight produces `A·(2/H) + N·A/H²` with
`A := ∑‖aₙ‖²` the ℓ² mass and `N := ⌈k/y⌉₊` the window LENGTH.  The `A/H` term is free
(it beats the ℓ¹ route by `L⁶·k^{1/(4 log L)}`), but the `N·A/H²` term carries `N ≍ k/L⁴`,
and pricing it against the crown's currency `k·(log X)^{−1/(32e)}` forces

  `H ≳ √k·L^{−3.24}`,

which is WORSE than the standing `Tstar = L⁴·k^{1/(4 log L)}`.  The `20N` is not slack: it
is the Montgomery–Vaughan constant at the UNIFORM spacing `δ = 1/N`, and the sharp
per-frequency spacing `δₙ ≍ 1/n` is not what `MVCore2.mvHilbertUniform_holds` supplies.

**THE REPAIR** (arithmetic verified, not yet in Lean): split the WINDOW dyadically first —
`(y, k/y) = ⋃_j (2^j y, 2^{j+1} y)`, `J ≍ L/log 2` blocks — apply the mean value per block,
and recombine by Cauchy–Schwarz over the blocks (cost: one factor `J`).  The `N`-term
becomes `J·∑_j M_j·A_j ≍ L·L³ = L⁴` in place of `N·A ≍ k·L^{−8}`, and the pricing then
forces only

  `H ≳ 19·L^{2.76}/log L` — POLY-LOG,

which is the scope's target.  §11–§13 land the unconditional stones that route needs (the
`dpoly` identification, the ℓ² mass with NO `k`-power, and the far-region reduction to the
weighted ℓ² tails); the dyadic-in-`n` split and the `τ`-layer-cake are NOT landed here.

## Traps observed

* **the FIFTH log scale.**  `(log X)^A` and `(log k)^A` are different glyphs; every lemma
  below states its height in `Real.log X ^ A` with `X` the SAME `X` the floor is read at.
  Nothing here speaks `log k`.
* **`A` is bound BEFORE the `∃K`** in every assembly, so `K` may (and does) depend on `A`;
  this is the only reason the height debit `log(3A)` can be absorbed.
* **the shifted variable** — the floors are stated in the BARE frequency `v`, exactly as
  `T0BandCapFree`'s are; `HalaszHead.seamCoeff_trivial_dist_eq` remains the consumer's
  adapter and is NOT applied here.
* **strict vs non-strict** — every floor here is non-strict (`≤`), like `band_floor_M0`;
  the STRICT `CapFreeFloor3` demand is not produced.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §1 — the numeric stones -/

private lemma plog_log_five_le : Real.log 5 ≤ 2 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h7 : (7 : ℝ) < Real.exp 2 := by rw [hsq]; nlinarith
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 5) (by linarith : (5 : ℝ) ≤ Real.exp 2)
  rwa [Real.log_exp] at this

private lemma plog_log_eighteen_le : Real.log 18 ≤ 3 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h7 : (7 : ℝ) < Real.exp 2 := by rw [hsq]; nlinarith
  have h3 : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h20 : (18 : ℝ) < Real.exp 3 := by rw [h3]; nlinarith
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 18) (by linarith : (18 : ℝ) ≤ Real.exp 3)
  rwa [Real.log_exp] at this

private lemma plog_log_two_le : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith

/-- `1 ≤ (log X)^A` past the scale floor, for every `A ≥ 0`. -/
private lemma plog_one_le_rpow {X A : ℝ} (hL : (1 : ℝ) ≤ Real.log X) (hA : 0 ≤ A) :
    (1 : ℝ) ≤ Real.log X ^ A := by
  calc (1 : ℝ) = Real.log X ^ (0 : ℝ) := (Real.rpow_zero _).symm
    _ ≤ Real.log X ^ A := Real.rpow_le_rpow_of_exponent_le hL hA

/-- **THE POLY-LOG HEIGHT'S OWN LOGARITHM.**  On `|v| ≤ (log X)^A` with `A ≥ 1`, for any
`b ≥ 3` with `log b ≤ b - 1`-shaped slack absorbed into `c ≥ b`:
`log(|2v| + b) ≤ c·A·loglog X` once `log(2 + b) ≤ (c-1)·A·loglog X`.  Stated in the two
instances the arms need (`b = 3`, `c = 5`; `b = 16`, `c = 18`) below. -/
private lemma plog_inner_log {X v A b c : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hA : 1 ≤ A)
    (hv : |v| ≤ Real.log X ^ A) (hb : 0 < b) (hbc : 2 + b ≤ c) (hlogc : Real.log c ≤ c - 2) :
    Real.log (|2 * v| + b) ≤ c * A * Real.log (Real.log X) := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLA : (1 : ℝ) ≤ Real.log X ^ A := plog_one_le_rpow hL1 (by linarith)
  have habs : |2 * v| = 2 * |v| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hbox : |2 * v| + b ≤ c * Real.log X ^ A := by
    rw [habs]
    have h1 : 2 * |v| ≤ 2 * Real.log X ^ A := by linarith
    have h2 : b ≤ b * Real.log X ^ A := by nlinarith
    nlinarith [hLA, hbc]
  have hpos : (0 : ℝ) < |2 * v| + b := by positivity
  have hc0 : (0 : ℝ) < c := by linarith
  have hstep := Real.log_le_log hpos hbox
  rw [Real.log_mul (ne_of_gt hc0) (ne_of_gt (by positivity : (0 : ℝ) < Real.log X ^ A)),
    Real.log_rpow hL0] at hstep
  have hAL : (1 : ℝ) ≤ A * Real.log (Real.log X) := by nlinarith
  nlinarith [hstep, hlogc, hAL]

/-- **POLY-LOG DRIFT 1** (`plog_drift_loglog`).  `loglog(|2v| + 3) ≤ log(5A) + logloglog X`
on `|v| ≤ (log X)^A`, `A ≥ 1` — the `T0BandCapFree.cfb_band_loglog` twin at a FREE height
exponent.  The height enters ONLY through the additive `log(5A)`; the leading term is
`logloglog X`, doubly logarithmic, which is the whole point. -/
theorem plog_drift_loglog {X v A : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hA : 1 ≤ A)
    (hv : |v| ≤ Real.log X ^ A) :
    Real.log (Real.log (|2 * v| + 3))
      ≤ Real.log (5 * A) + Real.log (Real.log (Real.log X)) := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hstep : Real.log (|2 * v| + 3) ≤ 5 * A * Real.log (Real.log X) :=
    plog_inner_log hX hA hv (by norm_num) (by norm_num) (by linarith [plog_log_five_le])
  have hinner : (1 : ℝ) < |2 * v| + 3 := by linarith [abs_nonneg (2 * v)]
  have hipos : (0 : ℝ) < Real.log (|2 * v| + 3) := Real.log_pos hinner
  have hA0 : (0 : ℝ) < 5 * A := by linarith
  have h := Real.log_le_log hipos hstep
  rwa [show (5 : ℝ) * A * Real.log (Real.log X) = (5 * A) * Real.log (Real.log X) from by ring,
    Real.log_mul (ne_of_gt hA0) (ne_of_gt hLL0)] at h

/-- **POLY-LOG DRIFT 2** (`plog_drift_logloglog`).  `logloglog(|2v| + 16) ≤ log(18A) +
logloglog X` on `|v| ≤ (log X)^A`, `A ≥ 1` — the `cfb_band_logloglog` twin.  One more `log`
than drift 1, paid by `log w ≤ w − 1`. -/
theorem plog_drift_logloglog {X v A : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hA : 1 ≤ A)
    (hv : |v| ≤ Real.log X ^ A) :
    Real.log (Real.log (Real.log (|2 * v| + 16)))
      ≤ Real.log (18 * A) + Real.log (Real.log (Real.log X)) := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hstep : Real.log (|2 * v| + 16) ≤ 18 * A * Real.log (Real.log X) :=
    plog_inner_log hX hA hv (by norm_num) (by norm_num) (by linarith [plog_log_eighteen_le])
  -- `|2v| + 16 ≥ 16 > e`, so the second log is `> 0` and the third is honest
  have he1lt : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
  have hpos : (0 : ℝ) < |2 * v| + 16 := by positivity
  have he16 : Real.exp 1 < |2 * v| + 16 := by linarith [abs_nonneg (2 * v)]
  have hin1 : (1 : ℝ) < Real.log (|2 * v| + 16) := (Real.lt_log_iff_exp_lt hpos).mpr he16
  have hin0 : (0 : ℝ) < Real.log (|2 * v| + 16) := by linarith
  have hA0 : (0 : ℝ) < 18 * A := by linarith
  have h2 := Real.log_le_log hin0 hstep
  rw [show (18 : ℝ) * A * Real.log (Real.log X) = (18 * A) * Real.log (Real.log X) from by ring,
    Real.log_mul (ne_of_gt hA0) (ne_of_gt hLL0)] at h2
  -- level 3
  have h2pos : (0 : ℝ) < Real.log (Real.log (|2 * v| + 16)) := Real.log_pos hin1
  have hsum0 : (0 : ℝ) < Real.log (18 * A) + Real.log (Real.log (Real.log X)) := by
    have : (0 : ℝ) < Real.log (18 * A) := Real.log_pos (by linarith)
    linarith
  have h3 := Real.log_le_log h2pos h2
  have h4 := Real.log_le_sub_one_of_pos hsum0
  linarith

/-! ## §2 — ARM 1: the real characters at poly-log height (coefficient `1/4`) -/

/-- **ARM 1 (poly-log, `χ² = 1`) — THE `k = 2` FLOOR AT A FREE HEIGHT EXPONENT**
(`plog_floor_real`).  For every `A ≥ 1`, every `χ` with `χ² = 1` (principal INCLUDED), every
`X ≥ exp(exp 1)` and every `1/2 ≤ |v| ≤ (log X)^A`:

  `(1/4)·loglog X − (23/16)·logloglog X − (1/4)·q − C ≤ 𝔻²(λ·χ̄, n^{iv}; X)`.

`ChiFloor.chi_floor_of_order` at `k = 2` with §1's poly-log drifts.  The coefficient is the
band's `1/4`, NOT the box's `1/16`: the `(3/4)·loglog(|2v|+3)` debit is doubly logarithmic at
poly-log height, so the bracket keeps its full `loglog X` and the `/k² = /4` delivers `1/4`.
`C` depends on `A` (through `log(5A)`, `log(18A)`) and on nothing else. -/
theorem plog_floor_real (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≠ 0 → χ ^ 2 = 1 →
      Real.exp (Real.exp 1) ≤ X → 1 / 2 ≤ |v| → |v| ≤ Real.log X ^ A →
        (1 / 4) * Real.log (Real.log X)
            - (23 / 16) * Real.log (Real.log (Real.log X))
            - (1 / 4) * (q : ℝ) - C
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨C₀, hC₀⟩ := chi_floor_of_order
  refine ⟨(C₀ + (3 / 4) * Real.log (5 * A) + 5 * Real.log (18 * A)) / 4, ?_⟩
  intro q χ X v hq hχ2 hX hv2 hvA
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hXe : Real.exp 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact le_trans (Real.exp_le_exp.mpr h1) hX
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hkt : (1 : ℝ) ≤ |((2 : ℕ) : ℝ) * v| := by
    rw [hcast, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hmain := hC₀ q χ 2 X v (by norm_num) ⟨1, by norm_num⟩ hχ2 hXe hkt
  rw [hcast, show ((2 : ℝ)) ^ 2 = 4 by norm_num] at hmain
  have hA1 := plog_drift_loglog (X := X) (v := v) (A := A) hX hA hvA
  have hA2 := plog_drift_logloglog (X := X) (v := v) (A := A) hX hA hvA
  have hP := primeDivSum_le_modulus (q := q) hq X
  linarith

/-! ## §3 — the VK debit at poly-log height -/

/-- **THE VK-BRANCH DEBIT AT POLY-LOG HEIGHT** (`plog_vk_debit`).  `VkTwistClose.vk_debit_le`'s
twin on `|v| ≤ (log X)^A` in place of the contour box `|v| ≤ 3X`:

  `2log4 + (3/4)log(1+log X) + (1/4)log(vkProfile C q (2v))`
      `≤ (3/4)·loglog X + (19/16)·logloglog X + (1/8)·log q + vkDebitConst C
          + (19/16)·log(3A)`.

**The whole pricing residue is this one line.**  On the box `vk_debit_le` reads
`loglog|2v| ≤ log 2 + loglog X` and pays `(3/16)·loglog X` — the coefficient collapse
`1/4 → 1/16`.  At poly-log height `loglog|2v| ≤ log(3A) + logloglog X`, doubly logarithmic,
and the `loglog X` coefficient stays `1 − 3/4 = 1/4`.  The `(loglog)⁴` in the profile is
priced by `log w ≤ w − 1` (four copies of `(1/4)·loglog|2v|`), giving `19/16 = 3/16 + 1` on
the `logloglog` slot. -/
lemma plog_vk_debit {C : ℝ} (hC : 1 ≤ C) {q : ℕ} [NeZero q] {X v A : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X) (hA : 1 ≤ A) (hv : |v| ≤ Real.log X ^ A)
    (hbig : Real.exp (Real.exp 100) ≤ |v|) :
    2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (vkProfile C q (2 * v))
      ≤ (3 / 4) * Real.log (Real.log X)
          + (19 / 16) * Real.log (Real.log (Real.log X))
          + (1 / 8) * Real.log q + vkDebitConst C + (19 / 16) * Real.log (3 * A) := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hXe : Real.exp 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact le_trans (Real.exp_le_exp.mpr h1) hX
  -- the socket's height floor transfers to `|2v|`
  have ht2 : Real.exp (Real.exp 100) ≤ |2 * v| := by
    have hle : |v| ≤ |2 * v| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg v]
    linarith
  obtain ⟨hg1, hg2⟩ := vk_height_facts ht2
  have hlt : (0 : ℝ) < Real.log |2 * v| := lt_of_lt_of_le (Real.exp_pos _) hg1
  have hllt : (0 : ℝ) < Real.log (Real.log |2 * v|) := by linarith
  -- (i) `log|2v| ≤ 3A·loglog X`
  have hinner : Real.log |2 * v| ≤ 3 * A * Real.log (Real.log X) := by
    have hLA : (1 : ℝ) ≤ Real.log X ^ A := plog_one_le_rpow hL1 (by linarith)
    have habs : |2 * v| = 2 * |v| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hbox : |2 * v| ≤ 2 * Real.log X ^ A := by rw [habs]; linarith
    have hpos : (0 : ℝ) < |2 * v| := by linarith [Real.exp_pos (Real.exp 100)]
    have hstep := Real.log_le_log hpos hbox
    rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity : (0 : ℝ) < Real.log X ^ A)),
      Real.log_rpow hL0] at hstep
    have hAL : (1 : ℝ) ≤ A * Real.log (Real.log X) := by nlinarith
    nlinarith [hstep, plog_log_two_le, hAL]
  -- (ii) `loglog|2v| ≤ log(3A) + logloglog X`
  have hA0 : (0 : ℝ) < 3 * A := by linarith
  have hmid : Real.log (Real.log |2 * v|)
      ≤ Real.log (3 * A) + Real.log (Real.log (Real.log X)) := by
    have h := Real.log_le_log hlt hinner
    rwa [show (3 : ℝ) * A * Real.log (Real.log X) = (3 * A) * Real.log (Real.log X) from by ring,
      Real.log_mul (ne_of_gt hA0) (ne_of_gt hLL0)] at h
  -- (iii) `logloglog|2v| ≤ loglog|2v| − 1`
  have htop : Real.log (Real.log (Real.log |2 * v|)) ≤ Real.log (Real.log |2 * v|) - 1 :=
    Real.log_le_sub_one_of_pos hllt
  -- the profile expansion and the `1 + log X` rounding
  have hexp := log_vkProfile (C := C) (by linarith) (q := q) (t := 2 * v) ht2
  have hone : Real.log (1 + Real.log X) ≤ Real.log 2 + Real.log (Real.log X) := by
    have h1 : (0 : ℝ) < 1 + Real.log X := by linarith
    have h2 : 1 + Real.log X ≤ 2 * Real.log X := by linarith
    calc Real.log (1 + Real.log X) ≤ Real.log (2 * Real.log X) := Real.log_le_log h1 h2
      _ = Real.log 2 + Real.log (Real.log X) := Real.log_mul (by norm_num) (ne_of_gt hL0)
  rw [hexp]
  unfold vkDebitConst
  linarith [plog_log_two_le, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

/-! ## §4 — ARM 2: the non-real characters at poly-log height (coefficient `1/4`) -/

/-- **ARM 2 (poly-log, `χ² ≠ 1`) — THE VK BRANCH ABOVE THE ABSOLUTE HEIGHT**
(`plog_floor_nonreal`).  For every `A ≥ 1`, `C ≥ 1`, every NON-REAL `χ mod q`, every
`X ≥ exp(exp 1)` and every `|v| ≤ (log X)^A`, GIVEN the VT-4 socket wherever it is honest
(`exp(exp 100) ≤ |v|`):

  `(1/4)·loglog X − (19/16)·logloglog X − (1/8)·log q − vkDebitConst C − vkMidDebit q`
      `− (19/16)·log(3A) − K ≤ 𝔻²(λ·χ̄, n^{iv}; X)`.

Two branches, exactly `VkTwistClose.chi_floor_vk_pointwise`'s, but the VK branch is priced by
§3 instead of `vk_debit_le`: coefficient `1/4`, not `1/16`.  The MID branch (`|v| <
exp(exp 100)`) is the box's own, and it ALREADY delivers `1/4` — it pays the height only
through the `X`-free `vkMidDebit q`. -/
theorem plog_floor_nonreal (A : ℝ) (hA : 1 ≤ A) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (C X v : ℝ),
      1 ≤ C → χ ^ 2 ≠ 1 → Real.exp (Real.exp 1) ≤ X → |v| ≤ Real.log X ^ A →
      (Real.exp (Real.exp 100) ≤ |v| → VkTwistUB C (χ ^ 2) X (2 * v)) →
        (1 / 4) * Real.log (Real.log X)
            - (19 / 16) * Real.log (Real.log (Real.log X))
            - (1 / 8) * Real.log q - vkDebitConst C - vkMidDebit q
            - (19 / 16) * Real.log (3 * A) - K
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨K, hK⟩ := chi_floor_low_of_Llower
  refine ⟨K, ?_⟩
  intro q _ χ C X v hC hχ2 hX hv hsock
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hDC : (0 : ℝ) ≤ vkDebitConst C := vkDebitConst_nonneg hC
  have hDM : (0 : ℝ) ≤ vkMidDebit q := vkMidDebit_nonneg q
  have hA0 : (0 : ℝ) ≤ Real.log (3 * A) := Real.log_nonneg (by linarith)
  by_cases hbig : Real.exp (Real.exp 100) ≤ |v|
  · -- THE VK BRANCH, at poly-log height
    have hlow := chi_Llower_341_vk χ C X v hXe (hsock hbig)
    have hfl := hK q χ X v (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (vkProfile C q (2 * v))) hXe hlow
    have hdeb := plog_vk_debit (C := C) hC (q := q) (X := X) (v := v) (A := A) hX hA hv hbig
    linarith
  · -- THE MID BRANCH: the absolute height `exp(exp 100)`, `X`-free
    have hvT : |v| ≤ Real.exp (Real.exp 100) := (not_le.mp hbig).le
    have hT₀ : (1 : ℝ) ≤ Real.exp (Real.exp 100) := by
      have : (0 : ℝ) ≤ Real.exp 100 := (Real.exp_pos 100).le
      calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr this
    have hlow := chi_Llower_341_height χ hχ2 X v (Real.exp (Real.exp 100)) hXe hT₀ hvT
    have hfl := hK q χ X v (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2
            * (1 + Real.log q))) hXe hlow
    have hone : Real.log (1 + Real.log X) ≤ Real.log 2 + Real.log (Real.log X) := by
      have h1 : (0 : ℝ) < 1 + Real.log X := by linarith
      have h2 : 1 + Real.log X ≤ 2 * Real.log X := by linarith
      calc Real.log (1 + Real.log X) ≤ Real.log (2 * Real.log X) := Real.log_le_log h1 h2
        _ = Real.log 2 + Real.log (Real.log X) := Real.log_mul (by norm_num) (ne_of_gt hL0)
    have hmid : 2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2
            * (1 + Real.log q))
        ≤ (3 / 4) * Real.log (Real.log X) + vkMidDebit q := by
      unfold vkMidDebit; linarith
    linarith

/-! ## §5 — the assembled value `plogM0` -/

/-- **THE ASSEMBLED POLY-LOG FLOOR VALUE** (`plogM0`).  `T0BandCapFree.cfbM0`'s shape with the
leading coefficient lifted `7/30 → 1/4` and the `q`-slot widened from `(1/4)·q` to `q` (which
is what absorbs the VK arm's `vkDebitConst (vkEulerCorr q · vkTwistConst q) + vkMidDebit q`,
both `O(log q)`):

  `plogM0 K q X = (1/4)·loglog X − (23/16)·logloglog X − (3/4)·log q − q − K`.

The `23/16` is the REAL arm's `logloglog` coefficient (the VK arm's is the smaller `19/16`),
and `K` carries every `X`-free constant including the height's `log(5A)`, `log(18A)`,
`log(3A)`. -/
def plogM0 (K : ℝ) (q : ℕ) (X : ℝ) : ℝ :=
  (1 / 4) * Real.log (Real.log X) - (23 / 16) * Real.log (Real.log (Real.log X))
    - (3 / 4) * Real.log q - (q : ℝ) - K

/-- The debit shifts `plogM0`'s constant additively (the `cfbM0_add_debit` twin). -/
theorem plogM0_add_debit (K D : ℝ) (q : ℕ) (X : ℝ) :
    plogM0 (K + D) q X = plogM0 K q X - D := by
  unfold plogM0; ring

/-- The `q`-content of the VK arm's two named debits fits the `plogM0` `q`-slot:
`vkDebitConst (vkEulerCorr q · vkTwistConst q) + vkMidDebit q ≤ Kq + (3/2)·log q` with `Kq`
absolute.  `vkEulerCorr q ≤ q`, `vkTwistConst q = 10⁷·q·(1+log q)`, `1 + log q ≤ q`. -/
private lemma plog_vk_qdebit (q : ℕ) [NeZero q] :
    vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q
      ≤ (2 * Real.log 4 + (31 / 16) * Real.log 2 + (1 / 4) * Real.log 10000000
          + 2 * Real.log 4 + (3 / 4) * Real.log 2
          + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100))))
        + (3 / 2) * Real.log q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hlq : (1 : ℝ) + Real.log q ≤ (q : ℝ) := by
    have := Real.log_le_sub_one_of_pos hq0; linarith
  have hEC : vkEulerCorr q ≤ (q : ℝ) := by
    have h1 : (1 : ℝ) ≤ vkEulerCorr q := one_le_vkEulerCorr q
    -- `∏_{p|q}(1 + 1/p) ≤ ∏_{p|q} p ≤ q` is not needed: `1 + 1/p ≤ p` for `p ≥ 2`
    have h2 : vkEulerCorr q ≤ (q : ℝ) := by
      unfold vkEulerCorr
      calc ∏ p ∈ q.primeFactors, (1 + 1 / (p : ℝ))
          ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := by
            refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
            have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
            have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
            have : (1 : ℝ) / (p : ℝ) ≤ 1 := by
              rw [div_le_one (by linarith)]; linarith
            linarith
        _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (q : ℝ) := by
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
              (Nat.prod_primeFactors_dvd q)
    exact h2
  have hECpos : (0 : ℝ) < vkEulerCorr q := vkEulerCorr_pos q
  have hTC : vkTwistConst q ≤ 10000000 * (q : ℝ) * (q : ℝ) := by
    unfold vkTwistConst
    nlinarith [hlq, hq1]
  have hTCpos : (0 : ℝ) < vkTwistConst q := by
    have := one_le_vkTwistConst (q := q); linarith
  have hprod : vkEulerCorr q * vkTwistConst q ≤ 10000000 * (q : ℝ) ^ 3 := by
    nlinarith [hEC, hTC, hECpos.le, hTCpos.le, hq1]
  have hprodpos : (0 : ℝ) < vkEulerCorr q * vkTwistConst q := by positivity
  have hlogprod : Real.log (vkEulerCorr q * vkTwistConst q)
      ≤ Real.log 10000000 + 3 * Real.log q := by
    have h := Real.log_le_log hprodpos hprod
    have hrw : Real.log (10000000 * (q : ℝ) ^ 3) = Real.log 10000000 + 3 * Real.log q := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    rwa [hrw] at h
  have hmid : vkMidDebit q ≤ 2 * Real.log 4 + (3 / 4) * Real.log 2
      + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100)))
      + (3 / 4) * Real.log q := by
    unfold vkMidDebit
    have hE0 : (0 : ℝ) < 3 * (3 + 2 * Real.exp (Real.exp 100)) := by
      positivity
    have harg : Real.log (3 * (3 + 2 * Real.exp (Real.exp 100)) * (q : ℝ) ^ 2
          * (1 + Real.log q))
        = Real.log (3 * (3 + 2 * Real.exp (Real.exp 100))) + 2 * Real.log q
          + Real.log (1 + Real.log q) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (ne_of_gt hE0) (by positivity),
        Real.log_pow]
      push_cast; ring
    have hll : Real.log (1 + Real.log q) ≤ Real.log q := by
      rcases eq_or_lt_of_le hlogq with h0 | h0
      · rw [← h0]; simp
      · exact Real.log_le_log (by linarith) hlq |>.trans (le_refl _)
    rw [harg]; linarith
  unfold vkDebitConst
  linarith

/-! ## §6 — the socket, discharged -/

/-- The VT-4 socket at the campaign's own constant, for the SQUARE character — the
`CofactorSupplier.capFreeFloor3_margin_all_chi` discharge, isolated. -/
private lemma plog_socket {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 ≠ 1)
    {X v : ℝ} (hXe : Real.exp 1 ≤ X) (hbig : Real.exp (Real.exp 100) ≤ |v|) :
    VkTwistUB (vkEulerCorr q * vkTwistConst q) (χ ^ 2) X (2 * v) := by
  have h2v : Real.exp (Real.exp 100) ≤ |2 * v| := by
    have hle : |v| ≤ |2 * v| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg v]
    linarith
  exact vkTwistUB_holds (χ ^ 2) hχ2 hXe h2v

/-! ## §7 — THE ASSEMBLED POLY-LOG FLOOR -/

/-- **P3 — THE POLY-LOG FLOOR** (`polylog_floor_M0`).  For every height exponent `A ≥ 1` and
every finite modulus range `Q` there is one `X`-free, `q`-free `K ≥ 0` with

  `plogM0 K q X ≤ 𝔻²(λ·χ̄, n^{iv}; X)`

for every `q ≤ Q`, EVERY `χ mod q`, every `X ≥ exp(exp 1)` and every `|v| ≤ (log X)^A`.

**The coefficient is `1/4`** — the `T0BandCapFree.band_floor_M0` assembly re-run with the
non-real arm taken through the VK branch (§4) instead of the height-capped mid branch, which
is what removes the `(1/4)·log(3 + 2T)` height price and lifts `7/30 → 1/4`.  Three arms,
one `χ²`-split and one `|v|`-split, exactly as `band_floor_M0`:

| class | supplier | delivery |
|---|---|---|
| `χ²=1`, `1/2 ≤ \|v\|` | §2 `plog_floor_real` | `(1/4)L − (23/16)ℓ − (1/4)q − C` |
| `χ²=1`, `\|v\| ≤ 1/2` | `CapFreeAssembly.chi_floor_band_arm Q` | `L − C` |
| `χ² ≠ 1` | §4 `plog_floor_nonreal` (socket §6) | `(1/4)L − (19/16)ℓ − …` |

**No socket remains**: `VkTwistLadder.vkTwistUB_holds` discharges it at
`C = vkEulerCorr q · vkTwistConst q`, whose two named debits are absorbed by the `q`-slot
(`plog_vk_qdebit`).  `K` depends on `A` and `Q` only. -/
theorem polylog_floor_M0 (A : ℝ) (hA : 1 ≤ A) (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ Real.log X ^ A →
        plogM0 K q X ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Kr, hKr⟩ := plog_floor_real A hA
  obtain ⟨Kn, hKn⟩ := plog_floor_nonreal A hA
  obtain ⟨Ks, hKs⟩ := chi_floor_band_arm Q
  set Kq : ℝ := 2 * Real.log 4 + (31 / 16) * Real.log 2 + (1 / 4) * Real.log 10000000
      + 2 * Real.log 4 + (3 / 4) * Real.log 2
      + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100))) with hKqdef
  refine ⟨max 0 (max Kr (max (Kn + Kq + (19 / 16) * Real.log (3 * A)) Ks)),
    le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kr (max (Kn + Kq + (19 / 16) * Real.log (3 * A)) Ks)) with hKdef
  have hKr' : Kr ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKn' : Kn + Kq + (19 / 16) * Real.log (3 * A) ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKs' : Ks ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X v hq hX hv
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  unfold plogM0
  by_cases hsq : χ ^ 2 = 1
  · by_cases hband : |v| ≤ 1 / 2
    · -- the Siegel-band arm, coefficient `1`
      have h := hKs q χ X v hq hX hband
      linarith
    · -- the `k = 2` real arm, coefficient `1/4`
      have h := hKr q χ X v hq0 hsq hX (le_of_lt (not_le.mp hband)) hv
      linarith
  · -- the VK arm, coefficient `1/4`, socket discharged
    have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
      nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
    have h := hKn q χ (vkEulerCorr q * vkTwistConst q) X v hC1 hsq hX hv
      (fun hbig => plog_socket χ hsq hXe hbig)
    have hqd := plog_vk_qdebit q
    rw [← hKqdef] at hqd
    have hlq : Real.log q ≤ (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (q : ℝ)); linarith
    linarith

/-! ## §8 — THE MASTER CHECK -/

/-- **THE MASTER CHECK** (`plog_floor_clears_gate`).  The `T0BandCapFree.cfb_floor_clears_gate`
twin at the LIFTED coefficient.  With `L := loglog X`, `ℓ := logloglog X` and the floor's
debits `D := (23/16)·ℓ + (3/4)·log q + q + K`,

  `16·D ≤ L  ⟹  (1009/45000)·e·L ≤ plogM0 K q X`.

The margin is `1/4 − (1009/45000)·e = 0.25 − 0.0609500… = 0.1890499… ≥ 1/16 = 0.0625`, so the
threshold constant is **`16`** — against `band_floor_M0`'s `22` at `7/30`, and against the
contour box's `1/16 = 0.0625`, which DOES clear the re-cut gate (`0.0609500 < 0.0625`; the
refuter's K3 finding).  This is the whole pricing content of the poly-log pin. -/
theorem plog_floor_clears_gate {K : ℝ} {q : ℕ} {X : ℝ}
    (hLL : 0 ≤ Real.log (Real.log X))
    (hthr : 16 * ((23 / 16) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log q
              + (q : ℝ) + K) ≤ Real.log (Real.log X)) :
    1009 / 45000 * Real.exp 1 * Real.log (Real.log X) ≤ plogM0 K q X := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hmul : Real.exp 1 * Real.log (Real.log X)
      ≤ 2.7182818286 * Real.log (Real.log X) :=
    mul_le_mul_of_nonneg_right he.le hLL
  unfold plogM0
  linarith

/-! ## §9 — the transports to the row datum -/

/-- **THE POLY-LOG FLOOR AT THE SUM-SIDE DATUM** (`polylog_floor_M0_liouChi`).  The
`band_floor_M0_liouChi` transport verbatim: `CapFreeAssembly.pretDistSq_liouChi_eq` is an
EQUALITY of distances. -/
theorem polylog_floor_M0_liouChi (A : ℝ) (hA : 1 ≤ A) (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ Real.log X ^ A →
        plogM0 K q X ≤ pretDistSq (liouChi χ) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := polylog_floor_M0 A hA Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ X v hq hX hv
  rw [pretDistSq_liouChi_eq]
  exact hK q χ X v hq hX hv

/-- **THE POLY-LOG FLOOR AT THE MASKED PIECE** (`polylog_floor_M0_pieceDatum`).  The
`M4T0Datum.band_floor_M0_pieceDatum` pattern at the lifted coefficient: the sum-side floor
less the mask's Mertens debit, through `CofactorSupplier.pretDistSq_pieceDatum_ge` (factor
`1`, the mask being `gxDatum` at `x = 0`). -/
theorem polylog_floor_M0_pieceDatum (A : ℝ) (hA : 1 ≤ A) (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X v D : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ Real.log X ^ A →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
        plogM0 (K + D) q X ≤ pretDistSq (pieceDatum χ 𝒥 Pseq Qseq) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := polylog_floor_M0_liouChi A hA Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X v D hq hX hv hdebit
  have hfloor := hK q χ X v hq hX hv
  have htr := pretDistSq_pieceDatum_ge χ Pseq Qseq
    (fun p _ => le_of_eq (costwist_norm v p)) X 𝒥
  rw [plogM0_add_debit]
  linarith

/-! ## §10 — THE FREE WINS -/

/-- **FREE WIN w2 — THE `T₀`-BAND FLOOR LIFTED `7/30 → 1/4`** (`band_floor_M0_vk`).
`T0BandCapFree.band_floor_M0`'s conclusion at `plogM0`'s coefficient `1/4`, on the SAME band
`|v| ≤ 2·seamT0 X + 1`.  An instance of §7 at `A := 3`: `seamT0 X = (log X)^{1/45} ≤ log X`,
so `2·seamT0 X + 1 ≤ 2·log X + 1 ≤ (log X)³` past the scale floor.

The lift matters because `band_floor_M0`'s `7/30 = 0.2333…` clears the gate `0.18665` with
margin `1/22`, while `1/4` clears it with margin `1/16` — and because the SAME statement now
holds at every poly-log height, not only at `seamT0`. -/
theorem band_floor_M0_vk (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
        plogM0 K q X ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := polylog_floor_M0 3 (by norm_num) Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ X v hq hX hv
  refine hK q χ X v hq hX ?_
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hLe : (2.7182818283 : ℝ) < Real.log X := by linarith [Real.exp_one_gt_d9]
  -- `seamT0 X = (log X)^{1/45} ≤ log X`, and `2·log X + 1 ≤ 3·log X ≤ (log X)³`
  have hseam : seamT0 X ≤ Real.log X := by
    unfold seamT0
    calc Real.log X ^ ((1 : ℝ) / 45) ≤ Real.log X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = Real.log X := Real.rpow_one _
  have hpow : Real.log X ^ (3 : ℝ) = Real.log X ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rw [hpow]
  have h2L : |v| ≤ 2 * Real.log X + 1 := by linarith
  have hL2 : (3 : ℝ) ≤ Real.log X ^ 2 := by nlinarith [hLe]
  have hcube : 2 * Real.log X + 1 ≤ Real.log X ^ 3 := by
    have : Real.log X ^ 3 = Real.log X * Real.log X ^ 2 := by ring
    nlinarith [hL2, hL1]
  linarith

/-- **FREE WIN w1 — THE PLAIN BOX FLOOR VALUE** (`boxM0`).  `plogM0`'s shape at the CONTOUR
BOX's coefficient `1/16`. -/
def boxM0 (K : ℝ) (q : ℕ) (X : ℝ) : ℝ :=
  (1 / 16) * Real.log (Real.log X) - (5 / 4) * Real.log (Real.log (Real.log X))
    - (3 / 4) * Real.log q - (q : ℝ) - K

/-- **FREE WIN w1 — THE PLAIN POINTWISE BOX FLOOR** (`box_floor_M0`).  The `M₀ ≤ 𝔻²` form on
the whole contour box `|v| ≤ 3X` at coefficient `1/16`, for EVERY `χ mod q ≤ Q`, with NO
threshold and NO margin spent.

`CofactorSupplier.capFreeFloor3_margin_all_chi`'s three arms with the
`(1/32)·loglog X + 25 + D < ⋯` wrapper removed: the arms deliver `1/16`, the wrapper spends
half of it on `CapFreeFloor3`'s strict demand.  A consumer that only needs a value `M₀` to
put in `e^{−M₀/(2e)}` (the `hRHS` pricing) should read THIS, not `CapFreeFloor3`.

`5/4` is the bulk arm's own `logloglog` coefficient (`chi_floor_real_bulk`); the VK arm's is
`1`, and the band arm has none. -/
theorem box_floor_M0 (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 3 * X →
        boxM0 K q X ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Kvk, hvk⟩ := chi_floor_vk_pointwise
  obtain ⟨Kb, hb⟩ := chi_floor_real_bulk
  obtain ⟨Ks, hKs⟩ := chi_floor_band_arm Q
  set Kq : ℝ := 2 * Real.log 4 + (31 / 16) * Real.log 2 + (1 / 4) * Real.log 10000000
      + 2 * Real.log 4 + (3 / 4) * Real.log 2
      + (1 / 4) * Real.log (3 * (3 + 2 * Real.exp (Real.exp 100))) with hKqdef
  refine ⟨max 0 (max Kb (max (Kvk + Kq) Ks)), le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kb (max (Kvk + Kq) Ks)) with hKdef
  have hKb' : Kb ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKv' : Kvk + Kq ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKs' : Ks ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X v hq hX hv
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  unfold boxM0
  by_cases hsq : χ ^ 2 = 1
  · by_cases hband : |v| ≤ 1 / 2
    · have h := hKs q χ X v hq hX hband
      linarith
    · have h := hb q χ X v hq0 hsq hX (le_of_lt (not_le.mp hband)) hv
      linarith
  · have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
      nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
    have h := hvk q χ (vkEulerCorr q * vkTwistConst q) X v hC1 hsq hX hv
      (fun hbig => plog_socket χ hsq hXe hbig)
    have hqd := plog_vk_qdebit q
    rw [← hKqdef] at hqd
    have hlq : Real.log q ≤ (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (q : ℝ)); linarith
    linarith

/-! ## §11 — THE WINDOW POLYNOMIAL IS A `dpoly`

The bridge that makes `MVCore2.dirichlet_poly_l2_mvt_final` applicable to `windowSum`.  The
point of the whole P2 page is in `winL2Mass`: the ℓ² coefficient mass of the window carries
NO `k`-power, whereas `HExit.norm_windowSum_le_mass`'s ℓ¹ mass carries `k^{1/(4 log L)}` (the
`(k/y)^{η}` of `FarStar`'s F-2b page) — and that `k`-power is exactly what pins the far arm's
truncation at `Tstar` instead of a poly-log height. -/

/-- **THE WINDOW COEFFICIENT.**  `windowSum`'s coefficient sequence at the line `Re s = σ`,
extended by `0` off the window `(y, X/y)` so it is indexed by `Finset.Icc 1 ⌈X/y⌉₊` — the
shape `L2MVT.dpoly` demands. -/
def winL2Coeff (g : ℕ → ℂ) (X y σ : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ then
    lambdaLin (restrictAbove y g) n / (((n : ℝ) ^ σ : ℝ) : ℂ)
  else 0

/-- `n^{σ+iτ} = n^σ·exp(i·τ·log n)` for `n ≥ 1` — the `cpow` split the `dpoly` shape needs.
(`Complex.cpow_def_of_ne_zero` + `Real.rpow_def_of_pos`, the `BallSup.div_cpow_eq_eIu`
pattern.) -/
private lemma natCpow_split {n : ℕ} (hn : 1 ≤ n) (σ τ : ℝ) :
    (n : ℂ) ^ ((σ : ℂ) + (τ : ℝ) * I)
      = (((n : ℝ) ^ σ : ℝ) : ℂ) * Complex.exp (I * (τ : ℂ) * (Real.log n : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Real.rpow_def_of_pos hnR,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The window index set sits inside `dpoly`'s index set. -/
private lemma window_subset_Icc (X y : ℝ) :
    Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ ⊆ Finset.Icc 1 ⌈X / y⌉₊ := by
  intro n hn
  rw [Finset.mem_Ioo] at hn
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- **P2 STONE 1 — `windowSum` IS A DIRICHLET POLYNOMIAL** (`windowSum_eq_dpoly`).  On the
vertical line `Re s = σ`,

  `windowSum g X y (σ + iτ) = dpoly ⌈X/y⌉₊ (winL2Coeff g X y σ) (−τ)`.

The sign flip is `windowSum`'s `1/n^s` against `dpoly`'s `n^{it}`; it is harmless downstream
because every consumer integrates over a SYMMETRIC `τ`-range. -/
theorem windowSum_eq_dpoly (g : ℕ → ℂ) (X y σ τ : ℝ) :
    windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)
      = dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) (-τ) := by
  unfold windowSum dpoly
  rw [← Finset.sum_subset (window_subset_Icc X y) (fun n _ hn => by
    unfold winL2Coeff; rw [if_neg hn]; ring)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : 1 ≤ n := by rw [Finset.mem_Ioo] at hn; omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hpow0 : (((n : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt (Real.rpow_pos_of_pos hnR σ)
  have hexp0 : Complex.exp (I * (τ : ℂ) * (Real.log n : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  unfold winL2Coeff
  rw [if_pos hn, natCpow_split hn1 σ τ]
  rw [show ((-τ : ℝ) : ℂ) = -(τ : ℂ) from by push_cast; ring]
  rw [show I * -(τ : ℂ) * (Real.log n : ℂ) = -(I * (τ : ℂ) * (Real.log n : ℂ)) from by ring,
    Complex.exp_neg]
  field_simp

/-- **THE ℓ² COEFFICIENT MASS OF THE WINDOW.**  `∑_{y<n<X/y} ‖Λ_ℓ(n)‖²/n^{2σ}` — the
quantity `dirichlet_poly_l2_mvt_final` charges for.  At the pin (`σ ≍ 1`, `y = L⁴`) this is
`≍ (log y)²/y = 16(log L)²/L⁴`: **no `k`-power at all**, against
`HExit.norm_windowSum_le_mass`'s ℓ¹ mass `≍ k^{1/(4 log L)}·L·log L`. -/
def winL2Mass (g : ℕ → ℂ) (X y σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ ^ 2 / ((n : ℝ) ^ σ) ^ 2

lemma winL2Mass_nonneg (g : ℕ → ℂ) (X y σ : ℝ) : 0 ≤ winL2Mass g X y σ :=
  Finset.sum_nonneg (fun n _ => by positivity)

/-- The `dpoly` ℓ² mass of `winL2Coeff` IS `winL2Mass` (the extension by `0` contributes
nothing). -/
theorem winL2Coeff_l2_eq (g : ℕ → ℂ) (X y σ : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌈X / y⌉₊, ‖winL2Coeff g X y σ n‖ ^ 2) = winL2Mass g X y σ := by
  unfold winL2Mass
  rw [← Finset.sum_subset (window_subset_Icc X y) (fun n _ hn => by
    unfold winL2Coeff; rw [if_neg hn]; simp)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : 1 ≤ n := by rw [Finset.mem_Ioo] at hn; omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hp0 : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnR σ
  unfold winL2Coeff
  rw [if_pos hn, norm_div, Complex.norm_real, Real.norm_of_nonneg hp0.le, div_pow]

/-- **P2 STONE 2 — THE MEAN VALUE AT THE WINDOW POLYNOMIAL** (`windowSum_l2_mvt`).
`MVCore2.dirichlet_poly_l2_mvt_final` transported through §11's identification:

  `∫_{−R}^{R} ‖windowSum g X y (σ + iτ)‖² dτ ≤ (2R + 20·⌈X/y⌉₊)·winL2Mass g X y σ`.

Unconditional (the Montgomery–Vaughan input is `MVCore2.mvHilbertUniform_holds`).  **The
`20·⌈X/y⌉₊` is ⟦THE N-TERM⟧** of the header: it is the uniform-spacing (`δ = 1/N`) Hilbert
constant, and it is what stops the `τ`-dyadic sum from reaching a poly-log truncation height
without the dyadic-in-`n` repair. -/
theorem windowSum_l2_mvt (g : ℕ → ℂ) (X y σ R : ℝ) :
    (∫ τ in (-R)..R, ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
      ≤ (2 * R + 20 * (⌈X / y⌉₊ : ℝ)) * winL2Mass g X y σ := by
  have hrw : (∫ τ in (-R)..R, ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
      = ∫ τ in (-R)..R, ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) τ‖ ^ 2 := by
    calc (∫ τ in (-R)..R, ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
        = ∫ τ in (-R)..R, ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) (-τ)‖ ^ 2 := by
          refine intervalIntegral.integral_congr (fun τ _ => ?_)
          rw [windowSum_eq_dpoly]
      _ = ∫ τ in (-R)..(R : ℝ), ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) τ‖ ^ 2 := by
          rw [intervalIntegral.integral_comp_neg
            (fun τ => ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) τ‖ ^ 2), neg_neg]
  rw [hrw, ← winL2Coeff_l2_eq g X y σ]
  exact dirichlet_poly_l2_mvt_final ⌈X / y⌉₊ (winL2Coeff g X y σ) R

/-! ## §12 — the far region's weighted ℓ² tails -/

/-- **THE `1/τ²`-WEIGHTED ℓ² TAIL** of the window polynomial beyond height `H`.  This is the
object that replaces `HExit.norm_windowSum_le_mass`'s ℓ¹ mass in the far arm's budget. -/
def winL2Tail (g : ℕ → ℂ) (X y σ H : ℝ) : ℝ :=
  ∫ τ in {τ : ℝ | H < |τ|}, ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2

/-- The far region translated to the centred one (`TruncFactor`'s private
`setIntegral_far_comp_sub`, re-derived — it is `private` there). -/
private lemma farL2_recentre (φ : ℝ → ℝ) (t₀ H : ℝ) :
    (∫ t in {t : ℝ | H < |t - t₀|}, φ (t - t₀)) = ∫ τ in {τ : ℝ | H < |τ|}, φ τ := by
  rw [← integral_indicator (measurableSet_farRegion t₀ H),
    ← integral_indicator (measurableSet_farAbs H)]
  rw [show (fun t : ℝ => Set.indicator {t : ℝ | H < |t - t₀|} (fun t => φ (t - t₀)) t)
        = (fun t : ℝ => Set.indicator {τ : ℝ | H < |τ|} φ (t - t₀)) from by
      funext t
      by_cases ht : t ∈ {t : ℝ | H < |t - t₀|}
      · have ht' : t - t₀ ∈ {τ : ℝ | H < |τ|} := ht
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      · have ht' : t - t₀ ∉ {τ : ℝ | H < |τ|} := ht
        rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']]
  exact integral_sub_right_eq_self (Set.indicator {τ : ℝ | H < |τ|} φ) t₀

/-- **P2 STONE 3 — THE FAR CROSS-INTEGRAL WITHOUT THE ℓ¹ MASSES**
(`crossKerFar_le_weighted_l2`).  `TruncFactor.crossKerFar_le_tail`'s replacement:

  `crossKerFar g X h y c₀ t₀ α β H ≤ ((X+h)^{c+1}/h)·(winL2Tail(c₀−β) + winL2Tail(c₀+β))`,
  `c = c₀ − α − β`,

with NO window mass of any kind on the right.  Three pointwise steps: the branch-2 kernel
bound `‖K(τ)‖ ≤ 2(X+h)^{c+1}/(h(c²+τ²)) ≤ 2(X+h)^{c+1}/(hτ²)` on the far region, the AM–GM
`‖W₋‖·‖W₊‖ ≤ (‖W₋‖² + ‖W₊‖²)/2` (no Cauchy–Schwarz needed — the two legs enter symmetrically),
and `farL2_recentre`.

The two integrability binders are the house conditional-assembly sockets: they are exactly
what a mean-value page for the tails discharges, and they are FALSE for no reason of
principle (the tails converge as soon as any `∫_{|τ|≤R}‖W‖² ≲ R + N` bound is available —
`windowSum_l2_mvt` is one).  They are stated rather than derived because deriving them is the
same dyadic work as bounding them, and the ⟦N-TERM REFUTATION⟧ shows that work needs the
dyadic-in-`n` split this file does not land. -/
theorem crossKerFar_le_weighted_l2 {g : ℕ → ℂ} {X h y c₀ t₀ α β H : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (hH : 0 < H)
    (hIm : IntegrableOn
      (fun τ : ℝ => ‖windowSum g X y (((c₀ - β : ℝ) : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2)
      {τ : ℝ | H < |τ|})
    (hIp : IntegrableOn
      (fun τ : ℝ => ‖windowSum g X y (((c₀ + β : ℝ) : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2)
      {τ : ℝ | H < |τ|}) :
    crossKerFar g X h y c₀ t₀ α β H
      ≤ (X + h) ^ (c₀ - α - β + 1) / h
          * (winL2Tail g X y (c₀ - β) H + winL2Tail g X y (c₀ + β) H) := by
  set c : ℝ := c₀ - α - β with hcdef
  have hXh : (0 : ℝ) < X + h := by linarith
  have hAmp : (0 : ℝ) < (X + h) ^ (c + 1) / h := by
    have := Real.rpow_pos_of_pos hXh (c + 1); positivity
  -- the far-region integrand, recentred
  have hrec : crossKerFar g X h y c₀ t₀ α β H
      = ∫ τ in {τ : ℝ | H < |τ|},
          ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) - (β : ℂ))‖
            * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) + (β : ℂ))‖
            * ‖hatKernel X h c τ‖ := by
    unfold crossKerFar
    exact farL2_recentre (fun τ =>
      ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) + (β : ℂ))‖
        * ‖hatKernel X h c τ‖) t₀ H
  -- the two legs' lines, in the `(σ : ℝ) + τ·I` normal form
  have hlineM : ∀ τ : ℝ, ((c₀ : ℂ) + (τ : ℝ) * I) - (β : ℂ)
      = ((c₀ - β : ℝ) : ℂ) + (τ : ℝ) * I := by intro τ; push_cast; ring
  have hlineP : ∀ τ : ℝ, ((c₀ : ℂ) + (τ : ℝ) * I) + (β : ℂ)
      = ((c₀ + β : ℝ) : ℂ) + (τ : ℝ) * I := by intro τ; push_cast; ring
  rw [hrec]
  have hdomInt : IntegrableOn
      (fun τ : ℝ => (X + h) ^ (c + 1) / h
        * (‖windowSum g X y (((c₀ - β : ℝ) : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2
            + ‖windowSum g X y (((c₀ + β : ℝ) : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2))
      {τ : ℝ | H < |τ|} := ((hIm.add hIp).const_mul _)
  have hsrcInt : IntegrableOn
      (fun τ : ℝ =>
        ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) + (β : ℂ))‖
          * ‖hatKernel X h c τ‖) {τ : ℝ | H < |τ|} := by
    have hI := crossKer_integrand_integrable (g := g) (X := X) (h := h) (y := y) (c₀ := c₀)
      (t₀ := (0 : ℝ)) (α := α) (β := β) hX hh hc
    simpa [hcdef] using hI.integrableOn
  refine le_trans (setIntegral_mono_on hsrcInt hdomInt (measurableSet_farAbs H)
    (fun τ hτ => ?_)) (le_of_eq ?_)
  · -- POINTWISE: branch-2 kernel + AM–GM
    simp only [Set.mem_setOf_eq] at hτ
    have hτne : τ ≠ 0 := by
      intro h0; rw [h0] at hτ; simp at hτ; linarith
    have hτ0 : (0 : ℝ) < τ ^ 2 := by positivity
    have hWmEq : ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) - (β : ℂ))‖
        = ‖windowSum g X y (((c₀ - β : ℝ) : ℂ) + (τ : ℝ) * I)‖ := by rw [hlineM τ]
    have hWpEq : ‖windowSum g X y (((c₀ : ℂ) + (τ : ℝ) * I) + (β : ℂ))‖
        = ‖windowSum g X y (((c₀ + β : ℝ) : ℂ) + (τ : ℝ) * I)‖ := by rw [hlineP τ]
    rw [hWmEq, hWpEq]
    set Wm := ‖windowSum g X y (((c₀ - β : ℝ) : ℂ) + (τ : ℝ) * I)‖ with hWmdef
    set Wp := ‖windowSum g X y (((c₀ + β : ℝ) : ℂ) + (τ : ℝ) * I)‖ with hWpdef
    have hWm0 : 0 ≤ Wm := norm_nonneg _
    have hWp0 : 0 ≤ Wp := norm_nonneg _
    have hker : ‖hatKernel X h c τ‖ ≤ 2 * (X + h) ^ (c + 1) / (h * τ ^ 2) := by
      refine (hatKernel_branch2 hX hh hc τ).trans ?_
      have hden : h * τ ^ 2 ≤ h * (c ^ 2 + τ ^ 2) := by nlinarith [sq_nonneg c, hh.le]
      have hnum : (0 : ℝ) ≤ 2 * (X + h) ^ (c + 1) := by
        have := Real.rpow_pos_of_pos hXh (c + 1); positivity
      exact div_le_div_of_nonneg_left hnum (by positivity) hden
    have hamgm : Wm * Wp ≤ (Wm ^ 2 + Wp ^ 2) / 2 := by nlinarith [sq_nonneg (Wm - Wp)]
    have hstep : Wm * Wp * ‖hatKernel X h c τ‖
        ≤ ((Wm ^ 2 + Wp ^ 2) / 2) * (2 * (X + h) ^ (c + 1) / (h * τ ^ 2)) :=
      mul_le_mul hamgm hker (norm_nonneg _) (by positivity)
    refine hstep.trans (le_of_eq ?_)
    field_simp
  · -- the constant factors out
    rw [integral_const_mul,
      integral_add hIm hIp]
    unfold winL2Tail
    ring

/-! ## §12 — THE BOX FLOOR AT THE MASKED PIECE, AND THE RE-CUT GATE

`box_floor_M0` (§10, free win w1) is stated at the ROW datum `λχ̄` on the whole contour box
`|v| ≤ 3X`.  The re-cut `T₀`-supplier reads it at the MASKED PIECE `λχ̄·g_𝒥`.  The transport
is `polylog_floor_M0_pieceDatum`'s VERBATIM, one coefficient down (`1/4 → 1/16`): the sum-side
rewrite through `CapFreeAssembly.pretDistSq_liouChi_eq` (an equality), then
`CofactorSupplier.pretDistSq_pieceDatum_ge` at factor `1` (the mask is `gxDatum` at `x = 0`),
with the Mertens debit absorbed into the floor's constant by `boxM0_add_debit`.

`box_floor_clears_gate_45` then composes the transported floor with the `n = 45` re-cut gate
`(1009/45000)·e` (`A2Wall.a2wall_gate_45`'s coefficient; the exponent arithmetic there is
EXACT, `1/45 − 1009/45000 = −1/5000`).  The margin is `1/16 − (1009/45000)·e = 0.00155008…`,
whence the threshold constant `700 < 645.1⁻¹`'s reciprocal.  This is the ONE statement the
re-cut supplier consumes; it is stated here rather than in `A2Wall` because the import runs
`FarL2 → A2Wall`, so the clearance arithmetic (`A2Wall.a2wall_box_clears_45`, two lines) is
re-run inline. -/

/-- The debit shifts `boxM0`'s constant additively (`plogM0_add_debit` / `cfbM0_add_debit`
at the box coefficient). -/
theorem boxM0_add_debit (K D : ℝ) (q : ℕ) (X : ℝ) :
    boxM0 (K + D) q X = boxM0 K q X - D := by
  unfold boxM0; ring

/-- **THE BOX FLOOR AT THE SUM-SIDE DATUM** (`box_floor_M0_liouChi`).  The
`polylog_floor_M0_liouChi` transport verbatim: `CapFreeAssembly.pretDistSq_liouChi_eq` is an
EQUALITY of distances, so nothing is spent. -/
theorem box_floor_M0_liouChi (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 3 * X →
        boxM0 K q X ≤ pretDistSq (liouChi χ) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := box_floor_M0 Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ X v hq hX hv
  rw [pretDistSq_liouChi_eq]
  exact hK q χ X v hq hX hv

/-- **THE BOX FLOOR AT THE MASKED PIECE** (`box_floor_M0_pieceDatum`).  For every finite
modulus range `Q` there is one `X`-free, `q`-free `K ≥ 0` with

  `boxM0 (K + D) q X ≤ 𝔻²(λχ̄·g_𝒥, n^{iv}; X)`

for every `q ≤ Q`, every `χ mod q`, every `X ≥ exp(exp 1)`, every box frequency `|v| ≤ 3X`
and every `D` dominating the mask's Mertens window mass — the same `D` the poly-log twin
`polylog_floor_M0_pieceDatum` pays, discharged in practice by
`CofactorSupplier.blockWindow_calibrated_debit_sum`.

NO threshold and NO margin: `box_floor_M0`'s three arms deliver `1/16` outright, and the mask
costs exactly the debit (factor `1`, `pretDistSq_pieceDatum_ge`). -/
theorem box_floor_M0_pieceDatum (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X v D : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 3 * X →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
        boxM0 (K + D) q X ≤ pretDistSq (pieceDatum χ 𝒥 Pseq Qseq) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := box_floor_M0_liouChi Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X v D hq hX hv hdebit
  have hfloor := hK q χ X v hq hX hv
  have htr := pretDistSq_pieceDatum_ge χ Pseq Qseq
    (fun p _ => le_of_eq (costwist_norm v p)) X 𝒥
  rw [boxM0_add_debit]
  linarith

/-- **THE BOX FLOOR CLEARS THE RE-CUT GATE, AT THE PIECE** (`box_floor_clears_gate_45`).
`A2Wall.a2wall_box_floor_clears_gate_45` composed with `box_floor_M0_pieceDatum`: with
`L := loglog X`, `ℓ := logloglog X` and the box floor's own debits at the mask,
`D₀ := (5/4)·ℓ + (3/4)·log q + q + (K + D)`,

  `700·D₀ ≤ L  ⟹  (1009/45000)·e·L ≤ 𝔻²(λχ̄·g_𝒥, n^{iv}; X)`   on `|v| ≤ 3X`.

The coefficient `(1009/45000)·e = 0.060950…` is exactly what `a2wall_gate_45` demands to make
the first exit summand decay at `δ = 1/5000` from the re-cut seam floor `(log X)^{1/45}`; the
box floor's `1/16 = 0.0625` pays it with margin `0.00155008…`, hence the threshold constant
`700`.  This is the statement the re-cut `T₀`-supplier consumes — floor, mask and gate in one
implication, with no band-strength (`7/30`, `1/4`) hypothesis anywhere. -/
theorem box_floor_clears_gate_45 (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X v D : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 3 * X →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      700 * ((5 / 4) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log q
              + (q : ℝ) + (K + D)) ≤ Real.log (Real.log X) →
        1009 / 45000 * Real.exp 1 * Real.log (Real.log X)
          ≤ pretDistSq (pieceDatum χ 𝒥 Pseq Qseq) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := box_floor_M0_pieceDatum Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X v D hq hX hv hdebit hthr
  have hfloor := hK q χ Pseq Qseq 𝒥 X v D hq hX hv hdebit
  obtain ⟨-, -, hLL, -⟩ := cff_scale_facts hX
  -- the margin: `(1009/45000)·e ≤ 1/16 − 1/700` (`A2Wall.a2wall_box_clears_45`)
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hmar : 1009 / 45000 * Real.exp 1 ≤ 1 / 16 - 1 / 700 := by linarith
  have hmul : 1009 / 45000 * Real.exp 1 * Real.log (Real.log X)
      ≤ (1 / 16 - 1 / 700) * Real.log (Real.log X) :=
    mul_le_mul_of_nonneg_right hmar (by linarith)
  have hbox : 1009 / 45000 * Real.exp 1 * Real.log (Real.log X) ≤ boxM0 (K + D) q X := by
    unfold boxM0
    linarith
  linarith

end Salt.MR
