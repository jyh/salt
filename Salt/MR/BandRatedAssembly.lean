import Salt.MR.VkMidSharp
import Salt.MR.BandRated
import Salt.MR.RbdSupply

/-!
# The assembled χ-floor with a RATED band branch (`BandRatedAssembly`)

QUEUE P2 item 6's residual **(a)**, worker-tier under the helm's 2026-08-26 ruling: *"a full
drop-in sibling of `capFreeFloor3_margin_all_chi_vt` (all `χ`, `|v| ≤ 3X`) composing this band
branch with the untouched bulk/VK branches."*

## What is and is not new here

`capFreeFloor3_margin_all_chi_vt` (`VkMidSharp.lean:505`) splits three ways and only one of the
three carries the ineffectivity:

* `χ² ≠ 1` → `chi_floor_vk_pointwise_sharp` — **effective** (Wave K).
* `χ² = 1`, `|v| > 1/2` → `chi_floor_real_bulk_sharp` — **effective** (Wave K).
* `χ² = 1`, `|v| ≤ 1/2` → `chi_floor_band_arm`, whose constant comes from
  `chi_Llower_band_uniform`, *"a bare induction-max over the characters of every modulus `q ≤ Q`"*
  with **no known growth rate in `Q`**.  This is the arm the arc calls the whole blocker.

This file swaps **only the third**.  The other two are consumed unchanged, from the same names, in
the same order.  ⛔ It is a SIBLING, never an edit: `capFreeFloor3_margin_all_chi_vt` is untouched
and stays the corpus's statement of record for the unrated route.

## The two visible costs, both already priced

1. **A scale gate rides in the statement.**  `margin_band_threshold_rated` carries
   `chi_Llower_real_of_L1`'s own gate `32·diskConst q / goldenL1 q ≤ log X`, and QUEUE item 6
   records it as *"CARRIED, NOT DISCHARGED — at the door's range it clears with enormous room, but
   that discharge belongs to the consumer"*.  It is threaded here, not discharged here.
2. **The threshold's bracket gains `bandConstQ Z δ q`.**  That is what *rated* means: the band
   constant is on the page and `O(log q)`, where the unrated arm's was an opaque `C(Q)`.

⚠️ **The coefficient trap this file walks past on purpose.**  Item 6 records that
`chi_floor_band_realclass_quarter` states `(1/4)·loglog X` while its coefficient-1 sibling hides
the `(3/4)` inside `B` — *"a consumer that reads the coefficient off that statement without
unfolding `B` over-credits the floor by a factor of four"*.  This file reads neither: it consumes
`margin_band_threshold_rated`, which already delivers the assembly's own `(1/32)·loglog X + 25 + D`
conclusion, so the `1/4` is spent inside that lemma and never crosses this boundary.
-/

namespace Salt.MR

open Finset Complex DirichletCharacter Salt.SW

/-- `27/2 ≤ diskConst q` for `1 ≤ q`.  Each of `√q`, `1 + log q` and `q` is `≥ 1` there, so the
head constant is the whole lower bound.  (Mathlib-adjacent to `diskConst_le`, which bounds the
other side; nothing in the corpus bounded this one below.) -/
theorem diskConst_ge_head {q : ℕ} (hq : 1 ≤ q) : 27 / 2 ≤ diskConst q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsqrt : (1 : ℝ) ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt hq1
    simpa using h
  have hlog : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have h1 : (1 : ℝ) ≤ Real.sqrt q * (1 + Real.log q) :=
    one_le_mul_of_one_le_of_one_le hsqrt (by linarith)
  have h2 : (1 : ℝ) ≤ Real.sqrt q * (1 + Real.log q) * (q : ℝ) :=
    one_le_mul_of_one_le_of_one_le h1 hq1
  unfold diskConst
  nlinarith [h2]

/-- **`bandConstQ` is nonnegative** whenever `1 ≤ Z`.  Its second branch alone already is: `log 2`
and `2·log 4 + (3/4)·log 2` are nonnegative, `−log (goldenL1 q) ≥ 0` because `goldenL1 q ≤ 1`, and
the remaining log has argument `≥ 16·1·1·(27/2)/1 = 216 ≥ 1`.  The `max` then carries it.

This is what lets the rated bracket be a STRENGTHENING of the unrated one, so a single threshold
hypothesis still implies the bulk and VK arms' own demands — the assembly law of
`CapFreeAssembly` §4, preserved rather than traded away for a second hypothesis. -/
theorem bandConstQ_nonneg {Z δ : ℝ} (hZ : 1 ≤ Z) (q : ℕ) [NeZero q] :
    0 ≤ bandConstQ Z δ q := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hg0 : 0 < goldenL1 q := goldenL1_pos q
  have hg1 : goldenL1 q ≤ 1 := goldenL1_le_one q
  have hglog : Real.log (goldenL1 q) ≤ 0 := Real.log_nonpos hg0.le hg1
  have hdisk : 27 / 2 ≤ diskConst q := diskConst_ge_head hq
  have hbig : (1 : ℝ) ≤ 16 * (q : ℝ) * Z * diskConst q / goldenL1 q := by
    rw [le_div_iff₀ hg0]
    -- `16·q·Z ≥ 16`, then multiply the `diskConst` head in on the left: two two-factor
    -- steps rather than one three-factor one, which is what the tactic could not see.
    have hqz : (16 : ℝ) ≤ 16 * (q : ℝ) * Z := by nlinarith [hq1, hZ]
    have hqz0 : (0 : ℝ) ≤ 16 * (q : ℝ) * Z := by linarith
    have hmul : 16 * (q : ℝ) * Z * (27 / 2) ≤ 16 * (q : ℝ) * Z * diskConst q :=
      mul_le_mul_of_nonneg_left hdisk hqz0
    have h216 : (216 : ℝ) ≤ 16 * (q : ℝ) * Z * (27 / 2) := by linarith
    linarith
  have hlogbig : (0 : ℝ) ≤ Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q) :=
    Real.log_nonneg hbig
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold bandConstQ
  refine le_trans ?_ (le_max_right _ _)
  linarith

/-- **THE ASSEMBLED χ-FLOOR WITH MARGIN, RATED BAND BRANCH** — QUEUE P2 item 6 residual (a).

A drop-in sibling of `capFreeFloor3_margin_all_chi_vt`: same conclusion, same range `|v| ≤ 3X`, all
`χ`.  Two differences, both in the hypotheses and both forced by the trade:

* the scale gate `32·diskConst q / goldenL1 q ≤ log X` (`chi_Llower_real_of_L1`'s own, carried);
* `bandConstQ Z δ q` inside the threshold bracket — the rated constant, `X`-free and `O(log q)`,
  standing where the unrated arm had an unrated `C(Q)`.

The existentials `Z`, `δ` come from `margin_band_threshold_rated`; both are `q`-free and `χ`-free,
which is the whole property the `K_vt` cushion needs. -/
theorem capFreeFloor3_margin_all_chi_vt_rated :
    ∃ Z δ K : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X D : ℝ),
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      32 * diskConst q / goldenL1 q ≤ Real.log X →
      40 * Real.log (Real.log (Real.log X))
          + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
              + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q
              + bandConstQ Z δ q + K + 25 + D)
        < Real.log (Real.log X) →
      ∀ v : ℝ, |v| ≤ 3 * X →
        (1 / 32) * Real.log (Real.log X) + 25 + D < pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Kvk, hvk⟩ := chi_floor_vk_pointwise_sharp
  obtain ⟨Kbulk, hbulk⟩ := chi_floor_real_bulk_sharp
  obtain ⟨Z, δ, Kband, hZ1, hδ, hband⟩ := margin_band_threshold_rated
  refine ⟨Z, δ, max 0 (max Kvk (max Kbulk Kband)), hZ1, hδ, le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kvk (max Kbulk Kband)) with hKdef
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKvk : Kvk ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbulk : Kbulk ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKband : Kband ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X D hX hD0 hgate hthr v hv
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hmcap : (0 : ℝ) ≤ mertensCap q := mertensCap_nonneg q
  have hC1 : (1 : ℝ) ≤ vkEulerCorr q * vkTwistConst q := by
    nlinarith [one_le_vkEulerCorr q, one_le_vkTwistConst (q := q)]
  have hvkD : (0 : ℝ) ≤ vkDebitConst (vkEulerCorr q * vkTwistConst q) :=
    vkDebitConst_nonneg hC1
  have hvkM : (0 : ℝ) ≤ vkMidDebitSharp q := vkMidDebitSharp_nonneg q
  have hbc : (0 : ℝ) ≤ bandConstQ Z δ q := bandConstQ_nonneg hZ1 q
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  by_cases hsq : χ ^ 2 = 1
  · by_cases hband2 : |v| ≤ 1 / 2
    · -- THE ONE BRANCH THAT CHANGED: the rated band floor, in place of `chi_floor_band_arm`.
      exact hband q χ X D hsq hX hD0 hgate (by linarith) v hband2
    · have hvbig : 1 / 2 ≤ |v| := le_of_lt (not_le.mp hband2)
      have h := hbulk q χ X v hq0 hsq hX hvbig hv
      linarith
  · have hψ : (χ ^ 2 : DirichletCharacter ℂ q) ≠ 1 := hsq
    have hsock : Real.exp (Real.exp 100) ≤ |v| →
        VkTwistUB (vkEulerCorr q * vkTwistConst q) (χ ^ 2) X (2 * v) := by
      intro hbig
      have h2v : Real.exp (Real.exp 100) ≤ |2 * v| := by
        have hle : |v| ≤ |2 * v| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          nlinarith [abs_nonneg v]
        linarith
      exact vkTwistUB_holds (χ ^ 2) hψ hXe h2v
    have h := hvk q χ (vkEulerCorr q * vkTwistConst q) X v hC1 hsq hX hv hsock
    linarith

/-! ## §2 — the rated constant over the arc range (QUEUE P2 item 6 residual (b), first link)

The rethread `_pieceDatum_vt → _arcDen → cofkL_capFreeFloor_at_socket` carries `K` SYMBOLICALLY,
which a `q`-dependent constant cannot be.  `bandConstQ Z δ q` is `O(log q)`, so on the arc range
`q ≤ arcDen 12 H = (log H)^12` it must be absorbed into `loglog H` exactly as `log q`,
`mertensCap q`, `vkDebitConst` and `vkMidDebitSharp` already are (`RbdSupply` §"the four
summands").  This is that fifth summand, and it is where *rated* pays: the unrated `C(Q)` had no
growth rate and could not have been absorbed at all.

⭐ SPEND NOTHING ON GRADE (the 08/26 standing instruction).  Every constant below is deliberately
generous — `q^{5/2} ≤ q³`, `diskConst q ≤ (81/2)q²`, `log q ≤ 12·loglog H` — because the consumer
budget clears any polynomial grade by hundreds of orders.  Sharpening `45` here buys nothing. -/

/-- The explicit `H`-free part of the arc-range bound on `bandConstQ`.  `Z`-dependent and
`δ`-dependent by construction: those are the two `q`-free, `χ`-free existentials
`margin_band_threshold_rated` produces, and keeping them visible is what makes the bound rated. -/
noncomputable def bandArcConst (Z δ : ℝ) : ℝ :=
  max (-Real.log δ)
    (Real.log 2 + 2 * Real.log 4 + (3 / 4) * Real.log 2
      - Real.log (Real.log ((3 + Real.sqrt 5) / 2))
      + (1 / 4) * Real.log (648 * Z / Real.log ((3 + Real.sqrt 5) / 2)))

/-- **THE FIFTH SUMMAND** (`bandConstQ_le_of_le_arcDen`) — the rated band constant absorbed into
`loglog H` over the major-arc denominator range, in the shape `RbdSupply`'s four siblings use. -/
theorem bandConstQ_le_of_le_arcDen {q H : ℕ} [NeZero q] {Z δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 < δ)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ)) (hq : (q : ℝ) ≤ arcDen 12 H) :
    bandConstQ Z δ q ≤ 48 * Real.log (Real.log (H : ℝ)) + bandArcConst Z δ := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqN : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hLH1 : (1 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := one_le_loglog_of_exp_le hH
  have hlogq : Real.log q ≤ 12 * Real.log (Real.log (H : ℝ)) := log_le_of_le_arcDen hH hq
  set c : ℝ := Real.log ((3 + Real.sqrt 5) / 2) with hcdef
  have hc0 : 0 < c := e4a_log_golden_pos
  -- `log (goldenL1 q) = log c − (5/2)·log q`
  have hrpow0 : (0 : ℝ) < (q : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hq0 _
  have hglog : Real.log (goldenL1 q) = c.log - (5 / 2) * Real.log q := by
    rw [goldenL1, Real.log_div (ne_of_gt hc0) (ne_of_gt hrpow0), Real.log_rpow hq0]
  -- `1 / goldenL1 q ≤ q³ / c`, via `q^{5/2} ≤ q³`
  have hrpow3 : (q : ℝ) ^ (5 / 2 : ℝ) ≤ (q : ℝ) ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (5 / 2 : ℝ) ≤ (3 : ℝ))
    rwa [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  -- the log-argument, bounded by `(648·Z/c)·q⁵`
  have hdisk : diskConst q ≤ 81 / 2 * (q : ℝ) ^ 2 := diskConst_le hqN
  have hdisk0 : (0 : ℝ) ≤ diskConst q := le_trans (by norm_num) (diskConst_ge_head hqN)
  have hg0 : 0 < goldenL1 q := goldenL1_pos q
  have hinv : 1 / goldenL1 q ≤ (q : ℝ) ^ (3 : ℕ) / c := by
    rw [goldenL1, one_div_div]
    gcongr
  have h16 : (0 : ℝ) ≤ 16 * (q : ℝ) * Z := by positivity
  have hnum : 16 * (q : ℝ) * Z * diskConst q ≤ 648 * Z * (q : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hdisk h16
    nlinarith [h]
  have hargle : 16 * (q : ℝ) * Z * diskConst q / goldenL1 q ≤ 648 * Z / c * (q : ℝ) ^ 6 := by
    rw [div_eq_mul_one_div]
    have hinv0 : (0 : ℝ) ≤ 1 / goldenL1 q := by positivity
    calc 16 * (q : ℝ) * Z * diskConst q * (1 / goldenL1 q)
        ≤ 648 * Z * (q : ℝ) ^ 3 * ((q : ℝ) ^ (3 : ℕ) / c) :=
          mul_le_mul hnum hinv hinv0 (by positivity)
      _ = 648 * Z / c * (q : ℝ) ^ 6 := by push_cast; ring
  have harg0 : (0 : ℝ) < 16 * (q : ℝ) * Z * diskConst q / goldenL1 q := by
    have : (0 : ℝ) < 27 / 2 := by norm_num
    have hd : (0 : ℝ) < diskConst q := lt_of_lt_of_le this (diskConst_ge_head hqN)
    positivity
  have hlogarg : Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q)
      ≤ Real.log (648 * Z / c) + 6 * Real.log q := by
    have hstep := Real.log_le_log harg0 hargle
    have hpos : (0 : ℝ) < 648 * Z / c := by positivity
    rwa [Real.log_mul (ne_of_gt hpos) (by positivity), Real.log_pow] at hstep
  -- assemble
  have hbranch2 : Real.log 2 - Real.log (goldenL1 q)
        + (2 * Real.log 4 + (3 / 4) * Real.log 2
          + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q))
      ≤ 48 * Real.log (Real.log (H : ℝ)) + bandArcConst Z δ := by
    have hb : bandArcConst Z δ ≥ Real.log 2 + 2 * Real.log 4 + (3 / 4) * Real.log 2
        - Real.log c + (1 / 4) * Real.log (648 * Z / c) := le_max_right _ _
    rw [hglog]
    linarith
  have hbranch1 : Real.log q - Real.log δ ≤ 48 * Real.log (Real.log (H : ℝ)) + bandArcConst Z δ := by
    have hb : bandArcConst Z δ ≥ -Real.log δ := le_max_left _ _
    linarith
  unfold bandConstQ
  exact max_le hbranch1 hbranch2

end Salt.MR
