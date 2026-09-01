/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Mathlib
import Salt.MR.A4FMidRange

/-!
# A4F S2 — the threshold family at θ = 3/4

The commissioning fold's structural finding: the far-branch mechanism carries an ADDITIVE
absolute constant `C` (Mertens window, exact tail, harmonic sums — each `O(1)` at every `X`),
so at `Y = exp((log X)^{3/4+ε'})` it yields `(1/8 − 1/(4π))·loglog X − (ε/2)·loglog X − C/2`
after `ε' := ε/(1 − 2/π)`, which meets the C-FREE target `(1/8 − 1/(4π) − ε)·loglog X` exactly
when `loglog X ≥ C/ε`.  The honest family, in the helm's given wording:

* **(i)** `mrtA4ii_far34_C` — the far theorem in the mechanism's NATIVE shape, `∃ C` outside,
  unconditional (the mid-range deliverable through the landed composer);
* **(ii)** `MRTLemmaA4iiFixed34T` — the THRESHOLD PRODUCER statement: `MRTLemmaA4iiFixed34`'s
  binders and hypotheses plus the threshold `C₀/ε ≤ loglog X`;
* **(iii)** the flags record: the C-free `MRTLemmaA4iiFixed34`'s far arm is STATEMENT-BLOCKED
  at small `X` by this mechanism (high-M arm landed, unaffected) — not refuted.

⚠️ **THE (ii) PRODUCER IS CONDITIONAL, AND THAT IS FLAGGED.**  `MRTLemmaA4iiFixed34`'s far
disjunct `(log X)^{1/16}/2 < |t − t₁|` has NO ceiling, so it spans the mid range AND the large
range `|t − t₁| > (log X)^{20}`; (i) reaches only the mid range.  The large arm is exactly the
Y-floor large Prop `MRTLargeRangeEquidistributionFixed` (open, priced at A4F-3).  Hence:
`mrtLemmaA4iiFixed34T_of_largeRangeFixed` produces (ii) from that Prop, and
`mrtLemmaA4iiFixed34T_mid` is the UNCONDITIONAL theorem on the mid range (the far disjunct
carrying its ceiling).  No statement was improvised; the wording is transcribed and the gap
is in the flags record.
-/

namespace Salt.MR

/-! ## (i) — the far theorem in the mechanism's native shape -/

/-- **S2 (i).**  The θ = 3/4 far theorem with the constant `C` OUTSIDE the quantifiers — the
mechanism's native shape; unconditional (the mid-range deliverable `mrt_mid_range_34`
through the landed Y-parametric composer). -/
theorem mrtA4ii_far34_C :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε' : ℝ),
      (∀ n, ‖f n‖ ≤ 1) → 0 < ε' → Real.exp 1 ≤ X →
      (Real.log X) ^ ((1 : ℝ) / 16) / 2 ≤ |t - t₁| → |t - t₁| ≤ (Real.log X) ^ (20 : ℕ) →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X →
        (1 / 2) * ((1 - 2 / Real.pi)
            * Real.log (Real.log X
                / Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε')))) - C)
          ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  obtain ⟨C, hC0, h34⟩ := mrt_mid_range_34
  refine ⟨C, hC0, ?_⟩
  intro f Pseq Qseq 𝒥 X t t₁ ε' hf hε hXe hlo hhi hmin
  have hs := h34 X (t - t₁) ε' hε hXe hlo hhi
  exact mrtA4ii_far_of_either_estimate f Pseq Qseq 𝒥 X _ t t₁ C hf hmin hs

/-! ## (ii) — the threshold producer -/

/-- **S2 (ii), the STATEMENT.**  `MRTLemmaA4iiFixed34`'s binders and hypotheses, plus the
threshold `C₀/ε ≤ loglog X` under which the C-free conclusion is produced.  The helm's
wording, transcribed; producers below. -/
def MRTLemmaA4iiFixed34T : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → Real.exp 1 ≤ X → |t| ≤ X → 0 < ε →
    |t₁| ≤ X → pretDistSq f (costwist t₁) X = mrtM f X →
    ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X
      ∨ (Real.log X) ^ ((1 : ℝ) / 16) / 2 < |t - t₁|) →
    C₀ / ε ≤ Real.log (Real.log X) →
      (1 / 8 - 1 / (4 * Real.pi) - ε) * Real.log (Real.log X)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X

/-- **The threshold arithmetic.**  From the far bound at `Y = exp((log X)^{3/4+ε'})` with
`ε' = ε/(1 − 2/π)`, the C-free target follows once `C/ε ≤ loglog X`:
`(1/2)·((1−2/π)·(1/4 − ε')·loglog X − C) = (1/8 − 1/(4π))·loglog X − (ε/2)·loglog X − C/2`. -/
lemma far34_threshold_close {X D C ε : ℝ} (hX1 : 1 ≤ Real.log X) (hε : 0 < ε)
    (hthr : C / ε ≤ Real.log (Real.log X))
    (hfar : (1 / 2) * ((1 - 2 / Real.pi)
        * Real.log (Real.log X
            / Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi)))))
        - C) ≤ D) :
    (1 / 8 - 1 / (4 * Real.pi) - ε) * Real.log (Real.log X) ≤ D := by
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπpos : 0 < Real.pi := by linarith
  have h2π : 2 / Real.pi < 1 := by rw [div_lt_one hπpos]; linarith
  have h12 : 0 < 1 - 2 / Real.pi := by linarith
  have hlogXpos : 0 < Real.log X := by linarith
  have hlogY : Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi))))
      = (Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi)) := Real.log_exp _
  have hratio : Real.log (Real.log X / (Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi)))
      = (1 - (3 / 4 + ε / (1 - 2 / Real.pi))) * Real.log (Real.log X) := by
    rw [Real.log_div hlogXpos.ne' (Real.rpow_pos_of_pos hlogXpos _).ne',
      Real.log_rpow hlogXpos]
    ring
  rw [hlogY, hratio] at hfar
  have hthr' : C ≤ ε * Real.log (Real.log X) := by
    rw [div_le_iff₀ hε] at hthr; linarith [hthr]
  have hkey : (1 / 2) * ((1 - 2 / Real.pi)
      * ((1 - (3 / 4 + ε / (1 - 2 / Real.pi))) * Real.log (Real.log X)) - C)
      = (1 / 8 - 1 / (4 * Real.pi)) * Real.log (Real.log X)
        - (ε / 2) * Real.log (Real.log X) - C / 2 := by
    have h12ne : (1 - 2 / Real.pi) ≠ 0 := h12.ne'
    have hs : (1 - 2 / Real.pi) * (ε / (1 - 2 / Real.pi)) = ε := by
      field_simp
      exact div_self (sub_pos.mpr (by linarith : (2 : ℝ) < Real.pi)).ne'
    calc (1 / 2) * ((1 - 2 / Real.pi)
          * ((1 - (3 / 4 + ε / (1 - 2 / Real.pi))) * Real.log (Real.log X)) - C)
        = (1 / 2) * ((1 - 2 / Real.pi) * (1 / 4) * Real.log (Real.log X)
            - ((1 - 2 / Real.pi) * (ε / (1 - 2 / Real.pi))) * Real.log (Real.log X) - C) := by
          ring
      _ = (1 / 2) * ((1 - 2 / Real.pi) * (1 / 4) * Real.log (Real.log X)
            - ε * Real.log (Real.log X) - C) := by rw [hs]
      _ = (1 / 8 - 1 / (4 * Real.pi)) * Real.log (Real.log X)
            - (ε / 2) * Real.log (Real.log X) - C / 2 := by
          have hπne : Real.pi ≠ 0 := hπpos.ne'
          field_simp
          ring
  rw [hkey] at hfar
  linarith [hfar, hthr']

/-- **S2 (ii), PRODUCED — conditionally on the Y-floor large Prop.**  The high-M arm is the
landed `mrtA4ii_high_M_target34`; the far arm splits at `(log X)^{20}`: the mid range through
(i), the large range through `MRTLargeRangeEquidistributionFixed` and the landed composer;
both close by the threshold arithmetic with `C₀ = max` of the two constants. -/
theorem mrtLemmaA4iiFixed34T_of_largeRangeFixed (hL : MRTLargeRangeEquidistributionFixed) :
    MRTLemmaA4iiFixed34T := by
  obtain ⟨C₁, hC₁0, hfar⟩ := mrtA4ii_far34_C
  obtain ⟨C₂, hC₂0, hlarge⟩ := hL
  refine ⟨max C₁ C₂, le_trans hC₁0 (le_max_left _ _), ?_⟩
  intro f Pseq Qseq 𝒥 X t t₁ ε hf hXe htX hε ht₁X hmin harm hthr
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogX1 : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hXe
  rcases harm with hM | hfarhyp
  · exact mrtA4ii_high_M_target34 f Pseq Qseq 𝒥 X t ε hf hXe htX hε hM
  · have hmin' : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X := by
      rw [hmin]; exact mrtM_le f hXpos.le htX
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h12 : 0 < 1 - 2 / Real.pi := by
      have : 2 / Real.pi < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have hε'pos : 0 < ε / (1 - 2 / Real.pi) := div_pos hε h12
    have hthr₁ : C₁ / ε ≤ Real.log (Real.log X) :=
      le_trans (div_le_div_of_nonneg_right (le_max_left _ _) hε.le) hthr
    have hthr₂ : C₂ / ε ≤ Real.log (Real.log X) :=
      le_trans (div_le_div_of_nonneg_right (le_max_right _ _) hε.le) hthr
    rcases le_or_gt |t - t₁| ((Real.log X) ^ (20 : ℕ)) with hmid | hlarge_range
    · have h := hfar f Pseq Qseq 𝒥 X t t₁ (ε / (1 - 2 / Real.pi)) hf hε'pos hXe
        hfarhyp.le hmid hmin'
      exact far34_threshold_close hlogX1 hε hthr₁ h
    · have hfloor : (Real.log X) ^ ((2 : ℝ) / 3)
          ≤ Real.log (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi)))) := by
        rw [Real.log_exp]
        exact Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)
      have ht := abs_le.mp htX
      have ht₁ := abs_le.mp ht₁X
      have hu2X : |t - t₁| ≤ 2 * X := abs_le.mpr ⟨by linarith, by linarith⟩
      have hb := hlarge X (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi))))
        (t - t₁) hXe hu2X hlarge_range hfloor
      have h := mrtA4ii_far_of_either_estimate f Pseq Qseq 𝒥 X
        (Real.exp ((Real.log X) ^ ((3 : ℝ) / 4 + ε / (1 - 2 / Real.pi)))) t t₁ C₂ hf hmin' hb
      exact far34_threshold_close hlogX1 hε hthr₂ h

/-- **S2 (ii) on the MID RANGE, UNCONDITIONAL.**  The threshold producer with the far
disjunct carrying its ceiling `|t − t₁| ≤ (log X)^{20}` — everything the mechanism proves
today with no hypothesis left. -/
theorem mrtLemmaA4iiFixed34T_mid :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ ε : ℝ),
      (∀ n, ‖f n‖ ≤ 1) → Real.exp 1 ≤ X → |t| ≤ X → 0 < ε →
      |t₁| ≤ X → pretDistSq f (costwist t₁) X = mrtM f X →
      ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X
        ∨ ((Real.log X) ^ ((1 : ℝ) / 16) / 2 < |t - t₁| ∧ |t - t₁| ≤ (Real.log X) ^ (20 : ℕ))) →
      C₀ / ε ≤ Real.log (Real.log X) →
        (1 / 8 - 1 / (4 * Real.pi) - ε) * Real.log (Real.log X)
          ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X := by
  obtain ⟨C₁, hC₁0, hfar⟩ := mrtA4ii_far34_C
  refine ⟨C₁, hC₁0, ?_⟩
  intro f Pseq Qseq 𝒥 X t t₁ ε hf hXe htX hε ht₁X hmin harm hthr
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogX1 : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hXe
  rcases harm with hM | ⟨hlo, hhi⟩
  · exact mrtA4ii_high_M_target34 f Pseq Qseq 𝒥 X t ε hf hXe htX hε hM
  · have hmin' : pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist t) X := by
      rw [hmin]; exact mrtM_le f hXpos.le htX
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h12 : 0 < 1 - 2 / Real.pi := by
      have : 2 / Real.pi < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have hε'pos : 0 < ε / (1 - 2 / Real.pi) := div_pos hε h12
    have h := hfar f Pseq Qseq 𝒥 X t t₁ (ε / (1 - 2 / Real.pi)) hf hε'pos hXe hlo.le hhi hmin'
    exact far34_threshold_close hlogX1 hε hthr h

end Salt.MR
