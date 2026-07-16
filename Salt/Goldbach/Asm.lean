/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.KerrY2
import Salt.Goldbach.Close

/-!
# G-ASM §1 — the sym slot, fully discharged (`gold_band_hsym_full`)

Design: the G-ASM fork off `docs/exploration/pilot.md` (~18:40).  Close's trichotomy
(`gold_band_hsym_wide_at_op`) left the MIDDLE piece as the residual hypothesis `hmid`
(FLAG G-CLOSE-1); KerrY2's `gold_hmid_discharge` supplies it at its own existential
constant.  Because the two constants come from different pricers, the packaged form
cannot be fed directly (the Kc-max reconciliation, G-KERRY2's lock); this file REBUILDS
the trichotomy from the primitive suppliers at the unified
`Kc := max (max Kce 1) KcY`:

* VANISH  (`pieceM k' ≤ opY N`)  — `gold_band_sym_vanish`, grade `≥ 0`;
* COLLAPSE (`opY N < pieceN k'`) — `gold_band_wide_price_at_op` at `Kce`, lifted by
  `boxPriceKerr_mono`, then `gold_band_survsum_geoN_floored`;
* MIDDLE  (the straddle)         — `gold_hmid_discharge` at `KcY`, lifted monotonically.

`gold_band_hsym_slot_full` then feeds `Surv.gold_band_hsym_tail_discharge`, emitting the
terminal's `hsym` input (`goldPsymK ≤ Wband + BTsym`) at `Cgeo := 4^12·gboxConst`.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset Salt.Chen

namespace Salt.Goldbach

/-- The monotone lift of the per-survivor geo grade in `Kc` (the RHS is linear in `Kc`
with nonnegative coefficient). -/
private theorem hsym_grade_mono (N : ℕ) (S : ℝ) {Kc Kc' : ℝ} (hKK : Kc ≤ Kc')
    (cut : ℕ)
    (h : S ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (cut : ℝ) / (Real.log N) ^ 12) :
    S ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc' * (cut : ℝ) / (Real.log N) ^ 12 := by
  refine le_trans h ?_
  have hg : (0 : ℝ) ≤ (4 : ℝ) ^ 12 * gboxConst := by
    have := gboxConst_nonneg; positivity
  have hcut : (0 : ℝ) ≤ (cut : ℝ) := Nat.cast_nonneg _
  have hlog : (0 : ℝ) ≤ ((Real.log N) ^ 12)⁻¹ := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ hlog
  refine mul_le_mul_of_nonneg_right ?_ hcut
  exact mul_le_mul_of_nonneg_left hKK hg

set_option maxHeartbeats 800000 in
-- the trichotomy composes two 30+-hypothesis engines; the bump is preemptive
/-- **`gold_band_hsym_full`** — the sym-leg per-survivor geo grade with NO residual
hypothesis, at the unified `Kc`. -/
theorem gold_band_hsym_full : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (Q a Ps : ℕ) (ε₀ QR : ℝ) (Dlev D K : ℕ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
      (∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)) →
      ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
          (D : ℝ)
                * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ)
                    * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
              ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
            goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
              ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ)
                  / (Real.log N) ^ 12 := by
  obtain ⟨Kce, xe, hKce, hengine⟩ := gold_band_wide_price_at_op
  obtain ⟨xf, hfloored⟩ := gold_band_survsum_geoN_floored
  obtain ⟨KcY, xY, hKcY, hmid⟩ := gold_hmid_discharge
  refine ⟨max (max Kce 1) KcY, max (max xe xf) xY,
    le_trans (le_max_right Kce 1) (le_max_left _ _), ?_⟩
  intro N hN Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hDbnd hDband k' hk' k hk i hi hDwide
  have hxe : xe ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hxf : xf ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hxY : xY ≤ N := le_trans (le_max_right _ _) hN
  have hKc1 : (1 : ℝ) ≤ max (max Kce 1) KcY :=
    le_trans (le_max_right Kce 1) (le_max_left _ _)
  by_cases hvan : pieceM k' ≤ opY N
  · -- VANISH
    rw [gold_band_sym_vanish N Q a Ps ε₀ (QR * Dlev) 0 k' k i hvan]
    have := gboxConst_nonneg
    positivity
  · rw [not_le] at hvan
    by_cases hcol : opY N < pieceN k'
    · -- COLLAPSE: `max (opY N) (pieceN k') = pieceN k'` — the y-floor engine
      have hmaxc : max (opY N) (pieceN k') = pieceN k' := max_eq_right (le_of_lt hcol)
      have hi' : i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K := by rw [← hmaxc]; exact hi
      have hDge := hDband k hk
      have hd1 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => Q * d), 1 ≤ d := fun d hd => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hd
      have hcop2 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => Q * d), Nat.Coprime (crtClassG Q (d / Q) N a) d :=
        fun d hd => gold_crtClassG_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQNa hPsN hd
      have hDsetD : ∀ d ∈ ((Nat.divisors Ps).filter
          (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d), d ≤ D :=
        fun d hd => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hd
      have hbox := hengine N hxe (goldSymSub N ε₀ 0 k' i) k' D
        (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d))
        (fun m => crtClassG Q (m / Q) N a) (goldCut N k) (goldCut N (k + 1)) k i K
        hi' hcol hDge hDwide (gold_norm_goldSymSub_le_one N ε₀ 0 k' i) hd1 hcop2 hDsetD
      have hsurv_eq : goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
          = (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (goldSymSub N ε₀ 0 k' i) (blockPrimeInd (pieceN k'))
                  (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m
                  (goldCut N (k + 1))‖)
            + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                  (fun d => Q * d),
                ‖apDiscBilinCutoff (goldSymSub N ε₀ 0 k' i) (blockPrimeInd (pieceN k'))
                    (2 ^ (i + 1) - 1) (pieceM k') (crtClassG Q (m / Q) N a) m
                    (goldCut N k)‖) := by
        unfold goldSymSurvSum; rw [hmaxc]
      have hbox' : goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
          ≤ boxPriceKerr (max (max Kce 1) KcY) k' i := by
        rw [hsurv_eq]
        exact le_trans hbox
          (boxPriceKerr_mono (le_trans (le_max_left Kce 1) (le_max_left _ _)) k' i)
      exact hfloored N hxf k' k i K (max (max Kce 1) KcY)
        (goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i) hKc1 hi' hcol hbox'
    · -- MIDDLE: `pieceN k' ≤ opY N < pieceM k'` — KerrY2's discharge, lifted
      rw [not_lt] at hcol
      exact hsym_grade_mono N _ (le_max_right _ _) _
        (hmid N hxY Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hDbnd hDband
          k' hk' hcol hvan k hk i hi hDwide)

/-- **`gold_band_hsym_slot_full`** — the terminal's `hsym` input, no residual: the full
trichotomy fed to `Surv.gold_band_hsym_tail_discharge`. -/
theorem gold_band_hsym_slot_full : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (Q a Ps : ℕ) (ε₀ QR : ℝ) (Dlev D K : ℕ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      1 ≤ QR * Dlev → (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
      (∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)) →
      ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
        goldPsymK N K Q a Ps ε₀ (QR * Dlev) 0 k'
          ≤ 24 * ((4 : ℝ) ^ 12 * gboxConst) * Kc * (N : ℝ) / (Real.log N) ^ 12
            + ∑ k ∈ Finset.range (Nat.log 2 N + 1),
                ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
                  (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
                  goldBandBtailSlot D Q (QR * Dlev) k' i := by
  obtain ⟨Kc, x₁, hKc, hfull⟩ := gold_band_hsym_full
  refine ⟨Kc, max x₁ 1, hKc, ?_⟩
  intro N hN Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hb hDbnd hDband
  have hx₁ : x₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  exact gold_band_hsym_tail_discharge (K := K) ε₀ QR Dlev D hQPs hQNa hPsN hQ1 hb
    (by have := gboxConst_nonneg; positivity) (le_trans zero_le_one hKc) hN1
    (hfull N hx₁ Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hDbnd hDband)

end Salt.Goldbach
