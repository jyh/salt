/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2Prime

/-!
# ⟦R3-A — THE A3 MIDDLE⟧: the primed row thread (`A3Middle`)

Design provenance: `docs/exploration/knot2-closure-freeze-0730.md`, stage **A3 — the numeral
re-thread**; ⟦R1⟧'s own fence (`flags.md` 2026-07-30 17:24): *"THE A3 MIDDLE un-threaded
(`seam_row_number' → capfree' → a2Mrow' → thm_a2'_of_rows'`) — mechanical, both suppliers
minted."*

⟦R1⟧ minted `M4RowMR.sum_lemma12RowsMR_priced_calibratedK2'` / `_end'`: the four-row exit
whose bracket carries the `X_d`-FREE `24/𝒫ⱼ` in place of `16·log₂(2X_d)/𝒫ⱼ`.  This file
carries that bracket up the CROSSING chain — the `3X`-minted strict/fused arm that
`ThmA2Rows.a2Rows_of_capfree3_end` walks — to `ThmA2Prime.a2Mrow'`, so that the JOIN's
`hrows` binder has a supplier.

## ⚠ THE DIRECTION, again

The primed bracket is SMALLER, so each primed row theorem is STRONGER than its landed
sibling and **cannot be derived from it**.  Every step below re-runs the landed proof
against the primed pricer; not one of them applies `a2RowsSum'_le_a2RowsSum`.  That is what
"no shortcut exists" means in the kernel.

## The one hypothesis that moves

`sum_lemma12RowsMR_priced_calibratedK2'`'s only new demand is the census's `4 ≤ P` floor,
stated as `2 ≤ A`.  On this chain it is FREE twice over: `CalFrameK.A_floor` is `24 ≤ A`,
and at the door `Adoor M ≥ 2^36`.  So the primed row theorems below carry the landed
hypothesis lists BYTE FOR BYTE — the `2 ≤ A` is read off the frame, never asked for.

## Contents

* §1 the weighting gates (private copies — `ThmA2Rows`'s are module-private);
* §2 `seam_row_number_nocap3_end'` — the socketed strict/fused row at the primed bracket;
* §3 `seam_row_number_capfree3_end'` — its cap-free instance at `t₁ := 0`, `S := 0`;
* §4 `a2Rows_of_capfree3_end'` — **THE A3 EXIT (strict/fused)**: the door's `hrows` supplier
  at `a2Mrow'`;
* §5–§7 the same three steps on the CLOSED-window arm — `seam_row_number_nocap3'`,
  `seam_row_number_capfree3'`, `a2Rows_of_capfree3'` — which is what
  `M4MeanSq.m4_meansq_per_chi_gen` consumes.

Additive: no landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

/-! ## §1 — the weighting gates, re-minted

`ThmA2Rows`'s §1 lemmas are `private` to that module.  The four numerals `9`/`244`/`3`/`3/2`
and the four weighing steps are reproduced here verbatim (same statements, same proofs), plus
the `a2RowsSum'` nonnegativity the primed slot needs. -/

/-- `ThmA2Rows.a2_weight_gates`, re-minted: with `w := (X/h)/T`, `0 ≤ w ≤ 1` and the four
`Tann`-linear factors weigh in at `9`, `244`, `3`, `3/2`. -/
private lemma a3_weight_gates {X h T Xd Q1 : ℝ} (hh4 : 4 ≤ h) (hX0 : 0 < X)
    (hT : X / h ≤ T) (hXd : X ≤ 4 * Xd) (hQ1 : Q1 ≤ h) (hQ10 : 0 ≤ Q1) :
    0 ≤ X / h / T ∧ X / h / T ≤ 1 ∧
      X / h / T * (2 * T * Q1 / Xd + 1) ≤ 9 ∧
      X / h / T * (2 * (2 * T) / Xd + 240) ≤ 244 ∧
      X / h / T * (2 * T / Xd + 1) ≤ 3 ∧
      X / h / T * (2 * T / X + 1) ≤ 3 / 2 := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hu0 : (0 : ℝ) < X / h := div_pos hX0 hh0
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hu0 hT
  have hXd0 : (0 : ℝ) < Xd := by linarith
  have hw0 : (0 : ℝ) ≤ X / h / T := le_of_lt (div_pos hu0 hT0)
  have hw1 : X / h / T ≤ 1 := (div_le_one hT0).mpr hT
  have hratio : X / h / Xd ≤ 4 / h := by
    rw [div_div, div_le_div_iff₀ (by positivity) hh0]
    nlinarith
  have hr0 : (0 : ℝ) ≤ X / h / Xd := le_of_lt (div_pos hu0 hXd0)
  refine ⟨hw0, hw1, ?_, ?_, ?_, ?_⟩
  · have hid : X / h / T * (2 * T * Q1 / Xd + 1) = 2 * Q1 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * Q1 * (X / h / Xd) ≤ 8 := by
      have hstep : 2 * Q1 * (X / h / Xd) ≤ 2 * Q1 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by linarith)
      have hval : 2 * Q1 * (4 / h) ≤ 8 := by
        rw [show 2 * Q1 * (4 / h) = 8 * Q1 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * (2 * T) / Xd + 240)
        = 4 * (X / h / Xd) + 240 * (X / h / T) := by
      field_simp; ring
    have h16 : 4 * (X / h / Xd) ≤ 4 := by
      have hstep : 4 * (X / h / Xd) ≤ 4 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 4 * (4 / h) ≤ 4 := by
        rw [show 4 * (4 / h) = 16 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / Xd + 1) = 2 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * (X / h / Xd) ≤ 2 := by
      have hstep : 2 * (X / h / Xd) ≤ 2 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 2 * (4 / h) ≤ 2 := by
        rw [show 2 * (4 / h) = 8 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / X + 1) = 2 / h + X / h / T := by
      field_simp
    have h2 : 2 / h ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hh0 (by norm_num)]
      linarith
    rw [hid]; linarith

/-- `ThmA2Rows.a2_row_weigh`, re-minted. -/
private lemma a3_row_weigh {w A B C D a b c d : ℝ}
    (hA : w * A ≤ a) (hB : w * B ≤ b) (hC : w * C ≤ c) (hD : w * D ≤ d) :
    w * (A + B + C + D) ≤ a + b + c + d := by
  have h : w * (A + B + C + D) = w * A + w * B + w * C + w * D := by ring
  rw [h]; linarith

/-- `ThmA2Rows.a2_level1_weigh`, re-minted. -/
private lemma a3_level1_weigh {w Hq Lq R Pq Br Z : ℝ}
    (hkey : ∀ R' : ℝ, 0 ≤ R' → 2 * (Hq * Lq + 1) * R' * Pq * Br ≤ 5280 * R' * Z)
    (hR0 : 0 ≤ w * R) (hR9 : w * R ≤ 9) (hZ0 : 0 ≤ Z) :
    w * (2 * (Hq * Lq + 1) * R * Pq * Br) ≤ 47520 * Z := by
  have hid : w * (2 * (Hq * Lq + 1) * R * Pq * Br)
      = 2 * (Hq * Lq + 1) * (w * R) * Pq * Br := by ring
  rw [hid]
  refine le_trans (hkey (w * R) hR0) ?_
  nlinarith [mul_nonneg hZ0 (by linarith : (0 : ℝ) ≤ 9 - w * R)]

/-- `ThmA2Rows.a2_term2_weigh`, re-minted: `1536·244 = 374784`. -/
private lemma a3_term2_weigh {w Cs R Y : ℝ} (hCs : 0 ≤ Cs) (hY : 0 ≤ Y) (hR : w * R ≤ 244) :
    w * (1536 * Cs * Real.exp 3 * R * Y) ≤ 374784 * Cs * Real.exp 3 * Y := by
  have hid : w * (1536 * Cs * Real.exp 3 * R * Y)
      = 1536 * Cs * Real.exp 3 * Y * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 1536 * Cs * Real.exp 3 * Y := by positivity
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR h0]

/-- `ThmA2Rows.a2_term3_weigh_mr`, re-minted: `960·3 = 2880 ≤ 5760`. -/
private lemma a3_term3_weigh_mr {w R S : ℝ} (hS : 0 ≤ S) (hR : w * R ≤ 3) :
    w * (960 * R * S) ≤ 5760 * S := by
  have hid : w * (960 * R * S) = 960 * S * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 960) hS)]

/-- `ThmA2Rows.a2_term4_weigh`, re-minted: `2·(3/2) = 3`. -/
private lemma a3_term4_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3 / 2) :
    w * (2 * (R * Z)) ≤ 3 * Z := by
  have hid : w * (2 * (R * Z)) = 2 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * Z)]

/-- `ThmA2.a2RowsSum'` is a sum of nonnegative terms — `ThmA2Rows.a2RowsSum_nonneg`'s twin,
and STRICTLY easier: the `p²` slot is the constant `24/𝒫ⱼ`, so the `log₂(2X_d) ≥ 0` step of
the landed proof disappears. -/
private lemma a2RowsSum'_nonneg {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    0 ≤ a2RowsSum' M Xd := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hH1 : (2 : ℝ) ≤ H1door M := H1door_two hM
  unfold a2RowsSum'
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH (H1door M) j := by
    rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) := by
    have h : 1 ≤ calP (Adoor M) (3072 * M) j := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ)
      / calH (H1door M) j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 24 / ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) :=
    div_nonneg (by norm_num) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

/-! ## §2 — THE SOCKETED ROW AT THE PRIMED BRACKET -/

set_option maxHeartbeats 1000000 in
-- the same fuse as `CapFreeArm3.seam_row_number_nocap3_end`, at ⟦R1⟧'s pricer
/-- **THE SOCKETED SEAM ROW AS ONE NUMBER — STRICT/FUSED, R1**
(`seam_row_number_nocap3_end'`).  `CapFreeArm3.seam_row_number_nocap3_end` with its
`Σ_j lemma12RowsMR_end` priced by `M4RowMR.sum_lemma12RowsMR_priced_calibratedK2_end'`: the
bracket's `p²` slot is the `X_d`-FREE constant `24/𝒫ⱼ`.

The hypothesis list is the landed one BYTE FOR BYTE — the pricer's `2 ≤ A` is read off
`CalFrameK.A_floor` (`24 ≤ A`), exactly as the landed proof reads `1 ≤ A` off it. -/
theorem seam_row_number_nocap3_end' :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ)
              * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 24 / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hseam⟩ := seam_row_calibratedK_nocap3_end
  obtain ⟨C, hC, hK2⟩ := sum_lemma12RowsMR_priced_calibratedK2_end'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE ONE MOVED READ⟧ `2 ≤ A`, from the frame's own `24 ≤ A`
  have hA2 : 2 ≤ A := le_trans (by norm_num) hF.A_floor
  have hG1 : 1 ≤ G := hF.one_le_G
  have hM1 : 1 ≤ M := hF.one_le_M
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd1
  have hT0 : (0 : ℝ) ≤ Tann := by linarith
  have hH1two : (2 : ℝ) ≤ H1 := hF.H1_two
  -- ⟦THE BRIDGE⟧ `X_d ≤ X`, from the junction's own two binders
  have hXdX : (Xd : ℝ) ≤ X := by
    have h2 : (2 : ℝ) * (Xd : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNXd
    linarith
  have hJdef : Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) := by
    have hlog : Real.log (Xd : ℝ) ≤ Real.log X := Real.log_le_log hXd0 hXdX
    calc Real.log ((calQK A G M Jb : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (Xd : ℝ)) := hQXd
      _ ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlog
      _ = (Real.log X) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hseaminst := hseam c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hasupp
  have hK2inst := hK2 A G M Jb N Xd H1 Tann a bfam c hA2 hG1 hM1 hXd1 hNXd hT0 hH1two hN4
    hreg hXdbig hdom ha1 hbf1 hc1 hasupp
  exact hseaminst.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2inst)) le_rfl)

/-! ## §3 — THE CAP-FREE ARM AT THE PRIMED BRACKET -/

set_option maxHeartbeats 1000000 in
-- one application of `seam_row_number_nocap3_end'`, at `t₁ := 0`, `S := 0`
/-- **THE CAP-FREE ARM AT THE `3X` BOX — STRICT/FUSED, R1** (`seam_row_number_capfree3_end'`).
`CapFreeArm3.seam_row_number_capfree3_end`'s twin over §2: the ball binder comes from
`CapFreeArm.ball_leg_vacuous_at_zero` at `S := 0`, datum-free, exactly as in the landed
proof. -/
theorem seam_row_number_capfree3_end' :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad 0 Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ)
              * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 24 / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hnum⟩ := seam_row_number_nocap3_end'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦S8⟧ the ball binder, from the emptiness at the origin, at `S := 0`
  have hSup := ball_leg_vacuous_at_zero (N := N) (a := a) (T := Tann)
    (show (1 : ℝ) < Real.log X by linarith)
  have h := hnum c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann 0 δ' V VJ L η Cb Rrad Rbar ε EP2 E 0
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  exact h.trans (le_of_eq (by ring))

/-! ## §4 — THE A3 EXIT: the `hrows` supplier at `a2Mrow'` -/

set_option maxHeartbeats 1000000 in
-- one predicate-blind application of §3 at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY AT THE `3X` MINT — STRICT/FUSED, R1**
(`a2Rows_of_capfree3_end'`) — **THE A3 MIDDLE'S EXIT**.
`ThmA2Rows.a2Rows_of_capfree3_end`'s twin over §3, landing at `ThmA2Prime.a2Mrow'`.

The hypothesis list, the weighting arithmetic and the four numerals `9`/`244`/`3`/`3/2` are
the landed theorem's verbatim; the ONLY change is the object the third weighing step lands
in — `a2RowsSum'` in place of `a2RowsSum`, which `a3_term3_weigh_mr` is blind to (it prices
`960·R·S ≤ 5760·S` for ANY nonnegative `S`).

This is the supplier `ThmA2Prime.thm_a2'_of_rows_pool'`'s `hrows` binder asks for, and it is
the only one: the primed slot admits no landed-form row. -/
theorem a2Rows_of_capfree3_end' :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow' Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ :=
    seam_row_number_capfree3_end'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint, at the PRIMED bracket⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (Adoor M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a3_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum' M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum'_nonneg hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow'
  refine a3_row_weigh ?_ ?_ ?_ ?_
  · exact a3_level1_weigh (fun R' hR' => level1_term_door_decays hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a3_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a3_term3_weigh_mr hRS0 hg3
  · exact a3_term4_weigh hZ0 hg32

/-! ## §5 — THE CLOSED-WINDOW ARM AT THE PRIMED BRACKET

§2–§4 carried ⟦R1⟧'s bracket up the STRICT/FUSED arm (the door's half-open cut).  §5–§7 do
the same for the CLOSED-window arm `X_d ≤ p·m` — the one `ThmA2Rows.a2Rows_of_capfree3` and
hence `M4MeanSq.m4_meansq_per_chi_gen` walk.  Same three steps, same one moved read. -/
set_option maxHeartbeats 1000000 in
-- the same fuse as `CapFreeArm3.seam_row_number_nocap3`, at ⟦R1⟧'s pricer
/-- **THE SOCKETED SEAM ROW AS ONE NUMBER — R1** (`seam_row_number_nocap3'`).
`CapFreeArm3.seam_row_number_nocap3` with its `Σ_j lemma12RowsMR` priced by
`M4RowMR.sum_lemma12RowsMR_priced_calibratedK2'`: the bracket's `p²` slot is the `X_d`-FREE
constant `24/𝒫ⱼ`.  This is the CLOSED-window arm — the one
`ThmA2Rows.a2Rows_of_capfree3` (hence `M4MeanSq`'s capstone) walks; §2/§3 above are its
strict/fused siblings.

The hypothesis list is the landed one BYTE FOR BYTE: the pricer's `2 ≤ A` is read off
`CalFrameK.A_floor` (`24 ≤ A`), where the landed proof reads `1 ≤ A`. -/
theorem seam_row_number_nocap3' :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad t₁ Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ)
              * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 24 / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hseam⟩ := seam_row_calibratedK_nocap3
  obtain ⟨C, hC, hK2⟩ := sum_lemma12RowsMR_priced_calibratedK2'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  have hA : 2 ≤ A := le_trans (by norm_num) hF.A_floor
  have hG1 : 1 ≤ G := hF.one_le_G
  have hM1 : 1 ≤ M := hF.one_le_M
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd1
  have hT0 : (0 : ℝ) ≤ Tann := by linarith
  have hH1two : (2 : ℝ) ≤ H1 := hF.H1_two
  -- ⟦THE BRIDGE⟧ `X_d ≤ X`, from the junction's own two binders
  have hXdX : (Xd : ℝ) ≤ X := by
    have h2 : (2 : ℝ) * (Xd : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNXd
    linarith
  have hJdef : Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) := by
    have hlog : Real.log (Xd : ℝ) ≤ Real.log X := Real.log_le_log hXd0 hXdX
    calc Real.log ((calQK A G M Jb : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (Xd : ℝ)) := hQXd
      _ ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlog
      _ = (Real.log X) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hseaminst := hseam c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad Rbar ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hasupp
  have hK2inst := hK2 A G M Jb N Xd H1 Tann a bfam c hA hG1 hM1 hXd1 hNXd hT0 hH1two hN4
    hreg hXdbig hdom ha1 hbf1 hc1 hasupp
  exact hseaminst.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2inst)) le_rfl)

/-! ## §6 — THE CLOSED-WINDOW CAP-FREE ARM -/
set_option maxHeartbeats 1000000 in
-- one application of `seam_row_number_nocap3'`, at `t₁ := 0`, `S := 0`
/-- **THE CAP-FREE ARM AT THE `3X` BOX — R1** (`seam_row_number_capfree3'`).
`CapFreeArm3.seam_row_number_capfree3`'s twin over §5: the ball binder comes from
`CapFreeArm.ball_leg_vacuous_at_zero` at `t₁ := 0`, `S := 0`, datum-free, exactly as in the
landed proof. -/
theorem seam_row_number_capfree3' :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the ball's centre, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q Tann Rrad 0 Rbar b →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a b cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ)
              * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 24 / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hnum⟩ := seam_row_number_nocap3'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann δ' V VJ L η Cb Rrad Rbar ε EP2 E
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦S8⟧ the ball binder, from the emptiness at the origin, at `S := 0`
  have hSup := ball_leg_vacuous_at_zero (N := N) (a := a) (T := Tann)
    (show (1 : ℝ) < Real.log X by linarith)
  have h := hnum c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann 0 δ' V VJ L η Cb Rrad Rbar ε EP2 E 0
    hF hH2 hX0 hXe hLXe hL4 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade hsockR
    hblk hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp
  exact h.trans (le_of_eq (by ring))

/-! ## §7 — THE CLOSED-WINDOW A3 EXIT -/
set_option maxHeartbeats 1000000 in
-- one predicate-blind application of ⟦R1⟧'s `3X`-minted cap-free row at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY AT THE `3X` MINT — R1** (`a2Rows_of_capfree3'`) —
**THE A3 MIDDLE'S CLOSED-WINDOW EXIT**.  `ThmA2Rows.a2Rows_of_capfree3`'s twin over §6,
landing at `ThmA2Prime.a2Mrow'`.

This is the arm `M4MeanSq.m4_meansq_per_chi_gen` consumes (its coefficient binder carries the
CLOSED window `X_d ≤ p·m`), so it is the supplier the joined capstone
`M4MeanSqPrime.m4_meansq_per_chi_gen_join` needs.  §4's `a2Rows_of_capfree3_end'` is the
strict/fused sibling, for the door's own half-open cut.

The hypothesis list, the weighting arithmetic and the four numerals are the landed theorem's
verbatim; the only change is the object the third weighing step lands in. -/
theorem a2Rows_of_capfree3' :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (Adoor M) (3072 * M) M 2 Ms Mt kk (H1door M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
          p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow' Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ :=
    seam_row_number_capfree3'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (Adoor M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1door M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a3_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum' M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum'_nonneg hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge M]
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow'
  refine a3_row_weigh ?_ ?_ ?_ ?_
  · exact a3_level1_weigh (fun R' hR' => level1_term_door_decays hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a3_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a3_term3_weigh_mr hRS0 hg3
  · exact a3_term4_weigh hZ0 hg32

end Salt.MR
