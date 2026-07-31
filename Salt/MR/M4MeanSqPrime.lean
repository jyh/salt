/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4MeanSqPool
import Salt.MR.A3Middle

/-!
# ⟦R3-A — THE CAPSTONE AT THE R1×R2 JOIN⟧ (`M4MeanSqPrime`)

`M4MeanSqPool` re-states `M4MeanSq`'s two capstones at ⟦R2⟧'s free pool.  This file takes the
last step: the same two statements with the row gate at ⟦R1⟧'s `ThmA2.a2RowsSum'` and the row
family at `ThmA2Prime.a2Mrow'`.

## ⟦THE THREE OBJECTS THAT MOVE, AND NOTHING ELSE⟧

Against `M4MeanSq.m4_meansq_per_chi_gen`:

| slot | landed | here |
|---|---|---|
| the row family | `a2Mrow` (`ThmA2Rows.a2Rows_of_capfree3`) | `a2Mrow'` (`A3Middle` §7) |
| `hgRows` | `5760·(a2RowsSum + C_p·2/M) ≤ (log X)^{−1/500}` | `… a2RowsSum' … ≤ π₀` |
| `hgP1`, the `𝒰`-leg, the band | three decaying targets | the one free pool `π₀` |

`ε ≤ θ₂₉₃ − 1/500` is gone (⟦R2⟧); `8640 ≤ (log X)^ε` SURVIVES verbatim (MAESTRO ERRATUM #2:
it is a `𝒰`-leg gate, not a pool gate — see `M4MeanSqPool`'s header).

## ⟦WHY THIS IS THE STRONGEST OF THE FOUR⟧

`a2RowsSum' ≤ a2RowsSum` and `a2Mrow' ≤ a2Mrow`, so both moved slots are WEAKER hypotheses;
`π₀` is free, so the three pooled gates are weaker than the landed decaying ones at every
`π₀ ≥ (log X)^{−1/500}`.  Setting `π₀ := (log X)^{−1/500}` and feeding the landed row through
`ThmA2Prime.a2Mrow'_le_a2Mrow` is NOT possible in that direction (the join direction warning),
which is exactly why the primed supplier had to be minted: `A3Middle` §5–§7.

## Contents

* §1 `m4_meansq_per_chi_gen_join`;
* §2 `m4_meansq_or_trivial_join`.

Additive: no landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE FIVE-SUMMAND MEAN SQUARE AT THE JOIN -/

set_option maxHeartbeats 1600000 in
-- same cause as `M4MeanSq.m4_meansq_per_chi_gen`: elaborating the ~75-binder list against
-- one statement is what costs the heartbeats, not any tactic search
/-- **⟦THE R1×R2 JOIN AT THE M4 DATUM⟧** (`m4_meansq_per_chi_gen_join`) — the capstone
`M4MeanSq.m4_meansq_per_chi_gen` at BOTH ⟦R1⟧'s primed row sum and ⟦R2⟧'s free pool:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁′²·exp(−M₀/e) + 1787702400·(log Q₁)^{1/3}/P₁^{1/12} + 188133·π₀`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)² + 6315000/h`.

⟦THE GATE LIST AGAINST `M4MeanSqPool.m4_meansq_per_chi_gen_pool`⟧ ONE line moves: `hgRows`
reads `ThmA2.a2RowsSum'`.  The row supplier is `A3Middle.a2Rows_of_capfree3'` (the
CLOSED-window arm, which is what this capstone's coefficient binder carries) and the
interface is `ThmA2Prime.thm_a2'_of_rows_pool'`; every other binder, including the surviving
`𝒰`-leg gate `8640 ≤ (log X)^ε`, is `M4MeanSq`'s verbatim.

⟦WHAT IT IS FOR⟧ this is the capstone with NO `X`-decaying right-hand side inside it and NO
`log₂(2X_d)` in its row gate — the two removals K4-CENSUS named, in one statement. -/
theorem m4_meansq_per_chi_gen_join :
    ∃ (Cq cq T₀ X₀ Cs Ccc : ℝ) (Kfl : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      ∀ (Qm q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ π₀ : ℝ),
            -- ⟦the two pins (FRAME's joint instantiation)⟧
            (Xd : ℝ) = X → N = 2 * Xd →
            -- ⟦the scale page⟧
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            -- ⟦the door and the block pin `P = Q`⟧
            1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
            ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                        (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
            -- ⟦the window floors, at the witness ladder⟧
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
                  (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            -- ⟦the calibration, the radius, the short-interval datum⟧
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            -- ⟦the `kmin`/`Ymax` ladder⟧
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6) — inside the existential scope⟧
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            -- ⟦the ε-window and the Perron budget⟧
            0 ≤ ε → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            -- ⟦the S8 datum⟧
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
              p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            -- ⟦THE PIN CHAIN, `hwin`-FREE (⟦THE WALL⟧'s rewire): the on-window
            -- factorization ALONE.  `hwinPin` is GONE — see §3″⟧
            SeamCoefW Xd P Q a b cf →
            -- ⟦the `T₀`-band datum: `m4_t0band_at_datum` is the supplier, and §2's
            -- `dpolyA_seamS0_bandDatum` the bridge — see the header on the A2-5 seam⟧
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            -- ⟦the cap-free floor's threshold⟧
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl Qm + 25)
              < Real.log (Real.log X) →
            -- ⟦the interface's grading gates, AT THE FREE POOL⟧
            0 ≤ π₀ →
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1 M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3'
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin _hkk _hMtY
    hRrad0 hRrad _hRlow hV1 hVδ hlogV hδsq hksthr hVJg _hCb0 _hCbound hXthr
    _hX₀k _hMfl0 _hk2 _hkX _hgateW _hYpin _hWY _hXY _hthrY hcqgate hCqgate
    hε0 habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band _hcff hpool hgP1 hgRows hgU hgBand
  -- ⟦THE SCALE PAGE⟧
  have hXe : Real.exp 1 ≤ X := le_trans exp_one_le_exp_exp_one hXee
  have hX3 : (3 : ℝ) ≤ X := le_of_lt (lt_of_lt_of_le exp_exp_one_gt_three hXee)
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hLX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 2) hlX2
  -- ⟦THE TWO PINS, in every shape the suppliers want⟧
  have hXdX : X ≤ (Xd : ℝ) := le_of_eq hXd.symm
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by rw [hXd]; linarith
  have hXd1 : 1 ≤ Xd := by exact_mod_cast hXd1'
  have hNcast : (N : ℝ) = 2 * X := by rw [hNXd]; push_cast; rw [hXd]
  have hMN : 2 * Xd ≤ N := le_of_eq hNXd.symm
  have hNle : (N : ℝ) ≤ 2 * (Xd : ℝ) := by rw [hNcast, hXd]
  have hXN : X ≤ (N : ℝ) := by rw [hNcast]; linarith
  have hN2X : (N : ℝ) ≤ 2 * X := le_of_eq hNcast
  have hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ) := by rw [hNcast, hXd]; linarith
  -- ⟦THE FRAME'S REMAINING ARITHMETIC⟧
  have hW4 : ∀ j ∈ ramI (H83 X theta293) P Q, 4 ≤ ramRbot (H83 X theta293) Xd j :=
    fun j hj => by linarith [hW5 j hj]
  have hlog2X : (0 : ℝ) ≤ 1 + Real.log (2 * X) := by
    have : (0 : ℝ) ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    linarith
  -- ⟦⟦WALL 1⟧'s REWIRE⟧ the window-restricted BAND law is consumed AS IS now: the row's
  -- `hwin`-free four-row exit (`M4RowMR`) reads only the on-window factorization, so the
  -- widening `coef_widen_of_window` is no longer on the path (it stays as the historical
  -- instance) and `hwinBand` — ⟦THE WALL⟧'s second head — is DELETED from the statement
  -- ⟦FIELD 1–4: THE FRAME⟧ — at the CO-FACTOR DATUM `ellLin (liouChi χ)` (the socket cut's
  -- `b`-slot; the frame no longer takes a multiplicative generator)
  have F : A2Frame3 b cf a N Xd P Q (Adoor M) (3072 * M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1door M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool' hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

/-! ## §2 — THE PER-SCALE DICHOTOMY AT THE JOIN -/

set_option maxHeartbeats 1600000 in
-- same cause as §1: the binder list is re-elaborated once per branch
set_option maxHeartbeats 1600000 in
-- same cause as `m4_meansq_per_chi_gen`: the binder list is re-elaborated once per branch
/-- **THE M4 PER-SCALE DICHOTOMY AT THE JOIN** (`m4_meansq_or_trivial_join`).
`M4MeanSq.m4_meansq_or_trivial` over §1: below the freeze's trivial threshold the window is
discarded, above it the JOINED five-summand mean square fires.  The split is on the window
length alone, unchanged. -/
theorem m4_meansq_or_trivial_join (Qm : ℕ) :
    ∃ Cq cq T₀ X₀ Cs Ccc Kfl : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      ∀ (q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ π₀ : ℝ)
            (xw ω H' : ℕ) (α Hp d₀ W : ℝ),
            2 ≤ xw → 2 ≤ ω →
            (Xd : ℝ) = X → N = 2 * Xd →
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
            ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                        (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
                  (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            0 ≤ ε → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
              p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            SeamCoefW Xd P Q a b cf →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
              < Real.log (Real.log X) →
            0 ≤ π₀ →
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum' M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1 M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_join
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
    hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band hcff hpool hgP1 hgRows hgU hgBand
  rcases le_or_gt ((H' : ℝ)) (trivThresh Hp d₀ W) with hshort | hlong
  · exact Or.inl ⟨hshort, m4_trivial_branch ha1 hxw hω hshort α⟩
  · refine Or.inr ⟨hlong, ?_⟩
    exact hper Qm q χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
      C₁' M₀ π₀
      hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
      hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hpool hgP1 hgRows hgU hgBand

/-! ## §GK — the G-lever twin

⟦R1⟧'s joined M4 mean-square pair at `G := s13GK K M` (`GLever`).  Suppliers are
`A3Middle.a2Rows_of_capfree3'_gk` and `ThmA2Prime.thm_a2'_of_rows_pool'_gk`; the row gate
reads `ThmA2.a2RowsSum'_gk` and the row family `ThmA2Prime.a2Mrow'_gk`. -/

set_option maxHeartbeats 1600000 in
theorem m4_meansq_per_chi_gen_join_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ X₀ Cs Ccc : ℝ) (Kfl : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      ∀ (Qm q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ π₀ : ℝ),
            -- ⟦the two pins (FRAME's joint instantiation)⟧
            (Xd : ℝ) = X → N = 2 * Xd →
            -- ⟦the scale page⟧
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            -- ⟦the door and the block pin `P = Q`⟧
            1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                        (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
            -- ⟦the window floors, at the witness ladder⟧
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
                  (calQK (Adoor M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            -- ⟦the calibration, the radius, the short-interval datum⟧
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            -- ⟦the `kmin`/`Ymax` ladder⟧
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6) — inside the existential scope⟧
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            -- ⟦the ε-window and the Perron budget⟧
            0 ≤ ε → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            -- ⟦the S8 datum⟧
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
              p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            -- ⟦THE PIN CHAIN, `hwin`-FREE (⟦THE WALL⟧'s rewire): the on-window
            -- factorization ALONE.  `hwinPin` is GONE — see §3″⟧
            SeamCoefW Xd P Q a b cf →
            -- ⟦the `T₀`-band datum: `m4_t0band_at_datum` is the supplier, and §2's
            -- `dpolyA_seamS0_bandDatum` the bridge — see the header on the A2-5 seam⟧
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            -- ⟦the cap-free floor's threshold⟧
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl Qm + 25)
              < Real.log (Real.log X) →
            -- ⟦the interface's grading gates, AT THE FREE POOL⟧
            0 ≤ π₀ →
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1 M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3'_gk K hK
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin _hkk _hMtY
    hRrad0 hRrad _hRlow hV1 hVδ hlogV hδsq hksthr hVJg _hCb0 _hCbound hXthr
    _hX₀k _hMfl0 _hk2 _hkX _hgateW _hYpin _hWY _hXY _hthrY hcqgate hCqgate
    hε0 habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band _hcff hpool hgP1 hgRows hgU hgBand
  -- ⟦THE SCALE PAGE⟧
  have hXe : Real.exp 1 ≤ X := le_trans exp_one_le_exp_exp_one hXee
  have hX3 : (3 : ℝ) ≤ X := le_of_lt (lt_of_lt_of_le exp_exp_one_gt_three hXee)
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hLX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 2) hlX2
  -- ⟦THE TWO PINS, in every shape the suppliers want⟧
  have hXdX : X ≤ (Xd : ℝ) := le_of_eq hXd.symm
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by rw [hXd]; linarith
  have hXd1 : 1 ≤ Xd := by exact_mod_cast hXd1'
  have hNcast : (N : ℝ) = 2 * X := by rw [hNXd]; push_cast; rw [hXd]
  have hMN : 2 * Xd ≤ N := le_of_eq hNXd.symm
  have hNle : (N : ℝ) ≤ 2 * (Xd : ℝ) := by rw [hNcast, hXd]
  have hXN : X ≤ (N : ℝ) := by rw [hNcast]; linarith
  have hN2X : (N : ℝ) ≤ 2 * X := le_of_eq hNcast
  have hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ) := by rw [hNcast, hXd]; linarith
  -- ⟦THE FRAME'S REMAINING ARITHMETIC⟧
  have hW4 : ∀ j ∈ ramI (H83 X theta293) P Q, 4 ≤ ramRbot (H83 X theta293) Xd j :=
    fun j hj => by linarith [hW5 j hj]
  have hlog2X : (0 : ℝ) ≤ 1 + Real.log (2 * X) := by
    have : (0 : ℝ) ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    linarith
  -- ⟦⟦WALL 1⟧'s REWIRE⟧ the window-restricted BAND law is consumed AS IS now: the row's
  -- `hwin`-free four-row exit (`M4RowMR`) reads only the on-window factorization, so the
  -- widening `coef_widen_of_window` is no longer on the path (it stays as the historical
  -- instance) and `hwinBand` — ⟦THE WALL⟧'s second head — is DELETED from the statement
  -- ⟦FIELD 1–4: THE FRAME⟧ — at the CO-FACTOR DATUM `ellLin (liouChi χ)` (the socket cut's
  -- `b`-slot; the frame no longer takes a multiplicative generator)
  have F : A2Frame3 b cf a N Xd P Q (Adoor M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1door M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool'_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

set_option maxHeartbeats 1600000 in
theorem m4_meansq_or_trivial_join_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
    ∃ Cq cq T₀ X₀ Cs Ccc Kfl : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      ∀ (q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ π₀ : ℝ)
            (xw ω H' : ℕ) (α Hp d₀ W : ℝ),
            2 ≤ xw → 2 ≤ ω →
            (Xd : ℝ) = X → N = 2 * Xd →
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                        (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
                  (calQK (Adoor M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            0 ≤ ε → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
              p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            SeamCoefW Xd P Q a b cf →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
              < Real.log (Real.log X) →
            0 ≤ π₀ →
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1 M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_join_gk K hK
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
    hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band hcff hpool hgP1 hgRows hgU hgBand
  rcases le_or_gt ((H' : ℝ)) (trivThresh Hp d₀ W) with hshort | hlong
  · exact Or.inl ⟨hshort, m4_trivial_branch ha1 hxw hω hshort α⟩
  · refine Or.inr ⟨hlong, ?_⟩
    exact hper Qm q χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
      C₁' M₀ π₀
      hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
      hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hpool hgP1 hgRows hgU hgBand

-- #audit (temporary)

end Salt.MR
