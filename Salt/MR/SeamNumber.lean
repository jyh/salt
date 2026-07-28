/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TypicalPriceK
import Mathlib.NumberTheory.ZetaValues

/-!
# `SeamNumber` — THE FUSE: the seam row as ONE number-shaped bound

`SeamCalibrationK.seam_row_calibratedK` closes the seam row end to end, but its right-hand
side still carries `Σ_j lemma12Rows` — a sum of sums over the coefficient support, not a
number.  `TypicalPriceK.sum_lemma12Rows_priced_calibratedK2` prices exactly that sum at the
K-ladder, with both small grades in place (the density collection at `C·(2/M)`, the `p²` row
at `16·log₂(2X_d)/P_j`).  **This file is the `.trans` that fuses them**, and nothing else:
no estimate is restated, no engine is re-derived, no constant is re-chosen.

## The `X`-vs-`X_d` reconciliation — the named consumer debt, paid in the open

The two halves are stated at DIFFERENT bases.  The seam row's frame lives at MR's global
scale `X` (`X ≤ N ≤ 2X`); the pricing side lives at the dyadic length `X_d` that
`TLegExit.lemma12Rows` is defined against (`2X_d ≤ N`, and the coefficient window
`[X_d, 2X_d]`).  The junction's own convention makes ONE direction a theorem and the rest a
debt:

* **`X_d ≤ X` is DERIVED** here, from the seam row's own two binders `2X_d ≤ N` and
  `N ≤ 2X`.  It is the only bridge the frames supply, and it is proved, not assumed.
* **`√(log X_d) ≤ √(log X)` is therefore the direction of the bridge** — so the pricing
  side's cutoff `log Q ≤ √(log X_d)` is STRICTLY STRONGER than the seam row's own
  `log Q_{Jb} ≤ (log X)^{1/2}`, and cannot be derived from it.  The fuse carries the
  `X_d`-based gate **(R1)** and DERIVES the seam row's `X`-based one from it — the
  reconciliation runs in the kernel, in that direction, and `seam_row_calibratedK`'s
  cutoff binder is consequently absent from the list below (it is implied, not dropped).
* the five remaining demands are `X_d`-facts with no `X`-side shadow at all, and are carried
  verbatim as **(R2)–(R6)**.

**No identification of `X` with `X_d` occurs anywhere in this file** (law #253): every gate
that the pricing side needs and the seam frame does not supply is a visible hypothesis.

## The six reconciliation gates

* **R1** `log Q_{Jb} ≤ √(log X_d)` — base `X_d`; the frame's cutoff is at base `X`, and the
  bridge `X_d ≤ X` points the wrong way.
* **R2** `100 ≤ √(log X_d)` — an `X_d`-threshold; the frame's guards (`e² ≤ log X`) are
  `X`-side, and far weaker.
* **R3** `N ≤ 4X_d` — the frame has `2X_d ≤ N`, the OTHER direction; `N ≍ 2X_d` is the
  dyadic convention, not a consequence.
* **R4** the per-level error-domination product — `TypicalDensity`'s own gate, per level,
  at base `X_d`.
* **R5** `‖a n‖ ≤ 1` — `seam_row_calibratedK` bounds `g`, `c`, `b`, `cf`; never `a`.
* **R6** `a n ≠ 0 → X_d ≤ n ≤ 2X_d` — the frame pins `a` from BELOW only
  (`n ≤ X → a n = 0`).

R1 is stated at the TOP LEVEL only: `calQK` is monotone in `j` (`calQK_mono`), so the
`Jb`-gate is the strongest of the family and the per-level gates the pricer asks for are
derived from it here.

Non-vacuity (hand-checked, not manufactured): R5/R6 sit with the frame's
`n ≤ X → a n = 0`, which is consistent — `X_d = X`, `N = 2X` leaves `a` supported on
`(X, 2X]` — and R2 forces `X_d ≥ e^{10000}`, which R4 tolerates at the K-ladder
(`(√X_d + 1)·(j²M)³ ≤ X_d/(j²M)` for `X_d` beyond `(Jb²M)^8`).

## §2 — the Basel upgrade (optional, wired to the demand side only)

`SeamCalibrationK.sum_ratioK_le` pays `Σ_j j^{−2} ≤ 2` where the truth is `π²/6`, and
`eq28_clears_of_M` pays for it in `M ≥ 8/δ`.  `sum_ratioK_le_basel` /
`eq28_clears_of_M_basel` re-run both at mathlib's `hasSum_zeta_two`, closing MR §9's
accounting at **`M ≥ 4/δ`** — MR's own scale.  The fuse itself is left at the landed `2/M`:
`K2`'s conclusion carries that constant inside a proved inequality, and improving it there
would mean touching `TypicalPriceK`.  The two families coexist (⟦V9b⟧'s parallel-family
ruling).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 p.6, §8.2 p.27, §9 p.31;
`docs/sources/mr_extract.md` §6.4, §6.6, §6.7; `docs/exploration/hsup-design.md` ⟦V9b⟧,
⟦V9c⟧ K-2/K-4.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — THE FUSE -/

/-- **THE SEAM ROW AS A NUMBER** (`seam_row_number`).

`SeamCalibrationK.seam_row_calibratedK` composed with
`TypicalPriceK.sum_lemma12Rows_priced_calibratedK2`: the `Σ_j lemma12Rows` that the seam row
left un-priced is replaced by

  `480·(T_ann/X_d + 1)·(Σ_j [X_d(2e·X_d/H_j + 1)(e/X_d²) + 16·log₂(2X_d)/P_j + 1/X_d] + C·2/M)`,

so the whole right-hand side is a formula in the parameters — **no integral, no coefficient
sum, no ladder hypothesis**.  The frame is `seam_row_calibratedK`'s verbatim, with the
cutoff binder replaced by the strictly stronger `X_d`-based gate (R1) it is derived from,
and the five further `X_d`-side demands (R2)–(R6) the pricing engines make.  See this
module's header for the gate-by-gate account. -/
theorem seam_row_number :
    ∃ Cq cq T₀ Ccol X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        -- ⟦THE K-STATION FRAME⟧ the twelve scalar gates, in place of every ladder hypothesis
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        -- the `VJ`-family, collapsed to its worst corner
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
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 Ccol → 0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        -- ⟦THE `𝒯`-SIDE FRAME⟧ the dyadic length and Lemma 12's coefficient contract
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        -- ⟦THE RECONCILIATION GATES⟧ (law #253) the six `X_d`-side demands the pricing
        -- engines make and the `X`-side seam frame does not supply.  R1 replaces
        -- `seam_row_calibratedK`'s own base-`X` cutoff, which it implies (`X_d ≤ X`).
        -- (R1) MR §2's cutoff at the DYADIC base, top level (monotone in `j`)
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        -- (R2) the large-`X_d` guard
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        -- (R3) the upper dyadic pin (`2X_d ≤ N` is the frame's; this is its converse half)
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- (R4) the per-level error-domination product gate
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ)
              * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        -- (R5) the seam coefficient's own `1`-bound
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        -- (R6) and its dyadic support
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
                + 480 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + C * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, Ccol, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hseam⟩ := seam_row_calibratedK
  obtain ⟨C, hC, hK2⟩ := sum_lemma12Rows_priced_calibratedK2
  refine ⟨Cq, cq, T₀, Ccol, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
    hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FRAME'S OWN READS⟧ everything the pricer needs that `CalFrameK` already carries
  have hA : 1 ≤ A := le_trans (by norm_num) hF.A_floor
  have hG1 : 1 ≤ G := hF.one_le_G
  have hM1 : 1 ≤ M := hF.one_le_M
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd1
  have hT0 : (0 : ℝ) ≤ Tann := by linarith
  have hH10 : (0 : ℝ) < H1 := by linarith [hF.H1_two]
  -- ⟦THE BRIDGE⟧ `X_d ≤ X`, from the junction's own two binders — the ONE derived relation
  have hXdX : (Xd : ℝ) ≤ X := by
    have h2 : (2 : ℝ) * (Xd : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNXd
    linarith
  -- ⟦THE DIRECTION CHECK⟧ `√(log X_d) ≤ √(log X)`: the seam row's OWN cutoff, at base `X`,
  -- is what (R1) implies — never the other way round
  have hJdef : Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) := by
    have hlog : Real.log (Xd : ℝ) ≤ Real.log X := Real.log_le_log hXd0 hXdX
    calc Real.log ((calQK A G M Jb : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (Xd : ℝ)) := hQXd
      _ ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlog
      _ = (Real.log X) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  -- ⟦R1 AT EVERY LEVEL⟧ `calQK` is monotone in `j`, so the top-level gate is the family
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  -- ⟦THE TWO HALVES⟧
  have hseaminst := hseam g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
  have hK2inst := hK2 A G M Jb N Xd H1 Tann a b c hA hG1 hM1 hXd1 hT0 hH10 hN4
    hreg hXdbig hdom ha1 hb1 hc1 hasupp hwin
  exact hseaminst.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2inst)) le_rfl)

/-! ## §2 — the Basel upgrade: MR's own re-pin scale `M = 4/δ` -/

/-- `Σ_{j=1}^{Jb} j^{−2} ≤ π²/6`, uniformly in the cutoff — mathlib's `hasSum_zeta_two`
against the finite partial sum.  `SeamCalibrationK.sum_invsq_Icc_le_two` pays `2` here
(`Analysis.PSeries`' telescoping bound); this is the sharp constant. -/
private lemma sum_invsq_Icc_le_pi_sq (Jb : ℕ) :
    ∑ j ∈ Finset.Icc 1 Jb, ((j : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
  have h := sum_le_hasSum (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Finset.Icc 1 Jb)
    (fun i _ => by positivity) hasSum_zeta_two
  simpa [one_div] using h

/-- **THE `j`-COLLECTION AT THE SHARP CONSTANT** (`sum_ratioK_le_basel`).
`SeamCalibrationK.sum_ratioK_le` with `Σ j^{−2} ≤ 2` replaced by `π²/6`. -/
theorem sum_ratioK_le_basel {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (Jb : ℕ) :
    ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
      ≤ Real.pi ^ 2 / (6 * (M : ℝ)) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcongr : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
        = (M : ℝ)⁻¹ * ((j : ℝ) ^ 2)⁻¹ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [log_calP_div_log_calQK hA hG hM hj.1]
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
    field_simp
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
  have hstep : (M : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 Jb, ((j : ℝ) ^ 2)⁻¹
      ≤ (M : ℝ)⁻¹ * (Real.pi ^ 2 / 6) :=
    mul_le_mul_of_nonneg_left (sum_invsq_Icc_le_pi_sq Jb) (by positivity)
  calc (M : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 Jb, ((j : ℝ) ^ 2)⁻¹
      ≤ (M : ℝ)⁻¹ * (Real.pi ^ 2 / 6) := hstep
    _ = Real.pi ^ 2 / (6 * (M : ℝ)) := by field_simp

/-- **MR §9 eq (28) AT MR'S OWN SCALE** (`eq28_clears_of_M_basel`).
`SeamCalibrationK.eq28_clears_of_M` needs `M ≥ 8/δ` because it pays `Σ j^{−2} ≤ 2`; at the
sharp `π²/6` the same accounting closes at **`M ≥ 4/δ`**, which is MR p.31's own re-pin
scale.  The margin: `1/50 + (2 + 1/50)·π²/24 ≤ 0.856 ≤ 1`. -/
theorem eq28_clears_of_M_basel {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (Jb : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hMδ : 4 / δ ≤ (M : ℝ)) :
    δ / 50 + (2 + 1 / 50) * ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
      ≤ δ := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsum := sum_ratioK_le_basel hA hG hM Jb
  have hMδ' : (4 : ℝ) ≤ (M : ℝ) * δ := by
    rw [div_le_iff₀ hδ] at hMδ; linarith
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpi0 : (0 : ℝ) ≤ Real.pi ^ 2 := sq_nonneg _
  have hstep : Real.pi ^ 2 / (6 * (M : ℝ)) ≤ Real.pi ^ 2 * δ / 24 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

end Salt.MR
