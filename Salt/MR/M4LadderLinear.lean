/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2Linear
import Salt.MR.M4MeanSq
import Salt.MR.M4Close
import Salt.MR.M4MeanSqPool
import Salt.MR.M4BridgeCover
import Salt.MR.M4BridgePhase
import Salt.MR.M4MeanSqPrime
import Salt.MR.M4BridgeDilate
import Salt.MR.M4ClassPrice

/-!
# `M4LadderLinear` — the M4 mean-square ladder at `AdoorL M = 2^36·M`

⟦LADDER-L, G1 §3⟧  The `_L` twin family of `M4MeanSq`, `M4Close`, `M4MeanSqPool`,
`M4BridgeCover`, `M4BridgePhase`, `M4MeanSqPrime`, `M4BridgeDilate` and `M4ClassPrice` at the
LINEAR door.  Purely additive: no landed declaration moves.

What each twin is:

* **The per-χ mean squares** (`m4_meansq_per_chi_gen_L`, `_pool_L`, `_join_L`, and their
  `_gk`/`_or_trivial` siblings) are the landed capstones with the door's ladder read at
  `AdoorL M`.  Their bodies are the landed ones: the whole chain below
  (`a2Frame3_witness`, `row_ladder_at_witness`, `a2Rows_of_capfree3*`) is `(A,G)`-parametric,
  so the anchor never leaves the symbol slot.  The exits land in `ThmA2Linear`'s
  `thm_a2'_of_rows*_L` and `ArithPageLinear`'s `a2Level1_L`/`a2RowsSum_L`.
* **The sockets** (`M4SievedDoorSq_L`, `M4SievedDoorSqSup_L`, `M4DoorGates_L`,
  `doorSievedCoeff_L`) are DEFINITIONS whose bodies read the door; they are re-minted, not
  transported.
* **The dilation/price page** (`M4BridgeDilate`, `M4ClassPrice`) rides `DoorLadderLinear`'s
  `memS_dilate_door_L`/`door_dilation_gate_L`, which is where the re-cut's one new
  hypothesis `1 ≤ M` enters.

Source pins: `docs/blueprints/flags.md` ⟦COMPOSE-FLAT-2⟧, ⟦LINEAR-PAGE⟧.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open MeasureTheory
open Salt.ExpSum
open Salt.Entropy.Chowla

/-! ### `M4MeanSq` :408 — `m4_cofactorSocket_at_witness` -/
/-- **THE CO-FACTOR SOCKET AT THE WITNESS LADDER** (`m4_cofactorSocket_at_witness_L`).
`CapFreeArm3.cofactorSocket_of_ellLin` at `b := ellLin (liouChi χ)`, `t₁ := 0`, the annulus
height `Tann := X` (the window's TOP — the row reads it antitonely), `Mt/kk := witMt/witKk`,
and `R̄` the uniform corner `cofactorRbd34loc(1/e, C_b, X, θ₂₉₃, kmin, Ymax, T*₂(Ymax), Rrad)`.

`hsockA` is `CaseASocket.caseASocket2_discharged`'s body at the capstone's own `X₀`. -/
theorem m4_cofactorSocket_at_witness_L {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {cf a : ℕ → ℂ} {N Xd P Q M : ℕ}
    {X h δ' VJ L Cb Rrad kmin Ymax EP2 cq T₀ X₀ : ℝ}
    (hsockA : ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (P' Q' : ℕ) (c' Cb' X' θ' : ℝ) (k₀' M' : ℕ) (t : ℝ),
        0 < c' → c' ≤ 1 / Real.exp 1 → 2 * c' < 1 → 0 ≤ Cb' → ShortIntervalDatum Cb' →
        X₀ ≤ (k₀' : ℝ) → pin2Gate ≤ (k₀' : ℝ) → k₀' ≤ M' → (M' : ℝ) ≤ 2 * (k₀' : ℝ) →
        0 ≤ cofactorMfl X' θ' (k₀' : ℝ) →
        CaseASocket2 g P' Q' c' Cb' X' θ' k₀' M' t)
    (F : A2Frame3 (ellLin (liouChi χ)) cf a N Xd P Q (AdoorL M) (3072 * M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀)
    (hX0 : 0 < X) (hh4 : 4 ≤ h) (hLXe : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X theta293 ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 (liouChi χ) X)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hRrad0 : 0 < Rrad)
    (hX₀k : X₀ ≤ kmin) (hMfl0 : 0 ≤ cofactorMfl X theta293 kmin) (hk2 : 2 ≤ kmin)
    (hkk : ∀ j ∈ ramI (H83 X theta293) P Q,
      kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtY : ∀ j ∈ ramI (H83 X theta293) P Q,
      ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) :
    CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0
      (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
        (Tstar2 Ymax (Real.log Ymax)) Rrad) (ellLin (liouChi χ)) := by
  have hgl : ∀ p : ℕ, p.Prime → ‖liouChi χ p‖ ≤ 1 := fun p _ => norm_liouChi_le_one χ p
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hh0 : (0 : ℝ) < h := by linarith
  -- ⟦the annulus at the window's TOP⟧ `2·(X/h) ≤ X` from `4 ≤ h`
  have h2aX : 2 * (X / h) ≤ X := by
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hh0]
    nlinarith
  have hblkX := F.blocks X h2aX le_rfl
  -- ⟦SUPPLIER 1⟧ the collision socket, VACUOUSLY, at the centre `0`
  have hsockP : PocketSocket3 (liouChi χ) P Q X theta293 0 :=
    pocketSocket_of_floor3 hgl theta293_pos (le_of_lt theta293_lt_one_div_32) hLXe hPlow
      hQhigh hPQ hfloor 0
  -- ⟦SUPPLIER 2⟧ CASE A, from the discharged slice
  have hA2 : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
      CaseASocket2 (liouChi χ) P Q (1 / Real.exp 1) Cb X theta293
        (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t := by
    intro j hj t
    obtain ⟨-, -, -, -, -, -, hk₀th, -, hk₀lo, hk₀hi, -, -, hhigh, hMtop, -, -, -⟩ :=
      hblkX j hj
    have hk₀pin : pin2Gate ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans pin2Gate_le_ballQuarterThreshold hk₀th
    have hk3 : (3 : ℝ) ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans three_le_ballQuarterThreshold hk₀th
    have hkMR : ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hkM : witKk (H83 X theta293) Xd j ≤ witMt (H83 X theta293) Xd j := by
      exact_mod_cast hkMR
    have hM2k : ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ 2 * ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hX₀kk : X₀ ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := le_trans hX₀k (hkk j hj)
    have hMflkk : (0 : ℝ) ≤ cofactorMfl X theta293 ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans hMfl0 (cofactorMfl_mono X theta293 (hkk j hj))
    exact hsockA (liouChi χ) hgl P Q (1 / Real.exp 1) Cb X theta293
      (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t hc0 le_rfl hc1 hCb0
      hCbound hX₀kk hk₀pin hkM hM2k hMflkk
  -- ⟦SUPPLIER 3⟧ the uniform ceiling
  have hMt1 : ∀ j ∈ ramI (H83 X theta293) P Q,
      (1 : ℝ) ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ pin2Gate := Real.one_le_exp (by norm_num)
    exact le_trans h1 (hMtpin j hj)
  have hRbdU := Rbd34loc_uniform (H83 X theta293) P Q (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) (1 / Real.exp 1) Cb X theta293 Rrad kmin Ymax hc0 hc1 hCb0
    (by linarith) hMtpin hkk hMt1 hMtY
  exact cofactorSocket_of_ellLin hgl hc1 hCb0 hRrad0 hsockP hblkX F.box hA2 hRbdU

/-! ### `M4MeanSq` :494 — `m4_meansq_per_chi_gen` -/
set_option maxHeartbeats 1600000 in
-- the ~75-binder joint instantiation: elaborating the three suppliers' argument lists
-- against one statement is what costs the heartbeats, not any tactic search
/-- **THE FIVE-SUMMAND MEAN SQUARE AT THE M4 DATUM** (`m4_meansq_per_chi_gen_L`).

For every Dirichlet character `χ mod q` in the door's modulus range `q ≤ Qm`, at every scale
`X` clearing the gates, and at any `T₀`-band bound `t0BandB X C₁′ M₀` the consumer holds:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁′²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·(log X)^{−1/500}`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`,

which is `ThmA2.thm_a2'_of_rows_L`' conclusion verbatim (M4-7 does arithmetic on the raw
summands, so nothing is re-shaped here).  This is the PER-SCALE statement: the dyadic cover
of `M4Dyadic` is the consumer's, not this theorem's.

`§5`'s `m4_t0band_at_datum` + `m4_t0band_of_live` are the `hT0band` slot's supplier, at
`C₁′ = cfbC₁ X C₁` and `M₀ = cfbM0 K q X`; the slot is explicit rather than inlined because
of the A2-5 seam (module docstring).

See the module docstring for the binder → supplier table. -/
theorem m4_meansq_per_chi_gen_L :
    ∃ (Cq cq T₀ X₀ Cs Ccc : ℝ) (Kfl : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      ∀ (Qm q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ),
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
            1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                        (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
                  (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
              p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
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
            -- ⟦the interface's two grading gates and the `4096` room⟧
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3_L
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin _hkk _hMtY
    hRrad0 hRrad _hRlow hV1 hVδ hlogV hδsq hksthr hVJg _hCb0 _hCbound hXthr
    _hX₀k _hMfl0 _hk2 _hkX _hgateW _hYpin _hWY _hXY _hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band _hcff hgP1 hgRows hL4096
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (3072 * M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_L hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hgP1 hgRows ⟨hε0, hεup⟩ hL4096

/-! ### `M4MeanSq` :789 — `m4_meansq_or_trivial` -/
set_option maxHeartbeats 1600000 in
-- same cause as `m4_meansq_per_chi_gen_L`: the binder list is re-elaborated once per branch
/-- **THE M4 PER-SCALE DICHOTOMY** (`m4_meansq_or_trivial_L`).  At a fixed scale the consumer
takes exactly one of two branches: the window is below the freeze's trivial threshold and is
discarded (`m4_trivial_branch`), or it is not and the five-summand mean square fires
(`m4_meansq_per_chi_gen_L`).  The mean-square gates are hypotheses in both branches — the split
is on the window length alone, which is what makes it usable inside the dyadic cover. -/
theorem m4_meansq_or_trivial_L (Qm : ℕ) :
    ∃ Cq cq T₀ X₀ Cs Ccc Kfl : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      ∀ (q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ)
            (xw ω H' : ℕ) (α Hp d₀ W : ℝ),
            2 ≤ xw → 2 ≤ ω →
            (Xd : ℝ) = X → N = 2 * Xd →
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                        (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
                  (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
              p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            SeamCoefW Xd P Q a b cf →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
              < Real.log (Real.log X) →
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_L
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
    hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band hcff hgP1 hgRows hL4096
  rcases le_or_gt ((H' : ℝ)) (trivThresh Hp d₀ W) with hshort | hlong
  · exact Or.inl ⟨hshort, m4_trivial_branch ha1 hxw hω hshort α⟩
  · refine Or.inr ⟨hlong, ?_⟩
    exact hper Qm q χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
      C₁' M₀
      hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
      hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 hεup habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hgP1 hgRows hL4096

/-! ### `M4MeanSq` :945 — `m4_cofactorSocket_at_witness_gk` -/
theorem m4_cofactorSocket_at_witness_L_gk (K : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    {cf a : ℕ → ℂ} {N Xd P Q M : ℕ}
    {X h δ' VJ L Cb Rrad kmin Ymax EP2 cq T₀ X₀ : ℝ}
    (hsockA : ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (P' Q' : ℕ) (c' Cb' X' θ' : ℝ) (k₀' M' : ℕ) (t : ℝ),
        0 < c' → c' ≤ 1 / Real.exp 1 → 2 * c' < 1 → 0 ≤ Cb' → ShortIntervalDatum Cb' →
        X₀ ≤ (k₀' : ℝ) → pin2Gate ≤ (k₀' : ℝ) → k₀' ≤ M' → (M' : ℝ) ≤ 2 * (k₀' : ℝ) →
        0 ≤ cofactorMfl X' θ' (k₀' : ℝ) →
        CaseASocket2 g P' Q' c' Cb' X' θ' k₀' M' t)
    (F : A2Frame3 (ellLin (liouChi χ)) cf a N Xd P Q (AdoorL M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀)
    (hX0 : 0 < X) (hh4 : 4 ≤ h) (hLXe : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X theta293 ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 (liouChi χ) X)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hRrad0 : 0 < Rrad)
    (hX₀k : X₀ ≤ kmin) (hMfl0 : 0 ≤ cofactorMfl X theta293 kmin) (hk2 : 2 ≤ kmin)
    (hkk : ∀ j ∈ ramI (H83 X theta293) P Q,
      kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtY : ∀ j ∈ ramI (H83 X theta293) P Q,
      ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) :
    CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0
      (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
        (Tstar2 Ymax (Real.log Ymax)) Rrad) (ellLin (liouChi χ)) := by
  have hgl : ∀ p : ℕ, p.Prime → ‖liouChi χ p‖ ≤ 1 := fun p _ => norm_liouChi_le_one χ p
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hh0 : (0 : ℝ) < h := by linarith
  -- ⟦the annulus at the window's TOP⟧ `2·(X/h) ≤ X` from `4 ≤ h`
  have h2aX : 2 * (X / h) ≤ X := by
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hh0]
    nlinarith
  have hblkX := F.blocks X h2aX le_rfl
  -- ⟦SUPPLIER 1⟧ the collision socket, VACUOUSLY, at the centre `0`
  have hsockP : PocketSocket3 (liouChi χ) P Q X theta293 0 :=
    pocketSocket_of_floor3 hgl theta293_pos (le_of_lt theta293_lt_one_div_32) hLXe hPlow
      hQhigh hPQ hfloor 0
  -- ⟦SUPPLIER 2⟧ CASE A, from the discharged slice
  have hA2 : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
      CaseASocket2 (liouChi χ) P Q (1 / Real.exp 1) Cb X theta293
        (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t := by
    intro j hj t
    obtain ⟨-, -, -, -, -, -, hk₀th, -, hk₀lo, hk₀hi, -, -, hhigh, hMtop, -, -, -⟩ :=
      hblkX j hj
    have hk₀pin : pin2Gate ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans pin2Gate_le_ballQuarterThreshold hk₀th
    have hk3 : (3 : ℝ) ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans three_le_ballQuarterThreshold hk₀th
    have hkMR : ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hkM : witKk (H83 X theta293) Xd j ≤ witMt (H83 X theta293) Xd j := by
      exact_mod_cast hkMR
    have hM2k : ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ 2 * ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hX₀kk : X₀ ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := le_trans hX₀k (hkk j hj)
    have hMflkk : (0 : ℝ) ≤ cofactorMfl X theta293 ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans hMfl0 (cofactorMfl_mono X theta293 (hkk j hj))
    exact hsockA (liouChi χ) hgl P Q (1 / Real.exp 1) Cb X theta293
      (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t hc0 le_rfl hc1 hCb0
      hCbound hX₀kk hk₀pin hkM hM2k hMflkk
  -- ⟦SUPPLIER 3⟧ the uniform ceiling
  have hMt1 : ∀ j ∈ ramI (H83 X theta293) P Q,
      (1 : ℝ) ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ pin2Gate := Real.one_le_exp (by norm_num)
    exact le_trans h1 (hMtpin j hj)
  have hRbdU := Rbd34loc_uniform (H83 X theta293) P Q (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) (1 / Real.exp 1) Cb X theta293 Rrad kmin Ymax hc0 hc1 hCb0
    (by linarith) hMtpin hkk hMt1 hMtY
  exact cofactorSocket_of_ellLin hgl hc1 hCb0 hRrad0 hsockP hblkX F.box hA2 hRbdU

/-! ### `M4MeanSq` :1021 — `m4_meansq_per_chi_gen_gk` -/
set_option maxHeartbeats 1600000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem m4_meansq_per_chi_gen_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ X₀ Cs Ccc : ℝ) (Kfl : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      ∀ (Qm q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ),
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
            1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            -- ⟦the interface's two grading gates and the `4096` room⟧
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3_L_gk K hK
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin _hkk _hMtY
    hRrad0 hRrad _hRlow hV1 hVδ hlogV hδsq hksthr hVJg _hCb0 _hCbound hXthr
    _hX₀k _hMfl0 _hk2 _hkX _hgateW _hYpin _hWY _hXY _hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band _hcff hgP1 hgRows hL4096
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hgP1 hgRows ⟨hε0, hεup⟩ hL4096

/-! ### `M4MeanSq` :1213 — `m4_meansq_or_trivial_gk` -/
set_option maxHeartbeats 1600000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem m4_meansq_or_trivial_L_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
    ∃ Cq cq T₀ X₀ Cs Ccc Kfl : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      ∀ (q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ)
            (xw ω H' : ℕ) (α Hp d₀ W : ℝ),
            2 ≤ xw → 2 ≤ ω →
            (Xd : ℝ) = X → N = 2 * Xd →
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            SeamCoefW Xd P Q a b cf →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
              < Real.log (Real.log X) →
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_L_gk K hK
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
    hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band hcff hgP1 hgRows hL4096
  rcases le_or_gt ((H' : ℝ)) (trivThresh Hp d₀ W) with hshort | hlong
  · exact Or.inl ⟨hshort, m4_trivial_branch ha1 hxw hω hshort α⟩
  · refine Or.inr ⟨hlong, ?_⟩
    exact hper Qm q χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
      C₁' M₀
      hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
      hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 hεup habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hgP1 hgRows hL4096

/-! ### `M4Close` :362 — `M4SievedDoorSq` -/
/-- **THE M4-7 SOCKET** — the mean square of the SIEVED λ-window sum on the door's measure,
at every tight-major frequency, with the band transport (hence `hlive`) as its own premise.

`L²`, not `L¹`: this is the level the mean-square tower natively produces, and §1 discharges
the Cauchy–Schwarz descent once.  See ⟦THE FIVE OPEN BRIDGES⟧ in the module header for the
supplier's remaining plumbing. -/
def M4SievedDoorSq_L (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen 12 H) H α →
        (∫ n, ‖absWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
              (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) H n α‖ ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (H : ℝ) ^ 2

/-! ### `M4Close` :395 — `M4DoorGates` -/
/-- **THE DOOR-DATA GATE BUNDLE** — M4-8's own hypothesis list, at the regime, uniform over
the window range.  `Cg` is the door glue's single opened constant; the `M`-gate is the
`24·Cg/δ` of M4-8 (the `8C/δ` of the freeze at the per-block grade `δ/3`, i.e. the `log ω`
absorption already applied).

`2 ≤ x`, `2 ≤ ω`, `ω ≤ x` are NOT here: the regime supplies them (`R.hx`, `R.hω`, `R.hωx`),
and so is `H + 1 ≤ x` (from `R.hheadroom`).  The witness for `hreach`/`hcount` at
`k := doorCount R.ω` is `M4Door.doorCount_gates`. -/
structure M4DoorGates_L (Cg : ℝ) (R : ChowlaRegime) (M k : ℕ) (δ : ℝ) : Prop where
  /-- the K-family's re-pin parameter is a genuine modulus -/
  hM : 1 ≤ M
  /-- the door grade is positive -/
  hδ : 0 < δ
  /-- the `M`-gate, after M4-8's `log ω` absorption -/
  hMδ : 24 * Cg / δ ≤ (M : ℝ)
  /-- the absorption's floor: `log ω ≥ 4` (where the cover/normaliser ratio is `< 3`) -/
  hlogω : 4 ≤ Real.log (R.ω : ℝ)
  /-- the geometric gate for the endpoint sum -/
  hpow : 2 ^ (k + 1) ≤ R.x
  /-- the cover count, IN-STATEMENT (law #253) -/
  hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2
  /-- the ladder exhausts the door window, at every window length in range -/
  hreach : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → doorLadder R.x H k ≤ R.x / R.ω
  /-- HS-3's analytic bundle, one per block, at every window length in range -/
  hblocks : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
    SieveBlockGate (AdoorL M) (3072 * M) M 2 (doorLadder R.x H (i + 1))

/-! ### `M4Close` :845 — `M4SievedDoorSq_gk` -/
/-- **THE M4-7 SOCKET AT THE LEVER** — `M4SievedDoorSq_L` (:368) at `G := s13GK K M`.  The
sieve set moves with `K`; the shape does not. -/
def M4SievedDoorSq_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen 12 H) H α →
        (∫ n, ‖absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
              (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n α‖ ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (H : ℝ) ^ 2

/-! ### `M4Close` :869 — `M4DoorGates_gk` -/
/-- **THE DOOR-DATA GATE BUNDLE AT THE LEVER** — `M4DoorGates_L` (:403) with the per-block
`SieveBlockGate` read at `G := s13GK K M`. -/
structure M4DoorGates_L_gk (K : ℕ) (Cg : ℝ) (R : ChowlaRegime) (M k : ℕ) (δ : ℝ) : Prop where
  /-- the K-family's re-pin parameter is a genuine modulus -/
  hM : 1 ≤ M
  /-- the door grade is positive -/
  hδ : 0 < δ
  /-- the `M`-gate, after M4-8's `log ω` absorption -/
  hMδ : 24 * Cg / δ ≤ (M : ℝ)
  /-- the absorption's floor: `log ω ≥ 4` (where the cover/normaliser ratio is `< 3`) -/
  hlogω : 4 ≤ Real.log (R.ω : ℝ)
  /-- the geometric gate for the endpoint sum -/
  hpow : 2 ^ (k + 1) ≤ R.x
  /-- the cover count, IN-STATEMENT (law #253) -/
  hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2
  /-- the ladder exhausts the door window, at every window length in range -/
  hreach : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → doorLadder R.x H k ≤ R.x / R.ω
  /-- HS-3's analytic bundle, one per block, at every window length in range -/
  hblocks : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
    SieveBlockGate (AdoorL M) (s13GK K M) M 2 (doorLadder R.x H (i + 1))

/-! ### `M4MeanSqPool` :59 — `m4_meansq_per_chi_gen_pool` -/
set_option maxHeartbeats 1600000 in
-- same cause as `M4MeanSq.m4_meansq_per_chi_gen_L`: elaborating the ~75-binder list against
-- one statement is what costs the heartbeats, not any tactic search
/-- **THE FIVE-SUMMAND MEAN SQUARE AT THE M4 DATUM** (`m4_meansq_per_chi_gen_L`).

For every Dirichlet character `χ mod q` in the door's modulus range `q ≤ Qm`, at every scale
`X` clearing the gates, and at any `T₀`-band bound `t0BandB X C₁′ M₀` the consumer holds:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁′²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·(log X)^{−1/500}`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`,

which is `ThmA2.thm_a2'_of_rows_L`' conclusion verbatim (M4-7 does arithmetic on the raw
summands, so nothing is re-shaped here).  This is the PER-SCALE statement: the dyadic cover
of `M4Dyadic` is the consumer's, not this theorem's.

`§5`'s `m4_t0band_at_datum` + `m4_t0band_of_live` are the `hT0band` slot's supplier, at
`C₁′ = cfbC₁ X C₁` and `M₀ = cfbM0 K q X`; the slot is explicit rather than inlined because
of the A2-5 seam (module docstring).

See the module docstring for the binder → supplier table. -/
theorem m4_meansq_per_chi_gen_pool_L :
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
            1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                        (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
                  (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
              p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3_L
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (3072 * M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool_L hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

/-! ### `M4MeanSqPool` :276 — `m4_meansq_or_trivial_pool` -/
set_option maxHeartbeats 1600000 in
-- same cause as §1: the binder list is re-elaborated once per branch
set_option maxHeartbeats 1600000 in
-- same cause as `m4_meansq_per_chi_gen_L`: the binder list is re-elaborated once per branch
/-- **THE M4 PER-SCALE DICHOTOMY** (`m4_meansq_or_trivial_L`).  At a fixed scale the consumer
takes exactly one of two branches: the window is below the freeze's trivial threshold and is
discarded (`m4_trivial_branch`), or it is not and the five-summand mean square fires
(`m4_meansq_per_chi_gen_L`).  The mean-square gates are hypotheses in both branches — the split
is on the window length alone, which is what makes it usable inside the dyadic cover. -/
theorem m4_meansq_or_trivial_pool_L (Qm : ℕ) :
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
            1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                        (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
                  (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
              p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_pool_L
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

/-! ### `M4MeanSqPool` :433 — `m4_meansq_per_chi_gen_pool_gk` -/
set_option maxHeartbeats 1600000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem m4_meansq_per_chi_gen_pool_L_gk (K : ℕ) (hK : K ≤ 170000000) :
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
            1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3_L_gk K hK
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

/-! ### `M4MeanSqPool` :625 — `m4_meansq_or_trivial_pool_gk` -/
set_option maxHeartbeats 1600000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem m4_meansq_or_trivial_pool_L_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
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
            1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_pool_L_gk K hK
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

/-! ### `M4BridgeCover` :358 — `doorSievedCoeff` -/
/-- **THE DOOR'S SIEVED DATUM**, named once: `1_𝒮·λ` at the door's own K-family
(`A = AdoorL M`, `G = 3072·M`, `J = 2`).  This is byte-exactly the coefficient sequence
inside `M4Close.M4SievedDoorSq_L`; the `def` is a spelling, definitionally transparent. -/
def doorSievedCoeff_L (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC

/-! ### `M4BridgeCover` :578 — `doorSievedCoeff_gk` -/
/-- **THE DOOR'S SIEVED DATUM AT THE LEVER** — `doorSievedCoeff_L` (:361) at `G := s13GK K M`.
Byte-exactly the coefficient sequence inside `M4Close.M4SievedDoorSq_L_gk`. -/
def doorSievedCoeff_L_gk (K M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC

/-! ### `M4BridgePhase` :371 — `M4SievedDoorSqSup` -/
/-- **THE SUB-WINDOW-UNIFORM SOCKET** — `M4Close.M4SievedDoorSq_L`'s obligation, moved to the
sub-window sup at the rational approximant.

Byte-for-byte `M4SievedDoorSq_L`'s statement with three changes, and only these three:
* the frequency is the *rational* `b/q` (`0 < q ≤ arcDen 12 H`), not the tight-major `α`;
* the integrand is the sup over sub-window lengths `K ≤ H`, not the full window sum;
* ⟦THE `q`-GRADING⟧ the right-hand side is `Braw H · q² · H²`, not `Braw H · H²` — the
  modulus of the residue-class split is carried into the grade rather than demoted, because
  the supplier's own loss is exactly `q` classes and the drift price carries a matching
  `1/q` (see the module header, §4).

The band transport is carried as the same premise, so the ⟦A2-5⟧ binder stays visible and is
never unfolded. -/
def M4SievedDoorSqSup_L (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H →
        (∫ n, (subWindowSup (memSCoeff (calP (AdoorL M) (3072 * M))
              (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) H n ((b : ℝ) / (q : ℝ))) ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2

/-! ### `M4BridgePhase` :517 — `M4SievedDoorSqSup_gk` -/
/-- **THE SUB-WINDOW-UNIFORM SOCKET AT THE LEVER** — `M4SievedDoorSqSup_L` (:384) at
`G := s13GK K M`. -/
def M4SievedDoorSqSup_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H →
        (∫ n, (subWindowSup (memSCoeff (calP (AdoorL M) (s13GK K M))
              (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n ((b : ℝ) / (q : ℝ))) ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2

/-! ### `M4MeanSqPrime` :56 — `m4_meansq_per_chi_gen_join` -/
set_option maxHeartbeats 1600000 in
-- same cause as `M4MeanSq.m4_meansq_per_chi_gen_L`: elaborating the ~75-binder list against
-- one statement is what costs the heartbeats, not any tactic search
/-- **⟦THE R1×R2 JOIN AT THE M4 DATUM⟧** (`m4_meansq_per_chi_gen_join_L`) — the capstone
`M4MeanSq.m4_meansq_per_chi_gen_L` at BOTH ⟦R1⟧'s primed row sum and ⟦R2⟧'s free pool:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁′²·exp(−M₀/e) + 1787702400·(log Q₁)^{1/3}/P₁^{1/12} + 188133·π₀`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)² + 6315000/h`.

⟦THE GATE LIST AGAINST `M4MeanSqPool.m4_meansq_per_chi_gen_pool_L`⟧ ONE line moves: `hgRows`
reads `ThmA2.a2RowsSum'_L`.  The row supplier is `A3Middle.a2Rows_of_capfree3'_L` (the
CLOSED-window arm, which is what this capstone's coefficient binder carries) and the
interface is `ThmA2Prime.thm_a2'_of_rows_pool'_L`; every other binder, including the surviving
`𝒰`-leg gate `8640 ≤ (log X)^ε`, is `M4MeanSq`'s verbatim.

⟦WHAT IT IS FOR⟧ this is the capstone with NO `X`-decaying right-hand side inside it and NO
`log₂(2X_d)` in its row gate — the two removals K4-CENSUS named, in one statement. -/
theorem m4_meansq_per_chi_gen_join_L :
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
            1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                        (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
                  (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
              p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3'_L
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (3072 * M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool'_L hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

/-! ### `M4MeanSqPrime` :267 — `m4_meansq_or_trivial_join` -/
set_option maxHeartbeats 1600000 in
-- same cause as §1: the binder list is re-elaborated once per branch
set_option maxHeartbeats 1600000 in
-- same cause as `m4_meansq_per_chi_gen_L`: the binder list is re-elaborated once per branch
/-- **THE M4 PER-SCALE DICHOTOMY AT THE JOIN** (`m4_meansq_or_trivial_join_L`).
`M4MeanSq.m4_meansq_or_trivial_L` over §1: below the freeze's trivial threshold the window is
discarded, above it the JOINED five-summand mean square fires.  The split is on the window
length alone, unchanged. -/
theorem m4_meansq_or_trivial_join_L (Qm : ℕ) :
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
            1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                        (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
                  (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
              p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_join_L
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

/-! ### `M4MeanSqPrime` :422 — `m4_meansq_per_chi_gen_join_gk` -/
set_option maxHeartbeats 1600000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem m4_meansq_per_chi_gen_join_L_gk (K : ℕ) (hK : K ≤ 170000000) :
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
            1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3'_L_gk K hK
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool'_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

/-! ### `M4MeanSqPrime` :614 — `m4_meansq_or_trivial_join_gk` -/
set_option maxHeartbeats 1600000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem m4_meansq_or_trivial_join_L_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
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
            1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_join_L_gk K hK
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

/-! ### `M4BridgeDilate` :355 — `door_gate_blocks` -/
/-- **The door gate at every block index.**  `M4Residue.door_dilation_gate'_L` gives `d < P₁`;
`calP_door_mono_L` lifts it to `d < P_j` for all `j ∈ [1,J]` — the exact hypothesis
`indicator_mul_dilate_liouville` demands.  STRICT throughout (`d₀ ≤ q ≤ W < P₁`).

⟦THE CAP IS `M`-RELATIVE⟧ the ceiling is the door's own bottom block `P₁`, not the numeral
`2^{262144}` reached through `log H ≤ 2^{21845}` — see `M4Residue.door_dilation_gate'_L`.  A
consumer at `W = (log H)^{12}` supplies `hW` from the old numeral route unchanged; a consumer
at `W = arcDen 12 H` supplies it from ⟦gate 12⟧'s re-cut line. -/
theorem door_gate_blocks_L {M J d q : ℕ} {W : ℝ} (hM : 1 ≤ M) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) :
    ∀ j ∈ Finset.Icc 1 J, d < calP (AdoorL M) (3072 * M) j := fun _ hj =>
  lt_of_lt_of_le (door_dilation_gate_calP_L (M := M) hdq hqW hW)
    (calP_door_mono_L hM (Finset.mem_Icc.mp hj).1)

/-! ### `M4BridgeDilate` :369 — `dilCoeff_memS_door` -/
/-- **THE DILATED DATUM FACTORS** (MRT step (b) at the door, pointwise):

```
      dilCoeff (1_𝒮·λ) d₀ q₀ r₀ (k)  =  λ(d₀) · classCoeff (1_𝒮·λ) q₀ r₀ (k)
```

for `k ≠ 0`.  The λ-half is `liouvilleC_mul` (no coprimality); the `1_𝒮`-half is
`memS_dilate_door_L` (the strict gate), routed through
`M4Residue.indicator_mul_dilate_liouville`. -/
theorem dilCoeff_memS_door_L {M J d q q₀ r₀ : ℕ} {W : ℝ} (hM : 1 ≤ M) (hd : d ≠ 0) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    {k : ℕ} (hk : k ≠ 0) :
    dilCoeff (memSCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) J
        liouvilleC) d q₀ r₀ k
      = liouvilleC d * classCoeff (memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) J liouvilleC) q₀ r₀ k := by
  simp only [dilCoeff, classCoeff, memSCoeff]
  by_cases hmod : k ≡ r₀ [MOD q₀]
  · rw [if_pos hmod, if_pos hmod]
    exact indicator_mul_dilate_liouville hd hk (door_gate_blocks_L hM hdq hqW hW)
  · rw [if_neg hmod, if_neg hmod, mul_zero]

/-! ### `M4BridgeDilate` :391 — `absWindowSum_dilCoeff_memS_door` -/
/-- **The factorisation under the window sum**: `λ(d₀)` comes out of the whole dilated
window sum, because every index of `Ioc n₀ (n₀+H₀)` is `≥ 1`. -/
theorem absWindowSum_dilCoeff_memS_door_L {M J d q q₀ r₀ H₀ n₀ : ℕ} {W : ℝ} (hM : 1 ≤ M)
    (hd : d ≠ 0) (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) (β : ℝ) :
    absWindowSum (dilCoeff (memSCoeff (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) J liouvilleC) d q₀ r₀) H₀ n₀ β
      = liouvilleC d * absWindowSum (classCoeff (memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) J liouvilleC) q₀ r₀) H₀ n₀ β := by
  unfold absWindowSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  rw [dilCoeff_memS_door_L (J := J) hM hd hdq hqW hW hk0]
  ring

/-! ### `M4BridgeDilate` :409 — `norm_absWindowSum_dilCoeff_memS_door` -/
/-- **The dilation is invisible to the modulus**: `‖λ(d₀)‖ = 1`, so the transported window
sum's norm is the norm of the *reduced* datum's window sum. -/
theorem norm_absWindowSum_dilCoeff_memS_door_L {M J d q q₀ r₀ H₀ n₀ : ℕ} {W : ℝ} (hM : 1 ≤ M)
    (hd : d ≠ 0) (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) (β : ℝ) :
    ‖absWindowSum (dilCoeff (memSCoeff (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) J liouvilleC) d q₀ r₀) H₀ n₀ β‖
      = ‖absWindowSum (classCoeff (memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) J liouvilleC) q₀ r₀) H₀ n₀ β‖ := by
  rw [absWindowSum_dilCoeff_memS_door_L (J := J) (H₀ := H₀) (n₀ := n₀) hM hd hdq hqW hW β,
    norm_mul, liouvilleC_norm hd, one_mul]

/-! ### `M4BridgeDilate` :621 — `m4_class_dilate_exit` -/
/-- **THE ROW'S EXIT — the per-class dilated statement.**  For the door's sieved Liouville
datum `1_𝒮·λ`, at a class `r` mod `q` with `d₀ = (r,q)` under the door gate
`d₀ ≤ q ≤ W < P₁` (`W` free — the cap is the door's own `P₁`, `M4Residue.door_dilation_gate'_L`):

1. **the transport** — `‖class sum‖ = ‖dilated window sum at the reduced datum‖`
   (`λ(d₀)` has modulus 1, so the dilation is invisible);
2. **the bookkeeping** — the dilated length is `H/d₀ ± 1`, both signs derived, and `≤ H`;
3. **the trivial branch** — every threshold above `H/d₀ + 1` closes the class outright.

The reduced class is coprime (`M4Residue.coprime_reduced_of_gcd`: `(r₀,q₀) = 1`), which is
what makes the character expansion (⟦BRIDGE 1⟧'s second half, `M4Close.
sum_liou_modEq_residue_eq`) legitimate at the dilated datum. -/
theorem m4_class_dilate_exit_L {M J q r H n : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) (α : ℝ) :
    ‖classWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) J liouvilleC) H n q r α‖
        = ‖absWindowSum (classCoeff (memSCoeff (calP (AdoorL M) (3072 * M))
            (calQK (AdoorL M) (3072 * M) M) J liouvilleC)
              (q / Nat.gcd r q) (r / Nat.gcd r q))
            (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) ((Nat.gcd r q : ℝ) * α)‖
      ∧ ((H : ℝ) / (Nat.gcd r q : ℝ) - 1 ≤ (dilLen H n (Nat.gcd r q) : ℝ)
          ∧ (dilLen H n (Nat.gcd r q) : ℝ) ≤ (H : ℝ) / (Nat.gcd r q : ℝ) + 1
          ∧ dilLen H n (Nat.gcd r q) ≤ H)
      ∧ (∀ thr : ℝ, (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr →
          ‖classWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
            (calQK (AdoorL M) (3072 * M) M) J liouvilleC) H n q r α‖ ≤ thr) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
  refine ⟨?_, ⟨le_dilLen_real H n hd, dilLen_le_real H n hd, dilLen_le_window H n hd⟩, ?_⟩
  · rw [classWindowSum_dilate _ hq r H n α]
    exact norm_absWindowSum_dilCoeff_memS_door_L (J := J)
      (H₀ := dilLen H n (Nat.gcd r q)) (n₀ := n / Nat.gcd r q) hM hd.ne' hdq hqW hW _
  · intro thr hthr
    exact norm_classWindowSum_le_thresh
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ J m) hq r H n α hthr

/-! ### `M4BridgeDilate` :737 — `door_gate_blocks_gk` -/
/-- **The door gate at every block index, at the lever** — `door_gate_blocks_L` (:363). -/
theorem door_gate_blocks_L_gk (K : ℕ) {M J d q : ℕ} {W : ℝ} (hM : 1 ≤ M) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) :
    ∀ j ∈ Finset.Icc 1 J, d < calP (AdoorL M) (s13GK K M) j := by
  intro j hj
  refine lt_of_lt_of_le ?_ (calP_door_mono_L_gk K hM (Finset.mem_Icc.mp hj).1)
  rw [calP_gk_one_eq] at hW ⊢
  exact door_dilation_gate_calP_L (M := M) hdq hqW hW

/-! ### `M4BridgeDilate` :746 — `dilCoeff_memS_door_gk` -/
/-- **THE DILATED DATUM FACTORS, AT THE LEVER** — `dilCoeff_memS_door_L` (:378). -/
theorem dilCoeff_memS_door_L_gk (K : ℕ) {M J d q q₀ r₀ : ℕ} {W : ℝ} (hM : 1 ≤ M) (hd : d ≠ 0)
    (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    {k : ℕ} (hk : k ≠ 0) :
    dilCoeff (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) J
        liouvilleC) d q₀ r₀ k
      = liouvilleC d * classCoeff (memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) J liouvilleC) q₀ r₀ k := by
  simp only [dilCoeff, classCoeff, memSCoeff]
  by_cases hmod : k ≡ r₀ [MOD q₀]
  · rw [if_pos hmod, if_pos hmod]
    exact indicator_mul_dilate_liouville hd hk (door_gate_blocks_L_gk K hM hdq hqW hW)
  · rw [if_neg hmod, if_neg hmod, mul_zero]

/-! ### `M4BridgeDilate` :761 — `absWindowSum_dilCoeff_memS_door_gk` -/
/-- **The factorisation under the window sum, at the lever** —
`absWindowSum_dilCoeff_memS_door_L` (:393). -/
theorem absWindowSum_dilCoeff_memS_door_L_gk (K : ℕ) {M J d q q₀ r₀ H₀ n₀ : ℕ} {W : ℝ}
    (hM : 1 ≤ M) (hd : d ≠ 0) (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) (β : ℝ) :
    absWindowSum (dilCoeff (memSCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) J liouvilleC) d q₀ r₀) H₀ n₀ β
      = liouvilleC d * absWindowSum (classCoeff (memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) J liouvilleC) q₀ r₀) H₀ n₀ β := by
  unfold absWindowSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  rw [dilCoeff_memS_door_L_gk K (J := J) hM hd hdq hqW hW hk0]
  ring

/-! ### `M4BridgeDilate` :779 — `norm_absWindowSum_dilCoeff_memS_door_gk` -/
/-- **The dilation is invisible to the modulus, at the lever** —
`norm_absWindowSum_dilCoeff_memS_door_L` (:411). -/
theorem norm_absWindowSum_dilCoeff_memS_door_L_gk (K : ℕ) {M J d q q₀ r₀ H₀ n₀ : ℕ} {W : ℝ}
    (hM : 1 ≤ M) (hd : d ≠ 0) (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) (β : ℝ) :
    ‖absWindowSum (dilCoeff (memSCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) J liouvilleC) d q₀ r₀) H₀ n₀ β‖
      = ‖absWindowSum (classCoeff (memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) J liouvilleC) q₀ r₀) H₀ n₀ β‖ := by
  rw [absWindowSum_dilCoeff_memS_door_L_gk K (J := J) (H₀ := H₀) (n₀ := n₀) hM hd hdq hqW hW β,
    norm_mul, liouvilleC_norm hd, one_mul]

/-! ### `M4BridgeDilate` :791 — `m4_class_dilate_exit_gk` -/
/-- **THE ROW'S EXIT AT THE LEVER — the per-class dilated statement** —
`m4_class_dilate_exit_L` (:633). -/
theorem m4_class_dilate_exit_L_gk (K : ℕ) {M J q r H n : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) (α : ℝ) :
    ‖classWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) J liouvilleC) H n q r α‖
        = ‖absWindowSum (classCoeff (memSCoeff (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M) J liouvilleC)
              (q / Nat.gcd r q) (r / Nat.gcd r q))
            (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) ((Nat.gcd r q : ℝ) * α)‖
      ∧ ((H : ℝ) / (Nat.gcd r q : ℝ) - 1 ≤ (dilLen H n (Nat.gcd r q) : ℝ)
          ∧ (dilLen H n (Nat.gcd r q) : ℝ) ≤ (H : ℝ) / (Nat.gcd r q : ℝ) + 1
          ∧ dilLen H n (Nat.gcd r q) ≤ H)
      ∧ (∀ thr : ℝ, (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr →
          ‖classWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M) J liouvilleC) H n q r α‖ ≤ thr) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
  refine ⟨?_, ⟨le_dilLen_real H n hd, dilLen_le_real H n hd, dilLen_le_window H n hd⟩, ?_⟩
  · rw [classWindowSum_dilate _ hq r H n α]
    exact norm_absWindowSum_dilCoeff_memS_door_L_gk K (J := J)
      (H₀ := dilLen H n (Nat.gcd r q)) (n₀ := n / Nat.gcd r q) hM hd.ne' hdq hqW hW _
  · intro thr hthr
    exact norm_classWindowSum_le_thresh
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ J m) hq r H n α hthr

/-! ### `M4ClassPrice` :227 — `norm_sum_windowClass_memS_dilate` -/
/-- **THE NON-COPRIME BRANCH — ONE DILATION, AN EQUALITY.**  At the residual frequency `0`,
`M4BridgeDilate.m4_class_dilate_exit_L` reads as a pure re-indexing of the bare class sum: the
class mod `q` of the window `(n, n+H]` is the class `r₀` mod `q₀` of the DILATED window
`(n/d₀, n/d₀ + dilLen]`, at the same sieved datum, and `‖λ(d₀)‖ = 1` makes the transport
loss-free.  Nothing is estimated here. -/
theorem norm_sum_windowClass_memS_dilate_L {M J q r H n : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) :
    ‖∑ m ∈ windowClass H n q r, memSCoeff (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) J liouvilleC m‖
      = ‖∑ m ∈ windowClass (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q)
            (q / Nat.gcd r q) (r / Nat.gcd r q),
          memSCoeff (calP (AdoorL M) (3072 * M))
            (calQK (AdoorL M) (3072 * M) M) J liouvilleC m‖ := by
  set c := memSCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) J liouvilleC
    with hc
  calc ‖∑ m ∈ windowClass H n q r, c m‖
      = ‖classWindowSum c H n q r 0‖ := by
        rw [classWindowSum_eq_classPhaseSum, classPhaseSum_zero]
    _ = ‖absWindowSum (classCoeff c (q / Nat.gcd r q) (r / Nat.gcd r q))
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) 0‖ := by
        have h := (m4_class_dilate_exit_L (J := J) (q := q) (r := r) (H := H) (n := n)
          (W := W) hM hq hqW hW 0).1
        rwa [mul_zero] at h
    _ = ‖∑ m ∈ windowClass (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q)
          (q / Nat.gcd r q) (r / Nat.gcd r q), c m‖ := by
        rw [absWindowSum_classCoeff_zero]

/-! ### `M4ClassPrice` :254 — `m4_class_price` -/
/-- **`m4_class_price_L` — THE PER-CLASS PRICE, both cases.**

For a class `r` mod `q` of the door's sieved `λ`-window sum at a tight-major rational `b/q`:

* `d₀ = (r,q) = 1` — the character expansion fires at `(q, r)` on the sieved window, and the
  `1/φ(q)` cancels (`hcop`);
* `d₀ > 1` — ONE dilation (an equality, zero loss) lands the class at the provably coprime
  `(q₀, r₀) = (q/d₀, r/d₀)` on the dilated window, where the same expansion fires (`hdil`).

The two hypotheses are the SAME row datum read at the two windows the two branches use; a
supplier uniform over the modulus range and the window range discharges both at once. -/
theorem m4_class_price_L {M J q r H n : ℕ} {W : ℝ} {B : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    (hcop : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ sievedWindow (MemS (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) J) H n, liouChi χ m‖ ≤ B)
    (hdil : ∀ χ : DirichletCharacter ℂ (q / Nat.gcd r q),
      ‖∑ m ∈ sievedWindow (MemS (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) J)
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q), liouChi χ m‖ ≤ B) :
    ‖∑ m ∈ windowClass H n q r, memSCoeff (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) J liouvilleC m‖ ≤ B := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the expansion at `(q, r)`
    haveI : NeZero q := ⟨hq.ne'⟩
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]
      exact hcase
    exact norm_sum_windowClass_memS_le_of_uniform hcopqr _ _ J H n hcop
  · -- ⟦d₀ > 1⟧ ONE dilation, then the expansion at the reduced (coprime) pair
    rw [norm_sum_windowClass_memS_dilate_L (J := J) hM hq hqW hW]
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    haveI : NeZero (q / Nat.gcd r q) := ⟨hq₀.ne'⟩
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    exact norm_sum_windowClass_memS_le_of_uniform hcop₀ _ _ J _ _ hdil

/-! ### `M4ClassPrice` :939 — `norm_sum_windowClass_memS_dilate_gk` -/
/-- **THE NON-COPRIME BRANCH AT THE LEVER** — `norm_sum_windowClass_memS_dilate_L` (:232). -/
theorem norm_sum_windowClass_memS_dilate_L_gk (K : ℕ) {M J q r H n : ℕ} {W : ℝ} (hM : 1 ≤ M)
    (hq : 0 < q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) :
    ‖∑ m ∈ windowClass H n q r, memSCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) J liouvilleC m‖
      = ‖∑ m ∈ windowClass (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q)
            (q / Nat.gcd r q) (r / Nat.gcd r q),
          memSCoeff (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M) J liouvilleC m‖ := by
  set c := memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) J liouvilleC
    with hc
  calc ‖∑ m ∈ windowClass H n q r, c m‖
      = ‖classWindowSum c H n q r 0‖ := by
        rw [classWindowSum_eq_classPhaseSum, classPhaseSum_zero]
    _ = ‖absWindowSum (classCoeff c (q / Nat.gcd r q) (r / Nat.gcd r q))
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) 0‖ := by
        have h := (m4_class_dilate_exit_L_gk K (J := J) (q := q) (r := r) (H := H) (n := n)
          (W := W) hM hq hqW hW 0).1
        rwa [mul_zero] at h
    _ = ‖∑ m ∈ windowClass (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q)
          (q / Nat.gcd r q) (r / Nat.gcd r q), c m‖ := by
        rw [absWindowSum_classCoeff_zero]

/-! ### `M4ClassPrice` :963 — `m4_class_price_gk` -/
/-- **THE PER-CLASS PRICE AT THE LEVER, both cases** — `m4_class_price_L` (:265). -/
theorem m4_class_price_L_gk (K : ℕ) {M J q r H n : ℕ} {W : ℝ} {B : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (hcop : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ sievedWindow (MemS (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) J) H n, liouChi χ m‖ ≤ B)
    (hdil : ∀ χ : DirichletCharacter ℂ (q / Nat.gcd r q),
      ‖∑ m ∈ sievedWindow (MemS (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) J)
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q), liouChi χ m‖ ≤ B) :
    ‖∑ m ∈ windowClass H n q r, memSCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) J liouvilleC m‖ ≤ B := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the expansion at `(q, r)`
    haveI : NeZero q := ⟨hq.ne'⟩
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]
      exact hcase
    exact norm_sum_windowClass_memS_le_of_uniform hcopqr _ _ J H n hcop
  · -- ⟦d₀ > 1⟧ ONE dilation, then the expansion at the reduced (coprime) pair
    rw [norm_sum_windowClass_memS_dilate_L_gk K (J := J) hM hq hqW hW]
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    haveI : NeZero (q / Nat.gcd r q) := ⟨hq₀.ne'⟩
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    exact norm_sum_windowClass_memS_le_of_uniform hcop₀ _ _ J _ _ hdil

/-! ## §Xw — ⟦KWIDE-65⟧ THE WIDE-CEILING TWINS (this file)

Mechanical widening of the flat `hK : K ≤ 170000000` binders on the `L`-chain: the ceiling
moves INSIDE the internal `∀ M` as `K ≤ 170000000 * M`, so the raised lever `KlevF` can flow.
Statements and proofs are verbatim apart from that antecedent and the `_kwide` re-pointing.
The originals are untouched.
-/

/-- ⟦WIDE CEILING TWIN⟧ (`m4_meansq_per_chi_gen_L_gk_kwide`) —
`m4_meansq_per_chi_gen_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_meansq_per_chi_gen_L_gk_kwide (K : ℕ) :
    ∃ (Cq cq T₀ X₀ Cs Ccc : ℝ) (Kfl : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      ∀ (Qm q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ),
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
            1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            -- ⟦the interface's two grading gates and the `4096` room⟧
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3_L_gk_kwide K
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin _hkk _hMtY
    hRrad0 hRrad _hRlow hV1 hVδ hlogV hδsq hksthr hVJg _hCb0 _hCbound hXthr
    _hX₀k _hMfl0 _hk2 _hkX _hgateW _hYpin _hWY _hXY _hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band _hcff hgP1 hgRows hL4096
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hKw hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hgP1 hgRows ⟨hε0, hεup⟩ hL4096

/-- ⟦WIDE CEILING TWIN⟧ (`m4_meansq_or_trivial_L_gk_kwide`) —
`m4_meansq_or_trivial_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_meansq_or_trivial_L_gk_kwide (K : ℕ) (Qm : ℕ) :
    ∃ Cq cq T₀ X₀ Cs Ccc Kfl : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      ∀ (q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ)
            (xw ω H' : ℕ) (α Hp d₀ W : ℝ),
            2 ≤ xw → 2 ≤ ω →
            (Xd : ℝ) = X → N = 2 * Xd →
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            SeamCoefW Xd P Q a b cf →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
              < Real.log (Real.log X) →
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_L_gk_kwide K
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
    hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band hcff hgP1 hgRows hL4096
  rcases le_or_gt ((H' : ℝ)) (trivThresh Hp d₀ W) with hshort | hlong
  · exact Or.inl ⟨hshort, m4_trivial_branch ha1 hxw hω hshort α⟩
  · refine Or.inr ⟨hlong, ?_⟩
    exact hper Qm q χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
      C₁' M₀
      hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
      hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 hεup habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hgP1 hgRows hL4096

/-- ⟦WIDE CEILING TWIN⟧ (`m4_meansq_per_chi_gen_pool_L_gk_kwide`) —
`m4_meansq_per_chi_gen_pool_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_meansq_per_chi_gen_pool_L_gk_kwide (K : ℕ) :
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
            1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3_L_gk_kwide K
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hKw hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

/-- ⟦WIDE CEILING TWIN⟧ (`m4_meansq_or_trivial_pool_L_gk_kwide`) —
`m4_meansq_or_trivial_pool_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_meansq_or_trivial_pool_L_gk_kwide (K : ℕ) (Qm : ℕ) :
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
            1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_pool_L_gk_kwide K
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
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
      hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hpool hgP1 hgRows hgU hgBand

/-- ⟦WIDE CEILING TWIN⟧ (`m4_meansq_per_chi_gen_join_L_gk_kwide`) —
`m4_meansq_per_chi_gen_join_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_meansq_per_chi_gen_join_L_gk_kwide (K : ℕ) :
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
            1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1_L M
                + 188133 * π₀
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3'_L_gk_kwide K
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
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
  have F : A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1doorL M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness_L` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hKw hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_pool'_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hpool hgP1 hgRows hgU hgBand

/-- ⟦WIDE CEILING TWIN⟧ (`m4_meansq_or_trivial_join_L_gk_kwide`) —
`m4_meansq_or_trivial_join_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_meansq_or_trivial_join_L_gk_kwide (K : ℕ) (Qm : ℕ) :
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
            1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                        (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
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
              thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
                  (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
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
                * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
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
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness_L` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
              p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
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
            374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ →
            5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀ →
            (Real.log X) ^ (-theta293 + ε) ≤ π₀ →
            4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀ →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1_L M
                    + 188133 * π₀
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_join_L_gk_kwide K
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ π₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
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
      hM hKw hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hpool hgP1 hgRows hgU hgBand

end Salt.MR

end
