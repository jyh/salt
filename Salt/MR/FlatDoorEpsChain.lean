/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorReceipt
import Salt.MR.V7RatedH
import Salt.MR.StrideGrade12bWalls
import Mathlib

/-!
# ⟦TIER S — THE DOOR AT THE HEAD'S GRADE, `ε`-FAMILY: THE CHAIN⟧ (`FlatDoorEpsChain`)
The rung-1 (capped) wave's own file, born EMPTY at freeze v1.3 (2026-09-16, at the fire) and
filled by the wave: the flat road's eight generic forms and seven replays re-cut at generic
`0 < ε ≤ 1/500` under the lattice-top cap `1/(500·h) ≤ ε`, `log h ≤ 9` (the `_b9` twins' binder),
the chain, the count leaf at `c := ⌈1/(500·ε)⌉`, and the head at the leaves' PINNED witnesses with
the tail kept — every step a landed name or a monotone transport, generic in the conclusion slot
`P` exactly as `DoorReceipt`'s chain is.  `FlatDoorEpsFamily` imports THIS file (never the
reverse): the frozen file's statement guard refuses a new declaration or a new import there, so
the wave's declarations live here and `FlatDoorEpsFamily`'s capped rung is assembled from them in
place.  Nothing here bears on twin primes (the frozen file's honest label, first line).
-/

open private uniformCap_arc uniformCap_shuffle spine_False_core_xi_sq_uniform from
  Salt.MR.S16Uniform

noncomputable section

open scoped BigOperators
open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §0 — ⟦THE NUMERALS AND THE TWO TRANSPORTS⟧ the cap's own constants -/

/-- **⟦THE LATTICE TOP⟧** (`epsChain_log_top_le_nine`) — `log 8103 ≤ 9`, the `_b9` twins' other
binder at `h := 8103` (`8103 < e⁹ = 8103.0839…`, via `Real.exp_one_gt_d9`).  The same numeral the
frozen file proves as C7; it is restated here because the frozen file imports THIS one. -/
theorem epsChain_log_top_le_nine : Real.log ((8103 : ℕ) : ℝ) ≤ 9 := by
  have hcast : ((8103 : ℕ) : ℝ) = (8103 : ℝ) := by norm_num
  rw [hcast, Real.log_le_iff_le_exp (by norm_num)]
  have h3 : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h5 : (2.7182818283 : ℝ) ^ (9 : ℕ) < (Real.exp 1) ^ (9 : ℕ) :=
    pow_lt_pow_left₀ h4 (by norm_num) (by norm_num)
  have h6 : (8103 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
  rw [h3]; linarith

/-- **⟦THE DOOR IS MONOTONE UP IN ITS GRADE⟧** (`mrtUniformityXiL2_mono`) — `MRTUniformityXiL2 R ρ`
is `∀ H …, Σ … ≤ ρ` (`MRTDoor.lean`), so a door at `ρ` is a door at any `ρ' ≥ ρ`.  This is the step
`FlatDoorPayload`'s construction names ("a door at `ρ ≤ δ₀` is a door at `δ₀`"). -/
theorem mrtUniformityXiL2_mono {R : ChowlaRegime} {ρ ρ' : ℝ} (hle : ρ ≤ ρ')
    (hd : MRTUniformityXiL2 R ρ) : MRTUniformityXiL2 R ρ' := by
  intro H _ hlo hhi
  exact le_trans (hd H hlo hhi) hle

/-- **⟦THE SOCKET RELAXATION, CO-FACTOR SIDE⟧** (`s16CofactorSupply_L_of_LH`) — the inflated
socket's supply implies the landed one, because `SocketBaseL → SocketBaseLH h`
(`socketBaseLH_of_socketBaseL`) and the socket sits in HYPOTHESIS position in both defs. -/
theorem s16CofactorSupply_L_of_LH {h K : ℕ} (hh : 0 < h) {Cq : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hs : S16CofactorSupply_LH_gk h K Cq R M) : S16CofactorSupply_L_gk K Cq R M := by
  intro H L q j A s hb
  exact hs H L q j A s (socketBaseLH_of_socketBaseL hh hb)

/-- **⟦THE SOCKET RELAXATION, BASE-SCALE SIDE⟧** (`s16BaseScaleCap96_L_of_LH`) — the same one-step
relaxation for ⟦ITEM 3⟧'s cap. -/
theorem s16BaseScaleCap96_L_of_LH {h K : ℕ} (hh : 0 < h) {R : ChowlaRegime} {M : ℕ}
    (hs : S16BaseScaleCap96_LH_gk h K R M) : S16BaseScaleCap96_L_gk K R M := by
  intro H L q j A s hb
  exact hs H L q j A s (socketBaseLH_of_socketBaseL hh hb)

/-- **⟦THE SUM SPLIT'S `log 2`, PAID FROM THE TOWER AT THE CAP⟧** (`epsChain_arm_split_cap`) —
`xceil_arm_split_h` (`XThread.lean:1153`) re-cut at the interval cap instead of at a pin: the
margin `ε²·H₊ − H₊/10^20` covers `log 2` for every `ε ≥ 1/(500·8103)`.  The room is the gate's
SECOND conjunct `50 ≤ loglog H₊`, which gives `log H₊ ≥ e^50 ≥ 10^21`, hence `H₊ ≥ 10^21`, against
a demand of `1.14·10^13`: **the headroom is a tower and the corner is a constant.** -/
theorem epsChain_arm_split_cap {ε : ℚ} (hcap : (1 : ℚ) / (500 * 8103) ≤ ε) {Hhi : ℕ}
    (hH4 : 4000000 ≤ Hhi) (hll : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) :
    Real.log 2 ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) - ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
  have hq : (1 : ℚ) ≤ 4051500 * ε := by
    rw [div_le_iff₀ (by norm_num)] at hcap; linarith
  have hqR : (1 : ℝ) ≤ 4051500 * (ε : ℝ) := by exact_mod_cast hq
  have hε0 : (0 : ℝ) < (ε : ℝ) := by linarith
  have hε2 : (1 : ℝ) / 16414652250000 ≤ (ε : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith [hqR, hε0]
  have hHR : (4000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by exact_mod_cast hH4
  have hHpos : (0 : ℝ) < ((Hhi : ℕ) : ℝ) := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log ((Hhi : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) < Real.log ((Hhi : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge hL0 (by norm_num : (0 : ℝ) < 50) hll
  have hexp50 : ((10 : ℝ) ^ (21 : ℕ)) ≤ Real.exp 50 := by
    have h50 : Real.exp 50 = (Real.exp 1) ^ (50 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [h50]
    calc ((10 : ℝ) ^ (21 : ℕ)) ≤ (2.7 : ℝ) ^ (50 : ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (50 : ℕ) := pow_le_pow_left₀ (by norm_num) h1.le 50
  have hLexp : Real.exp 50 ≤ Real.log ((Hhi : ℕ) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr hll
    rwa [Real.exp_log (by linarith : (0 : ℝ) < Real.log ((Hhi : ℕ) : ℝ))] at h1
  have hHbig : ((10 : ℝ) ^ (21 : ℕ)) ≤ ((Hhi : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos hHpos
    linarith
  have hstep : ((Hhi : ℕ) : ℝ) / 16414652250000 ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hε2 hHpos.le
    calc ((Hhi : ℕ) : ℝ) / 16414652250000 = 1 / 16414652250000 * ((Hhi : ℕ) : ℝ) := by ring
      _ ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) := h
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have e1 : ((Hhi : ℕ) : ℝ) / 16414652250000 = ((Hhi : ℕ) : ℝ) * (1 / 16414652250000) := by ring
  have e2 : ((Hhi : ℕ) : ℝ) / (10 : ℝ) ^ 20
      = ((Hhi : ℕ) : ℝ) * (1 / 100000000000000000000) := by norm_num; ring
  have hkey : Real.log 2
      ≤ ((Hhi : ℕ) : ℝ) / 16414652250000 - ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
    rw [e1, e2]
    have h21 : (1000000000000000000000 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by
      calc (1000000000000000000000 : ℝ) = (10 : ℝ) ^ (21 : ℕ) := by norm_num
        _ ≤ ((Hhi : ℕ) : ℝ) := hHbig
    linarith
  linarith [hkey, hstep]

/-! ## §1 — ⟦THE EIGHT `ε`-FORMS⟧ each landed form with `ε` moved to a parameter under the cap

Each `_Eps` sibling is its landed `def` (`DoorReceipt.lean` §1) with THREE edits and no others:
the `∃ ε : ℚ` binder is REMOVED (`ε` is the first parameter), the conjunct `1/500 ≤ ε` is
REPLACED by the capped rung's own `1/(500·8103) ≤ ε`, and `1/838400 ≤ δ₀` is REPLACED by the
`ε`-free numeral `1/(838400·8103) ≤ δ₀` — the exact pin `s15Arm_log_le_scaled` asks at `c := 8103`,
which is the ONE place the landed `δ₀` pin is read.  Every other conjunct is byte-identical. -/

def FlatHeadFormEps (ε : ℚ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      (1 : ℚ) / (500 * 8103) ≤ ε ∧ (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 26 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap = max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
              P R

def FlatSocketFormEps (ε : ℚ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (K δ₀ β : ℝ) (Hopq : ℕ), 0 < ε ∧ 0 < K ∧ K ≤ 2 ^ 539 ∧ 0 < δ₀ ∧
      (1 : ℚ) / (500 * 8103) ≤ ε ∧ (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧ 0 < β ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              (∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (Binsert : ℝ),
                (∀ m, lamCoeff m = a m + e m) →
                (∀ H : ℕ, 0 ≤ Bsieve H) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
                  NearRatTight (arcDen 12 H) H α →
                    (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
                      ≤ Bsieve H * (H : ℝ) ^ 2) →
                (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
                  (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
                    ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                      ∂(logMeasure R.x R.ω)) ≤ Binsert) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  K * (2 * Bsieve H) + 2 * Binsert ≤ δ₀) →
                P R)

def FlatDoorL2FormEps (ε : ℚ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ (1 : ℚ) / (500 * 8103) ≤ ε ∧
      (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
                M4DoorGates_L_gk K Cg R M k δ →
                (∀ H : ℕ, 0 ≤ Braw H) →
                M4SievedDoorSq_L_gk K R M Braw →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                  P R

def FlatRoadFormEps (ε : ℚ) (P : ChowlaRegime → Prop) : Prop :=
    ∃ (Cg : ℝ) (Kb δ₀ β : ℝ) (Hopq : ℕ), 1 ≤ Cg ∧ Cg ≤ 2 * 10 ^ 12 ∧
      0 < ε ∧ 0 < Kb ∧ Kb ≤ 2 ^ 539 ∧ 0 < δ₀ ∧ (1 : ℚ) / (500 * 8103) ≤ ε ∧
      (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧ 0 < β ∧
      ∀ (K : ℕ) (A : ℝ), 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
            ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              R.Hlo ≤ max Hcap U1floor ∧
              ∀ (δ Bceil : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
                M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
                (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
                (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                    ≤ Braw H) →
                (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
                2 * Kb * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
                M4ChiSummedFreeRow_L_gk K R M RS →
                  P R

def FlatCapstoneFormEps (ε : ℚ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg : ℝ) (Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ (1 : ℚ) / (500 * 8103) ≤ ε ∧ (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (Cp : ℝ), 0 ≤ Cp →
            ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRider ε g →
              ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
                Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
                (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                  Real.log (Real.log (R.Hhi : ℝ))
                    ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
                R.Hlo ≤ max Hcap U1floor ∧
                ∀ (M : ℕ), Mfl ≤ M → K ≤ 170000000 * M →
                  ∃ C' : ℝ, 0 < C' ∧
                    8 * C' ≤ (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
                        ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) ∧
                    ∀ (C₁ M₀ _epsf epsrf : ℕ → ℝ) (Kf : ℝ) (k : ℕ),
                      -- ⟦A⟧ THE SPINE ARITHMETIC
                      M4DoorGates_L_gk K Cg R M k δ₀ →
                      8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 4 →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloorL M : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
                      (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                        m4SmallGradeFits (doorRowFloorL M)
                          (fun H => 2 * RSanDoorRho (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) H)
                          (fun H => 2 * rStrWitness H) H) →
                      -- ⟦B1'⟧ THE FUSE'S OWN DEMANDS AT THE CONSTANT POOL
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorBaseFrame (A + s) j) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        374784 * Ct * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        GRowsZeroGate'''_L_gk K M (A + s) Cp
                          (constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi)) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log 376266
                            + (-Real.log (doorRhoOfDelta (s12DeltaSock δ₀ Kc)))
                          ≤ (theta293 - epsrf (A + s))
                              * Real.log (Real.log (((A + s : ℕ)) : ℝ))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293)
                          ≤ constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 500)
                          * constPool (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) R.Hhi) →
                      -- ⟦THE εr/ε SPLIT⟧ the absorption exponent's own window
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        0 ≤ epsrf (A + s) ∧ epsrf (A + s) ≤ theta293 - 1 / 500) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        calQK (AdoorL M) (s13GK K M) M 2 ≤ A + s ∧
                          Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
                              ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (100 : ℝ) ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) ∧
                          (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
                          ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) →
                      -- ⟦B4 RAW⟧ the crossing bound, carried
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
                          (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                          5 ≤ Real.log (Real.log (2 * T)) →
                          (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                              ‖spoly (2 * (A + s))
                                (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                            ≤ 8 * (0 : ℝ) ^ 2
                              + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                                    \ seamBall (((A + s : ℕ)) : ℝ) 0)
                                  ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                                      (calP (AdoorL M) (s13GK K M))
                                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                                      (mrAlpha (1 / 12)) 2,
                                  ‖spoly (2 * (A + s))
                                    (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                              + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                                  * (Real.log (((A + s : ℕ)) : ℝ))
                                      ^ (-theta293 + epsrf (A + s)))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
                      (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
                        DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kf
                          (doorRhoOfDelta (s12DeltaSock δ₀ Kc))) →
                        P R

def FlatConditionalFormEps (ε : ℚ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ (1 : ℚ) / (500 * 8103) ≤ ε ∧ (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧
      Kc ≤ 2 ^ 539 ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ A : ℝ, 162 ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
        ∃ Hcap : ℕ,
          Hcap ≤ max (flatDesignFloor A)
            (max (max Hopq (budgetFloorFlat (ε : ℝ) β A)) (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)) ∧
          ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ), XCeilRiderStrict ε g →
            max Hcap (max arcFloor36 loglogFloor50) ≤ U1floor →
            ∃ R : ChowlaRegime, R.eps = ε ∧ R.Hlo = U1floor ∧ g R.Hhi R.ω ≤ R.x ∧
              Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
              (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
                Real.log (Real.log (R.Hhi : ℝ))
                  ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
              ∀ M : ℕ,
                S15Sel''_L_gk K Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ Kc)) x₀ Mfl R M →
                 K ≤ 170000000 * M →
                S15CrossingBound_L_gk K R M → P R

def FlatKswinFormEps (ε : ℚ) (P : ChowlaRegime → Prop) (Awin : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ β : ℝ) (x₀ Hopq Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 1 ≤ Mfl ∧
      Cg ≤ 2 * 10 ^ 12 ∧ (1 : ℚ) / (500 * 8103) ≤ ε ∧ (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧
      (∀ A : ℝ, 162 ≤ A → Awin ≤ A → Mfl ≤ flatDoorM A) ∧
      0 < β ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧
      ∀ K : ℕ, ∃ Ct : ℝ, 0 < Ct ∧
        ∀ A : ℝ, 162 ≤ A → Awin ≤ A → budgetAFlat (ε : ℝ) β ≤ A →
          K ≤ 170000000 * flatDoorM A →
        (Hopq ≤ flatDesignBase A → flatWitFloor ε β A Hopq = flatDesignBase A) ∧
        ((x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) →
          Hopq ≤ flatDesignBase A →
          T₀ ≤ Real.exp (Real.sqrt ((flatWitFloor ε β A Hopq : ℕ) : ℝ) / 2) →
          Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 →
          ∀ g : ℕ → ℕ → ℕ, XCeilRiderStrict ε g → ∃ R : ChowlaRegime,
            R.eps = ε ∧ R.Hlo = flatWitFloor ε β A Hopq ∧ g R.Hhi R.ω ≤ R.x ∧
            Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((R.Hhi : ℕ) : ℝ) ∧
            (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
              Real.log (Real.log (R.Hhi : ℝ))
                ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
            3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
            Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
            (S16CofactorSupply_L_gk K Cq R (flatDoorM A) →
              S16BaseScaleCap96_L_gk K R (flatDoorM A) →
                P R))

def V7RatedFormEps (ε : ℚ) (P : ChowlaRegime → Prop) (A₀ : ℝ) : Prop :=
    ∃ (Cg Kc δ₀ Ct A β : ℝ) (Mfl : ℕ) (Cq cs T₀ Kq Ks C : ℝ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < Kc ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧ 0 < C ∧
      Real.log C ≤ 40 ∧ Cg ≤ 2 * 10 ^ 12 ∧ (1 : ℚ) / (500 * 8103) ≤ ε ∧
      (1 : ℝ) / (838400 * 8103) ≤ δ₀ ∧
      Mfl ≤ flatDoorM A ∧ 0 < β ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ R : ChowlaRegime,
        R.eps = ε ∧ R.Hlo = flatDesignBase A ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2)) ∧
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) ∧
        Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) ∧
        P R

/-! ## §2 — ⟦THE COUNT LEAF⟧ `|Ξ_H| ≤ 2^539` at every `ε` in the cap, not at a pin -/

/-- **⟦THE COUNT HOOK AT THE CAP⟧** (`bigXi_bounded_ceiling_of_cap`) —
`bigXi_bounded_ceiling_of_pin` (`GoldbachEnergyKc.lean:231`, at `ε = 1/500`) with the pin
replaced by the interval
`1/(500·8103) ≤ ε ≤ 1/500`.  The route is the pinned lemma's own: `bigXi_bounded_explicit`
(`GoldbachEnergyN0.lean:718`) at `K := e^40` (`ε`-free) and `C₁` read off the GENERIC
`hpt_holds_thr` (`:544`) at the `ε`-free threshold `T := 2^68`.

⟦THE WITNESS AND ITS SIZE⟧ `32·e^40·(2^63)²·4051500^10`.  `1/ε² ≤ 4051500² = 1.6415·10^13` carries
`C₁ ≤ 204800 + 1.681·10^18 + 1.1888·10^15·(68·log 2)² = 4.323·10^18 ≤ 2^63`, and `ε^{-10}` gives
`4051500^10 < 2^220`.  On the corpus's own chain (`e^40 ≤ 3^40 < 2^64`) the total is `2^414`
against `2^539` — **125 bits spare**.  The threshold's four demands are met with room: `4 ≤ ε²·T`
reads `1.8·10^7`, and `(2/ε²)^10 ≤ 2^450` against `T^9 = 2^612`. -/
theorem bigXi_bounded_ceiling_of_cap (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (hcap : (1 : ℚ) / (500 * 8103) ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXi ε H).card : ℝ) ≤ C := by
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hqcap : (1 : ℚ) ≤ 4051500 * ε := by
    rw [div_le_iff₀ (by norm_num)] at hcap; linarith
  have hcapR : (1 : ℝ) ≤ 4051500 * (ε : ℝ) := by exact_mod_cast hqcap
  have hεle : (ε : ℝ) ≤ 1 / 500 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε
    rwa [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
  have heps2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hεle]
  have hsqR : (1 : ℝ) ≤ 16414652250000 * (ε : ℝ) ^ 2 := by
    have h := one_le_pow₀ (n := 2) hcapR
    calc (1 : ℝ) ≤ (4051500 * (ε : ℝ)) ^ 2 := h
      _ = 16414652250000 * (ε : ℝ) ^ 2 := by ring
  have hu : (1 : ℝ) / (ε : ℝ) ^ 2 ≤ 16414652250000 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hTcastR : (((2 ^ 68 : ℕ)) : ℝ) = (2 : ℝ) ^ (68 : ℕ) := by push_cast; ring
  -- ⟦THE THRESHOLD'S FOUR DEMANDS⟧ at the `ε`-free `T := 2^68`
  have hT0 : N0' ≤ (2 : ℕ) ^ 68 := by unfold N0'; norm_num
  have hTA : (4 : ℚ) ≤ ε ^ 2 * (((2 ^ 68 : ℕ)) : ℚ) := by
    have hcast : (((2 ^ 68 : ℕ)) : ℚ) = 2 ^ (68 : ℕ) := by push_cast; ring
    have hsq : (1 : ℚ) ≤ 16414652250000 * ε ^ 2 := by
      have h := one_le_pow₀ (n := 2) hqcap
      calc (1 : ℚ) ≤ (4051500 * ε) ^ 2 := h
        _ = 16414652250000 * ε ^ 2 := by ring
    rw [hcast]
    norm_num
    linarith [hsq]
  have hTB : ((16 : ℕ) : ℝ) ^ (10 : ℕ) ≤ (((2 ^ 68 : ℕ)) : ℝ) := by
    rw [hTcastR]; norm_num
  have hTD : (2 / (ε : ℝ) ^ 2) ^ (10 : ℕ) ≤ ((((2 ^ 68 : ℕ)) : ℝ)) ^ (9 : ℕ) := by
    have h1 : (2 : ℝ) / (ε : ℝ) ^ 2 ≤ 2 ^ (45 : ℕ) := by
      rw [div_le_iff₀ (by positivity)]
      have : (2 : ℝ) ^ (45 : ℕ) = 35184372088832 := by norm_num
      rw [this]; linarith [hsqR]
    rw [hTcastR]
    calc ((2 : ℝ) / (ε : ℝ) ^ 2) ^ (10 : ℕ) ≤ ((2 : ℝ) ^ (45 : ℕ)) ^ (10 : ℕ) :=
          pow_le_pow_left₀ (by positivity) h1 10
      _ = (2 : ℝ) ^ (450 : ℕ) := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ (612 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((2 : ℝ) ^ (68 : ℕ)) ^ (9 : ℕ) := by rw [← pow_mul]
  -- ⟦THE CONSTANT⟧ the generic `hpt`, capped at `2^63`
  have hlogT : Real.log ((((2 ^ 68 : ℕ)) : ℝ)) ≤ 47.14 := by
    rw [hTcastR, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
  have hlogT0 : (0 : ℝ) ≤ Real.log ((((2 ^ 68 : ℕ)) : ℝ)) := Real.log_natCast_nonneg _
  have hlogTsq : (Real.log ((((2 ^ 68 : ℕ)) : ℝ))) ^ 2 ≤ 2222.2 := by
    have h := pow_le_pow_left₀ hlogT0 hlogT 2
    calc (Real.log ((((2 ^ 68 : ℕ)) : ℝ))) ^ 2 ≤ (47.14 : ℝ) ^ 2 := h
      _ ≤ 2222.2 := by norm_num
  have hpt : ∀ H n : ℕ, ((repCount (Salt.Entropy.Chowla.primeWindow ε H)
        (Salt.Entropy.Chowla.primeWindow ε H) n : ℕ) : ℝ)
      ≤ ((2 : ℝ) ^ (63 : ℕ)) * ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
    intro H n
    refine le_trans (hpt_holds_thr ε hε0 heps2 (1 / 256) (by norm_num) 16
      repCount_even_le_primorial_sixteen (2 ^ 68) hT0 hTA hTB hTD H n) ?_
    have hF : (0 : ℝ) ≤ ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n :=
      mul_nonneg (div_nonneg (by positivity) (sq_nonneg _)) (sTrunc2_nonneg n)
    have hbr : (ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2)
        ≤ 1188815000000000 := by
      have hA : (ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) ≤ 1180591620717412 := by
        rw [hTcastR]
        have h68 : (2 : ℝ) ^ (68 : ℕ) = 295147905179352825856 := by norm_num
        rw [h68]
        nlinarith [hεR0, hεle]
      have hB : (1 : ℝ) / (2 * (ε : ℝ) ^ 2) ≤ 8207326125000 := by
        have hid : (1 : ℝ) / (2 * (ε : ℝ) ^ 2) = (1 / (ε : ℝ) ^ 2) / 2 := by ring
        rw [hid]; linarith [hu]
      calc (ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2)
          ≤ 1180591620717412 + 2 + 8207326125000 := add_le_add (add_le_add hA le_rfl) hB
        _ ≤ 1188815000000000 := by norm_num
    have hbr0 : (0 : ℝ) ≤ (ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2) := by
      positivity
    have hprod : ((ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
          * (Real.log ((((2 ^ 68 : ℕ)) : ℝ))) ^ 2
        ≤ 1188815000000000 * 2222.2 :=
      mul_le_mul hbr hlogTsq (sq_nonneg _) (by norm_num)
    have hCL : (800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2) ≤ 1680860390400204800 := by
      have hid : (102400 : ℝ) / (ε : ℝ) ^ 2 = 102400 * (1 / (ε : ℝ) ^ 2) := by ring
      rw [hid]
      have h0 : (800 : ℝ) / (1 / 256 : ℝ) = 204800 := by norm_num
      rw [h0]; linarith [hu]
    have hCsum : (800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2)
          + ((ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
              * (Real.log ((((2 ^ 68 : ℕ)) : ℝ))) ^ 2
        ≤ (2 : ℝ) ^ (63 : ℕ) := by
      have h63 : (2 : ℝ) ^ (63 : ℕ) = 9223372036854775808 := by norm_num
      rw [h63]; linarith [hCL, hprod]
    calc ((800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2)
            + ((ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
                * (Real.log ((((2 ^ 68 : ℕ)) : ℝ))) ^ 2)
          * ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n
        = ((800 / (1 / 256 : ℝ) + 102400 / (ε : ℝ) ^ 2)
            + ((ε : ℝ) ^ 2 * (((2 ^ 68 : ℕ)) : ℝ) + 2 + 1 / (2 * (ε : ℝ) ^ 2))
                * (Real.log ((((2 ^ 68 : ℕ)) : ℝ))) ^ 2)
            * (((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) := by ring
      _ ≤ ((2 : ℝ) ^ (63 : ℕ)) * (((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :=
          mul_le_mul_of_nonneg_right hCsum hF
      _ = ((2 : ℝ) ^ (63 : ℕ)) * ((ε : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by ring
  -- ⟦THE EXPLICIT COUNT, AND THE CEILING⟧
  have hbase := bigXi_bounded_explicit ε hε0 heps2 ((2 : ℝ) ^ (63 : ℕ)) (Real.exp 40)
    (Real.exp_pos _) hFac2_lcm_sum_le_exp40 hpt
  refine ⟨32 * Real.exp 40 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 * (4051500 : ℝ) ^ (10 : ℕ),
    by positivity, ?_, 2, le_rfl, ?_⟩
  · have h40 : Real.exp 40 ≤ 3 ^ (40 : ℕ) := by simpa using exp_forty_le_pow40
    have hnn : (0 : ℝ) ≤ 32 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 * (4051500 : ℝ) ^ (10 : ℕ) := by positivity
    have hfold : 32 * Real.exp 40 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 * (4051500 : ℝ) ^ (10 : ℕ)
        = (32 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 * (4051500 : ℝ) ^ (10 : ℕ)) * Real.exp 40 := by ring
    have hnum : (32 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 * (4051500 : ℝ) ^ (10 : ℕ)) * 3 ^ (40 : ℕ)
        ≤ 2 ^ 539 := by norm_num
    rw [hfold]
    exact le_trans (mul_le_mul_of_nonneg_left h40 hnn) hnum
  · intro H _ hH2
    have hb := hbase H hH2
    have hid : 32 * Real.exp 40 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 / (ε : ℝ) ^ 10
        ≤ 32 * Real.exp 40 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 * (4051500 : ℝ) ^ (10 : ℕ) := by
      rw [div_le_iff₀ (by positivity)]
      have hp : (1 : ℝ) ≤ (4051500 * (ε : ℝ)) ^ (10 : ℕ) := one_le_pow₀ hcapR
      have hexp : (4051500 * (ε : ℝ)) ^ (10 : ℕ)
          = (4051500 : ℝ) ^ (10 : ℕ) * (ε : ℝ) ^ 10 := by ring
      rw [hexp] at hp
      have hpos : (0 : ℝ) < 32 * Real.exp 40 * ((2 : ℝ) ^ (63 : ℕ)) ^ 2 := by positivity
      nlinarith [hp, hpos]
    exact le_trans hb hid

/-! ## §3 — ⟦THE `ε`-HEAD⟧ the door-head's DEVICE with the head's TAIL kept, generic in `P` -/

/-- **⟦THE `A`-UNIFORM FLAT HEAD AT GENERIC `ε`, LEAVES PINNED, TAIL KEPT⟧**
(`flat_head_uniform_xceil_eps`) — `flat_head_uniform_xceil` (`XThread.lean:556`) with the pin
`ε := 1/500` replaced by the parameter under `0 < ε ≤ 1/500` and the cap, the leaves' witnesses
PINNED as the door-head pins them (`DoorReceipt.lean:1012`, `cD3 = 1/4`, `C = 1 + 2·(2·log 4)`) so
that the mint is the EXACT `ε/(256·(1 + 4·log 4))`, and the head's TAIL — the entropy collision —
kept, which the door-head drops.  Keeping both is what forces the two transports: the `D3` floor
and the circle-method grade are stated at the `∃`-witnesses, and each moves to the pinned witness
by ONE monotone step (`c ↦ 1/4` downward on a FLOOR, `C' ↦ 1 + 4·log 4` upward on a GRADE).

The six `ε` bounds the landed head reads off its pin are read off `ε ≤ 1/500` instead, by E1's
recipe (`SpineEpsFamily.lean:100`): each is `ε ≤ <numeral>` with the numeral above `1/500`.  The
count hook is `bigXi_bounded_ceiling_of_cap` (§2).  The conclusion slot is `P R`, built by `hP`
from the door AT THE MINT and the slot AT THE MINT — the door at `ρ ≤ δ₀` lifted to `δ₀` by
`mrtUniformityXiL2_mono`, the slot being the landed tail read at every `ρ' ≤ δ₀`. -/
theorem flat_head_uniform_xceil_eps (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (hcap : (1 : ℚ) / (500 * 8103) ≤ ε) (P : ChowlaRegime → Prop)
    (hP : ∀ R : ChowlaRegime, R.eps = ε →
      MRTUniformityXiL2 R ((ε : ℝ) / (256 * (1 + 4 * Real.log 4))) →
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) →
        MRTUniformityXiL2 R ρ → ¬ logChowla2Fails R.eps R.x R.ω) → P R) :
    FlatHeadFormEps ε P := by
  classical
  unfold FlatHeadFormEps
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := hreduce_holds_final_bounded
  obtain ⟨cD3', hcD3', hcD3'ge, H₀D3, hD3'⟩ := primeWindow_sum_inv_ge_bounded
  obtain ⟨C', hC', hCcap, hcm'⟩ := circle_method_estimate_sq_bounded (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  -- ⟦THE LEAVES' WITNESSES, PINNED⟧ the door-head's device (`DoorReceipt.lean:1012–1021`)
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = 1 + 2 * (2 * Real.log 4) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hcD3ge : 1 / 4 ≤ cD3 := by rw [hcD3def]
  have hC : 0 < C := by rw [hCdef]; positivity
  have hCnum : C ≤ 655 / 100 := by rw [hCdef, hlog4eq]; linarith
  have hCle : C' ≤ C := by rw [hCdef]; exact hCcap
  -- ⟦THE `ε` BOUNDS⟧ E1's recipe, read off `ε ≤ 1/500` instead of off the pin
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hεle : (ε : ℝ) ≤ 1 / 500 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε
    rwa [show (((1 : ℚ) / 500 : ℚ) : ℝ) = 1 / 500 by norm_num] at h
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    have h : (1 : ℝ) / 500 ≤ cE / (32 * Real.log 4) := by
      rw [le_div_iff₀ (by positivity), hlog4eq]; linarith
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by linarith
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    have h : (1 : ℝ) / 500 ≤ cD3 / 16 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
    linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    have h : (1 : ℝ) / 500 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    linarith
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (1 : ℚ) / 500 ≤ 1 / 2 := by norm_num
    linarith
  -- ⟦THE MINT⟧ the head's `δ₀` at the pinned witnesses IS the frozen file's term, exactly
  have hmint : cD3 / (16 * C) * (ε : ℝ) / 4 = (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) := by
    rw [hcD3def, hCdef]
    have hne : (1 : ℝ) + 2 * (2 * Real.log 4) ≠ 0 := by positivity
    field_simp
    ring
  have hqcap : (1 : ℚ) ≤ 4051500 * ε := by
    rw [div_le_iff₀ (by norm_num)] at hcap; linarith
  have hcapR : (1 : ℝ) ≤ 4051500 * (ε : ℝ) := by exact_mod_cast hqcap
  have hδnum : (1 : ℝ) / (838400 * 8103) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    rw [hmint, div_le_div_iff₀ (by norm_num) (by positivity), hlog4eq]
    linarith
  -- ⟦THE COUNT HOOK AT THE CAP⟧ §2, in place of the pinned hook
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded_ceiling_of_cap ε hε0 hε hcap
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat) — `A`-FREE, which is the whole point
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hε0, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hcap, hδnum, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ the landed proof chose `A := max A₀ (budgetAFlat ε β)` HERE
  intro A hA26 hAge
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro extraFloor U1floor g₅ hg₅
  obtain ⟨Rf, hReps, hRA, hRHlo, hRg, _hRcapEq, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil A hA26 ε hε0 hεQ1
      (max F (max extraFloor U1floor)) g₅ hg₅
  have hFlo : F ≤ Rf.Hlo := le_trans (le_max_left _ _) hRHlo
  have hxiHlo : H₀xi ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hFlo
  have hbudHlo : budgetFloorFlat (ε : ℝ) β A ≤ Rf.Hlo := by
    rw [hFdef] at hFlo; exact le_trans (le_max_right _ _) hFlo
  have hredHlo : max H₀red H₀D3 ≤ Rf.Hlo := by
    rw [hFdef, hOpqdef] at hFlo
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hFlo
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRx, ?_,
    fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact uniformCap_shuffle _ _ _ _ _
  -- ⟦THE SLOT⟧ `P R` from the door AT THE MINT and the tail AT THE MINT
  intro ρ _hρpos hρ hdoor
  refine hP Rf.toChowlaRegime hReps
    (mrtUniformityXiL2_mono (le_trans hρ hmint.le) hdoor) ?_
  intro ρ' _hρ'pos hρ'le hdoor' hfail
  have hρ4 : ρ' ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by rw [hmint]; exact hρ'le
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrementFlat Rf
  have hH4 : 4000000 ≤ H := le_trans Rf.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Rf.eps H : liouvilleWindow H ; logMeasure Rf.x Rf.ω]
      ≤ (H : ℝ) / (Rf.A * Real.log H) := by
    rw [mutualInfo_window_comm_flat]; exact hMI
  have hepsc : (Rf.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H := le_trans hredHlo hlo
  have hβR : cD3 * (Rf.eps : ℝ) / (144 * Real.log 4) = β := by rw [hReps, hβdef]
  have hAgeR : budgetAFlat (Rf.eps : ℝ) (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) ≤ Rf.A := by
    rw [hβR, hReps, hRA]; exact hAge
  have hfloorH : budgetFloorFlat (Rf.eps : ℝ)
      (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) Rf.A ≤ H := by
    rw [hβR, hReps, hRA]
    exact le_trans hbudHlo hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witnessFlat Rf H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hAgeR hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε`
  have hbudget2 : ρ' < cD3 / (16 * C) * (Rf.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ4, hpos]
  -- ⟦THE CORE⟧ at the FLAT threshold `κ = H/(A·log H)`, with the two transports supplied here
  refine spine_False_core_xi_sq_uniform Rf.toChowlaRegime hdoor' cE hcE H₀red hred cD3 hcD3
    H₀D3 ?_ C hC ?_ H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail
  · -- ⟦TRANSPORT 1⟧ the `D3` FLOOR moves DOWN to the pinned `1/4`
    intro eps H' hH0 hsq h1
    refine le_trans ?_ (hD3' eps H' hH0 hsq h1)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by rw [hcD3def]; exact hcD3'ge)
      (inv_nonneg.mpr (Real.log_natCast_nonneg H'))
  · -- ⟦TRANSPORT 2⟧ the circle-method GRADE moves UP to the pinned `1 + 2·(2·log 4)`
    intro eps H' _ x1 hx1 hcard
    refine le_trans (hcm' eps H' x1 hx1 hcard) ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle ?_) ?_
    · rw [div_eq_mul_inv]
      exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (Real.log_natCast_nonneg _))
    · positivity

/-! ## §4 — ⟦THE SEVEN REPLAYS AND THE CHAIN⟧ the landed bodies, at generic `ε` under the cap

Each replay is its landed body VERBATIM (`DoorReceipt.lean` §1) with the form names suffixed
`Eps`, `ε` threaded as the first parameter, and the `∃ ε` component dropped from every `obtain`
and `refine` tuple.  **Rows 1–5 read NO `ε` numeral at all** and are byte-identical otherwise.
The cap is spent at exactly four sites, each marked at the edit: the conditional's arm (row 6),
and the terminal's `flatWitFloor`/selector reads, the rated co-factor supply and the base-scale
cap (rows 7 and 7′).  Every one of those is the landed name's `_b9` twin at `h := 8103`, whose
binders are this file's `hεpin` and `epsChain_log_top_le_nine`. -/

/-- **⟦flat_socket_generic, AT GENERIC `ε`⟧** — `DoorReceipt`'s replay of the same
name, body VERBATIM, with the form names suffixed `Eps` and `ε` threaded as the first
parameter.  Any edit beyond that is commented AT the edit. -/
theorem flat_socket_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop) (h : FlatHeadFormEps ε P) :
    FlatSocketFormEps ε P := by
  unfold FlatSocketFormEps
  obtain ⟨K, δ₀, β, Hopq, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, hhead⟩ :=
    h
  obtain ⟨H₀, hH₀⟩ := sum_bigXi_norm_windowExpSum_sq_le_twelve ε hε
  refine ⟨K, δ₀, β, max Hopq H₀, hε, hK, hKb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro A hA162 hAge
  obtain ⟨Hcap, hCapEq, hhd⟩ := hhead A (by linarith) hAge
  refine ⟨max Hcap H₀, by rw [hCapEq]; exact uniformCap_arc _ _ _ _ _, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, _, hRU1, hRg, hRx, hcount, hRtow, hRcap, hR⟩ :=
    hhd 0 (max U1floor H₀) g hg
  have hU1 : U1floor ≤ R.Hlo := le_trans (le_max_left _ _) hRU1
  have harc : H₀ ≤ R.Hlo := le_trans (le_max_right _ _) hRU1
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, le_trans hRcap (by omega), ?_⟩
  intro a e Bsieve Binsert hsplit hB0 hsock hins hρ
  refine hR δ₀ hδ₀ le_rfl ?_
  intro H _ hlo hhi
  exact le_trans (hH₀ R hReps harc a e Bsieve K Binsert hsplit hB0 hsock hcount hins
    H hlo hhi) (hρ H hlo hhi)

/-- **⟦flat_doorL2_generic, AT GENERIC `ε`⟧** — `DoorReceipt`'s replay of the same
name, body VERBATIM, with the form names suffixed `Eps` and `ε` threaded as the first
parameter.  Any edit beyond that is commented AT the edit. -/
theorem flat_doorL2_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop) (h : FlatSocketFormEps ε P) :
    FlatDoorL2FormEps ε P := by
  unfold FlatDoorL2FormEps
  obtain ⟨Cg, hCg, hCgle, hpars⟩ := parseval_insert_budget_door_bounded
  obtain ⟨Kb, δ₀, β, Hopq, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hsk⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapLe, hexit⟩ := hsk A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hexit U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  have hA : 1 ≤ AdoorL M := one_le_AdoorL hgates.hM
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2
      liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (AdoorL M) (s13GK K M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · intro H hlo hhi
    rw [l2_budget_line Kb (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * Kb * Braw H ≤ 2 * Kb * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

/-- **⟦flat_road_generic, AT GENERIC `ε`⟧** — `DoorReceipt`'s replay of the same
name, body VERBATIM, with the form names suffixed `Eps` and `ε` threaded as the first
parameter.  Any edit beyond that is commented AT the edit. -/
theorem flat_road_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop) (h : FlatDoorL2FormEps ε P) :
    FlatRoadFormEps ε P := by
  unfold FlatRoadFormEps
  obtain ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, hdoor⟩ :=
    h
  refine ⟨Cg, Kb, δ₀, β, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ, ?_⟩
  intro K A hA162 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hdoor K A hA162 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ := hmain U1floor g hg
  refine ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, ?_⟩
  intro δ Bceil RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3
    hdgate hdrift hceil hbudget hrow
  have harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    intro H hlo hhi
    have h1 := harc3 H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    nlinarith [h1, harc1]
  have hchi : M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L_gk K j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hblk2 :=
    m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR Braw Bceil δ M k hgates hBraw0 ?_ hceil hbudget
  refine m4_sievedDoorSq_of_blk2_L_gk K (ℓ := blockLen)
    (fun H => by have := hBblk0 H; positivity)
    (fun H q _ _ _ _ => one_le_blockLen H q) ?_ ?_ ?_ ?_ hcov
  · intro H q hlo hhi _ _
    have h1 := harc H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hH1 : 1 ≤ H := by
      have : (1 : ℝ) ≤ (H : ℝ) := by nlinarith
      exact_mod_cast this
    exact blockLen_le H q hH1
  · intro H q hlo hhi _ _
    exact blockLen_narrow (R := R) hlo (harc H hlo hhi)
  · intro H q hlo hhi hq _
    exact blockLen_drift (R := R) hlo hq (harc H hlo hhi)
  · intro H hlo hhi
    have h := hdrift H hlo hhi
    have hres0 : (0 : ℝ) ≤ strataResidual H :=
      strataResidual_nonneg (one_le_arcDen_of_regime (R := R) hlo)
    have hB := hBcl0 H
    nlinarith [h]

/-- **⟦flat_capstone_generic, AT GENERIC `ε`⟧** — `DoorReceipt`'s replay of the same
name, body VERBATIM, with the form names suffixed `Eps` and `ε` threaded as the first
parameter.  Any edit beyond that is commented AT the edit. -/
theorem flat_capstone_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop)
    (h : FlatRoadFormEps ε P) (Awin : ℝ) (hband : S16BandLaneCBoundedL_winU Awin) :
    FlatCapstoneFormEps ε P Awin := by
  unfold FlatCapstoneFormEps
  obtain ⟨Cg, Kc, δ₀, β, Hopq, hCg, hCgle, hε, hKc, hKcb, hδ₀, hεpin, hδpin, hβ, hroadU⟩ :=
    h
  obtain ⟨x₀, Cband, hCband0, hCbandwin, hbandsplit⟩ := hband
  refine ⟨Cg, Kc, δ₀, β, x₀,
    max Hopq (max arcFloor36 loglogFloor50),
    s11GradeFloor (Cband * (4 : ℝ) ^ (s13Aexp)
      * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1),
    hCg, hε, hKc, hδ₀, s11GradeFloor_one_le _, hCgle,
    hεpin, hδpin, hKcb,
    (fun A hA162 hAw => flatDoorM_gradeFloor_win hA162 hCband0 (by linarith)),
    hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hfuse⟩ := m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling_kwide K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hroad⟩ := hroadU K A hA26 hAge
  refine ⟨max Hcap (max arcFloor36 loglogFloor50), flatCap_join_floor hCapLe, ?_⟩
  intro Cp hCp U1floor g hg
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hR⟩ :=
    hroad (max U1floor (max arcFloor36 loglogFloor50)) g hg
  refine ⟨R, hReps, le_trans (le_max_left _ _) hU1, hRg, hRx, hRtow, by omega, ?_⟩
  intro M hMfloor hKw
  have hM : 1 ≤ M := le_trans (s11GradeFloor_one_le _) hMfloor
  obtain ⟨C', hC'pos, hC'le, hbandslot⟩ := hbandsplit K M hM
  refine ⟨C', hC'pos, s11_grade_absorption'_L _ M hMfloor C' hC'le, ?_⟩
  intro C₁ M₀ _epsf epsrf Kf k hgates hend hj0 hdgate hfit hbf hgP1 hgRows hthr _heps293
    hband4096 _hepsr hbase5 hcapraw hbandbase harith
  -- ⟦the two absorbed floors⟧
  have harcfl : arcFloor36 ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hllfl : loglogFloor50 ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hllfl hlo)
  -- ⟦A1⟧ the socket's own threshold, and its `ρ`
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  have hδssq : δs ^ 2 = δ₀ / (16 * Kc) := s12DeltaSock_sq hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρpos : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦S2-COEFWS⟧ the row bundle's ONE analytic field, witnessed; the family pinned
  have hbase : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorRowZeroBase_L_gk K M (A + s) j liouvilleC
        (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC) := by
    intro H L q j A s hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbase5 H L q j A s hb
    exact ⟨h1, doorRowZeroBase_coefWS_witness_L_gk K (A + s) hM, h2, h3, h4, h5⟩
  -- ⟦ITEM 11, FROM THE CONSTANT-POOL FUSE⟧ at the door pin `t₁ ≡ 0`
  have hrow : M4ChiSummedFreeRow_L_gk K R M
      (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) :=
    hfuse Cp hCp R M C₁ M₀ epsrf Kf ρ liouvilleC
      (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 i liouvilleC)
      (fun _ _ => (0 : ℝ)) hM hKw hρpos (fun i m => norm_doorPunctCoeffU_le_one_L_gk K M i m)
      (fun p => liouvilleC_norm_le_one p) hbf hgP1 hgRows hthr _heps293 hband4096 hbase
      hcapraw (hbandslot R C₁ M₀ hbandbase) harith
  -- ⟦THE TWO TERMINAL CONJUNCTS⟧
  have hgate4 : ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
    m4_arith_gate4_rho_L M ρ
  have hceilconj : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
        ≤ δs ^ 2 := by
    intro H hlo hhi
    exact m4_arith_rs_ceiling_met_of_delta hδs.ne' (hHreg H hlo hhi).1 (hHreg H hlo hhi).2
  -- ⟦the road, fired at the share table⟧
  refine hR δ₀ (δ₀ / (8 * Kc))
    (m4ChiRowGraded_L M (fun _ H => RSanDoorRho ρ H)) (RSanDoorRho ρ) rStrWitness
    (fun H => 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
      * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
          (fun H => 2 * rStrWitness H) H)
    M k (doorRowFloorL M) hgates hM (fun H => RSanDoorRho_nonneg hρpos.le H)
    rStrWitness_nonneg ?_ hgate4 (fun H _ _ => rStrWitness_G1 H) ?_
    (arc36_of_regime harcfl) hdgate (fun H _ _ => le_rfl) ?_ ?_ hrow
  · -- ⟦gate 3c⟧ `0 ≤ Braw`
    intro H
    have hb := m4BclGraded_nonneg (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) (H := H)
      (by have := RSanDoorRho_nonneg hρpos.le H
          simpa using (by linarith : (0:ℝ) ≤ 2 * RSanDoorRho ρ H))
      (by have := rStrWitness_nonneg H
          simpa using (by linarith : (0:ℝ) ≤ 2 * rStrWitness H))
    positivity
  · -- ⟦gate 6⟧ ⟦G2⟧ at the `j₀`-floor
    intro H hlo hhi
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hSR1 : (1 : ℝ) ≤ strataResidual H := by
      have : (0 : ℝ) ≤ Real.log (arcDen 12 H) := Real.log_nonneg harc1
      unfold strataResidual
      linarith
    have hSRsq : (1 : ℝ) ≤ strataResidual H ^ 2 := by nlinarith
    have hRSle : RSanDoorRho ρ H ≤ rSanWitness H := by
      have h1 : RSanDoorRho ρ H ≤ 1 := by
        unfold RSanDoorRho
        rw [div_le_one (by nlinarith)]
        linarith
      exact le_trans h1 (le_max_left _ _)
    have hG := g2_of_j0_floor H (j₀ := doorRowFloorL M) (hj0 H hlo hhi)
    linarith
  · -- ⟦gate 10a⟧ the `H`-uniform ceiling, at TWO `δ_sock²`
    intro H hlo hhi
    have hH0 : 0 < H := by
      have := R.hHlo_floor
      omega
    have hle := m4BclGraded_le_of_fits (j₀ := doorRowFloorL M)
      (Fan := fun H => 2 * RSanDoorRho ρ H) (Ftr := fun H => 2 * rStrWitness H) hH0
      (hfit H hlo hhi)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
    have hceil := hceilconj H hlo hhi
    have hstep : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * m4BclGraded (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
            (fun H => 2 * rStrWitness H) H
        ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H))) :=
      mul_le_mul_of_nonneg_left hle hfac0
    have hval : 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * (2 * (m4Cmax H * (2 * RSanDoorRho ρ H)))
        = 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
            * (108 / 5 * RSanDoorRho ρ H)) := by
      unfold m4Cmax
      ring
    rw [hval] at hstep
    have h2 : 2 * (96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho ρ H)) ≤ 2 * δs ^ 2 := by linarith
    have hKcpos : (0 : ℝ) < 16 * Kc := by linarith
    have hval2 : 2 * δs ^ 2 = δ₀ / (8 * Kc) := by
      rw [hδssq]
      field_simp
      ring
    linarith [hstep, h2, hval2.le, hval2.ge]
  · -- ⟦gate 10b⟧ the budget line: the share table sums to `δ₀` exactly
    have hval : 2 * Kc * (δ₀ / (8 * Kc)) = δ₀ / 4 := by
      field_simp
      ring
    rw [hval]
    linarith [hend]

/-- **⟦flat_conditional_generic, AT GENERIC `ε`⟧** — `DoorReceipt`'s replay of the same
name, body VERBATIM, with the form names suffixed `Eps` and `ε` threaded as the first
parameter.  Any edit beyond that is commented AT the edit. -/
theorem flat_conditional_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatCapstoneFormEps ε P Awin) :
    FlatConditionalFormEps ε P Awin := by
  unfold FlatConditionalFormEps
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hCg, hε, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcapU⟩ :=
    h
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcapK⟩ := hcapU K
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro A hA26 hAge
  obtain ⟨Hcap, hCapLe, hmain⟩ := hcapK A hA26 hAge
  refine ⟨Hcap, hCapLe, ?_⟩
  intro U1floor g hg hU
  set δs : ℝ := s12DeltaSock δ₀ Kc with hδsdef
  have hδs : 0 < δs := s12DeltaSock_pos hδ₀ hKc
  set ρ : ℝ := doorRhoOfDelta δs with hρdef
  have hρ0 : 0 < ρ := doorRhoOfDelta_pos hδs.ne'
  have hρ1 : ρ ≤ 1 := doorRhoOfDelta_le_one δs
  -- ⟦THE ONE GENUINE ESTIMATE, SPENT⟧ the substituted `g' = s15Arm δ₀ ρ + g` still obeys the
  -- builder-side rider.  THE ONE EDIT ON THIS HOP: the arm is priced by `s15Arm_log_le_scaled`
  -- at `c := 8103` (the form's own `δ₀` pin `1/(838400·8103)`) and the sum split's `log 2` is
  -- paid by §0's `epsChain_arm_split_cap` — the gate's TOWER, not the caller's `ε ≥ 1/500`.
  have hlog8103R : Real.log (8103 : ℝ) ≤ 9 := by
    have hc : ((8103 : ℕ) : ℝ) = (8103 : ℝ) := by norm_num
    calc Real.log (8103 : ℝ) = Real.log ((8103 : ℕ) : ℝ) := by rw [hc]
      _ ≤ 9 := epsChain_log_top_le_nine
  have hg' : XCeilRider ε (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) := by
    intro Hhi ω hgate
    obtain ⟨hH4, hll, hωw⟩ := hgate
    have hHnn : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) := by positivity
    have hsplit2 : Real.log 2
        ≤ (ε : ℝ) ^ 2 * ((Hhi : ℕ) : ℝ) - ((Hhi : ℕ) : ℝ) / 10 ^ 20 :=
      epsChain_arm_split_cap hεpin hH4 hll
    have harm : Real.log ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ Real.log ((ω : ℕ) : ℝ) + ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by
      rw [hρdef, hδsdef]
      exact s15Arm_log_le_scaled (c := 8103) (by norm_num) (by norm_num)
        (by linarith) hδ₀ (by linarith [hδpin]) hKc hKcb hH4 hll
    have hgb := hg Hhi ω ⟨hH4, hll, hωw⟩
    have hHdiv : (0 : ℝ) ≤ ((Hhi : ℕ) : ℝ) / 10 ^ 20 := by positivity
    have harm' : Real.log ((s15Arm δ₀ ρ Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 := by linarith
    have hgb' : Real.log ((g Hhi ω : ℕ) : ℝ)
        ≤ 31 / (ε : ℝ) * ((Hhi : ℕ) : ℝ) - Real.log 2 := by linarith
    have hsum := xt_log_add_le harm' hgb'
    exact le_trans hsum (by linarith)
  obtain ⟨R, hReps, hU1, hRg, hRx, hRtow, hRcap, hfire⟩ :=
    hmain 0 le_rfl U1floor (fun Hhi ω => s15Arm δ₀ ρ Hhi ω + g Hhi ω) hg'
  have hRarm : s15Arm δ₀ ρ R.Hhi R.ω ≤ R.x := by omega
  have hRgg : g R.Hhi R.ω ≤ R.x := by omega
  have hHcapU : Hcap ≤ U1floor := le_trans (le_max_left _ _) hU
  have hHlo : R.Hlo = U1floor := by
    have : max Hcap U1floor = U1floor := max_eq_right hHcapU
    omega
  have hfl : loglogFloor50 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU
    omega
  have harcfl : arcFloor36 ≤ R.Hlo := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU
    omega
  refine ⟨R, hReps, hHlo, hRgg, hRx, hRtow, ?_⟩
  intro M hsel hKw
  obtain ⟨C', hC'pos, hgrade, hgo⟩ := hfire M hsel.mfloor hKw
  intro hcap
  obtain ⟨-, hlam50⟩ := regime_Hfloor_of_loglogFloor50 hfl
  obtain ⟨-, hΛ50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl R.hHlohi)
  have htow : Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ Real.exp (Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) / 2) := hRtow hlam50
  have hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)) :=
    fun H hlo _ => regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have harmdem : s13GArm' δ₀ R.Hhi R.ω ≤ R.x :=
    le_trans (s15Arm_demoted δ₀ ρ R.Hhi R.ω) hRarm
  have hωpos : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hgarm : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ) := by
    intro H hlo hhi
    refine le_trans (s15_gArmDoorRho_mono hωpos ?_ hhi) (s15Arm_rho hRarm)
    have hreg := hHreg H hlo hhi
    have := one_lt_log_of_loglog_ge hreg.1 (by norm_num : (0:ℝ) < 50) hreg.2
    linarith
  -- ⟦ITEM 16⟧ the arithmetic frame family, at the LINEAR anchor
  have harith := s15_doorArithFrameRho_L_family'' (C₁ := fun _ : ℕ => (1 : ℝ)) hsel.hM hρ0 hρ1
    hsel.anchor hHreg hgarm (fun _ => zero_le_one)
  -- ⟦the `M`-selection system⟧
  have hS : MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
    s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hsel.gRows hsel.half
      (hsel.head (by linarith))
  -- ⟦the band register⟧
  have hgate : S13BandGate'_L_gk K R M x₀ C' (fun _ => 1) :=
    s15_bandGate''_of_grade_L_gk K hfl hsel hgrade
  -- ⟦THE FIRE⟧
  refine hgo (fun _ => (1 : ℝ)) (s13BandM0 R ρ (fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (fun _ => theta293 - 1 / 500) 0 (doorCount R.ω)
    (s13_doorGates_of_MSelect'_L_gk K hsel.hM hδ₀ hS harmdem)
    (s13_endpoint_of_arm' hδ₀ harmdem)
    (s13_g2_jfloor_gen le_rfl (s13_g2_jfloor_of_MSelect'_L_gk K (by linarith) hS))
    (s13_gate8_L_gk le_rfl (s13_gate8_of_MSelect'_L_gk K (by linarith) hS))
    (s13_smallGradeFits_of_MSelect'_L_gk K hρ0 hρ1 hS)
    (fun H L q j A s hb => doorBaseFrame_at_socket_L hb (harith H L q j A s hb))
    (fun _ _ _ _ _ _ _ => s15_gP1_of_budget_gen hCt hρ0 hsel.gP1)
    (fun H L q j A s hb =>
      s15_gRows_const_at_socket_flat_doorL_gk K hfl hb hsel.hM hρ0 hρ1 htow hsel.rho
        hsel.lvl)
    (fun H L q j A s hb =>
      s12c_eps_threshold_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hlam50 htow
        hsel.rho le_rfl)
    (fun H L q j A s hb =>
      s15_heps293_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun H L q j A s hb =>
      s15_hband4096_at_socket_flat hfl (socketBase_of_socketBaseL hsel.hM hb) hρ0 hlam50 htow
        hsel.rho)
    (fun _ _ _ _ _ _ _ => ⟨by have := s13_theta293_margin_lo; linarith, le_rfl⟩)
    (fun H L q j A s hb =>
      s13_doorRowZeroBase_five_L_gk K hsel.hM (hgate.block H L q j A s hb)
        hb.2.2.2.2.2.2.1)
    hcap
    (doorBandBase_family'_L_gk K hsel.hM hρ0 hρ1 (fun _ => le_rfl) hHreg
      (hgarm R.Hhi R.hHlohi le_rfl) harith hgate)
    harith

/-- **⟦flat_kswin_generic, AT GENERIC `ε`⟧** — `DoorReceipt`'s replay of the same
name, body VERBATIM, with the form names suffixed `Eps` and `ε` threaded as the first
parameter.  Any edit beyond that is commented AT the edit. -/
theorem flat_kswin_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatConditionalFormEps ε P Awin) :
    FlatKswinFormEps ε P Awin := by
  unfold FlatKswinFormEps
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    h
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ := s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max 162 (budgetAFlat (ε : ℝ) β)) (le_max_left _ _) (le_max_right _ _)
  have hzero : XCeilRiderStrict ε (fun _ _ : ℕ => 0) := by
    intro Hhi ω hgate
    obtain ⟨-, -, hωw⟩ := hgate
    simp only [Nat.cast_zero, Real.log_zero]
    linarith [Real.log_natCast_nonneg ω]
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε2q
    rw [show (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  -- ⟦THE CAP, IN THE TWO SPELLINGS THE `_b9` TWINS TAKE⟧ the real one through the four-line
  -- cast (ONE `exact_mod_cast` does not lift a divided cap), the rational one directly
  have hεR : (1 : ℝ) / (500 * ((8103 : ℕ) : ℝ)) ≤ (ε : ℝ) := by
    have hq := hεpin
    rw [div_le_iff₀ (by norm_num)] at hq
    have h1R : (1 : ℝ) ≤ 4051500 * (ε : ℝ) := by
      have hh : (1 : ℚ) ≤ 4051500 * ε := by linarith
      exact_mod_cast hh
    rw [div_le_iff₀ (by norm_num)]
    push_cast
    linarith
  have hεpinQ : (1 : ℚ) / (500 * ((8103 : ℕ) : ℚ)) ≤ ε := by exact_mod_cast hεpin
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge
  refine ⟨fun hopq => flat_witFloor_eq_designBase_h_b9 (h := 8103) (by norm_num)
    epsChain_log_top_le_nine hA26 hβ hεR hε2 hε hεpinQ hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase_h_b9 (h := 8103) (by norm_num)
      epsChain_log_top_le_nine hA26 hβ hεR hε2 hε hεpinQ hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  have heps : (1 : ℚ) / (2 ^ 9 * ((8103 : ℕ) : ℚ)) ≤ R.eps := by
    rw [hReps]
    have hb : (1 : ℚ) / (2 ^ 9 * ((8103 : ℕ) : ℚ)) ≤ 1 / (500 * 8103) := by norm_num
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  have hδb : (1 : ℝ) / (838400 * 2 ^ 12 * ((8103 : ℕ) : ℝ) ^ 2) ≤ δ₀ := by
    refine le_trans ?_ hδpin
    have hc : ((8103 : ℕ) : ℝ) = (8103 : ℝ) := by norm_num
    rw [hc, div_le_div_iff₀ (by norm_num) (by norm_num)]
    norm_num
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win_h_g12b (h := 8103) hA26 K hKw
    (by norm_num) epsChain_log_top_le_nine hδ₀ hδb hKc hKcb
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)

/-- **⟦flat_v7_generic, AT GENERIC `ε`⟧** — `DoorReceipt`'s replay of the same
name, body VERBATIM, with the form names suffixed `Eps` and `ε` threaded as the first
parameter.  Any edit beyond that is commented AT the edit. -/
theorem flat_v7_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop)
    (h : ∀ Awin : ℝ, S16BandLaneCBoundedL_winU Awin → FlatKswinFormEps ε P Awin)
    (A₀ : ℝ) :
    V7RatedFormEps ε P A₀ := by
  unfold V7RatedFormEps
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ four Skolem REALS, minted outside everything
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated_h_b9 8103 (by norm_num) epsChain_log_top_le_nine
  obtain ⟨Awin, -, hband⟩ := s16_bandLaneWinL_holdsU
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    h Awin hband
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ the seven landed arms verbatim (`A'`), the eighth
  -- (`armVt Kvt`) outermost — every constant still minted BEFORE the lever: `Kvt` arrives at
  -- the supply obtain above, before the mint.
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (armVt Kvt) A' := ⟨_, rfl⟩
  have harmA : armVt Kvt ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hlift : A' ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) := by
    have h2 : Real.exp (3.2 * A) / 10 + 1 ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
      Real.add_one_le_exp _
    linarith
  have hopq : Hopq ≤ flatDesignBase A := by
    have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
    have hR : ((Hopq : ℕ) : ℝ) ≤ Real.exp (Real.exp (3.2 * A)) := by linarith
    have hceil := le_trans hR (Nat.le_ceil (Real.exp (Real.exp (3.2 * A))))
    rw [flatDesignBase]; exact_mod_cast hceil
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  -- ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider; the `g`-conjunct is discarded
  obtain ⟨R, hReps, hHlo, -, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin (fun _ _ : ℕ => 0)
      (xceilRiderStrict_zero ε)
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / (500 * ((8103 : ℕ) : ℚ)) ≤ R.eps := by
    rw [hReps]; exact_mod_cast hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have heps500R : (1 : ℝ) / (500 * ((8103 : ℕ) : ℝ)) ≤ (R.eps : ℝ) := by
    rw [hReps]
    have hq := hεpin
    rw [div_le_iff₀ (by norm_num)] at hq
    have h1R : (1 : ℝ) ≤ 4051500 * (ε : ℝ) := by
      have hh : (1 : ℚ) ≤ 4051500 * ε := by linarith
      exact_mod_cast hh
    rw [div_le_iff₀ (by norm_num)]
    push_cast
    linarith
  have h518 : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by nlinarith [hdes, hA162]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  have hthrgate : cofkRThr Cq Cb Xsk Y0 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1]
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    s16CofactorSupply_L_of_LH (by norm_num)
      (hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush)
  have hfireR : P R :=
    hfire2 hcofsupply
      (s16BaseScaleCap96_L_of_LH (by norm_num)
        (s16_baseScaleCap96_LH_at_klevF_b9 (h := 8103) (by norm_num) epsChain_log_top_le_nine
          hA26 (flatDoorM_one_le hA26) heps500 hxceil hwin))
  exact ⟨Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A,
    R, hReps, by rw [hHlo]; exact hbase hopq, hRtow, hdes, hwin, hfireR⟩

/-- **⟦THE CHAIN, AT GENERIC `ε`⟧** (`flat_chain_generic_eps`) — H1 ∘ … ∘ H7 at the cap:
`flat_chain_generic` (`DoorReceipt.lean:1076`) with every hop's `_eps` sibling.  The cap and the
`δ₀` pin travel INSIDE the forms, so no hop takes them as a hypothesis and this composition is
the landed one token for token. -/
theorem flat_chain_generic_eps (ε : ℚ) (P : ChowlaRegime → Prop) (h : FlatHeadFormEps ε P)
    (A₀ : ℝ) : V7RatedFormEps ε P A₀ :=
  flat_v7_generic_eps ε P (fun Awin hband => flat_kswin_generic_eps ε P Awin
    (flat_conditional_generic_eps ε P Awin
      (flat_capstone_generic_eps ε P (flat_road_generic_eps ε P (flat_doorL2_generic_eps ε P
        (flat_socket_generic_eps ε P h))) Awin hband))) A₀

end Salt.MR

end
