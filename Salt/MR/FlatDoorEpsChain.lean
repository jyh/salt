/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorReceipt
import Salt.MR.V7RatedH
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

end Salt.MR

end
