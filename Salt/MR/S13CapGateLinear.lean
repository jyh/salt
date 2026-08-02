/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16Budget
import Salt.MR.S13BandCapLinear
import Salt.MR.M4CapWireLinear
import Salt.MR.M4RowLinear
import Salt.MR.DoorLadderLinear

/-!
# `S13CapGateLinear` — THE CAP-GATE LANE AT THE LINEAR DOOR

⟦CAPGATE-L⟧  `S13FramesB` §8's per-block cap gate, its two bundles and the `S13CapGrid`
grid supply, re-cut at `AdoorL M = 2^36·M` with the `G`-slot `s13GK K M` and the width slot
`H1doorL M`.  Every statement is the landed one with the anchor substituted; every proof is
the landed body with the three door-unfolding steps re-routed through
`DoorLinear.one_le_AdoorL` / `DoorLadderLinear.H1door_two_L`.

⟦WHAT WAS ALREADY PAID⟧ `S13BandCapLinear` landed `s13CapFloor_all_L{,_gk}` (8 of the gate's
37 fields) and the two `𝒬K₂` reads; `S13FramesLinear` landed `s13_doorRowZeroBase_five_L_gk`,
which is the ONE door-reading field of the grid wave.  `M4CapWireLinear` landed
`DoorCapBasePerBlock_L_gk` and `m4_capRbd_at_door_L_gk`; `M4RowLinear`'s `G2Scaffold` landed
`DoorCapErrWS_L_gk` and `doorCoeffU_L_gk`.  What is minted here is exactly the join.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the two pins at the linear door -/

/-- `s13VJ_gk (S13FramesB:1511)` at the linear door. -/
def s13VJ_L_gk (K : ℕ) (M : ℕ) : ℝ :=
  Real.exp (mrAlpha (1 / 12) 2 * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ))

/-- `s13Mtail_gk (S13FramesB:1515)` at the linear door. -/
def s13Mtail_L_gk (K : ℕ) (M Nd P Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
    ‖winCutH Nd (doorCoeffU_L_gk K M) n‖ ^ 2 / (n : ℝ) ^ 2

/-- `doorCoeffU_seamCoefWS_band_H_gk (S13FramesB:1501)` at the linear door.  The band pair
law is `(Pseq, Qseq)`-abstract, so this is a re-instantiation. -/
theorem doorCoeffU_seamCoefWS_band_H_L_gk (K : ℕ) (M Xd P Q : ℕ)
    (hgate : ∀ i ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M i < P) :
    SeamCoefWS Xd P Q (winCutH Xd (doorCoeffU_L_gk K M)) (doorCoeffU_L_gk K M) liouvilleC :=
  memSCoeff_seamCoefWS_band_gen_U (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) 2 Xd P Q _ hgate
    (fun _ h1 h2 => winCutH_of_mem _ h1 h2)

/-- `m4_capKS_at_door_perBlock_gk (M4CapWire:1472)` at the linear door — the `𝒯_S` price is
datum-abstract, so only the door datum's name moves. -/
theorem m4_capKS_at_door_perBlock_L_gk (K : ℕ) {M Nd Xd P Q : ℕ} {Mr : ℕ → ℕ} {Tann : ℝ}
    (m₀ : ℕ → ℕ)
    (hlogX : 0 ≤ Real.log ((Nd : ℕ) : ℝ)) (hT : 1 ≤ Tann)
    (hm₀2 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 2 ≤ m₀ j)
    (hm₀ : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 ((Nd : ℕ) : ℝ) theta293) Xd j)
    (hMs : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd j ⊆ Finset.Icc 1 (Mr j))
    (hMs4 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ((Mr j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) :
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      5128 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * ((Mr j : ℕ) : ℝ)
          * (1 + Real.log (2 * Tann))
          * (∑ m ∈ Finset.Icc 1 (Mr j),
              ‖ramRcoeff (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j
                (doorCoeffU_L_gk K M) m‖ ^ 2 / (m : ℝ) ^ 2)
        ≤ 20512 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * (1 + Real.log (2 * Tann)) := by
  have hsq : ((Real.log ((Nd : ℕ) : ℝ)) ^ (-100 : ℝ)) ^ 2
      = (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) := by
    rw [← Real.rpow_natCast ((Real.log ((Nd : ℕ) : ℝ)) ^ (-100 : ℝ)) 2,
      ← Real.rpow_mul hlogX]
    norm_num
  intro j hj
  have hbase := KS_priced (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j (doorCoeffU_L_gk K M)
    (norm_doorCoeffU_le_one_L_gk K M) (m₀ j) (Mr j) (hm₀2 j hj) (hm₀ j hj) (hMs j hj)
    (hMs4 j hj) Tann ((Real.log ((Nd : ℕ) : ℝ)) ^ (-100 : ℝ)) hT
  rwa [hsq] at hbase

/-! ## §2 — ⟦THE 37-FIELD GATE AT THE LINEAR DOOR⟧ -/

/-- `S13FramesB.S13CapGatePerBlock_gk (:1996)` at the linear door.  Five fields move —
`QTann`, `kappa30Q`, `Q2_reg`, `budget`, `Rbd_socket` — and they move by anchor substitution
only; the other thirty-two are the landed terms verbatim. -/
structure S13CapGatePerBlock_L_gk (K : ℕ) (Cq cs T₀ Kq Ks C : ℝ) (M Nd q P Q Hreg : ℕ)
    (Tann Rrad Rbd CR EP2 εr : ℝ) : Prop where
  -- ⟦THE SCALE FLOOR⟧
  /-- `8 ≤ log X` — §3's `logX_four` strengthened by one octave (§8a's grid floor). -/
  logX_eight : 8 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `2 ≤ H₈₃ X θ₂₉₃` — ONE field for both bundles. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  -- ⟦(A) THE RAZOR — the three that do not reduce⟧
  /-- `𝒬K₂ ≤ q·T_ann`. -/
  QTann : ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- ⟦MR (21)⟧'s κ-gate at the designated level. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}` — the capstone's base-side modulus gate. -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  -- ⟦(B) THE SOCKET FLOOR AT `(q, T_ann)`⟧
  /-- `T₀ ≤ T_ann`. -/
  T0_Tann : T₀ ≤ Tann
  /-- Floor gate 1. -/
  floor1 : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 2. -/
  floor2 : 8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
    ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 3 — the `Kq` arm. -/
  floor3 : Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
    ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)
  /-- Floor gate 4 — the `Ks` arm. -/
  floor4 : (q : ℝ) ^ ((1 : ℝ) / 16)
    ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
  /-- `log(q·T_ann) ≤ Lr` at the pinned `Lr = (log X)^{11/10}`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ s13Lr Nd
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `P₈₃ X θ₂₉₃ ≤ P`. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `log 𝒬K₂ ≤ √(log X)` — `DoorRowZeroBase.reg` VERBATIM (§1's band gate). -/
  Q2_reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
    ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- `P ≤ Q` — the band is a band.  ⟦NOTHING relates `P` and `Q` beyond this⟧: the
  point-band forcing of §3's header was the scalar `Mr`'s artifact and is gone. -/
  P_le_Q : P ≤ Q
  /-- ⟦THE GRADED BUDGET, PER-BLOCK⟧ at the pinned `VJ`, `η`, `εd` and the per-block cap. -/
  budget : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    thinBundleGChi ((q : ℝ) * Tann) (s13VJ_L_gk K M) (calH (H1doorL M) 2)
        (calP (AdoorL M) (s13GK K M) 2) (calQK (AdoorL M) (s13GK K M) M 2)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ ((s13Mr Nd j : ℕ) : ℝ)
  /-- `H₈₃ ≤ j` on the grid. -/
  Hj : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    H83 ((Nd : ℕ) : ℝ) theta293 ≤ (j : ℝ)
  /-- `3 ≤ Q_base` on the grid. -/
  B3 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    3 ≤ ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j
  /-- `Q_base ≤ q·T_ann` on the grid. -/
  BT : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ (q : ℝ) * Tann
  /-- The κ-gate on the grid. -/
  kappa30 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)
  /-- `Q_base ≤ T_ann^{10}` on the grid. -/
  BT10 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ Tann ^ 10
  /-- `log Q_base ≤ Lr` on the grid. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ s13Lr Nd
  /-- The `cs`-gate on the grid — the field that CAPS `Lr` from above. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` SUPPLY⟧ the door's un-phased co-factor socket at the free centre. -/
  Rbd_socket : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
    CofactorSocket (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q Tann Rrad t₁ Rbd
      (doorCofactor0 χ (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 1)
  -- ⟦(F) LEMMA 12's ERROR ROW, ROW BY ROW⟧
  /-- `0 ≤ εr`. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}`. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- ⟦THE `φ(q)` LINE — correction 3's honest home⟧ `q ≤ arcDen 12 H = (log H)^{12}`, the
  H-SIDE modulus ledger `SocketBase` itself carries.  The `φ(q)` row does NOT close against
  the base-side `q_logX`; it closes here. -/
  q_arcDen : (q : ℝ) ≤ arcDen 12 Hreg
  /-- ⟦THE `φ(q)` ROW⟧ `4·520·φ(q)·W ≤ EP2` in the sufficient form `W ≤ 2μ^{−θ₂₉₃}` — the
  `4·520·φ(q)` vs `3·720` excess, charged to `EP2`.  Refuter form:
  `εr·μ ≥ log 16640 + 12·log log H + log(8Cμ)` (27 orders at the floor). -/
  phi_row : 4160 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) ≤ EP2
  /-- ⟦THE `p²`/END-MASS ROW⟧ against `EP2`. -/
  p2_row : 4 * (2 * (q.totient : ℝ) * Tann
        + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
      * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ)) + endMass Nd)
    ≤ EP2
  /-- ⟦THE COPRIME-TAIL ROW⟧ at the BAND value of `Mtail`, against `EP2`. -/
  tail_row : 4 * (2 * (q.totient : ℝ) * Tann
        + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * s13MtailBand C Nd P Q
    ≤ EP2
  /-- ⟦THE TAIL BAND's SIDE CONDITION 1⟧ `100·log Q ≤ log X_d`. -/
  Q_hundred : 100 * Real.log (Q : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- ⟦THE TAIL BAND's SIDE CONDITION 2⟧ the band product. -/
  band_product : ((Nat.sqrt Nd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
    ≤ ((Nd : ℕ) : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))

/-! ## §3 — the two bundles at the linear door -/

set_option maxHeartbeats 1000000 in
-- eleven fields of the error bundle re-elaborate against the levered datum
/-- `S13FramesB.s13_doorCapErrWS_perBlock_gk (:2115)` at the linear door. -/
theorem s13_doorCapErrWS_perBlock_L_gk (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {M Nd q P Q Hreg : ℕ}
    {Tann Rrad Rbd CR EP2 εr : ℝ}
    (hband : ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 100 * Real.log Q ≤ Real.log Xd →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
    (hM : 1 ≤ M) (hNd : 1 ≤ Nd)
    (hg : S13CapGatePerBlock_L_gk K Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 εr)
    (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ)) :
    G2Scaffold.DoorCapErrWS_L_gk K M Nd q Nd P Q (doorCoeffU_L_gk K M) liouvilleC Tann
      (s13E Nd Tann EP2) (s13MtailBand C Nd P Q) := by
  have h8 := hg.logX_eight
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := s13_Nd_pos h8
  have hlogX1 : (1 : ℝ) < Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hP2 : 2 ≤ P := s13_P_two h8 hg.P_low
  -- ⟦the datum's window pin⟧
  have hasupp : ∀ n : ℕ, winCutH Nd (doorCoeffU_L_gk K M) n ≠ 0 → Nd ≤ n ∧ n ≤ 2 * Nd := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    exact ⟨h1, h2⟩
  refine
    { Xd_eq := rfl
      Nd_one := hNd
      H83_two := hg.H83_two
      H83_le := s13_H83_le (by linarith)
      P_one := by omega
      Tann_nonneg := by linarith
      b_one := norm_doorCoeffU_le_one_L_gk K M
      cf_one := liouvilleC_norm_le_one
      coefWS := doorCoeffU_seamCoefWS_band_H_L_gk K M Nd P Q
        (door_band_gate_of_log (one_le_s13GK K hM) hlogX1 hg.Q2_reg hg.P_low)
      tail := ?_
      E_ge := ?_ }
  · -- ⟦the tail, WIRED at the band⟧
    exact hband P Q Nd (2 * Nd) (winCutH Nd (doorCoeffU_L_gk K M)) hP2 hg.P_le_Q hNd
      hg.Q_hundred hg.band_product (fun n => norm_doorRowDatumU_le_one_L_gk K M Nd n) hasupp
  · -- ⟦`E_ge`, row by row⟧
    have hH0 : (0 : ℝ) < H83 ((Nd : ℕ) : ℝ) theta293 := by
      rw [H83]; exact Real.rpow_pos_of_pos (by linarith) _
    have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    -- ⟦`W ≤ 2·μ^{−θ}` and `0 ≤ W`⟧
    have hWnn : (0 : ℝ) ≤ (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293 := by
      have : (0 : ℝ) ≤ Tann / ((Nd : ℕ) : ℝ) := by positivity
      positivity
    have hWle : (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293
        ≤ 2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := by
      have h2 : Tann / ((Nd : ℕ) : ℝ) + 1 ≤ 2 := by
        have : Tann / ((Nd : ℕ) : ℝ) ≤ 1 := (div_le_one hNd0).mpr hTX
        linarith
      have hHinv : (0 : ℝ) ≤ (H83 ((Nd : ℕ) : ℝ) theta293)⁻¹ := (inv_pos.mpr hH0).le
      have h3 : (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293
          ≤ 2 / H83 ((Nd : ℕ) : ℝ) theta293 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h2 hHinv
      have h4 : (2 : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293
          = 2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := by
        rw [H83, Real.rpow_neg (by linarith : (0 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ)),
          div_eq_mul_inv]
      linarith [h3, h4.le, h4.ge]
    -- ⟦row 1 — the `φ(q)` line⟧
    have hrow1 : 4 * ((q.totient : ℝ)
          * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293))
        ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293) + EP2 := by
      have hstep : (q.totient : ℝ)
            * ((Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
          ≤ (q.totient : ℝ) * (2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)) :=
        mul_le_mul_of_nonneg_left hWle hφ0
      have hnn : (0 : ℝ) ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1)
          / H83 ((Nd : ℕ) : ℝ) theta293) := by
        have : (0 : ℝ) ≤ Tann / ((Nd : ℕ) : ℝ) := by positivity
        positivity
      calc 4 * ((q.totient : ℝ)
              * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293))
          = 2080 * ((q.totient : ℝ)
              * ((Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)) := by
            ring
        _ ≤ 2080 * ((q.totient : ℝ)
              * (2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293))) :=
            mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = 4160 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := by ring
        _ ≤ EP2 := hg.phi_row
        _ ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1)
              / H83 ((Nd : ℕ) : ℝ) theta293) + EP2 := by linarith
    -- ⟦rows 2 and 3⟧
    have hrow2 := hg.p2_row
    have hrow3 := hg.tail_row
    rw [s13E]
    linarith [hrow1, hrow2, hrow3]

set_option maxHeartbeats 1000000 in
-- the bundle has fifty-eight fields; one `refine` elaborates the whole list
/-- `S13FramesB.s13_doorCapBase_perBlock_gk (:2211)` at the linear door. -/
theorem s13_doorCapBase_perBlock_L_gk (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {M Nd q P Q Hreg : ℕ}
    {Tann Rrad Rbd CR EP2 εr : ℝ} (hM : 1 ≤ M) (hNd : 1 ≤ Nd)
    (hg : S13CapGatePerBlock_L_gk K Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 εr)
    (hq : 1 ≤ q) (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ))
    (hTll : 5 ≤ Real.log (Real.log Tann))
    (hE : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L_gk K M)))
          (chiBarCoeff q χ (doorCoeffU_L_gk K M))
          (chiBarCoeff q χ liouvilleC) t‖ ^ 2) ≤ s13E Nd Tann EP2) :
    DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M Nd q Nd P Q (s13Mr Nd) s13Jb (doorCoeffU_L_gk K M)
      liouvilleC Tann (s13VJ_L_gk K M) (s13V Nd) (s13Lr Nd) s13Eta (s13EpsD q Nd) εr Rbd CR
      (s13KS Nd Tann) (s13E Nd Tann EP2) EP2 := by
  have h8 := hg.logX_eight
  have hLX4 : (4 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hLX1 : (1 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hLX0 : (0 : ℝ) < Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hNdR : (0 : ℝ) < ((Nd : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hNd
    linarith
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  -- ⟦the razor's level and its exponent⟧
  have halpha : mrAlpha (1 / 12) 2 = 7 / 48 := by rw [mrAlpha]; norm_num
  have hH1 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  have hcalH : calH (H1doorL M) 2 = 4 * H1doorL M := by rw [calH]; norm_num
  have hcalH0 : (0 : ℝ) < calH (H1doorL M) 2 := by rw [hcalH]; linarith
  -- ⟦the height scale⟧
  have hqT1 : (1 : ℝ) < (q : ℝ) * Tann := by nlinarith
  have hlogqT0 : (0 : ℝ) < Real.log ((q : ℝ) * Tann) := Real.log_pos hqT1
  have hloglog5 : (5 : ℝ) ≤ Real.log (Real.log ((q : ℝ) * Tann)) := by
    have hTpos : (0 : ℝ) < Tann := by linarith
    have h1 : Real.log Tann ≤ Real.log ((q : ℝ) * Tann) :=
      Real.log_le_log hTpos (by nlinarith)
    have hlogT0 : (0 : ℝ) < Real.log Tann := Real.log_pos hT1
    exact le_trans hTll (Real.log_le_log hlogT0 h1)
  have hlogqT1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * Tann) := by
    by_cases hc : (1 : ℝ) ≤ Real.log ((q : ℝ) * Tann)
    · exact hc
    · exfalso
      have hlt : Real.log ((q : ℝ) * Tann) < 1 := not_le.mp hc
      have : Real.log (Real.log ((q : ℝ) * Tann)) < 0 := Real.log_neg hlogqT0 hlt
      linarith
  -- ⟦the ladder⟧
  have hA0 : 0 < AdoorL M := one_le_AdoorL hM
  have hE2 : 2 ≤ calE (AdoorL M) (s13GK K M) 2 := by
    have h : calE (AdoorL M) (s13GK K M) 2 = AdoorL M * (s13GK K M) * 4 := by
      rw [calE]; norm_num [Nat.factorial]
    rw [h]
    have h1 : 1 ≤ AdoorL M := hA0
    have h2 : 1 ≤ s13GK K M := one_le_s13GK K hM
    nlinarith
  -- ⟦the pinned `Lr` and `V`⟧
  have hLr : s13Lr Nd = (Real.log ((Nd : ℕ) : ℝ)) ^ ((11 : ℝ) / 10) := rfl
  have hLrge : Real.log ((Nd : ℕ) : ℝ) ≤ s13Lr Nd := by
    rw [hLr]
    have := Real.rpow_le_rpow_of_exponent_le hLX1 (by norm_num : (1 : ℝ) ≤ (11 : ℝ) / 10)
    rwa [Real.rpow_one] at this
  have hLrpos : (0 : ℝ) < s13Lr Nd := by linarith
  have hlogLr : Real.log (s13Lr Nd) = (11 / 10 : ℝ) * Real.log (Real.log ((Nd : ℕ) : ℝ)) := by
    rw [hLr, Real.log_rpow hLX0]
  have hlogLXnn : (0 : ℝ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ)) := Real.log_nonneg hLX1
  refine
    { Jb_lo := by rw [s13Jb]; norm_num
      Jb_hi := by rw [s13Jb]
      Hseq_two := ?_
      alpha_nonneg := by rw [s13Jb, halpha]; norm_num
      Tann_one := by linarith
      qTann_one := hqT1
      P_three := ?_
      PQ := ?_
      QTann := hg.QTann
      kappa30Q := hg.kappa30Q
      loglog5 := hloglog5
      VJ_bound := ?_
      alpha_eta := by rw [s13Jb, halpha, s13Eta]; norm_num
      eta_half := by rw [s13Eta]; norm_num
      Tann_X := hTX
      X_pos := hNdR
      debit := ?_
      logX_pos := hLX0
      q_logX := hg.q_logX
      V_one := ?_
      V_inv := ?_
      T0_Tann := hg.T0_Tann
      floor1 := hg.floor1
      floor2 := hg.floor2
      floor3 := hg.floor3
      floor4 := hg.floor4
      logqT_one := hlogqT1
      logqT_L := hg.logqT_L
      L_exp := ?_
      logV_L := ?_
      H83_two := hg.H83_two
      logX_exp := ?_
      logX_four := hLX4
      cf_one := liouvilleC_norm_le_one
      P_low := hg.P_low
      Q_pos := hg.Q_pos
      Q_high := hg.Q_high
      range := s13_range_perBlock Nd P Q
      budget := hg.budget
      Hj := hg.Hj
      B3 := hg.B3
      BT := hg.BT
      kappa30 := hg.kappa30
      BT10 := hg.BT10
      WL := hg.WL
      gate := hg.gate
      Rbd_nonneg := hg.Rbd_nonneg
      Rbd_grade := hg.Rbd_grade
      Cq_gate := hg.Cq_gate
      Rbd_binder := m4_capRbd_at_door_L_gk K hg.Rbd_socket
      KS_nonneg := ?_
      KS_binder := ?_
      KS_gate := s13_KS_gate h8 hT1 hTX
      epsr_nonneg := hg.epsr_nonneg
      abs8640 := hg.abs8640
      EP2_gate := hg.EP2_gate
      E_row := le_rfl
      E_binder := hE }
  · -- ⟦`Hseq_two`⟧
    rw [s13Jb, hcalH]; linarith
  · -- ⟦`P_three`⟧
    rw [s13Jb, calP]
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ calE (AdoorL M) (s13GK K M) 2 := Nat.pow_le_pow_right (by norm_num) hE2
  · -- ⟦`PQ`⟧
    rw [s13Jb, calP, calQK]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 1 * calE (AdoorL M) (s13GK K M) 2 ≤ (2 ^ 2 * M) * calE (AdoorL M) (s13GK K M) 2 :=
      Nat.mul_le_mul_right _ (by omega)
    simpa using this
  · -- ⟦`VJ_bound`⟧
    intro v hv
    rw [s13VJ_L_gk, s13Jb]
    refine Real.exp_le_exp.mpr ?_
    rw [halpha]
    have hvle : (v : ℝ) ≤ calH (H1doorL M) 2
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) := by
      rw [ramI, Finset.mem_Icc] at hv
      have h1 : (v : ℝ) ≤ (⌊calH (H1doorL M) 2
          * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast hv.2
      have hQ1 : (1 : ℝ) ≤ ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) := by
        exact_mod_cast one_le_calQK (AdoorL M) (s13GK K M) M 2
      have h2 : (0 : ℝ) ≤ calH (H1doorL M) 2
          * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) := by
        have := Real.log_nonneg hQ1
        positivity
      exact le_trans h1 (Nat.floor_le h2)
    rw [div_le_iff₀ hcalH0]
    nlinarith [hvle, hcalH0]
  · -- ⟦`debit`⟧ an EQUALITY at the pinned `εd`
    rw [s13Jb, s13EpsD, halpha]
    have h1 : ((Nd : ℕ) : ℝ) ^ (2 * (7 / 48 : ℝ) * Real.log ((q : ℕ) : ℝ)
        / Real.log ((Nd : ℕ) : ℝ))
        = Real.exp (2 * (7 / 48 : ℝ) * Real.log ((q : ℕ) : ℝ)) := by
      rw [Real.rpow_def_of_pos hNdR]
      congr 1
      field_simp
    have h2 : (q : ℝ) ^ (2 * (7 / 48 : ℝ))
        = Real.exp (Real.log ((q : ℕ) : ℝ) * (2 * (7 / 48 : ℝ))) :=
      Real.rpow_def_of_pos hqR0 _
    rw [h1, h2]
    exact Real.exp_le_exp.mpr (le_of_eq (by ring))
  · -- ⟦`V_one`⟧
    rw [s13V]
    have := Real.rpow_le_rpow_of_exponent_le hLX1 (by norm_num : (0 : ℝ) ≤ (106 : ℝ))
    rwa [Real.rpow_zero] at this
  · -- ⟦`V_inv`⟧
    rw [s13V, ← Real.rpow_neg hLX0.le]
  · -- ⟦`L_exp`⟧
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  · -- ⟦`logV_L`⟧
    rw [s13V, Real.log_rpow hLX0, hlogLr]
    linarith
  · -- ⟦`logX_exp`⟧
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  · -- ⟦`KS_nonneg`⟧
    rw [s13KS]
    have h1 : (0 : ℝ) < (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) := Real.rpow_pos_of_pos hLX0 _
    have h2 : (0 : ℝ) ≤ Real.log (2 * Tann) := Real.log_nonneg (by linarith)
    positivity
  · -- ⟦`KS_binder`⟧ through `M4CapWire` §6b, at the per-block cap
    rw [s13KS]
    exact m4_capKS_at_door_perBlock_L_gk K (s13m0 Nd) hLX0.le (by linarith)
      (s13_m0_two h8 hg.Q_pos hg.Q_high) (s13_m0_bot Nd P Q) (s13_range_perBlock Nd P Q)
      (s13_Mr_sharp h8 hg.Q_pos hg.Q_high)

/-! ## §4 — ⟦THE COMPOSITE⟧ at the linear door -/


/-- `S13FramesB.doorCapBundle_at_workingPoint_perBlock_gk (:2406)` at the linear door. -/
theorem doorCapBundle_at_workingPoint_perBlock_L_gk (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ}
    {M Nd q P Q Hreg : ℕ} {Tann Rrad Rbd CR EP2 εr : ℝ}
    (hband : ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 100 * Real.log Q ≤ Real.log Xd →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
    (hM : 1 ≤ M) (hNd : 1 ≤ Nd) (hq : 1 ≤ q)
    (hg : S13CapGatePerBlock_L_gk K Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 εr)
    (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ))
    (hTll : 5 ≤ Real.log (Real.log Tann)) :
    ∃ (Xd P' Q' : ℕ) (Mr' : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
      (VJ V Lr η εd Rbd' CR' KS E EP2' Mtail : ℝ),
      G2Scaffold.DoorCapErrWS_L_gk K M Nd q Xd P' Q' b cf Tann E Mtail
        ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
              ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P' Q'
                (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L_gk K M)))
                (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
            → DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M Nd q Xd P' Q' Mr' Jb b cf Tann
                VJ V Lr η εd εr Rbd' CR' KS E EP2') := by
  refine ⟨Nd, P, Q, s13Mr Nd, s13Jb, doorCoeffU_L_gk K M, liouvilleC, s13VJ_L_gk K M,
    s13V Nd, s13Lr Nd,
    s13Eta, s13EpsD q Nd, Rbd, CR, s13KS Nd Tann, s13E Nd Tann EP2, EP2,
    s13MtailBand C Nd P Q,
    s13_doorCapErrWS_perBlock_L_gk K hband hM hNd hg hT1 hTX, ?_⟩
  intro hE
  exact s13_doorCapBase_perBlock_L_gk K hM hNd hg hq hT1 hTX hTll hE

/-! ## §5 — ⟦THE GRID SUPPLY AT THE LINEAR DOOR⟧

`S13CapGrid.s13CapGrid_all_gk`'s eighteen conjuncts.  SEVENTEEN of them never touch the
anchor — they read the socket base `A + s` and the pinned band `(s13BandP, s13BandQ)` only.
The ONE that does is `Q2_reg`, and `S13FramesLinear.s13_doorRowZeroBase_five_L_gk` already
supplies it at the linear block floor.  ⟦THE NEAR-KILL LESSON⟧ the wave is fired off `hTlo`
(the annulus LOWER edge), never off `TannGate`. -/

/-- `S13CapGrid.s13CapGrid_Q2_reg_gk (:1035)` at the linear door. -/
theorem s13CapGrid_Q2_reg_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (hb : SocketBaseL R M H L q j A s) (hblock : s13BlockFloor_L_gk K M ≤ A + s) :
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) :=
  (s13_doorRowZeroBase_five_L_gk K hM hblock hb.2.2.2.2.2.2.1).2.1

/-- **⟦THE GRID WAVE AT THE LINEAR DOOR⟧** (`s13CapGrid_all_L_gk`) — EIGHTEEN of
`S13CapGatePerBlock_L_gk`'s fields at one binder. -/
theorem s13CapGrid_all_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {cs T : ℝ}
    (hM : 1 ≤ M) (hcs : 1 ≤ cs) (hfl : loglogFloor50 ≤ R.Hlo)
    (hb : SocketBaseL R M H L q j A s) (hblock : s13BlockFloor_L_gk K M ≤ A + s)
    (hTlo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T)
    (hThi : 2 * T ≤ (((A + s : ℕ)) : ℝ)) :
    8 ≤ Real.log (((A + s : ℕ)) : ℝ)
    ∧ 2 ≤ H83 (((A + s : ℕ)) : ℝ) theta293
    ∧ (q : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ 12
    ∧ Real.log ((q : ℝ) * (2 * T)) ≤ s13Lr (A + s)
    ∧ P83 (((A + s : ℕ)) : ℝ) theta293 ≤ ((s13BandP (A + s) : ℕ) : ℝ)
    ∧ Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
        ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ))
    ∧ 0 < s13BandQ (A + s)
    ∧ ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Q83 (((A + s : ℕ)) : ℝ)
    ∧ s13BandP (A + s) ≤ s13BandQ (A + s)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        H83 (((A + s : ℕ)) : ℝ) theta293 ≤ (i : ℝ))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        3 ≤ ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (q : ℝ) * (2 * T))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        30 ≤ Real.log ((q : ℝ) * (2 * T))
          / Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i : ℕ) : ℝ)
          ≤ (2 * T) ^ 10)
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) i)
          ≤ s13Lr (A + s))
    ∧ (∀ i ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (s13BandQ (A + s)),
        420 * s13Lr (A + s) * (s13Lr (A + s)) ^ ((3 : ℝ) / 4)
            * (Real.log (s13Lr (A + s))) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293)
              (s13BandP (A + s)) i)) ^ 2)
    ∧ 100 * Real.log ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ)
    ∧ ((Nat.sqrt (A + s) : ℝ) + 1)
          * ∏ p ∈ primeBand (s13BandP (A + s)) (s13BandQ (A + s)), (1 + 3 / (p : ℝ))
        ≤ (((A + s : ℕ)) : ℝ)
          * (Real.log ((s13BandP (A + s) : ℕ) : ℝ)
              / Real.log ((s13BandQ (A + s) : ℕ) : ℝ)) := by
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  have hμ : (2000 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := s13CapGrid_mu_2000 hfl hbb
  have hΛ : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    s13CapGrid_Lambda_lo hfl hbb
  exact ⟨s13CapGrid_logX_eight hfl hbb, s13CapGrid_H83_two hμ hΛ, s13CapGrid_q_logX hfl hbb,
    s13CapGrid_logqT_L hfl hbb hTlo hThi, s13CapGrid_P_low (A + s),
    s13CapGrid_Q2_reg_L_gk K hM hb hblock, s13CapGrid_Q_pos hμ, s13CapGrid_Q_high (A + s),
    s13CapGrid_P_le_Q hμ hΛ, s13CapGrid_Hj hμ hΛ, s13CapGrid_B3 hμ hΛ,
    s13CapGrid_BT hfl hbb hTlo, s13CapGrid_kappa30 hfl hbb hTlo, s13CapGrid_BT10 hfl hbb hTlo,
    s13CapGrid_WL hμ hΛ, s13CapGrid_gate hcs hμ hΛ, s13CapGrid_Q_hundred hμ hΛ,
    s13CapGrid_band_product hμ hΛ⟩

/-! ## §6 — ⟦THE BUDGET FIELD AT THE LINEAR DOOR⟧

`S16Budget`'s ITEM-3 budget field (`s16_budget_field_gk_96`, :2029) at `AdoorL`.  The re-cut
RAISES `Lp = log 𝒫₂` by the factor `M/(⌊log₂M⌋+1)` and the whole numeric core
(`s16_budget_num_96`) is stated in the abstract symbols `μ, Λ, Lp, Lq, lS, llS, lq` — so the
product route is LADDER-BLIND and the only moving parts are the two door reads that feed it:
`Lq = 4M·Lp` (`s16_logQK2`, `(A,G)`-generic) and the width cap
`log 𝓗₂ ≤ 2 + Lp/73728` (re-cut below). -/

/-- `s16_logP1_le_logP2 (S16Budget:139)` at the linear door. -/
theorem s16_logP1_le_logP2_L (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 12288 := by
  rw [s16_logP1, s16_logP2]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hG : 3072 ≤ s13GK K M := by
    rw [s13GK]
    have h2 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    calc 3072 = 3072 * 1 * 1 := by ring
      _ ≤ 3072 * 2 ^ K * M := by exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) hM
  have hA : (1 : ℝ) ≤ (AdoorL M : ℝ) := by
    have h : (1 : ℕ) ≤ AdoorL M := one_le_AdoorL hM
    exact_mod_cast h
  have hGr : (3072 : ℝ) ≤ ((s13GK K M : ℕ) : ℝ) := by exact_mod_cast hG
  rw [le_div_iff₀ (by norm_num)]
  push_cast
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * ((s13GK K M : ℕ) : ℝ) - 12288)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ ((AdoorL M : ℕ) : ℝ)) hlog2.le)]

/-- `s16_logH2_le (S16Budget:156)` at the linear door. -/
theorem s16_logH2_le_L (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Real.log (calH (H1doorL M) 2)
      ≤ 2 + Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 73728 := by
  have h2 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  have hpin := H1door_pin_L hM
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    have := calP_door_one_ge_L hM; linarith
  have hcube : (0 : ℝ) < (H1doorL M) ^ 3 := by positivity
  have hmono := Real.log_le_log hcube hpin
  rw [Real.log_pow, Real.log_rpow hP0] at hmono
  have hlog1 : Real.log (H1doorL M)
      ≤ Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) / 6 := by linarith
  have hle := s16_logP1_le_logP2_L K hM
  rw [s16_calH_two, Real.log_mul (by norm_num) (by linarith)]
  have hlog4 : Real.log 4 ≤ 2 := by
    have : (4 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hsq : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [hsq]; nlinarith [Real.exp_pos 1]
    calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) this
      _ = 2 := Real.log_exp 2
  linarith

set_option maxHeartbeats 1600000 in
-- same cause as the landed `s16_budget_field_gk_96`: the numeric core's seven-symbol
-- instantiation re-elaborates against the linear anchor's casts
/-- `s16_budget_field_gk_96 (S16Budget:2029)` at the linear door. -/
theorem s16_budget_field_L_gk_96 (K : ℕ) {M Nd q P Q i : ℕ} {Tann : ℝ}
    (hM : 1 ≤ M) (hq : 1 ≤ q) (hQpos : 0 < Q)
    (hmu8 : 8 ≤ Real.log (Nd : ℝ))
    (hLam : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (Real.log (Nd : ℝ)))
    (hqlog : (q : ℝ) ≤ (Real.log (Nd : ℝ)) ^ 12)
    (hTann1 : 1 < Tann) (hTannhi : Tann ≤ (Nd : ℝ))
    (hQhigh : (Q : ℝ) ≤ Q83 (Nd : ℝ))
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (Nd : ℝ)))
    (hcap : Real.log (Real.log (Nd : ℝ))
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096)
    (hi : i ∈ ramI (H83 (Nd : ℝ) theta293) P Q) :
    thinBundleGChi ((q : ℝ) * Tann) (s13VJ_L_gk K M) (calH (H1doorL M) 2)
        (calP (AdoorL M) (s13GK K M) 2) (calQK (AdoorL M) (s13GK K M) M 2)
      * (Nd : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ ((s13Mr Nd i : ℕ) : ℝ) := by
  set X : ℝ := (Nd : ℝ) with hXdef
  set μ : ℝ := Real.log X with hmudef
  set Λ : ℝ := Real.log μ with hLamdef
  set Lp : ℝ := Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) with hLpdef
  set Lq : ℝ := Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) with hLqdef
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hX0 : (0 : ℝ) < X := by
    rcases Nat.eq_zero_or_pos Nd with h0 | hpos
    · exfalso
      rw [hmudef, hXdef, h0] at hμ0
      simp only [Nat.cast_zero, Real.log_zero] at hμ0
      exact lt_irrefl 0 hμ0
    · rw [hXdef]; exact_mod_cast hpos
  have hXexp : Real.exp μ = X := Real.exp_log hX0
  -- the base logs
  have hLp0 : (0 : ℝ) < Lp := by
    rw [hLpdef, s16_logP2]
    have hA : (1 : ℕ) ≤ AdoorL M := one_le_AdoorL hM
    have hG : (1 : ℕ) ≤ s13GK K M := one_le_s13GK K hM
    have h4 : (1 : ℝ) ≤ ((4 * (AdoorL M * s13GK K M) : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 4 * (AdoorL M * s13GK K M) := by
        have := Nat.mul_le_mul hA hG; omega
      exact_mod_cast this
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hLqval : Lq = ((4 * M : ℕ) : ℝ) * Lp := by rw [hLqdef, hLpdef, s16_logQK2]
  have hLpq : 4 * Lp ≤ Lq := by
    rw [hLqval]
    have : (4 : ℝ) ≤ ((4 * M : ℕ) : ℝ) := by
      have : (4 : ℕ) ≤ 4 * M := by omega
      exact_mod_cast this
    nlinarith [hLp0]
  have hΛ0 : (0 : ℝ) < Λ := by linarith [hLam]
  -- `12Λ ≤ μ`
  have h12 : 12 * Λ ≤ μ := by
    have hh : Real.exp Λ = μ := by rw [hLamdef]; exact Real.exp_log hμ0
    have h1 : Λ / 2 + 1 ≤ Real.exp (Λ / 2) := Real.add_one_le_exp _
    have h2 : Real.exp (Λ / 2) * Real.exp (Λ / 2) = μ := by
      rw [← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hh]
    nlinarith [hLam, h1, h2, Real.exp_pos (Λ / 2)]
  -- `S = q·Tann`
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hS0 : (0 : ℝ) < (q : ℝ) * Tann := by nlinarith
  have hlogTann0 : (0 : ℝ) < Real.log Tann := Real.log_pos hTann1
  have hlogq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hlogq12 : Real.log (q : ℝ) ≤ 12 * Λ := by
    have hpow : Real.log ((Real.log X) ^ 12) = 12 * Λ := by
      rw [Real.log_pow]; push_cast; rw [← hmudef, ← hLamdef]
    calc Real.log (q : ℝ) ≤ Real.log ((Real.log X) ^ 12) :=
          Real.log_le_log (by linarith) hqlog
      _ = 12 * Λ := hpow
  have hlogTann : Real.log Tann ≤ μ := by
    rw [hmudef]; exact Real.log_le_log (by linarith) hTannhi
  have hlS : Real.log ((q : ℝ) * Tann) ≤ μ + 12 * Λ := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have hlS0 : (0 : ℝ) < Real.log ((q : ℝ) * Tann) := by
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith
  have hllS : Real.log (Real.log ((q : ℝ) * Tann)) ≤ Λ + 1 := by
    have h2μ : Real.log ((q : ℝ) * Tann) ≤ Real.exp 1 * μ := by
      nlinarith [Real.add_one_le_exp (1 : ℝ), h12, hlS, hμ0]
    have hstep : Real.log (Real.log ((q : ℝ) * Tann)) ≤ Real.log (Real.exp 1 * μ) :=
      Real.log_le_log hlS0 h2μ
    have heq : Real.log (Real.exp 1 * μ) = 1 + Λ := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hμ0.ne', Real.log_exp]
    linarith
  -- the numeric core
  have hnum := s16_budget_num_96 (μ := μ) (Λ := Λ) (Lp := Lp) (Lq := Lq)
    (lS := Real.log ((q : ℝ) * Tann)) (llS := Real.log (Real.log ((q : ℝ) * Tann)))
    (lq := Real.log (q : ℝ)) hLam rfl hμ0 hLp0 hLpq (by rw [hLqdef]; exact hQ2reg)
    (by rw [hLpdef] at hcap ⊢; exact hcap) hlogq12 hlS0 hlS hllS
  -- ⟦THE CARD FACTOR⟧
  have hmr : mrAlpha (1 / 12) 2 = 7 / 48 := by rw [mrAlpha]; norm_num
  have hH2pos : (0 : ℝ) < calH (H1doorL M) 2 := by
    rw [s16_calH_two]; linarith [H1door_two_L hM]
  have hLq0 : (0 : ℝ) ≤ Lq := by rw [hLqval]; positivity
  have hcard := ramI_card_le (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
    (calQK (AdoorL M) (s13GK K M) M 2) (mul_nonneg hH2pos.le hLq0)
  have hH2le : calH (H1doorL M) 2 ≤ Real.exp (2 + Lp / 73728) := by
    have hlog := s16_logH2_le_L K hM
    rw [← hLpdef] at hlog
    calc calH (H1doorL M) 2 = Real.exp (Real.log (calH (H1doorL M) 2)) :=
          (Real.exp_log hH2pos).symm
      _ ≤ Real.exp (2 + Lp / 73728) := Real.exp_le_exp.mpr hlog
  have hexphalf : Real.exp (Λ / 2) * Real.exp (Λ / 2) = μ := by
    rw [← Real.exp_add, show Λ / 2 + Λ / 2 = Λ by ring, hLamdef]
    exact Real.exp_log hμ0
  have hLqexp : Lq ≤ Real.exp (Λ / 2) := by
    have hsqe : Real.sqrt μ = Real.exp (Λ / 2) := by
      rw [show μ = Real.exp (Λ / 2) ^ 2 by rw [sq]; exact hexphalf.symm]
      exact Real.sqrt_sq (Real.exp_pos _).le
    rw [← hsqe]; exact hQ2reg
  have hcardexp :
      ((ramI (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
        (calQK (AdoorL M) (s13GK K M) M 2)).card : ℝ)
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2) := by
    have hstep : calH (H1doorL M) 2 * Lq + 1
        ≤ Real.exp (2 + Lp / 73728) * Real.exp (Λ / 2) + 1 := by
      have := mul_le_mul hH2le hLqexp hLq0 (Real.exp_pos _).le
      linarith
    have hcomb : Real.exp (2 + Lp / 73728) * Real.exp (Λ / 2)
        = Real.exp (2 + Lp / 73728 + Λ / 2) := by rw [← Real.exp_add]
    have hone : (1 : ℝ) ≤ Real.exp (2 + Lp / 73728 + Λ / 2) := by
      rw [Real.one_le_exp_iff]; positivity
    have hplus : Real.exp (2 + Lp / 73728 + Λ / 2) + 1
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2) := by
      have : Real.exp (3 + Lp / 73728 + Λ / 2)
          = Real.exp 1 * Real.exp (2 + Lp / 73728 + Λ / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      nlinarith [Real.exp_one_gt_d9, hone]
    linarith [hcard, hstep, hcomb ▸ hstep]
  -- ⟦THE `VJ` FACTOR⟧
  have hVJ : (s13VJ_L_gk K M) ^ 2 = Real.exp ((7 / 24) * Lq) := by
    rw [s13VJ_L_gk, hmr, ← hLqdef, sq, ← Real.exp_add]
    congr 1; ring
  -- ⟦THE `X`-POWER⟧
  have hXr : X ^ (1 - 2 * s13Eta + s13EpsD q Nd)
      = Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by
    rw [Real.rpow_def_of_pos hX0, s13Eta, s13EpsD, hmr]
    congr 1
    rw [← hXdef, ← hmudef]
    field_simp
    ring
  -- ⟦THE ASSEMBLY⟧
  have h1680 : (1680 : ℝ) ≤ Real.exp 8 := by
    have h2 : Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7182818283 : ℝ) ^ (8 : ℕ) ≤ (Real.exp 1) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
    have h5 : (1680 : ℝ) ≤ (2.7182818283 : ℝ) ^ (8 : ℕ) := by norm_num
    linarith
  rw [thinBundleGChi, hVJ, hXr]
  set E : ℝ := 2 * (Real.log ((q : ℝ) * Tann) / Lp)
    * Real.log (Real.log ((q : ℝ) * Tann)) with hEdef
  have hprod :
      ((ramI (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
        (calQK (AdoorL M) (s13GK K M) M 2)).card : ℝ)
          * (1680 * Real.exp ((7 / 24) * Lq) * Real.exp E)
          * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ))
        ≤ Real.exp (3 + Lp / 73728 + Λ / 2)
          * (Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E)
          * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by
    have hA : (0 : ℝ) ≤ Real.exp ((7 / 24) * Lq) * Real.exp E := by positivity
    have hB : (0 : ℝ) ≤ Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ)) := by positivity
    have hC : (1680 : ℝ) * Real.exp ((7 / 24) * Lq) * Real.exp E
        ≤ Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E := by
      have := mul_le_mul_of_nonneg_right h1680 hA
      calc (1680 : ℝ) * Real.exp ((7 / 24) * Lq) * Real.exp E
          = 1680 * (Real.exp ((7 / 24) * Lq) * Real.exp E) := by ring
        _ ≤ Real.exp 8 * (Real.exp ((7 / 24) * Lq) * Real.exp E) := this
        _ = Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E := by ring
    have hcard0 : (0 : ℝ) ≤ ((ramI (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
        (calQK (AdoorL M) (s13GK K M) M 2)).card : ℝ) := Nat.cast_nonneg _
    have hmid := mul_le_mul hcardexp hC (by positivity) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hmid hB
  have hsum : Real.exp (3 + Lp / 73728 + Λ / 2)
      * (Real.exp 8 * Real.exp ((7 / 24) * Lq) * Real.exp E)
      * Real.exp ((19 / 24) * μ + (7 / 24) * Real.log (q : ℝ))
      = Real.exp (11 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + E
          + (7 / 24) * Real.log (q : ℝ) + (19 / 24) * μ) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  -- ⟦THE RIGHT-HAND SIDE⟧
  have hH830 : (0 : ℝ) < H83 X theta293 := by
    rw [H83, ← hmudef]; exact Real.rpow_pos_of_pos hμ0 _
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg hQR
  have hiQ : (i : ℝ) / H83 X theta293 ≤ μ / Λ := by
    rw [ramI, Finset.mem_Icc] at hi
    have h1 : (i : ℝ) ≤ H83 X theta293 * Real.log (Q : ℝ) := by
      have h2 : ((⌊H83 X theta293 * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ H83 X theta293 * Real.log (Q : ℝ) :=
        Nat.floor_le (mul_nonneg hH830.le hlogQ0)
      have h3 : (i : ℝ) ≤ ((⌊H83 X theta293 * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hi.2
      linarith
    have h4 : Real.log (Q : ℝ) ≤ μ / Λ := by
      have h5 : Real.log (Q83 X) = μ / Λ := by
        rw [Q83, Real.log_exp, ← hmudef, ← hLamdef]
      calc Real.log (Q : ℝ) ≤ Real.log (Q83 X) := Real.log_le_log (by linarith) hQhigh
        _ = μ / Λ := h5
    rw [div_le_iff₀ hH830]
    nlinarith [hH830, h1, h4]
  have hMr : 2 * X * Real.exp (-(i : ℝ) / H83 X theta293) ≤ ((s13Mr Nd i : ℕ) : ℝ) := by
    rw [hXdef, s13Mr]
    exact Nat.le_ceil _
  have hexpstep : Real.exp (μ - μ / Λ) ≤ 2 * X * Real.exp (-(i : ℝ) / H83 X theta293) := by
    have h1 : Real.exp (μ - μ / Λ) = X * Real.exp (-(μ / Λ)) := by
      rw [← hXexp, ← Real.exp_add]; congr 1
    have h2 : Real.exp (-(μ / Λ)) ≤ Real.exp (-(i : ℝ) / H83 X theta293) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith [hiQ]
    have h3 : X * Real.exp (-(μ / Λ)) ≤ X * Real.exp (-(i : ℝ) / H83 X theta293) :=
      mul_le_mul_of_nonneg_left h2 hX0.le
    nlinarith [Real.exp_pos (-(i : ℝ) / H83 X theta293), hX0, h1, h3]
  have hfin : Real.exp (11 + Lp / 73728 + Λ / 2 + (7 / 24) * Lq + E
      + (7 / 24) * Real.log (q : ℝ) + (19 / 24) * μ) ≤ Real.exp (μ - μ / Λ) := by
    apply Real.exp_le_exp.mpr
    rw [hEdef] at *
    linarith [hnum]
  linarith [hprod, hsum ▸ hprod, hfin, hexpstep, hMr]

/-! ## §7 — ⟦THE CAP-GATE SUPPLY AT THE LINEAR DOOR⟧

`S16Budget.s16_capGate_supply_wide_gk (:2370)` re-cut.  The two carried riders
(⟦RULING 9⟧'s co-factor debt and ITEM 3's base-scale cap) are re-stated at the LINEAR socket
and the LINEAR door: both get WEAKER, since `SocketBaseL → SocketBase` strengthens the
antecedent and `Adoor M ≤ AdoorL M` raises the cap's right side. -/

/-- ⟦ITEM 3⟧'s base-scale cap at the linear door and the linear socket. -/
def S16BaseScaleCap96_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
    Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) / 9.60000096

/-- ⟦RULING 9⟧'s co-factor block at the linear door and the linear socket. -/
def S16CofactorSupply_L_gk (K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
    ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
      ∃ Rrad Rbd CR : ℝ,
        0 ≤ Rbd
        ∧ Rbd ≤ CR * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-rho293)
        ∧ 1728 * Cq * CR ^ 2 ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (2 * theta293)
        ∧ (∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
            CofactorSocket (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) (A + s)
              (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T) Rrad t₁ Rbd
              (doorCofactor0 χ (calP (AdoorL M) (s13GK K M))
                (calQK (AdoorL M) (s13GK K M) M) 2 1))

/-- **⟦THE RE-CUT IS NOT A NEW ASK⟧** — the LANDED base-scale cap supplies the linear one.
Two independent slacknesses compose: `SocketBaseL → SocketBase` (the linear row floor is the
higher one) and `Adoor M ≤ AdoorL M` (the linear anchor is the larger one, by the factor
`M/(⌊log₂M⌋+1)`).  So whatever discharges ⟦ITEM 3⟧ at the landed door discharges it here. -/
theorem s16_baseScaleCap96_L_of_baseScaleCap96 (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (hcap : S16BaseScaleCap96_gk K R M) : S16BaseScaleCap96_L_gk K R M := by
  intro H L q j A s hb
  have hstep := hcap H L q j A s (socketBase_of_socketBaseL hM hb)
  have hmono : Real.log ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ)
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) := by
    rw [s16_logP2, s16_logP2]
    have hA : Adoor M ≤ AdoorL M := Adoor_le_AdoorL hM
    have hnat : 4 * (Adoor M * s13GK K M) ≤ 4 * (AdoorL M * s13GK K M) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA)
    have hR : ((4 * (Adoor M * s13GK K M) : ℕ) : ℝ)
        ≤ ((4 * (AdoorL M * s13GK K M) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    exact mul_le_mul_of_nonneg_right hR hlog2
  refine le_trans hstep ?_
  gcongr

set_option maxHeartbeats 1000000 in
-- 37 structure fields are checked against the levered per-block gate in one `exact`
/-- **⟦THE CAP GATE AT THE LINEAR DOOR⟧** (`s16_capGate_supply_L_gk`) —
`S16Budget.s16_capGate_supply_wide_gk (:2370)` at `AdoorL`.  The grid wave is the linear one
(§5), the floor wave is `S13BandCapLinear.s13CapFloor_all_L_gk`, the `eps` wave is the LANDED
`s13CapEps_all` (ladder-blind: it reads the socket base and the pinned band only, never the
anchor) composed through `ArithPageLinear.socketBase_of_socketBaseL`, and the `budget` field
is §6's. -/
theorem s16_capGate_supply_L_gk (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {R : ChowlaRegime} {M : ℕ}
    {epsf : ℕ → ℝ}
    (hM : 1 ≤ M) (hfl : loglogFloor50 ≤ R.Hlo) (hcs : Real.exp (-100) ≤ cs)
    (hblk : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s)
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hεr : ∀ A : ℕ, theta293 - 1 / 500 ≤ epsf A)
    (hcap : S16BaseScaleCap96_L_gk K R M) (hcof : S16CofactorSupply_L_gk K Cq R M) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGatePerBlock_L_gk K Cq cs T₀ Kq Ks C M (A + s) q P Q H (2 * T)
            Rrad Rbd CR EP2 (epsf (A + s)) := by
  intro H L q j A s hb T hTlo hThi hTgate hTll
  have hbb : SocketBase R M H L q j A s := socketBase_of_socketBaseL hM hb
  obtain ⟨Rrad, Rbd, CR, hRbd0, hRbdg, hCqg, hRsock⟩ := hcof H L q j A s hb T hTlo hThi
  -- the grid wave, at the linear door
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, -, g17, g18⟩ :=
    s13CapGrid_all_L_gk K hM (le_refl (1 : ℝ)) hfl hb (hblk H L q j A s hb) hTlo hThi
  -- `1 < 2T` off the annulus gate
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hT1 : (1 : ℝ) < 2 * T := by
    have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
    linarith
  have hT0le : (0 : ℝ) ≤ 2 * T := by linarith
  have hAN : A ≤ A + s := Nat.le_add_right _ _
  have hTflo : (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 2 * T := by linarith
  -- the floor wave, at the linear door
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ :=
    s13CapFloor_all_L_gk K hfl hbb hM hAN hTflo g6 hT₀ hKq hKs
  -- the eps wave, LADDER-BLIND
  obtain ⟨hP83pin, hgradepin⟩ := s13CapEps_pins_supply hfl hbb
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ :=
    s13CapEps_all hfl hbb (hεr (A + s)) hC0 hC hT0le hThi hP83pin hgradepin
  refine ⟨s13BandP (A + s), s13BandQ (A + s), Rrad, Rbd, CR,
    s13CapEP2 C q (A + s) (s13BandP (A + s)) (s13BandQ (A + s)) (2 * T), ?_⟩
  exact
    { logX_eight := g1
      H83_two := g2
      QTann := f1
      kappa30Q := f2
      q_logX := g3
      T0_Tann := f3
      floor1 := f4
      floor2 := f5
      floor3 := f6
      floor4 := f7
      logqT_L := g4
      P_low := g5
      Q2_reg := g6
      Q_pos := g7
      Q_high := g8
      P_le_Q := g9
      budget := fun i hi =>
        s16_budget_field_L_gk_96 K hM hb.2.2.2.1 g7 g1
          (s13CapGrid_Lambda_lo hfl hbb) g3 hT1 hThi g8 g6 (hcap H L q j A s hb) hi
      Hj := g10
      B3 := g11
      BT := g12
      kappa30 := g13
      BT10 := g14
      WL := g15
      gate := s16_capGrid_gate_cs hcs (s13CapGrid_mu_2000 hfl hbb)
        (s13CapGrid_Lambda_lo hfl hbb)
      Rbd_nonneg := hRbd0
      Rbd_grade := hRbdg
      Cq_gate := hCqg
      Rbd_socket := hRsock
      epsr_nonneg := e1
      abs8640 := e2
      EP2_gate := e3
      q_arcDen := e4
      phi_row := e5
      p2_row := e6
      tail_row := e7
      Q_hundred := g17
      band_product := g18 }

end Salt.MR

end
