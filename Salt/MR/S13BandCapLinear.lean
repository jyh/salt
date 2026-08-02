/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13FramesLinear
import Salt.MR.S14Compose

/-!
# `S13BandCapLinear` — THE BAND / CAP-FLOOR LAYER AT THE LINEAR DOOR

⟦LADDER-L G4⟧  `S13BandBase`'s four `𝒫₁`/`𝒬₂` reads and `S13CapFloor`'s `S13CapGatePerBlock`
supplier, re-cut at `AdoorL M = 2^36·M`.  The `G`-slot is untouched (`3072·M`, resp.
`s13GK K M`).

⟦WHY THESE ARE CHEAP AND WHY THEY ARE STILL OBLIGATIONS⟧ every statement here reads the door
only through `log 𝒫₁ = A·log 2`, `log 𝒬₂ = 16·A·G·M·log 2` and the floors `1 ≤ A`,
`2^36 ≤ A`.  The landed proofs discharge those floors by UNFOLDING `Adoor`
(`rw [Adoor]; positivity`), which is exactly what does not survive the re-cut — `AdoorL 0 = 0`
— so each one is re-stated with `1 ≤ M` and routed through `DoorLinear.AdoorL_ge` /
`one_le_AdoorL`.  As on the `S13Frames` page, the reads that are `(A,G)`-parametric are stated
ONCE at a symbolic anchor and both cuts are instances.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — `S13BandBase`'s level reads at the linear door -/

/-- `log 𝒫₁ = A_L(M)·log 2` at the linear door (`s13_band_log_calP_one` twin). -/
theorem s13_band_log_calP_one_L (M : ℕ) :
    Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) = ((AdoorL M : ℕ) : ℝ) * Real.log 2 :=
  log_calP_one_gen _ _

/-- `s13_band_log_calP_one_L` at the lever — level 1 is `K`-invariant. -/
theorem s13_band_log_calP_one_L_gk (K M : ℕ) :
    Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) = ((AdoorL M : ℕ) : ℝ) * Real.log 2 :=
  log_calP_one_gen _ _

/-- `log 𝒬₂ = 16·A_L·G·M·log 2` at the linear door (`s13_band_log_calQK_two` twin). -/
theorem s13_band_log_calQK_two_L (M : ℕ) :
    Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      = ((16 * (AdoorL M * (3072 * M) * M) : ℕ) : ℝ) * Real.log 2 := by
  rw [s13_calQK_doorL_two]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- `s13_band_log_calQK_two_L` at the lever. -/
theorem s13_band_log_calQK_two_L_gk (K M : ℕ) :
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      = ((16 * (AdoorL M * s13GK K M * M) : ℕ) : ℝ) * Real.log 2 := by
  have hQ2 : calQK (AdoorL M) (s13GK K M) M 2 = 2 ^ (16 * (AdoorL M * s13GK K M * M)) := by
    rw [calQK, calE_two]; ring_nf
  rw [hQ2]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- **⟦THE `𝒫₁` FLOOR AT THE LINEAR DOOR⟧** (`s13_band_loglog_calP_one_L`) —
`loglog 𝒫₁ ≥ 24.58` for every `M ≥ 1`.  The floor is the LANDED one: both cuts put
`2^36` under the anchor, so `gWin`'s covering-window budget `25 − 24.58 = 0.42` is
unchanged. -/
theorem s13_band_loglog_calP_one_L {M : ℕ} (hM : 1 ≤ M) :
    (2458 / 100 : ℝ) ≤ Real.log (Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hll : (-(3725 : ℝ) / 10000) ≤ Real.log (Real.log 2) := s13_band_loglog_two
  have hA : ((2 ^ 36 : ℕ) : ℝ) ≤ ((AdoorL M : ℕ) : ℝ) := by exact_mod_cast AdoorL_ge hM
  have hApos : (0 : ℝ) < ((AdoorL M : ℕ) : ℝ) := by
    have h2 : ((2 : ℝ)) ^ (36 : ℕ) ≤ ((AdoorL M : ℕ) : ℝ) := by push_cast at hA ⊢; linarith
    nlinarith [h2]
  have hlogA : (36 : ℝ) * Real.log 2 ≤ Real.log ((AdoorL M : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ 36 : ℕ) : ℝ)) hA
    rw [show ((2 ^ 36 : ℕ) : ℝ) = (2 : ℝ) ^ (36 : ℕ) by push_cast; ring, Real.log_pow] at h
    push_cast at h
    linarith
  rw [s13_band_log_calP_one_L, Real.log_mul (ne_of_gt hApos) (by linarith)]
  linarith

/-- `s13_band_loglog_calP_one_L` at the lever — level 1 does not move. -/
theorem s13_band_loglog_calP_one_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (2458 / 100 : ℝ) ≤ Real.log (Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) := by
  rw [calP_gk_one_eq]
  exact s13_band_loglog_calP_one_L hM

/-- **⟦THE `𝒬₂` FLOOR AT THE LINEAR DOOR⟧** (`s13_band_log_calQK_two_ge_L`) —
`log 𝒬₂ ≥ 1`, since `16·A_L·G·M ≥ 16` at `M ≥ 1`. -/
theorem s13_band_log_calQK_two_ge_L {M : ℕ} (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : 1 ≤ AdoorL M * (3072 * M) * M := by
    have hA := one_le_AdoorL hM
    have h2 : 1 ≤ 3072 * M := by omega
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ AdoorL M * (3072 * M) * M := Nat.mul_le_mul (Nat.mul_le_mul hA h2) hM
  have h16 : (16 : ℕ) ≤ 16 * (AdoorL M * (3072 * M) * M) := by omega
  have h16R : (16 : ℝ) ≤ ((16 * (AdoorL M * (3072 * M) * M) : ℕ) : ℝ) := by exact_mod_cast h16
  rw [s13_band_log_calQK_two_L]
  nlinarith [h16R, hlo]

/-- `s13_band_log_calQK_two_ge_L` at the lever. -/
theorem s13_band_log_calQK_two_ge_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : 1 ≤ AdoorL M * s13GK K M * M := by
    have hA := one_le_AdoorL hM
    have h2 : 1 ≤ s13GK K M := one_le_s13GK K hM
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ AdoorL M * s13GK K M * M := Nat.mul_le_mul (Nat.mul_le_mul hA h2) hM
  have h16 : (16 : ℕ) ≤ 16 * (AdoorL M * s13GK K M * M) := by omega
  have h16R : (16 : ℝ) ≤ ((16 * (AdoorL M * s13GK K M * M) : ℕ) : ℝ) := by exact_mod_cast h16
  rw [s13_band_log_calQK_two_L_gk]
  nlinarith [h16R, hlo]

/-! ## §2 — `S13CapFloor`'s `S13CapGatePerBlock` supplier at the linear door

The whole page reads the door through `𝒬K₂` alone.  `capfloor_one_lt_QK2`'s body is the only
one that unfolds the anchor, and it needs only `0 < A` and `0 < G`; stated there, the three
consumers below are instances. -/

/-- **`1 < 𝒬K₂`, ANCHOR-SYMBOLIC** (`capfloor_one_lt_QK2_gen`) — the positivity
`kappa30_of_TannGate` asks for, at any `A, G, M ≥ 1`. -/
theorem capfloor_one_lt_QK2_gen {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) :
    1 < ((calQK A G M 2 : ℕ) : ℝ) := by
  have hA0 : 0 < A := by omega
  have hE : 0 < calE A G 2 := by
    rw [calE]
    refine Nat.mul_pos (Nat.mul_pos hA0 (pow_pos (by omega : 0 < G) _)) ?_
    positivity
  have h : 1 < calQK A G M 2 := by
    rw [calQK]
    refine Nat.one_lt_two_pow_iff.mpr ?_
    have : 0 < (2 ^ 2 * M) * calE A G 2 := Nat.mul_pos (by positivity) hE
    omega
  exact_mod_cast h

/-- `1 < 𝒬K₂` at the linear door. -/
theorem capfloor_one_lt_QK2_L {M : ℕ} (hM : 1 ≤ M) :
    1 < ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) :=
  capfloor_one_lt_QK2_gen (one_le_AdoorL hM) (by omega) hM

/-- `capfloor_one_lt_QK2_L` at the lever. -/
theorem capfloor_one_lt_QK2_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    1 < ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) :=
  capfloor_one_lt_QK2_gen (one_le_AdoorL hM) (one_le_s13GK K hM) hM

/-- **⟦`QTann`, ANCHOR-SYMBOLIC⟧** — `𝒬K₂ ≤ q·T_ann`, `Q2_reg` exponentiated against the
gate (`log 𝒬K₂ ≤ r ≤ 30r ≤ log(q·T_ann)`). -/
theorem capfloor_QTann_gen {R : ChowlaRegime} {A G M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hAN : As ≤ Nd)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK A G M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK A G M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann := by
  have hgate := capfloor_tannGate hfl hb hAN hTlo (q := q)
  unfold TannGate at hgate
  rw [rpow_half_eq_sqrt] at hgate
  have hQ1 : 1 < ((calQK A G M 2 : ℕ) : ℝ) := capfloor_one_lt_QK2_gen hA hG hM
  have hQ0 : (0 : ℝ) < ((calQK A G M 2 : ℕ) : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) := Real.sqrt_nonneg _
  calc ((calQK A G M 2 : ℕ) : ℝ)
      = Real.exp (Real.log ((calQK A G M 2 : ℕ) : ℝ)) := (Real.exp_log hQ0).symm
    _ ≤ Real.exp (30 * Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (q : ℝ) * Tann := hgate

/-- **⟦`kappa30Q`, ANCHOR-SYMBOLIC⟧** — `30 ≤ log(q·T_ann)/log 𝒬K₂`. -/
theorem capfloor_kappa30Q_gen {R : ChowlaRegime} {A G M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hAN : As ≤ Nd)
    (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK A G M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((calQK A G M 2 : ℕ) : ℝ) := by
  refine kappa30_of_TannGate ((Nd : ℕ) : ℝ) ((q : ℝ) * Tann) (calQK A G M 2)
    (capfloor_one_lt_QK2_gen hA hG hM) ?_ (capfloor_tannGate hfl hb hAN hTlo)
  rw [rpow_half_eq_sqrt]; exact hQ2reg

/-- ⟦`QTann`⟧ at the linear door. -/
theorem capfloor_QTann_L {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann :=
  capfloor_QTann_gen hfl hb hAN (one_le_AdoorL hM) (by omega) hM hTlo hQ2reg

/-- ⟦`QTann`⟧ at the linear door, at the lever. -/
theorem capfloor_QTann_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann :=
  capfloor_QTann_gen hfl hb hAN (one_le_AdoorL hM) (one_le_s13GK K hM) hM hTlo hQ2reg

/-- ⟦`kappa30Q`⟧ at the linear door. -/
theorem capfloor_kappa30Q_L {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) :=
  capfloor_kappa30Q_gen hfl hb hAN (one_le_AdoorL hM) (by omega) hM hTlo hQ2reg

/-- ⟦`kappa30Q`⟧ at the linear door, at the lever. -/
theorem capfloor_kappa30Q_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hAN : As ≤ Nd)
    (hM : 1 ≤ M) (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) :=
  capfloor_kappa30Q_gen hfl hb hAN (one_le_AdoorL hM) (one_le_s13GK K hM) hM hTlo hQ2reg

/-- **⟦W-FLOOR'S SUPPLIER AT THE LINEAR DOOR⟧** (`s13CapFloor_all_L`) — EIGHT fields of
`S13FramesB.S13CapGatePerBlock` at one binder, with the two `𝒬K₂` reads at `AdoorL`.  The six
`T_ann`-only conjuncts are the landed terms verbatim: they never touch the anchor. -/
theorem s13CapFloor_all_L {R : ChowlaRegime} {M H L q j As s Nd : ℕ} {T₀ Kq Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hM : 1 ≤ M)
    (hAN : As ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)))
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) :
    ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann ∧
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ∧
    T₀ ≤ Tann ∧
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) ∧
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) ∧
    Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) :=
  ⟨capfloor_QTann_L hfl hb hAN hM hTlo hQ2reg,
   capfloor_kappa30Q_L hfl hb hAN hM hTlo hQ2reg,
   capfloor_T0_Tann hfl hb hAN hTlo hT₀,
   capfloor_floor1 hfl hb hAN hTlo,
   capfloor_floor2 hfl hb hAN hTlo,
   capfloor_floor3 hfl hb hAN hTlo hKq,
   capfloor_floor4 hfl hb hAN hTlo hKs,
   hQ2reg⟩

/-- `s13CapFloor_all_L` at the lever. -/
theorem s13CapFloor_all_L_gk (K : ℕ) {R : ChowlaRegime} {M H L q j As s Nd : ℕ}
    {T₀ Kq Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j As s) (hM : 1 ≤ M)
    (hAN : As ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)))
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) :
    ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann ∧
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ∧
    T₀ ≤ Tann ∧
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) ∧
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) ∧
    Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) :=
  ⟨capfloor_QTann_L_gk K hfl hb hAN hM hTlo hQ2reg,
   capfloor_kappa30Q_L_gk K hfl hb hAN hM hTlo hQ2reg,
   capfloor_T0_Tann hfl hb hAN hTlo hT₀,
   capfloor_floor1 hfl hb hAN hTlo,
   capfloor_floor2 hfl hb hAN hTlo,
   capfloor_floor3 hfl hb hAN hTlo hKq,
   capfloor_floor4 hfl hb hAN hTlo hKs,
   hQ2reg⟩

/-! ## §3 — `S14Compose`'s `p²` cap in logs, at the linear door -/

/-- **⟦THE `p²` CAP, IN LOGS, AT THE LINEAR DOOR⟧** (`s14_p2_in_logs_L`) —
`log 552960 + θ₂₉₃·loglog X_d ≤ A_L(M)·log 2`.  The re-cut RAISES the right side by the
factor `M/(⌊log₂M⌋+1)`, so the cap is strictly easier to meet than at the landed door — this
is the `lvl`-genre widening the whole re-cut buys. -/
theorem s14_p2_in_logs_L {M Xd : ℕ} {Cp : ℝ} (hX1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hg : GRowsZeroGate'''_L M Xd Cp (decayPool Xd)) :
    Real.log 552960 + theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  have hp2 := hg.p2
  have hP1pos : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := s15_calP_L_one_pos M
  have hP2pos : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := by
    have h : 0 < calP (AdoorL M) (3072 * M) 2 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hpool : decayPool Xd
      = Real.exp (-(theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))) := by
    rw [decayPool_def, Real.rpow_def_of_pos hL0]; ring_nf
  have hstep : 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ 1 / 4 * decayPool Xd := by
    have hpos : (0 : ℝ) < 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := one_div_pos.mpr hP2pos
    linarith
  rw [hpool] at hstep
  have hE : (0 : ℝ) < Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))) := Real.exp_pos _
  have hrw1 : 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      = 138240 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by ring
  have hrw2 : (1 : ℝ) / 4 * (Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))))⁻¹
      = 1 / (4 * Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))) := by
    field_simp
  rw [Real.exp_neg, hrw1, hrw2, div_le_div_iff₀ hP1pos (by positivity)] at hstep
  have hkey : 552960 * Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))
      ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
    s13_band_log_calP_one_L M] at hlog
  linarith

end Salt.MR

end
