/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13CapGrid
import Salt.MR.S13CapFloor
import Salt.MR.S13CapRbd
import Salt.MR.S11HoistGrade
import Salt.MR.S15SelLinearWide

/-!
# `S13FramesLinear` — THE FRAMES / SELECT LAYER AT THE LINEAR DOOR (`AdoorL M = 2^36·M`)

⟦LADDER-L G4⟧  `COMPOSE-FLAT-2` kernelized `flat_landed_ladder_break`: the road and the fuse
read the door a SECOND time, through the LADDER `calP (Adoor M) (s13GK K M)`, a copy the
register's re-cut missed.  `S15SelLinear` cut the REGISTER (`S15Sel''_L`); this page cuts the
`S13` FRAMES / SELECT layer the register's producers sit on — the Mertens/Rankin block gate,
the socket `M`-cap ⟦gate 8⟧, the row-zero base bundle, and the two generations of the
`M`-selection system (`MSelect`, `MSelect'`) with their satisfaction theorems.

⟦THE ONE STRUCTURAL MOVE⟧ four of the landed proofs on this layer read the anchor only
through `2^36 ≤ Adoor M` and `1 ≤ Adoor M`, and the `G`-slot only through `1 ≤ G`.  Rather
than replay them twice (once at `Adoor`, once at `AdoorL`) they are re-stated ONCE at a
SYMBOLIC anchor `A` with `2^36 ≤ A` (`s13_sieveBlockGate_gen`, `s13_gate8_gen`,
`s13_doorRowZeroBase_five_gen`, `s13_winFit_of_halfWindow_gen`), and both cuts are instances.
The landed declarations are untouched; what is added is the general form and the `_L`
instance.

⟦THE FOUR BREAK SITES THIS PAGE OWNS⟧ `MSelect_gk.gRows` and `MSelect'_gk.gRows` — the two
`242·λ₊ ≤ Adoor M` fields ⟦COMPOSE-FLAT-2⟧ named — are re-cut here as `MSelect_L_gk.gRows`
and `MSelect'_L_gk.gRows` at `AdoorL M`.  Every consumer bridge off those fields
(`s13_gate8_of_MSelect`, `s13_g2_jfloor_of_MSelect`, `s13_doorGates_of_MSelect'`,
`s13_smallGradeFits_of_MSelect'`) re-routes with its landed body.

⟦WHAT DOES NOT MOVE⟧ the `G`-slot (`3072·M`, resp. `s13GK K M`), every landed declaration,
and every statement that reads the anchor only through its FLOOR — `AdoorL_ge` has the LANDED
conclusion `2^36 ≤ ·` under the hypothesis `1 ≤ M` that every door consumer already carries
(⟦LINEAR-PAGE⟧'s transport-freeness).
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — the block scale at the linear door

`S15SelLinear.s13BlockExp_L` is the exponent; what is added here is the FLOOR
`s13BlockFloor_L M = 2^{s13BlockExp_L M}`, the shape `MSelect_L.blockCeil` reads. -/

/-- `S13FramesA.s13BlockFloor` at the linear anchor. -/
def s13BlockFloor_L (M : ℕ) : ℕ := 2 ^ s13BlockExp_L M

/-- `S13FramesA.s13BlockFloor_gk` at the linear anchor. -/
def s13BlockFloor_L_gk (K M : ℕ) : ℕ := 2 ^ s13BlockExp_L_gk K M

/-- The landed block floor sits BELOW the linear one (`s13BlockExp_le_L`), so every
`X`-floor supplied against the linear scale supplies the landed one for free. -/
theorem s13BlockFloor_le_L {M : ℕ} (hM : 1 ≤ M) : s13BlockFloor M ≤ s13BlockFloor_L M :=
  Nat.pow_le_pow_right (by norm_num) (s13BlockExp_le_L hM)

/-! ## §1 — ⟦THE MERTENS/RANKIN PAGE AT A SYMBOLIC ANCHOR⟧

`s13_sieveBlockGate`'s body reads `Adoor M` only through `2^36 ≤ Adoor M`, and `3072·M` only
through `1 ≤ 3072·M`.  Stated at a symbolic `(A, G)` it covers both cuts and both `G`-slots
(the lever's `s13GK K M` included) at once. -/

set_option maxHeartbeats 1000000 in
-- the four analytic conjuncts at astronomically large SYMBOLIC exponents `400·(A·G·M)²`;
-- every numeric step is an `nlinarith`/`positivity` over casts of those exponents
/-- **⟦THE MERTENS/RANKIN PAGE, ANCHOR-SYMBOLIC⟧** (`s13_sieveBlockGate_gen`) — HS-3's four
analytic gates at ANY anchor above `2^36` and any `G ≥ 1`, from the single scale floor
`2^{14427 + (64 + 8(⌊log₂M⌋+1)) + 400(A·G·M)²} ≤ X`.  `S13FramesA.s13_sieveBlockGate` is the
instance `A = Adoor M`, `G = 3072M`; `s13_sieveBlockGate_L` below is `A = AdoorL M`. -/
theorem s13_sieveBlockGate_gen {A G M X : ℕ} (hM : 1 ≤ M) (hG : 1 ≤ G) (hA36 : 2 ^ 36 ≤ A)
    (hX : 2 ^ (14427 + (64 + 8 * (Nat.log 2 M + 1)) + 400 * (A * G * M) ^ 2) ≤ X) :
    SieveBlockGate A G M 2 X := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  set N : ℕ := 14427 + (64 + 8 * (Nat.log 2 M + 1)) + 400 * (A * G * M) ^ 2 with hN
  have hXN : ((2 : ℝ)) ^ N ≤ (X : ℝ) := by
    have h : ((2 ^ N : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    simpa using h
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hX0 : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le h2pos hXN
  have hX1 : 1 ≤ X := by
    have : (0 : ℕ) < X := by exact_mod_cast hX0
    omega
  have hsplit : ∀ a : ℕ, a ≤ N → ((2 : ℝ)) ^ a ≤ (X : ℝ) := by
    intro a ha
    refine le_trans (pow_le_pow_right₀ (by norm_num) ha) hXN
  have hA : 14427 ≤ N := by rw [hN]; omega
  have hB : 64 + 8 * (Nat.log 2 M + 1) ≤ N := by rw [hN]; omega
  have hC : 400 * (A * G * M) ^ 2 ≤ N := by rw [hN]; omega
  -- ⟦GATE (b)⟧ `√log X ≥ 100`
  have hexp : Real.exp 10000 ≤ (X : ℝ) := by
    have hpow : ((2 : ℝ)) ^ (14427 : ℕ) = Real.exp ((14427 : ℕ) * Real.log 2) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    have hle : (10000 : ℝ) ≤ ((14427 : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      nlinarith [hlog2lo]
    calc Real.exp 10000 ≤ Real.exp (((14427 : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hle
      _ = ((2 : ℝ)) ^ (14427 : ℕ) := hpow.symm
      _ ≤ (X : ℝ) := hsplit _ hA
  have hbig : (100 : ℝ) ≤ Real.sqrt (Real.log X) := hbig_of_floor hexp
  have hlogX : ((N : ℕ) : ℝ) * Real.log 2 ≤ Real.log (X : ℝ) := by
    have h1 : Real.log (((2 : ℝ)) ^ N) ≤ Real.log (X : ℝ) := Real.log_le_log h2pos hXN
    rwa [Real.log_pow] at h1
  -- ⟦GATE (c)⟧ MR's regularity, at `j ∈ {1, 2}`
  have hA1N : 1 ≤ A := le_trans (by norm_num) hA36
  have hAd : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1N
  have hGR : (1 : ℝ) ≤ (G : ℝ) := by exact_mod_cast hG
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set W : ℝ := (A : ℝ) * (G : ℝ) * (M : ℝ) with hW
  have hAG1 : (1 : ℝ) ≤ (A : ℝ) * (G : ℝ) := by nlinarith
  have hW1 : (1 : ℝ) ≤ W := by rw [hW]; nlinarith
  have hWN : (400 : ℝ) * W ^ 2 ≤ ((N : ℕ) : ℝ) := by
    have h : ((400 * (A * G * M) ^ 2 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hC
    rw [hW]
    push_cast at h ⊢
    linarith
  have hreg2 : (256 : ℝ) * W ^ 2 ≤ Real.log (X : ℝ) := by
    have h1 : (400 : ℝ) * W ^ 2 * Real.log 2 ≤ ((N : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hWN hlog2.le
    nlinarith [sq_nonneg W, hW1]
  have hsqrtW : (16 : ℝ) * W ≤ Real.sqrt (Real.log X) := by
    have h1 : ((16 : ℝ) * W) ^ 2 ≤ Real.log (X : ℝ) := by nlinarith
    have h2 : Real.sqrt (((16 : ℝ) * W) ^ 2) ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by nlinarith)] at h2
  have hregj : ∀ j ∈ Finset.Icc 1 2,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    refine le_trans ?_ hsqrtW
    rw [log_calQK]
    have hAd0 : (0 : ℝ) < (A : ℝ) := by linarith
    have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
    have hG0 : (0 : ℝ) < (G : ℝ) := by linarith
    interval_cases j
    · rw [calE_one, hW]
      push_cast
      nlinarith [hlog2hi, hlog2, hAd, hMR, hGR, hAd0, hM0, hG0,
        mul_pos hAd0 hM0, mul_pos (mul_pos hAd0 hG0) hM0,
        mul_nonneg (mul_pos hAd0 hM0).le (sub_nonneg.mpr hGR),
        mul_nonneg (mul_pos hAd0 hG0).le (sub_nonneg.mpr hMR)]
    · rw [calE_two, hW]
      push_cast
      nlinarith [hlog2hi, hlog2, hAd, hMR, hGR, hAd0, hM0, hG0,
        mul_pos (mul_pos hAd0 hG0) hM0, mul_pos hAd0 hG0]
  -- ⟦GATE (d)⟧ the error domination, through `herr_of_floor`
  have hM8 : (M : ℝ) ^ 8 ≤ ((2 : ℝ)) ^ (8 * (Nat.log 2 M + 1)) := by
    have hlt : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    have hltR : (M : ℝ) ≤ ((2 : ℝ)) ^ (Nat.log 2 M + 1) := by
      have : ((M : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 M + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
      simpa using this
    calc (M : ℝ) ^ 8 ≤ (((2 : ℝ)) ^ (Nat.log 2 M + 1)) ^ 8 :=
          pow_le_pow_left₀ (by positivity) hltR 8
      _ = ((2 : ℝ)) ^ (8 * (Nat.log 2 M + 1)) := by rw [← pow_mul, Nat.mul_comm]
  have hXM : ((2 : ℝ)) ^ (64 : ℕ) * (M : ℝ) ^ 8 ≤ (X : ℝ) := by
    calc ((2 : ℝ)) ^ (64 : ℕ) * (M : ℝ) ^ 8
        ≤ ((2 : ℝ)) ^ (64 : ℕ) * ((2 : ℝ)) ^ (8 * (Nat.log 2 M + 1)) := by
          have : (0 : ℝ) < ((2 : ℝ)) ^ (64 : ℕ) := by positivity
          nlinarith [hM8]
      _ = ((2 : ℝ)) ^ (64 + 8 * (Nat.log 2 M + 1)) := by rw [← pow_add]
      _ ≤ (X : ℝ) := hsplit _ hB
  have hsqrtX : ((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4 ≤ Real.sqrt X := by
    have h1 : (((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4) ^ 2 ≤ (X : ℝ) := by
      have hid : (((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4) ^ 2
          = ((2 : ℝ)) ^ (64 : ℕ) * (M : ℝ) ^ 8 := by ring
      rw [hid]; exact hXM
    have h2 : Real.sqrt ((((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4) ^ 2) ≤ Real.sqrt X :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hlogP1 : (57 : ℝ) ≤ Real.log ((calP A G 1 : ℕ) : ℝ) := by
    rw [log_calP_one_gen]
    have hAd36 : ((2 : ℝ)) ^ (36 : ℕ) ≤ (A : ℝ) := by exact_mod_cast hA36
    have h36 : ((2 : ℝ)) ^ (36 : ℕ) = 68719476736 := by norm_num
    rw [h36] at hAd36
    nlinarith [hlog2lo, hAd36]
  have hexp57 : ∀ j : ℕ, 1 ≤ j →
      Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ)) ≤ 3 := by
    intro j hj
    have hmono : Real.log ((calP A G 1 : ℕ) : ℝ) ≤ Real.log ((calP A G j : ℕ) : ℝ) := by
      rw [log_calP, log_calP]
      have hE : calE A G 1 ≤ calE A G j := calE_mono A hG hj
      have hEc : ((calE A G 1 : ℕ) : ℝ) ≤ ((calE A G j : ℕ) : ℝ) := by exact_mod_cast hE
      exact mul_le_mul_of_nonneg_right hEc hlog2.le
    have hlogPj : (57 : ℝ) ≤ Real.log ((calP A G j : ℕ) : ℝ) := le_trans hlogP1 hmono
    have hlogPj0 : (0 : ℝ) < Real.log ((calP A G j : ℕ) : ℝ) := by linarith
    have hdiv : 57 / Real.log ((calP A G j : ℕ) : ℝ) ≤ 1 :=
      (div_le_one hlogPj0).mpr (by linarith)
    calc Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ))
        ≤ Real.exp 1 := Real.exp_le_exp.mpr hdiv
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have herrj : ∀ j ∈ Finset.Icc 1 2,
      ((Nat.sqrt X : ℝ) + 1)
          * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
        ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine herr_of_floor hA1N hG hM hj.1 hX1 ?_
    have hjR : ((j : ℝ)) ^ 2 * (M : ℝ) ≤ 4 * (M : ℝ) := by
      have hjle : ((j : ℝ)) ≤ 2 := by exact_mod_cast hj.2
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hjsq : ((j : ℝ)) ^ 2 ≤ 4 := by nlinarith
      exact mul_le_mul_of_nonneg_right hjsq (Nat.cast_nonneg M)
    have hj4 : (((j : ℝ)) ^ 2 * (M : ℝ)) ^ 4 ≤ 256 * (M : ℝ) ^ 4 := by
      have h0 : (0 : ℝ) ≤ ((j : ℝ)) ^ 2 * (M : ℝ) := by positivity
      calc (((j : ℝ)) ^ 2 * (M : ℝ)) ^ 4 ≤ (4 * (M : ℝ)) ^ 4 := pow_le_pow_left₀ h0 hjR 4
        _ = 256 * (M : ℝ) ^ 4 := by ring
    have hE := hexp57 j hj.1
    have hE0 : (0 : ℝ) < Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ)) := Real.exp_pos _
    have hM4 : (0 : ℝ) < (M : ℝ) ^ 4 := by positivity
    calc 16 * (((j : ℝ)) ^ 2 * (M : ℝ)) ^ 4
            * Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ))
        ≤ 16 * (256 * (M : ℝ) ^ 4) * 3 := by nlinarith
      _ = 12288 * (M : ℝ) ^ 4 := by ring
      _ ≤ ((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4 := by
          have h12 : (12288 : ℝ) ≤ ((2 : ℝ)) ^ (32 : ℕ) := by norm_num
          exact mul_le_mul_of_nonneg_right h12 (by positivity)
      _ ≤ Real.sqrt X := hsqrtX
  exact ⟨hX0, hbig, hregj, herrj⟩

/-- **⟦THE MERTENS/RANKIN PAGE AT THE LINEAR DOOR⟧** (`s13_sieveBlockGate_L`) — the `_gen`
instance at `A = AdoorL M`.  The only new hypothesis is `1 ≤ M`, which the landed statement
already carries. -/
theorem s13_sieveBlockGate_L {M X : ℕ} (hM : 1 ≤ M) (hX : s13BlockFloor_L M ≤ X) :
    SieveBlockGate (AdoorL M) (3072 * M) M 2 X :=
  s13_sieveBlockGate_gen hM (by omega) (AdoorL_ge hM) hX

/-- `s13_sieveBlockGate_L` at the `G`-lever. -/
theorem s13_sieveBlockGate_L_gk {K M X : ℕ} (hM : 1 ≤ M) (hX : s13BlockFloor_L_gk K M ≤ X) :
    SieveBlockGate (AdoorL M) (s13GK K M) M 2 X := by
  refine s13_sieveBlockGate_gen hM ?_ (AdoorL_ge hM) hX
  rw [s13GK]
  have : 0 < 3072 * 2 ^ K * M := by positivity
  omega

/-! ## §2 — ⟦A-4⟧ ⟦GATE 8⟧ THE SOCKET `M`-CAP -/

/-- **⟦GATE 8, ANCHOR-SYMBOLIC⟧** (`s13_gate8_gen`) — `arcDen 12 H < 𝒫₁ = 2^A` on the window
range, from `λ₊ ≤ Λ` and `12·Λ < A·log 2`.  `S13FramesA.s13_gate8` is the instance
`A = Adoor M`. -/
theorem s13_gate8_gen {R : ChowlaRegime} {A G : ℕ} {Λ : ℝ}
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ)
    (hgate : 12 * Λ < (A : ℝ) * Real.log 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H < ((calP A G 1 : ℕ) : ℝ) := by
  intro H hlo hhi
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hLH : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hLH
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) := by
    rw [arcDen, Real.log_rpow hL0]
  have hle := le_trans (s13_loglog_le_of_range (R := R) hlo hhi) hΛ
  have hlogP : Real.log ((calP A G 1 : ℕ) : ℝ) = (A : ℝ) * Real.log 2 := log_calP_one_gen A G
  have hP0 : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have h : 0 < calP A G 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hlt : Real.log (arcDen 12 H) < Real.log ((calP A G 1 : ℕ) : ℝ) := by
    rw [hlogarc, hlogP]; linarith
  have h1 := Real.exp_lt_exp.mpr hlt
  rwa [Real.exp_log (by linarith : (0 : ℝ) < arcDen 12 H), Real.exp_log hP0] at h1

/-- **⟦GATE 8 AT THE LINEAR DOOR⟧** (`s13_gate8_L`). -/
theorem s13_gate8_L {R : ChowlaRegime} {M : ℕ} {Λ : ℝ}
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ)
    (hgate : 12 * Λ < ((AdoorL M : ℕ) : ℝ) * Real.log 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) :=
  s13_gate8_gen (R := R) (G := 3072 * M) hΛ hgate

/-- `s13_gate8_L` at the `G`-lever — the anchor is `G`-free, so only the `G`-slot moves. -/
theorem s13_gate8_L_gk {R : ChowlaRegime} {K M : ℕ} {Λ : ℝ}
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ)
    (hgate : 12 * Λ < ((AdoorL M : ℕ) : ℝ) * Real.log 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) :=
  s13_gate8_gen (R := R) (G := s13GK K M) hΛ hgate

/-! ## §3 — ⟦B⟧ `DoorRowZeroBase`'s FIVE NON-`coefWS` FIELDS -/

/-- **⟦THE ROW-ZERO BASE BUNDLE, ANCHOR-SYMBOLIC⟧** (`s13_doorRowZeroBase_five_gen`).
`Q1_le_h` is the socket's own `j`-floor `M·A ≤ j`, `h_four` its `2 ≤ j` shadow, and the
other three are `SieveBlockGate`'s conjuncts at the base. -/
theorem s13_doorRowZeroBase_five_gen {A G M Xd j : ℕ} (hM : 1 ≤ M) (hG : 1 ≤ G)
    (hA36 : 2 ^ 36 ≤ A)
    (hXd : 2 ^ (14427 + (64 + 8 * (Nat.log 2 M + 1)) + 400 * (A * G * M) ^ 2) ≤ Xd)
    (hj : M * A ≤ j) :
    calQK A G M 2 ≤ Xd ∧
      Real.log ((calQK A G M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
      ((calQK A G M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
  have hgate := s13_sieveBlockGate_gen hM hG hA36 hXd
  have hA1 : 1 ≤ A := le_trans (by norm_num) hA36
  have ht1 : 1 ≤ A * G * M := by
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ A * G * M := Nat.mul_le_mul (Nat.mul_le_mul hA1 hG) hM
  have hj2 : 2 ≤ j := by
    have hfl : 2 ^ 36 ≤ M * A := by
      calc 2 ^ 36 = 1 * 2 ^ 36 := by ring
        _ ≤ M * A := Nat.mul_le_mul hM hA36
    have h36 : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
    omega
  have hQ1 : calQK A G M 1 = 2 ^ (M * A) := by rw [calQK, calE_one]; ring_nf
  have hQ2 : calQK A G M 2 = 2 ^ (16 * (A * G * M)) := by rw [calQK, calE_two]; ring_nf
  refine ⟨?_, hgate.2.2.1 2 (by simp), hgate.2.1, ?_, ?_⟩
  · rw [hQ2]
    have hstep : 16 * (A * G * M) ≤ 400 * (A * G * M) ^ 2 := by
      have h : (A * G * M) ^ 2 = (A * G * M) * (A * G * M) := by ring
      rw [h]
      calc 16 * (A * G * M) ≤ 400 * (A * G * M) := by omega
        _ = 400 * (A * G * M) * 1 := by ring
        _ ≤ 400 * (A * G * M) * (A * G * M) := Nat.mul_le_mul_left _ ht1
        _ = 400 * ((A * G * M) * (A * G * M)) := by ring
    refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hXd
    omega
  · have h : (2 : ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    have hR : ((2 ^ 2 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
    simpa using hR
  · rw [hQ1]
    have h : (2 : ℕ) ^ (M * A) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    exact_mod_cast h

/-- **⟦THE ROW-ZERO BASE BUNDLE AT THE LINEAR DOOR⟧** (`s13_doorRowZeroBase_five_L`). -/
theorem s13_doorRowZeroBase_five_L {M Xd j : ℕ} (hM : 1 ≤ M)
    (hXd : s13BlockFloor_L M ≤ Xd) (hj : doorRowFloorL M ≤ j) :
    calQK (AdoorL M) (3072 * M) M 2 ≤ Xd ∧
      Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
          ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
      ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
  s13_doorRowZeroBase_five_gen hM (by omega) (AdoorL_ge hM) hXd (by rwa [doorRowFloorL] at hj)

/-- `s13_doorRowZeroBase_five_L` at the `G`-lever. -/
theorem s13_doorRowZeroBase_five_L_gk (K : ℕ) {M Xd j : ℕ} (hM : 1 ≤ M)
    (hXd : s13BlockFloor_L_gk K M ≤ Xd) (hj : doorRowFloorL M ≤ j) :
    calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd ∧
      Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
          ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
      ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
  refine s13_doorRowZeroBase_five_gen hM ?_ (AdoorL_ge hM) hXd (by rwa [doorRowFloorL] at hj)
  rw [s13GK]
  have : 0 < 3072 * 2 ^ K * M := by positivity
  omega

/-! ## §4 — ⟦THE `M`-SELECTION SYSTEM, FIRST GENERATION, AT THE LINEAR DOOR⟧

`S13FramesA.MSelect`'s five fields, with field ⟦3⟧ (`gRows`) at `AdoorL M` — ⟦COMPOSE-FLAT-2⟧'s
FIRST named break site — and fields ⟦2⟧/⟦4⟧/⟦5⟧ at the linear row floor and block floor. -/

/-- **`S13FramesA.MSelect` AT THE LINEAR DOOR** (`MSelect_L`). -/
structure MSelect_L (Cg δ₀ Λ : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus (`AdoorL 0 = 0`). -/
  hM : 1 ≤ M
  /-- ⟦1⟧ the `b`-floor — `M4DoorGates.hMδ`, verbatim. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦2⟧ the ×1280 window's floor, at the LINEAR row floor. -/
  winFloor : Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ) ≤ Real.log (R.Hlo : ℝ)
  /-- ⟦3⟧ ⟦THE BREAK SITE⟧ the surviving `gRows` demand at the LINEAR anchor. -/
  gRows : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦4⟧ the `𝒰`-leg absorption line at the LINEAR window exponent. -/
  absorb : Real.log 8640
    ≤ (theta293 - 1 / 500) * Real.log (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
  /-- ⟦5⟧ the DEMOTED arm summand at the LINEAR block ceiling. -/
  blockCeil : 4 * R.ω * s13BlockFloor_L M ≤ R.x

/-- `MSelect_L` at the `G`-lever.  Only `blockCeil` moves. -/
structure MSelect_L_gk (K : ℕ) (Cg δ₀ Λ : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦1⟧ the `b`-floor. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦2⟧ the ×1280 window's floor (LEVEL 1: `doorRowFloorL` is K-INVARIANT). -/
  winFloor : Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ) ≤ Real.log (R.Hlo : ℝ)
  /-- ⟦3⟧ ⟦THE BREAK SITE⟧ `gRows` at the LINEAR anchor. -/
  gRows : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦4⟧ the `𝒰`-leg absorption line. -/
  absorb : Real.log 8640
    ≤ (theta293 - 1 / 500) * Real.log (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ))
  /-- ⟦5⟧ the LEVERED LINEAR block ceiling. -/
  blockCeil : 4 * R.ω * s13BlockFloor_L_gk K M ≤ R.x

/-- **⟦A-4 FROM `MSelect_L`⟧** (`s13_gate8_of_MSelect_L`) — ⟦gate 8⟧'s numeral gate off field
⟦3⟧ alone (`242·log 2 = 167.7 > 12`), at the LINEAR anchor. -/
theorem s13_gate8_of_MSelect_L {Cg δ₀ Λ : ℝ} {R : ChowlaRegime} {M : ℕ} (hΛ : 0 < Λ)
    (hS : MSelect_L Cg δ₀ Λ R M) : 12 * Λ < ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h := hS.gRows
  nlinarith [hΛ, h, hlog2]

/-- `s13_gate8_of_MSelect_L` at the lever — the conclusion is anchor-only, hence `K`-free. -/
theorem s13_gate8_of_MSelect_L_gk (K : ℕ) {Cg δ₀ Λ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hΛ : 0 < Λ) (hS : MSelect_L_gk K Cg δ₀ Λ R M) :
    12 * Λ < ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h := hS.gRows
  nlinarith [hΛ, h, hlog2]

/-- **⟦A-3 FROM `MSelect_L`⟧** (`s13_g2_jfloor_of_MSelect_L`) — ⟦G2⟧'s `j₀`-floor at the
LINEAR row floor (`doorRowFloorL M = M·AdoorL M ≥ AdoorL M ≥ 242Λ`). -/
theorem s13_g2_jfloor_of_MSelect_L {Cg δ₀ Λ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hΛ : 1 ≤ Λ) (hS : MSelect_L Cg δ₀ Λ R M) :
    4 * Real.log 263 + 48 * Λ ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : ((AdoorL M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have h : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]
      calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
        _ ≤ M * AdoorL M := Nat.mul_le_mul_right _ hS.hM
    exact_mod_cast h
  have h := hS.gRows
  linarith

/-- `s13_g2_jfloor_of_MSelect_L` at the lever. -/
theorem s13_g2_jfloor_of_MSelect_L_gk (K : ℕ) {Cg δ₀ Λ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hΛ : 1 ≤ Λ) (hS : MSelect_L_gk K Cg δ₀ Λ R M) :
    4 * Real.log 263 + 48 * Λ ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : ((AdoorL M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have h : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]
      calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
        _ ≤ M * AdoorL M := Nat.mul_le_mul_right _ hS.hM
    exact_mod_cast h
  have h := hS.gRows
  linarith

/-- `8·(4^m)² = 2^{4m+3}` — the headroom field's exponent, normalised (the landed
`s13_headroom_pow` is private to `S13FramesA`, so it is re-derived here). -/
private theorem s13_headroom_pow_L (m : ℕ) : 8 * (4 ^ m) ^ 2 = 2 ^ (4 * m + 3) := by
  have h1 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
  have h2 : ((2 : ℕ) ^ (2 * m)) ^ 2 = 2 ^ (4 * m) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [h1, h2, pow_add]
  ring

/-- **⟦THE LINEAR `M`-SELECTION SYSTEM IS NONEMPTY AT THE REGIME'S HEADROOM⟧**
(`s13_MSelect_L_of_headroom`) — the landed walk at the LINEAR block exponent.  The four
non-scale demands are carried; the block ceiling is discharged from `R.hPHheadroom`. -/
theorem s13_MSelect_L_of_headroom {Cg δ₀ Λ : ℝ} {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hwin : Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ) ≤ Real.log (R.Hlo : ℝ))
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ))
    (habs : Real.log 8640
      ≤ (theta293 - 1 / 500) * Real.log (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ)))
    (hhead : s13BlockExp_L M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect_L Cg δ₀ Λ R M := by
  refine ⟨hM, hbf, hwin, hgr, habs, ?_⟩
  have hfield := R.hPHheadroom
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hnat : 4 * s13BlockFloor_L M ≤ 8 * (4 ^ m) ^ 2 := by
    have h1 : 4 * s13BlockFloor_L M = 2 ^ (s13BlockExp_L M + 2) := by
      rw [s13BlockFloor_L, pow_add]; ring
    rw [h1, s13_headroom_pow_L]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((4 * s13BlockFloor_L M : ℕ) : ℝ) ≤ ((8 * (4 ^ m) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hchain : ((4 * R.ω * s13BlockFloor_L M : ℕ) : ℝ) ≤ (R.x : ℝ) := by
    push_cast at hcast hfield ⊢
    nlinarith [hcast, hfield, hω0]
  exact_mod_cast hchain

/-- `s13_MSelect_L_of_headroom` at the lever. -/
theorem s13_MSelect_L_of_headroom_gk (K : ℕ) {Cg δ₀ Λ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hwin : Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ) ≤ Real.log (R.Hlo : ℝ))
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ))
    (habs : Real.log 8640
      ≤ (theta293 - 1 / 500) * Real.log (Real.log 2 * ((doorRowFloorL M : ℕ) : ℝ)))
    (hhead : s13BlockExp_L_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect_L_gk K Cg δ₀ Λ R M := by
  refine ⟨hM, hbf, hwin, hgr, habs, ?_⟩
  have hfield := R.hPHheadroom
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hnat : 4 * s13BlockFloor_L_gk K M ≤ 8 * (4 ^ m) ^ 2 := by
    have h1 : 4 * s13BlockFloor_L_gk K M = 2 ^ (s13BlockExp_L_gk K M + 2) := by
      rw [s13BlockFloor_L_gk, pow_add]; ring
    rw [h1, s13_headroom_pow_L]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((4 * s13BlockFloor_L_gk K M : ℕ) : ℝ) ≤ ((8 * (4 ^ m) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hchain : ((4 * R.ω * s13BlockFloor_L_gk K M : ℕ) : ℝ) ≤ (R.x : ℝ) := by
    push_cast at hcast hfield ⊢
    nlinarith [hcast, hfield, hω0]
  exact_mod_cast hchain

/-! ## §5 — ⟦THE `M`-SELECTION SYSTEM, SECOND GENERATION, AT THE LINEAR DOOR⟧

`S13MSelect2.MSelect'` — the corrected system, whose ⟦4⟧ `winFit` IS `s13_smallGradeFits`'
gate.  `MSelect'_gk.gRows` is ⟦COMPOSE-FLAT-2⟧'s SECOND named break site. -/

/-- **⟦THE WINDOW GATE FROM THE HALF-WINDOW FLOOR, `j`-SYMBOLIC⟧**
(`s13_winFit_of_halfWindow_gen`) — `S13MSelect2.s13_winFit_of_halfWindow` with the row floor
carried as an OPAQUE real, which is all its body ever uses.  Both cuts instantiate. -/
theorem s13_winFit_of_halfWindow_gen {R : ChowlaRegime} {jr ρ : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hhalf : (7 / 10 : ℝ) * jr + 3 * Real.log (1 / ρ) ≤ Real.log (R.Hlo : ℝ) / 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * jr
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidual H) - Real.log ρ)
        ≤ Real.log (H : ℝ) := by
  intro H hlo _
  have hHlo4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hH4 : 4000000 ≤ H := le_trans hHlo4 hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hHloR : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast hHlo4
  have hloR : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlo
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hloR
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hlogHbig : (4000000 : ℝ) ≤ Real.log (H : ℝ) := le_trans s13_four_million_le_exp50 hexp50
  set w : ℝ := Real.sqrt (Real.log (H : ℝ)) with hw
  have hw2 : w ^ 2 = Real.log (H : ℝ) := Real.sq_sqrt hlogH0.le
  have hw0 : (0 : ℝ) < w := by rw [hw]; exact Real.sqrt_pos.mpr hlogH0
  have hw2000 : (2000 : ℝ) ≤ w := by nlinarith [hw2, hw0, hlogHbig]
  have hlogw : Real.log w = Real.log (Real.log (H : ℝ)) / 2 := by
    rw [hw]; exact Real.log_sqrt hlogH0.le
  have hlogwle : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hllH : Real.log (Real.log (H : ℝ)) ≤ 2 * w - 2 := by rw [hlogw] at hlogwle; linarith
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hSval : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) := by
    rw [strataResidual, harcpow, Real.log_pow]; push_cast; ring
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith
  have hS1 : (1 : ℝ) ≤ strataResidual H := by rw [hSval]; linarith
  have hlogS : Real.log (strataResidual H) ≤ strataResidual H - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hSle : strataResidual H - 1 ≤ 24 * w - 24 := by rw [hSval]; linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlog9 : Real.log 9 ≤ 4 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith
  have hinv : Real.log (1 / ρ) = - Real.log ρ := by rw [one_div, Real.log_inv]
  rw [hinv] at hhalf
  nlinarith [hhalf, hlogmono, hllH, hlogS, hSle, hlog9, hw2, hw2000, hw0]

/-- **`S13MSelect2.MSelect'` AT THE LINEAR DOOR** (`MSelect'_L`). -/
structure MSelect'_L (Cg δ₀ Λ ρ : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦1⟧ the `b`-floor, verbatim. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦2⟧ ⟦THE BREAK SITE⟧ `gRows` at the LINEAR anchor. -/
  gRows : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦3⟧ the DEMOTED arm summand at the LINEAR block ceiling. -/
  blockCeil : 4 * R.ω * s13BlockFloor_L M ≤ R.x
  /-- ⟦4⟧ THE TRUE WINDOW GATE at the LINEAR row floor. -/
  winFit : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
    (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
            + 2 * Real.log (strataResidual H) - Real.log ρ)
      ≤ Real.log (H : ℝ)

/-- `MSelect'_L` at the lever.  Only `blockCeil` moves. -/
structure MSelect'_L_gk (K : ℕ) (Cg δ₀ Λ ρ : ℝ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦1⟧ the `b`-floor. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦2⟧ ⟦THE BREAK SITE⟧ `gRows` at the LINEAR anchor. -/
  gRows : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦3⟧ the LEVERED LINEAR block ceiling. -/
  blockCeil : 4 * R.ω * s13BlockFloor_L_gk K M ≤ R.x
  /-- ⟦4⟧ THE TRUE WINDOW GATE at the LINEAR row floor. -/
  winFit : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
    (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
            + 2 * Real.log (strataResidual H) - Real.log ρ)
      ≤ Real.log (H : ℝ)

/-- **⟦A-4 FROM `MSelect'_L`⟧** (`s13_gate8_of_MSelect'_L`). -/
theorem s13_gate8_of_MSelect'_L {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} (hΛ : 0 < Λ)
    (hS : MSelect'_L Cg δ₀ Λ ρ R M) : 12 * Λ < ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h := hS.gRows
  nlinarith [hΛ, h, hlog2]

/-- `s13_gate8_of_MSelect'_L` at the lever. -/
theorem s13_gate8_of_MSelect'_L_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hΛ : 0 < Λ) (hS : MSelect'_L_gk K Cg δ₀ Λ ρ R M) :
    12 * Λ < ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h := hS.gRows
  nlinarith [hΛ, h, hlog2]

/-- **⟦A-3 FROM `MSelect'_L`⟧** (`s13_g2_jfloor_of_MSelect'_L`). -/
theorem s13_g2_jfloor_of_MSelect'_L {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hΛ : 1 ≤ Λ) (hS : MSelect'_L Cg δ₀ Λ ρ R M) :
    4 * Real.log 263 + 48 * Λ ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : ((AdoorL M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have h : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]
      calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
        _ ≤ M * AdoorL M := Nat.mul_le_mul_right _ hS.hM
    exact_mod_cast h
  have h := hS.gRows
  linarith

/-- `s13_g2_jfloor_of_MSelect'_L` at the lever. -/
theorem s13_g2_jfloor_of_MSelect'_L_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hΛ : 1 ≤ Λ) (hS : MSelect'_L_gk K Cg δ₀ Λ ρ R M) :
    4 * Real.log 263 + 48 * Λ ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
  have hlog := s13_log263_le_six
  have hdr : ((AdoorL M : ℕ) : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by
    have h : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]
      calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
        _ ≤ M * AdoorL M := Nat.mul_le_mul_right _ hS.hM
    exact_mod_cast h
  have h := hS.gRows
  linarith

/-- **⟦A-5 FROM `MSelect'_L`⟧** (`s13_smallGradeFits_of_MSelect'_L`) — field ⟦4⟧ IS
`s13_smallGradeFits`' gate, at the LINEAR row floor. -/
theorem s13_smallGradeFits_of_MSelect'_L {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hS : MSelect'_L Cg δ₀ Λ ρ R M) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      m4SmallGradeFits (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
        (fun H => 2 * rStrWitness H) H :=
  fun H hlo hhi => s13_smallGradeFits hρ0 hρ1 hlo (hS.winFit H hlo hhi)

/-- `s13_smallGradeFits_of_MSelect'_L` at the lever. -/
theorem s13_smallGradeFits_of_MSelect'_L_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hS : MSelect'_L_gk K Cg δ₀ Λ ρ R M) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      m4SmallGradeFits (doorRowFloorL M) (fun H => 2 * RSanDoorRho ρ H)
        (fun H => 2 * rStrWitness H) H :=
  fun H hlo hhi => s13_smallGradeFits hρ0 hρ1 hlo (hS.winFit H hlo hhi)

/-- **⟦THE SECOND-GENERATION LINEAR SYSTEM AT THE REGIME'S HEADROOM⟧**
(`s13_MSelect'_L_of_headroom`). -/
theorem s13_MSelect'_L_of_headroom {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ))
    (hwf : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ)
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidual H) - Real.log ρ)
        ≤ Real.log (H : ℝ))
    (hhead : s13BlockExp_L M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect'_L Cg δ₀ Λ ρ R M := by
  refine ⟨hM, hbf, hgr, ?_, hwf⟩
  have hfield := R.hPHheadroom
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hnat : 4 * s13BlockFloor_L M ≤ 8 * (4 ^ m) ^ 2 := by
    have h1 : 4 * s13BlockFloor_L M = 2 ^ (s13BlockExp_L M + 2) := by
      rw [s13BlockFloor_L, pow_add]; ring
    rw [h1, s13_headroom_pow_L]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((4 * s13BlockFloor_L M : ℕ) : ℝ) ≤ ((8 * (4 ^ m) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hchain : ((4 * R.ω * s13BlockFloor_L M : ℕ) : ℝ) ≤ (R.x : ℝ) := by
    push_cast at hcast hfield ⊢
    nlinarith [hcast, hfield, hω0]
  exact_mod_cast hchain

/-- `s13_MSelect'_L_of_headroom` at the lever. -/
theorem s13_MSelect'_L_of_headroom_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ))
    (hwf : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ)
          + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
              + 2 * Real.log (strataResidual H) - Real.log ρ)
        ≤ Real.log (H : ℝ))
    (hhead : s13BlockExp_L_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect'_L_gk K Cg δ₀ Λ ρ R M := by
  refine ⟨hM, hbf, hgr, ?_, hwf⟩
  have hfield := R.hPHheadroom
  set m : ℕ := ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ with hm
  have hnat : 4 * s13BlockFloor_L_gk K M ≤ 8 * (4 ^ m) ^ 2 := by
    have h1 : 4 * s13BlockFloor_L_gk K M = 2 ^ (s13BlockExp_L_gk K M + 2) := by
      rw [s13BlockFloor_L_gk, pow_add]; ring
    rw [h1, s13_headroom_pow_L]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((4 * s13BlockFloor_L_gk K M : ℕ) : ℝ) ≤ ((8 * (4 ^ m) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
  have hchain : ((4 * R.ω * s13BlockFloor_L_gk K M : ℕ) : ℝ) ≤ (R.x : ℝ) := by
    push_cast at hcast hfield ⊢
    nlinarith [hcast, hfield, hω0]
  exact_mod_cast hchain

/-- **⟦THE LINEAR SYSTEM AT THE HALF-WINDOW FLOOR⟧** (`s13_MSelect'_L_of_halfWindow`) — the
form the final assembly instantiates: two `M`-lowers, one `M`-upper at the window's lower
endpoint, and the block ceiling off `hPHheadroom`. -/
theorem s13_MSelect'_L_of_halfWindow {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ))
    (hhalf : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log (R.Hlo : ℝ) / 2)
    (hhead : s13BlockExp_L M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect'_L Cg δ₀ Λ ρ R M :=
  s13_MSelect'_L_of_headroom hM hbf hgr (s13_winFit_of_halfWindow_gen hfl hhalf) hhead

/-- `s13_MSelect'_L_of_halfWindow` at the lever. -/
theorem s13_MSelect'_L_of_halfWindow_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M)
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hbf : 24 * Cg / δ₀ ≤ (M : ℝ))
    (hgr : 242 * Λ ≤ ((AdoorL M : ℕ) : ℝ))
    (hhalf : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
      ≤ Real.log (R.Hlo : ℝ) / 2)
    (hhead : s13BlockExp_L_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1) :
    MSelect'_L_gk K Cg δ₀ Λ ρ R M :=
  s13_MSelect'_L_of_headroom_gk K hM hbf hgr (s13_winFit_of_halfWindow_gen hfl hhalf) hhead

/-! ## §6 — ⟦THE REGISTER SUPPLIES THE LINEAR SELECTION SYSTEM⟧

`S15Sel''_L`'s lines ARE `MSelect'_L`'s, so the flat register produced by
`S15SelLinearWide.s15_sel''_L_gk_witness_flat_wide` hands the whole `S13` layer its input. -/

/-- **THE LINEAR REGISTER SUPPLIES THE LINEAR SECOND-GENERATION SYSTEM**
(`MSelect'_L_of_S15Sel''_L`) — `bfloor`/`gRows` verbatim, `blockCeil` off `blk` and the
regime's headroom, `winFit` off `half`. -/
theorem MSelect'_L_of_S15Sel''_L {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)))
    (hsel : S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R M)
    (hgr : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((AdoorL M : ℕ) : ℝ)) :
    MSelect'_L Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
  s13_MSelect'_L_of_halfWindow hsel.hM hfl hsel.bfloor hgr hsel.half (hsel.head hΛ)

/-- `MSelect'_L_of_S15Sel''_L` at the lever. -/
theorem MSelect'_L_gk_of_S15Sel''_L_gk {K : ℕ} {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime} {M : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)))
    (hsel : S15Sel''_L_gk K Cg δ₀ Ct ρ x₀ Mfl R M)
    (hgr : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((AdoorL M : ℕ) : ℝ)) :
    MSelect'_L_gk K Cg δ₀ (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) ρ R M :=
  s13_MSelect'_L_of_halfWindow_gk K hsel.hM hfl hsel.bfloor hgr hsel.half (hsel.head hΛ)

end Salt.MR

end
