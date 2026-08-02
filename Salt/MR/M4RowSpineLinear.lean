/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowAssemblyLinear
import Salt.MR.M4SecondRoad
import Salt.MR.M4ArithPage
import Salt.MR.M4AssemblyPrime
import Salt.MR.M4RowsChiZero
import Salt.MR.M4Spine
import Salt.MR.S11Thread

/-!
# `M4RowSpineLinear` — THE SECOND ROAD / ARITHMETIC PAGE / SPINE at the LINEAR door

⟦LADDER-L, lane G2, layer 3⟧  The last of the three G2 pages: the second road
(`m4_second_road_L`, `_gk`, the tower), the arithmetic page's door exit
(`m4_arith_door_exit_L`), the prime/zero row bases and the spine's endpoint interval.  Same
convention: `AdoorL M = 2^36·M`, `G`-slot untouched, landed body replayed, purely additive.
-/

noncomputable section

open scoped BigOperators
open Complex MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

-- ⟦THE LINEAR ANCHOR'S ELABORATION COST⟧ every twin below reads `AdoorL M = 2^36·M` where its
-- landed original reads `Adoor M = 2^36·(⌊log₂ M⌋ + 1)`, so each `calP`/`calQK` occurrence
-- carries a longer term and the register-against-register instantiations (~40–100 conjuncts,
-- no tactic search anywhere) cost proportionally more `whnf` steps.  The limit is raised
-- file-wide rather than per-declaration because the cost is uniform across the page.
set_option maxHeartbeats 4000000

open G2Scaffold

/-! ## §1 — `M4SecondRoad` -/

/-- `M4BridgeBlock.M4SievedDoorSqBlk` with the count binder weakened to `H ≤ arcDen²·ℓ`
(⟦the q = 1 repair⟧).  Weakening a HYPOTHESIS of the supply makes this predicate STRONGER
than the landed one, and the whole χ-summed chain supplies it. -/
def M4SievedDoorSqBlk2_L (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff_L M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- **THE BLOCKED SOCKET, RE-CUT** (`m4_sievedDoorSq_of_blk2_L`) — `M4BridgeBlock`'s socket
theorem with `hℓcnt` weakened to `H ≤ arcDen²·ℓ`.  The proof is the landed one verbatim: the
count binder is only ever handed to the supply, never used by the socket. -/
theorem m4_sievedDoorSq_of_blk2_L {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ} {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk2_L R M ℓ Bblk) : M4SievedDoorSq_L R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff_L M with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  set L := ℓ H q with hL
  set N := numBlocks H L with hN
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β := by
    intro n
    have h := norm_absWindowSum_sq_le_drift_blocked (B₅ := 12) (H := H) (q := q) (n := n)
      (ℓ := L) hq hH hℓ0 (β := β) (θ := α - β) hd hℓdrift' c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    exact h
  have hmono : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_mono hpt
  have hconst : (∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β
        ∂(logMeasure R.x R.ω))
      = (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * ∫ n, blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_const_mul _ _
  have hsupply := hblk htr H hlo hhi b q hq hqQ hℓ1' hℓH' hℓcnt'
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) := by positivity
  have hstep : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hsupply hfac0)
  have hNL : N * L ≤ 2 * H := by
    have h1 : N * L ≤ H + L := by rw [hN]; exact numBlocks_mul_le H L
    omega
  have hNLR : (N : ℝ) * (L : ℝ) ≤ 2 * (H : ℝ) := by
    have : ((N * L : ℕ) : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hNL
    push_cast at this
    linarith
  have hNL0 : (0 : ℝ) ≤ (N : ℝ) * (L : ℝ) := by positivity
  have hsq : ((N : ℝ) * (L : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
  have hB := hB0 H
  have hpi2 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 := sq_nonneg _
  have hfin : (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
      ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by
    calc (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
        = (1 + 2 * Real.pi) ^ 2 * Bblk H * (((N : ℝ) * (L : ℝ)) ^ 2) := by ring
      _ ≤ (1 + 2 * Real.pi) ^ 2 * Bblk H * (4 * (H : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hpi2 hB)
      _ = 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by ring
  have hgr := hgrade H hlo hhi
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := hstep
    _ ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := hfin
    _ ≤ Braw H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgr (sq_nonneg _)

/-- `M4BridgeBlock.M4BlockMeanSqBlk` at the weakened count binder. -/
def M4BlockMeanSqBlk2_L (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff_L M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- `M4BridgeBlock.m4_cover_assembly_blk` at the weakened count binder — the same
`integral_door_cover_le_clean`, the same door-gate bundle, the same absolute factor `3`. -/
theorem m4_cover_assembly_blk2_L {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk2_L R M k ℓ Bblk) :
    M4SievedDoorSqBlk2_L R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff_L M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

set_option maxHeartbeats 1200000 in
-- the block sum is re-associated over the drift blocks and then over the ladder block, and
-- the stratified bound is instantiated once per drift block; every arithmetic step is
-- `linarith`/`nlinarith` with hints
/-- **⟦S-4a⟧ THE BLOCKED BLOCK MEAN SQUARE, FROM THE χ-SUMMED SUPPLY**
(`m4_blockMeanSqBlk2_of_chiSummed_L`).

Per drift block `m < N` the base is `n + m·ℓ` with `n` in the ladder block
`(X_{i+1}, X_i]`, i.e. a FREE block `(X_{i+1} + m·ℓ, X_i + m·ℓ]` whose fit is the ladder's
own (`X_i + H ≤ 2X_{i+1}` and `ℓ ≤ H`) and whose bottom is at most `2X_{i+1}`
(`M4BridgeBlock.blockBase_le_two_mul`'s arithmetic).  `M4Gauss`'s stratified bound fires
there, and the drift blocks contribute the factor `N`. -/
theorem m4_blockMeanSqBlk2_of_chiSummed_L {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ))
    (hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2)
    (hchi : M4ChiSummedBlockMeanSqN_L R M Bcl) :
    M4BlockMeanSqBlk2_L R M k blockLen
      (fun H => 8 * strataResidual H ^ 2 * Bcl H) := by
  intro H hlo hhi b q hq hqQ hℓ1 hℓH hℓcnt i hik
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harcH := harc H hlo hhi
  have hres0 : (0 : ℝ) ≤ strataResidual H := strataResidual_nonneg harc1
  have hB0 := hBcl0 H
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set L := blockLen H q with hLdef
  set N := numBlocks H L with hN
  have hLarc : 32 * arcDen 12 H ≤ (L : ℝ) := blockLen_arc_floor (R := R) hlo harcH
  have hL16 : 16 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    nlinarith [harcH, sq_nonneg (arcDen 12 H)]
  -- ⟦R-P5, THE x-SCALE LADDER AT THIS RUNG⟧ the base antecedents `M4Gauss` now asks for,
  -- discharged from the ladder's geometric floor (`doorLadder_ge_x_div_four_omega`), its
  -- CEILING (`doorLadder_le_start`, the (α) base cap) and the regime's own wave-II headroom
  -- `8·H₊·log²H₊ ≤ ⌊x/ω⌋` (whose two log factors are `≥ 1` at `H₊ ≥ 4·10⁶`)
  -- — NO new regime field, NO `g`-arm movement
  have hω0N : 0 < 4 * R.ω := by have := R.hω; omega
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have h : 0 < R.ω := by have := R.hω; omega
    exact_mod_cast h
  have hxdiv : R.x / (4 * R.ω) ≤ A := by
    rw [hA]
    exact doorLadder_ge_x_div_four_omega (H := H) R.hω hcount (by omega)
  -- ⟦(α) THE BASE CAP AT THIS RUNG⟧ the ceiling side of the socket's fourth base antecedent
  -- (the (α) base-cap surgery, JYH-granted 2026-07-30): the ladder never exceeds its own
  -- top, so `X_{i+1} ≤ x` and every drift-shifted base is `≤ x + H ≤ 2x`
  have hAtop : A ≤ R.x := by
    rw [hA]
    exact doorLadder_le_start hxH (i + 1)
  have hHhi4 : (4000000 : ℝ) ≤ (R.Hhi : ℝ) := by
    have h : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    exact_mod_cast h
  have hlogHhi : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have hexp : Real.exp 1 ≤ (R.Hhi : ℝ) := by nlinarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  have hxω : 8 * (R.ω : ℝ) * (R.Hhi : ℝ) ≤ (R.x : ℝ) := by
    have hh := R.hheadroom'
    have hcast : (((R.x / R.ω : ℕ)) : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := Nat.cast_div_le
    have hlogsq : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by
      nlinarith [hlogHhi]
    have h1 : 8 * (R.Hhi : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := by
      calc 8 * (R.Hhi : ℝ) = 8 * (R.Hhi : ℝ) * 1 := by ring
        _ ≤ 8 * (R.Hhi : ℝ) * (Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogsq (by linarith)
        _ = 8 * (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by ring
        _ ≤ (((R.x / R.ω : ℕ)) : ℝ) := hh
        _ ≤ (R.x : ℝ) / (R.ω : ℝ) := hcast
    rw [le_div_iff₀ hω0] at h1
    linarith
  have hHhiR : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
  have h8ωH : 8 * R.ω * H ≤ R.x := by
    have h : (8 : ℝ) * (R.ω : ℝ) * (H : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhiR, hω0]
    exact_mod_cast h
  have h2HA : 2 * (H : ℝ) ≤ (A : ℝ) := by
    have hn : 2 * H ≤ A := by
      refine le_trans ((Nat.le_div_iff_mul_le hω0N).mpr ?_) hxdiv
      calc 2 * H * (4 * R.ω) = 8 * R.ω * H := by ring
        _ ≤ R.x := h8ωH
    exact_mod_cast hn
  have hxA : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) := by
    have hdivub : R.x ≤ 4 * R.ω * (R.x / (4 * R.ω)) + 4 * R.ω :=
      le_mul_div_add (A := R.x) (d := 4 * R.ω) hω0N
    have h1 := (Nat.cast_le (α := ℝ)).mpr hdivub
    have h2 : (((R.x / (4 * R.ω) : ℕ)) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hxdiv
    push_cast at h1
    have hbig : 8 * (R.ω : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhi4, hω0]
    nlinarith [h1, h2, hω0, hbig]
  -- ⟦the drift blocks, one free block each⟧
  have hstrat := m4_freeBlockSup_of_chiSummed_L (R := R) (M := M) (Bcl := Bcl) hM hBcl0 hgate
    hchi H hlo hhi L hℓH hℓcnt hLarc hL16 b q hq hqQ
  have hper : ∀ m ∈ Finset.range N,
      ∑ n ∈ Finset.Ioc A B, (subWindowSup (doorSievedCoeff_L M) L (n + m * L)
          ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ 8 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
    intro m hm
    have hmL : m * L ≤ H := mul_le_of_lt_numBlocks (Finset.mem_range.mp hm)
    have hshift : ∑ n ∈ Finset.Ioc A B,
        (subWindowSup (doorSievedCoeff_L M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2
        = ∑ n ∈ Finset.Ioc (A + m * L) (B + m * L),
            (subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ))) ^ 2 :=
      sum_Ioc_shift (fun n => (subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ))) ^ 2)
        A B _
    rw [hshift]
    have hApos' : 0 < A + m * L := by omega
    have hAle : (A : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by
      exact_mod_cast (by omega : A ≤ A + m * L)
    have h2HA' : 2 * (H : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by linarith
    have hxA' : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * ((A + m * L : ℕ) : ℝ) := by
      nlinarith [hxA, hAle, hω0]
    have hcapA' : ((A + m * L : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hnat : A + m * L ≤ 2 * R.x :=
        calc A + m * L ≤ R.x + H := Nat.add_le_add hAtop hmL
          _ ≤ 2 * R.x := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfit' : (B + m * L) + L ≤ 2 * (A + m * L) := by omega
    have h := hstrat (A + m * L) (B + m * L) hApos' h2HA' hxA' hcapA' hfit'
    have hbase : ((A + m * L : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      have hnat : A + m * L ≤ 2 * A := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfac0 : (0 : ℝ) ≤ 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbase hfac0]
  -- ⟦the drift-block sum⟧
  have hswap : ∑ n ∈ Finset.Ioc A B, blockSupSq (doorSievedCoeff_L M) H L n ((b : ℝ) / (q : ℝ))
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ioc A B,
          (subWindowSup (doorSievedCoeff_L M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2 := by
    unfold blockSupSq
    exact Finset.sum_comm
  rw [hswap]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_of_eq ?_
  ring

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER⟧ — `m4_second_road_L`.**

The re-cut of `M4Join.m4_wave_exit_sup_split` (D-1(b)) at the composed
blocked-drift × stratified-Gauss × χ-summed supply.  The conclusion
`¬ logChowla2Fails R.eps R.x R.ω` is BYTE-IDENTICAL to the landed one.

⟦THE GATE CENSUS — FINAL AUDIT (wave ⑤, ⟦T-3e⟧)⟧ — finite, and every gate is classified
**witnessed** (a witness is exhibited in §6), **regime-absorbable** (one-sided `H`-LOWER on
the window range, hence absorbable by the `g`-arm/`U1floor` of the outer register),
**consumer data**, **THE ANALYTIC SLOT**, or **`H`-UPPER** (the sandwich genre — named, with
its binding order):

1. `M4DoorGates_L Cg R M k δ` — UNCHANGED, `hMδ` included (⟦UNTOUCHABLE⟧).  *consumer data.*
2. `1 ≤ M` — *consumer data.*
3. `∀ H, 0 ≤ RSan H`, `∀ H, 0 ≤ RStr H`, `∀ H, 0 ≤ Braw H` — *witnessed*
   (`rSanWitness_nonneg`, `rStrWitness_nonneg`; `Braw` by the consumer's own choice).
4. `∀ j H, j₀ ≤ j → RS j H ≤ RSan H` — the analytic envelope.  *consumer data* (the port's
   deliverable; its ceiling is `m4_second_road_rs_ceiling_L`).
5. `arcDen 12 H ^ 7 ≤ RStr H` — ⟦G1⟧, a FLOOR on witnessed data.  *witnessed*
   (`rStrWitness_G1` at `RStr H := max 1 (arcDen 12 H ^ 7)`).
6. `44·RSan H + 87·arcDen 12 H ≤ (4/3)^{j₀}` — ⟦G2⟧.  *`H`-UPPER, NON-BINDING*: at the
   anti-vacuity envelope it caps `loglog H ≲ 0.024·M·AdoorL M` (`g2_of_j0_floor`), slacker
   than ⟦gate 8⟧ by the factor `0.415·M ≈ 8·10⁶¹` at the honest `M`.  Discharged from the
   `j₀`-floor `j₀ ≳ 22 + 48·loglog H`, which `doorRowFloorL M = M·AdoorL M ≈ 5·10⁶⁷` clears by
   55 orders even at the tower's top.
7. `128·arcDen 12 H ³ ≤ H` — the window floor.  *regime-absorbable* (`H`-LOWER, `H`-only:
   `(log H)^{36} ≪ H`).
8. `arcDen 12 H < calP (AdoorL M) (3072M) 1` — the `M`-RELATIVE dilation gate.  **THE ONE
   BINDING `H`-UPPER**: `loglog H < 0.0578·AdoorL M`.  It is NOT the retired numeral
   `log H ≤ 2^{21845}` (⟦WALL C⟧'s genre, an absolute cap) — it is `M`-relative, and `M` is
   in the register's own witnessed group, chosen AFTER `R`.  **Wave ⑤ tested the
   ⟦A-6 / D0-TEST⟧ `D₀`-truncation against it and the truncation is REFUTED** — see the
   module header, `truncD_admissible_L` and `stratum_sq_le_chiSummed_at_truncD_L` for the exact
   accounting.  The door-anchor ask goes to JYH.
9. the composed drift price (⟦item 4′, RE-CUT⟧):
   `96(1+2π)²·(1 + log arcDen 12 H)²·m4BclGraded j₀ (2·RSan) (2·RStr) H ≤ Braw H`.
   **No `arcDen` power, no `q`, no `q²`** — this is the line the whole road exists to cut.
   *consumer data*; composed with ⟦10⟧ it is the port's ceiling (§6).
10. `M4GradeGateSplit R δ₀ δ Braw k` — the budget line at the head's own constant `δ₀`.
    *consumer data.*
11. `M4ChiSummedFreeRow_L R M RS` — **THE ANALYTIC SLOT**, the socket of S-1.  Inhabited
    (`m4_chiSummedFreeRow_trivial_L`); the port must inhabit it at the §6 ceiling.
    **⟦R-P5, wave P-1⟧ the socket now carries THREE BASE ANTECEDENTS inside its own
    `∀`-prefix** (`2^j ≤ A`, `√H ≤ A`, `R.x ≤ 16·R.ω·arcDen 12 H·A` — see `M4ChiSummed`'s
    header), **and ⟦(α)⟧ a FOURTH, the base cap `A ≤ 2·R.x`** (the (α) base-cap surgery,
    JYH-granted 2026-07-30; it is what makes the door's `DoorFuseFrame_L` hypotheses
    satisfiable — see `M4ChiSummed`'s ⟦THE (α) BASE-CAP SURGERY⟧).  All four only WEAKEN the
    socket, so this register line gains NOTHING: no new conjunct, no new gate, no anchor
    movement, and the port adds ZERO `H`-demand.  The cap is discharged INSIDE this
    theorem's proof, at §3's `m4_blockMeanSqBlk2_of_chiSummed_L`, from `doorLadder_le_start`
    and the regime's own `H + 1 ≤ R.x` — no new hypothesis on the register.

⟦F5 CHECK, RE-RUN — WITH THE x-ANTECEDENT⟧ `R.x` occurs in this register in exactly one
place — `g R.Hhi R.ω ≤ R.x`, an `X`-LOWER supplied by the spine — so there is no `X`-upper
anywhere and no `X`-upper can ride with an `X`-lower in any bundle (grep re-run over
`M4ChiSummed`, `M4Gauss`, `M4SecondRoad`: clean).  **The socket's new x-scale antecedent does
NOT change this**: `R.x ≤ 16·R.ω·arcDen 12 H·A` is a HYPOTHESIS inside ⟦item 11⟧'s Prop, not
a conjunct of this register — it is what the socket's SUPPLIER may assume, discharged here
from the ladder's own geometric floor (`doorLadder_ge_x_div_four_omega`, §3) and the regime's
wave-II headroom, with no new field and no `g`-arm movement.  Read as an `X`-comparison it is
an `X`-UPPER *given to* the supplier, i.e. an `X`-LOWER *on the base* — the same direction as
the `g`-arm, never against it.  ⟦WALL-D/F5's `DoorRowCarriedT0_L` bundle is not reached at
all.⟧  The
`H`-conjuncts are: one LOWER (⟦7⟧, regime-absorbable), two UPPERS (⟦6⟧ slack by 61 orders,
⟦8⟧ binding), and the rest are envelope floors on witnessed data. -/
theorem m4_second_road_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4ChiSummedFreeRow_L R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3 hdgate
    hdrift hgrade hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
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
  have hchi : M4ChiSummedBlockMeanSqN_L R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed_L (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2_L hgates hBblk0 hblk2
  refine hR δ Braw M k hgates hBraw0 hgrade ?_
  refine m4_sievedDoorSq_of_blk2_L (ℓ := blockLen)
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

/-- **THE TRUNCATION CEILING** `D₀ = ⌈2/√(truncBudget δ₀)⌉₊` — ⟦T-1⟧.

`(Cg, δ₀)`-ONLY: no `H`, no `q`, no `X`, no `M`.  At `δ₀ = 2·10⁻⁴⁹` the honest magnitude is
`≈ 1.4·10⁵¹` (`log₂ D₀ ≈ 170`), reproducing ⟦REF-SAND⟧'s `2^163` and ⟦D0-TEST⟧'s SITE-A
`2.9·10⁵⁰` to within the `96(1+2π)²`-vs-`Bblk` bookkeeping.  Against the door's own bottom
block `calP (AdoorL M) (3072M) 1 = 2^{AdoorL M}` with `AdoorL M ≥ 2^18 = 262144` the gate
`D₀ < 2^{AdoorL M}` is free by 261 974 bits — which is exactly why the truncation was worth
testing. -/
def truncD_L (δ₀ : ℝ) : ℕ := ⌈2 / Real.sqrt (truncBudget δ₀)⌉₊

theorem truncD_ge_L (δ₀ : ℝ) : 2 / Real.sqrt (truncBudget δ₀) ≤ ((truncD_L δ₀ : ℕ) : ℝ) :=
  Nat.le_ceil _

/-- **⟦THE SITE-A ADMISSIBILITY⟧** (`truncD_admissible_L`) — for a stratum `d > D₀` on a window
of length `L ≥ D₀`, the GATE-FREE trivial bound `L/d + 1` is under the split budget:

```
      (L/d + 1)²  ≤  truncBudget δ₀ · L² .
```

⟦THE ±1, HONESTLY⟧ `d > D₀ ≥ 2/√B` gives `L/d < √B·L/2`, and `L ≥ D₀ ≥ 2/√B` gives
`1 ≤ √B·L/2` — the two halves that the `2` in `D₀`'s numerator buys, one for the quotient
and one for the `+1`.  This is why the constant is `2/√B` and not `1/√B`.

⟦LENGTH-INVARIANT⟧ `L` enters only through `L ≥ D₀`, so the SAME `D₀` serves the ambient
`H`, the drift block `ℓ`, and the dilated `H/d` — ⟦D0-TEST⟧'s "ABSOLUTE".

⟦AND WHY IT DOES NOT COMPOSE⟧ the stratified recombination (`M4Gauss` §5) does not offer the
stratum the budget `truncBudget δ₀ · L²`; after the weighted Cauchy–Schwarz it offers
`4·B_cl·L²/d²`, which the trivial bound misses by `1/B_cl` at every `d`.  See the module
header. -/
theorem truncD_admissible_L {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {L d : ℕ}
    (hd : truncD_L δ₀ < d) (hL : truncD_L δ₀ ≤ L) :
    ((L : ℝ) / (d : ℝ) + 1) ^ 2 ≤ truncBudget δ₀ * (L : ℝ) ^ 2 := by
  have hB : 0 < truncBudget δ₀ := truncBudget_pos hδ₀
  have hs : 0 < Real.sqrt (truncBudget δ₀) := Real.sqrt_pos.mpr hB
  have hceil := truncD_ge_L δ₀
  have hdR : ((truncD_L δ₀ : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hLR : ((truncD_L δ₀ : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hd2 : 2 / Real.sqrt (truncBudget δ₀) < (d : ℝ) := lt_of_le_of_lt hceil hdR
  have hL2 : 2 / Real.sqrt (truncBudget δ₀) ≤ (L : ℝ) := le_trans hceil hLR
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_le_of_lt (by positivity) hd2
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  -- ⟦the two halves the `2` buys⟧
  have hds : (2 : ℝ) < (d : ℝ) * Real.sqrt (truncBudget δ₀) := by
    rw [div_lt_iff₀ hs] at hd2; linarith
  have hLs : (2 : ℝ) ≤ (L : ℝ) * Real.sqrt (truncBudget δ₀) := by
    rw [div_le_iff₀ hs] at hL2; linarith
  have hquot : (L : ℝ) / (d : ℝ) ≤ (L : ℝ) * Real.sqrt (truncBudget δ₀) / 2 := by
    rw [div_le_iff₀ hd0]
    nlinarith [mul_le_mul_of_nonneg_left hds.le hL0]
  have hkey : (L : ℝ) / (d : ℝ) + 1 ≤ (L : ℝ) * Real.sqrt (truncBudget δ₀) := by linarith
  have hnn : (0 : ℝ) ≤ (L : ℝ) / (d : ℝ) + 1 := by positivity
  have hsq : Real.sqrt (truncBudget δ₀) ^ 2 = truncBudget δ₀ := Real.sq_sqrt hB.le
  calc ((L : ℝ) / (d : ℝ) + 1) ^ 2
      ≤ ((L : ℝ) * Real.sqrt (truncBudget δ₀)) ^ 2 := by nlinarith
    _ = truncBudget δ₀ * (L : ℝ) ^ 2 := by rw [mul_pow, hsq]; ring

/-- **⟦THE ZERO-BYTE INSTANTIATION⟧** (`stratum_sq_le_chiSummed_at_truncD_L`) — ⟦D0-TEST⟧'s
structural fact, recorded in the kernel: the per-stratum bound holds with the door gate read
at `D₀` and NOTHING else moved.  `q` and the ceiling `W` are pure intermediates of the door
side (`M4Residue.door_dilation_gate'` concludes `d < calP …`; neither occurs), so the whole
chain instantiates at `W := truncD_L δ₀` on the strata `d ≤ D₀`.

What no instantiation supplies is the strata `d > D₀`; see the module header. -/
theorem stratum_sq_le_chiSummed_at_truncD_L {M K n q d Lw : ℕ} {δ₀ : ℝ} (hM : 1 ≤ M)
    (hq : 0 < q) (hd0 : 0 < d) (hdq : d ∣ q) (hdD : (d : ℝ) ≤ ((truncD_L δ₀ : ℕ) : ℝ))
    (hgate : ((truncD_L δ₀ : ℕ) : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) (b : ℤ)
    (hlen : dilLen K n d ≤ Lw) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L χ M Lw (n / d)) ^ 2 :=
  stratum_sq_le_chiSummed_L hM hq hd0 hdq hdD hgate b hlen

/-- **⟦THE COMPOSED `RS`-GRADE DEMAND⟧** (`m4_second_road_rs_ceiling_L`) — the number the port
gate quotes.

Composing ⟦item 9⟧ (the drift price) with ⟦item 10⟧ (`M4GradeGateSplit`) and dropping the
`H`-DECAYING half of `m4BclGraded` (its weighted head runs at `(4/3)^{j₀}·H^{-0.415}` and
`(8/3)^{j₀}·H^{-1.415}`, both nonnegative, so dropping them is free), the register's own
gates force

```
      96(1+2π)² · (1 + log arcDen 12 H)² · (108/5) · RSan H  ≤  δ₀² .
```

⟦THE SHAPE OF THE DEMAND — DOES IT DECAY?⟧ **It decays, and only at `loglog` scale.**
`96(1+2π)²·(108/5) ≈ 1.1·10⁵` is absolute; the only `H`-motion is `(1 + log arcDen)² =
(1 + 12·loglog H)²` in the DENOMINATOR of the ceiling.  So the port must deliver

```
      RSan H  ≲  δ₀² / (1.1·10⁵ · (1 + 12 loglog H)²)   ≈  2.5·10⁻¹⁰⁵ / (loglog H)²
```

at `δ₀ = 2·10⁻⁴⁹` (`96(1+2π)²·(108/5) ≈ 1.1·10⁵`, `δ₀² = 4·10⁻⁹⁸`)

— a CONSTANT times `(loglog H)^{-2}`, which is INSIDE ⟦D1-SCOPE⟧'s residual law (bounded
powers of `loglog H` are free; only positive powers of `log H` are fatal), and far weaker
than KMT's own `ε ≥ (log H)^{-1/200}`.  **No power of `arcDen` and no `q` appears** — that
is the whole content of the second road.  The `RStr` half is untouched by this ceiling: its
coefficient carries `H^{-0.415}` and vanishes against any envelope once `H ≳ 2^{j₀}` (the
`M4Maximal.m4SmallGradeFits` threshold), which is why ⟦G1⟧ can be witnessed at `arcDen⁷`
while ⟦G2⟧'s analytic half cannot. -/
theorem m4_second_road_rs_ceiling_L {R : ChowlaRegime} {δ₀ δ : ℝ} {RSan RStr Braw : ℕ → ℝ}
    {j₀ k : ℕ} (hδ : 0 ≤ δ)
    (hRSan0 : ∀ H : ℕ, 0 ≤ RSan H) (hRStr0 : ∀ H : ℕ, 0 ≤ RStr H)
    (hdrift : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H ≤ Braw H)
    (hgrade : M4GradeGateSplit R δ₀ δ Braw k) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSan H) ≤ δ₀ ^ 2 := by
  intro H hlo hhi
  have hpi : (0 : ℝ) < 1 + 2 * Real.pi := by have := Real.pi_pos; linarith
  have hBcl0 : 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  have hd := hdrift H hlo hhi
  have hfac0 : (0 : ℝ) ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 := by positivity
  have hBraw0 : 0 ≤ Braw H := le_trans (mul_nonneg hfac0 hBcl0) hd
  -- ⟦item 10 caps the budget by `δ₀²`⟧
  have hg := hgrade H hlo hhi
  have htail : (0 : ℝ) ≤ 4 * 2 ^ k / (R.x : ℝ) := by positivity
  have hsqrt : Real.sqrt (Braw H) ≤ δ₀ := by linarith
  have hsq : Real.sqrt (Braw H) ^ 2 = Braw H := Real.sq_sqrt hBraw0
  have hBrawδ : Braw H ≤ δ₀ ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.sqrt (Braw H) := Real.sqrt_nonneg _
    nlinarith
  -- ⟦the graded price dominates its analytic half⟧
  have hhead : (0 : ℝ) ≤ (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ / (H : ℝ)
      + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2)
        * (2 * RStr H) := by
    have := hRStr0 H
    positivity
  have hlow : 108 / 5 * RSan H
      ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    unfold m4BclGraded m4Cmax
    linarith
  calc 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSan H)
      ≤ 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
          * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
        mul_le_mul_of_nonneg_left hlow hfac0
    _ ≤ Braw H := hd
    _ ≤ δ₀ ^ 2 := hBrawδ

/-- `M4SievedDoorSqBlk2_L` (:291), at the lever. -/
def M4SievedDoorSqBlk2_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- `m4_sievedDoorSq_of_blk2_L` (:303), at the lever. -/
theorem m4_sievedDoorSq_of_blk2_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ}
    {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk2_L_gk K R M ℓ Bblk) : M4SievedDoorSq_L_gk K R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff_L_gk K M with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  set L := ℓ H q with hL
  set N := numBlocks H L with hN
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β := by
    intro n
    have h := norm_absWindowSum_sq_le_drift_blocked (B₅ := 12) (H := H) (q := q) (n := n)
      (ℓ := L) hq hH hℓ0 (β := β) (θ := α - β) hd hℓdrift' c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    exact h
  have hmono : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_mono hpt
  have hconst : (∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β
        ∂(logMeasure R.x R.ω))
      = (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * ∫ n, blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_const_mul _ _
  have hsupply := hblk htr H hlo hhi b q hq hqQ hℓ1' hℓH' hℓcnt'
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) := by positivity
  have hstep : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hsupply hfac0)
  have hNL : N * L ≤ 2 * H := by
    have h1 : N * L ≤ H + L := by rw [hN]; exact numBlocks_mul_le H L
    omega
  have hNLR : (N : ℝ) * (L : ℝ) ≤ 2 * (H : ℝ) := by
    have : ((N * L : ℕ) : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hNL
    push_cast at this
    linarith
  have hNL0 : (0 : ℝ) ≤ (N : ℝ) * (L : ℝ) := by positivity
  have hsq : ((N : ℝ) * (L : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
  have hB := hB0 H
  have hpi2 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 := sq_nonneg _
  have hfin : (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
      ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by
    calc (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
        = (1 + 2 * Real.pi) ^ 2 * Bblk H * (((N : ℝ) * (L : ℝ)) ^ 2) := by ring
      _ ≤ (1 + 2 * Real.pi) ^ 2 * Bblk H * (4 * (H : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hpi2 hB)
      _ = 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by ring
  have hgr := hgrade H hlo hhi
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := hstep
    _ ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := hfin
    _ ≤ Braw H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgr (sq_nonneg _)

/-- `M4BlockMeanSqBlk2_L` (:372), at the lever. -/
def M4BlockMeanSqBlk2_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ arcDen 12 H ^ 2 * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- `m4_cover_assembly_blk2_L` (:383), at the lever. -/
theorem m4_cover_assembly_blk2_L_gk (K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L_gk K Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk2_L_gk K R M k ℓ Bblk) :
    M4SievedDoorSqBlk2_L_gk K R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

set_option maxHeartbeats 1200000 in
-- the block sum is re-associated over the drift blocks and then over the ladder block, and
-- the stratified bound is instantiated once per drift block; every arithmetic step is
-- `linarith`/`nlinarith` with hints
/-- `m4_blockMeanSqBlk2_of_chiSummed_L` (:485), at the lever. -/
theorem m4_blockMeanSqBlk2_of_chiSummed_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 2 ≤ (H : ℝ))
    (hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2)
    (hchi : M4ChiSummedBlockMeanSqN_L_gk K R M Bcl) :
    M4BlockMeanSqBlk2_L_gk K R M k blockLen
      (fun H => 8 * strataResidual H ^ 2 * Bcl H) := by
  intro H hlo hhi b q hq hqQ hℓ1 hℓH hℓcnt i hik
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harcH := harc H hlo hhi
  have hres0 : (0 : ℝ) ≤ strataResidual H := strataResidual_nonneg harc1
  have hB0 := hBcl0 H
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set L := blockLen H q with hLdef
  set N := numBlocks H L with hN
  have hLarc : 32 * arcDen 12 H ≤ (L : ℝ) := blockLen_arc_floor (R := R) hlo harcH
  have hL16 : 16 * arcDen 12 H ^ 2 ≤ (H : ℝ) := by
    nlinarith [harcH, sq_nonneg (arcDen 12 H)]
  -- ⟦R-P5, THE x-SCALE LADDER AT THIS RUNG⟧ the base antecedents `M4Gauss` now asks for,
  -- discharged from the ladder's geometric floor (`doorLadder_ge_x_div_four_omega`), its
  -- CEILING (`doorLadder_le_start`, the (α) base cap) and the regime's own wave-II headroom
  -- `8·H₊·log²H₊ ≤ ⌊x/ω⌋` (whose two log factors are `≥ 1` at `H₊ ≥ 4·10⁶`)
  -- — NO new regime field, NO `g`-arm movement
  have hω0N : 0 < 4 * R.ω := by have := R.hω; omega
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have h : 0 < R.ω := by have := R.hω; omega
    exact_mod_cast h
  have hxdiv : R.x / (4 * R.ω) ≤ A := by
    rw [hA]
    exact doorLadder_ge_x_div_four_omega (H := H) R.hω hcount (by omega)
  -- ⟦(α) THE BASE CAP AT THIS RUNG⟧ the ceiling side of the socket's fourth base antecedent
  -- (the (α) base-cap surgery, JYH-granted 2026-07-30): the ladder never exceeds its own
  -- top, so `X_{i+1} ≤ x` and every drift-shifted base is `≤ x + H ≤ 2x`
  have hAtop : A ≤ R.x := by
    rw [hA]
    exact doorLadder_le_start hxH (i + 1)
  have hHhi4 : (4000000 : ℝ) ≤ (R.Hhi : ℝ) := by
    have h : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    exact_mod_cast h
  have hlogHhi : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have hexp : Real.exp 1 ≤ (R.Hhi : ℝ) := by nlinarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by linarith)).mpr hexp
  have hxω : 8 * (R.ω : ℝ) * (R.Hhi : ℝ) ≤ (R.x : ℝ) := by
    have hh := R.hheadroom'
    have hcast : (((R.x / R.ω : ℕ)) : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := Nat.cast_div_le
    have hlogsq : (1 : ℝ) ≤ Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by
      nlinarith [hlogHhi]
    have h1 : 8 * (R.Hhi : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := by
      calc 8 * (R.Hhi : ℝ) = 8 * (R.Hhi : ℝ) * 1 := by ring
        _ ≤ 8 * (R.Hhi : ℝ) * (Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogsq (by linarith)
        _ = 8 * (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) * Real.log (R.Hhi : ℝ) := by ring
        _ ≤ (((R.x / R.ω : ℕ)) : ℝ) := hh
        _ ≤ (R.x : ℝ) / (R.ω : ℝ) := hcast
    rw [le_div_iff₀ hω0] at h1
    linarith
  have hHhiR : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
  have h8ωH : 8 * R.ω * H ≤ R.x := by
    have h : (8 : ℝ) * (R.ω : ℝ) * (H : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhiR, hω0]
    exact_mod_cast h
  have h2HA : 2 * (H : ℝ) ≤ (A : ℝ) := by
    have hn : 2 * H ≤ A := by
      refine le_trans ((Nat.le_div_iff_mul_le hω0N).mpr ?_) hxdiv
      calc 2 * H * (4 * R.ω) = 8 * R.ω * H := by ring
        _ ≤ R.x := h8ωH
    exact_mod_cast hn
  have hxA : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) := by
    have hdivub : R.x ≤ 4 * R.ω * (R.x / (4 * R.ω)) + 4 * R.ω :=
      le_mul_div_add (A := R.x) (d := 4 * R.ω) hω0N
    have h1 := (Nat.cast_le (α := ℝ)).mpr hdivub
    have h2 : (((R.x / (4 * R.ω) : ℕ)) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hxdiv
    push_cast at h1
    have hbig : 8 * (R.ω : ℝ) ≤ (R.x : ℝ) := by nlinarith [hxω, hHhi4, hω0]
    nlinarith [h1, h2, hω0, hbig]
  -- ⟦the drift blocks, one free block each⟧
  have hstrat := m4_freeBlockSup_of_chiSummed_L_gk K (R := R) (M := M) (Bcl := Bcl) hM hBcl0 hgate
    hchi H hlo hhi L hℓH hℓcnt hLarc hL16 b q hq hqQ
  have hper : ∀ m ∈ Finset.range N,
      ∑ n ∈ Finset.Ioc A B, (subWindowSup (doorSievedCoeff_L_gk K M) L (n + m * L)
          ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ 8 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
    intro m hm
    have hmL : m * L ≤ H := mul_le_of_lt_numBlocks (Finset.mem_range.mp hm)
    have hshift : ∑ n ∈ Finset.Ioc A B,
        (subWindowSup (doorSievedCoeff_L_gk K M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2
        = ∑ n ∈ Finset.Ioc (A + m * L) (B + m * L),
            (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2 :=
      sum_Ioc_shift (fun n => (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2)
        A B _
    rw [hshift]
    have hApos' : 0 < A + m * L := by omega
    have hAle : (A : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by
      exact_mod_cast (by omega : A ≤ A + m * L)
    have h2HA' : 2 * (H : ℝ) ≤ ((A + m * L : ℕ) : ℝ) := by linarith
    have hxA' : (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * ((A + m * L : ℕ) : ℝ) := by
      nlinarith [hxA, hAle, hω0]
    have hcapA' : ((A + m * L : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hnat : A + m * L ≤ 2 * R.x :=
        calc A + m * L ≤ R.x + H := Nat.add_le_add hAtop hmL
          _ ≤ 2 * R.x := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfit' : (B + m * L) + L ≤ 2 * (A + m * L) := by omega
    have h := hstrat (A + m * L) (B + m * L) hApos' h2HA' hxA' hcapA' hfit'
    have hbase : ((A + m * L : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      have hnat : A + m * L ≤ 2 * A := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfac0 : (0 : ℝ) ≤ 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbase hfac0]
  -- ⟦the drift-block sum⟧
  have hswap : ∑ n ∈ Finset.Ioc A B, blockSupSq (doorSievedCoeff_L_gk K M) H L n ((b : ℝ) / (q : ℝ))
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ioc A B,
          (subWindowSup (doorSievedCoeff_L_gk K M) L (n + m * L) ((b : ℝ) / (q : ℝ))) ^ 2 := by
    unfold blockSupSq
    exact Finset.sum_comm
  rw [hswap]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_of_eq ?_
  ring

/-- `m4_second_road_L` (:683), at the lever. -/
theorem m4_second_road_L_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
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
            M4GradeGateSplit R δ₀ δ Braw k →
            M4ChiSummedFreeRow_L_gk K R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split_L_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3 hdgate
    hdrift hgrade hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
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
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed_L_gk K (k := k) hM hBcl0 hdgate harc
    hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2_L_gk K hgates hBblk0 hblk2
  refine hR δ Braw M k hgates hBraw0 hgrade ?_
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

/-- `stratum_sq_le_chiSummed_at_truncD_L` (:848), at the lever. -/
theorem stratum_sq_le_chiSummed_at_truncD_L_gk (K : ℕ) {M Kw n q d Lw : ℕ} {δ₀ : ℝ} (hM : 1 ≤ M)
    (hq : 0 < q) (hd0 : 0 < d) (hdq : d ∣ q) (hdD : (d : ℝ) ≤ ((truncD_L δ₀ : ℕ) : ℝ))
    (hgate : ((truncD_L δ₀ : ℕ) : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) (b : ℤ)
    (hlen : dilLen Kw n d ≤ Lw) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L_gk K χ M Lw (n / d)) ^ 2 :=
  stratum_sq_le_chiSummed_L_gk K hM hq hd0 hdq hdD hgate b hlen
/-! ## §2 — `M4ArithPage` -/

theorem calP_door_one_L (M : ℕ) : calP (AdoorL M) (3072 * M) 1 = 2 ^ AdoorL M := by
  rw [calP, calE_one]

theorem calQK_door_one_L (M : ℕ) : calQK (AdoorL M) (3072 * M) M 1 = 2 ^ (M * AdoorL M) := by
  rw [calQK, calE_one]
  norm_num

/-- **⟦THE GATED SOCKET⟧** (`m4_chiSummedFreeRowBig_of_doorGradeGated_L`) — `M4Assembly`'s
socket wire with `hgrade` and `henv` both taken only where the socket actually applies them.
The proof is `M4Assembly.m4_chiSummedFreeRowBig_of_doorGrade`'s, with `SocketBaseL` assembled
from the socket's binders instead of re-quantified. -/
theorem m4_chiSummedFreeRowBig_of_doorGradeGated_L {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    {C₁ M₀ : ℕ → ℝ}
    {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
        ≤ (q.totient : ℝ)
            * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s)) (M₀ (A + s)))
    (henv : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) := a2DoorGrade_L_nonneg hM (log_natCast_nonneg' (A + s)) hh0
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans (hgrade H L q j A s hb) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H L q j A s hb

/-- **⟦GATE 4, READ AT THE DOOR'S ENVELOPE⟧** (`m4_arith_gate4_L`) — `m4_second_road_L`'s
⟦gate 4⟧ `∀ j H, j₀ ≤ j → RS j H ≤ RSan H` at `j₀ := doorRowFloorL M`, `RSan := RSanDoor`.
Above the floor the spliced grade IS `RSanDoor H`; the `else` branch is never read. -/
theorem m4_arith_gate4_L (M : ℕ) :
    ∀ j H : ℕ, doorRowFloorL M ≤ j →
      m4ChiRowGraded_L M (fun _ H => RSanDoor H) j H ≤ RSanDoor H :=
  m4ChiRowGraded_an_L (fun _ _ _ => le_rfl)

/-- **`P₁` AT THE LEVER IS THE SAME NUMERAL** — `calP_door_one_L` re-read at `s13GK K M`. -/
theorem calP_door_one_at_lever_L (K M : ℕ) : calP (AdoorL M) (s13GK K M) 1 = 2 ^ AdoorL M := by
  rw [calP, calE_gk_one]

/-- **`Q₁` AT THE LEVER IS THE SAME NUMERAL** — `calQK_door_one_L` re-read at `s13GK K M`. -/
theorem calQK_door_one_at_lever_L (K M : ℕ) :
    calQK (AdoorL M) (s13GK K M) M 1 = 2 ^ (M * AdoorL M) := by
  rw [calQK, calE_gk_one]
  norm_num

/-- **⟦THE GATED SOCKET⟧ AT THE LEVER** — `m4_chiSummedFreeRowBig_of_doorGradeGated_L`
(:662). -/
theorem m4_chiSummedFreeRowBig_of_doorGradeGated_L_gk (Klev : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M)
    {C₁ M₀ : ℕ → ℝ}
    {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk Klev χ M j (A + s)
        ≤ (q.totient : ℝ)
            * a2DoorGrade_L_gk Klev M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
                (M₀ (A + s)))
    (henv : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_L_gk Klev M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig_L_gk Klev R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade_L_gk Klev M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) := a2DoorGrade_nonneg_L_gk Klev hM (log_natCast_nonneg' (A + s)) hh0
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans (hgrade H L q j A s hb) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H L q j A s hb
/-! ## §3 — `M4AssemblyPrime` -/

/-- **THE FUSE FRAME AT ONE BASE, POOLED AND RE-PRICED** (`DoorFuseFrame_pool'_L`) —
`M4AssemblyPool.DoorFuseFrame_pool` with its `gRows` field at `ThmA2.a2RowsSum'`.

Ten fields, nine of them byte-identical to `DoorFuseFrame_pool_L`'s.  The one that moves is
`gRows`, and it moves to the WEAKER demand (`a2RowsSum'_L ≤ a2RowsSum_L`): its `p²` slot is now
the `X_d`-FREE `24·(1/𝒫₁ + 1/𝒫₂)`, so the field reads no `log₂(2X_d)` at all. -/
structure DoorFuseFrame_pool'_L (M Xd j : ℕ) (Cs Ccc ε π₀ : ℝ) : Prop where
  /-- `e ≤ X_d` — the frozen interface's lower scale pin. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j` — the AS-2 MVT guard (NOT `3`). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame `2^j ≤ X_d·(log X_d)^{−1/5}`. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- `TannGate X_d (2X_d/2^j)` — the annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`, AT THE POOL. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀
  /-- **THE SECOND GRADING GATE, AT THE POOL AND AT ⟦R1⟧'s ROW SUM** — the `p²` slot is the
  `X_d`-FREE constant `24/𝒫ⱼ`, so nothing in this field grows with the base. -/
  gRows : 5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀
  /-- **THE `𝒰`-LEG, POOLED** — `ε` carries no exponent-room constraint. -/
  eps_pool : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀
  /-- **THE BAND ABSORPTION, POOLED**. -/
  band_pool : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀

/-- **⟦THE SLOT FUSE AT THE JOIN⟧** (`m4_chiFreeRowSq_sum_at_door_pool'_L`).
`ThmA2Prime.thm_a2'_of_rows_chiSummed_pool'` instantiated at the door datum

  `N := 2X_d`,  `X := X_d`,  `h := 2^j`,  `a χ := winCutH X_d (doorChiCoeff_L χ M)`,

whose right-hand side collapses to `φ(q)·a2DoorGrade_pool_L M X_d 2^j C₁ M₀ π₀` — the SAME
grade `M4AssemblyPool.m4_chiFreeRowSq_sum_at_door_pool` lands in, because the pooled grade
mentions no row sum.

⟦THE GATE LIST AGAINST THE R2 SIBLING⟧ every gate is verbatim except two, both weaker:
`hrowsSum` reads `a2Mrow'_L` and `hgRows` reads `a2RowsSum'_L`.  `0 ≤ π₀` is still derived from
`hgBand` and `hX3`, not assumed. -/
theorem m4_chiFreeRowSq_sum_at_door_pool'_L {q : ℕ} [NeZero q] {M Xd j : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)) (hX3 : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ))
    (hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhX : ((2 ^ j : ℕ) : ℝ)
      ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ)))
    (hTann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
    (hceil : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ ((Xd : ℕ) : ℝ) →
      TannGate ((Xd : ℕ) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
          * (∫ t in seamAnn ((Xd : ℕ) : ℝ) (2 * T),
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_L χ M)) t‖ ^ 2)
        ≤ a2Mrow'_L Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j Xd
      ≤ (q.totient : ℝ)
          * a2DoorGrade_pool_L M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
  have hpool : (0 : ℝ) ≤ π₀ := by
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) hX3
      have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
      Real.rpow_pos_of_pos hL0 _
    linarith
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_pool'_L (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_L χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (π₀ := π₀) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_L χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_L χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    hpool (fun _ => hgP1) (fun _ => hgRows) (fun _ => hgU) hgBand
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_pool_L
  ring

/-- **⟦THE ASSEMBLY, AT THE R1×R2 JOIN⟧** (`m4_chiSummedFreeRow_of_doorAssembly_pool'_L`) —
**THE EXIT**: ⟦item 11⟧ of `m4_second_road_L` from the named gates alone, at the joined grade.

THE COMPLETE GATE LIST: `hM`; `hframe` — `DoorFuseFrame_pool'_L` (TEN fields) at every base
the socket reaches, with the base-indexed pool `π₀`; `hrows` — the row family at
`ThmA2Prime.a2Mrow'` (supplied by `A3Middle.a2Rows_of_capfree3_end'`, and by nothing else);
`hband` — `M4Assembly`'s own band supplier, BYTE FOR BYTE unchanged; `hpool` and `henv` —
verbatim from the R2 sibling, since the pooled grade never mentions a row sum.

⟦WHAT THIS DEMONSTRATES⟧ the joined chain feeds the frames: `a2Rows_of_capfree3_end'_L` lands
in `a2Mrow'_L`, `a2Mrow'_L` is what `thm_a2'_of_rows_pool'_L` consumes, and the pool is what the
door's constant target wants.  Every `X_d`-decaying right-hand side inside the frame is
gone; what remains are base-LOWER demands (see this module's μ-ledger). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool'_L {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool'_L M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_pool_L hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool ?_
    henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool'_L hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool

/-- `DoorFuseFrame_pool'_L` (:75), at the lever.  Two of the ten fields move: `gP1`'s `𝒫₁` is
written at the levered base and `gRows` reads `ThmA2Prime.a2RowsSum'_gk`. -/
structure DoorFuseFrame_pool'_L_gk (K : ℕ) (M Xd j : ℕ) (Cs Ccc ε π₀ : ℝ) : Prop where
  /-- `e ≤ X_d` — the frozen interface's lower scale pin. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j` — the AS-2 MVT guard (NOT `3`). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame `2^j ≤ X_d·(log X_d)^{−1/5}`. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- `TannGate X_d (2X_d/2^j)` — the annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`, AT THE POOL AND THE LEVER. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀
  /-- **THE SECOND GRADING GATE, AT THE POOL AND AT ⟦R1⟧'s LEVERED ROW SUM** — the `p²` slot
  is the `X_d`-FREE constant `24/𝒫ⱼ`, so nothing in this field grows with the base. -/
  gRows : 5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀
  /-- **THE `𝒰`-LEG, POOLED** — `ε` carries no exponent-room constraint. -/
  eps_pool : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀
  /-- **THE BAND ABSORPTION, POOLED**. -/
  band_pool : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀

/-- `m4_chiFreeRowSq_sum_at_door_pool'_L` (:151), at the lever. -/
theorem m4_chiFreeRowSq_sum_at_door_pool'_L_gk (K : ℕ) {q : ℕ} [NeZero q] {M Xd j : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)) (hX3 : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ))
    (hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhX : ((2 ^ j : ℕ) : ℝ)
      ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ)))
    (hTann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
    (hceil : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ ((Xd : ℕ) : ℝ) →
      TannGate ((Xd : ℕ) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
          * (∫ t in seamAnn ((Xd : ℕ) : ℝ) (2 * T),
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
        ≤ a2Mrow'_L_gk K Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j Xd
      ≤ (q.totient : ℝ)
          * a2DoorGrade_pool_L_gk K M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
  have hpool : (0 : ℝ) ≤ π₀ := by
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by
      have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) hX3
      have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hrp : (0 : ℝ) < (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) :=
      Real.rpow_pos_of_pos hL0 _
    linarith
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_pool'_L_gk K (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_L_gk K χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (π₀ := π₀) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_L_gk K χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    hpool (fun _ => hgP1) (fun _ => hgRows) (fun _ => hgU) hgBand
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_pool_L_gk
  ring

/-- `m4_chiSummedFreeRow_of_doorAssembly_pool'_L` (:218), at the lever — **THE EXIT**, levered. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorFuseFrame_pool'_L_gk K M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)) (π₀ (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_L_gk K (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (hpool : ∀ A : ℕ, 0 ≤ π₀ A)
    (henv : ∀ H j A s : ℕ, doorRowFloorL M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorGrade_pool_L_gk K hM (C₁ := C₁) (M₀ := M₀) (π₀ := π₀) hpool
    ?_ henv
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb : SocketBaseL R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hb
  exact m4_chiFreeRowSq_sum_at_door_pool'_L_gk K hM hF.X_exp hF.X_three hF.h_four hF.h_window
    hF.tann hF.ceil5 (hrows H L q j A s hb) (hband H L q j A s hb) hF.gP1 hF.gRows hF.eps_pool
    hF.band_pool
/-! ## §4 — `M4RowsChiZero` -/

/-- **⟦THE DOOR DATUM IS BLOCK-LIVE, AT EVERY DOOR LEVEL⟧** (`blockLive_winCutH_doorCoeffU_L`) —
the scoper's ⟦PROBE 2⟧, factored.  `doorCoeffU_L M = 1_𝒮·λ` at the family
`(calP (AdoorL M) (3072M), calQK (AdoorL M) (3072M) M)` with `J = 2`; `MemS` gives a prime
factor in the block at each `i ∈ [1, 2]`, and the half-open cut cannot create support. -/
theorem blockLive_winCutH_doorCoeffU_L (M Xd : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 2) :
    BlockLive (calP (AdoorL M) (3072 * M) i) (calQK (AdoorL M) (3072 * M) M i)
      (winCutH Xd (doorCoeffU_L M)) :=
  blockLive_winCutH (blockLive_memSCoeff _ _ 2 liouvilleC hi)

/-- **⟦THE `a2Mrow_L`-GENRE ROW FAMILY AT THE DOOR, DENSITY-FREE⟧**
(`m4_hrowsSum_chi_door_zero_L`).  §5 at the door family and the vacuous ball, landed inside the
FROZEN interface's row constant `ThmA2.a2Mrow` at a FREE `Cp ≥ 0`.  The datum is pinned to
`winCutH X_d (doorCoeffU_L M)`, which is what makes the block-liveness gate free. -/
theorem m4_hrowsSum_chi_door_zero_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (3072 * M) j) (calQK (AdoorL M) (3072 * M) M j)
            (winCutH Xd (doorCoeffU_L M)) (bfam j) c) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (3072 * M))
                      (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L M))) t‖ ^ 2)
            ≤ a2Mrow_L Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_L M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_L M)) bfam ha1 hb1 hc1 N Xd
    (AdoorL M) (3072 * M) M 2 (H1doorL M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_L M Xd hM hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_L M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow_L hM hXd1 hCp

/-- **⟦THE SLOT, MET, DENSITY-FREE⟧** (`m4_hrowsSlot_at_door_zero_L`).  The statement below is
`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s `hrows` binder VERBATIM at `Cs ≡ Ct`,
`Ccc ≡ Cp` with `Cp` a free nonnegative real — in particular at `Cp := 0`.  Supplied by the
door page through the datum bridge `M4Assembly.chiBarCoeff_doorRowDatum`. -/
theorem m4_hrowsSlot_at_door_zero_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowZeroBase_L M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ a2Mrow_L Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L] using hslot

/-- **⟦A4 — ITEM 11 AT A FREE DENSITY CONSTANT⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_zero_L`).  `M4RowsChiEnd`'s `_end` assembly with `Cp`
free: `M4ChiSummed.M4ChiSummedFreeRow` at the door grade from `hM`, `hb1`, `hc1`, `hframe`,
`hbase` (`DoorRowZeroBase_L` — `dom`-free), `hcap`, `hband`, `henv`.

⟦THE ONE THING THAT MOVES AGAINST `m4_chiSummedFreeRow_of_doorAssembly_end_L`⟧ the density
constant is quantified `∀ Cp ≥ 0` instead of `∃ Cp > 0`, so a consumer may take `Cp := 0`;
and `hbase` asks six fields where the `_end` form asks seven. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_zero_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowZeroBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband henv

/-- ⟦PROBE 2⟧ AT THE G-LEVER (`blockLive_winCutH_doorCoeffU_L_gk`). -/
theorem blockLive_winCutH_doorCoeffU_L_gk (K : ℕ) (M Xd : ℕ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 2) :
    BlockLive (calP (AdoorL M) (s13GK K M) i) (calQK (AdoorL M) (s13GK K M) M i)
      (winCutH Xd (doorCoeffU_L_gk K M)) :=
  blockLive_winCutH (blockLive_memSCoeff _ _ 2 liouvilleC hi)

/-- **THE PER-BASE GATE BUNDLE, DENSITY-FREE, AT THE G-LEVER**
(`DoorRowZeroBase_L_gk`).  SIX fields, names UNCHANGED and in this order: `Q2_le`, `coefWS`,
`reg`, `big`, `h_four`, `Q1_le_h`.  `reg` is byte-identical to `S13CapGate_L`'s `Q2_reg` at the
levered symbol — that is the propagator the whole S13 supply reads. -/
structure DoorRowZeroBase_L_gk (K : ℕ) (M Xd j : ℕ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) : Prop where
  /-- The door's cutoff `Q₂ ≤ X_d`. -/
  Q2_le : calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law, level by level. -/
  coefWS : ∀ i ∈ Finset.Icc 1 2,
    SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) i) (calQK (AdoorL M) (s13GK K M) M i)
      (winCutH Xd (doorCoeffU_L_gk K M)) (bU i) cU
  /-- (R1) `log Q₂ ≤ √(log X_d)`. -/
  reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R2) `100 ≤ √(log X_d)`. -/
  big : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- The weighting frame's floor `4 ≤ 2^j`. -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- The weighting frame's `Q₁ ≤ h` at `h = 2^j`. -/
  Q1_le_h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)

/-- **⟦THE `a2Mrow_L`-GENRE ROW FAMILY AT THE DOOR, DENSITY-FREE⟧ AT THE
G-LEVER** (`m4_hrowsSum_chi_door_zero_L_gk`). -/
theorem m4_hrowsSum_chi_door_zero_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            (winCutH Xd (doorCoeffU_L_gk K M)) (bfam j) c) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ a2Mrow_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_L_gk K M)) bfam ha1 hb1 hc1 N Xd
    (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_L_gk K M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow_L_gk K hM hXd1 hCp

/-- **⟦THE SLOT, MET, DENSITY-FREE⟧ AT THE G-LEVER**
(`m4_hrowsSlot_at_door_zero_L_gk`). -/
theorem m4_hrowsSlot_at_door_zero_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

/-- **⟦ITEM 11⟧ AT THE ASSEMBLY WIRE, DENSITY-FREE, AT THE LEVER** —
`m4_chiSummedFreeRow_of_doorAssembly_zero_L` (:868). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_zero_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_L_gk K M (A + s) j Ct Cp (ε (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband henv
/-! ## §5 — `M4Spine` -/

set_option maxHeartbeats 1600000 in
-- the register is a 24-fold existential over a ~98-conjunct chain; the projection is a
-- straight-line search down the right spine of the `∧`-tree, no tactic search
/-- **THE ENDPOINT PROJECTION** (`doorRowCarriedT0_endpoint_L`).  Every instance of the
per-instance register asserts that the door's sieved χ-twisted datum VANISHES at the block
bottom `X_d`.  Its only discharge route is `X_d ∉ 𝒮`
(`M4Band.memSCoeff_eq_zero_of_not_memS`). -/
theorem doorRowCarriedT0_endpoint_L {Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ}
    {q : ℕ} {χ : DirichletCharacter ℂ q} {M Xd j : ℕ} {B : ℝ}
    (hreg : DoorRowCarriedT0_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B) :
    doorChiCoeff_L χ M Xd = 0 := by
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, hwin, δ', V, VJ, L, Cb, kmin, Ymax, εw, Xw, cqS,
    cgS, cW, SW, Rbar0, Dmask, hc⟩ := hreg
  repeat (first | exact hc.1 | replace hc := hc.2)

/-- **⟦WALL B⟧** (`m4_register_forces_endpoint_interval_L`).  ⟦THE FINAL REGISTER⟧'s per-instance
line — gate 11, at the `d = 1` instance — forces the sieved χ-twisted datum to vanish on a FULL
interval of `H + 2` consecutive integers at the bottom of every ladder block, at every window
length in range.  With `q = 1` (admissible: `1 ≤ arcDen 12 H`) there is no character zero
available, so the demand is `X_d ∉ 𝒮` for every one of those `H + 2` integers — while `𝒮` is
the Ramaré sieve, which keeps almost every integer.  The `s`-freedom `M4DoorClose`'s ⟦ENDPOINT
CONVENTION⟧ points at was spent by `M4Maximal.M4ChiDyadicRowMeanSq`'s own `∀ s`. -/
theorem m4_register_forces_endpoint_interval_L
    {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ}
    (hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
        doorRowFloorL M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
          ∀ s ≤ H / d + 1,
            DoorRowCarriedT0_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
              (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H))
    {H : ℕ} (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) {q : ℕ} (hq : 0 < q)
    (hqQ : (q : ℝ) ≤ arcDen 12 H) (χ : DirichletCharacter ℂ q) {i : ℕ} (hik : i < k)
    {j : ℕ} (hjL : j ≤ Nat.log 2 H) (hj0 : doorRowFloorL M ≤ j) :
    ∀ s ≤ H + 1, doorChiCoeff_L χ M (doorLadder R.x H (i + 1) - 1 + s) = 0 := by
  intro s hs
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hd1 : ((1 : ℕ) : ℝ) ≤ arcDen 12 H := by
    have : (1 : ℝ) ≤ arcDen 12 H := le_trans hq1 hqQ
    simpa using this
  have hreg := hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 1 (by norm_num) hd1 s
    (by simpa using hs)
  have hz := doorRowCarriedT0_endpoint_L hreg
  simpa using hz

/-- **THE REGISTER PINS THE ENDPOINT, AT THE LEVER** — `doorRowCarriedT0_endpoint_L`
(:563). -/
theorem doorRowCarriedT0_endpoint_L_gk (K : ℕ) {Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ}
    {q : ℕ} {χ : DirichletCharacter ℂ q} {M Xd j : ℕ} {B : ℝ}
    (hreg : DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B) :
    doorChiCoeff_L_gk K χ M Xd = 0 := by
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, hwin, δ', V, VJ, L, Cb, kmin, Ymax, εw, Xw, cqS,
    cgS, cW, SW, Rbar0, Dmask, hc⟩ := hreg
  repeat (first | exact hc.1 | replace hc := hc.2)

/-- **THE REGISTER FORCES THE WHOLE INTERVAL, AT THE LEVER** —
`m4_register_forces_endpoint_interval_L` (:578). -/
theorem m4_register_forces_endpoint_interval_L_gk (K : ℕ)
    {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ}
    (hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
        doorRowFloorL M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
          ∀ s ≤ H / d + 1,
            DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
              (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H))
    {H : ℕ} (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) {q : ℕ} (hq : 0 < q)
    (hqQ : (q : ℝ) ≤ arcDen 12 H) (χ : DirichletCharacter ℂ q) {i : ℕ} (hik : i < k)
    {j : ℕ} (hjL : j ≤ Nat.log 2 H) (hj0 : doorRowFloorL M ≤ j) :
    ∀ s ≤ H + 1, doorChiCoeff_L_gk K χ M (doorLadder R.x H (i + 1) - 1 + s) = 0 := by
  intro s hs
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hd1 : ((1 : ℕ) : ℝ) ≤ arcDen 12 H := by
    have : (1 : ℝ) ≤ arcDen 12 H := le_trans hq1 hqQ
    simpa using this
  have hreg := hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 1 (by norm_num) hd1 s
    (by simpa using hs)
  have hz := doorRowCarriedT0_endpoint_L_gk K hreg
  simpa using hz
/-! ## §6 — `S11Thread` -/

/-- **THE WAVE'S EXIT, SPLIT, WITH THE TOWER** (`m4_door_contradiction_of_live_split_tower_L`) —
`M4Close.m4_door_contradiction_of_live_split` with `M4Exit.m4_exit_socket_split`'s tower
conjunct FORWARDED instead of dropped.  Statement diff against the landed twin: one extra
conjunct in the `∃ R` payload, `50 ≤ loglog R.Hlo → loglog R.Hhi ≤ (loglog R.Hlo)^5`.  The
register (`M4DoorGates_L`, `0 ≤ Braw`, `M4GradeGateSplit`, `M4SievedDoorSq_L`) and the conclusion
are byte-identical. -/
theorem m4_door_contradiction_of_live_split_tower_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4SievedDoorSq_L R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_split_L
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  -- ⟦THE NAMED AMENDMENT⟧, named here instead of discarded
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ := hexit U1floor g
  exact ⟨R, hReps, hU1, hRg, hRtow, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R δ₀ δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **⟦THE SECOND ROAD'S TERMINAL REGISTER, WITH THE TOWER⟧** (`m4_second_road_tower_L`).
`M4SecondRoad.m4_second_road` with the tower endpoint law carried in the `∃ R` payload.  The
ten-item gate census, the analytic slot ⟦item 11⟧ and the conclusion are byte-identical to the
landed road; the proof is the landed proof with the extra component passed through. -/
theorem m4_second_road_tower_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) ∧
          ∀ (δ : ℝ) (RS : ℕ → ℕ → ℝ) (RSan RStr Braw : ℕ → ℝ) (M k j₀ : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ RSan H) → (∀ H : ℕ, 0 ≤ RStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 128 * arcDen 12 H ^ 3 ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                  * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H
                ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4ChiSummedFreeRow_L R M RS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split_tower_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, ?_⟩
  intro δ RS RSan RStr Braw M k j₀ hgates hM hRSan0 hRStr0 hBraw0 han hG1 hG2 harc3 hdgate
    hdrift hgrade hrow
  -- ⟦the window floor, read at the two powers the chain spends⟧
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
  have hchi : M4ChiSummedBlockMeanSqN_L R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) :=
    m4_chiSummedN_supplied_L j₀ hRSan0 hRStr0 han hG1 hG2 harc8 hrow
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H :=
    fun H => m4BclGraded_nonneg (by have := hRSan0 H; linarith) (by have := hRStr0 H; linarith)
  -- ⟦the blocked block mean square⟧
  have hblk2 := m4_blockMeanSqBlk2_of_chiSummed_L (k := k) hM hBcl0 hdgate harc hgates.hcount hchi
  have hBblk0 : ∀ H : ℕ, 0 ≤ 8 * strataResidual H ^ 2
      * m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H) H := by
    intro H
    have := hBcl0 H
    positivity
  -- ⟦the cover, then the socket⟧
  have hcov := m4_cover_assembly_blk2_L hgates hBblk0 hblk2
  refine hR δ Braw M k hgates hBraw0 hgrade ?_
  refine m4_sievedDoorSq_of_blk2_L (ℓ := blockLen)
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
/-! ## §Xk — ⟦CAP-RECUT P2(b)⟧ THE WIDE-CEILING TWINS

The lever raise `K := KlevF A ≈ 4·e^{1.6A}` breaks every flat `hK : K ≤ 170000000` binder on the
L chain.  The repair is a HYPOTHESIS WEAKENING: because `M` is quantified INSIDE these
statements, the ceiling must move inside with it, to `K ≤ 170000000·M` — the WIDE ceiling the
door frame (`DoorLadderLinear.calFrameK_satisfiable_doorH1_L_gk`) has carried all along and
that `ThmA2Linear.kwide` was throwing away.  The two twins below are the DEEPEST pair on the
chain (six consumers between them) and the pattern for the rest: statement verbatim with
`(hK : K ≤ 170000000)` deleted from the binder list and `K ≤ 170000000 * M →` inserted
immediately after the internal `1 ≤ M →`; proof verbatim with `calFrameK_doorH1_at_L_gk`
re-pointed at `calFrameK_doorH1_at_L_gk_kwide`.  The originals are untouched.
-/

/-- **⟦THE ROW FAMILY AT THE WIDE CEILING⟧** (`m4_hrowsSum_chi_door_zero_L_gk_kwide`) —
`m4_hrowsSum_chi_door_zero_L_gk` with the ceiling moved inside the `∀ M`.  Body verbatim off
`calFrameK_doorH1_at_L_gk_kwide`. -/
theorem m4_hrowsSum_chi_door_zero_L_gk_kwide (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            (winCutH Xd (doorCoeffU_L_gk K M)) (bfam j) c) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ a2Mrow_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hKw hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_L_gk K M)) bfam ha1 hb1 hc1 N Xd
    (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_L_gk_kwide K M Xd hM hKw hXdQ) hNXd hN4 hcoefWS
    (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_L_gk K M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow_L_gk K hM hXd1 hCp

/-- **⟦THE SLOT AT THE WIDE CEILING⟧** (`m4_hrowsSlot_at_door_zero_L_gk_kwide`) —
`m4_hrowsSlot_at_door_zero_L_gk` with the ceiling moved inside the `∀ M`.  Body verbatim. -/
theorem m4_hrowsSlot_at_door_zero_L_gk_kwide (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero_L_gk_kwide K
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hKw hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

end Salt.MR

end
