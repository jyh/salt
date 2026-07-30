/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12Compose
import Salt.MR.ConstantsExposed

/-!
# ⟦S13-A⟧ — THE SPINE-ARITHMETIC PAGES AT THE CERTIFIED WORKING POINT

PURELY ADDITIVE: no landed declaration is touched anywhere in this file.

`S12Compose.logChowla2_capstone_conditional` carries a residue in two groups.  This file is
the **(A) group** — the five spine-arithmetic items — made kernel at the working point the
`REF-L2-ARITH`/`REF-L2-FINAL` walks certified:

* `m = log₂ M + 1 = 66` (the `b`-floor `24·Cg/δ₀ = 2^65.125`: ONE bit of margin);
* `δ₀ = c₀·ε/4` at `ε = 1/500`, `c₀ = 1/(64·C_cm) ≥ 2.385496·10⁻³` (`ConstantsExposed`);
* `λ₋ = loglog H₋ ∈ [74.198, 83.667]`, `λ₊ = loglog H₊ ≤ λ₋^{9/2}` (the regime's own tower
  conjunct at the `9/2` exponent).

⟦WHAT IS A HYPOTHESIS AND WHY⟧  The capstone's `Cg`, `δ₀`, `ε` are `∃`-bound OPAQUE reals; a
kernel proof cannot read their numerals.  So the `b`-floor is delivered in two halves that
compose only at the call site:

* §1 the numeral certificate `s13_b_floor_cert` — `24·CgExpr/s13Delta0 ≤ s13M`, proved from
  `ConstantsExposed.Cg_le` and the `c₀` chain, with `s13M` in the `m = 66` window;
* §2 the assembly `s13_doorGates_of_arm`, which takes `24·Cg/δ ≤ M` as ONE hypothesis (that
  is the field `hMδ` itself) and discharges the OTHER SEVEN fields of `M4DoorGates` from the
  regime, the count, and the `g`-arm.

Likewise `λ₊` is an upper bound on the regime the compose HANDS us; `U1floor` controls only
`λ₋` from below.  So §4/§5's pages carry the window ceiling as a named hypothesis
(`s13LamHi`) and derive everything else.

⟦THE `g`-ARM⟧  `s13GArm M δ` packs the four `x`-floors the (A) group spends — all `H`-free
except the one that reads `H₊`, all legal in the capstone's `∀ g` slot because `M` and `δ₀`
are bound BEFORE `g`.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE CERTIFIED WORKING POINT (the `b`-floor, the `m = 66` window) -/

/-- **THE `L²` THRESHOLD, AS AN EXPRESSION** (`s13Delta0`) — `SpineFinal`'s
`log_chowla_two_budget_head_g_sq` witness `cD3/(16·C)·ε/4` at `cD3 = 1/4`, `C = CcmExpr`,
`ε = epsPin = 1/500`.  It is `ConstantsExposed.delta0Expr` with the `1/(2K)` REPLACED by the
`K`-free `1/4` — the whole content of the `L²` restructure's `b`-floor gain (603 → 65 bits). -/
def s13Delta0 : ℝ := (1 / 4 : ℝ) / (16 * CcmExpr) * (epsPin : ℝ) / 4

/-- The collapsed form: `δ₀ = 1/(128000·C_cm)`. -/
theorem s13Delta0_eq : s13Delta0 = 1 / (128000 * CcmExpr) := by
  have hC := CcmExpr_pos
  rw [s13Delta0, epsPin_cast]
  field_simp
  ring

theorem s13Delta0_pos : 0 < s13Delta0 := by
  have hC := CcmExpr_pos
  rw [s13Delta0_eq]; positivity

/-- **THE `δ₀` CERTIFICATE** — `1.1927·10⁻⁶ ≤ δ₀` (`c₀ = 1/(64·C_cm) ≥ 2.385496·10⁻³`, the
`REF-L2-ARITH` table's head number). -/
theorem s13Delta0_ge : 1 / 838400 ≤ s13Delta0 := by
  have hC := CcmExpr_pos
  have hCle := CcmExpr_le
  have hden : 128000 * CcmExpr ≤ 838400 := by nlinarith
  have hdenpos : (0 : ℝ) < 128000 * CcmExpr := by positivity
  rw [s13Delta0_eq]
  exact one_div_le_one_div_of_le hdenpos hden

/-- **THE WORKING MODULUS** (`s13M = 4.5·10¹⁹`) — the `K`-family re-pin parameter at the
certified point.  It sits in `[2^65, 2^66)`, so `log₂ M + 1 = 66`, and above the `b`-floor
`24·Cg/δ₀ = 4.0243·10¹⁹ = 2^65.125`: **the ONE bit of margin**. -/
def s13M : ℕ := 45000000000000000000

/-- `m = log₂ s13M + 1 = 66`. -/
theorem s13M_log : Nat.log 2 s13M + 1 = 66 := by
  have h : Nat.log 2 s13M = 65 := by
    refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_ <;> · rw [s13M]; norm_num
  omega

theorem s13M_pos : 1 ≤ s13M := by rw [s13M]; norm_num

/-- **THE `b`-FLOOR CERTIFICATE AT THE `L²` THRESHOLD** (`s13_b_floor_cert`) —
`24·Cg/δ₀ ≤ s13M`, i.e. `M4DoorGates.hMδ` holds at the working modulus.

The true value is `24·(2·e^{19/log 2}+1)·128000·C_cm = 4.0243·10¹⁹ = 2^65.125`; `s13M` is
`4.5·10¹⁹ < 2^66`.  This is the whole `b`-floor ledger of the `L²` route, in one line. -/
theorem s13_b_floor_cert : 24 * CgExpr / s13Delta0 ≤ (s13M : ℝ) := by
  have hCg := Cg_le
  have hCgpos := CgExpr_pos
  have hC := CcmExpr_pos
  have hCle := CcmExpr_le
  rw [s13Delta0_eq, one_div, div_inv_eq_mul, s13M]
  have hstep : 24 * CgExpr * (128000 * CcmExpr)
      ≤ 24 * (2 * 10 ^ 12) * (128000 * (655 / 100)) := by
    nlinarith [hCg, hCgpos, hC, hCle]
  refine le_trans hstep ?_
  norm_num

/-! ## §2 — ⟦A-1⟧ `M4DoorGates` AT `k := doorCount R.ω`

Seven of the eight fields are discharged here; `hMδ` is §1's certificate, carried as the one
hypothesis (it is the only field that reads the opaque `Cg`, `δ`).
-/

/-- **THE BLOCK-SCALE EXPONENT** (`s13BlockExp`) — the `log₂` floor a door-ladder rung must
clear for `SieveBlockGate (Adoor M) (3072M) M 2` to hold there.  Three summands, one per
analytic conjunct of the gate:

* `14427` — `X ≥ e^{10000}`, i.e. `√log X ≥ 100` (`SieveGlue.hbig_of_floor`);
* `64 + 8·(log₂M+1)` — `√X ≥ 2^{32}·M⁴ ≥ 16·(j²M)⁴·e^{57/log P_j}`
  (`SieveGlue.herr_of_floor`, the Mertens/Rankin page: the Euler product is already
  eliminated, and `e^{57/log P_j} ≤ e` because `log P₁ = Adoor M·log 2 ≥ 2.4·10¹⁰`);
* `400·(A·G·M)²` — `√log X ≥ 16·A·G·M ≥ log 𝒬_j` for `j ∈ {1,2}` (MR's regularity gate;
  `log 𝒬_2 = 16·A·G·M·log 2` on the nose).

All three are `H`-FREE, so the floor rides the `g`-arm and never touches the window. -/
def s13BlockExp (M : ℕ) : ℕ :=
  14427 + (64 + 8 * (Nat.log 2 M + 1)) + 400 * (Adoor M * (3072 * M) * M) ^ 2

/-- The block-scale floor itself, `2^{s13BlockExp M}`. -/
def s13BlockFloor (M : ℕ) : ℕ := 2 ^ s13BlockExp M

set_option maxHeartbeats 1000000 in
-- the four analytic conjuncts are discharged in one pass at astronomically large symbolic
-- exponents (`400·(A·G·M)²`), and every numeric step is an `nlinarith`/`positivity` over
-- casts of those exponents; the default budget is exhausted by the last two conjuncts
/-- **⟦THE MERTENS/RANKIN PAGE⟧** (`s13_sieveBlockGate`) — HS-3's four analytic gates at the
door family, from the single scale floor `s13BlockFloor M ≤ X`.

This is the one unpriced item of the (A) group: `M4DoorGates.hblocks` asks for
`SieveBlockGate (Adoor M) (3072M) M 2 (doorLadder R.x H (i+1))` at EVERY rung of the cover,
and `M4SecondRoad.doorLadder_ge_x_div_four_omega` puts every rung above `⌊x/(4ω)⌋`.  So one
`x`-floor on the `g`-arm discharges the whole family. -/
theorem s13_sieveBlockGate {M X : ℕ} (hM : 1 ≤ M) (hX : s13BlockFloor M ≤ X) :
    SieveBlockGate (Adoor M) (3072 * M) M 2 X := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  set N := s13BlockExp M with hN
  -- the real form of the floor
  have hXN : ((2 : ℝ)) ^ N ≤ (X : ℝ) := by
    have h : ((2 ^ N : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    simpa using h
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hX0 : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le h2pos hXN
  have hX1 : 1 ≤ X := by
    have : (0 : ℕ) < X := by exact_mod_cast hX0
    omega
  -- ⟦the exponent's three summands⟧
  have hsplit : ∀ a : ℕ, a ≤ N → ((2 : ℝ)) ^ a ≤ (X : ℝ) := by
    intro a ha
    refine le_trans (pow_le_pow_right₀ (by norm_num) ha) hXN
  have hA : 14427 ≤ N := by rw [hN, s13BlockExp]; omega
  have hB : 64 + 8 * (Nat.log 2 M + 1) ≤ N := by rw [hN, s13BlockExp]; omega
  have hC : 400 * (Adoor M * (3072 * M) * M) ^ 2 ≤ N := by rw [hN, s13BlockExp]; omega
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
  -- ⟦the log floor⟧ `log X ≥ N·log 2`
  have hlogX : ((N : ℕ) : ℝ) * Real.log 2 ≤ Real.log (X : ℝ) := by
    have h1 : Real.log (((2 : ℝ)) ^ N) ≤ Real.log (X : ℝ) := Real.log_le_log h2pos hXN
    rwa [Real.log_pow] at h1
  -- ⟦GATE (c)⟧ MR's regularity, at `j ∈ {1, 2}`
  have hAd : (1 : ℝ) ≤ (Adoor M : ℝ) := by
    have : 1 ≤ Adoor M := by
      rw [Adoor]
      have : 0 < 2 ^ 36 * (Nat.log 2 M + 1) := by positivity
      omega
    exact_mod_cast this
  have hG : (1 : ℝ) ≤ ((3072 * M : ℕ) : ℝ) := by
    have : 1 ≤ 3072 * M := by omega
    exact_mod_cast this
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set W : ℝ := (Adoor M : ℝ) * ((3072 * M : ℕ) : ℝ) * (M : ℝ) with hW
  have hAG1 : (1 : ℝ) ≤ (Adoor M : ℝ) * ((3072 * M : ℕ) : ℝ) := by nlinarith
  have hW1 : (1 : ℝ) ≤ W := by rw [hW]; nlinarith
  have hWN : (400 : ℝ) * W ^ 2 ≤ ((N : ℕ) : ℝ) := by
    have h : ((400 * (Adoor M * (3072 * M) * M) ^ 2 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
      exact_mod_cast hC
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
      Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    refine le_trans ?_ hsqrtW
    rw [log_calQK]
    have hWcast : W = (Adoor M : ℝ) * (3072 * (M : ℝ)) * (M : ℝ) := by
      rw [hW]; push_cast; ring
    have hAd0 : (0 : ℝ) < (Adoor M : ℝ) := by linarith
    have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
    interval_cases j
    · rw [calE_one, hWcast]
      push_cast
      nlinarith [hlog2hi, hlog2, hAd, hMR, hAd0, hM0,
        mul_pos hAd0 hM0, mul_nonneg (mul_pos hAd0 hM0).le (sub_nonneg.mpr hMR)]
    · rw [calE_two, hWcast]
      push_cast
      nlinarith [hlog2hi, hlog2, hAd, hMR, hAd0, hM0,
        mul_pos (mul_pos hAd0 hM0) hM0]
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
      have : (((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4) ^ 2
          = ((2 : ℝ)) ^ (64 : ℕ) * (M : ℝ) ^ 8 := by ring
      rw [this]; exact hXM
    have h2 : Real.sqrt ((((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4) ^ 2) ≤ Real.sqrt X :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  -- `e^{57/log P_j} ≤ e` : `log P_j ≥ Adoor M·log 2 ≥ 2^{36}·0.693 ≫ 57`
  have hlogP1 : (57 : ℝ) ≤ Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    rw [log_calP_door_one]
    have hAd36 : ((2 : ℝ)) ^ (36 : ℕ) ≤ (Adoor M : ℝ) := by
      have : 2 ^ 36 ≤ Adoor M := by
        rw [Adoor]
        have : 1 ≤ Nat.log 2 M + 1 := by omega
        calc 2 ^ 36 = 2 ^ 36 * 1 := by ring
          _ ≤ 2 ^ 36 * (Nat.log 2 M + 1) := by exact Nat.mul_le_mul_left _ this
      exact_mod_cast this
    have h36 : ((2 : ℝ)) ^ (36 : ℕ) = 68719476736 := by norm_num
    rw [h36] at hAd36
    nlinarith [hlog2lo, hAd36]
  have hexp57 : ∀ j : ℕ, 1 ≤ j →
      Real.exp (57 / Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)) ≤ 3 := by
    intro j hj
    have hmono : Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
        ≤ Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) := by
      rw [log_calP, log_calP]
      have hE : calE (Adoor M) (3072 * M) 1 ≤ calE (Adoor M) (3072 * M) j := by
        have := calE_mono (Adoor M) (show 1 ≤ 3072 * M by omega) hj
        exact this
      have hEc : ((calE (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
          ≤ ((calE (Adoor M) (3072 * M) j : ℕ) : ℝ) := by exact_mod_cast hE
      exact mul_le_mul_of_nonneg_right hEc hlog2.le
    have hlogPj : (57 : ℝ) ≤ Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) :=
      le_trans hlogP1 hmono
    have hlogPj0 : (0 : ℝ) < Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) := by
      linarith
    have hdiv : 57 / Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ) ≤ 1 :=
      (div_le_one hlogPj0).mpr (by linarith)
    calc Real.exp (57 / Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ))
        ≤ Real.exp 1 := Real.exp_le_exp.mpr hdiv
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have herrj : ∀ j ∈ Finset.Icc 1 2,
      ((Nat.sqrt X : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
              (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
        ≤ (X : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
            / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine herr_of_floor (by
      have : 1 ≤ Adoor M := by
        rw [Adoor]
        have : 0 < 2 ^ 36 * (Nat.log 2 M + 1) := by positivity
        omega
      exact this) (by omega) hM hj.1 hX1 ?_
    have hjR : ((j : ℝ)) ^ 2 * (M : ℝ) ≤ 4 * (M : ℝ) := by
      have hjle : ((j : ℝ)) ≤ 2 := by exact_mod_cast hj.2
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hjsq : ((j : ℝ)) ^ 2 ≤ 4 := by nlinarith
      exact mul_le_mul_of_nonneg_right hjsq (Nat.cast_nonneg M)
    have hj4 : (((j : ℝ)) ^ 2 * (M : ℝ)) ^ 4 ≤ 256 * (M : ℝ) ^ 4 := by
      have h0 : (0 : ℝ) ≤ ((j : ℝ)) ^ 2 * (M : ℝ) := by positivity
      calc (((j : ℝ)) ^ 2 * (M : ℝ)) ^ 4 ≤ (4 * (M : ℝ)) ^ 4 :=
            pow_le_pow_left₀ h0 hjR 4
        _ = 256 * (M : ℝ) ^ 4 := by ring
    have hE := hexp57 j hj.1
    have hE0 : (0 : ℝ) < Real.exp (57 / Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)) :=
      Real.exp_pos _
    have hM4 : (0 : ℝ) < (M : ℝ) ^ 4 := by positivity
    calc 16 * (((j : ℝ)) ^ 2 * (M : ℝ)) ^ 4
            * Real.exp (57 / Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ))
        ≤ 16 * (256 * (M : ℝ) ^ 4) * 3 := by nlinarith
      _ = 12288 * (M : ℝ) ^ 4 := by ring
      _ ≤ ((2 : ℝ)) ^ (32 : ℕ) * (M : ℝ) ^ 4 := by
          have h12 : (12288 : ℝ) ≤ ((2 : ℝ)) ^ (32 : ℕ) := by norm_num
          exact mul_le_mul_of_nonneg_right h12 (by positivity)
      _ ≤ Real.sqrt X := hsqrtX
  exact ⟨hX0, hbig, hregj, herrj⟩

/-! ### The `g`-arm -/

/-- **THE `(A)`-GROUP `g`-ARM** (`s13GArm M δ`) — the four `x`-floors the spine arithmetic
spends, packed into the capstone's `∀ g` slot.  Legal there because `M` and `δ₀` are bound
BEFORE `g` in `logChowla2_capstone_conditional`'s quantifier prefix.

| summand | what it buys |
|---|---|
| `2·ω·(H₊+2)` | `M4Door.doorCount_gates` — `hreach` and `hcount` at `k := doorCount ω` |
| `8·ω` | `hpow`: `2^{k+1} ≤ 8ω` through `2^k ≤ 4ω` |
| `4·ω·s13BlockFloor M` | `hblocks`: every ladder rung is `≥ ⌊x/(4ω)⌋ ≥ s13BlockFloor M` |
| `⌈128·ω/δ⌉₊` | ⟦THE NEW ARM⟧ the endpoint share `8·2^k/x ≤ δ/4` |

Only the first reads `H₊`; the other three are `H`-FREE. -/
def s13GArm (M : ℕ) (δ : ℝ) : ℕ → ℕ → ℕ := fun Hhi ω =>
  2 * ω * (Hhi + 2) + 8 * ω + 4 * ω * s13BlockFloor M + ⌈128 * (ω : ℝ) / δ⌉₊

/-- `4 ≤ log ω` at every regime — the `hlogω` field, from `R.hωbig` and `R.hPNTwindow`
alone (`64/ε ≥ 128` at `ε ≤ 1/2`, and `ε²H₊ ≥ ε²H₋ ≥ 4000 ≥ 1` makes the `log` term
nonnegative).  No `g`-arm, no window hypothesis. -/
theorem s13_logOmega_ge (R : ChowlaRegime) : 4 ≤ Real.log (R.ω : ℝ) := by
  have hεpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hεhalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : ((R.eps : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast R.heps1
    simpa using h
  have hHloR : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hsqrt : (2000 : ℝ) ≤ Real.sqrt (R.Hlo : ℝ) := by
    have h : Real.sqrt (4000000 : ℝ) ≤ Real.sqrt (R.Hlo : ℝ) := Real.sqrt_le_sqrt hHloR
    rwa [show (4000000 : ℝ) = 2000 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2000)] at h
  have hw := R.hPNTwindow
  have h4000 : (4000 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (R.Hlo : ℝ) := by linarith
  have hHle : (R.Hlo : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast R.hHlohi
  have hmono : (R.eps : ℝ) ^ 2 * (R.Hlo : ℝ) ≤ (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) :=
    mul_le_mul_of_nonneg_left hHle (sq_nonneg _)
  have hlogpos : (0 : ℝ) ≤ Real.log ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) :=
    Real.log_nonneg (by linarith)
  have h16 : (0 : ℝ) ≤ 16 / (R.eps : ℝ) * Real.log ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) :=
    mul_nonneg (by positivity) hlogpos
  have h64 : (128 : ℝ) ≤ 64 / (R.eps : ℝ) := by
    rw [le_div_iff₀ hεpos]; linarith
  linarith [R.hωbig]

/-- **⟦A-1⟧ THE DOOR-GLUE REGISTER, DISCHARGED** (`s13_doorGates_of_arm`) — seven of
`M4DoorGates`' eight fields, at `k := doorCount R.ω`, from the `g`-arm and the regime alone.

The eighth, `hMδ` (`24·Cg/δ ≤ M`), is the `b`-floor: it reads the capstone's OPAQUE `Cg`
and `δ₀`, so it is carried here as a hypothesis and certified numerically by
`s13_b_floor_cert` at `(CgExpr, s13Delta0, s13M)`. -/
theorem s13_doorGates_of_arm {Cg δ : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (hδ : 0 < δ) (hMδ : 24 * Cg / δ ≤ (M : ℝ))
    (harm : s13GArm M δ R.Hhi R.ω ≤ R.x) :
    M4DoorGates Cg R M (doorCount R.ω) δ := by
  have hω1 : 1 ≤ R.ω := by have := R.hω; omega
  have hcount : ((doorCount R.ω : ℕ) : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2 :=
    doorCount_le hω1
  -- ⟦the arm's four summands⟧
  have harm1 : 2 * R.ω * (R.Hhi + 2) ≤ R.x := by
    rw [s13GArm] at harm; omega
  have harm2 : 8 * R.ω ≤ R.x := by rw [s13GArm] at harm; omega
  have harm3 : 4 * R.ω * s13BlockFloor M ≤ R.x := by rw [s13GArm] at harm; omega
  refine ⟨hM, hδ, hMδ, s13_logOmega_ge R, ?_, hcount, ?_, ?_⟩
  · -- ⟦hpow⟧ `2^{k+1} ≤ 8ω ≤ x`
    have h4 : 2 ^ (doorCount R.ω) ≤ 4 * R.ω :=
      two_pow_le_four_mul_of_count R.hω hcount
    have : 2 ^ (doorCount R.ω + 1) = 2 ^ (doorCount R.ω) * 2 := by rw [pow_succ]
    omega
  · -- ⟦hreach⟧ the ladder exhausts the window, off `2ω(H+2) ≤ x`
    intro H hlo hhi
    have hbig : 2 * (R.ω : ℝ) * ((H : ℝ) + 2) ≤ (R.x : ℝ) := by
      have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
      have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
      have h1 : ((2 * R.ω * (R.Hhi + 2) : ℕ) : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast harm1
      push_cast at h1
      nlinarith
    exact (doorCount_gates hω1 hbig).1
  · -- ⟦hblocks⟧ every rung sits above `⌊x/(4ω)⌋ ≥ s13BlockFloor M`
    intro H hlo hhi i hik
    have hmid : s13BlockFloor M ≤ R.x / (4 * R.ω) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc s13BlockFloor M * (4 * R.ω) = 4 * R.ω * s13BlockFloor M := by ring
        _ ≤ R.x := harm3
    exact s13_sieveBlockGate hM
      (le_trans hmid (doorLadder_ge_x_div_four_omega (H := H) R.hω hcount (by omega)))

/-- **⟦A-2⟧ THE ENDPOINT SHARE, DISCHARGED** (`s13_endpoint_of_arm`) — `8·2^k/x ≤ δ/4` at
`k := doorCount R.ω`, off `2^k ≤ 4ω` (`M4SecondRoad.two_pow_le_four_mul_of_count`) and the
arm's ⟦NEW ARM⟧ `x ≥ 128·ω/δ`.  A pure `g`-lever: `H`-FREE. -/
theorem s13_endpoint_of_arm {δ : ℝ} {R : ChowlaRegime} {M : ℕ} (hδ : 0 < δ)
    (harm : s13GArm M δ R.Hhi R.ω ≤ R.x) :
    8 * 2 ^ (doorCount R.ω) / (R.x : ℝ) ≤ δ / 4 := by
  have hω1 : 1 ≤ R.ω := by have := R.hω; omega
  have hcount := doorCount_le hω1
  have h4 : 2 ^ (doorCount R.ω) ≤ 4 * R.ω := two_pow_le_four_mul_of_count R.hω hcount
  have h4R : ((2 ^ (doorCount R.ω) : ℕ) : ℝ) ≤ 4 * (R.ω : ℝ) := by exact_mod_cast h4
  have harm4 : ⌈128 * (R.ω : ℝ) / δ⌉₊ ≤ R.x := by rw [s13GArm] at harm; omega
  have hceil : 128 * (R.ω : ℝ) / δ ≤ (R.x : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast harm4
  have hx0 : (0 : ℝ) < (R.x : ℝ) := by
    have : 0 < R.x := by have := R.hx; omega
    exact_mod_cast this
  have hkey : 128 * (R.ω : ℝ) ≤ δ * (R.x : ℝ) := by
    rw [div_le_iff₀ hδ] at hceil
    linarith
  rw [div_le_div_iff₀ hx0 (by norm_num : (0:ℝ) < 4)]
  have h2R : (8 : ℝ) * ((2 : ℝ) ^ (doorCount R.ω)) ≤ 32 * (R.ω : ℝ) := by
    have : ((2 : ℝ)) ^ (doorCount R.ω) ≤ 4 * (R.ω : ℝ) := by
      simpa using h4R
    linarith
  linarith

/-! ## §3 — THE WINDOW CEILING (`λ₊` from `λ₋` through the `9/2` tower) -/

/-- **⟦THE WINDOW CEILING⟧** (`s13_loglogHhi_le`) — `λ₊ = loglog H₊ ≤ 4.481·10⁸` from the
regime's own `S0`-tower conjunct at the exponent `9/2` and the window's upper end
`λ₋ ≤ 83.66`.

`83.66^{9/2} = 83.66⁴·√83.66 ≤ 48985940·9.1466 = 4.48055·10⁸`.

⟦WHY `83.66` AND NOT `REF-L2-ARITH`'s `83.667`⟧ the ceiling is set by the `GRowsZeroGate.p2`
slot (`1.002·μ + 15 ≤ log2·Adoor M` at `μ ≈ 7000·λ₊ + 1.25·10⁵`), which at `m = 66` binds at
`λ₋ ≤ 83.6659`; `83.667` overshoots it by `1.1·10⁻³` and fails `p2` by `2.2·10⁸` out of
`3.1438·10¹²` (relative `7·10⁻⁵`).  See §7. -/
theorem s13_loglogHhi_le {R : ChowlaRegime}
    (h50 : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (htow : 50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
      Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2))
    (hlam : Real.log (Real.log (R.Hlo : ℝ)) ≤ 8366 / 100) :
    Real.log (Real.log (R.Hhi : ℝ)) ≤ 448100000 := by
  set x : ℝ := Real.log (Real.log (R.Hlo : ℝ)) with hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hsplit : x ^ ((9 : ℝ) / 2) = x ^ (4 : ℕ) * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 4, ← Real.rpow_add hx0]
    norm_num
  have hp4 : x ^ (4 : ℕ) ≤ (8366 / 100 : ℝ) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hx0.le hlam 4
  have hsq : Real.sqrt x ≤ 91466 / 10000 := by
    have hle : x ≤ (91466 / 10000 : ℝ) ^ 2 := by
      have : (8366 / 100 : ℝ) ≤ (91466 / 10000 : ℝ) ^ 2 := by norm_num
      linarith
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 91466 / 10000)] at h
  have hsq0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hp40 : (0 : ℝ) ≤ x ^ (4 : ℕ) := by positivity
  have hprod : x ^ (4 : ℕ) * Real.sqrt x
      ≤ (8366 / 100 : ℝ) ^ (4 : ℕ) * (91466 / 10000 : ℝ) :=
    mul_le_mul hp4 hsq hsq0 (by positivity)
  have hnum : (8366 / 100 : ℝ) ^ (4 : ℕ) * (91466 / 10000 : ℝ) ≤ 448100000 := by norm_num
  calc Real.log (Real.log (R.Hhi : ℝ)) ≤ x ^ ((9 : ℝ) / 2) := htow h50
    _ = x ^ (4 : ℕ) * Real.sqrt x := hsplit
    _ ≤ (8366 / 100 : ℝ) ^ (4 : ℕ) * (91466 / 10000 : ℝ) := hprod
    _ ≤ 448100000 := hnum

/-- `loglog H ≤ loglog H₊` at every window length in range. -/
theorem s13_loglog_le_of_range {R : ChowlaRegime} {H : ℕ} (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) :
    Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (R.Hhi : ℝ)) := by
  have hLH : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hLH
  have hH0 : (0 : ℝ) < (H : ℝ) := by
    have h4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
    have : (0 : ℕ) < H := by omega
    exact_mod_cast this
  have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
  exact Real.log_le_log hL0 (Real.log_le_log hH0 hHle)

/-! ## §4 — ⟦A-3⟧ THE ⟦G2⟧ `j₀`-FLOOR AND ⟦A-4⟧ ⟦GATE 8⟧ -/

/-- **⟦A-3⟧ THE ⟦G2⟧ `j₀`-FLOOR** (`s13_g2_jfloor`) — `4·log(263·max 1 (arcDen 12 H)) ≤
doorRowFloor M` on the whole window range, from the window ceiling `λ₊ ≤ Λ` and ONE numeral
gate `4·log 263 + 48·Λ ≤ doorRowFloor M`.

`arcDen 12 H = (log H)^{12}` and `log H ≥ e` in range, so the left side is
`4·log 263 + 48·loglog H` — the `S11Arc36`-genre numeral page. -/
theorem s13_g2_jfloor {R : ChowlaRegime} {M : ℕ} {Λ : ℝ}
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ)
    (hgate : 4 * Real.log 263 + 48 * Λ ≤ ((doorRowFloor M : ℕ) : ℝ)) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * Real.log (263 * max 1 (arcDen 12 H)) ≤ ((doorRowFloor M : ℕ) : ℝ) := by
  intro H hlo hhi
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hLH : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hLH
  have hmax : max 1 (arcDen 12 H) = arcDen 12 H := max_eq_right harc1
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) := by
    rw [arcDen, Real.log_rpow hL0]
  have hlogmul : Real.log (263 * arcDen 12 H) = Real.log 263 + Real.log (arcDen 12 H) :=
    Real.log_mul (by norm_num) (by linarith)
  have hle := le_trans (s13_loglog_le_of_range (R := R) hlo hhi) hΛ
  rw [hmax, hlogmul, hlogarc]
  linarith

/-- **⟦A-4⟧ ⟦GATE 8⟧ THE SOCKET `M`-CAP** (`s13_gate8`) — `arcDen 12 H < 𝒫₁ = 2^{Adoor M}` on
the window range, from `λ₊ ≤ Λ` and `12·Λ < Adoor M·log 2`.

At the working point `m = 66`: `Adoor M·log 2 = 3.1438·10¹²` against `12·λ₊ ≤ 5.378·10⁹` —
slack `585×`.  ⟦REF-L2-ARITH⟧'s ⟦NEW ARM⟧: this, not the drift cap, is what binds `λ` from
above through the `9/2` tower. -/
theorem s13_gate8 {R : ChowlaRegime} {M : ℕ} {Λ : ℝ}
    (hΛ : Real.log (Real.log (R.Hhi : ℝ)) ≤ Λ)
    (hgate : 12 * Λ < (Adoor M : ℝ) * Real.log 2) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
  intro H hlo hhi
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hLH : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hLH
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) := by
    rw [arcDen, Real.log_rpow hL0]
  have hle := le_trans (s13_loglog_le_of_range (R := R) hlo hhi) hΛ
  have hP0 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have := calP_door_one_ge M; linarith
  have hlogP : Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = (Adoor M : ℝ) * Real.log 2 :=
    log_calP_door_one M
  have hlt : Real.log (arcDen 12 H) < Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    rw [hlogarc, hlogP]; linarith
  have h1 := Real.exp_lt_exp.mpr hlt
  rwa [Real.exp_log (by linarith : (0:ℝ) < arcDen 12 H), Real.exp_log hP0] at h1

/-! ## §5 — ⟦A-5⟧ THE GRADED SPLIT'S SMALL-`j` THRESHOLD (THE TIGHT ONE)

`m4SmallGradeFits j₀ Fan Ftr H` is the ONE item whose floor is the window's whole width: at
`j₀ = doorRowFloor M = M·Adoor M ≈ 2.04·10³²` the demand is `log H ≳ (log 2)·j₀`, i.e.
`λ₋ = loglog H ≳ 74.04`.  ⟦REF-L2-ARITH⟧'s `λ₋ ≥ 74.198` is this inequality; the version
proved here needs only `74.045`.

⟦THE TWO SPENDS⟧  `(3/2)^{log₂H} ≤ H^{24/41}` (the integer fact `3^{41} ≤ 2^{65}`), so
the head room against `H²` is `H^{17/41}` for the `(4/3)^{j₀}` summand and `H^{58/41}`
for the `(8/3)^{j₀}` one.  Both give the SAME floor `log H ≥ (log 2)·j₀` — the design's
"the floor's exponent HALVES". -/

/-- `log 3 ≤ (65/41)·log 2` and `(19/12)·log 2 ≤ log 3`: the two integer facts
`3^{41} ≤ 2^{65}` and `2^{19} ≤ 3^{12}` that price `(3/2)^L`, `(4/3)^{j₀}`, `(8/3)^{j₀}`
against `log 2`.  (`log₂3 = 1.5849625`, and `19/12 = 1.58333 < 1.5849625 < 1.58537 = 65/41`.) -/
theorem s13_log_three_bounds :
    Real.log 3 ≤ 65 / 41 * Real.log 2 ∧ 19 / 12 * Real.log 2 ≤ Real.log 3 := by
  have hup : (3 : ℝ) ^ (41 : ℕ) ≤ (2 : ℝ) ^ (65 : ℕ) := by norm_num
  have hlo : (2 : ℝ) ^ (19 : ℕ) ≤ (3 : ℝ) ^ (12 : ℕ) := by norm_num
  constructor
  · have h := Real.log_le_log (by positivity) hup
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  · have h := Real.log_le_log (by positivity) hlo
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith

/-- **⟦A-5⟧ THE SMALL-`j` THRESHOLD, DISCHARGED** (`s13_smallGradeFits`) — from ONE gate:

  `(7/10)·j₀ + 3·G ≤ log H`,   `G := log 9 + 84·loglog H + 2·log(strataResidual H) − log ρ` .

`G` is the whole non-`j₀` charge (the `Λ^{84}` envelope, the strata residual squared, and the
`ρ`-page's own `log(1/ρ)`); at the certified point `G ≈ 6.5·10³` against `(7/10)·j₀ ≈
1.43·10³²`, so the gate IS the `λ₋`-floor and nothing else. -/
theorem s13_smallGradeFits {R : ChowlaRegime} {j₀ H : ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hlo : R.Hlo ≤ H)
    (hgate : (7 / 10 : ℝ) * (j₀ : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log (H : ℝ))
            + 2 * Real.log (strataResidual H) - Real.log ρ)
      ≤ Real.log (H : ℝ)) :
    m4SmallGradeFits j₀ (fun H => 2 * RSanDoorRho ρ H) (fun H => 2 * rStrWitness H) H := by
  obtain ⟨hlog3up, hlog3lo⟩ := s13_log_three_bounds
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl20 : (0 : ℝ) < Real.log 2 := by linarith
  -- ⟦the window scale⟧
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH0 : (0 : ℝ) < (H : ℝ) := by
    have : (0 : ℕ) < H := by omega
    exact_mod_cast this
  set Λ : ℝ := Real.log (H : ℝ) with hΛdef
  have hLexp : Real.exp 1 ≤ Λ := exp_one_le_log_of_regime_le R hlo
  have hΛ1 : (2 : ℝ) < Λ := by
    have := Real.exp_one_gt_d9
    linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hlogΛ0 : (0 : ℝ) < Real.log Λ := Real.log_pos (by linarith)
  -- ⟦the arc scale, as a nat power⟧
  have harcpow : arcDen 12 H = Λ ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  set S : ℝ := strataResidual H with hSdef
  have hS1 : (1 : ℝ) ≤ S := by
    rw [hSdef, strataResidual]
    have := Real.log_nonneg harc1
    linarith
  have hS0 : (0 : ℝ) < S := by linarith
  have hlogS0 : (0 : ℝ) ≤ Real.log S := Real.log_nonneg hS1
  have hRSt : rStrWitness H = Λ ^ (84 : ℕ) := by
    rw [rStrWitness, harcpow, ← pow_mul]
    exact max_eq_right (one_le_pow₀ (by linarith))
  -- ⟦the dyadic index⟧
  set L : ℕ := Nat.log 2 H with hLdef
  have hLpow : ((2 : ℝ)) ^ L ≤ (H : ℝ) := by
    have h : (2 : ℕ) ^ L ≤ H := Nat.pow_log_le_self 2 (by omega)
    have h' : ((2 ^ L : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h
    simpa using h'
  have hLlog : (L : ℝ) * Real.log 2 ≤ Λ := by
    have h := Real.log_le_log (by positivity) hLpow
    rwa [Real.log_pow] at h
  -- ⟦the three log numerals⟧
  have hlog32 : Real.log (3 / 2 : ℝ) ≤ 24 / 41 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith
  have hlog320 : (0 : ℝ) ≤ Real.log (3 / 2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlog43 : Real.log (4 / 3 : ℝ) ≤ 2890 / 10000 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith
  have hlog83 : Real.log (8 / 3 : ℝ) ≤ 9825 / 10000 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith
  -- ⟦the `(3/2)^L` spend⟧
  have hu32 : (L : ℝ) * Real.log (3 / 2 : ℝ) ≤ 24 / 41 * Λ := by
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    calc (L : ℝ) * Real.log (3 / 2 : ℝ) ≤ (L : ℝ) * (24 / 41 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlog32 hL0
      _ = 24 / 41 * ((L : ℝ) * Real.log 2) := by ring
      _ ≤ 24 / 41 * Λ := by linarith
  -- ⟦`G ≥ 0`⟧
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hG0 : (0 : ℝ) ≤ Real.log 9 + 84 * Real.log Λ + 2 * Real.log S - Real.log ρ := by
    have h9 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    linarith
  have hj0 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg j₀
  -- ⟦the two claims, by log comparison⟧
  set Q : ℝ := (H : ℝ) ^ 2 * RSanDoorRho ρ H with hQdef
  have hRS : RSanDoorRho ρ H = ρ / S ^ 2 := rfl
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQdef, hRS]; positivity
  have hlogQ : Real.log Q = 2 * Λ + Real.log ρ - 2 * Real.log S := by
    rw [hQdef, hRS, Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hD0 : (0 : ℝ) < 2 * Λ ^ (84 : ℕ) := by positivity
  have hclaim1 : 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
      * (2 * Λ ^ (84 : ℕ)) ≤ Q := by
    have hP0 : (0 : ℝ) < 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
        * (2 * Λ ^ (84 : ℕ)) := by positivity
    have hlogP : Real.log (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
          * (2 * Λ ^ (84 : ℕ)))
        = Real.log (9 / 2) + (L : ℝ) * Real.log (3 / 2 : ℝ)
          + (j₀ : ℝ) * Real.log (4 / 3 : ℝ) + Λ
          + (Real.log 2 + 84 * Real.log Λ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hle : Real.log (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
        * (2 * Λ ^ (84 : ℕ))) ≤ Real.log Q := by
      rw [hlogP, hlogQ]
      have h92 : Real.log (9 / 2 : ℝ) + Real.log 2 = Real.log 9 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      have h43 : (j₀ : ℝ) * Real.log (4 / 3 : ℝ) ≤ (j₀ : ℝ) * (2890 / 10000) :=
        mul_le_mul_of_nonneg_left hlog43 hj0
      linarith
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hP0, Real.exp_log hQ0] at h
  have hclaim2 : 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀ * (2 * Λ ^ (84 : ℕ)) ≤ Q := by
    have hP0 : (0 : ℝ) < 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
        * (2 * Λ ^ (84 : ℕ)) := by positivity
    have hlogP : Real.log (9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
          * (2 * Λ ^ (84 : ℕ)))
        = Real.log (9 / 5) + (L : ℝ) * Real.log (3 / 2 : ℝ)
          + (j₀ : ℝ) * Real.log (8 / 3 : ℝ)
          + (Real.log 2 + 84 * Real.log Λ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hle : Real.log (9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀
        * (2 * Λ ^ (84 : ℕ))) ≤ Real.log Q := by
      rw [hlogP, hlogQ]
      have h95 : Real.log (9 / 5 : ℝ) + Real.log 2 ≤ Real.log 9 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        exact Real.log_le_log (by norm_num) (by norm_num)
      have h83 : (j₀ : ℝ) * Real.log (8 / 3 : ℝ) ≤ (j₀ : ℝ) * (9825 / 10000) :=
        mul_le_mul_of_nonneg_left hlog83 hj0
      linarith
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hP0, Real.exp_log hQ0] at h
  -- ⟦assemble through the landed threshold lemma⟧
  refine m4SmallGradeFits_of_threshold (D := 2 * Λ ^ (84 : ℕ)) (le_of_eq (by rw [hRSt])) ?_ ?_
  · have := RSanDoorRho_nonneg hρ0.le H
    linarith
  · rw [← hLdef]
    have hexpand : (9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ)
          + 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀) * (2 * Λ ^ (84 : ℕ))
        = 9 / 2 * ((3 : ℝ) / 2) ^ L * ((4 : ℝ) / 3) ^ j₀ * (H : ℝ) * (2 * Λ ^ (84 : ℕ))
          + 9 / 5 * ((3 : ℝ) / 2) ^ L * ((8 : ℝ) / 3) ^ j₀ * (2 * Λ ^ (84 : ℕ)) := by ring
    rw [hexpand]
    have : (H : ℝ) ^ 2 * (2 * RSanDoorRho ρ H) = 2 * Q := by rw [hQdef]; ring
    rw [this]
    linarith

/-! ## §6 — ⟦B⟧ `DoorRowZeroBase`'s FIVE NON-`coefWS` FIELDS

`S12Compose`'s `hbase5` hypothesis, verbatim.  Three of the five are the SAME scale floor the
door blocks already spend (`s13BlockFloor`), and the other two ARE the socket's own `j`-floor:
`calQK (Adoor M) (3072M) M 1 = 2^{M·Adoor M} = 2^{doorRowFloor M}` on the nose, so
`Q1_le_h` is `doorRowFloor M ≤ j` re-read, and `h_four` is its `2 ≤ j` shadow. -/

/-- `𝒬₁ = 2^{doorRowFloor M}` at the door family — the identity behind `Q1_le_h`. -/
theorem s13_calQK_door_one : ∀ M : ℕ, calQK (Adoor M) (3072 * M) M 1 = 2 ^ doorRowFloor M := by
  intro M
  rw [calQK, calE_one, doorRowFloor]
  ring_nf

/-- `𝒬₂ = 2^{16·A·G·M}` at the door family. -/
theorem s13_calQK_door_two : ∀ M : ℕ,
    calQK (Adoor M) (3072 * M) M 2 = 2 ^ (16 * (Adoor M * (3072 * M) * M)) := by
  intro M
  rw [calQK, calE_two]
  ring_nf

/-- **⟦B — `DoorRowZeroBase`'s FIVE NON-`coefWS` FIELDS, DISCHARGED⟧**
(`s13_doorRowZeroBase_five`) — `S12Compose.logChowla2_capstone_conditional`'s `hbase5`
conjunction at ONE base, from the scale floor and the socket's `j`-floor.

`reg` and `big` are literally `SieveBlockGate`'s second and third conjuncts at the base
(`s13_sieveBlockGate`), so the Mertens/Rankin page pays for the row bundle too. -/
theorem s13_doorRowZeroBase_five {M Xd j : ℕ} (hM : 1 ≤ M)
    (hXd : s13BlockFloor M ≤ Xd) (hj : doorRowFloor M ≤ j) :
    calQK (Adoor M) (3072 * M) M 2 ≤ Xd ∧
      Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
          ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) ∧
      (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧
      ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
  have hgate := s13_sieveBlockGate hM hXd
  have hAd1 : 1 ≤ Adoor M := by
    rw [Adoor]
    have : 0 < 2 ^ 36 * (Nat.log 2 M + 1) := by positivity
    omega
  have ht1 : 1 ≤ Adoor M * (3072 * M) * M := by
    have h1 : 1 ≤ 3072 * M := by omega
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ Adoor M * (3072 * M) * M := by
          exact Nat.mul_le_mul (Nat.mul_le_mul hAd1 h1) hM
  -- ⟦the door's `j`-floor, twice⟧
  have hjfl : doorRowFloor M ≤ j := hj
  have hj2 : 2 ≤ j := by
    have h36 : 2 ^ 36 ≤ Adoor M := by
      rw [Adoor]
      have h1 : 1 ≤ Nat.log 2 M + 1 := by omega
      calc 2 ^ 36 = 2 ^ 36 * 1 := by ring
        _ ≤ 2 ^ 36 * (Nat.log 2 M + 1) := Nat.mul_le_mul_left _ h1
    have hfl : 2 ^ 36 ≤ doorRowFloor M := by
      rw [doorRowFloor]
      calc 2 ^ 36 = 1 * 2 ^ 36 := by ring
        _ ≤ M * Adoor M := Nat.mul_le_mul hM h36
    have : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
    omega
  refine ⟨?_, hgate.2.2.1 2 (by simp), hgate.2.1, ?_, ?_⟩
  · -- ⟦`Q2_le`⟧ `2^{16·A·G·M} ≤ 2^{s13BlockExp M} ≤ X_d`
    rw [s13_calQK_door_two]
    have hstep : 16 * (Adoor M * (3072 * M) * M)
        ≤ 400 * (Adoor M * (3072 * M) * M) ^ 2 := by
      have h : (Adoor M * (3072 * M) * M) ^ 2 = (Adoor M * (3072 * M) * M)
          * (Adoor M * (3072 * M) * M) := by ring
      rw [h]
      calc 16 * (Adoor M * (3072 * M) * M) ≤ 400 * (Adoor M * (3072 * M) * M) := by omega
        _ = 400 * (Adoor M * (3072 * M) * M) * 1 := by ring
        _ ≤ 400 * (Adoor M * (3072 * M) * M) * (Adoor M * (3072 * M) * M) :=
            Nat.mul_le_mul_left _ ht1
        _ = 400 * ((Adoor M * (3072 * M) * M) * (Adoor M * (3072 * M) * M)) := by ring
    have hexp : 16 * (Adoor M * (3072 * M) * M) ≤ s13BlockExp M := by
      rw [s13BlockExp]; omega
    have hfl : (2 : ℕ) ^ (16 * (Adoor M * (3072 * M) * M)) ≤ s13BlockFloor M := by
      rw [s13BlockFloor]
      exact Nat.pow_le_pow_right (by norm_num) hexp
    exact le_trans hfl hXd
  · -- ⟦`h_four`⟧ `4 = 2^2 ≤ 2^j`
    have h : (2 : ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    have hR : ((2 ^ 2 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
    simpa using hR
  · -- ⟦`Q1_le_h`⟧ the socket's `j`-floor, verbatim
    rw [s13_calQK_door_one]
    have h : (2 : ℕ) ^ doorRowFloor M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact_mod_cast h

end Salt.MR

end
