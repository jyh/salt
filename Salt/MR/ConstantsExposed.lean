/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TypicalDensity

/-!
# THE EXPOSURE CERTIFICATE — `Cg` and `δ₀` as kernel numerals

CG-SCOPE's byte-read established that every constant feeding the spine's
`hMδ` floor `24·Cg/δ₀ ≤ M` is EFFECTIVE (no ineffective leaf anywhere in the
chain).  This file turns that read into *kernel arithmetic*: the closed forms
of `Cg` and of `δ₀` are given names, and their numeric bounds are proved by
`norm_num`/`nlinarith` on explicit numerals, so the endgame's feasibility
question becomes decidable in-tree.

## The provenance (byte-verified, CG-SCOPE 2026-07-30)

`Cg` is born at `Salt.MR.typical_density_le` (`TypicalDensity.lean`) as the
`refine` witness `1/(exp(-19/log 2)/2) + 1`, and passes through
`SieveGlue → M4Sieve → M4Door → M4Close` with zero inflation.

`δ₀` is born at `Salt.Entropy.Chowla.log_chowla_two_budget_head_g`
(`SpineFinal.lean`) as `cD3/(16·C) · ε / (2·K)`, over four leaves:

| leaf | site | value |
|---|---|---|
| `cD3` | `primeWindow_sum_inv_ge` (`WindowMertensLower.lean`) | `1/4` |
| `C`   | `circle_method_estimate (2·log 4)` (`CircleMethod.lean`) | `1 + 2·(2·log 4)` |
| `ε`   | `exists_rat_btwn` at `min` of four arms (`SpineFinal.lean`) | pinned to `1/500` |
| `K`   | `bigXi_bounded` (`GoldbachEnergyFinal.lean`) | `16·Cd/ε¹⁶` |

and `K`'s own subchain: `Cd = 2·K_lcm·C₁²·ε⁶` (`hsq_holds3`),
`K_lcm = exp(24·ζ(2)) = exp(4π²)` (`hFac2_lcm_sum_le`, `GoldbachEnergyHsq2.lean`),
`C₁ = CL + CS` (`hpt_holds`), `CL = 800/c₀ + 102400/ε²` at `c₀ = 1/64`
(`Salt.M3Assembly.exists_const_mainTermSum_ge`), and
`CS = (ε²H₁+1)²·(log H₁)²/(2ε²)` at `H₁ = max N0 (max tA (max tB tD))` with
`N0 = 2^100` (`Salt.M5BigO.N0`).

## The reachability caveat (READ THIS BEFORE CITING)

Every one of those sites states an `∃`, and every downstream consumer
`obtain`s the witness.  A witness destructed by `obtain` is a `Classical.choose`
that the kernel cannot evaluate, so the bounds below are proved AT THE CLOSED
FORM, not at the opaque constant of the landed `∃`.  The identification
"closed form = the landed `refine` witness" is a proof-term reading, not a
kernel fact — except for `Cg`, where `typical_density_le_bounded` re-derives
the landed conclusion with the numeral wired into the statement (the body is
short and cites only public lemmas, so the twin is cheap).  Closing the same
gap for `δ₀` is the lever program's job, not this file's.

Two further proof-term readings used in pinning `H₁ = 2^100`: the three
non-`N0` arms of `H₁` are `tA = ⌈4/ε²⌉₊ = 10^6` (`four_le_threshold`),
`tB = ⌈z₀^10⌉₊ + 1 = 10^20 + 1` at `z₀ = Salt.M3Assembly.z0 = 100`, and
`tD = ⌈(2/ε²)^(10/9)⌉₊ + 1 ≈ 2.2·10^6` (`rpow_ge_threshold`) — all below
`2^100`, so `N0` is the max.  The lemmas below are therefore stated for an
arbitrary `H₁ ≤ 2^100`.

## What is proved

* `Cg_le`         : `Cg ≤ 2·10^12`  (true value `1.605·10^12`)
* `eps_admissible`: `1/500` sits strictly below all four `ε`-arms
* `Klcm_le`       : `exp(24·ζ(2)) ≤ 1.5·10^17` (true value `1.397·10^17`)
* `KExpr_le`      : `K ≤ 1.2·10^162` (true value `1.041·10^162`)
* `delta0_ge`     : `10^(-168) ≤ δ₀` (true value `2.29·10^(-168)`)
* `b_floor_cert`  : `24·Cg/δ₀ ≤ 2^603` (true value `1.68·10^181 = 2^602.02`)

The last line is the wall: the spine's `hMδ` forces `M ≥ 2^603`, against the
DRIFT cap `b ≤ 88` at the `K = 9/2` tower.
-/

namespace Salt.MR

open Finset ArithmeticFunction BoundingSieve

open scoped BigOperators ArithmeticFunction.omega

set_option maxRecDepth 40000
set_option exponentiation.threshold 3000

/-! ## §1 The sieve-mass constant `Cg` -/

/-- **`Cg`**, verbatim the `refine` witness of `Salt.MR.typical_density_le`. -/
noncomputable def CgExpr : ℝ := 1 / (Real.exp (-19 / Real.log 2) / 2) + 1

/-- `exp 55 ≤ 8·10^23` — the squaring step's ceiling (`e ≤ 2.72`). -/
theorem exp_55_le : Real.exp 55 ≤ 8 * 10 ^ 23 := by
  have h1 : Real.exp 1 ≤ 2.72 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h2 : Real.exp 55 = Real.exp 1 ^ (55 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc Real.exp 1 ^ (55 : ℕ) ≤ (2.72 : ℝ) ^ (55 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 55
    _ ≤ 8 * 10 ^ 23 := by norm_num

/-- `exp(19/log 2) ≤ 9·10^11`.  `log 2 > 0.6931471803` puts the exponent below
`27.5`; squaring lands on `exp 55`. -/
theorem exp_nineteen_div_log_two_le : Real.exp (19 / Real.log 2) ≤ 9 * 10 ^ 11 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogpos : (0 : ℝ) < Real.log 2 := by linarith
  have ha : 19 / Real.log 2 ≤ 27.5 := by
    rw [div_le_iff₀ hlogpos]; nlinarith
  set y := Real.exp (19 / Real.log 2) with hy
  have hypos : 0 < y := Real.exp_pos _
  have hsq : y ^ 2 ≤ 8 * 10 ^ 23 := by
    have hyy : y ^ 2 = Real.exp (2 * (19 / Real.log 2)) := by
      rw [hy, ← Real.exp_nat_mul]; norm_num
    rw [hyy]
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) exp_55_le
  nlinarith [hsq, hypos]

/-- The closed form of `Cg`: `1/(exp(-19/log 2)/2) + 1 = 2·exp(19/log 2) + 1`. -/
theorem CgExpr_eq : CgExpr = 2 * Real.exp (19 / Real.log 2) + 1 := by
  have h : Real.exp (-19 / Real.log 2) = (Real.exp (19 / Real.log 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [CgExpr, h]
  have hpos : (0 : ℝ) < Real.exp (19 / Real.log 2) := Real.exp_pos _
  field_simp

/-- `0 < Cg`. -/
theorem CgExpr_pos : 0 < CgExpr := by
  rw [CgExpr_eq]; positivity

/-- **THE `Cg` CERTIFICATE**: `Cg ≤ 2·10^12` (the true value is `1.605·10^12`). -/
theorem Cg_le : CgExpr ≤ 2 * 10 ^ 12 := by
  rw [CgExpr_eq]
  have h := exp_nineteen_div_log_two_le
  norm_num
  linarith

/-- **THE WIRED TWIN of `Salt.MR.typical_density_le`** — the conjunct
`C ≤ 2·10^12` added to the landed statement, with the landed body replayed at
the same witness.  This is the one place in the certificate where the bound is
a kernel fact ABOUT THE THEOREM and not merely about a closed form: consumers
that `obtain` from this twin get the numeral for free.  Nothing in the landed
`typical_density_le` is touched. -/
theorem typical_density_le_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (P Q X : ℕ), 2 ≤ P → P ≤ Q →
        100 * Real.log Q ≤ Real.log X →
        ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (X : ℝ) * (Real.log P / Real.log Q) →
        (((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card : ℝ)
          ≤ C * (Real.log P / Real.log Q) * X := by
  have hc₄ : (0 : ℝ) < Real.exp (-19 / Real.log 2) / 2 := by positivity
  refine ⟨CgExpr, CgExpr_pos, Cg_le, ?_⟩
  intro P Q X hP hPQ hgate herr
  rw [CgExpr]
  set c₄ : ℝ := Real.exp (-19 / Real.log 2) / 2 with hc₄def
  have hP2 : 2 ≤ Q := le_trans hP hPQ
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hP2)
  have hXnn : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hGpos : 0 < Salt.SelbergPort.selbergBoundingSum (densSieve P Q X) :=
    Salt.SelbergPort.selbergBoundingSum_pos _
  have hG := densSieve_boundingSum_ge hP hPQ hgate
  rw [← hc₄def] at hG
  have hsel := Salt.SelbergPort.selberg_bound_simple (densSieve P Q X)
  rw [densSieve_siftedSum] at hsel
  simp only [densSieve_totalMass, densSieve_level, densSieve_prodPrimes] at hsel
  have hmain : (X : ℝ) / Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)
      ≤ (1 / c₄) * (Real.log P / Real.log Q) * X := by
    rw [div_le_iff₀ hGpos]
    have hcoef : (0 : ℝ) ≤ 1 / c₄ * (Real.log P / Real.log Q) * X := by positivity
    have hstep := mul_le_mul_of_nonneg_left hG hcoef
    have hid : 1 / c₄ * (Real.log P / Real.log Q) * X * (c₄ * (Real.log Q / Real.log P))
        = X := by
      field_simp
    linarith [hstep, hid]
  calc (((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card : ℝ)
      ≤ (X : ℝ) / Salt.SelbergPort.selbergBoundingSum (densSieve P Q X)
          + ∑ d ∈ (bandProd P Q).divisors,
              (if (d : ℝ) ≤ (Nat.sqrt X : ℝ) + 1
                then (3 : ℝ) ^ (ω d) * |(densSieve P Q X).rem d| else 0) := hsel
    _ ≤ (1 / c₄) * (Real.log P / Real.log Q) * X
          + ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ)) := by
        gcongr
        exact densSieve_error_le P Q X
    _ ≤ (1 / c₄) * (Real.log P / Real.log Q) * X + (X : ℝ) * (Real.log P / Real.log Q) := by
        linarith [herr]
    _ = (1 / c₄ + 1) * (Real.log P / Real.log Q) * X := by ring

/-! ## §2 The `ε` pin and the circle-method constant `C` -/

/-- The pinned `ε`.  `SpineFinal` chooses `ε` by `exists_rat_btwn` below the
four-fold `min`; `eps_admissible` certifies that `1/500` is a legal choice. -/
def epsPin : ℚ := 1 / 500

@[simp] lemma epsPin_cast : ((epsPin : ℚ) : ℝ) = 1 / 500 := by norm_num [epsPin]

/-- **`C`**, the circle-method constant: `circle_method_estimate`'s witness
`1 + 2·C₀` at the spine's `C₀ = 2·log 4`. -/
noncomputable def CcmExpr : ℝ := 1 + 2 * (2 * Real.log 4)

private lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

/-- `0 < C`. -/
theorem CcmExpr_pos : 0 < CcmExpr := by
  have h : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  rw [CcmExpr]; linarith

/-- `C = 1 + 8·log 2 ≤ 6.55` (true value `6.5452`). -/
theorem CcmExpr_le : CcmExpr ≤ 655 / 100 := by
  have h : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [CcmExpr, log_four_eq]; linarith

/-- **THE `ε` PIN**: `1/500` is strictly below all four arms of `SpineFinal`'s
`min` (at the leaf values `cE = cD3 = 1/4` and `C = CcmExpr`), so it is a legal
`exists_rat_btwn` choice.  The binding arm is the fourth, `cD3/(16C) ≈ 0.0023873`. -/
theorem eps_admissible :
    ((epsPin : ℚ) : ℝ) <
      min (min (min ((1 / 4 : ℝ) / (32 * Real.log 4)) (1 / 2)) ((1 / 4 : ℝ) / 16))
        ((1 / 4 : ℝ) / (16 * CcmExpr)) := by
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := log_four_eq
  have h4pos : (0 : ℝ) < Real.log 4 := by rw [hlog4]; linarith
  have hCpos : 0 < CcmExpr := CcmExpr_pos
  rw [epsPin_cast]
  refine lt_min (lt_min (lt_min ?_ ?_) ?_) ?_
  · rw [lt_div_iff₀ (by linarith)]
    rw [hlog4]; linarith
  · norm_num
  · norm_num
  · rw [lt_div_iff₀ (by linarith)]
    rw [CcmExpr, hlog4]; linarith

/-! ## §3 The `δ₀` chain: `K_lcm`, `CL`, `CS`, `C₁`, `Cd`, `K` -/

/-- **`K_lcm`**, the doubled Euler-product majorant of `hFac2_lcm_sum_le`,
verbatim its `refine` witness `exp(24·∑' 1/n²)`. -/
noncomputable def KlcmExpr : ℝ := Real.exp (24 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2)

/-- `K_lcm = exp(4π²)` (Basel: the `ℕ`-indexed tsum is `ζ(2) = π²/6`, the `n = 0`
term being `1/0 = 0`). -/
theorem KlcmExpr_eq : KlcmExpr = Real.exp (4 * Real.pi ^ 2) := by
  rw [KlcmExpr, hasSum_zeta_two.tsum_eq]; congr 1; ring

/-- `exp 79 ≤ 2.2·10^34` — the squaring step's ceiling for `K_lcm`. -/
theorem exp_79_le : Real.exp 79 ≤ 22 * 10 ^ 33 := by
  have h1 : Real.exp 1 ≤ 2.72 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h2 : Real.exp 79 = Real.exp 1 ^ (79 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc Real.exp 1 ^ (79 : ℕ) ≤ (2.72 : ℝ) ^ (79 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 79
    _ ≤ 22 * 10 ^ 33 := by norm_num

/-- `0 < K_lcm`. -/
theorem KlcmExpr_pos : 0 < KlcmExpr := Real.exp_pos _

/-- **THE `K_lcm` CERTIFICATE**: `exp(24·ζ(2)) ≤ 1.5·10^17` (true value
`1.397·10^17`).  Route: `8π² ≤ 79` from `π < 3.141593`, then squaring. -/
theorem Klcm_le : KlcmExpr ≤ 15 * 10 ^ 16 := by
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [KlcmExpr_eq]
  set y := Real.exp (4 * Real.pi ^ 2) with hy
  have hypos : 0 < y := Real.exp_pos _
  have h2 : y ^ 2 ≤ 22 * 10 ^ 33 := by
    have hyy : y ^ 2 = Real.exp (2 * (4 * Real.pi ^ 2)) := by
      rw [hy, ← Real.exp_nat_mul]; norm_num
    rw [hyy]
    exact le_trans (Real.exp_le_exp.mpr (by nlinarith)) exp_79_le
  nlinarith [h2, hypos]

/-- **`CL`**, the large-`H` arm of `hpt_holds`'s `C₁`: `800/c₀ + 102400/ε²` at
`c₀ = 1/64` (`Salt.M3Assembly.exists_const_mainTermSum_ge`'s witness). -/
noncomputable def CLExpr : ℝ := 800 / (1 / 64) + 102400 / (epsPin : ℝ) ^ 2

/-- `CL = 25600051200` exactly at the pin — 35 bits, negligible beside `CS`. -/
theorem CLExpr_eq : CLExpr = 25600051200 := by rw [CLExpr, epsPin_cast]; norm_num

/-- **`CS`**, the small-`H` absorption arm of `hpt_holds`'s `C₁`:
`(ε²H₁+1)²·(log H₁)²/(2ε²)`.  This is where `N0 = 2^100` enters — the single
largest bit source in the whole floor. -/
noncomputable def CSExpr (H₁ : ℕ) : ℝ :=
  ((epsPin : ℝ) ^ 2 * H₁ + 1) ^ 2 * (Real.log H₁) ^ 2 / (2 * (epsPin : ℝ) ^ 2)

/-- `0 ≤ CS`. -/
theorem CSExpr_nonneg (H₁ : ℕ) : 0 ≤ CSExpr H₁ := by
  rw [CSExpr, epsPin_cast]; positivity

/-- **THE `CS` CERTIFICATE** at any `H₁ ≤ 2^100`: `CS ≤ 1.55·10^58` (true value
at `H₁ = 2^100`: `1.544·10^58`). -/
theorem CSExpr_le {H₁ : ℕ} (h1 : 1 ≤ H₁) (h2 : H₁ ≤ 2 ^ 100) :
    CSExpr H₁ ≤ 155 * 10 ^ 56 := by
  have hHR : (H₁ : ℝ) ≤ 2 ^ 100 := by exact_mod_cast h2
  have hH1R : (1 : ℝ) ≤ (H₁ : ℝ) := by exact_mod_cast h1
  have hlognn : 0 ≤ Real.log (H₁ : ℝ) := Real.log_nonneg hH1R
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog : Real.log (H₁ : ℝ) ≤ 69.315 := by
    have h := Real.log_le_log (by linarith) hHR
    have he : Real.log ((2 : ℝ) ^ 100) = 100 * Real.log 2 := by
      rw [Real.log_pow]; norm_num
    rw [he] at h
    linarith
  have hlogsq : (Real.log (H₁ : ℝ)) ^ 2 ≤ 4805 := by nlinarith
  have hA : (epsPin : ℝ) ^ 2 * (H₁ : ℝ) + 1 ≤ 50706025 * 10 ^ 17 := by
    rw [epsPin_cast]; nlinarith [hHR]
  have hAnn : (0 : ℝ) ≤ (epsPin : ℝ) ^ 2 * (H₁ : ℝ) + 1 := by
    rw [epsPin_cast]; positivity
  have hAsq : ((epsPin : ℝ) ^ 2 * (H₁ : ℝ) + 1) ^ 2 ≤ (50706025 * 10 ^ 17 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hAnn hA 2
  rw [CSExpr, epsPin_cast]
  have hden : (2 : ℝ) * (1 / 500) ^ 2 = 1 / 125000 := by norm_num
  rw [hden, div_eq_mul_inv, show ((1 : ℝ) / 125000)⁻¹ = 125000 by norm_num]
  have hstep : ((1 / 500 : ℝ) ^ 2 * (H₁ : ℝ) + 1) ^ 2 * (Real.log (H₁ : ℝ)) ^ 2
      ≤ (50706025 * 10 ^ 17 : ℝ) ^ 2 * 4805 := by
    have h1' : ((1 / 500 : ℝ) ^ 2 * (H₁ : ℝ) + 1) ^ 2 ≤ (50706025 * 10 ^ 17 : ℝ) ^ 2 := by
      rw [epsPin_cast] at hAsq; exact hAsq
    nlinarith [sq_nonneg (Real.log (H₁ : ℝ)), hlogsq, h1',
      sq_nonneg ((1 / 500 : ℝ) ^ 2 * (H₁ : ℝ) + 1)]
  nlinarith [hstep]

/-- **`C₁ = CL + CS`**, the representation-count constant of `hpt_holds`. -/
noncomputable def C1Expr (H₁ : ℕ) : ℝ := CLExpr + CSExpr H₁

/-- `0 < C₁`. -/
theorem C1Expr_pos (H₁ : ℕ) : 0 < C1Expr H₁ := by
  have h := CSExpr_nonneg H₁
  rw [C1Expr, CLExpr_eq]; linarith

/-- **THE `C₁` CERTIFICATE** at any `H₁ ≤ 2^100`: `C₁ ≤ 1.551·10^58`. -/
theorem C1Expr_le {H₁ : ℕ} (h1 : 1 ≤ H₁) (h2 : H₁ ≤ 2 ^ 100) :
    C1Expr H₁ ≤ 1551 * 10 ^ 55 := by
  have h := CSExpr_le h1 h2
  rw [C1Expr, CLExpr_eq]
  norm_num
  linarith

/-- **`Cd`**, the additive-energy constant of `hsq_holds3`:
`2·K_lcm·C₁²·ε⁶`. -/
noncomputable def CdExpr (H₁ : ℕ) : ℝ := 2 * KlcmExpr * (C1Expr H₁) ^ 2 * (epsPin : ℝ) ^ 6

/-- **`K`**, the large-spectrum bound of `bigXi_bounded_of_sieve`:
`16·Cd/ε¹⁶`. -/
noncomputable def KExpr (H₁ : ℕ) : ℝ := 16 * CdExpr H₁ / (epsPin : ℝ) ^ 16

/-- `K = 3.125·10^28 · K_lcm · C₁²` — the `ε⁶/ε¹⁶` collapse at the pin
(`32·500^10 = 3.125·10^28`). -/
theorem KExpr_eq (H₁ : ℕ) : KExpr H₁ = 3125 * 10 ^ 25 * (KlcmExpr * (C1Expr H₁) ^ 2) := by
  rw [KExpr, CdExpr, epsPin_cast]
  norm_num
  ring

/-- `0 < K`. -/
theorem KExpr_pos (H₁ : ℕ) : 0 < KExpr H₁ := by
  have h1 := KlcmExpr_pos
  have h2 := C1Expr_pos H₁
  rw [KExpr_eq]; positivity

/-- **THE `K` CERTIFICATE** at any `H₁ ≤ 2^100`: `K ≤ 1.2·10^162` (true value
`1.041·10^162`).  This is the constant that divides the spine's budget. -/
theorem KExpr_le {H₁ : ℕ} (h1 : 1 ≤ H₁) (h2 : H₁ ≤ 2 ^ 100) :
    KExpr H₁ ≤ 12 * 10 ^ 161 := by
  have hK := Klcm_le
  have hKpos := KlcmExpr_pos
  have hC := C1Expr_le h1 h2
  have hCpos := C1Expr_pos H₁
  have hCsq : (C1Expr H₁) ^ 2 ≤ (1551 * 10 ^ 55 : ℝ) ^ 2 := pow_le_pow_left₀ hCpos.le hC 2
  have hprod : KlcmExpr * (C1Expr H₁) ^ 2
      ≤ (15 * 10 ^ 16 : ℝ) * (1551 * 10 ^ 55 : ℝ) ^ 2 := by
    have hsqnn : (0 : ℝ) ≤ (C1Expr H₁) ^ 2 := sq_nonneg _
    nlinarith [hK, hKpos, hCsq, hsqnn]
  rw [KExpr_eq]
  nlinarith [hprod]

/-! ## §4 `δ₀` and the composite floor -/

/-- **`δ₀`**, verbatim `SpineFinal.log_chowla_two_budget_head_g`'s `refine`
witness `cD3/(16·C) · ε / (2·K)` at `cD3 = 1/4`. -/
noncomputable def delta0Expr (H₁ : ℕ) : ℝ :=
  (1 / 4 : ℝ) / (16 * CcmExpr) * (epsPin : ℝ) / (2 * KExpr H₁)

/-- The collapsed form: `δ₀ = 1/(64000·C·K)`. -/
theorem delta0Expr_eq (H₁ : ℕ) : delta0Expr H₁ = 1 / (64000 * CcmExpr * KExpr H₁) := by
  have hC := CcmExpr_pos
  have hK := KExpr_pos H₁
  rw [delta0Expr, epsPin_cast]
  field_simp
  ring

/-- `0 < δ₀`. -/
theorem delta0Expr_pos (H₁ : ℕ) : 0 < delta0Expr H₁ := by
  have hC := CcmExpr_pos
  have hK := KExpr_pos H₁
  rw [delta0Expr_eq]; positivity

/-- **THE `δ₀` CERTIFICATE** at any `H₁ ≤ 2^100`: `10^(-168) ≤ δ₀` (true value
`2.293·10^(-168)`; `log₂(1/δ₀) = 556.7`). -/
theorem delta0_ge {H₁ : ℕ} (h1 : 1 ≤ H₁) (h2 : H₁ ≤ 2 ^ 100) :
    1 / 10 ^ 168 ≤ delta0Expr H₁ := by
  have hC := CcmExpr_pos
  have hCle := CcmExpr_le
  have hK := KExpr_pos H₁
  have hKle := KExpr_le h1 h2
  have hden : 64000 * CcmExpr * KExpr H₁ ≤ 10 ^ 168 := by nlinarith
  have hdenpos : (0 : ℝ) < 64000 * CcmExpr * KExpr H₁ := by positivity
  rw [delta0Expr_eq]
  exact one_div_le_one_div_of_le hdenpos hden

/-- **THE COMPOSITE FLOOR CERTIFICATE**: `24·Cg/δ₀ ≤ 2^603`.

This is the number the S11 compose must beat.  The true value is
`1.68·10^181 = 2^602.02`; the certificate's roundings cost less than one bit.
Against the DRIFT cap (`b ≤ 88` at the `K = 9/2` tower, `b ≤ 250` at the
tower's continuum truth `4.0`) the spine's `hMδ` is short by ~350 bits. -/
theorem b_floor_cert {H₁ : ℕ} (h1 : 1 ≤ H₁) (h2 : H₁ ≤ 2 ^ 100) :
    24 * CgExpr / delta0Expr H₁ ≤ 2 ^ 603 := by
  have hCg := Cg_le
  have hCgpos := CgExpr_pos
  have hC := CcmExpr_pos
  have hCle := CcmExpr_le
  have hK := KExpr_pos H₁
  have hKle := KExpr_le h1 h2
  rw [delta0Expr_eq, one_div, div_inv_eq_mul]
  have hstep : 24 * CgExpr * (64000 * CcmExpr * KExpr H₁)
      ≤ 24 * (2 * 10 ^ 12) * (64000 * (655 / 100) * (12 * 10 ^ 161)) := by
    have h1' : CcmExpr * KExpr H₁ ≤ (655 / 100 : ℝ) * (12 * 10 ^ 161) := by nlinarith
    nlinarith [hCg, hCgpos, h1', hC, hK]
  refine le_trans hstep ?_
  norm_num

end Salt.MR
