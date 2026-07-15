/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenRows1
import Salt.Chen.ChenRows2
import Salt.Chen.MiddleK
import Salt.Chen.Headline3
import Salt.Chen.PDiag
import Salt.Chen.HeadlineW2

/-!
# Node fin8b — F2: the dichotomy dischargers → the consumer price slots

Design: `docs/blueprints/flags.md`, the `fin8a`/`fin8`/`fin7a`/`fin7b`/`PRICE-3b` entries and
the consumer `hBVblocksW_discharge'` (`PDiag.lean:682`) + the composition route
`CompositionSanity` (`PDiag.lean:782` → `mainA3_of_block_remainders_W` → the `hA3` shape).

**Scope (fin8b, the hA3 side).**  This file lands the *dichotomy dischargers*: closed
per-`(k,i)` (box) / per-`k` (sym/low) price terms that discharge the consumer's
`hprice`/`hpriceSym`/`hpriceLow` slots at the frozen operating point (`z := opZ x`,
`y := opY x`, `Ps := opPs x`, `Q := opQ`, `a := opA`, `QR := 1`, `Dlev := opDlev x`,
`D := opQ·opDlev x` — making the caller row `hDbnd` reflexive).

**The operating conductor.**  With `QR := 1` and `D := opQ·opDlev x`, the caller conductor
row `hDbnd : (opQ:ℝ)·(QR·Dlev) ≤ (D:ℝ)` is `(opQ·opDlev : ℝ) ≤ (opQ·opDlev : ℝ)` — reflexive.
The band `habs` residual is discharged at the call sites via `Headline3.band_habs_row`.

**The box dichotomy** (this node's first deliverable, `box_price_at_op`).  Each box `i` in
`dyadicBoundary (pieceN k) (pieceM k) (x/2+1) x (opZ x·opY x) K` is EITHER
* VANISHING — `2^i ≥ min (opZ x·pieceN k + 1) (x+1)` (the carrier cap): the doubly-restricted
  box carrier is `0` (`PriceClose.box_carrier_eq_zero_above_cap`), so the two-`T` sum is `0`; OR
* LIVE — `2^i < min (opZ x·pieceN k + 1) (x+1) ≤ opZ x·pieceN k + 1`: then the k-floor
  `kfloor_of_live_box` gives `x^{7/16}/8 ≤ 2^k` (so `2 ≤ k`), `box_rows_at_op` discharges the
  18 analytic rows, and `ChenHeadline.box_hprice_at_2pow_lo` prices the box by the Kerr term
  `boxPriceKerr Kc k i`.
The single closed price term `boxPriceKerr Kc k i` (Kc from `box_hprice_at_2pow_lo`, obtained
per-`x` since the carrier scale is `opZ x`) bounds BOTH branches (vanish: `0 ≤` nonneg price).

Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.

## The still-un-built numeric cores (recorded for fin8c / a re-scope — see the report)

The consumer also needs `hSum` (aggregate the per-box/per-piece prices into `Ccon·K·x/L^{11}`),
`hCE` (the `blockConvErrW` crumb `≤ Ccon·K·x/L^{11}`) and `hdiag`'s tower crumb
(`2^{Nat.log opW' x} ≤ x^{1/7}`-scale).  A corpus-wide grep confirms NO supporting tooling
exists for any of the three: `hNum_close_of_tower` (PriceClose) takes `RHD ≤ Ccon·K·x/L^{11}`
and `RCE ≤ Ccon·K·x/L^{11}` as HYPOTHESES; the Kerr forms `Kbeta_min`/`Km_min`/`Kbeta'_min`
have only nonnegativity lemmas; `blockConvErrW` has only `hconv_nn`.  These three are fresh,
node-sized operating-point estimates (the `PRICE-3`/`GLU-2W-fin` scoping finding, at its final
layer), not the wiring this file lands.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## The closed box price term -/

/-- **`boxPriceKerr` — the closed box price** (the `hprice`-slot value for box `(k,i)`).
Character-for-character the RHS of `ChenHeadline.box_hprice_at_2pow_lo` at `X = 2^{i+1}−1`,
`M = pieceM k`, `logN = log 2^k`.  Depends on `Kc` (the terminal's price constant, obtained
per-`x` at the operating carrier scale `opZ x`). -/
noncomputable def boxPriceKerr (Kc : ℝ) (k i : ℕ) : ℝ :=
  2 * ((Kbeta_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
        + (6 * (Km_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                  (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
            + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                * Kbeta'_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
      * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
      / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ))

/-- `boxPriceKerr` is nonnegative (`Kc ≥ 0`, all logs of `≥ 1` arguments are `≥ 0`, the
constants are positive). -/
theorem boxPriceKerr_nonneg {Kc : ℝ} (hKc : 0 ≤ Kc) (k i : ℕ) : 0 ≤ boxPriceKerr Kc k i := by
  unfold boxPriceKerr
  have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
    have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hM1 : (1 : ℕ) ≤ pieceM k := by
    have := two_pow_le_pieceM k
    have : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hXR : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1
  have hMR : (1 : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast hM1
  have hXM1 : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
          apply mul_le_mul hXR hMR (by norm_num) (by linarith)
  have hL0 : (0 : ℝ) ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) :=
    Real.log_nonneg hXM1
  have hlogN0 : (0 : ℝ) ≤ Real.log ((2 ^ k : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this
  have hkb := Kbeta_min_nonneg (K := Kc)
    (L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
    (logN := Real.log ((2 ^ k : ℕ) : ℝ)) (A := 13) (C0 := 18) hKc hL0 hlogN0
  have hkm := Km_min_nonneg (K := Kc)
    (L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
    (logN := Real.log ((2 ^ k : ℕ) : ℝ)) (A := 13) (C0 := 18) hKc hL0 hlogN0
  have hkb' := Kbeta'_min_nonneg (K := Kc)
    (L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
    (logN := Real.log ((2 ^ k : ℕ) : ℝ)) (A := 13) (C0 := 18) hKc hL0 hlogN0
  have hbracket : (0 : ℝ) ≤ Kbeta_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
        + (6 * (Km_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                  (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
            + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                * Kbeta'_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)) := by
    have h26 : (0 : ℝ) ≤ Real.sqrt 26 := Real.sqrt_nonneg _
    have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ ((13 : ℝ) + 5) := by positivity
    nlinarith [hkb, hkm, hkb', h26, h2p]
  have hXMnn : (0 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by positivity
  have hLpow : (0 : ℝ) ≤ (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ) :=
    Real.rpow_nonneg hL0 _
  exact mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hbracket hXMnn) hLpow)

/-! ## The box dichotomy discharger

`box_price_at_op` proves the consumer's box `hprice` slot: for a generic conductor `D` in the
operating range (`x^{11/24}/8 ≤ D ≤ x^{499/1000}`, `opQ·(QR·Dlev) ≤ D`), EVERY box of the
pieceN-boundary is bounded by the single closed price `boxPriceKerr Kc k i` — vanishing boxes
(`2^i ≥ cap`) by `box_carrier_eq_zero_above_cap` (LHS `= 0 ≤` nonneg price), live boxes
(`2^i < cap`) by `box_rows_at_op ∘ medium_box_price_at_op_lo` (via `kfloor_of_live_box`).  The
constant `Kc` and `N₀` are the argument-free terminal's globals, so the `N₀ ≤ 2^k` floor folds
into the uniform threshold `x₁`. -/

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`box_price_at_op` (fin8b, the box dichotomy discharger).**  The consumer's box `hprice`
slot at the operating point.  `QR Dlev D` are the operating conductor (fin8b sets `QR = 1`,
`Dlev = opDlev x`, `D = opQ·opDlev x`, making `hDbnd` reflexive).  Returns the closed price
`fun _ k i => boxPriceKerr Kc k i` and its per-box bound over the full pieceN-boundary. -/
theorem box_price_at_op (Ps : ℕ) (hPspos : 0 < Ps) (hQPs : Nat.Coprime opQ Ps)
    (hQa2 : Nat.Coprime opQ (opA + 2)) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (K : ℕ) (QR : ℝ) (Dlev D : ℕ)
    (hDbnd : (opQ : ℝ) * (QR * (Dlev : ℝ)) ≤ (D : ℝ)) :
    ∃ (Kc x₁ : ℝ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ), x₁ ≤ (x : ℝ) →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000) →
        ∀ (j k i : ℕ),
          i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) K →
          (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => opQ * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ x) (opY x) ε₀ j) 0
                    (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW opQ (m / opQ) opA) m x‖)
            + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                  (fun d => opQ * d),
                ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ x) (opY x) ε₀ j) 0
                      (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                    (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                    (crtClassW opQ (m / opQ) opA) m (x / 2 + 1)‖)
            ≤ boxPriceKerr Kc k i := by
  classical
  obtain ⟨Kc, N₀, hK0, hcore⟩ := medium_box_price_at_op_lo
  obtain ⟨xrows, hrows⟩ := box_rows_at_op
  have hQ1 : 1 ≤ opQ := opf_Q_pos
  -- the uniform threshold: past `xrows`, `exp(10^9)`, and where `x^{7/16}/8 ≥ max N₀ 2` (⟹ `2 ≤ k`
  -- and `N₀ ≤ 2^k` for every live box)
  refine ⟨Kc, max (max xrows (Real.exp (10 ^ 9))) (((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7)),
    hK0, fun x ε₀ hx₁ hDlo hDhi j k i hi => ?_⟩
  have hxrows : xrows ≤ (x : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx₁
  have hxexp : Real.exp (10 ^ 9) ≤ (x : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx₁
  have hxN₀ : ((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7) ≤ (x : ℝ) := le_trans (le_max_right _ _) hx₁
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hxexp
  have hexp1 : (1 : ℝ) ≤ Real.exp (10 ^ 9) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := le_trans hexp1 hxexp
  -- `x^{7/16}/8`: the live-box floor, `≥ N₀ + 2` past the threshold
  have hzR : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [opZ]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  -- the carrier cap
  set c : ℕ := min (opZ x * pieceN k + 1) (x + 1) with hc
  by_cases hlive : c ≤ 2 ^ i
  · -- VANISHING branch: `2^i ≥ cap` ⟹ carrier `= 0` ⟹ both sums `= 0`
    have hvanish : ∀ (T : ℕ), (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => opQ * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ x) (opY x) ε₀ j) 0 c)
                (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
              (crtClassW opQ (m / opQ) opA) m T‖) = 0 := by
      intro T
      apply Finset.sum_eq_zero
      intro m _
      rw [box_carrier_eq_zero_above_cap (α := blockAlpha (opZ x) (opY x) ε₀ j) hlive
        (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k) (crtClassW opQ (m / opQ) opA) m T,
        norm_zero]
    rw [hvanish x, hvanish (x / 2 + 1), add_zero]
    exact boxPriceKerr_nonneg hK0.le k i
  · -- LIVE branch: `2^i < cap ≤ opZ x·pieceN k + 1`
    rw [not_le] at hlive
    have hlive' : 2 ^ i < opZ x * pieceN k + 1 :=
      lt_of_lt_of_le hlive (le_trans (min_le_left _ _) (le_refl _))
    -- the 7/16 k-floor
    have hkf : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ) :=
      kfloor_of_live_box hx1R hi hlive' hzR
    -- `x^{7/16}/8 ≥ N₀ + 4` past the threshold
    have hfloorbig : ((N₀ + 4 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) / 8 := by
      have h8 : ((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7) ≤ (x : ℝ) := hxN₀
      have hbase : (0 : ℝ) ≤ ((8 * (N₀ + 4) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpow : ((8 * (N₀ + 4) : ℕ) : ℝ) = (((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7)) ^ ((7 : ℝ) / 16) := by
        rw [← Real.rpow_mul hbase, show (16 : ℝ) / 7 * ((7 : ℝ) / 16) = 1 by norm_num, Real.rpow_one]
      have hmono : (((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7)) ^ ((7 : ℝ) / 16) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hbase _) h8 (by norm_num)
      have h816 : ((8 * (N₀ + 4) : ℕ) : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) := by rw [hpow]; exact hmono
      have hcast : ((8 * (N₀ + 4) : ℕ) : ℝ) = 8 * ((N₀ + 4 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast] at h816
      linarith
    have hN₀2R : ((N₀ + 4 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := le_trans hfloorbig hkf
    have hN₀2 : N₀ + 4 ≤ 2 ^ k := by exact_mod_cast hN₀2R
    have hk : 2 ≤ k := by
      by_contra hk2
      rw [not_le] at hk2
      have hle : (2 : ℕ) ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [pow_one] at hle
      omega
    have hN₀ : N₀ ≤ 2 ^ k := by omega
    -- the 18 analytic rows
    obtain ⟨hxt, hNfloor, hL2, hX2, hD1, hDge_x, hDscale, hDsq, habs, hXsqrt, hMsqrt,
        herr_lev, herr_Mlev, hFX, hDx, hLbb, hfloor, hDXM⟩ :=
      hrows x hxrows k i (2 ^ (i + 1) - 1) (opZ x * opY x) K D (Real.log (4 * (x : ℝ)))
        rfl hi rfl hlive' rfl hDlo hDhi
    -- the carrier / Dset bookkeeping (verbatim `box_hprice_at_2pow_lo` body)
    have hα := norm_box_leg_le_one (opZ x) (opY x) ε₀ j (min (opZ x * pieceN k + 1) (x + 1)) i
    have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
        (fun d => opQ * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
    have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
        (fun d => opQ * d), Nat.Coprime (crtClassW opQ (m / opQ) opA) m :=
      fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
    have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
        (fun d => opQ * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
    unfold boxPriceKerr
    rw [two_mul]
    exact add_le_add
      (hcore x (Real.log (4 * (x : ℝ))) (opZ x * opY x) K k i _ (2 ^ (i + 1) - 1) x D _
        (fun m => crtClassW opQ (m / opQ) opA) hk hxt hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀ hL2
        hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor hDXM)
      (hcore x (Real.log (4 * (x : ℝ))) (opZ x * opY x) K k i _ (2 ^ (i + 1) - 1) (x / 2 + 1) D _
        (fun m => crtClassW opQ (m / opQ) opA) hk hxt hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀ hL2
        hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor hDXM)

end Salt.Chen
