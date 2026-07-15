/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AssembleA3
import Salt.Chen.PriceThree

/-!
# Node SYMLOW — the sym and low dichotomy dischargers → the consumer PsymK/PlowK slots

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin8b` entry (the ARG-FREE `Kc`/`N₀`
extraction trick + the templated plan: low = 2 regimes, no reconciliation; sym = 3 regimes with
the ONE reconciliation `z·max y (pieceN k) ≥ z·y`) and the `box_price_at_op` template
(`AssembleA3.lean`).

This file mirrors `box_price_at_op` for the sym/low band legs, producing `sym_price_at_op` and
`low_price_at_op` — the closed `PlowK`/`PsymK` per-piece terms whose conclusions are
character-for-character the `hpriceSym`/`hpriceLow` slots of `hBVblocksW_discharge'`
(`PDiag.lean:682`).

**The arg-free trick (mirrors `box_price_at_op`).**  The band feeders `sym_box_hprice_at_2pow_band`
/ `low_box_hprice_at_2pow_band` (`ChenFinal2`) and `middle_k_price` (`MiddleK`) fix `z`/`y`/`Ps`
OUTSIDE their `∀ x`, so their `Kc`/`N₀` are nominally per-`x` — unusable when the operating point
sets `z := opZ x`, `y := opY x`.  The fix: extract `Kb`/`N₀b` from the ARG-FREE terminal
`medium_box_price_at_op_band` (for the collapse/low legs, indicator `blockPrimeInd (pieceN k)`,
price at `log 2^k`) and `Km`/`N₀m` from `middle_medium_box_price_at_y` (for the middle `k`,
indicator `blockPrimeInd y`, price at `log y`), then replicate the row derivations of
`sym_rows_at_op`/`low_rows_at_op`/`middle_k_price` inline at `z := opZ x`, `y := opY x`.  The row
constants fold `N₀ ≤ 2^k` (resp. `≤ y`) into the uniform threshold `x₁` via `band_kfloor_of_live`.

**The regime tables.**

* `low_price_at_op` (2 regimes per `k`):
  - VANISH (`pieceN k ≤ opY x`): `blockAlphaLow` ≡ 0 (`blockAlphaLow_eq_zero_of_pieceN_le`), so
    the T-difference is `0`, priced by the nonneg `lowPriceK`.
  - LIVE (`opY x < pieceN k`): the per-box two-`T` price (`medium_box_price_at_op_band` twice,
    carrier `restrictAlpha (restrictAlpha (blockAlphaLow …)) …`, `norm_low_leg_le_one`) fed to
    `low_box_price_at_op`'s `box_disc_three_way` composition → the `hpriceLow` T-difference.

* `sym_price_at_op` (3 regimes per `k`):
  - VANISH (`pieceM k ≤ opY x`): `blockAlphaSym` ≡ 0 (`blockAlphaSym_eq_zero_of_pieceM_le`), the
    T-difference is `0`.
  - MIDDLE (`pieceN k < opY x < pieceM k`): indicator `blockPrimeInd (max y (pieceN k)) =
    blockPrimeInd y`, price at `log y` via `middle_medium_box_price_at_y`; `Km`.
  - COLLAPSE (`opY x ≤ pieceN k`): `max y (pieceN k) = pieceN k`, price at `log 2^k` via
    `medium_box_price_at_op_band`; `Kb`.  THE RECONCILIATION: `sym_box_price_at_op` ranges over
    `dyadicBoundary (max y (pieceN k)) … (z·max y (pieceN k))`; at the collapse `max = pieceN k`,
    so `F = z·pieceN k ≥ z·y ≥ x^{11/24}/8` (`zy_floor_ge`), which supplies the band `F`-floor
    directly — no membership transfer needed, the m-floor clause `F < 2^{i+1}` gives `F ≤ X`.

Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## The closed per-box price terms -/

/-- **`boxPriceKerrY` — the middle-`k` closed box price** (the Kerr price at `log y`, mirror of
`boxPriceKerr` with `Real.log ((2^k:ℕ):ℝ)` replaced by `Real.log (y:ℝ)`).  The per-box value at the
single middle `k` (`pieceN k < y < pieceM k`), where the sym indicator is `blockPrimeInd y`. -/
noncomputable def boxPriceKerrY (Kc : ℝ) (y k i : ℕ) : ℝ :=
  2 * ((Kbeta_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
            (Real.log (y : ℝ)) 13 18
        + (6 * (Km_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                  (Real.log (y : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
            + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                * Kbeta'_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                    (Real.log (y : ℝ)) 13 18 + 15360 + 1)))
      * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
      / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ))

/-- `boxPriceKerrY` is nonnegative when `Kc ≥ 0` and `1 ≤ y` (so `log y ≥ 0`). -/
theorem boxPriceKerrY_nonneg {Kc : ℝ} (hKc : 0 ≤ Kc) (y k i : ℕ) (hy : 1 ≤ y) :
    0 ≤ boxPriceKerrY Kc y k i := by
  unfold boxPriceKerrY
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
  have hlogy0 : (0 : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_nonneg; exact_mod_cast hy
  have hkb := Kbeta_min_nonneg (K := Kc)
    (L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
    (logN := Real.log (y : ℝ)) (A := 13) (C0 := 18) hKc hL0 hlogy0
  have hkm := Km_min_nonneg (K := Kc)
    (L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
    (logN := Real.log (y : ℝ)) (A := 13) (C0 := 18) hKc hL0 hlogy0
  have hkb' := Kbeta'_min_nonneg (K := Kc)
    (L := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
    (logN := Real.log (y : ℝ)) (A := 13) (C0 := 18) hKc hL0 hlogy0
  have hbracket : (0 : ℝ) ≤ Kbeta_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
            (Real.log (y : ℝ)) 13 18
        + (6 * (Km_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                  (Real.log (y : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
            + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                * Kbeta'_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                    (Real.log (y : ℝ)) 13 18 + 15360 + 1)) := by
    have h26 : (0 : ℝ) ≤ Real.sqrt 26 := Real.sqrt_nonneg _
    have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ ((13 : ℝ) + 5) := by positivity
    nlinarith [hkb, hkm, hkb', h26, h2p]
  have hXMnn : (0 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by positivity
  have hLpow : (0 : ℝ) ≤ (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ) :=
    Real.rpow_nonneg hL0 _
  exact mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hbracket hXMnn) hLpow)

/-! ## The closed per-piece price terms (the `PsymK`/`PlowK` slot values) -/

/-- **`lowPriceK` — the closed low per-piece price.**  For each `k`, the boundary-survivor sum of
box Kerr prices; nonneg, and `0`-dominating the vanishing regime (`pieceN k ≤ y`, LHS `= 0`). -/
noncomputable def lowPriceK (Kb : ℝ) (z x y K k : ℕ) : ℝ :=
  ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, boxPriceKerr Kb k i

/-- **`symPriceK` — the closed sym per-piece price.**  The boundary-survivor sum over
`dyadicBoundary (max y (pieceN k)) … (z·max y (pieceN k))`, per box the middle Kerr price
(`boxPriceKerrY Km`, when `pieceN k < y`) or the collapse Kerr price (`boxPriceKerr Kb`,
when `y ≤ pieceN k`).  Nonneg, `0`-dominating the vanishing regime. -/
noncomputable def symPriceK (Kb Km : ℝ) (z x y K k : ℕ) : ℝ :=
  ∑ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x (z * max y (pieceN k)) K,
    (if pieceN k < y then boxPriceKerrY Km y k i else boxPriceKerr Kb k i)

/-! ## `low_price_at_op` — the low dichotomy discharger (mandate item 1) -/

set_option maxHeartbeats 1600000 in -- deep arg-free replication: band-row bundle per box
open Classical in
/-- **`low_price_at_op` (SYMLOW item 1).**  The 2-regime low dichotomy per piece `k` at the
operating point (`z := opZ x`, `y := opY x`, `Q := opQ`, `a := opA`).  VANISH (`pieceN k ≤ opY x`):
`blockAlphaLow ≡ 0`, LHS `= 0 ≤ lowPriceK`.  LIVE (`opY x < pieceN k`): the per-box two-`T` price
(`medium_box_price_at_op_band` twice) → `low_box_price_at_op`.  Conclusion character-for-character
the `hpriceLow` slot of `hBVblocksW_discharge'`. -/
theorem low_price_at_op (Ps : ℕ) (hPspos : 0 < Ps) (hQPs : Nat.Coprime opQ Ps)
    (hQa2 : Nat.Coprime opQ (opA + 2)) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (X K : ℕ) (QR : ℝ) (Dlev D : ℕ)
    (hK : Nat.log 2 X ≤ K)
    (hDbnd : (opQ : ℝ) * (QR * (Dlev : ℝ)) ≤ (D : ℝ)) :
    ∃ (Kb x₁ : ℝ), 0 < Kb ∧
      ∀ (x : ℕ) (ε₀ : ℝ), x₁ ≤ (x : ℝ) → x ≤ X →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000) →
        ∀ (j k : ℕ), k ∈ Finset.range (Nat.log 2 x + 1) →
          (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => opQ * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k))
                    (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
                  (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW opQ (m / opQ) opA) m x
                - apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k))
                    (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
                  (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW opQ (m / opQ) opA) m
                  (x / 2 + 1)‖)
            ≤ lowPriceK Kb (opZ x) x (opY x) K k := by
  classical
  obtain ⟨Kb, N₀b, hK0b, hbody⟩ := medium_box_price_at_op_band
  obtain ⟨xrb, hxrb48, hrows⟩ := band_price_rows_at_op
  obtain ⟨xhb, hhabs⟩ := band_habs_row
  have hQ1 : 1 ≤ opQ := opf_Q_pos
  refine ⟨Kb, Real.exp (10 ^ 10) + (xrb : ℝ) + (xhb : ℝ) + ((8 * (N₀b + 4) : ℕ) : ℝ) ^ (3 : ℝ),
    hK0b, fun x ε₀ hx₁ hxX hDlo hDhi j k _hk => ?_⟩
  -- global scale facts
  have hexp0 : (0 : ℝ) ≤ Real.exp (10 ^ 10) := (Real.exp_pos _).le
  have hxrb0 : (0 : ℝ) ≤ (xrb : ℝ) := Nat.cast_nonneg _
  have hxhb0 : (0 : ℝ) ≤ (xhb : ℝ) := Nat.cast_nonneg _
  have hN₀0 : (0 : ℝ) ≤ ((8 * (N₀b + 4) : ℕ) : ℝ) ^ (3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htower : Real.exp (10 ^ 10) ≤ (x : ℝ) := by linarith [hx₁]
  have hxrbR : (xrb : ℝ) ≤ (x : ℝ) := by linarith [hx₁]
  have hxhbR : (xhb : ℝ) ≤ (x : ℝ) := by linarith [hx₁]
  have hN₀thr : ((8 * (N₀b + 4) : ℕ) : ℝ) ^ (3 : ℝ) ≤ (x : ℝ) := by linarith [hx₁]
  have hxrb : xrb ≤ x := by exact_mod_cast hxrbR
  have hxhb : xhb ≤ x := by exact_mod_cast hxhbR
  have hx48 : 10 ^ 48 ≤ x := le_trans hxrb48 hxrb
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by linarith [hxR]
  -- the `N₀`-floor `x^{1/3}/8 ≥ N₀b + 4`
  have hNfl : ((N₀b + 4 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 := by
    have hbase : (0 : ℝ) ≤ ((8 * (N₀b + 4) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpow : ((8 * (N₀b + 4) : ℕ) : ℝ)
        = (((8 * (N₀b + 4) : ℕ) : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul hbase, show (3 : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]
    have hmono : (((8 * (N₀b + 4) : ℕ) : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hN₀thr (by norm_num)
    have h813 : ((8 * (N₀b + 4) : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by rw [hpow]; exact hmono
    have hcast : ((8 * (N₀b + 4) : ℕ) : ℝ) = 8 * ((N₀b + 4 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at h813; linarith
  have h4le : (4 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 :=
    le_trans (by exact_mod_cast (show 4 ≤ N₀b + 4 by omega)) hNfl
  -- the `opY`/`opZ` floors
  have hyfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (opY x : ℝ) := by
    have htfl : (x : ℝ) ^ ((1 : ℝ) / 3) < (opY x : ℝ) + 1 := by
      rw [opY]; exact Nat.lt_floor_add_one _
    linarith
  have hopZ1R : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hx1R (by norm_num)
  have hopZ1 : 1 ≤ opZ x := by rw [opZ]; exact Nat.le_floor (by exact_mod_cast hopZ1R)
  have hopY4 : 4 ≤ opY x := by
    have : (4 : ℝ) ≤ (opY x : ℝ) := le_trans h4le hyfloor
    exact_mod_cast this
  have hzy2 : 2 ≤ opZ x * opY x := by
    calc 2 ≤ opY x := by omega
      _ ≤ opZ x * opY x := Nat.le_mul_of_pos_left _ hopZ1
  have hFlo : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opZ x * opY x : ℕ) : ℝ) := by
    have h := zy_floor_ge
      (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 10 ^ 10)) htower)
    have hzy : (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((opZ x * opY x : ℕ) : ℝ) := by
      simpa [opZ, opY] using h
    have hnn : (0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_nonneg hxpos.le _
    linarith
  -- the `D`-scale facts
  have hDub : (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
    le_trans hDhi (Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num))
  have hDx : (D : ℝ) ≤ Real.sqrt x := by
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
    rw [Real.sqrt_eq_rpow]; linarith [hDub]
  have hDpos : (0 : ℝ) < (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
    have := Real.rpow_pos_of_pos hxpos ((11 : ℝ) / 24); linarith
  have hD1 : 1 ≤ D := by
    have h0 : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le hDpos hDlo
    have : 0 < D := by exact_mod_cast h0
    omega
  have hxlo : x / 2 + 1 ≤ x := by omega
  -- the `hiX` structural row (from the corner clause, `pieceN k + 1 ≥ 2` in the live regime)
  -- the two regimes
  by_cases hvan : pieceN k ≤ opY x
  · -- VANISH: the low carrier is identically zero, so every apDiscBilinCutoff term is 0.
    have hzero : ∀ (T : ℕ) (m : ℕ),
        apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k))
            (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
          (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW opQ (m / opQ) opA) m T = 0 := by
      intro T m
      rw [apDiscBilinCutoff_congr (α' := fun _ => 0)
        (fun m' _ => by
          have hz : blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k) m' = 0 :=
            blockAlphaLow_eq_zero_of_pieceN_le hvan
          unfold restrictAlpha; rw [hz]; simp),
        apDiscBilinCutoff_zero]
    have hLHS0 : (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => opQ * d),
        ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k))
              (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
            (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW opQ (m / opQ) opA) m x
          - apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k))
              (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
            (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW opQ (m / opQ) opA) m
            (x / 2 + 1)‖) = 0 := by
      apply Finset.sum_eq_zero
      intro m _; rw [hzero x m, hzero (x / 2 + 1) m, sub_zero, norm_zero]
    rw [hLHS0]
    -- `lowPriceK ≥ 0` (nonneg box prices)
    unfold lowPriceK
    exact Finset.sum_nonneg (fun i _ => boxPriceKerr_nonneg hK0b.le k i)
  · -- LIVE: `opY x < pieceN k`
    rw [not_le] at hvan
    have hylt2 : opY x < 2 ^ k := lt_two_pow_of_lt_pieceN hvan
    have hpNk1 : 1 ≤ pieceN k := by omega
    have hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) :=
      band_kfloor_of_live hyfloor hylt2
    have hN₀2R : ((N₀b + 4 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := le_trans hNfl hNfloor
    have hN₀2 : N₀b + 4 ≤ 2 ^ k := by exact_mod_cast hN₀2R
    have hk : 2 ≤ k := by
      by_contra hk2; rw [not_le] at hk2
      have hle : (2 : ℕ) ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [pow_one] at hle; omega
    have hN₀ : N₀b ≤ 2 ^ k := by omega
    have hMlo : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (pieceM k : ℝ) := by
      have h2kM : ((2 ^ k : ℕ) : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast two_pow_le_pieceM k
      linarith [hNfloor]
    have hiX : ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) K,
        2 ^ (i + 1) ≤ X + 1 := by
      intro i hi
      rw [dyadicBoundary, Finset.mem_filter] at hi
      obtain ⟨-, hcorner, -, -⟩ := hi
      have hpk2 : 2 ≤ pieceN k + 1 := by omega
      have hle : 2 ^ (i + 1) ≤ x := by
        calc 2 ^ (i + 1) = 2 ^ i * 2 := by rw [pow_succ]
          _ ≤ 2 ^ i * (pieceN k + 1) := Nat.mul_le_mul_left _ hpk2
          _ ≤ x := hcorner
      omega
    -- the per-box price over the boundary
    have hprice : ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) K,
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => opQ * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j
                  (pieceN k)) (min (opZ x * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW opQ (m / opQ) opA) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => opQ * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j
                    (pieceN k)) (min (opZ x * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW opQ (m / opQ) opA) m (x / 2 + 1)‖)
          ≤ boxPriceKerr Kb k i := by
      intro i hi
      have hDsq : D < (2 ^ k + 1) * (2 ^ k + 1) := band_hDsq_of_kfloor hNfloor hDx hxR
      have hFX : (opZ x * opY x : ℕ) ≤ 2 ^ (i + 1) - 1 := band_F_le_X hi rfl
      have hX2 : 2 ≤ 2 ^ (i + 1) - 1 := band_two_le_X hi rfl hzy2
      obtain ⟨hXMlo, hXMhi⟩ := boundary_XM_raw hi
      obtain ⟨hLlo, hLub⟩ := boundary_log_bounds hx2 hi
      have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hxR
      have hL2 : 2 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) := by linarith [hLlo]
      have hLbb : Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) ≤ Real.log x + 3 := by
        linarith [hLub]
      have hLb0 : (0 : ℝ) ≤ Real.log x + 3 := by linarith
      have hXlo : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
        le_trans hFlo (by exact_mod_cast hFX)
      obtain ⟨hDscale, hXsqrt, hMsqrt, herr_lev, herr_Mlev, hfloor⟩ :=
        hrows x hxrb (2 ^ (i + 1) - 1) (pieceM k) D (opZ x * opY x) (Real.log x + 3)
          hXMlo hXMhi hXlo hMlo hFlo hDub hLb0 le_rfl
      have hDXM : (D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
        have hx4R : (4 : ℝ) ≤ (x : ℝ) := by linarith [hxR]
        have hsx : Real.sqrt x ≤ (x : ℝ) / 2 := by
          rw [show (x : ℝ) / 2 = Real.sqrt (((x : ℝ) / 2) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
          apply Real.sqrt_le_sqrt
          nlinarith [mul_nonneg (by linarith [hx4R] : (0 : ℝ) ≤ (x : ℝ) - 4) hxpos.le]
        have hXMloR : (x : ℝ) / 2 < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
          have hxlt : x < 2 * (x / 2 + 1) := by omega
          have hxltR : (x : ℝ) < 2 * ((x / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hxlt
          have h2 : ((x / 2 + 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
            have hc : (((2 ^ (i + 1) - 1) * pieceM k : ℕ) : ℝ)
                = ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by push_cast; ring
            rw [← hc]; exact_mod_cast le_of_lt hXMlo
          push_cast at hxltR h2; linarith
        linarith [hDx, hsx]
      have habs := hhabs x hxhb k i D hNfloor hDub hXMlo hXMhi
      have hα := norm_low_leg_le_one (opZ x) (opY x) ε₀ j (pieceN k)
        (min (opZ x * pieceN k + 1) (x + 1)) (x + 1) i
      have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => opQ * d), (1 : ℕ) ≤ m :=
            fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
      have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => opQ * d), Nat.Coprime (crtClassW opQ (m / opQ) opA) m :=
        fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
      have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => opQ * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
      unfold boxPriceKerr
      rw [two_mul]
      exact add_le_add
        (hbody x (Real.log x + 3) (opZ x * opY x) K k i _ (2 ^ (i + 1) - 1) x D _
          (fun m => crtClassW opQ (m / opQ) opA) hk htower hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀
          hL2 hX2 hD1 hDlo hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
          hDXM)
        (hbody x (Real.log x + 3) (opZ x * opY x) K k i _ (2 ^ (i + 1) - 1) (x / 2 + 1) D _
          (fun m => crtClassW opQ (m / opQ) opA) hk htower hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀
          hL2 hX2 hD1 hDlo hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
          hDXM)
    -- feed the box_disc_three_way composition
    have := low_box_price_at_op (x := x) (z := opZ x) (y := opY x) (ε₀ := ε₀) (j := j) (k := k)
      (X := X) (Q := opQ) (a := opA) Ps (QR * Dlev) K (fun i => boxPriceKerr Kb k i) hxlo hK hiX
      hprice
    exact this

/-! ## `sym_price_at_op` — the sym dichotomy discharger (mandate item 2) -/

set_option maxHeartbeats 1600000 in -- deep arg-free replication: band-row bundle per box
open Classical in
/-- **`sym_price_at_op` (SYMLOW item 2).**  The 3-regime sym dichotomy per piece `k` at the
operating point.  VANISH (`pieceM k ≤ opY x`): `blockAlphaSym ≡ 0`, LHS `= 0`.  MIDDLE
(`pieceN k < opY x < pieceM k`): price at `log y` via `middle_medium_box_price_at_y` (`Km`).
COLLAPSE (`opY x ≤ pieceN k`): `max = pieceN k`, price at `log 2^k` via
`medium_box_price_at_op_band` (`Kb`); the band `F`-floor is `z·pieceN k ≥ z·opY x ≥ x^{11/24}/8`.
Both live regimes route through `sym_box_price_at_op`'s `box_disc_three_way` composition; the
conclusion is character-for-character the `hpriceSym` slot of `hBVblocksW_discharge'`. -/
theorem sym_price_at_op (Ps : ℕ) (hPspos : 0 < Ps) (hQPs : Nat.Coprime opQ Ps)
    (hQa2 : Nat.Coprime opQ (opA + 2)) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (X K : ℕ) (QR : ℝ) (Dlev D : ℕ)
    (hK : Nat.log 2 X ≤ K)
    (hDbnd : (opQ : ℝ) * (QR * (Dlev : ℝ)) ≤ (D : ℝ)) :
    ∃ (Kb Km x₁ : ℝ), 0 < Kb ∧ 0 < Km ∧
      ∀ (x : ℕ) (ε₀ : ℝ), x₁ ≤ (x : ℝ) → x ≤ X →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (D : ℝ) ≤ (x : ℝ) ^ ((499 : ℝ) / 1000) →
        ∀ (j k : ℕ), k ∈ Finset.range (Nat.log 2 x + 1) →
          (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => opQ * d),
              ‖apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max (opY x) (pieceN k))) X (pieceM k)
                  (crtClassW opQ (m / opQ) opA) m x
                - apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k))
                  (blockPrimeInd (max (opY x) (pieceN k))) X (pieceM k)
                  (crtClassW opQ (m / opQ) opA) m (x / 2 + 1)‖)
            ≤ symPriceK Kb Km (opZ x) x (opY x) K k := by
  classical
  obtain ⟨Kb, N₀b, hK0b, hbody⟩ := medium_box_price_at_op_band
  obtain ⟨Km, N₀m, hK0m, hbodyM⟩ := middle_medium_box_price_at_y
  obtain ⟨xrb, hxrb48, hrows⟩ := band_price_rows_at_op
  obtain ⟨xhb, hhabs⟩ := band_habs_row
  have hQ1 : 1 ≤ opQ := opf_Q_pos
  refine ⟨Kb, Km, Real.exp (10 ^ 10) + (xrb : ℝ) + (xhb : ℝ)
      + ((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) ^ (3 : ℝ), hK0b, hK0m,
    fun x ε₀ hx₁ hxX hDlo hDhi j k _hk => ?_⟩
  -- global scale facts (identical preamble to `low_price_at_op`)
  have hexp0 : (0 : ℝ) ≤ Real.exp (10 ^ 10) := (Real.exp_pos _).le
  have hxrb0 : (0 : ℝ) ≤ (xrb : ℝ) := Nat.cast_nonneg _
  have hxhb0 : (0 : ℝ) ≤ (xhb : ℝ) := Nat.cast_nonneg _
  have hN₀0 : (0 : ℝ) ≤ ((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) ^ (3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htower : Real.exp (10 ^ 10) ≤ (x : ℝ) := by linarith [hx₁]
  have hxrbR : (xrb : ℝ) ≤ (x : ℝ) := by linarith [hx₁]
  have hxhbR : (xhb : ℝ) ≤ (x : ℝ) := by linarith [hx₁]
  have hN₀thr : ((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) ^ (3 : ℝ) ≤ (x : ℝ) := by linarith [hx₁]
  have hxrb : xrb ≤ x := by exact_mod_cast hxrbR
  have hxhb : xhb ≤ x := by exact_mod_cast hxhbR
  have hx48 : 10 ^ 48 ≤ x := le_trans hxrb48 hxrb
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by linarith [hxR]
  -- the `N₀`-floor `x^{1/3}/8 ≥ max N₀b N₀m + 4`
  have hNfl : ((max N₀b N₀m + 4 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 := by
    have hbase : (0 : ℝ) ≤ ((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpow : ((8 * (max N₀b N₀m + 4) : ℕ) : ℝ)
        = (((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul hbase, show (3 : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]
    have hmono : (((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hN₀thr (by norm_num)
    have h813 : ((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [hpow]; exact hmono
    have hcast : ((8 * (max N₀b N₀m + 4) : ℕ) : ℝ) = 8 * ((max N₀b N₀m + 4 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast] at h813; linarith
  have h4le : (4 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 :=
    le_trans (by exact_mod_cast (show 4 ≤ max N₀b N₀m + 4 by omega)) hNfl
  have hyfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (opY x : ℝ) := by
    have htfl : (x : ℝ) ^ ((1 : ℝ) / 3) < (opY x : ℝ) + 1 := by
      rw [opY]; exact Nat.lt_floor_add_one _
    linarith
  have hopZ1R : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hx1R (by norm_num)
  have hopZ1 : 1 ≤ opZ x := by rw [opZ]; exact Nat.le_floor (by exact_mod_cast hopZ1R)
  have hopY4 : 4 ≤ opY x := by
    have : (4 : ℝ) ≤ (opY x : ℝ) := le_trans h4le hyfloor
    exact_mod_cast this
  have hzy2 : 2 ≤ opZ x * opY x := by
    calc 2 ≤ opY x := by omega
      _ ≤ opZ x * opY x := Nat.le_mul_of_pos_left _ hopZ1
  have hFlo : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opZ x * opY x : ℕ) : ℝ) := by
    have h := zy_floor_ge
      (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 10 ^ 10)) htower)
    have hzy : (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((opZ x * opY x : ℕ) : ℝ) := by
      simpa [opZ, opY] using h
    have hnn : (0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_nonneg hxpos.le _
    linarith
  have hDub : (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
    le_trans hDhi (Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num))
  have hDx : (D : ℝ) ≤ Real.sqrt x := by
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
    rw [Real.sqrt_eq_rpow]; linarith [hDub]
  have hDpos : (0 : ℝ) < (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
    have := Real.rpow_pos_of_pos hxpos ((11 : ℝ) / 24); linarith
  have hD1 : 1 ≤ D := by
    have h0 : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le hDpos hDlo
    have : 0 < D := by exact_mod_cast h0
    omega
  have hxlo : x / 2 + 1 ≤ x := by omega
  have hx4R : (4 : ℝ) ≤ (x : ℝ) := by linarith [hxR]
  -- the QImage-family rows (regime-independent)
  have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => opQ * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
  have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => opQ * d), Nat.Coprime (crtClassW opQ (m / opQ) opA) m :=
    fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
  have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => opQ * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
  -- the 3 regimes
  by_cases hvan : pieceM k ≤ opY x
  · -- VANISH: the sym carrier is identically zero.
    have hzero : ∀ (T : ℕ) (m : ℕ),
        apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k))
          (blockPrimeInd (max (opY x) (pieceN k))) X (pieceM k) (crtClassW opQ (m / opQ) opA) m T
          = 0 := by
      intro T m
      rw [apDiscBilinCutoff_congr (α' := fun _ => 0)
        (fun m' _ => blockAlphaSym_eq_zero_of_pieceM_le hvan), apDiscBilinCutoff_zero]
    have hLHS0 : (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => opQ * d),
        ‖apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max (opY x) (pieceN k))) X (pieceM k) (crtClassW opQ (m / opQ) opA) m x
          - apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max (opY x) (pieceN k))) X (pieceM k) (crtClassW opQ (m / opQ) opA) m
            (x / 2 + 1)‖) = 0 := by
      apply Finset.sum_eq_zero
      intro m _; rw [hzero x m, hzero (x / 2 + 1) m, sub_zero, norm_zero]
    rw [hLHS0]
    unfold symPriceK
    refine Finset.sum_nonneg (fun i _ => ?_)
    split_ifs
    · exact boxPriceKerrY_nonneg hK0m.le _ _ _ (by omega)
    · exact boxPriceKerr_nonneg hK0b.le k i
  · rw [not_le] at hvan
    by_cases hmid : pieceN k < opY x
    · -- MIDDLE: `pieceN k < opY x < pieceM k`, price at `log y`.
      have hk : 2 ≤ k := by
        have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        have h6 : 6 ≤ 2 ^ (k + 1) := by
          have hpm : pieceM k = 2 ^ (k + 1) - 1 := rfl
          omega
        by_contra hc; rw [not_le] at hc
        have hle2 : (2 : ℕ) ^ (k + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp only [show (2 : ℕ) ^ 2 = 4 by norm_num] at hle2; omega
      have hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have h1 : opY x + 1 ≤ 2 ^ (k + 1) := by
          have hpm : pieceM k = 2 ^ (k + 1) - 1 := rfl
          have h2 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
          omega
        have h1R : ((opY x : ℕ) : ℝ) + 1 ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        have htfl : (x : ℝ) ^ ((1 : ℝ) / 3) < (opY x : ℝ) + 1 := by
          rw [opY]; exact Nat.lt_floor_add_one _
        have h2k1 : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
        rw [h2k1] at h1R; push_cast at h1R htfl ⊢; nlinarith [htfl, h1R]
      have hN₀m : N₀m ≤ opY x := by
        have hR : ((max N₀b N₀m + 4 : ℕ) : ℝ) ≤ (opY x : ℝ) := le_trans hNfl hyfloor
        have : max N₀b N₀m + 4 ≤ opY x := by exact_mod_cast hR
        have : N₀m ≤ max N₀b N₀m := le_max_right _ _
        omega
      unfold symPriceK
      refine sym_box_price_at_op (x := x) (z := opZ x) (y := opY x) (ε₀ := ε₀) (j := j) (k := k)
        (X := X) (Q := opQ) (a := opA) Ps (QR * Dlev) K
        (fun i => if pieceN k < opY x then boxPriceKerrY Km (opY x) k i
          else boxPriceKerr Kb k i) hxlo hK ?_ ?_
      · -- hiX
        intro i hi
        rw [max_eq_left (le_of_lt hmid)] at hi
        rw [dyadicBoundary, Finset.mem_filter] at hi
        obtain ⟨-, hcorner, -, -⟩ := hi
        have hle : 2 ^ (i + 1) ≤ x := by
          calc 2 ^ (i + 1) = 2 ^ i * 2 := by rw [pow_succ]
            _ ≤ 2 ^ i * (opY x + 1) := Nat.mul_le_mul_left _ (by omega)
            _ ≤ x := hcorner
        omega
      · -- hprice (middle)
        intro i hi
        rw [max_eq_left (le_of_lt hmid)] at hi
        rw [if_pos hmid, max_eq_left (le_of_lt hmid)]
        have hclause := hi
        rw [dyadicBoundary, Finset.mem_filter] at hclause
        obtain ⟨-, hcorner, -, hcut⟩ := hclause
        have hXMlo : x / 2 + 1 < (2 ^ (i + 1) - 1) * pieceM k := hcut
        have hMle : pieceM k ≤ 2 * (opY x + 1) := by
          have h1 := pieceM_le_two_pow k
          have h2 := two_pow_le_of_pieceN_lt hmid
          omega
        have hXMhi : (2 ^ (i + 1) - 1) * pieceM k ≤ 4 * x := by
          calc (2 ^ (i + 1) - 1) * pieceM k ≤ 2 ^ (i + 1) * (2 * (opY x + 1)) :=
                Nat.mul_le_mul (Nat.sub_le _ _) hMle
            _ = 4 * (2 ^ i * (opY x + 1)) := by rw [pow_succ]; ring
            _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner
        have hFX : (opZ x * opY x : ℕ) ≤ 2 ^ (i + 1) - 1 := band_F_le_X hi rfl
        have hX2 : 2 ≤ 2 ^ (i + 1) - 1 := band_two_le_X hi rfl hzy2
        obtain ⟨hLlo, hLub⟩ := xm_log_bounds hx2 hXMlo hXMhi
        have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hxR
        have hL2 : 2 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) := by linarith [hLlo]
        have hLbb : Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) ≤ Real.log x + 3 := by
          linarith [hLub]
        have hLb0 : (0 : ℝ) ≤ Real.log x + 3 := by linarith
        have hMlo : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (pieceM k : ℝ) :=
          le_trans hyfloor (by exact_mod_cast le_of_lt hvan)
        have hXlo : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
          le_trans hFlo (by exact_mod_cast hFX)
        obtain ⟨hDscale, hXsqrt, hMsqrt, herr_lev, herr_Mlev, hfloor⟩ :=
          hrows x hxrb (2 ^ (i + 1) - 1) (pieceM k) D (opZ x * opY x) (Real.log x + 3)
            hXMlo hXMhi hXlo hMlo hFlo hDub hLb0 le_rfl
        have hDXM : (D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
          have hsx : Real.sqrt x ≤ (x : ℝ) / 2 := by
            rw [show (x : ℝ) / 2 = Real.sqrt (((x : ℝ) / 2) ^ 2) by
              rw [Real.sqrt_sq (by positivity)]]
            apply Real.sqrt_le_sqrt
            nlinarith [mul_nonneg (by linarith [hx4R] : (0 : ℝ) ≤ (x : ℝ) - 4) hxpos.le]
          have hXMloR : (x : ℝ) / 2 < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
            have hxlt : x < 2 * (x / 2 + 1) := by omega
            have hxltR : (x : ℝ) < 2 * ((x / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hxlt
            have h2 : ((x / 2 + 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
              have hc : (((2 ^ (i + 1) - 1) * pieceM k : ℕ) : ℝ)
                  = ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by push_cast; ring
              rw [← hc]; exact_mod_cast le_of_lt hXMlo
            push_cast at hxltR h2; linarith
          linarith [hDx, hsx]
        have hDsq : D < (opY x + 1) * (opY x + 1) := hDsq_of_floor hyfloor hDx hxR
        have habs := hhabs x hxhb k i D hNfloor hDub hXMlo hXMhi
        have hα := norm_sym_leg_le_one (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k) i
        unfold boxPriceKerrY
        rw [two_mul]
        exact add_le_add
          (hbodyM x (Real.log x + 3) (opZ x * opY x) k (opY x) _ (2 ^ (i + 1) - 1) x D _
            (fun m => crtClassW opQ (m / opQ) opA) hk hmid hvan htower hyfloor hXMlo hXMhi hα hd1
            hcop2 hDsetD hN₀m hL2 hX2 hD1 hDlo hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
            hFX hDx hLbb hfloor hDXM)
          (hbodyM x (Real.log x + 3) (opZ x * opY x) k (opY x) _ (2 ^ (i + 1) - 1) (x / 2 + 1) D _
            (fun m => crtClassW opQ (m / opQ) opA) hk hmid hvan htower hyfloor hXMlo hXMhi hα hd1
            hcop2 hDsetD hN₀m hL2 hX2 hD1 hDlo hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
            hFX hDx hLbb hfloor hDXM)
    · -- COLLAPSE: `opY x ≤ pieceN k`, price at `log 2^k`.
      rw [not_lt] at hmid
      have hylt2 : opY x < 2 ^ k := lt_two_pow_of_le_pieceN hmid
      have hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) :=
        band_kfloor_of_live hyfloor hylt2
      have hN₀2R : ((max N₀b N₀m + 4 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := le_trans hNfl hNfloor
      have hN₀2 : max N₀b N₀m + 4 ≤ 2 ^ k := by exact_mod_cast hN₀2R
      have hk : 2 ≤ k := by
        by_contra hk2; rw [not_le] at hk2
        have hle : (2 : ℕ) ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp only [pow_one] at hle; omega
      have hN₀ : N₀b ≤ 2 ^ k := by
        have hle : N₀b ≤ max N₀b N₀m := le_max_left _ _
        omega
      have hMlo : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (pieceM k : ℝ) := by
        have h2kM : ((2 ^ k : ℕ) : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast two_pow_le_pieceM k
        linarith [hNfloor]
      have hFlo' : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opZ x * pieceN k : ℕ) : ℝ) := by
        refine le_trans hFlo ?_
        have : opZ x * opY x ≤ opZ x * pieceN k := Nat.mul_le_mul_left _ hmid
        exact_mod_cast this
      have hzy2' : 2 ≤ opZ x * pieceN k := le_trans hzy2 (Nat.mul_le_mul_left _ hmid)
      unfold symPriceK
      refine sym_box_price_at_op (x := x) (z := opZ x) (y := opY x) (ε₀ := ε₀) (j := j) (k := k)
        (X := X) (Q := opQ) (a := opA) Ps (QR * Dlev) K
        (fun i => if pieceN k < opY x then boxPriceKerrY Km (opY x) k i
          else boxPriceKerr Kb k i) hxlo hK ?_ ?_
      · -- hiX
        intro i hi
        rw [max_y_pieceN_eq hmid] at hi
        rw [dyadicBoundary, Finset.mem_filter] at hi
        obtain ⟨-, hcorner, -, -⟩ := hi
        have hpk2 : 2 ≤ pieceN k + 1 := by
          have : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
          unfold pieceN; omega
        have hle : 2 ^ (i + 1) ≤ x := by
          calc 2 ^ (i + 1) = 2 ^ i * 2 := by rw [pow_succ]
            _ ≤ 2 ^ i * (pieceN k + 1) := Nat.mul_le_mul_left _ hpk2
            _ ≤ x := hcorner
        omega
      · -- hprice (collapse)
        intro i hi
        rw [max_y_pieceN_eq hmid] at hi
        rw [if_neg (not_lt.mpr hmid), max_y_pieceN_eq hmid]
        have hDsq : D < (2 ^ k + 1) * (2 ^ k + 1) := band_hDsq_of_kfloor hNfloor hDx hxR
        have hFX : (opZ x * pieceN k : ℕ) ≤ 2 ^ (i + 1) - 1 := band_F_le_X hi rfl
        have hX2 : 2 ≤ 2 ^ (i + 1) - 1 := band_two_le_X hi rfl hzy2'
        obtain ⟨hXMlo, hXMhi⟩ := boundary_XM_raw hi
        obtain ⟨hLlo, hLub⟩ := boundary_log_bounds hx2 hi
        have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hxR
        have hL2 : 2 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) := by linarith [hLlo]
        have hLbb : Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) ≤ Real.log x + 3 := by
          linarith [hLub]
        have hLb0 : (0 : ℝ) ≤ Real.log x + 3 := by linarith
        have hXlo : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
          le_trans hFlo' (by exact_mod_cast hFX)
        obtain ⟨hDscale, hXsqrt, hMsqrt, herr_lev, herr_Mlev, hfloor⟩ :=
          hrows x hxrb (2 ^ (i + 1) - 1) (pieceM k) D (opZ x * pieceN k) (Real.log x + 3)
            hXMlo hXMhi hXlo hMlo hFlo' hDub hLb0 le_rfl
        have hDXM : (D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
          have hsx : Real.sqrt x ≤ (x : ℝ) / 2 := by
            rw [show (x : ℝ) / 2 = Real.sqrt (((x : ℝ) / 2) ^ 2) by
              rw [Real.sqrt_sq (by positivity)]]
            apply Real.sqrt_le_sqrt
            nlinarith [mul_nonneg (by linarith [hx4R] : (0 : ℝ) ≤ (x : ℝ) - 4) hxpos.le]
          have hXMloR : (x : ℝ) / 2 < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
            have hxlt : x < 2 * (x / 2 + 1) := by omega
            have hxltR : (x : ℝ) < 2 * ((x / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hxlt
            have h2 : ((x / 2 + 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by
              have hc : (((2 ^ (i + 1) - 1) * pieceM k : ℕ) : ℝ)
                  = ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) := by push_cast; ring
              rw [← hc]; exact_mod_cast le_of_lt hXMlo
            push_cast at hxltR h2; linarith
          linarith [hDx, hsx]
        have habs := hhabs x hxhb k i D hNfloor hDub hXMlo hXMhi
        have hα := norm_sym_leg_le_one (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k) i
        unfold boxPriceKerr
        rw [two_mul]
        exact add_le_add
          (hbody x (Real.log x + 3) (opZ x * pieceN k) K k i _ (2 ^ (i + 1) - 1) x D _
            (fun m => crtClassW opQ (m / opQ) opA) hk htower hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀
            hL2 hX2 hD1 hDlo hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
            hDXM)
          (hbody x (Real.log x + 3) (opZ x * pieceN k) K k i _ (2 ^ (i + 1) - 1) (x / 2 + 1) D _
            (fun m => crtClassW opQ (m / opQ) opA) hk htower hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀
            hL2 hX2 hD1 hDlo hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
            hDXM)

/-! ## The anti-#69 witness — the closed prices + slots feed `hBVblocksW_discharge'` (item 3)

The `example` below plugs `symPriceK`/`lowPriceK` (as the consumer's `PsymK`/`PlowK`) and the
`hpriceSym`/`hpriceLow` slot outputs (the shape `sym_price_at_op`/`low_price_at_op` produce, taken
here as hypotheses to sidestep the existential threshold) DIRECTLY into `hBVblocksW_discharge'`
(`PDiag`) at the operating point (`z := opZ x`, `y := opY x`, `Q := opQ`, `a := opA`).  It compiles
iff those outputs are exactly the slots the consumer demands — the anti-#69 slot check. -/

/-- **Anti-#69 (SYMLOW → the `PDiag` consumer).**  The closed prices and the sym/low slots feed the
exact `hpriceSym`/`hpriceLow`/`PsymK`/`PlowK` positions of `hBVblocksW_discharge'`. -/
example (x : ℕ) (ε₀ : ℝ) (Ps w' : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime opQ Ps)
    (QR : ℝ) (Dlev X K : ℕ) (Kb Km : ℝ)
    (hz : 1 ≤ opZ x) (hx2 : 2 ≤ x) (hxlo : x / 2 + 1 ≤ x) (hxX : x ≤ X) (hK : Nat.log 2 X ≤ K)
    (hw'2 : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) K,
        2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) K,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => opQ * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ x) (opY x) ε₀ j) 0
                  (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW opQ (m / opQ) opA) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => opQ * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ x) (opY x) ε₀ j) 0
                    (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW opQ (m / opQ) opA) m (x / 2 + 1)‖)
          ≤ Price j k i)
    (hpriceSym : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => opQ * d),
            ‖apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max (opY x) (pieceN k))) X (pieceM k)
                (crtClassW opQ (m / opQ) opA) m x
              - apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max (opY x) (pieceN k))) X (pieceM k)
                (crtClassW opQ (m / opQ) opA) m
                (x / 2 + 1)‖)
          ≤ symPriceK Kb Km (opZ x) x (opY x) K k)
    (hpriceLow : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => opQ * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k))
                  (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW opQ (m / opQ) opA) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) ε₀ j (pieceN k))
                  (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW opQ (m / opQ) opA) m
                (x / 2 + 1)‖)
          ≤ lowPriceK Kb (opZ x) x (opY x) K k)
    (Pdiag RHD RCE : ℝ)
    (hdiag : (opY x : ℝ) * (Nat.sqrt x : ℝ)
        * ((2 : ℝ) ^ Nat.log w' x + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag)
    (hSum : (∑ j ∈ Finset.range (maxBlock x (opZ x) ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) K,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1),
                symPriceK Kb Km (opZ x) x (opY x) K k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), lowPriceK Kb (opZ x) x (opY x) K k)
             + (1 / 2) * Pdiag))) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x (opZ x) ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x (opZ x) (opY x) ε₀ j opQ d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (∑ j ∈ Finset.range (maxBlock x (opZ x) ε₀ + 1),
        rosserRemainder (blockSwitchSieveW x (opZ x) (opY x) ε₀ j opQ opA Ps hPs hPodd) (QR * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 :=
  hBVblocksW_discharge' x (opZ x) (opY x) ε₀ opQ opA Ps w' hPs hPodd hQPs opf_Q_pos QR Dlev X K
    hz hx2 hxlo hxX hK hw'2 hPw' hiX Price hprice
    (fun _ k => symPriceK Kb Km (opZ x) x (opY x) K k)
    (fun _ k => lowPriceK Kb (opZ x) x (opY x) K k)
    hpriceSym hpriceLow Pdiag RHD RCE hdiag hSum hCE hNum

end Salt.Chen
