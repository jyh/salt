/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.FinA3
import Salt.Chen.AssembleA3b

/-!
# Node FIN-A3b — the arg-free low/sym restatements + the routed assembly → `hA3_bundle`

Companion to `FinA3` (`box_price_indep`, the §1 price monotonicity, `tripleSum_le_16x_at_op`).

* `low_price_indep` / `sym_price_indep` — `low_price_at_op` / `sym_price_at_op`
  (`AssembleA3b`) restated ARG-FREE by moving `Ps`/`X`/`K`/`QR`/`Dlev`/`D` inside the `∃`,
  so the price constants and the threshold `x₁` are genuinely x-independent (the CATCH #77
  fix, validated for the box leg by `box_price_indep`).  Bodies copied verbatim.

New file; imports `FinA3` + concrete modules only (never `Salt.Chen.All`).
Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

set_option maxHeartbeats 1600000 in -- verbatim `low_price_at_op` body: deep band-row bundle per box
open Classical in
/-- **`low_price_indep` — the arg-free low discharger.**  `low_price_at_op` with
`Ps`/`X`/`K`/`QR`/`Dlev`/`D` moved inside the `∃ Kb x₁`, so `(Kb, x₁)` are genuinely
x-independent handles (they come from the arg-free terminal `medium_box_price_at_op_band`).
Body copied verbatim from `low_price_at_op`. -/
theorem low_price_indep : ∃ (Kb x₁ : ℝ), 0 < Kb ∧
    ∀ (Ps : ℕ), 0 < Ps → Nat.Coprime opQ Ps → Nat.Coprime opQ (opA + 2) →
      (∀ p ∈ Ps.primeFactors, 3 ≤ p) → ∀ (X K : ℕ) (QR : ℝ) (Dlev D : ℕ),
        Nat.log 2 X ≤ K → (opQ : ℝ) * (QR * (Dlev : ℝ)) ≤ (D : ℝ) →
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
    hK0b, fun Ps hPspos hQPs hQa2 hPodd X K QR Dlev D hK hDbnd x ε₀ hx₁ hxX hDlo hDhi j k _hk => ?_⟩
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

set_option maxHeartbeats 1600000 in -- verbatim `sym_price_at_op` body: deep band-row bundle per box
open Classical in
/-- **`sym_price_indep` — the arg-free sym discharger.**  `sym_price_at_op` with
`Ps`/`X`/`K`/`QR`/`Dlev`/`D` moved inside the `∃ Kb Km x₁`, so `(Kb, Km, x₁)` are genuinely
x-independent handles (from the arg-free terminals `medium_box_price_at_op_band` /
`middle_medium_box_price_at_y`).  Body copied verbatim from `sym_price_at_op`. -/
theorem sym_price_indep : ∃ (Kb Km x₁ : ℝ), 0 < Kb ∧ 0 < Km ∧
    ∀ (Ps : ℕ), 0 < Ps → Nat.Coprime opQ Ps → Nat.Coprime opQ (opA + 2) →
      (∀ p ∈ Ps.primeFactors, 3 ≤ p) → ∀ (X K : ℕ) (QR : ℝ) (Dlev D : ℕ),
        Nat.log 2 X ≤ K → (opQ : ℝ) * (QR * (Dlev : ℝ)) ≤ (D : ℝ) →
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
    fun Ps hPspos hQPs hQa2 hPodd X K QR Dlev D hK hDbnd x ε₀ hx₁ hxX hDlo hDhi j k _hk => ?_⟩
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

/-! ## The `hA3_bundle` target-shape slot check (mandate item 3)

The arg-free restatements above are the low/sym blockers `box_price_indep` (`FinA3`) already
lands for the box leg — the three feed the still-to-be-written `hA3_bundle` assembly
(`mainA3_of_block_remainders_W ∘ hBVblocksW_discharge'` at the op witnesses; template
`PDiag`'s `CompositionSanity` example).  The example below fixes the EXACT bundle shape that
assembly must produce: a bundle `∃ x₁, ∀ x ≥ x₁, triplePrimeSumW opQ opA x (opP x)(opY x) ≤ M3 x`
fits the `hA3` slot of `chen_headline_of_A3_ledger` character-for-character, and — with the F2
ledger `hL` (hypothetical) — yields the Chen headline.  This is the anti-#69 slot check for the
`hA3_bundle` output. -/
example
    (hA3_bundle : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        triplePrimeSumW opQ opA x (opP x) (opY x) ≤ M3 x)
    (hL : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        0 < M1 x - M2 x / 2 - M3 x / 2
          - Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1) / 2) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite :=
  chen_headline_of_A3_ledger hA3_bundle hL

end Salt.Chen
