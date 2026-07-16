/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.GeoSum2
import Salt.Goldbach.RowsLive
import Salt.Chen.FinA3

/-!
# G-OPPLUMB — the operating-point plumbing (Goldbach terminal)

The terminal node before G-ASM: the op-plumbing that feeds the geometric `hSum` slot
(`gold_hSum_geo`) and the terminal (`gold_hBVblocksW_discharge'`).  It supplies

* the LIVE-box outer ratios at op (`gold_box_live_ratios`): the `hL1`/`hratio`/`hNXM` inputs of
  `gold_boxPriceKerr_geoN`, derived from the landed op floors (`gold_box_Xfloor`, `gold_box_Mfloor`,
  `gold_kfloor_live_z`, `gold_op_scales`);
* the outer-scale per-box price (`gold_box_hbox_geoN`): `boxPriceKerr Kc kp i ≤
  Cgeo·Kc·goldCut N (ka+1)/(log N)^{12}` at a LIVE box, the exact `hbox` summand of `gold_hSum_geo`;
* the per-box two-cutoff discharge (`gold_box_price_wide_or_dead`): the `hprice` slot per
  `(j,k',k,i)` — DEAD via `gold_box_price_dead_kerr`, LIVE-high via `gold_box_rows_wide` at the
  conductor — landing `carrier-sum ≤ boxPriceKerr Kc k' i`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The LIVE-box outer ratios at op (feeding `gold_boxPriceKerr_geoN`) -/

set_option maxHeartbeats 1600000 in
-- the live-cap `X·M ≤ 4·N^{1/8}·(2^kp)²` real chain + the two `Real.log` folds (mul/rpow/pow) and
-- the final `linarith` ratio close elaborate a long rpow-bearing chain; headroom above the default.
/-- **`gold_box_live_ratios`.**  At op, a LIVE annulus box (`2^i < opZ N·pieceN kp + 1`) meets the
three inputs of `gold_boxPriceKerr_geoN`: `hL1` (`1 ≤ log(X·M)`), `hratio` (`(10/31)·log(X·M) ≤
log 2^kp`, the worst-c ratio "met by every LIVE box"), and `hNXM` (`log N ≤ 3·log(X·M)`, so `cr = 3`
serves).  Derived from the landed op floors: `gold_box_Xfloor` (`N^{11/24}/4 ≤ X`), the live cap
(`X ≤ 2·opZ N·2^kp`), `pieceM_le_two_pow` (`M ≤ 2·2^kp`), the z-floor (`N^{1/3}/16 ≤ 2^kp`), and
`gold_op_scales` (`opZ N ≤ N^{1/8}`, `log N ≥ 2·10⁹`). -/
theorem gold_box_live_ratios : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (kp ka i K : ℕ),
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
        (opZ N * opY N) K →
      2 ^ i < opZ N * pieceN kp + 1 →
      (1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ∧
      ((10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
          ≤ Real.log ((2 ^ kp : ℕ) : ℝ)) ∧
      (Real.log N ≤ 3 * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) := by
  obtain ⟨xs, hs⟩ := gold_op_scales
  refine ⟨xs, fun N hN kp ka i K hi hlive => ?_⟩
  obtain ⟨hN2, hZ1, hy6, hlogZ_le, hlogZ_ge, hlogY_ge, hlogN, hZle, hZhalf, hYle, hYhalf,
    hexp4000, hN13_16⟩ := hs N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- the three landed floors
  have hXge : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
    gold_box_Xfloor (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 4000)) hexp4000) hi
  have hkp16 : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ ((2 ^ kp : ℕ) : ℝ) :=
    le_trans (gold_box_wge hN2 hZ1 hi hlive hYhalf) (gold_kfloor_live_z hN2 hi hlive)
  have hMge2kp : ((2 ^ kp : ℕ) : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast two_pow_le_pieceM kp
  -- real abbreviations + positivity
  set X : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) with hXdef
  set M : ℝ := (pieceM kp : ℝ) with hMdef
  set B : ℝ := Real.log ((2 ^ kp : ℕ) : ℝ) with hBdef
  have h2kpnn : (0 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by positivity
  have hM1 : (1 : ℝ) ≤ M := by
    have : (1 : ℕ) ≤ pieceM kp := by
      have := two_pow_le_pieceM kp; have := Nat.one_le_pow kp 2 (by norm_num); omega
    rw [hMdef]; exact_mod_cast this
  have hX1 : (1 : ℝ) ≤ X := by
    have : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
      have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hXdef]; exact_mod_cast this
  have hXMpos : (0 : ℝ) < X * M := by positivity
  have hXM1 : (1 : ℝ) ≤ X * M := by nlinarith [hX1, hM1]
  set L : ℝ := Real.log (X * M) with hLdef
  -- numeric log slack
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hlog16 : Real.log 16 ≤ 15 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)]
  -- LOWER bound `L ≥ 5/12·log N` (from `X·M ≥ N^{11/24}/4`)
  have hXMlo : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ X * M := by
    calc (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ X := hXge
      _ = X * 1 := (mul_one X).symm
      _ ≤ X * M := by apply mul_le_mul_of_nonneg_left hM1; linarith [hX1]
  have hLlogval : Real.log ((N : ℝ) ^ ((11 : ℝ) / 24) / 4)
      = 11 / 24 * Real.log N - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos]
  have hLlow0 : 11 / 24 * Real.log N - Real.log 4 ≤ L := by
    have := Real.log_le_log (by positivity) hXMlo; rwa [hLlogval] at this
  have hLlo : 5 / 12 * Real.log N ≤ L := by linarith [hLlow0, hlog4, hlogN]
  -- (hL1) and (hNXM)
  have hL1 : (1 : ℝ) ≤ L := by linarith [hLlo, hlogN]
  have hNXM : Real.log N ≤ 3 * L := by linarith [hLlo]
  -- UPPER bound `L ≤ log 4 + (1/8)·log N + 2·B` (from the live cap `X·M ≤ 4·N^{1/8}·(2^kp)^2`)
  have hXnat : 2 ^ (i + 1) - 1 ≤ 2 * (opZ N * 2 ^ kp) := by
    have h2i : 2 ^ i ≤ opZ N * pieceN kp := by omega
    have hpN : pieceN kp ≤ 2 ^ kp := Nat.sub_le (2 ^ kp) 1
    have hmul : opZ N * pieceN kp ≤ opZ N * 2 ^ kp := Nat.mul_le_mul_left _ hpN
    have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    omega
  have hXR : X ≤ 2 * (opZ N : ℝ) * ((2 ^ kp : ℕ) : ℝ) := by
    rw [hXdef]
    calc ((2 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ ((2 * (opZ N * 2 ^ kp) : ℕ) : ℝ) := by exact_mod_cast hXnat
      _ = 2 * (opZ N : ℝ) * ((2 ^ kp : ℕ) : ℝ) := by push_cast; ring
  have hMR : M ≤ 2 * ((2 ^ kp : ℕ) : ℝ) := by
    rw [hMdef]
    calc (pieceM kp : ℝ) ≤ ((2 * 2 ^ kp : ℕ) : ℝ) := by exact_mod_cast pieceM_le_two_pow kp
      _ = 2 * ((2 ^ kp : ℕ) : ℝ) := by push_cast; ring
  have hX2 : X ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 8) * ((2 ^ kp : ℕ) : ℝ) := by
    have hstep : 2 * (opZ N : ℝ) * ((2 ^ kp : ℕ) : ℝ)
        ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 8) * ((2 ^ kp : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hZle h2kpnn; linarith
    exact le_trans hXR hstep
  have hXMhi : X * M ≤ 4 * (N : ℝ) ^ ((1 : ℝ) / 8) * ((2 ^ kp : ℕ) : ℝ) ^ 2 := by
    have hb : (0 : ℝ) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 8) * ((2 ^ kp : ℕ) : ℝ) := by positivity
    calc X * M ≤ (2 * (N : ℝ) ^ ((1 : ℝ) / 8) * ((2 ^ kp : ℕ) : ℝ)) * (2 * ((2 ^ kp : ℕ) : ℝ)) :=
          mul_le_mul hX2 hMR (by linarith [hM1]) hb
      _ = 4 * (N : ℝ) ^ ((1 : ℝ) / 8) * ((2 ^ kp : ℕ) : ℝ) ^ 2 := by ring
  have hlogU : Real.log (4 * (N : ℝ) ^ ((1 : ℝ) / 8) * ((2 ^ kp : ℕ) : ℝ) ^ 2)
      = Real.log 4 + (1 / 8) * Real.log N + 2 * B := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hNpos, Real.log_pow, hBdef]; push_cast; ring
  have hLhi : L ≤ Real.log 4 + (1 / 8) * Real.log N + 2 * B := by
    have := Real.log_le_log hXMpos hXMhi; rwa [hlogU] at this
  -- (hratio) — `B ≥ (1/3)·log N − log 16`, then linarith
  have hBlo : (1 / 3) * Real.log N - Real.log 16 ≤ B := by
    have hval : Real.log ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) = 1 / 3 * Real.log N - Real.log 16 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos]
    have := Real.log_le_log (by positivity) hkp16; rwa [hval] at this
  have hratio : (10 / 31 : ℝ) * L ≤ B := by linarith [hLhi, hBlo, hlog4, hlog16, hlogN]
  exact ⟨hL1, hratio, hNXM⟩

/-! ## 2. The outer-scale per-box price (`hbox` summand of `gold_hSum_geo`) -/

/-- **`gold_box_hbox_geoN`.**  At a LIVE box at op, `boxPriceKerr Kc kp i ≤
Cgeo·Kc·goldCut N (ka+1)/(log N)^{12}` with `Cgeo := 3^{12}·gboxConst` — the exact `hbox` summand
`gold_hSum_geo` consumes (`Btail := 0`).  `gold_box_live_ratios` supplies `hL1`/`hratio`/`hNXM`
(`cr = 3`) into `gold_boxPriceKerr_geoN`. -/
theorem gold_box_hbox_geoN {Kc : ℝ} (hKc : 1 ≤ Kc) : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (kp ka i K : ℕ),
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka)
        (goldCut N (ka + 1)) (opZ N * opY N) K →
      2 ^ i < opZ N * pieceN kp + 1 →
      boxPriceKerr Kc kp i
        ≤ (3 ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 := by
  obtain ⟨xs, hs⟩ := gold_box_live_ratios
  obtain ⟨xt, ht⟩ := gold_op_scales
  refine ⟨max xs xt, fun N hN kp ka i K hi hlive => ?_⟩
  have hxs : xs ≤ N := le_trans (le_max_left _ _) hN
  have hxt : xt ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hL1, hratio, hNXM⟩ := hs N hxs kp ka i K hi hlive
  have hlogN0 : 0 < Real.log N := by have := (ht N hxt).2.2.2.2.2.2.1; linarith
  exact gold_boxPriceKerr_geoN hKc hi hL1 hratio hlogN0 (by norm_num) hNXM

/-! ## 3. The per-box two-cutoff discharge (`hprice` slot of `gold_hBVblocksW_discharge'`) -/

set_option maxHeartbeats 800000 in
-- the LIVE branch applies the ~19-hypothesis `gold_box_rows_wide` and the DEAD branch the empty-
-- carrier collapse; the defeq checks on the two-cutoff carrier shape need headroom.
/-- **`gold_box_price_wide_or_dead`.**  For the terminal's exact two-cutoff box carrier at op
(`z = opZ N`, `y = opY N`), the per-box price is `≤ boxPriceKerr Kc k' i` with `Kc := max Kc₀ 1 ≥ 1`
(`Kc₀` the `gold_box_rows_wide` constant): DEAD (`min (opZ N·pieceN k'+1) (N/2+1) ≤ 2^i`) via
`gold_box_price_dead_kerr`; LIVE via `gold_box_rows_wide` at the assembly-supplied wide level `D`
(`hDge`/`hDwide`) and `Dset` carrier rows (`hd1`/`hcop2`/`hDsetD`), then `boxPriceKerr_mono`. -/
theorem gold_box_price_wide_or_dead : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (ε₀ : ℝ) (j k' k i K Q a D : ℕ) (Dset : Finset ℕ) (ka : ℕ),
      i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut N ka)
        (goldCut N (ka + 1)) (opZ N * opY N) K →
      ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
      (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
      (∀ d ∈ Dset, 1 ≤ d) →
      (∀ d ∈ Dset, Nat.Coprime (crtClassG Q (d / Q) N a) d) →
      (∀ d ∈ Dset, d ≤ D) →
      (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha
            (blockAlpha (opZ N) (opY N) ε₀ j) 0 (min (opZ N * pieceN k' + 1) (N / 2 + 1)))
            (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
        + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha
              (blockAlpha (opZ N) (opY N) ε₀ j) 0 (min (opZ N * pieceN k' + 1) (N / 2 + 1)))
              (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
        ≤ boxPriceKerr Kc k' i := by
  obtain ⟨Kc₀, x₁, hKc₀, hwide⟩ := gold_box_rows_wide
  refine ⟨max Kc₀ 1, x₁, le_max_right _ _, ?_⟩
  intro N hN ε₀ j k' k i K Q a D Dset ka hi hDge hDwide hd1 hcop2 hDsetD
  by_cases hcap : min (opZ N * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i
  · exact gold_box_price_dead_kerr (le_trans zero_le_one (le_max_right _ _)) hcap Dset
  · have hlive : 2 ^ i < opZ N * pieceN k' + 1 :=
      lt_of_lt_of_le (not_le.mp hcap) (min_le_left _ _)
    have hβ := norm_box_leg_le_one (opZ N) (opY N) ε₀ j
      (min (opZ N * pieceN k' + 1) (N / 2 + 1)) i
    have hbound := hwide N hN
      (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
        (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
      k' D Dset (fun m => crtClassG Q (m / Q) N a) (goldCut N k) (goldCut N (k + 1)) ka i K
      hi hlive hDge hDwide hβ hd1 hcop2 hDsetD
    exact le_trans hbound (boxPriceKerr_mono (le_max_left _ _) k' i)

/-! ## 4. The terminal-facing per-box discharge at the QImage modulus set (`gold_box_hprice_op`) -/

set_option maxHeartbeats 800000 in
-- `gold_box_price_wide_or_dead` specialized to `Dset := QImage`; the `hcop2`/`hd1` divisor-image
-- rows are discharged internally, so only the wide rows remain.  Carrier defeq needs headroom.
/-- **`gold_box_hprice_op` (item 4).**  `gold_box_price_wide_or_dead` at the terminal's QImage
modulus set `Dset := (divisors Ps).filter (·< QR·Dlev) |>.image (Q·)` — the EXACT per-`(j,k',k,i)`
`hprice` slot of `gold_hBVblocksW_discharge'` (`PDiag.lean:511`).  The coprimality row `hcop2`
(`gold_crtClassG_coprime_of_mem`, from `Coprime Q Ps`/`Coprime Q (N−a)`/`Coprime Ps N`) and the
positivity row `hd1` are discharged internally; only the assembly's wide rows `hDge`/`hDwide` and
the modulus cap `hDsetD` remain (with `Price := boxPriceKerr Kc k'`, `Kc := max Kc₀ 1 ≥ 1`). -/
theorem gold_box_hprice_op : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (ε₀ : ℝ) (j k' k i K Q a D Ps Dlev : ℕ) (QR : ℝ) (ka : ℕ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut N ka)
        (goldCut N (ka + 1)) (opZ N * opY N) K →
      ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
      (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
      (∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
          (fun d => Q * d), d ≤ D) →
      (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
              (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
        + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ N) (opY N) ε₀ j) 0
                (min (opZ N * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
        ≤ boxPriceKerr Kc k' i := by
  obtain ⟨Kc, x₁, hKc, hpd⟩ := gold_box_price_wide_or_dead
  refine ⟨Kc, x₁, hKc, ?_⟩
  intro N hN ε₀ j k' k i K Q a D Ps Dlev QR ka hQPs hQNa hPsN hQ1 hi hDge hDwide hDsetD
  have hd1 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), 1 ≤ d := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    rw [Finset.mem_filter] at hd'
    have hpos : 0 < d' := Nat.pos_of_mem_divisors hd'.1
    have : 0 < Q * d' := Nat.mul_pos (by omega) hpos
    omega
  exact hpd N hN ε₀ j k' k i K Q a D _ ka hi hDge hDwide hd1
    (fun m hm => gold_crtClassG_coprime_of_mem (QR * Dlev) hQ1 hQPs hQNa hPsN hm) hDsetD

/-! ## 5. Byte-locks: the landed suppliers plug into the terminal's slots -/

section ByteLock

-- item 3 — the LIVE-box outer ratios feeding `gold_boxPriceKerr_geoN`
#check @Salt.Goldbach.gold_box_live_ratios
-- item 4 (hbox summand) — the outer-scale per-box price feeding `gold_hSum_geo`'s `hbox`
#check @Salt.Goldbach.gold_box_hbox_geoN
-- item 4 (per-box `hprice` discharge) — the general engine + the QImage-specialized terminal form
#check @Salt.Goldbach.gold_box_price_wide_or_dead
#check @Salt.Goldbach.gold_box_hprice_op
-- the geometric `hSum` slot (byte-locked to the terminal in `GeoSum2.gold_hSum_geo_slot`)
#check @Salt.Goldbach.gold_hSum_geo
-- the terminal whose `hprice` slot `gold_box_hprice_op` fills and whose `hSum` slot `gold_hSum_geo`
-- fills (both character-for-character)
#check @Salt.Goldbach.gold_hBVblocksW_discharge'

end ByteLock

end Salt.Goldbach
