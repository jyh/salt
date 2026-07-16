/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandRows2
import Salt.Goldbach.KerrY

/-!
# G-KERRY2 — the Y-indicator engine at the Y-FLOOR geometry (Goldbach A₃ sym-middle)

The missing supplier for `Close.gold_band_hsym_wide_at_op`'s `hmid` (FLAG G-CLOSE-1): the sym MIDDLE
piece survivors (`pieceN k' ≤ opY N < pieceM k'`, so `max (opY N) (pieceN k') = opY N`) on the WIDE
large-annulus band are provably NON-LIVE, so `KerrY.gold_kerrY_engine` (which needs liveness
`2^i < opZ N·pieceN k' + 1`) does not apply.  This file crosses the two landed parents:

* **`BandRows.gold_band_wide_price_at_op`** — the geometry template.  Its y-floor row derivations
  (`opY N < pieceN kp`, hence `2^{kp} > opY N ≥ N^{1/3}/2`) read the box geometry off the y-floor,
  with NO liveness.  Here the y-floor is on `pieceM` (`opY N < pieceM k'`), a HALVED floor
  (`2^{kp} > N^{1/3}/4`); every discharged row still clears at 4× margin.

* **`KerrY.gold_kerrY_engine`** — the Y-indicator template.  Its `medium_survivor_price_sqrtD` at
  `N := y`, the `log y` couplings, and the `goldBoxPriceKerrY Kc y kp i` collapse are reused; its
  three liveness-derived rows (`gold_box_zx_rows` / `gold_kfloor_live_z` / `gold_box_wge`) are
  REPLACED by the y-floor routes, and its z-dependent D0-window `gold_d0_window_z` (which needs the
  liveness-only ratio `hz_ratio`) is REPLACED by the liveness-free `gold_d0_window_band`.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* **`gold_kerrY2_engine`** — the two-cutoff sym-middle price against `blockPrimeInd y`
  (`2^{kp} ≤ y ≤ pieceM kp`) `≤ goldBoxPriceKerrY Kc y kp i`, at the y-floor geometry.
* **`gold_kerrY2_geoN`** — the outer `/(log N)^{12}` grade (`Cgeo := 4^{12}·gboxConst`), the
  Y-mirror of `gold_band_survsum_geoN_floored`, via `gold_boxPriceKerrY_geoN` with the inlined
  `band_ratio_core` pattern at `log y`.
* **`gold_hmid_discharge`** — `Close.gold_band_hsym_wide_at_op`'s `hmid` hypothesis, byte-exact.
  The interior (`2^{kp} ≤ opY N`) prices at `y := opY N`; the one-point boundary
  (`opY N = pieceN kp = 2^{kp}−1`, where `pieceM kp = 2·opY N + 1` breaks `M ≤ 2N`) prices at
  `y := 2^{kp}` via `blockPrimeInd (2^{kp}−1) = blockPrimeInd (2^{kp})` (composite for kp ≥ 2).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 0. The numeric engine (local mirrors of `KerrY §0`'s `private` toolkit) -/

/-- `(27/10)^n ≤ N^c` whenever `n ≤ c·10⁹` (`c > 0`), at `log N ≥ 10⁹`. -/
private theorem k2_const_le_rpow {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hn : (n : ℝ) ≤ c * 10 ^ 9) : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ c := by
  have hmul : c * (10 ^ 9 : ℝ) ≤ c * Real.log N := mul_le_mul_of_nonneg_left hlogN hc.le
  calc ((27 : ℝ) / 10) ^ n ≤ Real.exp (n : ℝ) := a12_pow27_le_exp n
    _ ≤ Real.exp (c * Real.log N) := Real.exp_le_exp.mpr (by linarith [hn, hmul])
    _ = (N : ℝ) ^ c := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring

/-- `C·N^a ≤ N^b` for `a < b`, `C ≤ (27/10)^n ≤ N^{b−a}`. -/
private theorem k2_mono_close {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {a b C : ℝ} {n : ℕ} (hab : a < b)
    (hC : C ≤ ((27 : ℝ) / 10) ^ n) (hnc : (n : ℝ) ≤ (b - a) * 10 ^ 9) :
    C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have hstep : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ (b - a) :=
    k2_const_le_rpow hNpos hlogN (by linarith) n hnc
  have hann : (0 : ℝ) ≤ (N : ℝ) ^ a := Real.rpow_nonneg hNpos.le _
  calc C * (N : ℝ) ^ a ≤ ((27 : ℝ) / 10) ^ n * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hC hann
    _ ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hstep hann
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hNpos]; congr 1; ring

/-- `L^E ≤ 262144·N^{1/2000}` for `0 ≤ E ≤ 18`, `0 ≤ L ≤ 2·log N`. -/
private theorem k2_Lpow_le {N : ℕ} {L : ℝ} (hlogN1 : 1 ≤ Real.log N)
    (hL0 : 0 ≤ L) (hLle : L ≤ 2 * Real.log N)
    (hpl : (Real.log N) ^ (18 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000))
    {E : ℝ} (hE0 : 0 ≤ E) (hE18 : E ≤ 18) :
    L ^ E ≤ (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) := by
  have h218 : (2 : ℝ) ^ (18 : ℝ) = 262144 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  calc L ^ E ≤ (2 * Real.log N) ^ E := Real.rpow_le_rpow hL0 hLle hE0
    _ = (2 : ℝ) ^ E * (Real.log N) ^ E := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ (2 : ℝ) ^ (18 : ℝ) * (Real.log N) ^ (18 : ℝ) := by
        refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE18)
          (Real.rpow_le_rpow_of_exponent_le hlogN1 hE18)
          (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) := by
        rw [h218]; exact mul_le_mul_of_nonneg_left hpl (by norm_num)

/-! ## 1. The block-indicator boundary equality (for the one-point y-floor boundary) -/

/-- `2^kp` is not prime for `kp ≥ 2` (it is `2·2^{kp-1}`, a nontrivial factorisation). -/
theorem k2_two_pow_not_prime {kp : ℕ} (hk : 2 ≤ kp) : ¬ (2 ^ kp : ℕ).Prime := by
  intro hp
  have hdvd : (2 : ℕ) ∣ 2 ^ kp := dvd_pow_self 2 (by omega : kp ≠ 0)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd) with h1 | h2
  · exact absurd h1 (by norm_num)
  · have : (4 : ℕ) ≤ 2 ^ kp := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ kp := Nat.pow_le_pow_right (by norm_num) hk
    omega

/-- At the y-floor boundary `opY N = 2^{kp}−1`, the sym indicator `blockPrimeInd (2^{kp}−1)`
equals `blockPrimeInd (2^{kp})` (they differ only at the composite `n = 2^{kp}`, kp ≥ 2). -/
theorem k2_blockPrimeInd_pred {kp : ℕ} (hk : 2 ≤ kp) :
    blockPrimeInd (2 ^ kp - 1) = blockPrimeInd (2 ^ kp) := by
  have h1 : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
  funext n
  unfold blockPrimeInd
  by_cases hn : 2 ^ kp - 1 < n ∧ n.Prime
  · rw [if_pos hn]
    have h2 : 2 ^ kp < n := by
      rcases hn with ⟨hlt, hp⟩
      by_contra hle
      have hne : n = 2 ^ kp := by omega
      rw [hne] at hp
      exact k2_two_pow_not_prime hk hp
    rw [if_pos ⟨h2, hn.2⟩]
  · rw [if_neg hn, if_neg]
    rintro ⟨hlt, hp⟩
    exact hn ⟨by omega, hp⟩

/-! ## 2. The Y-variant two-cutoff engine at the y-floor (the sym-middle survivor price) -/

set_option maxHeartbeats 4000000 in
-- the ~24-row wide-geometry discharge (mirror of `gold_kerrY_engine`) at the y-floor plus the band
-- `D0`-window and the 43-hypothesis generic pricer elaborate a long rpow/sqrt-bearing chain; the
-- whnf/defeq checks need headroom well above the default heartbeat budget.
/-- **`gold_kerrY2_engine`.**  The y-floor Y-indicator engine.  For a middle-piece survivor
(`2^{kp} ≤ y ≤ pieceM kp`, `opY N < pieceM kp` so the `kp`-floor `2^{kp} > N^{1/3}/4` holds) at a
WIDE per-annulus level (`hDge`, `hDwide`), the two-cutoff sym price against `blockPrimeInd y` is
`≤ goldBoxPriceKerrY Kc y kp i` — `KerrY.gold_kerrY_engine` with the three liveness rows swapped for
the y-floor routes and `gold_d0_window_z` swapped for `gold_d0_window_band`. -/
theorem gold_kerrY2_engine : ∃ (Kc : ℝ) (x₁ : ℕ), 0 < Kc ∧
    ∀ (N : ℕ), x₁ ≤ N →
      ∀ (β : ℕ → ℂ) (kp D y : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (T₁ T₂ ka i K : ℕ),
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka)
          (goldCut N (ka + 1)) (opZ N * opY N) K →
        2 ^ kp ≤ y →
        y ≤ pieceM kp →
        opY N < pieceM kp →
        (goldCut N (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) →
        (∀ m, ‖β m‖ ≤ 1) →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) → (∀ d ∈ Dset, d ≤ D) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd y)
              (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd y)
                (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₁‖)
          ≤ goldBoxPriceKerrY Kc y kp i := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ :=
    medium_survivor_price_sqrtD (A := 13) (C0 := 18) (by norm_num) (by norm_num)
  obtain ⟨xs, hs⟩ := gold_op_scales
  obtain ⟨xp, hp⟩ := a12_logpow_le_rpow 18 (1 / 2000) (by norm_num) (by norm_num)
  obtain ⟨xh, hh⟩ := a12_log_ge (3 * 10 ^ 10 + 10)
  refine ⟨Kc, max (max xs (max xp xh)) (max N₀ ((16 * N₀) ^ 3 + 1)), hKc, ?_⟩
  intro N hN β kp D y Dset r T₁ T₂ ka i K hi hkpy hyM hyfloorM hDge hDwide hβ hd1 hcop2 hDsetD
  have hxs : xs ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hxp : xp ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
  have hxh : xh ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
  have hN₀le : N₀ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hbigN : (16 * N₀) ^ 3 + 1 ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  obtain ⟨hN2, hZ1, hy6, hlogZ_le, hlogZ_ge, hlogY_ge, hlogN, hZle, hZhalf, hYle, hYhalf,
    hexp4000, hN13_16⟩ := hs N hxs
  obtain ⟨_, hlogNbig⟩ := hh N hxh
  have hpl : (Real.log N) ^ (18 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000) := hp N hxp
  -- basic positivity + tower facts
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN1 : (1 : ℝ) ≤ Real.log N := by linarith [hlogN]
  have hlogN9 : (10 : ℝ) ^ 9 ≤ Real.log N := by linarith [hlogN]
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by exact_mod_cast hZ1
  have hgc1 : 1 ≤ goldCut N (ka + 1) := one_le_goldCut hN2 (ka + 1)
  have hgcPos : (0 : ℝ) < (goldCut N (ka + 1) : ℝ) := by
    exact_mod_cast (by omega : 0 < goldCut N (ka + 1))
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hN13nn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hNpos.le _
  -- =============== the y-floor geometry (NEW vs. the box leg's liveness) ===============
  -- the middle-piece floor `opY N < 2^{kp+1}` ⟹ `2^{kp} > N^{1/3}/4`.
  have hyM2 : opY N < 2 ^ (kp + 1) := by unfold pieceM at hyfloorM; omega
  have h2kp1R : (opY N : ℝ) < 2 * ((2 ^ kp : ℕ) : ℝ) := by
    have hlt : (opY N : ℝ) < ((2 ^ (kp + 1) : ℕ) : ℝ) := by exact_mod_cast hyM2
    rw [show ((2 ^ (kp + 1) : ℕ) : ℝ) = 2 * ((2 ^ kp : ℕ) : ℝ) by push_cast; ring] at hlt
    exact hlt
  have h2kp4strong : (N : ℝ) ^ ((1 : ℝ) / 3) / 4 < ((2 ^ kp : ℕ) : ℝ) := by
    linarith [hYhalf, h2kp1R]
  have h2kpge : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ ((2 ^ kp : ℕ) : ℝ) := by
    linarith [h2kp4strong, hN13nn]
  have hMge2kp : ((2 ^ kp : ℕ) : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast two_pow_le_pieceM kp
  have hMfloor : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ (pieceM kp : ℝ) := by linarith [h2kpge, hMge2kp]
  -- the corner `2^{kp} ≤ goldCut(ka+1)`, so `goldCut(ka+1) > N^{1/3}/4`.
  have hcopy := hi
  rw [dyadicBoundary, Finset.mem_filter] at hcopy
  obtain ⟨_, hcorner, _, _⟩ := hcopy
  have hpc : pieceN kp + 1 = 2 ^ kp := by unfold pieceN; omega
  have hc1 : 2 ^ i * 2 ^ kp ≤ goldCut N (ka + 1) := by rw [← hpc]; exact hcorner
  have h2kp_le_gc : (2 ^ kp : ℕ) ≤ goldCut N (ka + 1) := by
    have h2i1 : (1 : ℕ) ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num)
    calc (2 ^ kp : ℕ) = 1 * 2 ^ kp := (one_mul _).symm
      _ ≤ 2 ^ i * 2 ^ kp := Nat.mul_le_mul_right _ h2i1
      _ ≤ goldCut N (ka + 1) := hc1
  have hgcge : (N : ℝ) ^ ((1 : ℝ) / 3) / 4 ≤ (goldCut N (ka + 1) : ℝ) := by
    have h2 : ((2 ^ kp : ℕ) : ℝ) ≤ (goldCut N (ka + 1) : ℝ) := by exact_mod_cast h2kp_le_gc
    linarith [h2kp4strong, h2]
  -- `hx : exp(10^10) ≤ goldCut(ka+1)` at the raised tower.
  have hlog_gc : (10 : ℝ) ^ 10 ≤ Real.log (goldCut N (ka + 1) : ℝ) := by
    have hstep : Real.log ((N : ℝ) ^ ((1 : ℝ) / 3) / 4) ≤ Real.log (goldCut N (ka + 1) : ℝ) :=
      Real.log_le_log (by positivity) hgcge
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos] at hstep
    linarith [hstep, hlogNbig, hlog4]
  have hx : Real.exp (10 ^ 10) ≤ (goldCut N (ka + 1) : ℝ) := by
    calc Real.exp (10 ^ 10) ≤ Real.exp (Real.log (goldCut N (ka + 1) : ℝ)) :=
          Real.exp_le_exp.mpr hlog_gc
      _ = (goldCut N (ka + 1) : ℝ) := Real.exp_log hgcPos
  -- `hk : 2 ≤ kp`
  have h2kp4 : (4 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
    have : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
    linarith [h2kpge]
  have hk : 2 ≤ kp := by
    by_contra hk2
    have : (2 : ℕ) ^ kp ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcast : ((2 ^ kp : ℕ) : ℝ) ≤ 2 := by
      have : ((2 ^ kp : ℕ) : ℝ) ≤ ((2 ^ 1 : ℕ) : ℝ) := by exact_mod_cast this
      simpa using this
    linarith [h2kp4, hcast]
  -- `hN₀ : N₀ ≤ 2^kp`
  have hN₀ : N₀ ≤ 2 ^ kp := by
    have hbigR : ((16 * N₀ : ℕ) : ℝ) ^ 3 ≤ (N : ℝ) := by
      have hle : ((16 * N₀) ^ 3 : ℕ) ≤ N := by omega
      calc ((16 * N₀ : ℕ) : ℝ) ^ 3 = (((16 * N₀) ^ 3 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (N : ℝ) := by exact_mod_cast hle
    have hcube : ((16 * N₀ : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
      have hmono := Real.rpow_le_rpow (by positivity) hbigR (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast ((16 * N₀ : ℕ) : ℝ) 3, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at hmono
    have hchain : ((16 * N₀ : ℕ) : ℝ) ≤ 16 * ((2 ^ kp : ℕ) : ℝ) :=
      le_trans hcube (by linarith [h2kpge])
    have hfin : ((N₀ : ℕ) : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
      have heq : ((16 * N₀ : ℕ) : ℝ) = 16 * ((N₀ : ℕ) : ℝ) := by push_cast; ring
      rw [heq] at hchain; linarith [hchain]
    exact_mod_cast hfin
  -- =============== the box-scale geometry (shared with the box leg) ===============
  have hXMlo_nat : goldCut N ka < (2 ^ (i + 1) - 1) * pieceM kp := (gold_box_XM_scale hi).1
  have hXMhi_nat : (2 ^ (i + 1) - 1) * pieceM kp ≤ 4 * goldCut N (ka + 1) :=
    (gold_box_XM_scale hi).2
  have hXge : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
    gold_box_Xfloor (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 4000)) hexp4000) hi
  have hXM2N : (2 ^ (i + 1) - 1) * pieceM kp ≤ 2 * N := by
    have := goldCut_le_half N (ka + 1); omega
  have hMge1 : (1 : ℝ) ≤ (pieceM kp : ℝ) := by
    have : (1 : ℕ) ≤ pieceM kp := by
      have := two_pow_le_pieceM kp; have := Nat.one_le_pow kp 2 (by norm_num); omega
    exact_mod_cast this
  have hXMpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    have hXpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (N : ℝ) ^ ((11 : ℝ) / 24) / 4 := by positivity
      linarith [hXge]
    positivity
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  have hXMloR : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    calc (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := hXge
      _ = ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
          apply mul_le_mul_of_nonneg_left hMge1; positivity
  have hlogval : Real.log ((N : ℝ) ^ ((11 : ℝ) / 24) / 4)
      = 11 / 24 * Real.log N - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos]
  have hLlow : 11 / 24 * Real.log N - Real.log 4 ≤ L := by
    have hle : Real.log ((N : ℝ) ^ ((11 : ℝ) / 24) / 4) ≤ L :=
      Real.log_le_log (by positivity) hXMloR
    rwa [hlogval] at hle
  have hL2 : (2 : ℝ) ≤ L := by linarith [hlogN, hlog4, hLlow]
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hXMhiR : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 2 * (N : ℝ) := by
    have : ((2 ^ (i + 1) - 1) * pieceM kp : ℕ) ≤ 2 * N := hXM2N
    have hc : (((2 ^ (i + 1) - 1) * pieceM kp : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc ⊢; linarith [hc]
  have hLle : L ≤ 2 * Real.log N := by
    have h4N : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 4 * (N : ℝ) := by linarith [hXMhiR]
    have hlog : L ≤ Real.log (4 * (N : ℝ)) := Real.log_le_log hXMpos h4N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at hlog
    linarith [hlog, hlog4, hlogN1]
  have hLbb : L ≤ Real.log (4 * (N : ℝ)) := by
    have h4N : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ 4 * (N : ℝ) := by linarith [hXMhiR]
    exact Real.log_le_log hXMpos h4N
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  -- structural rows
  have hX2 : 2 ≤ 2 ^ (i + 1) - 1 := by
    have h8 : (8 : ℝ) ≤ (N : ℝ) ^ ((11 : ℝ) / 24) := by
      have h813 : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by linarith [hN13_16]
      calc (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := h813
        _ ≤ (N : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
    have : (2 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by linarith [hXge, h8]
    exact_mod_cast this
  have hM2 : 2 ≤ pieceM kp := by
    have : (2 : ℝ) ≤ (pieceM kp : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
      linarith [hMfloor]
    exact_mod_cast this
  have hFX : opZ N * opY N ≤ 2 ^ (i + 1) - 1 := by
    have := gold_box_Ffloor hi; omega
  -- polylog rows (√X, √M floors)
  have hsqrtX : (N : ℝ) ^ ((11 : ℝ) / 48) / 2 ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
    rw [show (N : ℝ) ^ ((11 : ℝ) / 48) / 2
        = Real.sqrt (((N : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h48 : ((N : ℝ) ^ ((11 : ℝ) / 48)) ^ (2 : ℕ) = (N : ℝ) ^ ((11 : ℝ) / 24) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((11 : ℝ) / 48)) 2, ← Real.rpow_mul hNpos.le,
        show (11 : ℝ) / 48 * ((2 : ℕ) : ℝ) = 11 / 24 by push_cast; ring]
    have hsq : ((N : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ (2 : ℕ) = (N : ℝ) ^ ((11 : ℝ) / 24) / 4 := by
      rw [div_pow, h48]; norm_num
    rw [hsq]; exact hXge
  have hsqrtM : (N : ℝ) ^ ((1 : ℝ) / 6) / 4 ≤ Real.sqrt (pieceM kp : ℝ) := by
    rw [show (N : ℝ) ^ ((1 : ℝ) / 6) / 4
        = Real.sqrt (((N : ℝ) ^ ((1 : ℝ) / 6) / 4) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have h6 : ((N : ℝ) ^ ((1 : ℝ) / 6)) ^ (2 : ℕ) = (N : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 6)) 2, ← Real.rpow_mul hNpos.le,
        show (1 : ℝ) / 6 * ((2 : ℕ) : ℝ) = 1 / 3 by push_cast; ring]
    have hsq : ((N : ℝ) ^ ((1 : ℝ) / 6) / 4) ^ (2 : ℕ) = (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by
      rw [div_pow, h6]; norm_num
    rw [hsq]; exact hMfloor
  have hXsqrt : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
    have hLpow : L ^ ((13 : ℝ) + 3) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      k2_Lpow_le hlogN1 hL0 hLle hpl (by norm_num) (by norm_num)
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := by
      have hm := k2_mono_close hNpos hlogN9 (a := 1 / 2000) (b := 11 / 48) (C := 524288)
        (n := 14) (by norm_num) (by norm_num) (by norm_num)
      linarith
    calc L ^ ((13 : ℝ) + 3) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) := hLpow
      _ ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := htail
      _ ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := hsqrtX
  have hMrow : ∀ E : ℝ, 0 ≤ E → E ≤ 18 → L ^ E ≤ Real.sqrt (pieceM kp : ℝ) := by
    intro E hE0 hE18
    have hLpow : L ^ E ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      k2_Lpow_le hlogN1 hL0 hLle hpl hE0 hE18
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) / 4 := by
      have hm := k2_mono_close hNpos hlogN9 (a := 1 / 2000) (b := 1 / 6) (C := 1048576)
        (n := 15) (by norm_num) (by norm_num) (by norm_num)
      linarith
    linarith [hLpow, htail, hsqrtM]
  have hMsqrt : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM kp : ℝ) :=
    hMrow _ (by norm_num) (by norm_num)
  have herr_Mlev : L ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM kp : ℝ) :=
    hMrow _ (by norm_num) (by norm_num)
  -- `hfloor`
  have hfloor : ((3 : ℝ) / Real.log 2) ^ 8 * (N : ℝ) ^ ((1 : ℝ) / 6)
      * (Real.log (4 * (N : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt ((opZ N * opY N : ℕ) : ℝ) :=
    row_hfloor hexp4000 rfl rfl
  -- ================= the six wide D-upper rows =================
  have herr_lev : (D : ℝ) * L ^ ((13 : ℝ) + 5)
      ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := hDwide
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hDscale : (D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
      / L ^ (15 : ℝ) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    have h1518 : L ^ (15 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    calc (D : ℝ) * L ^ (15 : ℝ) ≤ (D : ℝ) * L ^ ((13 : ℝ) + 5) :=
          mul_le_mul_of_nonneg_left h1518 hDnn
      _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := herr_lev
  have hL18ge1 : (1 : ℝ) ≤ L ^ ((13 : ℝ) + 5) := by
    rw [show (1 : ℝ) = L ^ (0 : ℝ) from (Real.rpow_zero L).symm]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hDsqrtXM : (D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
    calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D : ℝ) * L ^ ((13 : ℝ) + 5) := mul_le_mul_of_nonneg_left hL18ge1 hDnn
      _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := herr_lev
  have hDXM : (D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
    have hXMge1 : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have hX2R : (2 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX2
      nlinarith [hX2R, hMge1]
    have hsqrtself : Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have h1 : Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
          ≤ Real.sqrt ((((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
              * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) :=
        Real.sqrt_le_sqrt (by nlinarith [hXMge1])
      rwa [Real.sqrt_mul_self hXMpos.le] at h1
    linarith [hDsqrtXM, hsqrtself]
  have hDx : (D : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hsqle : ((D : ℝ) * L ^ ((13 : ℝ) + 5)) * ((D : ℝ) * L ^ ((13 : ℝ) + 5))
        ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by
      have h := mul_le_mul herr_lev herr_lev (by positivity) (Real.sqrt_nonneg _)
      rwa [Real.mul_self_sqrt hXMpos.le] at h
    have hL18ge2 : (2 : ℝ) ≤ L ^ ((13 : ℝ) + 5) * L ^ ((13 : ℝ) + 5) := by
      have h1le : L ^ (1 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      rw [Real.rpow_one] at h1le
      nlinarith [le_trans hL2 h1le, hL18ge1]
    have hDDN : (D : ℝ) * (D : ℝ) ≤ (N : ℝ) := by
      have hexp : ((D : ℝ) * L ^ ((13 : ℝ) + 5)) * ((D : ℝ) * L ^ ((13 : ℝ) + 5))
          = ((D : ℝ) * (D : ℝ)) * (L ^ ((13 : ℝ) + 5) * L ^ ((13 : ℝ) + 5)) := by ring
      rw [hexp] at hsqle
      nlinarith [hsqle, hL18ge2, hXMhiR, mul_nonneg hDnn hDnn]
    rw [show (D : ℝ) = Real.sqrt ((D : ℝ) * (D : ℝ)) from (Real.sqrt_mul_self hDnn).symm]
    exact Real.sqrt_le_sqrt hDDN
  have hDsq : D < (2 ^ kp + 1) * (2 ^ kp + 1) := by
    have hsqrt2N : Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.sqrt (2 * (N : ℝ)) := Real.sqrt_le_sqrt hXMhiR
    have hkpnn : (0 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by positivity
    have hkpsq_lo : (N : ℝ) ^ ((2 : ℝ) / 3) / 256 ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) := by
      have h13sq : ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16)
          = (N : ℝ) ^ ((2 : ℝ) / 3) / 256 := by
        rw [show (N : ℝ) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) by
          rw [← Real.rpow_add hNpos]; norm_num]; ring
      have h13nn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by positivity
      calc (N : ℝ) ^ ((2 : ℝ) / 3) / 256
          = ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) := h13sq.symm
        _ ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) :=
            mul_le_mul h2kpge h2kpge h13nn hkpnn
    have h2N_le : 2 * (N : ℝ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
        * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) := by
      have hstep : (134217728 : ℝ) * (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
        have := k2_mono_close hNpos hlogN9 (a := 1) (b := 4 / 3) (C := 134217728)
          (n := 19) (by norm_num) (by norm_num) (by norm_num)
        exact this
      rw [Real.rpow_one] at hstep
      have h43 : (N : ℝ) ^ ((4 : ℝ) / 3)
          = ((N : ℝ) ^ ((2 : ℝ) / 3)) * ((N : ℝ) ^ ((2 : ℝ) / 3)) := by
        rw [← Real.rpow_add hNpos]; norm_num
      have hexp : ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
          = (N : ℝ) ^ ((4 : ℝ) / 3) / 65536 := by rw [h43]; ring
      rw [hexp]; linarith [hstep]
    have hsqrt2N_le : Real.sqrt (2 * (N : ℝ)) ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) := by
      have h1 : Real.sqrt (2 * (N : ℝ))
          ≤ Real.sqrt (((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)) :=
        Real.sqrt_le_sqrt h2N_le
      rw [Real.sqrt_mul_self (by positivity)] at h1
      linarith [h1, hkpsq_lo]
    have hDreal : (D : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) * ((2 ^ kp : ℕ) : ℝ) :=
      le_trans hDsqrtXM (le_trans hsqrt2N hsqrt2N_le)
    have hDnat : D ≤ 2 ^ kp * 2 ^ kp := by exact_mod_cast hDreal
    have hm : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
    nlinarith [hDnat, hm]
  -- `hD1 : 1 ≤ D` from the band floor `hDge` (`goldCut^{11/24} ≥ 8`).
  have hD1 : 1 ≤ D := by
    have h1010big : (100 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
    have h8 : (8 : ℝ) ≤ (goldCut N (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) := by
      have hlog8le : Real.log 8 ≤ 3 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; linarith [hlog2]
      have hlog8 : Real.log 8 ≤ (11 / 24) * Real.log (goldCut N (ka + 1) : ℝ) := by
        nlinarith [hlog_gc, hlog8le, h1010big]
      calc (8 : ℝ) = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp ((11 / 24) * Real.log (goldCut N (ka + 1) : ℝ)) := Real.exp_le_exp.mpr hlog8
        _ = (goldCut N (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) := by
            rw [Real.rpow_def_of_pos hgcPos]; congr 1; ring
    have hDR : (1 : ℝ) ≤ (D : ℝ) := by linarith [hDge, h8]
    exact_mod_cast hDR
  have herr_scale : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      L ≤ 2 * Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) :=
    fun e he2 heD heX => bridge_scale hM2 he2 heX heD hDscale (by norm_num) hL2
  have herr_LEpos : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      0 < Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) := by
    intro e he2 heD heX
    linarith [herr_scale e he2 heD heX, hL2]
  -- ================= the middle-piece Y-indicator specialisations =================
  -- the band `D0`-window at `Nb := y` (liveness-free: `gold_d0_window_band`, no `hz_ratio`).
  have hNfloorY : (goldCut N (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ) := by
    have hgcleN : (goldCut N (ka + 1) : ℝ) ≤ (N : ℝ) := by
      have : goldCut N (ka + 1) ≤ N := le_trans (goldCut_le_half N (ka + 1)) (Nat.div_le_self N 2)
      exact_mod_cast this
    have hgc13 : (goldCut N (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hgcPos.le hgcleN (by norm_num)
    have hyR : ((2 ^ kp : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hkpy
    linarith [hgc13, h2kp4strong, hyR, hN13nn]
  obtain ⟨D0, k0, hd_eq, hd_2, hd_main, hd_lo, hd_hi, hd_N', hd_conj7, hd_scale, hd_N⟩ :=
    gold_d0_window_band (Ne := N) (Nb := y) (M := pieceM kp) (X := 2 ^ (i + 1) - 1) (k := ka)
      hx hNfloorY hXMlo_nat hXMhi_nat
  have hD0lo_main : L ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : L ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_lo
  have herr_D0E : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      (D0 : ℝ) ≤ (Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ))) ^ (18 : ℝ) :=
    fun e he2 heD heX => hd_conj7 _ (herr_scale e he2 heD heX)
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_scale hDge)
  -- the indicator-specific rows at `N := y`
  have hy4N : 4 ≤ y := by
    have h4kpN : (4 : ℕ) ≤ 2 ^ kp := by exact_mod_cast h2kp4
    omega
  have hy1R : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 1 < y)
  have hlogYpos : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos hy1R
  have hN₀Y : N₀ ≤ y := le_trans hN₀ hkpy
  have hM2NY : pieceM kp ≤ 2 * y := by
    have h1 : pieceM kp ≤ 2 * 2 ^ kp := pieceM_le_two_pow kp
    omega
  have hNM : (y : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast hyM
  have hDsqY : D < (y + 1) * (y + 1) := hDsq_of_carrier_floor hkpy hDsq
  have hL13nn : (0 : ℝ) ≤ L ^ (13 : ℝ) := Real.rpow_nonneg hL0 _
  have habsY : 4 * (1 + Real.log D) * (D : ℝ)
      ≤ (y : ℝ) * (pieceM kp : ℝ) / L ^ (13 : ℝ) := by
    have habs : 4 * (1 + Real.log D) * (D : ℝ)
        ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) / L ^ (13 : ℝ) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
      have hlogD : Real.log D ≤ Real.log N := by
        have hDleN : (D : ℝ) ≤ (N : ℝ) := by
          have hself : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
            have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) * (N : ℝ)) :=
              Real.sqrt_le_sqrt (by nlinarith [hN1R])
            rwa [Real.sqrt_mul_self hNpos.le] at h1
          linarith [hDx, hself]
        rcases Nat.eq_zero_or_pos D with h0 | hDpos
        · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith [hlogN1]
        · exact Real.log_le_log (by exact_mod_cast hDpos) hDleN
      have hlogNle7L : Real.log N ≤ 7 * L := by nlinarith [hLlow, hlog4, hL2, hlogN1]
      have h14le18 : L ^ (14 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have hDL14 : (D : ℝ) * L ^ (14 : ℝ)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
        le_trans (mul_le_mul_of_nonneg_left h14le18 hDnn) herr_lev
      have hL14eq : L ^ (14 : ℝ) = L * L ^ (13 : ℝ) := by
        rw [show (14 : ℝ) = 1 + 13 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
      have hcoef : 4 * (1 + Real.log D) ≤ 32 * L := by nlinarith [hlogD, hlogNle7L, hL1]
      have hstep1 : 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
          ≤ 32 * ((D : ℝ) * L ^ (14 : ℝ)) := by
        rw [hL14eq]
        nlinarith [hcoef, hDnn, hL13nn, mul_nonneg hDnn hL13nn]
      have hBnn : (0 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := by positivity
      have hAnn : (0 : ℝ) ≤ 32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
        positivity
      have hkpMlo : (N : ℝ) ^ ((2 : ℝ) / 3) / 256 ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := by
        have h13sq : ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16)
            = (N : ℝ) ^ ((2 : ℝ) / 3) / 256 := by
          rw [show (N : ℝ) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) by
            rw [← Real.rpow_add hNpos]; norm_num]; ring
        have h13nn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by positivity
        calc (N : ℝ) ^ ((2 : ℝ) / 3) / 256
            = ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) * ((N : ℝ) ^ ((1 : ℝ) / 3) / 16) := h13sq.symm
          _ ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) :=
              mul_le_mul h2kpge hMfloor h13nn (by positivity)
      have hAAle : (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
          * (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
          ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
        have hAAeq : (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
            * (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
            = 1024 * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
          rw [show (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
              * (32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
              = 1024 * (Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
                  * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) by ring,
            Real.mul_self_sqrt hXMpos.le]
        rw [hAAeq]
        have hBBlo : 2048 * (N : ℝ)
            ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
          have hkpMlo2 : ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
              ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
            mul_le_mul hkpMlo hkpMlo (by positivity) hBnn
          have h2N_le : 2048 * (N : ℝ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
              * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) := by
            have hstep : (137438953472 : ℝ) * (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
              have := k2_mono_close hNpos hlogN9 (a := 1) (b := 4 / 3) (C := 137438953472)
                (n := 27) (by norm_num) (by norm_num) (by norm_num)
              exact this
            rw [Real.rpow_one] at hstep
            have h43 : (N : ℝ) ^ ((4 : ℝ) / 3)
                = ((N : ℝ) ^ ((2 : ℝ) / 3)) * ((N : ℝ) ^ ((2 : ℝ) / 3)) := by
              rw [← Real.rpow_add hNpos]; norm_num
            have hexp : ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
                = (N : ℝ) ^ ((4 : ℝ) / 3) / 65536 := by rw [h43]; ring
            rw [hexp]; linarith [hstep]
          linarith [hkpMlo2, h2N_le]
        nlinarith [hXMhiR, hBBlo]
      have hAle : 32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
          ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := by
        have h1 := Real.sqrt_le_sqrt hAAle
        rwa [Real.sqrt_mul_self hAnn, Real.sqrt_mul_self hBnn] at h1
      calc 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
          ≤ 32 * ((D : ℝ) * L ^ (14 : ℝ)) := hstep1
        _ ≤ 32 * Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
            mul_le_mul_of_nonneg_left hDL14 (by norm_num)
        _ ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := hAle
    refine le_trans habs ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have h2kyR : ((2 ^ kp : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hkpy
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2kyR (Nat.cast_nonneg _)) (inv_nonneg.mpr hL13nn)
  -- the SW couplings at `logN := log y`
  have hcoupG : Kc * L ^ ((13 : ℝ) + 18)
      ≤ Kbeta_min Kc L (Real.log (y : ℝ)) 13 18
          * (Real.log (y : ℝ)) ^ ((13 : ℝ) + 2 * 18) := Kbeta_min_coupling hlogYpos
  have hcoup3 : Kc * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min Kc L (Real.log (y : ℝ)) 13 18
          * (Real.log (y : ℝ)) ^ ((13 : ℝ) + 2 * 18) := Km_min_coupling hlogYpos
  have herr_book4 : ∀ e, 2 ≤ e → e ≤ D →
      Kc * (Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)))
            ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
        ≤ Kbeta'_min Kc L (Real.log (y : ℝ)) 13 18
            * (Real.log (y : ℝ)) ^ ((13 : ℝ) + 1 + 2 * 18) := fun e _ _ =>
    Kbeta'_min_coupling hKc.le hlogYpos (log_efold_nonneg (2 ^ (i + 1) - 1) (pieceM kp) e)
      (log_efold_le (2 ^ (i + 1) - 1) (pieceM kp) e) (by norm_num)
  have hKβnn : 0 ≤ Kbeta_min Kc L (Real.log (y : ℝ)) 13 18 :=
    Kbeta_min_nonneg hKc.le hL0 hlogYpos.le
  have hKmnn : 0 ≤ Km_min Kc L (Real.log (y : ℝ)) 13 18 :=
    Km_min_nonneg hKc.le hL0 hlogYpos.le
  have hKβ'nn : 0 ≤ Kbeta'_min Kc L (Real.log (y : ℝ)) 13 18 :=
    Kbeta'_min_nonneg hKc.le hL0 hlogYpos.le
  -- the single-cutoff price at `N := y`
  have hone : ∀ T : ℕ,
      (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd y)
            (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T‖)
        ≤ (Kbeta_min Kc L (Real.log (y : ℝ)) 13 18
              + (6 * (Km_min Kc L (Real.log (y : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min Kc L (Real.log (y : ℝ)) 13 18
                    + 15360 + 1)))
            * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) / L ^ (13 : ℝ) := fun T =>
    hbody (N : ℝ) (Real.log (4 * (N : ℝ))) (opZ N * opY N) β (2 ^ (i + 1) - 1) y (pieceM kp)
      T D0 D k0 (Nat.log 2 D) Dset r (Kbeta_min Kc L (Real.log (y : ℝ)) 13 18)
      (Km_min Kc L (Real.log (y : ℝ)) 13 18) (Kbeta'_min Kc L (Real.log (y : ℝ)) 13 18) 15
      hβ hKβnn hKmnn hKβ'nn hN₀Y hM2NY hd_N hd1 hcop2 hL1 hd_hi hd_N' hNM hD1 hDsetD hDsqY habsY
      hX2 hM2 (by norm_num) (by norm_num) hd_eq hd_2 hD0D rfl hDscale hD0lo_main hXsqrt hMsqrt
      herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E hDXM herr_scale hcoupG
      hcoup3 herr_book4
  unfold goldBoxPriceKerrY boxPriceKerrY
  rw [two_mul]
  exact add_le_add (hone T₂) (hone T₁)

/-! ## 3. The outer geo grade (the `hmid` `/(log N)^{12}` grade, `Cgeo := 4^{12}·gboxConst`)

The Y-mirror of `gold_band_survsum_geoN_floored`, via `gold_boxPriceKerrY_geoN` at `cr := 4`.  The
`hratio (10/31)·L ≤ log y` is the inlined `band_ratio_core` pattern at the WEAKENED middle-piece
floor (`kp·log 2 ≥ log N/3 − 2·log 2`, one `log 2` weaker than the low leg's, absorbed by the tower
`216·log 2 ≤ log N`), lifted to `log y` by `2^{kp} ≤ y`. -/
set_option maxHeartbeats 800000 in
-- the final `gold_boxPriceKerrY_geoN` application unifies the long rpow-bearing `boxPriceKerrY`
-- bracket; the isDefEq/whnf checks need headroom above the default heartbeat budget.
theorem gold_kerrY2_geoN : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (kp ka i K y : ℕ) (Kc P : ℝ), 1 ≤ Kc →
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
        (opZ N * opY N) K →
      opY N < pieceM kp → 2 ^ kp ≤ y →
      P ≤ goldBoxPriceKerrY Kc y kp i →
      P ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 := by
  obtain ⟨xs, hs⟩ := gold_op_scales
  refine ⟨xs, fun N hN kp ka i K y Kc P hKc hi hvan hkpy hP => ?_⟩
  obtain ⟨hN2, _hZ1, hy6, _, _, hlogY_ge, hlogN, _, _, hYle, hYhalf, _, _⟩ := hs N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hN13nn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hNpos.le _
  -- corner clause
  have hcopy := hi
  rw [dyadicBoundary, Finset.mem_filter] at hcopy
  obtain ⟨_, hcorner, _, _⟩ := hcopy
  have h2kppos : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
  have hpc : pieceN kp + 1 = 2 ^ kp := by unfold pieceN; omega
  have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
    have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hM1 : (1 : ℕ) ≤ pieceM kp := by
    have : (2 : ℕ) ≤ 2 ^ (kp + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (kp + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold pieceM; omega
  have hXR1 : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1
  have hMR1 : (1 : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast hM1
  have hprodpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by nlinarith
  -- (h3) the real corner `(i + kp + 1)·log 2 ≤ log N`
  have hcornerR : (2 : ℝ) ^ i * (2 : ℝ) ^ kp ≤ (N : ℝ) / 2 := by
    have hc1 : 2 ^ i * 2 ^ kp ≤ goldCut N (ka + 1) := by rw [← hpc]; exact hcorner
    have hc2 : 2 ^ i * 2 ^ kp ≤ N / 2 := le_trans hc1 (goldCut_le_half N (ka + 1))
    calc (2 : ℝ) ^ i * (2 : ℝ) ^ kp = ((2 ^ i * 2 ^ kp : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hc2
      _ ≤ (N : ℝ) / 2 := Nat.cast_div_le
  have h3 : ((i : ℝ) + (kp : ℝ) + 1) * Real.log 2 ≤ Real.log N := by
    have hle := Real.log_le_log (by positivity) hcornerR
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div hNne (by norm_num)] at hle
    nlinarith [hle]
  -- (h4) the WEAK middle-piece floor `log N/3 − 2·log 2 ≤ kp·log 2`
  have hyM2 : opY N < 2 ^ (kp + 1) := by unfold pieceM at hvan; omega
  have h2kp1R : (opY N : ℝ) < 2 * ((2 ^ kp : ℕ) : ℝ) := by
    have hlt : (opY N : ℝ) < ((2 ^ (kp + 1) : ℕ) : ℝ) := by exact_mod_cast hyM2
    rw [show ((2 ^ (kp + 1) : ℕ) : ℝ) = 2 * ((2 ^ kp : ℕ) : ℝ) by push_cast; ring] at hlt
    exact hlt
  have h2kp4strong : (N : ℝ) ^ ((1 : ℝ) / 3) / 4 < ((2 ^ kp : ℕ) : ℝ) := by
    linarith [hYhalf, h2kp1R]
  have hlog2kp : Real.log ((2 ^ kp : ℕ) : ℝ) = (kp : ℝ) * Real.log 2 := by
    rw [show ((2 ^ kp : ℕ) : ℝ) = (2 : ℝ) ^ kp by push_cast; ring, Real.log_pow]
  have h4 : Real.log N / 3 - 2 * Real.log 2 ≤ (kp : ℝ) * Real.log 2 := by
    have hlogkp : Real.log ((N : ℝ) ^ ((1 : ℝ) / 3) / 4) ≤ Real.log ((2 ^ kp : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) h2kp4strong.le
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos, hlog2kp] at hlogkp
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [hlog4eq] at hlogkp; linarith
  -- L's upper and lower bounds
  have hpNM : pieceN kp ≤ pieceM kp := by
    have : (2 : ℕ) ^ (kp + 1) = 2 * 2 ^ kp := by rw [pow_succ]; ring
    unfold pieceN pieceM; omega
  have hprod_ub : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) ≤ (2 : ℝ) ^ (i + kp + 2) := by
    have hXub : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
      calc ((2 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le _ _
        _ = (2 : ℝ) ^ (i + 1) := by push_cast; ring
    have hMub : (pieceM kp : ℝ) ≤ (2 : ℝ) ^ (kp + 1) := by
      unfold pieceM
      calc ((2 ^ (kp + 1) - 1 : ℕ) : ℝ) ≤ ((2 ^ (kp + 1) : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le _ _
        _ = (2 : ℝ) ^ (kp + 1) := by push_cast; ring
    calc ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)
        ≤ (2 : ℝ) ^ (i + 1) * (2 : ℝ) ^ (kp + 1) :=
          mul_le_mul hXub hMub (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (i + kp + 2) := by ring
  have hLub : L ≤ ((i : ℝ) + (kp : ℝ) + 2) * Real.log 2 := by
    rw [hLdef]
    have hmono := Real.log_le_log hprodpos hprod_ub
    rw [Real.log_pow] at hmono
    push_cast at hmono; nlinarith [hmono]
  have hLlb : Real.log N / 3 - Real.log 2 ≤ L := by
    rw [hLdef]
    have hoypos : (0 : ℝ) < (opY N : ℝ) := by exact_mod_cast (by omega : 0 < opY N)
    have hoyM : (opY N : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast (le_of_lt hvan)
    have hMprod : (pieceM kp : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by nlinarith
    have hchain : Real.log (opY N : ℝ)
        ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
      le_trans (Real.log_le_log hoypos hoyM)
        (Real.log_le_log (by linarith [hMR1]) hMprod)
    linarith [hlogY_ge, hchain]
  -- the ratio core (inlined `band_ratio_core` at the weak floor)
  have hlw : (216 : ℝ) * Real.log 2 ≤ Real.log N := by nlinarith [hlogN, hlog2le1, hlog2pos]
  have hcore : (10 / 31 : ℝ) * (((i : ℝ) + (kp : ℝ) + 2) * Real.log 2) ≤ (kp : ℝ) * Real.log 2 := by
    nlinarith [h3, h4, hlw, hlog2pos]
  have hL1 : (1 : ℝ) ≤ L := by linarith [hLlb, hlogN, hlog2le1]
  have hratio : (10 / 31 : ℝ) * L ≤ Real.log (y : ℝ) := by
    have h2kpy : Real.log ((2 ^ kp : ℕ) : ℝ) ≤ Real.log (y : ℝ) := by
      apply Real.log_le_log (by positivity); exact_mod_cast hkpy
    calc (10 / 31 : ℝ) * L
        ≤ (10 / 31 : ℝ) * (((i : ℝ) + (kp : ℝ) + 2) * Real.log 2) :=
          mul_le_mul_of_nonneg_left hLub (by norm_num)
      _ ≤ (kp : ℝ) * Real.log 2 := hcore
      _ = Real.log ((2 ^ kp : ℕ) : ℝ) := hlog2kp.symm
      _ ≤ Real.log (y : ℝ) := h2kpy
  have hNXM : Real.log N ≤ 4 * L := by linarith [hLlb, hlogN, hlog2le1]
  have hlogN0 : 0 < Real.log N := by linarith [hlogN]
  exact le_trans hP
    (gold_boxPriceKerrY_geoN (z := opZ N) (yb := opY N) hKc hi hL1 hratio hlogN0 (by norm_num) hNXM)

/-! ## 4. `gold_hmid_discharge` — Close's `hmid` hypothesis, byte-exact -/

set_option maxHeartbeats 800000 in
-- the `unfold goldSymSurvSum` + `boxPriceKerrY_mono` defeq checks over the long `boxPriceKerrY`
-- bracket need headroom above the default heartbeat budget.
/-- **`gold_hmid_discharge`.**  The missing supplier for `Close.gold_band_hsym_wide_at_op`'s `hmid`:
on every dyadic-boundary sym MIDDLE survivor (`pieceN k' ≤ opY N < pieceM k'`, so the max collapses
to `opY N`) the two-cutoff sym price grades to `(4^{12}·gboxConst)·Kc·goldCut N (k+1)/(log N)^{12}`.
The interior (`2^{k'} ≤ opY N`) prices the `blockPrimeInd (opY N)` carrier at `y := opY N`; the
one-point boundary (`opY N = 2^{k'}−1`, where `pieceM k' = 2·opY N + 1` breaks the pricer's
`M ≤ 2N`) prices at `y := 2^{k'}` via `blockPrimeInd (opY N) = blockPrimeInd (2^{k'})`.  The `Kc` is
this engine's own; the terminal `G-ASM` reconciles it against Close's via the RHS `Kc`-monotonicity
(`gboxConst ≥ 0`). -/
theorem gold_hmid_discharge : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (Q a Ps : ℕ) (ε₀ QR : ℝ) (Dlev D K : ℕ),
      Nat.Coprime Q Ps → Nat.Coprime Q (N - a) → Nat.Coprime Ps N → 1 ≤ Q →
      (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
      (∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ)) →
      ∀ k' ∈ Finset.range (Nat.log 2 N + 1), pieceN k' ≤ opY N → opY N < pieceM k' →
        ∀ k ∈ Finset.range (Nat.log 2 N + 1),
          ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            (D : ℝ)
                  * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ)
                      * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)
                ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) →
              goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
                ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (goldCut N (k + 1) : ℝ)
                    / (Real.log N) ^ 12 := by
  obtain ⟨Kc, xe, hKce, hengine⟩ := gold_kerrY2_engine
  obtain ⟨xg, hgeo⟩ := gold_kerrY2_geoN
  obtain ⟨xs2, hs2⟩ := gold_op_scales
  refine ⟨max Kc 1, max (max xe xg) xs2, le_max_right _ _, ?_⟩
  intro N hN Q a Ps ε₀ QR Dlev D K hQPs hQNa hPsN hQ1 hDbnd hDband k' hk' hcol hvan k hk i hi hDwide
  have hxe : xe ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hxg : xg ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hxs2 : xs2 ≤ N := le_trans (le_max_right _ _) hN
  have hKc1 : (1 : ℝ) ≤ max Kc 1 := le_max_right _ _
  obtain ⟨hN2, hZ1, hy6, _, _, _, hlogN, _, _, _, _, _, _⟩ := hs2 N hxs2
  have h2kppos : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
  have hmaxc : max (opY N) (pieceN k') = opY N := max_eq_left hcol
  have hDge : (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) := hDband k hk
  -- the QImage carrier rows (the sym survivor set)
  have hd1 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), 1 ≤ d := fun d hd => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hd
  have hcop2 : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), Nat.Coprime (crtClassG Q (d / Q) N a) d :=
    fun d hd => gold_crtClassG_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQNa hPsN hd
  have hDsetD : ∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), d ≤ D := fun d hd => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hd
  have hβ : ∀ m, ‖goldSymSub N ε₀ 0 k' i m‖ ≤ 1 := by
    unfold goldSymSub
    exact norm_restrictAlpha_le_one
      (norm_blockAlphaSym_le_one (opZ N) (opY N) ε₀ 0 (pieceN k') (pieceM k')) (2 ^ i) (2 ^ (i + 1))
  -- transfer the `max`-boundary to the `pieceN k'`-boundary (corner monotone in `Ne`)
  have hi' : i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
      (opZ N * opY N) K := by
    have hic := hi
    rw [dyadicBoundary, Finset.mem_filter] at hic ⊢
    obtain ⟨hmem, hcorner, hfl, hcut⟩ := hic
    refine ⟨hmem, ?_, hfl, hcut⟩
    rw [hmaxc] at hcorner
    exact le_trans (Nat.mul_le_mul (le_refl (2 ^ i))
      (by omega : pieceN k' + 1 ≤ opY N + 1)) hcorner
  by_cases hb : 2 ^ k' ≤ opY N
  · -- INTERIOR: `2^{k'} ≤ opY N`, price at `y := opY N`
    have hyM : opY N ≤ pieceM k' := le_of_lt hvan
    have hbound : goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
        ≤ goldBoxPriceKerrY (max Kc 1) (opY N) k' i := by
      refine le_trans ?_ (boxPriceKerrY_mono (le_max_left Kc 1) (opY N) k' i)
      have hEng := hengine N hxe (goldSymSub N ε₀ 0 k' i) k' D (opY N)
        (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d))
        (fun m => crtClassG Q (m / Q) N a) (goldCut N k) (goldCut N (k + 1)) k i K
        hi' hb hyM hvan hDge hDwide hβ hd1 hcop2 hDsetD
      unfold goldSymSurvSum
      rw [hmaxc]
      exact hEng
    exact hgeo N hxg k' k i K (opY N) (max Kc 1)
      (goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i) hKc1 hi' hvan hb hbound
  · -- BOUNDARY: `opY N = 2^{k'} − 1`, price at `y := 2^{k'}` (`blockPrimeInd` equal)
    have hb' : opY N < 2 ^ k' := by omega
    have hopY : opY N = 2 ^ k' - 1 := by unfold pieceN at hcol; omega
    have h7 : 7 ≤ 2 ^ k' := by omega
    have hk'2 : 2 ≤ k' := by
      rcases Nat.lt_or_ge k' 2 with hc | hc
      · interval_cases k' <;> norm_num at h7
      · exact hc
    have hkpy : 2 ^ k' ≤ 2 ^ k' := le_refl _
    have hyM : 2 ^ k' ≤ pieceM k' := two_pow_le_pieceM k'
    have hbound : goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
        ≤ goldBoxPriceKerrY (max Kc 1) (2 ^ k') k' i := by
      refine le_trans ?_ (boxPriceKerrY_mono (le_max_left Kc 1) (2 ^ k') k' i)
      have hEng := hengine N hxe (goldSymSub N ε₀ 0 k' i) k' D (2 ^ k')
        (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d))
        (fun m => crtClassG Q (m / Q) N a) (goldCut N k) (goldCut N (k + 1)) k i K
        hi' hkpy hyM hvan hDge hDwide hβ hd1 hcop2 hDsetD
      unfold goldSymSurvSum
      rw [hmaxc, hopY, k2_blockPrimeInd_pred hk'2]
      exact hEng
    exact hgeo N hxg k' k i K (2 ^ k') (max Kc 1)
      (goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i) hKc1 hi' hvan hkpy hbound

end Salt.Goldbach
