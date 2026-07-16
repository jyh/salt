/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.DSplit

/-!
# G-ROWSWIDE — the WIDE-level box-row bundle (Goldbach), resolving the G-DSPLIT certificate

**What this file lands (sorry-free, new file).**  `gold_box_rows_wide`: the exact analog of
`RowsLive.gold_box_rows_at_op`, but with the per-annulus sieve level `D` freed from the narrow
`[w, 2·w]` cap up to the FULL geometric window `D·L^{18} ≤ √(X·M)` (`L := log(X·M)`,
`X := 2^{i+1}−1`, `M := pieceM kp`).  Every residual analytic row of the engine
`gold_box_price_live_kerr` (`BoxRows3 §1`) is discharged at this wide level, so the two-cutoff box
price collapses onto the same closed `boxPriceKerr Kc kp i`; only the carrier/`Dset` rows
(`hβ`/`hd1`/`hcop2`/`hDsetD`) remain, supplied by the assembly.

## Why this resolves the DSplit obstruction (`gold_dsplit_head_cap_below_conductor`)

`DSplit.lean` proves, kernel-checked, that the NARROW head cap
`2·w`, `w := (goldCut N (ka+1)/(8·opZ N))^{1/2} ≈ N^{7/16}`, sits STRICTLY below the operating
conductor `opD N ≈ N^{1/2 − 9/100000}` on the top (saturating) live annulus.  Its recorded root
cause + fix: the engine's only genuine level constraints are `hDscale` (`D·L^{15} ≤ √(X·M)`) and
`herr_lev` (`D·L^{18} ≤ √(X·M)`, the tightest) — NOT `D ≤ 2w`; re-deriving RowsLive's rows at
`D ∈ [w, √(X·M)/L^{18}]` covers the whole conductor with NO tail on the annuli that afford it.  This
is exactly what the twin does (`Salt.Chen.box_rows_at_op`, `ChenRows1 §7`, discharges the same rows
at `D ≤ x^{499/1000}` over its global window).  `gold_box_rows_wide` is the Goldbach mirror.

On the top annulus `X·M ≈ 4·goldCut(ka+1) ≈ 2N`, so `√(X·M)/L^{18} ≈ √(2N)/L^{18}` and the wide
window EXCEEDS the conductor at the tower: `N^{9/100000} = e^{90000} ≫ L^{18} ≈ e^{373}` at
`log N ≥ 10^9` — an `e^{90000}` vs `e^{373}` margin.  So `D := opD N` is admissible on top-grade
annuli; the six D-upper rows hold there (and, per-annulus, wherever `opD N · L^{18} ≤ √(X·M)`).

## The six re-derived rows (each route, at the wide window)

* `herr_lev` — literally the wide hypothesis `hDwide`.
* `hDscale`  — `D·L^{15} ≤ D·L^{18} ≤ √(X·M)`  (`L^{15} ≤ L^{18}`, `L ≥ 1`).
* `hDXM`     — `D ≤ D·L^{18} ≤ √(X·M) ≤ X·M`  (`L^{18} ≥ 1`, `√t ≤ t` for `t ≥ 1`).
* `hDx`      — `(D)^2 ≤ X·M/L^{36} ≤ 2N/L^{36} ≤ N`  (`L^{36} ≥ 2`), so `D ≤ √N`.
* `hDsq`     — `D ≤ √(X·M) ≤ √(2N) ≤ N^{2/3}/256 ≤ (2^{kp})^2 < (2^{kp}+1)^2`  (`2^{kp} ≥ N^{1/3}`).
* `habs`     — `4(1+log D)·D·L^{13} ≤ 32·D·L^{14} ≤ 32√(X·M) ≤ 2^{kp}·M`  (`4(1+log D) ≤ 32L`,
  `L^{14} ≤ L^{18}`, and `(32√(X·M))^2 = 1024·X·M ≤ 2048N ≤ (2^{kp}·M)^2` at the tower).

The D-INDEPENDENT rows (`hz_ratio`/`hx`/`hX2`/`hM2`/`hFX`/`hXsqrt`/`hMsqrt`/`herr_Mlev`/`hfloor`/…)
are discharged exactly as in `gold_box_rows_at_op` (their derivations never read the D-window).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Salt.Chen

/-! ## 0. The numeric engine (local mirrors of `RowsLive §2`'s `private` toolkit) -/

/-- `(27/10)^n ≤ N^c` whenever `n ≤ c·10⁹` (`c > 0`), at `log N ≥ 10⁹`.  Mirror of
`gold_const_le_rpow`. -/
private theorem gold_const_le_rpow_w {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hn : (n : ℝ) ≤ c * 10 ^ 9) : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ c := by
  have hmul : c * (10 ^ 9 : ℝ) ≤ c * Real.log N := mul_le_mul_of_nonneg_left hlogN hc.le
  calc ((27 : ℝ) / 10) ^ n ≤ Real.exp (n : ℝ) := a12_pow27_le_exp n
    _ ≤ Real.exp (c * Real.log N) := Real.exp_le_exp.mpr (by linarith [hn, hmul])
    _ = (N : ℝ) ^ c := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring

/-- `C·N^a ≤ N^b` for `a < b`, `C ≤ (27/10)^n ≤ N^{b−a}`.  Mirror of `gold_mono_close`. -/
private theorem gold_mono_close_w {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hlogN : (10 : ℝ) ^ 9 ≤ Real.log N) {a b C : ℝ} {n : ℕ} (hab : a < b)
    (hC : C ≤ ((27 : ℝ) / 10) ^ n) (hnc : (n : ℝ) ≤ (b - a) * 10 ^ 9) :
    C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have hstep : ((27 : ℝ) / 10) ^ n ≤ (N : ℝ) ^ (b - a) :=
    gold_const_le_rpow_w hNpos hlogN (by linarith) n hnc
  have hann : (0 : ℝ) ≤ (N : ℝ) ^ a := Real.rpow_nonneg hNpos.le _
  calc C * (N : ℝ) ^ a ≤ ((27 : ℝ) / 10) ^ n * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hC hann
    _ ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a := mul_le_mul_of_nonneg_right hstep hann
    _ = (N : ℝ) ^ b := by rw [← Real.rpow_add hNpos]; congr 1; ring

/-- `L^E ≤ 262144·N^{1/2000}` for `0 ≤ E ≤ 18`, `0 ≤ L ≤ 2·log N`.  Mirror of `gold_Lpow_le`. -/
private theorem gold_Lpow_le_w {N : ℕ} {L : ℝ} (hlogN1 : 1 ≤ Real.log N)
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

/-! ## 1. The wide-window box-price leg -/

set_option maxHeartbeats 4000000 in
-- The ~24-row wide-geometry discharge elaborates a long rpow/sqrt-bearing chain and applies the
-- 39-hypothesis `gold_box_price_live_kerr`; the whnf/defeq checks need headroom above the default.
/-- **`gold_box_rows_wide`.**  At a LIVE annulus box at op with a per-annulus level in the WIDE
window `w ≤ D`, `D·L^{18} ≤ √(X·M)` (`L := log(X·M)`), the two-cutoff box price is
`≤ boxPriceKerr Kc kp i` — every residual analytic row of `gold_box_price_live_kerr` discharged at
the wide level.  Instantiable at `D := opD N` (the operating conductor) on annuli where
`opD N · L^{18} ≤ √(X·M)` — in particular the top-grade annuli (`X·M ≈ 2N`), where the DSplit
certificate `gold_dsplit_head_cap_below_conductor` showed the NARROW cap `2w` fell short.  Only the
carrier/`Dset` rows (`hβ`/`hd1`/`hcop2`/`hDsetD`) remain, supplied by the assembly. -/
theorem gold_box_rows_wide : ∃ (Kc : ℝ) (x₁ : ℕ), 0 < Kc ∧
    ∀ (N : ℕ), x₁ ≤ N →
      ∀ (β : ℕ → ℂ) (kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (T₁ T₂ ka i K : ℕ),
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut N ka) (goldCut N (ka + 1))
          (opZ N * opY N) K →
        2 ^ i < opZ N * pieceN kp + 1 →
        ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
        (D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) →
        (∀ m, ‖β m‖ ≤ 1) →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) → (∀ d ∈ Dset, d ≤ D) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
              (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
                (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₁‖)
          ≤ boxPriceKerr Kc kp i := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ := gold_box_price_live_kerr
  obtain ⟨xs, hs⟩ := gold_op_scales
  obtain ⟨xz, hzrows⟩ := gold_box_zx_rows
  obtain ⟨xp, hp⟩ := a12_logpow_le_rpow 18 (1 / 2000) (by norm_num) (by norm_num)
  refine ⟨Kc, max (max (max xs xz) xp) ((16 * N₀) ^ 3 + 1), hKc, ?_⟩
  intro N hN β kp D Dset r T₁ T₂ ka i K hi hlive hDge hDwide hβ hd1 hcop2 hDsetD
  have hxs : xs ≤ N := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hN
  have hxz : xz ≤ N := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hN
  have hxp : xp ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hbigN : (16 * N₀) ^ 3 + 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN2, hZ1, hy6, hlogZ_le, hlogZ_ge, hlogY_ge, hlogN, hZle, hZhalf, hYle, hYhalf,
    hexp4000, hN13_16⟩ := hs N hxs
  obtain ⟨_, hz_ratio, hx⟩ := hzrows N hxz kp ka i K hi hlive
  have hpl : (Real.log N) ^ (18 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2000) := hp N hxp
  -- basic positivity + tower facts
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN1 : (1 : ℝ) ≤ Real.log N := by linarith [hlogN]
  have hlogN9 : (10 : ℝ) ^ 9 ≤ Real.log N := by linarith [hlogN]
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by exact_mod_cast hZ1
  have h8zpos : (0 : ℝ) < 8 * (opZ N : ℝ) := by positivity
  have hgc1 : 1 ≤ goldCut N (ka + 1) := one_le_goldCut hN2 (ka + 1)
  have hgcPos : (0 : ℝ) < (goldCut N (ka + 1) : ℝ) := by
    exact_mod_cast (by omega : 0 < goldCut N (ka + 1))
  -- `w := (goldCut/(8z))^{1/2}`, `w² = goldCut/(8z)`, `N^{1/3}/16 ≤ w ≤ 2^kp`
  set w : ℝ := ((goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) with hwdef
  have hwnn : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hw2 : w * w = (goldCut N (ka + 1) : ℝ) / (8 * (opZ N : ℝ)) := by
    rw [hwdef, ← Real.rpow_add (by positivity), show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num,
      Real.rpow_one]
  have hwkf : w ≤ ((2 ^ kp : ℕ) : ℝ) := gold_kfloor_live_z hN2 hi hlive
  have hwge : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ w := gold_box_wge hN2 hZ1 hi hlive hYhalf
  -- box-scale geometry
  have hXMlo_nat : goldCut N ka < (2 ^ (i + 1) - 1) * pieceM kp := (gold_box_XM_scale hi).1
  have hXMhi_nat : (2 ^ (i + 1) - 1) * pieceM kp ≤ 4 * goldCut N (ka + 1) :=
    (gold_box_XM_scale hi).2
  have hMge2kp : ((2 ^ kp : ℕ) : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast two_pow_le_pieceM kp
  have hXge : (N : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) :=
    gold_box_Xfloor (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 4000)) hexp4000) hi
  have hMfloor : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ (pieceM kp : ℝ) :=
    gold_box_Mfloor hN2 hZ1 hi hlive hYhalf
  -- `X·M ≤ 2N`, real bounds
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
  -- `L` window: `2 ≤ L ≤ 2·log N`
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
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
  -- `hk : 2 ≤ kp`
  have h2kp4 : (4 : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
    have : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
    linarith [hwge, hwkf]
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
      le_trans hcube (by linarith [hwge, hwkf])
    have hfin : ((N₀ : ℕ) : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by
      have heq : ((16 * N₀ : ℕ) : ℝ) = 16 * ((N₀ : ℕ) : ℝ) := by push_cast; ring
      rw [heq] at hchain; linarith [hchain]
    exact_mod_cast hfin
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
      gold_Lpow_le_w hlogN1 hL0 hLle hpl (by norm_num) (by norm_num)
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := by
      have hm := gold_mono_close_w hNpos hlogN9 (a := 1 / 2000) (b := 11 / 48) (C := 524288)
        (n := 14) (by norm_num) (by norm_num) (by norm_num)
      linarith
    calc L ^ ((13 : ℝ) + 3) ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) := hLpow
      _ ≤ (N : ℝ) ^ ((11 : ℝ) / 48) / 2 := htail
      _ ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := hsqrtX
  have hMrow : ∀ E : ℝ, 0 ≤ E → E ≤ 18 → L ^ E ≤ Real.sqrt (pieceM kp : ℝ) := by
    intro E hE0 hE18
    have hLpow : L ^ E ≤ 262144 * (N : ℝ) ^ ((1 : ℝ) / 2000) :=
      gold_Lpow_le_w hlogN1 hL0 hLle hpl hE0 hE18
    have htail : (262144 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2000) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) / 4 := by
      have hm := gold_mono_close_w hNpos hlogN9 (a := 1 / 2000) (b := 1 / 6) (C := 1048576)
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
  -- ================= the SIX wide D-upper rows =================
  -- `2^kp ≥ N^{1/3}/16`
  have h2kpge : (N : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ ((2 ^ kp : ℕ) : ℝ) := le_trans hwge hwkf
  -- herr_lev — literally the wide hypothesis
  have herr_lev : (D : ℝ) * L ^ ((13 : ℝ) + 5)
      ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := hDwide
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := by positivity
  -- hDscale — `D·L^{15} ≤ D·L^{18} ≤ √(XM)`
  have hDscale : (D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
      / L ^ (15 : ℝ) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    have h1518 : L ^ (15 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    calc (D : ℝ) * L ^ (15 : ℝ) ≤ (D : ℝ) * L ^ ((13 : ℝ) + 5) :=
          mul_le_mul_of_nonneg_left h1518 hDnn
      _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := herr_lev
  -- `D ≤ √(XM)` (used by hDXM, hDsq)
  have hL18ge1 : (1 : ℝ) ≤ L ^ ((13 : ℝ) + 5) := by
    rw [show (1 : ℝ) = L ^ (0 : ℝ) from (Real.rpow_zero L).symm]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hDsqrtXM : (D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
    calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D : ℝ) * L ^ ((13 : ℝ) + 5) := mul_le_mul_of_nonneg_left hL18ge1 hDnn
      _ ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) := herr_lev
  -- hDXM — `D ≤ √(XM) ≤ XM`
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
  -- hDx — `D^2 ≤ N`, so `D ≤ √N`
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
  -- hDsq — `D ≤ √(XM) ≤ √(2N) ≤ (2^kp)^2`
  have hDsq : D < (2 ^ kp + 1) * (2 ^ kp + 1) := by
    have hsqrt2N : Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.sqrt (2 * (N : ℝ)) := Real.sqrt_le_sqrt hXMhiR
    -- `√(2N) ≤ (2^kp)^2`, via `2N ≤ ((2^kp)^2)^2` (tower)
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
        have := gold_mono_close_w hNpos hlogN9 (a := 1) (b := 4 / 3) (C := 134217728)
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
  -- hD1
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ (D : ℝ) := by
      have h1w : (1 : ℝ) ≤ w := by
        have : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / 16 := by linarith [hN13_16]
        linarith [hwge]
      linarith [hDge, h1w]
    exact_mod_cast this
  -- habs — `4(1+log D)·D·L^{13} ≤ 32·D·L^{14} ≤ 32√(XM) ≤ 2^kp·M`
  have hDleN : (D : ℝ) ≤ (N : ℝ) := by
    have hself : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) * (N : ℝ)) :=
        Real.sqrt_le_sqrt (by nlinarith [hN1R])
      rwa [Real.sqrt_mul_self hNpos.le] at h1
    linarith [hDx, hself]
  have hlogD : Real.log D ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos D with h0 | hDpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith [hlogN1]
    · exact Real.log_le_log (by exact_mod_cast hDpos) hDleN
  have hlogNle7L : Real.log N ≤ 7 * L := by nlinarith [hLlow, hlog4, hL2, hlogN1]
  have habs : 4 * (1 + Real.log D) * (D : ℝ)
      ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) / L ^ (13 : ℝ) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)]
    -- `D·L^{14} ≤ √(XM)`
    have h14le18 : L ^ (14 : ℝ) ≤ L ^ ((13 : ℝ) + 5) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hDL14 : (D : ℝ) * L ^ (14 : ℝ)
        ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left h14le18 hDnn) herr_lev
    have hL14eq : L ^ (14 : ℝ) = L * L ^ (13 : ℝ) := by
      rw [show (14 : ℝ) = 1 + 13 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
    have hcoef : 4 * (1 + Real.log D) ≤ 32 * L := by nlinarith [hlogD, hlogNle7L, hL1]
    -- `4(1+log D)·D·L^{13} ≤ 32·(D·L^{14})`
    have hL13nn : (0 : ℝ) ≤ L ^ (13 : ℝ) := Real.rpow_nonneg hL0 _
    have hstep1 : 4 * (1 + Real.log D) * (D : ℝ) * L ^ (13 : ℝ)
        ≤ 32 * ((D : ℝ) * L ^ (14 : ℝ)) := by
      rw [hL14eq]
      nlinarith [hcoef, hDnn, hL13nn, mul_nonneg hDnn hL13nn]
    -- `32·√(XM) ≤ 2^kp·M`  (square: `1024·XM ≤ 2048N ≤ (2^kp·M)^2`)
    have hMnn : (0 : ℝ) ≤ (pieceM kp : ℝ) := by positivity
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
        _ ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ) := mul_le_mul h2kpge hMfloor h13nn (by positivity)
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
      -- `1024·XM ≤ 2048N ≤ (2^kp·M)^2`
      have hBBlo : 2048 * (N : ℝ)
          ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) := by
        have hkpMlo2 : ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
            ≤ (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) * (((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
          mul_le_mul hkpMlo hkpMlo (by positivity) hBnn
        have h2N_le : 2048 * (N : ℝ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 3) / 256)
            * ((N : ℝ) ^ ((2 : ℝ) / 3) / 256) := by
          have hstep : (137438953472 : ℝ) * (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
            have := gold_mono_close_w hNpos hlogN9 (a := 1) (b := 4 / 3) (C := 137438953472)
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
  -- herr_scale / herr_LEpos (via bridge_scale on hDscale)
  have herr_scale : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      L ≤ 2 * Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) :=
    fun e he2 heD heX => bridge_scale hM2 he2 heX heD hDscale (by norm_num) hL2
  have herr_LEpos : ∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
      0 < Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)) := by
    intro e he2 heD heX
    linarith [herr_scale e he2 heD heX, hL2]
  -- close via `gold_box_price_live_kerr` at the op values
  have hFXR : opZ N * opY N ≤ 2 ^ (i + 1) - 1 := hFX
  exact hbody (N : ℝ) (Real.log (4 * (N : ℝ))) (opZ N * opY N) β kp D Dset r T₁ T₂ N (opZ N)
    (opY N) K ka i hN2 hi hlive hZ1 hz_ratio hx hDge hk hβ hN₀ hd1 hcop2 hL1 hD1 hDsetD hDsq habs
    hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFXR hDx hLbb hfloor herr_LEpos hDXM herr_scale

/-! ## 2. Byte-lock — the wide bundle + the DSplit certificate it resolves -/

section ByteLock

-- the wide row bundle (this file's deliverable)
#check @Salt.Goldbach.gold_box_rows_wide
-- the engine it discharges (wide `hDscale`/`herr_lev` are its own hypotheses)
#check @Salt.Goldbach.gold_box_price_live_kerr
-- the DEAD branch (fills `hprice` for dead boxes; no D-window)
#check @Salt.Goldbach.gold_box_price_dead_kerr
-- the narrow bundle this generalises
#check @Salt.Goldbach.gold_box_rows_at_op
-- the certificate this resolves: the NARROW head cap `2w` is below the op conductor
#check @Salt.Goldbach.gold_dsplit_head_cap_below_conductor

end ByteLock

end Salt.Goldbach
