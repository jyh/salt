/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Final2
import Salt.Goldbach.BandPrice

/-!
# G-BANDPRICE — the terminal wired with the band legs (A₃ terminal, item 4)

`gold_hBVblocksW_at_op` (`Final2.lean`) exposes the band price legs as four abstract binders
(`PsymK`/`PlowK` + `hpriceSym`/`hpriceLow`/`hsym`/`hlow`).  This file supplies those four binders
from `BandPrice.lean` (`goldPsymK`/`goldPlowK` + `gold_band_hpriceSym`/`gold_band_hpriceLow`/
`gold_band_hsym`/`gold_band_hlow`), leaving the band's single analytic residual `hgeo` (the
per-survivor cutoff-scale price — item 1's `gold_box_rows_wide` discharge) in its place.

`gold_hBVblocksW_at_op_band` therefore reduces the A₃ chain to the structural operating-point rows
plus the NON-band analytic bridge (`htail`, `hCE`, `hNum`, `hdiag`, `hPdiag`, and the constants) —
the band legs are discharged in-line.  Only `[propext, Classical.choice, Quot.sound]`; no
`native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

-- The terminal-interface `∀`-telescope names hypotheses that do not occur in the conclusion (as in
-- `Final2.gold_hBVblocksW_at_op`); the `unusedVariables` linter flags every such binder, so it is
-- disabled for this single mirroring statement.
set_option linter.unusedVariables false in
/-- **`gold_hBVblocksW_at_op_band` (item 4, the band-wired terminal).**  `gold_hBVblocksW_at_op`
with the four band binders supplied: `PsymK := goldPsymK`, `PlowK := goldPlowK`, `hpriceSym` and
`hpriceLow` by `box_disc_three_way` (`gold_band_hpriceSym`/`gold_band_hpriceLow`), and `hsym`/
`hlow` by the geometric absorb (`gold_band_hsym`/`gold_band_hlow`) against the residual per-survivor
geo price `hgeoSym`/`hgeoLow` (`Wband ≥ 24·Cgeo·Kc·N/L^{12}` via `hWband_band`).  The residual list
drops the four band legs: it is the structural op rows + `htail`/`hCE`/`hNum`/`hdiag`/`hPdiag` + the
constants. -/
theorem gold_hBVblocksW_at_op_band : ∃ (Kc : ℝ) (x₁ : ℕ), 1 ≤ Kc ∧
    ∀ (N : ℕ), x₁ ≤ N → ∀ (ε₀ : ℝ) (Q a Ps w' : ℕ)
      (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps)
      (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
      (hQ1 : 1 ≤ Q) (haN : a ≤ N)
      (QR : ℝ) (Dlev D X K : ℕ)
      (hb : 1 ≤ QR * Dlev)
      (hz : 1 ≤ opZ N) (hN2 : 2 ≤ N) (hNX : N / 2 ≤ X) (hK : Nat.log 2 X ≤ K)
      (hw'2 : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
      (hiX : ∀ k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, 2 ^ (i + 1) ≤ X + 1)
      (hDrows : ∀ k', ∀ k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
        ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) ∧
        (∀ d ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
            (fun d => Q * d), d ≤ D))
      (Pdiag Wband Ctail Ccon_band Ccon_diag RCE Cgeo : ℝ)
      (hmax : maxBlock N (opZ N) ε₀ = 0) (hlogpos : 0 < Real.log N)
      (hWband0 : 0 ≤ Wband) (hCband0 : 0 ≤ Ccon_band) (hCgeo0 : 0 ≤ Cgeo)
      (hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N)
      (hgeoSym : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
          ∀ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            goldSymSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
              ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12)
      (hgeoLow : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
          ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            goldLowSurvSum N Q a Ps ε₀ (QR * Dlev) 0 k' k i
              ≤ Cgeo * Kc * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12)
      (hWband_band : 24 * Cgeo * Kc * (N : ℝ) / (Real.log N) ^ 12 ≤ Wband)
      (hWband : Wband ≤ Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
      (hPdiag : Pdiag ≤ Ccon_diag * Kc * (N : ℝ) / (Real.log N) ^ 11)
      (htail : (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
            goldBtailMinSlot N D Q (QR * Dlev) k' i)
          ≤ Ctail * Kc * (N : ℝ) / (Real.log N) ^ 11)
      (hdiag : (opY N : ℝ) * (Nat.sqrt N : ℝ)
          * ((2 : ℝ) ^ Nat.log w' N + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag)
      (hCE : (∑ j ∈ Finset.range (maxBlock N (opZ N) ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < QR * Dlev then goldBlockConvErrW N (opZ N) (opY N) ε₀ j Q d else 0) ≤ RCE)
      (hNum : (48 * (3 ^ 12 * gboxConst) + Ctail + 3 * Ccon_band + Ccon_diag / 2)
              * Kc * (N : ℝ) / (Real.log N) ^ 11 + RCE ≤ (N : ℝ) / (Real.log N) ^ 10),
    (∑ j ∈ Finset.range (maxBlock N (opZ N) ε₀ + 1),
        rosserRemainder (goldBlockSwitchSieveW N (opZ N) (opY N) ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  obtain ⟨Kc, x₁, hKc, hterm⟩ := gold_hBVblocksW_at_op
  refine ⟨Kc, x₁, hKc, ?_⟩
  intro N hN ε₀ Q a Ps w' hPs hPodd hQPs hQNa hPsN hQ1 haN QR Dlev D X K hb hz hN2 hNX hK hw'2 hPw'
    hiX hDrows Pdiag Wband Ctail Ccon_band Ccon_diag RCE Cgeo hmax hlogpos hWband0 hCband0 hCgeo0
    hcount hgeoSym hgeoLow hWband_band hWband hPdiag htail hdiag hCE hNum
  have hKc0 : (0 : ℝ) ≤ Kc := le_trans zero_le_one hKc
  have hN1 : 1 ≤ N := by omega
  exact hterm N hN ε₀ Q a Ps w' hPs hPodd hQPs hQNa hPsN hQ1 haN QR Dlev D X K hb hz hN2 hNX hK
    hw'2 hPw' hiX hDrows (goldPsymK N K Q a Ps ε₀ (QR * Dlev))
    (goldPlowK N K Q a Ps ε₀ (QR * Dlev))
    (gold_band_hpriceSym ε₀ (QR * Dlev) hK hN1 hNX) (gold_band_hpriceLow ε₀ (QR * Dlev) hK hiX)
    Pdiag Wband Ctail Ccon_band Ccon_diag RCE hmax hlogpos hWband0 hCband0 hcount
    (fun k' hk' =>
      le_trans (gold_band_hsym ε₀ (QR * Dlev) hCgeo0 hKc0 hN1 hgeoSym k' hk') hWband_band)
    (fun k' hk' =>
      le_trans (gold_band_hlow ε₀ (QR * Dlev) hCgeo0 hKc0 hN1 hgeoLow k' hk') hWband_band)
    hWband hPdiag htail hdiag hCE hNum

/-! ## The `htail` tower close — the per-box firing reduction (item 3, structural heart)

`goldBtailMinSlot` fires (`= goldBtailMin`) only on a LIVE-LOW box, where `√(X·M) < D·L^{18}`
(`L := log(X·M)`, `X := 2^{i+1}−1`, `M := pieceM k'`).  On that branch the min additive leg is
converted `min(X, M) ≤ √(X·M) < D·L^{18}` (`Final.min_le_sqrt_mul`) and the harmonic head
`X·M = √(X·M)² < (D·L^{18})²`, giving the per-box bound below.  Summed over the `O(L²)` boxes and
closed against the operating conductor `D := opD N ≈ N^{1/2−9/100000}` (so `(D·L^{18})² ≈
N^{0.99982}·L^{36}` and `D·L^{18}·bnd ≈ N^{0.99691}·L^{18}·QR` — deficits `N^{−.00018}`, `N^{−.003}`
that dwarf every polylog at the tower `log N ≥ 10^9`), this yields
`Σ goldBtailMinSlot ≤ Ctail·Kc·N/(log N)^{11}` with (working the honest opDlev exponents)
`Ctail ≈ 48` absorbing the count and the deficit — the terminal's `htail` slot.  The summation and
the op-conductor tower step are the flagged residual; this lemma is the per-box conversion. -/

/-- **`gold_btail_slot_firing_le`.**  The per-box min-tail firing bound: on the LIVE-LOW branch the
`goldBtailMinSlot` crumb is at most `2·(2·(D·L^{18})²/Q·(1+log bnd) + 2·(D·L^{18})·bnd)`, where
`L := log((2^{i+1}−1)·pieceM k')`.  DEAD / wide branches are `0 ≤` the (nonneg) RHS; the firing
branch uses `min(X, M) ≤ √(X·M) < D·L^{18}` and `X·M < (D·L^{18})²`. -/
theorem gold_btail_slot_firing_le {N D Q : ℕ} {bnd : ℝ} (k' i : ℕ)
    (hQ1 : 1 ≤ Q) (hbnd : 1 ≤ bnd) :
    goldBtailMinSlot N D Q bnd k' i
      ≤ 2 * (2 * ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)))
                    ^ ((13 : ℝ) + 5)) ^ 2 / Q * (1 + Real.log bnd)
          + 2 * ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)))
                    ^ ((13 : ℝ) + 5)) * bnd) := by
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) with hXMdef
  set B : ℝ := (D : ℝ) * (Real.log XM) ^ ((13 : ℝ) + 5) with hBdef
  have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
    have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hM1 : (1 : ℕ) ≤ pieceM k' :=
    le_trans (Nat.one_le_pow _ _ (by norm_num)) (two_pow_le_pieceM k')
  have hXM1 : (1 : ℝ) ≤ XM := by
    rw [hXMdef]
    have hxR : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1
    have hmR : (1 : ℝ) ≤ (pieceM k' : ℝ) := by exact_mod_cast hM1
    nlinarith
  have hXM0 : 0 ≤ XM := by linarith
  have hlogXM0 : 0 ≤ Real.log XM := Real.log_nonneg hXM1
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg (by positivity) (Real.rpow_nonneg hlogXM0 _)
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have hlog0 : 0 ≤ Real.log bnd := Real.log_nonneg hbnd
  have hbnd0 : 0 ≤ bnd := by linarith
  have h1L : (0 : ℝ) ≤ 1 + Real.log bnd := by linarith
  have hRHS0 : (0 : ℝ) ≤ 2 * (2 * B ^ 2 / Q * (1 + Real.log bnd) + 2 * B * bnd) := by
    have t1 : (0 : ℝ) ≤ 2 * B ^ 2 / Q * (1 + Real.log bnd) := mul_nonneg (by positivity) h1L
    have t2 : (0 : ℝ) ≤ 2 * B * bnd :=
      mul_nonneg (mul_nonneg (by norm_num) hB0) hbnd0
    linarith
  unfold goldBtailMinSlot
  split_ifs with hdead hwide
  · exact hRHS0
  · exact hRHS0
  · -- firing branch: `√XM < B`
    have hfire : Real.sqrt XM < B := not_le.mp hwide
    have hXMlt : XM < B ^ 2 := by
      have hsq : Real.sqrt XM * Real.sqrt XM = XM := Real.mul_self_sqrt hXM0
      nlinarith [hfire, Real.sqrt_nonneg XM, hB0]
    have hmin : min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) ≤ B := by
      have hle : min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) ≤ Real.sqrt XM := by
        rw [hXMdef]; exact min_le_sqrt_mul (by positivity) (by positivity)
      linarith [hfire]
    unfold goldBtailMin
    have hTA : 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log bnd)
        ≤ 2 * B ^ 2 / Q * (1 + Real.log bnd) := by
      have hnum : 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) ≤ 2 * B ^ 2 := by
        have heq : 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) = 2 * XM := by
          rw [hXMdef]; ring
        rw [heq]; linarith [hXMlt]
      have hfac : 0 ≤ (1 + Real.log bnd) / Q := div_nonneg h1L (le_of_lt hQ0)
      have := mul_le_mul_of_nonneg_right hnum hfac
      calc 2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) / Q * (1 + Real.log bnd)
          = (2 * ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) * ((1 + Real.log bnd) / Q) := by
            ring
        _ ≤ (2 * B ^ 2) * ((1 + Real.log bnd) / Q) := this
        _ = 2 * B ^ 2 / Q * (1 + Real.log bnd) := by ring
    have hTB : 2 * min (((2 ^ (i + 1) - 1 : ℕ) : ℝ)) (pieceM k' : ℝ) * bnd ≤ 2 * B * bnd := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin (by norm_num : (0:ℝ) ≤ 2))
        hbnd0
      linarith [this]
    linarith [hTA, hTB]

end Salt.Goldbach
