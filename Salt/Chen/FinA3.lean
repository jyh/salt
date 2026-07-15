/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.Headline4
import Salt.Chen.AssembleA3
import Salt.Chen.PriceClose
import Salt.Chen.SwitchW
import Salt.Chen.PDiag
import Salt.Chen.HeadlineW2
import Salt.Chen.MediumFloor
import Salt.Chen.TripleCount
import Salt.Chen.ChenFinal
import Salt.Chen.ChenFinal2
import Salt.Chen.ChenHeadline
import Salt.Chen.PriceOne

/-!
# Node FIN-A3 — the `hA3_bundle` (the F1 target of `chen_headline_of_A3_ledger`)

This file assembles the six landed operating-point suppliers into the A₃ carrier bundle

  `hA3_bundle : ∃ x₁, ∀ x ≥ x₁, triplePrimeSumW opQ opA x (opP x) (opY x) ≤ M3 x`

via the `PDiag`:782 template: `hBVblocksW_discharge'` at the op witnesses, fed through
`mainA3_of_block_remainders_W`.

* Price / PsymK / PlowK are the closed terms of `box_price_at_op` / `sym_price_at_op` /
  `low_price_at_op`; the box and low legs are ROUTED to `0` in the vanish regime (the
  small-`2^k` boxes blow the closed price up, so the uniform-`W` bound only holds in the
  LIVE regime — see the PACK-A `lowPriceK_worst_le` note).  Sym is `k`-uniform.
* `hSum` is `AggSum.hSum_at_op` at the PACK-A worst-`W` bounds
  (`symPriceK_worst_le` / `lowPriceK_worst_le` / `boxPriceKerr_worst_le`); `hdiag` is
  `AggDiag.hdiag_slot_at_op`; `hCE` is `AggCE.hCE_at_op ∘ PackA.hRCE_at_op`; `hNum` is
  `PriceClose.hNum_close_of_tower` at the honest aggregate constant, the tower row folded
  into the threshold.
* Since the price constants are only `> 0` (not `≥ 1`), the worst-`W` lemmas are applied
  after bumping each constant to `max 1 K` via the price-monotonicity lemmas below.

New file; imports `Headline4` + concrete modules only (never `Salt.Chen.All`).
Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §1 — monotonicity of the closed Kerr prices in the price constant

The three Kerr minima `Kbeta_min`/`Km_min`/`Kbeta'_min` are each `K · (nonneg)`
(`PriceOne`), so the closed box prices are monotone in `K`.  This lets the worst-`W`
lemmas (which require `1 ≤ K`) be applied at `max 1 K` after bumping. -/

theorem Kbeta_min_mono_K {K1 K2 L logN A C0 : ℝ} (hK : K1 ≤ K2) (hL : 0 ≤ L) (hlogN : 0 ≤ logN) :
    Kbeta_min K1 L logN A C0 ≤ Kbeta_min K2 L logN A C0 := by
  unfold Kbeta_min
  have hc : (0 : ℝ) ≤ L ^ (A + C0) := Real.rpow_nonneg hL _
  have hd : (0 : ℝ) ≤ logN ^ (A + 2 * C0) := Real.rpow_nonneg hlogN _
  gcongr

theorem Km_min_mono_K {K1 K2 L logN A C0 : ℝ} (hK : K1 ≤ K2) (hL : 0 ≤ L) (hlogN : 0 ≤ logN) :
    Km_min K1 L logN A C0 ≤ Km_min K2 L logN A C0 := by
  unfold Km_min
  have hc : (0 : ℝ) ≤ L ^ (A + 1 + 2 * C0) := Real.rpow_nonneg hL _
  have hd : (0 : ℝ) ≤ logN ^ (A + 2 * C0) := Real.rpow_nonneg hlogN _
  gcongr

theorem Kbeta'_min_mono_K {K1 K2 L logN A C0 : ℝ} (hK : K1 ≤ K2) (hL : 0 ≤ L) (hlogN : 0 ≤ logN) :
    Kbeta'_min K1 L logN A C0 ≤ Kbeta'_min K2 L logN A C0 := by
  unfold Kbeta'_min
  have hc : (0 : ℝ) ≤ L ^ (A + 1 + 1 + 2 * C0) := Real.rpow_nonneg hL _
  have hd : (0 : ℝ) ≤ logN ^ (A + 1 + 2 * C0) := Real.rpow_nonneg hlogN _
  gcongr

/-- The shared bracket-monotonicity core for the box prices (both `boxPriceKerr` and
`boxPriceKerrY`, whose `logN` differs). -/
theorem box_bracket_mono {K1 K2 L logN : ℝ} (hK : K1 ≤ K2) (hL : 0 ≤ L) (hlogN : 0 ≤ logN) :
    Kbeta_min K1 L logN 13 18
        + (6 * (Km_min K1 L logN 13 18 + 448 + 32 * Real.sqrt 26)
          + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min K1 L logN 13 18 + 15360 + 1))
      ≤ Kbeta_min K2 L logN 13 18
        + (6 * (Km_min K2 L logN 13 18 + 448 + 32 * Real.sqrt 26)
          + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kbeta'_min K2 L logN 13 18 + 15360 + 1)) := by
  have h1 := Kbeta_min_mono_K (A := 13) (C0 := 18) hK hL hlogN
  have h2 := Km_min_mono_K (A := 13) (C0 := 18) hK hL hlogN
  have h3 := Kbeta'_min_mono_K (A := 13) (C0 := 18) hK hL hlogN
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ ((13 : ℝ) + 5) := by positivity
  nlinarith [h1, h2, h3, h2p]

theorem boxPriceKerr_mono {K1 K2 : ℝ} (hK : K1 ≤ K2) (k i : ℕ) :
    boxPriceKerr K1 k i ≤ boxPriceKerr K2 k i := by
  unfold boxPriceKerr
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) with hXM
  have hXM0 : (0 : ℝ) ≤ XM := by rw [hXM]; positivity
  have hL0 : (0 : ℝ) ≤ Real.log XM := by
    have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
      have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hM1 : (1 : ℕ) ≤ pieceM k := by
      have := two_pow_le_pieceM k
      have : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      omega
    apply Real.log_nonneg
    rw [hXM]
    have hXR : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1
    have hMR : (1 : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast hM1
    nlinarith [hXR, hMR]
  have hlogN0 : (0 : ℝ) ≤ Real.log ((2 ^ k : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this
  have hbr := box_bracket_mono hK hL0 hlogN0
  have hLpow : (0 : ℝ) ≤ (Real.log XM) ^ (13 : ℝ) := Real.rpow_nonneg hL0 _
  gcongr

theorem boxPriceKerrY_mono {K1 K2 : ℝ} (hK : K1 ≤ K2) (y k i : ℕ) :
    boxPriceKerrY K1 y k i ≤ boxPriceKerrY K2 y k i := by
  unfold boxPriceKerrY
  set XM : ℝ := ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ) with hXM
  have hXM0 : (0 : ℝ) ≤ XM := by rw [hXM]; positivity
  have hL0 : (0 : ℝ) ≤ Real.log XM := by
    have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
      have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hM1 : (1 : ℕ) ≤ pieceM k := by
      have := two_pow_le_pieceM k
      have : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      omega
    apply Real.log_nonneg
    rw [hXM]
    have hXR : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1
    have hMR : (1 : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast hM1
    nlinarith [hXR, hMR]
  -- here the third argument of the Kerr minima is `Real.log (y:ℝ)`, possibly zero (y small)
  by_cases hy1 : (1 : ℝ) ≤ (y : ℝ)
  · have hlogY0 : (0 : ℝ) ≤ Real.log (y : ℝ) := Real.log_nonneg hy1
    have hbr := box_bracket_mono hK hL0 hlogY0
    have hLpow : (0 : ℝ) ≤ (Real.log XM) ^ (13 : ℝ) := Real.rpow_nonneg hL0 _
    gcongr
  · -- y = 0: log 0 = 0, so the Kerr minima are 0 for both K; handle via nonneg of denom
    have hy1' : (y : ℝ) < 1 := not_le.mp hy1
    have hylog : Real.log (y : ℝ) = 0 := by
      rcases Nat.eq_zero_or_pos y with hy0 | hypos
      · simp [hy0]
      · exfalso
        have : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hypos
        linarith
    rw [hylog]
    have hbr := box_bracket_mono hK hL0 (le_refl (0 : ℝ))
    have hLpow : (0 : ℝ) ≤ (Real.log XM) ^ (13 : ℝ) := Real.rpow_nonneg hL0 _
    gcongr

theorem lowPriceK_mono {K1 K2 : ℝ} (hK : K1 ≤ K2) (z x y K k : ℕ) :
    lowPriceK K1 z x y K k ≤ lowPriceK K2 z x y K k := by
  unfold lowPriceK
  exact Finset.sum_le_sum (fun i _ => boxPriceKerr_mono hK k i)

theorem symPriceK_mono {Kb1 Kb2 Km1 Km2 : ℝ} (hKb : Kb1 ≤ Kb2) (hKm : Km1 ≤ Km2)
    (z x y K k : ℕ) :
    symPriceK Kb1 Km1 z x y K k ≤ symPriceK Kb2 Km2 z x y K k := by
  unfold symPriceK
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs with h
  · exact boxPriceKerrY_mono hKm y k i
  · exact boxPriceKerr_mono hKb k i

/-! ## §2 — the crude `tripleSum ≤ 16·x` at the operating point

`card_tripleSet_le_pairSum` bounds the switch count by the pair sum of inner prime counts;
each inner count `primeCountIoc (Lfun) (Ufun) ≤ Ufun = ⌊x/(q₁q₂)⌋ ≤ x/(q₁q₂)`, and the
landed `pairSum_le_at_op` caps `∑ 1/(q₁q₂) ≤ 16`.  This is the polylog `htriple` input the
CE→RCE collapse (`PackA.hRCE_at_op`) consumes. -/

theorem tripleSum_le_16x_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    tripleSum x (opZ x) (opY x) ≤ 16 * (x : ℝ) := by
  obtain ⟨xp, hp⟩ := pairSum_le_at_op
  refine ⟨max xp 1, fun x hx => ?_⟩
  have hxp : xp ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
  rw [tripleSum_eq_card]
  calc ((tripleSet x (opZ x) (opY x)).card : ℝ)
      ≤ ∑ q ∈ pairSet x (opZ x) (opY x), primeCountIoc (Lfun x q) (Ufun x q) :=
        card_tripleSet_le_pairSum _ _ _
    _ ≤ ∑ q ∈ pairSet x (opZ x) (opY x), (x : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have hle1 : primeCountIoc (Lfun x q) (Ufun x q) ≤ ((Ufun x q : ℕ) : ℝ) := by
          rw [primeCountIoc]
          have hc : ((Finset.Ioc (Lfun x q) (Ufun x q)).filter (fun p => p.Prime)).card
              ≤ (Finset.Ioc (Lfun x q) (Ufun x q)).card := Finset.card_filter_le _ _
          have hcard : (Finset.Ioc (Lfun x q) (Ufun x q)).card = Ufun x q - Lfun x q :=
            Nat.card_Ioc _ _
          have hfin : ((Finset.Ioc (Lfun x q) (Ufun x q)).filter (fun p => p.Prime)).card
              ≤ Ufun x q := by rw [hcard] at hc; omega
          exact_mod_cast hfin
        have hle2 : ((Ufun x q : ℕ) : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)) := by
          rw [Ufun]
          calc ((x / (q.1 * q.2) : ℕ) : ℝ)
              ≤ (x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ) := Nat.cast_div_le
            _ = (x : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)) := by push_cast; ring
        exact le_trans hle1 hle2
    _ = (x : ℝ) * ∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * (q.2 : ℝ)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun q _ => ?_); ring
    _ ≤ (x : ℝ) * 16 := mul_le_mul_of_nonneg_left (hp x hxp) hxpos
    _ = 16 * (x : ℝ) := by ring

/-! ## §3 — arg-free restatements of the price dischargers (the extraction the wiring needs)

`box_price_at_op` / `sym_price_at_op` / `low_price_at_op` (AssembleA3/A3b) fix `Ps`/`X`/`K`/`D`
*before* their `∀ x`, so at the operating point (where those are `opPs x`/`2x`/`…`/`opQ·opDlev x`,
all x-dependent) their `∃ Kc x₁` witnesses are per-`x`-opaque: they cannot be "destructured
first" for an x-independent tower closure.  The underlying terminals
(`medium_box_price_at_op_lo`/`_band`/`middle_medium_box_price_at_y`) ARE arg-free, so the fix is
a mechanical restatement moving `Ps`/`X`/`K`/`D` *inside* the `∃`.  This section lands the box
leg (`box_price_indep`); the low/sym legs follow the same template (see the report). -/

set_option maxHeartbeats 1600000 in -- verbatim `box_price_at_op` body: deep per-box row bundle
open Classical in
/-- **`box_price_indep` — the arg-free box discharger.**  `box_price_at_op` with `Ps`/`K`/`D`
moved inside the `∃ Kc x₁`, so `(Kc, x₁)` are genuinely x-independent handles (they come from the
arg-free terminal `medium_box_price_at_op_lo`).  Body copied verbatim from `box_price_at_op`. -/
theorem box_price_indep : ∃ (Kc x₁ : ℝ), 0 < Kc ∧
    ∀ (Ps : ℕ), 0 < Ps → Nat.Coprime opQ Ps → Nat.Coprime opQ (opA + 2) →
      (∀ p ∈ Ps.primeFactors, 3 ≤ p) → ∀ (K : ℕ) (QR : ℝ) (Dlev D : ℕ),
        (opQ : ℝ) * (QR * (Dlev : ℝ)) ≤ (D : ℝ) →
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
                  ‖apDiscBilinCutoff
                      (restrictAlpha (restrictAlpha (blockAlpha (opZ x) (opY x) ε₀ j) 0
                        (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                      (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                      (crtClassW opQ (m / opQ) opA) m (x / 2 + 1)‖)
              ≤ boxPriceKerr Kc k i := by
  classical
  obtain ⟨Kc, N₀, hK0, hcore⟩ := medium_box_price_at_op_lo
  obtain ⟨xrows, hrows⟩ := box_rows_at_op
  have hQ1 : 1 ≤ opQ := opf_Q_pos
  refine ⟨Kc, max (max xrows (Real.exp (10 ^ 9))) (((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7)),
    hK0, fun Ps hPspos hQPs hQa2 hPodd K QR Dlev D hDbnd x ε₀ hx₁ hDlo hDhi j k i hi => ?_⟩
  have hxrows : xrows ≤ (x : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx₁
  have hxexp : Real.exp (10 ^ 9) ≤ (x : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx₁
  have hxN₀ : ((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7) ≤ (x : ℝ) :=
    le_trans (le_max_right _ _) hx₁
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hxexp
  have hexp1 : (1 : ℝ) ≤ Real.exp (10 ^ 9) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := le_trans hexp1 hxexp
  have hzR : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [opZ]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  set c : ℕ := min (opZ x * pieceN k + 1) (x + 1) with hc
  by_cases hlive : c ≤ 2 ^ i
  · -- VANISHING branch: `2^i ≥ cap` ⟹ carrier `= 0` ⟹ both sums `= 0`
    have hvanish : ∀ (T : ℕ),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
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
    have hkf : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ) :=
      kfloor_of_live_box hx1R hi hlive' hzR
    have hfloorbig : ((N₀ + 4 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) / 8 := by
      have h8 : ((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7) ≤ (x : ℝ) := hxN₀
      have hbase : (0 : ℝ) ≤ ((8 * (N₀ + 4) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpow : ((8 * (N₀ + 4) : ℕ) : ℝ)
          = (((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7)) ^ ((7 : ℝ) / 16) := by
        rw [← Real.rpow_mul hbase, show (16 : ℝ) / 7 * ((7 : ℝ) / 16) = 1 by norm_num,
          Real.rpow_one]
      have hmono : (((8 * (N₀ + 4) : ℕ) : ℝ) ^ ((16 : ℝ) / 7)) ^ ((7 : ℝ) / 16)
          ≤ (x : ℝ) ^ ((7 : ℝ) / 16) :=
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
    obtain ⟨hxt, hNfloor, hL2, hX2, hD1, hDge_x, hDscale, hDsq, habs, hXsqrt, hMsqrt,
        herr_lev, herr_Mlev, hFX, hDx, hLbb, hfloor, hDXM⟩ :=
      hrows x hxrows k i (2 ^ (i + 1) - 1) (opZ x * opY x) K D (Real.log (4 * (x : ℝ)))
        rfl hi rfl hlive' rfl hDlo hDhi
    have hα := norm_box_leg_le_one (opZ x) (opY x) ε₀ j (min (opZ x * pieceN k + 1) (x + 1)) i
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
      (hcore x (Real.log (4 * (x : ℝ))) (opZ x * opY x) K k i _ (2 ^ (i + 1) - 1) x D _
        (fun m => crtClassW opQ (m / opQ) opA) hk hxt hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀ hL2
        hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor hDXM)
      (hcore x (Real.log (4 * (x : ℝ))) (opZ x * opY x) K k i _ (2 ^ (i + 1) - 1) (x / 2 + 1) D _
        (fun m => crtClassW opQ (m / opQ) opA) hk hxt hi rfl hNfloor hα hd1 hcop2 hDsetD hN₀ hL2
        hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor hDXM)

end Salt.Chen
