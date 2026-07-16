/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Asm

/-!
# G-ASM §2 — the terminal, fully composed (`gold_hBVblocksW_final`)

`gold_hBVblocksW_discharge'` (PDiag) at the operating point with every supplier plugged:
the box piecewise price (`Final`), the two band prices (`BandPrice`), the geometric
aggregate with the band-tail slot (`BandClose2`) fed the box `hbox`, the crumb towers
(96/144, `BandRows2`), the two band slot wires (§1 + `Close`), `gold_op_hCE`, the honest
diagonal row, and the tower close.  The remaining op-ARITHMETIC rows (the D-floors, the
diag/RCE prices, `hiX`, the scale floors, the log count) enter as named per-`N`
hypotheses; §3 discharges them.  The exposed real `CT` is the x₀(K)-pattern threshold
absorbed into `N₀` by the final wrapper.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset Salt.Chen

namespace Salt.Goldbach

set_option maxHeartbeats 1600000 in
-- the terminal composes ten multi-hypothesis suppliers; the bump is preemptive
set_option linter.unusedVariables false in
-- the giant ∀-telescope trips the linter on named rows (the Final2/BandPrice2 pattern)
/-- **`gold_hBVblocksW_final`** — the A₃ block-BV terminal at op, modulo the named
op-arithmetic rows (§3). -/
theorem gold_hBVblocksW_final : ∃ (CT : ℝ) (x₁ : ℕ), 0 ≤ CT ∧
    ∀ (N : ℕ), x₁ ≤ N →
      CT ≤ Real.log N →
      ∀ a : ℕ, a ≤ N → Nat.Coprime opQ a → Nat.Coprime opQ (N - a) →
      (1 : ℝ) ≤ 1 * (opDlev N : ℝ) →
      ((opQ : ℝ) * (1 * (opDlev N : ℝ)) ≤ ((opD N : ℕ) : ℝ)) →
      (∀ k, (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opD N : ℕ) : ℝ)) →
      (∀ k, ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2)
        ≤ ((opD N : ℕ) : ℝ)) →
      (((opD N : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) →
      ((1 : ℝ) * (opDlev N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) →
      ((Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N) →
      (∀ k' k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) (Nat.log 2 N),
          2 ^ (i + 1) ≤ N + 1) →
      ((opY N : ℝ) * (Nat.sqrt N : ℝ)
          * ((2 : ℝ) ^ Nat.log opW' N + ∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
        ≤ (N : ℝ) / (Real.log N) ^ 11) →
      (nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
          * goldTripleSum N (opZ N) (opY N) / ((opZ N : ℝ) - 1)
        ≤ (N : ℝ) / (Real.log N) ^ 11) →
      2 ≤ N → 1 ≤ opZ N →
      (∑ j ∈ Finset.range (maxBlock N (opZ N) (N : ℝ) + 1),
          rosserRemainder
            (goldBlockSwitchSieveW N (opZ N) (opY N) (N : ℝ) j opQ a (goldOpPs N)
              (goldOpPs_squarefree N) (goldOpPs_odd N))
            (1 * (opDlev N : ℝ)))
        ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  classical
  obtain ⟨KcB, xB, hKcB, hpriceB⟩ := gold_box_hprice_at_min
  obtain ⟨KcS, xS, hKcS, hsymslot⟩ := gold_band_hsym_slot_full
  obtain ⟨KcL, xL, hKcL, hlowslot⟩ := gold_band_hlow_slot_at_op
  obtain ⟨xT, htailT⟩ := gold_box_crumb_tower
  obtain ⟨xBT, hbandT⟩ := gold_band_crumb_tower
  obtain ⟨xCE, hCEop⟩ := gold_op_hCE
  obtain ⟨xH, hhbox⟩ := gold_box_hbox_at_min (Kc := KcB) hKcB
  set KcT : ℝ := max (max KcB KcS) KcL with hKcTdef
  have hKcT1 : (1 : ℝ) ≤ KcT :=
    le_trans hKcB (le_trans (le_max_left _ _) (le_max_left _ _))
  have hKcBT : KcB ≤ KcT := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKcST : KcS ≤ KcT := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKcLT : KcL ≤ KcT := le_max_right _ _
  set CgeoB : ℝ := 3 ^ 12 * gboxConst with hCgeoBdef
  set CbandC : ℝ := 24 * ((4 : ℝ) ^ 12 * gboxConst) with hCbandCdef
  set Ctotal : ℝ := 48 * CgeoB + 96 + 3 * CbandC + 1 / 2 + 144 with hCtotaldef
  have hgb0 : (0 : ℝ) ≤ gboxConst := gboxConst_nonneg
  have hCgeoB0 : (0 : ℝ) ≤ CgeoB := by rw [hCgeoBdef]; positivity
  have hCbandC0 : (0 : ℝ) ≤ CbandC := by rw [hCbandCdef]; positivity
  have hKcT0 : (0 : ℝ) ≤ KcT := le_trans zero_le_one hKcT1
  refine ⟨2 * (max Ctotal 1 * KcT),
    max (max (max xB xS) (max xL xT)) (max (max xBT xCE) xH),
    by positivity, ?_⟩
  intro N hN htower a haN hQa hQNa hb1 hDbnd hDband hDgeB hDsc hbndsc hcount hiX
    hPdiagRow hRCERow hN2 hz1
  have hxB : xB ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hxS : xS ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hxL : xL ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hN
  have hxT : xT ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hN
  have hxBT : xBT ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hxCE : xCE ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hxH : xH ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  -- shared op facts
  have hQ1 : 1 ≤ opQ := by have := opf_Q2; omega
  have hQPs : Nat.Coprime opQ (goldOpPs N) := gold_opQ_coprime_Ps N
  have hPsN : Nat.Coprime (goldOpPs N) N := goldOpPs_coprime_N N
  have hw'2 : 2 ≤ opW' := by have := opf_w'3; omega
  have hPw' : ∀ p ∈ (goldOpPs N).primeFactors, opW' ≤ p :=
    fun p hp => ((goldOpPs_window N p hp).2).1
  have hlogpos : (0 : ℝ) < Real.log N :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast hN2))
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hDsetD : ∀ d ∈ ((Nat.divisors (goldOpPs N)).filter
      (fun d : ℕ => (d : ℝ) < 1 * (opDlev N : ℝ))).image (fun d => opQ * d),
      d ≤ opD N :=
    fun d hd => le_D_of_mem_QImage (1 * ((opDlev N : ℕ) : ℝ)) hQ1 hDbnd hd
  -- the aggregate pieces
  set Wband : ℝ := CbandC * KcT * (N : ℝ) / (Real.log N) ^ 12 with hWbanddef
  have hWband0 : (0 : ℝ) ≤ Wband := by rw [hWbanddef]; positivity
  set Pdiag : ℝ := (opY N : ℝ) * (Nat.sqrt N : ℝ)
      * ((2 : ℝ) ^ Nat.log opW' N + ∑ d ∈ Nat.divisors (goldOpPs N), nuChen d) with hPdiagdef
  -- the geo-grade lift Kc → KcT (shared by the box and band legs)
  have hgeolift : ∀ (Kc C S : ℝ) (cut : ℕ), Kc ≤ KcT → 0 ≤ C →
      S ≤ C * Kc * (cut : ℝ) / (Real.log N) ^ 12 →
      S ≤ C * KcT * (cut : ℝ) / (Real.log N) ^ 12 := by
    intro Kc C S cut hKK hC0 h
    refine le_trans h ?_
    have hcut : (0 : ℝ) ≤ (cut : ℝ) := Nat.cast_nonneg _
    have hlg : (0 : ℝ) ≤ ((Real.log N) ^ 12)⁻¹ := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hcut) hlg
    exact mul_le_mul_of_nonneg_left hKK hC0
  have hNlift : ∀ (Kc C S : ℝ), Kc ≤ KcT → 0 ≤ C →
      S ≤ C * Kc * (N : ℝ) / (Real.log N) ^ 12 →
      S ≤ C * KcT * (N : ℝ) / (Real.log N) ^ 12 := by
    intro Kc C S hKK hC0 h
    refine le_trans h ?_
    have hlg : (0 : ℝ) ≤ ((Real.log N) ^ 12)⁻¹ := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hN0) hlg
    exact mul_le_mul_of_nonneg_left hKK hC0
  -- the terminal application
  refine gold_hBVblocksW_discharge' N (opZ N) (opY N) (N : ℝ) opQ a (goldOpPs N) opW'
    (goldOpPs_squarefree N) (goldOpPs_odd N) hQPs hQ1 haN
    1 (opDlev N) N (Nat.log 2 N)
    hz1 hN2 (Nat.div_le_self _ _) (le_refl _) hw'2 hPw' hiX
    (fun _j k' _k i => goldPriceMin KcB N (opD N) opQ (1 * ((opDlev N : ℕ) : ℝ)) k' i)
    (fun j k' k i hi => hpriceB N hxB (N : ℝ) j k' k i (Nat.log 2 N) opQ a (opD N)
      (goldOpPs N) (opDlev N) 1 hQPs hQNa hPsN hQ1 hb1 hi (hDgeB k) hDsetD)
    (fun j k' => goldPsymK N (Nat.log 2 N) opQ a (goldOpPs N) (N : ℝ)
      (1 * ((opDlev N : ℕ) : ℝ)) j k')
    (fun j k' => goldPlowK N (Nat.log 2 N) opQ a (goldOpPs N) (N : ℝ)
      (1 * ((opDlev N : ℕ) : ℝ)) j k')
    (gold_band_hpriceSym (N : ℝ) (1 * ((opDlev N : ℕ) : ℝ)) (le_refl _)
      (le_trans (by norm_num) hN2) (Nat.div_le_self _ _))
    (gold_band_hpriceLow (N : ℝ) (1 * ((opDlev N : ℕ) : ℝ)) (le_refl _) hiX)
    Pdiag
    (Ctotal * KcT * (N : ℝ) / (Real.log N) ^ 11)
    ((N : ℝ) / (Real.log N) ^ 11)
    (le_of_eq hPdiagdef.symm)
    ?_ ?_ ?_
  · -- hSum: the geometric aggregate with the band-tail slot
    have hagg := gold_hSum_geo_band N (opZ N) (opY N) (Nat.log 2 N) (N : ℝ) KcT
      (fun _j k' _k i => goldPriceMin KcB N (opD N) opQ (1 * ((opDlev N : ℕ) : ℝ)) k' i)
      (fun j k' => goldPsymK N (Nat.log 2 N) opQ a (goldOpPs N) (N : ℝ)
        (1 * ((opDlev N : ℕ) : ℝ)) j k')
      (fun j k' => goldPlowK N (Nat.log 2 N) opQ a (goldOpPs N) (N : ℝ)
        (1 * ((opDlev N : ℕ) : ℝ)) j k')
      (fun k' _k i => goldBtailMinSlot N (opD N) opQ (1 * ((opDlev N : ℕ) : ℝ)) k' i)
      (fun k' => ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) (Nat.log 2 N),
            goldBandBtailSlot (opD N) opQ (1 * ((opDlev N : ℕ) : ℝ)) k' i)
      (fun k' => ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) (Nat.log 2 N),
            goldBandBtailSlot (opD N) opQ (1 * ((opDlev N : ℕ) : ℝ)) k' i)
      Pdiag Wband CgeoB 96 CbandC 1 144
      (maxBlock_op_eq_zero hz1 hN2)
      hKcT0 hlogpos hWband0 hCgeoB0 hCbandC0
      (gold_goldCut_geosum (by omega : 1 ≤ N))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcount
    · exact le_trans hagg (le_of_eq (by rw [hCtotaldef]))
    · -- hbox at KcT (lift the geo part from KcB; the Btail part unchanged)
      intro k' hk' k hk i hi
      have h := hhbox N hxH (opD N) opQ (1 * ((opDlev N : ℕ) : ℝ)) k' k i (Nat.log 2 N) hi
      have hg : CgeoB * KcB * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12
          ≤ CgeoB * KcT * (goldCut N (k + 1) : ℝ) / (Real.log N) ^ 12 := by
        have hcut : (0 : ℝ) ≤ (goldCut N (k + 1) : ℝ) := Nat.cast_nonneg _
        have hlg : (0 : ℝ) ≤ ((Real.log N) ^ 12)⁻¹ := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hcut) hlg
        exact mul_le_mul_of_nonneg_left hKcBT hCgeoB0
      linarith
    · -- htail (the box crumb tower, 96)
      exact htailT N hxT (opD N) opQ (Nat.log 2 N) (1 * ((opDlev N : ℕ) : ℝ)) KcT
        hQ1 hb1 hKcT1 hDsc hbndsc
    · -- hsym at KcT (§1's slot, lifted)
      intro k' hk'
      have h := hsymslot N hxS opQ a (goldOpPs N) (N : ℝ) 1 (opDlev N) (opD N)
        (Nat.log 2 N) hQPs hQNa hPsN hQ1 hb1 hDbnd (fun k _ => hDband k) k' hk'
      refine le_trans h (add_le_add ?_ (le_refl _))
      rw [hWbanddef, hCbandCdef]
      have h24 : (0 : ℝ) ≤ 24 * ((4 : ℝ) ^ 12 * gboxConst) := by positivity
      have hlg : (0 : ℝ) ≤ ((Real.log N) ^ 12)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKcST h24) hN0) hlg
    · -- hlow at KcT (Close's slot, lifted)
      intro k' hk'
      have h := hlowslot N hxL opQ a (goldOpPs N) (N : ℝ) 1 (opDlev N) (opD N)
        (Nat.log 2 N) hQPs hQNa hPsN hQ1 hb1 hDbnd (fun k _ => hDband k) k' hk'
      refine le_trans h (add_le_add ?_ (le_refl _))
      rw [hWbanddef, hCbandCdef]
      have h24 : (0 : ℝ) ≤ 24 * ((4 : ℝ) ^ 12 * gboxConst) := by positivity
      have hlg : (0 : ℝ) ≤ ((Real.log N) ^ 12)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKcLT h24) hN0) hlg
    · -- hbandtail (the band crumb tower, 144)
      exact hbandT N hxBT (opD N) opQ (Nat.log 2 N) (1 * ((opDlev N : ℕ) : ℝ)) KcT
        hQ1 hb1 hKcT1 hDsc hbndsc
    · -- hWband (le_refl at CbandC)
      rw [hWbanddef]
    · -- hPdiag (the row, lifted through 1 ≤ KcT)
      have h1 : Pdiag ≤ (N : ℝ) / (Real.log N) ^ 11 := by rw [hPdiagdef]; exact hPdiagRow
      refine le_trans h1 ?_
      have : (1 : ℝ) * 1 * (N : ℝ) / (Real.log N) ^ 11
          = (N : ℝ) / (Real.log N) ^ 11 := by ring
      calc (N : ℝ) / (Real.log N) ^ 11
          = 1 * 1 * (N : ℝ) / (Real.log N) ^ 11 := by ring
        _ ≤ 1 * KcT * (N : ℝ) / (Real.log N) ^ 11 := by
            have hlg : (0 : ℝ) ≤ ((Real.log N) ^ 11)⁻¹ := by positivity
            rw [div_eq_mul_inv, div_eq_mul_inv]
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hN0) hlg
            nlinarith
  · -- hCE: the op conversion-error row chained with the RCE price
    exact le_trans (hCEop N hxCE 1 (opDlev N)) hRCERow
  · -- hNum: the tower close at the exposed threshold
    refine gold_hNum_close_of_tower (Ccon := max Ctotal 1) (K := KcT) hN0 hlogpos ?_ ?_ ?_
    · -- RHD ≤ (max Ctotal 1)·KcT·N/L^11
      have hCle : Ctotal ≤ max Ctotal 1 := le_max_left _ _
      have hlg : (0 : ℝ) ≤ ((Real.log N) ^ 11)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hN0) hlg
      exact mul_le_mul_of_nonneg_right hCle hKcT0
    · -- RCE ≤ (max Ctotal 1)·KcT·N/L^11
      have h1 : (1 : ℝ) ≤ max Ctotal 1 * KcT := by
        have := le_max_right Ctotal 1
        nlinarith
      calc (N : ℝ) / (Real.log N) ^ 11
          = 1 * ((N : ℝ) / (Real.log N) ^ 11) := by ring
        _ ≤ (max Ctotal 1 * KcT) * ((N : ℝ) / (Real.log N) ^ 11) := by
            refine mul_le_mul_of_nonneg_right h1 ?_
            positivity
        _ = max Ctotal 1 * KcT * (N : ℝ) / (Real.log N) ^ 11 := by ring
    · -- the tower row: the exposed CT
      exact le_trans (le_of_eq (by ring)) htower

end Salt.Goldbach
