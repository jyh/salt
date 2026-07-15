/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.FinA3b
import Salt.Chen.Headline4
import Salt.Chen.AggSum
import Salt.Chen.AggCE
import Salt.Chen.AggDiag
import Salt.Chen.PackA
import Salt.Chen.TheHeadline
import Salt.Chen.H4Cond

/-!
# Node FIN-A3c — the piecewise assembly → `hA3_bundle`

Closes the A₃ side.  Instantiates `PDiag`'s `hBVblocksW_discharge' ∘ mainA3_of_block_remainders_W`
at the operating witnesses to produce

  `hA3_bundle : ∃ x₁, ∀ x ≥ x₁, triplePrimeSumW opQ opA x (opP x) (opY x) ≤ M3 x`.

* **The piecewise Price** (`PriceBoxOp` / `PriceLowOp`): the box and low prices routed to `0` in
  the box-vanish / low-vanish regimes (the small-`2^k` boxes blow the closed Kerr price up, so the
  uniform-`W` bound only holds in the LIVE regime).  `priceBoxOp_le` / `priceLowOp_le` are the
  uniform `≤ W` bounds; sym is `W`-uniform (`symPriceK_worst_le` directly).
* **The assembly** (`hA3_bundle`): destructures the three arg-free dischargers `box_price_indep` /
  `low_price_indep` / `sym_price_indep` (`FinA3`/`FinA3b`), bumps their constants to a single
  `Khat ≥ 1`, and feeds the `PDiag`:782 composition at `z = opZ x`, `y = opY x`, `Ps = opPs x`,
  `Dlev = opDlev x`, `ε = opEps`, `ε₀ = (x : ℝ)`, `X = 2x`, `K = Nat.log 2 (2x)`.

New file; imports `FinA3b` + concrete modules only (never `Salt.Chen.All`).
Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §1 — the piecewise box / low prices (the load-bearing risk) -/

/-- The **piecewise box price**: `0` in the box-vanish regime (`min (opZ x·pieceN k + 1) (x+1) ≤
2^i`, where the doubly-restricted carrier is identically zero), else the closed Kerr price
`boxPriceKerr Kc k i`. -/
noncomputable def PriceBoxOp (Kc : ℝ) (x k i : ℕ) : ℝ :=
  if min (opZ x * pieceN k + 1) (x + 1) ≤ 2 ^ i then 0 else boxPriceKerr Kc k i

/-- The **piecewise low price**: `0` in the low-vanish regime (`pieceN k ≤ opY x`, where the low
band carrier is identically zero), else the closed per-piece low price `lowPriceK Kb`. -/
noncomputable def PriceLowOp (Kb : ℝ) (KK x k : ℕ) : ℝ :=
  if pieceN k ≤ opY x then 0 else lowPriceK Kb (opZ x) x (opY x) KK k

/-- The **uniform box-price bound** at the LIVE regime: each piecewise box price is
`≤ CconBox·Kc·x/(log x)^12`.  Vanish → `0`; live → `boxPriceKerr_worst_le` at the box `k`-floor
`x^{7/16}/8 ≤ 2^k` (`kfloor_of_live_box` + `ratio_le_of_floor` at `c = 7/16`, `margin_box`). -/
theorem priceBoxOp_le {x : ℕ} {Kc : ℝ} {KK k i : ℕ}
    (hKc : 1 ≤ Kc) (hx2 : 2 ≤ x) (hlogx : (400 : ℝ) ≤ Real.log x)
    (hx1R : (1 : ℝ) ≤ (x : ℝ)) (hzR : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8))
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) KK) :
    PriceBoxOp Kc x k i ≤ CconBox * Kc * (x : ℝ) / (Real.log x) ^ 12 := by
  unfold PriceBoxOp
  split_ifs with hvan
  · exact div_nonneg (mul_nonneg (mul_nonneg CconBox_nonneg (by linarith)) (Nat.cast_nonneg _))
      (by positivity)
  · rw [not_le] at hvan
    have hlive : 2 ^ i < opZ x * pieceN k + 1 := lt_of_lt_of_le hvan (min_le_left _ _)
    have hkf : (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ) :=
      kfloor_of_live_box hx1R hi hlive hzR
    obtain ⟨hlo, hhi⟩ := boundary_XM_raw hi
    obtain ⟨-, hLup⟩ := xm_log_bounds hx2 hlo hhi
    have hratio := ratio_le_of_floor hx2 hLup hkf (margin_box (by linarith))
    exact boxPriceKerr_worst_le hKc hx2 (by linarith) hi hratio

/-- The **uniform low-price bound** at the LIVE regime: each piecewise low price is
`≤ 3·CconBox·Kb·x/(log x)^12`.  Vanish → `0`; live (`opY x < pieceN k`) → `lowPriceK_worst_le` at
the band `k`-floor `x^{1/3}/8 ≤ 2^k` (`band_kfloor_of_live`). -/
theorem priceLowOp_le {x : ℕ} {Kb : ℝ} {KK k : ℕ}
    (hKb : 1 ≤ Kb) (hx2 : 2 ≤ x) (hlogx : (400 : ℝ) ≤ Real.log x)
    (hyfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (opY x : ℝ)) :
    PriceLowOp Kb KK x k ≤ 3 * CconBox * Kb * (x : ℝ) / (Real.log x) ^ 12 := by
  unfold PriceLowOp
  split_ifs with hvan
  · exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) CconBox_nonneg)
      (by linarith)) (Nat.cast_nonneg _)) (by positivity)
  · rw [not_le] at hvan
    have hylt2 : opY x < 2 ^ k := lt_two_pow_of_lt_pieceN hvan
    exact lowPriceK_worst_le (opZ x) (opY x) hKb hx2 hlogx (band_kfloor_of_live hyfloor hylt2)

/-! ## §2 — the assembly: `hA3_bundle` -/

set_option maxHeartbeats 1600000 in -- deep op-point composition: ~30 discharger hypotheses at op
/-- **`hA3_bundle` — the A₃ carrier bundle.**  Instantiates `hBVblocksW_discharge' ∘
`mainA3_of_block_remainders_W` (`PDiag`:782 template) at the operating witnesses.  The three
arg-free price dischargers (`box_price_indep`/`low_price_indep`/`sym_price_indep`) are bumped to a
single constant `Khat ≥ 1`; the box and low legs are routed to the piecewise `PriceBoxOp`/
`PriceLowOp` (`0` in the vanish regimes), sym is `W`-uniform.  The aggregate closes via the tower
(`hNum_close_of_tower` at `Cconst`, folded into the threshold). -/
theorem hA3_bundle : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    triplePrimeSumW opQ opA x (opP x) (opY x) ≤ M3 x := by
  classical
  -- the three arg-free price dischargers
  obtain ⟨KcB, xB, hKcB, hboxbody⟩ := box_price_indep
  obtain ⟨KbL, xL, hKbL, hlowbody⟩ := low_price_indep
  obtain ⟨KbS, KmS, xS, hKbS, hKmS, hsymbody⟩ := sym_price_indep
  -- the remaining ∃-threshold suppliers
  obtain ⟨xt, _hxt8, htower⟩ := opf_tower
  obtain ⟨xf, hfloors⟩ := op_floors
  obtain ⟨xd, hdiag_slot⟩ := hdiag_slot_at_op
  obtain ⟨xnu, hnu⟩ := nu_sum_le_log_at_op
  obtain ⟨xtr, htr16⟩ := tripleSum_le_16x_at_op
  obtain ⟨xlp, hlp⟩ := a12_logpow_le_rpow 17 ((1 : ℝ) / 8) (by norm_num) (by norm_num)
  -- the single bumped price constant `Khat ≥ 1`, dominating each of `KcB`/`KbL`/`KbS`/`KmS`
  set Khat : ℝ := max (max 1 KcB) (max (max KbL KbS) KmS) with hKhatdef
  have hKhat1 : (1 : ℝ) ≤ Khat := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKhatB : KcB ≤ Khat := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKhatL : KbL ≤ Khat :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hKhatS : KbS ≤ Khat :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hKhatM : KmS ≤ Khat := le_trans (le_max_right _ _) (le_max_right _ _)
  have hKhat0 : (0 : ℝ) ≤ Khat := le_trans (by norm_num) hKhat1
  -- the aggregate closure constant `Cconst ≥ 1`
  set Cconst : ℝ := max 1 (9 * (6 * CconBox * Khat) + 1 / 2) with hCconstdef
  have hCconst1 : (1 : ℝ) ≤ Cconst := le_max_left _ _
  -- the operating threshold
  refine ⟨max (max (max ⌈xB⌉₊ ⌈xL⌉₊) (max ⌈xS⌉₊ xt))
            (max (max (max xf xd) (max xnu xtr))
              (max (max xlp ⌈Real.exp 400⌉₊) (max ⌈Real.exp (2 * Cconst)⌉₊ 65536))),
    fun x hx => ?_⟩
  -- extract every threshold ≤ x
  have s0 := le_trans (Nat.le_max_left _ _) hx
  have s1 := le_trans (Nat.le_max_right _ _) hx
  have hcB := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _) s0)
  have hcL := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _) s0)
  have hcS := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) s0)
  have hxt := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) s0)
  have s10 := le_trans (Nat.le_max_left _ _) s1
  have s11 := le_trans (Nat.le_max_right _ _) s1
  have hxf := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _) s10)
  have hxd := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _) s10)
  have hxnu := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) s10)
  have hxtr := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) s10)
  have hxlp := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _) s11)
  have hexp400 := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _) s11)
  have hexp2c := le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) s11)
  have h65536 := le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) s11)
  -- the global scale facts
  have hxexp400 : Real.exp 400 ≤ (x : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hexp400)
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hxexp400
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hxexp400
  have hlogx400 : (400 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hxexp400; rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log x := hlogpos.le
  have hLpos11 : (0 : ℝ) < (Real.log x) ^ 11 := pow_pos hlogpos 11
  have hLpos12 : (0 : ℝ) < (Real.log x) ^ 12 := pow_pos hlogpos 12
  have hx2R : (2 : ℝ) ≤ (x : ℝ) :=
    le_trans (by linarith [Real.add_one_le_exp (400 : ℝ)]) hxexp400
  have hx2 : 2 ≤ x := by exact_mod_cast hx2R
  -- the tower / floor facts
  obtain ⟨-, -, hw'z, hz3, -, -, -, hyx2, -, -, hStop3, hDlev2, -, -, -, -, -⟩ := htower x hxt
  obtain ⟨hDlow, hDhi, -, -, hyfloor⟩ := hfloors x hxf
  have hz1 : 1 ≤ opZ x := by omega
  have hz2 : 2 ≤ opZ x := by omega
  have hzR : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [opZ]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hw'2 : 2 ≤ opW' := le_trans (by norm_num) opf_w'3
  have hxlo : x / 2 + 1 ≤ x := by omega
  have hxX : x ≤ 2 * x := by omega
  -- the operating witnesses (`KK = ⌊log₂ 2x⌋`) and the shared conductor bound
  set KK : ℕ := Nat.log 2 (2 * x) with hKKdef
  have hxB_le : xB ≤ (x : ℝ) := le_trans (Nat.le_ceil xB) (by exact_mod_cast hcB)
  have hxL_le : xL ≤ (x : ℝ) := le_trans (Nat.le_ceil xL) (by exact_mod_cast hcL)
  have hxS_le : xS ≤ (x : ℝ) := le_trans (Nat.le_ceil xS) (by exact_mod_cast hcS)
  have hDbnd : (opQ : ℝ) * ((1 : ℝ) * (opDlev x : ℝ)) ≤ ((opQ * opDlev x : ℕ) : ℝ) :=
    le_of_eq (by push_cast; ring)
  -- the box price slot (piecewise: vanish → 0, live → `box_price_indep` then mono)
  have hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) KK,
      (∑ m ∈ ((Nat.divisors (opPs x)).filter (fun d : ℕ => (d : ℝ) < (1 : ℝ) * (opDlev x))).image
            (fun d => opQ * d),
          ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha (opZ x) (opY x) (x : ℝ) j) 0
                (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
              (crtClassW opQ (m / opQ) opA) m x‖)
        + (∑ m ∈ ((Nat.divisors (opPs x)).filter
              (fun d : ℕ => (d : ℝ) < (1 : ℝ) * (opDlev x))).image (fun d => opQ * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha
                  (blockAlpha (opZ x) (opY x) (x : ℝ) j) 0
                  (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW opQ (m / opQ) opA) m (x / 2 + 1)‖)
        ≤ PriceBoxOp Khat x k i := by
    intro j k i hi
    unfold PriceBoxOp
    split_ifs with hvan
    · have hz0 : ∀ (T : ℕ),
          (∑ m ∈ ((Nat.divisors (opPs x)).filter
                (fun d : ℕ => (d : ℝ) < (1 : ℝ) * (opDlev x))).image (fun d => opQ * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha
                    (blockAlpha (opZ x) (opY x) (x : ℝ) j)
                    0 (min (opZ x * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW opQ (m / opQ) opA) m T‖) = 0 := by
        intro T
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [box_carrier_eq_zero_above_cap (α := blockAlpha (opZ x) (opY x) (x : ℝ) j) hvan
          (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k) (crtClassW opQ (m / opQ) opA) m T,
          norm_zero]
      rw [hz0 x, hz0 (x / 2 + 1)]; norm_num
    · have hb := hboxbody (opPs x) (opf_Ps_pos x) (opf_QPs x) opf_Qa2 (opf_Psodd x) KK (1 : ℝ)
        (opDlev x) (opQ * opDlev x) hDbnd x (x : ℝ) hxB_le hDlow hDhi j k i hi
      exact le_trans hb (boxPriceKerr_mono hKhatB k i)
  -- the sym price slot (`sym_price_indep` then mono; `W`-uniform)
  have hpriceSym : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
      (∑ m ∈ ((Nat.divisors (opPs x)).filter (fun d : ℕ => (d : ℝ) < (1 : ℝ) * (opDlev x))).image
            (fun d => opQ * d),
          ‖apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) (x : ℝ) j (pieceN k) (pieceM k))
              (blockPrimeInd (max (opY x) (pieceN k))) (2 * x) (pieceM k)
              (crtClassW opQ (m / opQ) opA) m x
            - apDiscBilinCutoff (blockAlphaSym (opZ x) (opY x) (x : ℝ) j (pieceN k) (pieceM k))
              (blockPrimeInd (max (opY x) (pieceN k))) (2 * x) (pieceM k)
              (crtClassW opQ (m / opQ) opA) m (x / 2 + 1)‖)
        ≤ symPriceK Khat Khat (opZ x) x (opY x) KK k := by
    intro j k hk
    have hs := hsymbody (opPs x) (opf_Ps_pos x) (opf_QPs x) opf_Qa2 (opf_Psodd x) (2 * x) KK (1 : ℝ)
      (opDlev x) (opQ * opDlev x) le_rfl hDbnd x (x : ℝ) hxS_le hxX hDlow hDhi j k hk
    exact le_trans hs (symPriceK_mono hKhatS hKhatM (opZ x) x (opY x) KK k)
  -- the low price slot (piecewise: vanish → 0, live → `low_price_indep` then mono)
  have hpriceLow : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
      (∑ m ∈ ((Nat.divisors (opPs x)).filter (fun d : ℕ => (d : ℝ) < (1 : ℝ) * (opDlev x))).image
            (fun d => opQ * d),
          ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) (x : ℝ) j (pieceN k))
                (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
              (blockPrimeInd (pieceN k)) (2 * x) (pieceM k) (crtClassW opQ (m / opQ) opA) m x
            - apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) (x : ℝ) j (pieceN k))
                (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
              (blockPrimeInd (pieceN k)) (2 * x) (pieceM k) (crtClassW opQ (m / opQ) opA) m
              (x / 2 + 1)‖)
        ≤ PriceLowOp Khat KK x k := by
    intro j k hk
    unfold PriceLowOp
    split_ifs with hvan
    · have hzero : ∀ (T m : ℕ),
          apDiscBilinCutoff (restrictAlpha (blockAlphaLow (opZ x) (opY x) (x : ℝ) j (pieceN k))
                (min (opZ x * pieceN k + 1) (x + 1)) (x + 1))
              (blockPrimeInd (pieceN k)) (2 * x) (pieceM k) (crtClassW opQ (m / opQ) opA) m T
            = 0 := by
        intro T m
        rw [apDiscBilinCutoff_congr (α' := fun _ => 0)
          (fun m' _ => by
            have hz : blockAlphaLow (opZ x) (opY x) (x : ℝ) j (pieceN k) m' = 0 :=
              blockAlphaLow_eq_zero_of_pieceN_le hvan
            unfold restrictAlpha; rw [hz]; simp),
          apDiscBilinCutoff_zero]
      refine le_of_eq (Finset.sum_eq_zero (fun m _ => ?_))
      rw [hzero x m, hzero (x / 2 + 1) m, sub_zero, norm_zero]
    · have hl := hlowbody (opPs x) (opf_Ps_pos x) (opf_QPs x) opf_Qa2 (opf_Psodd x) (2 * x) KK
        (1 : ℝ) (opDlev x) (opQ * opDlev x) le_rfl hDbnd x (x : ℝ) hxL_le hxX hDlow hDhi j k hk
      exact le_trans hl (lowPriceK_mono hKhatL (opZ x) x (opY x) KK k)
  -- the `hiX` structural row
  have hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) KK,
      2 ^ (i + 1) ≤ 2 * x + 1 := by
    intro k i hi
    rw [dyadicBoundary, Finset.mem_filter] at hi
    obtain ⟨-, hcorner, -, -⟩ := hi
    have h2i : 2 ^ i ≤ x := by
      calc 2 ^ i = 2 ^ i * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ i * (pieceN k + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ x := hcorner
    rw [pow_succ]; omega
  -- the `hSum` aggregate at the single operating block
  have hmax : maxBlock x (opZ x) (x : ℝ) = 0 := maxBlock_op_eq_zero hz1 hx2
  have hcount : (Nat.log 2 x : ℝ) + 1 ≤ 2 * Real.log x := nat_log2_count_le hx2 (by linarith)
  have hW0 : (0 : ℝ) ≤ 6 * CconBox * Khat * (x : ℝ) / (Real.log x) ^ 12 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) CconBox_nonneg) hKhat0) hxpos.le)
      hLpos12.le
  have hbox : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
      ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (opZ x * opY x) KK,
      PriceBoxOp Khat x k i ≤ 6 * CconBox * Khat * (x : ℝ) / (Real.log x) ^ 12 := by
    intro k _ i hi
    refine le_trans (priceBoxOp_le hKhat1 hx2 hlogx400 hx1R hzR hi) ?_
    exact (div_le_div_iff_of_pos_right hLpos12).mpr
      (by nlinarith [mul_nonneg (mul_nonneg CconBox_nonneg hKhat0) hxpos.le])
  have hsym : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
      symPriceK Khat Khat (opZ x) x (opY x) KK k
        ≤ 6 * CconBox * Khat * (x : ℝ) / (Real.log x) ^ 12 := by
    intro k _
    have h1 := symPriceK_worst_le (k := k) (K := KK) (opZ x) (opY x) hKhat1 hKhat1 hx2 hlogx400
      hyfloor
    have he : (3 : ℝ) * CconBox * (Khat + Khat) * (x : ℝ) / (Real.log x) ^ 12
        = 6 * CconBox * Khat * (x : ℝ) / (Real.log x) ^ 12 := by ring
    rwa [he] at h1
  have hlow : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
      PriceLowOp Khat KK x k ≤ 6 * CconBox * Khat * (x : ℝ) / (Real.log x) ^ 12 := by
    intro k _
    refine le_trans (priceLowOp_le (k := k) (KK := KK) hKhat1 hx2 hlogx400 hyfloor) ?_
    exact (div_le_div_iff_of_pos_right hLpos12).mpr
      (by nlinarith [mul_nonneg (mul_nonneg CconBox_nonneg hKhat0) hxpos.le])
  have hWbound : 6 * CconBox * Khat * (x : ℝ) / (Real.log x) ^ 12
      ≤ (6 * CconBox * Khat) * (1 : ℝ) * (x : ℝ) / (Real.log x) ^ 12 := le_of_eq (by ring)
  have hPdiag : opPdiag x ≤ (1 : ℝ) * (1 : ℝ) * (x : ℝ) / (Real.log x) ^ 11 := by
    rw [one_mul, one_mul]; exact (hdiag_slot x hxd).2
  have hSum := hSum_at_op x (opZ x) (opY x) KK (x : ℝ) (1 : ℝ)
    (fun _j k i => PriceBoxOp Khat x k i) (fun _j k => symPriceK Khat Khat (opZ x) x (opY x) KK k)
    (fun _j k => PriceLowOp Khat KK x k) (opPdiag x)
    (6 * CconBox * Khat * (x : ℝ) / (Real.log x) ^ 12) (6 * CconBox * Khat) (1 : ℝ)
    hmax (by norm_num) hlogpos hW0 hbox hsym hlow hWbound hPdiag hcount
  -- the `hCE` crumb
  have hQfac : ∀ p ∈ opQ.primeFactors, p < opW' := by
    intro p hp
    rw [opf_Q_primeFactors, Finset.mem_filter, Finset.mem_range] at hp; exact hp.1
  have hCEsum := hCE_at_op x (opZ x) (opY x) opQ (opPs x) opW' (1 : ℝ) (opDlev x) (opf_Ps_sq x)
    hz2 hx2 opf_Q_pos (opf_QPs x) hQfac (opf_Psy x) hw'z
  have hSigma : (∑ d ∈ Nat.divisors (opPs x), nuChen d) ≤ Real.log x := hnu x hxnu
  have htriple : tripleSum x (opZ x) (opY x) ≤ (x : ℝ) * (Real.log x) ^ 4 := by
    have h2 : (2 : ℝ) ≤ Real.log x := by linarith
    have hL4 : (16 : ℝ) ≤ (Real.log x) ^ 4 := by
      calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        _ ≤ (Real.log x) ^ 4 := by gcongr
    calc tripleSum x (opZ x) (opY x) ≤ 16 * (x : ℝ) := htr16 x hxtr
      _ = (x : ℝ) * 16 := by ring
      _ ≤ (x : ℝ) * (Real.log x) ^ 4 := mul_le_mul_of_nonneg_left hL4 hxpos.le
  have hz1pos : (0 : ℝ) < (opZ x : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (opZ x : ℝ) := by exact_mod_cast hz3
    linarith
  have hzlow : (x : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ (opZ x : ℝ) - 1 := by
    have hzfl : (x : ℝ) ^ ((1 : ℝ) / 8) < (opZ x : ℝ) + 1 := by
      rw [opZ]; exact Nat.lt_floor_add_one _
    have h48 : (4 : ℝ) ^ (8 : ℝ) = 65536 := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hbase : ((65536 : ℝ)) ^ ((1 : ℝ) / 8) = 4 := by
      rw [← h48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        show (8 : ℝ) * ((1 : ℝ) / 8) = 1 by norm_num, Real.rpow_one]
    have hx65536 : (65536 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h65536
    have hx18ge4 : (4 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [← hbase]; exact Real.rpow_le_rpow (by norm_num) hx65536 (by norm_num)
    linarith
  have hkey : 2 * (Real.log x) ^ (4 + 12) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    have hlp17 : (Real.log x) ^ (17 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := hlp x hxlp
    have hconv : (Real.log x) ^ (17 : ℝ) = (Real.log x) ^ (17 : ℕ) := by
      rw [show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h216 : 2 * (Real.log x) ^ (16 : ℕ) ≤ (Real.log x) ^ (17 : ℕ) := by
      have he : (Real.log x) ^ (17 : ℕ) = Real.log x * (Real.log x) ^ (16 : ℕ) := by ring
      rw [he]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.log x - 2 by linarith) (pow_nonneg hlogx0 16)]
    have hstep : (Real.log x) ^ (17 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by rw [← hconv]; exact hlp17
    exact le_trans h216 hstep
  have hCE := le_trans hCEsum (hRCE_at_op (x := x) (z := opZ x) (y := opY x) (Q := opQ)
    (Ps := opPs x) (Kc := 1) (Ccon := Cconst) (C := 4) hx2 hlogpos
    (by rw [mul_one]; exact hCconst1) hSigma htriple hz1pos hzlow hkey)
  -- the `hNum` closure via the tower
  have htower2 : 2 * (Cconst * (1 : ℝ)) ≤ Real.log x := by
    rw [mul_one]
    have hle : Real.exp (2 * Cconst) ≤ (x : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hexp2c)
    have := Real.log_le_log (Real.exp_pos _) hle; rwa [Real.log_exp] at this
  have hRHD : (9 * (6 * CconBox * Khat) + 1 / 2) * (1 : ℝ) * (x : ℝ) / (Real.log x) ^ 11
      ≤ Cconst * (1 : ℝ) * (x : ℝ) / (Real.log x) ^ 11 := by
    refine (div_le_div_iff_of_pos_right hLpos11).mpr ?_
    have hle : (9 * (6 * CconBox * Khat) + 1 / 2) * (1 : ℝ) ≤ Cconst * (1 : ℝ) := by
      rw [mul_one, mul_one]; exact le_max_right _ _
    exact mul_le_mul_of_nonneg_right hle hxpos.le
  have hNum := hNum_close_of_tower (Ccon := Cconst) (K := 1) hxpos.le hlogpos hRHD (le_refl _)
    htower2
  -- compose
  refine mainA3_of_block_remainders_W x (opZ x) (opY x) (opP x) opQ opA opW' (opPs x) (opDlev x)
    (x : ℝ) opEps (1 + opEps) (1 : ℝ) hz1 hxpos (opf_Ps_sq x) (opf_Psodd x) (opf_Psy x)
    (opf_Pslow x) hx2 hyx2 opf_Qfull (opf_Pfull' x) opf_Qa2 hDlev2 (le_refl (1 : ℝ)) opf_eps_pos
    opf_w0R3 opf_eps1000 (le_refl (1 + opEps))
    (h4_cond_of_base opEps (1 + opEps) opf_eps_pos.le (le_refl _)) hStop3 ?_
  exact hBVblocksW_discharge' x (opZ x) (opY x) (x : ℝ) opQ opA (opPs x) opW' (opf_Ps_sq x)
    (opf_Psodd x) (opf_QPs x) opf_Q_pos (1 : ℝ) (opDlev x) (2 * x) KK hz1 hx2 hxlo hxX le_rfl hw'2
    (opf_Psw' x) hiX (fun _j k i => PriceBoxOp Khat x k i) hprice
    (fun _j k => symPriceK Khat Khat (opZ x) x (opY x) KK k) (fun _j k => PriceLowOp Khat KK x k)
    hpriceSym hpriceLow (opPdiag x)
    ((9 * (6 * CconBox * Khat) + 1 / 2) * (1 : ℝ) * (x : ℝ) / (Real.log x) ^ 11)
    (Cconst * (1 : ℝ) * (x : ℝ) / (Real.log x) ^ 11) (hdiag_slot x hxd).1 hSum hCE hNum

/-! ## §3 — the compiled headline (F1 consumed; F2 ledger hypothetical) -/

/-- **The Chen headline from the A₃ ledger.**  `hA3_bundle` fills the `hA3` slot of
`chen_headline_of_A3_ledger` character-for-character; with the F2 ledger `hL` (hypothetical) the
twin-almost-prime headline follows. -/
example
    (hL : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        0 < M1 x - M2 x / 2 - M3 x / 2
          - Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1) / 2) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite :=
  chen_headline_of_A3_ledger hA3_bundle hL

end Salt.Chen
