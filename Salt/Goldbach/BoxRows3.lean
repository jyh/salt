/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.D0Win2
import Salt.Goldbach.Agg2
import Salt.Chen.AssembleA3

/-!
# G-BOXROWS3 — the z-dependent box-price packagings (Goldbach)

Design: G-BOXROWS2's flag is RESOLVED by D0Win2's z-dependent floor
(`gold_box_price_engine_at_live_z`, whose `hz : z ≤ goldCut^{1/8}` blocker is gone, replaced by the
satisfiable `hz1`/`hz_ratio`/`hDge`).  This file builds the packagings BoxRows2 correctly refused
to build on the false hypothesis.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The LIVE-branch box-price collapse onto `boxPriceKerr` (deliverable 1)

`gold_box_price_engine_at_live_z` (D0Win2 §3) re-exported at the Kerr minima
`Kβ := Kbeta_min Kc L logN 13 18` / `Km := Km_min …` / `Kβ' := Kbeta'_min …`
(`L := log((2^{i+1}−1)·pieceM kp)`, `logN := log(2^kp)`): the three SW-coupling rows
`hcoupG`/`hcoup3`/`herr_book4` are discharged by `gold_box_hcoupG`/`gold_box_hcoup3`/
`gold_box_herr_book4` (BoxRows §1) and the RHS collapses — character-for-character — onto the twin's
closed box price `boxPriceKerr Kc kp i` (reused verbatim at the block scale `2^kp`).  The remaining
analytic scale rows (`hDsq`/`habs`/`hDscale`/`hXsqrt`/`hMsqrt`/`herr_lev`/`herr_Mlev`/`hDXM`/… and
the z-specific `hz1`/`hz_ratio`/`hDge`) stay parametric — their at-op discharge is the annulus-scale
`gold_box_rows_at_op` bundle (the flagged residual, see the report). -/

set_option maxHeartbeats 1600000 in
-- the 39-hypothesis engine application (`gold_box_price_engine_at_live_z`) re-elaborates the long
-- rpow-bearing row list; the whnf/defeq checks (incl. the RHS↔`boxPriceKerr` collapse) need
-- headroom above the default heartbeat budget.
/-- **`gold_box_price_live_kerr` (§1).**  For a LIVE annulus box, the two-cutoff box price
(`T₂`,`T₁`) is `≤ boxPriceKerr Kc kp i` — `gold_box_price_engine_at_live_z` at the Kerr minima, with
the coupling rows discharged (BoxRows §1) and the RHS collapsed onto the twin's closed price.  The
LHS is byte-identical to `gold_hBVblocksW_discharge'`'s `hprice` slot (at `X = 2^{i+1}−1`,
`M = pieceM kp`); the analytic scale rows remain hypotheses. -/
theorem gold_box_price_live_kerr : ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
    ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
      (T₁ T₂ Ne z y K ka i : ℕ),
      2 ≤ Ne →
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1)) (z * y) K →
      2 ^ i < z * pieceN kp + 1 →
      1 ≤ z →
      6 * Real.log (8 * (z : ℝ)) + 15 ≤ Real.log (goldCut Ne (ka + 1) : ℝ) →
      Real.exp (10 ^ 9) ≤ (goldCut Ne (ka + 1) : ℝ) →
      ((goldCut Ne (ka + 1) : ℝ) / (8 * (z : ℝ))) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) →
      2 ≤ kp →
      (∀ m, ‖β m‖ ≤ 1) → N₀ ≤ 2 ^ kp →
      (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
      1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) →
      1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (2 ^ kp + 1) * (2 ^ kp + 1) →
      (4 * (1 + Real.log D) * (D : ℝ)
          ≤ ((2 ^ kp : ℕ) : ℝ) * (pieceM kp : ℝ)
              / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ (13 : ℝ)) →
      2 ≤ 2 ^ (i + 1) - 1 → 2 ≤ pieceM kp →
      ((D : ℝ) ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
          / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ (15 : ℝ)) →
      ((Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 3)
          ≤ Real.sqrt ((2 ^ (i + 1) - 1 : ℕ) : ℝ)) →
      ((Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 3)
          ≤ Real.sqrt (pieceM kp : ℝ)) →
      ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) →
      ((Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (pieceM kp : ℝ)) →
      F ≤ 2 ^ (i + 1) - 1 →
      ((D : ℝ) ≤ Real.sqrt x) →
      (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) ≤ Lb) →
      (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (F : ℝ)) →
      (∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
          0 < Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ))) →
      ((D : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) →
      (∀ e, 2 ≤ e → e ≤ D → e ≤ 2 ^ (i + 1) - 1 →
          Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
            ≤ 2 * Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ))) →
      (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
            (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₂‖)
        + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp))
              (2 ^ (i + 1) - 1) (pieceM kp) (r d) d T₁‖)
        ≤ boxPriceKerr Kc kp i := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ := gold_box_price_engine_at_live_z
  refine ⟨Kc, N₀, hKc, ?_⟩
  intro x Lb F β kp D Dset r T₁ T₂ Ne z y K ka i hNe hi hlive hz1 hz_ratio hx hDge hk hβ hN₀
    hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor herr_LEpos hDXM herr_scale
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  set logN : ℝ := Real.log ((2 ^ kp : ℕ) : ℝ) with hlogNdef
  have hlogNpos : 0 < logN := by
    rw [hlogNdef]
    apply Real.log_pos
    have : (2 : ℕ) ≤ 2 ^ kp := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ kp := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (4 : ℕ) ≤ 2 ^ kp := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ kp := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast (by omega : (1 : ℕ) < 2 ^ kp)
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hKβnn : 0 ≤ Kbeta_min Kc L logN 13 18 := Kbeta_min_nonneg hKc.le hL0 hlogNpos.le
  have hKmnn : 0 ≤ Km_min Kc L logN 13 18 := Km_min_nonneg hKc.le hL0 hlogNpos.le
  have hKβ'nn : 0 ≤ Kbeta'_min Kc L logN 13 18 := Kbeta'_min_nonneg hKc.le hL0 hlogNpos.le
  have hcoupG : Kc * L ^ ((13 : ℝ) + 18)
      ≤ Kbeta_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) := gold_box_hcoupG hlogNpos
  have hcoup3 : Kc * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) := gold_box_hcoup3 hlogNpos
  have herr_book4 : ∀ e, 2 ≤ e → e ≤ D →
      Kc * (Real.log (((((2 ^ (i + 1) - 1) / e : ℕ)) : ℝ) * (pieceM kp : ℝ)))
            ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
        ≤ Kbeta'_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 1 + 2 * 18) := fun e _ _ =>
    gold_box_herr_book4 hKc.le hlogNpos (gold_box_efold_nonneg (2 ^ (i + 1) - 1) (pieceM kp) e)
      (gold_box_efold_le (2 ^ (i + 1) - 1) (pieceM kp) e)
  have hmain := hbody x Lb F β (2 ^ (i + 1) - 1) (pieceM kp) kp D Dset r
    (Kbeta_min Kc L logN 13 18) (Km_min Kc L logN 13 18) (Kbeta'_min Kc L logN 13 18)
    T₁ T₂ Ne z y K ka i hNe hi hlive hz1 hz_ratio hx rfl rfl hDge hk hβ hKβnn hKmnn hKβ'nn hN₀
    hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor herr_LEpos hDXM herr_scale hcoupG hcoup3 herr_book4
  -- the engine RHS at the Kerr minima IS `boxPriceKerr Kc kp i` (byte-for-byte the closed price)
  exact hmain

/-! ## 2. The DEAD-branch box-price collapse onto `boxPriceKerr` (deliverable 2, the DEAD half)

The dead box (`min (z·pieceN k' + 1) (N/2 + 1) ≤ 2^i`) has an empty carrier, so both annulus-cutoff
sums vanish and any nonneg price discharges the slot — in particular `boxPriceKerr Kc k' i` (nonneg
by `boxPriceKerr_nonneg`).  Together with §1 this pins BOTH ends of the box dichotomy onto the SAME
closed price `boxPriceKerr Kc k' i`, so the per-box case split folds against `Price := boxPriceKerr
Kc k'` uniformly (the LIVE half via §1, the DEAD half here). -/

/-- **`gold_box_price_dead_kerr` (§2).**  A DEAD box's two-cutoff price is `≤ boxPriceKerr Kc k' i`
for any `Kc ≥ 0` — direct reuse of `gold_box_price_row_dead` at `P := boxPriceKerr Kc k' i`
(nonneg).  The DEAD half of the box case split, targeting the same closed price as §1. -/
theorem gold_box_price_dead_kerr {Kc : ℝ} (hKc : 0 ≤ Kc) {z y : ℕ} {ε₀ : ℝ}
    {j k' k i N Q a : ℕ}
    (hcap : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) (Dset : Finset ℕ) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
            (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
      ≤ boxPriceKerr Kc k' i :=
  gold_box_price_row_dead hcap (boxPriceKerr_nonneg hKc k' i) Dset

/-! ## 3. The `hSum` close — `gold_hSum_at_op` with all slots filled (deliverable 3)

`gold_hSum_at_op` (Agg §2) instantiated at the uniform worst-`W` per-boundary / per-piece bounds:
each box price `= Wbox := Ccon_box·Kc·N/L^{13}`, each band price `= Wband := Ccon_band·Kc·N/L^{12}`,
and the diagonal budget `= Ccon_diag·Kc·N/L^{11}` — so the `hbox`/`hsym`/`hlow` worst-`W` slots
close by `le_refl` and the quadruple/single annulus `Σ`-closures fold to
`RHD := (12·Ccon_box + 3·Ccon_band + Ccon_diag/2)·Kc·N/L^{11}`.  This is the exact `hSum` slot
`gold_hBVblocksW_discharge'` consumes (Agg §2 / PDiag Part D), at the concrete worst-`W` prices the
box/band packagings supply. -/

/-- **`gold_hSum_discharged` (§3).**  `gold_hSum_at_op` at the uniform worst-`W` prices — the box
quadruple `Σ` (const price `Wbox`), the two band single `Σ`s (const price `Wband`), and the diagonal
budget close to `RHD`.  The `hSum` slot of `gold_hBVblocksW_discharge'` with every worst-`W` slot
filled (`Price`/`PsymK`/`PlowK`/`Pdiag` the concrete constants; the `hbox`/`hsym`/`hlow` and
`hWbox`/`hWband`/`hPdiag` slots all `le_refl`). -/
theorem gold_hSum_discharged (N z y K : ℕ) (ε₀ Kc Ccon_box Ccon_band Ccon_diag : ℝ)
    (hmax : maxBlock N z ε₀ = 0) (hKc0 : 0 ≤ Kc) (hlogpos : 0 < Real.log N)
    (hCb0 : 0 ≤ Ccon_box) (hCband0 : 0 ≤ Ccon_band)
    (hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N) :
    (∑ _j ∈ Finset.range (maxBlock N z ε₀ + 1),
        ((∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K,
                Ccon_box * Kc * (N : ℝ) / (Real.log N) ^ 13)
          + ((1 / 2) * (∑ _k' ∈ Finset.range (Nat.log 2 N + 1),
                Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
             + (∑ _k' ∈ Finset.range (Nat.log 2 N + 1),
                Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
             + (1 / 2) * (Ccon_diag * Kc * (N : ℝ) / (Real.log N) ^ 11))))
      ≤ (12 * Ccon_box + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
  have hWbox0 : (0 : ℝ) ≤ Ccon_box * Kc * (N : ℝ) / (Real.log N) ^ 13 := by positivity
  have hWband0 : (0 : ℝ) ≤ Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12 := by positivity
  exact gold_hSum_at_op N z y K ε₀ Kc
    (fun _ _ _ _ => Ccon_box * Kc * (N : ℝ) / (Real.log N) ^ 13)
    (fun _ _ => Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
    (fun _ _ => Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
    (Ccon_diag * Kc * (N : ℝ) / (Real.log N) ^ 11)
    (Ccon_box * Kc * (N : ℝ) / (Real.log N) ^ 13)
    (Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
    Ccon_box Ccon_band Ccon_diag hmax hKc0 hlogpos hWbox0 hWband0 hCb0 hCband0
    (fun _ _ _ _ _ _ => le_refl _) (fun _ _ => le_refl _) (fun _ _ => le_refl _)
    (le_refl _) (le_refl _) (le_refl _) hcount

section ByteLock

-- item 1's LIVE workhorse (D0Win2) + its honest lower bound + z-floor keystones
#check @Salt.Goldbach.gold_box_price_engine_at_live_z
#check @Salt.Goldbach.gold_live_annulus_lower
#check @Salt.Goldbach.gold_kfloor_live_z
#check @Salt.Goldbach.gold_d0_window_z
-- the DEAD keystone the DEAD branch reuses
#check @Salt.Goldbach.gold_box_price_row_dead
-- the twin closed price the LIVE branch collapses onto (reused verbatim, block scale `2^kp`)
#check @Salt.Chen.boxPriceKerr
#check @Salt.Chen.boxPriceKerr_nonneg
-- the x-generic coupling suppliers (BoxRows §1)
#check @Salt.Goldbach.gold_box_hcoupG
#check @Salt.Goldbach.gold_box_hcoup3
#check @Salt.Goldbach.gold_box_herr_book4
#check @Salt.Goldbach.gold_box_efold_le
#check @Salt.Goldbach.gold_box_efold_nonneg
-- the aggregate + terminal the packagings feed
#check @Salt.Goldbach.gold_hSum_at_op
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
-- THIS FILE's deliverables: the LIVE collapse (§1), the DEAD collapse (§2), the hSum close (§3)
#check @Salt.Goldbach.gold_box_price_live_kerr
#check @Salt.Goldbach.gold_box_price_dead_kerr
#check @Salt.Goldbach.gold_hSum_discharged
-- the composed A₃ terminal whose `hBVblocksW` slot the terminal + packagings + hSum close fill
#check @Salt.Goldbach.gold_mainA3_of_block_remainders_W

/-- **Composition sanity — the box dichotomy folds onto `boxPriceKerr Kc k' i`.**  For the exact
`hprice`-slot two-cutoff box sum of `gold_hBVblocksW_discharge'`, the per-box cap-dichotomy folds
onto the SAME closed price `boxPriceKerr Kc k' i`: the DEAD branch via §2
(`gold_box_price_dead_kerr`), the LIVE branch via §1 (`gold_box_price_live_kerr`, its analytic-row
output supplied as `hlive`).  This pins the per-box `Price := boxPriceKerr Kc k'` choice the
`hprice` slot consumes. -/
example {Kc : ℝ} (hKc : 0 ≤ Kc) {z y : ℕ} {ε₀ : ℝ} {j k' k i N Q a : ℕ} {Dset : Finset ℕ}
    (hlive : 2 ^ i < min (z * pieceN k' + 1) (N / 2 + 1) →
        (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
              (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
              (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
          + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
                (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
          ≤ boxPriceKerr Kc k' i) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
            (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N k)‖)
      ≤ boxPriceKerr Kc k' i := by
  by_cases h : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i
  · exact gold_box_price_dead_kerr hKc h Dset
  · exact hlive (not_le.mp h)

/-- **Composition sanity — `gold_hSum_discharged` IS the terminal's `hSum` slot (worst-`W`).**  At
`Price`/`PsymK`/`PlowK`/`Pdiag` the concrete worst-`W` constants, `gold_hSum_discharged`'s
conclusion matches `gold_hBVblocksW_discharge'`'s `hSum` slot LHS ≤ `RHD` character-for-character —
the box/band packagings, worst-`W`-absorbed, feed exactly here. -/
example (N z y K : ℕ) (ε₀ Kc Ccon_box Ccon_band Ccon_diag : ℝ)
    (hmax : maxBlock N z ε₀ = 0) (hKc0 : 0 ≤ Kc) (hlogpos : 0 < Real.log N)
    (hCb0 : 0 ≤ Ccon_box) (hCband0 : 0 ≤ Ccon_band)
    (hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N) :
    (∑ _j ∈ Finset.range (maxBlock N z ε₀ + 1),
        ((∑ k' ∈ Finset.range (Nat.log 2 N + 1),
            ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ _i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (z * y) K,
                Ccon_box * Kc * (N : ℝ) / (Real.log N) ^ 13)
          + ((1 / 2) * (∑ _k' ∈ Finset.range (Nat.log 2 N + 1),
                Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
             + (∑ _k' ∈ Finset.range (Nat.log 2 N + 1),
                Ccon_band * Kc * (N : ℝ) / (Real.log N) ^ 12)
             + (1 / 2) * (Ccon_diag * Kc * (N : ℝ) / (Real.log N) ^ 11))))
      ≤ (12 * Ccon_box + 3 * Ccon_band + Ccon_diag / 2) * Kc * (N : ℝ) / (Real.log N) ^ 11 :=
  gold_hSum_discharged N z y K ε₀ Kc Ccon_box Ccon_band Ccon_diag hmax hKc0 hlogpos hCb0 hCband0
    hcount

end ByteLock

end Salt.Goldbach
