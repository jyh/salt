/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.GeoSum2
import Salt.Goldbach.BandPrice
import Salt.Chen.DyadicWindow

/-!
# G-BANDWIN — the liveness-FREE band price chain (Goldbach A₃ band leg, sprint Q1, node 1)

Design: the G-SURV re-scope (ledger ~12:15).  The band survivors are HIGH-PASS
(`m > z·pieceN k'`, spanning `(5/24)·log₂N` scales above the box engine's `hlive` gate), so the
band route is **liveness-free**: it never touches the box's z-dependent live floor
(`gold_kfloor_live_z`, whose `hlive` gate the band survivors fail).  Instead it prices at the
**PIECE FLOOR** `(goldCut Ne (k+1))^{1/3}/8 ≤ 2^{k'}`, exactly the twin's band route
(`Salt.Chen.d0_window_of_XM_band` / `medium_box_price_at_op_band`), transported to the Goldbach
outer-annulus geometry.

This is the Goldbach mirror of the twin's `d0_window_of_XM_band`:

* **`gold_d0_window_band`** (this node) — the 9-conjunct `D0`-window at the band floor, derived from
  the annulus-native bounds `goldCut Ne k < X·M ≤ 4·goldCut Ne (k+1)` (the half-bound via
  `goldCut_succ_le_two_mul`, dissolving the factor-8 off-by-one) with the band-floor exponent `1/3`
  (not the box's `7/16`/`11/24`), `W := (1/3)·log x − 7`, ratio `L ≤ (31/10)·W`, tower
  `exp(10^{10})` (so the binding row `4·(31/10)^{17} ≤ W` closes, margin ≈ 3.7×), and the `x`-scale
  floor conjunct kept at `x^{11/24}/8` via the bump `x^{1/3} ≤ x^{11/24}` — character-for-character
  the twin's `d0_window_of_XM_band` at `x := goldCut Ne (k+1)`, `N := Nb`.

  | quantity                                     | value at `t = log x = 10^{10}`      |
  |----------------------------------------------|-------------------------------------|
  | `W = (1/3)·10^{10} − 7`                       | `≈ 3.333·10⁹`                       |
  | ratio bound used: `L ≤ (31/10)·W`            | `31/10 = 3.1 > 3 = lim L/W`         |
  | binding requirement `4·(31/10)^{17} ≤ W`     | `4·(31/10)^{17} ≈ 9.02·10⁸`         |
  | **room** `W / (4·(31/10)^{17})`              | **`≈ 3.7×`**                        |

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. `gold_d0_window_band` — the band-floor D0-window (node 1) -/

/-- **`gold_d0_window_band`.**  `gold_d0_window_annulus` re-run at the band floor: the block floor
at the band bottom `(goldCut Ne (k+1))^{1/3}/8 ≤ Nb` (exponent `1/3`, not `7/16`),
`W := (1/3)·log x − 7`, tower `exp(10^{10})` (so `4·(31/10)^{17} ≤ W`), ratio `L ≤ (31/10)·W`, and
the `x`-scale floor conjunct kept at `x^{11/24}/8` (the bump `x^{1/3} ≤ x^{11/24}`).  Conclusion
character-for-character `gold_d0_window_annulus`'s (so it feeds `gold_box_price_engine`'s `hD0*`
rows verbatim), with the floor conjunct at `x^{11/24}/8` instead of `x^{7/16}/8`.  The factor-8
collision never bites: `hL_lo` uses the NON-strict `x/2 + 1 ≤ X·M`, from
`goldCut_succ_le_two_mul`.
Since 2026-11-19 the proof is an instance of `Salt.Chen.d0_window_core_band` (`DyadicWindow`). -/
theorem gold_d0_window_band {Ne Nb M X k : ℕ}
    (hx : Real.exp (10 ^ 10) ≤ (goldCut Ne (k + 1) : ℝ))
    (hNfloor : (goldCut Ne (k + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (Nb : ℝ))
    (hXMlo : goldCut Ne k < X * M)
    (hXMhi : X * M ≤ 4 * goldCut Ne (k + 1)) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log (Nb : ℝ)) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (goldCut Ne (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8
      ∧ D0 ≤ Nb := by
  -- the half-bound `x/2 + 1 ≤ X·M` from `goldCut_succ_le_two_mul` (dissolves the off-by-one).
  have hle := goldCut_succ_le_two_mul Ne k
  exact Salt.Chen.d0_window_core_band hx hNfloor (by omega) hXMhi

/-! ## 2. `gold_box_price_engine_at_band` — the base engine at the band floor (node 2a)

`gold_box_price_engine` (Price, the LIVENESS-FREE base engine) with its nine `hD0*` rows discharged
from `gold_d0_window_band` (fed the band k-floor `(goldCut Ne (ka+1))^{1/3}/8 ≤ 2^{kp}` as a clean
HYPOTHESIS — no `z`, no `hlive`).  The Goldbach mirror of `gold_box_price_engine_at_live_annulus`
with the LIVE machinery removed: the false `hlive`/`hz` are GONE (the band survivors are high-pass,
they fail the box `hlive` gate), replaced by the band-floor hypothesis `hNfloor`; the floor conjunct
`hd_scale : D0 ≤ x^{11/24}/8` meets the engine's `hDge : x^{11/24}/8 ≤ D` (exponent `11/24`, the
twin's band `d0_window_of_XM_band` scale, not the box's `7/16`).  Tower `exp(10^{10})`.  Conclusion
byte-identical to `gold_box_price_engine_at_live_annulus`'s (the two-cutoff
`≤ 2·(bracket·XM/L^{13})` sum). -/
set_option maxHeartbeats 800000 in
-- the base engine (`gold_box_price_engine`) application re-elaborates the ~43-hypothesis
-- rpow-bearing row list; the whnf/defeq checks need headroom above the default budget.
/-- `gold_box_price_engine_at_band` with the Siegel–Walfisz statement as the hypothesis `hSWall`,
in place of the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem gold_box_price_engine_at_band_of_SW (hSWall : Salt.BV.SiegelWalfisz) :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (X M kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
        (Kβ Km Kβ' : ℝ) (T₁ T₂ Ne z y K ka i : ℕ),
        2 ≤ Ne →
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1))
          (z * y) K →
        Real.exp (10 ^ 10) ≤ (goldCut Ne (ka + 1) : ℝ) →
        (goldCut Ne (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ kp : ℕ) : ℝ) →
        X = 2 ^ (i + 1) - 1 → M = pieceM kp →
        (goldCut Ne (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        2 ≤ kp →
        (∀ m, ‖β m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ 2 ^ kp →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (2 ^ kp + 1) * (2 ^ kp + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ kp : ℕ) : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) →
        2 ≤ X → 2 ≤ M →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (15 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (M : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (M : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt x) →
        (Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 18)
            ≤ Kβ * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 2 * 18)
            ≤ Km * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (∀ e, 2 ≤ e → e ≤ D →
            Kc * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
              ≤ Kβ' * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 1 + 2 * 18)) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₁‖)
          ≤ 2 * ((Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kβ' + 15360 + 1)))
              * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hKc, hbody⟩ := (gold_box_price_engine_of_SW hSWall)
  refine ⟨Kc, N₀, hKc, ?_⟩
  intro x Lb F β X M kp D Dset r Kβ Km Kβ' T₁ T₂ Ne z y K ka i hNe hi hx hNfloor hXeq hMeq
    hDge hk hβ hKβ hKm hKβ' hN₀ hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt
    hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor herr_LEpos hDXM herr_scale hcoupG hcoup3
    herr_book4
  -- the keystone: the band D0-window from `gold_d0_window_band`, at the band floor.
  have hsc := gold_box_XM_scale hi
  rw [← hXeq, ← hMeq] at hsc
  obtain ⟨D0, k0, hd_eq, hd_2, hd_main, hd_lo, hd_hi, hd_N', hd_conj7, hd_scale, hd_N⟩ :=
    gold_d0_window_band (Ne := Ne) (Nb := 2 ^ kp) (M := M) (X := X) (k := ka)
      hx hNfloor hsc.1 hsc.2
  -- the x-generic geometry rows re-derived from the piece parameter.
  have hM2N : M ≤ 2 * 2 ^ kp := by rw [hMeq]; exact pieceM_le_two_pow kp
  have hNM : ((2 ^ kp : ℕ) : ℝ) ≤ (M : ℝ) := by rw [hMeq]; exact_mod_cast two_pow_le_pieceM kp
  -- the D0 rows re-shaped to the engine's exponents / slots.
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_scale hDge)
  have hD0lo_main : (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_lo
  have herr_D0E : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (18 : ℝ) :=
    fun e he2 heD heX => hd_conj7 _ (herr_scale e he2 heD heX)
  exact hbody x Lb F β X M kp D0 D k0 Dset r Kβ Km Kβ' T₁ T₂ hk hβ hKβ hKm hKβ' hN₀ hM2N hd_N
    hd1 hcop2 hL1 hd_hi hd_N' hNM hD1 hDsetD hDsq habs hX2 hM2 hd_eq hd_2 hD0D hDscale hD0lo_main
    hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E hDXM
    herr_scale hcoupG hcoup3 herr_book4

/-- `gold_box_price_engine_at_band_of_SW` at the unconditional gate
`Salt.SW.siegelWalfisz_holds`. -/
theorem gold_box_price_engine_at_band :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (X M kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
        (Kβ Km Kβ' : ℝ) (T₁ T₂ Ne z y K ka i : ℕ),
        2 ≤ Ne →
        i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1))
          (z * y) K →
        Real.exp (10 ^ 10) ≤ (goldCut Ne (ka + 1) : ℝ) →
        (goldCut Ne (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ kp : ℕ) : ℝ) →
        X = 2 ^ (i + 1) - 1 → M = pieceM kp →
        (goldCut Ne (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        2 ≤ kp →
        (∀ m, ‖β m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ 2 ^ kp →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (2 ^ kp + 1) * (2 ^ kp + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ kp : ℕ) : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) →
        2 ≤ X → 2 ≤ M →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (15 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (M : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (M : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt x) →
        (Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 18)
            ≤ Kβ * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 2 * 18)
            ≤ Km * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (∀ e, 2 ≤ e → e ≤ D →
            Kc * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
              ≤ Kβ' * (Real.log ((2 ^ kp : ℕ) : ℝ)) ^ ((13 : ℝ) + 1 + 2 * 18)) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN kp)) X M (r d) d T₁‖)
          ≤ 2 * ((Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kβ' + 15360 + 1)))
              * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) :=
  gold_box_price_engine_at_band_of_SW Salt.SW.siegelWalfisz_holds

/-! ## 3. `gold_band_box_kerr` — the Kerr-minima collapse onto `boxPriceKerr` (node 2b)

`gold_box_price_engine_at_band` re-exported at the Kerr minima `Kβ := Kbeta_min Kc L logN 13 18` /
`Km := Km_min …` / `Kβ' := Kbeta'_min …` (`L := log((2^{i+1}−1)·pieceM kp)`, `logN := log(2^kp)`):
the three SW-coupling rows are discharged by `gold_box_hcoupG`/`gold_box_hcoup3`/
`gold_box_herr_book4` (BoxRows §1) and the RHS collapses — character-for-character — onto the twin's
closed box price `boxPriceKerr Kc kp i`.  The Goldbach mirror of `gold_box_price_live_kerr` at the
band floor: the LIVE-specific `hlive`/`hz1`/`hz_ratio` are GONE, replaced by the band-floor
`hNfloor` + the `11/24` floor `hDge`.  The remaining analytic scale rows stay parametric (the
composition supplies them from the band geometry). -/
set_option maxHeartbeats 1600000 in
-- the 39-hypothesis engine application re-elaborates the long rpow-bearing row list (incl. the
-- RHS↔`boxPriceKerr` collapse); the whnf/defeq checks need headroom above the default budget.
/-- `gold_band_box_kerr` with the Siegel–Walfisz statement as the hypothesis `hSWall`, in place of
the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem gold_band_box_kerr_of_SW (hSWall : Salt.BV.SiegelWalfisz) : ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
    ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
      (T₁ T₂ Ne z y K ka i : ℕ),
      2 ≤ Ne →
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1)) (z * y) K →
      Real.exp (10 ^ 10) ≤ (goldCut Ne (ka + 1) : ℝ) →
      (goldCut Ne (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ kp : ℕ) : ℝ) →
      (goldCut Ne (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
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
  obtain ⟨Kc, N₀, hKc, hbody⟩ := (gold_box_price_engine_at_band_of_SW hSWall)
  refine ⟨Kc, N₀, hKc, ?_⟩
  intro x Lb F β kp D Dset r T₁ T₂ Ne z y K ka i hNe hi hx hNfloor hDge hk hβ hN₀
    hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor herr_LEpos hDXM herr_scale
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  set logN : ℝ := Real.log ((2 ^ kp : ℕ) : ℝ) with hlogNdef
  have hlogNpos : 0 < logN := by
    rw [hlogNdef]
    apply Real.log_pos
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
    T₁ T₂ Ne z y K ka i hNe hi hx hNfloor rfl rfl hDge hk hβ hKβnn hKmnn hKβ'nn hN₀
    hd1 hcop2 hL1 hD1 hDsetD hDsq habs hX2 hM2 hDscale hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor herr_LEpos hDXM herr_scale hcoupG hcoup3 herr_book4
  -- the engine RHS at the Kerr minima IS `boxPriceKerr Kc kp i` (byte-for-byte the closed price)
  exact hmain

/-- `gold_band_box_kerr_of_SW` at the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem gold_band_box_kerr : ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
    ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (kp D : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
      (T₁ T₂ Ne z y K ka i : ℕ),
      2 ≤ Ne →
      i ∈ dyadicBoundary (pieceN kp) (pieceM kp) (goldCut Ne ka) (goldCut Ne (ka + 1)) (z * y) K →
      Real.exp (10 ^ 10) ≤ (goldCut Ne (ka + 1) : ℝ) →
      (goldCut Ne (ka + 1) : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ kp : ℕ) : ℝ) →
      (goldCut Ne (ka + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
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
        ≤ boxPriceKerr Kc kp i :=
  gold_band_box_kerr_of_SW Salt.SW.siegelWalfisz_holds

/-! ## 4. `gold_band_survsum_geoN` — the outer-scale conversion (node 2c)

The band mirror of `gold_box_hbox_geoN`: the leg-agnostic geo bridge that turns a per-survivor
`boxPriceKerr Kc kp i` bound (from `gold_band_box_kerr` at the band carrier) into the outer-scale
geo grade `Cgeo·Kc·goldCut N (ka+1)/(log N)^{12}` (`Cgeo := cr^{12}·gboxConst`), via the LANDED
`gold_boxPriceKerr_geoN`.  Leg-agnostic: the caller (G-SURV-2) supplies the band-box price `hbox`
(low leg direct, sym leg after the `max (opY N) (pieceN k') = pieceN k'` collapse) and the outer
ratio `hNXM : log N ≤ cr·log(X·M)` (holds on the high annuli the high-pass band survivors populate,
`goldCut(ka+1) ≳ N^{19/24}`; the carrier vanishes on low annuli).  This is the `hgeoSym`/`hgeoLow`
per-survivor grade the terminal `gold_hBVblocksW_at_op_band` consumes. -/
/-- **The outer-scale conversion (node 2c).** With `X := 2^{i+1} − 1` and `M := pieceM kp`: for
a dyadic boundary index `i` of the band carrier (`hi`), under `1 ≤ Kc` (`hKc`), the fold-log
floor `1 ≤ log(X·M)` (`hL1`), the ratio `(10/31)·log(X·M) ≤ log 2^{kp}` (`hratio`), `0 < log N`
(`hlogN0`), `1 ≤ cr` (`hcr`) and the outer ratio `log N ≤ cr·log(X·M)` (`hNXM`), a per-survivor
price `P ≤ boxPriceKerr Kc kp i` (`hbox`) converts to the geo grade
`P ≤ (cr^{12}·gboxConst)·Kc·goldCut N (ka+1) / (log N)^{12}`, via the landed
`gold_boxPriceKerr_geoN`. Leg-agnostic: the band mirror of `gold_box_hbox_geoN`. -/
theorem gold_band_survsum_geoN {N K kp ka i : ℕ} {Kc cr P : ℝ}
    (hKc : 1 ≤ Kc)
    (hi : i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (opZ N * opY N) K)
    (hL1 : 1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hratio : (10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.log ((2 ^ kp : ℕ) : ℝ))
    (hlogN0 : 0 < Real.log N) (hcr : 1 ≤ cr)
    (hNXM : Real.log N ≤ cr * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    (hbox : P ≤ boxPriceKerr Kc kp i) :
    P ≤ (cr ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 :=
  le_trans hbox (gold_boxPriceKerr_geoN hKc hi hL1 hratio hlogN0 hcr hNXM)

end Salt.Goldbach
