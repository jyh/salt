/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.PDiag
import Salt.Chen.PriceClose

/-!
# G-PRICE — the box / sym / low survivor prices at the `crtClassG` residue (Goldbach suppliers)

Design: `docs/exploration/pilot.md` (the PDiag/SW2/WindowSW/BandIdent interfaces + Opt-A) and the
twin price stack `Salt/Chen/PriceOne.lean` … `PriceThree.lean` / `SqrtDFold.lean` (the generic
bilinear pricer `medium_survivor_price_sqrtD`, residue-parametric).  This file is the
Goldbach mirror of `Salt.Chen.box_hprice_at_2pow` / `sym_box_hprice_at_2pow` /
`low_box_hprice_at_2pow` under `crtClassW ↦ crtClassG`, `x ↦ N`, and the OUTER DYADIC ANNULUS axis
(the box cutoffs are `goldCut N (k+1)` / `goldCut N k`, not `x` / `x/2+1`).

## The residue-parametric reuse (Q6a-4 recon, verified)

`medium_survivor_price_sqrtD` prices the one-cutoff sum
`∑_{d∈Dset} ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖`
for an ARBITRARY residue `r` (only `hcop2 : ∀ d ∈ Dset, Coprime (r d) d`), an ARBITRARY cutoff `T`
(the bound is `T`-independent), and an ARBITRARY `‖·‖ ≤ 1` carrier `α`.  The twin's hard-wiring to
`crtClassW` lives ONLY in its Dset bookkeeping row `crtClassW_coprime_of_mem`; everything else
(carrier bridges, the `1 ≤ m` / `m ≤ D` image rows, the pieceN→`2^k` indicator bridge, the engine)
is residue-agnostic and REUSED verbatim.  The one genuinely-Goldbach row is
`gold_crtClassG_coprime_of_mem` (§1): the `crtClassG`-coprimality over the `Q`-shifted divisor
image, off `Coprime Q (N−a)` (the switch `hQa2` slot) and `Coprime Ps N` (`goldPs_coprime_N`, the
`d ∤ N` unit that replaces the twin's `a+2` odd split).

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* §1 **`gold_crtClassG_coprime_of_mem`** — the `crtClassG` Dset-image coprimality (the Goldbach
  bookkeeping row; the only residue-specific input of the box suppliers).
* §2–§4 the box / sym / low per-box price suppliers (`medium_survivor_price_sqrtD` twice, at
  `T = goldCut N (k+1)` and `T = goldCut N k`), parametric over the engine's analytic row list —
  the direct `box_disc_three_way` per-box `hprice` slot at `crtClassG`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The `crtClassG` Dset-image coprimality (the Goldbach bookkeeping row)

The `hcop2` slot of `medium_survivor_price_sqrtD` at the operating divisor image
`Dset := ((divisors Ps).filter (·<bound)).image (Q··)` with residue `r m := crtClassG Q (m/Q) N a`.
Mirrors `Salt.Chen.crtClassW_coprime_of_mem`; the twin's odd-`d` split (`2 ∤ d`) is replaced by the
switch unit `Coprime d N` (off `Coprime Ps N`, i.e. `d ∤ N` on `goldPs`). -/

/-- **`gold_crtClassG_coprime_of_mem` (§1).**  At `m = Q·d` in the operating divisor image,
`m/Q = d` and `crtClassG_coprime` closes `Coprime (crtClassG Q d N a) (Q·d)` from `Coprime Q d`
(off `Coprime Q Ps`), `Coprime Q (N−a)` (the switch `hQa2`), and `Coprime d N` (off `Coprime Ps N`,
the `goldPs` unit). -/
theorem gold_crtClassG_coprime_of_mem {Q Ps N a : ℕ} (bound : ℝ) (hQ1 : 1 ≤ Q)
    (hQPs : Nat.Coprime Q Ps) (hQNa : Nat.Coprime Q (N - a)) (hPsN : Nat.Coprime Ps N)
    {m : ℕ}
    (hm : m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d)) :
    Nat.Coprime (crtClassG Q (m / Q) N a) m := by
  rw [Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdvd, _⟩, _⟩ := hd
  have hQd_div : Q * d / Q = d := Nat.mul_div_cancel_left d (by omega)
  rw [hQd_div]
  have hQd : Nat.Coprime Q d := Nat.Coprime.coprime_dvd_right hdvd hQPs
  have hdN : Nat.Coprime d N := Nat.Coprime.coprime_dvd_left hdvd hPsN
  exact crtClassG_coprime hQd hQNa hdN

/-! ## 2. The two-cutoff engine wrapper (`box_disc_three_way`'s per-box `hprice` slot)

`medium_survivor_price_sqrtD` (A = 13, C0 = 18, B = 15 — `medium_box_price_at_op`'s convention)
applied TWICE, at the two annulus cutoffs `T₂ = goldCut N (k+1)` and `T₁ = goldCut N k`, on the
`blockPrimeInd (pieceN k')` indicator (bridged to `2^k'` by `sum_norm_apDiscBilinCutoff_pieceN`,
`M ≤ 2·2^k'`/`2^k' ≤ M` from `pieceM_le_two_pow`/`two_pow_le_pieceM` at the caller).  The engine's
bound is `T`-INDEPENDENT, so the two-cutoff sum is `≤ 2·(the Kerr box price)` — exactly the per-box
`hprice` slot of `box_disc_three_way` (MediumFloor).  Residue/carrier-agnostic: `β`, `r` are
abstract (`hβ`/`hcop2`), so the caller instantiates `β :=` the box carrier and `r := crtClassG …`.

Unlike the twin's `medium_box_price_at_op`, the `D0`-window and SW-coupling rows are NOT derived
from a `(x/2+1, x)` boundary (an annulus box has `X·M ≈ goldCut N k`, so `d0_window_of_XM`'s
`L ≈ log x` is unavailable per annulus); they enter as the engine's named analytic hypotheses,
discharged downstream from the annulus geometry (the per-annulus `L`-scale). -/

set_option maxHeartbeats 1000000 in
-- The 43-hypothesis engine application elaborates a long rpow-bearing row list twice; the
-- whnf/defeq checks on those atoms need headroom above the default heartbeat budget.
/-- **`gold_box_price_engine` (§2).**  The two-cutoff (`T₂`, `T₁`) box price, `≤ 2·Kerr`, via
`medium_survivor_price_sqrtD` twice on `blockPrimeInd (pieceN k)` (bridged to `2^k`).  The full
engine row list at `A = 13`, `C0 = 18`, `B = 15`, `N = 2^k` (the "27 named analytic rows"). -/
theorem gold_box_price_engine :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x Lb : ℝ) (F : ℕ) (β : ℕ → ℂ) (X M k D0 D k0 : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
        (Kβ Km Kβ' : ℝ) (T₁ T₂ : ℕ),
        2 ≤ k →
        (∀ m, ‖β m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ 2 ^ k → M ≤ 2 * 2 ^ k → D0 ≤ 2 ^ k →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ (18 : ℝ)) →
        ((D0 : ℝ) ≤ (Real.log ((2 ^ k : ℕ) : ℝ)) ^ (18 : ℝ)) →
        (((2 ^ k : ℕ) : ℝ) ≤ (M : ℝ)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (2 ^ k + 1) * (2 ^ k + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) →
        2 ≤ X → 2 ≤ M →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (15 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (M : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (M : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt x) →
        (Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (18 : ℝ)) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 18)
            ≤ Kβ * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (Kc * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 2 * 18)
            ≤ Km * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ ((13 : ℝ) + 2 * 18)) →
        (∀ e, 2 ≤ e → e ≤ D →
            Kc * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
              ≤ Kβ' * (Real.log ((2 ^ k : ℕ) : ℝ)) ^ ((13 : ℝ) + 1 + 2 * 18)) →
        (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN k)) X M (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN k)) X M (r d) d T₁‖)
          ≤ 2 * ((Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kβ' + 15360 + 1)))
              * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨K, N₀, hK0, hbody⟩ :=
    medium_survivor_price_sqrtD (A := 13) (C0 := 18) (by norm_num) (by norm_num)
  refine ⟨K, N₀, hK0, fun x Lb F β X M k D0 D k0 Dset r Kβ Km Kβ' T₁ T₂ hk hβ hKβ hKm hKβ' hN₀
    hM2N hD0N hd1 hcop2 hL1 hD0 hD0N' hNM hD1 hDsetD hDsq habs hX2 hM2 hD0eq h2D0 hD0D hDscale
    hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E
    hDXM herr_scale hcoupG hcoup3 herr_book4 => ?_⟩
  have hone : ∀ T : ℕ,
      (∑ d ∈ Dset, ‖apDiscBilinCutoff β (blockPrimeInd (pieceN k)) X M (r d) d T‖)
        ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
              + ((2 : ℝ) ^ ((13 : ℝ) + 5) * Kβ' + 15360 + 1)))
            * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (13 : ℝ) := by
    intro T
    rw [sum_norm_apDiscBilinCutoff_pieceN hk]
    exact hbody x Lb F β X (2 ^ k) M T D0 D k0 (Nat.log 2 D) Dset r Kβ Km Kβ' 15 hβ hKβ hKm hKβ'
      hN₀ hM2N hD0N hd1 hcop2 hL1 hD0 hD0N' hNM hD1 hDsetD hDsq habs hX2 hM2 (by norm_num)
      (by norm_num) hD0eq h2D0 hD0D rfl hDscale hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo
      herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E hDXM herr_scale hcoupG hcoup3 herr_book4
  rw [two_mul]
  exact add_le_add (hone T₂) (hone T₁)

/-! ## 3. Consumption sanity — how the engine supplies the three legs' per-box `hprice`

`gold_box_price_engine`'s conclusion is EXACTLY the per-box `hprice` slot of
`Salt.Chen.box_disc_three_way` (the two-cutoff sum over the reduced top `2^{i+1}−1`), which is what
`SW2.gold_hNum_at_opW` (box leg) and `SW2.gold_PloW_sym_of_box_disc` /
`SW2.gold_PloW_low_of_box_disc` (band legs) consume per annulus.  The three legs instantiate the
engine's `β`/`r` differently but reduce to the SAME two-cutoff application:

* **box leg** — `β :=` the doubly-restricted box carrier `restrictAlpha (restrictAlpha
  (blockAlpha z y ε₀ j) 0 c) (2^i) (2^{i+1})` (`hβ` from `norm_box_leg_le_one`), indicator
  `blockPrimeInd (pieceN k')` verbatim;
* **low leg** — `β :=` the low carrier (`norm_low_leg_le_one`), indicator
  `blockPrimeInd (pieceN k')` verbatim;
* **sym leg** — `β :=` the sym carrier (`norm_sym_leg_le_one`), indicator `blockPrimeInd (max y
  (pieceN k'))` collapsed to `blockPrimeInd (pieceN k')` by `max_y_pieceN_eq` (needs
  `y ≤ pieceN k'`) BEFORE the engine, so the same lemma applies.

For all three, `r := fun m => crtClassG Q (m/Q) N a`, with the three Dset-image rows discharged by
the reused `Salt.Chen.one_le_of_mem_QImage` (`hd1`), `gold_crtClassG_coprime_of_mem` (`hcop2`, the
one Goldbach-specific row), and `Salt.Chen.le_D_of_mem_QImage` (`hDsetD`).  Only the engine's
analytic row list (the D0-window + scale + SW-coupling rows) remains, discharged downstream from the
per-annulus `L`-scale. -/

section ConsumptionSanity

-- the engine + the one Goldbach-specific bookkeeping row
#check @Salt.Goldbach.gold_box_price_engine
#check @Salt.Goldbach.gold_crtClassG_coprime_of_mem
-- the per-box `hprice` consumer (the two-cutoff sum lands in this slot, T₂/T₁ = goldCut (k+1)/k)
#check @Salt.Chen.box_disc_three_way
-- the three annulus telescopes that call `box_disc_three_way` per annulus (box / sym / low)
#check @Salt.Goldbach.gold_hNum_at_opW
#check @Salt.Goldbach.gold_PloW_sym_of_box_disc
#check @Salt.Goldbach.gold_PloW_low_of_box_disc
-- the reused (residue-agnostic) Dset-image rows + carrier bridges + indicator collapse
#check @Salt.Chen.one_le_of_mem_QImage
#check @Salt.Chen.le_D_of_mem_QImage
#check @Salt.Chen.norm_box_leg_le_one
#check @Salt.Chen.norm_sym_leg_le_one
#check @Salt.Chen.norm_low_leg_le_one
#check @Salt.Chen.max_y_pieceN_eq

end ConsumptionSanity

end Salt.Goldbach
