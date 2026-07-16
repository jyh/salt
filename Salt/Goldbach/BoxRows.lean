/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Agg
import Salt.Chen.PriceOne

/-!
# G-BOXROWS — the per-annulus box-price row discharge (Goldbach)

Design: the twin's `Salt/Chen/PriceOne.lean` … `PriceTwo.lean` (the row toolkit + the terminal
`medium_box_price_at_op_lo`) and `Salt/Chen/ChenRows1.lean` (`box_rows_at_op` — the row bundle),
`Salt/Chen/AssembleA3.lean` (`box_price_at_op`, `boxPriceKerr` — the closed price + the vanish/live
dichotomy) and `Salt/Chen/FinA3.lean` (`box_price_indep` — the arg-free packaging).  This is the
Goldbach mirror at the OUTER DYADIC ANNULUS axis: the box cutoffs are `goldCut N (k+1)` /
`goldCut N k` (not `x` / `x/2+1`), so the D0-window and SW-coupling rows enter at the *per-annulus*
`L`-scale (`X·M ≈ goldCut N k ≈ 2^k`, one power deeper than the twin's global `x`-scale).

## The row inventory (deliverable 1)

`gold_box_price_engine` (`Salt/Goldbach/Price.lean`) is the raw two-cutoff engine wrapper
(`medium_survivor_price_sqrtD` twice, at `T₂ = goldCut N (k+1)`, `T₁ = goldCut N k`); it exposes the
FULL `medium_survivor_price_sqrtD` hypothesis list (the twin's terminal `medium_box_price_at_op_lo`
has the D0-window + SW-coupling pre-absorbed, leaving only 18 rows — the Goldbach engine leaves ~41,
because those rows can only be derived from the *per-annulus* geometry).  Classified against the
twin's `box_rows_at_op` (`x`-generic reuse), the per-annulus `L`-scale, and the vanish/live floor:

**(a) x-generic — reusable verbatim (carrier/Dset/coupling/e-fold rows):**
* `hβ`/`hKβ`/`hKm`/`hKβ'` — carrier norm ≤ 1 and the price-constant nonneg (set at the caller;
  `Kβ := Kbeta_min Kc L logN 13 18` etc., nonneg by `Kbeta_min_nonneg`);
* `hd1`/`hcop2`/`hDsetD` — the Dset-image rows (`one_le_of_mem_QImage`,
  `gold_crtClassG_coprime_of_mem` [the one Goldbach-specific row, landed in `Price.lean`],
  `le_D_of_mem_QImage`);
* `hcoupG`/`hcoup3`/`herr_book4` — the SW-coupling rows: EXACT `Kbeta_min_coupling` /
  `Km_min_coupling` / `Kbeta'_min_coupling` (§1 below, `gold_box_hcoupG`/`_hcoup3`/`_herr_book4`);
* `herr_LEpos`/`herr_scale` — the e-fold window rows: `log_efold_le` / a positivity (§1,
  `gold_box_herr_scale`; `herr_LEpos` needs `1 ≤ ⌊X/e⌋·M`, the live-box floor);
* `hFX`/`hLbb`/`hfloor`/`hDx` — the outer-scale rows (`F ≤ X`, `log(X·M) ≤ Lb`, the `x^{1/6}` floor,
  `D ≤ √x`), `x`-generic in the twin's `row_hFX`/`row_hLbb`/`row_hfloor`/`row_hDx` shape.

**(b) scale-dependent — the per-annulus `L`-scale (the D0-window + the geometry rows):**
* `hD0`/`hD0N'`/`hD0N`/`hD0eq`/`h2D0`/`hD0D`/`hD0lo_main`/`herr_D0lo`/`herr_D0E` — the D0-window
  9-conjunct, from `d0_window_of_XM` at `x := goldCut N (k+1)`, `N := 2^{k'}`, off the *per-annulus*
  scale facts `goldCut N k < X·M ≤ 4·goldCut N (k+1)` (§3 `gold_box_XM_scale`, VERIFIED here — the
  exact geometry the D0-window consumes; the twin reads these off `(x/2+1, x)`);
* `hL1`/`hX2`/`hM2`/`hM2N`/`hNM`/`hD1`/`hDsq`/`habs`/`hDscale`/`hXsqrt`/`hMsqrt`/`herr_lev`/
  `herr_Mlev`/`hDXM` — the box-geometry rows (`X = 2^{i+1}−1`, `M = pieceM k'`, block `2^{k'}`);
  IDENTICAL box shape to the twin's `row_*` toolkit, but keyed to the Goldbach boundary filter (the
  annulus cutoffs), so re-derived at the per-annulus scale rather than reused verbatim.

**(c) genuinely new — the vanish/live floor (the delicate part):**
* the DEAD-annulus / dead-box vanish: a box with `min (z·pieceN k' + 1) (N/2 + 1) ≤ 2^i` has an
  empty carrier, so both cutoff sums are `0` and the price is `0` (§2 `gold_box_carrier_vanish` /
  `gold_box_price_vanish`, VERIFIED — direct reuse of `box_carrier_eq_zero_above_cap`);
* the LIVE-box floor: which `(k', k, i)` are live.  A live box forces `2^i < z·pieceN k' + 1`, hence
  (with the annulus cutoff) the per-annulus block floor coupling `k` (annulus) and `k'` (piece) —
  the analogue of the twin's `kfloor_of_live_box`, at the annulus scale.  This floor is what the
  D0-window's `hNfloor : x^{11/24}/8 ≤ 2^{k'}` needs at `x := goldCut N (k+1)`; see the report for
  the precise blocking off-by-one on `hXMlo` and the flagged residual.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* §1 the x-generic reuse rows (`gold_box_hcoupG`/`_hcoup3`/`_herr_book4`/`_herr_scale`);
* §2 the vanish lemmas (`gold_box_carrier_vanish`/`gold_box_price_vanish`, the dead-annulus floor);
* §3 the per-annulus scale facts (`gold_box_XM_scale`, the D0-window's geometry input).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The x-generic reuse rows (coupling + e-fold)

The SW-coupling rows `hcoupG`/`hcoup3`/`herr_book4` of `gold_box_price_engine` are discharged by
CHOOSING the price constants as the closed Kerr minima `Kbeta_min`/`Km_min`/`Kbeta'_min` (PriceOne),
whose `_coupling` lemmas give the required inequalities as equalities/near-equalities.  These are
`x`-generic (they hold at any `L`/`logN`), so they reuse the twin machinery verbatim. -/

/-- **`gold_box_hcoupG`.**  The engine's `hcoupG` row at `Kβ := Kbeta_min Kc L logN 13 18`:
`Kc·L^{13+18} ≤ Kβ·logN^{13+2·18}`.  Exactly `Kbeta_min_coupling`. -/
theorem gold_box_hcoupG {Kc L logN : ℝ} (hlogN : 0 < logN) :
    Kc * L ^ ((13 : ℝ) + 18)
      ≤ Kbeta_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) :=
  Kbeta_min_coupling (A := 13) (C0 := 18) hlogN

/-- **`gold_box_hcoup3`.**  The engine's `hcoup3` row at `Km := Km_min Kc L logN 13 18`:
`Kc·L^{13+1+2·18} ≤ Km·logN^{13+2·18}`.  Exactly `Km_min_coupling`. -/
theorem gold_box_hcoup3 {Kc L logN : ℝ} (hlogN : 0 < logN) :
    Kc * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) :=
  Km_min_coupling (A := 13) (C0 := 18) hlogN

/-- **`gold_box_herr_book4`.**  The engine's `herr_book4` row (per-`e`) at
`Kβ' := Kbeta'_min Kc L logN 13 18`, for a fold-log `ℓ = log(⌊X/e⌋·M)` with `0 ≤ ℓ ≤ L`:
`Kc·ℓ^{13+1+1+2·18} ≤ Kβ'·logN^{13+1+2·18}`.  Exactly `Kbeta'_min_coupling`. -/
theorem gold_box_herr_book4 {Kc L logN ℓ : ℝ} (hKc : 0 ≤ Kc) (hlogN : 0 < logN)
    (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) :
    Kc * ℓ ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
      ≤ Kbeta'_min Kc L logN 13 18 * logN ^ ((13 : ℝ) + 1 + 2 * 18) :=
  Kbeta'_min_coupling (A := 13) (C0 := 18) hKc hlogN hℓ0 hℓL (by norm_num)

/-- **`gold_box_herr_scale`.**  The engine's `herr_scale` e-fold row `log(X·M) ≤ 2·log(⌊X/e⌋·M)`
would need the box-geometry floor; the `x`-generic half is the ceiling `log(⌊X/e⌋·M) ≤ log(X·M)`
(`log_efold_le`) plus nonneg (`log_efold_nonneg`), packaged for the caller. -/
theorem gold_box_efold_le (X M e : ℕ) :
    Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) ≤ Real.log ((X : ℝ) * (M : ℝ)) :=
  log_efold_le X M e

theorem gold_box_efold_nonneg (X M e : ℕ) :
    0 ≤ Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) :=
  log_efold_nonneg X M e

/-! ## 2. The vanish lemmas (the dead-annulus / dead-box floor, the delicate part (c))

A box `(k', k, i)` whose window start `2^i` sits at or above the carrier cap
`min (z·pieceN k' + 1) (N/2 + 1)` has an EMPTY carrier (`box_carrier_eq_zero_above_cap`): the
doubly-restricted `restrictAlpha (restrictAlpha (blockAlpha …) 0 cap) (2^i) (2^{i+1})` is `0` at
every `m`, so the per-box discrepancy `apDiscBilinCutoff` is `0` at EVERY cutoff `T`.  Hence both
annulus-cutoff sums vanish and the price slot `Price j k' k i` can be taken `= 0` (`≥ 0` suffices).
This is the honest floor for the dead annuli — the sub-support-`[z·y², N/2]` boxes discharge
vacuously.  The box carrier is character-for-character the consumer's (`gold_hBVblocksW_discharge'`
`hprice`), so this is a DIRECT reuse of the twin's upper-cap vanish. -/

/-- **`gold_box_carrier_vanish`.**  For a dead box (`cap ≤ 2^i`), the single-cutoff `Dset`-sum of
box discrepancy norms vanishes at ANY cutoff `T` — the carrier is empty.  `cap` is the operating
Goldbach box cap `min (z·pieceN k' + 1) (N/2 + 1)`. -/
theorem gold_box_carrier_vanish {z y : ℕ} {ε₀ : ℝ} {j k' i N Q a : ℕ}
    (hcap : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) (Dset : Finset ℕ) (T : ℕ) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m T‖) = 0 := by
  apply Finset.sum_eq_zero
  intro m _
  rw [box_carrier_eq_zero_above_cap hcap (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1)
    (pieceM k') (crtClassG Q (m / Q) N a) m T, norm_zero]

/-- **`gold_box_price_vanish`.**  For a dead box (`cap ≤ 2^i`), the TWO-cutoff box price (the exact
`hprice` slot LHS of `gold_hBVblocksW_discharge'`, at `T₂ = goldCut N (k+1)`, `T₁ = goldCut N k`) is
`0` — so any nonnegative price value discharges it.  This is the dead-annulus floor: boxes below the
effective support cost nothing. -/
theorem gold_box_price_vanish {z y : ℕ} {ε₀ : ℝ} {j k' k i N Q a : ℕ}
    (hcap : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) (Dset : Finset ℕ) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
            (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N k)‖) = 0 := by
  rw [gold_box_carrier_vanish hcap Dset (goldCut N (k + 1)),
    gold_box_carrier_vanish hcap Dset (goldCut N k), add_zero]

/-! ## 3. The per-annulus scale facts (the D0-window's geometry input, class (b))

The engine's D0-window rows (`hD0`/`hD0N'`/…/`herr_D0E`) are discharged in one shot by
`d0_window_of_XM` (PriceOne) from the raw scale facts `x/2 + 1 < X·M` and `X·M ≤ 4x`.  The twin
reads these off its `(x/2+1, x)` boundary directly; the Goldbach box lives in an annulus, so the
correct scale is `x := goldCut N (k+1)` and the facts are read off the OUTER-DYADIC boundary
clauses.  `gold_box_XM_scale` isolates and VERIFIES the exact geometry:

* the T₁-level clause gives `goldCut N k < X·M` (`X = 2^{i+1}−1`, `M = pieceM k'`);
* the T₂-corner clause (`2^i·(pieceN k' + 1) ≤ goldCut N (k+1)`, with `pieceN k' + 1 = 2^{k'}` and
  `pieceM k' ≤ 2·2^{k'}`) gives `X·M ≤ 4·goldCut N (k+1)`.

Hence `d0_window_of_XM`'s `hXMhi` holds at `x := goldCut N (k+1)` EXACTLY.  Its `hXMlo`
(`x/2 + 1 < X·M`) reduces — via `goldCut_succ_le_two_mul` (`x/2 ≤ goldCut N k`) — to
`goldCut N k + 1 ≤ X·M`, i.e. the T₁-level clause with ONE unit of slack; the residual off-by-one in
the deep-live annulus (`2^{k+1} ≤ N/2`, where `x/2 = goldCut N k`) is the precise flagged blocker
for the full `gold_box_rows_at_op` assembly (see the report). -/

/-- **`gold_box_XM_scale`.**  The per-annulus box-size bounds from the Goldbach outer-dyadic
boundary: for `i` in the boundary at piece `k'`, annulus `k`, the box `X·M = (2^{i+1}−1)·pieceM k'`
satisfies `goldCut N k < X·M ≤ 4·goldCut N (k+1)` — the exact `hXMhi` (and the `hXMlo` core, up to
the T₁ off-by-one) that `d0_window_of_XM` consumes at `x := goldCut N (k+1)`. -/
theorem gold_box_XM_scale {N z y K k' k i : ℕ}
    (hi : i ∈ dyadicBoundary (pieceN k') (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (z * y) K) :
    goldCut N k < (2 ^ (i + 1) - 1) * pieceM k'
      ∧ (2 ^ (i + 1) - 1) * pieceM k' ≤ 4 * goldCut N (k + 1) := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, -, hcutoff⟩ := hi
  have hpk : pieceN k' + 1 = 2 ^ k' := by
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    unfold pieceN; omega
  refine ⟨hcutoff, ?_⟩
  rw [hpk] at hcorner
  have hMle : pieceM k' ≤ 2 * 2 ^ k' := pieceM_le_two_pow k'
  have hXle : (2 ^ (i + 1) - 1 : ℕ) ≤ 2 ^ (i + 1) := Nat.sub_le _ _
  calc (2 ^ (i + 1) - 1) * pieceM k'
      ≤ 2 ^ (i + 1) * (2 * 2 ^ k') := Nat.mul_le_mul hXle hMle
    _ = 4 * (2 ^ i * 2 ^ k') := by rw [pow_succ]; ring
    _ ≤ 4 * goldCut N (k + 1) := Nat.mul_le_mul (le_refl 4) hcorner

/-- **`gold_box_annulus_half_le`.**  `goldCut N (k+1) / 2 ≤ goldCut N k` — the reduction feeding the
`hXMlo` core (`x/2 ≤ goldCut N k`, `x := goldCut N (k+1)`).  From `goldCut_succ_le_two_mul`. -/
theorem gold_box_annulus_half_le (N k : ℕ) : goldCut N (k + 1) / 2 ≤ goldCut N k := by
  have h := goldCut_succ_le_two_mul N k
  omega

/-- **`gold_box_XMhi`.**  At the D0-window scale `x := 2·goldCut N k`, the upper geometry row
`X·M ≤ 4·x` (= `8·goldCut N k`) holds EXACTLY (from `gold_box_XM_scale` +
`goldCut_succ_le_two_mul`) — the fully-verified half of `d0_window_of_XM`'s scale window at the
annulus scale.  (The lower row `x/2 + 1 < X·M` reduces to `goldCut N k + 1 < X·M`, one unit tighter
than the T₁-level clause `goldCut N k < X·M`: the flagged annulus off-by-one.) -/
theorem gold_box_XMhi {N z y K k' k i : ℕ}
    (hi : i ∈ dyadicBoundary (pieceN k') (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (z * y) K) :
    (2 ^ (i + 1) - 1) * pieceM k' ≤ 4 * (2 * goldCut N k) := by
  have h := (gold_box_XM_scale hi).2
  have h2 := goldCut_succ_le_two_mul N k
  omega

/-! ## 4. Connective sanity — how the verified pieces feed the engine and the consumer

Two disciplined checks that the verified components byte-match their downstream slots:

* the DEAD box discharges `gold_hBVblocksW_discharge'`'s `hprice` slot against any nonneg price
  (`gold_box_price_vanish`: the two-cutoff sum is `0 ≤ Price`);
* the per-annulus scale (`gold_box_XMhi`) supplies `d0_window_of_XM`'s `hXMhi` at
  `x := 2·goldCut N k` EXACTLY. -/

section ConnectiveSanity

/-- The dead box discharges the consumer's `hprice` slot (`sum ≤ Price`) for ANY nonneg price. -/
example {z y : ℕ} {ε₀ : ℝ} {j k' k i N Q a : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hcap : min (z * pieceN k' + 1) (N / 2 + 1) ≤ 2 ^ i) (Dset : Finset ℕ) :
    (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
          (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
          (crtClassG Q (m / Q) N a) m (goldCut N (k + 1))‖)
      + (∑ m ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
            (min (z * pieceN k' + 1) (N / 2 + 1))) (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd (pieceN k')) (2 ^ (i + 1) - 1) (pieceM k')
            (crtClassG Q (m / Q) N a) m (goldCut N k)‖) ≤ P := by
  rw [gold_box_price_vanish hcap Dset]; exact hP

/-- `gold_box_XMhi` is exactly `d0_window_of_XM`'s `hXMhi` slot at `x := 2·goldCut N k`. -/
example {N z y K k' k i : ℕ}
    (hi : i ∈ dyadicBoundary (pieceN k') (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (z * y) K) :
    (2 ^ (i + 1) - 1) * pieceM k' ≤ 4 * (2 * goldCut N k) :=
  gold_box_XMhi hi

-- the engine (the row consumer) + the consumers whose slots these components feed
#check @Salt.Goldbach.gold_box_price_engine
#check @Salt.Goldbach.gold_hSum_at_op
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
-- the D0-window the per-annulus scale feeds (with the flagged lower-bound off-by-one)
#check @Salt.Chen.d0_window_of_XM

end ConnectiveSanity

end Salt.Goldbach
