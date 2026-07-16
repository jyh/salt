/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.SW2
import Salt.Goldbach.Agg

/-!
# G-BANDENG — the Goldbach band pricers (sym/low legs of `gold_hSum_at_op`)

The box-price leg of `gold_hSum_at_op` closes through `gold_hNum_at_opW` (the annulus telescope ∘
`box_disc_three_way`).  This file closes the two BAND legs — the `hsym`/`hlow` slots — by supplying
the `hdiffK` inputs of `SW2.gold_PloW_sym_of_box_disc` / `gold_PloW_low_of_box_disc` and the
one-`log` annulus absorption `PsymK 0 k' ≤ Wband`.

## The band annulus telescope is NOT `box_disc_three_way`

The main box telescopes over dyadic sub-boxes `(2^i, 2^{i+1}]` at the SINGLE window cutoff `T`
(twin `sym_box_price_at_op`, via `box_disc_three_way` — the `restrictAlpha`-to-`2^i` carrier).
The Goldbach BAND rectangles are already `m`-resolved: the `hdiffK` slots of
`gold_PloW_sym_of_box_disc` / `gold_PloW_low_of_box_disc` carry the FULL band carrier
(`blockAlphaSym` / `restrictAlpha (blockAlphaLow ..)`) and telescope over the OUTER dyadic ANNULI
`(goldCut N k, goldCut N (k+1)]` at the CUTOFF axis.  So the per-`(k',k)` term is a pure
cutoff-difference `‖A(goldCut N (k+1)) − A(goldCut N k)‖`, priced by the triangle inequality against
a per-annulus two-`T` box price (the shared single-`T` engine, `medium_box_price_at_op_band`,
applied at the two annulus endpoints) — NOT by `box_disc_three_way`.

## The gap census — what the sym/low legs need that is not landed

`gold_PloW_sym_of_box_disc` / `gold_PloW_low_of_box_disc` (SW2, landed) reshape the band-rect `|·|`
sums into their `hdiffK` slots, but leave `hdiffK` OPEN.  `gold_hSum_at_op` (Agg, landed) closes
the block aggregate from ABSTRACT `PsymK`/`PlowK` with `hsym`/`hlow : PsymK 0 k' ≤ Wband`, also
OPEN.  The missing pieces, classified:

* **`hdiffK` (sym/low)** — GENERIC.  The per-`(k',k)` cutoff-difference `≤` per-annulus two-`T`
  box price, then summed.  Pure triangle inequality + `Finset` folding — the annulus adaptation
  the twin never needs (its band is a single `T`-difference).  Landed here as
  `gold_band_price_sym` / `gold_band_price_low`, and compiled into the SW2 slots as
  `gold_hdiffK_sym_discharge` / `gold_hdiffK_low_discharge`.
* **the two-`T` box price `Price k' k`** — ADAPTATION-NEEDED (NOT landed here, terminal-owned).
  The shared single-`T` engine `medium_box_price_at_op_band` (α-generic, `T`-uniform RHS) at the
  two annulus endpoints `goldCut N (k+1)`, `goldCut N k`, with the `max`-collapse
  `max y (pieceN k') = pieceN k'` (sym) and the live-geometry floor `x^{1/3}/8 ≤ 2^{k'}` — the same
  operating-point instantiation the box leg (G-ROWSLIVE) performs.  Left as a NAMED hypothesis, as
  in the twin (`sym_box_price_at_op`'s `Price i`).
* **`PsymK 0 k' ≤ Wband`** — GENERIC.  The annulus `Σ_k` costs one `log` (`^{13} → ^{12}`), absorbed
  by `gold_log_absorb`.  Landed here as `gold_band_annulus_absorb`.

Only `[propext, Classical.choice, Quot.sound]`; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The structural band pricers — the `hdiffK` slot per piece `k'` -/

/-- **`gold_band_price_sym`** — the sym-band `hdiffK` discharge at one piece `k'`.  The annulus
telescope of the sym cutoff-differences is bounded, annulus by annulus, by a per-annulus two-`T`
box price `Price k` via the triangle inequality `‖A(goldCut (k+1)) − A(goldCut k)‖ ≤
‖A(goldCut (k+1))‖ + ‖A(goldCut k)‖`.  Conclusion character-for-character the `hdiffK k'` slot of
`gold_PloW_sym_of_box_disc`; `Price k` is a NAMED two-`T` box price (the terminal supplies it via
`medium_box_price_at_op_band` at the two endpoints). -/
theorem gold_band_price_sym {N z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (k' : ℕ) (Price : ℕ → ℝ)
    (hprice : ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                  (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                  (goldCut N k)‖)
          ≤ Price k) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
              (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N (k + 1))
            - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
              (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N k)‖)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k := by
  classical
  refine Finset.sum_le_sum (fun k hk => le_trans ?_ (hprice k hk))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun m _ => norm_sub_le _ _)

/-- **`gold_band_price_low`** — the low-band `hdiffK` discharge at one piece `k'`.  Same triangle
telescope as `gold_band_price_sym`, at the low carrier
`restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k')) (min (z·pieceN k'+1) (N/2+1)) (N/2+1)` and the
primeInd `blockPrimeInd (pieceN k')`.  Conclusion character-for-character the `hdiffK k'` slot of
`gold_PloW_low_of_box_disc`. -/
theorem gold_band_price_low {N z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (k' : ℕ) (Price : ℕ → ℝ)
    (hprice : ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                  (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                    (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                  (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                  (goldCut N k)‖)
          ≤ Price k) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1),
        ∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
          ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
              (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N (k + 1))
            - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
              (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
              (goldCut N k)‖)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k := by
  classical
  refine Finset.sum_le_sum (fun k hk => le_trans ?_ (hprice k hk))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun m _ => norm_sub_le _ _)

/-! ## 2. The compiled `hdiffK` discharges — the full band-rect `|·|` sum bounds -/

/-- **`gold_hdiffK_sym_discharge`** — the sym leg, compiled.  Feeds `gold_band_price_sym` (per piece
`k'`) into `gold_PloW_sym_of_box_disc`'s `hdiffK` slot with `PsymK k' := Σ_k Price k' k`, yielding
the full band-rect `|goldBandSymRectDisc|` sum bound `SW2` hands to G-PDIAG.  The only input is the
per-`(k',k)` two-`T` box price `Price k' k` (terminal-supplied). -/
theorem gold_hdiffK_sym_discharge {N z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (Price : ℕ → ℕ → ℝ) (hN2 : 2 ≤ N) (hQ1 : 1 ≤ Q) (hNeX : N / 2 ≤ X)
    (hprice : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k') (pieceM k'))
                  (blockPrimeInd (max y (pieceN k'))) X (pieceM k') (crtClassG Q (m / Q) N a) m
                  (goldCut N k)‖)
          ≤ Price k' k) :
    (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandSymRectDisc N z y ε₀ j (pieceN k') (pieceM k') (Q * d)
            (crtClassG Q d N a)| else 0)
      ≤ ∑ k' ∈ Finset.range (Nat.log 2 N + 1),
          ∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k' k :=
  gold_PloW_sym_of_box_disc Ps bound
    (fun k' => ∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k' k) hN2 hQ1 hNeX
    (fun k' hk' => gold_band_price_sym Ps bound k' (Price k') (fun k hk => hprice k' hk' k hk))

/-- **`gold_hdiffK_low_discharge`** — the low leg, compiled.  Mirror of `gold_hdiffK_sym_discharge`
through `gold_PloW_low_of_box_disc` (note its window row is `N/2+1 ≤ X+1`). -/
theorem gold_hdiffK_low_discharge {N z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (Price : ℕ → ℕ → ℝ) (hN2 : 2 ≤ N) (hQ1 : 1 ≤ Q) (hNeX : N / 2 + 1 ≤ X + 1)
    (hprice : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                  (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                (goldCut N (k + 1))‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k'))
                    (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1))
                  (blockPrimeInd (pieceN k')) X (pieceM k') (crtClassG Q (m / Q) N a) m
                  (goldCut N k)‖)
          ≤ Price k' k) :
    (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |goldBandLowDisc N z y ε₀ j (pieceN k') (pieceM k')
            (min (z * pieceN k' + 1) (N / 2 + 1)) (N / 2 + 1) (Q * d) (crtClassG Q d N a)| else 0)
      ≤ ∑ k' ∈ Finset.range (Nat.log 2 N + 1),
          ∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k' k :=
  gold_PloW_low_of_box_disc Ps bound
    (fun k' => ∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k' k) hN2 hQ1 hNeX
    (fun k' hk' => gold_band_price_low Ps bound k' (Price k') (fun k hk => hprice k' hk' k hk))

/-! ## 3. The annulus absorption — `PsymK 0 k' ≤ Wband` (the `hsym`/`hlow` slot value) -/

/-- **`gold_band_annulus_absorb`** — the one-`log` band absorb.  The per-piece band price
`PsymK 0 k' = Σ_k Price k` (the annulus `Σ_k`, `⌊log₂N⌋+1` terms) of a per-annulus single-`T`-scale
price `Price k ≤ C/(log N)^{13}` closes one power: `≤ 2C/(log N)^{12}` — the `Wband` bound that
`gold_hSum_at_op`'s `hsym`/`hlow` slots consume. -/
theorem gold_band_annulus_absorb {N : ℕ} (Price : ℕ → ℝ) (Wsingle C : ℝ)
    (hlogpos : 0 < Real.log N)
    (hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N)
    (hWs0 : 0 ≤ Wsingle) (hC0 : 0 ≤ C)
    (hPk : ∀ k ∈ Finset.range (Nat.log 2 N + 1), Price k ≤ Wsingle)
    (hWs : Wsingle ≤ C / (Real.log N) ^ 13) :
    (∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k) ≤ 2 * C / (Real.log N) ^ 12 := by
  have hstep : (∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k)
      ≤ ((Nat.log 2 N : ℝ) + 1) * Wsingle := by
    calc (∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k)
        ≤ ∑ _k ∈ Finset.range (Nat.log 2 N + 1), Wsingle := Finset.sum_le_sum hPk
      _ = ((Nat.log 2 N : ℝ) + 1) * Wsingle := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hcnt0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by positivity
  exact le_trans hstep (gold_log_absorb (L := Real.log N) (cnt := (Nat.log 2 N : ℝ) + 1)
    (C := C) (val := Wsingle) (p := 12) hlogpos hcnt0 hcount hC0 hWs0 hWs)

/-! ## 4. The handoff — how the band legs close `gold_hSum_at_op`

The terminal (G-PDIAG) chains, per block `j`:

* **`hsym`/`hlow` values** — `PsymK j k' := Σ_k Price_sym j k' k`, `PlowK j k' := Σ_k Price_low j k'
  k`, where `Price_·` is the per-annulus two-`T` box price from `medium_box_price_at_op_band` (α =
  `blockAlphaSym`/`restrictAlpha (blockAlphaLow ..)`, at the two annulus endpoints).
* **`gold_hSum_at_op`'s `hsym`/`hlow`** — `PsymK 0 k' ≤ Wband` via `gold_band_annulus_absorb` (per
  `k'`), with `Wband := 2·C/(log N)^{12}`, `C := Ccon_band·Kc·N`.
* **the band-rect `|·|` sums** — bounded by `Σ_{k'} PsymK 0 k'` via
  `gold_hdiffK_sym_discharge` / `gold_hdiffK_low_discharge`; feeds
  `gold_bandDiscW_le_three_pieces_diag` and G-PDIAG's honest diagonal into
  `gold_hBVblocksW_discharge'`.

The one input NOT landed here (terminal-owned, shared with the box leg): the two-`T` price `Price
k' k` — `medium_box_price_at_op_band` at `T ∈ {goldCut N (k+1), goldCut N k}` with the sym
`max`-collapse and the live-geometry floor `x^{1/3}/8 ≤ 2^{k'}`. -/

section Handoff

/-- The `hsym`/`hlow` slot of `gold_hSum_at_op`, assembled at the operating block: with the
block-0 band price `PsymK 0 k' := Σ_k Price k' k` (`Price k' k` the per-piece/per-annulus two-`T`
box price) and per-annulus `Price k' k ≤ Wsingle ≤ C/(log N)^{13}`, every piece prices at
`Wband := 2·C/(log N)^{12}`.  This is `gold_hSum_at_op`'s `hsym` (and `hlow`) slot, verbatim. -/
theorem gold_band_hsym_slot {N : ℕ} (Price : ℕ → ℕ → ℝ) (Wsingle C : ℝ)
    (hlogpos : 0 < Real.log N)
    (hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N)
    (hWs0 : 0 ≤ Wsingle) (hC0 : 0 ≤ C)
    (hPk : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
        Price k' k ≤ Wsingle)
    (hWs : Wsingle ≤ C / (Real.log N) ^ 13) :
    ∀ k' ∈ Finset.range (Nat.log 2 N + 1),
      (∑ k ∈ Finset.range (Nat.log 2 N + 1), Price k' k) ≤ 2 * C / (Real.log N) ^ 12 :=
  fun k' hk' => gold_band_annulus_absorb (Price k') Wsingle C hlogpos hcount hWs0 hC0
    (fun k hk => hPk k' hk' k hk) hWs

#check @Salt.Goldbach.gold_band_price_sym
#check @Salt.Goldbach.gold_band_price_low
#check @Salt.Goldbach.gold_hdiffK_sym_discharge
#check @Salt.Goldbach.gold_hdiffK_low_discharge
#check @Salt.Goldbach.gold_band_annulus_absorb
#check @Salt.Goldbach.gold_hSum_at_op

end Handoff

end Salt.Goldbach
