/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Price
import Salt.Goldbach.SwitchBV

/-!
# G-PRICE (assembly) — the numeric closure + the terminal `mainA3` scaffold (Goldbach)

Design: the twin's `Salt/Chen/PriceClose.lean` (the tower budget `tower_budget` /
`hNum_close_of_tower`) and the Goldbach switch endpoint `Salt/Goldbach/Switch.lean`
(`gold_mainA3_of_hBVswitch`) + `Salt/Goldbach/SwitchBV.lean` (`gold_hBVswitch_of_generalBV`).  This
is the assembly half of G-PRICE: the box/sym/low prices land in `Salt/Goldbach/Price.lean`; here the
Σ-budget closes into `N/(log N)^{10}` and the `mainA3` slot is threaded to a byte-locked interface.

## The numeric closure is `x`-generic (verbatim reuse)

`Salt.Chen.tower_budget` and `Salt.Chen.hNum_close_of_tower` carry NO twin-specific structure —
they are pure real-arithmetic closures (`m·x/L^{11} ≤ x/L^{10}` at `m ≤ L`; the `RHD + RCE ≤
x/L^{10}` fold at `2·Ccon·K ≤ log x`).  The Goldbach mirrors below are those lemmas at `x := N`.
The aggregate constant `Ccon` absorbs the ONE extra Opt-A `log` (the annulus count `⌊log₂N⌋+1`) via
consuming the BV backbone at saving `A+1` — a per-`N` factor dwarfed by the tower `log N ≥ w'^{w'}`.

## The terminal `mainA3` scaffold + the G-ASM byte-lock

`gold_mainA3_at_op` composes the two landed switch-endpoint lemmas: `gold_hBVswitch_of_generalBV`
(the summed honest-discrepancy `hHD` + conversion-error `hCE` + numeric `hNum` ⟹ the `hBVswitch`
Rosser-remainder bound) feeding `gold_mainA3_of_hBVswitch` (the sharp keystone ⟹ the `mainA3`
shape).  It keeps parametric EXACTLY the slots G-ASM must still supply (§3 lists them): the survivor
Λ-bridge `hbridge` (G-SW's byte-lock — NOT attempted here), the switched-discrepancy aggregates
`hHD`/`hCE` (fed by the box prices through the block↔switch remainder identity), and the tower
`hNum` (this file's `gold_hNum_close_of_tower`).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The numeric closure at `x := N` (the tower budget mirrors) -/

/-- **`gold_tower_budget`** — the closure core at `x := N`: `m·N/L^{11} ≤ N/L^{10}` for `m ≤ L`,
`L > 0`.  One power of `L` of tower headroom traded for the aggregate budget factor `m` (the
`⌊log₂N⌋+1` annulus count × the per-box constant).  Verbatim `Salt.Chen.tower_budget`. -/
theorem gold_tower_budget {N L m : ℝ} (hN : 0 ≤ N) (hL : 0 < L) (hmL : m ≤ L) :
    m * N / L ^ 11 ≤ N / L ^ 10 :=
  tower_budget hN hL hmL

/-- **`gold_hNum_close_of_tower`** — the exact `hNum` slot of `gold_hBVblocksW_discharge'` /
`gold_hBVswitch_of_generalBV` (`RHD + RCE ≤ N/(log N)^{10}`) from the two aggregate bounds
`RHD, RCE ≤ Ccon·K·N/(log N)^{11}` and the tower `2·Ccon·K ≤ log N`.
`Salt.Chen.hNum_close_of_tower` at `x := N`. -/
theorem gold_hNum_close_of_tower {N : ℕ} {RHD RCE Ccon K : ℝ}
    (hN : 0 ≤ (N : ℝ)) (hL : 0 < Real.log N)
    (hRHD : RHD ≤ Ccon * K * (N : ℝ) / (Real.log N) ^ 11)
    (hRCE : RCE ≤ Ccon * K * (N : ℝ) / (Real.log N) ^ 11)
    (htower : 2 * (Ccon * K) ≤ Real.log N) :
    RHD + RCE ≤ (N : ℝ) / (Real.log N) ^ 10 :=
  hNum_close_of_tower hN hL hRHD hRCE htower

/-! ## 2. The terminal `mainA3` scaffold (`gold_mainA3_at_op`)

`gold_mainA3_of_hBVswitch ∘ gold_hBVswitch_of_generalBV`: the switched honest-discrepancy /
conversion-error aggregates (`hHD`/`hCE`, the box-price outputs through the block↔switch remainder
identity) plus the tower `hNum` yield the `hBVswitch` Rosser bound, and the sharp keystone folds it
to the `mainA3` shape.  All analytic content stays parametric; this is the composition scaffold. -/

/-- **`gold_mainA3_at_op` (the terminal scaffold).**  Feeds `gold_hBVswitch_of_generalBV`'s summed
Rosser bound (from the switched-discrepancy aggregates `hHD`/`hCE` at `RHD`/`RCE` + the tower
`hNum`) into `gold_mainA3_of_hBVswitch`, emitting the exact `mainA3`-slot shape.  The Λ-bridge
`hbridge` and the structural keystone rows stay parametric for G-ASM (do NOT attempt the Λ-bridge —
G-SW's byte-lock). -/
theorem gold_mainA3_at_op (N z y Ps Dlev : ℕ) (ε K Q LHS RHD RCE : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hbridge : LHS ≤ Real.log N * (goldSwitchSieve N z y Ps hPs hPodd).siftedSum)
    (hHD : (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < Q * Dlev then |goldSwitchHonestDisc N z y d| else 0) ≤ RHD)
    (hCE : (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < Q * Dlev then goldSwitchConvErr N z y d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (N : ℝ) / (Real.log N) ^ 10) :
    LHS
      ≤ Real.log N *
          (goldTripleSum N z y * Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd)
              * (Fchain (maxDepth (goldSwitchSieve N z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (N : ℝ) / (Real.log N) ^ 10) :=
  gold_mainA3_of_hBVswitch N z y Ps Dlev ε K Q LHS hPs hPodd hPy hPlow hD2 hQ hε hw0 hεsmall hKe
    h4 hStop hbridge
    (gold_hBVswitch_of_generalBV N z y Ps hPs hPodd Q Dlev hHD hCE hNum)

/-! ## 3. The G-ASM byte-lock — the exact remaining interface

`gold_mainA3_at_op` delivers the `mainA3` shape.  Every hypothesis G-ASM must still supply, at the
Goldbach operating witnesses (`N`, `z := opZ N`, `y := opY N`, `Ps := goldOpPs N`, `Q := opQ`,
`Dlev := opD N`, `ε := opEps`):

1. **`hbridge`** — the survivor Λ-bridge
   `goldTriplePrimeSum … ≤ log N · (goldSwitchSieve …).siftedSum` (`LHS := goldTriplePrimeSum`).
   G-SW's byte-lock; NOT this arc's.
2. **`hHD` / `hCE`** — the switched honest-discrepancy / conversion-error aggregates bounded by
   `RHD`/`RCE`.  These are where the box/sym/low prices (`Price.gold_box_price_engine`, summed by
   `SW2.gold_hNum_at_opW` / `gold_PloW_sym_of_box_disc` / `gold_PloW_low_of_box_disc` through
   `gold_hBVblocksW_discharge'`) land, via the block↔switch remainder identity
   (`SwitchBV.gold_memClassG` + `goldBlockSwitchSieveW_abs_rem_le`).  The Σ over blocks/pieces/
   annuli/boundaries closes into `Ccon·K·N/(log N)^{11}` (the annulus count absorbed at saving
   `A+1`), feeding `gold_hNum_close_of_tower`.
3. **`hNum`** — `RHD + RCE ≤ N/(log N)^{10}`; supplied by `gold_hNum_close_of_tower` (§1) once
   `hHD`/`hCE` are at the `Ccon·K·N/L^{11}` shape and the tower `2·Ccon·K ≤ log N` holds.
4. the structural keystone rows (`hPy`/`hPlow`/`h4`/`hStop`/…) — the op facts `goldOpPs_py`,
   `opf_*`, and the landed `gold_switch_upper_B` inputs.

The box prices themselves (deliverables 1–2) are LANDED in `Price.lean`; what remains for the full
`mainA3` close is the per-annulus row discharge (the `L`-scale analytic rows of
`gold_box_price_engine`) and the block↔switch aggregation — the flagged downstream work. -/

section GAsmByteLock

-- the terminal scaffold + its two composed legs
#check @Salt.Goldbach.gold_mainA3_at_op
#check @Salt.Goldbach.gold_mainA3_of_hBVswitch
#check @Salt.Goldbach.gold_hBVswitch_of_generalBV
-- the numeric closure
#check @Salt.Goldbach.gold_hNum_close_of_tower
#check @Salt.Goldbach.gold_tower_budget
-- the block-path terminal the box prices feed (the discharge whose rows the box prices fill)
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
-- the box price supplier + the Goldbach bookkeeping row
#check @Salt.Goldbach.gold_box_price_engine
#check @Salt.Goldbach.gold_crtClassG_coprime_of_mem

end GAsmByteLock

end Salt.Goldbach
