/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Agg

/-!
# G-AGG (seam 2 + composition) — the block↔switch A₃ terminal `gold_mainA3_of_block_remainders_W`

Design: the twin's `Salt/Chen/SwitchW.lean` (`mainA3_of_block_remainders_W`) — the W-route A₃
terminal the twin's `chen_headline` actually consumes (via `FinA3c.hA3_bundle`).  This is the
Goldbach mirror: the block-path box-price close (`gold_hBVblocksW_discharge'`'s summed W Rosser
remainder `≤ N/(log N)^{10}`) folds — through the block decomposition of the W-switch sifted sum
(`goldSwitchSieveW_siftedSum_eq_sum_blocks`), the per-block sharp keystone
(`gold_block_switch_upper_B_W`), and the `rfl` W/maxDepth factorings — into the exact `mainA3`
shape.  The Λ-carrier bridge `hbridge` stays a hypothesis (G-ASM supplies it at
`LHS := goldTriplePrimeSum`).

## Why the W route (an architectural note for the house — see the report)

The box prices (`gold_box_price_engine`) and the entire PDiag/SW2/block chain are `φ(Q)`-normalized
W / CRT-`Q·d` objects; they feed the **W path** (`goldBlockSwitchSieveW`, residue `crtClassG`).
The twin's landed `chen_headline` uses this same W route, whose `mainA3` carrier is
`tripleSum/φ(Q)·W·Ffac` (`Salt/Chen/Headline4.lean`'s `M3`).  The Goldbach
`gold_mainA3_of_hBVswitch`
(`Salt/Goldbach/Switch.lean`) / `gold_mainA3_at_op` (`Salt/Goldbach/PriceClose.lean`) instead carry
the NON-W switch sieve (no `/φ(Q)`), which the box-price W machinery cannot feed (a `φ(Q)`
mismatch).  `gold_mainA3_of_block_remainders_W` below is therefore the faithful terminal, resolving
the "block-remainder → A₃" example G-PDIAG deferred; the `/φ(Q)` shape gap in
`gold_mainA3_of_hBVswitch` is flagged for the house/Fable to reconcile.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 1. The W-route A₃ terminal (`gold_mainA3_of_block_remainders_W`) -/

set_option maxHeartbeats 800000 in
-- the per-block keystone `rwa` and the block-sum reassembly carry the deep sieve carrier terms;
-- the defeq checks on `goldBlockSwitchSieveW`'s fields need headroom above the default budget.
/-- **`gold_mainA3_of_block_remainders_W` — the composed A₃ bound (the W route).**  Given the
Λ-bridge `hbridge : LHS ≤ log N · (goldSwitchSieveW …).siftedSum` (G-ASM's, at `LHS =
goldTriplePrimeSum`) and the block-remainder close `hBVblocksW` (the box-price output through
`gold_hBVblocksW_discharge'`), the sharp keystone folds to the exact `mainA3` shape
`goldTripleSum/φ(Q)·W·(Fchain + slack) + N/(log N)^{10}`.  Mirrors
`Salt.Chen.mainA3_of_block_remainders_W`. -/
theorem gold_mainA3_of_block_remainders_W (N z y Q a Ps Dlev : ℕ) (ε₀ ε K QR LHS : ℝ)
    (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQR : 1 ≤ QR)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hbridge : LHS ≤ Real.log N * (goldSwitchSieveW N z y Q a Ps hPs hPodd).siftedSum)
    (hBVblocksW : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
        ≤ (N : ℝ) / (Real.log N) ^ 10) :
    LHS
      ≤ Real.log N *
          (goldTripleSum N z y / (Q.totient : ℝ)
              * Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd)
              * (Fchain (maxDepth (goldSwitchSieve N z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (N : ℝ) / (Real.log N) ^ 10) := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set Wswitch := Salt.BrunLower.W (goldSwitchSieve N z y Ps hPs hPodd) with hWswitch
  set Ffac := Fchain (maxDepth (goldSwitchSieve N z y Ps hPs hPodd)) (logRatio y Dlev)
      + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev) with hFfac
  -- per-block sharp keystone, with W / maxDepth collapsed to the global switch values (rfl)
  have hblock : ∀ j, (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).siftedSum
      ≤ goldBlockTripleSum N z y ε₀ j / (Q.totient : ℝ) * Wswitch * Ffac
        + rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev) := by
    intro j
    have h := gold_block_switch_upper_B_W N z y ε₀ j Q a Ps Dlev ε K QR hPs hPodd hPy hPlow hD2
      hQR hε hw0 hεsmall hKe h4 hStop
    rwa [goldBlockSwitchSieveW_W_eq, goldBlockSwitchSieveW_maxDepth_eq, ← hWswitch, ← hFfac] at h
  -- sum the blocks: the carrier factors out, `∑ blockTripleSum/φ(Q)` reassembles, the slot closes
  have hRHS : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
        (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).siftedSum)
      ≤ goldTripleSum N z y / (Q.totient : ℝ) * Wswitch * Ffac
        + (N : ℝ) / (Real.log N) ^ 10 := by
    have hstep : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).siftedSum)
        ≤ ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
            (goldBlockTripleSum N z y ε₀ j / (Q.totient : ℝ) * Wswitch * Ffac
              + rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd)
                  (QR * Dlev)) :=
      Finset.sum_le_sum (fun j _ => hblock j)
    rw [Finset.sum_add_distrib] at hstep
    have hfac : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          goldBlockTripleSum N z y ε₀ j / (Q.totient : ℝ) * Wswitch * Ffac)
        = goldTripleSum N z y / (Q.totient : ℝ) * Wswitch * Ffac := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div,
        ← goldTripleSum_eq_sum_blockTripleSum N z y ε₀ hz hε₀]
    rw [hfac] at hstep
    linarith [hstep, hBVblocksW]
  calc LHS
      ≤ Real.log N * (goldSwitchSieveW N z y Q a Ps hPs hPodd).siftedSum := hbridge
    _ = Real.log N * ∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).siftedSum := by
        rw [goldSwitchSieveW_siftedSum_eq_sum_blocks N z y ε₀ hz hε₀ Q a Ps hPs hPodd]
    _ ≤ Real.log N * (goldTripleSum N z y / (Q.totient : ℝ) * Wswitch * Ffac
          + (N : ℝ) / (Real.log N) ^ 10) := mul_le_mul_of_nonneg_left hRHS hlogN

/-! ## 2. The `hCE` slot confirm (`gold_hCE_at_op` fills it, N-free per the gate)

`gold_hCE_at_op` (`Salt/Goldbach/SwitchBV.lean`) at `ε₀ := N` (single block) IS the `hCE` slot of
`gold_hBVblocksW_discharge'` character-for-character, with `RCE` the finding-5 product
`ν(Q)·(Σ_{d∣Ps} ν(d))·goldTripleSum/(z−1)`.  This example pins the slot match. -/

/-- **The `hCE` slot of `gold_hBVblocksW_discharge'` is filled by `gold_hCE_at_op`.**  At `ε₀ := N`
the conversion-error double sum is bounded by the finding-5 product — the exact `hCE` position
`gold_mainA3_of_block_remainders_W` needs (through `gold_hBVblocksW_discharge'`). -/
example (N z y Q Ps w' : ℕ) (QR : ℝ) (Dlev : ℕ)
    (hPs : Squarefree Ps) (hz2 : 2 ≤ z) (hN2 : 2 ≤ N) (hQ1 : 1 ≤ Q)
    (hQPs : Nat.Coprime Q Ps) (hQfac : ∀ p ∈ Q.primeFactors, p < w')
    (hPy : ∀ p ∈ Ps.primeFactors, p < y) (hw'z : w' ≤ z) :
    (∑ j ∈ Finset.range (maxBlock N z (N : ℝ) + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then goldBlockConvErrW N z y (N : ℝ) j Q d else 0)
      ≤ nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * goldTripleSum N z y / ((z : ℝ) - 1) :=
  gold_hCE_at_op N z y Q Ps w' QR Dlev hPs hz2 hN2 hQ1 hQPs hQfac hPy hw'z

/-! ## 3. The G-ASM byte-lock — the complete remaining interface

With `gold_mainA3_of_block_remainders_W` (§1) landed, the A₃ carrier bundle
`gold_a12_hA3 : ∃ x₁, ∀ N ≥ x₁, goldTriplePrimeSum … ≤ M3ᴺ` reduces to the following, all at the
operating witnesses (`z := opZ N`, `y := opY N`, `Ps := goldOpPs N`, `Q := opQ`, `Dlev := opD N`,
`ε := opEps`, `ε₀ := (N : ℝ)`, `a := gold_op_residue`, `QR := opQ`):

1. **The Λ-bridge `hbridge`** — `goldTriplePrimeSum … ≤ log N · (goldSwitchSieveW …).siftedSum`
   (`LHS := goldTriplePrimeSum`).  G-SW's byte-lock; NOT this arc's.  NOTE the sieve is the
   **W-switch** `goldSwitchSieveW` (residue `crtClassG`), not the non-W `goldSwitchSieve` of the
   vestigial `gold_mainA3_of_hBVswitch`.
2. **The general-`a` A₁ re-instantiation** (G-OMEGA byte-lock) — `gold_a12_hA1` is hardcoded to
   `opA`, but the A₂/A₃ residue is the parametric `a := gold_op_residue` (with `Coprime opQ (N−a)`);
   G-ASM re-invokes the A₁ chain at that witness so A₁/A₂/A₃ share ONE residue.
3. **The structural rows** — `hz`/`hε₀`/`hPs`/`hPodd`/`hPy`/`hPlow`/`hD2`/`hQR`/`hε`/`hw0`/
   `hεsmall`/`hKe`/`h4`/`hStop` of `gold_mainA3_of_block_remainders_W`, from the
   `opf_*`/`goldOpPs_*` facts
   and the landed `gold_switch_upper_B` inputs (`h4` = `h4_cond_of_base`).
4. **The block-remainder close `hBVblocksW`** — `gold_hBVblocksW_discharge'` at the op witnesses,
   fed by:
   * `hprice`/`hpriceSym`/`hpriceLow` — the per-boundary / per-piece box prices, from
     **`gold_box_price_engine`** with its analytic rows discharged at the per-annulus `L`-scale
     (`gold_box_rows_at_op` / `gold_box_price_indep` — NOT LANDED; the flagged residual, see the
     report) through the SW2 annulus telescopes `gold_hNum_at_opW` / `gold_PloW_sym_of_box_disc` /
     `gold_PloW_low_of_box_disc`;
   * `hSum` — **`gold_hSum_at_op`** (§ `Agg.lean`), the annulus aggregate, at the worst-`W`
     per-boundary bounds `Wbox ≤ Ccon_box·Kc·N/L^{13}`, `Wband ≤ Ccon_band·Kc·N/L^{12}`
     (`hbox`/`hsym`/`hlow`), `RHD := (12·Ccon_box + 3·Ccon_band + Ccon_diag/2)·Kc·N/L^{11}`;
   * `hdiag` — `gold_diagAggW_le_honest` (landed, PDiag);
   * `hCE` — `gold_hCE_at_op` (§2), `RCE := ν(Q)·(Σ ν(d))·goldTripleSum/(z−1)`;
   * `hNum` — **`gold_hNum_close_of_tower`** at the aggregate `Ccon`, the tower `2·Ccon·K ≤ log N`
     folded into the threshold.
5. **The `∀ N` wrapper** — the `∃ x₁, ∀ N ≥ x₁` threshold collecting every sub-threshold above
   (the tower/floor/count bounds), the shape `chen_headline_of_A3_ledger`'s Goldbach mirror
   consumes.

The ONLY genuinely-open analytic work is 4's box-price row discharge (`gold_box_price_indep`); every
other slot is landed (§1, §2, `gold_hSum_at_op`, `gold_hNum_close_of_tower`,
`gold_diagAggW_le_honest`, `gold_hBVblocksW_discharge'`). -/

section GAsmByteLock

-- the composed W-route A₃ terminal (this file) + seam-1 aggregate
#check @Salt.Goldbach.gold_mainA3_of_block_remainders_W
#check @Salt.Goldbach.gold_hSum_at_op
-- the block terminal it feeds + the numeric closes it consumes
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
#check @Salt.Goldbach.gold_hNum_close_of_tower
#check @Salt.Goldbach.gold_hCE_at_op
#check @Salt.Goldbach.gold_diagAggW_le_honest
-- the annulus telescopes + the box supplier (whose analytic rows are the flagged residual)
#check @Salt.Goldbach.gold_hNum_at_opW
#check @Salt.Goldbach.gold_PloW_sym_of_box_disc
#check @Salt.Goldbach.gold_PloW_low_of_box_disc
#check @Salt.Goldbach.gold_box_price_engine
-- the sifted-sum block split + per-block keystone (the composition's spine)
#check @Salt.Goldbach.goldSwitchSieveW_siftedSum_eq_sum_blocks
#check @Salt.Goldbach.gold_block_switch_upper_B_W

end GAsmByteLock

end Salt.Goldbach
