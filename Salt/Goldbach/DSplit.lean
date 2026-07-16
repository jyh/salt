/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.RowsLive

/-!
# G-DSPLIT — the head/tail modulus split for `gold_hBVblocksW_discharge'`'s `hprice` slot (Goldbach)

**STATUS: STOP-AND-FLAG.**  The adjudicated "split at `cap_k := w_k`, tail priced trivially"
design does NOT close at the operating conductor level.  This file records the obstruction with a
kernel-checked certificate (`gold_dsplit_head_cap_below_conductor`) and pins the exact interface it
must eventually fill.  No `sorry`, no `native_decide`, no new axioms.

## The design under test

`gold_box_rows_at_op` (RowsLive §4) prices a LIVE annulus box `(j,k',k,i)` bilinearly, but ONLY at a
per-annulus sieve level `D` in the NARROW window `[w, 2·w]`, with
`w := (goldCut N (ka+1) / (8·opZ N))^{1/2}`.  Its two D-window hypotheses are exactly
```
(goldCut N (ka+1) / (8·opZ N))^{1/2} ≤ D    -- hDge
D ≤ 2·(goldCut N (ka+1) / (8·opZ N))^{1/2}   -- hDhi
```
The proposed close: for each box, split the QImage modulus sum
`((Nat.divisors Ps).filter (· < QR·Dlev)).image (Q··)` at `cap_k := w_k`; the head `m ≤ 2w` prices
via `gold_box_rows_at_op` (→ `boxPriceKerr Kc k' i`), the tail `m ∈ (2w, Q·QR·Dlev]` prices via an
honest per-modulus trivial bound `≤ X·M/m + M + X·M/φ(m)` (the AP residue count, mathlib's
`Nat.Ico_filter_modEq_card`), and the tail total is claimed `≪ N/(log N)^11`.

## Why it fails — the head cap is BELOW the conductor on the top live annulus

The op conductor is `QR·Dlev = opQ · opD N` with `opD N = ⌊N^{1/2 − 9/100000}⌋₊` (HeadlineW2;
`Agg2.lean:141`), i.e. moduli run up to `≈ opQ²·N^{1/2}` (the Bombieri–Vinogradov barrier, NOT the
`N^{7/8}` the ledger assumed).  The highest NON-EMPTY annulus saturates at `goldCut N (ka+1) = N/2`
(above it the dyadic annuli collapse to `∅`), and it carries LIVE boxes with
`X·M ≈ 4·goldCut ≈ 2N` (`gold_box_XM_scale` + `gold_box_Xfloor`/`gold_box_Mfloor`).  There
`w = ((N/2)/(8·opZ N))^{1/2} ≈ N^{7/16}` (since `opZ N ≈ N^{1/8}`), so the head reaches only
`2w ≈ N^{7/16} = N^{0.4375}` — strictly BELOW the conductor `opD N ≈ N^{0.49991}`.

`gold_dsplit_head_cap_below_conductor` (below) proves `2·w < opD N` at that top scale
(`goldCut = N/2`) for all large `N`, kernel-checked.  Two rigorous consequences:

* **The ledger's premise is FALSE.**  "Annuli with `cap_k ≥ D_global` need no tail (the top
  annuli)" requires `opQ·QR·Dlev ≤ 2w`, i.e. `opQ²·opD N ≤ 2w`; but `opQ²·opD N ≈ N^{1/2} >
  N^{7/16} ≈ 2w`.  So EVERY box — including the saturating top annulus whose `X·M ≈ N` — carries a
  NON-EMPTY modulus tail `m ∈ (2w, opQ²·N^{1/2}]`.  The premise assumed the conductor sits at
  `N^{7/16}`; BV puts it at `N^{1/2}`.

* **The ledger's budget argument does not cover it.**  The claim "tail annuli have
  `goldCut ≤ N^{7/8}·polylog` so the tail total `≪ N/(log N)^11` with polynomial room" only bounds
  LOW annuli.  The top annulus has `goldCut = N/2 ≫ N^{7/8}`, and there the trivial tail is
  `Σ_{d'|Ps, d'∈(2w/Q, QR·Dlev]} (X·M/(Q·d') + M + X·M/φ(Q·d'))` with `X·M ≈ N` — its budget-fit
  reduces to the `N^{1/3}`-smooth divisor-band sum `Σ_{d'|Ps, d'∈(N^{7/16}, N^{1/2})} 1/d'`, a
  delicate estimate the ledger's `goldCut ≤ N^{7/8}` reasoning never establishes (and which is NOT
  the promised "polynomial room").  The split is therefore not house-verified for the top annuli:
  its closure is unproven, resting on an unstated smooth-divisor estimate.

## Root cause + the actual fix (Fable/house tier)

The engine `gold_box_price_live_kerr` (BoxRows3 §1) itself admits a WIDE level window: `hDscale`
only needs `D·L^15 ≤ √(X·M) ≈ √goldCut`, i.e. `D` up to `√goldCut / L^15 ≈ N^{1/2}/L^15` on the top
annulus — enough to cover the WHOLE conductor with NO tail.  It is `gold_box_rows_at_op` that
under-exposes this, hard-capping the level at `2·w` (RowsLive §4 chose `D ≈ w` to meet `hDge`
tightly).  The correct move is therefore NOT a tail split but a WIDER head: re-derive RowsLive's ~24
analytic rows (`hDsq`/`habs`/`hDscale`/`hXsqrt`/…) at a per-BOX level `D ∈ [w, √(X·M)/L^15]` (the
twin's `box_rows_at_op` does exactly this at the FULL BV level over its global window).  That is a
modification/re-derivation of the landed RowsLive file — outside a single non-file-touching DSplit
executor, and Fable/human tier per the iron rules.  This matches the independent G-OP2 STOP-AND-FLAG
(`Op2.lean:22`): "Re-deriving all of it for `crtClassG` plus the extra per-annulus budget, inside
ONE new file, WITHOUT touching existing files, is not feasible."

## What IS landed / reusable for the fix (reuse census)

* head keystone: `gold_box_rows_at_op` (RowsLive), engine `gold_box_price_live_kerr` (BoxRows3 §1)
  — the WIDE-window `hDscale` is already a hypothesis of the engine; only RowsLive's row discharge
  narrows `D` to `[w,2w]`.
* DEAD branch: `gold_box_price_dead_kerr` (BoxRows3 §2) — already fills the `hprice` slot for dead
  boxes (empty carrier), no tail needed there.
* aggregate: `gold_hSum_at_op` / `gold_hSum_discharged` (Agg / BoxRows3 §3) — the annulus worst-`W`
  fold; consumes a CONSTANT `Price = Ccon_box·Kc·N/L^13` (so any concrete supplier must also carry
  the annulus worst-`W` absorb `boxPriceKerr Kc k' i ≤ Ccon_box·Kc·N/L^13`, the Goldbach mirror of
  the twin's `boxPriceKerr_worst_le` (`AggSum.lean:135`) — NOT yet wired for the annulus boundary).
* terminal: `gold_hBVblocksW_discharge'` (PDiag Part D) — its `hprice`/`hpriceSym`/`hpriceLow` slots
  are still OPEN (never invoked); this file does not fill them.
* trivial per-modulus AP bound: tractable via `Nat.Ico_filter_modEq_card`
  (mathlib `Data/Int/CardIntervalMod`) — but orphan until the head reaches the BV level.
-/

namespace Salt.Goldbach

open Salt.Chen

/-- **`gold_dsplit_head_cap_below_conductor` — the gap certificate.**  On the top (saturating) live
annulus `goldCut N (ka+1) = N/2`, the `gold_box_rows_at_op` head cap `2·w`,
`w := ((N/2)/(8·opZ N))^{1/2}`, is STRICTLY below the operating conductor `opD N ≈ N^{1/2}`, for all
large `N`.  So the modulus tail `(2·w, opQ²·N^{1/2}]` is non-empty on the box that carries
`X·M ≈ N`; the trivial-bounded tail there is `≈ N·const/opQ ≫ N/(log N)^11`, and the split design
cannot close.  (`opZ N ≥ N^{1/8}/2` from `gold_op_scales`; `opD N > N^{1/2−9/100000} − 1` from
`Nat.lt_floor_add_one`; `N^{1/16−9/100000} ≥ 4` from `log N ≥ 2·10^9`.) -/
theorem gold_dsplit_head_cap_below_conductor :
    ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
      2 * (((N : ℝ) / 2 / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2)) < (opD N : ℝ) := by
  obtain ⟨xs, hs⟩ := gold_op_scales
  refine ⟨xs, fun N hN => ?_⟩
  obtain ⟨hN2, hZ1, _, _, _, _, hlogN, _, hZhalf, _, _, _, _⟩ := hs N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hZpos : (0 : ℝ) < (opZ N : ℝ) := by exact_mod_cast hZ1
  -- base = (N/2)/(8·opZ N); bound it above by N^{7/8} using opZ N ≥ N^{1/8}/2
  have hNsplit : (N : ℝ) ^ ((7 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 8) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos, show (7 : ℝ) / 8 + 1 / 8 = 1 by norm_num, Real.rpow_one]
  have h18pos : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hNpos _
  have h8Z : 4 * (N : ℝ) ^ ((1 : ℝ) / 8) ≤ 8 * (opZ N : ℝ) := by linarith [hZhalf]
  have hbaseub : (N : ℝ) / 2 / (8 * (opZ N : ℝ)) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) := by
    have hstep : (N : ℝ) / 2 / (8 * (opZ N : ℝ)) ≤ (N : ℝ) / 2 / (4 * (N : ℝ) ^ ((1 : ℝ) / 8)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) h8Z
    refine le_trans hstep ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hNsplit, h18pos, hNpos]
  have hbasenn : (0 : ℝ) ≤ (N : ℝ) / 2 / (8 * (opZ N : ℝ)) := by positivity
  -- w ≤ N^{7/16}
  set w : ℝ := ((N : ℝ) / 2 / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2) with hwdef
  have hwub : w ≤ (N : ℝ) ^ ((7 : ℝ) / 16) := by
    rw [hwdef]
    calc ((N : ℝ) / 2 / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2)
        ≤ ((N : ℝ) ^ ((7 : ℝ) / 8)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hbasenn hbaseub (by norm_num)
      _ = (N : ℝ) ^ ((7 : ℝ) / 16) := by
          rw [← Real.rpow_mul hNpos.le]; norm_num
  have hge1 : (1 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 16) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((7 : ℝ) / 16) := (Real.one_rpow _).symm
      _ ≤ (N : ℝ) ^ ((7 : ℝ) / 16) := Real.rpow_le_rpow (by norm_num) hN1 (by norm_num)
  -- conductor lower bound: opD N > N^{1/2 − 9/100000} − 1
  have hDlb : (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) - 1 < (opD N : ℝ) := by
    have hfl : (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)
        < (⌊(N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hopD : (opD N : ℝ) = (⌊(N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)⌋₊ : ℝ) := rfl
    rw [hopD]; linarith [hfl]
  -- margin: 4·N^{7/16} ≤ N^{1/2 − 9/100000}
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hNc4 : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 16 - 9 / 100000) := by
    have h20 : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 20) := by
      rw [Real.rpow_def_of_pos hNpos]
      have he : Real.log 4 ≤ Real.log N * (1 / 20) := by nlinarith [hlogN, hlog4]
      calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (Real.log N * (1 / 20)) := Real.exp_le_exp.mpr he
    calc (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 20) := h20
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 16 - 9 / 100000) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hmargin : 4 * (N : ℝ) ^ ((7 : ℝ) / 16) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
    have hspl : (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)
        = (N : ℝ) ^ ((7 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 16 - 9 / 100000) := by
      rw [← Real.rpow_add hNpos, show (7 : ℝ) / 16 + (1 / 16 - 9 / 100000) = 1 / 2 - 9 / 100000 by
        norm_num]
    have h716pos : (0 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 16) := by positivity
    rw [hspl]; nlinarith [hNc4, h716pos]
  -- close: 2·w ≤ 2·N^{7/16} ≤ 4·N^{7/16} − 2 < N^{1/2−9/100000} − 1 < opD N
  linarith [hwub, hge1, hmargin, hDlb]

/-! ## Byte-lock — the interface this file's fix must eventually fill (machine-anchored) -/

section ByteLock

-- the head keystone (narrow `[w, 2w]` D-window) and its wide-window engine
#check @Salt.Goldbach.gold_box_rows_at_op
#check @Salt.Goldbach.gold_box_price_live_kerr
-- the DEAD branch (already fills `hprice` for dead boxes) + the annulus scale facts
#check @Salt.Goldbach.gold_box_price_dead_kerr
#check @Salt.Goldbach.gold_box_XM_scale
#check @Salt.Goldbach.gold_box_Xfloor
#check @Salt.Goldbach.gold_box_Mfloor
-- the aggregate the concrete supplier must feed (constant worst-`W` price)
#check @Salt.Goldbach.gold_hSum_discharged
-- the terminal whose `hprice`/`hpriceSym`/`hpriceLow` slots remain OPEN
#check @Salt.Goldbach.gold_hBVblocksW_discharge'
-- the count-level honest disc (source of the trivial per-modulus AP bound)
#check @Salt.Goldbach.goldBlockBoxHonestDisc
-- THIS FILE's certificate: the head cap is strictly below the op conductor
#check @Salt.Goldbach.gold_dsplit_head_cap_below_conductor

end ByteLock

end Salt.Goldbach
