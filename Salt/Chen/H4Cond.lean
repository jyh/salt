/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SharpF

/-!
# H4C — the conditioned Hyp-(4) supplier (catch #66 repair)

Catch #66 (flags.md, 2026-07-14 H2-GATE): the unconditioned supplier slot

  `h4 : ∀ s' z' D', 1 ≤ D' → Vlow s' D' ≤ (3K / logRatio z' D') · W s'`

threaded by every A₁/A₂/A₃ carrier is FALSE for every `K` (at `z' = 1, D' = 1`:
`Vlow = 1 > 0 = RHS` by the division conventions; at honest `z' = 2, D' = 2⁶⁰` it contradicts
`hKe : K ≤ 1 + ε`).  The repair (chen.md GATE RESULT, correction C1, node H4C): the slot is
CONDITIONED on the sieve-class rows (`hz`/`hguard`/`hnu`) and the flat-cell operating window
`1 ≤ logRatio z' D' ≤ 3` — exactly the facts in scope at the real use sites (the depth-1 base
cases of `T_le_of_peel_step_w`/`_wp`/`_wpc` and `hh_sharp_of_window`'s flat cell).

`h4_cond_of_base` below is the supplier GLU-2W calls to fill the conditioned slot.

## The premise-set choice (adjustment of the gate's proposed route, documented)

The gate proposed discharging via `h4_base` at `u := D'^{1/3}` + `thresh_mono`, under a NEW
op-row `hw0z : (w0R ε)³ ≤ z'`.  That route is not taken, for a structural reason: the op-row
mentions the ∀-bound `z'`, so it would have to live INSIDE the conditioned slot's premise
bundle — and no use site can discharge it there (the windowed induction's cutoff shrinks to an
arbitrary sieve prime `p`, and the `hguard` row at `p` bounds `p` from below only by
`exp(19/log(1+ε))`, which is BELOW `w0R ε = exp(40/log(1+ε))`).  For the same reason the
draft bundle's per-prime row `w0R ε ≤ p` is TRIMMED: it is not derivable at the use sites,
whose per-prime stock is exactly `hz`/`hguard`/`hnu`.

Instead the discharge anchors `vratio_prod_le` at the minimal up-window prime
`p₀ ≥ D'^{1/3}`, whose threshold guard is supplied per-prime by the `hguard` row itself —
this is `SharpF.vlow_le_of_guard` (VD1), already landed.  Consequences:

* **no op-row**: the `(w0R ε)³ ≤ z'` obligation disappears; GLU-2W owes exactly the
  `hz`/`hguard`/`hnu` rows it already discharges at its concrete sieves (e.g.
  `twinA1_hguard`/`switch_hguard` from `hPlow : w0R ε ≤ p`) plus `0 ≤ ε` and `1 + ε ≤ K`;
* `h4_base` (`Hyp4.lean`) remains the per-instance form for abstract-`u` callers; the
  conditioned ∀-slot is supplied here.
-/

namespace Salt.Chen

/-- **H4C — the conditioned Hyp-(4) supplier** (catch #66 repair; the plug GLU-2W calls).
The V-ratio bound `Vlow s' D' ≤ (3K / logRatio z' D') · W s'` holds under the sieve-class
rows (prime support `< z'`, the `hguard` threshold guards, the `hnu` density bound) and the
flat-cell window `1 ≤ logRatio z' D' ≤ 3` — the exact premise bundle every use site has in
scope.  Discharge: `vlow_le_of_guard` (VD1) at `K = 1 + ε`, then numerator monotonicity from
`1 + ε ≤ K`.  NO `(w0R ε)³ ≤ z'` op-row is required (see the module docstring). -/
theorem h4_cond_of_base (ε K : ℝ) (hε : 0 ≤ ε) (hK : 1 + ε ≤ K) :
    ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
      (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
      (∀ q ∈ s'.prodPrimes.primeFactors,
          3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
      (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
      1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
      Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s' := by
  intro s' z' D' _hD' hz hguard hnu hS1 hS3
  have hS0 : (0 : ℝ) < logRatio z' D' := by linarith
  calc Vlow s' D'
      ≤ (3 * (1 + ε) / logRatio z' D') * Salt.BrunLower.W s' :=
        vlow_le_of_guard s' ε z' D' hε hz hguard hnu hS1 hS3
    _ ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s' :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith) hS0.le) (Salt.BrunLower.W_pos s').le

end Salt.Chen
