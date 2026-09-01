/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.BandRatedAssembly

/-!
# QUEUE 7b — the co-factor supply at the `h`-INFLATED arc cap (`HDoorSupply`)

The producer wave for `HDoorArc.M4SievedDoorSqH`, commissioned by the helm 2026-08-31 17:4x
at **`h = 2`**, executor tier, transcription-shaped.  Every statement here is a landed name's
statement with **exactly one change**: the major-arc denominator allowance
`arcDen 12 H` becomes `h · arcDen 12 H`.

## Why the change is confined to one substitution

The cap reaches the co-factor chain through `ArithPageLinear.SocketBaseL`'s fifth conjunct
`(q : ℝ) ≤ arcDen 12 H`, and **all five of its consumers factor through ONE lemma** —
`RbdSupply.log_le_of_le_arcDen` (`log q ≤ 12·loglog H`).  Under inflation that single input
becomes `log q ≤ log h + 12·loglog H`, and the five rows follow from it verbatim.  §1 is that
lemma; §2–§3 are the five rows; §4 is the threshold page where the cost is paid.

## Where the cost lands, and the margin (measured before a byte was written)

Write `Λ := loglog H` and `L := log h`.  The five rows carry, on `log q`, the coefficients
`1/8`, `0` (inside a `log`), `3/4`, `0` (inside a `log`) and `4`; against the threshold page's
`32·` weight that is `4 + 24 + 128 = 156`, and `156 × 12 = 1872` reproduces the landed
`Λ`-total exactly — the identity that checks the table is right.  The landed hypothesis carries
`1900Λ + 20·log(7+12Λ) + 2300`, so the slack is `28Λ + 4·log(7+12Λ) + 84`, and

* the `h`-cost is `156·L` on the three bare rows, plus at most `8·log 2` of second-order
  cost where the two `log` rows widen `log(12Λ) → log(L+12Λ)` and
  `log(7+12Λ) → log(7+L+12Λ)` (both absorbed for `L ≤ 7`);
* ⭐ **the cost coefficient and the slack coefficient on `Λ` are the same number, `28`** —
  so the budget condition is `L ≲ Λ + 3` and the cap-inflation budget is itself about `log H`.

At the family's own floor `Λ ≥ 1` (from `hH : exp 1 ≤ log H`) the `h = 2` instance spends
`164·log 2 = 113.68` against `28 + 4·log 19 + 84 = 123.78` — **it fits by ×1.09, and that
margin is DISCLOSED, not comfortable.**  `pieceFloor_vt_threshold_h` carries the budget as an
explicit hypothesis so the family is honest about it; `pieceFloor_vt_threshold_two` discharges
it at `h = 2` from `hH` alone, so the `h = 2` lane needs no hypothesis the landed lane lacks.

⛔ **THE TWO-SITE WARNING.**  `SocketBaseL` carries the cap TWICE, moving OPPOSITE WAYS: the
fifth conjunct `q ≤ arcDen 12 H` (inflation STRENGTHENS the demand) and the eleventh
`x ≤ 16ω·arcDen 12 H·A` (inflation WEAKENS it, and `cofkL_logX_floor` DIVIDES by it).  A port
that inflates one and not the other is measuring a different object.  §5 moves both together.

⛔ **B₅ stays `12` throughout — iron rule 1.**  The exponent never moves; only the allowance.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the base substitution: ONE lemma, from which the five rows follow -/

/-- The inflated allowance is positive and at least the landed one (`h ≥ 1`). -/
lemma arcDen_le_h_mul_arcDen {H h : ℕ} (hh : 0 < h) :
    arcDen 12 H ≤ (h : ℝ) * arcDen 12 H := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hA : (0 : ℝ) ≤ arcDen 12 H := by
    rw [arcDen]; positivity
  nlinarith

/-- **THE `log q` SUMMAND AT THE INFLATED CAP** (`log_le_of_le_arcDen_h`) — the `h`-family of
`RbdSupply.log_le_of_le_arcDen`.  `q ≤ h·(log H)^12 ⟹ log q ≤ log h + 12·loglog H`.

This is the **only** place the inflation is read.  Every row below consumes this conclusion
and nothing else about the cap, which is why the wave is a transcription: the landed proofs
are re-run against `L + 12Λ` where they read `12Λ`. -/
lemma log_le_of_le_arcDen_h {q H h : ℕ} [NeZero q] (hh : 0 < h)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    Real.log q ≤ Real.log h + 12 * Real.log (Real.log (H : ℝ)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogH : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hH
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hA2 : (2 : ℝ) ≤ arcDen 12 H := two_le_arcDen hH
  have h := Real.log_le_log (by linarith : (0 : ℝ) < (q : ℝ)) hq
  rw [Real.log_mul (ne_of_gt hh0) (by linarith : arcDen 12 H ≠ 0),
    log_arcDen_twelve hlogH] at h
  exact h

/-- `mertensCap`'s argument is `max 2 q`, which obeys the inflated cap for the same reason it
obeys the landed one — `2 ≤ arcDen 12 H ≤ h·arcDen 12 H`. -/
lemma log_max_two_le_of_le_arcDen_h {q H h : ℕ} (hh : 0 < h)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    Real.log ((max 2 q : ℕ) : ℝ) ≤ Real.log h + 12 * Real.log (Real.log (H : ℝ)) := by
  have hlogH : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hH
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hA2 : (2 : ℝ) ≤ arcDen 12 H := two_le_arcDen hH
  have hmono := arcDen_le_h_mul_arcDen (H := H) hh
  have hcast : ((max 2 q : ℕ) : ℝ) = max 2 (q : ℝ) := by push_cast; rfl
  have hle : ((max 2 q : ℕ) : ℝ) ≤ (h : ℝ) * arcDen 12 H := by
    rw [hcast]; exact max_le (by linarith) hq
  have hpos : (0 : ℝ) < ((max 2 q : ℕ) : ℝ) := by
    rw [hcast]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have h := Real.log_le_log hpos hle
  rwa [Real.log_mul (ne_of_gt hh0) (by linarith : arcDen 12 H ≠ 0),
    log_arcDen_twelve hlogH] at h

end Salt.MR
