/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.BandRatedAssembly
import Salt.MR.BandRatedSocket
import Salt.MR.HDoorArc
import Salt.MR.M4ClassPrice

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

open Salt.SW
open Salt.Entropy.Chowla
open Salt.ExpSum

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

/-- `log 4 = 2·log 2`.  `RbdSupply`'s copy is `private` to that file; this is the same
one-liner, kept local for the same reason. -/
private lemma log_four_eq_two_mul_log_two : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  push_cast; ring

/-! ## §2 — the three `RbdSupply` rows at the inflated cap

Each is the landed proof re-run against `L + 12Λ` where it read `12Λ`.  Two of the three
carry the inflation only INSIDE a logarithm — that is why the `h`-cost of the whole table is
`156·L` and not more, and it is a fact about the shape of `mertensCap` and `vkMidDebitSharp`,
not a choice made here. -/

/-- **THE `mertensCap` SUMMAND AT THE INFLATED CAP** (`mertensCap_le_of_le_arcDen_h`).
The `h`-family of `RbdSupply.mertensCap_le_of_le_arcDen`: the inflation enters INSIDE the
logarithm, `log(12Λ) → log(L + 12Λ)`. -/
lemma mertensCap_le_of_le_arcDen_h {q H h : ℕ} (hh : 0 < h)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    mertensCap q
      ≤ Real.log (Real.log h + 12 * Real.log (Real.log (H : ℝ))) + 21 := by
  have hmax := log_max_two_le_of_le_arcDen_h hh hH hq
  have h2le : (2 : ℝ) ≤ ((max 2 q : ℕ) : ℝ) := by
    have h : (2 : ℕ) ≤ max 2 q := le_max_left _ _
    exact_mod_cast h
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmax : Real.log 2 ≤ Real.log ((max 2 q : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) h2le
  have hlogmaxpos : (0 : ℝ) < Real.log ((max 2 q : ℕ) : ℝ) := lt_of_lt_of_le hlog2pos hlogmax
  have hll : Real.log (Real.log ((max 2 q : ℕ) : ℝ))
      ≤ Real.log (Real.log h + 12 * Real.log (Real.log (H : ℝ))) :=
    Real.log_le_log hlogmaxpos hmax
  have hdiv : 12 / Real.log ((max 2 q : ℕ) : ℝ) ≤ 12 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2pos hlogmax
  have h12 : 12 / Real.log 2 ≤ 17.4 := by
    rw [div_le_iff₀ hlog2pos]
    linarith [Real.log_two_gt_d9]
  have hM := mertensM_le_three
  unfold mertensCap
  linarith

/-- **THE `vkDebitConst` SUMMAND AT THE INFLATED CAP** (`vkDebitConst_le_of_le_arcDen_h`).
The `h`-family of `RbdSupply.vkDebitConst_le_of_le_arcDen`.  This row carries `log q` BARE at
coefficient `3/4`, so it is one of the three that pay: `10 + 9Λ ↦ 10 + (3/4)·L + 9Λ`. -/
lemma vkDebitConst_le_of_le_arcDen_h {q H h : ℕ} [NeZero q] (hh : 0 < h)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    vkDebitConst (vkEulerCorr q * vkTwistConst q)
      ≤ 10 + (3 / 4) * Real.log h + 9 * Real.log (Real.log (H : ℝ)) := by
  have hlogq := log_le_of_le_arcDen_h hh hH hq
  have hC := log_vkEuler_mul_vkTwist_le (q := q)
  have h2 := Real.log_two_lt_d9
  have h4 := log_four_eq_two_mul_log_two
  unfold vkDebitConst
  linarith

/-- **THE `vkMidDebitSharp` SUMMAND AT THE INFLATED CAP** (`vkMidDebitSharp_le_of_le_arcDen_h`).
The `h`-family of `RbdSupply.vkMidDebitSharp_le_of_le_arcDen`: like `mertensCap`, the
inflation enters only INSIDE the logarithm, `log(7+12Λ) → log(7+L+12Λ)`.

The landed proof's two roundings are untouched; the only edit is that `hstep`'s
`B := 6 + 12Λ` becomes `6 + L + 12Λ`, still nonnegative, so `e^100 + B ≤ e^100·(1+B)` runs
verbatim. -/
lemma vkMidDebitSharp_le_of_le_arcDen_h {q H h : ℕ} [NeZero q] (hh : 0 < h)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    vkMidDebitSharp q
      ≤ 29 + (1 / 4) * Real.log (7 + Real.log h + 12 * Real.log (Real.log (H : ℝ))) := by
  have hLH1 := one_le_loglog_of_exp_le hH
  have hlogq := log_le_of_le_arcDen_h hh hH hq
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have h2 := Real.log_two_lt_d9
  have h2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 := log_four_eq_two_mul_log_two
  set LH : ℝ := Real.log (Real.log (H : ℝ)) with hLHdef
  set Lh : ℝ := Real.log h with hLhdef
  have hE1 : (1 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h0 : (0 : ℝ) ≤ Real.exp 100 := (Real.exp_pos 100).le
    calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr h0
  have he100 : (1 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  -- the height term: `log(2e^A + 2) ≤ log 4 + e^100`
  have hht : Real.log (2 * Real.exp (Real.exp 100) + 2) ≤ Real.log 4 + Real.exp 100 := by
    have hb : 2 * Real.exp (Real.exp 100) + 2 ≤ 4 * Real.exp (Real.exp 100) := by linarith
    have h1 : Real.log (2 * Real.exp (Real.exp 100) + 2)
        ≤ Real.log (4 * Real.exp (Real.exp 100)) := Real.log_le_log (by positivity) hb
    have h2' : Real.log (4 * Real.exp (Real.exp 100)) = Real.log 4 + Real.exp 100 := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    linarith
  -- the inner argument, rounded to `e^100 + (6 + L + 12Λ)`
  have hinner : 7 / 2 + Real.log 2 + Real.log q
      + Real.log (2 * Real.exp (Real.exp 100) + 2)
      ≤ Real.exp 100 + (6 + Lh + 12 * LH) := by linarith
  have hinner0 : (0 : ℝ) < 7 / 2 + Real.log 2 + Real.log q
      + Real.log (2 * Real.exp (Real.exp 100) + 2) := by
    have hnn : (0 : ℝ) ≤ Real.log (2 * Real.exp (Real.exp 100) + 2) :=
      Real.log_nonneg (by linarith)
    linarith
  -- pull `e^100` out of the logarithm
  have hB0 : (0 : ℝ) ≤ 6 + Lh + 12 * LH := by linarith
  have h7pos : (0 : ℝ) < 7 + Lh + 12 * LH := by linarith
  have hstep : Real.exp 100 + (6 + Lh + 12 * LH)
      ≤ Real.exp 100 * (7 + Lh + 12 * LH) := by
    nlinarith [he100, hB0]
  have hlogstep : Real.log (Real.exp 100 + (6 + Lh + 12 * LH))
      ≤ 100 + Real.log (7 + Lh + 12 * LH) := by
    have h1 : Real.log (Real.exp 100 + (6 + Lh + 12 * LH))
        ≤ Real.log (Real.exp 100 * (7 + Lh + 12 * LH)) :=
      Real.log_le_log (by linarith) hstep
    have h2' : Real.log (Real.exp 100 * (7 + Lh + 12 * LH))
        = 100 + Real.log (7 + Lh + 12 * LH) := by
      rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt h7pos), Real.log_exp]
    linarith
  have hlogmono : Real.log (7 / 2 + Real.log 2 + Real.log q
        + Real.log (2 * Real.exp (Real.exp 100) + 2))
      ≤ Real.log (Real.exp 100 + (6 + Lh + 12 * LH)) := Real.log_le_log hinner0 hinner
  unfold vkMidDebitSharp
  linarith

/-! ## §3 — the fifth (RATED band) row at the inflated cap

`bandConstQ Z δ q` is the summand that only the RATED lane has, and it is the expensive one:
its `max` takes the branch whose coefficient on `log q` is `4` (`log q − log δ` is the other
branch, coefficient `1`), so against the threshold's `32·` weight it contributes `128` of the
table's `156`.  **That 128 is where escape 1 would act** — routing this row into the page's own
`hKB` constant slot via a sibling `bandArcConstH` drops the cost to `28·log h` — and it is
PRE-AUTHORIZED but NOT TAKEN: at `h = 2` the lemma-floor route clears without it. -/

/-- **THE FIFTH SUMMAND AT THE INFLATED CAP** (`bandConstQ_le_of_le_arcDen_h`) — the `h`-family
of `BandRatedAssembly.bandConstQ_le_of_le_arcDen`.

`48Λ + bandArcConst ↦ 4·L + 48Λ + bandArcConst`.  Both branches of the `max` are re-run: the
`−log δ` branch pays `L` and the disk branch pays `4L`, so the `max` pays `4L`. -/
theorem bandConstQ_le_of_le_arcDen_h {q H h : ℕ} [NeZero q] {Z δ : ℝ} (hZ : 1 ≤ Z) (_hδ : 0 < δ)
    (hh : 0 < h) (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    bandConstQ Z δ q
      ≤ 4 * Real.log h + 48 * Real.log (Real.log (H : ℝ)) + bandArcConst Z δ := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqN : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hLH1 : (1 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := one_le_loglog_of_exp_le hH
  have hlogq : Real.log q ≤ Real.log h + 12 * Real.log (Real.log (H : ℝ)) :=
    log_le_of_le_arcDen_h hh hH hq
  set c : ℝ := Real.log ((3 + Real.sqrt 5) / 2) with hcdef
  have hc0 : 0 < c := e4a_log_golden_pos
  -- `log (goldenL1 q) = log c − (5/2)·log q`
  have hrpow0 : (0 : ℝ) < (q : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hq0 _
  have hglog : Real.log (goldenL1 q) = c.log - (5 / 2) * Real.log q := by
    rw [goldenL1, Real.log_div (ne_of_gt hc0) (ne_of_gt hrpow0), Real.log_rpow hq0]
  -- `1 / goldenL1 q ≤ q³ / c`, via `q^{5/2} ≤ q³`
  have hrpow3 : (q : ℝ) ^ (5 / 2 : ℝ) ≤ (q : ℝ) ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (5 / 2 : ℝ) ≤ (3 : ℝ))
    rwa [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  -- the log-argument, bounded by `(648·Z/c)·q⁵`
  have hdisk : diskConst q ≤ 81 / 2 * (q : ℝ) ^ 2 := diskConst_le hqN
  have hdisk0 : (0 : ℝ) ≤ diskConst q := le_trans (by norm_num) (diskConst_ge_head hqN)
  have hg0 : 0 < goldenL1 q := goldenL1_pos q
  have hinv : 1 / goldenL1 q ≤ (q : ℝ) ^ (3 : ℕ) / c := by
    rw [goldenL1, one_div_div]
    gcongr
  have h16 : (0 : ℝ) ≤ 16 * (q : ℝ) * Z := by positivity
  have hnum : 16 * (q : ℝ) * Z * diskConst q ≤ 648 * Z * (q : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hdisk h16
    nlinarith [h]
  have hargle : 16 * (q : ℝ) * Z * diskConst q / goldenL1 q ≤ 648 * Z / c * (q : ℝ) ^ 6 := by
    rw [div_eq_mul_one_div]
    have hinv0 : (0 : ℝ) ≤ 1 / goldenL1 q := by positivity
    calc 16 * (q : ℝ) * Z * diskConst q * (1 / goldenL1 q)
        ≤ 648 * Z * (q : ℝ) ^ 3 * ((q : ℝ) ^ (3 : ℕ) / c) :=
          mul_le_mul hnum hinv hinv0 (by positivity)
      _ = 648 * Z / c * (q : ℝ) ^ 6 := by ring
  have harg0 : (0 : ℝ) < 16 * (q : ℝ) * Z * diskConst q / goldenL1 q := by
    have : (0 : ℝ) < 27 / 2 := by norm_num
    have hd : (0 : ℝ) < diskConst q := lt_of_lt_of_le this (diskConst_ge_head hqN)
    positivity
  have hlogarg : Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q)
      ≤ Real.log (648 * Z / c) + 6 * Real.log q := by
    have hstep := Real.log_le_log harg0 hargle
    have hpos : (0 : ℝ) < 648 * Z / c := by positivity
    rwa [Real.log_mul (ne_of_gt hpos) (by positivity), Real.log_pow] at hstep
  -- assemble: the disk branch pays `4·log q`, the `δ` branch pays `1·log q`
  have hbranch2 : Real.log 2 - Real.log (goldenL1 q)
        + (2 * Real.log 4 + (3 / 4) * Real.log 2
          + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q))
      ≤ 4 * Real.log h + 48 * Real.log (Real.log (H : ℝ)) + bandArcConst Z δ := by
    have hb : bandArcConst Z δ ≥ Real.log 2 + 2 * Real.log 4 + (3 / 4) * Real.log 2
        - Real.log c + (1 / 4) * Real.log (648 * Z / c) := le_max_right _ _
    rw [hglog]
    linarith
  have hbranch1 : Real.log q - Real.log δ
      ≤ 4 * Real.log h + 48 * Real.log (Real.log (H : ℝ)) + bandArcConst Z δ := by
    have hb : bandArcConst Z δ ≥ -Real.log δ := le_max_left _ _
    linarith
  unfold bandConstQ
  exact max_le hbranch1 hbranch2

/-! ## §4 — THE BINDING ARM: the threshold page, and what `h` costs there

This is the page no document had named before the 08/31 measurement, and it is where the whole
cap-inflation is paid.  The five rows above assemble to

  `156·L + 1872·Λ + 8·log(L+12Λ) + 8·log(7+L+12Λ) + 2216 + 32·K + 32·bandArcConst`

against the landed hypothesis's `1900·Λ + 20·log(7+12Λ) + 2300 + 32·Kbig`.  For `L ≤ 7` the
two `log` rows are absorbed at a cost of `8·log 2`, and what is left is the budget

  `156·L + 8·log 2  ≤  28·Λ + 4·log(7+12Λ) + 84`.

⭐ **The `Λ`-coefficient on each side is `28`.**  The condition is `L ≲ Λ + 3`: the door may be
twisted by any shift up to about `e³·log H` before a numeral has to move.

⚠️ **THE MARGIN IS DISCLOSED, NOT COMFORTABLE.**  At the family's own floor `Λ ≥ 1` and `h = 2`
the budget spends `164·log 2 = 113.68` against `28 + 4·log 19 + 84 = 123.78` — **×1.09**.  (The
pre-wave measurement published ×1.14 because it had not yet charged the `8·log 2` of
second-order cost the two `log` rows carry; this is the corrected figure, and it is the one the
kernel checks.)  At the socket's own floor `Λ ≥ 518` — in scope at every application site,
merely not passed — the same budget clears by ×135; threading it is ESCAPE 2 and it ADDS A
HYPOTHESIS, so it is not taken here. -/

/-- **THE THRESHOLD PAGE AT THE INFLATED CAP** (`pieceFloor_vt_threshold_of_loglog_rated_h`) —
the `h`-family of `BandRatedAssembly.pieceFloor_vt_threshold_of_loglog_rated`.

The conclusion and the `hthr` hypothesis are BYTE-IDENTICAL to the landed page's: the numerals
`1900`, `20`, `2300` do not move, and no consumer of the landed page has to change shape.  The
family carries its own budget as `hbud` — that is the honest statement of what an `h`-inflation
costs, and `pieceFloor_vt_threshold_of_loglog_rated_two` discharges it at `h = 2` from `hH`
alone.

`hh7 : log h ≤ 7` is what lets the `mertensCap` row's `log(L + 12Λ)` be absorbed into the
page's own `log(7 + 12Λ)`; it is a bound on `h` of about `1096`, far above any `h` this budget
could otherwise afford, so it constrains nothing. -/
theorem pieceFloor_vt_threshold_of_loglog_rated_h {q H h : ℕ} [NeZero q]
    {X K Kbig D Z δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 < δ) (hh : 0 < h)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H)
    (hh7 : Real.log h ≤ 7)
    (hbud : 156 * Real.log h + 8 * Real.log 2
      ≤ 28 * Real.log (Real.log (H : ℝ))
        + 4 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 84)
    (hKB : K + bandArcConst Z δ ≤ Kbig)
    (hthr : 40 * Real.log (Real.log (Real.log X))
        + 1900 * Real.log (Real.log (H : ℝ))
        + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        + 2300 + 32 * Kbig + 32 * D
      < Real.log (Real.log X)) :
    40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
          + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q
          + bandConstQ Z δ q + K + 25 + D)
      < Real.log (Real.log X) := by
  have hLH1 := one_le_loglog_of_exp_le hH
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hband := bandConstQ_le_of_le_arcDen_h (q := q) (H := H) (h := h) hZ hδ hh hH hq
  set LH : ℝ := Real.log (Real.log (H : ℝ)) with hLHdef
  set Lh : ℝ := Real.log h with hLhdef
  have hlogq := log_le_of_le_arcDen_h hh hH hq
  have hcap := mertensCap_le_of_le_arcDen_h (q := q) hh hH hq
  have hvkd := vkDebitConst_le_of_le_arcDen_h (q := q) hh hH hq
  have hvkm := vkMidDebitSharp_le_of_le_arcDen_h (q := q) hh hH hq
  have h7pos : (0 : ℝ) < 7 + 12 * LH := by linarith
  have hlognn : (0 : ℝ) ≤ Real.log (7 + 12 * LH) := Real.log_nonneg (by linarith)
  -- ⟦row 2's widened logarithm, absorbed: `L ≤ 7` puts `L + 12Λ` under `7 + 12Λ`⟧
  have habs2 : Real.log (Lh + 12 * LH) ≤ Real.log (7 + 12 * LH) :=
    Real.log_le_log (by linarith) (by linarith)
  -- ⟦row 4's widened logarithm, absorbed at a cost of `log 2`: `7 + L + 12Λ ≤ 2·(7 + 12Λ)`⟧
  have habs4 : Real.log (7 + Lh + 12 * LH) ≤ Real.log 2 + Real.log (7 + 12 * LH) := by
    have hle : 7 + Lh + 12 * LH ≤ 2 * (7 + 12 * LH) := by linarith
    have h1 : Real.log (7 + Lh + 12 * LH) ≤ Real.log (2 * (7 + 12 * LH)) :=
      Real.log_le_log (by linarith) hle
    have h2 : Real.log (2 * (7 + 12 * LH)) = Real.log 2 + Real.log (7 + 12 * LH) :=
      Real.log_mul (by norm_num) (ne_of_gt h7pos)
    linarith
  linarith

/-- ⭐ **THE `h = 2` LANE, AND IT ASKS FOR NOTHING THE LANDED LANE DOES NOT**
(`pieceFloor_vt_threshold_of_loglog_rated_two`).

Hypothesis-for-hypothesis this is `BandRatedAssembly.pieceFloor_vt_threshold_of_loglog_rated`
with `hq` alone changed, from `q ≤ arcDen 12 H` to `q ≤ 2·arcDen 12 H`.  The budget is
discharged from `hH`: `Λ ≥ 1` gives `28Λ ≥ 28`, and `7 + 12Λ ≥ 19 ≥ 16` gives
`4·log(7+12Λ) ≥ 16·log 2`, so the demand `164·log 2 ≤ 112 + 16·log 2` is
`148·log 2 ≤ 112`, i.e. `log 2 ≤ 0.7567…`. -/
theorem pieceFloor_vt_threshold_of_loglog_rated_two {q H : ℕ} [NeZero q]
    {X K Kbig D Z δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 < δ)
    (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ 2 * arcDen 12 H)
    (hKB : K + bandArcConst Z δ ≤ Kbig)
    (hthr : 40 * Real.log (Real.log (Real.log X))
        + 1900 * Real.log (Real.log (H : ℝ))
        + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        + 2300 + 32 * Kbig + 32 * D
      < Real.log (Real.log X)) :
    40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
          + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q
          + bandConstQ Z δ q + K + 25 + D)
      < Real.log (Real.log X) := by
  have hLH1 := one_le_loglog_of_exp_le hH
  have h2lt := Real.log_two_lt_d9
  have h2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set LH : ℝ := Real.log (Real.log (H : ℝ)) with hLHdef
  have hcast : (((2 : ℕ) : ℝ)) = (2 : ℝ) := by norm_num
  have hlog2N : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by rw [hcast]
  -- ⟦`4·log(7+12Λ) ≥ 16·log 2`, from `7 + 12Λ ≥ 16`⟧
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hge : Real.log 16 ≤ Real.log (7 + 12 * LH) :=
    Real.log_le_log (by norm_num) (by linarith)
  refine pieceFloor_vt_threshold_of_loglog_rated_h (h := 2) hZ hδ (by norm_num) hH
    (by rw [hcast]; exact hq) (by rw [hlog2N]; linarith) ?_ hKB hthr
  rw [hlog2N]
  linarith

/-! ## §5 — the exit at the inflated cap

`capFreeFloor3_pieceDatum_arcDen_rated` is the form a consumer whose modulus range is the
major-arc denominator cap reads.  Its `h`-family is the landed exit with the arc binder
inflated and nothing else touched — the `K` it produces is still ONE symbolic nonnegative real,
so a consumer's cushion is unchanged in SHAPE, which is the property the rated lane was built
for. -/

/-- **THE EXIT AT THE INFLATED CAP** (`capFreeFloor3_pieceDatum_arcDen_rated_h`) — the
`h`-family of `BandRatedAssembly.capFreeFloor3_pieceDatum_arcDen_rated`.

Only the arc binder moves: `q ≤ arcDen 12 H ↦ q ≤ h·arcDen 12 H`.  The budget travels with it
as `hbud`/`hh7`, exactly as on the page below. -/
theorem capFreeFloor3_pieceDatum_arcDen_rated_h (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log h ≤ 7) :
    ∃ Z δ K : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (H : ℕ) (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X D : ℝ),
      Real.exp 1 ≤ Real.log (H : ℝ) → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      156 * Real.log h + 8 * Real.log 2
          ≤ 28 * Real.log (Real.log (H : ℝ))
            + 4 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 84 →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      32 * diskConst q / goldenL1 q ≤ Real.log X →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 1900 * Real.log (Real.log (H : ℝ))
          + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
          + 2300 + 32 * K + 32 * D
        < Real.log (Real.log X) →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X := by
  obtain ⟨Z, δ, K, hZ, hδ, hK0, hK⟩ := capFreeFloor3_pieceDatum_vt_rated
  refine ⟨Z, δ, K + max 0 (bandArcConst Z δ), hZ, hδ,
    add_nonneg hK0 (le_max_left _ _), ?_⟩
  intro q _ H χ Pseq Qseq 𝒥 X D hH harc hbud hX hD0 hgate hdebit hthr
  exact hK q χ Pseq Qseq 𝒥 X D hX hD0 hgate hdebit
    (pieceFloor_vt_threshold_of_loglog_rated_h hZ hδ hh hH harc hh7 hbud
      (by linarith [le_max_right (0 : ℝ) (bandArcConst Z δ)]) hthr)

/-- ⭐ **THE EXIT AT `h = 2`** (`capFreeFloor3_pieceDatum_arcDen_rated_two`) — binder-for-binder
the landed rated exit, with `q ≤ arcDen 12 H` alone replaced by `q ≤ 2·arcDen 12 H`.

**No hypothesis is added and none is dropped.**  That is the whole claim of the `h = 2` lane,
and it is what makes the producer wave for `HDoorArc.M4SievedDoorSqH` a transcription as to the
cap rather than a design act. -/
theorem capFreeFloor3_pieceDatum_arcDen_rated_two :
    ∃ Z δ K : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (H : ℕ) (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X D : ℝ),
      Real.exp 1 ≤ Real.log (H : ℝ) → (q : ℝ) ≤ 2 * arcDen 12 H →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      32 * diskConst q / goldenL1 q ≤ Real.log X →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 1900 * Real.log (Real.log (H : ℝ))
          + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
          + 2300 + 32 * K + 32 * D
        < Real.log (Real.log X) →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X := by
  obtain ⟨Z, δ, K, hZ, hδ, hK0, hK⟩ := capFreeFloor3_pieceDatum_vt_rated
  refine ⟨Z, δ, K + max 0 (bandArcConst Z δ), hZ, hδ,
    add_nonneg hK0 (le_max_left _ _), ?_⟩
  intro q _ H χ Pseq Qseq 𝒥 X D hH harc hX hD0 hgate hdebit hthr
  exact hK q χ Pseq Qseq 𝒥 X D hX hD0 hgate hdebit
    (pieceFloor_vt_threshold_of_loglog_rated_two hZ hδ hH harc
      (by linarith [le_max_right (0 : ℝ) (bandArcConst Z δ)]) hthr)

/-! ## §6 — THE SOCKET, WITH BOTH CAP SITES MOVED TOGETHER

⛔⛔ **THIS IS THE TRAP THE MEASUREMENT LEFT BEHIND, AND IT IS THE REASON THIS SECTION EXISTS.**
`ArithPageLinear.SocketBaseL` mentions `arcDen 12 H` TWICE, and the two occurrences move in
OPPOSITE DIRECTIONS under inflation:

* the **fifth** conjunct `(q : ℝ) ≤ arcDen 12 H` — inflating it **STRENGTHENS** the demand
  (a wider range of moduli must be served), and it is what §1–§5 above pay for;
* the **eleventh** conjunct `(R.x : ℝ) ≤ 16·ω·arcDen 12 H·A` — inflating it **WEAKENS** the
  hypothesis, and `RegisterSupply.cofkL_logX_floor` **DIVIDES** by it
  (`A ≥ 4^{2E}/(2·arcDen 12 H)`), so the inflation is a SUBTRACTION of `log h` from a floor
  that is LINEAR in `H₊`.

⇒ **A port that inflated only one of the two would be measuring a different object.**
`SocketBaseLH` moves both, and every lemma below is the landed one re-run against it.

The eleventh site is free by an enormous margin — the floor spends `H₊/(90200·h²)` and is asked
for `H₊/(10⁶·h²)`, so at `H₊ ≥ 10²⁶·h⁴` a subtraction of `log h ≤ 7` is invisible.  It is
nonetheless CARRIED, not waved: `hh7` appears in the statement.

⛔⛔ **AND THE `h²` IS NOT COSMETIC — IT IS WAVE H3 BLOCK E's WHOLE CONTENT (ruling (a),
2026-09-02).**  Until block E these pages demanded the FLAT `1/500 ≤ R.eps`, which the `h`
head's own pin `ε = 1/(500·h)` makes **FALSE at `h ≥ 2`**; at `1/(500h)` the closing
coefficient of the flat conclusion `H₊/10⁶ ≤ log(A+s)` goes NEGATIVE at `h = 4`, so no `H₊`
closes it.  Both sides were hypotheses of conditional statements, so **no gate in the
repository could see it.**  The repair is the `h`-explicit conclusion below. -/

/-- **THE LINEAR SOCKET AT THE INFLATED CAP** (`SocketBaseLH`) — `ArithPageLinear.SocketBaseL`
with **BOTH** occurrences of the arc denominator inflated to `h · arcDen 12 H`.

⭐ **THE INFLATED SOCKET IS STRICTLY WEAKER** (`socketBaseLH_of_socketBaseL`): BOTH inflated
conjuncts are relaxations — a wider modulus range in the fifth, a larger right-hand side in the
eleventh — so `SocketBaseL → SocketBaseLH h` for every `h ≥ 1`, and the converse fails at
`h ≥ 2`.  ⛔ **"Opposite ways" is a statement about the PROOF, not about the implication**: one
site makes the GOAL harder (more moduli must be served) and the other makes an INPUT weaker
(`cofkL_logX_floor` divides by the cap).  Both are costs, and a port that moved only one would
be pricing a different object — but neither reverses the implication.

⛔ **AND THIS IS NOT A SHORTCUT TO THE DOOR SOCKET.**  What runs backwards is at the `α`-set,
not here: `NearRatTight (h·arcDen 12 H) H α` admits STRICTLY MORE `α` than the landed cap does
(`HDoorArc.lean:423-429`), so `M4SievedDoorSqH` is a STRONGER Prop than `M4SievedDoorSq` and
`nearRatTight_mono` cannot supply it.  The two facts point opposite ways and both are true. -/
def SocketBaseLH (h : ℕ) (R : ChowlaRegime) (M H L q j A s : ℕ) : Prop :=
  R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ L ≤ H ∧ 0 < q ∧ (q : ℝ) ≤ (h : ℝ) * arcDen 12 H ∧
    j ≤ Nat.log 2 L ∧ doorRowFloorL M ≤ j ∧ 0 < A ∧ 2 ^ j ≤ A ∧ Real.sqrt (H : ℝ) ≤ (A : ℝ) ∧
    (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) ∧
    (A : ℝ) ≤ 2 * (R.x : ℝ) ∧ s ≤ L

/-- ⭐ **THE SOCKET AT `h = 1` IS THE LANDED SOCKET** (`socketBaseL_of_socketBaseLH_one`) —
the anti-drift check.  A family that did not reduce to the landed object at `h = 1` would be a
different definition wearing the same name; this is the one implication that must hold, and it
does, in both directions. -/
theorem socketBaseLH_one_iff {R : ChowlaRegime} {M H L q j A s : ℕ} :
    SocketBaseLH 1 R M H L q j A s ↔ SocketBaseL R M H L q j A s := by
  unfold SocketBaseLH SocketBaseL
  norm_num

/-- ⭐ **EVERY LANDED SOCKET IS AN INFLATED SOCKET** (`socketBaseLH_of_socketBaseL`) — the
direction that DOES hold, stated because the docstring above would otherwise be an unchecked
claim about it.  Both inflated conjuncts are relaxations, so the implication is one `nlinarith`
per site; the converse is false at `h ≥ 2` (a modulus in `(arcDen 12 H, 2·arcDen 12 H]` witnesses
it) and is deliberately not stated. -/
theorem socketBaseLH_of_socketBaseL {h : ℕ} {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hh : 0 < h) (hb : SocketBaseL R M H L q j A s) : SocketBaseLH h R M H L q j A s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hb
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hA : (0 : ℝ) ≤ arcDen 12 H := by rw [arcDen]; positivity
  have hω : (0 : ℝ) ≤ (R.ω : ℝ) := by positivity
  have hAn : (0 : ℝ) ≤ (A : ℝ) := by positivity
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8, h9, h10, ?_, h12, h13⟩
  · nlinarith
  · nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hω) hA]

set_option maxHeartbeats 1000000 in
/-- **⟦THE `log X` FLOOR AT THE INFLATED SOCKET⟧** (`cofkL_logX_floor_h`) — the `h`-family of
`RegisterSupply.cofkL_logX_floor`, and **the eleventh-conjunct half of the two-site port**.

The regime's `hPHheadroom` against the socket's inflated `x ≤ 16·ω·(h·(log H)¹²)·A` gives
`A ≥ 4^{2⌊ε²H₊⌋}/(2·h·(log H)¹²)`, so the floor loses exactly `log h`.

⭐ **⟦RULING (a)⟧ THE PIN IS THE HEAD's OWN, AND THE CONCLUSION IS `h`-EXPLICIT.**  At
`ε ≥ 1/(500·h)` the primorial exponent floor is `E ≥ H₊/(250000·h²) − 1`, so the leading term
is `H₊/(90200·h²)` and the demand must be `H₊/(10⁶·h²)`: the gap is
`H₊·(1.009·10⁻⁵)/h²` against a debit `24·√H₊ + 10.47`, i.e. **`√H₊ ≥ 2.38·10⁶·h²`**.  That is
what `hHhi : 10²⁶·h⁴ ≤ H₊` buys (`√H₊ ≥ 10¹³·h²`, margin `4.2·10⁶×`), and the road's own
`hlo : 518 ≤ loglog H₋` supplies it for free — `log H₊ ≥ 10⁸` against a cost of
`26·log 10 + 4·log h ≤ 88.1`.  `hh7` pays the `− log h`. -/
theorem cofkL_logX_floor_h {R : ChowlaRegime} {h M H L q j A s : ℕ} (hh : 0 < h)
    (hh7 : Real.log h ≤ 7)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ)) :
    (R.Hhi : ℝ) / (10 ^ 6 * (h : ℝ) ^ 2) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have h2 : H ≤ R.Hhi := hb.2.1
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have h11 : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    hb.2.2.2.2.2.2.2.2.2.2.1
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hh2 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hh1]
  have hh24 : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 4 := by nlinarith [hh2, sq_nonneg ((h : ℝ))]
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by nlinarith [hHhi, hh2, hh24]
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hω0 : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  -- ⟦the arc denominator, inflated⟧
  have harc : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos hlogH0 12
  have harcH : (0 : ℝ) < (h : ℝ) * arcDen 12 H := by positivity
  have hlogarc : Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) :=
    log_arcDen_twelve hlogH0
  -- ⟦the primorial majorant⟧
  set E : ℕ := ⌊R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)⌋₊ with hEdef
  have hPH0 : 8 * (((4 ^ E : ℕ) : ℝ)) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := R.hPHheadroom
  have hW : (((4 ^ E : ℕ) : ℝ)) = (4 : ℝ) ^ E := by push_cast; ring
  rw [hW] at hPH0
  -- ⟦the combination, `ω` cancelled⟧
  have hmul : (8 * ((4 : ℝ) ^ E) ^ 2) * (R.ω : ℝ)
      ≤ (16 * ((h : ℝ) * arcDen 12 H) * (A : ℝ)) * (R.ω : ℝ) := by
    have := le_trans hPH0 h11; linarith
  have h8w : 8 * ((4 : ℝ) ^ E) ^ 2 ≤ 16 * ((h : ℝ) * arcDen 12 H) * (A : ℝ) :=
    le_of_mul_le_mul_right hmul hω0
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast h8
  have hkey : ((4 : ℝ) ^ E) ^ 2 / (2 * ((h : ℝ) * arcDen 12 H)) ≤ (A : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- ⟦the logarithm of the floor: the inflation is exactly a `− log h`⟧
  have hlogW : Real.log (((4 : ℝ) ^ E) ^ 2) = 2 * (E : ℝ) * Real.log 4 := by
    rw [← pow_mul, Real.log_pow]
    push_cast; ring
  have harc2 : (0 : ℝ) < 2 * ((h : ℝ) * arcDen 12 H) := by linarith
  have hW2pos : (0 : ℝ) < ((4 : ℝ) ^ E) ^ 2 := by positivity
  have heq : Real.log (((4 : ℝ) ^ E) ^ 2 / (2 * ((h : ℝ) * arcDen 12 H)))
      = 2 * (E : ℝ) * Real.log 4 - Real.log 2 - Real.log h
        - 12 * Real.log (Real.log (H : ℝ)) := by
    rw [Real.log_div (ne_of_gt hW2pos) (ne_of_gt harc2), hlogW,
      Real.log_mul (by norm_num) (ne_of_gt harcH),
      Real.log_mul (ne_of_gt hh0) (ne_of_gt harc), hlogarc]
    ring
  have hlogA : 2 * (E : ℝ) * Real.log 4 - Real.log 2 - Real.log h
      - 12 * Real.log (Real.log (H : ℝ)) ≤ Real.log (A : ℝ) := by
    have hle : Real.log (((4 : ℝ) ^ E) ^ 2 / (2 * ((h : ℝ) * arcDen 12 H)))
        ≤ Real.log (A : ℝ) := Real.log_le_log (div_pos hW2pos harc2) hkey
    rw [heq] at hle
    exact hle
  -- ⟦the floor of the primorial exponent⟧
  have hEfl : (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) - 1 ≤ (E : ℝ) := by
    have hq : (R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ)) < (E : ℚ) + 1 := by
      rw [hEdef]; exact Nat.lt_floor_add_one _
    have hR : ((R.eps ^ 2 * ((R.Hhi : ℕ) : ℚ) : ℚ) : ℝ) < ((E : ℚ) : ℝ) + 1 := by
      exact_mod_cast hq
    push_cast at hR
    linarith
  -- ⟦⟦(a)⟧⟧ THE `ε` FLOOR AT THE SHIFTED PIN: `1/(500h) ≤ ε` gives `250000·h²·ε² ≥ 1`
  have hεh : (1 : ℝ) ≤ 500 * (h : ℝ) * (R.eps : ℝ) := by
    have h500 : (0 : ℝ) < 500 * (h : ℝ) := by linarith
    rw [div_le_iff₀ h500] at hε
    linarith
  have heps2 : (1 : ℝ) ≤ 250000 * (h : ℝ) ^ 2 * (R.eps : ℝ) ^ 2 := by nlinarith [hεh]
  have hepsH : (R.Hhi : ℝ) ≤ 250000 * (h : ℝ) ^ 2 * ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ)) := by
    nlinarith [heps2, hHhi0]
  have hEbig : (R.Hhi : ℝ) ≤ 250000 * (h : ℝ) ^ 2 * ((E : ℝ) + 1) := by
    have hstep : 250000 * (h : ℝ) ^ 2 * ((R.eps : ℝ) ^ 2 * (R.Hhi : ℝ))
        ≤ 250000 * (h : ℝ) ^ 2 * ((E : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hEfl]) (by positivity)
    linarith [hepsH, hstep]
  have hE0 : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg _
  -- ⟦the two crude brackets on `H₊`⟧
  have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hlogmono : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := Real.log_le_log hH0 hHle
  have hllmono : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (R.Hhi : ℝ)) :=
    Real.log_le_log hlogH0 hlogmono
  have hllsub : Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (R.Hhi : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hsq : Real.log (R.Hhi : ℝ) ≤ 2 * Real.sqrt (R.Hhi : ℝ) - 2 :=
    cofk_log_le_two_sqrt hHhi0
  -- ⟦⟦(a)⟧⟧ the square-root floor is now `h`-EXPLICIT: `√H₊ ≥ 10^13·h²`
  have hv : (10 : ℝ) ^ 13 * (h : ℝ) ^ 2 ≤ Real.sqrt (R.Hhi : ℝ) := by
    have hid : ((10 : ℝ) ^ 13 * (h : ℝ) ^ 2) ^ 2 = (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 := by ring
    have h1 : Real.sqrt (((10 : ℝ) ^ 13 * (h : ℝ) ^ 2) ^ 2) ≤ Real.sqrt (R.Hhi : ℝ) :=
      Real.sqrt_le_sqrt (by rw [hid]; exact hHhi)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hvsq : Real.sqrt (R.Hhi : ℝ) * Real.sqrt (R.Hhi : ℝ) = (R.Hhi : ℝ) :=
    Real.mul_self_sqrt hHhi0.le
  have hv0 : (0 : ℝ) ≤ Real.sqrt (R.Hhi : ℝ) := Real.sqrt_nonneg _
  have hprod : (10 : ℝ) ^ 13 * (h : ℝ) ^ 2 * Real.sqrt (R.Hhi : ℝ) ≤ (R.Hhi : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hv hv0) (le_of_eq hvsq)
  -- ⟦the numeral: `log A ≥ H₊/(10⁶h²)`, paying `log h ≤ 7` as well⟧
  have hlog4 : (1.3862 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9]
  have hlog2 : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
  have hElog : (1.3862 : ℝ) * (E : ℝ) ≤ (E : ℝ) * Real.log 4 := by
    have h := mul_le_mul_of_nonneg_left hlog4 hE0
    linarith only [h]
  have hdebit : 12 * Real.log (Real.log (H : ℝ)) ≤ 24 * Real.sqrt (R.Hhi : ℝ) := by
    linarith only [hllmono, hllsub, hsq]
  have hlow : 2.7724 * (E : ℝ) - 7.6932 - 24 * Real.sqrt (R.Hhi : ℝ) ≤ Real.log (A : ℝ) := by
    linarith only [hElog, hlogA, hdebit, hlog2, hh7]
  have hXpos : (0 : ℝ) < 10 ^ 6 * (h : ℝ) ^ 2 := by positivity
  have hmulL : (10 ^ 6 * (h : ℝ) ^ 2)
        * (2.7724 * (E : ℝ) - 7.6932 - 24 * Real.sqrt (R.Hhi : ℝ))
      ≤ (10 ^ 6 * (h : ℝ) ^ 2) * Real.log (A : ℝ) :=
    mul_le_mul_of_nonneg_left hlow hXpos.le
  have hsm1 : 10 ^ 6 * (h : ℝ) ^ 2 * 7.6932 ≤ (R.Hhi : ℝ) := by
    linarith only [hHhi, hh24]
  have hhs : (0 : ℝ) ≤ (h : ℝ) ^ 2 * Real.sqrt (R.Hhi : ℝ) := by positivity
  have hsm2 : 24 * (10 ^ 6 * ((h : ℝ) ^ 2 * Real.sqrt (R.Hhi : ℝ))) ≤ (R.Hhi : ℝ) := by
    nlinarith only [hprod, hhs]
  have hfloor : (R.Hhi : ℝ) / (10 ^ 6 * (h : ℝ) ^ 2) ≤ Real.log (A : ℝ) := by
    rw [div_le_iff₀ hXpos]
    nlinarith only [hmulL, hEbig, hsm1, hsm2]
  -- ⟦the exit⟧
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast h8
  have hAs : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hlogAs : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    Real.log_le_log (by linarith) hAs
  linarith

/-- **⟦THE `μ`-FLOOR AT THE INFLATED SOCKET⟧** (`cofkL_mu_floor_h`) —
`loglog(A+s) ≥ log H₊ − 28`, the `h`-family of `RegisterSupply.cofkL_mu_floor`.  Reads the cap
only through §6's floor.

⭐ **THIS IS WHERE RULING (a)'s COST LANDS, AND IT IS THE ONLY PLACE IT LANDS.**  The landed
`− 14` is `log(10⁶) ≤ 13.82`; at the `h`-explicit floor the subtraction is
`log(10⁶·h²) = 6·log 10 + 2·log h ≤ 13.87 + 14 = 27.87`.  Every consumer of this floor on the
road has `10²¹`-scale slack for the extra 14 — and the cushion
`32·Kvt + 32·D ≤ log H₊/4` never sees it at all, because it is an ANTECEDENT carried to the
capstones. -/
theorem cofkL_mu_floor_h {R : ChowlaRegime} {h M H L q j A s : ℕ} (hh : 0 < h)
    (hh7 : Real.log h ≤ 7)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ)) :
    Real.log (R.Hhi : ℝ) - 28 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hLh0 : (0 : ℝ) ≤ Real.log h := Real.log_nonneg hh1
  have hh2 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hh1]
  have hh24 : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 4 := by nlinarith [hh2, sq_nonneg ((h : ℝ))]
  have hfl := cofkL_logX_floor_h hh hh7 hb hε hHhi hH
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by nlinarith [hHhi, hh2, hh24]
  have hXpos : (0 : ℝ) < (10 : ℝ) ^ 6 * (h : ℝ) ^ 2 := by positivity
  have hbigpos : (0 : ℝ) < (R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := div_pos hHhi0 hXpos
  have hstep : Real.log ((R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2))
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    Real.log_le_log hbigpos hfl
  have hsplit : Real.log ((R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2))
      = Real.log (R.Hhi : ℝ) - Real.log ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := by
    rw [Real.log_div (ne_of_gt hHhi0) (ne_of_gt hXpos)]
  have h106 : Real.log ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) ≤ 28 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    linarith [cofk_log_ten_le, hh7, hLh0]
  rw [hsplit] at hstep
  linarith

/-- The inflated socket's scale still clears the supplier's own gate `e^e ≤ X`
(`cofkL_X_ge_expexp_h`). -/
theorem cofkL_X_ge_expexp_h {R : ChowlaRegime} {h M H L q j A s : ℕ} (hh : 0 < h)
    (hh7 : Real.log h ≤ 7)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hHhi : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ))
    (hH : (4000000 : ℝ) ≤ (H : ℝ)) :
    Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hh2 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith [hh1]
  have hh24 : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 4 := by nlinarith [hh2, sq_nonneg ((h : ℝ))]
  have hfl := cofkL_logX_floor_h hh hh7 hb hε hHhi hH
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have hApos : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    have h : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by exact_mod_cast this
    linarith
  have hXpos : (0 : ℝ) < (10 : ℝ) ^ 6 * (h : ℝ) ^ 2 := by positivity
  have he : Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have h4 : (3 : ℝ) ≤ (R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := by
      rw [le_div_iff₀ hXpos]; nlinarith [hHhi, hh24]
    linarith
  have h := Real.exp_le_exp.mpr he
  rwa [Real.exp_log hApos] at h

/-! ## §7 — the fifth-conjunct half at the socket: the scale gate and the threshold -/

set_option maxHeartbeats 1000000 in
/-- **⟦THE SCALE GATE AT THE INFLATED SOCKET⟧** (`cofkL_scale_gate_at_socket_h`) — the
`h`-family of `BandRatedSocket.cofkL_scale_gate_at_socket`.

The gate's whole content is that two logarithms are far apart: `log(1900·q⁵)` is now
`≤ 1899 + 5·log h + 60·loglog H` against `loglog X ≥ log H₊ − 28 ≥ 10⁴·√(log H₊) − 28`.  The
`5·log h ≤ 35` the inflation adds is invisible at that scale, and so is ruling (a)'s further
`− 14`; both are CARRIED, not waved. -/
theorem cofkL_scale_gate_at_socket_h {R : ChowlaRegime} {h M H L q j A s : ℕ} [NeZero q]
    (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hlo : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (harc : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H) :
    32 * diskConst q / goldenL1 q ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHlo0 : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  have hlogH : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hHlo0 hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ) := by
    have hLhh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hlogle : Real.log ((10 : ℝ) ^ 26 * (h : ℝ) ^ 4) ≤ Real.log (R.Hhi : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8, hh7]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  have hHe : Real.exp 1 ≤ Real.log (H : ℝ) := by
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  -- ⟦the `μ`-floor and the scale floor, at the INFLATED socket⟧
  have hmu := cofkL_mu_floor_h hh hh7 hb hε hHhi14 hH4
  have hfl := cofkL_logX_floor_h hh hh7 hb hε hHhi14 hH4
  have hlogXpos : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have hbig : (0 : ℝ) < (R.Hhi : ℝ) / ((10 : ℝ) ^ 6 * (h : ℝ) ^ 2) := by positivity
    linarith
  -- ⟦`loglog H` against `√(log H₊)`⟧
  have hLH0 : (0 : ℝ) < Real.log (R.Hhi : ℝ) := by linarith
  have hΛ : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log (R.Hhi : ℝ)) :=
    Real.log_le_log (by linarith) hlogHhi
  have hlogLH : Real.log (Real.log (R.Hhi : ℝ)) ≤ 2 * Real.sqrt (Real.log (R.Hhi : ℝ)) - 2 :=
    cofk_log_le_two_sqrt hLH0
  have hv : (10 : ℝ) ^ 4 ≤ Real.sqrt (Real.log (R.Hhi : ℝ)) := by
    have h1' : Real.sqrt (((10 : ℝ) ^ 4) ^ 2) ≤ Real.sqrt (Real.log (R.Hhi : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h1'
  have hv0 : (0 : ℝ) ≤ Real.sqrt (Real.log (R.Hhi : ℝ)) := Real.sqrt_nonneg _
  have hvsq : Real.sqrt (Real.log (R.Hhi : ℝ)) * Real.sqrt (Real.log (R.Hhi : ℝ))
      = Real.log (R.Hhi : ℝ) := Real.mul_self_sqrt hLH0.le
  have hprodv : (10 : ℝ) ^ 4 * Real.sqrt (Real.log (R.Hhi : ℝ)) ≤ Real.log (R.Hhi : ℝ) := by
    nlinarith [hv, hvsq, hv0]
  -- ⟦the quintic, and its logarithm — the inflation adds `5·log h`⟧
  have hlogq : Real.log q ≤ Real.log h + 12 * Real.log (Real.log (H : ℝ)) :=
    log_le_of_le_arcDen_h hh hHe harc
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
  have hqpos : (0 : ℝ) < 1900 * (q : ℝ) ^ 5 := by positivity
  have hlogpoly : Real.log (1900 * (q : ℝ) ^ 5) = Real.log 1900 + 5 * Real.log q := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlog1900 : Real.log 1900 ≤ 1899 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1900 by norm_num)
    linarith
  have hchain : Real.log (1900 * (q : ℝ) ^ 5)
      ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    rw [hlogpoly]; linarith
  have hfin : 1900 * (q : ℝ) ^ 5 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h := Real.exp_le_exp.mpr hchain
    rwa [Real.exp_log hqpos, Real.exp_log hlogXpos] at h
  exact le_trans scaleGate_le_quintic hfin

set_option maxHeartbeats 1000000 in
/-- **⟦THE THRESHOLD AT THE INFLATED SOCKET, RATED⟧** (`cofkL_threshold_at_socket_rated_h`) —
the `h`-family of `BandRatedSocket.cofkL_threshold_at_socket_rated`.

⭐ **THE NUMERALS DO NOT MOVE AND THE CUSHION DOES NOT MOVE.**  This page never reads the fifth
conjunct at all — its `H`-side legs are `loglog H` against `√(log H₊)` — so the only route by
which `h` could reach it is the `μ`-floor, i.e. the ELEVENTH conjunct, and §6 has already shown
that costs `log h` against a floor linear in `H₊`.  The statement is byte-identical to the
landed one apart from the socket it reads and the `ε`-floor's `h` (block E).

⭐ **AND RULING (a)'s EXTRA 14 IS INVISIBLE HERE, MEASURED.**  The μ-floor now reads
`LH − 28`; the close is `hmargin : 4280·√LH + 2420 + LH/4 < μ/2 + μ/4`, whose slack is
`≥ 720·√LH − 2430 ≥ 7.2·10⁶` against a cost of `3·28/4 = 21`. -/
theorem cofkL_threshold_at_socket_rated_h {R : ChowlaRegime} {h M H L q j A s : ℕ}
    {Kvt D : ℝ} (hh : 0 < h) (hh7 : Real.log h ≤ 7)
    (hb : SocketBaseLH h R M H L q j A s)
    (hε : (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ))
    (hlo : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)))
    (hcush : 32 * Kvt + 32 * D ≤ Real.log (R.Hhi : ℝ) / 4) :
    40 * Real.log (Real.log (Real.log (((A + s : ℕ)) : ℝ)))
        + 1900 * Real.log (Real.log (H : ℝ))
        + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        + 2300 + 32 * Kvt + 32 * D
      < Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hHlo0 : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  have hlogH : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hHlo0 hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hlogH1 : (1 : ℝ) < Real.log (H : ℝ) := by linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ) := by
    have hLhh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hlogle : Real.log ((10 : ℝ) ^ 26 * (h : ℝ) ^ 4) ≤ Real.log (R.Hhi : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8, hh7]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  -- ⟦THE `μ`-FLOOR, at the INFLATED socket⟧
  have hmu := cofkL_mu_floor_h hh hh7 hb hε hHhi14 hH4
  set μ : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hμdef
  set LH : ℝ := Real.log (R.Hhi : ℝ) with hLHdef
  have hμ : LH - 28 ≤ μ := hmu
  have hμbig : (10 : ℝ) ^ 8 - 28 ≤ μ := by linarith
  have hμ0 : (0 : ℝ) < μ := by nlinarith
  -- ⟦the `logloglog` leg⟧ `40·log μ ≤ μ/4`
  have hlogμ : Real.log μ ≤ 2 * Real.sqrt μ - 2 := cofk_log_le_two_sqrt hμ0
  have hsμ : (320 : ℝ) ≤ Real.sqrt μ := by
    have h1' : Real.sqrt ((320 : ℝ) ^ 2) ≤ Real.sqrt μ := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h1'
  have hsμ0 : (0 : ℝ) ≤ Real.sqrt μ := Real.sqrt_nonneg _
  have hsμsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ0.le
  have hprodμ : 320 * Real.sqrt μ ≤ μ := by nlinarith [hsμ, hsμsq, hsμ0]
  have hleg1 : 40 * Real.log μ ≤ μ / 4 := by linarith
  -- ⟦the `loglog H` legs⟧ dominated by `4280·√(log H₊)`
  have hΛ : Real.log (Real.log (H : ℝ)) ≤ Real.log LH :=
    Real.log_le_log (by linarith) hlogHhi
  have hLH0 : (0 : ℝ) < LH := by linarith
  have hlogLH : Real.log LH ≤ 2 * Real.sqrt LH - 2 := cofk_log_le_two_sqrt hLH0
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := Real.log_nonneg (by linarith)
  have hv : (10 : ℝ) ^ 4 ≤ Real.sqrt LH := by
    have h1' : Real.sqrt (((10 : ℝ) ^ 4) ^ 2) ≤ Real.sqrt LH := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num)] at h1'
  have hv0 : (0 : ℝ) ≤ Real.sqrt LH := Real.sqrt_nonneg _
  have hvsq : Real.sqrt LH * Real.sqrt LH = LH := Real.mul_self_sqrt hLH0.le
  have hprodv : (10 : ℝ) ^ 4 * Real.sqrt LH ≤ LH := by nlinarith [hv, hvsq, hv0]
  have hlogterm : Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
      ≤ 6 + 24 * Real.sqrt LH := by
    have hpos : (0 : ℝ) < 7 + 12 * Real.log (Real.log (H : ℝ)) := by linarith
    have hsub : Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        ≤ 7 + 12 * Real.log (Real.log (H : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos hpos
    linarith
  have hleg2 : 1900 * Real.log (Real.log (H : ℝ))
      + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 2300
      ≤ 4280 * Real.sqrt LH + 2420 := by linarith
  -- ⟦the close⟧
  have hmargin : 4280 * Real.sqrt LH + 2420 + LH / 4 < μ / 2 + μ / 4 := by
    nlinarith [hprodv, hv, hμ, hv0]
  linarith

/-! ## §8 — the exit at the inflated socket, and where the tight margin goes

⭐⭐ **THE ×1.09 MARGIN NEVER BINDS HERE, AND THE REASON IS NOT AN ESCAPE.**  §4's budget is
tight because the threshold page is stated at ITS OWN floor `Λ ≥ 1` — the weakest floor in the
corpus.  The socket carries `hlo : 518 ≤ loglog H₋` **in its own landed binder list**, and
`H₋ ≤ H`, so at every application site `Λ ≥ 518` and the budget clears by four orders of
magnitude.

⛔ **THIS IS NOT ESCAPE 2, AND THE DIFFERENCE IS THE WHOLE POINT.**  Escape 2 was *threading the
socket's `Λ`-floor into the threshold page* — that ADDS A HYPOTHESIS to a page that does not
have one, and the commission forbids it without a flag.  Here the hypothesis is ALREADY IN THE
LANDED STATEMENT; discharging `hbud` from it adds nothing and changes no binder.  ⇒ the tight
margin is a property of the PAGE stated in isolation, not of the program.

The binding constraint at the socket is therefore `hh7 : log h ≤ 7` (`h ≤ 1096`), which comes
from the `mertensCap` row's absorption in §4 and the `log X` floor's subtraction in §6 — not
from the `Λ`-budget at all. -/

set_option maxHeartbeats 1000000 in
/-- **⟦THE RATED SOCKET AT THE INFLATED CAP, `K`-UNIFORM⟧**
(`cofkL_capFreeFloor_at_socket_rated_uniform_h`) — the `h`-family of
`V7Rated.cofkL_capFreeFloor_at_socket_rated_uniform`, and the wave's exit.

**Binder-for-binder the landed name, with `SocketBaseL` replaced by `SocketBaseLH h`, the two
hypotheses `0 < h`, `log h ≤ 7` added on the `h` itself, and — since wave H3 block E — the
`ε`-floor spelled at the `h` head's own pin `1/(500·h)` rather than the flat `1/500`.**
Nothing about the regime, the cushion or the `Λ`-floor moves, and the `Kvt` it exports is the
same kind of object: one symbolic nonnegative real, chosen before `R`, `H` and `q` are bound.

⭐ **THAT LAST FACT IS WHY THE CAP CANNOT REACH THE `Kvt` CUSHION ON THE RATED LANE** — the
three witnesses are hoisted above every binder the inflation touches, so no instantiation of
the cap can move them.  It is the structural fact the 08/31 measurement reported, now carried
by an `h`-family statement rather than read off the landed one. -/
theorem cofkL_capFreeFloor_at_socket_rated_uniform_h (h : ℕ) (hh : 0 < h)
    (hh7 : Real.log h ≤ 7) :
    ∃ Z δ Kvt : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ Kvt ∧
      ∀ (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (χ : DirichletCharacter ℂ q),
        SocketBaseLH h R M H L q j A s → 1 ≤ M →
        (1 : ℝ) / (500 * (h : ℝ)) ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) := by
  obtain ⟨Z, δ, Kvt, hZ, hδ, hK0, hK⟩ := capFreeFloor3_pieceDatum_arcDen_rated_h h hh hh7
  refine ⟨Z, δ, Kvt, hZ, hδ, hK0, ?_⟩
  intro K R M H L q j A s χ hb hM hε hlo hcush 𝒥 h𝒥
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have harc : (q : ℝ) ≤ (h : ℝ) * arcDen 12 H := hb.2.2.2.2.1
  -- ⟦the design floor⟧
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH4
  have hlogHe : Real.exp 1 ≤ Real.log (H : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  -- ⟦`H₊ ≥ 10^14`⟧
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hlogHlo8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hlo : ℝ) := by linarith
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by linarith) hHloH
  have hlogHhi : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) hHHhi
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 26 * (h : ℝ) ^ 4 ≤ (R.Hhi : ℝ) := by
    have hLhh : (0 : ℝ) ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hlogle : Real.log ((10 : ℝ) ^ 26 * (h : ℝ) ^ 4) ≤ Real.log (R.Hhi : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8, hh7]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  -- ⟦THE BUDGET, DISCHARGED FROM THE SOCKET'S OWN `Λ`-FLOOR — no binder added⟧
  have hΛ518 : (518 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by
    have hmono : Real.log (Real.log (R.Hlo : ℝ)) ≤ Real.log (Real.log (H : ℝ)) :=
      Real.log_le_log (by linarith) hlogmono
    linarith
  have hlognn : (0 : ℝ) ≤ Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) :=
    Real.log_nonneg (by linarith)
  have hbud : 156 * Real.log h + 8 * Real.log 2
      ≤ 28 * Real.log (Real.log (H : ℝ))
        + 4 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) + 84 := by
    have h2lt := Real.log_two_lt_d9
    linarith
  -- ⟦the scale gate, the debit page, the threshold — all at the INFLATED socket⟧
  have hXee : Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) :=
    cofkL_X_ge_expexp_h hh hh7 hb hε hHhi14 hH4
  have hgate : 32 * diskConst q / goldenL1 q ≤ Real.log (((A + s : ℕ)) : ℝ) :=
    cofkL_scale_gate_at_socket_h hh hh7 hb hε hlo harc
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hD0 : (0 : ℝ) ≤ 2 * Real.log (M : ℝ) + Real.log 4 + 50 := by
    have h1' : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
    have h2' : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hdebit := cofkL_debit_bound K M (((A + s : ℕ)) : ℝ) hM 𝒥 h𝒥
  have hthr := cofkL_threshold_at_socket_rated_h (Kvt := Kvt)
    (D := 2 * Real.log (M : ℝ) + Real.log 4 + 50) hh hh7 hb hε hlo hcush
  exact hK q H χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
    (((A + s : ℕ)) : ℝ) (2 * Real.log (M : ℝ) + Real.log 4 + 50)
    hlogHe harc hbud hXee hD0 hgate hdebit hthr

/-- ⭐ **THE EXIT AT `h = 2`** (`cofkL_capFreeFloor_at_socket_rated_uniform_two`) — the
commissioned lane, with the two `h`-hypotheses discharged by `norm_num`-level arithmetic. -/
theorem cofkL_capFreeFloor_at_socket_rated_uniform_two :
    ∃ Z δ Kvt : ℝ, 1 ≤ Z ∧ 0 < δ ∧ 0 ≤ Kvt ∧
      ∀ (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} (χ : DirichletCharacter ℂ q),
        SocketBaseLH 2 R M H L q j A s → 1 ≤ M →
        (1 : ℝ) / 1000 ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) := by
  obtain ⟨Z, δ, Kvt, hZ, hδ, hK0, hK⟩ :=
    cofkL_capFreeFloor_at_socket_rated_uniform_h 2 (by norm_num)
      (by
        have hcast : (((2 : ℕ) : ℝ)) = (2 : ℝ) := by norm_num
        rw [hcast]
        linarith [Real.log_two_lt_d9])
  refine ⟨Z, δ, Kvt, hZ, hδ, hK0, ?_⟩
  intro K R M H L q j A s χ hb hM hε hlo hcush 𝒥 h𝒥
  refine hK K χ hb hM ?_ hlo hcush 𝒥 h𝒥
  have hcast : (500 : ℝ) * (((2 : ℕ) : ℝ)) = 1000 := by norm_num
  rw [hcast]
  exact hε

/-! ## §9 — THE DOOR SIDE: the sup socket and its bridge at the inflated cap

§1–§8 built the CO-FACTOR supply at `h·arcDen 12 H`.  This section walks the other consumer of
the same cap — the door's own mean-square chain
`M4BlockMeanSqSupQ → M4SievedDoorSqSup → M4SievedDoorSq` — to its `h`-family, so that
`HDoorArc.M4SievedDoorSqH`'s open slot moves DOWN one level, from the sieved door square to the
per-block mean square at the inflated modulus range.

⛔ **THE DRIFT LEMMA HAD TO BE GENERALISED, AND THAT IS A FACT ABOUT THE STATEMENT, NOT THE
PROOF.**  `M4Abel.norm_phase_sum_arcDen_drift` and its two feeders are stated with the LITERAL
`arcDen B₅ H` in both the hypothesis and the conclusion, and `h·arcDen 12 H` is not `arcDen B₅ H`
for any `B₅`.  Their proofs, however, never read the cap as anything but an opaque real — so
§9.1 restates the three at a free cap `Q` and the landed proofs run verbatim.  ⭐ *The pin was in
the SPELLING, not in the mathematics; nothing here re-derives an estimate.*

⭐ **AND ONE THING NEEDED NO PORT AT ALL:** `M4BridgePhase.qgraded_drift_price_le` is stated with
a FREE `A` under `(q : ℝ) ≤ A`, so `A := h·arcDen 12 H` instantiates it VERBATIM.  The
commission's worry that the drift factor "is never re-chosen" is answered by the landed bytes. -/

/-! ### §9.1 — the Abel drift at a FREE cap -/

/-- The drift factor at a free cap: `|θ| ≤ Q/(q·H)` and a window of length `≤ H` give
`|θ|·(N − M) ≤ Q/q`.  `M4Abel.abs_mul_window_le_of_arcDen` with `arcDen B₅ H` freed to `Q`. -/
theorem abs_mul_window_le_of_cap {Q : ℝ} {H q M N : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hlen : N - M ≤ H) {θ : ℝ} (hθ : |θ| ≤ Q / ((q : ℝ) * (H : ℝ))) :
    |θ| * ((N - M : ℕ) : ℝ) ≤ Q / (q : ℝ) := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlenR : ((N - M : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlen
  have h1 : |θ| * ((N - M : ℕ) : ℝ) ≤ |θ| * (H : ℝ) :=
    mul_le_mul_of_nonneg_left hlenR (abs_nonneg θ)
  have h2 : |θ| * (H : ℝ) ≤ Q / ((q : ℝ) * (H : ℝ)) * (H : ℝ) :=
    mul_le_mul_of_nonneg_right hθ hHR.le
  have h3 : Q / ((q : ℝ) * (H : ℝ)) * (H : ℝ) = Q / (q : ℝ) := by
    field_simp
  linarith

/-- **THE M4-0′ PAYLOAD AT A FREE CAP** (`norm_phase_sum_cap_drift`) —
`M4Abel.norm_phase_sum_arcDen_drift` with the cap freed.  Same proof. -/
theorem norm_phase_sum_cap_drift {Q : ℝ} {H q M N : ℕ} (hMN : M ≤ N) (hq : 0 < q)
    (hH : 0 < H) (hlen : N - M ≤ H) {θ : ℝ}
    (hθ : |θ| ≤ Q / ((q : ℝ) * (H : ℝ))) {A : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hpart : ∀ K, M ≤ K → K ≤ N → ‖∑ m ∈ Finset.Ioc M K, A m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc M N, eR (θ * (m : ℝ)) * A m‖
      ≤ (1 + 2 * Real.pi * (Q / (q : ℝ))) * B := by
  refine le_trans (norm_phase_sum_Ioc_drift hMN θ hpart) ?_
  refine mul_le_mul_of_nonneg_right ?_ hB
  have hstep := abs_mul_window_le_of_cap (Q := Q) hq hH hlen hθ
  have heq : 2 * Real.pi * |θ| * ((N - M : ℕ) : ℝ)
      = 2 * Real.pi * (|θ| * ((N - M : ℕ) : ℝ)) := by ring
  rw [heq]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  linarith [mul_le_mul_of_nonneg_left hstep hpi]

/-- **THE WINDOW DRIFT AT A FREE CAP** (`norm_absWindowSum_le_drift_cap`) —
`M4BridgePhase.norm_absWindowSum_le_drift` with the cap freed.  Same proof. -/
theorem norm_absWindowSum_le_drift_cap {Q : ℝ} {H q n : ℕ} (hq : 0 < q) (hH : 0 < H)
    {β θ : ℝ} (hθ : |θ| ≤ Q / ((q : ℝ) * (H : ℝ))) (a : ℕ → ℂ) :
    ‖absWindowSum a H n (β + θ)‖
      ≤ (1 + 2 * Real.pi * (Q / (q : ℝ))) * subWindowSup a H n β := by
  rw [absWindowSum_add_eq_phase_sum]
  refine norm_phase_sum_cap_drift (M := n) (N := n + H) (A := phaseCoeff a β)
    (B := subWindowSup a H n β) (Nat.le_add_right n H) hq hH (by omega) hθ
    (subWindowSup_nonneg a H n β) ?_
  intro K h1 h2
  rw [sum_Ioc_phaseCoeff_eq_sub a β h1]
  exact le_subWindowSup a H n β (by omega)

/-! ### §9.2 — the sup socket at the inflated cap, and the bridge onto `M4SievedDoorSqH` -/

/-- **THE SUB-WINDOW-UNIFORM SOCKET AT THE INFLATED CAP** (`M4SievedDoorSqSupH`) —
`M4BridgePhase.M4SievedDoorSqSup` with its modulus range inflated to `q ≤ h·arcDen 12 H` and
NOTHING else changed: same integrand, same measure, same `q`-graded right-hand side. -/
def M4SievedDoorSqSupH (h : ℕ) (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
        (∫ n, (subWindowSup (memSCoeff (calP (Adoor M) (3072 * M))
              (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n ((b : ℝ) / (q : ℝ))) ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2

/-- **THE BRIDGE AT THE INFLATED CAP** (`m4_sievedDoorSqH_of_supH`) — the `h`-family of
`M4BridgePhase.m4_sievedDoorSq_of_sup`, and **the first producer `HDoorArc.M4SievedDoorSqH` has
ever had.**

The proof is the landed one with `arcDen 12 H` read as `h·arcDen 12 H` throughout: the
`NearRatTight` witness now arrives with `q ≤ h·arcDen 12 H` and radius
`|α − b/q| ≤ (h·arcDen 12 H)/(qH)`, and §9.1's free-cap drift takes it. -/
theorem m4_sievedDoorSqH_of_supH {h : ℕ} {R : ChowlaRegime} {M : ℕ} {Braw Braw' : ℕ → ℝ}
    (hgrade : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      (1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * Braw' H)
        ≤ Braw H)
    (hsup : M4SievedDoorSqSupH h R M Braw') : M4SievedDoorSqH h R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  set c := memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC
    with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  -- ⟦the pointwise drift bound, squared, at the INFLATED cap⟧
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ))) ^ 2
          * (subWindowSup c H n β) ^ 2 := by
    intro n
    -- ⚠️ NOT named `h`: the shift is `h`, and shadowing it here silently retypes every
    -- `(h : ℝ)` below the `have`.
    have hdr := norm_absWindowSum_le_drift_cap (Q := (h : ℝ) * arcDen 12 H) (H := H) (q := q)
      (n := n) (β := β) (θ := α - β) hq hH hd c
    have he : β + (α - β) = α := by ring
    rw [he] at hdr
    calc ‖absWindowSum c H n α‖ ^ 2
        ≤ ((1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ)))
            * subWindowSup c H n β) ^ 2 := by gcongr
      _ = (1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ))) ^ 2
            * (subWindowSup c H n β) ^ 2 := by ring
  -- ⟦the integral, and the grade⟧
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ))) ^ 2
          * (subWindowSup c H n β) ^ 2 ∂(logMeasure R.x R.ω) := integral_logMeasure_mono hpt
    _ = (1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ))) ^ 2
          * ∫ n, (subWindowSup c H n β) ^ 2 ∂(logMeasure R.x R.ω) :=
        integral_logMeasure_const_mul _ _
    _ ≤ (1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ))) ^ 2
          * (Braw' H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsup htr H hlo hhi b q hq hqQ) (sq_nonneg _)
    _ = ((1 + 2 * Real.pi * ((h : ℝ) * arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * Braw' H))
          * (H : ℝ) ^ 2 := by ring
    _ ≤ Braw H * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (hgrade H q hlo hhi hq hqQ) (sq_nonneg _)

/-- ⭐ **THE `q`-FREE READING AT THE INFLATED CAP** (`m4_sievedDoorSqH_of_supH_uniform`) — and
**this is the node that needed no port.**

`M4BridgePhase.qgraded_drift_price_le` is stated with a FREE `A` under `(q : ℝ) ≤ A`, so
`A := h·arcDen 12 H` instantiates it VERBATIM — the `q` cancels the drift's `1/q` exactly as it
does at the landed cap, and the absolute price is `(1 + 2π)²·(h·arcDen 12 H)²`, i.e. the landed
price times `h²`.  That `h²` is the honest cost of the inflation on this arm, inside a
`(log H)^{24}` vs `(log H)^{−30}` gap. -/
theorem m4_sievedDoorSqH_of_supH_uniform {h : ℕ} {R : ChowlaRegime} {M : ℕ}
    {Braw Braw' : ℕ → ℝ} (hB0 : ∀ H : ℕ, 0 ≤ Braw' H)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (1 + 2 * Real.pi) ^ 2 * (((h : ℝ) * arcDen 12 H) ^ 2 * Braw' H) ≤ Braw H)
    (hsup : M4SievedDoorSqSupH h R M Braw') : M4SievedDoorSqH h R M Braw :=
  m4_sievedDoorSqH_of_supH
    (fun H _q hlo hhi hq hqQ =>
      le_trans (qgraded_drift_price_le hq hqQ (hB0 H)) (hgrade H hlo hhi)) hsup

/-- **THE INFLATED SUP SOCKET IS INHABITED** (`m4_sievedDoorSqSupH_trivial`) — the anti-vacuity
duty, discharged for the new socket at the same time it is introduced, exactly as
`HDoorArc.m4_sievedDoorSqH_trivial` was for `M4SievedDoorSqH`.

⛔ **THIS IS OWED AND IT IS NOT CEREMONY.**  `m4_sievedDoorSqH_of_supH` takes this Prop as a
HYPOTHESIS, and the kernel cannot check that a hypothesis is inhabited: an uninhabited sup
socket would make the bridge vacuously usable, with a green build and a clean axiom audit. -/
theorem m4_sievedDoorSqSupH_trivial (h : ℕ) (R : ChowlaRegime) (M : ℕ) :
    M4SievedDoorSqSupH h R M (fun _ => 1) := by
  intro _ H _ _ _ b q hq _
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  refine integral_logMeasure_le_of_le R.hx R.hω (fun n => ?_)
  have hle := subWindowSup_le_of_norm_le_one
    (a := memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) H n
    ((b : ℝ) / (q : ℝ))
  have h0 := subWindowSup_nonneg
    (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    H n ((b : ℝ) / (q : ℝ))
  have hsq : (subWindowSup (memSCoeff (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (H : ℝ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg ((H : ℕ) : ℝ)]

/-! ### §9.3 — one level further down: the covering side at the inflated cap

`M4ClassPrice.m4_cover_assembly_supQ` carries the modulus range as a pure THREAD — the covering
argument reads only that the integrand is nonnegative, and passes `hqQ` straight to the block
predicate.  So the `h`-family is the landed proof with one binder retyped, and the composition
lands `M4SievedDoorSqH` on `M4BlockMeanSqSupQH`.

⇒ **the open slot for the twisted `L²` door is now the PER-BLOCK MEAN SQUARE at the inflated
modulus range**, which is where the analytic content of the seven producers actually lives.
⛔ **This wave does not touch that content and never claimed to.** -/

/-- **THE `q`-GRADED PER-BLOCK MEAN SQUARE AT THE INFLATED CAP** (`M4BlockMeanSqSupQH`) —
`M4ClassPrice.M4BlockMeanSqSupQ` with `q ≤ arcDen 12 H` inflated to `q ≤ h·arcDen 12 H`. -/
def M4BlockMeanSqSupQH (h : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
    (q : ℝ) ≤ (h : ℝ) * arcDen 12 H → ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE COVERING SIDE AT THE INFLATED CAP** (`m4_cover_assembly_supQH`) — the `h`-family of
`M4ClassPrice.m4_cover_assembly_supQ`.  The covering argument never reads the cap; `hqQ` is a
thread. -/
theorem m4_cover_assembly_supQH {h : ℕ} {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bblk : ℕ → ℝ} (hgates : M4DoorGates Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqSupQH h R M k Bblk) :
    M4SievedDoorSqSupH h R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2)
    (P := Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ)
  simp only [doorSievedCoeff] at hmain
  have heq : 3 * (Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
      = 3 * Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- ⭐⭐ **THE WAVE'S EXIT** (`m4_sievedDoorSqH_of_blockQH`) — `M4SievedDoorSqH` produced from
the per-block mean square at the inflated modulus range, in one composition.

**This is what the wave delivers as an object rather than as a table.**  `HDoorArc`'s N4s socket
was declared open with no producer and none manufacturable from the landed socket; it now has a
producer whose only remaining input is the block predicate at `h·arcDen 12 H`.  The price paid
for the inflation is visible on the page: `(1 + 2π)²·(h·arcDen 12 H)²`, the landed absolute
price times `h²`.

⛔ **WHAT IS STILL OPEN, STATED PLAINLY:** `M4BlockMeanSqSupQH h`.  That is the seven producers'
own analytic content at a wider modulus range, and **this wave is silent on it** — as the 08/31
measurement said it would be, and as `hsock` on the `h`-mint still records. -/
theorem m4_sievedDoorSqH_of_blockQH {h : ℕ} {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bblk Braw : ℕ → ℝ} (hgates : M4DoorGates Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (1 + 2 * Real.pi) ^ 2 * (((h : ℝ) * arcDen 12 H) ^ 2 * (3 * Bblk H)) ≤ Braw H)
    (hblk : M4BlockMeanSqSupQH h R M k Bblk) :
    M4SievedDoorSqH h R M Braw :=
  m4_sievedDoorSqH_of_supH_uniform (fun H => by have := hB0 H; positivity) hgrade
    (m4_cover_assembly_supQH hgates hB0 hblk)

/-! ### §9.4 — the last transcription: the class price at the inflated cap

`M4ClassPrice.m4_blockMeanSqSupQ_of_classPrice` threads the modulus range through to the class
price and reads nothing else about it.  Porting it puts the wave's open slot exactly where the
seven producers' mathematics lives: **the per-class sup bound, at moduli up to `h·arcDen 12 H`
instead of `arcDen 12 H`.**  Nothing below this line is analytic content, and nothing above it
was. -/

/-- **THE CLASS PRICE ASSEMBLED, AT THE INFLATED CAP** (`m4_blockMeanSqSupQH_of_classPriceH`) —
the `h`-family of `M4ClassPrice.m4_blockMeanSqSupQ_of_classPrice`.  The block grade is
`(B H)²/H²`, unchanged; only the range of `q` the class price must serve has widened. -/
theorem m4_blockMeanSqSupQH_of_classPriceH {h : ℕ} {R : ChowlaRegime} {M k : ℕ} {B : ℕ → ℝ}
    (hclass : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (h : ℝ) * arcDen 12 H →
      ∀ i < k, ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        ∀ K, K ≤ H → ∀ r, r < q →
          ‖∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ ≤ B H) :
    M4BlockMeanSqSupQH h R M k (fun H => B H ^ 2 / (H : ℝ) ^ 2) := by
  intro H hlo hhi b q hq hqQ i hik
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  -- ⟦pointwise on the block: the class price squared⟧
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) ^ 2 * B H ^ 2 := fun n hn =>
    subWindowSup_sq_le_class_count (doorSievedCoeff M) H n hq b
      (fun K hK r hr => hclass H hlo hhi q hq hqQ i hik n hn K hK r hr)
  have hcard : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * ((q : ℝ) ^ 2 * B H ^ 2) := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            ((q : ℝ) ^ 2 * B H ^ 2) := Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * ((q : ℝ) ^ 2 * B H ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  have hrhs : B H ^ 2 / (H : ℝ) ^ 2 * (q : ℝ) ^ 2 * (H : ℝ) ^ 2
        * (doorLadder R.x H (i + 1) : ℝ)
      = (doorLadder R.x H (i + 1) : ℝ) * ((q : ℝ) ^ 2 * B H ^ 2) := by
    field_simp
  rw [hrhs]
  refine le_trans hcard ?_
  have hQB : (0 : ℝ) ≤ (q : ℝ) ^ 2 * B H ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hc hQB

/-- **THE INFLATED BLOCK PREDICATE IS INHABITED** (`m4_blockMeanSqSupQH_trivial`) — the
anti-vacuity duty for the wave's remaining open slot, discharged at the trivial per-class grade
`B H := H`.

⛔ **OWED, AND FOR THE SHARP REASON.**  `m4_sievedDoorSqH_of_blockQH` takes
`M4BlockMeanSqSupQH h` as a HYPOTHESIS, and the kernel cannot check that a hypothesis is
inhabited: an uninhabited block predicate would make the whole `h`-door chain vacuously usable
with a green build and a clean axiom audit.  ⚠️ At `B ≡ H` the block grade is `1` and the
`M4GradeGate` of course fails — **that failure is the analytic gap the seven producers close,
and it is a different thing from vacuity.** -/
theorem m4_blockMeanSqSupQH_trivial (h : ℕ) (R : ChowlaRegime) (M k : ℕ) :
    M4BlockMeanSqSupQH h R M k (fun H => (H : ℝ) ^ 2 / (H : ℝ) ^ 2) := by
  refine m4_blockMeanSqSupQH_of_classPriceH (B := fun H => (H : ℝ)) ?_
  intro H _ _ q _ _ i _ n _ K hK r _
  calc ‖∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖
      ≤ ∑ m ∈ windowClass K n q r, ‖doorSievedCoeff M m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ windowClass K n q r, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun m _ => norm_doorSievedCoeff_le_one M m)
    _ = ((windowClass K n q r).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (H : ℝ) := by
        have hcard : (windowClass K n q r).card ≤ K := by
          have hsub := Finset.card_le_card (windowClass_subset K n q r)
          rwa [Nat.card_Ioc, Nat.add_sub_cancel_left] at hsub
        have : ((windowClass K n q r).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcard
        have hKH : (K : ℝ) ≤ (H : ℝ) := by exact_mod_cast hK
        linarith

/-! ### §9.5 — the reduction, read at the door mint

`HDoorArc.m4_doorL2_supply_500_H` takes `M4SievedDoorSqH` as a hypothesis and says of itself:
*"It mints the door; it does not open it … its supplier (N4s) has no producer. ⇒ the twisted
`L²` door is now REACHABLE, NOT DONE."*  §9.2–§9.4 supplied that producer, so the mint can now
be read one level down.  This composition is that reading, stated once so no consumer has to
assemble it. -/

/-- ⭐⭐ **THE `h`-MINT, OFF THE BLOCK PREDICATE** (`m4_doorL2_supply_500_H_of_blockQH`) —
`HDoorArc.m4_doorL2_supply_500_H` with its `hsock : M4SievedDoorSqH h R M Braw` replaced by
what now produces it: the per-block mean square at the inflated modulus range, plus the grade
link that pays the drift price.

**What the twisted `L²` door now waits on, in one name: `M4BlockMeanSqSupQH h`.**

⛔ **AND WHAT THAT IS.**  Through `m4_blockMeanSqSupQH_of_classPriceH` it is the per-class sup
bound at moduli up to `h·arcDen 12 H` — the seven landed producers' own analytic content at a
wider modulus range.  **That estimate is not attempted here and this wave never claimed it.**
The door is still REACHABLE, NOT DONE; what has changed is *what it is reachable FROM*. -/
theorem m4_doorL2_supply_500_H_of_blockQH (h : ℕ) (hh : 0 < h) :
    ∃ (Cg KXi : ℝ), 1 ≤ Cg ∧ 0 < KXi ∧ ∃ H₀ : ℕ,
      ∀ (R : ChowlaRegime), R.eps = 1 / 500 → H₀ ≤ R.Hlo →
        ∀ (Braw Bblk : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
          M4DoorGates Cg R M k δ →
          (∀ H : ℕ, 0 ≤ Braw H) →
          (∀ H : ℕ, 0 ≤ Bblk H) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
            (1 + 2 * Real.pi) ^ 2 * (((h : ℝ) * arcDen 12 H) ^ 2 * (3 * Bblk H)) ≤ Braw H) →
          M4BlockMeanSqSupQH h R M k Bblk →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            MRTUniformityXiL2H h R (2 * KXi * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, KXi, hCg, hKXi, H₀, hmint⟩ := m4_doorL2_supply_500_H h hh
  refine ⟨Cg, KXi, hCg, hKXi, H₀, ?_⟩
  intro R hReps hfloor Braw Bblk Bceil δ M k hgates hBraw0 hBblk0 hgrade hblk hceil
  exact hmint R hReps hfloor Braw Bceil δ M k hgates hBraw0
    (m4_sievedDoorSqH_of_blockQH hgates hBblk0 hgrade hblk) hceil

end Salt.MR
