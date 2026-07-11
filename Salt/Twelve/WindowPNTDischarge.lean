/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.GapsUncond

/-!
# Discharging `WindowPNT` from the ordinary Prime Number Theorem

The capstone `gaps_le_twelve` (`Salt/Twelve/GapsUncond.lean`) carries two named
analytic hypotheses, `WindowPNT` and `EHall`.  `WindowPNT` — the assertion that
the long window `(N, 64N]` holds `(63−ε)·N/log N` primes eventually — needs only
*ordinary* PNT: since `(N, 64N]` is a fixed-ratio (hence long) window,
`π(64N) − π(N) ∼ 63·N/log N` follows from two instances of `π(x) ∼ x/log x`.
This module isolates that entire remaining gap to a single named interface,
`PiAsymp`, mirroring the project's `EHall` pattern.  PNT itself (`PiAsymp`)
arrives later from mathlib upstream / a `PrimeNumberTheoremAnd` dependency and is
*not* proved here.

## Carrier choice for `PiAsymp`

We state `PiAsymp` as an `Asymptotics.IsEquivalent`:
`(fun x ↦ (π ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / log x)`.  This is *exactly* the
shape of `PrimeNumberTheoremAnd`'s `pi_alt'`, so the day the dependency lands the
interface is discharged by a one-liner with no massaging.  Internally the
derivation immediately converts to the ratio-tendsto form via
`Asymptotics.isEquivalent_iff_tendsto_one` (the denominator `x/log x` is
eventually nonzero on `atTop`); the two carriers are interchangeable in mathlib,
and `IsEquivalent` is the one a future upstream statement plugs into cleanly.
-/

open Filter Topology Asymptotics

namespace Salt.Twelve

/-- The Prime Number Theorem in `π ∼ x/log x` form (the classical statement;
supplied later by mathlib upstream or a PNT dependency).  Stated as
`Asymptotics.IsEquivalent` to match `PrimeNumberTheoremAnd.pi_alt'` verbatim. -/
def PiAsymp : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) (fun x : ℝ => x / Real.log x)

/-- **The seam theorem.**  Ordinary PNT (`PiAsymp`) discharges the long-window
hypothesis `WindowPNT`.  For `N → ∞`: `π(64N)/(64N/log 64N) → 1` and
`π(N)/(N/log N) → 1` (two instances of `PiAsymp` along the casts `x := 64N`,
`x := N`), while `log N/(log 64 + log N) → 1`; hence
`(π(64N) − π(N))·log N/N → 64·1·1 − 1 = 63`, so eventually `≥ 63 − ε`. -/
theorem windowPNT_of_piAsymp (h : PiAsymp) : WindowPNT := by
  -- `PiAsymp` as an explicit `IsEquivalent`, then as a ratio tending to `1`.
  have hequiv : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => x / Real.log x) := h
  have hnz : ∀ᶠ x : ℝ in atTop, (fun x : ℝ => x / Real.log x) x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos hx
    exact (div_pos (by linarith) hlogx).ne'
  have hratio := (isEquivalent_iff_tendsto_one hnz).mp hequiv
  -- `π(64N)/(64N/log 64N) → 1`.
  have ha : Tendsto (fun N : ℕ => (Nat.primeCounting (64 * N) : ℝ)
        / ((64 * (N : ℝ)) / Real.log (64 * (N : ℝ)))) atTop (𝓝 1) := by
    have hcast64 : Tendsto (fun N : ℕ => (64 : ℝ) * (N : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have hcomp := hratio.comp hcast64
    refine Filter.Tendsto.congr (fun N => ?_) hcomp
    have hfloor : ⌊(64 : ℝ) * (N : ℝ)⌋₊ = 64 * N := by
      rw [show (64 : ℝ) * (N : ℝ) = ((64 * N : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    simp only [Function.comp_apply, Pi.div_apply, hfloor]
  -- `π(N)/(N/log N) → 1`.
  have hb : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 1) := by
    have hcomp := hratio.comp tendsto_natCast_atTop_atTop
    refine Filter.Tendsto.congr (fun N => ?_) hcomp
    simp only [Function.comp_apply, Pi.div_apply, Nat.floor_natCast]
  -- `log N/(log 64 + log N) → 1`.
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun N : ℕ => Real.log 64 + Real.log (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ (Real.log 64) hlogN
  have hr : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (Real.log 64 + Real.log (N : ℝ)))
      atTop (𝓝 1) := by
    have hz0 : Tendsto (fun N : ℕ => (-Real.log 64) / (Real.log 64 + Real.log (N : ℝ)))
        atTop (𝓝 0) := Filter.Tendsto.div_atTop tendsto_const_nhds hden
    have hsum : Tendsto (fun N : ℕ => 1 + (-Real.log 64) / (Real.log 64 + Real.log (N : ℝ)))
        atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hz0
    rw [add_zero] at hsum
    refine Filter.Tendsto.congr (fun N => ?_) hsum
    have h64 : (0 : ℝ) < Real.log 64 := Real.log_pos (by norm_num)
    have hlogNnn : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have hdenne : Real.log 64 + Real.log (N : ℝ) ≠ 0 := by
      have : (0 : ℝ) < Real.log 64 + Real.log (N : ℝ) := by linarith
      exact this.ne'
    field_simp
    ring
  -- Assemble: `(π(64N) − π(N))·log N/N → 64·1·1 − 1 = 63`.
  have hg : Tendsto (fun N : ℕ =>
        ((Nat.primeCounting (64 * N) : ℝ) - (Nat.primeCounting N : ℝ)) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 63) := by
    have hconst : Tendsto (fun _ : ℕ => (64 : ℝ)) atTop (𝓝 64) := tendsto_const_nhds
    have hcomb := ((hconst.mul ha).mul hr).sub hb
    rw [show (64 : ℝ) * 1 * 1 - 1 = 63 by norm_num] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN2
    have hNgt1 : (1 : ℕ) < N := by omega
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : (0 : ℕ) < N).ne'
    have hlogN0 : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hNgt1)
    have hlogNne : Real.log (N : ℝ) ≠ 0 := hlogN0.ne'
    have hlog64pos : (0 : ℝ) < Real.log 64 := Real.log_pos (by norm_num)
    have hdenne : Real.log 64 + Real.log (N : ℝ) ≠ 0 := by
      have : (0 : ℝ) < Real.log 64 + Real.log (N : ℝ) := by linarith
      exact this.ne'
    have hlog64N : Real.log (64 * (N : ℝ)) = Real.log 64 + Real.log (N : ℝ) :=
      Real.log_mul (by norm_num) hNne
    rw [hlog64N]
    field_simp
  -- Peel off `ε` and turn the limit `63` into the eventual lower bound.
  intro ε hε
  filter_upwards [hg.eventually_const_le (show (63 : ℝ) - ε < 63 by linarith),
    eventually_ge_atTop 2] with N hgeN hN2
  have hNgt1 : (1 : ℕ) < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < N)
  have hlogN0 : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hNgt1)
  rw [div_le_iff₀ hlogN0]
  rw [le_div_iff₀ hNpos] at hgeN
  linarith [hgeN]

/-- **The headline corollary.**  Explicit bounded prime gaps `≤ 12`, now resting
on the single classical input `PiAsymp` (ordinary PNT) together with `EHall`.
Definitionally just `gaps_le_twelve ∘ windowPNT_of_piAsymp` — no new analytic
content beyond the seam theorem. -/
theorem gaps_le_twelve_of_piAsymp (hpi : PiAsymp) (hEH : EHall) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 :=
  gaps_le_twelve (windowPNT_of_piAsymp hpi) hEH

end Salt.Twelve
