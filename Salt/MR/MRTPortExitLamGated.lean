/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTPortLadderGates
import Salt.MR.MRTPortExitLam

/-!
# ⟦E4⟧ THE SEAL — ONE PRICING LINE LEFT (`m4_exit_lam_of_rowMeanSqLam_gated`)

`MRTPortExitLam.m4_exit_lam_of_rowMeanSqLam` (E2) is the D8 → D9 composition, but it
still exposes SIX hypotheses: the three ladder gates, the row pricing line, the
`H`-uniform ladder tail, and the row mean square itself.  This file discharges four of
them through E2's own `∀ (U1floor) (g)` slot, leaving exactly TWO.

The move is the corpus's standing floor-absorption idiom (`S12ConstCompose.lean:537`,
and the `⌈128·ω/δ⌉₊` summand of `S13FramesA.s13GArm`): E2's `c` is bound by its `∃`
BEFORE the `∀ g` binder, so the caller may instantiate `g` at an arm that mentions `c`.
We take

  `g' Hhi ω := max (g Hhi ω) (max (2·ω·(Hhi+2) + 8·ω) ⌈32·ω/c⌉₊)`

and peel three arms off `g' R.Hhi R.ω ≤ R.x`:

* arm 1 returns the caller's own `g R.Hhi R.ω ≤ R.x` untouched;
* arm 2 is exactly `MRTPortLadderGates.m4_ladder_gates_lam`'s ℕ arm, which yields the
  three ladder gates AND the normaliser floor `3 ≤ Z`;
* arm 3 pays E2's ladder tail: `2^k ≤ 4·ω` (`M4SecondRoad.two_pow_le_four_mul_of_count`
  — ⚠️ a ℕ conclusion against an ℝ gate, so it crosses by `exact_mod_cast`, the landed
  idiom of `S13FramesA.s13_endpoint_of_arm`) gives `8·2^k ≤ 32·ω ≤ c·x`, and
  `Z ≥ 3` with `R.hHlo_floor : 4000000 ≤ H₋` gives `Z·H₋ ≥ 1`.

⛔ SCOPE — THIS IS THE WAVE'S TERMINUS AND THEREFORE THE MOST INFLATABLE POINT IN IT.
What survives is TWO hypotheses, and NEITHER is closed here:

* the pricing line `∀ H ∈ [H₋, H₊], 6 * MS H ≤ c` at an opaque existential `c` — this
  is what a FUTURE SUPPLY WAVE must meet, and meeting it uniformly over the window is
  not a numeral chase but the statement that the row mean square beats the trivial
  ceiling by a fixed factor;
* `M4RowMeanSqLam R (doorCount R.ω) MS` — the unsieved row mean square at EVERY
  tight-major `α`, class D.  **This is GAP α wearing the row's clothes.**

⛔ **GAP α** (the major arc / the supply for `M4RowMeanSqLam`), **GAP A.1** (`MRTThmA1`
is a `def … : Prop` with no producer), and **GAP X** (the conclusion is delivered at an
`∃ R`-CHOSEN regime — unboundedly many scales, NOT all large scales) all stand
UNTOUCHED by this file.  This node does not make the chain shorter than its analytic
input; it RELOCATES the open object from the door integral to the row integral and
prices it.  Nothing here closes the door, touches the arc, or proves anything about `λ`
that did not exist before.

⛔ **STALE WHEN WRITTEN, CORRECTED 2026-08-26 (math, arc Wave H node H-2).**  The line below
was true when the executor wrote it and false by the time the wave landed: this module IS
rooted.  `Salt/MR/All.lean` imports it, and `m4_exit_lam_of_rowMeanSqLam_gated`
sits in the `#audit_axioms` tail.  The original sentence is kept rather than
deleted, per `MRTPortRowLam.lean`'s
append-only idiom:

> ⚠️ This module is NOT rooted in any aggregate — it must be built targeted
> (`../saltbuild.sh Salt.MR.MRTPortExitLamGated`) until a maestro-tier session roots it.

*The maestro-tier session it waits for has already happened; the sentence outlived its own
condition.*
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **⟦E4⟧ THE SEAL.**  `m4_exit_lam_of_rowMeanSqLam` (E2) with the ladder register and
the ladder tail absorbed into the `g`-arm: `¬ logChowla2Fails R.eps R.x R.ω` now follows
from ONE pricing line `6 * MS H ≤ c` plus the row input `M4RowMeanSqLam R (doorCount R.ω) MS`.

⛔ Both survivors are open: the row input is GAP α in the row's currency (class D), and
the regime is `∃`-chosen (GAP X).  See the module docstring. -/
theorem m4_exit_lam_of_rowMeanSqLam_gated :
    ∃ (ε : ℚ) (c : ℝ), 0 < ε ∧ 0 < c ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          (∀ MS : ℕ → ℝ,
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 6 * MS H ≤ c) →
            M4RowMeanSqLam R (doorCount R.ω) MS →
              ¬ logChowla2Fails R.eps R.x R.ω)
    := by
  obtain ⟨ε, c, hε, hc, hchain⟩ := m4_exit_lam_of_rowMeanSqLam
  refine ⟨ε, c, hε, hc, ?_⟩
  intro U1floor g
  -- ⟦THE ABSORBING ARM⟧ legal because `c` is bound by E2's `∃` BEFORE its `∀ g`.
  obtain ⟨R, hReps, hRU1, hRg', hRtow, hR⟩ :=
    hchain U1floor (fun Hhi ω =>
      max (g Hhi ω) (max (2 * ω * (Hhi + 2) + 8 * ω) ⌈(32 : ℝ) * (ω : ℝ) / c⌉₊))
  have hRg2 : max (g R.Hhi R.ω)
      (max (2 * R.ω * (R.Hhi + 2) + 8 * R.ω) ⌈(32 : ℝ) * (R.ω : ℝ) / c⌉₊) ≤ R.x := hRg'
  refine ⟨R, hReps, hRU1, le_trans (le_max_left _ _) hRg2, hRtow, ?_⟩
  intro MS hprice hrow
  -- ⟦arm 2⟧ the ladder register's ℕ arm
  have harm : 2 * R.ω * (R.Hhi + 2) + 8 * R.ω ≤ R.x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRg2
  -- ⟦arm 3⟧ the tail price
  have harmc : ⌈(32 : ℝ) * (R.ω : ℝ) / c⌉₊ ≤ R.x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRg2
  obtain ⟨hreach, hpow, hk3, hZ3⟩ := m4_ladder_gates_lam R harm
  -- ⟦the ℕ→ℝ crossing: `two_pow_le_four_mul_of_count` concludes in ℕ, the gate is in ℝ⟧
  have hω1 : 1 ≤ R.ω := by have := R.hω; omega
  have h4 : 2 ^ (doorCount R.ω) ≤ 4 * R.ω :=
    two_pow_le_four_mul_of_count R.hω (doorCount_le hω1)
  have h4R : ((2 ^ (doorCount R.ω) : ℕ) : ℝ) ≤ 4 * (R.ω : ℝ) := by exact_mod_cast h4
  have h2R : (8 : ℝ) * ((2 : ℝ) ^ (doorCount R.ω)) ≤ 32 * (R.ω : ℝ) := by
    have h : ((2 : ℝ)) ^ (doorCount R.ω) ≤ 4 * (R.ω : ℝ) := by simpa using h4R
    linarith
  have hx0 : (0 : ℝ) < (R.x : ℝ) := by
    have h : 0 < R.x := by have := R.hx; omega
    exact_mod_cast h
  have hceil : (32 : ℝ) * (R.ω : ℝ) / c ≤ (R.x : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast harmc
  have hkey : 32 * (R.ω : ℝ) ≤ c * (R.x : ℝ) := by
    rw [div_le_iff₀ hc] at hceil
    linarith
  have hHlo1 : (1 : ℝ) ≤ (R.Hlo : ℝ) := by
    have h : 1 ≤ R.Hlo := by have := R.hHlo_floor; omega
    exact_mod_cast h
  have hcx : (0 : ℝ) < c * (R.x : ℝ) := mul_pos hc hx0
  have htail : (8 : ℝ) * 2 ^ (doorCount R.ω)
      ≤ c * (R.x : ℝ) * (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) * (R.Hlo : ℝ) := by
    have hZH : (1 : ℝ)
        ≤ (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) * (R.Hlo : ℝ) := by
      nlinarith [hZ3, hHlo1]
    calc (8 : ℝ) * 2 ^ (doorCount R.ω) ≤ 32 * (R.ω : ℝ) := h2R
      _ ≤ c * (R.x : ℝ) := hkey
      _ ≤ c * (R.x : ℝ)
            * ((∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) * (R.Hlo : ℝ)) :=
          le_mul_of_one_le_right hcx.le hZH
      _ = c * (R.x : ℝ) * (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹)
            * (R.Hlo : ℝ) := by ring
  exact hR (doorCount R.ω) MS hreach hpow hk3 hprice htail hrow

end Salt.MR

end
