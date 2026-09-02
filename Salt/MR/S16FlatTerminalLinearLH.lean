/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalLinear
import Salt.MR.S16ProducersH
import Salt.MR.S16FlatTerminalExitH

/-!
# THE FLAT-LINEAR LANE AT THE INFLATED SOCKET — the two riders, re-quantified

⟦WHAT THIS FILE SETTLES⟧  `S16FlatTerminalLinear` carries the flat-linear lane's two open
riders — the band-lane `C` rider `S16BandLaneCBoundedL` and the crossing bound
`S15CrossingBound_L_gk` — both quantified over the LANDED linear socket `SocketBaseL`.  The
`h`-lane's hops need the same two riders quantified over the INFLATED socket
`HDoorSupply.SocketBaseLH h`, whose arc denominator is `h · arcDen 12 H`.  This file states
them and pins each to its landed twin at `h = 1`.

⛔ **NEITHER DEF IS A THEOREM AND NEITHER GAINS A PRODUCER HERE.**  `S16BandLaneCBoundedL`
has **no producer anywhere in the corpus** at `h = 1` (34 binder sites across 9 modules, zero
discharges); re-quantifying it at `SocketBaseLH h` re-states an open rider, it does not open a
new one.  `S15CrossingBound_LH_gk` is H2c's target.  The `h`-lane's conditionality is therefore
**exactly** the `h = 1` lane's conditionality, on the same two objects.

⭐ **THE DIRECTION THAT HOLDS IS THE ONE THAT IS USELESS HERE.**
`socketBaseLH_of_socketBaseL` gives `SocketBaseL → SocketBaseLH h`, so an `LH` rider — whose
socket sits in HYPOTHESIS position under a `∀` — is a **STRONGER** Prop than its landed twin:
`S16BandLaneCBoundedLH h K → S16BandLaneCBoundedL K` is the implication that would follow, and
the converse, which is the one a consumer at `h ≥ 2` would want, is **NOT** claimed and is
false in general at `h ≥ 2`.  Only the `h = 1` twin laws below are stated, and they are stated
as theorems rather than left as docstring claims.

⟦IMPORT DIRECTION⟧  This file does **not** import `Salt.MR.HSeamCheck`.  `HSeamCheck` is a leaf
(`All.lean` is its only importer) and it hosts the integration acceptance for this lane, so the
edge runs `HSeamCheck → S16FlatTerminalLinearLH`; the reverse edge is a cycle Lake rejects.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE BAND-LANE RIDER AT THE INFLATED SOCKET -/

/-- **⟦THE BAND-LANE `C` RIDER, AT THE INFLATED SOCKET⟧** (`S16BandLaneCBoundedLH`) —
`S16FlatTerminalLinear.S16BandLaneCBoundedL` with **both** of its
`∀ H L q j A s, SocketBaseL R M H L q j A s →` quantifiers read at
`HDoorSupply.SocketBaseLH h R M H L q j A s`.  Everything else — the `x₀`/`Cband` witness, the
`log Cband ≤ 40` cap, the `C'` bound, the band base `DoorBandBase_L_gk` and the `t0BandB`
conclusion — is byte-identical to the landed rider.

The landed rider has no producer in the corpus; this one re-quantifies that same open rider at
the inflated socket.  `s16BandLaneCBoundedLH_one_iff` pins it. -/
def S16BandLaneCBoundedLH (h K : ℕ) : Prop :=
  ∃ (x₀ : ℕ) (Cband : ℝ), 0 < Cband ∧ Real.log Cband ≤ 40 ∧ ∀ (M : ℕ), 1 ≤ M →
    ∃ C' : ℝ, 0 < C' ∧
      C' ≤ (Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
          * (M : ℝ) ^ (2.1 : ℝ) ∧
      ∀ (R : ChowlaRegime) (C₁ M₀ : ℕ → ℝ),
        ((∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            DoorBandBase_L_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
          ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
            ∀ χ : DirichletCharacter ℂ q,
              (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
                ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
                ≤ t0BandB (((A + s : ℕ)) : ℝ)
                    (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))

/-! ## §1 — THE CROSSING BOUND AT THE INFLATED SOCKET -/

/-- **⟦THE CROSSING BOUND AT THE INFLATED SOCKET⟧** (`S15CrossingBound_LH_gk`) —
`S16FlatTerminalLinear.S15CrossingBound_L_gk` with its one
`∀ H L q j A s, SocketBaseL R M H L q j A s →` quantifier read at `SocketBaseLH h`.

⭐ **THE `ε_r` WINDOW DOES NOT MOVE.**  The exponent `-theta293 + (theta293 - 1/500)` is
carried UNCHANGED: the window is `h`-blind, and at `h = 1` it is discharged socket-free at the
landed site.  A `1/(500·h)` here would be a different object, not a port. -/
def S15CrossingBound_LH_gk (h K : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseLH h R M H L q j A s →
    ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
      2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
          ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
        ≤ 8 * (0 : ℝ) ^ 2
          + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                \ seamBall (((A + s : ℕ)) : ℝ) 0)
              ∩ seamTtotG (chiBarCoeff q χ liouvilleC)
                  (calP (AdoorL M) (s13GK K M))
                  (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                  (mrAlpha (1 / 12)) 2,
              ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
          + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
              * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + (theta293 - 1 / 500)))


/-! ## §2 — THE `h = 1` TWIN LAWS (the anti-drift gate) -/

/-- ⭐ **THE BAND-LANE RIDER AT `h = 1` IS THE LANDED RIDER**
(`s16BandLaneCBoundedLH_one_iff`) — the anti-drift gate for §0.  A def that did not reduce to
its landed twin at `h = 1` would be a different definition wearing the same name, and nothing
downstream could see the drift: both occurrences of the socket sit in HYPOTHESIS position, so a
drifted def would still elaborate everywhere it is consumed.  Stated as a theorem, not asserted
in a docstring. -/
theorem s16BandLaneCBoundedLH_one_iff (K : ℕ) :
    S16BandLaneCBoundedLH 1 K ↔ S16BandLaneCBoundedL K := by
  unfold S16BandLaneCBoundedLH S16BandLaneCBoundedL
  simp only [socketBaseLH_one_iff]

/-- ⭐ **THE CROSSING BOUND AT `h = 1` IS THE LANDED CROSSING BOUND**
(`s15CrossingBound_LH_gk_one_iff`) — the anti-drift gate for §1, and the statement that keeps
H2c honest: its target at `h = 1` must be the object the landed supplier already meets. -/
theorem s15CrossingBound_LH_gk_one_iff (K : ℕ) (R : ChowlaRegime) (M : ℕ) :
    S15CrossingBound_LH_gk 1 K R M ↔ S15CrossingBound_L_gk K R M := by
  unfold S15CrossingBound_LH_gk S15CrossingBound_L_gk
  simp only [socketBaseLH_one_iff]

end Salt.MR
