/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13FramesA

/-!
# ⟦E1⟧ THE SIEVE-FREE DOOR REGISTER (`m4_ladder_gates_lam`)

`S13FramesA.s13_doorGates_of_arm` discharges seven of the eight `M4DoorGates` fields
at `k := doorCount R.ω` from a `g`-arm and the regime alone.  But `M4DoorGates` is a
SIEVED register: it drags in `M`, `δ`, `Cg` and `SieveBlockGate`, none of which the
sieve-free (δ₀-split) road has.

This file is that register with the five sieve fields (`hM`, `hδ`, `hMδ`, `hcount`,
`hblocks`) deleted — the four gates the unsieved row chain actually reads, at the
in-statement count `doorCount R.ω`:

* the ladder EXHAUSTS the window uniformly over the admissible `H`-range
  (`M4Door.doorCount_gates`, off the arm's `2·ω·(H₊+2)` summand);
* the geometric ceiling `2^{k+1} ≤ x` (`M4SecondRoad.two_pow_le_four_mul_of_count`,
  off the arm's `8·ω` summand);
* the `log ω` cancellation `k ≤ 3·Z` (`M4Door.door_count_le_three_mul_norm` at
  `S13FramesA.s13_logOmega_ge`) — ARM-FREE, regime fields only;
* the normaliser floor `3 ≤ Z` (`M4Door.door_norm_ge` + `s13_logOmega_ge`) —
  ARM-FREE likewise.

⚠️ SCOPE.  Nothing here is a statement about `λ`, about the row mean square, or about
the frequency `α`.  It is the door's ladder bookkeeping, stated in the currency the
sieve-free road consumes.

⚠️ THE `harm` HYPOTHESIS.  The frozen statement keeps the ℕ arm
`2·ω·(H₊+2) + 8·ω ≤ x`.  Only the first two conjuncts read it; conjuncts 3 and 4 are
proved from the `ChowlaRegime` fields alone.  A refuter argued conjuncts 1–2 are also
arm-derivable (`hheadroom'` + `hHlo_floor` + `hωx`); that route needs an unelaborated
`1 ≤ Real.log R.Hhi` step and is NOT taken here.  The redundancy costs the caller one
`max` branch and cannot make the statement false.

⚠️ This module is NOT rooted in any aggregate — it must be built targeted
(`../saltbuild.sh Salt.MR.MRTPortLadderGates`) until a maestro-tier session roots it.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **⟦E1⟧ THE SIEVE-FREE DOOR REGISTER** (`m4_ladder_gates_lam`) — the four ladder
gates at `k := doorCount R.ω`, from the ℕ arm `2·ω·(H₊+2) + 8·ω ≤ x` and the regime.

Line-for-line the proof of `s13_doorGates_of_arm` with the five sieve fields deleted,
plus the two `log ω`-cancellation conjuncts the unsieved road reads in place of the
sieved `hcount`. -/
theorem m4_ladder_gates_lam (R : ChowlaRegime)
    (harm : 2 * R.ω * (R.Hhi + 2) + 8 * R.ω ≤ R.x) :
    (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
        doorLadder R.x H (doorCount R.ω) ≤ R.x / R.ω)
      ∧ 2 ^ (doorCount R.ω + 1) ≤ R.x
      ∧ ((doorCount R.ω : ℕ) : ℝ)
          ≤ 3 * ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹
      ∧ (3 : ℝ) ≤ ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹ := by
  have hω1 : 1 ≤ R.ω := by have := R.hω; omega
  have hcount : ((doorCount R.ω : ℕ) : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2 :=
    doorCount_le hω1
  -- ⟦the arm's two summands⟧
  have harm1 : 2 * R.ω * (R.Hhi + 2) ≤ R.x := by omega
  have harm2 : 8 * R.ω ≤ R.x := by omega
  -- ⟦the two ARM-FREE inputs: the `log ω` floor and the normaliser's lower half⟧
  have hlogω : 4 ≤ Real.log (R.ω : ℝ) := s13_logOmega_ge R
  have hZ : Real.log (R.ω : ℝ) - 1 ≤ ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹ :=
    door_norm_ge R.hx R.hω R.hωx
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ⟦hreach⟧ the ladder exhausts the window, off `2ω(H+2) ≤ x`
    intro H hlo hhi
    have hbig : 2 * (R.ω : ℝ) * ((H : ℝ) + 2) ≤ (R.x : ℝ) := by
      have hHle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
      have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
      have h1 : ((2 * R.ω * (R.Hhi + 2) : ℕ) : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast harm1
      push_cast at h1
      nlinarith
    exact (doorCount_gates hω1 hbig).1
  · -- ⟦hpow⟧ `2^{k+1} ≤ 8ω ≤ x`
    have h4 : 2 ^ (doorCount R.ω) ≤ 4 * R.ω :=
      two_pow_le_four_mul_of_count R.hω hcount
    have hps : 2 ^ (doorCount R.ω + 1) = 2 ^ (doorCount R.ω) * 2 := by rw [pow_succ]
    omega
  · -- ⟦the `log ω` cancellation⟧ `k ≤ 3·Z`
    exact door_count_le_three_mul_norm hlogω hcount hZ
  · -- ⟦the normaliser floor⟧ `Z ≥ log ω − 1 ≥ 3`
    linarith

end Salt.MR

end
