/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Tuple
import Salt.Maynard.CongCount

/-!
# CRT solvability of the tuple congruence system (blueprint N4.3)

`cong_solvable` discharges the `hsol` hypothesis threaded through
`congCountTuple_approx` (N4.1) and hence `S1Bound` (N4.3): given `k+1`
pairwise-coprime moduli — the fixed sieve modulus `W k` and, for each
coordinate `i`, the combined modulus `lcm(dᵢ, eᵢ)` — the joint system

* `c ≡ ν₀ (mod W k)`;
* `lcm(dᵢ, eᵢ) ∣ c + hSeq k i` for every `i` (equivalently `c ≡ -hSeq k i`)

has a solution `c`.

Route (mirrors `Salt.Maynard.exists_nu0`): iterated CRT. We fold
`Nat.chineseRemainder` over `Finset.univ : Finset (Fin k)`, starting from
the residue `ν₀` mod `W k` and combining, one coordinate at a time, the
per-coordinate target residue `aᵢ` (chosen so `aᵢ + hSeq k i ≡ 0 mod
lcm(dᵢ,eᵢ)`) with the accumulated modulus `W k * ∏_{j∈s} lcm(dⱼ,eⱼ)`.
Coprimality of the new coordinate modulus to the accumulator comes from
`hcopW` (vs. `W k`) and `hcoplcm` (vs. the earlier coordinates, distinct
since the coordinate is fresh to the fold).
-/

namespace Salt.Maynard

open Finset

/-- **N4.3.** The joint `W`-trick + coordinate congruence system is solvable:
there is a residue `c` with `c ≡ ν₀ (mod W k)` and, for every coordinate `i`,
`lcm(dᵢ, eᵢ) ∣ c + hSeq k i`. This discharges the `hsol` hypothesis of
`congCountTuple_approx`, making `S1_upper` unconditional. -/
theorem cong_solvable (k : ℕ) (d e : Fin k → ℕ) (ν₀ : ℕ)
    (hWpos : 0 < W k) (hlcmpos : ∀ i, 0 < Nat.lcm (d i) (e i))
    (hcopW : ∀ i, Nat.Coprime (W k) (Nat.lcm (d i) (e i)))
    (hcoplcm : ∀ i j, i ≠ j → Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))) :
    ∃ c : ℕ, c % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i) := by
  classical
  -- `hWpos` is part of the N4.1 hypothesis bundle; positivity of `W k` is not
  -- needed by the CRT fold itself (each `Nat.chineseRemainder` step only needs
  -- coprimality), so we simply retain it as an available fact.
  have _ := hWpos
  -- Per-coordinate target residue `aᵢ`, chosen so that `lcm(dᵢ,eᵢ) ∣ aᵢ + hSeq k i`.
  set a : Fin k → ℕ :=
    fun i => Nat.lcm (d i) (e i) * (hSeq k i / Nat.lcm (d i) (e i) + 1) - hSeq k i
    with ha
  -- The defining property of `aᵢ`.
  have haZero : ∀ i, Nat.lcm (d i) (e i) ∣ (a i + hSeq k i) := by
    intro i
    have hLpos : 0 < Nat.lcm (d i) (e i) := hlcmpos i
    have hdm := Nat.div_add_mod (hSeq k i) (Nat.lcm (d i) (e i))
    have hmlt := Nat.mod_lt (hSeq k i) hLpos
    have hXY : Nat.lcm (d i) (e i) * (hSeq k i / Nat.lcm (d i) (e i) + 1)
        = Nat.lcm (d i) (e i) * (hSeq k i / Nat.lcm (d i) (e i)) + Nat.lcm (d i) (e i) := by
      ring
    have key : a i + hSeq k i
        = Nat.lcm (d i) (e i) * (hSeq k i / Nat.lcm (d i) (e i) + 1) := by
      simp only [ha]
      omega
    rw [key]
    exact dvd_mul_right _ _
  have haModEq : ∀ i, a i + hSeq k i ≡ 0 [MOD Nat.lcm (d i) (e i)] :=
    fun i => Nat.modEq_zero_iff_dvd.mpr (haZero i)
  -- Generalized statement: solvable over any subset of coordinates, keeping
  -- the `W k` congruence throughout.
  suffices hgen : ∀ s : Finset (Fin k), ∃ c : ℕ,
      c % W k = ν₀ % W k ∧ ∀ i ∈ s, Nat.lcm (d i) (e i) ∣ (c + hSeq k i) by
    obtain ⟨c, hcW, hc⟩ := hgen Finset.univ
    exact ⟨c, hcW, fun i => hc i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨ν₀, rfl, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert x s hx ih =>
    obtain ⟨c₁, hc₁W, hc₁⟩ := ih
    -- Accumulated modulus after the previous coordinates.
    set M : ℕ := W k * ∏ j ∈ s, Nat.lcm (d j) (e j) with hM
    -- The fresh coordinate modulus is coprime to the accumulator.
    have hcopx : Nat.Coprime (Nat.lcm (d x) (e x)) M := by
      rw [hM]
      apply Nat.Coprime.mul_right
      · exact (hcopW x).symm
      · apply Nat.Coprime.prod_right
        intro j hj
        exact hcoplcm x j (by rintro rfl; exact hx hj)
    -- CRT: combine `a x` (mod lcm x) with `c₁` (mod M).
    obtain ⟨c, hcx, hcM⟩ := Nat.chineseRemainder hcopx (a x) c₁
    refine ⟨c, ?_, ?_⟩
    · -- `c ≡ c₁ ≡ ν₀ (mod W k)`, since `W k ∣ M`.
      have hWdvd : W k ∣ M := by rw [hM]; exact dvd_mul_right (W k) _
      have hcWk : c % W k = c₁ % W k := hcM.of_dvd hWdvd
      exact hcWk.trans hc₁W
    · intro i hi
      rcases Finset.mem_insert.mp hi with hix | his
      · -- `i = x`: `c ≡ a x`, and `a x + hSeq k x ≡ 0`.
        subst hix
        exact Nat.modEq_zero_iff_dvd.mp ((hcx.add_right (hSeq k i)).trans (haModEq i))
      · -- `i ∈ s`: `c ≡ c₁ (mod lcm i)` via `lcm i ∣ M`, and `lcm i ∣ c₁ + hSeq k i`.
        have hdvdM : Nat.lcm (d i) (e i) ∣ M := by
          rw [hM]
          exact (Finset.dvd_prod_of_mem _ his).trans (dvd_mul_left _ (W k))
        have hci : c ≡ c₁ [MOD Nat.lcm (d i) (e i)] := hcM.of_dvd hdvdM
        have hc₁0 : c₁ + hSeq k i ≡ 0 [MOD Nat.lcm (d i) (e i)] :=
          Nat.modEq_zero_iff_dvd.mpr (hc₁ i his)
        exact Nat.modEq_zero_iff_dvd.mp ((hci.add_right (hSeq k i)).trans hc₁0)

end Salt.Maynard
