/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Switch

/-!
# G-SW — the Goldbach switch BV bridge (the class `prod ≡ N (mod d)`) + the AggCE crumb, W2

Design: `docs/exploration/q1-design.md`, node **G-SW** (D3).  This file is the Goldbach mirror of
`Salt/Chen/SwitchBV.lean` (the switched remainder → bilinear reduction) and `Salt/Chen/AggCE.lean`
(the conversion-error crumb), at the reflected switch class `prod3 ≡ N (mod d)`.

## THE GATE FINDING — the `{q ∣ N}` unit seam VANISHES

The twin needs `switch_dvd_coprime_two` (`2` is a unit mod odd `d`) + odd-`d` casework.  For
Goldbach the switch class is `N (mod d)`, and the unit fact is **`Coprime d N`** — FREE for every
`d ∣ Ps` whenever the sifting modulus is coprime to `N` (the caller supplies `goldPs`, and
`Salt.Goldbach.goldPs_coprime_N` discharges `hPsN`).  No odd-`d` split is needed — strictly
simpler than the twin (`gold_switch_coprime_N` replaces `switch_dvd_coprime_two`).

## What this file lands (sorry-free, new file)

* **Part A** — the unit fact `gold_switch_coprime_N`/`gold_N_isUnit_of_dvd`; residue-`N`
  products are coprime to `d` (`gold_prod_isUnit_of_residue_N`).
* **Part B** — `goldSwitchSieve_multSum_eq_dvdCount`/`_apCount`: the per-`d` residue-class mass is
  the count of admissible triples with `prod3 ≡ N (mod d)` (the class the bilinear engine reads).
* **Part C** — the `0/1` semiprime-block `α` (`goldSemiprimeBlockInd`, `‖α‖ ≤ 1`).
* **Part D** — the honest per-`d` remainder split
  `rem d = (resCount − ν·unitCount) − ν·nonUnitCount`, its triangle bound, the summed L¹
  reduction, and the composition scaffold `gold_hBVswitch_of_generalBV` (the exact `hBVswitch`
  shape `gold_mainA3_of_hBVswitch` names).
* **Part E** — the AggCE conversion-error crumb (N-free per the gate): the finding-5 forcing
  `gold_nonunit_forces_fst_dvd` and the operating-point estimate `gold_hCE_at_op`.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen

namespace Salt.Goldbach

/-! ## Part A — the unit fact (the `{q ∣ N}` seam VANISHES) -/

/-- **The Goldbach switch unit fact.**  Every `d ∣ Ps` is coprime to `N` when the sifting modulus
`Ps` is coprime to `N` — the direct replacement of the twin's `switch_dvd_coprime_two` (`2` a
unit mod odd `d`).  At instantiation `Ps := goldPs N z w'`, `hPsN` is `goldPs_coprime_N`. -/
theorem gold_switch_coprime_N {Ps N : ℕ} (hPsN : Nat.Coprime Ps N) {d : ℕ} (hd : d ∣ Ps) :
    Nat.Coprime d N :=
  Nat.Coprime.coprime_dvd_left hd hPsN

/-- **`N` is a unit mod `d`.**  For `d ∣ Ps` (with `Coprime Ps N`), `(N : ZMod d)` is a unit;
the residue-`N` class the switched `multSum d` registers is the unit class. -/
theorem gold_N_isUnit_of_dvd {Ps N : ℕ} (hPsN : Nat.Coprime Ps N) {d : ℕ} (hd : d ∣ Ps) :
    IsUnit ((N : ℕ) : ZMod d) :=
  (ZMod.isUnit_iff_coprime N d).mpr (gold_switch_coprime_N hPsN hd).symm

/-- **A residue-`N` product is coprime to `d`.**  If `(prod : ZMod d) = (N : ZMod d)` and
`d ∣ Ps` (coprime to `N`), then `(prod : ZMod d)` is a unit — no non-coprime products enter the
switched residue-class count.  Mirrors `prod_isUnit_of_residue_two`. -/
theorem gold_prod_isUnit_of_residue_N {Ps N : ℕ} (hPsN : Nat.Coprime Ps N) {d prod : ℕ}
    (hd : d ∣ Ps) (hres : ((prod : ℕ) : ZMod d) = ((N : ℕ) : ZMod d)) :
    IsUnit ((prod : ℕ) : ZMod d) := by
  rw [hres]; exact gold_N_isUnit_of_dvd hPsN hd

/-! ## Part B — the per-`d` AP-count reformulation of `multSum` (class `prod ≡ N`) -/

/-- **`multSum d` counts triples with `d ∣ N − prod` (FULL).**  Fibering `goldTripleSet` over
`n = N − prod3 t ∈ twinWindow N` and matching the per-`n` fibre against `goldACount`.  Mirrors
`switchSieve_multSum_eq_dvdCount` with `prod3 − 2 ↦ N − prod3`. -/
theorem goldSwitchSieve_multSum_eq_dvdCount (N z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    (goldSwitchSieve N z y Ps hPs hPodd).multSum d
      = (((goldTripleSet N z y).filter (fun t => d ∣ (N - prod3 t))).card : ℝ) := by
  classical
  rw [goldSwitchSieve_multSum]
  have Hmem : ∀ t ∈ (goldTripleSet N z y).filter (fun t => d ∣ (N - prod3 t)),
      N - prod3 t ∈ twinWindow N := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h := ht.1
    rw [goldTripleSet, Finset.mem_filter] at h
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := h
    rw [twinWindow, Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise Hmem, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [twinWindow, Finset.mem_Icc] at hn
  have hfib : (((goldTripleSet N z y).filter (fun t => d ∣ (N - prod3 t))).filter
        (fun t => N - prod3 t = n))
      = (goldTripleSet N z y).filter (fun t => d ∣ (N - prod3 t) ∧ N - prod3 t = n) := by
    rw [Finset.filter_filter]
  rw [hfib]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    unfold goldACount
    rw [Nat.cast_inj]
    refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
    rw [goldTripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := ht
    constructor
    · intro hpe
      refine ⟨?_, by omega⟩
      have hnp : N - prod3 t = n := by omega
      rw [hnp]; exact hdn
    · rintro ⟨_, hpn⟩; omega
  · rw [if_neg hdn, eq_comm, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro t _
    rintro ⟨hdvd, hpn⟩
    rw [hpn] at hdvd
    exact hdn hdvd

/-- **`multSum d` is an AP-count at residue `N` (FULL).**  Recasting through
`d ∣ (N − prod) ⟺ (prod : ZMod d) = (N : ZMod d)` (valid since `prod ≤ N/2 ≤ N`): the switched
residue-class mass is the count of admissible triples with `prod3 ≡ N (mod d)` — the class the
bilinear engine reads (unit-restricted for `d ∣ Ps` via `gold_prod_isUnit_of_residue_N`).
Mirrors `switchSieve_multSum_eq_apCount` (`2 ↦ N`). -/
theorem goldSwitchSieve_multSum_eq_apCount (N z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    (goldSwitchSieve N z y Ps hPs hPodd).multSum d
      = (((goldTripleSet N z y).filter
            (fun t => ((prod3 t : ℕ) : ZMod d) = ((N : ℕ) : ZMod d))).card : ℝ) := by
  classical
  rw [goldSwitchSieve_multSum_eq_dvdCount, Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [goldTripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := ht
  have hpN : prod3 t ≤ N := by omega
  constructor
  · intro hdvd
    have hz0 : ((N - prod3 t : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpN, sub_eq_zero] at hz0
    exact hz0.symm
  · intro hcong
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    rw [Nat.cast_sub hpN, sub_eq_zero]
    exact hcong.symm

/-! ## Part C — the semiprime-block indicator `α` with `‖α‖ ≤ 1` -/

open Classical in
/-- **The semiprime-block indicator** `α(m) = [m = p₁·p₂, z ≤ p₁ ≤ y < p₂, both prime]` — the
`m`-side coefficient of the bilinear split `prod = (p₁p₂)·p₃`.  N-independent: reused verbatim
from the twin `semiprimeBlockInd` shape (the block window is the same). -/
noncomputable def goldSemiprimeBlockInd (z y m : ℕ) : ℂ :=
  if (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₁ * p₂ = m) then 1 else 0

/-- **`‖α‖ ≤ 1`.**  The semiprime-block indicator is `0/1`-valued. -/
theorem norm_goldSemiprimeBlockInd_le_one (z y m : ℕ) : ‖goldSemiprimeBlockInd z y m‖ ≤ 1 := by
  unfold goldSemiprimeBlockInd
  split_ifs <;> simp

/-! ## Part D — the honest per-`d` remainder split + the composition scaffold -/

open Classical in
/-- **`goldSwitchResCount`** — the admissible triples with `prod ≡ N (mod d)` (`= multSum d`). -/
noncomputable def goldSwitchResCount (N z y d : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter
      (fun t => ((prod3 t : ℕ) : ZMod d) = ((N : ℕ) : ZMod d))).card : ℝ)

open Classical in
/-- **`goldSwitchUnitCount`** — the admissible triples whose product is a UNIT mod `d`. -/
noncomputable def goldSwitchUnitCount (N z y d : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter (fun t => IsUnit ((prod3 t : ℕ) : ZMod d))).card : ℝ)

open Classical in
/-- **`goldSwitchNonUnitCount`** — the admissible triples whose product is NOT coprime to `d`. -/
noncomputable def goldSwitchNonUnitCount (N z y d : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter (fun t => ¬ IsUnit ((prod3 t : ℕ) : ZMod d))).card : ℝ)

/-- `totalMass` splits into the coprime and non-coprime triple counts. -/
theorem goldSwitchUnit_add_switchNonUnit (N z y d : ℕ) :
    goldSwitchUnitCount N z y d + goldSwitchNonUnitCount N z y d = goldTripleSum N z y := by
  classical
  unfold goldSwitchUnitCount goldSwitchNonUnitCount
  rw [goldTripleSum_eq_card, ← Nat.cast_add]
  congr 1
  exact Finset.card_filter_add_card_filter_not
    (s := goldTripleSet N z y) (p := fun t => IsUnit ((prod3 t : ℕ) : ZMod d))

/-- **The honest per-`d` remainder split (FULL).**
`rem d = (resCount − ν·unitCount) − ν·nonUnitCount`.  Mirrors `switchSieve_rem_split`. -/
theorem goldSwitchSieve_rem_split (N z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    (goldSwitchSieve N z y Ps hPs hPodd).rem d
      = (goldSwitchResCount N z y d - nuChen d * goldSwitchUnitCount N z y d)
        - nuChen d * goldSwitchNonUnitCount N z y d := by
  rw [BoundingSieve.rem, goldSwitchSieve_nu, goldSwitchSieve_totalMass,
    ← goldSwitchUnit_add_switchNonUnit N z y d]
  have hM : (goldSwitchSieve N z y Ps hPs hPodd).multSum d = goldSwitchResCount N z y d :=
    goldSwitchSieve_multSum_eq_apCount N z y Ps hPs hPodd d
  rw [hM]
  ring

/-- **The per-`d` bridge bound (FULL).**  `|rem d| ≤ |resCount − ν·unitCount| + ν·nonUnitCount`.
Mirrors `switchSieve_abs_rem_le`. -/
theorem goldSwitchSieve_abs_rem_le (N z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    |(goldSwitchSieve N z y Ps hPs hPodd).rem d|
      ≤ |goldSwitchResCount N z y d - nuChen d * goldSwitchUnitCount N z y d|
        + nuChen d * goldSwitchNonUnitCount N z y d := by
  have hconv : 0 ≤ nuChen d * goldSwitchNonUnitCount N z y d := by
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · unfold goldSwitchNonUnitCount; positivity
  rw [goldSwitchSieve_rem_split]
  have h := abs_sub (goldSwitchResCount N z y d - nuChen d * goldSwitchUnitCount N z y d)
      (nuChen d * goldSwitchNonUnitCount N z y d)
  rwa [abs_of_nonneg hconv] at h

/-- The honest residue-class discrepancy against the coprime main term. -/
noncomputable def goldSwitchHonestDisc (N z y d : ℕ) : ℝ :=
  goldSwitchResCount N z y d - nuChen d * goldSwitchUnitCount N z y d

/-- The conversion error `ν(d)·(non-coprime triple count)`. -/
noncomputable def goldSwitchConvErr (N z y d : ℕ) : ℝ :=
  nuChen d * goldSwitchNonUnitCount N z y d

/-- **The summed L¹ reduction (FULL).**  Mirrors `switchSieve_rosserRemainder_split_le`. -/
theorem goldSwitchSieve_rosserRemainder_split_le (N z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (bound : ℝ) :
    rosserRemainder (goldSwitchSieve N z y Ps hPs hPodd) bound
      ≤ (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |goldSwitchHonestDisc N z y d| else 0)
        + (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then goldSwitchConvErr N z y d else 0) := by
  rw [rosserRemainder, goldSwitchSieve_prodPrimes, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  by_cases h : (d : ℝ) < bound
  · rw [if_pos h, if_pos h, if_pos h]
    exact goldSwitchSieve_abs_rem_le N z y Ps hPs hPodd d
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

/-- **`gold_hBVswitch_of_generalBV` — the composition scaffold.**  Under the two summed bounds
`hHD` (the honest-discrepancy sum — the bilinear-engine output, `Coprime d N` FREE via
`gold_switch_coprime_N`) and `hCE` (the conversion-error sum) plus `hNum`, the switched Rosser
remainder meets the EXACT `hBVswitch` shape `gold_mainA3_of_hBVswitch` names.  Mirrors
`hBVswitch_of_generalBV`. -/
theorem gold_hBVswitch_of_generalBV (N z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (Q : ℝ) (Dlev : ℕ) {RHD RCE : ℝ}
    (hHD : (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < Q * Dlev then |goldSwitchHonestDisc N z y d| else 0) ≤ RHD)
    (hCE : (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < Q * Dlev then goldSwitchConvErr N z y d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (N : ℝ) / (Real.log N) ^ 10) :
    rosserRemainder (goldSwitchSieve N z y Ps hPs hPodd) (Q * Dlev)
      ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  refine le_trans (goldSwitchSieve_rosserRemainder_split_le N z y Ps hPs hPodd (Q * Dlev)) ?_
  linarith [hHD, hCE, hNum]

/-! ## Part E — the AggCE conversion-error crumb (N-free per the gate) -/

/-- **`gold_nonunit_forces_fst_dvd` — the finding-5 prime forcing.**  A block triple whose product
is non-coprime to `Q·d` has its narrow prime `p₁ = t.1` dividing `d`.  The size argument
(`p ≤ y < p₂ ≤ p₃` rules out `p₂, p₃`; `p₁ ≥ z ≥ w' >` every prime of `Q` forbids `p₁ ∣ Q`) is
N-free — mirrors `Salt.Chen.nonunit_forces_fst_dvd` at `goldTripleSet`. -/
theorem gold_nonunit_forces_fst_dvd {N z y Q Ps w' d : ℕ}
    (hQ1 : 1 ≤ Q)
    (hQfac : ∀ p ∈ Q.primeFactors, p < w') (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hw'z : w' ≤ z) (hd : d ∈ Nat.divisors Ps)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ goldTripleSet N z y)
    (hnu : ¬ IsUnit ((prod3 t : ℕ) : ZMod (Q * d))) :
    t.1 ∣ d := by
  obtain ⟨hdPs, hPs0⟩ := Nat.mem_divisors.mp hd
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  haveI : NeZero (Q * d) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  rw [goldTripleSet, Finset.mem_filter] at ht
  obtain ⟨_, hz_le, _, hy21, h2122, hp1, hp21, hp22, _, _⟩ := ht
  have hnc : ¬ Nat.Coprime (prod3 t) (Q * d) := fun hc =>
    hnu ((ZMod.isUnit_iff_coprime (prod3 t) (Q * d)).mpr hc)
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (show Nat.gcd (prod3 t) (Q * d) ≠ 1 from hnc)
  have hp_pt : p ∣ prod3 t := hpg.trans (Nat.gcd_dvd_left _ _)
  have hp_Qd : p ∣ Q * d := hpg.trans (Nat.gcd_dvd_right _ _)
  have hpQd : p ∣ Q ∨ p ∣ d := hp.dvd_mul.mp hp_Qd
  have hp_le_y : p ≤ y := by
    rcases hpQd with hQ | hdd
    · have : p ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hQ, by omega⟩
      have := hQfac p this
      omega
    · have : p ∈ Ps.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdd.trans hdPs, hPs0⟩
      have := hPy p this
      omega
  rw [prod3] at hp_pt
  have hp_eq_t1 : p = t.1 := by
    rcases (hp.dvd_mul.mp hp_pt) with h12 | h3
    · rcases (hp.dvd_mul.mp h12) with h1 | h2
      · exact (Nat.prime_dvd_prime_iff_eq hp hp1).mp h1
      · have := (Nat.prime_dvd_prime_iff_eq hp hp21).mp h2
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp hp22).mp h3
      omega
  rcases hpQd with hQ | hdd
  · exfalso
    have : p ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hQ, by omega⟩
    have hpw' := hQfac p this
    omega
  · rw [hp_eq_t1] at hdd
    exact hdd

/-! ## Part F — the W/block remainder identification (`rem_W d` IS the `Q·d`-discrepancy)

The Goldbach mirror of `Salt/Chen/SwitchW.lean` Part C, at the LANDED CRT residue
`crtClassG Q d N a` (`Salt/Goldbach/Residue.lean`), which fuses `N − a (mod Q)` (the
AP-membership of the paired value `N − n`) with `N (mod d)` (the switch congruence `d ∣ n`). -/

/-- **The support fold (D3).**  On the W-support the pair `(n ≡ a (mod Q), d ∣ n)` is the SINGLE
class `(N − n) ≡ crtClassG (mod Q·d)`.  The ℕ-subtraction (`N − n`) is the Goldbach friction
(the reflection saturates off the window): the fold needs `n ≤ N` and `a ≤ N` (free at the
consumer — `n ∈ twinWindow N` and `a < Q ≤ N`).  Mirrors `memClassW_iff`. -/
theorem gold_memClassG {Q d N a n : ℕ} (hQd : Nat.Coprime Q d) (hnN : n ≤ N) (haN : a ≤ N) :
    (n % Q = a % Q ∧ d ∣ n) ↔ (N - n) ≡ crtClassG Q d N a [MOD Q * d] := by
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hQd]
  constructor
  · rintro ⟨hap, hdvd⟩
    have hapQ : n ≡ a [MOD Q] := hap
    have hNmod : (N - n) ≡ (N - a) [MOD Q] := by
      have key : (N - n) + n = (N - a) + a := by omega
      have h1 : (N - n) + n ≡ (N - a) + n [MOD Q] := by
        rw [key]; exact Nat.ModEq.add_left (N - a) hapQ.symm
      exact Nat.ModEq.add_right_cancel' n h1
    have hdmod : (N - n) ≡ N [MOD d] :=
      (Nat.modEq_iff_dvd' (Nat.sub_le N n)).mpr (by rwa [Nat.sub_sub_self hnN])
    exact ⟨hNmod.trans (crtClassG_modEq_left N a hQd).symm,
      hdmod.trans (crtClassG_modEq_right N a hQd).symm⟩
  · rintro ⟨hQside, hdside⟩
    have hNmod : (N - n) ≡ (N - a) [MOD Q] := hQside.trans (crtClassG_modEq_left N a hQd)
    have hna : a ≡ n [MOD Q] := by
      have hn' : N ≡ (N - a) + n [MOD Q] := by
        calc N = (N - n) + n := (Nat.sub_add_cancel hnN).symm
          _ ≡ (N - a) + n [MOD Q] := Nat.ModEq.add_right n hNmod
      have hcancel : (N - a) + a ≡ (N - a) + n [MOD Q] := by
        rw [Nat.sub_add_cancel haN]; exact hn'
      exact Nat.ModEq.add_left_cancel' (N - a) hcancel
    have hdside' : (N - n) ≡ N [MOD d] := hdside.trans (crtClassG_modEq_right N a hQd)
    refine ⟨hna.symm, ?_⟩
    have := (Nat.modEq_iff_dvd' (Nat.sub_le N n)).mp hdside'
    rwa [Nat.sub_sub_self hnN] at this

open Classical in
/-- **`goldBlockResCountM`** — block-`j` triples with `prod3 ≡ c (mod m)` (free modulus). -/
noncomputable def goldBlockResCountM (N z y : ℕ) (ε₀ : ℝ) (j m c : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧
        ((prod3 t : ℕ) : ZMod m) = ((c : ℕ) : ZMod m))).card : ℝ)

open Classical in
/-- **`goldBlockUnitCountM`** — block-`j` triples with `prod3` a unit mod `m`. -/
noncomputable def goldBlockUnitCountM (N z y : ℕ) (ε₀ : ℝ) (j m : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod m))).card : ℝ)

open Classical in
/-- **`goldBlockNonUnitCountM`** — block-`j` triples with `prod3` NOT coprime to `m`. -/
noncomputable def goldBlockNonUnitCountM (N z y : ℕ) (ε₀ : ℝ) (j m : ℕ) : ℝ :=
  (((goldTripleSet N z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod m))).card : ℝ)

/-- `goldBlockUnitCountM + goldBlockNonUnitCountM = goldBlockTripleSum` at every modulus. -/
theorem goldBlockUnitM_add_blockNonUnitM (N z y : ℕ) (ε₀ : ℝ) (j m : ℕ) :
    goldBlockUnitCountM N z y ε₀ j m + goldBlockNonUnitCountM N z y ε₀ j m
      = goldBlockTripleSum N z y ε₀ j := by
  classical
  unfold goldBlockUnitCountM goldBlockNonUnitCountM
  rw [goldBlockTripleSum_eq_card, ← Nat.cast_add]
  congr 1
  have hU : (goldTripleSet N z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod m))
      = (goldBlockTripleSet N z y ε₀ j).filter (fun t => IsUnit ((prod3 t : ℕ) : ZMod m)) := by
    rw [goldBlockTripleSet, Finset.filter_filter]
  have hN : (goldTripleSet N z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod m))
      = (goldBlockTripleSet N z y ε₀ j).filter
          (fun t => ¬ IsUnit ((prod3 t : ℕ) : ZMod m)) := by
    rw [goldBlockTripleSet, Finset.filter_filter]
  rw [hU, hN]
  exact Finset.card_filter_add_card_filter_not
    (s := goldBlockTripleSet N z y ε₀ j) (p := fun t => IsUnit ((prod3 t : ℕ) : ZMod m))

open Classical in
/-- **`multSum_W d` counts block triples in the CRT class mod `Q·d` (D3, FULL).**  The AP filter
FOLDS into the class via `gold_memClassG` (needs `a ≤ N`, free at the consumer), fibering the
block triples over `n = N − prod3`.  Mirrors `blockMultSumW_eq_apCount` (`2 ↦ N`, `crtClassW ↦
crtClassG`). -/
theorem goldBlockMultSumW_eq_apCount (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) (hQd : Nat.Coprime Q d) (haN : a ≤ N) :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).multSum d
      = goldBlockResCountM N z y ε₀ j (Q * d) (crtClassG Q d N a) := by
  classical
  set c := crtClassG Q d N a with hc
  rw [goldBlockSwitchSieveW_multSum, Finset.sum_filter]
  have hmerge : ∀ n ∈ twinWindow N,
      (if n % Q = a % Q then (if d ∣ n then goldBlockACount N z y ε₀ j n else 0) else 0)
        = (if (N - n) ≡ c [MOD Q * d] then goldBlockACount N z y ε₀ j n else 0) := by
    intro n hn
    rw [twinWindow, Finset.mem_Icc] at hn
    have hnN : n ≤ N := by omega
    by_cases h1 : n % Q = a % Q
    · by_cases h2 : d ∣ n
      · rw [if_pos h1, if_pos h2, if_pos ((gold_memClassG hQd hnN haN).mp ⟨h1, h2⟩)]
      · rw [if_pos h1, if_neg h2,
          if_neg (fun hcl => h2 (((gold_memClassG hQd hnN haN).mpr hcl).2))]
    · rw [if_neg h1, if_neg (fun hcl => h1 (((gold_memClassG hQd hnN haN).mpr hcl).1))]
  rw [Finset.sum_congr rfl hmerge]
  have Hmem : ∀ t ∈ (goldTripleSet N z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d]),
      N - prod3 t ∈ twinWindow N := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h := ht.1
    rw [goldTripleSet, Finset.mem_filter] at h
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := h
    rw [twinWindow, Finset.mem_Icc]; omega
  have hcard : (((goldTripleSet N z y).filter
        (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d])).card : ℝ)
      = ∑ n ∈ twinWindow N,
          if (N - n) ≡ c [MOD Q * d] then goldBlockACount N z y ε₀ j n else 0 := by
    rw [Finset.card_eq_sum_card_fiberwise Hmem, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [twinWindow, Finset.mem_Icc] at hn
    have hfib : (((goldTripleSet N z y).filter
            (fun t => blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d])).filter
            (fun t => N - prod3 t = n))
        = (goldTripleSet N z y).filter
            (fun t => (blockIdx z ε₀ t.1 = j ∧ prod3 t ≡ c [MOD Q * d])
              ∧ N - prod3 t = n) := by
      rw [Finset.filter_filter]
    rw [hfib]
    by_cases hcn : (N - n) ≡ c [MOD Q * d]
    · rw [if_pos hcn]
      unfold goldBlockACount
      rw [Nat.cast_inj]
      refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
      rw [goldTripleSet, Finset.mem_filter] at ht
      obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := ht
      constructor
      · rintro ⟨⟨hb, _⟩, hpn⟩
        exact ⟨hb, by omega⟩
      · rintro ⟨hb, hpe⟩
        refine ⟨⟨hb, ?_⟩, by omega⟩
        rw [hpe]; exact hcn
    · rw [if_neg hcn, Nat.cast_eq_zero, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro t ht
      rintro ⟨⟨_, hcl⟩, hpn⟩
      rw [goldTripleSet, Finset.mem_filter] at ht
      obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := ht
      have hpe : prod3 t = N - n := by omega
      rw [hpe] at hcl
      exact hcn hcl
  rw [← hcard]
  unfold goldBlockResCountM
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t _ => ?_))
  constructor
  · rintro ⟨hb, hcl⟩
    exact ⟨hb, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcl⟩
  · rintro ⟨hb, hcl⟩
    exact ⟨hb, (ZMod.natCast_eq_natCast_iff _ _ _).mp hcl⟩

/-- **The W honest per-`d` discrepancy at modulus `Q·d`** (the C4-windowed-chain target). -/
noncomputable def goldBlockHonestDiscW (N z y : ℕ) (ε₀ : ℝ) (j Q a d : ℕ) : ℝ :=
  goldBlockResCountM N z y ε₀ j (Q * d) (crtClassG Q d N a)
    - nuChen (Q * d) * goldBlockUnitCountM N z y ε₀ j (Q * d)

/-- **The W conversion error at modulus `Q·d`** — `ν(Q·d)·(non-coprime block count)`. -/
noncomputable def goldBlockConvErrW (N z y : ℕ) (ε₀ : ℝ) (j Q d : ℕ) : ℝ :=
  nuChen (Q * d) * goldBlockNonUnitCountM N z y ε₀ j (Q * d)

/-- **The honest W remainder split (D3 + C3, FULL).**  `rem_W d` is EXACTLY the landed split
shape at the shifted modulus (`ν(d)·(goldBlockTripleSum/φ(Q)) = ν(Q·d)·goldBlockTripleSum` by
multiplicativity).  Mirrors `blockSwitchSieveW_rem_split`. -/
theorem goldBlockSwitchSieveW_rem_split (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (d : ℕ) (hQd : Nat.Coprime Q d) (haN : a ≤ N) :
    (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).rem d
      = (goldBlockResCountM N z y ε₀ j (Q * d) (crtClassG Q d N a)
          - nuChen (Q * d) * goldBlockUnitCountM N z y ε₀ j (Q * d))
        - nuChen (Q * d) * goldBlockNonUnitCountM N z y ε₀ j (Q * d) := by
  have hmul : nuChen (Q * d) = nuChen Q * nuChen d := nuChen_mult.map_mul_of_coprime hQd
  rw [BoundingSieve.rem, goldBlockSwitchSieveW_nu, goldBlockSwitchSieveW_totalMass,
    goldBlockMultSumW_eq_apCount N z y ε₀ j Q a Ps hPs hPodd d hQd haN,
    ← goldBlockUnitM_add_blockNonUnitM N z y ε₀ j (Q * d), hmul, nuChen_apply Q]
  ring

/-- **The per-`d` W bridge bound.**  `|rem_W d| ≤ |goldBlockHonestDiscW| + goldBlockConvErrW`.
Mirrors `blockSwitchSieveW_abs_rem_le`. -/
theorem goldBlockSwitchSieveW_abs_rem_le (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (d : ℕ) (hQd : Nat.Coprime Q d) (haN : a ≤ N) :
    |(goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd).rem d|
      ≤ |goldBlockHonestDiscW N z y ε₀ j Q a d| + goldBlockConvErrW N z y ε₀ j Q d := by
  have hconv : 0 ≤ nuChen (Q * d) * goldBlockNonUnitCountM N z y ε₀ j (Q * d) := by
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · unfold goldBlockNonUnitCountM; positivity
  rw [goldBlockSwitchSieveW_rem_split N z y ε₀ j Q a Ps hPs hPodd d hQd haN]
  have h := abs_sub (goldBlockResCountM N z y ε₀ j (Q * d) (crtClassG Q d N a)
      - nuChen (Q * d) * goldBlockUnitCountM N z y ε₀ j (Q * d))
      (nuChen (Q * d) * goldBlockNonUnitCountM N z y ε₀ j (Q * d))
  rw [abs_of_nonneg hconv] at h
  exact h

/-- **The summed L¹ reduction of the W block Rosser remainder.**  Per `d ∣ Ps` the coprimality
`gcd(Q, d) = 1` comes from `hQPs`.  Mirrors `blockRemW_rosserRemainder_split_le`. -/
theorem goldBlockRemW_rosserRemainder_split_le (N z y : ℕ) (ε₀ : ℝ) (j Q a Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hQPs : Nat.Coprime Q Ps) (haN : a ≤ N) (bound : ℝ) :
    rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd) bound
      ≤ (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then |goldBlockHonestDiscW N z y ε₀ j Q a d| else 0)
        + (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then goldBlockConvErrW N z y ε₀ j Q d else 0) := by
  rw [rosserRemainder, goldBlockSwitchSieveW_prodPrimes, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hQd : Nat.Coprime Q d := hQPs.coprime_dvd_right (Nat.mem_divisors.mp hd).1
  by_cases h : (d : ℝ) < bound
  · rw [if_pos h, if_pos h, if_pos h]
    exact goldBlockSwitchSieveW_abs_rem_le N z y ε₀ j Q a Ps hPs hPodd d hQd haN
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

/-- **The block sum of the W L¹ reductions.**  Mirrors `sum_blockRemW_split_le`. -/
theorem gold_sum_blockRemW_split_le (N z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps) (haN : a ≤ N) (bound : ℝ) :
    (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
        rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd) bound)
      ≤ (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
            ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then |goldBlockHonestDiscW N z y ε₀ j Q a d| else 0)
        + (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
            ∑ d ∈ Nat.divisors Ps,
              if (d : ℝ) < bound then goldBlockConvErrW N z y ε₀ j Q d else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact goldBlockRemW_rosserRemainder_split_le N z y ε₀ j Q a Ps hPs hPodd hQPs haN bound

/-- **`gold_hBVblocksW_of_generalBV` — the composed W block-remainder close.**  Under the two
summed NAMED bounds `hHD_W` (the honest-discrepancy double sum — the C4-windowed-chain output at
the Q-shifted moduli `Q·d`, residues `crtClassG Q d N a`) and `hCE` plus `hNum`, the W block
Rosser remainders sum below `N/(log N)^10` — the exact `hBVblocksW` slot.  Mirrors
`hBVblocksW_of_generalBV`. -/
theorem gold_hBVblocksW_of_generalBV (N z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps) (haN : a ≤ N)
    (QR : ℝ) (Dlev : ℕ) {RHD RCE : ℝ}
    (hHD : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < QR * Dlev then |goldBlockHonestDiscW N z y ε₀ j Q a d| else 0) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
          ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < QR * Dlev then goldBlockConvErrW N z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (N : ℝ) / (Real.log N) ^ 10) :
    (∑ j ∈ Finset.range (maxBlock N z ε₀ + 1),
        rosserRemainder (goldBlockSwitchSieveW N z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  refine le_trans (gold_sum_blockRemW_split_le N z y ε₀ Q a Ps hPs hPodd hQPs haN (QR * Dlev)) ?_
  linarith [hHD, hCE, hNum]

/-! ## Part G — the AggCE crumb at the operating point (`hCE_at_op`, N-free per the gate) -/

/-- **`gold_hCE_at_op` — the `goldBlockConvErrW` conversion-error crumb (node HCE).**  At the
operating point `ε₀ := N` (single block, `maxBlock_op_eq_zero`) the `hCE` double sum is bounded by
the finding-5 product `ν(Q)·(Σ_{d∣Ps} ν(d))·goldTripleSum / (z − 1)`.  Route: the finding-5
forcing `gold_nonunit_forces_fst_dvd` caps each `d`-crumb by `ν(Q)·ν(d)·#{t : p₁ ∣ d}`; Fubini
over triples + `nuChen_sum_dvd_le` (reused, N-free) + `ν(p₁) ≤ 1/(z−1)` gives the bound.  Mirrors
`Salt.Chen.hCE_at_op`. -/
theorem gold_hCE_at_op (N z y Q Ps w' : ℕ) (QR : ℝ) (Dlev : ℕ)
    (hPs : Squarefree Ps) (hz2 : 2 ≤ z) (hN2 : 2 ≤ N) (hQ1 : 1 ≤ Q)
    (hQPs : Nat.Coprime Q Ps) (hQfac : ∀ p ∈ Q.primeFactors, p < w')
    (hPy : ∀ p ∈ Ps.primeFactors, p < y) (hw'z : w' ≤ z) :
    (∑ j ∈ Finset.range (maxBlock N z (N : ℝ) + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then goldBlockConvErrW N z y (N : ℝ) j Q d else 0)
      ≤ nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * goldTripleSum N z y / ((z : ℝ) - 1) := by
  classical
  have hnn : ∀ d : ℕ, 0 ≤ nuChen d := fun d => by rw [nuChen_apply]; positivity
  have hconv_nn : ∀ d, 0 ≤ goldBlockConvErrW N z y (N : ℝ) 0 Q d := by
    intro d
    unfold goldBlockConvErrW goldBlockNonUnitCountM
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · positivity
  have hnu_t1 : ∀ t ∈ goldTripleSet N z y, nuChen t.1 ≤ 1 / ((z : ℝ) - 1) := by
    intro t ht
    rw [goldTripleSet, Finset.mem_filter] at ht
    obtain ⟨_, hz_le, _, _, _, hp1, _, _, _, _⟩ := ht
    rw [nuChen_prime hp1]
    have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz2
    have ht1R : (z : ℝ) ≤ t.1 := by exact_mod_cast hz_le
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hbcd : ∀ d ∈ Nat.divisors Ps,
      goldBlockConvErrW N z y (N : ℝ) 0 Q d
        ≤ nuChen Q * nuChen d * (((goldTripleSet N z y).filter (fun t => t.1 ∣ d)).card : ℝ) := by
    intro d hd
    have hcopQd : Nat.Coprime Q d := hQPs.coprime_dvd_right (Nat.mem_divisors.mp hd).1
    have hmul : nuChen (Q * d) = nuChen Q * nuChen d := nuChen_mult.map_mul_of_coprime hcopQd
    unfold goldBlockConvErrW goldBlockNonUnitCountM
    rw [hmul]
    have hsub : (goldTripleSet N z y).filter
          (fun t => blockIdx z (N : ℝ) t.1 = 0 ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod (Q * d)))
        ⊆ (goldTripleSet N z y).filter (fun t => t.1 ∣ d) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, gold_nonunit_forces_fst_dvd hQ1 hQfac hPy hw'z hd ht.1 ht.2.2⟩
    have hcard : (((goldTripleSet N z y).filter
          (fun t => blockIdx z (N : ℝ) t.1 = 0
            ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod (Q * d)))).card : ℝ)
        ≤ (((goldTripleSet N z y).filter (fun t => t.1 ∣ d)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact mul_le_mul_of_nonneg_left hcard (mul_nonneg (hnn Q) (hnn d))
  have hBd : ∀ d : ℕ, (((goldTripleSet N z y).filter (fun t => t.1 ∣ d)).card : ℝ)
      = ∑ t ∈ goldTripleSet N z y, (if t.1 ∣ d then (1 : ℝ) else 0) := by
    intro d
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun t _ => by by_cases h : t.1 ∣ d <;> simp [h])
  rw [maxBlock_op_eq_zero (by omega) hN2, zero_add, Finset.sum_range_one]
  calc (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < QR * Dlev
          then goldBlockConvErrW N z y (N : ℝ) 0 Q d else 0)
      ≤ ∑ d ∈ Nat.divisors Ps, goldBlockConvErrW N z y (N : ℝ) 0 Q d := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        split_ifs with h
        · exact le_refl _
        · exact hconv_nn d
    _ ≤ ∑ d ∈ Nat.divisors Ps,
          nuChen Q * nuChen d * (((goldTripleSet N z y).filter (fun t => t.1 ∣ d)).card : ℝ) :=
        Finset.sum_le_sum hbcd
    _ = nuChen Q * ∑ d ∈ Nat.divisors Ps,
          ∑ t ∈ goldTripleSet N z y, (if t.1 ∣ d then nuChen d else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [hBd d, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by by_cases h : t.1 ∣ d <;> simp [h])
    _ = nuChen Q * ∑ t ∈ goldTripleSet N z y,
          ∑ d ∈ (Nat.divisors Ps).filter (fun d => t.1 ∣ d), nuChen d := by
        rw [Finset.sum_comm]
        refine congrArg _ (Finset.sum_congr rfl (fun t _ => ?_))
        rw [Finset.sum_filter]
    _ ≤ nuChen Q * ∑ t ∈ goldTripleSet N z y, nuChen t.1 * (∑ d ∈ Nat.divisors Ps, nuChen d) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t ht => ?_)) (hnn Q)
        rw [goldTripleSet, Finset.mem_filter] at ht
        obtain ⟨_, _, _, _, _, hp1, _, _, _, _⟩ := ht
        exact nuChen_sum_dvd_le hPs hp1
    _ = nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d)
          * (∑ t ∈ goldTripleSet N z y, nuChen t.1) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d)
          * (goldTripleSum N z y / ((z : ℝ) - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (hnn Q) (Finset.sum_nonneg (fun d _ => hnn d)))
        calc ∑ t ∈ goldTripleSet N z y, nuChen t.1
            ≤ ∑ _t ∈ goldTripleSet N z y, (1 / ((z : ℝ) - 1)) :=
              Finset.sum_le_sum (fun t ht => hnu_t1 t ht)
          _ = ((goldTripleSet N z y).card : ℝ) * (1 / ((z : ℝ) - 1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = goldTripleSum N z y / ((z : ℝ) - 1) := by rw [goldTripleSum_eq_card]; ring
    _ = nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * goldTripleSum N z y / ((z : ℝ) - 1) := by
        ring

end Salt.Goldbach
