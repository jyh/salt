/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchSieve
import Salt.Chen.PerEEngine2

/-!
# SW3 — the switched remainder → bilinear discrepancy reduction

Design: `docs/blueprints/flags.md`, entries "2026-07-13 SW-A₃ RECON", "2026-07-13 SW12", and
"2026-07-13 PE1+PE2".  This is the link from SW12's NAMED `hBVswitch` to the general-BV engine
`general_BV_final'` (`PerEEngine2.lean`).

## What the switched remainder is (the per-`d` object)

`rosserRemainder (switchSieve x z y Ps hPs hPodd) (Q·Dlev)` sums `|rem d|` over `d ∣ Ps`,
`d < Q·Dlev`, where (SwitchSieve.`switchSieve_rem`)

  `rem d = multSum d − ν(d)·totalMass = (∑_{n∈window} [d∣n]·aCount n) − (1/φd)·tripleSum`.

Each `multSum d` is an **AP-count of the triple sequence at residue `2`**: since `n = prod−2`
for the products `prod = p₁p₂p₃` of admissible triples, `d ∣ n ⟺ prod ≡ 2 (mod d)`.  So

  `multSum d = #{t ∈ tripleSet : prod3 t ≡ 2 (mod d)}`  (`switchSieve_multSum_eq_apCount`).

## The route to `apDiscBilin` (the recon design)

Split each triple `t = (p₁,p₂,p₃)` as `m = p₁·p₂` (the **semiprime block**, `α` = its `0/1`
indicator, `‖α‖ ≤ 1` by unique factorization) and `p = p₃` (`β` = the interval-prime indicator
`blockPrimeInd`-shape).  The congruence `prod ≡ 2 (mod d)` becomes the bilinear `m·p ≡ 2 (mod d)`
that `apDiscBilin α β X M 2 d` measures.  Dyadically decomposing the `p₃`-range into blocks
`[N, M]`, `M ≤ 2N`, and pricing each block's `∑_d ‖apDiscBilin‖` by `general_BV_final'` (once PE3
lands its per-`e` discharge) yields the switched `rosserRemainder ≤ x/(log x)^10`.

## ODD MODULI — the recon's `R₀ = 2` warning DISSOLVES here (`switch_dvd_coprime_two`)

`general_BV_final'` fixes the residue `R₀ = 2` and requires `Coprime 2 d` at every summed
modulus.  The recon flagged the even-`d` part as needing a separate split.  **In THIS instance no
split is needed:** every `d ∣ Ps` is ODD (`hPodd` gives every prime factor of `Ps` is `≥ 3`), so
`Coprime 2 d` is FREE — exactly the way `twinA1`'s even-`d` glue obligation dissolved.  And for
odd `d`, `prod ≡ 2 (mod d)` forces `gcd(prod, d) = 1` (residue `2` is a unit mod an odd `d`), so
the residue-class count only sees products coprime to `d` — matching the `apDiscBilin` unit
main term.

## Status of this file (honest floor)

FULLY PROVEN (Floor A + the odd-moduli resolution + the honest per-`d` split + the composition
scaffold):
* `switch_dvd_coprime_two` — the odd-moduli dissolution;
* `switchSieve_multSum_eq_dvdCount` / `switchSieve_multSum_eq_apCount` — the per-`d` AP-count
  reformulation (the congruence identity, the load-bearing bridge input);
* `two_isUnit_of_dvd` / `prod_isUnit_of_residue_two` — residue `2` is a unit / the residue-class
  count is coprime-restricted for odd `d`;
* `semiprimeBlockInd` + `norm_semiprimeBlockInd_le_one` — the `0/1` semiprime-block `α` with
  `‖α‖ ≤ 1`, the exact hypothesis shape `general_BV_final'` consumes;
* `switchSieve_rem_split` / `switchSieve_abs_rem_le` — the honest per-`d` split
  `rem d = (residue-class discrepancy vs the COPRIME main term) − (conversion error)` and its
  triangle bound (the bilinear analogue of `twinA1_rem_eq` / `twinA1_abs_rem_le`);
* `switchSieve_rosserRemainder_split_le` — the summed L¹ reduction of the switched Rosser
  remainder into the honest-discrepancy sum + the conversion-error sum;
* `hBVswitch_of_generalBV` — the composition scaffold reaching the exact `hBVswitch` shape SW12
  named, with the two summed bounds + the numeric closure as the three NAMED remaining
  obligations (structured for the one-line plug).

FLAGGED (the remaining Floor-B work — the honest bilinear reduction, i.e. the `hHD` obligation of
`hBVswitch_of_generalBV`): see the closing flag `docs/blueprints/flags.md`.  The clean identity
`switchHonestDisc d = ‖apDiscBilin(α,β,…)‖` does NOT hold on the nose because `apDiscBilin` carries
NO product-window coupling while `aCount` has the hard window `x/2+2 ≤ prod ≤ x`; removing that
coupling is the dyadic-block decomposition (`O(log²x)` interior boxes + boundary boxes) that turns
`∑_d |switchHonestDisc d|` into `∑_{blocks} ∑_d ‖apDiscBilin (semiprimeBlockInd z y)
(blockPrimeInd N) X M 2 d‖`, priced by `general_BV_final'` — the multi-node SW3 continuation.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the odd-moduli dissolution (`R₀ = 2` is free) -/

/-- **The switch moduli are odd.**  Every `d ∣ Ps` is coprime to `2`: if `2 ∣ d ∣ Ps` then `2`
would be a prime factor of `Ps`, contradicting `hPodd` (`3 ≤ 2`).  This is the exact
dissolution of `twinA1`'s even-`d` glue obligation, and it discharges — for free — the
`Coprime R₀ d` (`R₀ = 2`) hypothesis that `general_BV_final'` requires at every summed modulus. -/
theorem switch_dvd_coprime_two {Ps : ℕ} (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) {d : ℕ} (hd : d ∣ Ps) : Nat.Coprime 2 d := by
  refine (Nat.prime_two.coprime_iff_not_dvd).mpr (fun h2d => ?_)
  have h2Ps : (2 : ℕ) ∣ Ps := h2d.trans hd
  have hmem : (2 : ℕ) ∈ Ps.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2Ps, hPs.ne_zero⟩
  have := hPodd 2 hmem
  omega

/-! ## Part B — the per-`d` AP-count reformulation of `multSum` -/

/-- **`multSum d` counts triples with `d ∣ prod−2` (FULL).**  The switched sieve's residue-class
mass at modulus `d` equals the number of admissible triples whose product `prod = p₁p₂p₃`
satisfies `d ∣ (prod − 2)` — i.e. `n = prod − 2` lands in the divisibility class the sieve tests.
Proved by fibering `tripleSet` over `n = prod3 t − 2` (every triple has `prod−2 ∈ window`, as in
`tripleSum_eq_card`) and matching the per-`n` fibre against `aCount`. -/
theorem switchSieve_multSum_eq_dvdCount (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    (switchSieve x z y Ps hPs hPodd).multSum d
      = (((tripleSet x z y).filter (fun t => d ∣ (prod3 t - 2))).card : ℝ) := by
  classical
  rw [switchSieve_multSum]
  -- Fibre the filtered triple set over `n = prod3 t − 2 ∈ twinWindow x`.
  have Hmem : ∀ t ∈ (tripleSet x z y).filter (fun t => d ∣ (prod3 t - 2)),
      prod3 t - 2 ∈ twinWindow x := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h := ht.1
    rw [tripleSet, Finset.mem_filter] at h
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := h
    rw [twinWindow, Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise Hmem, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  -- The fibre over `n` combines the two filters (`Finset.filter_filter`).
  have hfib : (((tripleSet x z y).filter (fun t => d ∣ (prod3 t - 2))).filter
        (fun t => prod3 t - 2 = n))
      = (tripleSet x z y).filter (fun t => d ∣ (prod3 t - 2) ∧ prod3 t - 2 = n) := by
    rw [Finset.filter_filter]
  rw [hfib]
  by_cases hdn : d ∣ n
  · -- `d ∣ n`: the fibre is exactly `{t : prod3 t = n + 2}` = `aCount`'s support.
    rw [if_pos hdn]
    unfold aCount
    rw [Nat.cast_inj]
    refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
    -- `t ∈ tripleSet ⟹ prod3 t ≥ 2`, so `prod−2 = n ⟺ prod = n+2`, and then `d ∣ (prod−2) = d ∣ n`.
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
    constructor
    · intro hpe
      refine ⟨?_, by omega⟩
      have hn : prod3 t - 2 = n := by omega
      rw [hn]; exact hdn
    · rintro ⟨_, hpn⟩; omega
  · -- `¬ d ∣ n`: the fibre is empty (any triple in it would force `d ∣ n`).
    rw [if_neg hdn, eq_comm, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro t _
    rintro ⟨hdvd, hpn⟩
    rw [hpn] at hdvd
    exact hdn hdvd

/-- **`multSum d` is an AP-count at residue `2` (FULL).**  Recasting
`switchSieve_multSum_eq_dvdCount` through `d ∣ (prod − 2) ⟺ (prod : ZMod d) = (2 : ZMod d)`
(valid since every admissible product is `≥ 2`): the switched sieve's residue-class mass is the
count of admissible triples with `prod3 t ≡ 2 (mod d)`.  This is the exact congruence the
bilinear `apDiscBilin α β X M 2 d` measures once `prod = p₁p₂·p₃` is split. -/
theorem switchSieve_multSum_eq_apCount (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    (switchSieve x z y Ps hPs hPodd).multSum d
      = (((tripleSet x z y).filter
            (fun t => ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))).card : ℝ) := by
  classical
  rw [switchSieve_multSum_eq_dvdCount, Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  -- On `tripleSet`, `prod3 t ≥ x/2 + 2 ≥ 2`, so `(prod3 t − 2 : ZMod d) = (prod3 t) − 2`.
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
  have hp2 : 2 ≤ prod3 t := by omega
  constructor
  · intro hdvd
    have : ((prod3 t - 2 : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hp2, sub_eq_zero] at this
    exact this
  · intro hcong
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    rw [Nat.cast_sub hp2, sub_eq_zero]
    exact hcong

/-! ## Part C — residue `2` is a unit mod odd `d` (the coprime-restriction match) -/

/-- **`2` is a unit mod an odd modulus.**  For `d ∣ Ps` (hence coprime to `2`, `switch_dvd_
coprime_two`), `(2 : ZMod d)` is a unit.  Together with `switchSieve_multSum_eq_apCount` this
says the switched residue-class count `multSum d` only registers products `prod ≡ 2 (mod d)` that
are automatically coprime to `d` — matching the *unit-restricted* main term of `apDiscBilin`. -/
theorem two_isUnit_of_dvd {Ps : ℕ} (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) {d : ℕ} (hd : d ∣ Ps) :
    IsUnit ((2 : ℕ) : ZMod d) :=
  (ZMod.isUnit_iff_coprime 2 d).mpr (switch_dvd_coprime_two hPs hPodd hd)

/-- **A residue-`2` product is coprime to an odd `d`.**  If `(prod : ZMod d) = (2 : ZMod d)` and
`d ∣ Ps` (odd), then `(prod : ZMod d)` is a unit: the residue-`2` class is the unit class.  This
is the bilinear analogue of `twinA1`'s "`d − 2` is a reduced residue" (`coprime_sub_two`) — it is
why no non-coprime products enter the switched residue-class count. -/
theorem prod_isUnit_of_residue_two {Ps : ℕ} (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) {d prod : ℕ} (hd : d ∣ Ps)
    (hres : ((prod : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d)) : IsUnit ((prod : ℕ) : ZMod d) := by
  rw [hres]; exact two_isUnit_of_dvd hPs hPodd hd

/-! ## Part D — the semiprime-block indicator `α` with `‖α‖ ≤ 1` -/

open Classical in
/-- **The semiprime-block indicator** `α(m) = [m = p₁·p₂, z ≤ p₁ ≤ y < p₂, both prime]`.  This is
the `m`-side coefficient of the bilinear split `prod = (p₁p₂)·p₃`: `m = p₁p₂` is the "semiprime
block".  By unique factorization the witnessing `(p₁, p₂)` is unique when it exists, so this `0/1`
indicator IS the switch multiplicity (`aCount`'s `m`-fibre) — the recon's α-multiplicity finding.
Typed `ℕ → ℂ` to feed `apDiscBilin`/`bilinTwist`/`general_BV_final'` directly. -/
noncomputable def semiprimeBlockInd (z y m : ℕ) : ℂ :=
  if (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₁ * p₂ = m) then 1 else 0

/-- **`‖α‖ ≤ 1` (FULL).**  The semiprime-block indicator is `0/1`-valued, so its norm is `≤ 1` —
the exact `hα : ∀ m, ‖α m‖ ≤ 1` hypothesis `general_BV_final'` consumes on the `m`-side. -/
theorem norm_semiprimeBlockInd_le_one (z y m : ℕ) : ‖semiprimeBlockInd z y m‖ ≤ 1 := by
  unfold semiprimeBlockInd
  split_ifs <;> simp

/-- The semiprime-block indicator is `0/1`-valued (auxiliary; the `≤ 1` bound is
`norm_semiprimeBlockInd_le_one`). -/
theorem semiprimeBlockInd_eq_zero_or_one (z y m : ℕ) :
    semiprimeBlockInd z y m = 0 ∨ semiprimeBlockInd z y m = 1 := by
  unfold semiprimeBlockInd
  split_ifs
  · right; rfl
  · left; rfl

/-! ## Part E — the honest per-`d` remainder split (discrepancy + conversion error) -/

/-- **`switchResCount`** — the admissible triples with `prod ≡ 2 (mod d)` (`= multSum d`, by
`switchSieve_multSum_eq_apCount`); the residue-class count. -/
noncomputable def switchResCount (x z y d : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))).card : ℝ)

open Classical in
/-- **`switchUnitCount`** — the admissible triples whose product is a UNIT mod `d` (coprime to
`d`); the support of `apDiscBilin`'s coprime main term. -/
noncomputable def switchUnitCount (x z y d : ℕ) : ℝ :=
  (((tripleSet x z y).filter (fun t => IsUnit ((prod3 t : ℕ) : ZMod d))).card : ℝ)

open Classical in
/-- **`switchNonUnitCount`** — the admissible triples whose product is NOT coprime to `d`; the
conversion-error support (the `ψ_{χ₀}↔ψ` analogue: products sharing a factor with `d`).  For odd
`d ∣ Ps` these are exactly the triples with `p₁ ∣ d` — bounded at `x/(log x)^10`-budget by SW4. -/
noncomputable def switchNonUnitCount (x z y d : ℕ) : ℝ :=
  (((tripleSet x z y).filter (fun t => ¬ IsUnit ((prod3 t : ℕ) : ZMod d))).card : ℝ)

/-- `totalMass` splits into the coprime and non-coprime triple counts. -/
theorem switchUnit_add_switchNonUnit (x z y d : ℕ) :
    switchUnitCount x z y d + switchNonUnitCount x z y d = tripleSum x z y := by
  classical
  unfold switchUnitCount switchNonUnitCount
  rw [tripleSum_eq_card, ← Nat.cast_add]
  congr 1
  exact Finset.card_filter_add_card_filter_not
    (s := tripleSet x z y) (p := fun t => IsUnit ((prod3 t : ℕ) : ZMod d))

/-- **The honest per-`d` remainder split (FULL).**  The switched AP-remainder decomposes as

  `rem d = (switchResCount − ν(d)·switchUnitCount) − ν(d)·switchNonUnitCount`,

i.e. `(honest residue-class discrepancy against the COPRIME main term) − (conversion error)`.
The first bracket is what the dyadic decomposition turns into `∑_{blocks} ‖apDiscBilin‖` (whose
main term is the coprime/unit mass, matching `switchUnitCount`); the second is the conversion
error (`twinA1`'s `ω(d)·log/φ(d)` analogue).  This is the bilinear counterpart of
`twinA1_rem_eq`. -/
theorem switchSieve_rem_split (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    (switchSieve x z y Ps hPs hPodd).rem d
      = (switchResCount x z y d - nuChen d * switchUnitCount x z y d)
        - nuChen d * switchNonUnitCount x z y d := by
  rw [BoundingSieve.rem, switchSieve_nu, switchSieve_totalMass,
    ← switchUnit_add_switchNonUnit x z y d]
  have hM : (switchSieve x z y Ps hPs hPodd).multSum d = switchResCount x z y d :=
    switchSieve_multSum_eq_apCount x z y Ps hPs hPodd d
  rw [hM]
  ring

/-- **The per-`d` bridge bound (FULL).**  `|rem d| ≤ (honest discrepancy) + (conversion error)`,
the triangle inequality on `switchSieve_rem_split` (the conversion error is `≥ 0`).  This is the
bilinear analogue of `twinA1_abs_rem_le`: summing over `d` and dyadically decomposing the honest
discrepancy into `∑_d ‖apDiscBilin‖` (priced by `general_BV_final'`) plus the conversion-error sum
gives the switched `rosserRemainder` bound. -/
theorem switchSieve_abs_rem_le (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (d : ℕ) :
    |(switchSieve x z y Ps hPs hPodd).rem d|
      ≤ |switchResCount x z y d - nuChen d * switchUnitCount x z y d|
        + nuChen d * switchNonUnitCount x z y d := by
  have hconv : 0 ≤ nuChen d * switchNonUnitCount x z y d := by
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · unfold switchNonUnitCount; positivity
  rw [switchSieve_rem_split]
  have h := abs_sub (switchResCount x z y d - nuChen d * switchUnitCount x z y d)
      (nuChen d * switchNonUnitCount x z y d)
  rwa [abs_of_nonneg hconv] at h

/-! ## Part F — the summed reduction + the composition scaffold (`hBVswitch_of_generalBV`) -/

/-- The honest residue-class discrepancy against the coprime main term (the `apDiscBilin`
target after dyadic decomposition). -/
noncomputable def switchHonestDisc (x z y d : ℕ) : ℝ :=
  switchResCount x z y d - nuChen d * switchUnitCount x z y d

/-- The conversion error `ν(d)·(non-coprime triple count)` (the `twinA1` `ω(d)·log/φ(d)`
analogue). -/
noncomputable def switchConvErr (x z y d : ℕ) : ℝ :=
  nuChen d * switchNonUnitCount x z y d

/-- **The summed reduction (FULL).**  The switched Rosser remainder at any level `bound` is
bounded by the summed honest discrepancy plus the summed conversion error:

  `rosserRemainder (switchSieve …) bound`
    `≤ ∑_{d∣Ps, d<bound} |switchHonestDisc d| + ∑_{d∣Ps, d<bound} switchConvErr d`.

Termwise `switchSieve_abs_rem_le`, then `Finset.sum_add_distrib`.  This is the switched analogue
of `twinA1`'s `(39)` L¹ reduction: the first sum is what the dyadic decomposition prices against
`general_BV_final'` (`∑_d ‖apDiscBilin (semiprimeBlockInd z y) (blockPrimeInd N) X M 2 d‖` over
the `O(log²x)` interior blocks); the second is the crude-bounded conversion error (SW4). -/
theorem switchSieve_rosserRemainder_split_le (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (bound : ℝ) :
    rosserRemainder (switchSieve x z y Ps hPs hPodd) bound
      ≤ (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then |switchHonestDisc x z y d| else 0)
        + (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then switchConvErr x z y d else 0) := by
  rw [rosserRemainder, switchSieve_prodPrimes, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  by_cases h : (d : ℝ) < bound
  · rw [if_pos h, if_pos h, if_pos h]
    exact switchSieve_abs_rem_le x z y Ps hPs hPodd d
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

/-- **`hBVswitch_of_generalBV` — the composition scaffold (structured for the one-line plug).**
Under the two summed bounds — `hHD` (the dyadic-reduced honest-discrepancy sum, the SW3
continuation's output through `general_BV_final'`) and `hCE` (the conversion-error sum, SW4's
crude bound) — plus the numeric closure `hNum` (SW4's row: the two envelopes clear the
`x/(log x)^10` budget), the switched Rosser remainder meets the EXACT `hBVswitch` shape SW12
named.  Composes `switchSieve_rosserRemainder_split_le` with the three named obligations.

What remains NAMED (the honest split of the remaining work):
* `hHD` — bound the honest-discrepancy sum by dyadically decomposing each `switchHonestDisc d`
  into `∑_{blocks} ‖apDiscBilin (semiprimeBlockInd z y) (blockPrimeInd N) X M 2 d‖` (the interior
  boxes have the product-window coupling removed) and pricing each block by `general_BV_final'`
  (once PE3 discharges its per-`e` slot; `Coprime 2 d` is FREE via `switch_dvd_coprime_two`);
* `hCE` — the conversion error is `∑_d ν(d)·#{triples : p₁ ∣ d}`, crude-bounded (SW4);
* `hNum` — the numeric row (SW4, with SS3c's `Fchain` values).  The `x/(log x)^10` budget is
  generous (the S4 ledger row). -/
theorem hBVswitch_of_generalBV (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (Q : ℝ) (Dlev : ℕ) {RHD RCE : ℝ}
    (hHD : (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < Q * Dlev then |switchHonestDisc x z y d| else 0)
        ≤ RHD)
    (hCE : (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < Q * Dlev then switchConvErr x z y d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    rosserRemainder (switchSieve x z y Ps hPs hPodd) (Q * Dlev)
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  refine le_trans (switchSieve_rosserRemainder_split_le x z y Ps hPs hPodd (Q * Dlev)) ?_
  linarith [hHD, hCE, hNum]

end Salt.Chen
