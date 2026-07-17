/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# GB-7 (+ GB-8/GB-10) — the `hpt` assembly (the rebuild's final pole)

Compose the abstract Selberg upper bound (`Salt.SelbergPort.selberg_bound_simple`)
at the gold instance (`goldSelbergSieve`) into the `hpt` residual of
`W3_AE_d_of_sieve` (`Salt/Entropy/Chowla/QuadrupleCount.lean`), i.e. the pointwise
representation-count majorant
`r(n) ≤ if Even n then C₁·(ε²H/log²H)·sTrunc2 n else 0`.

The assembly splits, per the GB-0 parity freeze
(`docs/exploration/s3-a3-design.md`), into:

* **the odd branch** (`repCount_eq_zero_of_window_odd`): when every window prime is
  odd (which holds once `4 ≤ ε²H`, `primeWindow_odd_of_four_le`), an odd target `n`
  has no representation `p + q = n` (odd + odd = even), so `repCount = 0`;
* **the even branch** (`goldSiftedSum_le_main_add_err`): the Selberg sieve at the
  gold instance, `repCount ≤ siftedSum ≤ n·sTrunc2 n/(c₀ log²z) + errSum` with the
  error sum bounded, twin-track style (`goldErrSum_le`, mirroring `M2.N4_2`), by
  `(z²+1)⁴`.

All numeric constants are symbolic (`c₀`, `C₁`); the twin template is
`Salt/Brun/M5Assembly.lean`.
-/

import Mathlib
import Salt.Entropy.Chowla.GoldbachEnergyGc
import Salt.Entropy.Chowla.GoldbachEnergySieve
import Salt.Brun.M5Assembly

open ArithmeticFunction Finset

namespace Salt.Entropy.Chowla

/-! ## The odd branch: `repCount = 0` for odd `n` with an odd window -/

/-- Once `4 ≤ ε²H`, every window prime `p` satisfies `p > ε²H/2 ≥ 2`, hence `p ≥ 3`
is an odd prime.  (For smaller `ε²H` the window can contain `2`; that regime is the
source of the ungated-`hpt` mismatch flagged in the module note.) -/
lemma primeWindow_odd_of_four_le {eps : ℚ} {H p : ℕ} (hH : 4 ≤ eps ^ 2 * (H : ℚ))
    (hp : p ∈ primeWindow eps H) : Odd p := by
  have hmem := mem_primeWindow.mp hp
  have hpp : p.Prime := hmem.2.1
  have hlt : eps ^ 2 * (H : ℚ) / 2 < (p : ℚ) := hmem.2.2
  have h2 : (2 : ℚ) < (p : ℚ) := by linarith
  have hp2 : 2 < p := by exact_mod_cast h2
  exact hpp.odd_of_ne_two (by omega)

/-- **The odd branch (GB-8).**  If every window prime is odd, an odd target `n` has
`repCount = 0`: a representation `p + q = n` would need `p + q` odd, impossible for
two odd primes. -/
lemma repCount_eq_zero_of_window_odd {eps : ℚ} {H n : ℕ}
    (hwin : ∀ p ∈ primeWindow eps H, Odd p) (hn : Odd n) :
    repCount (primeWindow eps H) (primeWindow eps H) n = 0 := by
  rw [repCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨p, q⟩ hpq
  rw [Finset.mem_product] at hpq
  have hpo : Odd p := hwin p hpq.1
  have hqo : Odd q := hwin q hpq.2
  have hsum : Even (p + q) := hpo.add_odd hqo
  simp only []
  intro heq
  rw [heq] at hsum
  exact (Nat.not_even_iff_odd.mpr hn) hsum

/-! ## The error sum (GB-10), twin-track style (mirror `M2.N4_2`) -/

/-- **The gold error sum bound.**  The `selberg_bound_simple` error term for the
gold sieve at `level = z²` is `≤ (z²+1)⁴`.  Route: `|rem d| ≤ ρ_n(d) ≤ 2^ω(d)`
(`goldEnergySieve_abs_rem_le`, `rhoG_squarefree_le`), so each guarded summand is
`≤ 3^ω(d)·2^ω(d) = 6^ω(d) ≤ d³` (`six_pow_omega_le_d_cubed`), then the crude
`Σ_{d ≤ z²} d³ ≤ (z²+1)⁴` (`sum_cube_le_pow4`). -/
lemma goldErrSum_le (n P : ℕ) (hn : 2 ∣ n) (hP : Squarefree P) (z : ℕ) :
    (∑ d ∈ P.divisors, if (d : ℝ) ≤ (z : ℝ) ^ 2 then
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d)
          * |(goldEnergySieve n P hn hP).rem d| else 0)
      ≤ ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := by
  classical
  calc ∑ d ∈ P.divisors, (if (d : ℝ) ≤ (z : ℝ) ^ 2 then
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d)
            * |(goldEnergySieve n P hn hP).rem d| else 0)
      ≤ ∑ d ∈ P.divisors, (if (d : ℝ) ≤ (z : ℝ) ^ 2 then (d : ℝ) ^ 3 else 0) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hdvd : d ∣ P := (Nat.mem_divisors.mp hd).1
        have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
        have hsq : Squarefree d := hP.squarefree_of_dvd hdvd
        split_ifs with h
        · have hk : ArithmeticFunction.cardDistinctFactors d = omega d :=
            (Salt.M5Assembly.omega_eq_cardDistinctFactors d).symm
          rw [hk]
          have h1 : |(goldEnergySieve n P hn hP).rem d| ≤ (rhoG n d : ℝ) :=
            goldEnergySieve_abs_rem_le d hd0
          have h2 : (rhoG n d : ℝ) ≤ (2 : ℝ) ^ omega d := by
            exact_mod_cast rhoG_squarefree_le n d hsq
          calc (3 : ℝ) ^ omega d * |(goldEnergySieve n P hn hP).rem d|
              ≤ (3 : ℝ) ^ omega d * (rhoG n d : ℝ) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ ≤ (3 : ℝ) ^ omega d * (2 : ℝ) ^ omega d :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = (6 : ℝ) ^ omega d := by rw [← mul_pow]; norm_num
            _ ≤ (d : ℝ) ^ 3 := by exact_mod_cast six_pow_omega_le_d_cubed hsq
        · exact le_rfl
    _ ≤ ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := by
        have hfe : ∑ d ∈ P.divisors, (if (d : ℝ) ≤ (z : ℝ) ^ 2 then (d : ℝ) ^ 3 else 0)
            = ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z : ℝ) ^ 2), (d : ℝ) ^ 3 :=
          (Finset.sum_filter _ _).symm
        rw [hfe]
        have hsub : P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z : ℝ) ^ 2)
            ⊆ Finset.range (z ^ 2 + 1) := by
          intro d hd
          rw [Finset.mem_filter] at hd
          rw [Finset.mem_range]
          have hle : d ≤ z ^ 2 := by
            have h2 := hd.2
            rw [show ((z : ℝ) ^ 2) = ((z ^ 2 : ℕ) : ℝ) by push_cast; ring] at h2
            exact_mod_cast h2
          omega
        calc ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z : ℝ) ^ 2), (d : ℝ) ^ 3
            ≤ ∑ d ∈ Finset.range (z ^ 2 + 1), (d : ℝ) ^ 3 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ = ((∑ d ∈ Finset.range (z ^ 2 + 1), d ^ 3 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast sum_cube_le_pow4 (z ^ 2 + 1)

/-! ## The sieve seam (GB-7 pole): `repCount ≤ main + error` for even `n` -/

/-- **The GB-7 pole.**  For even `n ≥ 1` and admissible sieve parameters
`(z, P, level = z²)` — `P` squarefree with all primes `≤ z`, window primes `> z`,
and the composed denominator lower bound `hbound` (from
`goldSelbergBoundingSum_ge_log_sq_div_sTrunc2`) — the ordered representation count
is bounded by the Selberg main term plus the error:
`repCount ≤ n·sTrunc2 n/(c₀ log²z) + (z²+1)⁴`.

Composition: `repCount ≤ siftedSum` (`repCount_le_siftedSum`, GB-9) `≤
totalMass/selbergBoundingSum + errSum` (`selberg_bound_simple`), then the mass term
via `hbound` and the error via `goldErrSum_le` (GB-10). -/
theorem goldSiftedSum_le_main_add_err (eps : ℚ) (H : ℕ) (n P : ℕ) (hn : 2 ∣ n)
    (hn0 : n ≠ 0) (hP : Squarefree P) (z : ℕ) (hz2 : 2 ≤ z)
    (hPz : ∀ q, q.Prime → q ∣ P → q ≤ z)
    (hwin : ∀ p ∈ primeWindow eps H, z < p)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (hlvl : (1 : ℝ) ≤ (z : ℝ) ^ 2)
    (hbound : c₀ * (Real.log z) ^ 2 / sTrunc2 n
        ≤ Salt.SelbergPort.selbergBoundingSum (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl)) :
    (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
      ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := by
  have hsT_pos : 0 < sTrunc2 n := sTrunc2_pos hn0
  have hlogpos : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hden_pos : 0 < c₀ * (Real.log z) ^ 2 := mul_pos hc₀ (pow_pos hlogpos 2)
  have hlower_pos : 0 < c₀ * (Real.log z) ^ 2 / sTrunc2 n := div_pos hden_pos hsT_pos
  set S := Salt.SelbergPort.selbergBoundingSum (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl)
    with hSdef
  have hSpos : 0 < S := lt_of_lt_of_le hlower_pos hbound
  -- The Selberg upper bound at the gold instance, reduced to `P`/`z²`/`goldEnergySieve.rem`.
  have hsb := Salt.SelbergPort.selberg_bound_simple
    (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl)
  simp only [goldSelbergSieve_prodPrimes, goldSelbergSieve_level, ← hSdef] at hsb
  have htm : (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl).totalMass = (n : ℝ) :=
    @goldEnergySieve_totalMass n P hn hP
  have hrem : (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl).rem
      = (goldEnergySieve n P hn hP).rem := rfl
  rw [htm, hrem] at hsb
  -- The mass term: `n / S ≤ n·sTrunc2 n / (c₀ log²z)`.
  have hmain : (n : ℝ) / S ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) := by
    rw [div_le_div_iff₀ hSpos hden_pos]
    have hb2 : c₀ * (Real.log z) ^ 2 ≤ S * sTrunc2 n := by
      rw [div_le_iff₀ hsT_pos] at hbound; exact hbound
    nlinarith [hb2, Nat.cast_nonneg (α := ℝ) n]
  calc (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
      ≤ (goldEnergySieve n P hn hP).siftedSum :=
        repCount_le_siftedSum n P hn hP eps H hPz hwin
    _ = (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl).siftedSum := rfl
    _ ≤ (n : ℝ) / S + ∑ d ∈ P.divisors, if (d : ℝ) ≤ (z : ℝ) ^ 2 then
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d)
            * |(goldEnergySieve n P hn hP).rem d| else 0 := hsb
    _ ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 :=
        add_le_add hmain (goldErrSum_le n P hn hP z)

/-! ## The uniform-in-`n` denominator bound (for a single `C₁`) -/

/-- **The bounding-sum bound with `c₀`/`z₀` uniform in `n`.**  `goldSelbergBoundingSum_
ge_log_sq_div_sTrunc2` packages the constant `c₀` *inside* the `∀ n`; but the final
`hpt` must fix a single `C₁ = O(1/c₀)` before quantifying `n`.  This lemma pulls the
absolute constant `c₀ = 1/64` (`M3Assembly.exists_const_mainTermSum_ge`) out front,
re-running the `d·m` coprime factorization chain (`mainTermSum_le_sTrunc2_mul_
coprimeSum`, `selbergTerms_eq_gTwin_of_coprime`) verbatim. -/
theorem goldBoundingSum_ge_uniform :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ z₀ : ℕ, ∀ (n P : ℕ) (hn : 2 ∣ n) (hP : Squarefree P), n ≠ 0 →
      ∀ (z : ℕ), z₀ ≤ z → ∀ (hlvl : (1 : ℝ) ≤ (z : ℝ) ^ 2),
        (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
            ⊆ P.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ (z : ℝ) ^ 2) →
        c₀ * (Real.log z) ^ 2 / sTrunc2 n
          ≤ Salt.SelbergPort.selbergBoundingSum
              (goldSelbergSieve n P hn hP ((z : ℝ) ^ 2) hlvl) := by
  obtain ⟨c₀, hc₀, z₀, hz₀⟩ := Salt.M3Assembly.exists_const_mainTermSum_ge
  refine ⟨c₀, hc₀, z₀, fun n P hn hP hn0 z hz hlvl hsub => ?_⟩
  have hcop_le :
      (∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
          (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m)
        ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
    calc (∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m)
        = ∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), (goldEnergySieve n P hn hP).selbergTerms m := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hm
          exact (selbergTerms_eq_gTwin_of_coprime m hm.1.2.1 hm.1.2.2 hm.2).symm
      _ ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ℓ hℓ _ => ?_)
          rw [Finset.mem_filter, Finset.mem_range] at hℓ
          exact goldSelbergTerms_nonneg_of_odd hℓ.2.1 hℓ.2.2
  have hcarrier : c₀ * (Real.log z) ^ 2 / sTrunc2 n
      ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          (goldEnergySieve n P hn hP).selbergTerms ℓ := by
    rw [div_le_iff₀ (sTrunc2_pos hn0)]
    calc c₀ * (Real.log z) ^ 2
        ≤ Salt.M3Assembly.mainTermSum z := hz₀ z hz
      _ ≤ sTrunc2 n * ∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m :=
          mainTermSum_le_sTrunc2_mul_coprimeSum z hn0
      _ ≤ sTrunc2 n * ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ :=
          mul_le_mul_of_nonneg_left hcop_le (sTrunc2_nonneg n)
      _ = (∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ) * sTrunc2 n := mul_comm _ _
  exact le_trans hcarrier (carrierSum_le_selbergBoundingSum ((z : ℝ) ^ 2) hlvl z hsub)

/-! ## The even branch, `P = primorial z` discharged (GB-7 packaged) -/

/-- **The even-branch representation bound at `P = primorial z`.**  Combines the pole
core (`goldSiftedSum_le_main_add_err`) with the uniform denominator bound
(`goldBoundingSum_ge_uniform`), discharging `hP`/`hPz`/`hsub`/`hbound` via
`primorial`.  What remains for GB-15: pick `z = z(H)` with `z₀ ≤ z`, `2 ≤ z`, and
`z < ` every window prime; then bound `n·sTrunc2 n/(c₀ log²z) + (z²+1)⁴` by
`C₁·(ε²H/log²H)·sTrunc2 n` using `n ≤ 2ε²H`, `log z ≍ log H`, and `(z²+1)⁴ = o(main)`
(the rpow/constant seam). -/
theorem repCount_even_le_primorial :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ z₀ : ℕ, ∀ (eps : ℚ) (H n : ℕ), 2 ∣ n → n ≠ 0 →
      ∀ (z : ℕ), z₀ ≤ z → 2 ≤ z → (∀ p ∈ primeWindow eps H, z < p) →
        (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
          ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := by
  obtain ⟨c₀, hc₀, z₀, hbnd⟩ := goldBoundingSum_ge_uniform
  refine ⟨c₀, hc₀, z₀, fun eps H n hn hn0 z hz hz2 hwin => ?_⟩
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hlvl : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by nlinarith
  have hP : Squarefree (primorial z) := Salt.M5Assembly.primorial_squarefree z
  have hPz : ∀ q, q.Prime → q ∣ primorial z → q ≤ z :=
    fun q hq hdvd => (hq.dvd_primorial_iff).mp hdvd
  have hsub : (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
      ⊆ (primorial z).divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ (z : ℝ) ^ 2) := by
    intro ℓ hℓ
    rw [Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨(Squarefree.dvd_primorial hℓsq).trans (primorial_dvd_primorial (le_of_lt hℓz)),
      hP.ne_zero⟩, ?_⟩
    have hℓR : (ℓ : ℝ) ≤ (z : ℝ) := by exact_mod_cast (le_of_lt hℓz)
    exact pow_le_pow_left₀ (Nat.cast_nonneg ℓ) hℓR 2
  have hbound := hbnd n (primorial z) hn hP hn0 z hz hlvl hsub
  exact goldSiftedSum_le_main_add_err eps H n (primorial z) hn hn0 hP z hz2 hPz hwin
    c₀ hc₀ hlvl hbound

end Salt.Entropy.Chowla

/-
## FLAG (GB-7 pole): the ungated `hpt` at the frozen `else 0` rbound is FALSE

`W3_AE_d_of_sieve` (QuadrupleCount.lean) takes `hpt : ∀ H n, repCount … n ≤ rbound H n`
UNGATED in `H`.  The GB-0 frozen rbound is `if Even n then C₁·(ε²H/log²H)·sTrunc2 n
else 0`.  For SMALL `H` (`ε²H < 4`) the window can contain `2`, so an odd target can
have a representation and `repCount > 0 = rbound`.  Concrete counterexample (verified
by `#eval`): `eps = 1`, `H = 3` gives `primeWindow 1 3 = {2, 3}`, and for the odd
target `n = 5`, `repCount {2,3} {2,3} 5 = 2 > 0 = rbound … 5`.  Hence NO `C₁` makes the
ungated `hpt` true at the frozen rbound (enlarging `C₁` cannot help the `else 0`
odd branch).  Option (a) from the dispatch (absorb small `H` by a large `C₁`) closes
only the EVEN branch; the odd small-`H` branch is the genuine hole.

## FIX (recommended, for GB-0/GB-15/Fable)

Drop the parity split: re-freeze `rbound H n := C₁·(ε²H/log²H)·sTrunc2 n` for ALL `n`
(no `if Even`).  Then:
  • `hpt` becomes TRUE and ungated: even `n` via the sieve (large `H`) + crude
    `repCount ≤ |window|²` (bounded `H`); odd `n` via `repCount = 0` (large `H`,
    window odd) + crude (bounded `H`) — now dischargeable since the odd rbound is > 0.
  • `hsq` re-runs with NO new work: `sum_sTruncW_sq_le` (GoldbachEnergyHsqAsm.lean)
    already bounds `∑_{n ∈ 𝒫_H+𝒫_H} sTruncW h n ^ 2` over the FULL sumset (both
    parities); the frozen `hsq_holds2` was DISCARDING the odd terms via the `if Even`.
    A no-`if` `hsq_holds_gen'` is strictly easier (delete the `by_cases he : Even n`
    split).  `C = 2K·C₁²·ε⁶` is unchanged.
Alternative (b): gate `W3_AE_d_of_sieve`'s `hpt` at `4 ≤ ε²H` (a QuadrupleCount edit)
and keep `else 0`.  Then `primeWindow_odd_of_four_le` + `repCount_eq_zero_of_window_odd`
close the odd branch directly.

## GB-15 SEAM: what remains after this file

Landed here (all axiom-clean, `[propext, Classical.choice, Quot.sound]`):
  • `repCount_eq_zero_of_window_odd`, `primeWindow_odd_of_four_le` — the odd branch.
  • `goldErrSum_le` — the error sum `≤ (z²+1)⁴` (GB-10).
  • `goldSiftedSum_le_main_add_err` — the pole: `repCount(even) ≤
    n·sTrunc2 n/(c₀ log²z) + (z²+1)⁴`.
  • `goldBoundingSum_ge_uniform` — the denominator bound with `c₀ = 1/64` uniform in `n`.
  • `repCount_even_le_primorial` — the even branch at `P = primorial z`, with
    `hP`/`hPz`/`hsub`/`hbound` discharged; only `z`, the window gap `z < 𝒫_H`, and
    `n`-range remain as inputs.

The ONLY residual (the rpow/constant seam, deferred): pick `z = z(H)` (e.g.
`z := ⌊(H:ℝ)^(1/10)⌋₊`) and for `H ≥ H₀(ε)` show `z₀ ≤ z`, `2 ≤ z`, and
`(z:ℚ) ≤ ε²H/2` (⟹ `z < p` for every window prime `p > ε²H/2`), then bound
`n·sTrunc2 n/(c₀ log²z) + (z²+1)⁴ ≤ C₁·(ε²H/log²H)·sTrunc2 n` using `n ≤ 2ε²H`
(sumset), `log z ≥ (1/20)·log H`, and `(z²+1)⁴ ≤ ε²H/log²H` (H^{4/5} = o(H)),
absorbed into `H₀`.  With `sTrunc2 n ≥ 1` this gives `C₁ = O(1/c₀) = O(64)` times a
factor depending on `ε` (allowed: `hsq_holds*` take `C₁` as input; the final chain
quantifies `ε` outermost).  Template: `Salt/Brun/M5Assembly.lean` (rpow bookkeeping
`rpow_tenth_sq`, `guardedErrorSum_le`).  Compose with `hsq_holds*` (no-`if` variant
per the FIX) into `W3_AE_d_of_sieve` → `bigXi_bounded_of_sieve`; GB-14b's lcm bound
is the only other open input to the |Ξ_H| ≤ C hookup.
-/
