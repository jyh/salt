/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# GB-6 — the `g`-function split and the main-term denominator bound (rebuild node GB-6)

The Selberg-term split and the singular-series (`𝔖`) transfer for the
binary-Goldbach energy sieve (`docs/exploration/s3-a3-design.md`, sections
"GB-SIEVE-R0", "GB-0 — THE REBUILD DESIGN FREEZE").  Consumes the sieve instance
of `Salt/Entropy/Chowla/GoldbachEnergySieve.lean` (`goldEnergySieve`, `nuG`) and
the twin main-term machinery of `Salt/Brun/` (`gTwin`, `mainTermSum`,
`exists_const_mainTermSum_ge`) — the twin `mainTermSum ≥ c₀·(log z)²` bound is a
statement PURELY about `gTwin`, so it is reused verbatim as a black box.

* **The prime split** (`goldSelbergTerms_prime_dvd` / `_not_dvd`): the sieve's
  `selbergTerms` at a prime `p` is `1/(p−1)` when `p ∣ n` (`ρ_n(p) = 1`) and
  `2/(p−2)` when `p ∤ n` (`ρ_n(p) = 2`).  Mirrors the twin
  `selbergTerms_odd_prime_eq` at the `goldEnergySieve` instance; the `p ∤ n`
  branch is where the `n`-even guard `hn : 2 ∣ n` forces `p ≥ 3`.

* **The `𝔖` comparison** (`gTwin_le_sCorr_mul_selbergTerms`): for odd squarefree
  `ℓ`, the gold term is exactly `gTwin ℓ · ∏_{p ∣ ℓ, p ∣ n} (p−2)/(2(p−1))`;
  since each correction factor lies in `(0, 1]` and `{p ∣ ℓ, p ∣ n} ⊆
  {p ∣ n odd}`, the correction product is `≥ 1/sCorr n` where
  `sCorr n = ∏_{p ∣ n odd} 2(p−1)/(p−2)`.  Hence `gTwin ℓ ≤ sCorr n · gold(ℓ)`.

* **The denominator bound** (`goldCarrierSum_ge_log_sq`): summing the comparison
  over the twin `mainTermSum` carrier `{ℓ < z : odd, squarefree}` transfers the
  twin's `mainTermSum ≥ c₀ (log z)²` to
  `c₀ (log z)² / sCorr n ≤ ∑_ℓ gold(ℓ)`.  The optional bridge
  (`carrierSum_le_selbergBoundingSum`) drops this carrier sum into the literal
  `selbergBoundingSum` of the `goldSelbergSieve` `SelbergSieve` under a divisor
  subset hypothesis (discharged downstream by GB-7's parameter choice).

`sCorr n = ∏_{p ∣ n odd} 2(p−1)/(p−2) = 2^{ω_odd(n)} · ∏(p−1)/(p−2)` — the extra
`2^{ω_odd(n)}` versus the `hsq` majorant `sTrunc n = ∏(p−1)/(p−2)` is the honest
per-prime loss of this crude comparison; see the GB-7 seam note in the flag/report.

No `sorry`, no `native_decide`, no new axioms.
-/
import Mathlib
import Salt.Entropy.Chowla.GoldbachEnergySieve
import Salt.Brun.M3Assembly
import Salt.Brun.SelbergPort

open ArithmeticFunction Finset

namespace Salt.Entropy.Chowla

variable {n P : ℕ} {hn : 2 ∣ n} {hP : Squarefree P}

/-! ## Part 1 — the prime split -/

/-- At a prime `p`, the gold Selberg term is `ν_n(p)/(1 − ν_n(p))` (as
`p.primeFactors = {p}`).  Mirrors the twin `selbergTerms_prime`. -/
lemma goldSelbergTerms_prime (p : ℕ) (hp : p.Prime) :
    (goldEnergySieve n P hn hP).selbergTerms p = nuG n p * (1 - nuG n p)⁻¹ := by
  rw [BoundingSieve.selbergTerms_apply, goldEnergySieve_nu, hp.primeFactors, Finset.prod_singleton]

/-- **GB-6, the `p ∣ n` split.**  At `p ∣ n` we have `ρ_n(p) = 1`, so
`ν_n(p) = 1/p` and `selbergTerms p = (1/p)/(1 − 1/p) = 1/(p−1)`. -/
lemma goldSelbergTerms_prime_dvd (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) :
    (goldEnergySieve n P hn hP).selbergTerms p = 1 / ((p : ℝ) - 1) := by
  rw [goldSelbergTerms_prime p hp, nuG_apply, rhoG_prime_dvd hp hpn]
  push_cast
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [show (1 : ℝ) - 1 / p = ((p : ℝ) - 1) / p by field_simp, inv_div]
  field_simp

/-- **GB-6, the `p ∤ n` split.**  At `p ∤ n` we have `ρ_n(p) = 2`, so
`ν_n(p) = 2/p` and `selbergTerms p = (2/p)/(1 − 2/p) = 2/(p−2)`.  The `n`-even
guard forces `p ≥ 3` (else `p = 2 ∣ n`, contradicting `p ∤ n`). -/
lemma goldSelbergTerms_prime_not_dvd (p : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    (goldEnergySieve n P hn hP).selbergTerms p = 2 / ((p : ℝ) - 2) := by
  rw [goldSelbergTerms_prime p hp, nuG_apply, rhoG_prime_not_dvd hp hpn]
  push_cast
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | hodd
    · exact absurd hn (h2 ▸ hpn)
    · obtain ⟨k, hk⟩ := hodd; have := hp.two_le; omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  rw [show (1 : ℝ) - 2 / p = ((p : ℝ) - 2) / p by field_simp, inv_div]
  field_simp

/-! ## Part 2 — the singular-series majorant and the per-`ℓ` comparison -/

/-- The singular-series correction majorant
`sCorr n = ∏_{p ∣ n, p odd} 2(p−1)/(p−2)`.  Bounds the per-`ℓ` correction product
uniformly; `= 2^{ω_odd(n)} · ∏(p−1)/(p−2)` (the `2^{ω}` is the crude-comparison
loss versus the `hsq` majorant `sTrunc n`). -/
noncomputable def sCorr (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => Odd p), (2 * ((p : ℝ) - 1)) / ((p : ℝ) - 2)

/-- Every prime factor of the odd squarefree `ℓ` is `≥ 3`. -/
private lemma three_le_of_mem_odd_primeFactors {ℓ p : ℕ} (hℓodd : Odd ℓ)
    (hp : p ∈ ℓ.primeFactors) : 3 ≤ p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2d : (2 : ℕ) ∣ ℓ := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.odd_iff] at hℓodd; omega
  have := hpp.two_le; omega

/-- `sCorr n > 0` (each factor `2(p−1)/(p−2) > 0` for `p ≥ 3`). -/
lemma sCorr_pos (n : ℕ) : 0 < sCorr n := by
  rw [sCorr]
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp := Nat.prime_of_mem_primeFactors hp.1
  have hp3 : 3 ≤ p := by
    have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hp.2
    have := hpp.two_le; omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  apply div_pos <;> linarith

/-- **GB-6, the `𝔖` comparison.**  For odd squarefree `ℓ`, the bare twin term
`gTwin ℓ` is at most `sCorr n` times the gold Selberg term.  This is the
per-`ℓ` singular-series transfer: `gTwin ℓ = gold(ℓ) · ∏_{p ∣ ℓ, p ∣ n}
2(p−1)/(p−2)`, and the correction product is `≤ sCorr n`. -/
lemma gTwin_le_sCorr_mul_selbergTerms (ℓ : ℕ) (hℓodd : Odd ℓ) (hℓsq : Squarefree ℓ)
    (hn0 : n ≠ 0) :
    Salt.M3Expansion.gTwin ℓ ≤ sCorr n * (goldEnergySieve n P hn hP).selbergTerms ℓ := by
  classical
  -- per-prime facts on `ℓ.primeFactors`
  have hp3 : ∀ p ∈ ℓ.primeFactors, 3 ≤ p := fun p hp => three_le_of_mem_odd_primeFactors hℓodd hp
  -- the per-prime identity `2/(p−2) = corr(p) · gold(p)`
  have hkey : ∀ p ∈ ℓ.primeFactors,
      (2 : ℝ) / ((p : ℝ) - 2)
        = (if p ∣ n then (2 * ((p : ℝ) - 1)) / ((p : ℝ) - 2) else 1)
          * (goldEnergySieve n P hn hP).selbergTerms p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3 p hp
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, goldSelbergTerms_prime_dvd p hpp hpn]; field_simp
    · rw [if_neg hpn, goldSelbergTerms_prime_not_dvd p hpp hpn, one_mul]
  -- the gold term over `ℓ` is nonnegative (each prime factor gives a positive value)
  have hst_nonneg : 0 ≤ (goldEnergySieve n P hn hP).selbergTerms ℓ := by
    rw [← (goldEnergySieve n P hn hP).selbergTerms_isMultiplicative.prod_primeFactors hℓsq]
    apply Finset.prod_nonneg
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3 p hp
    by_cases hpn : p ∣ n
    · rw [goldSelbergTerms_prime_dvd p hpp hpn]; apply div_nonneg (by norm_num); linarith
    · rw [goldSelbergTerms_prime_not_dvd p hpp hpn]; apply div_nonneg (by norm_num); linarith
  -- the correction product is `≤ sCorr n`
  have hcorr : (∏ p ∈ ℓ.primeFactors,
        (if p ∣ n then (2 * ((p : ℝ) - 1)) / ((p : ℝ) - 2) else 1)) ≤ sCorr n := by
    rw [← Finset.prod_filter, sCorr]
    have hsub : ℓ.primeFactors.filter (fun p => p ∣ n)
        ⊆ n.primeFactors.filter (fun p => Odd p) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hpℓ, hpn⟩ := hp
      have hpp := Nat.prime_of_mem_primeFactors hpℓ
      have hp3' := hp3 p hpℓ
      exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpn, hn0⟩,
        (hpp.eq_two_or_odd').resolve_left (by omega)⟩
    rw [← Finset.prod_sdiff hsub]
    apply le_mul_of_one_le_left
    · apply Finset.prod_nonneg
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3 p hp.1
      apply div_nonneg <;> linarith
    · calc (1 : ℝ)
          = ∏ _p ∈ (n.primeFactors.filter (fun p => Odd p)) \
              (ℓ.primeFactors.filter (fun p => p ∣ n)), (1 : ℝ) := Finset.prod_const_one.symm
        _ ≤ ∏ p ∈ (n.primeFactors.filter (fun p => Odd p)) \
              (ℓ.primeFactors.filter (fun p => p ∣ n)),
                (2 * ((p : ℝ) - 1)) / ((p : ℝ) - 2) := by
            apply Finset.prod_le_prod
            · intro p _; norm_num
            · intro p hp
              rw [Finset.mem_sdiff, Finset.mem_filter] at hp
              have hpp := Nat.prime_of_mem_primeFactors hp.1.1
              have hp3' : 3 ≤ p := by
                have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hp.1.2
                have := hpp.two_le; omega
              have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3'
              rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 2)]; linarith
  -- assemble
  have hprodeq : (∏ p ∈ ℓ.primeFactors, (2 : ℝ) / ((p : ℝ) - 2))
      = (∏ p ∈ ℓ.primeFactors,
          (if p ∣ n then (2 * ((p : ℝ) - 1)) / ((p : ℝ) - 2) else 1))
        * (goldEnergySieve n P hn hP).selbergTerms ℓ := by
    rw [← (goldEnergySieve n P hn hP).selbergTerms_isMultiplicative.prod_primeFactors hℓsq,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hkey
  calc Salt.M3Expansion.gTwin ℓ
      = (∏ p ∈ ℓ.primeFactors,
            (if p ∣ n then (2 * ((p : ℝ) - 1)) / ((p : ℝ) - 2) else 1))
          * (goldEnergySieve n P hn hP).selbergTerms ℓ := by
        rw [Salt.M3Expansion.gTwin]; exact hprodeq
    _ ≤ sCorr n * (goldEnergySieve n P hn hP).selbergTerms ℓ :=
        mul_le_mul_of_nonneg_right hcorr hst_nonneg

/-! ## Part 3 — the carrier-sum denominator bound -/

/-- The twin main-term carrier sum, transferred to the gold Selberg terms:
`mainTermSum z ≤ sCorr n · ∑_{ℓ < z, odd, squarefree} gold(ℓ)`.  Immediate from
the per-`ℓ` comparison and `Finset.mul_sum`. -/
lemma mainTermSum_le_sCorr_mul_carrierSum (z : ℕ) (hn0 : n ≠ 0) :
    Salt.M3Assembly.mainTermSum z
      ≤ sCorr n * ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          (goldEnergySieve n P hn hP).selbergTerms ℓ := by
  rw [Salt.M3Assembly.mainTermSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  rw [Finset.mem_filter, Finset.mem_range] at hℓ
  exact gTwin_le_sCorr_mul_selbergTerms ℓ hℓ.2.1 hℓ.2.2 hn0

/-- **GB-6, the main-term denominator bound.**  The gold Selberg carrier sum is
`≥ c₀ (log z)² / sCorr n` for all large `z`, with `c₀` the twin main-term
constant (`1/64`).  Reuses the twin `exists_const_mainTermSum_ge` verbatim (that
bound is a statement purely about `gTwin`), then divides the constant by the
singular-series majorant `sCorr n`. -/
theorem goldCarrierSum_ge_log_sq (hn0 : n ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
      c₀ * (Real.log z) ^ 2 / sCorr n
        ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
  obtain ⟨c₀, hc₀, z₀, hz₀⟩ := Salt.M3Assembly.exists_const_mainTermSum_ge
  refine ⟨c₀, hc₀, z₀, fun z hz => ?_⟩
  rw [div_le_iff₀ (sCorr_pos n)]
  calc c₀ * (Real.log z) ^ 2
      ≤ Salt.M3Assembly.mainTermSum z := hz₀ z hz
    _ ≤ sCorr n * ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ :=
        mainTermSum_le_sCorr_mul_carrierSum z hn0
    _ = (∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ) * sCorr n := mul_comm _ _

/-! ## Part 4 — the bridge to the literal `selbergBoundingSum` (GB-7 seam) -/

/-- The `goldEnergySieve` promoted to a `SelbergSieve` by adjoining a `level`.
`selbergTerms`/`prodPrimes` are inherited unchanged from the `BoundingSieve`. -/
noncomputable def goldSelbergSieve (n P : ℕ) (hn : 2 ∣ n) (hP : Squarefree P)
    (level : ℝ) (hlvl : 1 ≤ level) : SelbergSieve where
  toBoundingSieve := goldEnergySieve n P hn hP
  level := level
  one_le_level := hlvl

@[simp] lemma goldSelbergSieve_prodPrimes (level : ℝ) (hlvl : 1 ≤ level) :
    (goldSelbergSieve n P hn hP level hlvl).prodPrimes = P := rfl

@[simp] lemma goldSelbergSieve_level (level : ℝ) (hlvl : 1 ≤ level) :
    (goldSelbergSieve n P hn hP level hlvl).level = level := rfl

@[simp] lemma goldSelbergSieve_selbergTerms (level : ℝ) (hlvl : 1 ≤ level) :
    (goldSelbergSieve n P hn hP level hlvl).selbergTerms
      = (goldEnergySieve n P hn hP).selbergTerms := rfl

/-- **The GB-7 bridge.**  The gold carrier sum is at most the literal
`selbergBoundingSum` of the `goldSelbergSieve`, provided the carrier
`{ℓ < z : odd, squarefree}` sits inside the sieve's divisor window
`{l ∣ P : l² ≤ level}`.  The extra terms are dropped by `selbergTerms_pos`.  The
subset hypothesis is GB-7's parameter obligation (`P ⊇ primorial(z)`,
`level ≥ z²`), mirroring the twin `selbergBoundingSum_ge_mainTermSum`. -/
lemma carrierSum_le_selbergBoundingSum (level : ℝ) (hlvl : 1 ≤ level) (z : ℕ)
    (hsub : (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
        ⊆ P.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ level)) :
    (∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
        (goldEnergySieve n P hn hP).selbergTerms ℓ)
      ≤ Salt.SelbergPort.selbergBoundingSum (goldSelbergSieve n P hn hP level hlvl) := by
  classical
  rw [Salt.SelbergPort.selbergBoundingSum]
  simp only [goldSelbergSieve_prodPrimes, goldSelbergSieve_level, goldSelbergSieve_selbergTerms]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro l hl _
  rw [Finset.mem_filter, Nat.mem_divisors] at hl
  exact le_of_lt ((goldEnergySieve n P hn hP).selbergTerms_pos hl.1.1)

/-- **GB-6, the composed denominator bound at the literal `selbergBoundingSum`.**
For all large `z` and any admissible `(level, hsub)`, the Selberg bounding sum of
the gold sieve is `≥ c₀ (log z)² / sCorr n`.  This is the surface GB-7 feeds to
`selberg_bound_simple` (`siftedSum ≤ totalMass / selbergBoundingSum + error`). -/
theorem goldSelbergBoundingSum_ge_log_sq (hn0 : n ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ z₀ : ℕ, ∀ (z : ℕ), z₀ ≤ z → ∀ (level : ℝ) (hlvl : 1 ≤ level),
      (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
          ⊆ P.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ level) →
      c₀ * (Real.log z) ^ 2 / sCorr n
        ≤ Salt.SelbergPort.selbergBoundingSum (goldSelbergSieve n P hn hP level hlvl) := by
  obtain ⟨c₀, hc₀, z₀, hz₀⟩ := goldCarrierSum_ge_log_sq (hn := hn) (hP := hP) hn0
  refine ⟨c₀, hc₀, z₀, fun z hz level hlvl hsub => ?_⟩
  exact le_trans (hz₀ z hz) (carrierSum_le_selbergBoundingSum level hlvl z hsub)

end Salt.Entropy.Chowla
