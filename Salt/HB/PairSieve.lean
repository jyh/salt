/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.SelbergPort
import Salt.Brun.M3
import Salt.Brun.M3Expansion
import Salt.Brun.M3Assembly

/-!
# HB 1983 §3, Lemma 8 — the two-dimensional (twin-pair) sieve upper bound

This file is the WP1 node of the HB-ENGINE campaign.  Heath-Brown's Lemma 8
bounds, for `x < n ≤ 2x` with `d₁ ∣ n`, `d₂ ∣ (n+2)`, and both cofactors
`n/d₁`, `(n+2)/d₂` free of prime factors `< Z`,

  `S(d₁,d₂;Z)  ≪  (x / (d₁ d₂)) · (d₁ d₂ / φ(d₁ d₂)) · (log Z)⁻²  +  (remainder)`.

We simplify to the twin forms `l₁(n) = n`, `l₂(n) = n+2` (the campaign target),
and — following HB's conditions making the `lᵢ` odd — take `d₁, d₂` odd and
coprime.  After the CRT reduction `n ≡ 0 (d₁)`, `n ≡ −2 (d₂)` fixing `n` to one
class mod `d₁ d₂`, the object is a two-dimensional twin sieve of total mass
`≈ x/(d₁ d₂)` with the same local density `ν(p) = 2/p` (for `p ∤ 2 d₁ d₂`).

## The route (Selberg, on the landed engine)

The proof runs the general proven Selberg `Λ²` bound
`Salt.SelbergPort.selberg_bound_simple`
(`s.siftedSum ≤ s.totalMass / S + Σ_{d∣P, d≤y} 3^{ω(d)}|rem d|`, where
`S = selbergBoundingSum s = Σ_{ℓ∣P, ℓ²≤y} g(ℓ)`), on a `SelbergSieve`
instance whose `siftedSum` is `S(d₁,d₂;Z)`.  The bound then needs the
**denominator lower bound** `S ≥ c·(log Z)²`, which is the genuinely
two-dimensional estimate.

## What is proven here (sorry-free)

* `Salt.HB.selberg_upper_of_bounds` — **Stone 3 (the reduction/transfer).**
  From `selberg_bound_simple` plus the packaged bounds `totalMass ≤ M`,
  `0 < D ≤ S`, `errSum ≤ E`, concludes `siftedSum ≤ M/D + E`.  This is exactly
  the shape HB's `S⁰→S³` transfer chain (Lemma 2) consumes.

* `Salt.HB.selbergTerms_eq_gTwin_of_nu` and
  `Salt.HB.boundingSum_ge_mainTermSum` and
  `Salt.HB.boundingSum_ge_log_sq_of_twinDensity` — **Stone 2 (the denominator
  lower bound).**  For *any* `SelbergSieve` carrying the twin local density
  `ν(p) = 2/p` on its (odd) sifted primes, whose sifted primes include all odd
  primes `< z` and whose level is `≥ z²`, the Selberg denominator satisfies
  `S ≥ (1/64)·(log z)²`.  This abstracts the Brun-track
  `selbergBoundingSum_ge_log_sq` (`M5Assembly.lean:169`) away from its concrete
  instance, reusing the instance-free `(log z)²` chain of `Salt.M3Assembly`
  (whose mechanism — radical-grouping + `divSum_ge_sq` — is the `divSum_ge_sq`
  route named in the campaign spec).

* `Salt.HB.pairSieve_lemma8` — **the assembled Lemma 8 (conditional on the
  instance).**  For a twin-density `SelbergSieve`, `siftedSum ≤ 64 M/(log z)² + E`.
  With `siftedSum = S(d₁,d₂;Z)`, `M = x/(d₁d₂)`-grade total mass and `z ≈ Z`,
  this is HB's Lemma 8 (the `d₁ d₂/φ(d₁ d₂)` factor is absorbed into `M` and the
  denominator bound; see the residuals below).

## Residuals (the honest partial — named per the Zeno ladder)

* **R1 (Stone 1, the instance).**  Constructing the concrete `SelbergSieve`
  whose `siftedSum` equals `S(d₁,d₂;Z)` — i.e. the CRT residue-class count
  `n ≡ 0 (d₁)`, `n ≡ −2 (d₂)`, total mass `x/(d₁d₂) + O(1)`, and the
  remainder bound `|rem d| ≤ 3^{ω(d)}`-grade via the class count.  This is
  B-tier plumbing mirroring `Salt.TwinSieve.sieve` (`Salt/Brun/Sieve.lean`) +
  `Salt.Brun.M2.progression_count_bound`, but for the general AP-pair linear
  forms (out of the pure-`n(n+2)` shape the Brun track built).

* **R2 (the `φ(d₁d₂)` sharpening).**  When `d₁ d₂` shares prime factors with the
  sieve range, those primes carry local density `1/p` (not `2/p`), so the clean
  `(log z)²` denominator here (which assumes twin density on *all* sifted primes)
  degrades to the `φ(d₁d₂)/(d₁d₂)`-restricted two-dimensional harmonic square.
  `boundingSum_ge_log_sq_of_twinDensity` covers the sub-case where `d₁ d₂` is
  `z`-rough; the coprimality-restricted refinement is the resisting estimate.

## Death map (inherited from the campaign)

Beyond-level-½ error control (HB-R4, the Kloosterman wall) is the campaign's
predicted death rung; this WP1 node lives entirely on the level-½ Selberg engine
and makes no beyond-½ claim.
-/

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

namespace Salt.HB

variable (s : SelbergSieve)

/-! ## Stone 3 — the reduction / transfer -/

/-- **Stone 3 (the transfer).**  From the general Selberg `Λ²` bound
`selberg_bound_simple`, package the three inputs — a total-mass upper bound
`M`, a positive Selberg-denominator lower bound `D`, and an error-sum upper
bound `E` — into the Lemma-8 shape `siftedSum ≤ M/D + E`.  This is the estimate
HB's `S⁰→S³` transfer chain (Lemma 2) consumes. -/
theorem selberg_upper_of_bounds {M D E : ℝ}
    (hM0 : 0 ≤ M) (hmass : s.totalMass ≤ M)
    (hD : 0 < D) (hden : D ≤ Salt.SelbergPort.selbergBoundingSum s)
    (herr : (∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0) ≤ E) :
    s.siftedSum ≤ M / D + E := by
  have hsel := Salt.SelbergPort.selberg_bound_simple s
  have hSpos := Salt.SelbergPort.selbergBoundingSum_pos s
  have h1 : s.totalMass / Salt.SelbergPort.selbergBoundingSum s ≤ M / D := by
    rw [div_le_div_iff₀ hSpos hD]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmass) hD.le,
      mul_nonneg hM0 (sub_nonneg.mpr hden)]
  linarith [hsel, h1, herr]

/-! ## Stone 2 — the two-dimensional denominator lower bound -/

/-- For an odd squarefree `ℓ ∣ prodPrimes`, if the local density is the twin
`ν(p) = 2/p` on every (odd) sifted prime, then the Selberg term at `ℓ` is the
bare twin product `gTwin ℓ = ∏_{p∣ℓ} 2/(p−2)`.  The abstract (instance-free)
analogue of `Salt.TwinSieve.selbergTerms_eq_gTwin`. -/
lemma selbergTerms_eq_gTwin_of_nu {ℓ : ℕ}
    (hℓP : ℓ ∣ s.prodPrimes) (hℓodd : Odd ℓ) (hℓsq : Squarefree ℓ)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → p ≠ 2 → s.nu p = 2 / (p : ℝ)) :
    s.selbergTerms ℓ = Salt.M3Expansion.gTwin ℓ := by
  rw [← s.selbergTerms_isMultiplicative.prod_primeFactors hℓsq, Salt.M3Expansion.gTwin]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpℓ : p ∣ ℓ := Nat.dvd_of_mem_primeFactors hp
  have hpP : p ∣ s.prodPrimes := hpℓ.trans hℓP
  have hpodd : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hℓodd) (even_iff_two_dvd.mpr hpℓ)
  have h3 : 3 ≤ p := by
    have h2 := hpp.two_le
    rcases hpp.eq_two_or_odd' with h | h
    · exact absurd h hpodd
    · rcases h with ⟨k, hk⟩; omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast h3
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  rw [BoundingSieve.selbergTerms_apply, hpp.primeFactors, Finset.prod_singleton,
    hnu p hpp hpP hpodd]
  rw [show (1 : ℝ) - 2 / p = (p - 2) / p by field_simp, inv_div]
  field_simp

/-- **Stone 2, sieve glue.**  For a `SelbergSieve` carrying the twin density
`ν(p) = 2/p` on its odd sifted primes, whose sifted primes include every odd
squarefree `ℓ < z` and whose level is `≥ z²`, the Selberg denominator dominates
the (instance-free) twin main-term sum `mainTermSum z = Σ_{ℓ<z, odd sqfree} gTwin ℓ`.
Abstracts `Salt.M5Assembly.selbergBoundingSum_ge_mainTermSum`. -/
lemma boundingSum_ge_mainTermSum (z : ℕ)
    (hlevel : (z : ℝ) ^ 2 ≤ s.level)
    (hcontains : ∀ ℓ, Odd ℓ → Squarefree ℓ → ℓ < z → ℓ ∣ s.prodPrimes)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → p ≠ 2 → s.nu p = 2 / (p : ℝ)) :
    Salt.SelbergPort.selbergBoundingSum s ≥ Salt.M3Assembly.mainTermSum z := by
  classical
  rw [ge_iff_le, Salt.SelbergPort.selbergBoundingSum, ← Finset.sum_filter,
    Salt.M3Assembly.mainTermSum]
  set small : Finset ℕ := (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) with hsmall
  set big : Finset ℕ :=
    s.prodPrimes.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ s.level) with hbig
  have hsub : small ⊆ big := by
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    rw [hbig, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨hcontains ℓ hℓodd hℓsq hℓz, BoundingSieve.prodPrimes_ne_zero⟩, ?_⟩
    have hℓR : (ℓ : ℝ) ≤ (z : ℝ) := by exact_mod_cast (le_of_lt hℓz)
    have hℓnn : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    calc (ℓ : ℝ) ^ 2 ≤ (z : ℝ) ^ 2 := by gcongr
      _ ≤ s.level := hlevel
  have heq : ∑ ℓ ∈ small, Salt.M3Expansion.gTwin ℓ = ∑ ℓ ∈ small, s.selbergTerms ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    exact (selbergTerms_eq_gTwin_of_nu s (hcontains ℓ hℓodd hℓsq hℓz) hℓodd hℓsq hnu).symm
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro l hl _
  rw [hbig, Finset.mem_filter, Nat.mem_divisors] at hl
  exact le_of_lt (s.selbergTerms_pos hl.1.1)

/-- **Stone 2 (the two-dimensional denominator lower bound).**  For a
`SelbergSieve` with twin local density `ν(p) = 2/p` on its odd sifted primes,
sifted primes covering every odd squarefree `ℓ < z`, and level `≥ z²`
(`z ≥ 100`), the Selberg denominator grows quadratically:
`S ≥ (1/64)·(log z)²`.  This is the `divSum_ge_sq`-route estimate of the
campaign spec, made instance-generic; the `(log z)²` chain itself is the landed
`Salt.M3Assembly` (radical-grouping + `divSum_ge_sq`). -/
theorem boundingSum_ge_log_sq_of_twinDensity (z : ℕ)
    (hz : 100 ≤ z) (hlevel : (z : ℝ) ^ 2 ≤ s.level)
    (hcontains : ∀ ℓ, Odd ℓ → Squarefree ℓ → ℓ < z → ℓ ∣ s.prodPrimes)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → p ≠ 2 → s.nu p = 2 / (p : ℝ)) :
    Salt.SelbergPort.selbergBoundingSum s ≥ (1 / 64 : ℝ) * (Real.log z) ^ 2 := by
  have h1 := boundingSum_ge_mainTermSum s z hlevel hcontains hnu
  have hz0 : Salt.M3Assembly.z0 ≤ z := by unfold Salt.M3Assembly.z0; omega
  have hsqrt_ge1 : (1 : ℕ) ≤ z.sqrt := by
    have h4 : (4 : ℕ) ≤ z.sqrt := Nat.le_sqrt.mpr (by omega)
    omega
  have hlog4 : (4 : ℝ) ≤ Real.log z := Salt.M3Assembly.log_ge_four hz0
  have hD := Salt.M3Assembly.stepD hz0
  have hpos : (0 : ℝ) ≤ (1 / 8 : ℝ) * Real.log z := by linarith
  have hsq : ((1 / 8 : ℝ) * Real.log z) ^ 2 ≤ (oddHarmonicSum (z.sqrt - 1)) ^ 2 :=
    pow_le_pow_left₀ hpos hD 2
  have hchain := Salt.M3Assembly.mainTermSum_ge_oddHarmonicSum_sq (z := z) hsqrt_ge1
  have heq : ((1 / 8 : ℝ) * Real.log z) ^ 2 = (1 / 64 : ℝ) * (Real.log z) ^ 2 := by ring
  rw [heq] at hsq
  linarith [h1, hchain, hsq]

/-! ## The assembled Lemma 8 (conditional on the instance) -/

/-- **HB 1983, Lemma 8 (twin case, assembled).**  For a `SelbergSieve` carrying
the twin density `ν(p) = 2/p` on its odd sifted primes (all odd squarefree
`ℓ < z` sifted, level `≥ z²`, `z ≥ 100`), with total mass `≤ M` and Selberg
error sum `≤ E`, the sifted sum obeys

  `siftedSum ≤ 64 · M / (log z)² + E`.

Reading this at the Stone-1 instance (`siftedSum = S(d₁,d₂;Z)`,
`M = x/(d₁ d₂)`-grade, `z ≈ Z`) is HB's Lemma 8.  See the module residuals R1
(the instance) and R2 (the `φ(d₁d₂)` sharpening when `d₁ d₂` is not `z`-rough). -/
theorem pairSieve_lemma8 (z : ℕ) {M E : ℝ}
    (hz : 100 ≤ z) (hlevel : (z : ℝ) ^ 2 ≤ s.level)
    (hcontains : ∀ ℓ, Odd ℓ → Squarefree ℓ → ℓ < z → ℓ ∣ s.prodPrimes)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → p ≠ 2 → s.nu p = 2 / (p : ℝ))
    (hM0 : 0 ≤ M) (hmass : s.totalMass ≤ M)
    (herr : (∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0) ≤ E) :
    s.siftedSum ≤ 64 * M / (Real.log z) ^ 2 + E := by
  have hlog4 : (4 : ℝ) ≤ Real.log z :=
    Salt.M3Assembly.log_ge_four (by unfold Salt.M3Assembly.z0; omega)
  have hLpos : (0 : ℝ) < Real.log z := by linarith
  have hLne : (Real.log z) ≠ 0 := ne_of_gt hLpos
  have hL2pos : (0 : ℝ) < (Real.log z) ^ 2 := pow_pos hLpos 2
  have hDpos : (0 : ℝ) < (1 / 64 : ℝ) * (Real.log z) ^ 2 :=
    mul_pos (by norm_num) hL2pos
  have hden := boundingSum_ge_log_sq_of_twinDensity s z hz hlevel hcontains hnu
  have key := selberg_upper_of_bounds s hM0 hmass hDpos hden herr
  have heq2 : M / ((1 / 64 : ℝ) * (Real.log z) ^ 2) = 64 * M / (Real.log z) ^ 2 := by
    field_simp
  rw [heq2] at key
  exact key

end Salt.HB
