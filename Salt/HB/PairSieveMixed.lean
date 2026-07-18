/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.PairInstance
import Salt.Maynard.ShiuSieve
import Salt.Brun.M3Assembly

/-!
# HB 1983 §3, Lemma 8 — the mixed-density (cofactor) pair sieve (WP1 / R2)

This file discharges residual **R2** of `Salt.HB.PairSieve`: the mixed-density
pair sieve whose consumer is HB's (3.3).  Unlike the landed `Salt.HB.hb_lemma8`
(`Salt.HB.PairInstance`), which requires `d₁ d₂` to be `z`-rough so that every
sifted prime carries the full twin density `2/p`, here `d₁ d₂` may share prime
factors with the sift range: at `p ∣ d₁ d₂` the honest local density is `1/p`,
not `2/p`, because the sift target is the **cofactors** `n/d₁`, `(n+2)/d₂`
(which are the objects HB's (3.3) sees), not the product `n(n+2)`.

## The floor (this section — the resisting estimate)

The Selberg denominator of the mixed sieve is bounded below by the
**coprimality-restricted** twin main-term sum
`restrictedMainTermSum M Z = Σ_{ℓ<Z, sqfree, (ℓ,M)=1} gTwin ℓ`, where `M = 2 d₁ d₂`.
Restricting the twin `(log Z)²`-floor of `Salt.M3Assembly` to `ℓ` coprime to
`M` costs the classical `φ`-factor `(φ(M)/M)²`, which we extract **for free**
from the landed `Salt.Maynard.copHarmonic_uniform_lower` (the `q`-uniform
coprime-harmonic lower bound) at `q = M`.  Because `2 ∣ M`, coprimality to `M`
subsumes oddness, so the whole restricted radical/diagonal chain reuses the
landed `divSum_ge_sq`, `Salt.M3Assembly.term_bound`, and
`Salt.M3Expansion.radical_fiber_bound` verbatim.

Result of this section:
`restrictedMainTermSum_ge : restrictedMainTermSum M Z ≥ (copHarmonic Z.sqrt M)²`.
-/

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega ArithmeticFunction.Omega

namespace Salt.HB

open Salt.M3Expansion (nuStar gTwin rad)

/-! ## §1 — the coprimality-restricted twin main-term sum -/

/-- The twin Selberg main-term sum restricted to `ℓ` coprime to `M`
(`Σ_{ℓ<Z, sqfree, (ℓ,M)=1} gTwin ℓ`).  When `M = 2 d₁ d₂`, coprimality to `M`
forces `ℓ` odd and `z`-coprime-to-`d₁d₂`, so every prime `p ∣ ℓ` carries the
full twin density and `gTwin ℓ = ∏_{p∣ℓ} 2/(p-2)` is the honest local factor. -/
noncomputable def restrictedMainTermSum (M Z : ℕ) : ℝ :=
  ∑ ℓ ∈ (Finset.range Z).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ M), gTwin ℓ

/-- Coprimality to an even modulus forces oddness. -/
lemma odd_of_coprime_two_dvd {m M : ℕ} (h2M : 2 ∣ M) (hcop : Nat.Coprime m M) : Odd m := by
  rcases Nat.even_or_odd m with he | ho
  · exfalso
    have h2m : (2 : ℕ) ∣ m := he.two_dvd
    have hg : (2 : ℕ) ∣ Nat.gcd m M := Nat.dvd_gcd h2m h2M
    rw [Nat.Coprime] at hcop
    rw [hcop] at hg
    exact absurd hg (by decide)
  · exact ho

/-! ## §1a — the restricted radical grouping (`Σ ν* ≤ Σ gTwin`, coprime to `M`) -/

/-- **Restricted N3.2.**  The `ν*`-sum over `m < Z` coprime to `M` is bounded by
the restricted twin Selberg main-term sum.  Reuses `radical_fiber_bound` after
enlarging each fiber from `(m,M)=1` to merely `Odd m` (legitimate since
`ν* ≥ 0`), and preserves coprimality under the radical map (`rad m ∣ m`). -/
lemma nuStarCop_sum_le_restrictedMainTermSum (M Z : ℕ) (h2M : 2 ∣ M) :
    ∑ m ∈ (Finset.range Z).filter (fun m => Nat.Coprime m M), nuStar m
      ≤ restrictedMainTermSum M Z := by
  classical
  set Fcop := (Finset.range Z).filter (fun m => Nat.Coprime m M) with hF
  set Gcop := (Finset.range Z).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ M) with hG
  have hmaps : ∀ m ∈ Fcop, rad m ∈ Gcop := by
    intro m hm
    rw [hF, Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmz, hmcop⟩ := hm
    have hmodd : Odd m := odd_of_coprime_two_dvd h2M hmcop
    have hm0 : m ≠ 0 := by rintro rfl; simp at hmodd
    have hdvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
    rw [hG, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Salt.M3Expansion.rad_squarefree m, hmcop.coprime_dvd_left hdvd⟩
    calc rad m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
      _ < Z := hmz
  rw [restrictedMainTermSum, ← hG, ← Finset.sum_fiberwise_of_maps_to hmaps nuStar]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  rw [hG, Finset.mem_filter] at hℓ
  have hℓodd : Odd ℓ := odd_of_coprime_two_dvd h2M hℓ.2.2
  -- enlarge the fiber to the `Odd`-only fiber, then apply `radical_fiber_bound`
  have hsub : Fcop.filter (fun m => rad m = ℓ)
      ⊆ ((Finset.range Z).filter Odd).filter (fun m => rad m = ℓ) := by
    intro m hm
    rw [Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_range] at hm
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨hm.1.1, odd_of_coprime_two_dvd h2M hm.1.2⟩, hm.2⟩
  calc ∑ m ∈ Fcop.filter (fun m => rad m = ℓ), nuStar m
      ≤ ∑ m ∈ ((Finset.range Z).filter Odd).filter (fun m => rad m = ℓ), nuStar m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro m _ _; unfold nuStar; positivity
    _ ≤ gTwin ℓ := Salt.M3Expansion.radical_fiber_bound Z ℓ hℓodd

/-! ## §1b — the restricted diagonal (`(copHarmonic)² ≤ Σ ν*`) -/

/-- **Restricted N3.4 + Step A.**  The restricted coprime-harmonic square is
bounded by the restricted `ν*`-sum, via the landed `divSum_ge_sq` (diagonal)
and `term_bound` (`τ(m)/m ≤ ν*(m)` for odd `m`, and `(m,M)=1 ⟹ Odd m`). -/
lemma copHarmonic_sq_le_nuStarCop_sum (M Z : ℕ) (h2M : 2 ∣ M) :
    (Salt.Maynard.copHarmonic Z.sqrt M) ^ 2
      ≤ ∑ m ∈ (Finset.range Z).filter (fun m => Nat.Coprime m M), nuStar m := by
  classical
  set S := (Finset.range Z).filter (fun m => Nat.Coprime m M) with hS
  set T := (Finset.range Z.sqrt).filter (fun a => Nat.Coprime a M) with hT
  have h0T : (0 : ℕ) ∉ T := by
    rw [hT, Finset.mem_filter]
    rintro ⟨_, hcop0⟩
    rw [Nat.coprime_zero_left] at hcop0
    rw [hcop0] at h2M; exact absurd h2M (by decide)
  have hST : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ S ∧ a ∣ (a * b) := by
    intro a ha b hb
    rw [hT, Finset.mem_filter, Finset.mem_range] at ha hb
    refine ⟨?_, dvd_mul_right a b⟩
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by nlinarith [Nat.sqrt_le' Z, ha.1, hb.1], Nat.Coprime.mul_left ha.2 hb.2⟩
  have hge := divSum_ge_sq S T h0T hST
  have hcop : Salt.Maynard.copHarmonic Z.sqrt M = ∑ a ∈ T, (1 : ℝ) / a := by rw [hT]; rfl
  have hdiag : (Salt.Maynard.copHarmonic Z.sqrt M) ^ 2 ≤ divSum S := by rw [hcop]; exact hge
  have hterm : divSum S ≤ ∑ m ∈ S, nuStar m := by
    unfold divSum
    apply Finset.sum_le_sum
    intro m hm
    rw [hS, Finset.mem_filter] at hm
    exact Salt.M3Assembly.term_bound (odd_of_coprime_two_dvd h2M hm.2)
  exact le_trans hdiag hterm

/-- **The restricted twin `(log Z)²`-floor input.**  `restrictedMainTermSum M Z`
dominates the square of the coprime-harmonic sum `Σ_{a<√Z,(a,M)=1} 1/a`. -/
lemma restrictedMainTermSum_ge (M Z : ℕ) (h2M : 2 ∣ M) :
    restrictedMainTermSum M Z ≥ (Salt.Maynard.copHarmonic Z.sqrt M) ^ 2 :=
  le_trans (copHarmonic_sq_le_nuStarCop_sum M Z h2M)
    (nuStarCop_sum_le_restrictedMainTermSum M Z h2M)

/-! ## §2 — the abstract restricted Selberg floor (Stone 2, mixed) -/

variable (s : SelbergSieve)

/-- For odd squarefree `ℓ ∣ prodPrimes` **coprime to `M`** (with `2 ∣ M`), if the
local density is the twin `ν(p) = 2/p` on every sifted prime not dividing `M`,
then `selbergTerms ℓ = gTwin ℓ`.  The coprime-to-`M` analogue of
`Salt.HB.selbergTerms_eq_gTwin_of_nu`. -/
lemma selbergTerms_eq_gTwin_cop {M ℓ : ℕ}
    (hℓP : ℓ ∣ s.prodPrimes) (hℓcop : Nat.Coprime ℓ M) (hℓsq : Squarefree ℓ) (h2M : 2 ∣ M)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → ¬ p ∣ M → s.nu p = 2 / (p : ℝ)) :
    s.selbergTerms ℓ = gTwin ℓ := by
  rw [← s.selbergTerms_isMultiplicative.prod_primeFactors hℓsq, gTwin]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpℓ : p ∣ ℓ := Nat.dvd_of_mem_primeFactors hp
  have hpP : p ∣ s.prodPrimes := hpℓ.trans hℓP
  have hpM : ¬ p ∣ M := by
    intro hpM
    have hg : p ∣ Nat.gcd ℓ M := Nat.dvd_gcd hpℓ hpM
    rw [Nat.Coprime] at hℓcop; rw [hℓcop] at hg
    exact absurd (Nat.dvd_one.mp hg) hpp.one_lt.ne'
  have hpodd : p ≠ 2 := by rintro rfl; exact hpM h2M
  have h3 : 3 ≤ p := by
    have h2 := hpp.two_le
    rcases hpp.eq_two_or_odd' with h | h
    · exact absurd h hpodd
    · rcases h with ⟨k, hk⟩; omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast h3
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  rw [BoundingSieve.selbergTerms_apply, hpp.primeFactors, Finset.prod_singleton,
    hnu p hpp hpP hpM]
  rw [show (1 : ℝ) - 2 / p = (p - 2) / p by field_simp, inv_div]
  field_simp

/-- **Stone 2 (mixed), sieve glue.**  For a `SelbergSieve` carrying the twin
density `ν(p) = 2/p` on sifted primes off `M`, whose sifted primes include every
squarefree `ℓ < Z` coprime to `M` and whose level is `≥ Z²`, the Selberg
denominator dominates the restricted twin main-term sum. -/
lemma boundingSum_ge_restrictedMainTermSum {M Z : ℕ} (h2M : 2 ∣ M)
    (hlevel : (Z : ℝ) ^ 2 ≤ s.level)
    (hcontains : ∀ ℓ, Squarefree ℓ → Nat.Coprime ℓ M → ℓ < Z → ℓ ∣ s.prodPrimes)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → ¬ p ∣ M → s.nu p = 2 / (p : ℝ)) :
    Salt.SelbergPort.selbergBoundingSum s ≥ restrictedMainTermSum M Z := by
  classical
  rw [ge_iff_le, Salt.SelbergPort.selbergBoundingSum, ← Finset.sum_filter, restrictedMainTermSum]
  set small : Finset ℕ := (Finset.range Z).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ M)
    with hsmall
  set big : Finset ℕ :=
    s.prodPrimes.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ s.level) with hbig
  have hsub : small ⊆ big := by
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓsq, hℓcop⟩ := hℓ
    rw [hbig, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨hcontains ℓ hℓsq hℓcop hℓz, BoundingSieve.prodPrimes_ne_zero⟩, ?_⟩
    have hℓR : (ℓ : ℝ) ≤ (Z : ℝ) := by exact_mod_cast (le_of_lt hℓz)
    have hℓnn : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    calc (ℓ : ℝ) ^ 2 ≤ (Z : ℝ) ^ 2 := by gcongr
      _ ≤ s.level := hlevel
  have heq : ∑ ℓ ∈ small, gTwin ℓ = ∑ ℓ ∈ small, s.selbergTerms ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓsq, hℓcop⟩ := hℓ
    exact (selbergTerms_eq_gTwin_cop s (hcontains ℓ hℓsq hℓcop hℓz) hℓcop hℓsq h2M hnu).symm
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro l hl _
  rw [hbig, Finset.mem_filter, Nat.mem_divisors] at hl
  exact le_of_lt (s.selbergTerms_pos hl.1.1)

/-- `log(⌊√Z⌋) ≥ (1/4) log Z` for `Z ≥ 100` (the nat-sqrt loses at most a factor
`4` in the log, absorbing the `√Z/2` and `−log 2` slacks). -/
lemma log_sqrt_ge {Z : ℕ} (hZ : 100 ≤ Z) :
    (1 / 4 : ℝ) * Real.log Z ≤ Real.log (Z.sqrt : ℝ) := by
  have hZpos : (0 : ℝ) < (Z : ℝ) := by
    have : (100 : ℝ) ≤ Z := by exact_mod_cast hZ
    linarith
  have hsqrtR : Real.sqrt Z - 1 < (Z.sqrt : ℝ) := by
    have := Salt.M3Assembly.sqrt_real_lt_nat_sqrt_succ Z; linarith
  have hsqrtZ_ge : (4 : ℝ) ≤ Real.sqrt Z := by
    have h100 : (100 : ℝ) ≤ Z := by exact_mod_cast hZ
    have hmono : Real.sqrt 100 ≤ Real.sqrt Z := Real.sqrt_le_sqrt (by linarith)
    have h10 : Real.sqrt 100 = 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h10] at hmono; linarith
  have hhalf : Real.sqrt Z / 2 ≤ (Z.sqrt : ℝ) := by linarith
  have hhalfpos : (0 : ℝ) < Real.sqrt Z / 2 := by linarith
  have hmono : Real.log (Real.sqrt Z / 2) ≤ Real.log (Z.sqrt : ℝ) :=
    Real.log_le_log hhalfpos hhalf
  have hlogsplit : Real.log (Real.sqrt Z / 2) = Real.log Z / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hZpos.le]
  have hlog4 : (4 : ℝ) ≤ Real.log Z :=
    Salt.M3Assembly.log_ge_four (by unfold Salt.M3Assembly.z0; omega)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  rw [hlogsplit] at hmono
  linarith

/-- **Stone 2 (mixed), the φ-restricted `(log Z)²` floor.**  For a mixed-density
`SelbergSieve` (twin density off `M`, all squarefree coprime-to-`M` `ℓ < Z`
sifted, level `≥ Z²`, `Z ≥ 100`, `2 ∣ M`, `M ≥ 1`), the Selberg denominator
grows like `(φ(M)/M)²·(log Z)²` — the mixed-density price is exactly the
`φ(M)`-factor, extracted from `copHarmonic_uniform_lower`. -/
theorem boundingSum_ge_phi_log_sq {M Z : ℕ}
    (hZ : 100 ≤ Z) (hM1 : 1 ≤ M) (h2M : 2 ∣ M)
    (hlevel : (Z : ℝ) ^ 2 ≤ s.level)
    (hcontains : ∀ ℓ, Squarefree ℓ → Nat.Coprime ℓ M → ℓ < Z → ℓ ∣ s.prodPrimes)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → ¬ p ∣ M → s.nu p = 2 / (p : ℝ)) :
    Salt.SelbergPort.selbergBoundingSum s
      ≥ (Nat.totient M / M : ℝ) ^ 2 * (1 / 16) * (Real.log Z) ^ 2 := by
  have hsqrt2 : 2 ≤ Z.sqrt := by
    have h10 : 10 ≤ Z.sqrt := Nat.le_sqrt.mpr (by omega)
    omega
  have hcop_lower := Salt.Maynard.copHarmonic_uniform_lower M Z.sqrt hM1 hsqrt2
  have hlogsqrt := log_sqrt_ge hZ
  have hphi_nn : (0 : ℝ) ≤ (Nat.totient M / M : ℝ) := by positivity
  have hlogZ_pos : (0 : ℝ) < Real.log Z := by
    have := Salt.M3Assembly.log_ge_four (show Salt.M3Assembly.z0 ≤ Z by
      unfold Salt.M3Assembly.z0; omega)
    linarith
  have hA : (Nat.totient M / M : ℝ) * ((1 / 4) * Real.log Z)
      ≤ Salt.Maynard.copHarmonic Z.sqrt M := by
    calc (Nat.totient M / M : ℝ) * ((1 / 4) * Real.log Z)
        ≤ (Nat.totient M / M : ℝ) * Real.log (Z.sqrt : ℝ) :=
          mul_le_mul_of_nonneg_left hlogsqrt hphi_nn
      _ ≤ _ := hcop_lower
  have hA_nn : (0 : ℝ) ≤ (Nat.totient M / M : ℝ) * ((1 / 4) * Real.log Z) :=
    mul_nonneg hphi_nn (by linarith [hlogZ_pos])
  have hsq : ((Nat.totient M / M : ℝ) * ((1 / 4) * Real.log Z)) ^ 2
      ≤ (Salt.Maynard.copHarmonic Z.sqrt M) ^ 2 := pow_le_pow_left₀ hA_nn hA 2
  have heq : ((Nat.totient M / M : ℝ) * ((1 / 4) * Real.log Z)) ^ 2
      = (Nat.totient M / M : ℝ) ^ 2 * (1 / 16) * (Real.log Z) ^ 2 := by ring
  rw [heq] at hsq
  have hfloor := boundingSum_ge_restrictedMainTermSum s h2M hlevel hcontains hnu
  have hrest := restrictedMainTermSum_ge M Z h2M
  linarith [hfloor, hrest, hsq]

/-! ## §3 — the assembled mixed Lemma 8′ (conditional on the instance) -/

/-- **HB 1983, Lemma 8′ (mixed / cofactor case, assembled).**  For a mixed-density
`SelbergSieve` (twin density `2/p` off `M`, density `1/p` on the odd primes of
`M`; all squarefree coprime-to-`M` `ℓ < Z` sifted, level `≥ Z²`, `Z ≥ 100`,
`2 ∣ M`), with total mass `≤ mass` and Selberg error sum `≤ E`, the sifted sum
obeys

  `siftedSum ≤ 16·(M/φ(M))²·mass / (log Z)² + E`.

Read at the mixed instance (`siftedSum = S′(d₁,d₂;Z)`, `M = 2 d₁ d₂`,
`mass = x/(d₁ d₂)`, `M/φ(M) = 2 d₁ d₂/φ(d₁ d₂)`), the constant is
`64·(d₁ d₂/φ(d₁ d₂))²·(x/(d₁ d₂))` — HB's (3.3) shape.  This is the
coprimality-restricted refinement (R2) of `Salt.HB.pairSieve_lemma8`. -/
theorem pairSieveMixed_lemma8 {M Z : ℕ} {mass E : ℝ}
    (hZ : 100 ≤ Z) (hM1 : 1 ≤ M) (h2M : 2 ∣ M)
    (hlevel : (Z : ℝ) ^ 2 ≤ s.level)
    (hcontains : ∀ ℓ, Squarefree ℓ → Nat.Coprime ℓ M → ℓ < Z → ℓ ∣ s.prodPrimes)
    (hnu : ∀ p, p.Prime → p ∣ s.prodPrimes → ¬ p ∣ M → s.nu p = 2 / (p : ℝ))
    (hmass0 : 0 ≤ mass) (hmass : s.totalMass ≤ mass)
    (herr : (∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0) ≤ E) :
    s.siftedSum ≤ 16 * ((M : ℝ) / (Nat.totient M : ℝ)) ^ 2 * mass / (Real.log Z) ^ 2 + E := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hφpos : (0 : ℝ) < (Nat.totient M : ℝ) := by
    have := Nat.totient_pos.mpr (show 0 < M by omega); exact_mod_cast this
  have hLpos : (0 : ℝ) < Real.log Z := by
    have := Salt.M3Assembly.log_ge_four (show Salt.M3Assembly.z0 ≤ Z by
      unfold Salt.M3Assembly.z0; omega)
    linarith
  have hL2pos : (0 : ℝ) < (Real.log Z) ^ 2 := pow_pos hLpos 2
  have hDpos : (0 : ℝ) < (Nat.totient M / M : ℝ) ^ 2 * (1 / 16) * (Real.log Z) ^ 2 := by
    have hφM : (0 : ℝ) < (Nat.totient M / M : ℝ) := div_pos hφpos hMR
    positivity
  have hden := boundingSum_ge_phi_log_sq s hZ hM1 h2M hlevel hcontains hnu
  have key := selberg_upper_of_bounds s hmass0 hmass hDpos hden herr
  have hφ0 : (Nat.totient M : ℝ) ≠ 0 := ne_of_gt hφpos
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMR
  have hL0 : Real.log Z ≠ 0 := ne_of_gt hLpos
  have hconv : mass / ((Nat.totient M / M : ℝ) ^ 2 * (1 / 16) * (Real.log Z) ^ 2)
      = 16 * ((M : ℝ) / (Nat.totient M : ℝ)) ^ 2 * mass / (Real.log Z) ^ 2 := by
    rw [div_eq_iff (ne_of_gt hDpos)]
    field_simp
  rw [hconv] at key
  exact key

/-! ## §4 — the mixed local density `nuMix` -/

/-- The mixed twin/AP density: `ν(p) = 1/p` for `p ∣ M` (the primes at which the
cofactor sift kills only one residue class of `t`), `ν(p) = 2/p` for `p ∤ M`
(the honest twin primes).  Completely multiplicative on squarefrees. -/
noncomputable def nuMix (M : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => (∏ p ∈ d.primeFactors, (if p ∣ M then (1 : ℝ) else 2)) / d, by simp⟩

@[simp] lemma nuMix_apply (M d : ℕ) :
    nuMix M d = (∏ p ∈ d.primeFactors, (if p ∣ M then (1 : ℝ) else 2)) / d := rfl

lemma nuMix_mult (M : ℕ) : (nuMix M).IsMultiplicative := by
  constructor
  · simp [nuMix_apply]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [Nat.coprime_zero_left] at hmn; subst hmn; simp [nuMix_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.coprime_zero_right] at hmn; subst hmn; simp [nuMix_apply]
    rw [nuMix_apply, nuMix_apply, nuMix_apply, Nat.primeFactors_mul hm hn,
      Finset.prod_union (Nat.Coprime.disjoint_primeFactors hmn), Nat.cast_mul, mul_div_mul_comm]

lemma nuMix_pos (M p : ℕ) (hp : p.Prime) : 0 < nuMix M p := by
  rw [nuMix_apply, hp.primeFactors, Finset.prod_singleton]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

lemma nuMix_lt_one (M p : ℕ) (hp : p.Prime) (h2M : 2 ∣ M) : nuMix M p < 1 := by
  rw [nuMix_apply, hp.primeFactors, Finset.prod_singleton]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  split_ifs with h
  · rw [div_lt_one hp0]; linarith
  · have hpne2 : p ≠ 2 := by rintro rfl; exact h h2M
    have hp3 : 3 ≤ p := by
      rcases Nat.eq_or_lt_of_le hp.two_le with heq | hlt
      · exact absurd heq.symm hpne2
      · exact hlt
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    rw [div_lt_one hp0]; linarith

lemma nuMix_eq_two_div (M p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) : nuMix M p = 2 / (p : ℝ) := by
  rw [nuMix_apply, hp.primeFactors, Finset.prod_singleton, if_neg hpM]

/-! ## §4a — the cofactor sift map and its injectivity -/

/-- On the AP-pair window, the cofactor product is the twin product divided by
`d₁ d₂`: `(n/d₁)·((n+2)/d₂) = n(n+2)/(d₁ d₂)` (exact, since `d₁ ∣ n`,
`d₂ ∣ (n+2)`). -/
lemma cofProd_eq_twinDiv {d₁ d₂ n : ℕ} (h1 : d₁ ∣ n) (h2 : d₂ ∣ (n + 2)) :
    (n / d₁) * ((n + 2) / d₂) = n * (n + 2) / (d₁ * d₂) :=
  Nat.div_mul_div_comm h1 h2

/-- **The cofactor sift is injective on the window.**  Since it factors as
`twinProd / (d₁ d₂)` with `d₁ d₂ ∣ twinProd`, injectivity reduces to the global
injectivity of `n ↦ n(n+2)`. -/
lemma cofProd_injOn (x d₁ d₂ : ℕ) (hcop : Nat.Coprime d₁ d₂) :
    ∀ a ∈ baseSet x d₁ d₂, ∀ b ∈ baseSet x d₁ d₂,
      (a / d₁) * ((a + 2) / d₂) = (b / d₁) * ((b + 2) / d₂) → a = b := by
  intro a ha b hb heq
  rw [baseSet, Finset.mem_filter] at ha hb
  obtain ⟨_, ha1, ha2⟩ := ha
  obtain ⟨_, hb1, hb2⟩ := hb
  rw [cofProd_eq_twinDiv ha1 ha2, cofProd_eq_twinDiv hb1 hb2] at heq
  have hWa : d₁ * d₂ ∣ a * (a + 2) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (ha1.mul_right _) (ha2.mul_left _)
  have hWb : d₁ * d₂ ∣ b * (b + 2) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (hb1.mul_right _) (hb2.mul_left _)
  have hprod : a * (a + 2) = b * (b + 2) := by
    have hc := congrArg (fun q => d₁ * d₂ * q) heq
    simp only [Nat.mul_div_cancel' hWa, Nat.mul_div_cancel' hWb] at hc
    exact hc
  exact Salt.TwinSieve.twinProd_injective hprod

/-! ## §4b — the mixed-density Selberg instance -/

/-- The mixed-density AP-pair `BoundingSieve`: sifts the **cofactor products**
`(n/d₁)·((n+2)/d₂)` for `n` in the AP-pair window by the primes dividing
`primorial Z`, with mixed density `ν = nuMix (2 d₁ d₂)` and total mass
`x/(d₁ d₂)`. -/
noncomputable def mixBoundingSieve (x d₁ d₂ Z : ℕ) : BoundingSieve where
  support := (baseSet x d₁ d₂).image (fun n => (n / d₁) * ((n + 2) / d₂))
  prodPrimes := primorial Z
  prodPrimes_squarefree := Salt.M5Assembly.primorial_squarefree Z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (x : ℝ) / (d₁ * d₂)
  nu := nuMix (2 * (d₁ * d₂))
  nu_mult := nuMix_mult _
  nu_pos_of_prime := fun p hp _ => nuMix_pos _ p hp
  nu_lt_one_of_prime := fun p hp _ => nuMix_lt_one _ p hp (dvd_mul_right 2 (d₁ * d₂))

/-- The mixed-density AP-pair `SelbergSieve`, with level `Z²`. -/
noncomputable def mixPairSieve (x d₁ d₂ Z : ℕ) (hZ : 1 ≤ Z) : SelbergSieve where
  toBoundingSieve := mixBoundingSieve x d₁ d₂ Z
  level := (Z : ℝ) ^ 2
  one_le_level := by
    have hZ1 : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
    nlinarith

variable {x d₁ d₂ Z : ℕ} {hZ : 1 ≤ Z}

@[simp] lemma mixPairSieve_prodPrimes :
    (mixPairSieve x d₁ d₂ Z hZ).prodPrimes = primorial Z := rfl
@[simp] lemma mixPairSieve_totalMass :
    (mixPairSieve x d₁ d₂ Z hZ).totalMass = (x : ℝ) / (d₁ * d₂) := rfl
@[simp] lemma mixPairSieve_level : (mixPairSieve x d₁ d₂ Z hZ).level = (Z : ℝ) ^ 2 := rfl
@[simp] lemma mixPairSieve_nu : (mixPairSieve x d₁ d₂ Z hZ).nu = nuMix (2 * (d₁ * d₂)) := rfl

/-- `siftedSum` counts `n` in the window whose cofactor product `(n/d₁)((n+2)/d₂)`
is coprime to `primorial Z` — the honest `S′(d₁,d₂;Z)`. -/
lemma mixPairSieve_siftedSum (hcop : Nat.Coprime d₁ d₂) :
    (mixPairSieve x d₁ d₂ Z hZ).siftedSum
      = (((baseSet x d₁ d₂).filter
          (fun n => Nat.Coprime (primorial Z) ((n / d₁) * ((n + 2) / d₂)))).card : ℝ) := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ (baseSet x d₁ d₂).image (fun n => (n / d₁) * ((n + 2) / d₂)),
      if Nat.Coprime (primorial Z) m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (cofProd_injOn x d₁ d₂ hcop),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `multSum d` counts `n` in the window with `d ∣ (n/d₁)((n+2)/d₂)`. -/
lemma mixPairSieve_multSum (hcop : Nat.Coprime d₁ d₂) (d : ℕ) :
    (mixPairSieve x d₁ d₂ Z hZ).multSum d
      = (((baseSet x d₁ d₂).filter
          (fun n => d ∣ (n / d₁) * ((n + 2) / d₂))).card : ℝ) := by
  change (∑ m ∈ (baseSet x d₁ d₂).image (fun n => (n / d₁) * ((n + 2) / d₂)),
      if d ∣ m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (cofProd_injOn x d₁ d₂ hcop),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## §4c — the assembled concrete mixed Lemma 8′ (modulo the Selberg error sum)

The mixed instance's total mass, level, sifted set, and local density are all
discharged here; the only remaining input is the **Selberg error sum bound**
`herr`, i.e. the `3^ω`-weighted remainder `Σ_{d∣P, d≤Z²} 3^{ω(d)}|rem d|`.  For
the mixed instance this is the honest analogue of `hbPairSieve_errSum_le`
(`Salt.HB.PairInstance`): the AP-pair CRT count of the cofactor-sift residue set
`{r < d·d₁d₂ : d₁∣r, d₂∣(r+2), d ∣ (r/d₁)(r+2/d₂)}` equals
`∏_{p∣d}(if p ∣ 2d₁d₂ then 1 else 2)`, giving `|rem d| ≤ 2·ρ_mix(d) ≤ 2^{ω(d)+1}`
via `Salt.HB.congCount_Ioc_bound`, hence a crude `O(Z⁸)` bound as in the rough
case.  That residue-count identity (a mixed CRT + field-root count, unlike the
`z`-rough `card_apResidues`) is the residual R2-instance; feeding any explicit
`E` here completes the mixed Lemma 8′ unconditionally. -/

/-- **HB 1983, Lemma 8′ (mixed / cofactor case, concrete AP-pair instance).**
For `Z ≥ 100`, `d₁, d₂` a positive odd coprime pair (**no roughness assumption**),
the honest cofactor-sifted count over the AP window obeys

  `S′(d₁,d₂;Z) ≤ 64·(d₁d₂/φ(d₁d₂))²·(x/(d₁d₂))/(log Z)² + E`,

where `S′(d₁,d₂;Z) = #{n ∈ (x,2x] : d₁∣n, d₂∣(n+2), ((n/d₁)(n+2/d₂), P(Z)) = 1}`
and `E` bounds the mixed Selberg error sum.  The `(d₁d₂/φ(d₁d₂))²` factor is the
mixed-density price (R2), delivered by `Salt.HB.pairSieveMixed_lemma8`. -/
theorem hb_lemma8' (hZ : 100 ≤ Z) (hZ1 : 1 ≤ Z) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (ho1 : Odd d₁) (ho2 : Odd d₂) (hcop12 : Nat.Coprime d₁ d₂) {E : ℝ}
    (herr : (∑ d ∈ (mixPairSieve x d₁ d₂ Z hZ1).prodPrimes.divisors,
        if (d : ℝ) ≤ (mixPairSieve x d₁ d₂ Z hZ1).level then
          (3 : ℝ) ^ ω d * |(mixPairSieve x d₁ d₂ Z hZ1).rem d| else 0) ≤ E) :
    (((baseSet x d₁ d₂).filter
        (fun n => Nat.Coprime (primorial Z) ((n / d₁) * ((n + 2) / d₂)))).card : ℝ)
      ≤ 64 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
          / (Real.log Z) ^ 2 + E := by
  have h2M : (2 : ℕ) ∣ 2 * (d₁ * d₂) := dvd_mul_right 2 _
  have hM1 : 1 ≤ 2 * (d₁ * d₂) := by have := Nat.mul_pos hd₁ hd₂; omega
  have hlevel : (Z : ℝ) ^ 2 ≤ (mixPairSieve x d₁ d₂ Z hZ1).level := by
    rw [mixPairSieve_level]
  have hcontains : ∀ ℓ, Squarefree ℓ → Nat.Coprime ℓ (2 * (d₁ * d₂)) → ℓ < Z →
      ℓ ∣ (mixPairSieve x d₁ d₂ Z hZ1).prodPrimes := by
    intro ℓ hℓsq _ hℓz
    rw [mixPairSieve_prodPrimes]
    exact (Squarefree.dvd_primorial hℓsq).trans (primorial_dvd_primorial (le_of_lt hℓz))
  have hnu : ∀ p, p.Prime → p ∣ (mixPairSieve x d₁ d₂ Z hZ1).prodPrimes →
      ¬ p ∣ 2 * (d₁ * d₂) → (mixPairSieve x d₁ d₂ Z hZ1).nu p = 2 / (p : ℝ) := by
    intro p hp _ hpM
    rw [mixPairSieve_nu, nuMix_eq_two_div _ p hp hpM]
  have hmass0 : (0 : ℝ) ≤ (x : ℝ) / (d₁ * d₂) := by positivity
  have hmass : (mixPairSieve x d₁ d₂ Z hZ1).totalMass ≤ (x : ℝ) / (d₁ * d₂) :=
    le_of_eq mixPairSieve_totalMass
  have key := pairSieveMixed_lemma8 (mixPairSieve x d₁ d₂ Z hZ1)
    (M := 2 * (d₁ * d₂)) (mass := (x : ℝ) / (d₁ * d₂)) (E := E)
    hZ hM1 h2M hlevel hcontains hnu hmass0 hmass herr
  rw [mixPairSieve_siftedSum hcop12] at key
  have hodd : Odd (d₁ * d₂) := ho1.mul ho2
  have hnd : ¬ (2 : ℕ) ∣ (d₁ * d₂) := by
    have hm := Nat.odd_iff.mp hodd; omega
  have hcop2 : Nat.Coprime 2 (d₁ * d₂) := Nat.prime_two.coprime_iff_not_dvd.mpr hnd
  have hφ : Nat.totient (2 * (d₁ * d₂)) = Nat.totient (d₁ * d₂) := by
    rw [Nat.totient_mul hcop2, Nat.totient_two, one_mul]
  rw [hφ] at key
  have hconv : (16 : ℝ) * ((↑(2 * (d₁ * d₂)) / (Nat.totient (d₁ * d₂) : ℝ)) ^ 2)
        * ((x : ℝ) / (d₁ * d₂)) / (Real.log Z) ^ 2
      = 64 * ((d₁ * d₂ : ℝ) / (Nat.totient (d₁ * d₂))) ^ 2 * ((x : ℝ) / (d₁ * d₂))
          / (Real.log Z) ^ 2 := by
    push_cast; ring
  rw [hconv] at key
  exact key

end Salt.HB
