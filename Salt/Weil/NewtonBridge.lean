/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.LFunction
import Salt.Weil.Orbits
import Mathlib

/-!
# Weil track, node W2T6.H3 — the finite Newton identity (the UFD bridge)

Blueprint: `docs/exploration/w2t6-design.md` §5 (H3) and §10 (frozen statement).

This is the finite, purely combinatorial Newton identity relating the "complete" monic
coefficient sums `aCoeff` (Harcos's `a_d`) to the von-Mangoldt / log-derivative sums
`cCoeffN` (the irreducible-power sums `c_j`):
```
  n · a_n = ∑_{j ∈ Icc 1 n} a_{n-j} · c_j.
```
The heart is the factorization reindex `(k', π, r) ↔ K` where `K = k' · π^r` ranges over the
monic degree-`n` polynomials of `𝔽_p[X]`: each monic `K` decomposes uniquely, and the
multiplicity-weighted degree sum `∑_{π^r ∣ K} deg π = deg K = n` collapses the double sum.
No power series, no infinite Euler product — the content the rejected `PowerSeries.log` route
would also have to prove, here with the least scaffolding.

**Coordination note.** The in-flight `Salt/Weil/MomentOrbit.lean` defines a `cCoeff` and an
`irredMonicOfDeg` with the *same underlying sum* as the `cCoeffN` / `irredMonicOfDegN` here;
the two are definitionally the same object (irreducible monic degree-`d` polynomials via the
`tuplePoly` coefficient filter). The house unifies them at assembly (a `cCoeff = cCoeffN`
bridge or a rename). This file imports neither `MomentOrbit` nor `.All`.
-/

namespace Salt.Weil

open scoped BigOperators
open Polynomial UniqueFactorizationMonoid

variable {p : ℕ} [Fact p.Prime]

/-! ### The finite index sets: monic / irreducible-monic polynomials -/

/-- The Finset of monic degree-`d` polynomials of `𝔽_p[X]`, as the image of the coefficient
tuple map `tuplePoly` (avoiding the missing `Finite {k // Monic ∧ natDegree = d}`). -/
noncomputable def monicOfDegN (p : ℕ) [Fact p.Prime] (d : ℕ) : Finset (ZMod p)[X] :=
  Finset.univ.image (fun c : Fin d → ZMod p => tuplePoly c)

open Classical in
/-- The Finset of irreducible monic degree-`d` polynomials. -/
noncomputable def irredMonicOfDegN (p : ℕ) [Fact p.Prime] (d : ℕ) : Finset (ZMod p)[X] :=
  (monicOfDegN p d).filter Irreducible

/-- The Finset of irreducible monic polynomials of degree `≤ n`. -/
noncomputable def irrLe (p : ℕ) [Fact p.Prime] (n : ℕ) : Finset (ZMod p)[X] :=
  (Finset.range (n + 1)).biUnion (irredMonicOfDegN p)

/-- **Harcos's `c_n`** (freeze §10 shape):
`c_n = ∑_{d ∣ n} d · ∑_{π irred monic, deg π = d} η(π)^{n/d}`. -/
noncomputable def cCoeffN (a b : ZMod p) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (d : ℂ) * ∑ k ∈ irredMonicOfDegN p d, eta a b k ^ (n / d)

/-! ### `tuplePoly` is injective; membership in the index sets -/

theorem tuplePoly_injective {d : ℕ} {c₁ c₂ : Fin d → ZMod p}
    (h : tuplePoly c₁ = tuplePoly c₂) : c₁ = c₂ := by
  funext i
  have h1 := tuplePoly_coeff c₁ i.isLt
  have h2 := tuplePoly_coeff c₂ i.isLt
  rw [h] at h1
  have : c₁ ⟨(i : ℕ), i.isLt⟩ = c₂ ⟨(i : ℕ), i.isLt⟩ := h1.symm.trans h2
  simpa using this

theorem mem_monicOfDegN {d : ℕ} {K : (ZMod p)[X]} :
    K ∈ monicOfDegN p d ↔ K.Monic ∧ K.natDegree = d := by
  constructor
  · intro hK
    rw [monicOfDegN, Finset.mem_image] at hK
    obtain ⟨c, _, rfl⟩ := hK
    exact ⟨tuplePoly_monic c, tuplePoly_natDegree c⟩
  · rintro ⟨hM, hd⟩
    rw [monicOfDegN, Finset.mem_image]
    refine ⟨fun i : Fin d => K.coeff i, Finset.mem_univ _, ?_⟩
    have hcd : K.coeff d = 1 := by have h := hM.coeff_natDegree; rwa [hd] at h
    have hsum : K = ∑ i ∈ Finset.range (d + 1), C (K.coeff i) * X ^ i :=
      Polynomial.as_sum_range_C_mul_X_pow' K (by rw [hd]; exact Nat.lt_succ_self d)
    rw [Finset.sum_range_succ, hcd, map_one, one_mul] at hsum
    rw [tuplePoly, Fin.sum_univ_eq_sum_range (fun i => C (K.coeff i) * X ^ i) d, add_comm]
    exact hsum.symm

theorem mem_irredMonicOfDegN {d : ℕ} {k : (ZMod p)[X]} :
    k ∈ irredMonicOfDegN p d ↔ k.Monic ∧ k.natDegree = d ∧ Irreducible k := by
  classical
  rw [irredMonicOfDegN, Finset.mem_filter, mem_monicOfDegN]
  tauto

theorem mem_irrLe {n : ℕ} {k : (ZMod p)[X]} :
    k ∈ irrLe p n ↔ k.Monic ∧ Irreducible k ∧ k.natDegree ≤ n := by
  rw [irrLe, Finset.mem_biUnion]
  constructor
  · rintro ⟨d, hd, hk⟩
    rw [Finset.mem_range, Nat.lt_succ_iff] at hd
    rw [mem_irredMonicOfDegN] at hk
    exact ⟨hk.1, hk.2.2, hk.2.1 ▸ hd⟩
  · rintro ⟨hM, hirr, hle⟩
    refine ⟨k.natDegree, Finset.mem_range.mpr (Nat.lt_succ_of_le hle), ?_⟩
    rw [mem_irredMonicOfDegN]
    exact ⟨hM, rfl, hirr⟩

/-- **`aCoeff` as a sum over monic polynomials.** -/
theorem aCoeff_sum (a b : ZMod p) (d : ℕ) :
    aCoeff a b d = ∑ K ∈ monicOfDegN p d, eta a b K := by
  rw [aCoeff_eq]
  refine (Finset.sum_image ?_).symm
  intro c₁ _ c₂ _ h
  exact tuplePoly_injective h

/-- The Finset of prime-power pairs `(π, r)` with `π` irreducible monic and `deg π · r ≤ n`. -/
noncomputable def ppPairs (p : ℕ) [Fact p.Prime] (n : ℕ) : Finset ((ZMod p)[X] × ℕ) :=
  (irrLe p n ×ˢ Finset.Icc 1 n).filter (fun q => q.1.natDegree * q.2 ≤ n)

/-! ### The UFD collapse: `∑_{π^r ∣ K} deg π = deg K` -/

/-- For irreducible monic `π` and `K ≠ 0`, `π^r ∣ K` iff `r` is at most the multiplicity of `π`. -/
theorem pow_dvd_iff_le_count {π K : (ZMod p)[X]} (hmon : π.Monic) (hirr : Irreducible π)
    (hK : K ≠ 0) (r : ℕ) :
    π ^ r ∣ K ↔ r ≤ Multiset.count π (normalizedFactors K) := by
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
        (pow_ne_zero r hmon.ne_zero) hK,
      Irreducible.normalizedFactors_pow hirr, hmon.normalize_eq_self,
      Multiset.le_count_iff_replicate_le]

/-- The degrees of the (monic) irreducible factors of a monic `K` sum to `deg K`. -/
theorem sum_natDegree_normalizedFactors {K : (ZMod p)[X]} (hK : K.Monic) :
    ((normalizedFactors K).map Polynomial.natDegree).sum = K.natDegree := by
  rw [← Polynomial.natDegree_multiset_prod _
        (UniqueFactorizationMonoid.zero_notMem_normalizedFactors K),
      UniqueFactorizationMonoid.prod_normalizedFactors_eq hK.ne_zero, hK.normalize_eq_self]

open Classical in
/-- **The multiplicity-weighted degree collapse.** For monic `K` of degree `n`, the total degree
`∑ deg π` over prime-power divisors `(π, r)` with `π^r ∣ K` equals `deg K = n`. -/
theorem weightSum_eq {n : ℕ} {K : (ZMod p)[X]} (hK : K ∈ monicOfDegN p n) :
    ∑ q ∈ (ppPairs p n).filter (fun q => q.1 ^ q.2 ∣ K), q.1.natDegree = n := by
  classical
  rw [mem_monicOfDegN] at hK
  obtain ⟨hKmon, hKdeg⟩ := hK
  have hK0 : K ≠ 0 := hKmon.ne_zero
  unfold ppPairs
  rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
  have key : ∀ π ∈ irrLe p n,
      (∑ r ∈ Finset.Icc 1 n, if π.natDegree * r ≤ n ∧ π ^ r ∣ K then π.natDegree else 0)
        = π.natDegree * Multiset.count π (normalizedFactors K) := by
    intro π hπ
    rw [mem_irrLe] at hπ
    obtain ⟨hπmon, hπirr, _⟩ := hπ
    have hcount : Multiset.count π (normalizedFactors K) ≤ n := by
      have hdvd : π ^ Multiset.count π (normalizedFactors K) ∣ K :=
        (pow_dvd_iff_le_count hπmon hπirr hK0 _).mpr le_rfl
      have hle := Polynomial.natDegree_le_of_dvd hdvd hK0
      rw [hπmon.natDegree_pow, hKdeg] at hle
      exact le_trans (Nat.le_mul_of_pos_right _ hπirr.natDegree_pos) hle
    rw [← Finset.sum_filter]
    have hfilt : (Finset.Icc 1 n).filter (fun r => π.natDegree * r ≤ n ∧ π ^ r ∣ K)
        = Finset.Icc 1 (Multiset.count π (normalizedFactors K)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, _, hdvd⟩
        exact ⟨h1, (pow_dvd_iff_le_count hπmon hπirr hK0 r).mp hdvd⟩
      · rintro ⟨h1, hr⟩
        have hdvd : π ^ r ∣ K := (pow_dvd_iff_le_count hπmon hπirr hK0 r).mpr hr
        have hdeg : π.natDegree * r ≤ n := by
          have h := Polynomial.natDegree_le_of_dvd hdvd hK0
          rw [hπmon.natDegree_pow, hKdeg, mul_comm] at h
          exact h
        exact ⟨⟨h1, hr.trans hcount⟩, hdeg, hdvd⟩
    rw [hfilt, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl key]
  have hsub : (normalizedFactors K).toFinset ⊆ irrLe p n := by
    intro π hπ
    rw [Multiset.mem_toFinset] at hπ
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor π hπ
    have hne : π ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
    have hmon : π.Monic := by
      have h1 := UniqueFactorizationMonoid.normalize_normalized_factor π hπ
      have h2 := Polynomial.monic_normalize hne
      rwa [h1] at h2
    have hle : π.natDegree ≤ n := by
      have := Polynomial.natDegree_le_of_dvd
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hπ) hK0
      rwa [hKdeg] at this
    exact mem_irrLe.mpr ⟨hmon, hirr, hle⟩
  have hzero : ∀ π ∈ irrLe p n, π ∉ (normalizedFactors K).toFinset →
      π.natDegree * Multiset.count π (normalizedFactors K) = 0 := by
    intro π _ hπ
    rw [Multiset.mem_toFinset] at hπ
    rw [Multiset.count_eq_zero.mpr hπ, mul_zero]
  rw [← Finset.sum_subset hsub hzero, ← hKdeg, ← sum_natDegree_normalizedFactors hKmon,
    Finset.sum_multiset_map_count]
  exact Finset.sum_congr rfl (fun π _ => by rw [smul_eq_mul, mul_comm])

/-! ### The per-pair collapse (η multiplicativity + cofactor bijection) -/

open Classical in
/-- **The per-pair collapse.** For monic `π` with `deg π · r ≤ n`, the term
`deg π · η(π)^r · a_{n - deg π · r}` equals the sum of `deg π · η(K)` over the monic degree-`n`
polynomials `K` divisible by `π^r` (the cofactor `k'` ranges over `monicOfDegN (n - deg π · r)`). -/
theorem key2 (a b : ZMod p) {π : (ZMod p)[X]} (hπmon : π.Monic) {r n : ℕ}
    (hle : π.natDegree * r ≤ n) :
    (π.natDegree : ℂ) * eta a b π ^ r * aCoeff a b (n - π.natDegree * r)
      = ∑ K ∈ (monicOfDegN p n).filter (fun K => π ^ r ∣ K), (π.natDegree : ℂ) * eta a b K := by
  classical
  have hπr : (π ^ r).Monic := hπmon.pow r
  rw [← eta_pow a b hπmon, aCoeff_sum, mul_assoc, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_bij' (fun k' _ => π ^ r * k') (fun K _ => K /ₘ π ^ r) ?_ ?_ ?_ ?_ ?_
  · intro k' hk'
    rw [mem_monicOfDegN] at hk'
    obtain ⟨hk'mon, hk'deg⟩ := hk'
    rw [Finset.mem_filter, mem_monicOfDegN]
    refine ⟨⟨hπr.mul hk'mon, ?_⟩, dvd_mul_right _ _⟩
    rw [hπr.natDegree_mul hk'mon, hπmon.natDegree_pow, hk'deg, mul_comm r π.natDegree]
    omega
  · intro K hK
    rw [Finset.mem_filter, mem_monicOfDegN] at hK
    obtain ⟨⟨hKmon, hKdeg⟩, hdvd⟩ := hK
    have hKeq : π ^ r * (K /ₘ π ^ r) = K := by
      have hmod : K %ₘ π ^ r = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hπr).mpr hdvd
      have h := Polynomial.modByMonic_add_div K (π ^ r)
      rwa [hmod, zero_add] at h
    rw [mem_monicOfDegN]
    have hpq : (π ^ r * (K /ₘ π ^ r)).Monic := by rw [hKeq]; exact hKmon
    refine ⟨hπr.of_mul_monic_left hpq, ?_⟩
    rw [Polynomial.natDegree_divByMonic K hπr, hKdeg, hπmon.natDegree_pow, mul_comm r π.natDegree]
  · intro k' _
    exact mul_divByMonic_cancel_left k' hπr
  · intro K hK
    rw [Finset.mem_filter, mem_monicOfDegN] at hK
    obtain ⟨_, hdvd⟩ := hK
    have hmod : K %ₘ π ^ r = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hπr).mpr hdvd
    have h := Polynomial.modByMonic_add_div K (π ^ r)
    rwa [hmod, zero_add] at h
  · intro k' hk'
    rw [mem_monicOfDegN] at hk'
    rw [eta_mul a b hπr hk'.1]

/-! ### The reindex: RHS as a sum over prime-power pairs -/

open Classical in
/-- **`cCoeffN` as a sum over prime-power pairs of fixed size.** The divisor-indexed sum defining
`c_j` reindexes (via `(d, π) ↦ (π, j/d)`, `d = deg π`) to a sum over pairs `(π, r)` with
`deg π · r = j`. -/
theorem cCoeffN_eq (a b : ZMod p) {j n : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    cCoeffN a b j
      = ∑ q ∈ (ppPairs p n).filter (fun q => q.1.natDegree * q.2 = j),
          (q.1.natDegree : ℂ) * eta a b q.1 ^ q.2 := by
  classical
  have hj0 : j ≠ 0 := by omega
  rw [cCoeffN]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => (x.2, j / x.1)) (fun q _ => ⟨q.1.natDegree, q.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_sigma, Nat.mem_divisors, mem_irredMonicOfDegN] at hx
    obtain ⟨⟨hdvd, _⟩, hmon, hdeg, hirr⟩ := hx
    have hx1pos : 0 < x.1 := hdeg ▸ hirr.natDegree_pos
    have hcancel : x.2.natDegree * (j / x.1) = j := by rw [hdeg, Nat.mul_div_cancel' hdvd]
    rw [Finset.mem_filter]
    refine ⟨?_, hcancel⟩
    unfold ppPairs
    rw [Finset.mem_filter, Finset.mem_product, mem_irrLe, Finset.mem_Icc]
    refine ⟨⟨⟨hmon, hirr, by rw [hdeg]; exact le_trans (Nat.le_of_dvd (by omega) hdvd) hjn⟩,
      ?_, ?_⟩, by rw [hcancel]; exact hjn⟩
    · rw [Nat.one_le_div_iff hx1pos]; exact Nat.le_of_dvd (by omega) hdvd
    · exact le_trans (Nat.div_le_self j x.1) hjn
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqpp, hqeq⟩ := hq
    unfold ppPairs at hqpp
    rw [Finset.mem_filter, Finset.mem_product, mem_irrLe] at hqpp
    obtain ⟨⟨⟨hmon, hirr, _⟩, _⟩, _⟩ := hqpp
    rw [Finset.mem_sigma, Nat.mem_divisors, mem_irredMonicOfDegN]
    exact ⟨⟨⟨q.2, hqeq.symm⟩, hj0⟩, hmon, rfl, hirr⟩
  · rintro ⟨x1, x2⟩ hx
    rw [Finset.mem_sigma, mem_irredMonicOfDegN] at hx
    obtain ⟨_, _, hdeg, _⟩ := hx
    dsimp only
    rw [hdeg]
  · rintro ⟨q1, q2⟩ hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqpp, hqeq⟩ := hq
    unfold ppPairs at hqpp
    rw [Finset.mem_filter, Finset.mem_product, mem_irrLe] at hqpp
    obtain ⟨⟨⟨_, hirr, _⟩, _⟩, _⟩ := hqpp
    have hpos : 0 < q1.natDegree := hirr.natDegree_pos
    have hval : j / q1.natDegree = q2 := by rw [← hqeq, Nat.mul_div_cancel_left q2 hpos]
    dsimp only
    rw [hval]
  · rintro ⟨x1, x2⟩ hx
    rw [Finset.mem_sigma, mem_irredMonicOfDegN] at hx
    obtain ⟨_, _, hdeg, _⟩ := hx
    dsimp only
    rw [hdeg]

/-- **The RHS as a sum over prime-power pairs.** Combining `cCoeffN_eq` (per `j`) with the
fiberwise grouping `(π, r) ↦ deg π · r` turns the divisor-indexed RHS into a single sum over
`ppPairs`. -/
theorem newton_rhs_pp (a b : ZMod p) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, aCoeff a b (n - j) * cCoeffN a b j
      = ∑ q ∈ ppPairs p n,
          (q.1.natDegree : ℂ) * eta a b q.1 ^ q.2 * aCoeff a b (n - q.1.natDegree * q.2) := by
  classical
  have hmaps : ∀ q ∈ ppPairs p n, q.1.natDegree * q.2 ∈ Finset.Icc 1 n := by
    intro q hq
    unfold ppPairs at hq
    rw [Finset.mem_filter, Finset.mem_product, mem_irrLe, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨_, hirr, _⟩, hr1, _⟩, hle⟩ := hq
    rw [Finset.mem_Icc]
    exact ⟨Nat.mul_pos hirr.natDegree_pos hr1, hle⟩
  have hL : ∑ j ∈ Finset.Icc 1 n, aCoeff a b (n - j) * cCoeffN a b j
      = ∑ j ∈ Finset.Icc 1 n, ∑ q ∈ (ppPairs p n).filter (fun q => q.1.natDegree * q.2 = j),
          (q.1.natDegree : ℂ) * eta a b q.1 ^ q.2 * aCoeff a b (n - q.1.natDegree * q.2) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    rw [cCoeffN_eq a b hj.1 hj.2, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mem_filter] at hq
    rw [hq.2]; ring
  rw [hL, Finset.sum_fiberwise_of_maps_to hmaps]

/-! ### Assembly: the Newton identity -/

/-- **H3 — the finite Newton identity (the UFD bridge).** For `n ≥ 1`,
`n · a_n = ∑_{j ∈ Icc 1 n} a_{n-j} · c_j` where `a_d = aCoeff` and `c_j = cCoeffN`. Proved by the
factorization reindex `K = k' · π^r`: each term collapses (`key2`) to a sum over monic degree-`n`
`K` divisible by `π^r`; swapping order and applying the multiplicity-weighted degree collapse
(`weightSum_eq`) yields `∑_K η(K) · n = n · a_n`. Hypothesis-free in `a, b` (holds even at `ab = 0`;
gate-verified at `p = 3, 5, 7`). -/
theorem newton_bridge (a b : ZMod p) (n : ℕ) (_hn : 1 ≤ n) :
    (n : ℂ) * aCoeff a b n = ∑ j ∈ Finset.Icc 1 n, aCoeff a b (n - j) * cCoeffN a b j := by
  classical
  have hterm : ∀ q ∈ ppPairs p n,
      (q.1.natDegree : ℂ) * eta a b q.1 ^ q.2 * aCoeff a b (n - q.1.natDegree * q.2)
        = ∑ K ∈ (monicOfDegN p n).filter (fun K => q.1 ^ q.2 ∣ K),
            (q.1.natDegree : ℂ) * eta a b K := by
    intro q hq
    unfold ppPairs at hq
    rw [Finset.mem_filter, Finset.mem_product, mem_irrLe] at hq
    obtain ⟨⟨⟨hmon, _, _⟩, _⟩, hle⟩ := hq
    exact key2 a b hmon hle
  have hR : ∑ q ∈ ppPairs p n, ∑ K ∈ (monicOfDegN p n).filter (fun K => q.1 ^ q.2 ∣ K),
        (q.1.natDegree : ℂ) * eta a b K
      = ∑ K ∈ monicOfDegN p n, eta a b K * (n : ℂ) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun K hK => ?_)
    rw [← Finset.sum_filter, Finset.sum_congr rfl
        (fun q _ => mul_comm ((q.1.natDegree : ℂ)) (eta a b K)),
      ← Finset.mul_sum, ← Nat.cast_sum, weightSum_eq hK]
  rw [newton_rhs_pp, Finset.sum_congr rfl hterm, hR, aCoeff_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun K _ => mul_comm _ _)

end Salt.Weil
