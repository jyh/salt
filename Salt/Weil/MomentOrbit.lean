/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.LFunction
import Salt.Weil.Orbits
import Salt.Weil.ArtinSchreier
import Mathlib

/-!
# Weil track, node W2T6.H1 — the orbit reorganization

Blueprint: `docs/exploration/w2t6-design.md` (§5, the H1 node). Harcos Thm 6, equation (10):
the twisted Kloosterman moment over `𝔽_{p^n}` reorganizes as the irreducible-factor sum
```
kloostermanMoment a b n = ∑_{d ∣ n} d · ∑_{k irred. monic, deg = d} η(k)^{n/d}.
```

* **`irredMonicOfDeg p d`** — the finite set of irreducible monic degree-`d` polynomials over
  `𝔽_p`, built from the coefficient-tuple picture (`tuplePoly`) filtered by `Irreducible`.
* **`cCoeff a b n`** — the irreducible / log-derivative sum `∑_{d ∣ n} d ∑_{k} η(k)^{n/d}`.
* **`kloostermanMoment_eq_cCoeff`** (H1) — the reorganization, for all `a, b` and `n ≠ 0`.

The proof combines **H1a** (each root `x` of an irreducible monic `k` of degree `d ∣ n` has
`ψ(Tr_n(a·x + b·x⁻¹)) = η(k)^{n/d}`, via the Frobenius-orbit trace sum + Vieta) with **H1b**
(the fiber of `minpoly` over `k` has exactly `deg k` roots, via `card_rootSet_eq_natDegree`).
-/

namespace Salt.Weil

open Polynomial
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-! ### The irreducible-monic finite set and the coefficient sum `c_n` -/

open Classical in
/-- The finite set of irreducible monic polynomials of degree `d` over `𝔽_p`, realised as the
`Irreducible`-filtered image of the coefficient tuples `Fin d → 𝔽_p` under `tuplePoly`. -/
noncomputable def irredMonicOfDeg (p d : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] :=
  ((Finset.univ : Finset (Fin d → ZMod p)).image tuplePoly).filter (fun k => Irreducible k)

open Classical in
/-- **The irreducible / log-derivative sum** `c_n = ∑_{d ∣ n} d · ∑_{k} η(k)^{n/d}` (the inner
sum over irreducible monic `k` of degree `d`). Harcos eq. (10)'s Newton-convolution term. -/
noncomputable def cCoeff (a b : ZMod p) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (d : ℂ) * ∑ k ∈ irredMonicOfDeg p d, eta a b k ^ (n / d)

/-- Every monic polynomial of degree `d` is `tuplePoly` of its low coefficients. -/
theorem monic_eq_tuplePoly {d : ℕ} {k : (ZMod p)[X]} (hk : k.Monic) (hd : k.natDegree = d) :
    k = tuplePoly (fun i : Fin d => k.coeff i) := by
  apply Polynomial.ext
  intro j
  rcases lt_trichotomy j d with hj | hj | hj
  · rw [tuplePoly_coeff _ hj]
  · rw [hj]
    have hkd : k.coeff d = 1 := by rw [← hd]; exact hk.coeff_natDegree
    have htd : (tuplePoly (fun i : Fin d => k.coeff (i : ℕ))).coeff d = 1 := by
      have h := (tuplePoly_monic (fun i : Fin d => k.coeff (i : ℕ))).coeff_natDegree
      rwa [tuplePoly_natDegree] at h
    rw [hkd, htd]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hj),
      coeff_eq_zero_of_natDegree_lt (by rw [tuplePoly_natDegree]; exact hj)]

/-- Membership in `irredMonicOfDeg`: exactly the irreducible monic polynomials of degree `d`. -/
theorem mem_irredMonicOfDeg {d : ℕ} {k : (ZMod p)[X]} :
    k ∈ irredMonicOfDeg p d ↔ k.Monic ∧ k.natDegree = d ∧ Irreducible k := by
  classical
  rw [irredMonicOfDeg, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨c, -, rfl⟩, hirr⟩
    exact ⟨tuplePoly_monic c, tuplePoly_natDegree c, hirr⟩
  · rintro ⟨hm, hdeg, hirr⟩
    refine ⟨⟨fun i => k.coeff i, Finset.mem_univ _, ?_⟩, hirr⟩
    exact (monic_eq_tuplePoly hm hdeg).symm

/-! ### The Frobenius orbit: periodicity, distinctness, and the factorization `∏(X − t) = k` -/

/-- Periodicity: a period-`d` function summed over `range (q·d)` is `q` copies of one period. -/
private theorem sum_range_period {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d q : ℕ)
    (hper : ∀ i, f (i + d) = f i) :
    ∑ i ∈ Finset.range (q * d), f i = q • ∑ i ∈ Finset.range d, f i := by
  have hper' : ∀ m i, f (i + m * d) = f i := by
    intro m
    induction m with
    | zero => simp
    | succ j jh => intro i; rw [Nat.succ_mul, ← Nat.add_assoc, hper, jh]
  induction q with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_comm (m * d) i, hper']

/-- For `x ≠ 0` the minimal polynomial has nonzero constant term (else `X ∣ minpoly` forces
`minpoly = X`, whose only root is `0`). -/
theorem minpoly_coeff_zero_ne_zero {n : ℕ} {x : GaloisField p n} (hx : x ≠ 0) :
    (minpoly (ZMod p) x).coeff 0 ≠ 0 := by
  intro hc0
  have hXdvd : (X : (ZMod p)[X]) ∣ minpoly (ZMod p) x := X_dvd_iff.mpr hc0
  have hirr := galoisField_minpoly_irreducible n x
  have hmon := minpoly.monic (galoisField_isIntegral n x)
  have hassoc : Associated (X : (ZMod p)[X]) (minpoly (ZMod p) x) :=
    (Polynomial.irreducible_X).associated_of_dvd hirr hXdvd
  have hEq : (X : (ZMod p)[X]) = minpoly (ZMod p) x :=
    eq_of_monic_of_associated monic_X hmon hassoc
  have : aeval x (X : (ZMod p)[X]) = 0 := by rw [hEq]; exact minpoly.aeval (ZMod p) x
  rw [aeval_X] at this
  exact hx this

/-- A root of `minpoly x ∣ X^{p^m} − X` gives `x^{p^m} = x`; specialised via the Gauss iff. -/
theorem root_pow_card_dvd {n : ℕ} {x : GaloisField p n} {m : ℕ}
    (hdvd : minpoly (ZMod p) x ∣ (X ^ p ^ m - X : (ZMod p)[X])) :
    x ^ p ^ m = x := by
  obtain ⟨c, hc⟩ := hdvd
  have h : aeval x (X ^ p ^ m - X : (ZMod p)[X]) = 0 := by
    rw [hc, map_mul, minpoly.aeval, zero_mul]
  rw [map_sub, map_pow, aeval_X] at h
  exact sub_eq_zero.mp h

/-- `x^{p^d} = x` for `d = deg(minpoly x)`: the minimal polynomial divides `X^{p^d} − X`. -/
theorem root_pow_natDegree {n : ℕ} (x : GaloisField p n) :
    x ^ p ^ (minpoly (ZMod p) x).natDegree = x := by
  have hdpos := minpoly.natDegree_pos (galoisField_isIntegral n x)
  apply root_pow_card_dvd
  refine (irreducible_monic_dvd_X_pow_card_pow_sub_X_iff _ hdpos.ne'
    (minpoly.monic (galoisField_isIntegral n x)) (galoisField_minpoly_irreducible n x)).mpr dvd_rfl

/-- **Orbit distinctness.** The Frobenius orbit `i ↦ x^{p^i}` is injective on `range d`
(`d = deg(minpoly x)`): a coincidence would put `x` in a proper subfield, contradicting the
degree of its minimal polynomial via the Gauss iff. -/
theorem orbit_injOn {n : ℕ} (x : GaloisField p n) :
    Set.InjOn (fun i => x ^ p ^ i) (Finset.range (minpoly (ZMod p) x).natDegree) := by
  have key : ∀ i j : ℕ, j < (minpoly (ZMod p) x).natDegree → i ≤ j →
      x ^ p ^ i = x ^ p ^ j → i = j := by
    intro i j hjd hle hij
    by_contra hne
    have hlt : 0 < j - i := Nat.sub_pos_of_lt (lt_of_le_of_ne hle hne)
    have hfrob : Function.Injective (⇑(frobenius (GaloisField p n) p))^[i] :=
      Function.Injective.iterate (frobenius (GaloisField p n) p).injective i
    have hxfix : x ^ p ^ (j - i) = x := by
      have hcancel : (⇑(frobenius (GaloisField p n) p))^[i] x
          = (⇑(frobenius (GaloisField p n) p))^[i] (x ^ p ^ (j - i)) := by
        rw [iterate_frobenius, iterate_frobenius, ← pow_mul, ← pow_add, Nat.sub_add_cancel hle]
        exact hij
      exact (hfrob hcancel).symm
    have hdvd : minpoly (ZMod p) x ∣ (X ^ p ^ (j - i) - X : (ZMod p)[X]) :=
      minpoly.dvd _ _ (by rw [map_sub, map_pow, aeval_X, hxfix, sub_self])
    have hdd : (minpoly (ZMod p) x).natDegree ∣ (j - i) :=
      (irreducible_monic_dvd_X_pow_card_pow_sub_X_iff _ hlt.ne'
        (minpoly.monic (galoisField_isIntegral n x)) (galoisField_minpoly_irreducible n x)).mp hdvd
    have := Nat.le_of_dvd hlt hdd
    omega
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases le_total i j with hle | hle
  · exact key i j hj hle hij
  · exact (key j i hi hle hij.symm).symm

/-- Constant coefficient of `∏ (X − a)` over a finite set of roots. -/
private theorem prod_X_sub_C_coeff_zero {K : Type*} [Field K] (S : Finset K) :
    (∏ a ∈ S, (X - C a)).coeff 0 = ∏ a ∈ S, (-a) := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  exact Finset.prod_congr rfl fun a _ => by simp

/-- Linear coefficient of `∏ (X − a)`: the `(d−1)`-elementary-symmetric sum (with signs). -/
private theorem prod_X_sub_C_coeff_one {K : Type*} [Field K] [DecidableEq K] (S : Finset K) :
    (∏ a ∈ S, (X - C a)).coeff 1 = ∑ a ∈ S, ∏ b ∈ S.erase a, (-b) := by
  have hd : derivative (∏ a ∈ S, (X - C a)) = ∑ a ∈ S, ∏ b ∈ S.erase a, (X - C b) := by
    rw [Finset.prod_eq_multiset_prod, derivative_prod, ← Finset.sum_eq_multiset_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one,
      Finset.prod_eq_multiset_prod, ← Finset.erase_val]
  have h1 : (∏ a ∈ S, (X - C a)).coeff 1 = eval 0 (derivative (∏ a ∈ S, (X - C a))) := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]; push_cast; ring
  rw [h1, hd, eval_finsetSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [eval_prod]
  exact Finset.prod_congr rfl fun b _ => by simp

/-- **The orbit factorization.** For `x ≠ 0`, the product of `(X − t)` over the Frobenius orbit of
`x` equals `minpoly x` mapped into `𝔽_{p^n}`: the orbit is exactly the (separable, split) root
set of the minimal polynomial. -/
theorem orbit_prod_eq_minpoly_map {n : ℕ} (hn : n ≠ 0) (x : GaloisField p n) :
    ∏ a ∈ (Finset.range (minpoly (ZMod p) x).natDegree).image (fun i => x ^ p ^ i), (X - C a)
      = (minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n)) := by
  classical
  have hint := galoisField_isIntegral n x
  have hmon : (minpoly (ZMod p) x).Monic := minpoly.monic hint
  have hirr : Irreducible (minpoly (ZMod p) x) := galoisField_minpoly_irreducible n x
  have hddvd : (minpoly (ZMod p) x).natDegree ∣ n := galoisField_minpoly_natDegree_dvd n hn x
  have hkdvd : minpoly (ZMod p) x ∣ (X ^ p ^ n - X : (ZMod p)[X]) :=
    (irreducible_monic_dvd_X_pow_card_pow_sub_X_iff n hn hmon hirr).mpr hddvd
  have hsep : ((minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n))).Separable :=
    ((separable_X_pow_card_pow_sub_X n hn).of_dvd hkdvd).map
  have hmapmon : ((minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n))).Monic :=
    hmon.map _
  have hsplitBig : Splits (X ^ p ^ n - X : (GaloisField p n)[X]) := by
    have h := Polynomial.splits_X_pow_nat_card_sub_X (K := GaloisField p n)
    rwa [GaloisField.card p n hn] at h
  have hmapeq : (X ^ p ^ n - X : (ZMod p)[X]).map (algebraMap (ZMod p) (GaloisField p n))
      = (X ^ p ^ n - X : (GaloisField p n)[X]) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  have hmapdvd : (minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n)) ∣
      (X ^ p ^ n - X : (GaloisField p n)[X]) := by
    rw [← hmapeq]; exact Polynomial.map_dvd _ hkdvd
  have hbigne : (X ^ p ^ n - X : (GaloisField p n)[X]) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn (Fact.out : p.Prime).one_lt
  have hsplit : Splits ((minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n))) :=
    Splits.of_dvd hsplitBig hbigne hmapdvd
  have hmapne : (minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n)) ≠ 0 :=
    hmapmon.ne_zero
  set R := ((minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n))).roots with hR
  have hRcard : R.card = (minpoly (ZMod p) x).natDegree := by
    rw [hR, splits_iff_card_roots.mp hsplit]
    exact hmon.natDegree_map _
  have hRnodup : R.Nodup := nodup_roots hsep
  have hSsub : (Finset.range (minpoly (ZMod p) x).natDegree).image (fun i => x ^ p ^ i)
      ⊆ R.toFinset := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨i, -, rfl⟩ := ha
    rw [Multiset.mem_toFinset, hR, mem_roots hmapne, IsRoot.def, eval_map, ← aeval_def]
    exact galoisField_frobenius_orbit_isRoot n x i
  have hStF : (Finset.range (minpoly (ZMod p) x).natDegree).image (fun i => x ^ p ^ i)
      = R.toFinset := by
    apply Finset.eq_of_subset_of_card_le hSsub
    rw [Multiset.toFinset_card_of_nodup hRnodup, hRcard,
      Finset.card_image_of_injOn (orbit_injOn x), Finset.card_range]
  rw [hStF, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hRnodup.dedup]
  exact (Splits.eq_prod_roots_of_monic hsplit hmapmon).symm

/-- Reciprocal sum over a finite set of nonzero elements. -/
private theorem sum_inv_eq {K : Type*} [Field K] [DecidableEq K] (S : Finset K)
    (hS : ∀ a ∈ S, a ≠ 0) :
    (∑ a ∈ S, a⁻¹) = (∑ a ∈ S, ∏ b ∈ S.erase a, b) / (∏ a ∈ S, a) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [eq_div_iff (Finset.prod_ne_zero_iff.mpr fun b hb => hS b hb),
    ← Finset.mul_prod_erase S (fun x => x) ha]
  field_simp [hS a ha]

/-- `∏ (−b) = (−1)^{card} · ∏ b` over a finite set. -/
private theorem prod_neg {K : Type*} [Field K] (t : Finset K) :
    ∏ b ∈ t, (-b) = (-1) ^ t.card * ∏ b ∈ t, b := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun b _ => (neg_one_mul b).symm

/-- **Orbit sum = −nextCoeff.** The Frobenius-orbit sum of `x` equals `−nextCoeff(minpoly x)`
mapped into `𝔽_{p^n}` — Vieta on the orbit factorization. -/
theorem orbit_sum {n : ℕ} (hn : n ≠ 0) (x : GaloisField p n) :
    ∑ i ∈ Finset.range (minpoly (ZMod p) x).natDegree, x ^ p ^ i
      = algebraMap (ZMod p) (GaloisField p n) (-(minpoly (ZMod p) x).nextCoeff) := by
  classical
  have hinj := (algebraMap (ZMod p) (GaloisField p n)).injective
  have h1 := prod_X_sub_C_nextCoeff (R := GaloisField p n)
    (s := (Finset.range (minpoly (ZMod p) x).natDegree).image (fun i => x ^ p ^ i))
    (fun a => a)
  rw [orbit_prod_eq_minpoly_map hn x, nextCoeff_map hinj,
    Finset.sum_image (orbit_injOn x)] at h1
  rw [map_neg, h1, neg_neg]

/-- **Orbit reciprocal sum = −coeff₁/coeff₀** (the reciprocal-Vieta). The sum of inverses over the
Frobenius orbit of `x ≠ 0` equals `−(coeff₁/coeff₀)(minpoly x)` mapped into `𝔽_{p^n}`. -/
theorem orbit_inv_sum {n : ℕ} (hn : n ≠ 0) {x : GaloisField p n} (hx : x ≠ 0) :
    ∑ i ∈ Finset.range (minpoly (ZMod p) x).natDegree, (x ^ p ^ i)⁻¹
      = algebraMap (ZMod p) (GaloisField p n)
        (-((minpoly (ZMod p) x).coeff 1 / (minpoly (ZMod p) x).coeff 0)) := by
  classical
  have hprod := orbit_prod_eq_minpoly_map hn x
  have hdpos : 0 < (minpoly (ZMod p) x).natDegree :=
    minpoly.natDegree_pos (galoisField_isIntegral n x)
  set d := (minpoly (ZMod p) x).natDegree with hd
  set S := (Finset.range d).image (fun i => x ^ p ^ i) with hS
  have hSne : ∀ a ∈ S, a ≠ 0 := by
    intro a ha
    rw [hS, Finset.mem_image] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact pow_ne_zero _ hx
  have hScard : S.card = d := by
    rw [hS, Finset.card_image_of_injOn (orbit_injOn x), Finset.card_range]
  have hsign : ((-1 : GaloisField p n)) ^ (d - 1) = (-1) ^ d * (-1) := by
    conv_rhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
    ring
  -- coeff 0 and coeff 1 of the orbit product, pushed through `coeff_map`
  have hc0 : algebraMap (ZMod p) (GaloisField p n) ((minpoly (ZMod p) x).coeff 0)
      = (-1) ^ d * ∏ a ∈ S, a := by
    rw [← coeff_map, ← hprod, prod_X_sub_C_coeff_zero, prod_neg, hScard]
  have hc1 : algebraMap (ZMod p) (GaloisField p n) ((minpoly (ZMod p) x).coeff 1)
      = (-1) ^ d * (-1) * ∑ a ∈ S, ∏ b ∈ S.erase a, b := by
    rw [← coeff_map, ← hprod, prod_X_sub_C_coeff_one]
    have hterm : ∀ a ∈ S, ∏ b ∈ S.erase a, (-b) = (-1) ^ (d - 1) * ∏ b ∈ S.erase a, b := by
      intro a ha
      rw [prod_neg, Finset.card_erase_of_mem ha, hScard]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsign]
  -- the reciprocal identity + sign bookkeeping
  have hPne : (∏ a ∈ S, a) ≠ 0 := Finset.prod_ne_zero_iff.mpr hSne
  have hsgn : ((-1 : GaloisField p n)) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [← Finset.sum_image (orbit_injOn x) (f := fun a => a⁻¹), sum_inv_eq S hSne,
    map_neg, map_div₀, hc0, hc1, ← neg_div,
    div_eq_div_iff hPne (mul_ne_zero hsgn hPne)]
  ring

/-! ### H1a: the per-root character identity -/

/-- The absolute trace of a period-`d` element, pushed into `𝔽_{p^n}`, is `n/d` copies of the
one-period Frobenius sum. -/
private theorem algMap_trace_period {n : ℕ} (hn : n ≠ 0) (x : GaloisField p n) (d : ℕ)
    (hdn : d ∣ n) (hper : ∀ i, x ^ p ^ (i + d) = x ^ p ^ i) :
    algebraMap (ZMod p) (GaloisField p n) (Algebra.trace (ZMod p) (GaloisField p n) x)
      = (n / d) • ∑ i ∈ Finset.range d, x ^ p ^ i := by
  rw [galoisField_trace_eq_sum_frobenius p n hn,
    show Finset.range n = Finset.range (n / d * d) from by rw [Nat.div_mul_cancel hdn]]
  exact sum_range_period (fun i => x ^ p ^ i) d (n / d) hper

/-- **H1a.** For `x ≠ 0` a root of `k = minpoly x` (irreducible monic of degree `d ∣ n`),
`ψ(Tr_n(a·x + b·x⁻¹)) = η(k)^{n/d}`: the trace of `x` and of `x⁻¹` are `n/d` times the Vieta
data `−nextCoeff k` and `−coeff₁/coeff₀`, so the character factors as an `(n/d)`-th power. -/
theorem traceChar_eq_eta_pow {n : ℕ} (hn : n ≠ 0) (a b : ZMod p) {x : GaloisField p n}
    (hx : x ≠ 0) :
    traceAddChar p n (algebraMap (ZMod p) (GaloisField p n) a * x
        + algebraMap (ZMod p) (GaloisField p n) b * x⁻¹)
      = eta a b (minpoly (ZMod p) x) ^ (n / (minpoly (ZMod p) x).natDegree) := by
  have hint := galoisField_isIntegral n x
  have hdn : (minpoly (ZMod p) x).natDegree ∣ n := galoisField_minpoly_natDegree_dvd n hn x
  have hxd : x ^ p ^ (minpoly (ZMod p) x).natDegree = x := root_pow_natDegree x
  have hperx : ∀ i, x ^ p ^ (i + (minpoly (ZMod p) x).natDegree) = x ^ p ^ i := by
    intro i; rw [pow_add, mul_comm, pow_mul, hxd]
  have hxinvd : x⁻¹ ^ p ^ (minpoly (ZMod p) x).natDegree = x⁻¹ := by rw [inv_pow, hxd]
  have hperinv : ∀ i, x⁻¹ ^ p ^ (i + (minpoly (ZMod p) x).natDegree) = x⁻¹ ^ p ^ i := by
    intro i; rw [pow_add, mul_comm, pow_mul, hxinvd]
  have hinj := (algebraMap (ZMod p) (GaloisField p n)).injective
  have htrx : Algebra.trace (ZMod p) (GaloisField p n) x
      = (n / (minpoly (ZMod p) x).natDegree) • (-(minpoly (ZMod p) x).nextCoeff) := by
    apply hinj
    rw [algMap_trace_period hn x _ hdn hperx, orbit_sum hn x, map_nsmul]
  have htrxinv : Algebra.trace (ZMod p) (GaloisField p n) x⁻¹
      = (n / (minpoly (ZMod p) x).natDegree) •
        (-((minpoly (ZMod p) x).coeff 1 / (minpoly (ZMod p) x).coeff 0)) := by
    apply hinj
    rw [algMap_trace_period hn x⁻¹ _ hdn hperinv, map_nsmul]
    congr 1
    rw [← orbit_inv_sum hn hx]
    exact Finset.sum_congr rfl fun i _ => by rw [inv_pow]
  rw [traceAddChar_apply, map_add,
    show Algebra.trace (ZMod p) (GaloisField p n) (algebraMap (ZMod p) (GaloisField p n) a * x)
      = a * Algebra.trace (ZMod p) (GaloisField p n) x from by
        rw [← Algebra.smul_def, map_smul, smul_eq_mul],
    show Algebra.trace (ZMod p) (GaloisField p n) (algebraMap (ZMod p) (GaloisField p n) b * x⁻¹)
      = b * Algebra.trace (ZMod p) (GaloisField p n) x⁻¹ from by
        rw [← Algebra.smul_def, map_smul, smul_eq_mul],
    htrx, htrxinv]
  have hw : a * ((n / (minpoly (ZMod p) x).natDegree) • (-(minpoly (ZMod p) x).nextCoeff))
      + b * ((n / (minpoly (ZMod p) x).natDegree) •
          (-((minpoly (ZMod p) x).coeff 1 / (minpoly (ZMod p) x).coeff 0)))
      = (n / (minpoly (ZMod p) x).natDegree) • (-(a * (minpoly (ZMod p) x).nextCoeff)
          + -(b * ((minpoly (ZMod p) x).coeff 1 / (minpoly (ZMod p) x).coeff 0))) := by
    simp only [nsmul_eq_mul]; ring
  rw [hw, AddChar.map_nsmul_eq_pow, AddChar.map_add_eq_mul, eta,
    if_neg (minpoly_coeff_zero_ne_zero hx)]

/-! ### H1b: the fiber partition -/

/-- A monic irreducible of degree `d ∣ n` splits over `𝔽_{p^n}`. -/
private theorem minpoly_map_splits {n : ℕ} (hn : n ≠ 0) {k : (ZMod p)[X]} (hmon : k.Monic)
    (hirr : Irreducible k) (hd : k.natDegree ∣ n) :
    Splits (k.map (algebraMap (ZMod p) (GaloisField p n))) := by
  have hkdvd : k ∣ (X ^ p ^ n - X : (ZMod p)[X]) :=
    (irreducible_monic_dvd_X_pow_card_pow_sub_X_iff n hn hmon hirr).mpr hd
  have hsplitBig : Splits (X ^ p ^ n - X : (GaloisField p n)[X]) := by
    have h := Polynomial.splits_X_pow_nat_card_sub_X (K := GaloisField p n)
    rwa [GaloisField.card p n hn] at h
  have hmapeq : (X ^ p ^ n - X : (ZMod p)[X]).map (algebraMap (ZMod p) (GaloisField p n))
      = (X ^ p ^ n - X : (GaloisField p n)[X]) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  have hbigne : (X ^ p ^ n - X : (GaloisField p n)[X]) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn (Fact.out : p.Prime).one_lt
  exact Splits.of_dvd hsplitBig hbigne (by rw [← hmapeq]; exact Polynomial.map_dvd _ hkdvd)

/-- **H1b, the fiber count.** For an irreducible monic `k ≠ X` of degree `d ∣ n`, the set of
nonzero `x ∈ 𝔽_{p^n}` with `minpoly x = k` is exactly the root set of `k`, of cardinality `d`. -/
theorem minpoly_fiber_card {n : ℕ} (hn : n ≠ 0) {k : (ZMod p)[X]} (hmon : k.Monic)
    (hirr : Irreducible k) (hd : k.natDegree ∣ n) (hkX : k ≠ X) :
    ((Finset.univ.erase (0 : GaloisField p n)).filter
      (fun x => minpoly (ZMod p) x = k)).card = k.natDegree := by
  classical
  have hφinj := (algebraMap (ZMod p) (GaloisField p n)).injective
  have hmapmon := hmon.map (algebraMap (ZMod p) (GaloisField p n))
  have hmapne := hmapmon.ne_zero
  have hsplit := minpoly_map_splits hn hmon hirr hd
  have hsep : (k.map (algebraMap (ZMod p) (GaloisField p n))).Separable :=
    ((separable_X_pow_card_pow_sub_X n hn).of_dvd
      ((irreducible_monic_dvd_X_pow_card_pow_sub_X_iff n hn hmon hirr).mpr hd)).map
  have hcoeff0 : k.coeff 0 ≠ 0 := fun h0 => hkX (eq_of_monic_of_associated monic_X hmon
      ((Polynomial.irreducible_X).associated_of_dvd hirr (X_dvd_iff.mpr h0))).symm
  have hEq : (Finset.univ.erase (0 : GaloisField p n)).filter (fun x => minpoly (ZMod p) x = k)
      = (k.map (algebraMap (ZMod p) (GaloisField p n))).roots.toFinset := by
    ext x
    rw [Finset.mem_filter, Finset.mem_erase, Multiset.mem_toFinset, mem_roots hmapne, IsRoot.def,
      eval_map, ← aeval_def]
    constructor
    · rintro ⟨-, hmp⟩
      rw [← hmp]; exact minpoly.aeval (ZMod p) x
    · intro haeval
      have hxint := galoisField_isIntegral n x
      have hmp : minpoly (ZMod p) x = k :=
        eq_of_monic_of_associated (minpoly.monic hxint) hmon
          ((galoisField_minpoly_irreducible n x).associated_of_dvd hirr (minpoly.dvd _ _ haeval))
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [aeval_def, eval₂_at_zero] at haeval
        exact hcoeff0 (hφinj (by rw [haeval, map_zero]))
      exact ⟨⟨hx0, Finset.mem_univ _⟩, hmp⟩
  rw [hEq, Multiset.toFinset_card_of_nodup (nodup_roots hsep), splits_iff_card_roots.mp hsplit]
  exact hmon.natDegree_map _

/-- Summing over the units of a finite field equals summing over its nonzero elements. -/
private theorem sum_units_eq_erase {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {M : Type*} [AddCommMonoid M] (F : K → M) :
    ∑ t : Kˣ, F (t : K) = ∑ x ∈ Finset.univ.erase (0 : K), F x := by
  refine Finset.sum_bij (fun (t : Kˣ) _ => (t : K)) ?_ ?_ ?_ ?_
  · intro t _; exact Finset.mem_erase.mpr ⟨t.ne_zero, Finset.mem_univ _⟩
  · intro t₁ _ t₂ _ h; exact Units.ext h
  · intro x hx; exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro t _; rfl

/-! ### H1: the moment ↔ irreducible-sum reorganization -/

/-- **H1 (Harcos eq. 10).** The twisted Kloosterman moment over `𝔽_{p^n}` reorganizes as the
irreducible-factor sum `c_n = ∑_{d ∣ n} d ∑_{k} η(k)^{n/d}`. Holds for all `a, b` and `n ≠ 0`.
Combining H1a (each root contributes `η(k)^{n/d}`) with H1b (the `minpoly` fiber over `k` has
exactly `deg k` roots). -/
theorem kloostermanMoment_eq_cCoeff (a b : ZMod p) {n : ℕ} (hn : n ≠ 0) :
    kloostermanMoment a b n = cCoeff a b n := by
  classical
  have hmaps : ∀ x ∈ Finset.univ.erase (0 : GaloisField p n),
      minpoly (ZMod p) x ∈ (n.divisors).biUnion (fun d => irredMonicOfDeg p d) := by
    intro x _
    exact Finset.mem_biUnion.mpr ⟨(minpoly (ZMod p) x).natDegree,
      Nat.mem_divisors.mpr ⟨galoisField_minpoly_natDegree_dvd n hn x, hn⟩,
      mem_irredMonicOfDeg.mpr ⟨minpoly.monic (galoisField_isIntegral n x), rfl,
        galoisField_minpoly_irreducible n x⟩⟩
  have hdisj : (↑n.divisors : Set ℕ).PairwiseDisjoint (fun d => irredMonicOfDeg p d) := by
    intro d₁ _ d₂ _ hne
    refine Finset.disjoint_left.mpr fun k hk1 hk2 => hne ?_
    exact ((mem_irredMonicOfDeg.mp hk1).2.1).symm.trans (mem_irredMonicOfDeg.mp hk2).2.1
  have step1 : kloostermanMoment a b n = ∑ x ∈ Finset.univ.erase (0 : GaloisField p n),
      eta a b (minpoly (ZMod p) x) ^ (n / (minpoly (ZMod p) x).natDegree) := by
    rw [kloostermanMoment, ← sum_units_eq_erase (fun x => eta a b (minpoly (ZMod p) x)
      ^ (n / (minpoly (ZMod p) x).natDegree))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Units.val_inv_eq_inv_val]
    exact traceChar_eq_eta_pow hn a b (Units.ne_zero t)
  rw [step1, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun x => eta a b (minpoly (ZMod p) x) ^ (n / (minpoly (ZMod p) x).natDegree)),
    Finset.sum_biUnion hdisj]
  unfold cCoeff
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hkmon, hkdeg, hkirr⟩ := mem_irredMonicOfDeg.mp hk
  have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hconst : ∀ x ∈ (Finset.univ.erase (0 : GaloisField p n)).filter
      (fun x => minpoly (ZMod p) x = k),
      eta a b (minpoly (ZMod p) x) ^ (n / (minpoly (ZMod p) x).natDegree)
        = eta a b k ^ (n / d) := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2, hkdeg]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  by_cases hkX : k = X
  · subst hkX
    rw [show eta a b (X : (ZMod p)[X]) ^ (n / d) = 0 from by
      rw [eta_of_coeff_zero a b (by simp),
        zero_pow (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) hdpos).ne']]
    ring
  · rw [minpoly_fiber_card hn hkmon hkirr (hkdeg ▸ hdn) hkX, hkdeg]

end Salt.Weil
