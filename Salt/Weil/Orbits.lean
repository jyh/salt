/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Kloosterman

/-!
# Weil track, node W1.3′ — Frobenius orbits ↔ irreducible monics + Gauss factorization

Source: Harcos, *Weil's bound for Kloosterman sums*, §2, Theorem 3 + Corollary 2.

For a prime `p` and `n ≠ 0`, we work inside `𝔽_{p^n} = GaloisField p n`, the splitting
field of `X^{p^n} − X` over `𝔽_p = ZMod p`. The Frobenius map is `σ : x ↦ x^p`.

## Theorem 3 (forward): orbit ↔ minimal polynomial

Each `x : 𝔽_{p^n}` has minimal polynomial `minpoly (ZMod p) x` over `𝔽_p` which is:
* irreducible (`galoisField_minpoly_irreducible`), and
* of degree `d ∣ n` (`galoisField_minpoly_natDegree_dvd`).

The Frobenius orbit `{x, x^p, …, x^{p^{d−1}}}` lies in its root set: every `x^{p^i}` is a
root (`galoisField_frobenius_orbit_isRoot`, `galoisField_frobenius_pow_mem_rootSet`). This
is the forward inclusion `orbit ⊆ rootSet`; the engine is the char-`p` identity
`aeval (y^p) f = (aeval y f)^p` for `f ∈ 𝔽_p[X]` (`aeval_pow_card`), i.e. Frobenius fixes
`𝔽_p`-coefficients.

## Corollary 2 (Gauss): the honest divisibility form

Mathlib has no `∏_{d ∣ n} ∏_{k irred. monic, deg = d} k` product, so we land the
equivalent structural facts that pin down that factorization for the L-function layer (W2):

* `separable_X_pow_card_pow_sub_X` / `squarefree_X_pow_card_pow_sub_X`: `X^{p^n} − X` is
  separable, hence squarefree — every irreducible factor has multiplicity one.
* `irreducible_monic_dvd_X_pow_card_pow_sub_X_iff`: a monic irreducible `k ∈ 𝔽_p[X]`
  divides `X^{p^n} − X` **iff** `deg k ∣ n`. Squarefreeness + this membership test determine
  the full multiset of irreducible monic factors. The `⟸` direction also realises Theorem 3's
  converse: a monic irreducible of degree `d ∣ n` has a root in `𝔽_{p^n}`.
-/

namespace Salt.Weil

open Polynomial

variable {p : ℕ} [h_prime : Fact p.Prime] (n : ℕ)

/-! ### Integrality and the minimal polynomial (Theorem 3, forward) -/

/-- Every element of `𝔽_{p^n}` is integral over `𝔽_p` (finite extension). -/
theorem galoisField_isIntegral (x : GaloisField p n) : IsIntegral (ZMod p) x :=
  Algebra.IsIntegral.isIntegral x

/-- **Theorem 3 (part 1).** The minimal polynomial of `x ∈ 𝔽_{p^n}` over `𝔽_p` is irreducible. -/
theorem galoisField_minpoly_irreducible (x : GaloisField p n) :
    Irreducible (minpoly (ZMod p) x) :=
  minpoly.irreducible (galoisField_isIntegral n x)

/-- **Theorem 3 (part 2).** The minimal polynomial degree divides `n`. -/
theorem galoisField_minpoly_natDegree_dvd (hn : n ≠ 0) (x : GaloisField p n) :
    (minpoly (ZMod p) x).natDegree ∣ n := by
  have h := minpoly.degree_dvd (galoisField_isIntegral n x)
  rwa [GaloisField.finrank p hn] at h

/-! ### The Frobenius orbit lies in the root set -/

/-- **Char-`p` transfer.** For any `f ∈ 𝔽_p[X]`, `aeval (y^p) f = (aeval y f)^p`: the
Frobenius endomorphism fixes the `𝔽_p`-coefficients of `f`. -/
private theorem aeval_pow_card (f : (ZMod p)[X]) (y : GaloisField p n) :
    aeval (y ^ p) f = (aeval y f) ^ p := by
  have h : (algebraMap (ZMod p) (GaloisField p n)).comp (frobenius (ZMod p) p)
      = (frobenius (GaloisField p n) p).comp (algebraMap (ZMod p) (GaloisField p n)) := by
    ext z
    simp only [RingHom.comp_apply]
    exact (algebraMap (ZMod p) (GaloisField p n)).map_frobenius p z
  have key := map_aeval_eq_aeval_map h f y
  rw [ZMod.frobenius_zmod p, Polynomial.map_id] at key
  simp only [frobenius_def] at key
  exact key.symm

/-- **Theorem 3 (forward inclusion).** Every element `x^{p^i}` of the Frobenius orbit of `x`
is a root of `minpoly (ZMod p) x`. -/
theorem galoisField_frobenius_orbit_isRoot (x : GaloisField p n) (i : ℕ) :
    aeval (x ^ p ^ i) (minpoly (ZMod p) x) = 0 := by
  induction i with
  | zero =>
    simp only [pow_zero, pow_one]
    exact minpoly.aeval (ZMod p) x
  | succ k ih =>
    have hpow : x ^ p ^ (k + 1) = (x ^ p ^ k) ^ p := by rw [pow_succ, pow_mul]
    rw [hpow, aeval_pow_card, ih, zero_pow h_prime.out.pos.ne']

/-- The Frobenius orbit is contained in the root set of the minimal polynomial. -/
theorem galoisField_frobenius_pow_mem_rootSet (x : GaloisField p n) (i : ℕ) :
    x ^ p ^ i ∈ (minpoly (ZMod p) x).rootSet (GaloisField p n) := by
  rw [mem_rootSet]
  exact ⟨minpoly.ne_zero (galoisField_isIntegral n x), galoisField_frobenius_orbit_isRoot n x i⟩

/-! ### Corollary 2 (Gauss): separability and the divisibility characterization -/

/-- **Separability.** `X^{p^n} − X` is separable over `𝔽_p`. -/
theorem separable_X_pow_card_pow_sub_X (hn : n ≠ 0) :
    (X ^ p ^ n - X : (ZMod p)[X]).Separable :=
  galois_poly_separable p (p ^ n) (dvd_pow_self p hn)

/-- **Squarefreeness.** Consequently every irreducible factor of `X^{p^n} − X` is simple. -/
theorem squarefree_X_pow_card_pow_sub_X (hn : n ≠ 0) :
    Squarefree (X ^ p ^ n - X : (ZMod p)[X]) :=
  (separable_X_pow_card_pow_sub_X n hn).squarefree

/-- **Corollary 2 (Gauss, honest form).** A monic irreducible `k ∈ 𝔽_p[X]` divides
`X^{p^n} − X` iff `deg k ∣ n`. With squarefreeness this determines the multiset of
irreducible monic factors, and the `⟸` direction realises Theorem 3's converse (a monic
irreducible of degree `d ∣ n` has a root in `𝔽_{p^n}`). -/
theorem irreducible_monic_dvd_X_pow_card_pow_sub_X_iff (hn : n ≠ 0)
    {k : (ZMod p)[X]} (hk_monic : k.Monic) (hk_irred : Irreducible k) :
    k ∣ (X ^ p ^ n - X : (ZMod p)[X]) ↔ k.natDegree ∣ n := by
  constructor
  · intro hk_dvd
    have hsplit : Splits (X ^ p ^ n - X : (GaloisField p n)[X]) := by
      have h := Polynomial.splits_X_pow_nat_card_sub_X (K := GaloisField p n)
      rwa [GaloisField.card p n hn] at h
    have hmap : (X ^ p ^ n - X : (ZMod p)[X]).map (algebraMap (ZMod p) (GaloisField p n))
        = (X ^ p ^ n - X : (GaloisField p n)[X]) := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
    have hne : (X ^ p ^ n - X : (GaloisField p n)[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn h_prime.out.one_lt
    have hkmapdvd : k.map (algebraMap (ZMod p) (GaloisField p n)) ∣
        (X ^ p ^ n - X : (GaloisField p n)[X]) := by
      rw [← hmap]
      simpa only [Polynomial.coe_mapRingHom] using
        map_dvd (Polynomial.mapRingHom (algebraMap (ZMod p) (GaloisField p n))) hk_dvd
    have hks : Splits (k.map (algebraMap (ZMod p) (GaloisField p n))) :=
      Splits.of_dvd hsplit hne hkmapdvd
    have hdvd := hk_irred.natDegree_dvd_finrank hks
    rwa [GaloisField.finrank p hn] at hdvd
  · intro hd
    haveI : Fact (Irreducible k) := ⟨hk_irred⟩
    have hkne : k ≠ 0 := hk_monic.ne_zero
    have hfinK : Module.finrank (ZMod p) (AdjoinRoot k) = k.natDegree := by
      rw [(AdjoinRoot.powerBasis hkne).finrank, AdjoinRoot.powerBasis_dim]
    have hdvd' : Module.finrank (ZMod p) (AdjoinRoot k) ∣
        Module.finrank (ZMod p) (GaloisField p n) := by
      rw [hfinK, GaloisField.finrank p hn]; exact hd
    obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd'
    have hβ : aeval (AdjoinRoot.powerBasis hkne).gen k = 0 := by
      have hb := minpoly.aeval (ZMod p) (AdjoinRoot.powerBasis hkne).gen
      rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hk_monic hkne] at hb
    have hα : aeval (φ (AdjoinRoot.powerBasis hkne).gen) k = 0 := by
      rw [aeval_algHom_apply, hβ, map_zero]
    have hαpow : aeval (φ (AdjoinRoot.powerBasis hkne).gen)
        (X ^ p ^ n - X : (ZMod p)[X]) = 0 := by
      rw [map_sub, map_pow, aeval_X, galoisField_pow_card p n hn _, sub_self]
    rw [minpoly.eq_of_irreducible_of_monic hk_irred hα hk_monic]
    exact minpoly.dvd (ZMod p) _ hαpow

end Salt.Weil
