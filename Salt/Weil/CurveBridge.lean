/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Moments
import Salt.Weil.ArtinSchreier
import Salt.Weil.WeilStepanov
import Mathlib

/-!
# Weil track, Corollary 3 — the moment ↔ curve bridge (Harcos §3, Cor 3)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder). This file completes Harcos's
Corollary 3: it rewrites the Artin–Schreier fibre count produced by
`sum_kloostermanMoment_twist` (`Salt.Weil.Moments`) as the point count of the hyperelliptic
curve `y² = (x^p − x)² − 4ab`, the input Theorem 7 (`weil_stepanov`, `Salt.Weil.WeilStepanov`)
consumes.

* **The completing-the-square fibre count** (`card_kloosterman_fiber`, PB-floor (1)). For a
  field `K` of characteristic `≠ 2` and `A, B ≠ 0`, the unit solutions `t` of the Kloosterman
  equation `A·t + B·t⁻¹ = c` are in bijection with the square roots of the discriminant:
  `#{t ∈ Kˣ : A·t + B·t⁻¹ = c} = #{y : y² = c² − 4AB}`, via `t ↦ 2A·t − c` (inverse
  `y ↦ (y + c)/(2A)`, a unit because `B ≠ 0` rules out the `t = 0` corner). No correction
  terms: the bijection is exact.

* **The curve** (`curvePoly`) `f = (X^p − X)² − C (4ab)` over `𝔽_{p^n}`, with
  `curvePoly_eval`, `curvePoly_natDegree`, `curvePoly_coeff_zero`.

* **The not-a-square lemma** (`curvePoly_not_isSquare`, PB-floor (3), Harcos p. 12): the
  gating hypothesis of `weil_stepanov`. If `f.map` into the algebraic closure were `g²`, then
  `(X^p − X − g)(X^p − X + g) = 4ab` is a nonzero constant, forcing both factors to be
  constants, whence `2(X^p − X)` is constant — impossible for `deg = p ≥ 1`.

* **Corollary 3 itself** (`sum_kloostermanMoment_eq_pointCount`): summing the twisted moments
  over `m ∈ 𝔽_p` equals `pointCount (curvePoly a b n)`, with the `m = 0` term extracted as the
  standalone `#𝔽_{p^n}ˣ = p^n − 1` in `sum_kloostermanMoment_erase_zero_eq`.
-/

namespace Salt.Weil

open Polynomial
open scoped BigOperators

/-! ### The completing-the-square fibre count (PB-floor (1)) -/

/-- **The completing-the-square bijection** (Harcos p. 9, Cor 3). Over a field `K` with
`2 ≠ 0`, and `A, B ≠ 0`, for each `c : K` the unit solutions `t` of `A·t + B·t⁻¹ = c` biject
with the square roots of the discriminant `c² − 4AB`:
`#{t ∈ Kˣ : c = A·t + B·t⁻¹} = #{y : K : y² = c² − 4AB}`.

The map is `t ↦ 2A·t − c`; its inverse `y ↦ (y + c)/(2A)` lands in `Kˣ` because `B ≠ 0` forces
`y + c ≠ 0` (else `4AB = 0`). Multiplying the Kloosterman equation by `t` gives the quadratic
`A·t² − c·t + B = 0`, and `(2A·t − c)² = c² − 4AB` is exactly its completed square. This is the
per-`x` count Cor 3 sums over `x` (with `c = x^p − x`). -/
theorem card_kloosterman_fiber {K : Type*} [Field K] (c A B : K)
    (hA : A ≠ 0) (hB : B ≠ 0) (h2 : (2 : K) ≠ 0) :
    Nat.card {t : Kˣ // c = A * (t : K) + B * ((t⁻¹ : Kˣ) : K)}
      = Nat.card {y : K // y ^ 2 = c ^ 2 - 4 * A * B} := by
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h2A : 2 * A ≠ 0 := mul_ne_zero h2 hA
  refine Nat.card_congr {
    toFun := fun p => ⟨2 * A * (p.1 : K) - c, ?_⟩
    invFun := fun q => ⟨Units.mk0 ((q.1 + c) / (2 * A)) ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · -- membership of `2A·t − c` in `{y : y² = c² − 4AB}`
    have ht := p.2
    rw [Units.val_inv_eq_inv_val] at ht
    have hs : (p.1 : K) ≠ 0 := p.1.ne_zero
    field_simp [hs] at ht
    linear_combination (-4 * A) * ht
  · -- `(q.1 + c)/(2A) ≠ 0`
    refine div_ne_zero ?_ h2A
    intro hyc
    have hyeq : q.1 = -c := by linear_combination hyc
    have hcontra : (4 : K) * A * B = 0 := by
      have hq := q.2; rw [hyeq] at hq; linear_combination hq
    exact (mul_ne_zero (mul_ne_zero h4 hA) hB) hcontra
  · -- membership of the preimage unit in `{t : c = A·t + B·t⁻¹}`
    have hyc : q.1 + c ≠ 0 := by
      intro hyc0
      have hyeq : q.1 = -c := by linear_combination hyc0
      have hcontra : (4 : K) * A * B = 0 := by
        have hq := q.2; rw [hyeq] at hq; linear_combination hq
      exact (mul_ne_zero (mul_ne_zero h4 hA) hB) hcontra
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    linear_combination -q.2
  · -- left inverse
    intro p
    apply Subtype.ext
    apply Units.ext
    rw [Units.val_mk0]
    field_simp
    ring
  · -- right inverse
    intro q
    apply Subtype.ext
    simp only [Units.val_mk0]
    field_simp
    ring

/-! ### The curve `y² = (x^p − x)² − 4ab` -/

variable {p n : ℕ} [Fact p.Prime]

/-- **The Corollary 3 curve** `f = (X^p − X)² − C (4ab)` over `𝔽_{p^n}`, coefficients pushed
in from `𝔽_p` via `algebraMap`. `weil_stepanov` bounds its point count `#{(x, y) : y² = f(x)}`.
-/
noncomputable def curvePoly (a b : ZMod p) (n : ℕ) : (GaloisField p n)[X] :=
  (X ^ p - X) ^ 2 -
    C (4 * algebraMap (ZMod p) (GaloisField p n) a * algebraMap (ZMod p) (GaloisField p n) b)

/-- Evaluation of the curve: `f(x) = (x^p − x)² − 4ab`. -/
@[simp] theorem curvePoly_eval (a b : ZMod p) (x : GaloisField p n) :
    (curvePoly a b n).eval x =
      (x ^ p - x) ^ 2 -
        4 * algebraMap (ZMod p) (GaloisField p n) a * algebraMap (ZMod p) (GaloisField p n) b := by
  simp [curvePoly]

/-- `2 ≠ 0` in `𝔽_{p^n}` for odd `p` (`p ≠ 2`): the prime-field scalar `(2 : 𝔽_p)` is nonzero
since `p ∤ 2`, and `algebraMap` is injective. -/
private theorem two_ne_zero' (hp2 : p ≠ 2) : (2 : GaloisField p n) ≠ 0 := by
  have hz : (2 : ZMod p) ≠ 0 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
    simpa using h2
  have hmap := (map_ne_zero_iff (algebraMap (ZMod p) (GaloisField p n))
    (FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p n))).mpr hz
  rwa [show (2 : GaloisField p n) = algebraMap (ZMod p) (GaloisField p n) 2 from
    (map_ofNat _ 2).symm]

/-- `weil_stepanov`'s `f(0) ≠ 0` hypothesis: `f.coeff 0 = f(0) = −4ab ≠ 0` (the constant term
of `(X^p − X)²` vanishes since `p ≥ 1`). -/
theorem curvePoly_coeff_zero_ne_zero (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    (curvePoly a b n).coeff 0 ≠ 0 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  have h4 : (4 : GaloisField p n) ≠ 0 := by
    rw [show (4 : GaloisField p n) = 2 * 2 by norm_num]
    exact mul_ne_zero (two_ne_zero' hp2) (two_ne_zero' hp2)
  have hAne : algebraMap (ZMod p) (GaloisField p n) a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha
  have hBne : algebraMap (ZMod p) (GaloisField p n) b ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hb
  rw [coeff_zero_eq_eval_zero, curvePoly_eval, zero_pow hp0]
  intro hcontra
  exact (mul_ne_zero (mul_ne_zero h4 hAne) hBne) (by linear_combination -hcontra)

/-- `weil_stepanov`'s degree input: `deg f = 2p` (so `1 ≤ deg f`). The top term `X^{2p}` of
`(X^p − X)²` dominates the constant `C (4ab)`. -/
theorem curvePoly_natDegree (a b : ZMod p) :
    (curvePoly a b n).natDegree = 2 * p := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hlt : (X : (GaloisField p n)[X]).degree < ((X : (GaloisField p n)[X]) ^ p).degree := by
    rw [degree_X_pow, degree_X]; exact_mod_cast hp1
  have hXpX : ((X : (GaloisField p n)[X]) ^ p - X).degree = (p : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt hlt, degree_X_pow]
  have hsq : (((X : (GaloisField p n)[X]) ^ p - X) ^ 2).degree = ((2 * p : ℕ) : WithBot ℕ) := by
    rw [degree_pow, hXpX, two_smul, ← Nat.cast_add]; congr 1; omega
  have hCdeg : (C (4 * algebraMap (ZMod p) (GaloisField p n) a *
        algebraMap (ZMod p) (GaloisField p n) b) : (GaloisField p n)[X]).degree
      < (((X : (GaloisField p n)[X]) ^ p - X) ^ 2).degree := by
    rw [hsq]
    exact lt_of_le_of_lt degree_C_le
      (by exact_mod_cast Nat.mul_pos (by norm_num) (Fact.out : p.Prime).pos)
  apply natDegree_eq_of_degree_eq_some
  rw [curvePoly, degree_sub_eq_left_of_degree_lt hCdeg, hsq]

/-! ### The not-a-square lemma (PB-floor (3)) -/

/-- **The gating lemma for Theorem 7** (Harcos p. 12). Over the algebraic closure of
`𝔽_{p^n}`, the curve polynomial `f = (X^p − X)² − C (4ab)` is not a perfect square (for
`a, b ≠ 0` and odd `p`). If `f.map = g²`, then `(X^p − X − g)(X^p − X + g) = 4ab` is a nonzero
constant, so both factors are units, hence degree `0`; but their sum `2(X^p − X)` then has
degree `≤ 0`, contradicting `deg (X^p − X) = p ≥ 1`. This discharges `weil_stepanov`'s
non-square hypothesis for `curvePoly`. -/
theorem curvePoly_not_isSquare (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    ¬ ∃ g : (AlgebraicClosure (GaloisField p n))[X],
      (curvePoly a b n).map
          (algebraMap (GaloisField p n) (AlgebraicClosure (GaloisField p n))) = g ^ 2 := by
  rintro ⟨g, hg⟩
  set φ := algebraMap (GaloisField p n) (AlgebraicClosure (GaloisField p n)) with hφ
  have hinjφ : Function.Injective φ :=
    FaithfulSMul.algebraMap_injective (GaloisField p n) (AlgebraicClosure (GaloisField p n))
  have hp1 : 1 < p := by have := (Fact.out : p.Prime).two_le; omega
  have h2K : (2 : GaloisField p n) ≠ 0 := two_ne_zero' hp2
  have h4K : (4 : GaloisField p n) ≠ 0 := by
    rw [show (4 : GaloisField p n) = 2 * 2 by norm_num]; exact mul_ne_zero h2K h2K
  set κ : GaloisField p n :=
    4 * algebraMap (ZMod p) (GaloisField p n) a * algebraMap (ZMod p) (GaloisField p n) b with hκ
  have hκK : κ ≠ 0 := by
    have hinj := FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p n)
    exact mul_ne_zero (mul_ne_zero h4K ((map_ne_zero_iff _ hinj).mpr ha))
      ((map_ne_zero_iff _ hinj).mpr hb)
  have hmap : (curvePoly a b n).map φ = (X ^ p - X) ^ 2 - C (φ κ) := by
    simp only [curvePoly, hκ, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
  rw [hmap] at hg
  set P : (AlgebraicClosure (GaloisField p n))[X] := X ^ p - X with hP
  have key : (P - g) * (P + g) = C (φ κ) := by linear_combination hg
  have hCunit : IsUnit (C (φ κ)) := isUnit_C.mpr ((map_ne_zero_iff φ hinjφ).mpr hκK).isUnit
  have hunit : IsUnit ((P - g) * (P + g)) := by rw [key]; exact hCunit
  have hd1 : (P - g).degree = 0 := degree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_left hunit)
  have hd2 : (P + g).degree = 0 := degree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_right hunit)
  have hsum : (P - g) + (P + g) = 2 * P := by ring
  have hle : (2 * P).degree ≤ 0 := by
    rw [← hsum]; exact (degree_add_le _ _).trans (by rw [hd1, hd2]; simp)
  have h2L : (2 : AlgebraicClosure (GaloisField p n)) ≠ 0 := by
    rw [show (2 : AlgebraicClosure (GaloisField p n)) = φ 2 from (map_ofNat φ 2).symm]
    exact (map_ne_zero_iff φ hinjφ).mpr h2K
  have hdP : P.degree = (p : WithBot ℕ) := by
    rw [hP, degree_sub_eq_left_of_degree_lt (by rw [degree_X_pow, degree_X]; exact_mod_cast hp1)]
    exact degree_X_pow p
  have hd2P : (2 * P).degree = (p : WithBot ℕ) := by
    rw [show (2 : (AlgebraicClosure (GaloisField p n))[X]) = C 2 from (map_ofNat C 2).symm,
      degree_C_mul h2L]
    exact hdP
  rw [hd2P] at hle
  have : (p : ℕ) ≤ 0 := by exact_mod_cast hle
  omega

/-! ### Corollary 3 — the moment ↔ curve identity -/

/-- **Fubini for counting.** Summing a relation's column counts over `α` equals summing its row
counts over `β`: `∑ₐ #{b : R a b} = ∑_b #{a : R a b}`, both counting the pairs of `R`. -/
private theorem sum_card_transpose {α β : Type*} [Fintype α] [Fintype β] (R : α → β → Prop) :
    ∑ a, Nat.card {b // R a b} = ∑ b, Nat.card {a // R a b} := by
  classical
  have h : ∀ a : α, Nat.card {b // R a b} = ∑ b, (if R a b then 1 else 0 : ℕ) := by
    intro a; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; simp
  have h' : ∀ b : β, Nat.card {a // R a b} = ∑ a, (if R a b then 1 else 0 : ℕ) := by
    intro b; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; simp
  simp_rw [h, h']
  exact Finset.sum_comm

/-- **Corollary 3, the Artin–Schreier fibre count as a curve point count** (Nat level). Summing
the Artin–Schreier fibre counts of `sum_kloostermanMoment_twist` over the units `t` equals the
point count of `curvePoly`: transpose the double sum (`sum_card_transpose`), apply the
completing-the-square bijection per `x` (`card_kloosterman_fiber` at `c = x^p − x`), fold the
discriminant into `f(x)` (`curvePoly_eval`), and refibre (`subtypeProdEquivSigmaSubtype`). No
correction terms — the bijection is exact under `a, b ≠ 0` and odd `p`. -/
theorem sum_card_fiber_eq_pointCount (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) (hp2 : p ≠ 2) :
    ∑ t : (GaloisField p n)ˣ, Nat.card {x : GaloisField p n //
        x ^ p - x = algebraMap (ZMod p) (GaloisField p n) a * (t : GaloisField p n) +
          algebraMap (ZMod p) (GaloisField p n) b *
            ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n)}
      = pointCount (curvePoly a b n) := by
  set A := algebraMap (ZMod p) (GaloisField p n) a with hA
  set B := algebraMap (ZMod p) (GaloisField p n) b with hB
  have hAne : A ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha
  have hBne : B ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hb
  have h2 : (2 : GaloisField p n) ≠ 0 := two_ne_zero' hp2
  rw [sum_card_transpose (fun (t : (GaloisField p n)ˣ) (x : GaloisField p n) =>
    x ^ p - x = A * (t : GaloisField p n) +
      B * ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n))]
  have hfiber : ∀ x : GaloisField p n,
      Nat.card {t : (GaloisField p n)ˣ // x ^ p - x = A * (t : GaloisField p n) +
          B * ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n)}
        = Nat.card {y : GaloisField p n // y ^ 2 = (x ^ p - x) ^ 2 - 4 * A * B} :=
    fun x => card_kloosterman_fiber (x ^ p - x) A B hAne hBne h2
  have hdisc : ∀ x : GaloisField p n,
      (x ^ p - x) ^ 2 - 4 * A * B = (curvePoly a b n).eval x := fun x => by
    rw [curvePoly_eval, hA, hB]
  simp_rw [hfiber, hdisc]
  unfold pointCount
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (x y : GaloisField p n) => y ^ 2 = (curvePoly a b n).eval x)).symm

/-- **Corollary 3** (Harcos §3). Summing the twisted Kloosterman moments over `m ∈ 𝔽_p` equals
the point count of the curve `y² = (x^p − x)² − 4ab`:
`∑_{m} M_n(m·a, m·b) = #{(x, y) : y² = (curvePoly a b n)(x)}`. The right side is what
`weil_stepanov` bounds; the left is reconstructed from the per-`m` moments (Thm 6) plus the
`m = 0` term. -/
theorem sum_kloostermanMoment_eq_pointCount (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∑ m : ZMod p, kloostermanMoment (m * a) (m * b) n = (pointCount (curvePoly a b n) : ℂ) := by
  rw [sum_kloostermanMoment_twist a b hn, ← Nat.cast_sum]
  exact_mod_cast sum_card_fiber_eq_pointCount a b ha hb hp2

/-- **The `m = 0` term** of Corollary 3. `M_n(0, 0) = #𝔽_{p^n}ˣ = p^n − 1`: the trace character
is trivial on the zero argument, so every unit contributes `1`. This is Cor 3's standalone
constant. -/
theorem kloostermanMoment_zero_zero (n : ℕ) :
    kloostermanMoment (0 : ZMod p) 0 n = (Fintype.card (GaloisField p n)ˣ : ℂ) := by
  unfold kloostermanMoment
  simp

/-- **Corollary 3, `m ≠ 0` form.** Extracting the `m = 0` term (`= p^n − 1`), the sum of the
nontrivial twisted moments is `pointCount (curvePoly a b n) − (p^n − 1)`. Combined with Theorem 6
(`M_n = −(αⁿ + βⁿ)`) and Theorem 7 (`|pointCount − q| = O(√q)`), this feeds the descent. -/
theorem sum_kloostermanMoment_erase_zero_eq (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp2 : p ≠ 2) (hn : n ≠ 0) :
    ∑ m ∈ Finset.univ.erase (0 : ZMod p), kloostermanMoment (m * a) (m * b) n
      = (pointCount (curvePoly a b n) : ℂ) - (Fintype.card (GaloisField p n)ˣ : ℂ) := by
  have hsplit : ∑ m : ZMod p, kloostermanMoment (m * a) (m * b) n
      = kloostermanMoment (0 * a) (0 * b) n
        + ∑ m ∈ Finset.univ.erase (0 : ZMod p), kloostermanMoment (m * a) (m * b) n :=
    (Finset.add_sum_erase Finset.univ (fun m => kloostermanMoment (m * a) (m * b) n)
      (Finset.mem_univ 0)).symm
  rw [sum_kloostermanMoment_eq_pointCount a b ha hb hp2 hn] at hsplit
  rw [zero_mul, zero_mul, kloostermanMoment_zero_zero] at hsplit
  linear_combination -hsplit

end Salt.Weil
