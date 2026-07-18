/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHClose2
import Mathlib.NumberTheory.Primorial

/-!
# T-BAL R5 — the EFFECTIVE truncated Euler product supplier (`H_lower` scaffolding)

This module builds the effective (explicit-error) Euler-product tools R5 (`H_lower`) needs and
that mathlib's asymptotic `eulerProduct` does NOT supply: a **Rankin tail** bound for the
multiplicative Selberg factor `g`, the **product-sum bridge** `H(z) = P(z) − tail(z)` (P the full
`z`-smooth product), and the **ζ·L product form** of `P(z)` (via the landed local-split gift).

## The bottom-up stones

* **§1 — the Rankin machinery (general, `f`-generic).**
  `sqfree_rpow_prod` (a^α splits over prime factors for squarefree `a`),
  `alpha_weighted_divprod` (the α-weighted DIVPROD `Σ_{a∣m} g(a)·a^α = ∏_{p∣m}(1+f(p)p^α)`), and
  `rankin_tail_le` — the Rankin trick at a structural exponent `α`:
  `Σ_{a∣m, a>z} g(a) ≤ z^{−α}·∏_{p∣m}(1+f(p)p^α)`. This is exactly the
  "Rankin-for-multiplicative-`g`" lemma the endgame flag localized as absent from mathlib.

* **§2 — the primorial support bridge (`selHSum` ↔ smooth-squarefree divisor sum).**
  `selHSum χ z = Σ_{a∣z#, a≤z} g(a)` and the full smooth product
  `Σ_{a∣z#} g(a) = ∏_{p≤z}(1+g(p))`; so `P(z) − H(z) = the Rankin tail`, whence
  `H(z) ≥ (1−δ_b)·P(z)` with `δ_b = tail/P`.

* **§3 — the ζ·L product form of `P(z)`** (the landed gift `one_add_selG_eq_local_inv`, lifted to
  the primorial): `∏_{p≤z}(1+g(p)) = ∏_{p≤z} 1/((1−1/p)(1−χ_ℝ(p)/p))`.

The remaining effective Mertens (ζ-side `∏(1−1/p)⁻¹`) and effective truncated-Euler (L-side
`∏(1−χ/p)⁻¹` vs `L(1,χ)`) links, and the numerical `δ_b ≤ 300 z^{−0.4}` constant, are RECORDED
in the module-tail flag (see `docs/blueprints/flags.md`, the R5-EULER entry).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

open Finset

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §1 — the Rankin machinery (`f`-generic, over a squarefree modulus `m`) -/

/-- For squarefree `a`, `(a:ℝ)^α` splits over the prime factors: `a^α = ∏_{p∣a} p^α`
(`a = ∏_{p∣a} p` on the squarefree support, then `rpow` distributes over the finite product of
nonnegatives). -/
lemma sqfree_rpow_prod {a : ℕ} (ha : Squarefree a) (α : ℝ) :
    (a : ℝ) ^ α = ∏ p ∈ a.primeFactors, (p : ℝ) ^ α := by
  have hcast : (a : ℝ) = ∏ p ∈ a.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ha]
  rw [hcast, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]

/-- **The α-weighted DIVPROD.** For squarefree `m`, any real `α`, and any real `f`,
`Σ_{a∣m} (∏_{p∣a} f p)·a^α = ∏_{p∣m}(1 + f(p)·p^α)`. Route: on each squarefree divisor `a`,
`(∏_{p∣a} f p)·a^α = ∏_{p∣a}(f p·p^α)` (`sqfree_rpow_prod` + `prod_mul_distrib`), then DIVPROD
(`sum_divisors_prod_primeFactors` at `f' p = f p·p^α`). -/
lemma alpha_weighted_divprod {m : ℕ} (hm : Squarefree m) (α : ℝ) (f : ℕ → ℝ) :
    ∑ a ∈ m.divisors, (∏ p ∈ a.primeFactors, f p) * (a : ℝ) ^ α
      = ∏ p ∈ m.primeFactors, (1 + f p * (p : ℝ) ^ α) := by
  have hstep : ∀ a ∈ m.divisors, (∏ p ∈ a.primeFactors, f p) * (a : ℝ) ^ α
      = ∏ p ∈ a.primeFactors, (f p * (p : ℝ) ^ α) := by
    intro a ha
    have hasf : Squarefree a := hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha)
    rw [sqfree_rpow_prod hasf, ← Finset.prod_mul_distrib]
  calc ∑ a ∈ m.divisors, (∏ p ∈ a.primeFactors, f p) * (a : ℝ) ^ α
      = ∑ a ∈ m.divisors, ∏ p ∈ a.primeFactors, (f p * (p : ℝ) ^ α) :=
        Finset.sum_congr rfl hstep
    _ = ∏ p ∈ m.primeFactors, (f p * (p : ℝ) ^ α + 1) :=
        (sum_divisors_prod_primeFactors (f := fun p => f p * (p : ℝ) ^ α) hm).symm
    _ = ∏ p ∈ m.primeFactors, (1 + f p * (p : ℝ) ^ α) :=
        Finset.prod_congr rfl (fun p _ => by ring)

/-- **The Rankin tail bound** (the multiplicative-`g` Rankin trick, the flagged-absent lemma). For
squarefree `m`, a structural exponent `α ≥ 0`, a positive cut `z`, and a nonnegative factor `f` on
`m`'s primes, the `g`-mass of the divisors of `m` exceeding `z` is Rankin-bounded:
`Σ_{a∣m, a>z} (∏_{p∣a} f p) ≤ z^{−α}·∏_{p∣m}(1 + f(p)·p^α)`.
Route: for `a > z`, `1 ≤ (a/z)^α = z^{−α}a^α`, so each tail term `≤ z^{−α}·(term·a^α)`; drop the
`a>z` filter (all terms `≥ 0`) and apply the α-weighted DIVPROD. -/
lemma rankin_tail_le {m : ℕ} (hm : Squarefree m) {α : ℝ} (hα : 0 ≤ α)
    {z : ℝ} (hz : 0 < z) {f : ℕ → ℝ} (hfnn : ∀ p ∈ m.primeFactors, 0 ≤ f p) :
    ∑ a ∈ m.divisors.filter (fun a : ℕ => z < (a : ℝ)), (∏ p ∈ a.primeFactors, f p)
      ≤ z ^ (-α) * ∏ p ∈ m.primeFactors, (1 + f p * (p : ℝ) ^ α) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hprodnn : ∀ a ∈ m.divisors, 0 ≤ ∏ p ∈ a.primeFactors, f p := by
    intro a ha
    refine Finset.prod_nonneg fun p hp => hfnn p ?_
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ha) hm0 hp
  rw [← alpha_weighted_divprod hm α f, Finset.mul_sum]
  calc ∑ a ∈ m.divisors.filter (fun a : ℕ => z < (a : ℝ)), (∏ p ∈ a.primeFactors, f p)
      ≤ ∑ a ∈ m.divisors.filter (fun a : ℕ => z < (a : ℝ)),
          z ^ (-α) * ((∏ p ∈ a.primeFactors, f p) * (a : ℝ) ^ α) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [Finset.mem_filter] at ha
        obtain ⟨had, hza⟩ := ha
        have hterm_nn : 0 ≤ ∏ p ∈ a.primeFactors, f p := hprodnn a had
        have hzα : (0 : ℝ) < z ^ α := Real.rpow_pos_of_pos hz α
        have h1 : (1 : ℝ) ≤ z ^ (-α) * (a : ℝ) ^ α := by
          rw [Real.rpow_neg hz.le, inv_mul_eq_div, le_div_iff₀ hzα, one_mul]
          exact Real.rpow_le_rpow hz.le hza.le hα
        calc ∏ p ∈ a.primeFactors, f p
            = (∏ p ∈ a.primeFactors, f p) * 1 := (mul_one _).symm
          _ ≤ (∏ p ∈ a.primeFactors, f p) * (z ^ (-α) * (a : ℝ) ^ α) :=
              mul_le_mul_of_nonneg_left h1 hterm_nn
          _ = z ^ (-α) * ((∏ p ∈ a.primeFactors, f p) * (a : ℝ) ^ α) := by ring
    _ ≤ ∑ a ∈ m.divisors, z ^ (-α) * ((∏ p ∈ a.primeFactors, f p) * (a : ℝ) ^ α) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro a ha _
        have hterm_nn : 0 ≤ ∏ p ∈ a.primeFactors, f p := hprodnn a ha
        have : (0 : ℝ) ≤ z ^ (-α) := (Real.rpow_pos_of_pos hz _).le
        positivity

/-! ## §2 — the primorial support bridge (`selHSum` ↔ smooth-squarefree divisor sum)

`H(z) = Σ_{r≤z, sqfree} g(r)` is the `r ≤ z` truncation of the FULL `z`-smooth product
`P(z) = Σ_{a∣z#} g(a) = ∏_{p≤z}(1+g(p))` (over the divisors of the primorial `z#`), since a
squarefree `r ≤ z` is exactly a divisor of `z#` that is `≤ z`. The gap `P(z) − H(z)` is the
`z`-smooth tail, Rankin-bounded by §1. -/

/-- Two distinct primes are relatively prime (the primorial-squarefree ingredient). -/
lemma isRelPrime_of_primes_ne {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    IsRelPrime p r := by
  intro d hdp hdr
  rcases (Nat.dvd_prime hp).mp hdp with rfl | rfl
  · exact isUnit_one
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdr) hpr

/-- **The primorial is squarefree** (a product of distinct primes). -/
lemma squarefree_primorial (z : ℕ) : Squarefree (primorial z) := by
  rw [primorial]
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp r hr hpr
    rw [Finset.mem_coe, Finset.mem_filter] at hp hr
    exact isRelPrime_of_primes_ne hp.2 hr.2 hpr
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.prime.irreducible.squarefree

/-- **The support bridge (index sets).** The squarefree naturals `≤ z` are exactly the divisors of
the primorial `z#` that are `≤ z`: a squarefree `r ≤ z` divides `z#` (its primes are `≤ r ≤ z`), and
every divisor of the squarefree `z#` is squarefree. -/
lemma sqfree_le_eq_primorial_divisors (z : ℕ) :
    (Finset.Icc 1 z).filter Squarefree = (primorial z).divisors.filter (· ≤ z) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_hr1, hrz⟩, hrsf⟩
    exact ⟨⟨hrsf.dvd_primorial.trans (primorial_dvd_primorial hrz), (primorial_pos z).ne'⟩, hrz⟩
  · rintro ⟨⟨hrdvd, _⟩, hrz⟩
    have hrsf : Squarefree r := (squarefree_primorial z).squarefree_of_dvd hrdvd
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hrsf.ne_zero, hrz⟩, hrsf⟩

/-- **`H(z)` as the primorial-restricted divisor sum.** `H(z) = Σ_{a∣z#, a≤z} g(a)`. -/
lemma selHSum_eq_primorial_le (χ : DirichletCharacter ℂ q) (z : ℕ) :
    selHSum χ z = ∑ a ∈ (primorial z).divisors.filter (· ≤ z), selGmul χ a := by
  rw [selHSum, sqfree_le_eq_primorial_divisors]

/-- **The full `z`-smooth product** `P(z) = Σ_{a∣z#} g(a)` (the Euler product over primes `≤ z`,
no size cut). -/
def selHFull (χ : DirichletCharacter ℂ q) (z : ℕ) : ℝ :=
  ∑ a ∈ (primorial z).divisors, selGmul χ a

/-- **§3 — the ζ·L product form of `P(z)`** (the landed local-split gift, lifted to the primorial):
`P(z) = ∏_{p≤z} 1/((1−1/p)(1−χ_ℝ(p)/p))`. Direct from `selHblock_divisors_eq` at the squarefree
`m = z#`, whose prime factors are the primes `≤ z`. -/
lemma selHFull_eq_zetaL (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) :
    selHFull χ z
      = ∏ p ∈ (primorial z).primeFactors, 1 / ((1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ))) := by
  rw [selHFull]
  exact selHblock_divisors_eq χ hsq (squarefree_primorial z)

/-- **The split `P(z) = H(z) + tail(z)`.** The full smooth product decomposes into the `r ≤ z` part
(`= H(z)`) and the `z`-smooth tail `Σ_{a∣z#, a>z} g(a)`. -/
lemma selHFull_eq_add_tail (χ : DirichletCharacter ℂ q) (z : ℕ) :
    selHFull χ z = selHSum χ z
      + ∑ a ∈ (primorial z).divisors.filter (fun a => ¬ a ≤ z), selGmul χ a := by
  rw [selHFull, selHSum_eq_primorial_le χ z]
  exact (Finset.sum_filter_add_sum_filter_not _ (· ≤ z) _).symm

/-- **The effective smooth-product lower bound for `H(z)` (stone 2 core).** For `z ≥ 1` and a
structural exponent `α ≥ 0`, the truncation defect `P(z) − H(z)` (the `z`-smooth tail) is
Rankin-bounded, so
`H(z) ≥ P(z) − z^{−α}·∏_{p≤z}(1 + g(p)·p^α)`.
The Rankin factor is §1's `rankin_tail_le` at `f = g = selG χ` and `m = z#`. -/
theorem selHSum_ge_full_sub_rankin (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z : ℕ} (hz : 1 ≤ z) {α : ℝ} (hα : 0 ≤ α) :
    selHFull χ z
        - (z : ℝ) ^ (-α) * ∏ p ∈ (primorial z).primeFactors, (1 + selG χ p * (p : ℝ) ^ α)
      ≤ selHSum χ z := by
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have htail_eq : (primorial z).divisors.filter (fun a => ¬ a ≤ z)
      = (primorial z).divisors.filter (fun a : ℕ => (z : ℝ) < (a : ℝ)) := by
    refine Finset.filter_congr fun a _ => ?_
    simp only [not_le, Nat.cast_lt]
  have hfnn : ∀ p ∈ (primorial z).primeFactors, 0 ≤ selG χ p := fun p hp =>
    (selG_pos χ hsq (Nat.prime_of_mem_primeFactors hp).two_le).le
  have hrankin := rankin_tail_le (squarefree_primorial z) hα hzR (f := selG χ) hfnn
  rw [selHFull_eq_add_tail χ z, htail_eq]
  have hbound : ∑ a ∈ (primorial z).divisors.filter (fun a : ℕ => (z : ℝ) < (a : ℝ)), selGmul χ a
      ≤ (z : ℝ) ^ (-α) * ∏ p ∈ (primorial z).primeFactors, (1 + selG χ p * (p : ℝ) ^ α) := by
    simpa only [selGmul] using hrankin
  linarith

/-- **The effective truncated Euler product lower bound for `H(z)` (stones 2+3 combined).** The
headline R5 supply: `H(z)` is bounded below by the truncated ζ·L Euler product minus the Rankin
defect,
`H(z) ≥ ∏_{p≤z} 1/((1−1/p)(1−χ_ℝ(p)/p)) − z^{−α}·∏_{p≤z}(1 + g(p)·p^α)`.
The first product is the effective ζ·L supply (`selHFull_eq_zetaL`); the second is the `δ_b`-defect
whose numerical `≤ 300 z^{−0.4}·(first)` bound is recorded in the R5-EULER flag. -/
theorem selHSum_ge_zetaL_sub_rankin (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z : ℕ} (hz : 1 ≤ z) {α : ℝ} (hα : 0 ≤ α) :
    (∏ p ∈ (primorial z).primeFactors, 1 / ((1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ))))
        - (z : ℝ) ^ (-α) * ∏ p ∈ (primorial z).primeFactors, (1 + selG χ p * (p : ℝ) ^ α)
      ≤ selHSum χ z := by
  rw [← selHFull_eq_zetaL χ hsq z]
  exact selHSum_ge_full_sub_rankin χ hsq hz hα

/-! ## §4 — the ζ-side / L-side factorisation (the Mertens hook and the L-side wall)

`P(z) = ∏_{p≤z}(1−1/p)⁻¹ · ∏_{p≤z}(1−χ(p)/p)⁻¹`. The **ζ-side** is corpus-effective: the prime set
`(primorial z).primeFactors` is exactly `(range(z+1)).filter Prime`, the index of
`Salt.Mertens.mertens_third`, so `∏(1−1/p)⁻¹ ≈ e^γ log z` with an explicit error (this supplies the
`1/u` pole at the deep-regime scale `z = e^{1/u}`). The **L-side** `∏(1−χ(p)/p)⁻¹` vs `L(1,χ) = L₁`
is the genuine wall — see the R5-EULER flag for the exact statement it must supply. -/

/-- **The primorial's prime factors are the primes `≤ z`** — the re-index that hooks the corpus
`mertens_third` (indexed by `(range(z+1)).filter Prime`) onto the ζ-side factor of `P(z)`. -/
lemma primorial_primeFactors (z : ℕ) :
    (primorial z).primeFactors = (Finset.range (z + 1)).filter Nat.Prime := by
  rw [primorial]
  exact Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)

/-- **The ζ·L factorisation of `P(z)`** (the Mertens hook). `P(z)` splits into the ζ-side
`∏_{p≤z}(1−1/p)⁻¹` (corpus-effective via `mertens_third` + `primorial_primeFactors`) and the L-side
`∏_{p≤z}(1−χ_ℝ(p)/p)⁻¹` (the effective-truncated-Euler wall). -/
lemma selHFull_eq_zeta_mul_L (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) :
    selHFull χ z
      = (∏ p ∈ (primorial z).primeFactors, (1 - 1 / (p : ℝ))⁻¹)
        * (∏ p ∈ (primorial z).primeFactors, (1 - chiRe χ p / (p : ℝ))⁻¹) := by
  rw [selHFull_eq_zetaL χ hsq z, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [one_div, mul_inv]

end Salt.SW

end
