/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The Goldbach-sieve `hsq` majorant (rebuild nodes GB-11 + GB-14)

The squared-main-term majorant of the binary-Goldbach upper sieve
(`docs/exploration/s3-a3-design.md`, sections "GB-SIEVE-R0" and "GB-0 — THE
REBUILD DESIGN FREEZE").  Two nodes:

* **GB-11 — the frozen defs.**  For a modulus `d`, the per-prime weight
  `hFac d = ∏_{p ∣ d} 1/(p−2)` (odd `d` ⟹ every `p ≥ 3` ⟹ `p−2 ≥ 1 > 0`) and
  the truncated singular-series majorant `sTrunc n = ∑_{d ∣ n, sqfree, odd}
  hFac d`.  Basic API: positivity, multiplicativity over coprime factors, and
  the powerset bound `sTrunc n ≤ ∏_{p ∣ n, odd} (1 + 1/(p−2))`.

* **GB-14 — the Euler-product majorant** (the load-bearing node).  The double
  sum over odd squarefree `d₁, d₂` of `hFac d₁ · hFac d₂ / lcm(d₁,d₂)` is
  bounded by an ABSOLUTE constant, uniformly in the range cap `X`.  Route: the
  double sum factors per-prime — for odd squarefree `d₁, d₂`,
  `hFac d₁ · hFac d₂ / lcm(d₁,d₂) = ∏_p c(p, memberships)` where each prime
  `p ≥ 3` contributes `1` (in neither), `1/((p−2)p)` (in exactly one — twice),
  or `1/((p−2)²p)` (in both); so the sum ≤ `∏_{p odd prime ≤ X}
  (1 + 2/((p−2)p) + 1/((p−2)²p))`.  Each local factor is `1 + O(1/p²)`, so the
  product is bounded by `exp(∑_p O(1/p²)) ≤ exp(9·ζ(2))` (direct
  `Real.add_one_le_exp` + `summable_one_div_nat_pow`, NOT `euler_tail_L`: the
  `p = 3` local factor puts `∑ x_p > 1/2`, so `prod_one_add_le` does not
  apply — the exp majorant is the right tool).
-/
import Mathlib

open Finset

namespace Salt.Entropy.Chowla

/-! ## GB-11 — the frozen definitions -/

/-- The per-prime weight `hFac d = ∏_{p ∣ d} 1/(p−2)`.  For odd squarefree `d`
every prime factor `p ≥ 3`, so each factor `1/(p−2) ≥ 1 > 0`. -/
noncomputable def hFac (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2))

/-- The truncated singular-series majorant: the sum of `hFac d` over the odd
squarefree divisors of `n`. -/
noncomputable def sTrunc (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => Squarefree d ∧ Odd d), hFac d

/-! ## Odd prime factors are `≥ 3` -/

/-- Every prime factor of an odd number is at least `3`. -/
lemma three_le_of_odd_primeFactor {d p : ℕ} (hd : Odd d) (hp : p ∈ d.primeFactors) :
    3 ≤ p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : d % 2 = 1 := Nat.odd_iff.mp hd
    omega
  have := hpp.two_le
  omega

/-! ## GB-11 API -/

/-- `hFac d > 0` for odd `d` (every prime factor `p ≥ 3`, so `1/(p−2) > 0`). -/
theorem hFac_pos {d : ℕ} (hd : Odd d) : 0 < hFac d := by
  rw [hFac]
  apply Finset.prod_pos
  intro p hp
  have h3 := three_le_of_odd_primeFactor hd hp
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  exact one_div_pos.mpr this

/-- `hFac d ≥ 0` for odd `d`. -/
theorem hFac_nonneg {d : ℕ} (hd : Odd d) : 0 ≤ hFac d := (hFac_pos hd).le

/-- Multiplicativity of `hFac` over coprime factors. -/
theorem hFac_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : Nat.Coprime m n) : hFac (m * n) = hFac m * hFac n := by
  rw [hFac, hFac, hFac, Nat.primeFactors_mul hm hn,
    Finset.prod_union h.disjoint_primeFactors]

/-- `sTrunc n ≥ 0`. -/
theorem sTrunc_nonneg (n : ℕ) : 0 ≤ sTrunc n := by
  apply Finset.sum_nonneg
  intro d hd
  rw [Finset.mem_filter] at hd
  exact hFac_nonneg hd.2.2

/-- An odd prime is at least `3`. -/
lemma three_le_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have h2 := hp.two_le
  have : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  omega

/-! ## Powerset factorization helpers (shared by `sTrunc_le_prod` and GB-14) -/

/-- For `S ⊆ P`, the per-element `if`-product splits as the product over `S`
(true branch) times the product over `P \ S` (false branch). -/
private lemma prod_ite_split {S P : Finset ℕ} (hSP : S ⊆ P) (f g : ℕ → ℝ) :
    (∏ p ∈ P, (if p ∈ S then f p else g p)) = (∏ p ∈ S, f p) * ∏ p ∈ P \ S, g p := by
  rw [← Finset.prod_sdiff hSP]
  have h1 : (∏ p ∈ P \ S, (if p ∈ S then f p else g p)) = ∏ p ∈ P \ S, g p :=
    Finset.prod_congr rfl (fun p hp => if_neg (Finset.mem_sdiff.mp hp).2)
  have h2 : (∏ p ∈ S, (if p ∈ S then f p else g p)) = ∏ p ∈ S, f p :=
    Finset.prod_congr rfl (fun p hp => if_pos hp)
  rw [h1, h2, mul_comm]

/-- For `S ⊆ P`, `∏_{p∈P} (if p∈S then f p else 1) = ∏_{p∈S} f p`. -/
private lemma prod_ite_one {S P : Finset ℕ} (hSP : S ⊆ P) (f : ℕ → ℝ) :
    (∏ p ∈ P, (if p ∈ S then f p else 1)) = ∏ p ∈ S, f p := by
  rw [prod_ite_split hSP f (fun _ => 1), Finset.prod_const_one, mul_one]

/-- **Sum over the powerset = product of local sums.**  Summing a per-element
`if`-product over all subsets of `P` yields the product of the two branch
values.  This is `Finset.prod_add` in `if`-form; applying it twice factors the
GB-14 double sum into an Euler product. -/
private lemma sum_powerset_prod_ite (P : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ S ∈ P.powerset, ∏ p ∈ P, (if p ∈ S then f p else g p))
      = ∏ p ∈ P, (f p + g p) := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [prod_ite_split (Finset.mem_powerset.mp hS)]

/-- **GB-11, the powerset bound.**  `sTrunc n` is at most the Euler product over
the odd prime factors of `n` of `1 + 1/(p−2)`.  The odd squarefree divisors of
`n` inject (via `primeFactors`) into the powerset of `n`'s odd prime factors;
enlarging to the full powerset (nonnegative terms) and applying `prod_add`
gives the product. -/
theorem sTrunc_le_prod (n : ℕ) :
    sTrunc n ≤ ∏ p ∈ n.primeFactors.filter (fun p => Odd p), (1 + 1 / ((p : ℝ) - 2)) := by
  classical
  set Dn := n.divisors.filter (fun d => Squarefree d ∧ Odd d) with hDn
  set P := n.primeFactors.filter (fun p => Odd p) with hP
  have hmem : ∀ d ∈ Dn, d.primeFactors ⊆ P := by
    intro d hd
    rw [hDn, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, hn0⟩, _, hodd⟩ := hd
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h3 := three_le_of_odd_primeFactor hodd hp
    rw [hP, Finset.mem_filter]
    refine ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hdn, hn0⟩, ?_⟩
    rcases hpp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hInj : Set.InjOn Nat.primeFactors ↑Dn := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hDn, Finset.mem_filter] at hx hy
    have hx' := Nat.prod_primeFactors_of_squarefree hx.2.1
    rw [← hx', hxy, Nat.prod_primeFactors_of_squarefree hy.2.1]
  have hStr : sTrunc n
      = ∑ S ∈ Dn.image Nat.primeFactors, ∏ p ∈ S, (1 / ((p : ℝ) - 2)) := by
    have hsum : sTrunc n = ∑ d ∈ Dn, hFac d := rfl
    have himg : (∑ S ∈ Dn.image Nat.primeFactors, ∏ p ∈ S, (1 / ((p : ℝ) - 2)))
        = ∑ d ∈ Dn, ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) :=
      Finset.sum_image hInj
    rw [hsum, himg]
    exact Finset.sum_congr rfl (fun d _ => rfl)
  rw [hStr]
  have hsub : Dn.image Nat.primeFactors ⊆ P.powerset := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨d, hd, rfl⟩ := hS
    rw [Finset.mem_powerset]
    exact hmem d hd
  have hnn : ∀ S ∈ P.powerset, 0 ≤ ∏ p ∈ S, (1 / ((p : ℝ) - 2)) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    apply Finset.prod_nonneg
    intro p hp
    have hpP := hS hp
    rw [hP, Finset.mem_filter] at hpP
    have hpp := Nat.prime_of_mem_primeFactors hpP.1
    have h3 := three_le_of_odd_prime hpp hpP.2
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    exact (one_div_pos.mpr this).le
  calc ∑ S ∈ Dn.image Nat.primeFactors, ∏ p ∈ S, (1 / ((p : ℝ) - 2))
      ≤ ∑ S ∈ P.powerset, ∏ p ∈ S, (1 / ((p : ℝ) - 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun S hS _ => hnn S hS)
    _ = ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 2)) := by
        have hrw : (∑ S ∈ P.powerset, ∏ p ∈ S, (1 / ((p : ℝ) - 2)))
            = ∑ S ∈ P.powerset, ∏ p ∈ P, (if p ∈ S then (1 / ((p : ℝ) - 2)) else 1) :=
          Finset.sum_congr rfl (fun S hS =>
            (prod_ite_one (Finset.mem_powerset.mp hS) (fun p => 1 / ((p : ℝ) - 2))).symm)
        rw [hrw, sum_powerset_prod_ite]
        exact Finset.prod_congr rfl (fun p _ => by ring)

/-! ## GB-14 — the Euler-product majorant

The per-prime local factors `uu p = 1/(p−2)` and `vv p = 1/p`, and the
lcm-coupled double-sum summand `Gterm S₁ S₂` in factored form. -/

/-- Local factor `1/(p−2)` (the `(p−2)⁻¹` of `hFac`). -/
private noncomputable def uu (p : ℕ) : ℝ := 1 / ((p : ℝ) - 2)

/-- Local factor `1/p` (from the reciprocal lcm). -/
private noncomputable def vv (p : ℕ) : ℝ := 1 / (p : ℝ)

/-- The per-prime factored form of `hFac d₁ · hFac d₂ / lcm(d₁,d₂)`: over a pair
of squarefree odd prime-factor sets `S₁, S₂`, the `uu`-weight of each times the
`vv`-weight of the union (the union = prime factors of the lcm). -/
private noncomputable def Gterm (S₁ S₂ : Finset ℕ) : ℝ :=
  (∏ p ∈ S₁, uu p) * (∏ p ∈ S₂, uu p) * ∏ p ∈ S₁ ∪ S₂, vv p

private lemma vv_nonneg (p : ℕ) : 0 ≤ vv p := by simp only [vv]; positivity

private lemma uu_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ uu p := by
  simp only [uu]
  have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact one_div_nonneg.mpr (by linarith)

/-- **The lcm identity.**  For squarefree `d₁, d₂`, the real cast of
`lcm(d₁,d₂)` equals the product of the primes in `pf d₁ ∪ pf d₂` (the lcm is
squarefree with exactly those prime factors). -/
private lemma cast_lcm_eq_prod {d₁ d₂ : ℕ} (h1 : Squarefree d₁) (h2 : Squarefree d₂) :
    (Nat.lcm d₁ d₂ : ℝ) = ∏ p ∈ d₁.primeFactors ∪ d₂.primeFactors, (p : ℝ) := by
  have hd1 : d₁ ≠ 0 := h1.ne_zero
  have hd2 : d₂ ≠ 0 := h2.ne_zero
  have hlcm0 : Nat.lcm d₁ d₂ ≠ 0 := Nat.lcm_ne_zero hd1 hd2
  have hlcmdvd : Nat.lcm d₁ d₂ ∣ d₁ * d₂ :=
    ⟨Nat.gcd d₁ d₂, by rw [← Nat.gcd_mul_lcm d₁ d₂]; ring⟩
  have hsq : Squarefree (Nat.lcm d₁ d₂) := by
    rw [Nat.squarefree_iff_factorization_le_one hlcm0]
    intro p
    rw [Nat.factorization_lcm hd1 hd2, Finsupp.sup_apply, sup_le_iff]
    exact ⟨(Nat.squarefree_iff_factorization_le_one hd1).mp h1 p,
      (Nat.squarefree_iff_factorization_le_one hd2).mp h2 p⟩
  have hpf : (Nat.lcm d₁ d₂).primeFactors = d₁.primeFactors ∪ d₂.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_union]
    constructor
    · rintro ⟨hpp, hpl, _⟩
      rcases (Nat.Prime.dvd_mul hpp).mp (hpl.trans hlcmdvd) with h | h
      · exact Or.inl ⟨hpp, h, hd1⟩
      · exact Or.inr ⟨hpp, h, hd2⟩
    · rintro (⟨hpp, hpd, _⟩ | ⟨hpp, hpd, _⟩)
      · exact ⟨hpp, hpd.trans (Nat.dvd_lcm_left d₁ d₂), hlcm0⟩
      · exact ⟨hpp, hpd.trans (Nat.dvd_lcm_right d₁ d₂), hlcm0⟩
  have hprod : (∏ p ∈ (Nat.lcm d₁ d₂).primeFactors, p) = Nat.lcm d₁ d₂ :=
    Nat.prod_primeFactors_of_squarefree hsq
  rw [hpf] at hprod
  rw [← hprod, Nat.cast_prod]

/-- `Gterm S₁ S₂ ≥ 0` when both index sets consist of primes `≥ 3`. -/
private lemma Gterm_nonneg {S₁ S₂ : Finset ℕ} (h1 : ∀ p ∈ S₁, 3 ≤ p)
    (h2 : ∀ p ∈ S₂, 3 ≤ p) : 0 ≤ Gterm S₁ S₂ := by
  simp only [Gterm]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact Finset.prod_nonneg fun p hp => uu_nonneg (h1 p hp)
  · exact Finset.prod_nonneg fun p hp => uu_nonneg (h2 p hp)
  · exact Finset.prod_nonneg fun p _ => vv_nonneg p

/-- **The per-prime factorization of `Gterm`.**  For `S₁, S₂ ⊆ P`, `Gterm S₁ S₂`
is the product over `P` of the local factor (an `uu` for each membership in
`S₁`, `S₂`, and a `vv` for membership in the union). -/
private lemma Gterm_eq_ccprod {S₁ S₂ P : Finset ℕ} (h1 : S₁ ⊆ P) (h2 : S₂ ⊆ P) :
    Gterm S₁ S₂ = ∏ p ∈ P, ((if p ∈ S₁ then uu p else 1)
      * (if p ∈ S₂ then uu p else 1) * (if p ∈ S₁ ∪ S₂ then vv p else 1)) := by
  have hu : S₁ ∪ S₂ ⊆ P := Finset.union_subset h1 h2
  simp only [Gterm]
  rw [← prod_ite_one h1 uu, ← prod_ite_one h2 uu, ← prod_ite_one hu vv,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- **The GB-14 double-sum factorization.**  Summing `Gterm` over all pairs of
subsets of `P` yields the Euler product of the local factors
`1 + 2/((p−2)p) + 1/((p−2)²p)`.  Proved by applying `sum_powerset_prod_ite`
twice (inner `S₂`, then outer `S₁`). -/
private lemma doubleSum_powerset_eq_prod (P : Finset ℕ) :
    (∑ S₁ ∈ P.powerset, ∑ S₂ ∈ P.powerset, Gterm S₁ S₂)
      = ∏ p ∈ P, (uu p ^ 2 * vv p + uu p * vv p + (uu p * vv p + 1)) := by
  have hinner : ∀ S₁ ∈ P.powerset,
      (∑ S₂ ∈ P.powerset, Gterm S₁ S₂)
        = ∏ p ∈ P, (if p ∈ S₁ then uu p ^ 2 * vv p + uu p * vv p
            else uu p * vv p + 1) := by
    intro S₁ hS₁
    have hS₁P : S₁ ⊆ P := Finset.mem_powerset.mp hS₁
    have hstep : ∀ S₂ ∈ P.powerset, Gterm S₁ S₂
        = ∏ p ∈ P, (if p ∈ S₂
            then (if p ∈ S₁ then uu p else 1) * uu p * vv p
            else (if p ∈ S₁ then uu p else 1) * (if p ∈ S₁ then vv p else 1)) := by
      intro S₂ hS₂
      rw [Gterm_eq_ccprod hS₁P (Finset.mem_powerset.mp hS₂)]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      by_cases h : p ∈ S₂
      · simp only [h, if_true, Finset.mem_union, or_true]
      · simp only [h, if_false, Finset.mem_union, or_false, mul_one]
    rw [Finset.sum_congr rfl hstep,
      sum_powerset_prod_ite P
        (fun p => (if p ∈ S₁ then uu p else 1) * uu p * vv p)
        (fun p => (if p ∈ S₁ then uu p else 1) * (if p ∈ S₁ then vv p else 1))]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    by_cases h : p ∈ S₁
    · simp only [h, if_true]; ring
    · simp only [h, if_false, one_mul]
  rw [Finset.sum_congr rfl hinner,
    sum_powerset_prod_ite P
      (fun p => uu p ^ 2 * vv p + uu p * vv p)
      (fun p => uu p * vv p + 1)]

/-- **The Euler product is bounded by an absolute constant.**  For any set `P`
of primes `≥ 3`, the product of local factors `1 + 2/((p−2)p) + 1/((p−2)²p)` is
at most `exp(9·ζ(2))`.  Each local factor `≤ exp(x_p)` with
`x_p = 2/((p−2)p) + 1/((p−2)²p) ≤ 9/p²`, and `∑_p 1/p² ≤ ζ(2)` uniformly
(`summable_one_div_nat_pow`). -/
private lemma prod_L_le_exp {P : Finset ℕ} (hP : ∀ p ∈ P, 3 ≤ p) :
    (∏ p ∈ P, (uu p ^ 2 * vv p + uu p * vv p + (uu p * vv p + 1)))
      ≤ Real.exp (9 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) := by
  have huu : ∀ p ∈ P, 0 ≤ uu p := fun p hp => uu_nonneg (hP p hp)
  have hstep1 : (∏ p ∈ P, (uu p ^ 2 * vv p + uu p * vv p + (uu p * vv p + 1)))
      ≤ Real.exp (∑ p ∈ P, (2 * (uu p * vv p) + uu p ^ 2 * vv p)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have t1 : 0 ≤ uu p ^ 2 * vv p := mul_nonneg (sq_nonneg _) (vv_nonneg p)
      have t2 : 0 ≤ uu p * vv p := mul_nonneg (huu p hp) (vv_nonneg p)
      linarith
    · intro p _
      have heq : uu p ^ 2 * vv p + uu p * vv p + (uu p * vv p + 1)
          = (2 * (uu p * vv p) + uu p ^ 2 * vv p) + 1 := by ring
      rw [heq]
      exact Real.add_one_le_exp _
  have hxle : ∀ p ∈ P, (2 * (uu p * vv p) + uu p ^ 2 * vv p) ≤ 9 * (1 / (p : ℝ) ^ 2) := by
    intro p hp
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hp
    simp only [uu, vv]
    set q : ℝ := (p : ℝ) with hqdef
    have hq2 : (0 : ℝ) < q - 2 := by linarith
    have hq0 : (0 : ℝ) < q := by linarith
    have hq2' : q - 2 ≠ 0 := hq2.ne'
    have hq0' : q ≠ 0 := hq0.ne'
    rw [← sub_nonneg]
    have hexp : 9 * (1 / q ^ 2) - (2 * (1 / (q - 2) * (1 / q)) + (1 / (q - 2)) ^ 2 * (1 / q))
        = (7 * q ^ 2 - 33 * q + 36) / (q ^ 2 * (q - 2) ^ 2) := by
      field_simp
      ring
    rw [hexp]
    apply div_nonneg
    · nlinarith [sq_nonneg (q - 3), h3]
    · positivity
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    have h := Real.summable_one_div_nat_pow (p := 2)
    exact h.mpr (by norm_num)
  have hsum_le : (∑ p ∈ P, (2 * (uu p * vv p) + uu p ^ 2 * vv p))
      ≤ 9 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
    calc (∑ p ∈ P, (2 * (uu p * vv p) + uu p ^ 2 * vv p))
        ≤ ∑ p ∈ P, 9 * (1 / (p : ℝ) ^ 2) := Finset.sum_le_sum hxle
      _ = 9 * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 9 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 9)
          exact hsummable.sum_le_tsum P (fun n _ => by positivity)
  exact le_trans hstep1 (Real.exp_le_exp.mpr hsum_le)

/-- **GB-14 — the Euler-product majorant.**  The double sum over odd squarefree
`d₁, d₂ ≤ X` of `hFac d₁ · hFac d₂ / lcm(d₁,d₂)` is bounded by an absolute
constant `K = exp(9·ζ(2))`, uniformly in `X`.  This is the `hsq` long pole: the
squared-main-term Fubini of the binary-Goldbach upper sieve converges. -/
theorem hFac_lcm_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℕ),
      ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
        ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
          hFac d₁ * hFac d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K := by
  classical
  refine ⟨Real.exp (9 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2), Real.exp_pos _, fun X => ?_⟩
  set D := (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d) with hDdef
  set P := (Finset.range (X + 1)).filter (fun p => p.Prime ∧ Odd p) with hPdef
  have hP3 : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    rw [hPdef, Finset.mem_filter] at hp
    exact three_le_of_odd_prime hp.2.1 hp.2.2
  have hpfsub : ∀ d ∈ D, d.primeFactors ⊆ P := by
    intro d hd
    rw [hDdef, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hdlt, _, hodd⟩ := hd
    have hd0 : 0 < d := by have := Nat.odd_iff.mp hodd; omega
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hodd_p : Odd p := by
      rcases hpp.eq_two_or_odd' with h | h
      · have := three_le_of_odd_primeFactor hodd hp; omega
      · exact h
    have hple : p ≤ d := Nat.le_of_dvd hd0 hpd
    rw [hPdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp, hodd_p⟩
  have hInj : Set.InjOn Nat.primeFactors ↑D := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hDdef, Finset.mem_filter] at hx hy
    have hx' := Nat.prod_primeFactors_of_squarefree hx.2.1
    rw [← hx', hxy, Nat.prod_primeFactors_of_squarefree hy.2.1]
  have hterm : ∀ d₁ ∈ D, ∀ d₂ ∈ D,
      hFac d₁ * hFac d₂ / (Nat.lcm d₁ d₂ : ℝ)
        = Gterm d₁.primeFactors d₂.primeFactors := by
    intro d₁ hd₁ d₂ hd₂
    rw [hDdef, Finset.mem_filter] at hd₁ hd₂
    have hsq1 := hd₁.2.1
    have hsq2 := hd₂.2.1
    have e1 : hFac d₁ = ∏ p ∈ d₁.primeFactors, uu p := rfl
    have e2 : hFac d₂ = ∏ p ∈ d₂.primeFactors, uu p := rfl
    have hlcm : (Nat.lcm d₁ d₂ : ℝ)
        = ∏ p ∈ d₁.primeFactors ∪ d₂.primeFactors, (p : ℝ) :=
      cast_lcm_eq_prod hsq1 hsq2
    have hvvprod : (∏ p ∈ d₁.primeFactors ∪ d₂.primeFactors, vv p)
        = 1 / (Nat.lcm d₁ d₂ : ℝ) := by
      simp only [vv, one_div]
      rw [Finset.prod_inv_distrib, ← hlcm]
    rw [e1, e2]
    simp only [Gterm]
    rw [hvvprod]
    ring
  have hEq : (∑ d₁ ∈ D, ∑ d₂ ∈ D, hFac d₁ * hFac d₂ / (Nat.lcm d₁ d₂ : ℝ))
      = ∑ d₁ ∈ D, ∑ d₂ ∈ D, Gterm d₁.primeFactors d₂.primeFactors :=
    Finset.sum_congr rfl (fun d₁ hd₁ =>
      Finset.sum_congr rfl (fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂))
  have hsubP : D.image Nat.primeFactors ⊆ P.powerset := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨d, hd, rfl⟩ := hS
    rw [Finset.mem_powerset]
    exact hpfsub d hd
  have hGnn : ∀ S₁ ∈ P.powerset, ∀ S₂ ∈ P.powerset, 0 ≤ Gterm S₁ S₂ := by
    intro S₁ hS₁ S₂ hS₂
    exact Gterm_nonneg (fun p hp => hP3 p (Finset.mem_powerset.mp hS₁ hp))
      (fun p hp => hP3 p (Finset.mem_powerset.mp hS₂ hp))
  have hreindex : (∑ d₁ ∈ D, ∑ d₂ ∈ D,
        hFac d₁ * hFac d₂ / (Nat.lcm d₁ d₂ : ℝ))
      ≤ ∑ S₁ ∈ P.powerset, ∑ S₂ ∈ P.powerset, Gterm S₁ S₂ := by
    rw [hEq]
    have hInner : ∀ d₁ ∈ D, (∑ d₂ ∈ D, Gterm d₁.primeFactors d₂.primeFactors)
        = ∑ S₂ ∈ D.image Nat.primeFactors, Gterm d₁.primeFactors S₂ :=
      fun d₁ _ => (Finset.sum_image hInj).symm
    rw [Finset.sum_congr rfl hInner]
    have hOuter : (∑ d₁ ∈ D,
          ∑ S₂ ∈ D.image Nat.primeFactors, Gterm d₁.primeFactors S₂)
        = ∑ S₁ ∈ D.image Nat.primeFactors,
            ∑ S₂ ∈ D.image Nat.primeFactors, Gterm S₁ S₂ :=
      (Finset.sum_image (f := fun S₁ => ∑ S₂ ∈ D.image Nat.primeFactors, Gterm S₁ S₂)
        hInj).symm
    rw [hOuter]
    calc (∑ S₁ ∈ D.image Nat.primeFactors,
            ∑ S₂ ∈ D.image Nat.primeFactors, Gterm S₁ S₂)
        ≤ ∑ S₁ ∈ D.image Nat.primeFactors,
            ∑ S₂ ∈ P.powerset, Gterm S₁ S₂ := by
          apply Finset.sum_le_sum
          intro S₁ hS₁
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubP
          intro S₂ hS₂mem _
          exact hGnn S₁ (hsubP hS₁) S₂ hS₂mem
      _ ≤ ∑ S₁ ∈ P.powerset, ∑ S₂ ∈ P.powerset, Gterm S₁ S₂ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubP
          intro S₁ hS₁mem _
          exact Finset.sum_nonneg (fun S₂ hS₂mem => hGnn S₁ hS₁mem S₂ hS₂mem)
  calc (∑ d₁ ∈ D, ∑ d₂ ∈ D, hFac d₁ * hFac d₂ / (Nat.lcm d₁ d₂ : ℝ))
      ≤ ∑ S₁ ∈ P.powerset, ∑ S₂ ∈ P.powerset, Gterm S₁ S₂ := hreindex
    _ = ∏ p ∈ P, (uu p ^ 2 * vv p + uu p * vv p + (uu p * vv p + 1)) :=
        doubleSum_powerset_eq_prod P
    _ ≤ Real.exp (9 * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) := prod_L_le_exp hP3

end Salt.Entropy.Chowla
