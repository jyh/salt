/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.SelWeight
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Selberg optimization stones (`T-BAL` R4, wave 3b) — `selberg_opt_eq` + `selweight_abs_le_one`

Design: the JYH-ratified **T-BAL S₀ synthesis freeze** (`docs/exploration/tbal-s0-freeze.md`),
against the HOUSE-CORRECTED `selWeight` (`Salt/SW/SelWeight.lean`, local factor `(d:ℝ)/selHmul χ d`
= `1/ν(d)`). This module lands the two no-analysis optimization stones on the corrected weight:

* **`selberg_opt_eq`** — `V(selWeight) = 1/H(z)` EXACT, where the DH main term quadratic form is
  stated in the ν(lcm) form the R6/R7 consumers want:
  `V(w) := Σ_{d,e ≤ z, sf} w_d w_e · ν(lcm(d,e))`, `ν(n) = selHmul χ n / n = ∏_{p∣n} h(p)/p`
  (the flags' `V(w) = Σ w_d w_e ν([d,e])`). Route (hand-rolled, support-native on
  `(Icc 1 z).filter Squarefree`, no mathlib `BoundingSieve` instantiation): diagonalize
  `V = Σ_l g(l)⁻¹ · y_l²`, `y_l = Σ_{l∣d} ν(d) w_d`, via the ν-inversion
  `ν(g)⁻¹ = Σ_{l∣g} g(l)⁻¹` (from mathlib's `prodPrimeFactors_add_of_squarefree`); the corrected
  def was BUILT so `ν(d)·w_d = μ(d) g(d) G_d/H` telescopes to `y_l = μ(l) g(l)/H`, whence
  `V = Σ_l g(l)/H² = H/H² = 1/H`.

* **`selweight_abs_le_one`** — `|selWeight χ z d| ≤ 1`, via the classical partial-`H` bound
  `∏_{p∣d}(1+g(p))·G_d ≤ H(z)` (an injection of the `d`-part/coprime-part factorization into the
  squarefree support ≤ `z`).

Numerically certified verbatim (freeze defs, scratchpad `collapse_check.py`): the collapse
`y_l = μ(l) g(l)/H` and `V = 1/H` hold to `~1e-16` over `χ ∈ {triv, mixed}`, `z ∈ {6..30}`,
`l ∈ {1,2,3,6,10,30}` (catch #163: validated off `l = 1`); `max|selWeight_d| = 1` at `d = 1`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex Finset

noncomputable section

namespace Salt.SW

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-! ## §1 — the local density `ν(n) = h(n)/n` and its multiplicative algebra -/

/-- **The Selberg local density** `ν(n) = selHmul χ n / n = ∏_{p∣n} h(p)/p` (the DH main term's
per-modulus factor; `= h(p)/p` at primes). -/
def selNu {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ := selHmul χ n / (n : ℝ)

/-- `0 < selHmul χ d` for real `χ` (a product of positive prime factors; empty product `= 1`). -/
lemma selHmul_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (d : ℕ) :
    0 < selHmul χ d :=
  Finset.prod_pos (fun _p hp => selH_pos χ hsq (Nat.prime_of_mem_primeFactors hp).two_le)

/-- `0 < selNu χ d` for real `χ`, `d ≥ 1`. -/
lemma selNu_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {d : ℕ} (hd : 1 ≤ d) :
    0 < selNu χ d :=
  div_pos (selHmul_pos χ hsq d) (by exact_mod_cast hd)

/-- The prime factors of `lcm d e` (for `d, e ≠ 0`) are the union of those of `d` and `e`. -/
lemma primeFactors_lcm {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    (Nat.lcm d e).primeFactors = d.primeFactors ∪ e.primeFactors := by
  have hlcm : Nat.lcm d e ≠ 0 := Nat.lcm_ne_zero hd he
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_union, ne_eq]
  constructor
  · rintro ⟨hp, hpl, -⟩
    have hpde : p ∣ d * e := hpl.trans (Nat.lcm_dvd (dvd_mul_right d e) (dvd_mul_left e d))
    rcases (Nat.Prime.dvd_mul hp).mp hpde with h | h
    · exact Or.inl ⟨hp, h, hd⟩
    · exact Or.inr ⟨hp, h, he⟩
  · rintro (⟨hp, hpd, -⟩ | ⟨hp, hpe, -⟩)
    · exact ⟨hp, hpd.trans (Nat.dvd_lcm_left d e), hlcm⟩
    · exact ⟨hp, hpe.trans (Nat.dvd_lcm_right d e), hlcm⟩

/-- **`selHmul` gcd/lcm multiplicativity.** `h(lcm)·h(gcd) = h(d)·h(e)` (`∏` over union·inter =
`∏` over `d`·`e`). -/
lemma selHmul_lcm_mul_gcd {q : ℕ} (χ : DirichletCharacter ℂ q) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    selHmul χ (Nat.lcm d e) * selHmul χ (Nat.gcd d e) = selHmul χ d * selHmul χ e := by
  rw [selHmul, selHmul, selHmul, selHmul, primeFactors_lcm hd he, Nat.primeFactors_gcd hd he]
  exact Finset.prod_union_inter

/-- **The `ν(lcm)` split.** For squarefree `d, e ≥ 1`,
`ν(lcm(d,e)) = ν(d)·ν(e)·ν(gcd(d,e))⁻¹` (`ν` multiplicative, `lcm·gcd = d·e`). -/
lemma selNu_lcm_split {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {d e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) :
    selNu χ (Nat.lcm d e) = selNu χ d * selNu χ e * (selNu χ (Nat.gcd d e))⁻¹ := by
  have hd0 : d ≠ 0 := by omega
  have he0 : e ≠ 0 := by omega
  have hg1 : 1 ≤ Nat.gcd d e := Nat.gcd_pos_of_pos_left e (by omega)
  have hgcdNu : selNu χ (Nat.gcd d e) ≠ 0 := (selNu_pos χ hsq hg1).ne'
  have hmul : selNu χ (Nat.lcm d e) * selNu χ (Nat.gcd d e) = selNu χ d * selNu χ e := by
    rw [selNu, selNu, selNu, selNu, div_mul_div_comm, div_mul_div_comm,
      selHmul_lcm_mul_gcd χ hd0 he0]
    congr 1
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_comm (Nat.lcm d e) (Nat.gcd d e), Nat.gcd_mul_lcm]
  rw [← div_eq_mul_inv, eq_div_iff hgcdNu]
  exact hmul

/-! ## §2 — the squarefree divisor-sum identity (DIVPROD) and `ν`-inversion -/

/-- **DIVPROD.** For squarefree `m` and any real `f`,
`∏_{p∣m} (f p + 1) = Σ_{a∣m} ∏_{p∣a} f p`. Mathlib's `prodPrimeFactors_add_of_squarefree`
(with `g = ζ`), the multiplicative "sum over squarefree divisors". -/
lemma sum_divisors_prod_primeFactors {f : ℕ → ℝ} {m : ℕ} (hm : Squarefree m) :
    ∏ p ∈ m.primeFactors, (f p + 1)
      = ∑ a ∈ m.divisors, ∏ p ∈ a.primeFactors, f p := by
  have hF : (ArithmeticFunction.prodPrimeFactors f).IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors f
  have hζ : ((ζ : ArithmeticFunction ℝ)).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  have key := hF.prodPrimeFactors_add_of_squarefree hζ hm
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.prodPrimeFactors_apply hm.ne_zero] at key
  have goalRHS : ∑ a ∈ m.divisors, ∏ p ∈ a.primeFactors, f p
      = ∑ i ∈ m.divisors, (ArithmeticFunction.prodPrimeFactors f) i := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [ArithmeticFunction.prodPrimeFactors_apply (Nat.pos_of_mem_divisors ha).ne']
  rw [goalRHS, ← key]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.prodPrimeFactors_apply hp0,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hp0, Nat.cast_one,
    (Nat.prime_of_mem_primeFactors hp).primeFactors, Finset.prod_singleton]

/-- Rewrite the DIVPROD RHS as a sum over `divisors` of the multiplicative `f` value. -/
lemma sum_divisors_eq_prod_primeFactors {f : ℕ → ℝ} {m : ℕ} (hm : Squarefree m) :
    ∑ a ∈ m.divisors, ∏ p ∈ a.primeFactors, f p = ∏ p ∈ m.primeFactors, (f p + 1) :=
  (sum_divisors_prod_primeFactors hm).symm

/-- Per-prime: `(g(p))⁻¹ + 1 = p/h(p)` for `p ≥ 2` (`g = h/(p−h)`). -/
lemma inv_selG_add_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ}
    (hp : 2 ≤ p) : (selG χ p)⁻¹ + 1 = (p : ℝ) / selH χ p := by
  have hpos := selH_pos χ hsq hp
  rw [selG, inv_div, div_add_one hpos.ne']
  congr 1
  ring

/-- **`ν`-inversion.** For squarefree `m ≥ 1`, `ν(m)⁻¹ = Σ_{l∣m} g(l)⁻¹` (`ν(m) = h(m)/m`, the
Selberg Möbius inversion of the local factors, via DIVPROD at `f = g⁻¹`). -/
lemma selNu_inv_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (_hm1 : 1 ≤ m) (hm : Squarefree m) :
    (selNu χ m)⁻¹ = ∑ l ∈ m.divisors, (selGmul χ l)⁻¹ := by
  have hstep : ∑ l ∈ m.divisors, (selGmul χ l)⁻¹
      = ∑ l ∈ m.divisors, ∏ p ∈ l.primeFactors, (selG χ p)⁻¹ := by
    apply Finset.sum_congr rfl
    intro l _
    rw [selGmul, Finset.prod_inv_distrib]
  rw [hstep, sum_divisors_eq_prod_primeFactors hm]
  -- ∏_{p∣m} ((g p)⁻¹ + 1) = ∏_{p∣m} p/h(p) = m/h(m) = ν(m)⁻¹
  have hprod : ∏ p ∈ m.primeFactors, ((selG χ p)⁻¹ + 1)
      = ∏ p ∈ m.primeFactors, ((p : ℝ) / selH χ p) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact inv_selG_add_one χ hsq (Nat.prime_of_mem_primeFactors hp).two_le
  rw [hprod, Finset.prod_div_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm]
  rw [selNu, selHmul, inv_div]

/-! ## §3 — the coprime inner sum, the `ν·selWeight` cancellation, and the collapse -/

/-- **The coprime inner sum** `G_d = Σ_{r ≤ z/d, (r,d)=1, sf} g(r)` (the `selWeight` inner sum). -/
def selCopSum {q : ℕ} (χ : DirichletCharacter ℂ q) (z d : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 (z / d)).filter (fun r => Squarefree r ∧ Nat.Coprime r d), selGmul χ r

/-- **The diagonal factor** `y_l = Σ_{l ∣ d ≤ z, sf} ν(d)·θ_d`. -/
def selY {q : ℕ} (χ : DirichletCharacter ℂ q) (z l : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, if l ∣ d then selNu χ d * selWeight χ z d else 0

/-- `selGmul` is multiplicative across coprime factors. -/
lemma selGmul_mul_of_coprime {q : ℕ} (χ : DirichletCharacter ℂ q) {a b : ℕ}
    (hab : Nat.Coprime a b) : selGmul χ (a * b) = selGmul χ a * selGmul χ b := by
  rw [selGmul, selGmul, selGmul, Nat.Coprime.primeFactors_mul hab,
    Finset.prod_union hab.disjoint_primeFactors]

/-- `g(e)·g(n/e) = g(n)` for `e ∣ n`, `n` squarefree. -/
lemma selGmul_mul_div {q : ℕ} (χ : DirichletCharacter ℂ q) {n e : ℕ} (hn : Squarefree n)
    (he : e ∣ n) : selGmul χ e * selGmul χ (n / e) = selGmul χ n := by
  have hcop : Nat.Coprime e (n / e) :=
    Nat.coprime_of_squarefree_mul (by rwa [Nat.mul_div_cancel' he])
  rw [← selGmul_mul_of_coprime χ hcop, Nat.mul_div_cancel' he]

/-- **The `ν·θ` cancellation** (the corrected def telescopes): for `d ≤ z` squarefree,
`ν(d)·θ_d = μ(d)·g(d)·G_d/H` — the `h(d)/d · d/h(d)` factor collapses. -/
lemma selNu_mul_selWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z d : ℕ}
    (hd1 : 1 ≤ d) (hdz : d ≤ z) (hdsf : Squarefree d) :
    selNu χ d * selWeight χ z d
      = (moebius d : ℝ) * selGmul χ d * selCopSum χ z d / selHSum χ z := by
  have hz1 : 1 ≤ z := le_trans hd1 hdz
  have hHmul : selHmul χ d ≠ 0 := (selHmul_pos χ hsq d).ne'
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hH : selHSum χ z ≠ 0 := (selHSum_pos χ hsq hz1).ne'
  rw [selWeight, if_pos ⟨hdz, hdsf⟩, selNu, selCopSum]
  field_simp

/-- `Σ_{i ∣ k} μ(i) = [k = 1]` (Möbius over divisors; `μ ⋆ ζ = 1`). -/
lemma sum_moebius_divisors (k : ℕ) :
    ∑ i ∈ k.divisors, (moebius i : ℝ) = if k = 1 then (1 : ℝ) else 0 := by
  have h : ((moebius * ζ : ArithmeticFunction ℝ)) k = ∑ i ∈ k.divisors, (moebius i : ℝ) := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    exact Finset.sum_congr rfl (fun i _ => ArithmeticFunction.intCoe_apply)
  rw [← h, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- `Σ_{l ∣ e ∣ n} μ(e) = [n = l]·μ(l)` for squarefree `n`, `l ∣ n` (reindex `e = l·e'`). -/
lemma sum_moebius_filter_dvd {n l : ℕ} (hn : Squarefree n) (hln : l ∣ n) :
    ∑ e ∈ n.divisors.filter (fun e => l ∣ e), (moebius e : ℝ)
      = if n = l then (moebius l : ℝ) else 0 := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hl0 : l ≠ 0 := fun h => hn0 (by subst h; exact Nat.eq_zero_of_zero_dvd hln)
  have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
  have hcopLD : Nat.Coprime l (n / l) :=
    Nat.coprime_of_squarefree_mul (by rwa [Nat.mul_div_cancel' hln])
  have hreindex : ∑ e ∈ n.divisors.filter (fun e => l ∣ e), (moebius e : ℝ)
      = ∑ e' ∈ (n / l).divisors, (moebius (l * e') : ℝ) := by
    refine Finset.sum_nbij' (fun e => e / l) (fun e' => l * e') ?_ ?_ ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_filter, Nat.mem_divisors] at he
      obtain ⟨⟨hedvd, _⟩, hle⟩ := he
      rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      · rw [← Nat.mul_dvd_mul_iff_left hlpos, Nat.mul_div_cancel' hle, Nat.mul_div_cancel' hln]
        exact hedvd
      · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hln) hlpos).ne'
    · intro e' he'
      rw [Nat.mem_divisors] at he'
      obtain ⟨he'dvd, _⟩ := he'
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, hn0⟩, Dvd.intro e' rfl⟩
      calc l * e' ∣ l * (n / l) := Nat.mul_dvd_mul_left l he'dvd
        _ = n := Nat.mul_div_cancel' hln
    · intro e he
      rw [Finset.mem_filter, Nat.mem_divisors] at he
      exact Nat.mul_div_cancel' he.2
    · intro e' _
      exact Nat.mul_div_cancel_left e' hlpos
    · intro e he
      rw [Finset.mem_filter, Nat.mem_divisors] at he
      rw [Nat.mul_div_cancel' he.2]
  rw [hreindex]
  have hcong : ∀ e' ∈ (n / l).divisors,
      (moebius (l * e') : ℝ) = (moebius l : ℝ) * (moebius e' : ℝ) := by
    intro e' he'
    have hcop : Nat.Coprime l e' :=
      hcopLD.coprime_dvd_right (Nat.dvd_of_mem_divisors he')
    rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime isMultiplicative_moebius hcop]
    push_cast; ring
  rw [Finset.sum_congr rfl hcong, ← Finset.mul_sum, sum_moebius_divisors]
  by_cases h : n = l
  · subst h; rw [Nat.div_self hlpos]; simp
  · have hne1 : n / l ≠ 1 := by
      intro hq; exact h (by rw [← Nat.mul_div_cancel' hln, hq, mul_one])
    rw [if_neg hne1, if_neg h, mul_zero]

/-- **The core collapse** (the crux reindex `(d,r) ↦ (n = d·r, d)`): for squarefree `l ≤ z`,
`Σ_{l ∣ d ≤ z, sf} μ(d)·g(d)·G_d = μ(l)·g(l)`. Numerically certified off `l = 1` (catch #163). -/
lemma selCore_collapse {q : ℕ} (χ : DirichletCharacter ℂ q) {z l : ℕ}
    (hl1 : 1 ≤ l) (hlz : l ≤ z) (hlsf : Squarefree l) :
    ∑ d ∈ ((Finset.Icc 1 z).filter Squarefree).filter (fun d => l ∣ d),
        (moebius d : ℝ) * selGmul χ d * selCopSum χ z d
      = (moebius l : ℝ) * selGmul χ l := by
  set A := ((Finset.Icc 1 z).filter Squarefree).filter (fun d => l ∣ d) with hAdef
  set B := fun d => (Finset.Icc 1 (z / d)).filter (fun r => Squarefree r ∧ Nat.Coprime r d)
    with hBdef
  set E := fun (n : ℕ) => n.divisors.filter (fun e => l ∣ e) with hEdef
  have hlA : l ∈ A := by
    rw [hAdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨hl1, hlz⟩, hlsf⟩, dvd_refl l⟩
  -- distribute + flatten the LHS to a sigma sum
  have step1 : ∑ d ∈ A, (moebius d : ℝ) * selGmul χ d * selCopSum χ z d
      = ∑ p ∈ A.sigma B, (moebius p.1 : ℝ) * selGmul χ p.1 * selGmul χ p.2 := by
    have hd : ∀ d ∈ A, (moebius d : ℝ) * selGmul χ d * selCopSum χ z d
        = ∑ r ∈ B d, (moebius d : ℝ) * selGmul χ d * selGmul χ r := by
      intro d _; rw [selCopSum, Finset.mul_sum]
    rw [Finset.sum_congr rfl hd, Finset.sum_sigma']
  rw [step1]
  -- reindex to A.sigma E
  have step2 : ∑ p ∈ A.sigma B, (moebius p.1 : ℝ) * selGmul χ p.1 * selGmul χ p.2
      = ∑ p ∈ A.sigma E, (moebius p.2 : ℝ) * selGmul χ p.2 * selGmul χ (p.1 / p.2) := by
    refine Finset.sum_nbij' (fun p => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ))
      (fun p => (⟨p.2, p.1 / p.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
    · -- hi
      intro p hp
      simp only [Finset.mem_sigma, hAdef, hBdef, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨⟨hd1, hdz⟩, hdsf⟩, hld⟩, ⟨hr1, hrz⟩, hrsf, hrcop⟩ := hp
      have hd0 : 0 < p.1 := hd1
      have hprodz : p.1 * p.2 ≤ z := by
        rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd0).mp hrz
      have hprodsf : Squarefree (p.1 * p.2) := (Nat.squarefree_mul hrcop.symm).mpr ⟨hdsf, hrsf⟩
      have hpos : 0 < p.1 * p.2 := Nat.mul_pos hd0 hr1
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · simp only [hAdef, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨⟨hpos, hprodz⟩, hprodsf⟩, hld.trans (dvd_mul_right p.1 p.2)⟩
      · simp only [hEdef, Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨dvd_mul_right p.1 p.2, hpos.ne'⟩, hld⟩
    · -- hj
      intro p hp
      simp only [Finset.mem_sigma, hAdef, hEdef, Finset.mem_filter, Finset.mem_Icc,
        Nat.mem_divisors] at hp
      obtain ⟨⟨⟨⟨hn1, hnz⟩, hnsf⟩, hln⟩, ⟨hedvd, hn0⟩, hle⟩ := hp
      have hepos : 0 < p.2 := Nat.pos_of_dvd_of_pos hedvd (by omega)
      have hqpos : 0 < p.1 / p.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hedvd) hepos
      have hcop : Nat.Coprime (p.1 / p.2) p.2 :=
        (Nat.coprime_of_squarefree_mul (by rw [Nat.mul_div_cancel' hedvd]; exact hnsf)).symm
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · simp only [hAdef, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨⟨hepos, le_trans (Nat.le_of_dvd (by omega) hedvd) hnz⟩,
          Squarefree.squarefree_of_dvd hedvd hnsf⟩, hle⟩
      · simp only [hBdef, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hqpos, Nat.div_le_div_right hnz⟩,
          Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hedvd) hnsf, hcop⟩
    · -- left_inv
      intro p hp
      simp only [Finset.mem_sigma, hAdef, hBdef, Finset.mem_filter, Finset.mem_Icc] at hp
      have hd0 : 0 < p.1 := hp.1.1.1.1
      simp only [Nat.mul_div_cancel_left _ hd0]
    · -- right_inv
      intro p hp
      simp only [Finset.mem_sigma, hEdef, Finset.mem_filter, Nat.mem_divisors] at hp
      have hedvd : p.2 ∣ p.1 := hp.2.1.1
      simp only [Nat.mul_div_cancel' hedvd]
    · -- summand
      intro p hp
      simp only [Finset.mem_sigma, hAdef, Finset.mem_filter, Finset.mem_Icc] at hp
      have hd0 : 0 < p.1 := hp.1.1.1.1
      simp only [Nat.mul_div_cancel_left _ hd0]
  rw [step2, Finset.sum_sigma]
  -- inner: pull g(n) out, apply moebius
  have step3 : ∀ n ∈ A, ∑ e ∈ E n, (moebius e : ℝ) * selGmul χ e * selGmul χ (n / e)
      = selGmul χ n * (if n = l then (moebius l : ℝ) else 0) := by
    intro n hn
    rw [hAdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨_, _⟩, hnsf⟩, hln⟩ := hn
    have hterm : ∀ e ∈ E n, (moebius e : ℝ) * selGmul χ e * selGmul χ (n / e)
        = selGmul χ n * (moebius e : ℝ) := by
      intro e he
      rw [hEdef, Finset.mem_filter, Nat.mem_divisors] at he
      have hg := selGmul_mul_div χ hnsf he.1.1
      rw [mul_assoc, hg, mul_comm]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    exact sum_moebius_filter_dvd hnsf hln
  rw [Finset.sum_congr rfl step3]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' A l (fun n => selGmul χ n * (moebius l : ℝ)), if_pos hlA]
  ring

/-! ## §4 — the diagonalization and `selberg_opt_eq` -/

/-- **The DH main-term quadratic form** `V(θ) = Σ_{d,e ≤ z, sf} θ_d θ_e · ν(lcm(d,e))`
(the R6/R7-consumer ν(lcm) form; the flags' `V(w) = Σ w_d w_e ν([d,e])`). -/
def selMainTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, ∑ e ∈ (Finset.Icc 1 z).filter Squarefree,
    selWeight χ z d * selWeight χ z e * selNu χ (Nat.lcm d e)

/-- **The diagonal factor collapses.** `y_l = μ(l)·g(l)/H` for squarefree `l ≤ z` (the `ν·θ`
cancellation + the core reindex). -/
lemma selY_collapse {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z l : ℕ}
    (hl1 : 1 ≤ l) (hlz : l ≤ z) (hlsf : Squarefree l) :
    selY χ z l = (moebius l : ℝ) * selGmul χ l / selHSum χ z := by
  rw [selY, ← Finset.sum_filter]
  have hcong : ∑ d ∈ ((Finset.Icc 1 z).filter Squarefree).filter (fun d => l ∣ d),
        selNu χ d * selWeight χ z d
      = ∑ d ∈ ((Finset.Icc 1 z).filter Squarefree).filter (fun d => l ∣ d),
        (moebius d : ℝ) * selGmul χ d * selCopSum χ z d / selHSum χ z := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    exact selNu_mul_selWeight χ hsq hd.1.1.1 hd.1.1.2 hd.1.2
  rw [hcong, ← Finset.sum_div, selCore_collapse χ hl1 hlz hlsf]

/-- **The Selberg diagonalization** (hand-rolled on the squarefree support ≤ `z`):
`V(θ) = Σ_{l ≤ z, sf} g(l)⁻¹·y_l²` via `ν(lcm) = ν_d ν_e ν(gcd)⁻¹` and the ν-inversion. -/
lemma selMainTerm_diag {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} :
    selMainTerm χ z
      = ∑ g ∈ (Finset.Icc 1 z).filter Squarefree, (selGmul χ g)⁻¹ * (selY χ z g) ^ 2 := by
  set S := (Finset.Icc 1 z).filter Squarefree with hSdef
  have hterm : ∀ d ∈ S, ∀ e ∈ S,
      selWeight χ z d * selWeight χ z e * selNu χ (Nat.lcm d e)
        = ∑ g ∈ S, (if g ∣ d then selNu χ d * selWeight χ z d else 0)
            * (if g ∣ e then selNu χ e * selWeight χ z e else 0) * (selGmul χ g)⁻¹ := by
    intro d hd e he
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hd he
    obtain ⟨⟨hd1, hdz⟩, hdsf⟩ := hd
    obtain ⟨⟨he1, hez⟩, hesf⟩ := he
    have hg1 : 1 ≤ Nat.gcd d e := Nat.gcd_pos_of_pos_left e (by omega)
    have hgsf : Squarefree (Nat.gcd d e) := hdsf.squarefree_of_dvd (Nat.gcd_dvd_left d e)
    have hBsum : ∑ g ∈ S, (if g ∣ d ∧ g ∣ e then (selGmul χ g)⁻¹ else 0)
        = ∑ g ∈ (Nat.gcd d e).divisors, (selGmul χ g)⁻¹ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext g
      simp only [hSdef, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨⟨_, _⟩, _⟩, hgd, hge⟩
        exact ⟨⟨hgd, hge⟩, (Nat.gcd_pos_of_pos_left e (by omega)).ne'⟩
      · rintro ⟨⟨hgd, hge⟩, _⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hgd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hgd) hdz⟩, hdsf.squarefree_of_dvd hgd⟩, hgd, hge⟩
    have hstep : ∀ g ∈ S, (if g ∣ d then selNu χ d * selWeight χ z d else 0)
          * (if g ∣ e then selNu χ e * selWeight χ z e else 0) * (selGmul χ g)⁻¹
        = (selNu χ d * selWeight χ z d) * (selNu χ e * selWeight χ z e)
            * (if g ∣ d ∧ g ∣ e then (selGmul χ g)⁻¹ else 0) := by
      intro g _
      rw [ite_zero_mul_ite_zero]
      split_ifs with h <;> ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hBsum, ← selNu_inv_eq χ hsq hg1 hgsf,
      selNu_lcm_split χ hsq hd1 he1]
    ring
  calc selMainTerm χ z
      = ∑ d ∈ S, ∑ e ∈ S, ∑ g ∈ S,
          (if g ∣ d then selNu χ d * selWeight χ z d else 0)
            * (if g ∣ e then selNu χ e * selWeight χ z e else 0) * (selGmul χ g)⁻¹ := by
        rw [selMainTerm]
        exact Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))
    _ = ∑ d ∈ S, ∑ g ∈ S, ∑ e ∈ S,
          (if g ∣ d then selNu χ d * selWeight χ z d else 0)
            * (if g ∣ e then selNu χ e * selWeight χ z e else 0) * (selGmul χ g)⁻¹ :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ = ∑ g ∈ S, ∑ d ∈ S, ∑ e ∈ S,
          (if g ∣ d then selNu χ d * selWeight χ z d else 0)
            * (if g ∣ e then selNu χ e * selWeight χ z e else 0) * (selGmul χ g)⁻¹ :=
        Finset.sum_comm
    _ = ∑ g ∈ S, (selGmul χ g)⁻¹ * (selY χ z g) ^ 2 := by
        apply Finset.sum_congr rfl
        intro g _
        rw [selY, sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring

/-- **`selberg_opt_eq` (R4).** The Selberg-optimal weight makes the DH main term exactly `1/H(z)`:
`V(selWeight) = Σ_{d,e ≤ z, sf} θ_d θ_e ν(lcm(d,e)) = 1/H(z)`. The corrected `selWeight` telescopes
(`y_l = μ(l)g(l)/H`), so `V = Σ_l g(l)/H² = H/H² = 1/H`. Numerically certified to `~1e-16`. -/
theorem selberg_opt_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 1 ≤ z) : selMainTerm χ z = 1 / selHSum χ z := by
  rw [selMainTerm_diag χ hsq]
  have hH : selHSum χ z ≠ 0 := (selHSum_pos χ hsq hz).ne'
  have key : ∑ g ∈ (Finset.Icc 1 z).filter Squarefree, (selGmul χ g)⁻¹ * (selY χ z g) ^ 2
      = ∑ g ∈ (Finset.Icc 1 z).filter Squarefree, selGmul χ g / (selHSum χ z) ^ 2 := by
    apply Finset.sum_congr rfl
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_Icc] at hg
    obtain ⟨⟨hg1, hgz⟩, hgsf⟩ := hg
    have hgpos : 0 < selGmul χ g := selGmul_pos χ hsq g
    have hmu : (moebius g : ℝ) ^ 2 = 1 := by
      rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or).mp
          ((ArithmeticFunction.moebius_ne_zero_iff_squarefree).mpr hgsf) with h | h <;>
        rw [h] <;> norm_num
    rw [selY_collapse χ hsq hg1 hgz hgsf, div_pow, mul_pow, hmu, one_mul, pow_two (selGmul χ g),
      ← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hgpos.ne', one_mul]
  rw [key, ← Finset.sum_div,
    show (∑ g ∈ (Finset.Icc 1 z).filter Squarefree, selGmul χ g) = selHSum χ z from rfl,
    pow_two, ← div_div, div_self hH]

/-! ## §5 — `selweight_abs_le_one` via the partial-`H` bound -/

/-- **The local factor as a divisor sum.** For squarefree `d ≥ 1`,
`(d/h(d))·g(d) = ∏_{p∣d}(1+g(p)) = Σ_{a∣d} g(a)` (the `d`-part / coprime-part regrouping). -/
lemma selWeight_local_eq_prod {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {d : ℕ}
    (_hd1 : 1 ≤ d) (hdsf : Squarefree d) :
    (d : ℝ) / selHmul χ d * selGmul χ d = ∏ p ∈ d.primeFactors, (selG χ p + 1) := by
  have hd : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hdsf]
  rw [selHmul, selGmul, hd, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos := selH_pos χ hsq hpp
  have hlt := selH_lt_of_prime χ hsq hpp
  have hden : (p : ℝ) - selH χ p ≠ 0 := by linarith
  rw [selG]
  field_simp
  ring

/-- **The partial-`H` bound** (the classical `|λ_d| ≤ 1` core): `(Σ_{a∣d} g(a))·G_d ≤ H(z)`, via the
injection `(a,b) ↦ a·b` of the `d`-part × coprime-part factorization into the squarefree support. -/
lemma partial_H_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z d : ℕ}
    (hd1 : 1 ≤ d) (_hdz : d ≤ z) (hdsf : Squarefree d) :
    (∑ a ∈ d.divisors, selGmul χ a) * selCopSum χ z d ≤ selHSum χ z := by
  set B := (Finset.Icc 1 (z / d)).filter (fun r => Squarefree r ∧ Nat.Coprime r d) with hBdef
  have hd0 : 0 < d := by omega
  have hinj : ∀ x ∈ d.divisors ×ˢ B, ∀ y ∈ d.divisors ×ˢ B,
      x.1 * x.2 = y.1 * y.2 → x = y := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.mem_product, Nat.mem_divisors, hBdef, Finset.mem_filter, Finset.mem_Icc]
      at hab hab'
    obtain ⟨⟨had, _⟩, _, _, hbd⟩ := hab
    obtain ⟨⟨ha'd, _⟩, _, _, hb'd⟩ := hab'
    have hab' : Nat.Coprime a b' := Nat.Coprime.coprime_dvd_left had hb'd.symm
    have ha'b : Nat.Coprime a' b := Nat.Coprime.coprime_dvd_left ha'd hbd.symm
    have h1 : a ∣ a' := hab'.dvd_of_dvd_mul_right ⟨b, heq.symm⟩
    have h2 : a' ∣ a := ha'b.dvd_of_dvd_mul_right ⟨b', heq⟩
    have haa' : a = a' := Nat.dvd_antisymm h1 h2
    have hbb' : b = b' := by
      have := heq; rw [haa'] at this
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_dvd_of_pos ha'd hd0) this
    exact Prod.ext haa' hbb'
  have himg : (d.divisors ×ˢ B).image (fun p => p.1 * p.2)
      ⊆ (Finset.Icc 1 z).filter Squarefree := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_product, Nat.mem_divisors, hBdef, Finset.mem_filter,
      Finset.mem_Icc] at hn
    obtain ⟨⟨a, b⟩, ⟨⟨had, _⟩, ⟨hb1, hbz⟩, hbsf, hbd⟩, rfl⟩ := hn
    have hasf : Squarefree a := hdsf.squarefree_of_dvd had
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos had hd0
    have haz : a ≤ d := Nat.le_of_dvd hd0 had
    have hcop : Nat.Coprime a b := Nat.Coprime.coprime_dvd_left had hbd.symm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos hapos hb1, ?_⟩, (Nat.squarefree_mul hcop).mpr ⟨hasf, hbsf⟩⟩
    calc a * b ≤ d * b := by gcongr
      _ ≤ z := by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd0).mp hbz
  rw [selCopSum, ← hBdef, Finset.sum_mul_sum]
  calc ∑ a ∈ d.divisors, ∑ b ∈ B, selGmul χ a * selGmul χ b
      = ∑ a ∈ d.divisors, ∑ b ∈ B, selGmul χ (a * b) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        rw [hBdef, Finset.mem_filter] at hb
        exact (selGmul_mul_of_coprime χ
          (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors ha) hb.2.2.symm)).symm
    _ = ∑ p ∈ d.divisors ×ˢ B, selGmul χ (p.1 * p.2) := by rw [← Finset.sum_product']
    _ = ∑ n ∈ (d.divisors ×ˢ B).image (fun p => p.1 * p.2), selGmul χ n :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ (Finset.Icc 1 z).filter Squarefree, selGmul χ n :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun n _ _ => (selGmul_pos χ hsq n).le)
    _ = selHSum χ z := rfl

/-- **`selweight_abs_le_one` (R4).** `|θ_d| ≤ 1` — the classical Halberstam–Richert Selberg-weight
bound, via `|μ(d)| ≤ 1` and the partial-`H` monotonicity `(d/h(d))·g(d)·G_d ≤ H(z)`.
Numerically `max_d|θ_d| = 1` at `d = 1`. -/
theorem selweight_abs_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z d : ℕ} :
    |selWeight χ z d| ≤ 1 := by
  by_cases hcond : d ≤ z ∧ Squarefree d
  · obtain ⟨hdz, hdsf⟩ := hcond
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hdsf.ne_zero
    have hz1 : 1 ≤ z := le_trans hd1 hdz
    have hH : 0 < selHSum χ z := selHSum_pos χ hsq hz1
    have hHmul : 0 < selHmul χ d := selHmul_pos χ hsq d
    have hGmul : 0 < selGmul χ d := selGmul_pos χ hsq d
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hcop_nonneg : 0 ≤ selCopSum χ z d :=
      Finset.sum_nonneg (fun b _ => (selGmul_pos χ hsq b).le)
    have hmu_le : |(moebius d : ℝ)| ≤ 1 := by
      rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or).mp
          ((ArithmeticFunction.moebius_ne_zero_iff_squarefree).mpr hdsf) with h | h <;>
        rw [h] <;> norm_num
    have hlocal : (d : ℝ) / selHmul χ d * selGmul χ d = ∑ a ∈ d.divisors, selGmul χ a := by
      have h2 : ∑ a ∈ d.divisors, selGmul χ a = ∏ p ∈ d.primeFactors, (selG χ p + 1) := by
        simp only [selGmul]
        exact (sum_divisors_prod_primeFactors hdsf).symm
      rw [selWeight_local_eq_prod χ hsq hd1 hdsf]; exact h2.symm
    have hX : (d : ℝ) / selHmul χ d * selGmul χ d / selHSum χ z * selCopSum χ z d ≤ 1 := by
      rw [hlocal, div_mul_eq_mul_div, div_le_one hH]
      exact partial_H_bound χ hsq hd1 hdz hdsf
    have hXnn : 0 ≤ (d : ℝ) / selHmul χ d * selGmul χ d / selHSum χ z * selCopSum χ z d := by
      positivity
    rw [selWeight, if_pos ⟨hdz, hdsf⟩]
    show |(moebius d : ℝ) * ((d : ℝ) / selHmul χ d) * selGmul χ d / selHSum χ z
        * selCopSum χ z d| ≤ 1
    rw [show (moebius d : ℝ) * ((d : ℝ) / selHmul χ d) * selGmul χ d / selHSum χ z * selCopSum χ z d
        = (moebius d : ℝ)
            * ((d : ℝ) / selHmul χ d * selGmul χ d / selHSum χ z * selCopSum χ z d) by ring,
      abs_mul, abs_of_nonneg hXnn]
    calc |(moebius d : ℝ)|
          * ((d : ℝ) / selHmul χ d * selGmul χ d / selHSum χ z * selCopSum χ z d)
        ≤ 1 * ((d : ℝ) / selHmul χ d * selGmul χ d / selHSum χ z * selCopSum χ z d) :=
          mul_le_mul_of_nonneg_right hmu_le hXnn
      _ = (d : ℝ) / selHmul χ d * selGmul χ d / selHSum χ z * selCopSum χ z d := one_mul _
      _ ≤ 1 := hX
  · rw [selWeight, if_neg hcond, abs_zero]; exact zero_le_one

end Salt.SW

end
