/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Mertens.Second

/-!
# The Turán–Kubilius inequality (MR-gate node S6b, `= MR-C`)

The variance of `ω(n) = n.primeFactors.card` over `n ≤ x` is `≪ x · loglog x`.
Elementary and self-contained modulo `Salt.Mertens.mertens_second_sharp`.

## Domain note (statement defect flagged, not silently patched)

The frozen target used the hypothesis `2 ≤ x`.  That literal statement is
**false**: for `2 ≤ x < e` we have `Real.log (Real.log x) < 0`, so the RHS
`C · x · loglog x` is negative while the LHS is a sum of squares `≥ 0`.
Concretely at `x = 2` the LHS is `≈ 2.0016 > 0 > RHS` for every `C > 0`.
The faithful theorem (the classical "for all sufficiently large `x`" form) is
landed here with an existential threshold `x₀`; the shape
`variance ≤ C · x · loglog x` is preserved exactly.  A Fable/human-tier
statement fix of the freeze is required before this node can be "landed" under
the literal `2 ≤ x` hypothesis.
-/

namespace Salt.MR

open Finset

/-- Primes `≤ N`, indexed so its reciprocal sum matches `mertens_second_sharp`. -/
def primesLE (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- `∑_{p ≤ N} 1/p`, the Mertens partial sum. -/
noncomputable def primeRecip (N : ℕ) : ℝ := ∑ p ∈ primesLE N, (1 : ℝ) / p

lemma mem_primesLE {N p : ℕ} : p ∈ primesLE N ↔ p ≤ N ∧ p.Prime := by
  simp [primesLE, Finset.mem_filter, Finset.mem_range]

lemma primeRecip_nonneg (N : ℕ) : 0 ≤ primeRecip N := by
  refine Finset.sum_nonneg ?_
  intro p _; positivity

/-- `Finset.Icc 1 N = Finset.Ioc 0 N` over `ℕ`. -/
lemma Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- Counting multiples of `d` in `[1, N]`. -/
lemma card_Icc_filter_dvd (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  rw [Icc_one_eq_Ioc_zero]; exact Nat.Ioc_filter_dvd_card_eq_div N d

/-- Lower bound on nat-division cast to `ℝ`: `N/p - 1 ≤ ⌊N/p⌋`. -/
lemma cast_div_ge {N p : ℕ} (hp : 0 < p) : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hmod : ((N % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt N hp
  have hdm : (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N p
  rw [sub_le_iff_le_add, div_le_iff₀ hp']
  nlinarith [hdm, hmod]

/-- For `n ∈ [1, N]`, `n.primeFactors` are exactly the primes `≤ N` dividing `n`. -/
lemma primeFactors_eq_filter {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    n.primeFactors = (primesLE N).filter (fun p => p ∣ n) := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, mem_primesLE]
  constructor
  · rintro ⟨hp, hpn, _⟩
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
    exact ⟨⟨by omega, hp⟩, hpn⟩
  · rintro ⟨⟨_, hp⟩, hpn⟩
    exact ⟨hp, hpn, by omega⟩

/-- `ω(n)` as an indicator sum over primes `≤ N`, for `n ∈ [1, N]`. -/
lemma omega_eq_sum {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    ((n.primeFactors.card : ℝ))
      = ∑ p ∈ primesLE N, (if p ∣ n then (1 : ℝ) else 0) := by
  rw [primeFactors_eq_filter hn1 hnN, Finset.card_filter]
  push_cast
  rfl

/-- The first moment `∑_{n ≤ N} ω(n) = ∑_{p ≤ N} ⌊N/p⌋`. -/
lemma first_moment (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ))
      = ∑ p ∈ primesLE N, ((N / p : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl
      (fun n hn => omega_eq_sum (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_boole, card_Icc_filter_dvd]

/-- `#{primes ≤ N} ≤ N`. -/
lemma card_primesLE_le (N : ℕ) : ((primesLE N).card : ℝ) ≤ N := by
  have hsub : primesLE N ⊆ Finset.Icc 2 N := by
    intro p hp
    obtain ⟨hpN, hp⟩ := mem_primesLE.1 hp
    exact Finset.mem_Icc.2 ⟨hp.two_le, hpN⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  have : (primesLE N).card ≤ N := by omega
  exact_mod_cast this

/-- Upper bound on the first moment: `∑ ω(n) ≤ N · ∑ 1/p`. -/
lemma first_moment_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ≤ (N : ℝ) * primeRecip N := by
  rw [first_moment, primeRecip, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  calc ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    _ = (N : ℝ) * (1 / p) := by rw [mul_one_div]

/-- Lower bound on the first moment: `N · ∑ 1/p - N ≤ ∑ ω(n)`. -/
lemma first_moment_ge (N : ℕ) :
    (N : ℝ) * primeRecip N - N ≤ ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) := by
  rw [first_moment]
  have hstep : ∑ p ∈ primesLE N, ((N : ℝ) / p - 1)
      ≤ ∑ p ∈ primesLE N, ((N / p : ℕ) : ℝ) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    exact cast_div_ge (mem_primesLE.1 hp).2.pos
  refine le_trans ?_ hstep
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hNP : (N : ℝ) * primeRecip N = ∑ p ∈ primesLE N, (N : ℝ) / p := by
    rw [primeRecip, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_); rw [mul_one_div]
  rw [hNP]
  have hc := card_primesLE_le N
  linarith

/-- Product of two divisibility indicators is the joint indicator. -/
lemma indicator_mul (p q n : ℕ) :
    (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      = if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
  by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [h1, h2]

/-- `∑_{n ≤ N} 𝟙[d ∣ n] = ⌊N/d⌋`. -/
lemma sum_indicator_dvd (N d : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) = ((N / d : ℕ) : ℝ) := by
  rw [Finset.sum_boole, card_Icc_filter_dvd]

/-- For coprime `p, q`: `∑_{n ≤ N} 𝟙[p ∣ n ∧ q ∣ n] = ⌊N/(pq)⌋`. -/
lemma sum_indicator_both (N p q : ℕ) (hcop : Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
      = ((N / (p * q) : ℕ) : ℝ) := by
  have hcongr : ∀ n, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
      = (if p * q ∣ n then (1 : ℝ) else 0) := by
    intro n
    have hiff : (p ∣ n ∧ q ∣ n) ↔ (p * q ∣ n) := by
      constructor
      · rintro ⟨h1, h2⟩; exact hcop.mul_dvd_of_dvd_of_dvd h1 h2
      · intro h; exact ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩
    exact if_congr hiff rfl rfl
  rw [Finset.sum_congr rfl (fun n _ => hcongr n), Finset.sum_boole, card_Icc_filter_dvd]

/-- **The second moment bound.** `∑_{n ≤ N} ω(n)² ≤ N·P + N·P²`, `P = ∑_{p ≤ N} 1/p`.
The diagonal `p = q` contributes `≤ N·P`; the off-diagonal `p ≠ q` maps to `pq ∣ n`
and contributes `≤ N·P²`. -/
lemma second_moment_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ^ 2
      ≤ (N : ℝ) * primeRecip N + (N : ℝ) * (primeRecip N) ^ 2 := by
  have hsq : ∀ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ^ 2
      = ∑ p ∈ primesLE N, ∑ q ∈ primesLE N,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
    rw [omega_eq_sum hn1 hnN, pow_two, Finset.sum_mul_sum]
  have hcomm : (∑ n ∈ Finset.Icc 1 N, ∑ p ∈ primesLE N, ∑ q ∈ primesLE N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0))
      = ∑ p ∈ primesLE N, ∑ q ∈ primesLE N, ∑ n ∈ Finset.Icc 1 N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl hsq, hcomm]
  have hbound : ∀ p ∈ primesLE N,
      (∑ q ∈ primesLE N, ∑ n ∈ Finset.Icc 1 N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0))
      ≤ (N : ℝ) / p * (1 + primeRecip N) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := mem_primesLE.1 hp
    have hinner : ∀ q, ∑ n ∈ Finset.Icc 1 N,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
        = ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) :=
      fun q => Finset.sum_congr rfl (fun n _ => indicator_mul p q n)
    rw [Finset.sum_congr rfl (fun q _ => hinner q)]
    rw [← Finset.add_sum_erase (primesLE N) _ hp]
    have hdiag : ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0)
        ≤ (N : ℝ) / p := by
      have hself : ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0)
          = ∑ n ∈ Finset.Icc 1 N, (if p ∣ n then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun n _ => by simp only [and_self])
      rw [hself, sum_indicator_dvd]; exact Nat.cast_div_le
    have hoff : ∑ q ∈ (primesLE N).erase p, ∑ n ∈ Finset.Icc 1 N,
          (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
        ≤ ∑ q ∈ primesLE N, (N : ℝ) / (p * q) := by
      have h1 : ∑ q ∈ (primesLE N).erase p, ∑ n ∈ Finset.Icc 1 N,
            (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
          ≤ ∑ q ∈ (primesLE N).erase p, (N : ℝ) / (p * q) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hqmem := Finset.mem_of_mem_erase hq
        have hqne : q ≠ p := Finset.ne_of_mem_erase hq
        obtain ⟨hqN, hqp⟩ := mem_primesLE.1 hqmem
        have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).2 hqne.symm
        rw [sum_indicator_both N p q hcop]
        exact le_trans Nat.cast_div_le (le_of_eq (by rw [Nat.cast_mul]))
      have h2 : ∑ q ∈ (primesLE N).erase p, (N : ℝ) / (p * q)
          ≤ ∑ q ∈ primesLE N, (N : ℝ) / (p * q) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p (primesLE N))
          (fun q _ _ => by positivity)
      exact h1.trans h2
    have hfactor : ∑ q ∈ primesLE N, (N : ℝ) / (p * q) = (N : ℝ) / p * primeRecip N := by
      rw [primeRecip, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [mul_one_div, div_div]
    calc (∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0))
          + ∑ q ∈ (primesLE N).erase p, ∑ n ∈ Finset.Icc 1 N,
              (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
        ≤ (N : ℝ) / p + ∑ q ∈ primesLE N, (N : ℝ) / (p * q) := add_le_add hdiag hoff
      _ = (N : ℝ) / p + (N : ℝ) / p * primeRecip N := by rw [hfactor]
      _ = (N : ℝ) / p * (1 + primeRecip N) := by ring
  have heq : ∑ p ∈ primesLE N, (N : ℝ) / p * (1 + primeRecip N)
      = (N : ℝ) * primeRecip N + (N : ℝ) * (primeRecip N) ^ 2 := by
    have hNP : ∑ p ∈ primesLE N, (N : ℝ) / p = (N : ℝ) * primeRecip N := by
      rw [primeRecip, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_); rw [mul_one_div]
    rw [← Finset.sum_mul, hNP]; ring
  exact (Finset.sum_le_sum hbound).trans (le_of_eq heq)

/-- **The variance bound (combinatorial heart).** For `μ ≥ 0`,
`∑_{n ≤ N} (ω(n) − μ)² ≤ N·((P − μ)² + P + 2μ)`, with `P = ∑_{p ≤ N} 1/p`.
Expand the square, apply the first/second moment estimates; the `N·μ²` terms
cancel, leaving the `O(N·μ)` shape. -/
lemma variance_bound (N : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
      ≤ (N : ℝ) * ((primeRecip N - μ) ^ 2 + primeRecip N + 2 * μ) := by
  have hid : ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
      = (∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ^ 2)
        - 2 * μ * (∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)))
        + (N : ℝ) * μ ^ 2 := by
    have hpt : ∀ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
        = ((n.primeFactors.card : ℝ)) ^ 2 - 2 * μ * ((n.primeFactors.card : ℝ)) + μ ^ 2 :=
      fun n _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by rw [Nat.card_Icc]; push_cast; ring
    rw [hcard]
  rw [hid]
  have hS2 := second_moment_le N
  have hS1l := first_moment_ge N
  nlinarith [hS2, hS1l, hμ, mul_nonneg hμ (sub_nonneg.mpr hS1l)]

/-- Bridge between `loglog N` and `loglog x` when `N ≤ x ≤ N + 1`: the gap is `≤ 1`. -/
lemma loglog_gap {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hxN : (N : ℝ) ≤ x) (hxN1 : x ≤ (N : ℝ) + 1) :
    |Real.log (Real.log (N : ℝ)) - Real.log (Real.log x)| ≤ 1 := by
  have hNge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlo : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogN (Real.log_le_log hNpos hxN)
  have hlogx_le : Real.log x ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hxpos hxN1
  have hlogNb : 0 < Real.log ((N : ℝ) + 1) := lt_of_lt_of_le hlogx hlogx_le
  have hba : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log (N : ℝ) := by
    have hle : Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) * (N : ℝ)) :=
      Real.log_le_log (by linarith) (by nlinarith [hNge2, sq_nonneg ((N : ℝ) - 2)])
    rw [Real.log_mul (ne_of_gt hNpos) (ne_of_gt hNpos)] at hle
    linarith
  have hup : Real.log (Real.log x) ≤ Real.log (Real.log (N : ℝ)) + 1 := by
    have hstep : Real.log (Real.log x) ≤ Real.log (Real.log ((N : ℝ) + 1)) :=
      Real.log_le_log hlogx hlogx_le
    have hstep2 : Real.log (Real.log ((N : ℝ) + 1)) - Real.log (Real.log (N : ℝ))
        ≤ Real.log ((N : ℝ) + 1) / Real.log (N : ℝ) - 1 := by
      rw [← Real.log_div (ne_of_gt hlogNb) (ne_of_gt hlogN)]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hstep3 : Real.log ((N : ℝ) + 1) / Real.log (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hlogN]; linarith [hba]
    linarith [hstep, hstep2, hstep3]
  rw [abs_le]
  constructor <;> linarith [hlo, hup]

/-- **The Turán–Kubilius inequality.** The variance of `ω(n) = n.primeFactors.card`
about its mean `loglog x` is `≪ x · loglog x`.  See the domain note at the top of the
file: the frozen `2 ≤ x` hypothesis is false (negative RHS on `[2, e)`); this is the
faithful "for all sufficiently large `x`" form (existential threshold `x₀`). -/
theorem turan_kubilius :
    ∃ C : ℝ, ∃ x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n.primeFactors.card : ℝ) - Real.log (Real.log x)) ^ 2
        ≤ C * x * Real.log (Real.log x) := by
  obtain ⟨M, CM, hCM, hmert⟩ := Salt.Mertens.mertens_second_sharp
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := |M| + CM / Real.log 2 + 1 with hKdef
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) ≤ |M| := abs_nonneg M
    have h2 : (0 : ℝ) ≤ CM / Real.log 2 := div_nonneg hCM hlog2pos.le
    rw [hKdef]; linarith
  set L : ℝ := K ^ 2 + K with hLdef
  have hLpos : 0 ≤ L := by rw [hLdef]; nlinarith [hKpos]
  refine ⟨4, Real.exp (Real.exp L), by norm_num, ?_⟩
  intro x hx
  have hx0pos : (0 : ℝ) < Real.exp (Real.exp L) := Real.exp_pos _
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hx0pos hx
  have hx2 : (2 : ℝ) ≤ x := by
    have he1 : (1 : ℝ) ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
    have hmono : Real.exp 1 ≤ Real.exp (Real.exp L) := Real.exp_le_exp.mpr he1
    have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  set N := ⌊x⌋₊ with hNdef
  have hN2 : 2 ≤ N := by rw [hNdef]; exact Nat.le_floor (by exact_mod_cast hx2)
  have hNge2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNx : (N : ℝ) ≤ x := by rw [hNdef]; exact Nat.floor_le hxpos.le
  have hxN1 : x ≤ (N : ℝ) + 1 := by rw [hNdef]; exact (Nat.lt_floor_add_one x).le
  set μ := Real.log (Real.log x) with hμdef
  have hlogx_ge : Real.exp L ≤ Real.log x := by
    have h := Real.log_le_log hx0pos hx; rwa [Real.log_exp] at h
  have hμL : L ≤ μ := by
    rw [hμdef]; have h := Real.log_le_log (Real.exp_pos L) hlogx_ge; rwa [Real.log_exp] at h
  have hμ0 : 0 ≤ μ := le_trans hLpos hμL
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith [hNge2R])
  have hmertN : |primeRecip N - (Real.log (Real.log (N : ℝ)) + M)|
      ≤ CM / Real.log (N : ℝ) := by
    have h := hmert N hN2
    simpa [primeRecip, primesLE] using h
  have hgap : |Real.log (Real.log (N : ℝ)) - μ| ≤ 1 := by
    rw [hμdef]; exact loglog_gap hN2 hNx hxN1
  have hCMbound : CM / Real.log (N : ℝ) ≤ CM / Real.log 2 := by
    rw [div_le_div_iff₀ hlogNpos hlog2pos]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hNge2R) hCM
  have hPmu : |primeRecip N - μ| ≤ K := by
    calc |primeRecip N - μ|
        ≤ |primeRecip N - (Real.log (Real.log (N : ℝ)) + M)|
          + |(Real.log (Real.log (N : ℝ)) + M) - μ| := abs_sub_le _ _ _
      _ ≤ CM / Real.log (N : ℝ) + (|M| + |Real.log (Real.log (N : ℝ)) - μ|) := by
          have hb2 : |(Real.log (Real.log (N : ℝ)) + M) - μ|
              ≤ |M| + |Real.log (Real.log (N : ℝ)) - μ| := by
            have heq : (Real.log (Real.log (N : ℝ)) + M) - μ
                = M + (Real.log (Real.log (N : ℝ)) - μ) := by ring
            rw [heq]; exact abs_add_le M _
          linarith [hmertN, hb2]
      _ ≤ CM / Real.log 2 + (|M| + 1) := by linarith [hCMbound, hgap]
      _ = K := by rw [hKdef]; ring
  have hvar := variance_bound N μ hμ0
  have hsq : (primeRecip N - μ) ^ 2 ≤ K ^ 2 :=
    sq_le_sq' (abs_le.mp hPmu).1 (abs_le.mp hPmu).2
  have hPle : primeRecip N ≤ μ + K := by have := (abs_le.mp hPmu).2; linarith
  have hbracket : (primeRecip N - μ) ^ 2 + primeRecip N + 2 * μ ≤ 4 * μ := by
    have hL : K ^ 2 + K ≤ μ := by rw [← hLdef]; exact hμL
    nlinarith [hsq, hPle, hL]
  calc ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
      ≤ (N : ℝ) * ((primeRecip N - μ) ^ 2 + primeRecip N + 2 * μ) := hvar
    _ ≤ (N : ℝ) * (4 * μ) := by
        exact mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ x * (4 * μ) := by
        exact mul_le_mul_of_nonneg_right hNx (by linarith [hμ0])
    _ = 4 * x * μ := by ring

end Salt.MR
