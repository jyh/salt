/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.RosserChain
import Salt.Chen.Tail
import Salt.BrunLower.Defs
import Salt.BrunLower.LowerMoebius
import Salt.BrunLower.Pointwise

/-!
# C1c — The two-sided explicit linear sieve (BJS Theorem 6)

The two-sided Rosser–Iwaniec linear sieve of Bordignon, Johnston, Starichkova
(*An explicit version of Chen's theorem and the linear sieve*, arXiv:2207.09452v6,
**BJS**), Theorem 6 — to our knowledge the first Rosser–Iwaniec linear sieve
formalisation.  Keystone 1 of the `chen` rung.

## BJS Theorem 6 (verbatim, dossier Item 1)

For an arithmetic weight `A = {a(n)}`, a set of primes `ℙ`, `P(z) = ∏_{p<z} p`,
sifted sum `S(A,ℙ,z)`, densities `gₙ` with `0 ≤ gₙ(p) < 1`, remainders
`r(d) = |A_d| − Σ a(n) gₙ(d)`, and hypothesis (4) (a windowed Mertens bound with
constant `1+ε`, `0 < ε ≤ 1/74`, primes in `ℙ∖ℚ`), BJS prove:

* (5) upper, for `D ≥ z`:  `S(A,ℙ,z) < (F(s) + εC₁(ε)e²h(s)) X_A + R`,
* (6) lower, for `D ≥ z²`:  `S(A,ℙ,z) > (f(s) − εC₂(ε)e²h(s)) X_A − R`,

where `s = log D/log z`, `X_A = |A|∏_{p|P(z)}(1−gₙ(p)) = V(z)|A|`,
`R = Σ_{d|P(z), d<QD} |r(d)|`, `F,f` the linear-sieve functions (the truncated
Rosser chains `Fchain`/`fchain` of C1a), `h(s)` piecewise `e⁻²/e⁻ˢ/3s⁻¹e⁻ˢ`, and
`C₁(ε),C₂(ε)` from Table 1 (at `ε = 1/10000`: `C₁ = 106, C₂ = 108`).

## The BJS proof skeleton (arXiv:2207.09452v6, §2.1–2.4)

The proof is the Nathanson/Rosser combinatorial-chain induction:

1. **Rosser weights `λ±`** (Nathanson Thm 9.3): a parity-signed truncation of `μ`
   supported on the ordered prime factorisations `d = p₁ > ⋯ > pᵣ < z` satisfying
   the Rosser condition `pₘ < yₘ := (D/(p₁⋯pₘ))^{1/2}` at positions `m ≡ ν (mod 2)`
   (`ν = 1` upper, `ν = 2` lower).  These are `IsUpperMoebius`/`IsLowerMoebius`.
2. **Buchstab decomposition** (Nathanson Lemma 9.3):
   `G(z,λ±) := Σ_{d|P(z)} λ±(d) g(d) = V(z) ± Σ_n Tₙ(D,z)`, where
   `Tₙ(D,z) = Σ_{yₙ≤pₙ<⋯<p₁<z, pₘ<yₘ (m≡n mod2)} g(p₁⋯pₙ) V(pₙ)` is the `n`-th
   iterated Buchstab remainder.
3. **The `Tₙ` bound** (BJS Lemma 11, the analytic heart): by induction on the chain
   depth `n`, using the `fₙ`/`h`/`H` bounds (C1a/C1b) and hypothesis (4) (which
   enters as `V(u)/V(z) ≤ K log z/log u`, `1 < K < 1+ε`),
   `Tₙ(D,z) < V(z)(fₙ(s) + ετₙe²h(s))` with `τₙ` the BJS constants (31).
4. **Proposition 13**: summing (2) over odd/even `n` and applying (3),
   `G(z,λ+) < V(z)(F(s) + εe²h(s) Σ τ_{2n−1})` and dually for the lower side.
   Lemmas 12/14 bound `Σ τ_{2n−1} =: C₁(ε)`, `Σ τ_{2n} =: C₂(ε)` (Table 1).
5. **Assembly** (Thm 6 = Nathanson Thm 9.7): `S ≤ Σ_d λ+(d)|A_d|`, split
   `|A_d| = Σ a gₙ(d) + r(d)`; the main term is `X_A·G(z,λ+)/V(z)` and the
   remainder is `Σ λ+(d) r(d)`, `|λ+| ≤ 1`, supported on `d < QD` — giving (5)/(10).
   The `d < QD` support and the `D ≥ z` (upper) / `D ≥ z²` (lower) asymmetry come
   from the Rosser condition (a length-`r` chain has product `< D`; the smallest
   prime is `< z` from `d|P(z)`, forcing the level split).

## What this file lands (floor B)

* **Part I (FULL)** — the generic parity-signed truncation-sieve engine
  (`TruncSieve`): from the three H-R/Rosser structural rules (`one_mem`,
  `dvd_closed`, `add_prime`), the truncated Möbius weight `μ·[P]` is
  `IsUpperMoebius` (`ν=1`) / `IsLowerMoebius` (`ν=2`).  This is layer (2) — the
  pointwise ± inequalities / Buchstab telescoping — proved once, abstractly, by
  the single-peel-of-the-smallest-prime argument (generalising the B2 block-Brun
  machinery of `Salt/BrunLower/Pointwise.lean`, whose helper lemmas transfer
  verbatim).
* **Part II (FULL)** — the Rosser truncation predicate `rosserCond` (layer (1)):
  a genuine divisor-closed positional predicate on ordered prime factorisations,
  with divisor-closure, the parity closure rule, and the level/support bound
  `rosserCond → d < D`-shape.  Instantiated into a `TruncSieve`, feeding Part I
  to give the Rosser weights' `IsUpperMoebius`/`IsLowerMoebius`.  Plus the block
  witness `blockTruncSieve` (from B2's `chi`) confirming the engine end-to-end.
* **Part III (FULL)** — the Theorem-6 assembly `linear_sieve_upper` /
  `linear_sieve_lower` over `BoundingSieve`: from a `TruncSieve`, the Rosser
  support bound, `0 ≤ totalMass`, and the **main-term comparison as a hypothesis**
  (BJS Proposition 13 / Lemma 11 — layer (3), parameterised per floor B), the
  target sifted-sum bounds with the `R = Σ_{d<QD}|rem d|` remainder, via mathlib's
  `siftedSum_le_mainSum_errSum_of_upperMoebius` and node B1's lower dual.
* **Part IV** — the BJS (5)/(6)-shaped corollaries `linear_sieve_upper_chain` /
  `linear_sieve_lower_chain` packaging the main term as
  `W s · (Fchain/fchain N s ± εCᵢe²h(s))` with `ε, Cᵢ` as parameters (the frozen
  instance `ε = 1/10000, C₁ = 106, C₂ = 108` is a numeric specialisation).

**FLAG (floor B, honest).** The main-term comparison (layer (3), BJS Prop 13 /
Lemma 11 — the `Tₙ` chain induction that couples the analytic `fₙ`/`h`/`H` bounds
to the prime sums through hypothesis (4)) is a **named hypothesis** here, not
discharged.  Discharging it is the remaining analytic heart of C1c (a follow-up:
the Buchstab decomposition (2) + the `τₙ` bookkeeping (3)/(4)).  Everything else —
the full Rosser combinatorics (layers 1+2) and the assembly (5) — is proved.
-/

open Finset Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

namespace Salt.Chen

/-! ## Part I — the generic parity-signed truncation sieve

An abstract predicate `P : ℕ → Prop` with the three BJS/H-R structural rules
(2.1)/(2.2)/(2.3): `P 1`, divisor closure, and the parity closure rule.  The
Möbius weight `μ·[P]` is then upper (`ν=1`) or lower (`ν=2`) Möbius.  The proof is
the single-peel-of-the-smallest-prime telescoping, generalised from the B2
block-Brun machinery (`Salt.BrunLower.peel_term_nonneg` etc.). -/

/-- A **parity-signed truncation sieve** (BJS/H-R (2.1)–(2.3) genus): a divisor-closed
predicate `P` on `ℕ` with a parity closure rule keyed to `side = ν ∈ {1,2}`.  Instances:
the Rosser predicate (`rosserSieve`, Part II) and the H-R block predicate
(`blockTruncSieve`). -/
structure TruncSieve where
  /-- The truncation predicate `[P]` (a `{0,1}` indicator via `μ·[P]`). -/
  P : ℕ → Prop
  /-- `P` is decidable (used as a `{0,1}` indicator). -/
  decP : DecidablePred P
  /-- The parity `ν ∈ {1,2}`: `1` = upper (`λ⁺`), `2` = lower (`λ⁻`). -/
  side : ℕ
  /-- `side ∈ {1,2}`. -/
  hside : side = 1 ∨ side = 2
  /-- **(2.1)** `P 1`. -/
  one_mem : P 1
  /-- **(2.2)** divisor closure: `P d → t ∣ d → P t`. -/
  dvd_closed : ∀ ⦃d t : ℕ⦄, d ≠ 0 → t ∣ d → P d → P t
  /-- **(2.3)** parity closure: prepending a prime smaller than every prime factor of `t`,
  when `Ω(t) ≡ ν (mod 2)`, preserves `P`. -/
  add_prime : ∀ ⦃p t : ℕ⦄, p.Prime → t ≠ 0 → (∀ q ∈ t.primeFactors, p < q) →
      t.primeFactors.card % 2 = side % 2 → P t → P (p * t)

attribute [instance] TruncSieve.decP

/-- The truncated Möbius weight `λ_ν(d) = μ(d)·[P(d)]` (the Rosser weights when `P`
is `rosserCond`). -/
noncomputable def TruncSieve.lam (S : TruncSieve) (d : ℕ) : ℝ :=
  (μ d : ℝ) * (if S.P d then 1 else 0)

lemma TruncSieve.lam_eq_zero_of_not (S : TruncSieve) {d : ℕ} (h : ¬ S.P d) :
    S.lam d = 0 := by
  simp [TruncSieve.lam, if_neg h]

/-- `|λ_ν(d)| ≤ 1` (the Rosser weights are `μ`-truncations). -/
lemma TruncSieve.abs_lam_le_one (S : TruncSieve) (d : ℕ) : |S.lam d| ≤ 1 := by
  rw [TruncSieve.lam, abs_mul]
  have hμ : |(μ d : ℝ)| ≤ 1 := by
    have : ((|μ d| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast abs_moebius_le_one
    rwa [Int.cast_abs, Int.cast_one] at this
  have hite : |(if S.P d then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> norm_num
  calc |(μ d : ℝ)| * |(if S.P d then (1 : ℝ) else 0)|
      ≤ 1 * 1 := mul_le_mul hμ hite (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The generic peel-term nonnegativity (BJS/H-R Lemma 1, sign form): for a prime `p`
below every prime factor of a squarefree `t`, the Möbius-weighted boundary bracket
`μ(t)([P(t)]−[P(pt)])` carries the single sign `(−1)^{ν−1}`.  Generalises
`Salt.BrunLower.peel_term_nonneg`. -/
lemma TruncSieve.peel_term_nonneg (S : TruncSieve) {p t : ℕ} (hp : p.Prime)
    (ht : Squarefree t) (hlt : ∀ q ∈ t.primeFactors, p < q) :
    0 ≤ (-1 : ℝ) ^ (S.side - 1) *
        ((μ t : ℝ) * ((if S.P t then (1 : ℝ) else 0)
                      - (if S.P (p * t) then (1 : ℝ) else 0))) := by
  by_cases hC : S.P (p * t)
  · have hpt0 : p * t ≠ 0 := Nat.mul_ne_zero hp.ne_zero ht.ne_zero
    have hA : S.P t := S.dvd_closed hpt0 (dvd_mul_left t p) hC
    rw [if_pos hA, if_pos hC, sub_self, mul_zero, mul_zero]
  · rw [if_neg hC]
    by_cases hA : S.P t
    · rw [if_pos hA, sub_zero]
      have hpar_ne : ¬ (t.primeFactors.card % 2 = S.side % 2) := fun hpar =>
        hC (S.add_prime hp ht.ne_zero hlt hpar hA)
      have hmu : (μ t : ℝ) = (-1 : ℝ) ^ t.primeFactors.card :=
        Salt.BrunLower.moebius_real_of_squarefree ht
      have hsign : (μ t : ℝ) = (-1 : ℝ) ^ (S.side - 1) := by
        rcases S.hside with hs | hs
        · rw [hs] at hpar_ne ⊢
          rw [hmu, (Nat.even_iff.mpr (by omega : t.primeFactors.card % 2 = 0)).neg_one_pow]
          norm_num
        · rw [hs] at hpar_ne ⊢
          rw [hmu, (Nat.odd_iff.mpr (by omega : t.primeFactors.card % 2 = 1)).neg_one_pow]
          norm_num
      rw [hsign, mul_one]
      exact mul_self_nonneg _
    · rw [if_neg hA, sub_self, mul_zero, mul_zero]

/-- The core of the pointwise ± inequality: for squarefree `n ≠ 1`, the alternating
Möbius sum against `[P]`, times `(−1)^{ν−1}`, is nonnegative.  Generalises
`Salt.BrunLower.neg_one_pow_mul_sum_moebius_chi_nonneg`. -/
lemma TruncSieve.sum_nonneg (S : TruncSieve) {n : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1) :
    0 ≤ (-1 : ℝ) ^ (S.side - 1) *
        ∑ d ∈ n.divisors, (μ d : ℝ) * (if S.P d then (1 : ℝ) else 0) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  set p := n.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime hn1
  have hpn : p ∣ n := Nat.minFac_dvd n
  set m := n / p with hm_def
  have hn_eq : p * m = n := Nat.mul_div_cancel' hpn
  have hm0 : m ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hn_eq; exact hn0 hn_eq.symm
  have hpm : ¬ p ∣ m := by
    intro hd
    have hpp : p * p ∣ n := by rw [← hn_eq]; exact mul_dvd_mul_left p hd
    exact hp.ne_one (Nat.isUnit_iff.mp (hn p hpp))
  have hmdvd : m ∣ n := ⟨p, by rw [← hn_eq]; ring⟩
  have hmsf : Squarefree m := Squarefree.squarefree_of_dvd hmdvd hn
  have hlt : ∀ q ∈ m.primeFactors, p < q := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    have hle : p ≤ q := Nat.minFac_le_of_dvd hqp.two_le (hqm.trans hmdvd)
    have hne : q ≠ p := by rintro rfl; exact hpm hqm
    omega
  have hsplit : ∑ d ∈ n.divisors, (μ d : ℝ) * (if S.P d then (1 : ℝ) else 0)
      = ∑ t ∈ m.divisors, (μ t : ℝ) *
          ((if S.P t then (1 : ℝ) else 0)
            - (if S.P (p * t) then (1 : ℝ) else 0)) := by
    rw [← hn_eq,
      Salt.BrunLower.sum_over_divisors_prime_mul hp hpm hm0
        (fun d => (μ d : ℝ) * (if S.P d then (1 : ℝ) else 0)),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have htm : t ∣ m := Nat.dvd_of_mem_divisors ht
    have hpt : ¬ p ∣ t := fun h => hpm (h.trans htm)
    have hcop : Nat.Coprime p t := (hp.coprime_iff_not_dvd).mpr hpt
    have hmuZ : μ (p * t) = - μ t := by
      rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]; ring
    have hmu : (μ (p * t) : ℝ) = -(μ t : ℝ) := by rw [hmuZ]; push_cast; ring
    rw [hmu]; ring
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_nonneg
  intro t ht
  have htm : t ∣ m := Nat.dvd_of_mem_divisors ht
  have htsf : Squarefree t := Squarefree.squarefree_of_dvd htm hmsf
  have hltt : ∀ q ∈ t.primeFactors, p < q :=
    fun q hq => hlt q (Nat.primeFactors_mono htm hm0 hq)
  exact S.peel_term_nonneg hp htsf hltt

/-- The Möbius-`[P]` sum over `n.divisors` collapses to the sum over the radical's
divisors (`μ` kills non-squarefree divisors).  Generalises
`Salt.BrunLower.sum_moebius_chi_eq_over_radical`. -/
lemma sum_moebius_ite_eq_over_radical (P : ℕ → Prop) [DecidablePred P] {n : ℕ} (hn0 : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : ℝ) * (if P d then (1 : ℝ) else 0)
      = ∑ d ∈ (∏ p ∈ n.primeFactors, p).divisors,
          (μ d : ℝ) * (if P d then (1 : ℝ) else 0) := by
  have hrad_dvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hrad_ne0 : (∏ p ∈ n.primeFactors, p) ≠ 0 :=
    (Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)).ne'
  refine (Finset.sum_subset (Nat.divisors_subset_of_dvd hn0 hrad_dvd) ?_).symm
  intro d hd hdr
  rcases eq_or_ne (μ d) 0 with hmu | hmu
  · simp [hmu]
  · exfalso
    have hsqf : Squarefree d := moebius_ne_zero_iff_squarefree.mp hmu
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hddvd : d ∣ ∏ p ∈ n.primeFactors, p := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsqf]
      exact Finset.prod_dvd_prod_of_subset _ _ (fun p => p) (Nat.primeFactors_mono hdn hn0)
    exact hdr (Nat.mem_divisors.mpr ⟨hddvd, hrad_ne0⟩)

/-- **Part I upper endpoint** (BJS/H-R (2.5), `ν = 1`): the Rosser weight `μ·[P]` of an
upper (`side = 1`) truncation sieve is `IsUpperMoebius`. -/
theorem TruncSieve.isUpperMoebius (S : TruncSieve) (hs1 : S.side = 1) :
    IsUpperMoebius S.lam := by
  intro n
  change (if n = 1 then (1 : ℝ) else 0)
      ≤ ∑ d ∈ n.divisors, (μ d : ℝ) * (if S.P d then (1 : ℝ) else 0)
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp only [Nat.divisors_one, Finset.sum_singleton]
    rw [if_pos S.one_mem, moebius_apply_one]; norm_num
  · rw [if_neg hn1, sum_moebius_ite_eq_over_radical S.P hn0]
    have h := S.sum_nonneg (Salt.BrunLower.squarefree_prod_primeFactors n)
      (Salt.BrunLower.prod_primeFactors_ne_one hn0 hn1)
    rw [hs1] at h
    simpa using h

/-- **Part I lower endpoint** (BJS/H-R (2.5), `ν = 2`): the Rosser weight `μ·[P]` of a
lower (`side = 2`) truncation sieve is `IsLowerMoebius` (node B1). -/
theorem TruncSieve.isLowerMoebius (S : TruncSieve) (hs2 : S.side = 2) :
    Salt.BrunLower.IsLowerMoebius S.lam := by
  intro n
  change ∑ d ∈ n.divisors, (μ d : ℝ) * (if S.P d then (1 : ℝ) else 0)
      ≤ (if n = 1 then (1 : ℝ) else 0)
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp only [Nat.divisors_one, Finset.sum_singleton]
    rw [if_pos S.one_mem, moebius_apply_one]; norm_num
  · rw [if_neg hn1, sum_moebius_ite_eq_over_radical S.P hn0]
    have h := S.sum_nonneg (Salt.BrunLower.squarefree_prod_primeFactors n)
      (Salt.BrunLower.prod_primeFactors_ne_one hn0 hn1)
    rw [hs2] at h
    have hpow : (-1 : ℝ) ^ (2 - 1) = -1 := by norm_num
    rw [hpow] at h
    linarith

/-! ## Part III — the Theorem-6 assembly over `BoundingSieve`

Given a `TruncSieve` (the Rosser weights, layers 1+2), the Rosser support bound
`P d → d < QD`, `0 ≤ totalMass`, and the **main-term comparison** (BJS Prop 13 /
Lemma 11) as a hypothesis, the mathlib sifted-sum plumbing yields BJS (5)/(6). -/

/-- The Rosser remainder `R = Σ_{d | P(z), d < bound} |r(d)|` (BJS (10), `bound = QD`). -/
noncomputable def rosserRemainder (s : BoundingSieve) (bound : ℝ) : ℝ :=
  ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) < bound then |s.rem d| else 0

/-- The truncation-sieve error sum is bounded by the Rosser remainder: since `|λ| ≤ 1`
and `λ` is supported on the Rosser set `{d : P d}` which lies below `bound = QD`,
`errSum λ = Σ |λ(d)||r(d)| ≤ Σ_{d<QD} |r(d)| = R`. -/
lemma errSum_lam_le (S : TruncSieve) (s : BoundingSieve) {bound : ℝ}
    (hsupp : ∀ d, S.P d → (d : ℝ) < bound) :
    s.errSum S.lam ≤ rosserRemainder s bound := by
  rw [errSum]
  unfold rosserRemainder
  apply Finset.sum_le_sum
  intro d _
  by_cases hP : S.P d
  · rw [if_pos (hsupp d hP)]
    calc |S.lam d| * |s.rem d|
        ≤ 1 * |s.rem d| := mul_le_mul_of_nonneg_right (S.abs_lam_le_one d) (abs_nonneg _)
      _ = |s.rem d| := one_mul _
  · rw [S.lam_eq_zero_of_not hP, abs_zero, zero_mul]
    split_ifs <;> positivity

/-- **Linear sieve, upper bound** (BJS Theorem 6, (5)).  From an upper (`side = 1`)
truncation sieve `S`, the Rosser support bound (`P d → d < bound = QD`),
`0 ≤ totalMass`, and the **main-term comparison** `mainSum λ⁺ ≤ mainBound` (BJS
Proposition 13 / Lemma 11, parameterised),
`siftedSum ≤ totalMass · mainBound + R`. -/
theorem linear_sieve_upper (s : BoundingSieve) (S : TruncSieve) (hside : S.side = 1)
    {bound mainBound : ℝ}
    (hsupp : ∀ d, S.P d → (d : ℝ) < bound)
    (htm : 0 ≤ s.totalMass)
    (hmain : s.mainSum S.lam ≤ mainBound) :
    s.siftedSum ≤ s.totalMass * mainBound + rosserRemainder s bound := by
  have hU := siftedSum_le_mainSum_errSum_of_upperMoebius S.lam (S.isUpperMoebius hside) (s := s)
  have hmul : s.totalMass * s.mainSum S.lam ≤ s.totalMass * mainBound :=
    mul_le_mul_of_nonneg_left hmain htm
  have herr := errSum_lam_le S s hsupp
  linarith [hU, hmul, herr]

/-- **Linear sieve, lower bound** (BJS Theorem 6, (6)).  From a lower (`side = 2`)
truncation sieve `S`, the Rosser support bound, `0 ≤ totalMass`, and the main-term
comparison `mainBound ≤ mainSum λ⁻`,
`totalMass · mainBound − R ≤ siftedSum`. -/
theorem linear_sieve_lower (s : BoundingSieve) (S : TruncSieve) (hside : S.side = 2)
    {bound mainBound : ℝ}
    (hsupp : ∀ d, S.P d → (d : ℝ) < bound)
    (htm : 0 ≤ s.totalMass)
    (hmain : mainBound ≤ s.mainSum S.lam) :
    s.totalMass * mainBound - rosserRemainder s bound ≤ s.siftedSum := by
  have hL := Salt.BrunLower.siftedSum_ge_mainSum_errSum_of_lowerMoebius S.lam
    (S.isLowerMoebius hside) (s := s)
  have hmul : s.totalMass * mainBound ≤ s.totalMass * s.mainSum S.lam :=
    mul_le_mul_of_nonneg_left hmain htm
  have herr := errSum_lam_le S s hsupp
  linarith [hL, hmul, herr]

/-! ## Part IV — the BJS (5)/(6)-shaped exports

Packaging the main term as `W s · (Fchain/fchain N s ± εCᵢe²h(s))` (`W s = V(z)`,
`Fchain/fchain` the truncated Rosser chains of C1a), with `ε, Cᵢ` as parameters
(the frozen row is `ε = 1/10000, C₁ = 106, C₂ = 108`). -/

/-- BJS's `h(s)` (7): `e⁻²` on `[1,2]`, `e⁻ˢ` on `[2,3]`, `3s⁻¹e⁻ˢ` on `[3,∞)`
(documentation of the slack shape; never a Lean statement of `F`/`f`). -/
noncomputable def hBJS (s : ℝ) : ℝ :=
  if s ≤ 2 then Real.exp (-2)
  else if s ≤ 3 then Real.exp (-s)
  else 3 * s⁻¹ * Real.exp (-s)

/-- **BJS Theorem 6 (5)**, chain form.  With `mainBound = W s·(Fchain N s + εC₁e²h(s))`
the main-term comparison (BJS Prop 13) gives the explicit upper linear sieve. -/
theorem linear_sieve_upper_chain (s : BoundingSieve) (S : TruncSieve) (hside : S.side = 1)
    {bound : ℝ} (hsupp : ∀ d, S.P d → (d : ℝ) < bound) (htm : 0 ≤ s.totalMass)
    (N : ℕ) (sparam ε C₁ : ℝ)
    (hmain : s.mainSum S.lam
      ≤ Salt.BrunLower.W s * (Fchain N sparam + ε * C₁ * Real.exp 2 * hBJS sparam)) :
    s.siftedSum
      ≤ s.totalMass * (Salt.BrunLower.W s * (Fchain N sparam + ε * C₁ * Real.exp 2 * hBJS sparam))
        + rosserRemainder s bound :=
  linear_sieve_upper s S hside hsupp htm hmain

/-- **BJS Theorem 6 (6)**, chain form.  With `mainBound = W s·(fchain N s − εC₂e²h(s))`
the main-term comparison (BJS Prop 13) gives the explicit lower linear sieve. -/
theorem linear_sieve_lower_chain (s : BoundingSieve) (S : TruncSieve) (hside : S.side = 2)
    {bound : ℝ} (hsupp : ∀ d, S.P d → (d : ℝ) < bound) (htm : 0 ≤ s.totalMass)
    (N : ℕ) (sparam ε C₂ : ℝ)
    (hmain : Salt.BrunLower.W s * (fchain N sparam - ε * C₂ * Real.exp 2 * hBJS sparam)
      ≤ s.mainSum S.lam) :
    s.totalMass * (Salt.BrunLower.W s * (fchain N sparam - ε * C₂ * Real.exp 2 * hBJS sparam))
        - rosserRemainder s bound ≤ s.siftedSum :=
  linear_sieve_lower s S hside hsupp htm hmain

/-! ## Part II (a) — the block-sieve witness

The H-R block predicate `chi` (B0/B2) instantiates `TruncSieve`, confirming the Part I
engine reproduces the B2 `IsUpperMoebius`/`IsLowerMoebius` results end-to-end. -/

/-- The H-R block predicate (`Salt.BrunLower.chi`) as an upper (`ν = 1`) truncation
sieve. -/
noncomputable def blockTruncSieve (Lam z : ℝ) (b : ℕ) (hb : 1 ≤ b) : TruncSieve where
  P := fun d => Salt.BrunLower.chi Lam z 1 b d
  decP := fun d => Salt.BrunLower.instDecidableChi Lam z 1 b d
  side := 1
  hside := Or.inl rfl
  one_mem := Salt.BrunLower.chi_one Lam z hb (by norm_num)
  dvd_closed := @fun _d _t hd htd hchi => Salt.BrunLower.chi_dvd_closed Lam z hd htd hchi
  add_prime := @fun _p _t hp ht hlt hpar hchi =>
    Salt.BrunLower.chi_add_smaller_prime Lam z hp ht hlt hpar hchi

/-! ## Part II (b) — the genuine Rosser truncation predicate (layer 1)

The Rosser–Iwaniec truncation on ordered prime factorisations (Nathanson Thm 9.3):
for squarefree `d = p₁ > p₂ > ⋯ > pᵣ` (the descending list of distinct prime
factors, `rlist d`), require the BJS Rosser condition `(p₁⋯pₘ)·pₘ² < D` — i.e.
`pₘ < yₘ := (D/(p₁⋯pₘ))^{1/2}` — at every position `m` with `m ≡ ν (mod 2)`.

Divisor closure (the crux) holds by the **sorted-sublist positional domination**
`rlist_getElem_le`: `t ∣ d` gives a descending sublist, hence via the order
embedding on indices (`fin_orderEmbedding_le`) the `i`-th largest prime of `t` is
`≤` that of `d`, so `t`'s prefix products and elements are dominated by `d`'s at
each position.  The parity closure holds because prepending a smaller prime lands
it at position `Ω(t)+1`, of parity opposite to `ν` when `Ω(t) ≡ ν`, hence
*unchecked*.  This gives the concrete Rosser weights via Part I. -/

section RosserPredicate
open List

/-- Descending sorted list of the distinct prime factors of `d` (BJS `p₁ > ⋯ > pᵣ`). -/
noncomputable def rlist (d : ℕ) : List ℕ := d.primeFactors.sort (· ≥ ·)

lemma rlist_length (d : ℕ) : (rlist d).length = d.primeFactors.card := Finset.length_sort _
lemma rlist_nodup (d : ℕ) : (rlist d).Nodup := Finset.sort_nodup _ _
lemma rlist_sortedGE (d : ℕ) : (rlist d).SortedGE := (Finset.sortedGT_sort _).sortedGE
lemma rlist_mem {d p : ℕ} : p ∈ rlist d ↔ p ∈ d.primeFactors := Finset.mem_sort _

lemma rlist_sublist {t d : ℕ} (hsub : t.primeFactors ⊆ d.primeFactors) :
    rlist t <+ rlist d := by
  have hsub' : (rlist t) ⊆ (rlist d) := fun p hp => rlist_mem.mpr (hsub (rlist_mem.mp hp))
  exact List.sublist_of_subperm_of_pairwise ((rlist_nodup t).subperm hsub')
    (rlist_sortedGE t).pairwise (rlist_sortedGE d).pairwise

/-- An order embedding `Fin m ↪o Fin n` dominates the identity: `i ≤ f i`. -/
lemma fin_orderEmbedding_le {m n : ℕ} (f : Fin m ↪o Fin n) :
    ∀ (j : ℕ) (hj : j < m), (j : ℕ) ≤ (f ⟨j, hj⟩ : ℕ) := by
  intro j
  induction j with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hj
    have hk : k < m := by omega
    have hlt : ((⟨k, hk⟩ : Fin m)) < ⟨k + 1, hj⟩ := Fin.mk_lt_mk.mpr (by omega)
    have hfl : (f ⟨k, hk⟩ : ℕ) < (f ⟨k + 1, hj⟩ : ℕ) := f.strictMono hlt
    have := ih hk
    omega

/-- **Sorted-sublist positional domination**: the `i`-th largest prime of `t` is `≤` the
`i`-th largest of `d` (`t.primeFactors ⊆ d.primeFactors`). -/
lemma rlist_getElem_le {t d : ℕ} (hsub : t.primeFactors ⊆ d.primeFactors)
    (i : ℕ) (hi : i < (rlist t).length) :
    (rlist t)[i] ≤ (rlist d)[i]'(lt_of_lt_of_le hi ((rlist_sublist hsub).length_le)) := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (rlist_sublist hsub)
  have hival : i ≤ (f ⟨i, hi⟩ : ℕ) := fin_orderEmbedding_le f i hi
  have heq : (rlist t)[i] = (rlist d)[(f ⟨i, hi⟩ : ℕ)] := by
    have h := hf ⟨i, hi⟩; simpa [List.get_eq_getElem] using h
  rw [heq]
  exact (rlist_sortedGE d).getElem_ge_getElem_of_le hival

/-- `getD`-form domination for `j < (rlist t).length` (the divisor-closure workhorse). -/
lemma rlist_getD_le {t d : ℕ} (hsub : t.primeFactors ⊆ d.primeFactors)
    (j : ℕ) (hj : j < (rlist t).length) :
    (rlist t).getD j 1 ≤ (rlist d).getD j 1 := by
  have hjd : j < (rlist d).length := lt_of_lt_of_le hj ((rlist_sublist hsub).length_le)
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hjd]
  exact rlist_getElem_le hsub j hj

/-- Prefix product of the `m` largest prime factors of `d` (BJS `p₁⋯pₘ`). -/
noncomputable def rprefix (d m : ℕ) : ℕ := ∏ j ∈ Finset.range m, (rlist d).getD j 1

/-- The `(i+1)`-th largest prime factor of `d` (BJS `pₘ`, `m = i+1`); `1` past the end. -/
noncomputable def relem (d i : ℕ) : ℕ := (rlist d).getD i 1

/-- **The Rosser truncation predicate** (`side = ν ∈ {1,2}`): at every position `m`
(the `m`-th largest prime factor) with `m ≡ ν (mod 2)`, the BJS Rosser condition
`(p₁⋯pₘ)·pₘ² < D` holds (equivalently `pₘ < yₘ = (D/(p₁⋯pₘ))^{1/2}`).  Upper
(`ν = 1`) checks odd positions; lower (`ν = 2`) checks even positions. -/
def rosserCond (side D d : ℕ) : Prop :=
  ∀ i : ℕ, i < (rlist d).length → (i + 1) % 2 = side % 2 →
    rprefix d (i + 1) * (relem d i) ^ 2 < D

/-- **(2.1)** `rosserCond side D 1` (vacuous: `1` has no prime factors). -/
lemma rosserCond_one (side D : ℕ) : rosserCond side D 1 := by
  intro i hi _
  simp [rlist, Nat.primeFactors_one] at hi

/-- **(2.2) divisor closure**: the Rosser condition is preserved under divisors (via the
positional domination `rlist_getD_le` and `Finset.prod_le_prod'`). -/
lemma rosserCond_dvd_closed {side D d t : ℕ} (hd : d ≠ 0) (htd : t ∣ d)
    (hcond : rosserCond side D d) : rosserCond side D t := by
  have hsub : t.primeFactors ⊆ d.primeFactors := Nat.primeFactors_mono htd hd
  intro i hi hpar
  have hi_d : i < (rlist d).length := lt_of_lt_of_le hi ((rlist_sublist hsub).length_le)
  have hpref : rprefix t (i + 1) ≤ rprefix d (i + 1) := by
    apply Finset.prod_le_prod'
    intro j hj
    rw [Finset.mem_range] at hj
    exact rlist_getD_le hsub j (by omega)
  have helem : relem t i ≤ relem d i := rlist_getD_le hsub i hi
  calc rprefix t (i + 1) * (relem t i) ^ 2
      ≤ rprefix d (i + 1) * (relem d i) ^ 2 :=
        Nat.mul_le_mul hpref (Nat.pow_le_pow_left helem 2)
    _ < D := hcond i hi_d hpar

/-- `rlist (p·t) = rlist t ++ [p]` when `p` is a prime below every prime factor of `t`. -/
lemma rlist_mul_prime {p t : ℕ} (hp : p.Prime) (ht : t ≠ 0)
    (hlt : ∀ q ∈ t.primeFactors, p < q) :
    rlist (p * t) = rlist t ++ [p] := by
  have hpt : p ∉ t.primeFactors := fun h => absurd (hlt p h) (lt_irrefl p)
  have hpf : (p * t).primeFactors = insert p t.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero ht, hp.primeFactors, Finset.insert_eq]
  have hsortedR : (rlist t ++ [p]).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨(rlist_sortedGE t).pairwise, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb; subst hb
    exact le_of_lt (hlt a (rlist_mem.mp ha))
  have hcoe : (↑(rlist (p * t)) : Multiset ℕ) = ↑(rlist t ++ [p]) := by
    rw [← Multiset.coe_add, rlist, rlist, Finset.sort_eq, Finset.sort_eq, hpf,
      Finset.insert_val_of_notMem hpt]
    rw [add_comm, Multiset.coe_singleton, Multiset.singleton_add]
  exact List.Perm.eq_of_sortedGE (rlist_sortedGE (p * t)) hsortedR (Multiset.coe_eq_coe.mp hcoe)

/-- **(2.3) parity closure**: prepending a prime below every prime factor of `t`, when
`Ω(t) ≡ ν (mod 2)`, preserves the Rosser condition (the new prime lands at position
`Ω(t)+1`, of parity opposite to `ν`, hence *unchecked*). -/
lemma rosserCond_add_prime {side D p t : ℕ} (hp : p.Prime) (ht : t ≠ 0)
    (hlt : ∀ q ∈ t.primeFactors, p < q)
    (hpar : t.primeFactors.card % 2 = side % 2)
    (hcond : rosserCond side D t) : rosserCond side D (p * t) := by
  have hlisteq : rlist (p * t) = rlist t ++ [p] := rlist_mul_prime hp ht hlt
  have hlen_t : (rlist t).length = t.primeFactors.card := rlist_length t
  have hlen : (rlist (p * t)).length = (rlist t).length + 1 := by
    rw [hlisteq, List.length_append, List.length_singleton]
  intro i hi hpari
  rw [hlen] at hi
  have hi' : i ≤ (rlist t).length := by omega
  rcases lt_or_eq_of_le hi' with hlt_i | heq_i
  · have hpref : rprefix (p * t) (i + 1) = rprefix t (i + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hlisteq, List.getD_append _ _ _ _ (by omega)]
    have helem : relem (p * t) i = relem t i := by
      rw [relem, relem, hlisteq, List.getD_append _ _ _ _ hlt_i]
    rw [hpref, helem]
    exact hcond i hlt_i hpari
  · exfalso
    rw [heq_i, hlen_t] at hpari
    omega

/-- **The Rosser weights as a `TruncSieve`** (layers 1+2, concrete): the genuine
Rosser–Iwaniec positional truncation, feeding Part I to give the Rosser weights'
`IsUpperMoebius` (`ν = 1`) / `IsLowerMoebius` (`ν = 2`). -/
noncomputable def rosserSieve (side D : ℕ) (hside : side = 1 ∨ side = 2) : TruncSieve where
  P := fun d => rosserCond side D d
  decP := fun _ => Classical.propDecidable _
  side := side
  hside := hside
  one_mem := rosserCond_one side D
  dvd_closed := @fun _d _t hd htd hc => rosserCond_dvd_closed hd htd hc
  add_prime := @fun _p _t hp ht hlt hpar hc => rosserCond_add_prime hp ht hlt hpar hc

/-- The Rosser upper weights are `IsUpperMoebius` (BJS λ⁺, via Part I). -/
theorem rosserSieve_isUpperMoebius (D : ℕ) :
    IsUpperMoebius (rosserSieve 1 D (Or.inl rfl)).lam :=
  (rosserSieve 1 D (Or.inl rfl)).isUpperMoebius rfl

/-- The Rosser lower weights are `IsLowerMoebius` (BJS λ⁻, via Part I). -/
theorem rosserSieve_isLowerMoebius (D : ℕ) :
    Salt.BrunLower.IsLowerMoebius (rosserSieve 2 D (Or.inr rfl)).lam :=
  (rosserSieve 2 D (Or.inr rfl)).isLowerMoebius rfl

end RosserPredicate

end Salt.Chen
