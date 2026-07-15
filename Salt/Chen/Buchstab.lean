/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.LinearSieve

/-!
# C1c′ — The Rosser support bound (`hsupp`) and the linear-sieve plug

This file discharges the **support bound `hsupp`** of the two-sided explicit linear sieve
(BJS Theorem 6, `Salt/Chen/LinearSieve.lean`), and plumbs the Rosser weights into the
sieve endpoints.  It is the completion of keystone 1 of the `chen` rung on the support
side; the analytic **main-term comparison `hmain`** (BJS Proposition 13 / Lemma 11 — the
Buchstab-chain `Tₙ` induction) remains the named hypothesis it already is in
`LinearSieve.lean`, flagged below.

## The Rosser support bound (BJS Theorem 6 assembly / Nathanson Thm 9.7)

The Rosser weights `λ±(d) = μ(d)·[rosserCond ν D d]` are supported on squarefree `d` whose
descending prime factorisation `d = p₁ > ⋯ > pᵣ` satisfies the Rosser check
`(p₁⋯pₘ)·pₘ² < D` at the checked positions `m ≡ ν (mod 2)`.  From this the support bound
`d < D` follows (`support_core`), organised by whether the last prime position `r` is
itself checked (`m = L`) or the check sits at `m = L − 1`:

* **Upper (ν = 1, `rosserCond_upper_lt`)** — position `1` is *always* checked (it is odd), so
  even a single prime `p₁` obeys `p₁³ < D`, giving `p₁ < D`.  Hence `d < D` for **every**
  squarefree `d` with only `2 ≤ D` required — no `d ∣ P(z)` restriction.  This is why the
  upper endpoint needs only `D ≥ z`.
* **Lower (ν = 2, `rosserCond_lower_lt`)** — position `1` is *unchecked* (it is odd, `ν`
  even), so the single-prime case `r = 1` is not bounded by the Rosser condition alone.  It
  is rescued by `d ∣ P(z)` (all prime factors `< z`) together with `z ≤ D` (which
  `D ≥ z²` supplies): `p₁ < z ≤ D`.  This is the honest home of the `D ≥ z` vs `D ≥ z²`
  asymmetry.

## The structural finding on `linear_sieve_lower` (flagged)

`LinearSieve.errSum_lam_le` (hence `linear_sieve_lower`/`_chain`) demands the support bound
`∀ d, S.P d → (d:ℝ) < bound` **unconditionally in `d`**.  For a `side = 2` `TruncSieve`
this is *structurally unsatisfiable*: `one_mem` + `add_prime` with `t = 1` (whose parity
`0` matches `ν = 2`) force `P p` for **every** prime `p`, so `{d : P d}` contains all
primes and admits no finite bound.  The lower support genuinely lives on `d ∣ prodPrimes`
(the summation range of `errSum`).  We therefore provide the corrected divisor-restricted
plumbing `errSum_lam_le_div` / `linear_sieve_lower_div` (using node B1's lower-Möbius dual)
and route the lower endpoint through it.  The upper endpoint plugs into the unmodified
`linear_sieve_upper_chain` directly.
-/

open Finset Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

namespace Salt.Chen

open List

/-! ## Part A — structural facts about `rlist` / `rprefix` / `relem` -/

/-- The full prefix product over all prime positions recovers `d` (squarefree). -/
theorem rprefix_full {d : ℕ} (hd : Squarefree d) :
    rprefix d (rlist d).length = d := by
  have hl : ∏ j ∈ Finset.range (rlist d).length, (rlist d).getD j 1 = (rlist d).prod := by
    rw [← Fin.prod_univ_eq_prod_range (fun j => (rlist d).getD j 1) (rlist d).length,
      ← Fin.prod_univ_getElem (rlist d)]
    exact Finset.prod_congr rfl (fun i _ => List.getD_eq_getElem (rlist d) 1 i.2)
  unfold rprefix
  rw [hl]
  have hprod : (rlist d).prod = d := by
    rw [← Multiset.prod_coe, rlist, Finset.sort_eq]
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hd, Finset.prod_eq_multiset_prod]
    simp
  exact hprod

/-- Strict descent of the sorted prime list: `pₘ₊₁ < pₘ`. -/
theorem relem_descent {d : ℕ} (i : ℕ) (hi : i + 1 < (rlist d).length) :
    relem d (i + 1) < relem d i := by
  have hlt : (rlist d)[i + 1] < (rlist d)[i]'(by omega) :=
    (sortedGT_iff_getElem_gt_getElem_of_lt.mp (Finset.sortedGT_sort d.primeFactors))
      (i := i + 1) (j := i) (by omega)
  rw [relem, relem, List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ (by omega : i < (rlist d).length)]
  exact hlt

/-- Each listed prime factor is `≥ 2`. -/
theorem two_le_relem {d i : ℕ} (hi : i < (rlist d).length) : 2 ≤ relem d i := by
  rw [relem, List.getD_eq_getElem _ _ hi]
  exact (Nat.prime_of_mem_primeFactors (rlist_mem.mp (List.getElem_mem hi))).two_le

theorem relem_pos {d i : ℕ} (hi : i < (rlist d).length) : 0 < relem d i := by
  have := two_le_relem hi; omega

/-- Prefix products are positive (empty product `1`, else products of primes). -/
theorem rprefix_pos {d : ℕ} (m : ℕ) : 0 < rprefix d m := by
  unfold rprefix
  apply Finset.prod_pos
  intro j _
  rcases lt_or_ge j (rlist d).length with hj | hj
  · exact relem_pos hj
  · rw [List.getD_eq_default _ _ hj]; norm_num

/-- `rprefix` recursion: `p₁⋯pₘ₊₁ = (p₁⋯pₘ)·pₘ₊₁`. -/
theorem rprefix_succ (d m : ℕ) : rprefix d (m + 1) = rprefix d m * relem d m := by
  unfold rprefix relem
  rw [Finset.prod_range_succ]

/-! ## Part B — the Rosser support core and the two endpoints -/

/-- **Rosser support core.** If a *checked* position `m` is either the last (`m = L`) or
second-to-last (`m + 1 = L`) prime position of `d` (squarefree), then the Rosser check
`(p₁⋯pₘ)·pₘ² < D` forces `d < D`.  (The tail after `m` has at most one prime, `< pₘ`.) -/
theorem support_core {D d : ℕ} (hd : Squarefree d) {m : ℕ} (hm1 : 1 ≤ m)
    (hmL : m ≤ (rlist d).length) (htail : (rlist d).length ≤ m + 1)
    (hchk : rprefix d m * (relem d (m - 1)) ^ 2 < D) : d < D := by
  set L := (rlist d).length with hL
  have hfull : rprefix d L = d := rprefix_full hd
  have hm1L : m - 1 < L := by omega
  have hrelem2 : 0 < (relem d (m - 1)) ^ 2 := by have := relem_pos hm1L; positivity
  rcases (by omega : L = m ∨ L = m + 1) with hcase | hcase
  · have hdeq : d = rprefix d m := by rw [hcase] at hfull; exact hfull.symm
    calc d = rprefix d m := hdeq
      _ ≤ rprefix d m * (relem d (m - 1)) ^ 2 := Nat.le_mul_of_pos_right _ hrelem2
      _ < D := hchk
  · have hdeq : d = rprefix d m * relem d m := by
      rw [hcase, rprefix_succ] at hfull; exact hfull.symm
    have hdesc : relem d m < relem d (m - 1) := by
      have := relem_descent (m - 1) (by omega : (m - 1) + 1 < L)
      rwa [show m - 1 + 1 = m by omega] at this
    have hchain : relem d m < (relem d (m - 1)) ^ 2 := by
      have h1 : relem d (m - 1) ≤ (relem d (m - 1)) ^ 2 := by
        rw [sq]; exact Nat.le_mul_of_pos_right _ (relem_pos hm1L)
      omega
    calc d = rprefix d m * relem d m := hdeq
      _ < rprefix d m * (relem d (m - 1)) ^ 2 :=
          mul_lt_mul_of_pos_left hchain (rprefix_pos (d := d) m)
      _ < D := hchk

/-- **Upper Rosser support (ν = 1).** Every squarefree `d` satisfying the upper Rosser
condition has `d < D` (needs only `2 ≤ D`). -/
theorem rosserCond_upper_lt {D d : ℕ} (hd : Squarefree d) (hD : 2 ≤ D)
    (hcond : rosserCond 1 D d) : d < D := by
  set L := (rlist d).length with hL
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · have hf : rprefix d L = d := rprefix_full hd
    rw [hL0] at hf
    simp only [rprefix, Finset.range_zero, Finset.prod_empty] at hf
    omega
  · rcases Nat.even_or_odd L with hev | hodd
    · have hL2 : 2 ≤ L := by rcases hev with ⟨k, hk⟩; omega
      have hpar : (L - 2 + 1) % 2 = 1 % 2 := by rcases hev with ⟨k, hk⟩; omega
      have hchk := hcond (L - 2) (by omega) hpar
      apply support_core hd (m := L - 1) (by omega) (by omega) (by omega)
      rw [show L - 1 - 1 = L - 2 by omega]
      rwa [show L - 2 + 1 = L - 1 by omega] at hchk
    · have hLodd : L % 2 = 1 := Nat.odd_iff.mp hodd
      have hpar : (L - 1 + 1) % 2 = 1 % 2 := by omega
      have hchk := hcond (L - 1) (by omega) hpar
      apply support_core hd (m := L) (by omega) (le_refl _) (by omega)
      rwa [show L - 1 + 1 = L by omega] at hchk

/-- **Lower Rosser support (ν = 2).** For squarefree `d` all of whose prime factors are
`< z` (i.e. `d ∣ P(z)`), the lower Rosser condition gives `d < D` — using `z ≤ D` only in
the single-prime case `r = 1`, the honest home of the `D ≥ z²` asymmetry. -/
theorem rosserCond_lower_lt {D d z : ℕ} (hd : Squarefree d) (hz : 2 ≤ z) (hzD : z ≤ D)
    (hsmooth : ∀ p ∈ d.primeFactors, p < z) (hcond : rosserCond 2 D d) : d < D := by
  set L := (rlist d).length with hL
  rcases Nat.lt_or_ge L 2 with hLlt | hLge
  · interval_cases L
    · have hf : rprefix d 0 = d := by rw [hL]; exact rprefix_full hd
      simp only [rprefix, Finset.range_zero, Finset.prod_empty] at hf
      omega
    · have hf : rprefix d 1 = d := by rw [hL]; exact rprefix_full hd
      rw [rprefix_succ, show rprefix d 0 = 1 by
        simp [rprefix, Finset.range_zero, Finset.prod_empty], one_mul] at hf
      have hmem : relem d 0 ∈ d.primeFactors := by
        rw [relem, List.getD_eq_getElem _ _ (by omega : 0 < (rlist d).length)]
        exact rlist_mem.mp (List.getElem_mem _)
      have := hsmooth _ hmem
      omega
  · rcases Nat.even_or_odd L with hev | hodd
    · have hLeven : L % 2 = 0 := Nat.even_iff.mp hev
      have hpar : (L - 1 + 1) % 2 = 2 % 2 := by omega
      have hchk := hcond (L - 1) (by omega) hpar
      apply support_core hd (m := L) (by omega) (le_refl _) (by omega)
      rwa [show L - 1 + 1 = L by omega] at hchk
    · have hLodd : L % 2 = 1 := Nat.odd_iff.mp hodd
      have hL3 : 3 ≤ L := by omega
      have hpar : (L - 2 + 1) % 2 = 2 % 2 := by omega
      have hchk := hcond (L - 2) (by omega) hpar
      apply support_core hd (m := L - 1) (by omega) (by omega) (by omega)
      rw [show L - 1 - 1 = L - 2 by omega]
      rwa [show L - 2 + 1 = L - 1 by omega] at hchk

/-! ## Part C0 — the Buchstab-decomposition base term `V(z)`

The multiplicative identity `∑_{d|P(z)} μ(d) g(d) = ∏_{p|P(z)}(1 − g(p)) = V(z)` is the
`n = 0` term of the Buchstab decomposition `G(z, λ±) = V(z) ± Σₙ Tₙ` (BJS Prop 13, via
Nathanson Lemma 9.3): it is the untruncated Möbius sum, obtained here directly from
mathlib's `prodPrimeFactors_one_sub_of_squarefree`.  Combined with `mainSum_lam_defect`,
`mainSum S.lam` differs from `V(z)` exactly by the Rosser-violating Möbius mass — the
combinatorial content that the deferred `Tₙ` prime-tuple organisation (Nathanson 9.3)
resolves into `±Σₙ Tₙ`. -/

/-- **Buchstab base term** (BJS Prop 13, the `V(z)` term): the untruncated Möbius sum
`∑_{d|P(z)} μ(d) ν(d)` equals the H-R density product `W(z) = V(z)`. -/
theorem mainSum_moebius_eq_W (s : BoundingSieve) :
    s.mainSum (fun d => (μ d : ℝ)) = Salt.BrunLower.W s := by
  rw [mainSum, Salt.BrunLower.W]
  exact (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    s.nu s.nu_mult s.prodPrimes_squarefree).symm

/-- The truncated Rosser main sum differs from `V(z)` exactly by the Möbius mass on the
Rosser-*violating* divisors — the defect that Nathanson Lemma 9.3 reorganises into the
signed Buchstab tail `∓Σₙ Tₙ`. -/
theorem mainSum_lam_defect (s : BoundingSieve) (S : TruncSieve) :
    Salt.BrunLower.W s - s.mainSum S.lam
      = ∑ d ∈ divisors s.prodPrimes, (μ d : ℝ) * (if S.P d then 0 else 1) * s.nu d := by
  rw [← mainSum_moebius_eq_W, mainSum, mainSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [TruncSieve.lam]
  by_cases h : S.P d <;> simp [h]

/-! ## Part C — the squarefree-augmented Rosser truncation sieve

The plain `rosserSieve` predicate does not bound non-squarefree arguments (`rosserCond`
sees only the radical).  Augmenting with `Squarefree` makes the support bound
*unconditional in `d`* on the upper side — and does not change `.lam` (`μ` already vanishes
off the squarefrees).  It is a valid `TruncSieve` (squarefreeness is `add_prime`-closed
because a prepended smaller prime is coprime to the tail). -/

/-- The Rosser weights with the squarefree indicator folded into the predicate. -/
noncomputable def rosserSquarefreeSieve (side D : ℕ) (hside : side = 1 ∨ side = 2) :
    TruncSieve where
  P := fun d => rosserCond side D d ∧ Squarefree d
  decP := fun _ => Classical.propDecidable _
  side := side
  hside := hside
  one_mem := ⟨rosserCond_one side D, squarefree_one⟩
  dvd_closed := @fun _d _t hd htd hc =>
    ⟨rosserCond_dvd_closed hd htd hc.1, hc.2.squarefree_of_dvd htd⟩
  add_prime := @fun p t hp ht hlt hpar hc => by
    refine ⟨rosserCond_add_prime hp ht hlt hpar hc.1, ?_⟩
    have hpt : ¬ p ∣ t := by
      intro hdvd
      exact absurd (hlt p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, ht⟩)) (lt_irrefl p)
    exact (Nat.squarefree_mul_iff.mpr
      ⟨(hp.coprime_iff_not_dvd).mpr hpt, hp.squarefree, hc.2⟩)

@[simp] theorem rosserSquarefreeSieve_P (side D : ℕ) (hside : side = 1 ∨ side = 2) (d : ℕ) :
    (rosserSquarefreeSieve side D hside).P d = (rosserCond side D d ∧ Squarefree d) := rfl

@[simp] theorem rosserSquarefreeSieve_side (side D : ℕ) (hside : side = 1 ∨ side = 2) :
    (rosserSquarefreeSieve side D hside).side = side := rfl

/-! ## Part D — the upper endpoint plug (into `linear_sieve_upper_chain`)

The upper support bound is unconditional in `d`, so the Rosser weights plug directly into
the unmodified `linear_sieve_upper_chain`.  Only the main-term comparison `hmain` (BJS
Prop 13) remains a hypothesis. -/

/-- **Upper linear sieve, Rosser weights (BJS Theorem 6, (5)).**  With the support bound
`hsupp` fully discharged (`rosserCond_upper_lt`), the explicit upper sieve holds for the
Rosser weights, remainder cut at `bound = Q·D`, given only the BJS Prop-13 main-term
comparison `hmain`. -/
theorem linear_sieve_upper_rosser (s : BoundingSieve) (D : ℕ) (hD : 2 ≤ D)
    (htm : 0 ≤ s.totalMass) (N : ℕ) (sparam ε C₁ Q : ℝ) (hQ : 1 ≤ Q)
    (hmain : s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s * (Fchain N sparam + ε * C₁ * Real.exp 2 * hBJS sparam)) :
    s.siftedSum
      ≤ s.totalMass * (Salt.BrunLower.W s *
          (Fchain N sparam + ε * C₁ * Real.exp 2 * hBJS sparam))
        + rosserRemainder s (Q * D) := by
  refine linear_sieve_upper_chain s (rosserSquarefreeSieve 1 D (Or.inl rfl)) rfl
    (bound := Q * D) ?_ htm N sparam ε C₁ hmain
  intro d hPd
  obtain ⟨hcond, hsf⟩ := hPd
  have hlt : d < D := rosserCond_upper_lt hsf hD hcond
  have hcast : (d : ℝ) < (D : ℝ) := by exact_mod_cast hlt
  calc (d : ℝ) < (D : ℝ) := hcast
    _ = 1 * (D : ℝ) := (one_mul _).symm
    _ ≤ Q * (D : ℝ) := mul_le_mul_of_nonneg_right hQ (by positivity)

/-! ## Part E — the corrected divisor-restricted lower plumbing

`errSum_lam_le` in `LinearSieve.lean` demands an *unconditional* support bound, which is
unsatisfiable for `side = 2` (see the header flag).  The divisor-restricted variant keeps
the `d ∣ prodPrimes` information that `errSum` sums over, which is all that is needed. -/

/-- Divisor-restricted error-sum bound: the truncation error is `≤ R` using only the
support bound on divisors of `prodPrimes` (all squarefree).  Corrects
`LinearSieve.errSum_lam_le` for the lower side. -/
theorem errSum_lam_le_div (S : TruncSieve) (s : BoundingSieve) {bound : ℝ}
    (hsupp : ∀ d, d ∣ s.prodPrimes → S.P d → (d : ℝ) < bound) :
    s.errSum S.lam ≤ rosserRemainder s bound := by
  rw [errSum]
  unfold rosserRemainder
  apply Finset.sum_le_sum
  intro d hd
  have hdvd : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hd).1
  by_cases hP : S.P d
  · rw [if_pos (hsupp d hdvd hP)]
    calc |S.lam d| * |s.rem d|
        ≤ 1 * |s.rem d| := mul_le_mul_of_nonneg_right (S.abs_lam_le_one d) (abs_nonneg _)
      _ = |s.rem d| := one_mul _
  · rw [S.lam_eq_zero_of_not hP, abs_zero, zero_mul]
    split_ifs <;> positivity

/-- **Linear sieve, lower bound (divisor-restricted).** The corrected lower endpoint (node
B1's lower-Möbius dual) with the honest `d ∣ prodPrimes` support hypothesis. -/
theorem linear_sieve_lower_div (s : BoundingSieve) (S : TruncSieve) (hside : S.side = 2)
    {bound mainBound : ℝ}
    (hsupp : ∀ d, d ∣ s.prodPrimes → S.P d → (d : ℝ) < bound)
    (htm : 0 ≤ s.totalMass)
    (hmain : mainBound ≤ s.mainSum S.lam) :
    s.totalMass * mainBound - rosserRemainder s bound ≤ s.siftedSum := by
  have hL := Salt.BrunLower.siftedSum_ge_mainSum_errSum_of_lowerMoebius S.lam
    (S.isLowerMoebius hside) (s := s)
  have hmul : s.totalMass * mainBound ≤ s.totalMass * s.mainSum S.lam :=
    mul_le_mul_of_nonneg_left hmain htm
  have herr := errSum_lam_le_div S s hsupp
  linarith

/-- **Lower linear sieve, Rosser weights (BJS Theorem 6, (6)).**  The lower support bound is
discharged on `d ∣ prodPrimes` (`rosserCond_lower_lt`), using the smoothness of `prodPrimes`
(`hz`, i.e. `prodPrimes = P(z)`) and `z ≤ D` (from `D ≥ z²`).  Only the BJS Prop-13 lower
main-term comparison `hmain` remains a hypothesis. -/
theorem linear_sieve_lower_rosser (s : BoundingSieve) (D z : ℕ) (hz2 : 2 ≤ z) (hzD : z ≤ D)
    (hz : ∀ p ∈ s.prodPrimes.primeFactors, p < z)
    (htm : 0 ≤ s.totalMass) (N : ℕ) (sparam ε C₂ Q : ℝ) (hQ : 1 ≤ Q)
    (hmain : Salt.BrunLower.W s * (fchain N sparam - ε * C₂ * Real.exp 2 * hBJS sparam)
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam) :
    s.totalMass * (Salt.BrunLower.W s * (fchain N sparam - ε * C₂ * Real.exp 2 * hBJS sparam))
        - rosserRemainder s (Q * D) ≤ s.siftedSum := by
  refine linear_sieve_lower_div s (rosserSquarefreeSieve 2 D (Or.inr rfl)) rfl
    (bound := Q * D) ?_ htm hmain
  intro d hdvd hPd
  obtain ⟨hcond, hsf⟩ := hPd
  have hsmooth : ∀ p ∈ d.primeFactors, p < z := fun p hp =>
    hz p (Nat.primeFactors_mono hdvd s.prodPrimes_squarefree.ne_zero hp)
  have hlt : d < D := rosserCond_lower_lt hsf hz2 hzD hsmooth hcond
  have hcast : (d : ℝ) < (D : ℝ) := by exact_mod_cast hlt
  calc (d : ℝ) < (D : ℝ) := hcast
    _ = 1 * (D : ℝ) := (one_mul _).symm
    _ ≤ Q * (D : ℝ) := mul_le_mul_of_nonneg_right hQ (by positivity)

end Salt.Chen
