/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Op
import Salt.Chen.TwinA2

/-!
# G-OMEGA (wave W4) — the Goldbach `A₂` omega carrier and its op bundle

The missing A₂ carrier for the Goldbach headline `goldbach_of_hypotheses_W` (the mirror of
`Salt.Chen.chen_of_hypotheses_W`, `Assembly.lean:715`).  The twin razor's three-term ledger
consumes an `omegaPrimeSumW Q a x P y ≤ mainA2` slot backed by the aggregated A₂ carrier
`omegaPrimeSumW` (Assembly.lean:476) with its decomposition (`omegaPrimeSumW_decomp`), density
coefficient (`twinA2W_hcoef`), and BV row (`a12_hBV_A2`).  This file mirrors that stack under the
frozen Goldbach substitution `n + 2 ↦ N − n`, reusing the landed Goldbach A₂ infrastructure
(`Salt/Goldbach/A2W.lean`).

## The load-bearing Goldbach shape (vs twin)

The paired value is the reflection `N − n`, so the split sifting bridge and the decomposition
land on the **punctured** prime window `{p ∈ [z, y] : p prime, p ∤ N}` — the same puncture
`goldPs` applies to its sifting primes.  Two Goldbach-shaped facts feed this:

* the reflected mod transfer `n ≡ a (Q) ⟹ (N − n) ≡ (N − a) (Q)` (needs `n ≤ N`, `a ≤ N`; the
  twin translation `(n+2) % Q = (a+2) % Q` was free) — carried by `gold_op_residue`'s
  `Coprime opQ (N − a)`;
* the window prime `n ≥ N/2` exceeds `y = ⌊N^{1/3}⌋` (`gold_op_Yhalf`), which forces every prime
  factor of `N − n` off `N` (a prime `q ∣ N ∧ q ∣ (N−n) ⟹ q ∣ n ⟹ q = n > y`, impossible).

## Deliverables

1. `goldOmegaPrimeSum` — the aggregated A₂ carrier `Σ_{n≡a(Q)} Λ(n)·1_keep·ω_{≤y}(N−n)`.
2. `goldOmegaPrimeSum_decomp` — the decomposition into the punctured per-prime slices `goldA2pW`.
3. `goldA2W_hcoef` — the density coefficient factorisation (a mass identity, as in the twin).
4. `gold_a12_hBV_A2` — the Finding-4 aggregated BV row (`∃ B C` outside `∀ N`).
5. `gold_a12_hA2` — the A₂ op bundle delivering the `goldOmegaPrimeSum ≤ mainA2` slot at `x := N`.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV Salt.Chen

namespace Salt.Goldbach

/-! ## Part A — the carrier, the W-transparency, and the punctured split bridge -/

/-- **The W-restricted aggregated Goldbach A₂ carrier** (`omegaPrimeSumW` mirror at `N − n`).
The keep condition is inlined exactly as `goldA2pW` (A2W.lean): `n` prime, `N − n` coprime to the
sifting product `P`, and `n ≡ a (mod Q)`; the weight `ω_{≤y}(N − n)` counts the small prime
factors of the reflected value. -/
noncomputable def goldOmegaPrimeSum (Q a N P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow N,
    vonMangoldt n
      * (if Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q then (1 : ℝ) else 0)
      * (omegaLe y (N - n) : ℝ)

/-- The `W`-value transparency (`twinA2SieveW_W_eq` mirror): the per-prime A₂ instance carries the
same sifting data (`prodPrimes = P`, `nu = nuChen`) as the A₁ instance, so the density products
agree definitionally. -/
lemma goldA2SieveW_W_eq (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    Salt.BrunLower.W (goldA2SieveW Q a N P p hP hPodd)
      = Salt.BrunLower.W (goldA1SieveW Q a N P hP hPodd) := rfl

/-- **The punctured split sifting bridge** (`factors_ge_z_of_sift_W` mirror at `N − n`).  Under
the split trio (`hQfull`/`hPfull'`/`hQNa`) with `hPfull'` asserting fullness only for the
survivor primes (`¬ q ∣ N`, matching the punctured `goldPs`), at a kept prime point `n` with
`z ≤ n` every prime factor of `N − n` is `≥ z`.  The `q ∣ N` primes in `[w', z)` are ruled out by
`q ∣ (N−n) ∧ q ∣ N ⟹ q ∣ n ⟹ q = n`, impossible since `q < z ≤ n`. -/
theorem gold_factors_ge_z_of_sift {Q a P w' z N n : ℕ}
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a))
    (hcop : Nat.Coprime P (N - n)) (hmod : n % Q = a % Q)
    (hnN : n ≤ N) (haN : a ≤ N) (hnprime : Nat.Prime n) (hzn : z ≤ n) :
    ∀ p ∈ (N - n).primeFactors, z ≤ p := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ (N - n) := Nat.dvd_of_mem_primeFactors hp
  by_contra hlt
  rw [not_le] at hlt
  by_cases hw : p < w'
  · -- small range [2, w'): p ∣ Q, and the reflected mod-Q transfer puts p inside gcd(Q, N−a) = 1
    have hpQ : p ∣ Q := hQfull p hpp hw
    have hmod2 : (N - n) % Q = (N - a) % Q := by
      have hapQ : n ≡ a [MOD Q] := hmod
      have key : (N - n) + n = (N - a) + a := by omega
      have h1 : (N - n) + n ≡ (N - a) + n [MOD Q] := by
        rw [key]; exact Nat.ModEq.add_left (N - a) hapQ.symm
      exact Nat.ModEq.add_right_cancel' n h1
    have hpn2 : p ∣ (N - n) % Q := (Nat.dvd_mod_iff hpQ).mpr hpd
    rw [hmod2] at hpn2
    have hpa2 : p ∣ (N - a) := (Nat.dvd_mod_iff hpQ).mp hpn2
    have hdvd1 : p ∣ Nat.gcd Q (N - a) := Nat.dvd_gcd hpQ hpa2
    rw [Nat.Coprime] at hQNa
    rw [hQNa] at hdvd1
    exact hpp.ne_one (Nat.dvd_one.mp hdvd1)
  · -- sieve range [w', z): the survivor primes divide `P` against `(P, N−n) = 1`
    rw [not_lt] at hw
    have hpN : ¬ p ∣ N := by
      intro hpNdvd
      have hpn : p ∣ n := by
        have := Nat.dvd_sub hpNdvd hpd
        rwa [Nat.sub_sub_self hnN] at this
      have hpeq : p = n := (hnprime.eq_one_or_self_of_dvd p hpn).resolve_left hpp.ne_one
      omega
    have hpP : p ∣ P := hPfull' p hpp hw hlt hpN
    have hdvd1 : p ∣ Nat.gcd P (N - n) := Nat.dvd_gcd hpP hpd
    rw [Nat.Coprime] at hcop
    rw [hcop] at hdvd1
    exact hpp.ne_one (Nat.dvd_one.mp hdvd1)

/-! ## Part B — the decomposition into punctured per-prime slices -/

/-- **The carrier identification** (`omegaPrimeSumW_decomp` mirror, punctured window).  Under the
split trio and the window-prime bounds (`hzy : z ≤ y`, `hyw`: window primes exceed `y`), the
carrier decomposes into the per-prime slices `goldA2pW` over the punctured prime window
`{p ∈ [z, y] : p prime, p ∤ N}`: at a kept point every prime factor of `N − n` lies in `[z, y]`
and misses `N`, so `ω_{≤y}(N − n)` counts exactly those `p`; Fubini swaps the two sums. -/
theorem goldOmegaPrimeSum_decomp {Q a N P y z w' : ℕ}
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a)) (haN : a ≤ N) (hzy : z ≤ y)
    (hyw : ∀ n ∈ twinWindow N, Nat.Prime n → y < n) :
    goldOmegaPrimeSum Q a N P y
      = ∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), goldA2pW Q a N P p := by
  unfold goldOmegaPrimeSum goldA2pW
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q
  · -- kept point: the split bridge + window bounds force factors into the punctured [z, y]
    have hnmem := hn
    rw [twinWindow, Finset.mem_Icc] at hnmem
    have hnN : n ≤ N := by omega
    have hyn : y < n := hyw n hn hk.1
    have hzn : z ≤ n := by omega
    have hbr := gold_factors_ge_z_of_sift hQfull hPfull' hQNa hk.2.1 hk.2.2 hnN haN hk.1 hzn
    have hn2 : 2 ≤ n := hk.1.two_le
    have hNn0 : N - n ≠ 0 := by omega
    rw [← Finset.mul_sum]
    congr 1
    have hset : (N - n).primeFactors.filter (· ≤ y)
        = ((Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N)).filter (· ∣ (N - n)) := by
      ext q
      simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hqp, hqd, _⟩, hqy⟩
        have hqmem : q ∈ (N - n).primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, hNn0⟩
        refine ⟨⟨⟨hbr q hqmem, hqy⟩, hqp, ?_⟩, hqd⟩
        intro hqN
        have hqn : q ∣ n := by
          have := Nat.dvd_sub hqN hqd
          rwa [Nat.sub_sub_self hnN] at this
        have hqeqn : q = n := (hk.1.eq_one_or_self_of_dvd q hqn).resolve_left hqp.ne_one
        omega
      · rintro ⟨⟨⟨_, hqy⟩, hqp, _⟩, hqd⟩
        exact ⟨⟨hqp, hqd, hNn0⟩, hqy⟩
    rw [Finset.sum_boole, omegaLe, hset]
  · -- discarded point: both sides vanish
    simp only [if_neg hk, mul_zero, zero_mul, Finset.sum_const_zero]

/-! ## Part C — the density coefficient factorisation (`hcoef`) -/

/-- **`goldA2W_hcoef`** (`twinA2W_hcoef` mirror).  A mass identity:
`totalMass_p·W_p = (Λmass_W·V)·(1/(p−1))` with `Λmass_W = totalMass (goldA1SieveW)` and
`V = W (goldA1SieveW)`; the smooth conventions make it definitional (no dispersion row). -/
theorem goldA2W_hcoef (Qm a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (goldA2SieveW Qm a N P p hP hPodd).totalMass
        * Salt.BrunLower.W (goldA2SieveW Qm a N P p hP hPodd)
      ≤ ((goldA1SieveW Qm a N P hP hPodd).totalMass
          * Salt.BrunLower.W (goldA1SieveW Qm a N P hP hPodd)) * (1 / ((p : ℝ) - 1)) := by
  apply le_of_eq
  rw [goldA2SieveW_W_eq, goldA2SieveW_totalMass, goldA1SieveW_totalMass]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ## Part D — the aggregated BV row, Finding-4 form (`∃ B C` outside `∀ N`)

The `goldA2_hBVagg_W` mirror with the `∃ B C` pulled OUTSIDE the `∀`, so the operating-point
consumer (`gold_a12_hA2`) can choose its threshold as a function of the `N`-independent `B, C`
from `psi_BV_of_siegelWalfisz'`.  Body is `goldA2_hBVagg_W`'s composition verbatim (the punctured
per-prime split `goldRosserRemainderW2_le_split` + the shared W2 dispersion/conversion legs). -/
set_option linter.unusedVariables false in
theorem gold_a12_hBV_A2 : ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
    ∀ (Qm a N z y Dtot P : ℕ) (ε Qlev : ℝ)
      (hP : Squarefree P) (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q)
      (hPz : ∀ q ∈ P.primeFactors, q < z)
      (hPlow : ∀ q ∈ P.primeFactors, w0R ε ≤ (q : ℝ))
      (hPcopN : Nat.Coprime P N)
      (hN : 4 ≤ N) (hz3 : 3 ≤ z) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hwz : w0R ε ≤ (z : ℝ))
      (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P) (hQma : Nat.Coprime Qm a)
      (hQmPr : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, Nat.Coprime Qm p)
      (hQlev : 1 ≤ Qlev) (hD1 : 1 ≤ Dtot),
      ( (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B →
        C * (N : ℝ) / (Real.log N) ^ (11 : ℝ) + C * (N : ℝ) / (Real.log N) ^ (11 : ℝ)
          + 2 * Real.log N
              * ((Qm.primeFactors.card : ℝ)
                  + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
              * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1))
          ≤ (N : ℝ) / (Real.log N) ^ 10 →
        ∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N),
            rosserRemainder (goldA2SieveW Qm a N P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ))
          ≤ (N : ℝ) / (Real.log N) ^ 10 ) := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, ?_⟩
  intro Qm a N z y Dtot P ε Qlev hP hPodd hPz hPlow hPcopN hN hz3 hε hw0 hwz hQm1 hQmP hQma
    hQmPr hQlev hD1 hlevel hclose
  classical
  have hN2 : 2 ≤ N := by omega
  have hQlev0 : (0 : ℝ) ≤ Qlev := by linarith
  have hBND1 : (1 : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    have hD1R : (1 : ℝ) ≤ (Dtot : ℝ) := by exact_mod_cast hD1
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    nlinarith [hQlev, hD1R, hy0]
  have hpdB : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      (p : ℝ) * (d : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    intro p hpR d _hd hlt
    rw [Finset.mem_filter, Finset.mem_Icc] at hpR
    obtain ⟨⟨_hzp, hpy⟩, hpp⟩ := hpR
    have hppos : 0 < p := hpp.pos
    have hpposR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
    have hcd : p * cdiv Dtot p ≤ Dtot + p := by
      have h1 : (Dtot - 1) / p * p ≤ Dtot - 1 := Nat.div_mul_le_self _ _
      unfold cdiv
      calc p * ((Dtot - 1) / p + 1) = (Dtot - 1) / p * p + p := by ring
        _ ≤ Dtot + p := by omega
    have hcdR : (p : ℝ) * (cdiv Dtot p : ℝ) ≤ (Dtot : ℝ) + (p : ℝ) := by
      calc (p : ℝ) * (cdiv Dtot p : ℝ) = ((p * cdiv Dtot p : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((Dtot + p : ℕ) : ℝ) := by exact_mod_cast hcd
        _ = (Dtot : ℝ) + (p : ℝ) := by push_cast; ring
    have hpyR : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast hpy
    calc (p : ℝ) * (d : ℝ)
        ≤ (p : ℝ) * (Qlev * (cdiv Dtot p : ℝ)) :=
          mul_le_mul_of_nonneg_left hlt.le hpposR.le
      _ = Qlev * ((p : ℝ) * (cdiv Dtot p : ℝ)) := by ring
      _ ≤ Qlev * ((Dtot : ℝ) + (p : ℝ)) := mul_le_mul_of_nonneg_left hcdR hQlev0
      _ ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hQlev0
          linarith
  have hlev' : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      ((Qm * (p * d) : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B := by
    intro p hpR d hd hlt
    have h1 := hpdB p hpR d hd hlt
    have hQm0 : (0 : ℝ) ≤ (Qm : ℝ) := Nat.cast_nonneg _
    calc ((Qm * (p * d) : ℕ) : ℝ) = (Qm : ℝ) * ((p : ℝ) * (d : ℝ)) := by push_cast; ring
      _ ≤ (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) := mul_le_mul_of_nonneg_left h1 hQm0
      _ ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B := hlevel
  have hGsub : (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N)
      ⊆ (Finset.Icc z y).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hsum : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        rosserRemainder (goldA2SieveW Qm a N P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ)))
      ≤ (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (N - 2) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (N / 2 - 1) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then convTerm N (Qm * (p * d)) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hpG
    have hpG' := hpG
    rw [Finset.mem_filter, Finset.mem_Icc] at hpG'
    obtain ⟨⟨hzp, _hpy⟩, hpp, hpN⟩ := hpG'
    have hp3 : 3 ≤ p := by omega
    have hpP : Nat.Coprime p P := (Nat.Prime.coprime_iff_not_dvd hpp).mpr (fun hpdvd =>
      absurd (hPz p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, hP.ne_zero⟩)) (by omega))
    exact goldRosserRemainderW2_le_split Qm a N P p hP hPodd hQm1 hQma hQmP
      (hQmPr p (hGsub hpG)) hpp hp3 hpP hPcopN hpN hN _
  have hbv1 := hbv N (N - 2) hN2 (by omega : N - 2 ≤ N)
  have hbv2 := hbv N (N / 2 - 1) hN2 (by omega : N / 2 - 1 ≤ N)
  have hnnD : ∀ (y' : ℕ) p, (0 : ℝ) ≤ ∑ d ∈ P.divisors,
      if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then dispDisc y' (Qm * (p * d)) else 0 := by
    intro y' p
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact dispDisc_nonneg _ _
    · exact le_refl 0
  have hnnC : ∀ p, (0 : ℝ) ≤ ∑ d ∈ P.divisors,
      if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then convTerm N (Qm * (p * d)) else 0 := by
    intro p
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact convTerm_nonneg _ _
    · exact le_refl 0
  have hS1 : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (N - 2) (Qm * (p * d)) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun p _ _ => hnnD (N - 2) p))
      (le_trans (dispDiscW2_double_le_Icc Qm (N - 2) hQm1 hP.ne_zero hPz hlev') hbv1)
  have hS2 : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (N / 2 - 1) (Qm * (p * d)) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun p _ _ => hnnD (N / 2 - 1) p))
      (le_trans (dispDiscW2_double_le_Icc Qm (N / 2 - 1) hQm1 hP.ne_zero hPz hlev') hbv2)
  have hconv := convSumW2_le Qm hP hPodd hQm1 hPz hz3 hN hBND1 hpdB
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (twinA1SieveW Qm a N P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, hPlow q hq,
        by exact_mod_cast hPz q hq, twinA1_hnu P q hq⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hK0 : 0 ≤ 2 * Real.log N
      * ((Qm.primeFactors.card : ℝ)
          + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3) := by
    have h0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlogB : 0 ≤ Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) := Real.log_nonneg hBND1
    have : 0 ≤ (Qm.primeFactors.card : ℝ)
        + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3 := by positivity
    exact mul_nonneg (by positivity) this
  have hconv2 : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then convTerm N (Qm * (p * d)) else 0)
      ≤ 2 * Real.log N
          * ((Qm.primeFactors.card : ℝ)
              + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun p _ _ => hnnC p)) ?_
    refine le_trans hconv ?_
    apply mul_le_mul_of_nonneg_right _ hSp0
    exact mul_le_mul_of_nonneg_left hMbound hK0
  linarith [hsum, hS1, hS2, hconv2, hclose]

/-! ## Part E — the operating-point A₂ bundle (`gold_a12_hA2`)

The window prime `n ≥ N/2` exceeds `y = opY N = ⌊N^{1/3}⌋` past a threshold — the fact that
punctures the omega decomposition (`goldOmegaPrimeSum_decomp`'s `hyw`). -/

/-- **`opY N < N/2`** past `10^48`: `opY N ≤ N^{1/3}` and `2·N^{1/3} + 2 ≤ N` for `N ≥ 10^48`
(`s = N^{1/3} ≥ 10^{16}`, so `s^3 = N ≥ 10^{32}·s ≥ 2s + 2`).  Hence every window prime exceeds
`opY N`. -/
theorem gold_op_Yhalf : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → opY N < N / 2 := by
  refine ⟨10 ^ 48, fun N hN => ?_⟩
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  set s : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3) with hs
  have hpow3 : s ^ (3 : ℕ) = (N : ℝ) := by
    rw [hs, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hNpos.le]
    norm_num
  have h16 : (10 : ℝ) ^ 16 ≤ s := by
    have hmono : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hx48R (by norm_num)
    have hcompute : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ 16 := by
      rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hs]; linarith [hmono, hcompute.le, hcompute.ge]
  have hsnn : (0 : ℝ) ≤ s := le_trans (by positivity) h16
  have hyN_le : (opY N : ℝ) ≤ s := by
    rw [hs, opY]; exact Nat.floor_le (Real.rpow_nonneg hNpos.le _)
  have hssq : (10 : ℝ) ^ 32 ≤ s ^ 2 := by
    have hm := mul_le_mul h16 h16 (by norm_num : (0 : ℝ) ≤ 10 ^ 16) hsnn
    calc (10 : ℝ) ^ 32 = 10 ^ 16 * 10 ^ 16 := by norm_num
      _ ≤ s * s := hm
      _ = s ^ 2 := by ring
  have h1 : (10 : ℝ) ^ 32 * s ≤ s ^ 3 := by
    calc (10 : ℝ) ^ 32 * s ≤ s ^ 2 * s := mul_le_mul_of_nonneg_right hssq hsnn
      _ = s ^ 3 := by ring
  have hbig : 2 * (opY N : ℝ) + 2 ≤ (N : ℝ) := by
    have h2 : 2 * s + 2 ≤ (10 : ℝ) ^ 32 * s := by nlinarith [h16]
    rw [← hpow3]; linarith [hyN_le, h2, h1]
  have hbigN : 2 * opY N + 2 ≤ N := by exact_mod_cast hbig
  omega

/-- **`goldOpP` is full over the survivors** (the `hPfull'` slot of `goldOmegaPrimeSum_decomp`):
every prime `q ∈ [opW', opZ N)` with `q ∤ N` divides the punctured window product `goldOpP N`. -/
theorem goldOpP_pfull (N : ℕ) :
    ∀ q, q.Prime → opW' ≤ q → q < opZ N → ¬ q ∣ N → q ∣ goldOpP N := by
  intro q hqp hw hlt hqN
  unfold goldOpP goldPs
  exact Finset.dvd_prod_of_mem (fun p => p)
    (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hw, hlt⟩, hqp, hqN⟩)

set_option linter.unusedVariables false in
/-- **The `hA2` slot of `goldbach_of_hypotheses_W` at the frozen operating point.**  The A₂ omega
carrier's upper bound at `x := N`, over the reflected residue `a` (`gold_op_residue`'s witness,
supplying `Coprime opQ a` and `Coprime opQ (N − a)`).  Byte-mirrors `Salt.Chen.a12_hA2` with the
punctured window aggregation: `goldOmegaPrimeSum_decomp` folds the carrier into the per-prime
`goldA2pW`, `twin_A2_upper` aggregates them (per-prime `gold_A2_per_prime_W`, density coefficient
`goldA2W_hcoef`), and `gold_a12_hBV_A2` discharges the aggregated Rosser remainder. -/
theorem gold_a12_hA2 : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (a : ℕ), a ≤ N → Nat.Coprime opQ a → Nat.Coprime opQ (N - a) →
    goldOmegaPrimeSum opQ a N (goldOpP N) (opY N)
      ≤ ((goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N) (goldOpP_odd N)).totalMass
            * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
                (goldOpP_squarefree N) (goldOpP_odd N)))
          * (A2grid ((Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N))
                (opZ N) (opD N)
                (fun p => maxDepth (goldA2SieveW opQ a N (goldOpP N) p
                    (goldOpP_squarefree N) (goldOpP_odd N)))
              + ∑ p ∈ (Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
                  (1 / ((p : ℝ) - 1))
                    * (opEps * CsharpB opEps * Real.exp 2
                        * hBJS (logRatio (opZ N) (cdiv (opD N) p))))
        + (N : ℝ) / (Real.log N) ^ 10 := by
  obtain ⟨B, C, hB, hC, hbvfun⟩ := gold_a12_hBV_A2
  obtain ⟨x₂, hlev⟩ := a12_level2 B hB
  obtain ⟨x₃, hcl⟩ := a12_close2 C hC
  obtain ⟨x₄, hcd2⟩ := a12_cdiv2
  obtain ⟨x₅, hcds⟩ := a12_cdivStop
  obtain ⟨x₆, hYhalf⟩ := gold_op_Yhalf
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max (max x₂ x₃) (max x₄ x₅)) (max x₆ xt), fun N hN a haN hQma hQNa => ?_⟩
  obtain ⟨hQlog, hwz, hw'z, hz3, hzD, hD1, hzy, -, -, -, -, -, -, -, -, -, hx4⟩ :=
    htower N (by omega)
  have hQ1 : 1 ≤ opQ := by have := opf_Q2; omega
  have hQlevR : (1 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast hQ1
  have hε : (0 : ℝ) < opEps := a12_eps_pos
  have hw0 : (3 : ℝ) ≤ w0R opEps := a12_hw0
  have hx1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hyD : opY N ≤ opD N := by
    rw [opY, opD]
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num))
  have hyw : ∀ n ∈ twinWindow N, Nat.Prime n → opY N < n := by
    intro n hn _
    rw [twinWindow, Finset.mem_Icc] at hn
    have := hYhalf N (by omega)
    omega
  classical
  set S := (Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N) with hS
  have hGsub : S ⊆ (Finset.Icc (opZ N) (opY N)).filter Nat.Prime := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    exact ⟨hp.1, hp.2.1⟩
  -- the carrier identification (punctured window)
  have hdecomp := goldOmegaPrimeSum_decomp (Q := opQ) (a := a) (N := N) (P := goldOpP N)
    (y := opY N) (z := opZ N) (w' := opW') opf_Qfull (goldOpP_pfull N) hQNa haN hzy hyw
  rw [← hS] at hdecomp
  -- slack nonnegativity
  have hCs : 0 ≤ CsharpB opEps := by
    rw [CsharpB]
    apply div_nonneg (by norm_num)
    have h := chSharpB_lt_one a12_eps_lt_249
    linarith
  have hslacknn : ∀ p ∈ S, 0 ≤ opEps * CsharpB opEps * Real.exp 2
      * hBJS (logRatio (opZ N) (cdiv (opD N) p)) := fun p _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hε.le hCs) (Real.exp_pos 2).le)
      (hBJS_pos (logRatio (opZ N) (cdiv (opD N) p))).le
  -- per-prime supplier bounds
  have hper : ∀ p ∈ S,
      goldA2pW opQ a N (goldOpP N) p
        ≤ ((goldA2SieveW opQ a N (goldOpP N) p (goldOpP_squarefree N)
                (goldOpP_odd N)).totalMass
              * Salt.BrunLower.W (goldA2SieveW opQ a N (goldOpP N) p
                  (goldOpP_squarefree N) (goldOpP_odd N)))
            * (Fchain (maxDepth (goldA2SieveW opQ a N (goldOpP N) p
                  (goldOpP_squarefree N) (goldOpP_odd N)))
                  (logRatio (opZ N) (cdiv (opD N) p))
                + opEps * CsharpB opEps * Real.exp 2
                    * hBJS (logRatio (opZ N) (cdiv (opD N) p)))
          + rosserRemainder (goldA2SieveW opQ a N (goldOpP N) p
              (goldOpP_squarefree N) (goldOpP_odd N)) ((opQ : ℝ) * (cdiv (opD N) p : ℝ)) := by
    intro p hp
    have hpf := hGsub hp
    have hp' := hpf
    rw [Finset.mem_filter, Finset.mem_Icc] at hp'
    exact le_trans (goldA2pW_le_siftedSumW opQ a N (goldOpP N) p (goldOpP_squarefree N)
        (goldOpP_odd N))
      (gold_A2_per_prime_W opQ a N (goldOpP N) p (opZ N) (cdiv (opD N) p) opEps (1 + opEps)
        ((opQ : ℝ)) (goldOpP_squarefree N) (goldOpP_odd N) (goldOpP_pz N) (goldOpP_plow N)
        hp'.2.one_lt.le (hcd2 N (by omega) p hpf) hQlevR hε hw0 (le_refl _)
        a12_eps_lt_249 (stepHypWPC_sharpB opEps hε.le a12_eps_le_1000)
        (h4_cond_of_base opEps (1 + opEps) hε.le (le_refl _)) (hcds N (by omega) p hpf))
  -- the density coefficient
  have hcoef : ∀ p ∈ S,
      (goldA2SieveW opQ a N (goldOpP N) p (goldOpP_squarefree N) (goldOpP_odd N)).totalMass
          * Salt.BrunLower.W (goldA2SieveW opQ a N (goldOpP N) p
              (goldOpP_squarefree N) (goldOpP_odd N))
        ≤ ((goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
              (goldOpP_odd N)).totalMass
            * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
                (goldOpP_squarefree N) (goldOpP_odd N)))
            * (1 / ((p : ℝ) - 1)) :=
    fun p _ => goldA2W_hcoef opQ a N (goldOpP N) p (goldOpP_squarefree N) (goldOpP_odd N)
  -- aggregate
  have hupper := twin_A2_upper
    (Λmass := (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
        (goldOpP_odd N)).totalMass)
    (V := Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
        (goldOpP_squarefree N) (goldOpP_odd N)))
    S (opZ N) (opD N)
    (fun p => goldA2pW opQ a N (goldOpP N) p)
    (fun p => (goldA2SieveW opQ a N (goldOpP N) p (goldOpP_squarefree N)
        (goldOpP_odd N)).totalMass
        * Salt.BrunLower.W (goldA2SieveW opQ a N (goldOpP N) p
            (goldOpP_squarefree N) (goldOpP_odd N)))
    (fun p => rosserRemainder (goldA2SieveW opQ a N (goldOpP N) p
        (goldOpP_squarefree N) (goldOpP_odd N)) ((opQ : ℝ) * (cdiv (opD N) p : ℝ)))
    (fun p => opEps * CsharpB opEps * Real.exp 2
        * hBJS (logRatio (opZ N) (cdiv (opD N) p)))
    (fun p => maxDepth (goldA2SieveW opQ a N (goldOpP N) p
        (goldOpP_squarefree N) (goldOpP_odd N)))
    hslacknn hper hcoef
  -- the aggregated BV row
  have hagg := hbvfun opQ a N (opZ N) (opY N) (opD N) (goldOpP N) opEps ((opQ : ℝ))
    (goldOpP_squarefree N) (goldOpP_odd N) (goldOpP_pz N) (goldOpP_plow N)
    (goldOpP_coprime_N N) hx4 hz3 hε hw0 hwz hQ1 (gold_opQ_coprime_P N) hQma
    (opf_QmPr N hw'z) hQlevR hD1 (hlev N (by omega) hQlog hyD) (hcl N (by omega) hQlog)
  rw [hdecomp]
  linarith [hupper, hagg]

end Salt.Goldbach
