/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WeightTrivia
import Salt.Chen.TripleCount
import Salt.Chen.SwitchConstant

/-!
# C5 — the Chen assembly (the capstone of the `chen` rung)

Design: `docs/blueprints/chen.md`, the C5 row.  This file composes the landed Chen corpus into
Chen's theorem in the **modulo-named-hypotheses** form (the honest current state): the razor

  `Σ_{n} Λ(n)·1_{prime∧sifted}·1_{P₂}(n+2)  ≥  A₁ − ½·Σ_p A_{2,p} − ½·A₃ − ½·strip`

is composed GENUINELY from Tao's Lemma 11 (`chen_weight_le_indicator`/`chen_weight_struct`, C4b),
the coprimality-cut prime-power strip (`stripSum_le`, C4b), and the switch count (`tripleSum`,
C3d), leaving only the three analytic main-term values as named inputs (`hA1`, `hA2`, `hA3`) and
the numeric ledger closure as `hledger`.

## The unsifted-A₃ verification (hPerE drops off the critical path)

The classical Chen switch sifts the switched triple-sequence `a_n = Σ 1_{n = p₁p₂p₃}` to push the
count down to `c̄ ≈ 0.363`.  Our C3d endpoint (`triple_count_le`) already lands the **unsifted**
count at `3·log(8/3)·log(3/2)/4 = 0.29827 < 0.363084` (`chen_switch_const_lt`).  Since the switch
carrier obeys the crude domination

  `A₃ = Σ_{n} Λ(n)·1_{sifted}·1_{T}(n+2)  ≤  log x · Σ_{n} a_n = log x · tripleSum`

(`triplePrimeSum_le` below, proved in FULL), and `0.298 < 0.363` clears the ledger line WITHOUT
any sieving of the switched sequence, the whole `hPerE`/keystone-2 (`general_BV_final`,
`PerEEngine`) debt is **off the critical path** for C5.  C5 never imports `GeneralBV`/`PerEEngine`.

## The ledger arithmetic (as landed)

At the frozen operating point (`z = x^{1/8}`, `y = x^{1/3}`, `D = x^{1/2−ε'}`, `ε_sieve = 1/10000`)
the numeric closure `hledger` is discharged by the two landed ledger lines:

* `two_log_three_sub_log_six_sub_cbar_pos : 0 < 2·log 3 − log 6 − 0.363084`  (C4a — the A₁/A₂
  main-term margin `2log3 − log6 = log(3/2) ≥ 2/5 > 0.363084`);
* `chen_switch_const_lt : 3·log(8/3)·log(3/2)/4 < 0.363084`  (C3d — the switch count clears the
  same line, with margin 17.85%).

Together `mainA1 − ½·mainA2 − ½·mainA3 > 0` at the carrier normalisation `Π₂x/(4 log z)`, with the
`o(x/log x)` strip and PNT-residual terms absorbed by the C0 ledger reserve.  Because the Rosser
chain VALUES (`fchain`/`Fchain`) are kept symbolic in the corpus (C1b′, the value certification, is
deferred), the connection of `mainA1`/`mainA2` to the literal numbers is threaded THROUGH the named
inputs — this is exactly the "modulo-named-hypotheses" boundary the mandate fixes.

## The named debt list (minimal)

`chen_positivity` takes, beyond the structural range conditions:

* `hPfull` — `P` is divisible by every prime `< z` (so a survivor's `n+2` has all prime factors
  `≥ z`; TRUE for `P = ∏_{p<z} p`, the sifting modulus).  This makes the razor's coprimality cut
  genuine and is the honest home of the ℚ-window `[w₀,z)` vs `[2,z)` bridge (paid by the caller in
  the choice of `P`);
* `hA1 : mainA1 ≤ A1primeSum` — the A₁ lower bound (the **prime-restricted** carrier, so a survivor
  is genuinely prime; consumes `twin_A1_lower` of C2a plus the prime-power strip);
* `hA2 : omegaPrimeSum ≤ mainA2` — the aggregated A₂ upper bound (consumes `twin_A2_upper` of C2b);
* `hA3 : Real.log x * tripleSum x z y ≤ mainA3` — the switch bound (consumes `triple_count_le` of
  C3d; the `hPerE` debt is off-path per the verification above);
* `hledger` — the numeric ledger closure (discharged by the two lines above at the operating point).

Everything else — the pointwise weight inequality, the four-way expansion, the strip bound, and the
unsifted-A₃ domination — is discharged in full here.  No `sorry`, no `native_decide`, no new axioms;
`hPerE`, `hτrec`, `htau`, `h4`, `hBV`, `hcoef`, `hBVagg` are the parametric debts owned by the
consumed nodes (C2a/C2b/C3d) and never re-opened here.
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the prime-restricted, sifted window carriers -/

/-- The keep indicator `1_{n prime ∧ (n+2, P) = 1}` (real-valued).  Restricting to prime `n`
makes a survivor genuinely prime (the P₂ headline needs `p.Prime`); the coprimality cut, together
with `hPfull`, forces every prime factor of `n+2` to be `≥ z`, so Chen's weight (C4b) applies. -/
noncomputable def keepR (P n : ℕ) : ℝ := if Nat.Prime n ∧ Nat.Coprime P (n + 2) then 1 else 0

lemma keepR_nonneg (P n : ℕ) : 0 ≤ keepR P n := by unfold keepR; split_ifs <;> norm_num

lemma keepR_le_one (P n : ℕ) : keepR P n ≤ 1 := by unfold keepR; split_ifs <;> norm_num

lemma keepR_eq_one_of_ne_zero {P n : ℕ} (h : keepR P n ≠ 0) : keepR P n = 1 := by
  unfold keepR at h ⊢
  by_cases hh : Nat.Prime n ∧ Nat.Coprime P (n + 2)
  · rw [if_pos hh]
  · rw [if_neg hh] at h; exact absurd rfl h

lemma keepR_eq_one_iff {P n : ℕ} : keepR P n = 1 ↔ Nat.Prime n ∧ Nat.Coprime P (n + 2) := by
  unfold keepR
  by_cases hh : Nat.Prime n ∧ Nat.Coprime P (n + 2)
  · rw [if_pos hh]; exact ⟨fun _ => hh, fun _ => rfl⟩
  · rw [if_neg hh]; exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hh⟩

/-- The A₁ carrier: the prime-restricted, sifted window `Λ`-mass `Σ_{p∈window, sifted} log p`. -/
noncomputable def A1primeSum (x P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n

/-- The aggregated A₂ carrier `Σ_p A_{2,p} = Σ_{n} Λ(n)·1_{keep}·ω_{≤y}(n+2)` (the `ω`-sum). -/
noncomputable def omegaPrimeSum (x P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * (omegaLe y (n + 2) : ℝ)

/-- The A₃ switch carrier `Σ_{n} Λ(n)·1_{keep}·1_T(n+2)` (Chen's triple pattern). -/
noncomputable def triplePrimeSum (x P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * tripleT y (n + 2)

/-- The prime-power strip carrier `Σ_{n} Λ(n)·1_{keep}·S(n+2)` (the coprimality-cut strip). -/
noncomputable def stripPrimeSum (x P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * (sqStrip y (n + 2) : ℝ)

/-- The P₂ carrier `Σ_{n} Λ(n)·1_{keep}·1_{P₂}(n+2)` — the quantity the razor lower-bounds. -/
noncomputable def p2PrimeSum (x z P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * p2Ind z (n + 2)

/-! ## Part B — the coprimality bridge (`sifted ⟹ factors ≥ z`) -/

/-- **The sifting bridge.**  If `P` is divisible by every prime `< z` and `(P, n+2) = 1`, then
every prime factor of `n+2` is `≥ z`.  (A prime factor `p < z` would divide both `P` and `n+2`,
contradicting coprimality.)  This is the honest home of the small-prime `ℚ`-window bridge: a caller
supplies `hPfull` by choosing `P = ∏_{p<z} p`. -/
theorem factors_ge_z_of_sift {P z n : ℕ} (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hcop : Nat.Coprime P (n + 2)) : ∀ p ∈ (n + 2).primeFactors, z ≤ p := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ (n + 2) := Nat.dvd_of_mem_primeFactors hp
  by_contra hlt
  rw [not_le] at hlt
  have hpP : p ∣ P := hPfull p hpp hlt
  have hdvd1 : p ∣ Nat.gcd P (n + 2) := Nat.dvd_gcd hpP hpd
  rw [Nat.Coprime] at hcop
  rw [hcop] at hdvd1
  exact hpp.ne_one (Nat.dvd_one.mp hdvd1)

/-! ## Part C — the razor reduction (Tao Lemma 11, summed) -/

/-- **The razor reduction (38).**  Composing Chen's pointwise weight inequality (C4b's
`chen_weight_le_indicator ∘ chen_weight_struct`) over the prime-restricted, sifted window:

  `A₁ − ½·Σ_p A_{2,p} − ½·A₃ − ½·strip  ≤  Σ_{n} Λ(n)·1_{keep}·1_{P₂}(n+2)`.

The four carriers are the linear pieces of Chen's real-valued weight `1 − ½ω − ½·1_T − ½S`;
Tao's Lemma 11 dominates that weight by `1_{P₂}` at every window point where `n+2` is sifted
(factors `≥ z`, via `hPfull`) and `< (y+1)³`. -/
theorem razor_reduction {x z P y : ℕ} (hx : 2 ≤ x) (hyx : x < (y + 1) ^ 3)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P) :
    A1primeSum x P - omegaPrimeSum x P y / 2 - triplePrimeSum x P y / 2 - stripPrimeSum x P y / 2
      ≤ p2PrimeSum x z P := by
  -- pointwise: `Λ·keep·chenWeight ≤ Λ·keep·p2Ind`
  have hpt : ∀ n ∈ twinWindow x,
      vonMangoldt n * keepR P n * chenWeight y (n + 2)
        ≤ vonMangoldt n * keepR P n * p2Ind z (n + 2) := by
    intro n hn
    by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2)
    · have hcop := factors_ge_z_of_sift hPfull hk.2
      rw [twinWindow, Finset.mem_Icc] at hn
      have hn2 : 2 ≤ n + 2 := by omega
      have hub : n + 2 ≤ x := by omega
      have hmy : n + 2 < (y + 1) ^ 3 := lt_of_le_of_lt hub hyx
      have hstruct : ¬ IsP2 z (n + 2) →
          2 ≤ (omegaLe y (n + 2) : ℝ) + tripleT y (n + 2) + (sqStrip y (n + 2) : ℝ) :=
        fun hnp2 => chen_weight_struct hn2 hcop hmy hnp2
      have hle := chen_weight_le_indicator hstruct
      exact mul_le_mul_of_nonneg_left hle (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n))
    · have hkeep0 : keepR P n = 0 := by unfold keepR; rw [if_neg hk]
      simp [hkeep0]
  have hsum := Finset.sum_le_sum hpt
  -- the RHS sum is `p2PrimeSum`
  have hRHS : ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * p2Ind z (n + 2) = p2PrimeSum x z P :=
    rfl
  -- expand the LHS into the four carriers
  have hterm : ∀ n, vonMangoldt n * keepR P n * chenWeight y (n + 2)
      = vonMangoldt n * keepR P n
        - vonMangoldt n * keepR P n * (omegaLe y (n + 2) : ℝ) / 2
        - vonMangoldt n * keepR P n * tripleT y (n + 2) / 2
        - vonMangoldt n * keepR P n * (sqStrip y (n + 2) : ℝ) / 2 := by
    intro n; rw [chenWeight]; ring
  rw [Finset.sum_congr rfl (fun n _ => hterm n)] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div] at hsum
  rw [hRHS] at hsum
  exact hsum

/-! ## Part D — the strip bound (C4b, discharged) -/

/-- **The prime-power strip is negligible.**  `stripPrimeSum ≤ log x · x/(z−1) ≈ x^{7/8} log x`.
On a sifted `n+2` the weight's native strip count equals the `z`-restricted count
(`sqStrip_eq_sqStripZ`), so `stripPrimeSum` is dominated termwise by the C4b sum `stripSum_le`
bounds. -/
theorem stripPrimeSum_le {x z P y : ℕ} (hx : 2 ≤ x) (hz : 2 ≤ z)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P) :
    stripPrimeSum x P y ≤ Real.log x * (x : ℝ) / ((z : ℝ) - 1) := by
  rw [stripPrimeSum]
  refine le_trans ?_ (stripSum_le (y := y) hx hz)
  apply Finset.sum_le_sum
  intro n _
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2)
  · have hkeep1 : keepR P n = 1 := by unfold keepR; rw [if_pos hk]
    have hcop := factors_ge_z_of_sift hPfull hk.2
    have hn0 : n + 2 ≠ 0 := by omega
    have heq := sqStrip_eq_sqStripZ (z := z) (y := y) hn0 hcop
    rw [hkeep1, mul_one, heq]
  · have hkeep0 : keepR P n = 0 := by unfold keepR; rw [if_neg hk]
    rw [hkeep0]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg vonMangoldt_nonneg (by positivity)

/-! ## Part E — the unsifted-A₃ bound (C3d, discharged; hPerE off the critical path) -/

/-- If a window point `n` is prime and sifted, and `n+2` matches Chen's triple pattern, then it is
one of the admissible triples counted by `aCount` — hence `aCount ≥ 1`.  The switch's sieve is
never used: the admissibility `z ≤ p₁` comes from the coprimality cut (`hPfull`), not from any
distribution estimate on the switched sequence. -/
theorem aCount_ge_one_of {x z y P n : ℕ} (hx : 2 ≤ x) (hn : n ∈ twinWindow x)
    (hk : Nat.Prime n ∧ Nat.Coprime P (n + 2)) (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (htp : TripleP y (n + 2)) : (1 : ℝ) ≤ aCount x z y n := by
  obtain ⟨p₁, p₂, p₃, hp1, hp2, hp3, hprod, hp1y, hyp2, hp23⟩ := htp
  have hn2pos : 0 < n + 2 := by omega
  -- p₁ ∣ n+2, hence z ≤ p₁ by the sifting bridge
  have hp1dvd : p₁ ∣ (n + 2) := ⟨p₂ * p₃, by rw [hprod]; ring⟩
  have hp2dvd : p₂ ∣ (n + 2) := ⟨p₁ * p₃, by rw [hprod]; ring⟩
  have hp3dvd : p₃ ∣ (n + 2) := ⟨p₁ * p₂, by rw [hprod]; ring⟩
  have hp1mem : p₁ ∈ (n + 2).primeFactors := Nat.mem_primeFactors.mpr ⟨hp1, hp1dvd, by omega⟩
  have hzp1 : z ≤ p₁ := factors_ge_z_of_sift hPfull hk.2 p₁ hp1mem
  -- window bounds
  rw [twinWindow, Finset.mem_Icc] at hn
  have hlo : x / 2 + 2 ≤ n + 2 := by omega
  have hhi : n + 2 ≤ x := by omega
  have hp1x : p₁ ≤ x := le_trans (Nat.le_of_dvd hn2pos hp1dvd) hhi
  have hp2x : p₂ ≤ x := le_trans (Nat.le_of_dvd hn2pos hp2dvd) hhi
  have hp3x : p₃ ≤ x := le_trans (Nat.le_of_dvd hn2pos hp3dvd) hhi
  -- membership in the admissible-triple set
  have ht : (p₁, p₂, p₃) ∈ tripleSet x z y := by
    rw [tripleSet, Finset.mem_filter]
    refine ⟨?_, hzp1, hp1y, hyp2, hp23, hp1, hp2, hp3, ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_product]
      refine ⟨?_, ?_, ?_⟩ <;> rw [Finset.mem_Icc]
      · exact ⟨hp1.one_lt.le, hp1x⟩
      · exact ⟨hp2.one_lt.le, hp2x⟩
      · exact ⟨hp3.one_lt.le, hp3x⟩
    · show x / 2 + 2 ≤ prod3 (p₁, p₂, p₃)
      rw [prod3]; rw [← hprod]; exact hlo
    · show prod3 (p₁, p₂, p₃) ≤ x
      rw [prod3]; rw [← hprod]; exact hhi
  have hmem : (p₁, p₂, p₃) ∈ (tripleSet x z y).filter (fun t => prod3 t = n + 2) := by
    rw [Finset.mem_filter]
    exact ⟨ht, by show prod3 (p₁, p₂, p₃) = n + 2; rw [prod3, ← hprod]⟩
  rw [aCount]
  have hcard : 0 < ((tripleSet x z y).filter (fun t => prod3 t = n + 2)).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  exact_mod_cast hcard

/-- **The unsifted-A₃ domination.**  `A₃ = triplePrimeSum ≤ log x · tripleSum` — the switch carrier
is bounded by `log x` times the *unsifted* C3d triple count.  This is the composition that keeps
`hPerE`/keystone-2 off the critical path: the switched-sequence sieve is never applied, because the
C3d count (`0.298`) is already below the ledger line (`0.363`). -/
theorem triplePrimeSum_le {x z P y : ℕ} (hx : 2 ≤ x)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P) :
    triplePrimeSum x P y ≤ Real.log x * tripleSum x z y := by
  have hlogx : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  rw [triplePrimeSum, tripleSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  -- Λ(n) ≤ log x
  have hnmem := hn
  rw [twinWindow, Finset.mem_Icc] at hnmem
  have hn1 : 1 ≤ n := by omega
  have hnx : n ≤ x := by omega
  have hΛle : vonMangoldt n ≤ Real.log x := by
    refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
    · exact_mod_cast hn1
    · exact_mod_cast hnx
  -- keep·tripleT ≤ aCount
  have hkt_nonneg : 0 ≤ keepR P n * tripleT y (n + 2) :=
    mul_nonneg (keepR_nonneg P n) (tripleT_nonneg y (n + 2))
  have hkt_le : keepR P n * tripleT y (n + 2) ≤ aCount x z y n := by
    by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2)
    · have hkeep1 : keepR P n = 1 := by unfold keepR; rw [if_pos hk]
      rw [hkeep1, one_mul]
      by_cases htp : TripleP y (n + 2)
      · rw [tripleT_eq_one htp]
        exact aCount_ge_one_of hx hn hk hPfull htp
      · unfold tripleT; rw [if_neg htp]; rw [aCount]; positivity
    · have hkeep0 : keepR P n = 0 := by unfold keepR; rw [if_neg hk]
      rw [hkeep0, zero_mul, aCount]; positivity
  -- assemble: Λ·(keep·T) ≤ log x·(keep·T) ≤ log x·aCount
  calc vonMangoldt n * keepR P n * tripleT y (n + 2)
      = vonMangoldt n * (keepR P n * tripleT y (n + 2)) := by ring
    _ ≤ Real.log x * (keepR P n * tripleT y (n + 2)) :=
        mul_le_mul_of_nonneg_right hΛle hkt_nonneg
    _ ≤ Real.log x * aCount x z y n := mul_le_mul_of_nonneg_left hkt_le hlogx

/-! ## Part F — the finite-`x` positivity core (`chen_positivity`) -/

/-- **`chen_positivity` — the finite-`x` core (the razor, fully composed).**  At the operating
point, the prime-restricted, sifted P₂-carrier is strictly positive, given the three analytic
main-term bounds (`hA1`, `hA2`, `hA3`) and the numeric ledger closure (`hledger`).  The structural
razor (`razor_reduction`), the strip bound (`stripPrimeSum_le`, C4b), and the unsifted-A₃
domination (`triplePrimeSum_le`, C3d) are all discharged in full.

The named debts are minimal and honest:
* `hA1 : mainA1 ≤ A1primeSum x P` — A₁ lower bound (C2a `twin_A1_lower` + prime-power strip);
* `hA2 : omegaPrimeSum x P y ≤ mainA2` — A₂ upper bound (C2b `twin_A2_upper`);
* `hA3 : Real.log x * tripleSum x z y ≤ mainA3` — switch bound (C3d `triple_count_le`);
* `hledger : 0 < mainA1 − ½·mainA2 − ½·mainA3 − ½·(log x · x/(z−1))` — the C0 ledger closure. -/
theorem chen_positivity {x z P y : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z) (hyx : x < (y + 1) ^ 3)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : Real.log x * tripleSum x z y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    0 < p2PrimeSum x z P := by
  have hred := razor_reduction hx hyx hPfull
  have hS := stripPrimeSum_le (y := y) hx hz hPfull
  have hT := triplePrimeSum_le (z := z) (y := y) hx hPfull
  have hTb : triplePrimeSum x P y ≤ mainA3 := le_trans hT hA3
  linarith [hred, hA1, hA2, hTb, hS, hledger]

/-! ## Part G — the survivor and the infinitude headline -/

/-- `IsP2` is monotone-decreasing in the size threshold: a P₂ with both factors `≥ z` is a P₂ with
both factors `≥ z'` whenever `z' ≤ z`.  Lets a survivor's `IsP2 z` (with `z = x^{1/8}`) collapse to
the genuine P₂ property `IsP2 2` (prime, or a product of two primes). -/
theorem isP2_mono {z z' m : ℕ} (h : z' ≤ z) (hm : IsP2 z m) : IsP2 z' m := by
  rcases hm with hp | ⟨p, q, hpp, hqp, hmpq, hzp, hzq⟩
  · exact Or.inl hp
  · exact Or.inr ⟨p, q, hpp, hqp, hmpq, le_trans h hzp, le_trans h hzq⟩

/-- **The Chen survivor.**  From the positivity of the P₂-carrier there is a prime `n` in the window
`[x/2, x−2]` with `n+2` a genuine P₂ (prime, or a product of two primes).  Since `n ≥ x/2`, the
survivor is large. -/
theorem chen_survivor {x z P y : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z) (hyx : x < (y + 1) ^ 3)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : Real.log x * tripleSum x z y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    ∃ n : ℕ, x / 2 ≤ n ∧ n.Prime ∧ IsP2 2 (n + 2) := by
  have hpos := chen_positivity hx hz hyx hPfull hA1 hA2 hA3 hledger
  have hpos' : 0 < ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * p2Ind z (n + 2) := hpos
  -- a strictly positive term exists
  obtain ⟨n, hn, hterm⟩ : ∃ n ∈ twinWindow x, 0 < vonMangoldt n * keepR P n * p2Ind z (n + 2) := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    exact absurd (Finset.sum_nonpos hcon) (not_le.mpr hpos')
  -- decode the term: keep = 1 (prime ∧ sifted), p2Ind = 1 (IsP2 z)
  have hkeepne : keepR P n ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  have hkeep1 : keepR P n = 1 := keepR_eq_one_of_ne_zero hkeepne
  obtain ⟨hprime, _hcop⟩ := keepR_eq_one_iff.mp hkeep1
  have hp2ne : p2Ind z (n + 2) ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  have hIsP2z : IsP2 z (n + 2) := by
    unfold p2Ind at hp2ne
    by_contra hnp2
    rw [if_neg hnp2] at hp2ne
    exact hp2ne rfl
  have hlo : x / 2 ≤ n := by rw [twinWindow, Finset.mem_Icc] at hn; exact hn.1
  exact ⟨n, hlo, hprime, isP2_mono hz hIsP2z⟩

/-- **`chen_of_hypotheses` — the Chen headline (modulo the named analytic debts).**  Given that the
`chen_positivity` input package is available at arbitrarily large operating points `x` (bundled as
`H`: for every threshold `X` there is an `x` with `X ≤ x/2` and the full razor inputs), there are
infinitely many primes `p` with `p + 2` a P₂ (prime, or a product of two primes).

This is Chen's theorem in the honest current form: the analytic values (`mainA1`/`mainA2`/`mainA3`)
and the ledger closure are threaded through `H`, which packages the outputs of C2a/C2b/C3d at the
operating point.  The infinitude is genuine (`Set.infinite_of_forall_exists_gt`): each operating
point yields a prime survivor `p ≥ x/2 ≥ X`, so `X → ∞` gives infinitely many. -/
theorem chen_of_hypotheses
    (H : ∀ X : ℕ, ∃ (x z P y : ℕ) (mainA1 mainA2 mainA3 : ℝ),
        X ≤ x / 2 ∧ 2 ≤ x ∧ 2 ≤ z ∧ x < (y + 1) ^ 3 ∧
        (∀ q, q.Prime → q < z → q ∣ P) ∧
        mainA1 ≤ A1primeSum x P ∧
        omegaPrimeSum x P y ≤ mainA2 ∧
        Real.log x * tripleSum x z y ≤ mainA3 ∧
        0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨x, z, P, y, mainA1, mainA2, mainA3,
    hXx, hx, hz, hyx, hPfull, hA1, hA2, hA3, hledger⟩ := H (a + 1)
  obtain ⟨n, hlo, hprime, hIsP2⟩ := chen_survivor hx hz hyx hPfull hA1 hA2 hA3 hledger
  refine ⟨n, ⟨hprime, hIsP2⟩, ?_⟩
  omega

end Salt.Chen
