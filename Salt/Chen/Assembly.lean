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

## The A₃ route (58c rewrite — the honest post-#41/#53 narrative)

⚠ HISTORY: this section originally claimed the **unsifted** count model closed the ledger
(`0.29827 < 0.363084` via the crude domination `A₃ ≤ log x · tripleSum`, `triplePrimeSum_le`
below).  CATCH #41 (2026-07-13) discredited that route: the `Λ(n) ≤ log x` step drops Λ's prime
support, so `log x · tripleSum` is `x`-scale against the `x/log x`-scale main terms — TRUE but
NOT LOAD-BEARING; no ledger closes through it.  `triplePrimeSum_le` is kept below as a documented
true lemma only.

The honest route, as landed (H-AMENDMENT 1 + the catch-#53 count):
* the `hA3` slot takes the Λ-carrier `triplePrimeSum ≤ mainA3` DIRECTLY;
* `mainA3` is supplied by the **switched-sequence sieve** (`mainA3_of_block_remainders_W`,
  SwitchW.lean) at the windowed/cutoff BV (`hBVblocksW`, discharged at the operating point);
* the count input is the `log(N/p₁p₂)`-WEIGHTED count at the manifest `c̄/2` constant
  (`tripleSum_le_cbar_final`, CountFinal.lean — BJS Lemma 52's honest form; the old unsifted
  `0.29827` model was 3.3× loose per catch #53 and is superseded);
* the ledger closes through the certified razor (`razor_scalar_margin`, M = 0.012151) with the
  error bundle proven ≤ 1/200 (FinLed3.lean).
The full discharge map: `docs/blueprints/chen.md` (H-AMENDMENT 2) and the flags ledger
(#41, #49, #53, and the endgame arc #59–#78).

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

## H-AMENDMENT 2 — the W-trick family (`_W`, 2026-07-14)

★ CATCH #65 (kernel record: `Salt/Chen/Headline.lean`) tore the original H-package at the
`hPfull`/`hA1` seam: no modulus `P` can carry every prime `< z` (the razor's need) AND the A₁
suppliers' structural constraints (`ν(2) = 1/φ(2) = 1` excludes `2` from every sieve modulus; the
Rosser guard excludes `[3, w₀)`).  The ratified repair (`docs/blueprints/chen.md`, H-AMENDMENT 2,
D1–D8 with gate corrections C1–C7) restricts every razor carrier to a residue class
`n ≡ a (mod Q)`, so small primes are excluded from `n+2` by AP-MEMBERSHIP
(`gcd(n+2, Q) = gcd(a+2, Q) = 1`), not by sieving.  Parts H–L below add the W-family alongside
the original (D1):

* `keepW Q a P n` — the W-keep indicator; the five W-carriers (`A1primeSumW` … `p2PrimeSumW`)
  mirror the landed five at `keepW`;
* `factors_ge_z_of_sift_W` — the split bridge: `hPfull` splits into `hQfull` (every prime `< w'`
  divides `Q`) + `hPfull'` (every prime in `[w', z)` divides `P`) + `hQa2` (`Coprime Q (a+2)`);
  no gap at the `w'` boundary (gate surface 1);
* the `_W` mirrors `razor_reduction_W`/`stripPrimeSum_le_W`/`aCount_ge_one_of_W`/
  `chen_positivity_W`/`chen_survivor_W`, and the amended headline consumer
  `chen_of_hypotheses_W` — H_W gains `Q a w'` in the ∃ with the three split hypotheses replacing
  `hPfull`;
* `residue_witness` — the D1 residue `a = Q − 1` has `gcd(Q, a+2) = gcd(Q, Q+1) = 1` for free.

Supplier expectations (post-gate, C1-corrected): the `hA1`/`hA2`/`hA3` slots of the W-family are
re-supplied at the AP-restricted instances by the W-supplier nodes (A1W/A2W′/A3W — support
filtered by `Q ∣ n+1` at `a = Q − 1`; A2W′ is a per-prime instance CONSTRUCTION per C5), NOT
majorized by the unrestricted carriers (D2: the ledger normalizes by the AP-scale `X_W/φ(Q)`).
Their `h4` slot is CONDITIONED per catch #66 (node H4C); `h4` lives in the suppliers, never in
this file.  At instantiation (GLU-2W): `w' = w0N ε ≥ 3`, `Q = Qval ε`, `a = Q − 1`
(`Salt/Chen/Hyp4.lean`).

The OLD `keepR` family below stays intact and load-bearing for the record: catch #65's kernel
theorems (`catch65_slot_torn`/`catch65_no_H_at_odd_P`, Headline.lean) are stated against it.
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
is bounded by `log x` times the *unsifted* C3d triple count.  ⚠ CATCH #41 (2026-07-13): this bound
is TRUE but NOT LOAD-BEARING — `log x · tripleSum` is `x`-scale against the `x/log x`-scale main
terms (the `Λ(n) ≤ log x` step drops `Λ`'s prime support), so no ledger closes through it.  The
assembly now takes the honest Λ-carrier `triplePrimeSum ≤ mainA3` directly (H-amendment 1); the
switched-sequence sieve (SW-A₃) discharges it.  Kept as a documented true lemma. -/
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

The named debts are minimal and honest (hA3 amended per catch #41 — H-AMENDMENT 1, 2026-07-13:
the slot takes the Λ-carrier itself; the previous `log x · tripleSum` shape was undischargeable):
* `hA1 : mainA1 ≤ A1primeSum x P` — A₁ lower bound (C2a `twin_A1_lower` + prime-power strip);
* `hA2 : omegaPrimeSum x P y ≤ mainA2` — A₂ upper bound (C2b `twin_A2_upper`);
* `hA3 : triplePrimeSum x P y ≤ mainA3` — the switch bound (the SW-A₃ switched-sequence sieve);
* `hledger : 0 < mainA1 − ½·mainA2 − ½·mainA3 − ½·(log x · x/(z−1))` — the C0 ledger closure.

⚠ CATCH #65 (2026-07-14): torn at hPfull/hA1 — kernel record in Headline.lean; superseded by
`chen_positivity_W` (the `_W` family, H-AMENDMENT 2). -/
theorem chen_positivity {x z P y : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z) (hyx : x < (y + 1) ^ 3)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : triplePrimeSum x P y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    0 < p2PrimeSum x z P := by
  have hred := razor_reduction hx hyx hPfull
  have hS := stripPrimeSum_le (y := y) hx hz hPfull
  linarith [hred, hA1, hA2, hA3, hS, hledger]

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
    (hA3 : triplePrimeSum x P y ≤ mainA3)
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
point yields a prime survivor `p ≥ x/2 ≥ X`, so `X → ∞` gives infinitely many.

⚠ CATCH #65 (2026-07-14): torn at hPfull/hA1 — kernel record in Headline.lean; superseded by
`chen_of_hypotheses_W` (the `_W` family, H-AMENDMENT 2). -/
theorem chen_of_hypotheses
    (H : ∀ X : ℕ, ∃ (x z P y : ℕ) (mainA1 mainA2 mainA3 : ℝ),
        X ≤ x / 2 ∧ 2 ≤ x ∧ 2 ≤ z ∧ x < (y + 1) ^ 3 ∧
        (∀ q, q.Prime → q < z → q ∣ P) ∧
        mainA1 ≤ A1primeSum x P ∧
        omegaPrimeSum x P y ≤ mainA2 ∧
        triplePrimeSum x P y ≤ mainA3 ∧
        0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨x, z, P, y, mainA1, mainA2, mainA3,
    hXx, hx, hz, hyx, hPfull, hA1, hA2, hA3, hledger⟩ := H (a + 1)
  obtain ⟨n, hlo, hprime, hIsP2⟩ := chen_survivor hx hz hyx hPfull hA1 hA2 hA3 hledger
  refine ⟨n, ⟨hprime, hIsP2⟩, ?_⟩
  omega

/-! ## Part H — the W-trick carriers (H-AMENDMENT 2, D1)

The W-keep indicator adds the residue-class membership `n ≡ a (mod Q)` to `keepR`'s conjunction;
the five carriers mirror Parts A's five at `keepW`.  The AP-membership is what pays the small-prime
range `[2, w')` in the split bridge (Part I): a kept point has `gcd(n+2, Q) = gcd(a+2, Q) = 1`. -/

/-- The W-keep indicator `1_{n prime ∧ (n+2, P) = 1 ∧ n ≡ a (mod Q)}` (real-valued).  The residue
membership replaces small-prime sieving: together with `hQfull` and `hQa2` it forces every prime
factor `< w'` of `n+2` out (Part I), while the coprimality cut handles `[w', z)` via `hPfull'`. -/
noncomputable def keepW (Q a P n : ℕ) : ℝ :=
  if Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q then 1 else 0

lemma keepW_nonneg (Q a P n : ℕ) : 0 ≤ keepW Q a P n := by unfold keepW; split_ifs <;> norm_num

lemma keepW_le_one (Q a P n : ℕ) : keepW Q a P n ≤ 1 := by unfold keepW; split_ifs <;> norm_num

lemma keepW_eq_one_of_ne_zero {Q a P n : ℕ} (h : keepW Q a P n ≠ 0) : keepW Q a P n = 1 := by
  unfold keepW at h ⊢
  by_cases hh : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q
  · rw [if_pos hh]
  · rw [if_neg hh] at h; exact absurd rfl h

lemma keepW_eq_one_iff {Q a P n : ℕ} :
    keepW Q a P n = 1 ↔ Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q := by
  unfold keepW
  by_cases hh : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q
  · rw [if_pos hh]; exact ⟨fun _ => hh, fun _ => rfl⟩
  · rw [if_neg hh]; exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hh⟩

/-- The W-restricted A₁ carrier: the prime-restricted, sifted, AP-restricted window `Λ`-mass. -/
noncomputable def A1primeSumW (Q a x P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n

/-- The W-restricted aggregated A₂ carrier `Σ_{n≡a(Q)} Λ(n)·1_{keepW}·ω_{≤y}(n+2)`. -/
noncomputable def omegaPrimeSumW (Q a x P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * (omegaLe y (n + 2) : ℝ)

/-- The W-restricted A₃ switch carrier `Σ_{n≡a(Q)} Λ(n)·1_{keepW}·1_T(n+2)`. -/
noncomputable def triplePrimeSumW (Q a x P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * tripleT y (n + 2)

/-- The W-restricted prime-power strip carrier `Σ_{n≡a(Q)} Λ(n)·1_{keepW}·S(n+2)`. -/
noncomputable def stripPrimeSumW (Q a x P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * (sqStrip y (n + 2) : ℝ)

/-- The W-restricted P₂ carrier — the quantity the W-razor lower-bounds. -/
noncomputable def p2PrimeSumW (Q a x z P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * p2Ind z (n + 2)

/-! ## Part I — the split sifting bridge (D1; gate surface 1: no `w'`-boundary gap) -/

/-- **The split sifting bridge.**  `hPfull` splits at `w'`: if every prime `< w'` divides `Q`
(`hQfull`), every prime in `[w', z)` divides `P` (`hPfull'`), and `(Q, a+2) = 1` (`hQa2`), then at
a kept point — `(P, n+2) = 1` and `n ≡ a (mod Q)` — every prime factor of `n+2` is `≥ z`.

For a prime `p ∣ n+2` with `p < z`: if `p < w'` then `p ∣ Q`, and the mod-`Q` transfer
`n % Q = a % Q ⟹ (n+2) % Q = (a+2) % Q` puts `p ∣ a+2` (via `Nat.dvd_mod_iff` twice), so
`p ∣ gcd(Q, a+2) = 1` — impossible; if `w' ≤ p < z` then `p ∣ P` against `(P, n+2) = 1` as in
`factors_ge_z_of_sift`.  Every `p < z` falls in one of the two ranges — no boundary gap; in
particular `p = 2` is excluded by `hQfull` at the instantiation `w' = w0N ε ≥ 3`. -/
theorem factors_ge_z_of_sift_W {Q a P w' z n : ℕ}
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2))
    (hcop : Nat.Coprime P (n + 2)) (hmod : n % Q = a % Q) :
    ∀ p ∈ (n + 2).primeFactors, z ≤ p := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ (n + 2) := Nat.dvd_of_mem_primeFactors hp
  by_contra hlt
  rw [not_le] at hlt
  by_cases hw : p < w'
  · -- small range [2, w'): p ∣ Q, and the mod-Q transfer puts p inside gcd (Q, a+2) = 1
    have hpQ : p ∣ Q := hQfull p hpp hw
    have hmod2 : (n + 2) % Q = (a + 2) % Q := by
      conv_lhs => rw [Nat.add_mod, hmod, ← Nat.add_mod]
    have hpn2 : p ∣ (n + 2) % Q := (Nat.dvd_mod_iff hpQ).mpr hpd
    rw [hmod2] at hpn2
    have hpa2 : p ∣ (a + 2) := (Nat.dvd_mod_iff hpQ).mp hpn2
    have hdvd1 : p ∣ Nat.gcd Q (a + 2) := Nat.dvd_gcd hpQ hpa2
    rw [Nat.Coprime] at hQa2
    rw [hQa2] at hdvd1
    exact hpp.ne_one (Nat.dvd_one.mp hdvd1)
  · -- sieve range [w', z): p ∣ P against (P, n+2) = 1
    rw [not_lt] at hw
    have hpP : p ∣ P := hPfull' p hpp hw hlt
    have hdvd1 : p ∣ Nat.gcd P (n + 2) := Nat.dvd_gcd hpP hpd
    rw [Nat.Coprime] at hcop
    rw [hcop] at hdvd1
    exact hpp.ne_one (Nat.dvd_one.mp hdvd1)

/-! ## Part J — the W-mirrors of the razor chain

Near-verbatim mirrors of Parts C/D/E: the landed proofs consume `hPfull` ONLY through
`factors_ge_z_of_sift` at kept points, so swapping in the split bridge is the whole change. -/

/-- **The W-razor reduction.**  `razor_reduction` at `keepW`, with the split bridge in place of
`hPfull`: Tao's Lemma 11 dominates Chen's weight by `1_{P₂}` at every AP-restricted kept point. -/
theorem razor_reduction_W {x z P y Q a w' : ℕ} (hx : 2 ≤ x) (hyx : x < (y + 1) ^ 3)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) :
    A1primeSumW Q a x P - omegaPrimeSumW Q a x P y / 2 - triplePrimeSumW Q a x P y / 2
      - stripPrimeSumW Q a x P y / 2 ≤ p2PrimeSumW Q a x z P := by
  -- pointwise: `Λ·keepW·chenWeight ≤ Λ·keepW·p2Ind`
  have hpt : ∀ n ∈ twinWindow x,
      vonMangoldt n * keepW Q a P n * chenWeight y (n + 2)
        ≤ vonMangoldt n * keepW Q a P n * p2Ind z (n + 2) := by
    intro n hn
    by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q
    · have hcop := factors_ge_z_of_sift_W hQfull hPfull' hQa2 hk.2.1 hk.2.2
      rw [twinWindow, Finset.mem_Icc] at hn
      have hn2 : 2 ≤ n + 2 := by omega
      have hub : n + 2 ≤ x := by omega
      have hmy : n + 2 < (y + 1) ^ 3 := lt_of_le_of_lt hub hyx
      have hstruct : ¬ IsP2 z (n + 2) →
          2 ≤ (omegaLe y (n + 2) : ℝ) + tripleT y (n + 2) + (sqStrip y (n + 2) : ℝ) :=
        fun hnp2 => chen_weight_struct hn2 hcop hmy hnp2
      have hle := chen_weight_le_indicator hstruct
      exact mul_le_mul_of_nonneg_left hle
        (mul_nonneg vonMangoldt_nonneg (keepW_nonneg Q a P n))
    · have hkeep0 : keepW Q a P n = 0 := by unfold keepW; rw [if_neg hk]
      simp [hkeep0]
  have hsum := Finset.sum_le_sum hpt
  -- the RHS sum is `p2PrimeSumW`
  have hRHS : ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * p2Ind z (n + 2)
      = p2PrimeSumW Q a x z P := rfl
  -- expand the LHS into the four carriers
  have hterm : ∀ n, vonMangoldt n * keepW Q a P n * chenWeight y (n + 2)
      = vonMangoldt n * keepW Q a P n
        - vonMangoldt n * keepW Q a P n * (omegaLe y (n + 2) : ℝ) / 2
        - vonMangoldt n * keepW Q a P n * tripleT y (n + 2) / 2
        - vonMangoldt n * keepW Q a P n * (sqStrip y (n + 2) : ℝ) / 2 := by
    intro n; rw [chenWeight]; ring
  rw [Finset.sum_congr rfl (fun n _ => hterm n)] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div] at hsum
  rw [hRHS] at hsum
  exact hsum

/-- **The W prime-power strip bound.**  `stripPrimeSum_le` at `keepW`: the AP-restricted strip
carrier is dominated termwise by the same C4b sum, via the split bridge at kept points. -/
theorem stripPrimeSum_le_W {x z P y Q a w' : ℕ} (hx : 2 ≤ x) (hz : 2 ≤ z)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) :
    stripPrimeSumW Q a x P y ≤ Real.log x * (x : ℝ) / ((z : ℝ) - 1) := by
  rw [stripPrimeSumW]
  refine le_trans ?_ (stripSum_le (y := y) hx hz)
  apply Finset.sum_le_sum
  intro n _
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q
  · have hkeep1 : keepW Q a P n = 1 := by unfold keepW; rw [if_pos hk]
    have hcop := factors_ge_z_of_sift_W hQfull hPfull' hQa2 hk.2.1 hk.2.2
    have hn0 : n + 2 ≠ 0 := by omega
    have heq := sqStrip_eq_sqStripZ (z := z) (y := y) hn0 hcop
    rw [hkeep1, mul_one, heq]
  · have hkeep0 : keepW Q a P n = 0 := by unfold keepW; rw [if_neg hk]
    rw [hkeep0]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg vonMangoldt_nonneg (by positivity)

/-- **The W triple-membership bound.**  `aCount_ge_one_of` at `keepW`: a kept, AP-restricted
window point matching Chen's triple pattern is an admissible triple, hence `aCount ≥ 1`.  The
admissibility `z ≤ p₁` comes from the split bridge, not from any sieving of the switched
sequence.  (Mirrored for the A3W supplier node; the assembly's own A₃ slot takes the Λ-carrier
`triplePrimeSumW ≤ mainA3` directly, per H-AMENDMENT 1.) -/
theorem aCount_ge_one_of_W {x z y P Q a w' n : ℕ} (hx : 2 ≤ x) (hn : n ∈ twinWindow x)
    (hk : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2))
    (htp : TripleP y (n + 2)) : (1 : ℝ) ≤ aCount x z y n := by
  obtain ⟨p₁, p₂, p₃, hp1, hp2, hp3, hprod, hp1y, hyp2, hp23⟩ := htp
  have hn2pos : 0 < n + 2 := by omega
  -- p₁ ∣ n+2, hence z ≤ p₁ by the split sifting bridge
  have hp1dvd : p₁ ∣ (n + 2) := ⟨p₂ * p₃, by rw [hprod]; ring⟩
  have hp2dvd : p₂ ∣ (n + 2) := ⟨p₁ * p₃, by rw [hprod]; ring⟩
  have hp3dvd : p₃ ∣ (n + 2) := ⟨p₁ * p₂, by rw [hprod]; ring⟩
  have hp1mem : p₁ ∈ (n + 2).primeFactors := Nat.mem_primeFactors.mpr ⟨hp1, hp1dvd, by omega⟩
  have hzp1 : z ≤ p₁ := factors_ge_z_of_sift_W hQfull hPfull' hQa2 hk.2.1 hk.2.2 p₁ hp1mem
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

/-! ## Part K — the W-positivity, the W-survivor, and the amended headline consumer -/

/-- **`chen_positivity_W` — the finite-`x` core at the W-carriers.**  `chen_positivity` with the
split bridge: given the three analytic main-term bounds at the AP-RESTRICTED instances (D2: they
must be re-supplied there, not majorized — the ledger normalizes by the AP-scale `X_W/φ(Q)`) and
the identical ledger conjunct, the W-restricted P₂-carrier is strictly positive. -/
theorem chen_positivity_W {x z P y Q a w' : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z) (hyx : x < (y + 1) ^ 3)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2))
    (hA1 : mainA1 ≤ A1primeSumW Q a x P)
    (hA2 : omegaPrimeSumW Q a x P y ≤ mainA2)
    (hA3 : triplePrimeSumW Q a x P y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    0 < p2PrimeSumW Q a x z P := by
  have hred := razor_reduction_W hx hyx hQfull hPfull' hQa2
  have hS := stripPrimeSum_le_W (y := y) hx hz hQfull hPfull' hQa2
  linarith [hred, hA1, hA2, hA3, hS, hledger]

/-- **The W Chen survivor.**  `chen_survivor` at the W-carriers: from the positivity of the
W-restricted P₂-carrier there is a prime `n ≥ x/2` in the window with `n+2` a genuine P₂. -/
theorem chen_survivor_W {x z P y Q a w' : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z) (hyx : x < (y + 1) ^ 3)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2))
    (hA1 : mainA1 ≤ A1primeSumW Q a x P)
    (hA2 : omegaPrimeSumW Q a x P y ≤ mainA2)
    (hA3 : triplePrimeSumW Q a x P y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    ∃ n : ℕ, x / 2 ≤ n ∧ n.Prime ∧ IsP2 2 (n + 2) := by
  have hpos := chen_positivity_W hx hz hyx hQfull hPfull' hQa2 hA1 hA2 hA3 hledger
  have hpos' : 0 < ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * p2Ind z (n + 2) := hpos
  -- a strictly positive term exists
  obtain ⟨n, hn, hterm⟩ :
      ∃ n ∈ twinWindow x, 0 < vonMangoldt n * keepW Q a P n * p2Ind z (n + 2) := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    exact absurd (Finset.sum_nonpos hcon) (not_le.mpr hpos')
  -- decode the term: keepW = 1 (prime ∧ sifted ∧ AP-member), p2Ind = 1 (IsP2 z)
  have hkeepne : keepW Q a P n ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  have hkeep1 : keepW Q a P n = 1 := keepW_eq_one_of_ne_zero hkeepne
  obtain ⟨hprime, -⟩ := keepW_eq_one_iff.mp hkeep1
  have hp2ne : p2Ind z (n + 2) ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  have hIsP2z : IsP2 z (n + 2) := by
    unfold p2Ind at hp2ne
    by_contra hnp2
    rw [if_neg hnp2] at hp2ne
    exact hp2ne rfl
  have hlo : x / 2 ≤ n := by rw [twinWindow, Finset.mem_Icc] at hn; exact hn.1
  exact ⟨n, hlo, hprime, isP2_mono hz hIsP2z⟩

/-- **`chen_of_hypotheses_W` — the amended Chen headline (H-AMENDMENT 2).**  The H_W-package: for
every threshold `X` there is an operating point `x` with the residue-class data `Q a w'`, the
three split sifting hypotheses (`hQfull`/`hPfull'`/`hQa2` replacing catch #65's torn `hPfull`),
the three analytic main-term bounds at the W-carriers, and the identical ledger conjunct.  Then
there are infinitely many primes `p` with `p + 2` a P₂.

The `3 ≤ w'` conjunct pins the intended instantiation window (`w' = w0N ε ≥ 3`, so `q = 2` falls
to `hQfull`); the extraction itself needs only the split bridge.  Suppliers: A1W/A2W′/A3W at the
AP-restricted instances, GLU-2W discharges (with `Q = Qval ε`, `a = Q − 1`, `residue_witness`). -/
theorem chen_of_hypotheses_W
    (H : ∀ X : ℕ, ∃ (x z P y Q a w' : ℕ) (mainA1 mainA2 mainA3 : ℝ),
        X ≤ x / 2 ∧ 2 ≤ x ∧ 2 ≤ z ∧ 3 ≤ w' ∧ x < (y + 1) ^ 3 ∧
        (∀ q, q.Prime → q < w' → q ∣ Q) ∧
        (∀ q, q.Prime → w' ≤ q → q < z → q ∣ P) ∧
        Nat.Coprime Q (a + 2) ∧
        mainA1 ≤ A1primeSumW Q a x P ∧
        omegaPrimeSumW Q a x P y ≤ mainA2 ∧
        triplePrimeSumW Q a x P y ≤ mainA3 ∧
        0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  obtain ⟨x, z, P, y, Q, a, w', mainA1, mainA2, mainA3,
    hXx, hx, hz, _hw3, hyx, hQfull, hPfull', hQa2, hA1, hA2, hA3, hledger⟩ := H (b + 1)
  obtain ⟨n, hlo, hprime, hIsP2⟩ :=
    chen_survivor_W hx hz hyx hQfull hPfull' hQa2 hA1 hA2 hA3 hledger
  refine ⟨n, ⟨hprime, hIsP2⟩, ?_⟩
  omega

/-! ## Part L — the residue witness (D1's `a = Q − 1`; GLU-2W helpers) -/

/-- **The residue witness.**  D1 takes `a = Q − 1`; then `a + 2 = Q + 1` and
`gcd(Q, a+2) = gcd(Q, Q+1) = 1` — the `hQa2` slot is free, no CRT needed. -/
theorem residue_witness (Q : ℕ) (hQ : 2 ≤ Q) : Nat.Coprime Q (Q - 1 + 2) := by
  have h : Q - 1 + 2 = Q + 1 := by omega
  rw [h]
  simp

/-- The companion form: `gcd(Q, a) = gcd(Q, Q−1) = 1` at `a = Q − 1` (consecutive integers), in
case a W-mirror needs the residue itself coprime to the modulus. -/
theorem residue_witness' (Q : ℕ) (hQ : 2 ≤ Q) : Nat.Coprime Q (Q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, by omega⟩
  simp

end Salt.Chen
