/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.GrahamHard

/-!
# ARM B part B2, wave **W6b-H1b** — the TWO INPUTS of the six flagged H1 rows

`Salt/SW/GrahamHard.lean` (W6b-H1) landed the substrate of An 2022 §5 over `ℚ` and recorded
six ABSENT rows in `docs/blueprints/flags.md` (the four 09-05 entries). Their executor's
diagnosis was that the six are not six defects but **two inputs**: a squarefree-density
factorisation of `ρ₀`'s SERIES (for H5a/H5c) and the evaluation
`Σ_{n ≤ Q}(μ(n)/n)·log(Q/n) → 1` (for H6c/H6d, and through them H6e/H6f). This file lands
the first input WHOLE, together with the two H rows it closes, and part of the second.

## What is here

* **The coprime-subseries tool (T1–T5).** For `f` absolutely summable, multiplicative on
  coprime pairs and ZERO off squarefree, the level-`t` subseries `S_f(t) = Σ'_{(n,t)=1} f(n)`
  satisfies the prime step `S_f(t) = (1 + f p)·S_f(pt)` and the closed form
  `S_f(t)·∏_{p ∣ t}(1 + f p) = Σ' f`. This is the "`tsum` split" the H1 flag named as
  missing, and it is one stone, not two: **T6** and **T7** are its two instances.
* **T6/T7 — the two densities.** `(φ(r)/r)·S_{μ/n²}(r) = ρ₀·(r/κ(r))` (H5a's main term) and
  `(t/φ(t))·S_{μ²/(κφ)}(t) = c₀·κ(t)/t` (H6e's main term, with `c₀` DEFINED as its series).
* **P1/P2 and H5a/H5c** — the counting half of An's Lemma 3.7 over `ℚ` and its two-log
  weighted partial summation.
* **C1** — the exact harmonic identity `Σ_{n ≤ N}(μ(n)/n)·H(⌊N/n⌋) = 1` — and with it
  **C2** (the sawtooth-log piece), **THE CONSTANT C3** (`Σ(μ(n)/n)log(Q/n) → 1`) and
  **H6c**. C2 runs by ONE discrete Abel over `(a, N]` and a total-variation split, NOT by
  the fibre decomposition of `n ↦ ⌊Q/n⌋₊`.
* **S1** — the `t`-smooth convolution `Σ_{m ≤ X,(m,t)=1} μ(m)G(m) =
  Σ_{d ≤ X smooth} Σ_{e ≤ X/d} μ(e)G(de)` — **S2**, the smooth partial sum against its
  Euler product, and **S3**, its tail, by a FINITE prime-step induction carried for every
  `Y > 0` (the surplus below `Y = 1` is what pays for the geometric tail at the step).
* **S4, H6d, H6f and H6e** — the four coprime-restricted rows, the last two through the
  `κ`-expansion `μ(n)/κ(n) = (μ(n)/n)·Σ_{d ∣ n} μ(d)/κ(d)`. **All six of the W6b-H freeze's
  flagged rows are now closed.**
* Three PUBLIC helpers the next wave (H2) consumes: `summable_moebius_sq_div_kappa_totient`,
  `log_rpow_le_rpow_quarter` (`(log x)^A ≤ (4A)^A x^{1/4}`) and `one_le_c0`.

## ⚠ THE HONEST LABEL — what this file does and does NOT prove

**NO frozen row of this cut is absent.** All twenty-two land, the six W6b-H freeze rows
(H5a, H5c, H6c, H6d, H6e, H6f) among them; the six 09-05 flag entries are RETIRED in
`docs/blueprints/flags.md`. A consumer should still read this file's declaration list, not
the wave's label.

**H6e lands in the NAMED form.** `coprime_sum_moebius_div_kappa_log_eq` states the row with
the LANDED constant `c0` as its main term, because the frozen `∃ c₀` shape exports no witness
and the H2 wave's H7c consumes H6e's main term AS `c0`. The frozen shape is kept as the
one-line corollary `coprime_sum_moebius_div_kappa_log_exists`; `0 < c0` is the public
`one_le_c0`.

**Everything proved here is an UPPER bound or an exact identity** — no asymptotic and no
lower bound anywhere. Where a constant is `∃`-bound it is **non-effective**: H5a and H5c
pass through no rate at all (they are elementary, `C = 4` and `C = 250 + 39·C_{H5a}`), but
the wave's remaining rows would pass through `mmuRate_holds` by way of H6a/H6b, whose `x₀`
is not extracted anywhere in the corpus — so their constants, when they land, will print
their DERIVATION and never a numeral.

**`c0` is a SERIES, not a number.** It is `Σ'_n μ(n)²/(κ(n)φ(n))`; `c₀ = ζ(2)` is true and
is never used, and `ρ₀·c₀ = 1` is true and is never used. T7 is stated at the series.

**T4/T5 hold for `f` zero off squarefree only** — the tool is NOT a general Euler product.
The must-FAIL control is in T5's docstring: at `f = 1/n²` and `t = 2` the closed form is
false by `1.542124 ≠ 1.644931`, because the true factor is `(1 − 1/4)^{−1}`.

**T3 carries `t ≠ 0` and `s ≠ 0`.** The v1 statement without them is FALSE at `(t, s) =
(0, 1)`: both `primeFactors` are `∅` while `Coprime n 0 ↔ n = 1`, so `coprimeSeries f 0 =
f 1`. The measured control is in T3's docstring.

**The six H rows are the W6b-H freeze's statements, landing HERE and not in
`GrahamHard.lean`.** That file is byte-unchanged by this wave; the two that landed (H5a,
H5c) carry its frozen types.

**Three mutants were MEASURED and STRUCK** and are recorded as NOT controls in the docstrings
that own them: P2 with `X^{1/4} → X^0` and P2 with `σ(r) → 1` (in P2's), and C2 with the
`+ 1` in the log DROPPED (in C2's) — that last measures `×log²(2Q) = −0.81 … −0.05` over
`Q = 10² … 10⁶`, bounded and shrinking, so it PASSES at every tested point.

**F6** (no net numerator log): every frozen statement here is log-free (T1–T7, P1, P2, S1,
S2, S3, C1) or carries its logs in a bounded one-variable pair (H5a's `√M·σ`, H5c's
`(1 + |log M + α|)(1 + |log M + β|)`) or in the DENOMINATOR only (C2, C3, H6c, S4, H6d, H6f
and H6e all read `(log 2Q)^{−A}`). The route's numerator logs — `log Q·f(Q)` in H6c,
`(1 + log Q)/√Q` in C3's `D`-tail, `(1 + log Q)²` in the far tails of H6d and H6e — are each
closed by the A4 helper at `A`, `A + 1` or `A + 2`, and none survives to a statement.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

namespace Salt.SW

open ArithmeticFunction

/-- The coprime subseries of `f` at level `t`: `Σ'_{(n,t)=1} f(n)`. -/
noncomputable def coprimeSeries (f : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑' n : ℕ, if Nat.Coprime n t then f n else 0

/-- `c₀ := Σ'_{n squarefree} 1/(κ(n)·φ(n))` — An's Lemma 3.11 constant, DEFINED as its
series (`= ζ(2)` in truth, never needed). -/
noncomputable def c0 : ℝ := ∑' n : ℕ, (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))

/-! ## I. THE COPRIME-SUBSERIES TOOL -/

/-- **T1.** The coprime indicator of an absolutely summable `f` is summable: it is
dominated by `|f|` termwise. -/
theorem summable_coprime_indicator {f : ℕ → ℝ} (hf : Summable (fun n => |f n|)) (t : ℕ) :
    Summable (fun n : ℕ => if Nat.Coprime n t then f n else 0) := by
  classical
  refine Summable.of_norm_bounded hf fun n => ?_
  by_cases hc : Nat.Coprime n t
  · rw [if_pos hc]
    exact le_of_eq (Real.norm_eq_abs _)
  · rw [if_neg hc, norm_zero]
    exact abs_nonneg _

/-- **T2.** At level 1 the subseries is the whole series (`Nat.coprime_one_right`). -/
theorem coprimeSeries_one (f : ℕ → ℝ) : coprimeSeries f 1 = ∑' n : ℕ, f n := by
  unfold coprimeSeries
  exact tsum_congr fun n => if_pos (Nat.coprime_one_right n)

/-- **T3.** The subseries depends on the level only through its prime factors.

The nonzero binders `ht`, `hs` are LOAD-BEARING and are spent on
`Nat.disjoint_primeFactors`. The must-FAIL control (measured): without them, at
`(t, s) = (0, 1)` and `f = μ/n²`, `coprimeSeries f 0 = f 1 = 1.000000` while
`coprimeSeries f 1 = ρ₀ = 0.607927` (and at `f = [n = 2]`: `0` vs `1`) — both
`primeFactors` are `∅`, but `Coprime n 0 ↔ n = 1`. -/
theorem coprimeSeries_eq_of_primeFactors_eq (f : ℕ → ℝ) {t s : ℕ} (ht : t ≠ 0) (hs : s ≠ 0)
    (h : t.primeFactors = s.primeFactors) :
    coprimeSeries f t = coprimeSeries f s := by
  classical
  have hone : t = 1 ↔ s = 1 := by
    constructor
    · rintro rfl
      rw [Nat.primeFactors_one] at h
      rcases Nat.primeFactors_eq_empty.mp h.symm with h0 | h1
      · exact absurd h0 hs
      · exact h1
    · rintro rfl
      rw [Nat.primeFactors_one] at h
      rcases Nat.primeFactors_eq_empty.mp h with h0 | h1
      · exact absurd h0 ht
      · exact h1
  have hiff : ∀ n : ℕ, Nat.Coprime n t ↔ Nat.Coprime n s := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.coprime_zero_left, Nat.coprime_zero_left]
      exact hone
    · rw [← Nat.disjoint_primeFactors hn ht, ← Nat.disjoint_primeFactors hn hs, h]
  unfold coprimeSeries
  refine tsum_congr fun n => ?_
  by_cases hc : Nat.Coprime n t
  · rw [if_pos hc, if_pos ((hiff n).mp hc)]
  · rw [if_neg hc, if_neg fun hcs => hc ((hiff n).mpr hcs)]

/-- **T4 (the prime step).** `S_f(t) = (1 + f p)·S_f(pt)` for a prime `p ∤ t`.

Split the level-`t` indicator by `p ∣ n`: the `p ∤ n` half IS the level-`pt` series, and
the `p ∣ n` half reindexes by `n = p·e` (`Function.Injective.tsum_eq`, the support being
inside the multiples of `p`) to `f p · S_f(pt)` — the terms with `p ∣ e` die because
`p² ∣ p·e` and `hsq` kills `f` off squarefree.

The must-FAIL control (measured): with `(1 + f p)` → `(1 - f p)` at `f = μ/n²`, `t = 1`,
`p = 2`, `(1 − f(2))·S_f(2) = (5/4)·0.810570 = 1.013212 ≠ 0.607927 = S_f(1)`. -/
theorem coprimeSeries_eq_mul_prime {f : ℕ → ℝ} (hf : Summable (fun n => |f n|))
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hsq : ∀ n : ℕ, ¬ Squarefree n → f n = 0)
    {p t : ℕ} (hp : p.Prime) (hpt : ¬ p ∣ t) :
    coprimeSeries f t = (1 + f p) * coprimeSeries f (p * t) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hcpt : Nat.Coprime p t := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpt
  have hcop : ∀ n : ℕ, Nat.Coprime n (p * t) ↔ (¬ p ∣ n) ∧ Nat.Coprime n t := by
    intro n
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun hd => (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp h1) hd, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1), h2⟩
  have hsA : Summable (fun n : ℕ => if Nat.Coprime n (p * t) then f n else 0) :=
    summable_coprime_indicator hf (p * t)
  have hsB : Summable (fun n : ℕ => if Nat.Coprime n t ∧ p ∣ n then f n else 0) := by
    refine Summable.of_norm_bounded hf fun n => ?_
    by_cases hc : Nat.Coprime n t ∧ p ∣ n
    · rw [if_pos hc]
      exact le_of_eq (Real.norm_eq_abs _)
    · rw [if_neg hc, norm_zero]
      exact abs_nonneg _
  have hsplit : ∀ n : ℕ, (if Nat.Coprime n t then f n else 0)
      = (if Nat.Coprime n (p * t) then f n else 0)
        + (if Nat.Coprime n t ∧ p ∣ n then f n else 0) := by
    intro n
    by_cases hct : Nat.Coprime n t
    · by_cases hd : p ∣ n
      · rw [if_pos hct, if_neg fun hc => ((hcop n).mp hc).1 hd, if_pos ⟨hct, hd⟩, zero_add]
      · rw [if_pos hct, if_pos ((hcop n).mpr ⟨hd, hct⟩), if_neg fun hb => hd hb.2, add_zero]
    · rw [if_neg hct, if_neg fun hc => hct ((hcop n).mp hc).2, if_neg fun hb => hct hb.1,
        add_zero]
  have hBval : ∀ e : ℕ, (if Nat.Coprime (p * e) t ∧ p ∣ p * e then f (p * e) else 0)
      = f p * (if Nat.Coprime e (p * t) then f e else 0) := by
    intro e
    by_cases hce : Nat.Coprime e (p * t)
    · have hde : ¬ p ∣ e := ((hcop e).mp hce).1
      have hcet : Nat.Coprime e t := ((hcop e).mp hce).2
      have hcpe : Nat.Coprime p e := (Nat.Prime.coprime_iff_not_dvd hp).mpr hde
      have hc1 : Nat.Coprime (p * e) t := Nat.Coprime.mul_left hcpt hcet
      rw [if_pos ⟨hc1, dvd_mul_right p e⟩, if_pos hce, hmul p e hcpe]
    · rw [if_neg hce, mul_zero]
      by_cases hc1 : Nat.Coprime (p * e) t ∧ p ∣ p * e
      · rw [if_pos hc1]
        have hcet : Nat.Coprime e t := Nat.Coprime.coprime_dvd_left (dvd_mul_left e p) hc1.1
        have hde : p ∣ e := by
          by_contra hde
          exact hce ((hcop e).mpr ⟨hde, hcet⟩)
        obtain ⟨e', rfl⟩ := hde
        refine hsq _ fun hsqf => ?_
        exact absurd (Nat.isUnit_iff.mp (hsqf p ⟨e', by ring⟩)) hp.one_lt.ne'
      · rw [if_neg hc1]
  have hre : (∑' e : ℕ, (if Nat.Coprime (p * e) t ∧ p ∣ p * e then f (p * e) else 0))
      = ∑' n : ℕ, (if Nat.Coprime n t ∧ p ∣ n then f n else 0) := by
    refine Function.Injective.tsum_eq
      (f := fun n : ℕ => if Nat.Coprime n t ∧ p ∣ n then f n else 0)
      (g := fun e : ℕ => p * e) (fun a b hab => Nat.eq_of_mul_eq_mul_left hp0 hab) ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_cases hc : Nat.Coprime n t ∧ p ∣ n
    · obtain ⟨e, rfl⟩ := hc.2
      exact ⟨e, rfl⟩
    · exact absurd (if_neg hc) hn
  unfold coprimeSeries
  rw [tsum_congr hsplit, hsA.tsum_add hsB, ← hre, tsum_congr hBval, hsA.tsum_mul_left]
  ring

/-- The tool over a FINSET of primes: `S_f(∏ P)·∏_{p ∈ P}(1 + f p) = Σ' f`, by induction
on `P` with T4 as the step. -/
private lemma coprimeSeries_prod_primes {f : ℕ → ℝ} (hf : Summable (fun n => |f n|))
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hsq : ∀ n : ℕ, ¬ Squarefree n → f n = 0) (P : Finset ℕ) :
    (∀ p ∈ P, Nat.Prime p) →
      coprimeSeries f (∏ p ∈ P, p) * ∏ p ∈ P, (1 + f p) = ∑' n : ℕ, f n := by
  classical
  refine Finset.induction_on P ?_ ?_
  · intro _
    simpa using coprimeSeries_one f
  · intro q P hq ih hprime
    have hqp : Nat.Prime q := hprime q (Finset.mem_insert_self q P)
    have hPp : ∀ p ∈ P, Nat.Prime p := fun p hp => hprime p (Finset.mem_insert_of_mem hp)
    have hqdvd : ¬ q ∣ ∏ p ∈ P, p := by
      intro hd
      obtain ⟨a, ha, hqa⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hd
      exact hq ((Nat.prime_dvd_prime_iff_eq hqp (hPp a ha)).mp hqa ▸ ha)
    have hT4 := coprimeSeries_eq_mul_prime hf hmul hsq hqp hqdvd
    have hIH := ih hPp
    rw [hT4] at hIH
    rw [Finset.prod_insert hq, Finset.prod_insert hq]
    linear_combination hIH

/-- **T5 (the closed form).** `S_f(t)·∏_{p ∣ t}(1 + f p) = Σ' f` for every `t ≥ 1`.

T3 transfers the level to `∏_{p ∣ t} p` (a squarefree level with the same prime factors),
where the Finset induction of `coprimeSeries_prod_primes` applies.

The must-FAIL control (measured): without `hsq` the row is FALSE — at `f = 1/n²`, `t = 2`,
`S_f(2)·(1 + f(2)) = 1.542124 ≠ 1.644931 = Σ' f` (the true factor is `(1 − 1/4)^{−1}`). -/
theorem coprimeSeries_mul_prod_eq {f : ℕ → ℝ} (hf : Summable (fun n => |f n|))
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hsq : ∀ n : ℕ, ¬ Squarefree n → f n = 0) (t : ℕ) (ht : 1 ≤ t) :
    coprimeSeries f t * ∏ p ∈ t.primeFactors, (1 + f p) = ∑' n : ℕ, f n := by
  classical
  have hprime : ∀ p ∈ t.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hpf : (∏ p ∈ t.primeFactors, p).primeFactors = t.primeFactors :=
    Nat.primeFactors_prod hprime
  have hprodpos : 0 < ∏ p ∈ t.primeFactors, p :=
    Finset.prod_pos fun p hp => (hprime p hp).pos
  have htrans : coprimeSeries f t = coprimeSeries f (∏ p ∈ t.primeFactors, p) :=
    coprimeSeries_eq_of_primeFactors_eq f (by omega) (by omega) hpf.symm
  rw [htrans]
  exact coprimeSeries_prod_primes hf hmul hsq t.primeFactors hprime

/-! ### The two instances -/

/-- `φ(r)/r = ∏_{p ∣ r}(1 − 1/p)` for `r ≥ 1` (Totient.lean:295, cast per prime). -/
private lemma totient_div_eq_prod_one_sub (r : ℕ) (hr : 1 ≤ r) :
    (Nat.totient r : ℝ) / r = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hppos : (0 : ℝ) < ∏ p ∈ r.primeFactors, (p : ℝ) := by
    refine Finset.prod_pos fun p hp => ?_
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hcast : ∏ p ∈ r.primeFactors, (((p - 1 : ℕ)) : ℝ)
      = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hkey : (Nat.totient r : ℝ) * ∏ p ∈ r.primeFactors, (p : ℝ)
      = (r : ℝ) * ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
    have h := Nat.totient_mul_prod_primeFactors r
    have h' : ((Nat.totient r * ∏ p ∈ r.primeFactors, p : ℕ) : ℝ)
        = ((r * ∏ p ∈ r.primeFactors, (p - 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [← hcast]
    exact h'
  have hsplit : ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ))
      = (∏ p ∈ r.primeFactors, ((p : ℝ) - 1)) / ∏ p ∈ r.primeFactors, (p : ℝ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    field_simp
  rw [hsplit, div_eq_div_iff hr0.ne' hppos.ne']
  linear_combination hkey

/-- `κ(r)/r = ∏_{p ∣ r}(1 + 1/p)` — `kappa`'s definition divided by `r ≥ 1`. -/
private lemma kappa_div_eq_prod_one_add (r : ℕ) (hr : 1 ≤ r) :
    kappa r / r = ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  rw [kappa, mul_comm, mul_div_assoc, div_self hr0.ne', mul_one]

private lemma prod_one_sub_pos (r : ℕ) : (0 : ℝ) < ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)) := by
  refine Finset.prod_pos fun p hp => ?_
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

private lemma prod_one_add_pos (r : ℕ) : (0 : ℝ) < ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
  refine Finset.prod_pos fun p hp => ?_
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  positivity

private lemma prod_one_sub_sq_pos (r : ℕ) :
    (0 : ℝ) < ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  refine Finset.prod_pos fun p hp => ?_
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hsq : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  have : (1 : ℝ) / (p : ℝ) ^ 2 < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

/-- `Σ_n |μ(n)/n²|` converges (dominated by `1/n²`). -/
private lemma summable_abs_moebius_div_sq :
    Summable (fun n : ℕ => |(moebius n : ℝ) / (n : ℝ) ^ 2|) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded hsum fun n => ?_
  rw [Real.norm_eq_abs, abs_abs]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr hmu

/-- **T6 (H5a's density).** `(φ(r)/r)·S_{μ/n²}(r) = ρ₀·(r/κ(r))`.

T5 at `f = μ/n²` gives `S·∏(1 − p^{−2}) = ρ₀`; the finite algebra is the per-prime
`(1 − 1/p)(1 + 1/p) = 1 − 1/p²`.

The must-FAIL control (measured): with `ρ₀·(r/κ(r))` → `ρ₀·(κ(r)/r)` at `r = 6`, the RHS
reads `1.215854` against the LHS `0.303964`. -/
theorem totient_div_mul_coprimeSeries_moebius_div_sq (r : ℕ) (hr : 1 ≤ r) :
    (Nat.totient r : ℝ) / r * coprimeSeries (fun n => (moebius n : ℝ) / (n : ℝ) ^ 2) r
      = rho0 * ((r : ℝ) / kappa r) := by
  classical
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hmul : ∀ a b : ℕ, Nat.Coprime a b →
      (moebius (a * b) : ℝ) / ((a * b : ℕ) : ℝ) ^ 2
        = (moebius a : ℝ) / (a : ℝ) ^ 2 * ((moebius b : ℝ) / (b : ℝ) ^ 2) := by
    intro a b hab
    rw [div_mul_div_comm, isMultiplicative_moebius.map_mul_of_coprime hab]
    push_cast
    ring
  have hsqz : ∀ n : ℕ, ¬ Squarefree n → (moebius n : ℝ) / (n : ℝ) ^ 2 = 0 := by
    intro n hn
    rw [moebius_eq_zero_of_not_squarefree hn]
    simp
  have hT5 := coprimeSeries_mul_prod_eq (f := fun n : ℕ => (moebius n : ℝ) / (n : ℝ) ^ 2)
    summable_abs_moebius_div_sq hmul hsqz r hr
  have hprodeq : ∏ p ∈ r.primeFactors, (1 + (moebius p : ℝ) / (p : ℝ) ^ 2)
      = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
    push_cast
    ring
  have hrho : (∑' n : ℕ, (moebius n : ℝ) / (n : ℝ) ^ 2) = rho0 := rfl
  rw [hprodeq, hrho] at hT5
  have hkey : (∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)))
        * ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ))
      = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    ring
  have h1 := prod_one_sub_pos r
  have h2 := prod_one_add_pos r
  have h3 := prod_one_sub_sq_pos r
  have hkapr : (r : ℝ) / kappa r = 1 / ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
    rw [kappa, div_eq_div_iff (mul_ne_zero hr0.ne' h2.ne') h2.ne']
    ring
  rw [totient_div_eq_prod_one_sub r hr, hkapr]
  have hS : coprimeSeries (fun n : ℕ => (moebius n : ℝ) / (n : ℝ) ^ 2) r
      = rho0 / ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [eq_div_iff h3.ne']
    exact hT5
  rw [hS, ← hkey]
  field_simp

/-- `p^{3/2} ≤ p² − 1` for every real `p ≥ 2` — the polynomial identity
`(p² − 1)² − p³ = p²(p − 2)(p + 1) + 1 ≥ 1`. -/
private lemma rpow_three_halves_le {p : ℝ} (hp : 2 ≤ p) : p ^ ((3/2 : ℝ)) ≤ p ^ 2 - 1 := by
  have hp0 : (0 : ℝ) < p := by linarith
  have ha : (0 : ℝ) < p ^ ((3/2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  have hsq : (p ^ ((3/2 : ℝ))) ^ 2 = p ^ 3 := by
    rw [← Real.rpow_natCast (p ^ ((3/2 : ℝ))) 2, ← Real.rpow_mul hp0.le,
      show (3/2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hb : (0 : ℝ) < p ^ 2 - 1 := by nlinarith
  by_contra hcon
  rw [not_le] at hcon
  have h1 : (p ^ 2 - 1) ^ 2 < (p ^ ((3/2 : ℝ))) ^ 2 := by nlinarith
  rw [hsq] at h1
  nlinarith [h1,
    mul_nonneg (mul_nonneg (mul_nonneg hp0.le hp0.le) (by linarith : (0 : ℝ) ≤ p - 2))
      (by linarith : (0 : ℝ) ≤ p + 1)]

/-- `κ` is multiplicative on coprime pairs (`Nat.Coprime.primeFactors_mul` +
`Finset.prod_union`). -/
private lemma kappa_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    kappa (a * b) = kappa a * kappa b := by
  rw [kappa, kappa, kappa, Nat.Coprime.primeFactors_mul hab,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
  push_cast
  ring

/-- On squarefree `n`, `κ(n)·φ(n) = ∏_{p ∣ n}(p² − 1)`. -/
private lemma kappa_mul_totient_eq_prod (n : ℕ) (hn : 1 ≤ n) (hsqf : Squarefree n) :
    kappa n * (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ 2 - 1) := by
  have hn0 : 0 < n := hn
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsqf
  have hphiN : Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
    have h := Nat.totient_mul_prod_primeFactors n
    rw [hprod] at h
    exact Nat.eq_of_mul_eq_mul_left hn0 (by rw [mul_comm]; exact h)
  have hphi : (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [hphiN, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, hprod]
  have hkap : kappa n = ∏ p ∈ n.primeFactors, ((p : ℝ) + 1) := by
    rw [kappa, hnR, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    field_simp
  rw [hkap, hphi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  ring

/-- `n^{3/2} ≤ κ(n)·φ(n)` on squarefree `n ≥ 1` — the per-prime `p^{3/2} ≤ p² − 1`.
MEASURED: no squarefree `n ≤ 10⁵` violates it; the ratio's max is 1 at `n = 1`. -/
private lemma rpow_three_halves_le_kappa_mul_totient (n : ℕ) (hn : 1 ≤ n) (hsqf : Squarefree n) :
    (n : ℝ) ^ ((3/2 : ℝ)) ≤ kappa n * (Nat.totient n : ℝ) := by
  rw [kappa_mul_totient_eq_prod n hn hsqf]
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsqf
  have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, hprod]
  rw [hnR, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity) _]
  refine Finset.prod_le_prod (fun p _ => Real.rpow_nonneg (by positivity) _) fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  exact rpow_three_halves_le hp2

/-- **T7's summability helper (PUBLIC; H2's wave consumes it).**
`Σ_n |μ(n)²/(κ(n)φ(n))|` converges: off squarefree the term is 0, and on squarefree `n`
`κ(n)φ(n) = ∏_{p ∣ n}(p² − 1) ≥ ∏ p^{3/2} = n^{3/2}`, so the term is `≤ n^{−3/2}` and
`Real.summable_one_div_nat_rpow` applies at `p = 3/2`. -/
theorem summable_moebius_sq_div_kappa_totient :
    Summable (fun n : ℕ => |(moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))|) := by
  classical
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((3/2 : ℝ))) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  refine Summable.of_norm_bounded hsum fun n => ?_
  rw [Real.norm_eq_abs, abs_abs]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · by_cases hsqf : Squarefree n
    · have hbound := rpow_three_halves_le_kappa_mul_totient n hn hsqf
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ ((3/2 : ℝ)) := Real.rpow_pos_of_pos hnR _
      have hkpos : (0 : ℝ) < kappa n * (Nat.totient n : ℝ) := lt_of_lt_of_le hpos hbound
      have hmu : ((moebius n : ℝ)) ^ 2 = 1 := by
        have h := moebius_sq (n := n)
        rw [if_pos hsqf] at h
        exact_mod_cast h
      rw [hmu, abs_of_nonneg (div_nonneg zero_le_one hkpos.le)]
      exact one_div_le_one_div_of_le hpos hbound
    · rw [moebius_eq_zero_of_not_squarefree hsqf, Int.cast_zero, zero_pow (by norm_num),
        zero_div, abs_zero]
      positivity

private lemma summable_moebius_sq_div_kappa_totient' :
    Summable (fun n : ℕ => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) :=
  summable_moebius_sq_div_kappa_totient.of_abs

/-- **T7 (H6e's main term).** `(t/φ(t))·S_{μ²/(κφ)}(t) = c₀·κ(t)/t`.

T5 at `f = μ²/(κφ)` (multiplicative on coprime pairs — the `(0, 1)` branch is `0 = 0` —
and zero off squarefree) gives `S·∏ p²/(p² − 1) = c₀`; the finite algebra is the
per-prime `(1 − 1/p)·(p²/(p² − 1))·(1 + 1/p) = 1`.

The must-FAIL control (measured): with `c₀·κ(t)/t` → `c₀·t/κ(t)` at `t = 2`, the RHS
reads `1.096621` against the LHS `2.467398`. -/
theorem div_totient_mul_coprimeSeries_inv_kappa_totient (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ) / Nat.totient t
        * coprimeSeries (fun n => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) t
      = c0 * kappa t / t := by
  classical
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hmul : ∀ a b : ℕ, Nat.Coprime a b →
      (moebius (a * b) : ℝ) ^ 2 / (kappa (a * b) * (Nat.totient (a * b) : ℝ))
        = (moebius a : ℝ) ^ 2 / (kappa a * (Nat.totient a : ℝ))
          * ((moebius b : ℝ) ^ 2 / (kappa b * (Nat.totient b : ℝ))) := by
    intro a b hab
    rw [div_mul_div_comm, kappa_mul_of_coprime hab, Nat.totient_mul hab,
      isMultiplicative_moebius.map_mul_of_coprime hab]
    push_cast
    ring
  have hsqz : ∀ n : ℕ, ¬ Squarefree n →
      (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ)) = 0 := by
    intro n hn
    rw [moebius_eq_zero_of_not_squarefree hn]
    simp
  have hT5 := coprimeSeries_mul_prod_eq
    (f := fun n : ℕ => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ)))
    summable_moebius_sq_div_kappa_totient hmul hsqz t ht
  have hprodeq : ∏ p ∈ t.primeFactors,
        (1 + (moebius p : ℝ) ^ 2 / (kappa p * (Nat.totient p : ℝ)))
      = ∏ p ∈ t.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpos2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    have hk : kappa p = (p : ℝ) + 1 := by
      rw [kappa, hpp.primeFactors, Finset.prod_singleton]
      field_simp
    have hphi : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.totient_prime hpp, Nat.cast_sub hpp.one_le, Nat.cast_one]
    have hmu : ((moebius p : ℝ)) ^ 2 = 1 := by
      rw [moebius_apply_prime hpp]
      norm_num
    rw [hk, hphi, hmu, show ((p : ℝ) + 1) * ((p : ℝ) - 1) = (p : ℝ) ^ 2 - 1 by ring,
      eq_div_iff hpos2.ne']
    field_simp
    ring
  have hc0 : (∑' n : ℕ, (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) = c0 := rfl
  rw [hprodeq, hc0] at hT5
  have hVpos : (0 : ℝ) < ∏ p ∈ t.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hpos2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hUpos := prod_one_sub_pos t
  have hWpos := prod_one_add_pos t
  have hUVW : (∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)))
      * (∏ p ∈ t.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)))
      * (∏ p ∈ t.primeFactors, (1 + 1 / (p : ℝ))) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpos2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    field_simp
    ring
  have hS : coprimeSeries (fun n : ℕ => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) t
      = c0 / ∏ p ∈ t.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
    rw [eq_div_iff hVpos.ne']
    exact hT5
  have hcast : (t : ℝ) / (Nat.totient t : ℝ)
      = 1 / ∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := totient_div_eq_prod_one_sub t ht
    rw [div_eq_iff ht0.ne'] at h
    rw [h, div_eq_div_iff (mul_ne_zero hUpos.ne' ht0.ne') hUpos.ne']
    ring
  rw [hcast, hS, mul_div_assoc, kappa_div_eq_prod_one_add t ht, div_mul_div_comm, one_mul,
    div_eq_iff (mul_ne_zero hUpos.ne' hVpos.ne')]
  linear_combination (-c0) * hUVW

/-! ## II. THE COUNTING HALF (H5) -/

/-- `(x^q)^k = x^(q·k)` for a natural `k` (the landed `rpow_pow_nat` recipe, re-derived:
a `private` cannot cross a file boundary). -/
private lemma rpow_pow_nat {x : ℝ} (hx : 0 ≤ x) (q : ℝ) (k : ℕ) :
    (x ^ q) ^ k = x ^ (q * (k : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ q) k, ← Real.rpow_mul hx]

/-- The telescoping step of `Σ f^{−1/2}` (the landed recipe, re-derived). -/
private lemma rpow_step_half (t : ℝ) (ht : 0 ≤ t) :
    (t + 1) ^ (-(1/2) : ℝ) ≤ 2 * (t + 1) ^ ((1/2) : ℝ) - 2 * t ^ ((1/2) : ℝ) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hinv : (t + 1) ^ (-(1/2) : ℝ) = ((t + 1) ^ ((1/2) : ℝ))⁻¹ := Real.rpow_neg ht1.le _
  rw [hinv]
  set a : ℝ := (t + 1) ^ ((1/2) : ℝ) with ha
  set b : ℝ := t ^ ((1/2) : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos ht1 _
  have hb0 : (0 : ℝ) ≤ b := Real.rpow_nonneg ht _
  have ha2 : a ^ 2 = t + 1 := by
    rw [ha, rpow_pow_nat ht1.le, show ((1/2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hb2 : b ^ 2 = t := by
    rw [hb, rpow_pow_nat ht, show ((1/2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  rw [inv_eq_one_div, div_le_iff₀ ha0]
  nlinarith [sq_nonneg (a - b), ha2, hb2]

/-- `Σ_{f ≤ N} f^{−1/2} ≤ 2·N^{1/2}` (the landed recipe, re-derived). -/
private lemma sum_rpow_neg_half_le (N : ℕ) :
    ∑ f ∈ Finset.Icc 1 N, (f : ℝ) ^ (-(1/2) : ℝ) ≤ 2 * (N : ℝ) ^ ((1/2) : ℝ) := by
  induction N with
  | zero => simp [Real.zero_rpow]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, rpow_step_half (m : ℝ) (by positivity)]

/-- `(Q/e)^q = Q^q·e^{−q}` (the landed `div_rpow_neg` recipe, re-derived). -/
private lemma div_rpow_neg {Q e : ℝ} (hQ : 0 ≤ Q) (he : 0 ≤ e) (q : ℝ) :
    (Q / e) ^ q = Q ^ q * e ^ (-q) := by
  rw [div_eq_mul_inv, Real.mul_rpow hQ (inv_nonneg.mpr he), Real.inv_rpow he, Real.rpow_neg he]

/-- `1 ≤ σ_{−1/4}(r)` for `r ≥ 1` — the divisor `e = 1` alone. -/
private lemma one_le_sigmaQ (r : ℕ) (hr : 1 ≤ r) : (1 : ℝ) ≤ sigmaQ r := by
  rw [sigmaQ]
  have h1 : (1 : ℕ) ∈ r.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hle := Finset.single_le_sum
    (f := fun e : ℕ => (e : ℝ) ^ (-(1/4 : ℝ)))
    (fun e _ => Real.rpow_nonneg (by positivity) _) h1
  simpa using hle

/-- `d² ∣ b²·a` with `a` squarefree forces `d ∣ b`: split off `g = gcd d b`, cancel `g²`,
and `d'²` — coprime to `b'²` — divides the squarefree `a`, hence `d' = 1`. -/
private lemma dvd_of_sq_dvd_sq_mul {d b a : ℕ} (ha : Squarefree a) (h : d ^ 2 ∣ b ^ 2 * a) :
    d ∣ b := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : b ^ 2 * a = 0 := by simpa using h
    have hane : a ≠ 0 := ha.ne_zero
    have : b = 0 := by
      rcases Nat.mul_eq_zero.mp h0 with hb | hab
      · exact pow_eq_zero_iff (by norm_num) |>.mp hb
      · exact absurd hab hane
    simp [this]
  · have hg0 : 0 < Nat.gcd d b := Nat.gcd_pos_of_pos_left b hd
    have hgd : Nat.gcd d b ∣ d := Nat.gcd_dvd_left d b
    have hgb : Nat.gcd d b ∣ b := Nat.gcd_dvd_right d b
    have hdeq : d = Nat.gcd d b * (d / Nat.gcd d b) := (Nat.mul_div_cancel' hgd).symm
    have hbeq : b = Nat.gcd d b * (b / Nat.gcd d b) := (Nat.mul_div_cancel' hgb).symm
    have hcop : Nat.Coprime (d / Nat.gcd d b) (b / Nat.gcd d b) :=
      Nat.coprime_div_gcd_div_gcd hg0
    have hg2 : 0 < Nat.gcd d b ^ 2 := by positivity
    have hstep : Nat.gcd d b ^ 2 * (d / Nat.gcd d b) ^ 2
        ∣ Nat.gcd d b ^ 2 * ((b / Nat.gcd d b) ^ 2 * a) := by
      calc Nat.gcd d b ^ 2 * (d / Nat.gcd d b) ^ 2 = d ^ 2 := by
            rw [← mul_pow, ← hdeq]
        _ ∣ b ^ 2 * a := h
        _ = Nat.gcd d b ^ 2 * ((b / Nat.gcd d b) ^ 2 * a) := by
            rw [← mul_assoc, ← mul_pow, ← hbeq]
    have h2 : (d / Nat.gcd d b) ^ 2 ∣ (b / Nat.gcd d b) ^ 2 * a :=
      (Nat.mul_dvd_mul_iff_left hg2).mp hstep
    have hcop2 : Nat.Coprime ((d / Nat.gcd d b) ^ 2) ((b / Nat.gcd d b) ^ 2) :=
      Nat.Coprime.pow 2 2 hcop
    have hda : (d / Nat.gcd d b) ^ 2 ∣ a := hcop2.dvd_of_dvd_mul_left h2
    have hunit : IsUnit (d / Nat.gcd d b) :=
      ha (d / Nat.gcd d b) (by rw [← pow_two]; exact hda)
    have h1 : d / Nat.gcd d b = 1 := Nat.isUnit_iff.mp hunit
    rw [hdeq, h1, mul_one]
    exact hgb

/-- **P1.** `Σ_{d² ∣ n} μ(d) = μ(n)²` for `n ≥ 1`.

`Nat.sq_mul_squarefree_of_pos` writes `n = b²·a` with `a` squarefree; the `d` with `d² ∣ n`
are EXACTLY the divisors of `b`, so the sum is `[b = 1]`, and `b = 1 ↔ Squarefree n`.

The must-FAIL control (measured): with `μ(n)²` → `μ(n)` at `n = 2` the LHS is `1` and the
RHS `−1`. -/
theorem sum_moebius_sq_dvd_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n), (moebius d : ℝ)
      = (moebius n : ℝ) ^ 2 := by
  classical
  obtain ⟨a, b, ha0, hb0, hab, hasq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hset : (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, _⟩, hdvd⟩
      refine ⟨dvd_of_sq_dvd_sq_mul hasq ?_, by omega⟩
      rw [hab]
      exact hdvd
    · rintro ⟨hdb, _⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdb hb0
      have hdb' : d ≤ b := Nat.le_of_dvd hb0 hdb
      have hbn : b ≤ n := by nlinarith [hab, ha0, hb0]
      refine ⟨⟨hd1, by omega⟩, ?_⟩
      rw [← hab]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hdb 2) a
  have hiff : b = 1 ↔ Squarefree n := by
    constructor
    · rintro rfl
      have han : a = n := by simpa using hab
      exact han ▸ hasq
    · intro hsq
      exact Nat.isUnit_iff.mp (hsq b ⟨a, by rw [← hab]; ring⟩)
  have hmn : ((moebius n : ℝ)) ^ 2 = if Squarefree n then (1 : ℝ) else 0 := by
    have h := moebius_sq (n := n)
    by_cases hs : Squarefree n
    · rw [if_pos hs] at h ⊢
      exact_mod_cast h
    · rw [if_neg hs] at h ⊢
      exact_mod_cast h
  rw [hset, sum_divisors_moebius_real, hmn]
  by_cases hb1 : b = 1
  · rw [if_pos hb1, if_pos (hiff.mp hb1)]
  · rw [if_neg hb1, if_neg fun hs => hb1 (hiff.mpr hs)]

/-- `Σ_{k ∣ r} μ(k)/k = φ(r)/r` — only the squarefree divisors survive, they are the
subsets of `r.primeFactors`, and `Finset.prod_one_add` turns the powerset sum into
`∏_{p ∣ r}(1 − 1/p)`, which is `φ(r)/r`. -/
private lemma sum_moebius_div_eq_totient_div (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ r.divisors, (moebius k : ℝ) / k = (Nat.totient r : ℝ) / r := by
  classical
  have hr0 : r ≠ 0 := by omega
  have hfilter : ∑ k ∈ r.divisors, (moebius k : ℝ) / k
      = ∑ k ∈ r.divisors.filter Squarefree, (moebius k : ℝ) / k := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun k hk hk' => ?_).symm
    have hns : ¬ Squarefree k := fun hs => hk' (Finset.mem_filter.mpr ⟨hk, hs⟩)
    rw [moebius_eq_zero_of_not_squarefree hns, Int.cast_zero, zero_div]
  rw [hfilter, Nat.sum_divisors_filter_squarefree hr0, totient_div_eq_prod_one_sub r hr]
  have hbridge : (UniqueFactorizationMonoid.normalizedFactors r).toFinset = r.primeFactors := by
    rw [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
  rw [hbridge]
  have hform : ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ))
      = ∏ p ∈ r.primeFactors, (1 + -(1 / (p : ℝ))) := by
    refine Finset.prod_congr rfl fun p _ => by ring
  rw [hform, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hsub : t ⊆ r.primeFactors := Finset.mem_powerset.mp ht
  have hprime : ∀ p ∈ t, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
  have hpw : (↑t : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hne
  have hval : t.val.prod = ∏ p ∈ t, p := Finset.prod_val t
  rw [hval, isMultiplicative_moebius.map_prod (fun p : ℕ => p) t hpw, Nat.cast_prod,
    Int.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [moebius_apply_prime (hprime p hp)]
  push_cast
  ring

/-- `|⌊y⌋₊ − y| ≤ min(1, y)` for `y ≥ 0`. -/
private lemma abs_floor_sub_le_min {y : ℝ} (hy : 0 ≤ y) :
    |((⌊y⌋₊ : ℕ) : ℝ) - y| ≤ min 1 y := by
  have h1 : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy
  have h2 : y < ((⌊y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one y
  have h3 : (0 : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonpos (by linarith), neg_sub]
  exact le_min (by linarith) (by linarith)

/-- `min(1, y) ≤ y^{1/4}` for `y ≥ 0` (K37). -/
private lemma min_one_le_rpow_quarter {y : ℝ} (hy : 0 ≤ y) : min 1 y ≤ y ^ (1/4 : ℝ) := by
  rcases le_or_gt y 1 with h | h
  · rcases eq_or_lt_of_le hy with rfl | hy0
    · rw [Real.zero_rpow (by norm_num), min_eq_right zero_le_one]
    · rw [min_eq_right h]
      calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
        _ ≤ y ^ (1/4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy0 h (by norm_num)
  · rw [min_eq_left h.le]
    have hle := Real.rpow_le_rpow (zero_le_one) h.le (by norm_num : (0 : ℝ) ≤ 1/4)
    rwa [Real.one_rpow] at hle

/-- **P2.** `|#{m ≤ X : (m,r)=1} − (φ(r)/r)·X| ≤ X^{1/4}·σ_{−1/4}(r)` for `X ≥ 0`.

`sum_coprime_eq_moebius_multiples` at `F ≡ 1` writes the count as `Σ_{k ∣ r} μ(k)⌊X/k⌋₊`,
the main term as `Σ_{k ∣ r} μ(k)(X/k)` (`Σ μ(k)/k = φ(r)/r`), and the difference is
controlled termwise by `|⌊y⌋₊ − y| ≤ min(1, y) ≤ y^{1/4}` at `y = X/k`.

The must-FAIL control (measured): with the density DROPPED (`(φ(r)/r)·X` → `X`), the ratio
to `X^{1/4}σ(r)` is `6.5399 / 24.1438 / 39.1517` at `(r, X) = (6, 10²) / (30, 10³) /
(30030, 10⁴)` — UNBOUNDED.

Two mutants were MEASURED and STRUCK, and are recorded here so nobody re-proposes them as
controls. `X^{1/4}` → `X^0`: the error `|#{e ≤ X, (e,r)=1} − (φ(r)/r)X|` reads
`1.81 / 1.08 / 0.75` at `(30030, 10³) / (30030, 10⁴) / (510510, 10⁴)` against
`σ = 20.65 / 20.65 / 30.81` — the Möbius-weighted fractional parts cancel far below
`2^{ω(r)}`, so this row's exponent is a CONVENIENCE for H5a's assembly, not a sharp claim.
`σ(r)` → `1`: max ratio `0.723` on the refuter's grid. Neither FAILS. -/
theorem abs_card_coprime_sub_le (r : ℕ) (hr : 1 ≤ r) (X : ℝ) (hX : 0 ≤ X) :
    |(((Finset.Icc 1 ⌊X⌋₊).filter (fun m => Nat.Coprime m r)).card : ℝ)
        - (Nat.totient r : ℝ) / r * X|
      ≤ X ^ (1/4 : ℝ) * sigmaQ r := by
  classical
  have hcard : (((Finset.Icc 1 ⌊X⌋₊).filter (fun m => Nat.Coprime m r)).card : ℝ)
      = ∑ k ∈ r.divisors, (moebius k : ℝ) * ((⌊X⌋₊ / k : ℕ) : ℝ) := by
    have h := sum_coprime_eq_moebius_multiples r ⌊X⌋₊ hr (fun _ => (1 : ℝ))
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    norm_num
  have hmain : (Nat.totient r : ℝ) / r * X = ∑ k ∈ r.divisors, (moebius k : ℝ) * (X / k) := by
    rw [← sum_moebius_div_eq_totient_div r hr, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hcard, hmain, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ r.divisors,
          ((moebius k : ℝ) * ((⌊X⌋₊ / k : ℕ) : ℝ) - (moebius k : ℝ) * (X / k))|
      ≤ ∑ k ∈ r.divisors,
          |(moebius k : ℝ) * ((⌊X⌋₊ / k : ℕ) : ℝ) - (moebius k : ℝ) * (X / k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ r.divisors, X ^ (1/4 : ℝ) * (k : ℝ) ^ (-(1/4 : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
        have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        have hy : (0 : ℝ) ≤ X / (k : ℝ) := by positivity
        have hfl : ((⌊X⌋₊ / k : ℕ) : ℝ) = ((⌊X / (k : ℝ)⌋₊ : ℕ) : ℝ) := by
          rw [Nat.floor_div_natCast]
        have hmu : |((moebius k : ℤ) : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        rw [hfl, ← mul_sub, abs_mul]
        calc |((moebius k : ℤ) : ℝ)| * |((⌊X / (k : ℝ)⌋₊ : ℕ) : ℝ) - X / (k : ℝ)|
            ≤ 1 * (X / (k : ℝ)) ^ (1/4 : ℝ) := by
              refine mul_le_mul hmu ?_ (abs_nonneg _) zero_le_one
              exact le_trans (abs_floor_sub_le_min hy) (min_one_le_rpow_quarter hy)
          _ = X ^ (1/4 : ℝ) * (k : ℝ) ^ (-(1/4 : ℝ)) := by
              rw [one_mul, div_rpow_neg hX hk0.le]
    _ = X ^ (1/4 : ℝ) * sigmaQ r := by
        rw [sigmaQ, Finset.mul_sum]

/-- `|μ(n)/n²| ≤ 1/n²` (at `n = 0` both sides are `0`). -/
private lemma abs_moebius_div_sq_le (n : ℕ) :
    |(moebius n : ℝ) / (n : ℝ) ^ 2| ≤ 1 / (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr hmu

/-- The `1/n²`-dominated tail: a series bounded termwise by `1/n²` differs from its partial
sum over `[1, D]` by at most `2/(D + 1)` (`sum_Ioo_inv_sq_le` on every finite window,
passed to the tsum by `Real.tsum_le_of_sum_le`). -/
private lemma abs_tsum_sub_sum_le {g : ℕ → ℝ} (hg : Summable g)
    (hb : ∀ n : ℕ, |g n| ≤ 1 / (n : ℝ) ^ 2) (D : ℕ) :
    |(∑' n : ℕ, g n) - ∑ n ∈ Finset.Icc 1 D, g n| ≤ 2 / ((D : ℝ) + 1) := by
  classical
  set b : ℕ → ℝ := fun n => if n ∈ Finset.Icc 1 D then 0 else 1 / (n : ℝ) ^ 2 with hbdef
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    rw [hbdef]
    dsimp only
    split_ifs
    · exact le_refl 0
    · positivity
  have hbsum : Summable b := by
    refine Summable.of_nonneg_of_le hb0 (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr (by norm_num) : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2)
    rw [hbdef]
    dsimp only
    split_ifs
    · positivity
    · exact le_refl _
  have hbtsum : (∑' n : ℕ, b n) ≤ 2 / ((D : ℝ) + 1) := by
    refine Real.tsum_le_of_sum_le hb0 fun s => ?_
    have hs' : ∑ n ∈ s, b n = ∑ n ∈ s.filter (fun n => D < n), b n := by
      refine (Finset.sum_filter_of_ne fun n _ hne => ?_).symm
      by_contra hcon
      rw [not_lt] at hcon
      refine hne ?_
      rw [hbdef]
      dsimp only
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [if_neg (by simp)]
        norm_num
      · rw [if_pos (Finset.mem_Icc.mpr ⟨hn0, hcon⟩)]
    have hsubset : s.filter (fun n => D < n) ⊆ Finset.Ioo D (s.sup id + 1) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Finset.mem_Ioo]
      have hle : n ≤ s.sup id := Finset.le_sup (f := id) hn.1
      exact ⟨hn.2, by omega⟩
    rw [hs']
    calc ∑ n ∈ s.filter (fun n => D < n), b n
        ≤ ∑ n ∈ Finset.Ioo D (s.sup id + 1), b n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i _ _ => hb0 i
      _ ≤ ∑ n ∈ Finset.Ioo D (s.sup id + 1), (((n : ℝ)) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [hbdef]
          dsimp only
          split_ifs
          · positivity
          · rw [one_div]
      _ ≤ 2 / ((D : ℝ) + 1) := sum_Ioo_inv_sq_le D (s.sup id + 1)
  have hg' : Summable (fun n : ℕ => if n ∈ Finset.Icc 1 D then g n else 0) :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 D) fun n hn => if_neg hn
  have hsum' : (∑' n : ℕ, (if n ∈ Finset.Icc 1 D then g n else 0))
      = ∑ n ∈ Finset.Icc 1 D, g n := by
    rw [tsum_eq_sum (s := Finset.Icc 1 D) fun n hn => if_neg hn]
    exact Finset.sum_congr rfl fun n hn => if_pos hn
  have hdiff : (∑' n : ℕ, g n) - ∑ n ∈ Finset.Icc 1 D, g n
      = ∑' n : ℕ, (g n - (if n ∈ Finset.Icc 1 D then g n else 0)) := by
    rw [hg.tsum_sub hg', hsum']
  have hpt : ∀ n : ℕ, |g n - (if n ∈ Finset.Icc 1 D then g n else 0)| ≤ b n := by
    intro n
    by_cases hn : n ∈ Finset.Icc 1 D
    · rw [if_pos hn, sub_self, abs_zero, hbdef]
      dsimp only
      rw [if_pos hn]
    · rw [if_neg hn, sub_zero, hbdef]
      dsimp only
      rw [if_neg hn]
      exact hb n
  have habs : Summable (fun n : ℕ => |g n - (if n ∈ Finset.Icc 1 D then g n else 0)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt hbsum
  rw [hdiff]
  calc |∑' n : ℕ, (g n - (if n ∈ Finset.Icc 1 D then g n else 0))|
      ≤ ∑' n : ℕ, |g n - (if n ∈ Finset.Icc 1 D then g n else 0)| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun n : ℕ => g n - (if n ∈ Finset.Icc 1 D then g n else 0)) (by simpa using habs)
        simpa using h
    _ ≤ ∑' n : ℕ, b n := Summable.tsum_le_tsum hpt habs hbsum
    _ ≤ 2 / ((D : ℝ) + 1) := hbtsum

/-- **H5a (the H freeze's row, verbatim).** `|Σ_{m ≤ M, (m,r)=1} μ²(m) − ρ₀(r/κ(r))M|
≤ C·√M·σ_{−1/4}(r)`, with `C = 4`.

P1 opens `μ²(m)` as `Σ_{d² ∣ m} μ(d)`; the swap sends the pair `(m, d)` to
`d ≤ √N`, `m = d²e`, and the coprimality splits as `(d, r) = 1 ∧ (e, r) = 1`; P2 at
`X = M/d²` supplies each inner count with error `X^{1/4}σ(r) = M^{1/4}d^{−1/2}σ(r)`, and
`Σ_{d ≤ √M} d^{−1/2} ≤ 2·M^{1/4}` (NOT `2√M` — the sum runs to `⌊√M⌋₊, not to M) turns the
total error into `2√M·σ(r)`. The main term is `(φ(r)/r)·M` times the partial sum of the
coprime subseries, whose tail costs `2M/(D+1) ≤ 2√M`, and T6 identifies the full series as
`ρ₀(r/κ(r))`.

The must-FAIL control (measured): with the density `ρ₀·(r/κ(r))` → `ρ₀·(φ(r)/r)`, the
ratio `|count − main|/(√M·σ(6))` at `r = 6` and `M = 10² / 10⁴ / 10⁶` is
`0.0186 / 0.0104 / 0.0002` FROZEN (counts 31 / 3043 / 303963) against
`0.3314 / 3.1379 / 31.2749` MUTANT — the GROWTH is the kill; a fixed-`M` comparison
would pass at a large enough `C`. -/
theorem sqf_coprime_count_eq : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → ∀ M : ℝ, 1 ≤ M →
    |∑ m ∈ (Finset.Icc 1 ⌊M⌋₊).filter (fun m => Nat.Coprime m r), (moebius m : ℝ) ^ 2
        - rho0 * ((r : ℝ) / kappa r) * M| ≤ C * M ^ (1/2 : ℝ) * sigmaQ r := by
  classical
  refine ⟨4, by norm_num, fun r hr M hM => ?_⟩
  set N : ℕ := ⌊M⌋₊ with hNdef
  set D : ℕ := Nat.sqrt N with hDdef
  have hM0 : (0 : ℝ) < M := by linarith
  have hNM : (N : ℝ) ≤ M := Nat.floor_le hM0.le
  have hMN : M < (N : ℝ) + 1 := Nat.lt_floor_add_one M
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hM)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hsig1 : (1 : ℝ) ≤ sigmaQ r := one_le_sigmaQ r hr
  have hphi0 : (0 : ℝ) ≤ (Nat.totient r : ℝ) / r := by positivity
  have hphi1 : (Nat.totient r : ℝ) / r ≤ 1 := by
    rw [div_le_one hr0]
    exact_mod_cast Nat.totient_le r
  -- the coprime-restricted summand of the subseries
  set g : ℕ → ℝ := fun n => if Nat.Coprime n r then (moebius n : ℝ) / (n : ℝ) ^ 2 else 0
    with hgdef
  have hgsum : Summable g := summable_coprime_indicator summable_abs_moebius_div_sq r
  have hgb : ∀ n : ℕ, |g n| ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rw [hgdef]
    dsimp only
    split_ifs
    · exact abs_moebius_div_sq_le n
    · rw [abs_zero]
      positivity
  -- STEP 1-3: the swap
  have hstep1 : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m r), (moebius m : ℝ) ^ 2
      = ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ^ 2 ∣ m),
          (if Nat.Coprime m r then (moebius d : ℝ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    by_cases hc : Nat.Coprime m r
    · rw [if_pos hc, Finset.sum_congr rfl (fun d _ => if_pos hc)]
      exact (sum_moebius_sq_dvd_eq m hm1).symm
    · rw [if_neg hc, Finset.sum_congr rfl (fun d _ => if_neg hc), Finset.sum_const, smul_zero]
  have hstep2 : ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ^ 2 ∣ m),
          (if Nat.Coprime m r then (moebius d : ℝ) else 0)
      = ∑ d ∈ Finset.Icc 1 D, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m),
          (if Nat.Coprime m r then (moebius d : ℝ) else 0) := by
    refine Finset.sum_comm' ?_
    intro m d
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, ⟨hd1, _⟩, hdvd⟩
      have hd2m : d ^ 2 ≤ m := Nat.le_of_dvd (by omega) hdvd
      refine ⟨⟨⟨hm1, hmN⟩, hdvd⟩, hd1, ?_⟩
      rw [hDdef]
      exact Nat.le_sqrt.mpr (by nlinarith)
    · rintro ⟨⟨⟨hm1, hmN⟩, hdvd⟩, hd1, _⟩
      have hd2m : d ^ 2 ≤ m := Nat.le_of_dvd (by omega) hdvd
      exact ⟨⟨hm1, hmN⟩, ⟨hd1, by nlinarith⟩, hdvd⟩
  have hstep3 : ∀ d : ℕ, 1 ≤ d →
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ^ 2 ∣ m),
          (if Nat.Coprime m r then (moebius d : ℝ) else 0)
        = (moebius d : ℝ) * ∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0) := by
    intro d hd1
    have hd2 : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd1
    rw [sum_dvd_reindex hd2 (fun m => if Nat.Coprime m r then (moebius d : ℝ) else 0),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hc : Nat.Coprime (d ^ 2 * e) r
    · rw [if_pos hc, if_pos hc, mul_one]
    · rw [if_neg hc, if_neg hc, mul_zero]
  have hLHS : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m r), (moebius m : ℝ) ^ 2
      = ∑ d ∈ Finset.Icc 1 D, (moebius d : ℝ) * ∑ e ∈ Finset.Icc 1 (N / d ^ 2),
          (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0) := by
    rw [hstep1, hstep2]
    exact Finset.sum_congr rfl fun d hd => hstep3 d (Finset.mem_Icc.mp hd).1
  -- STEP 4: the per-`d` comparison against P2
  have hper : ∀ d ∈ Finset.Icc 1 D,
      |(moebius d : ℝ) * (∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
        - (Nat.totient r : ℝ) / r * M * g d|
      ≤ M ^ (1/4 : ℝ) * sigmaQ r * (d : ℝ) ^ (-(1/2) : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hcastd : ((d ^ 2 : ℕ) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
    have hX0 : (0 : ℝ) ≤ M / ((d ^ 2 : ℕ) : ℝ) := by rw [hcastd]; positivity
    have hfl : ⌊M / ((d ^ 2 : ℕ) : ℝ)⌋₊ = N / d ^ 2 := by
      rw [Nat.floor_div_natCast]
    have hXq : (M / ((d ^ 2 : ℕ) : ℝ)) ^ (1/4 : ℝ)
        = M ^ (1/4 : ℝ) * (d : ℝ) ^ (-(1/2) : ℝ) := by
      rw [div_rpow_neg hM0.le (by positivity) (1/4 : ℝ), hcastd,
        ← Real.rpow_natCast (d : ℝ) 2, ← Real.rpow_mul hdR.le]
      norm_num
    by_cases hcd : Nat.Coprime d r
    · have hcd2 : Nat.Coprime (d ^ 2) r := Nat.Coprime.pow_left 2 hcd
      have hinner : (∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
          = (((Finset.Icc 1 (N / d ^ 2)).filter (fun e => Nat.Coprime e r)).card : ℝ) := by
        have hpt : ∀ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0)
              = (if Nat.Coprime e r then (1 : ℝ) else 0) := by
          intro e _
          by_cases hc : Nat.Coprime e r
          · rw [if_pos (Nat.Coprime.mul_left hcd2 hc), if_pos hc]
          · have hne : ¬ Nat.Coprime (d ^ 2 * e) r := fun hcon =>
              hc (Nat.Coprime.coprime_dvd_left (dvd_mul_left e (d ^ 2)) hcon)
            rw [if_neg hne, if_neg hc]
        rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          mul_one]
      have hP2 := abs_card_coprime_sub_le r hr (M / ((d ^ 2 : ℕ) : ℝ)) hX0
      rw [hfl] at hP2
      have hgd : g d = (moebius d : ℝ) / (d : ℝ) ^ 2 := by
        rw [hgdef]; dsimp only; rw [if_pos hcd]
      have hmaind : (Nat.totient r : ℝ) / r * M * g d
          = (moebius d : ℝ) * ((Nat.totient r : ℝ) / r * (M / ((d ^ 2 : ℕ) : ℝ))) := by
        rw [hgd, hcastd]
        field_simp
      rw [hinner, hmaind, ← mul_sub, abs_mul]
      have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc |((moebius d : ℤ) : ℝ)|
              * |(((Finset.Icc 1 (N / d ^ 2)).filter (fun e => Nat.Coprime e r)).card : ℝ)
                  - (Nat.totient r : ℝ) / r * (M / ((d ^ 2 : ℕ) : ℝ))|
          ≤ 1 * ((M / ((d ^ 2 : ℕ) : ℝ)) ^ (1/4 : ℝ) * sigmaQ r) := by
            refine mul_le_mul hmu hP2 (abs_nonneg _) zero_le_one
        _ = M ^ (1/4 : ℝ) * sigmaQ r * (d : ℝ) ^ (-(1/2) : ℝ) := by
            rw [one_mul, hXq]; ring
    · have hzero : (∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0)) = 0 := by
        refine Finset.sum_eq_zero fun e _ => ?_
        refine if_neg fun hc => hcd ?_
        exact Nat.Coprime.coprime_dvd_left
          (dvd_trans (dvd_pow_self d (by norm_num)) (Dvd.intro e rfl)) hc
      have hgd : g d = 0 := by
        rw [hgdef]; dsimp only; rw [if_neg hcd]
      rw [hzero, hgd, mul_zero, mul_zero, sub_zero, abs_zero]
      have : (0 : ℝ) ≤ (d : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg hdR.le _
      have hMq : (0 : ℝ) ≤ M ^ (1/4 : ℝ) := Real.rpow_nonneg hM0.le _
      positivity
  -- STEP 5: sum the per-`d` errors
  have hDM : (D : ℝ) ≤ M ^ (1/2 : ℝ) := by
    have h1 : ((D : ℝ)) ^ 2 ≤ M := by
      have hnat : D * D ≤ N := Nat.sqrt_le N
      have : ((D * D : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnat
      push_cast at this
      nlinarith
    have h2 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((D : ℝ)) ^ 2) h1
      (by norm_num : (0 : ℝ) ≤ 1/2)
    rwa [← Real.rpow_natCast (D : ℝ) 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (D : ℝ)),
      show ((2 : ℕ) : ℝ) * (1/2 : ℝ) = 1 by norm_num, Real.rpow_one] at h2
  have hD2 : (D : ℝ) ^ (1/2 : ℝ) ≤ M ^ (1/4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (D : ℝ)) hDM
      (by norm_num : (0 : ℝ) ≤ 1/2)
    rwa [← Real.rpow_mul hM0.le, show (1/2 : ℝ) * (1/2 : ℝ) = 1/4 by norm_num] at h
  have hMsplit : M ^ (1/4 : ℝ) * M ^ (1/4 : ℝ) = M ^ (1/2 : ℝ) := by
    rw [← Real.rpow_add hM0, show (1/4 : ℝ) + (1/4 : ℝ) = 1/2 by norm_num]
  have herr : |(∑ d ∈ Finset.Icc 1 D, (moebius d : ℝ) * ∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
        - ∑ d ∈ Finset.Icc 1 D, (Nat.totient r : ℝ) / r * M * g d|
      ≤ 2 * M ^ (1/2 : ℝ) * sigmaQ r := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 D, ((moebius d : ℝ) * (∑ e ∈ Finset.Icc 1 (N / d ^ 2),
              (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
            - (Nat.totient r : ℝ) / r * M * g d)|
        ≤ ∑ d ∈ Finset.Icc 1 D, |(moebius d : ℝ) * (∑ e ∈ Finset.Icc 1 (N / d ^ 2),
              (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
            - (Nat.totient r : ℝ) / r * M * g d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 D, M ^ (1/4 : ℝ) * sigmaQ r * (d : ℝ) ^ (-(1/2) : ℝ) :=
          Finset.sum_le_sum hper
      _ = M ^ (1/4 : ℝ) * sigmaQ r * ∑ d ∈ Finset.Icc 1 D, (d : ℝ) ^ (-(1/2) : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ M ^ (1/4 : ℝ) * sigmaQ r * (2 * (D : ℝ) ^ ((1/2) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (sum_rpow_neg_half_le D) ?_
          have : (0 : ℝ) ≤ M ^ (1/4 : ℝ) := Real.rpow_nonneg hM0.le _
          nlinarith [hsig1]
      _ ≤ M ^ (1/4 : ℝ) * sigmaQ r * (2 * M ^ (1/4 : ℝ)) := by
          have hpos : (0 : ℝ) ≤ M ^ (1/4 : ℝ) * sigmaQ r := by
            have : (0 : ℝ) ≤ M ^ (1/4 : ℝ) := Real.rpow_nonneg hM0.le _
            nlinarith [hsig1]
          nlinarith [hD2, hpos]
      _ = 2 * M ^ (1/2 : ℝ) * sigmaQ r := by
          rw [← hMsplit]; ring
  -- STEP 6-7: the main term against the full subseries and T6
  have hmainsum : ∑ d ∈ Finset.Icc 1 D, (Nat.totient r : ℝ) / r * M * g d
      = (Nat.totient r : ℝ) / r * M * ∑ d ∈ Finset.Icc 1 D, g d := by
    rw [Finset.mul_sum]
  have hT6 := totient_div_mul_coprimeSeries_moebius_div_sq r hr
  have hser : (Nat.totient r : ℝ) / r * (∑' n : ℕ, g n) = rho0 * ((r : ℝ) / kappa r) := hT6
  have hMD : M ^ (1/2 : ℝ) ≤ (D : ℝ) + 1 := by
    have hnat : N < (D + 1) * (D + 1) := Nat.lt_succ_sqrt N
    have hcast : (N : ℝ) + 1 ≤ ((D : ℝ) + 1) ^ 2 := by
      have : (N : ℝ) + 1 ≤ (((D + 1) * (D + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this
      nlinarith
    have h1 : M ≤ ((D : ℝ) + 1) ^ 2 := by linarith
    have h2 := Real.rpow_le_rpow hM0.le h1 (by norm_num : (0 : ℝ) ≤ 1/2)
    rwa [← Real.rpow_natCast ((D : ℝ) + 1) 2,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (D : ℝ) + 1),
      show ((2 : ℕ) : ℝ) * (1/2 : ℝ) = 1 by norm_num, Real.rpow_one] at h2
  have htail : |(∑' n : ℕ, g n) - ∑ n ∈ Finset.Icc 1 D, g n| ≤ 2 / ((D : ℝ) + 1) :=
    abs_tsum_sub_sum_le hgsum hgb D
  have hmainerr : |(Nat.totient r : ℝ) / r * M * (∑ d ∈ Finset.Icc 1 D, g d)
      - rho0 * ((r : ℝ) / kappa r) * M| ≤ 2 * M ^ (1/2 : ℝ) * sigmaQ r := by
    have hrw : (Nat.totient r : ℝ) / r * M * (∑ d ∈ Finset.Icc 1 D, g d)
        - rho0 * ((r : ℝ) / kappa r) * M
        = (Nat.totient r : ℝ) / r * M * ((∑ d ∈ Finset.Icc 1 D, g d) - (∑' n : ℕ, g n)) := by
      rw [← hser]; ring
    rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient r : ℝ) / r * M),
      abs_sub_comm]
    have hDpos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    have hstep : M / ((D : ℝ) + 1) ≤ M ^ (1/2 : ℝ) := by
      rw [div_le_iff₀ hDpos]
      calc M = M ^ (1/2 : ℝ) * M ^ (1/2 : ℝ) := by
            rw [← Real.rpow_add hM0, show (1/2 : ℝ) + (1/2 : ℝ) = 1 by norm_num, Real.rpow_one]
        _ ≤ M ^ (1/2 : ℝ) * ((D : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hMD (Real.rpow_nonneg hM0.le _)
    calc (Nat.totient r : ℝ) / r * M * |(∑' n : ℕ, g n) - ∑ d ∈ Finset.Icc 1 D, g d|
        ≤ 1 * M * (2 / ((D : ℝ) + 1)) := by
          refine mul_le_mul (mul_le_mul hphi1 (le_refl M) hM0.le zero_le_one) htail
            (abs_nonneg _) (by positivity)
      _ = 2 * (M / ((D : ℝ) + 1)) := by field_simp
      _ ≤ 2 * M ^ (1/2 : ℝ) := by linarith
      _ ≤ 2 * M ^ (1/2 : ℝ) * sigmaQ r := by
          have : (0 : ℝ) ≤ M ^ (1/2 : ℝ) := Real.rpow_nonneg hM0.le _
          nlinarith [hsig1]
  -- STEP 8: assemble
  rw [hLHS]
  have hsplit : (∑ d ∈ Finset.Icc 1 D, (moebius d : ℝ) * ∑ e ∈ Finset.Icc 1 (N / d ^ 2),
          (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
        - rho0 * ((r : ℝ) / kappa r) * M
      = ((∑ d ∈ Finset.Icc 1 D, (moebius d : ℝ) * ∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
          - ∑ d ∈ Finset.Icc 1 D, (Nat.totient r : ℝ) / r * M * g d)
        + ((Nat.totient r : ℝ) / r * M * (∑ d ∈ Finset.Icc 1 D, g d)
          - rho0 * ((r : ℝ) / kappa r) * M) := by
    rw [hmainsum]; ring
  rw [hsplit]
  calc |((∑ d ∈ Finset.Icc 1 D, (moebius d : ℝ) * ∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
          - ∑ d ∈ Finset.Icc 1 D, (Nat.totient r : ℝ) / r * M * g d)
        + ((Nat.totient r : ℝ) / r * M * (∑ d ∈ Finset.Icc 1 D, g d)
          - rho0 * ((r : ℝ) / kappa r) * M)|
      ≤ |(∑ d ∈ Finset.Icc 1 D, (moebius d : ℝ) * ∑ e ∈ Finset.Icc 1 (N / d ^ 2),
            (if Nat.Coprime (d ^ 2 * e) r then (1 : ℝ) else 0))
          - ∑ d ∈ Finset.Icc 1 D, (Nat.totient r : ℝ) / r * M * g d|
        + |(Nat.totient r : ℝ) / r * M * (∑ d ∈ Finset.Icc 1 D, g d)
          - rho0 * ((r : ℝ) / kappa r) * M| := abs_add_le _ _
    _ ≤ 2 * M ^ (1/2 : ℝ) * sigmaQ r + 2 * M ^ (1/2 : ℝ) * sigmaQ r :=
        add_le_add herr hmainerr
    _ = 4 * M ^ (1/2 : ℝ) * sigmaQ r := by ring

/-- The telescoping step of `Σ f^{−3/4}` (the landed recipe, re-derived). -/
private lemma rpow_step_three_quarter (t : ℝ) (ht : 0 ≤ t) :
    (t + 1) ^ (-(3/4) : ℝ) ≤ 4 * (t + 1) ^ ((1/4) : ℝ) - 4 * t ^ ((1/4) : ℝ) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hcube : ((t + 1) ^ ((1/4) : ℝ)) ^ 3 = (t + 1) ^ ((3/4) : ℝ) := by
    rw [rpow_pow_nat ht1.le, show ((1/4 : ℝ)) * ((3 : ℕ) : ℝ) = (3/4 : ℝ) by norm_num]
  have hinv : (t + 1) ^ (-(3/4) : ℝ) = ((t + 1) ^ ((3/4) : ℝ))⁻¹ := Real.rpow_neg ht1.le _
  rw [hinv, ← hcube]
  set a : ℝ := (t + 1) ^ ((1/4) : ℝ) with ha
  set b : ℝ := t ^ ((1/4) : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos ht1 _
  have hb0 : (0 : ℝ) ≤ b := Real.rpow_nonneg ht _
  have ha4 : a ^ 4 = t + 1 := by
    rw [ha, rpow_pow_nat ht1.le, show ((1/4 : ℝ)) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hb4 : b ^ 4 = t := by
    rw [hb, rpow_pow_nat ht, show ((1/4 : ℝ)) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have ha3 : (0 : ℝ) < a ^ 3 := by positivity
  rw [inv_eq_one_div, div_le_iff₀ ha3]
  nlinarith [mul_nonneg (sq_nonneg (a - b))
    (show (0 : ℝ) ≤ 3 * a ^ 2 + 2 * a * b + b ^ 2 by positivity), ha4, hb4]

/-- `Σ_{f ≤ N} f^{−3/4} ≤ 4·N^{1/4}` (the landed recipe, re-derived). -/
private lemma sum_rpow_neg_three_quarter_le (N : ℕ) :
    ∑ f ∈ Finset.Icc 1 N, (f : ℝ) ^ (-(3/4) : ℝ) ≤ 4 * (N : ℝ) ^ ((1/4) : ℝ) := by
  induction N with
  | zero => simp [Real.zero_rpow]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, rpow_step_three_quarter (m : ℝ) (by positivity)]

/-- `log u ≤ 4·u^{1/4}` for `u ≥ 1` (the landed recipe, re-derived). -/
private lemma log_le_four_rpow_quarter {u : ℝ} (hu : 1 ≤ u) :
    Real.log u ≤ 4 * u ^ ((1/4) : ℝ) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : Real.log (u ^ ((1/4) : ℝ)) = (1/4 : ℝ) * Real.log u := Real.log_rpow hu0 _
  have h2 : Real.log (u ^ ((1/4) : ℝ)) ≤ u ^ ((1/4) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 _)
  have h3 : (0 : ℝ) ≤ u ^ ((1/4) : ℝ) := (Real.rpow_pos_of_pos hu0 _).le
  linarith

/-- `Σ_{f ≤ m} 1/f ≤ 1 + log m` (the landed recipe, re-derived). -/
private lemma sum_inv_le_one_add_log (m : ℕ) :
    ∑ f ∈ Finset.Icc 1 m, ((f : ℝ))⁻¹ ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- `Σ_{f ≤ M} f^{−1/2}·log(2Y/f) ≤ (2 log 2 + 16)·Y^{1/2}` for `M ≤ Y` (the landed
recipe, re-derived). -/
private lemma sum_rpow_neg_half_log_le {Y : ℝ} (hY : 1 ≤ Y) {M : ℕ} (hM : (M : ℝ) ≤ Y) :
    ∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * Y / (f : ℝ))
      ≤ (2 * Real.log 2 + 16) * Y ^ ((1/2) : ℝ) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hbound : ∀ f ∈ Finset.Icc 1 M,
      (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * Y / (f : ℝ))
        ≤ Real.log 2 * (f : ℝ) ^ (-(1/2) : ℝ)
          + 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ) := by
    intro f hf
    have hf1 : 1 ≤ f := (Finset.mem_Icc.mp hf).1
    have hfM : f ≤ M := (Finset.mem_Icc.mp hf).2
    have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf1
    have hfY : (f : ℝ) ≤ Y := le_trans (by exact_mod_cast hfM) hM
    have hYf1 : (1 : ℝ) ≤ Y / (f : ℝ) := (one_le_div hf0).mpr hfY
    have hsplit : Real.log (2 * Y / (f : ℝ)) = Real.log 2 + Real.log (Y / (f : ℝ)) := by
      rw [show 2 * Y / (f : ℝ) = 2 * (Y / (f : ℝ)) by ring,
        Real.log_mul (by norm_num) (by positivity)]
    have hlogb : Real.log (Y / (f : ℝ)) ≤ 4 * (Y / (f : ℝ)) ^ ((1/4) : ℝ) :=
      log_le_four_rpow_quarter hYf1
    have hdr : (Y / (f : ℝ)) ^ ((1/4) : ℝ) = Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(1/4) : ℝ) :=
      div_rpow_neg hY0.le hf0.le _
    have hmul : (f : ℝ) ^ (-(1/2) : ℝ) * (f : ℝ) ^ (-(1/4) : ℝ) = (f : ℝ) ^ (-(3/4) : ℝ) := by
      rw [← Real.rpow_add hf0, show (-(1/2 : ℝ)) + (-(1/4 : ℝ)) = (-(3/4) : ℝ) by norm_num]
    have hfp : (0 : ℝ) < (f : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_pos_of_pos hf0 _
    rw [hsplit, mul_add]
    have hstep : (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (Y / (f : ℝ))
        ≤ 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ) := by
      calc (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (Y / (f : ℝ))
          ≤ (f : ℝ) ^ (-(1/2) : ℝ) * (4 * (Y / (f : ℝ)) ^ ((1/4) : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogb hfp.le
        _ = 4 * Y ^ ((1/4) : ℝ) * ((f : ℝ) ^ (-(1/2) : ℝ) * (f : ℝ) ^ (-(1/4) : ℝ)) := by
            rw [hdr]; ring
        _ = 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ) := by rw [hmul]
    nlinarith [hstep]
  have hMY2 : ((M : ℕ) : ℝ) ^ ((1/2) : ℝ) ≤ Y ^ ((1/2) : ℝ) :=
    Real.rpow_le_rpow (by positivity) hM (by norm_num)
  have hMY4 : ((M : ℕ) : ℝ) ^ ((1/4) : ℝ) ≤ Y ^ ((1/4) : ℝ) :=
    Real.rpow_le_rpow (by positivity) hM (by norm_num)
  have hYY : Y ^ ((1/4) : ℝ) * Y ^ ((1/4) : ℝ) = Y ^ ((1/2) : ℝ) := by
    rw [← Real.rpow_add hY0, show ((1/4 : ℝ)) + ((1/4 : ℝ)) = ((1/2) : ℝ) by norm_num]
  have hY4 : (0 : ℝ) ≤ Y ^ ((1/4) : ℝ) := Real.rpow_nonneg hY0.le _
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc ∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * Y / (f : ℝ))
      ≤ ∑ f ∈ Finset.Icc 1 M, (Real.log 2 * (f : ℝ) ^ (-(1/2) : ℝ)
          + 4 * Y ^ ((1/4) : ℝ) * (f : ℝ) ^ (-(3/4) : ℝ)) := Finset.sum_le_sum hbound
    _ = Real.log 2 * (∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(1/2) : ℝ))
          + 4 * Y ^ ((1/4) : ℝ) * (∑ f ∈ Finset.Icc 1 M, (f : ℝ) ^ (-(3/4) : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.log 2 * (2 * ((M : ℕ) : ℝ) ^ ((1/2) : ℝ))
          + 4 * Y ^ ((1/4) : ℝ) * (4 * ((M : ℕ) : ℝ) ^ ((1/4) : ℝ)) := by
        gcongr
        · exact sum_rpow_neg_half_le M
        · exact sum_rpow_neg_three_quarter_le M
    _ ≤ Real.log 2 * (2 * Y ^ ((1/2) : ℝ)) + 4 * Y ^ ((1/4) : ℝ) * (4 * Y ^ ((1/4) : ℝ)) := by
        gcongr
    _ = (2 * Real.log 2 + 16) * Y ^ ((1/2) : ℝ) := by rw [← hYY]; ring

/-- **The general discrete Abel identity** over `[1, N]`:
`Σ_{m ≤ N} a_m G(m) = A_N·G(N) − Σ_{n < N} A_n·(G(n+1) − G(n))` with `A_n = Σ_{m ≤ n} a_m`.
(The landed `mwWeighted_abel` is weight-`1/n`-specific; this is the general form.) -/
private lemma abel_sum (a G : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, a m * G m
      = (∑ m ∈ Finset.Icc 1 N, a m) * G N
        - ∑ n ∈ Finset.Ico 1 N, (∑ m ∈ Finset.Icc 1 n, a m) * (G (n + 1) - G n) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_Ico_succ_top hn, ih]
    ring

/-- The telescoping sum `Σ_{m ≤ N}(G(m+1) − G(m)) = G(N+1) − G(1)`. -/
private lemma sum_telescope_nat (G : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, (G (m + 1) - G m) = G (N + 1) - G 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    ring

/-- `F(y) = y·((log y − 1 + α)(log y − 1 + β) + 1)` has derivative
`(log y + α)(log y + β)` at every `y > 0` — the antiderivative An's partial summation
needs, written out so no integral is ever formed. -/
private lemma hasDerivAt_bigF (α β : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y * ((Real.log y - 1 + α) * (Real.log y - 1 + β) + 1))
      ((Real.log x + α) * (Real.log x + β)) x := by
  have hxne : x ≠ 0 := hx.ne'
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hxne
  have h1 : HasDerivAt (fun y : ℝ => Real.log y - 1 + α) x⁻¹ x :=
    (hlog.sub_const 1).add_const α
  have h2 : HasDerivAt (fun y : ℝ => Real.log y - 1 + β) x⁻¹ x :=
    (hlog.sub_const 1).add_const β
  have h4 : HasDerivAt (fun y : ℝ => (Real.log y - 1 + α) * (Real.log y - 1 + β) + 1)
      (x⁻¹ * (Real.log x - 1 + β) + (Real.log x - 1 + α) * x⁻¹) x := (h1.mul h2).add_const 1
  have h5 : HasDerivAt (fun y : ℝ => y * ((Real.log y - 1 + α) * (Real.log y - 1 + β) + 1))
      (1 * ((Real.log x - 1 + α) * (Real.log x - 1 + β) + 1)
        + x * (x⁻¹ * (Real.log x - 1 + β) + (Real.log x - 1 + α) * x⁻¹)) x :=
    (hasDerivAt_id x).mul h4
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hxne
  have h6 : 1 * ((Real.log x - 1 + α) * (Real.log x - 1 + β) + 1)
        + x * (x⁻¹ * (Real.log x - 1 + β) + (Real.log x - 1 + α) * x⁻¹)
      = (Real.log x + α) * (Real.log x + β) := by
    calc 1 * ((Real.log x - 1 + α) * (Real.log x - 1 + β) + 1)
          + x * (x⁻¹ * (Real.log x - 1 + β) + (Real.log x - 1 + α) * x⁻¹)
        = ((Real.log x - 1 + α) * (Real.log x - 1 + β) + 1)
          + (x * x⁻¹) * ((Real.log x - 1 + β) + (Real.log x - 1 + α)) := by ring
      _ = (Real.log x + α) * (Real.log x + β) := by rw [hxx]; ring
  rw [← h6]
  exact h5

/-- The mean-value step for `F`: on `[u, v]` with `0 < u < v` there is `ξ ∈ (u, v)` with
`F(v) − F(u) = (log ξ + α)(log ξ + β)·(v − u)`. -/
private lemma bigF_mvt (α β : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    ∃ ξ ∈ Set.Ioo u v,
      v * ((Real.log v - 1 + α) * (Real.log v - 1 + β) + 1)
        - u * ((Real.log u - 1 + α) * (Real.log u - 1 + β) + 1)
      = (Real.log ξ + α) * (Real.log ξ + β) * (v - u) := by
  have hcont : ContinuousOn (fun y : ℝ => y * ((Real.log y - 1 + α) * (Real.log y - 1 + β) + 1))
      (Set.Icc u v) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hu hy.1
    exact ((hasDerivAt_bigF α β hy0).continuousAt).continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun y : ℝ => y * ((Real.log y - 1 + α) * (Real.log y - 1 + β) + 1))
    (fun y : ℝ => (Real.log y + α) * (Real.log y + β)) huv hcont
    (fun x hx => hasDerivAt_bigF α β (lt_trans hu hx.1))
  refine ⟨ξ, hξ, ?_⟩
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
  rw [hslope]
  field_simp

/-- The per-step bound `|F(m+1) − F(m) − g(m)| ≤ (1/m)(|log m + α| + |log m + β| + 1)`:
the mean value `g(ξ)` at `ξ ∈ (m, m+1)` differs from `g(m)` by `δ(a + b + δ)` with
`0 < δ = log ξ − log m ≤ log(1 + 1/m) ≤ 1/m ≤ 1`. -/
private lemma bigF_step_bound (α β : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    |((m : ℝ) + 1) * ((Real.log ((m : ℝ) + 1) - 1 + α) * (Real.log ((m : ℝ) + 1) - 1 + β) + 1)
        - (m : ℝ) * ((Real.log m - 1 + α) * (Real.log m - 1 + β) + 1)
      - (Real.log m + α) * (Real.log m + β)|
      ≤ (1 / (m : ℝ)) * (|Real.log m + α| + |Real.log m + β| + 1) := by
  have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  obtain ⟨ξ, hξ, hval⟩ := bigF_mvt α β hmpos (by linarith : (m : ℝ) < (m : ℝ) + 1)
  have hξ0 : (0 : ℝ) < ξ := lt_trans hmpos hξ.1
  set δ : ℝ := Real.log ξ - Real.log (m : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ, sub_nonneg]
    exact Real.log_le_log hmpos hξ.1.le
  have hδ1 : δ ≤ 1 / (m : ℝ) := by
    have h1 : Real.log ξ ≤ Real.log ((m : ℝ) + 1) := Real.log_le_log hξ0 hξ.2.le
    have h2 : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
      have hq : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ ((m : ℝ) + 1) / (m : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by linarith) hmpos.ne'] at hq
      have hid : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
        field_simp
        ring
      linarith [hq, hid.le, hid.ge]
    rw [hδ]
    linarith
  have hδle1 : δ ≤ 1 := le_trans hδ1 (by rw [div_le_one hmpos]; linarith)
  have hlogξ : Real.log ξ = Real.log (m : ℝ) + δ := by rw [hδ]; ring
  rw [hval, hlogξ]
  have hexp : (Real.log (m : ℝ) + δ + α) * (Real.log (m : ℝ) + δ + β) * (((m : ℝ) + 1) - (m : ℝ))
      - (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β)
      = δ * ((Real.log (m : ℝ) + α) + (Real.log (m : ℝ) + β) + δ) := by ring
  rw [hexp, abs_mul, abs_of_nonneg hδ0]
  have hb : |(Real.log (m : ℝ) + α) + (Real.log (m : ℝ) + β) + δ|
      ≤ |Real.log (m : ℝ) + α| + |Real.log (m : ℝ) + β| + 1 := by
    calc |(Real.log (m : ℝ) + α) + (Real.log (m : ℝ) + β) + δ|
        ≤ |(Real.log (m : ℝ) + α) + (Real.log (m : ℝ) + β)| + |δ| := abs_add_le _ _
      _ ≤ (|Real.log (m : ℝ) + α| + |Real.log (m : ℝ) + β|) + |δ| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ |Real.log (m : ℝ) + α| + |Real.log (m : ℝ) + β| + 1 := by
          rw [abs_of_nonneg hδ0]
          linarith
  have hnn : (0 : ℝ) ≤ |Real.log (m : ℝ) + α| + |Real.log (m : ℝ) + β| + 1 := by positivity
  exact mul_le_mul hδ1 hb (abs_nonneg _) (by positivity)

/-- `1 ≤ ∏_{p ∣ r}(1 + 1/p)`. -/
private lemma one_le_prod_one_add (r : ℕ) : (1 : ℝ) ≤ ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
  calc (1 : ℝ) = ∏ _p ∈ r.primeFactors, (1 : ℝ) := by rw [Finset.prod_const_one]
    _ ≤ ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
        refine Finset.prod_le_prod (fun p _ => zero_le_one) fun p _ => ?_
        have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith

/-- `r ≤ κ(r)`, hence `0 < r/κ(r) ≤ 1`. -/
private lemma le_kappa (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) ≤ kappa r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have h := kappa_div_eq_prod_one_add r hr
  have h1 := one_le_prod_one_add r
  have : (1 : ℝ) ≤ kappa r / r := by rw [h]; exact h1
  rwa [le_div_iff₀ hr0, one_mul] at this

private lemma div_kappa_pos (r : ℕ) (hr : 1 ≤ r) : (0 : ℝ) < (r : ℝ) / kappa r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk := le_kappa r hr
  exact div_pos hr0 (by linarith)

private lemma div_kappa_le_one (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) / kappa r ≤ 1 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk := le_kappa r hr
  rw [div_le_one (by linarith)]
  exact hk

/-- `|ρ₀| ≤ 2` — the `D = 0` case of the `1/n²`-dominated tail bound. -/
private lemma abs_rho0_le_two : |rho0| ≤ 2 := by
  have h := abs_tsum_sub_sum_le (g := fun n : ℕ => (moebius n : ℝ) / (n : ℝ) ^ 2)
    summable_abs_moebius_div_sq.of_abs abs_moebius_div_sq_le 0
  simpa [rho0] using h

/-- The one-step variation of `g(y) = (log y + α)(log y + β)` on the integers. -/
private lemma g_step_bound (α β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |(Real.log ((n : ℝ) + 1) + α) * (Real.log ((n : ℝ) + 1) + β)
        - (Real.log n + α) * (Real.log n + β)|
      ≤ (1 / (n : ℝ)) * (|Real.log n + α| + |Real.log n + β| + 1) := by
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set δ : ℝ := Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ, sub_nonneg]
    exact Real.log_le_log hnpos (by linarith)
  have hδ1 : δ ≤ 1 / (n : ℝ) := by
    have hq : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ ((n : ℝ) + 1) / (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) hnpos.ne'] at hq
    have hid : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp
      ring
    rw [hδ]
    linarith [hq, hid.le, hid.ge]
  have hlog : Real.log ((n : ℝ) + 1) = Real.log (n : ℝ) + δ := by rw [hδ]; ring
  rw [hlog, show (Real.log (n : ℝ) + δ + α) * (Real.log (n : ℝ) + δ + β)
      - (Real.log (n : ℝ) + α) * (Real.log (n : ℝ) + β)
      = δ * ((Real.log (n : ℝ) + α) + (Real.log (n : ℝ) + β) + δ) by ring, abs_mul,
    abs_of_nonneg hδ0]
  have hδle1 : δ ≤ 1 := le_trans hδ1 (by rw [div_le_one hnpos]; linarith)
  have hb : |(Real.log (n : ℝ) + α) + (Real.log (n : ℝ) + β) + δ|
      ≤ |Real.log (n : ℝ) + α| + |Real.log (n : ℝ) + β| + 1 := by
    calc |(Real.log (n : ℝ) + α) + (Real.log (n : ℝ) + β) + δ|
        ≤ |(Real.log (n : ℝ) + α) + (Real.log (n : ℝ) + β)| + |δ| := abs_add_le _ _
      _ ≤ (|Real.log (n : ℝ) + α| + |Real.log (n : ℝ) + β|) + |δ| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ |Real.log (n : ℝ) + α| + |Real.log (n : ℝ) + β| + 1 := by
          rw [abs_of_nonneg hδ0]
          linarith
  exact mul_le_mul hδ1 hb (abs_nonneg _) (by positivity)

/-- The partial sum of `g` against its antiderivative `F`, termwise by the mean-value step. -/
private lemma sum_g_sub_bigF_le (α β : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    |∑ m ∈ Finset.Icc 1 N, (Real.log m + α) * (Real.log m + β)
       - (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
            * (Real.log ((N : ℝ) + 1) - 1 + β) + 1)
          - ((-1 + α) * (-1 + β) + 1))|
      ≤ ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) * (|Real.log m + α| + |Real.log m + β| + 1) := by
  set G : ℕ → ℝ :=
    fun k => (k : ℝ) * ((Real.log (k : ℝ) - 1 + α) * (Real.log (k : ℝ) - 1 + β) + 1) with hG
  have hGN : G (N + 1) = ((N : ℝ) + 1)
      * ((Real.log ((N : ℝ) + 1) - 1 + α) * (Real.log ((N : ℝ) + 1) - 1 + β) + 1) := by
    simp only [hG]
    push_cast
    ring
  have hG1 : G 1 = (-1 + α) * (-1 + β) + 1 := by
    simp only [hG]
    rw [Nat.cast_one, Real.log_one]
    ring
  rw [← hGN, ← hG1, ← sum_telescope_nat G hN, ← Finset.sum_sub_distrib]
  calc |∑ m ∈ Finset.Icc 1 N, ((Real.log m + α) * (Real.log m + β) - (G (m + 1) - G m))|
      ≤ ∑ m ∈ Finset.Icc 1 N, |(Real.log m + α) * (Real.log m + β) - (G (m + 1) - G m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) * (|Real.log m + α| + |Real.log m + β| + 1) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hGm1 : G (m + 1) = ((m : ℝ) + 1)
            * ((Real.log ((m : ℝ) + 1) - 1 + α) * (Real.log ((m : ℝ) + 1) - 1 + β) + 1) := by
          simp only [hG]
          push_cast
          ring
        have hGm : G m = (m : ℝ)
            * ((Real.log (m : ℝ) - 1 + α) * (Real.log (m : ℝ) - 1 + β) + 1) := by
          simp only [hG]
        rw [hGm1, hGm, show (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β)
            - (((m : ℝ) + 1) * ((Real.log ((m : ℝ) + 1) - 1 + α)
                * (Real.log ((m : ℝ) + 1) - 1 + β) + 1)
              - (m : ℝ) * ((Real.log (m : ℝ) - 1 + α) * (Real.log (m : ℝ) - 1 + β) + 1))
            = -(((m : ℝ) + 1) * ((Real.log ((m : ℝ) + 1) - 1 + α)
                * (Real.log ((m : ℝ) + 1) - 1 + β) + 1)
              - (m : ℝ) * ((Real.log (m : ℝ) - 1 + α) * (Real.log (m : ℝ) - 1 + β) + 1)
              - (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β)) by ring, abs_neg]
        exact bigF_step_bound α β hm1

set_option maxHeartbeats 1200000 in
-- H5c is one long estimate chain (discrete Abel, the mean-value step, and four separate
-- bounds assembled in a single `calc`); it exceeds the default elaboration budget.
/-- **H5c (the H freeze's row, verbatim).** The two-log weighted form of H5a.

Discrete Abel (`abel_sum`) against H5a's counting function turns the weighted sum into
`ρ₀(r/κ(r))·Σ_{m ≤ N} g(m)` plus a boundary term and a variation sum, both weighed by
`|E(n)| ≤ C·√n·σ(r)`; `Σ_{n ≤ N} n^{−1/2}log(2M/n) ≤ (2 log 2 + 16)√M` closes the
variation sum. The main term meets its antiderivative
`F(x) = x((log x − 1 + α)(log x − 1 + β) + 1)` through the mean-value theorem on each
`[m, m+1]` — no integral is ever formed — and **the residue `F(1) = αβ − (α+β) + 2` is
carried**, not dropped: at `M = 1, α = β = 0` the sum is `0` while the main term is `2`.

The must-FAIL control (measured): with the main-term factor
`((log M − 1 + α)(log M − 1 + β) + 1)` → `((log M + α)(log M + β))` at `α = β = 0`,
`r = 1`, the ratio to `√M(1 + log M)²` is `3.654 / 9.554 / 25.815` at
`M = 10³ / 10⁴ / 10⁵` (growing) against `0.0216 / 0.0217 / 0.0010` frozen. -/
theorem sqf_coprime_sum_log_mul_log_eq : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → ∀ M : ℝ, 1 ≤ M →
    ∀ α β : ℝ,
    |∑ m ∈ (Finset.Icc 1 ⌊M⌋₊).filter (fun m => Nat.Coprime m r),
        (moebius m : ℝ) ^ 2 * (Real.log m + α) * (Real.log m + β)
      - rho0 * ((r : ℝ) / kappa r) * M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)|
      ≤ C * M ^ (1/2 : ℝ) * sigmaQ r * (1 + |Real.log M + α|) * (1 + |Real.log M + β|) := by
  classical
  obtain ⟨C5, hC5pos, hC5⟩ := sqf_coprime_count_eq
  refine ⟨250 + 39 * C5, by linarith, fun r hr M hM α β => ?_⟩
  set N : ℕ := ⌊M⌋₊ with hNdef
  have hM0 : (0 : ℝ) < M := by linarith
  have hNM : (N : ℝ) ≤ M := Nat.floor_le hM0.le
  have hMN : M < (N : ℝ) + 1 := Nat.lt_floor_add_one M
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hM)
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hsig1 : (1 : ℝ) ≤ sigmaQ r := one_le_sigmaQ r hr
  set L : ℝ := Real.log M with hLdef
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg hM
  set Q : ℝ := rho0 * ((r : ℝ) / kappa r) with hQdef
  have hQ2 : |Q| ≤ 2 := by
    rw [hQdef, abs_mul, abs_of_nonneg (div_kappa_pos r hr).le]
    calc |rho0| * ((r : ℝ) / kappa r) ≤ 2 * ((r : ℝ) / kappa r) := by
          exact mul_le_mul_of_nonneg_right abs_rho0_le_two (div_kappa_pos r hr).le
      _ ≤ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left (div_kappa_le_one r hr) (by norm_num)
      _ = 2 := by ring
  set P : ℝ := (1 + |L + α|) * (1 + |L + β|) with hPdef
  have hP1 : (1 : ℝ) ≤ P := by
    rw [hPdef]
    nlinarith [abs_nonneg (L + α), abs_nonneg (L + β)]
  have hPge : 1 + |L + α| + |L + β| ≤ P := by
    rw [hPdef]
    nlinarith [abs_nonneg (L + α), abs_nonneg (L + β)]
  have hMh : (1 : ℝ) ≤ M ^ (1/2 : ℝ) := Real.one_le_rpow hM (by norm_num)
  have hMq : (1 : ℝ) ≤ M ^ (1/4 : ℝ) := Real.one_le_rpow hM (by norm_num)
  have hMqh : M ^ (1/4 : ℝ) ≤ M ^ (1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
  have hLq : L ≤ 4 * M ^ (1/4 : ℝ) := log_le_four_rpow_quarter hM
  have hq2 : M ^ (1/4 : ℝ) * M ^ (1/4 : ℝ) = M ^ (1/2 : ℝ) := by
    rw [← Real.rpow_add hM0]
    norm_num
  have hsq25 : (1 + L) ^ 2 ≤ 25 * M ^ (1/2 : ℝ) := by
    nlinarith [hLq, hq2, hMqh, hMh, hL0, sq_nonneg (4 * M ^ (1/4 : ℝ) - L)]
  -- the summand and the weight
  set a : ℕ → ℝ := fun m => if Nat.Coprime m r then (moebius m : ℝ) ^ 2 else 0 with hadef
  set gg : ℕ → ℝ := fun m => (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β) with hggdef
  -- the frozen sum, rewritten
  have hLHS : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m r),
        (moebius m : ℝ) ^ 2 * (Real.log m + α) * (Real.log m + β)
      = ∑ m ∈ Finset.Icc 1 N, a m * gg m := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hadef, hggdef]
    dsimp only
    by_cases hc : Nat.Coprime m r
    · rw [if_pos hc, if_pos hc]
      ring
    · rw [if_neg hc, if_neg hc, zero_mul]
  -- the counting function through H5a
  have hEbound : ∀ n : ℕ, 1 ≤ n →
      |(∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)| ≤ C5 * (n : ℝ) ^ (1/2 : ℝ) * sigmaQ r := by
    intro n hn
    have h := hC5 r hr (n : ℝ) (by exact_mod_cast hn)
    rw [Nat.floor_natCast] at h
    have heq : ∑ m ∈ (Finset.Icc 1 n).filter (fun m => Nat.Coprime m r), (moebius m : ℝ) ^ 2
        = ∑ m ∈ Finset.Icc 1 n, a m := by
      rw [Finset.sum_filter]
    rw [heq] at h
    rw [hQdef]
    exact h
  -- the two Abel identities
  have hsum1 : ∀ n : ℕ, (∑ _m ∈ Finset.Icc 1 n, (1 : ℝ)) = (n : ℝ) := by
    intro n
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    norm_num
  have hg1 : ∑ m ∈ Finset.Icc 1 N, gg m
      = (N : ℝ) * gg N - ∑ n ∈ Finset.Ico 1 N, (n : ℝ) * (gg (n + 1) - gg n) := by
    have h := abel_sum (fun _ => (1 : ℝ)) gg hN1
    simp only [one_mul] at h
    rw [h, hsum1 N]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [hsum1 n]
  have hga := abel_sum a gg hN1
  have hdecomp : (∑ m ∈ Finset.Icc 1 N, a m * gg m) - Q * (∑ m ∈ Finset.Icc 1 N, gg m)
      = ((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N
        - ∑ n ∈ Finset.Ico 1 N,
            ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n) := by
    have hexp : ∑ n ∈ Finset.Ico 1 N,
            ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n)
        = (∑ n ∈ Finset.Ico 1 N, (∑ m ∈ Finset.Icc 1 n, a m) * (gg (n + 1) - gg n))
          - Q * ∑ n ∈ Finset.Ico 1 N, (n : ℝ) * (gg (n + 1) - gg n) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hga, hg1, hexp]
    ring
  -- the log comparison on `[1, N]`
  have hlogcmp : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      |Real.log (n : ℝ) + α| + |Real.log (n : ℝ) + β| + 1 ≤ P + 2 * (L - Real.log (n : ℝ)) := by
    intro n hn1 hnN
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnM : (n : ℝ) ≤ M := le_trans (by exact_mod_cast hnN) hNM
    have hln0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have hlnL : Real.log (n : ℝ) ≤ L := Real.log_le_log (by linarith) hnM
    have hstep : ∀ γ : ℝ, |Real.log (n : ℝ) + γ| ≤ |L + γ| + (L - Real.log (n : ℝ)) := by
      intro γ
      calc |Real.log (n : ℝ) + γ| = |(L + γ) + (-(L - Real.log (n : ℝ)))| := by
            congr 1; ring
        _ ≤ |L + γ| + |-(L - Real.log (n : ℝ))| := abs_add_le _ _
        _ = |L + γ| + (L - Real.log (n : ℝ)) := by
            rw [abs_neg]
            congr 1
            exact abs_of_nonneg (by linarith)
    linarith [hstep α, hstep β, hPge]
  -- the boundary term
  have hlogN : L ≤ Real.log 2 + Real.log (N : ℝ) := by
    have h2N : M ≤ 2 * (N : ℝ) := by linarith
    calc L ≤ Real.log (2 * (N : ℝ)) := Real.log_le_log hM0 h2N
      _ = Real.log 2 + Real.log (N : ℝ) := Real.log_mul (by norm_num) (by linarith)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hggN : |gg N| ≤ P := by
    rw [hggdef, hPdef]
    dsimp only
    have hlnL : Real.log (N : ℝ) ≤ L := Real.log_le_log (by linarith) hNM
    have hstep : ∀ γ : ℝ, |Real.log (N : ℝ) + γ| ≤ 1 + |L + γ| := by
      intro γ
      calc |Real.log (N : ℝ) + γ| = |(L + γ) + (-(L - Real.log (N : ℝ)))| := by
            congr 1; ring
        _ ≤ |L + γ| + |-(L - Real.log (N : ℝ))| := abs_add_le _ _
        _ = |L + γ| + (L - Real.log (N : ℝ)) := by
            rw [abs_neg]
            congr 1
            exact abs_of_nonneg (by linarith)
        _ ≤ 1 + |L + γ| := by linarith
    rw [abs_mul]
    exact mul_le_mul (by linarith [hstep α]) (by linarith [hstep β]) (abs_nonneg _)
      (by positivity)
  have hT2 : |((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N|
      ≤ C5 * M ^ (1/2 : ℝ) * sigmaQ r * P := by
    rw [abs_mul]
    have hNh : (N : ℝ) ^ (1/2 : ℝ) ≤ M ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hNM (by norm_num)
    have hb1 := hEbound N hN1
    have hnn : (0 : ℝ) ≤ C5 * (N : ℝ) ^ (1/2 : ℝ) * sigmaQ r :=
      mul_nonneg (mul_nonneg hC5pos.le (Real.rpow_nonneg (by linarith) _)) (by linarith)
    calc |(∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)| * |gg N|
        ≤ (C5 * (N : ℝ) ^ (1/2 : ℝ) * sigmaQ r) * P :=
          mul_le_mul hb1 hggN (abs_nonneg _) hnn
      _ ≤ C5 * M ^ (1/2 : ℝ) * sigmaQ r * P :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hNh hC5pos.le) (by linarith)) (by linarith)
  -- the variation sum
  have hT3 : ∑ n ∈ Finset.Ico 1 N,
        |((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n)|
      ≤ 38 * C5 * sigmaQ r * P * M ^ (1/2 : ℝ) := by
    have hterm : ∀ n ∈ Finset.Ico 1 N,
        |((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n)|
          ≤ C5 * sigmaQ r * ((n : ℝ) ^ (-(1/2) : ℝ) * P
              + 2 * ((n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ)))) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
      have hnN : n ≤ N := le_of_lt (Finset.mem_Ico.mp hn).2
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnM : (n : ℝ) ≤ M := le_trans (by exact_mod_cast hnN) hNM
      have hln0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
      have hstep : |gg (n + 1) - gg n|
          ≤ (1 / (n : ℝ)) * (|Real.log (n : ℝ) + α| + |Real.log (n : ℝ) + β| + 1) := by
        rw [hggdef]
        dsimp only
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        exact g_step_bound α β hn1
      have hcmp := hlogcmp n hn1 hnN
      have hlogd : L - Real.log (n : ℝ) ≤ Real.log (2 * M / (n : ℝ)) := by
        rw [Real.log_div (by positivity) hnpos.ne', Real.log_mul (by norm_num) hM0.ne']
        have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      have hEn := hEbound n hn1
      have hrp : (n : ℝ) ^ (1/2 : ℝ) * (1 / (n : ℝ)) = (n : ℝ) ^ (-(1/2) : ℝ) := by
        rw [eq_comm, show (-(1/2) : ℝ) = (1/2 : ℝ) + (-1 : ℝ) by norm_num,
          Real.rpow_add hnpos, Real.rpow_neg_one]
        ring
      have hnn : (0 : ℝ) ≤ C5 * (n : ℝ) ^ (1/2 : ℝ) * sigmaQ r :=
        mul_nonneg (mul_nonneg hC5pos.le (Real.rpow_nonneg (by linarith) _)) (by linarith)
      rw [abs_mul]
      calc |(∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)| * |gg (n + 1) - gg n|
          ≤ (C5 * (n : ℝ) ^ (1/2 : ℝ) * sigmaQ r)
              * ((1 / (n : ℝ)) * (P + 2 * Real.log (2 * M / (n : ℝ)))) := by
            refine mul_le_mul hEn ?_ (abs_nonneg _) hnn
            refine le_trans hstep ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith
        _ = C5 * sigmaQ r * (((n : ℝ) ^ (1/2 : ℝ) * (1 / (n : ℝ))) * P
              + 2 * (((n : ℝ) ^ (1/2 : ℝ) * (1 / (n : ℝ))) * Real.log (2 * M / (n : ℝ)))) := by
            ring
        _ = C5 * sigmaQ r * ((n : ℝ) ^ (-(1/2) : ℝ) * P
              + 2 * ((n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ)))) := by
            rw [hrp]
    have hnonneg : ∀ n ∈ Finset.Icc 1 N, n ∉ Finset.Ico 1 N →
        (0 : ℝ) ≤ C5 * sigmaQ r * ((n : ℝ) ^ (-(1/2) : ℝ) * P
          + 2 * ((n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ)))) := by
      intro n hn _
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnM : (n : ℝ) ≤ M := le_trans (by exact_mod_cast hnN) hNM
      have hlogd : (0 : ℝ) ≤ Real.log (2 * M / (n : ℝ)) := by
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ (by linarith)]
        linarith
      have hrp0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg (by linarith) _
      have hP0 : (0 : ℝ) ≤ P := by linarith
      have : (0 : ℝ) ≤ sigmaQ r := by linarith
      positivity
    calc ∑ n ∈ Finset.Ico 1 N,
          |((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n)|
        ≤ ∑ n ∈ Finset.Ico 1 N, C5 * sigmaQ r * ((n : ℝ) ^ (-(1/2) : ℝ) * P
            + 2 * ((n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ)))) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ Finset.Icc 1 N, C5 * sigmaQ r * ((n : ℝ) ^ (-(1/2) : ℝ) * P
            + 2 * ((n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ)))) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self hnonneg
      _ = C5 * sigmaQ r * (P * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2) : ℝ))
            + 2 * ∑ n ∈ Finset.Icc 1 N,
                (n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ 38 * C5 * sigmaQ r * P * M ^ (1/2 : ℝ) := by
          have h1 : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2) : ℝ) ≤ 2 * (N : ℝ) ^ ((1/2) : ℝ) :=
            sum_rpow_neg_half_le N
          have h1' : (N : ℝ) ^ ((1/2) : ℝ) ≤ M ^ (1/2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) hNM (by norm_num)
          have h2 : ∑ n ∈ Finset.Icc 1 N,
              (n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ))
              ≤ (2 * Real.log 2 + 16) * M ^ ((1/2) : ℝ) := sum_rpow_neg_half_log_le hM hNM
          have hP0 : (0 : ℝ) ≤ P := by linarith
          have hCs : (0 : ℝ) ≤ C5 * sigmaQ r := mul_nonneg hC5pos.le (by linarith)
          have hS1 : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2) : ℝ) ≤ 2 * M ^ (1/2 : ℝ) := by
            linarith
          have hS2 : ∑ n ∈ Finset.Icc 1 N,
              (n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ)) ≤ 18 * M ^ (1/2 : ℝ) :=
            le_trans h2 (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
          have hi1 : P * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2) : ℝ))
              ≤ P * (2 * M ^ (1/2 : ℝ)) := mul_le_mul_of_nonneg_left hS1 hP0
          have hi3 : (1 : ℝ) * M ^ (1/2 : ℝ) ≤ P * M ^ (1/2 : ℝ) :=
            mul_le_mul_of_nonneg_right hP1 (by linarith)
          have hinner : P * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2) : ℝ))
              + 2 * ∑ n ∈ Finset.Icc 1 N,
                  (n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ))
              ≤ 38 * P * M ^ (1/2 : ℝ) := by
            linarith [hi1, hi3, hS2]
          calc C5 * sigmaQ r * (P * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1/2) : ℝ))
                + 2 * ∑ n ∈ Finset.Icc 1 N,
                    (n : ℝ) ^ (-(1/2) : ℝ) * Real.log (2 * M / (n : ℝ)))
              ≤ C5 * sigmaQ r * (38 * P * M ^ (1/2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hinner hCs
            _ = 38 * C5 * sigmaQ r * P * M ^ (1/2 : ℝ) := by ring
  -- the main term against the antiderivative
  have hbigF1 : |(-1 + α) * (-1 + β) + 1| ≤ 2 * P * (1 + L) ^ 2 := by
    have hab : ∀ γ : ℝ, 1 + |γ| ≤ (1 + |L + γ|) * (1 + L) := by
      intro γ
      have h1 : |γ| ≤ |L + γ| + L := by
        calc |γ| = |(L + γ) + (-L)| := by congr 1; ring
          _ ≤ |L + γ| + |(-L)| := abs_add_le _ _
          _ = |L + γ| + L := by rw [abs_neg, abs_of_nonneg hL0]
      nlinarith [abs_nonneg (L + γ), hL0, h1]
    have h2 : |(-1 + α) * (-1 + β) + 1| ≤ (1 + |α|) * (1 + |β|) + 1 := by
      calc |(-1 + α) * (-1 + β) + 1| ≤ |(-1 + α) * (-1 + β)| + |(1 : ℝ)| := abs_add_le _ _
        _ = |(-1 + α)| * |(-1 + β)| + 1 := by rw [abs_mul, abs_one]
        _ ≤ (1 + |α|) * (1 + |β|) + 1 := by
            have ha : |(-1 + α)| ≤ 1 + |α| := by
              calc |(-1 + α)| ≤ |(-1 : ℝ)| + |α| := abs_add_le _ _
                _ = 1 + |α| := by rw [abs_neg, abs_one]
            have hb : |(-1 + β)| ≤ 1 + |β| := by
              calc |(-1 + β)| ≤ |(-1 : ℝ)| + |β| := abs_add_le _ _
                _ = 1 + |β| := by rw [abs_neg, abs_one]
            have hmm := mul_le_mul ha hb (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 + |α|)
            linarith
    have h3 : (1 + |α|) * (1 + |β|) ≤ P * (1 + L) ^ 2 := by
      have := mul_le_mul (hab α) (hab β) (by positivity)
        (mul_nonneg (by positivity) (by linarith))
      calc (1 + |α|) * (1 + |β|) ≤ ((1 + |L + α|) * (1 + L)) * ((1 + |L + β|) * (1 + L)) := this
        _ = P * (1 + L) ^ 2 := by rw [hPdef]; ring
    have hsq1 : (1 : ℝ) ≤ (1 + L) ^ 2 := by nlinarith [hL0]
    have h4 : (1 : ℝ) ≤ P * (1 + L) ^ 2 := by nlinarith [hP1, hsq1]
    linarith
  have hbdry : |((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
        * (Real.log ((N : ℝ) + 1) - 1 + β) + 1)
      - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)| ≤ P := by
    obtain ⟨η, hη, hval⟩ := bigF_mvt α β hM0 hMN
    rw [hval, abs_mul]
    have hη0 : (0 : ℝ) < η := lt_trans hM0 hη.1
    have hlo : L ≤ Real.log η := Real.log_le_log hM0 hη.1.le
    have hhi : Real.log η ≤ Real.log 2 + L := by
      have hNb : (N : ℝ) + 1 ≤ 2 * M := by linarith
      calc Real.log η ≤ Real.log (2 * M) := Real.log_le_log hη0 (le_trans hη.2.le hNb)
        _ = Real.log 2 + L := Real.log_mul (by norm_num) hM0.ne'
    have hstep : ∀ γ : ℝ, |Real.log η + γ| ≤ 1 + |L + γ| := by
      intro γ
      calc |Real.log η + γ| = |(L + γ) + (Real.log η - L)| := by congr 1; ring
        _ ≤ |L + γ| + |Real.log η - L| := abs_add_le _ _
        _ = |L + γ| + (Real.log η - L) := by
            congr 1
            exact abs_of_nonneg (by linarith)
        _ ≤ 1 + |L + γ| := by linarith
    have hgη : |(Real.log η + α) * (Real.log η + β)| ≤ P := by
      rw [abs_mul, hPdef]
      exact mul_le_mul (by linarith [hstep α]) (by linarith [hstep β]) (abs_nonneg _)
        (by positivity)
    have hlen : |(N : ℝ) + 1 - M| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    calc |(Real.log η + α) * (Real.log η + β)| * |(N : ℝ) + 1 - M|
        ≤ P * 1 := mul_le_mul hgη hlen (abs_nonneg _) (by linarith)
      _ = P := by ring
  have hharm : ∑ m ∈ Finset.Icc 1 N,
        (1 / (m : ℝ)) * (|Real.log (m : ℝ) + α| + |Real.log (m : ℝ) + β| + 1)
      ≤ 2 * P * (1 + L) ^ 2 := by
    have hb : ∀ m ∈ Finset.Icc 1 N,
        (1 / (m : ℝ)) * (|Real.log (m : ℝ) + α| + |Real.log (m : ℝ) + β| + 1)
          ≤ (P + 2 * L) * ((m : ℝ))⁻¹ := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hln0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
      have hcmp := hlogcmp m hm1 hmN
      rw [one_div, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    calc ∑ m ∈ Finset.Icc 1 N,
          (1 / (m : ℝ)) * (|Real.log (m : ℝ) + α| + |Real.log (m : ℝ) + β| + 1)
        ≤ ∑ m ∈ Finset.Icc 1 N, (P + 2 * L) * ((m : ℝ))⁻¹ := Finset.sum_le_sum hb
      _ = (P + 2 * L) * ∑ m ∈ Finset.Icc 1 N, ((m : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (P + 2 * L) * (1 + Real.log (N : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log N) ?_
          linarith
      _ ≤ 2 * P * (1 + L) ^ 2 := by
          have hlnN : Real.log (N : ℝ) ≤ L := Real.log_le_log (by linarith) hNM
          have hlnN0 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
          have hh1 : (P + 2 * L) * (1 + Real.log (N : ℝ)) ≤ (P + 2 * L) * (1 + L) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          have hh2 : P + 2 * L ≤ 2 * P * (1 + L) := by nlinarith [hP1, hL0]
          have hh3 : (P + 2 * L) * (1 + L) ≤ (2 * P * (1 + L)) * (1 + L) :=
            mul_le_mul_of_nonneg_right hh2 (by linarith)
          calc (P + 2 * L) * (1 + Real.log (N : ℝ)) ≤ (2 * P * (1 + L)) * (1 + L) :=
                le_trans hh1 hh3
            _ = 2 * P * (1 + L) ^ 2 := by ring
  have hT1 : |(∑ m ∈ Finset.Icc 1 N, gg m)
      - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)| ≤ 125 * P * M ^ (1/2 : ℝ) := by
    have hmid := sum_g_sub_bigF_le α β hN1
    have hggsum : ∑ m ∈ Finset.Icc 1 N, gg m
        = ∑ m ∈ Finset.Icc 1 N, (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β) := by
      rw [hggdef]
    rw [hggsum]
    have hsplit : (∑ m ∈ Finset.Icc 1 N, (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β))
          - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)
        = ((∑ m ∈ Finset.Icc 1 N, (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β))
            - (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                * (Real.log ((N : ℝ) + 1) - 1 + β) + 1) - ((-1 + α) * (-1 + β) + 1)))
          + (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                * (Real.log ((N : ℝ) + 1) - 1 + β) + 1)
              - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1))
          - ((-1 + α) * (-1 + β) + 1) := by ring
    rw [hsplit]
    have hstep1 : |((∑ m ∈ Finset.Icc 1 N, (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β))
            - (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                * (Real.log ((N : ℝ) + 1) - 1 + β) + 1) - ((-1 + α) * (-1 + β) + 1)))
          + (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                * (Real.log ((N : ℝ) + 1) - 1 + β) + 1)
              - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1))
          - ((-1 + α) * (-1 + β) + 1)|
        ≤ 2 * P * (1 + L) ^ 2 + P + 2 * P * (1 + L) ^ 2 := by
      calc |((∑ m ∈ Finset.Icc 1 N, (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β))
              - (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                  * (Real.log ((N : ℝ) + 1) - 1 + β) + 1) - ((-1 + α) * (-1 + β) + 1)))
            + (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                  * (Real.log ((N : ℝ) + 1) - 1 + β) + 1)
                - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1))
            - ((-1 + α) * (-1 + β) + 1)|
          ≤ |((∑ m ∈ Finset.Icc 1 N, (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β))
              - (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                  * (Real.log ((N : ℝ) + 1) - 1 + β) + 1) - ((-1 + α) * (-1 + β) + 1)))
            + (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                  * (Real.log ((N : ℝ) + 1) - 1 + β) + 1)
                - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1))|
              + |(-1 + α) * (-1 + β) + 1| := by
            rw [sub_eq_add_neg]
            calc |_ + -((-1 + α) * (-1 + β) + 1)| ≤ |_| + |(-((-1 + α) * (-1 + β) + 1))| :=
                  abs_add_le _ _
              _ = _ := by rw [abs_neg]
        _ ≤ (2 * P * (1 + L) ^ 2 + P) + 2 * P * (1 + L) ^ 2 := by
            refine add_le_add ?_ hbigF1
            calc |_ + _| ≤ |((∑ m ∈ Finset.Icc 1 N,
                    (Real.log (m : ℝ) + α) * (Real.log (m : ℝ) + β))
                  - (((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                      * (Real.log ((N : ℝ) + 1) - 1 + β) + 1) - ((-1 + α) * (-1 + β) + 1)))|
                + |(((N : ℝ) + 1) * ((Real.log ((N : ℝ) + 1) - 1 + α)
                      * (Real.log ((N : ℝ) + 1) - 1 + β) + 1)
                    - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1))| := abs_add_le _ _
              _ ≤ 2 * P * (1 + L) ^ 2 + P := add_le_add (le_trans hmid hharm) hbdry
        _ = 2 * P * (1 + L) ^ 2 + P + 2 * P * (1 + L) ^ 2 := by ring
    have hfin : 2 * P * (1 + L) ^ 2 + P + 2 * P * (1 + L) ^ 2 ≤ 125 * P * M ^ (1/2 : ℝ) := by
      have hP0 : (0 : ℝ) ≤ P := by linarith
      have hA : P * (1 + L) ^ 2 ≤ P * (25 * M ^ (1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq25 hP0
      have hB : P ≤ P * M ^ (1/2 : ℝ) := by nlinarith [hMh, hP0]
      have hC : (0 : ℝ) ≤ P * M ^ (1/2 : ℝ) := mul_nonneg hP0 (by linarith)
      linarith [hA, hB, hC]
    linarith [hstep1, hfin]
  -- assemble
  rw [hLHS]
  have hmain : (∑ m ∈ Finset.Icc 1 N, a m * gg m)
      - Q * M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)
      = (((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N
        - ∑ n ∈ Finset.Ico 1 N,
            ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n))
        + Q * ((∑ m ∈ Finset.Icc 1 N, gg m)
          - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)) := by
    rw [← hdecomp]
    ring
  have hgoal : Q * M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)
      = rho0 * ((r : ℝ) / kappa r) * M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1) := by
    rw [hQdef]
  rw [← hgoal, hmain]
  have hsum3 : |∑ n ∈ Finset.Ico 1 N,
        ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n)|
      ≤ 38 * C5 * sigmaQ r * P * M ^ (1/2 : ℝ) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) hT3
  have hQP : |Q * ((∑ m ∈ Finset.Icc 1 N, gg m)
      - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1))| ≤ 250 * P * M ^ (1/2 : ℝ) := by
    rw [abs_mul]
    have hnn : (0 : ℝ) ≤ 125 * P * M ^ (1/2 : ℝ) :=
      mul_nonneg (by linarith) (by linarith)
    calc |Q| * |(∑ m ∈ Finset.Icc 1 N, gg m)
            - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1)|
        ≤ 2 * (125 * P * M ^ (1/2 : ℝ)) := mul_le_mul hQ2 hT1 (abs_nonneg _) (by norm_num)
      _ = 250 * P * M ^ (1/2 : ℝ) := by ring
  have hcombine : |(((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N
        - ∑ n ∈ Finset.Ico 1 N,
            ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n))
      + Q * ((∑ m ∈ Finset.Icc 1 N, gg m)
        - M * ((Real.log M - 1 + α) * (Real.log M - 1 + β) + 1))|
      ≤ (C5 * M ^ (1/2 : ℝ) * sigmaQ r * P + 38 * C5 * sigmaQ r * P * M ^ (1/2 : ℝ))
        + 250 * P * M ^ (1/2 : ℝ) := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ hQP)
    calc |((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N
          - ∑ n ∈ Finset.Ico 1 N,
              ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n)|
        = |((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N
          + -(∑ n ∈ Finset.Ico 1 N,
              ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n))| := by
          rw [sub_eq_add_neg]
      _ ≤ |((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N|
          + |-(∑ n ∈ Finset.Ico 1 N,
              ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n))| :=
          abs_add_le _ _
      _ = |((∑ m ∈ Finset.Icc 1 N, a m) - Q * (N : ℝ)) * gg N|
          + |∑ n ∈ Finset.Ico 1 N,
              ((∑ m ∈ Finset.Icc 1 n, a m) - Q * (n : ℝ)) * (gg (n + 1) - gg n)| := by
          rw [abs_neg]
      _ ≤ C5 * M ^ (1/2 : ℝ) * sigmaQ r * P + 38 * C5 * sigmaQ r * P * M ^ (1/2 : ℝ) :=
          add_le_add hT2 hsum3
  refine le_trans hcombine ?_
  have hP0 : (0 : ℝ) ≤ P := by linarith
  have hMh0 : (0 : ℝ) ≤ M ^ (1/2 : ℝ) := by linarith
  have hexpand : (250 + 39 * C5) * M ^ (1/2 : ℝ) * sigmaQ r * (1 + |L + α|) * (1 + |L + β|)
      = (250 + 39 * C5) * (M ^ (1/2 : ℝ) * sigmaQ r * P) := by
    rw [hPdef]; ring
  rw [hexpand]
  have hPM : (0 : ℝ) ≤ M ^ (1/2 : ℝ) * P := mul_nonneg hMh0 hP0
  have hkey : M ^ (1/2 : ℝ) * P * 1 ≤ M ^ (1/2 : ℝ) * P * sigmaQ r :=
    mul_le_mul_of_nonneg_left hsig1 hPM
  linarith [hkey]

/-! ## III. THE CONSTANT -/

/-- **The A4 helper (PUBLIC; H2's wave consumes it).**
`(log x)^A ≤ (4A)^A·x^{1/4}` for `x ≥ 1` and `A > 0`, from mathlib's
`Real.log_le_rpow_div` at `ε = 1/(4A)`.

This is the device every far tail of this file is closed with. The landed
`log u ≤ 4u^{1/4}` keeps only its `1 + log Q ≤ 5Q^{1/4}` half: its FIXED exponent does not
beat `(log 2Q)^A` above `A = 1` — applied to C3's `D`-tail it leaves
`Θ(Q^{(A+1)/4 − 1/2})`, unbounded for `A > 1`. -/
theorem log_rpow_le_rpow_quarter (A : ℝ) (hA : 0 < A) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ A ≤ (4 * A) ^ A * x ^ (1/4 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hAne : A ≠ 0 := hA.ne'
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hA4 : (0 : ℝ) < 1 / (4 * A) := by positivity
  have h1 : Real.log x ≤ 4 * A * x ^ (1 / (4 * A) : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le hA4
    have hrw : x ^ (1 / (4 * A) : ℝ) / (1 / (4 * A)) = 4 * A * x ^ (1 / (4 * A) : ℝ) := by
      field_simp
    linarith [h, hrw.le, hrw.ge]
  have h2 : Real.log x ^ A ≤ (4 * A * x ^ (1 / (4 * A) : ℝ)) ^ A :=
    Real.rpow_le_rpow hlog h1 hA.le
  have h3 : (4 * A * x ^ (1 / (4 * A) : ℝ)) ^ A = (4 * A) ^ A * x ^ (1/4 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le,
      show (1 / (4 * A) : ℝ) * A = 1/4 by field_simp]
  linarith [h2, h3.le, h3.ge]

/-- **The swap stone** (the landed `sum_divisors_swap` recipe, re-derived):
`Σ_{r ≤ N} Σ_{e ∣ r} F(e, r) = Σ_{e ≤ N} Σ_{f ≤ N/e} F(e, e·f)`. -/
private lemma sum_divisors_swap (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 N, ∑ e ∈ r.divisors, F e r
      = ∑ e ∈ Finset.Icc 1 N, ∑ f ∈ Finset.Icc 1 (N / e), F e (e * f) := by
  have h1 : ∑ r ∈ Finset.Icc 1 N, ∑ e ∈ r.divisors, F e r
      = ∑ e ∈ Finset.Icc 1 N, ∑ r ∈ (Finset.Icc 1 N).filter (fun r => e ∣ r), F e r := by
    refine Finset.sum_comm' ?_
    intro r e
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hr1, hrN⟩, hed, hr0⟩
      have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hed (by omega)
      exact ⟨⟨⟨hr1, hrN⟩, hed⟩, he1, le_trans (Nat.le_of_dvd (by omega) hed) hrN⟩
    · rintro ⟨⟨⟨hr1, hrN⟩, hed⟩, _⟩
      exact ⟨⟨hr1, hrN⟩, hed, by omega⟩
  rw [h1]
  refine Finset.sum_congr rfl fun e he => ?_
  exact sum_dvd_reindex (Finset.mem_Icc.mp he).1 (fun r => F e r)

/-- **C1 (the exact identity).** `Σ_{n ≤ N}(μ(n)/n)·H(⌊N/n⌋) = 1` for `N ≥ 1`.

The divisor-sum swap sends `(n, m)` to `k = n·m` and the inner sum becomes
`Σ_{d ∣ k} μ(d) = [k = 1]`, so only `k = 1` survives.

This row is its own control — the `N = 6` instance
`49/20 − 11/12 − 1/2 − 1/5 + 1/6 = 1` is checked by `norm_num` in §2(b) below. -/
theorem sum_moebius_div_mul_harmonic_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) / n * ∑ m ∈ Finset.Icc 1 (N / n), (1 : ℝ) / m = 1 := by
  classical
  have hswap := sum_divisors_swap N (fun e r => (moebius e : ℝ) / (r : ℝ))
  have hL : ∑ r ∈ Finset.Icc 1 N, ∑ e ∈ r.divisors, (moebius e : ℝ) / (r : ℝ) = 1 := by
    have hterm : ∀ r ∈ Finset.Icc 1 N,
        (∑ e ∈ r.divisors, (moebius e : ℝ) / (r : ℝ))
          = (if r = 1 then (1 : ℝ) else 0) / (r : ℝ) := by
      intro r _
      rw [← Finset.sum_div, sum_divisors_moebius_real]
    rw [Finset.sum_congr rfl hterm]
    have hz : ∀ b ∈ Finset.Icc 1 N, b ≠ 1 → (if b = 1 then (1 : ℝ) else 0) / (b : ℝ) = 0 := by
      intro b _ hbne
      rw [if_neg hbne, zero_div]
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩) hz]
    norm_num
  have hgoal : ∑ n ∈ Finset.Icc 1 N,
        (moebius n : ℝ) / n * ∑ m ∈ Finset.Icc 1 (N / n), (1 : ℝ) / m
      = ∑ e ∈ Finset.Icc 1 N, ∑ f ∈ Finset.Icc 1 (N / e), (moebius e : ℝ) / ((e * f : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  rw [hgoal, ← hswap]
  exact hL

/-! ### C2 — the sawtooth-log piece `P(Q)` -/

/-- The sawtooth log's argument is `≥ 1`: `⌊Q/x⌋₊ + 1 > Q/x`. -/
private lemma sawtooth_arg_ge_one {Q x : ℝ} (hQ : 0 < Q) (hx : 0 < x) :
    1 ≤ ((⌊Q / x⌋₊ : ℝ) + 1) * x / Q := by
  have hlt : Q / x < (⌊Q / x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : Q / x * x ≤ ((⌊Q / x⌋₊ : ℝ) + 1) * x := mul_le_mul_of_nonneg_right hlt.le hx.le
  have h3 : Q / x * x = Q := by field_simp
  rw [le_div_iff₀ hQ, one_mul]
  linarith

/-- The sawtooth log's argument is `≤ 1 + x/Q` (`⌊Q/x⌋₊ ≤ Q/x`). -/
private lemma sawtooth_arg_le {Q x : ℝ} (hQ : 0 < Q) (hx : 0 < x) :
    ((⌊Q / x⌋₊ : ℝ) + 1) * x / Q ≤ 1 + x / Q := by
  have hfl : ((⌊Q / x⌋₊ : ℝ)) ≤ Q / x := Nat.floor_le (by positivity)
  have h1 : (⌊Q / x⌋₊ : ℝ) * x ≤ Q / x * x := mul_le_mul_of_nonneg_right hfl hx.le
  have h3 : Q / x * x = Q := by field_simp
  have h4 : (1 + x / Q) * Q = Q + x := by field_simp
  rw [div_le_iff₀ hQ]
  nlinarith

/-- `0 ≤ w(x)` for the sawtooth weight `w(x) = (1/x)·log((⌊Q/x⌋₊+1)·x/Q)`. -/
private lemma sawtooth_w_nonneg {Q x : ℝ} (hQ : 0 < Q) (hx : 0 < x) :
    0 ≤ Real.log (((⌊Q / x⌋₊ : ℝ) + 1) * x / Q) / x :=
  div_nonneg (Real.log_nonneg (sawtooth_arg_ge_one hQ hx)) hx.le

/-- `w(x) ≤ 1/Q` for `0 < x`: `log u ≤ u − 1 ≤ x/Q`, then divide by `x`. -/
private lemma sawtooth_w_le {Q x : ℝ} (hQ : 0 < Q) (hx : 0 < x) :
    Real.log (((⌊Q / x⌋₊ : ℝ) + 1) * x / Q) / x ≤ 1 / Q := by
  have hge := sawtooth_arg_ge_one hQ hx
  have hle := sawtooth_arg_le hQ hx
  have hlog : Real.log (((⌊Q / x⌋₊ : ℝ) + 1) * x / Q)
      ≤ ((⌊Q / x⌋₊ : ℝ) + 1) * x / Q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hstep : Real.log (((⌊Q / x⌋₊ : ℝ) + 1) * x / Q) ≤ x / Q := by linarith
  have h5 : Real.log (((⌊Q / x⌋₊ : ℝ) + 1) * x / Q) / x ≤ (x / Q) / x :=
    (div_le_div_iff_of_pos_right hx).mpr hstep
  have h6 : (x / Q) / x = 1 / Q := by field_simp
  linarith

/-- The sawtooth log's argument is `≤ 2` on `0 < x ≤ Q`. -/
private lemma sawtooth_arg_le_two {Q x : ℝ} (hQ : 0 < Q) (hx : 0 < x) (hxQ : x ≤ Q) :
    ((⌊Q / x⌋₊ : ℝ) + 1) * x / Q ≤ 2 := by
  have hle := sawtooth_arg_le hQ hx
  have h : x / Q ≤ 1 := by rw [div_le_one hQ]; exact hxQ
  linarith

/-- **The sawtooth step, off a jump.** With `c` the common numerator `k + 1`,
`log(c(n+1)/Q)/(n+1) − log(cn/Q)/n = (n·log((n+1)/n) − log(cn/Q))/(n(n+1))`, whose numerator
lies in `[−log 2, 1]`, so the step is at most `1/(n(n+1))`. -/
private lemma sawtooth_step_core {Q c : ℝ} (hQ : 0 < Q) {n : ℕ} (hn : 1 ≤ n) (hc : 0 < c)
    (hc1 : 1 ≤ c * (n : ℝ) / Q) (hc2 : c * (n : ℝ) / Q ≤ 2) :
    |Real.log (c * ((n : ℝ) + 1) / Q) / ((n : ℝ) + 1) - Real.log (c * (n : ℝ) / Q) / (n : ℝ)|
      ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn10 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hne1 : (n : ℝ) ≠ 0 := hn0.ne'
  have hne2 : (n : ℝ) + 1 ≠ 0 := hn10.ne'
  have hB0 : (0 : ℝ) < c * (n : ℝ) / Q := by linarith
  have hA0 : (0 : ℝ) < c * ((n : ℝ) + 1) / Q := by positivity
  have hratio : c * ((n : ℝ) + 1) / Q / (c * (n : ℝ) / Q) = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp
  have hlogdiff : Real.log (c * ((n : ℝ) + 1) / Q) - Real.log (c * (n : ℝ) / Q)
      = Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
    rw [← Real.log_div hA0.ne' hB0.ne', hratio]
  have hYnn : 0 ≤ Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hn0]
    linarith
  have hYle : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) by positivity)
    have h2 : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp
      ring
    linarith
  have hXnn : 0 ≤ Real.log (c * (n : ℝ) / Q) := Real.log_nonneg hc1
  have hXle : Real.log (c * (n : ℝ) / Q) ≤ 1 := by
    have h := Real.log_le_log hB0 hc2
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  have hnY : (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hYle hn0.le
    rw [mul_one_div, div_self hne1] at h
    linarith
  have hnYnn : 0 ≤ (n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) := by positivity
  have hlogA : Real.log (c * ((n : ℝ) + 1) / Q)
      = Real.log (c * (n : ℝ) / Q) + Real.log (((n : ℝ) + 1) / (n : ℝ)) := by linarith
  have hid : Real.log (c * ((n : ℝ) + 1) / Q) / ((n : ℝ) + 1)
        - Real.log (c * (n : ℝ) / Q) / (n : ℝ)
      = ((n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) - Real.log (c * (n : ℝ) / Q))
          / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [hlogA]
    field_simp
    ring
  have hnum : |(n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) - Real.log (c * (n : ℝ) / Q)|
      ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [hid, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1))]
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr hnum

/-- **The sawtooth step bound.** `|w(n+1) − w(n)| ≤ 1/n² + (⌊Q/n⌋₊ − ⌊Q/(n+1)⌋₊)/Q`: off a
jump the two weights share the numerator and `sawtooth_step_core` applies; across a jump both
lie in `[0, 1/Q]` and the floor difference pays for the whole of it. -/
private lemma sawtooth_step_le {Q : ℝ} (hQ : 0 < Q) {n : ℕ} (hn : 1 ≤ n) (hnQ : (n : ℝ) ≤ Q) :
    |Real.log (((⌊Q / ((n : ℝ) + 1)⌋₊ : ℝ) + 1) * ((n : ℝ) + 1) / Q) / ((n : ℝ) + 1)
        - Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q) / (n : ℝ)|
      ≤ 1 / (n : ℝ) ^ 2 + ((⌊Q / (n : ℝ)⌋₊ : ℝ) - (⌊Q / ((n : ℝ) + 1)⌋₊ : ℝ)) / Q := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn10 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hmono : ⌊Q / ((n : ℝ) + 1)⌋₊ ≤ ⌊Q / (n : ℝ)⌋₊ := by
    refine Nat.floor_mono ?_
    gcongr
    linarith
  by_cases hjump : ⌊Q / ((n : ℝ) + 1)⌋₊ = ⌊Q / (n : ℝ)⌋₊
  · rw [hjump]
    have hcore := sawtooth_step_core (Q := Q) (c := (⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) hQ hn
      (by positivity) (sawtooth_arg_ge_one hQ hn0) (sawtooth_arg_le_two hQ hn0 hnQ)
    have hle : 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hzero : ((⌊Q / (n : ℝ)⌋₊ : ℝ) - (⌊Q / (n : ℝ)⌋₊ : ℝ)) / Q = 0 := by ring
    rw [hzero]
    linarith
  · have hlt : ⌊Q / ((n : ℝ) + 1)⌋₊ < ⌊Q / (n : ℝ)⌋₊ := lt_of_le_of_ne hmono hjump
    have hd : (1 : ℝ) ≤ (⌊Q / (n : ℝ)⌋₊ : ℝ) - (⌊Q / ((n : ℝ) + 1)⌋₊ : ℝ) := by
      have h : ((⌊Q / ((n : ℝ) + 1)⌋₊ : ℕ) : ℝ) + 1 ≤ ((⌊Q / (n : ℝ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hlt
      linarith
    have hw0 := sawtooth_w_nonneg hQ hn0
    have hw0' := sawtooth_w_le hQ hn0
    have hw1 := sawtooth_w_nonneg hQ hn10
    have hw1' := sawtooth_w_le hQ hn10
    have hstep : 1 / Q ≤ ((⌊Q / (n : ℝ)⌋₊ : ℝ) - (⌊Q / ((n : ℝ) + 1)⌋₊ : ℝ)) / Q :=
      (div_le_div_iff_of_pos_right hQ).mpr hd
    have hsq : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
    rw [abs_le]
    constructor <;> linarith

/-- Discrete Abel over `(a, N]`: the difference of the two `[1, ·]` identities. -/
private lemma abel_sum_Ioc (c G : ℕ → ℝ) {a N : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) :
    ∑ m ∈ Finset.Ioc a N, c m * G m
      = (∑ m ∈ Finset.Icc 1 N, c m) * G N - (∑ m ∈ Finset.Icc 1 a, c m) * G a
        - ∑ n ∈ Finset.Ico a N, (∑ m ∈ Finset.Icc 1 n, c m) * (G (n + 1) - G n) := by
  have h1 := abel_sum c G (le_trans ha haN)
  have h2 := abel_sum c G ha
  have hIcc1 : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIcc2 : Finset.Icc 1 a = Finset.Ioc 0 a := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hs1 : ∑ m ∈ Finset.Icc 1 a, c m * G m + ∑ m ∈ Finset.Ioc a N, c m * G m
      = ∑ m ∈ Finset.Icc 1 N, c m * G m := by
    rw [hIcc1, hIcc2]
    exact Finset.sum_Ioc_consecutive _ (Nat.zero_le a) haN
  have hs2 : ∑ n ∈ Finset.Ico 1 a, (∑ m ∈ Finset.Icc 1 n, c m) * (G (n + 1) - G n)
      + ∑ n ∈ Finset.Ico a N, (∑ m ∈ Finset.Icc 1 n, c m) * (G (n + 1) - G n)
      = ∑ n ∈ Finset.Ico 1 N, (∑ m ∈ Finset.Icc 1 n, c m) * (G (n + 1) - G n) :=
    Finset.sum_Ico_consecutive _ ha haN
  linarith

/-- The telescoping sum over `[a, N)`: `Σ (G n − G (n+1)) = G a − G N`. -/
private lemma sum_Ico_telescope (G : ℕ → ℝ) {a N : ℕ} (h : a ≤ N) :
    ∑ n ∈ Finset.Ico a N, (G n - G (n + 1)) = G a - G N := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    ring

/-- The trivial bound `|P(Q)| ≤ 1`, from `0 ≤ w ≤ 1/Q` termwise and `⌊Q⌋₊ ≤ Q`. -/
private lemma abs_sawtooth_sum_le_one {Q : ℝ} (hQ : 1 ≤ Q) :
    |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊,
        (moebius n : ℝ) / n * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)| ≤ 1 := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊Q⌋₊,
      |(moebius n : ℝ) / n * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)| ≤ 1 / Q := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnQ : (n : ℝ) ≤ Q := le_trans (by exact_mod_cast hnN) hNQ
    have hwn := sawtooth_w_nonneg hQ0 hn0
    have hwl := sawtooth_w_le hQ0 hn0
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have heq : (moebius n : ℝ) / (n : ℝ)
          * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)
        = (moebius n : ℝ) * (Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q) / (n : ℝ)) := by
      ring
    rw [heq, abs_mul, abs_of_nonneg hwn]
    calc |((moebius n : ℤ) : ℝ)| * (Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q) / (n : ℝ))
        ≤ 1 * (1 / Q) := mul_le_mul hmu hwl hwn (by norm_num)
      _ = 1 / Q := one_mul _
  calc |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊,
          (moebius n : ℝ) / n * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)|
      ≤ ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊,
          |(moebius n : ℝ) / n * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊Q⌋₊, (1 : ℝ) / Q := Finset.sum_le_sum hterm
    _ = ((⌊Q⌋₊ : ℕ) : ℝ) * (1 / Q) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one hQ0]
        exact hNQ

/-- `|x − y − z| ≤ |x| + |y| + |z|`. -/
private lemma abs_sub_sub_le (x y z : ℝ) : |x - y - z| ≤ |x| + |y| + |z| := by
  have h1 : |x - y - z| ≤ |x - y| + |z| := by
    rw [sub_eq_add_neg (x - y) z]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg]
  have h2 : |x - y| ≤ |x| + |y| := by
    rw [sub_eq_add_neg x y]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg]
  linarith

set_option maxHeartbeats 4000000 in
-- C2 carries the two regimes, the `K`/`a` cut arithmetic, one discrete Abel and a total
-- variation split inside a SINGLE declaration; it exceeds the default budget by far.
/-- **C2 (the sawtooth-log piece `P`).** `|Σ_{n ≤ Q}(μ(n)/n)·log((⌊Q/n⌋₊+1)n/Q)| ≤
C/(log 2Q)^A` for every `A > 0`.

TWO REGIMES. Below `Q₀(A) := 4096·((4A)^A)⁴ + 4096` the trivial `0 ≤ w(n) ≤ 1/Q` gives
`|P| ≤ ⌊Q⌋₊/Q ≤ 1`, absorbed into `C ≥ (log 2Q₀)^A`. Above it the A4 helper
`log_rpow_le_rpow_quarter` gives `(log 2Q)^A ≤ √Q/4`, so the integer `K := ⌊(log 2Q)^A⌋₊ + 1`
is `≤ √Q/2` and the cut `a := ⌊Q/K⌋₊` satisfies `a ≥ √Q`: the range `[1, a]` is bounded
termwise by `a/Q ≤ 1/K ≤ (log 2Q)^{−A}`, and on `(a, N]` a SINGLE discrete Abel
(`abel_sum_Ioc`) against `Mmu` runs at saving `B = 2A + 1`. **No fibre decomposition is
needed** — the total variation of `w` is `≤ 1/n²` off a jump of `⌊Q/·⌋₊` and
`≤ (⌊Q/n⌋₊ − ⌊Q/(n+1)⌋₊)/Q` across one, and the jump part TELESCOPES to `⌊Q/a⌋₊/Q ≤ 2K/Q`.
On `[a, N]`, `log 2n ≥ ½·log 2Q`, so `|Mmu n| ≤ C_B·2^B·n/(log 2Q)^B` throughout.

The constant is NON-EFFECTIVE: it carries `mmuRate_holds`'s window through H6a at `2A + 1`.

The must-FAIL control (measured): with `μ(n)` → `μ²(n)`, `|Σ|·log²(2Q) = 8.8 … 62.5` over
`Q = 10² … 10⁶` — UNBOUNDED. **Recorded so nobody re-proposes it as a control:** the mutant
that DROPS the `+ 1` (`log(⌊Q/n⌋₊·n/Q)`) measures
`×log²(2Q) = −0.81 / −0.31 / +0.27 / +0.10 / −0.05` over the same range — bounded and
shrinking, it PASSES at every tested point and is NOT a kill-check (the sawtooth log carries
its own Möbius cancellation). -/
theorem abs_sum_moebius_mul_log_floor_ratio_le (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n * Real.log (((⌊Q / n⌋₊ : ℝ) + 1) * n / Q)|
      ≤ C / Real.log (2 * Q) ^ A := by
  classical
  have hB0 : (0 : ℝ) < 2 * A + 1 := by linarith
  obtain ⟨CB, hCB, hMbound⟩ := abs_sum_moebius_le_div_log_pow (2 * A + 1) hB0
  have hkap0 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hQ04096 : (4096 : ℝ) ≤ 4096 * ((4 * A) ^ A) ^ 4 + 4096 := by
    nlinarith [pow_pos hkap0 4]
  have hlogQ0 : 0 < Real.log (2 * (4096 * ((4 * A) ^ A) ^ 4 + 4096)) :=
    Real.log_pos (by linarith)
  have h2B : (0 : ℝ) < (2 : ℝ) ^ (2 * A + 1) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨max (Real.log (2 * (4096 * ((4 * A) ^ A) ^ 4 + 4096)) ^ A)
    (1 + 8 * CB * 2 ^ (2 * A + 1)), lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro Q hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQne : Q ≠ 0 := hQpos.ne'
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : 0 < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  rcases lt_or_ge Q (4096 * ((4 * A) ^ A) ^ 4 + 4096) with hsmall | hbig
  -- ═══ REGIME 1: the trivial bound, absorbed into `C` ═══
  · have htriv := abs_sawtooth_sum_le_one hQ
    have hmono : Real.log (2 * Q) ^ A
        ≤ Real.log (2 * (4096 * ((4 * A) ^ A) ^ 4 + 4096)) ^ A :=
      Real.rpow_le_rpow hlog2Q.le (Real.log_le_log (by linarith) (by linarith)) hA.le
    refine le_trans htriv ?_
    rw [le_div_iff₀ hlog2QA, one_mul]
    exact le_trans hmono (le_max_left _ _)
  -- ═══ REGIME 2: the cut, the termwise range and one discrete Abel ═══
  · have hQ4096 : (4096 : ℝ) ≤ Q := by linarith
    have hq40 : (0 : ℝ) < Q ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hq4pow : (Q ^ (1 / 4 : ℝ)) ^ 4 = Q := by
      rw [rpow_pow_nat hQpos.le, show (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have hs0 : (0 : ℝ) < Q ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hspow : (Q ^ (1 / 2 : ℝ)) ^ 2 = Q := by
      rw [rpow_pow_nat hQpos.le, show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have hsq4 : Q ^ (1 / 2 : ℝ) = (Q ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [rpow_pow_nat hQpos.le, show (1 / 4 : ℝ) * ((2 : ℕ) : ℝ) = 1 / 2 by norm_num]
    have hq48 : (8 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := by
      refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hq40.le ?_
      rw [hq4pow]
      linarith [show (8 : ℝ) ^ 4 = 4096 by norm_num]
    have hs64 : (64 : ℝ) ≤ Q ^ (1 / 2 : ℝ) := by
      rw [hsq4]
      nlinarith only [hq48]
    have hkapq : (8 : ℝ) * (4 * A) ^ A ≤ Q ^ (1 / 4 : ℝ) := by
      refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hq40.le ?_
      rw [hq4pow, show (8 * (4 * A) ^ A) ^ 4 = 4096 * ((4 * A) ^ A) ^ 4 by ring]
      linarith
    have hA4 := log_rpow_le_rpow_quarter A hA (show (1 : ℝ) ≤ 2 * Q by linarith)
    have hsplit24 : (2 * Q) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 4 : ℝ) * Q ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hQpos.le
    have h2quarter : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 / 4 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hLA : Real.log (2 * Q) ^ A ≤ Q ^ (1 / 2 : ℝ) / 4 := by
      have h1 : Real.log (2 * Q) ^ A
          ≤ (4 * A) ^ A * ((2 : ℝ) ^ (1 / 4 : ℝ) * Q ^ (1 / 4 : ℝ)) := by
        rw [← hsplit24]; exact hA4
      have hstep : (2 : ℝ) ^ (1 / 4 : ℝ) * Q ^ (1 / 4 : ℝ) ≤ 2 * Q ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right h2quarter hq40.le
      have h2 : (4 * A) ^ A * ((2 : ℝ) ^ (1 / 4 : ℝ) * Q ^ (1 / 4 : ℝ))
          ≤ (4 * A) ^ A * (2 * Q ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep hkap0.le
      have h3 : (4 * A) ^ A * (2 * Q ^ (1 / 4 : ℝ)) ≤ Q ^ (1 / 2 : ℝ) / 4 := by
        rw [hsq4]
        nlinarith only [hq40, hkap0, hkapq, mul_nonneg (sub_nonneg.mpr hkapq) hq40.le]
      linarith
    have hL1 : (1 : ℝ) ≤ Real.log (2 * Q) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hKgt : Real.log (2 * Q) ^ A < ((⌊Real.log (2 * Q) ^ A⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hKfl : ((⌊Real.log (2 * Q) ^ A⌋₊ : ℕ) : ℝ) ≤ Real.log (2 * Q) ^ A :=
      Nat.floor_le hlog2QA.le
    set K : ℕ := ⌊Real.log (2 * Q) ^ A⌋₊ + 1 with hKdef
    have hKcast : ((K : ℕ) : ℝ) = ((⌊Real.log (2 * Q) ^ A⌋₊ : ℕ) : ℝ) + 1 := by
      rw [hKdef]; push_cast; ring
    have hK1 : 1 ≤ K := by rw [hKdef]; omega
    have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
    have hKne : (K : ℝ) ≠ 0 := hK0.ne'
    have hKgt' : Real.log (2 * Q) ^ A < (K : ℝ) := by rw [hKcast]; exact hKgt
    have hKb : (K : ℝ) ≤ Real.log (2 * Q) ^ A + 1 := by rw [hKcast]; linarith
    have hKle : (K : ℝ) ≤ Q ^ (1 / 2 : ℝ) / 2 := by linarith
    have hQK : 2 * Q ^ (1 / 2 : ℝ) ≤ Q / (K : ℝ) := by
      have h1 : Q / (Q ^ (1 / 2 : ℝ) / 2) ≤ Q / (K : ℝ) :=
        div_le_div_of_nonneg_left hQpos.le hK0 hKle
      have h2 : Q / (Q ^ (1 / 2 : ℝ) / 2) = 2 * Q ^ (1 / 2 : ℝ) := by
        rw [eq_comm, eq_div_iff (by positivity)]
        nlinarith only [hspow]
      linarith
    set a : ℕ := ⌊Q / (K : ℝ)⌋₊ with hadef
    have haQK : ((a : ℕ) : ℝ) ≤ Q / (K : ℝ) := Nat.floor_le (by positivity)
    have hagt : Q / (K : ℝ) < ((a : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hage : Q ^ (1 / 2 : ℝ) ≤ ((a : ℕ) : ℝ) := by linarith
    have ha1 : 1 ≤ a := by
      have h : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by linarith
      exact_mod_cast h
    have ha1R : (1 : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha1
    have haR0 : (0 : ℝ) < ((a : ℕ) : ℝ) := by linarith
    have hQKQ : Q / (K : ℝ) ≤ Q := by
      rw [div_le_iff₀ hK0]
      nlinarith only [hK1R, hQpos]
    have haN : a ≤ ⌊Q⌋₊ := by
      rw [hadef]
      exact Nat.floor_mono hQKQ
    have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
    have haQ : ((a : ℕ) : ℝ) ≤ Q := le_trans haQK hQKQ
    have hN1 : 1 ≤ ⌊Q⌋₊ := le_trans ha1 haN
    have hNR1 : (1 : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN1
    -- `log 2m ≥ ½ log 2Q` for every `m ≥ a`
    have hlogstep : ∀ m : ℕ, a ≤ m → Real.log (2 * Q) / 2 ≤ Real.log (2 * (m : ℝ)) := by
      intro m hm
      have hma : ((a : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hsm : Q ^ (1 / 2 : ℝ) ≤ (m : ℝ) := le_trans hage hma
      have hm2 : (2 * Q) ^ (1 / 2 : ℝ) ≤ 2 * (m : ℝ) := by
        refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
        have hh : ((2 * Q) ^ (1 / 2 : ℝ)) ^ 2 = 2 * Q := by
          rw [rpow_pow_nat (by positivity),
            show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
        rw [hh]
        nlinarith only [hspow, hs0, hsm]
      have hlogr : Real.log ((2 * Q) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log (2 * Q) :=
        Real.log_rpow (by linarith) _
      have h := Real.log_le_log (by positivity) hm2
      rw [hlogr] at h
      linarith
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = CB * 2 ^ (2 * A + 1) / Real.log (2 * Q) ^ (2 * A + 1) :=
      ⟨_, rfl⟩
    have hLB : (0 : ℝ) < Real.log (2 * Q) ^ (2 * A + 1) := Real.rpow_pos_of_pos hlog2Q _
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    -- H6a on `[a, N]`, re-windowed by the log step
    have hMb : ∀ m : ℕ, a ≤ m → |∑ i ∈ Finset.Icc 1 m, (moebius i : ℝ)| ≤ D * (m : ℝ) := by
      intro m hm
      have hma : ((a : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
      have hfl : ⌊(m : ℝ)⌋₊ = m := Nat.floor_natCast m
      have h := hMbound (m : ℝ) hm1
      rw [hfl] at h
      have hstep := hlogstep m hm
      have hhalf : (0 : ℝ) < Real.log (2 * Q) / 2 := by linarith
      have hpow0 : (0 : ℝ) < (Real.log (2 * Q) / 2) ^ (2 * A + 1) :=
        Real.rpow_pos_of_pos hhalf _
      have hpow : (Real.log (2 * Q) / 2) ^ (2 * A + 1)
          ≤ Real.log (2 * (m : ℝ)) ^ (2 * A + 1) :=
        Real.rpow_le_rpow hhalf.le hstep hB0.le
      have hdiv : (Real.log (2 * Q) / 2) ^ (2 * A + 1)
          = Real.log (2 * Q) ^ (2 * A + 1) / 2 ^ (2 * A + 1) :=
        Real.div_rpow hlog2Q.le (by norm_num : (0 : ℝ) ≤ 2) (2 * A + 1)
      have hstep1 : CB * (m : ℝ) / Real.log (2 * (m : ℝ)) ^ (2 * A + 1)
          ≤ CB * (m : ℝ) / (Real.log (2 * Q) / 2) ^ (2 * A + 1) :=
        div_le_div_of_nonneg_left (by positivity) hpow0 hpow
      have hstep2 : CB * (m : ℝ) / (Real.log (2 * Q) / 2) ^ (2 * A + 1) = D * (m : ℝ) := by
        rw [hdiv, hD]
        field_simp
        try ring
      linarith only [h, hstep1, hstep2.le, hstep2.ge]
    -- the weight and the floor sequence
    obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ m : ℕ,
        w m = Real.log (((⌊Q / (m : ℝ)⌋₊ : ℝ) + 1) * (m : ℝ) / Q) / (m : ℝ) := ⟨_, fun _ => rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, ∀ m : ℕ, G m = ((⌊Q / (m : ℝ)⌋₊ : ℕ) : ℝ) := ⟨_, fun _ => rfl⟩
    have hsumeq : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊,
          (moebius n : ℝ) / n * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)
        = ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) * w n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hw n]
      ring
    rw [hsumeq]
    have hsplit : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) * w n
        = ∑ n ∈ Finset.Icc 1 a, (moebius n : ℝ) * w n
          + ∑ n ∈ Finset.Ioc a ⌊Q⌋₊, (moebius n : ℝ) * w n := by
      have hIcc1 : Finset.Icc 1 ⌊Q⌋₊ = Finset.Ioc 0 ⌊Q⌋₊ := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      have hIcc2 : Finset.Icc 1 a = Finset.Ioc 0 a := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      rw [hIcc1, hIcc2]
      exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le a) haN).symm
    -- the termwise range `[1, a]`
    have hsmallrange : |∑ n ∈ Finset.Icc 1 a, (moebius n : ℝ) * w n| ≤ 1 / (K : ℝ) := by
      have hterm : ∀ n ∈ Finset.Icc 1 a, |(moebius n : ℝ) * w n| ≤ 1 / Q := by
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hwn : 0 ≤ w n := by rw [hw n]; exact sawtooth_w_nonneg hQpos hn0
        have hwl : w n ≤ 1 / Q := by rw [hw n]; exact sawtooth_w_le hQpos hn0
        have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        rw [abs_mul, abs_of_nonneg hwn]
        calc |((moebius n : ℤ) : ℝ)| * w n ≤ 1 * (1 / Q) := mul_le_mul hmu hwl hwn (by norm_num)
          _ = 1 / Q := one_mul _
      calc |∑ n ∈ Finset.Icc 1 a, (moebius n : ℝ) * w n|
          ≤ ∑ n ∈ Finset.Icc 1 a, |(moebius n : ℝ) * w n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 a, (1 : ℝ) / Q := Finset.sum_le_sum hterm
        _ = ((a : ℕ) : ℝ) * (1 / Q) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            norm_num
        _ ≤ 1 / (K : ℝ) := by
            rw [mul_one_div, div_le_div_iff₀ hQpos hK0]
            have h := mul_le_mul_of_nonneg_right haQK hK0.le
            have h2 : Q / (K : ℝ) * (K : ℝ) = Q := by field_simp
            linarith only [h, h2.le, h2.ge]
    -- the Abel range `(a, N]`
    have habel := abel_sum_Ioc (fun m => (moebius m : ℝ)) w ha1 haN
    have hwN0 : 0 ≤ w ⌊Q⌋₊ := by rw [hw]; exact sawtooth_w_nonneg hQpos (by linarith)
    have hwNle : w ⌊Q⌋₊ ≤ 1 / Q := by rw [hw]; exact sawtooth_w_le hQpos (by linarith)
    have hwa0 : 0 ≤ w a := by rw [hw]; exact sawtooth_w_nonneg hQpos haR0
    have hwale : w a ≤ 1 / Q := by rw [hw]; exact sawtooth_w_le hQpos haR0
    have hb1 : |(∑ m ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius m : ℝ)) * w ⌊Q⌋₊| ≤ D := by
      rw [abs_mul, abs_of_nonneg hwN0]
      calc |∑ m ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius m : ℝ)| * w ⌊Q⌋₊
          ≤ (D * ((⌊Q⌋₊ : ℕ) : ℝ)) * (1 / Q) :=
            mul_le_mul (hMb _ haN) hwNle hwN0 (by positivity)
        _ ≤ D := by
            rw [mul_one_div, div_le_iff₀ hQpos]
            nlinarith only [hD0, hNQ]
    have hb2 : |(∑ m ∈ Finset.Icc 1 a, (moebius m : ℝ)) * w a| ≤ D := by
      rw [abs_mul, abs_of_nonneg hwa0]
      calc |∑ m ∈ Finset.Icc 1 a, (moebius m : ℝ)| * w a
          ≤ (D * ((a : ℕ) : ℝ)) * (1 / Q) :=
            mul_le_mul (hMb _ le_rfl) hwale hwa0 (by positivity)
        _ ≤ D := by
            rw [mul_one_div, div_le_iff₀ hQpos]
            nlinarith only [hD0, haQ]
    -- the total variation
    have hGnn : ∀ m : ℕ, 0 ≤ G m := by
      intro m; rw [hG]; positivity
    have hGa : G a ≤ 2 * (K : ℝ) := by
      have h4 : G a ≤ Q / ((a : ℕ) : ℝ) := by
        rw [hG]; exact Nat.floor_le (by positivity)
      have h1 : (2 : ℝ) ≤ Q / (K : ℝ) := by linarith
      have hhalf : Q / (K : ℝ) / 2 ≤ ((a : ℕ) : ℝ) := by linarith
      have h5 : Q / (K : ℝ) ≤ 2 * ((a : ℕ) : ℝ) := by linarith
      have h6 := mul_le_mul_of_nonneg_right h5 hK0.le
      have h7 : Q / (K : ℝ) * (K : ℝ) = Q := by field_simp
      have hQa : Q ≤ 2 * (K : ℝ) * ((a : ℕ) : ℝ) := by nlinarith only [h6, h7]
      have h8 : Q / ((a : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
        rw [div_le_iff₀ haR0]
        linarith
      linarith
    have hvar : ∑ n ∈ Finset.Ico a ⌊Q⌋₊,
          |(∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ)) * (w (n + 1) - w n)|
        ≤ D * (1 + Real.log Q + 2 * (K : ℝ)) := by
      have hterm : ∀ n ∈ Finset.Ico a ⌊Q⌋₊,
          |(∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ)) * (w (n + 1) - w n)|
            ≤ D * (1 / (n : ℝ)) + D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) * (G n - G (n + 1)) := by
        intro n hn
        obtain ⟨han, hnN⟩ := Finset.mem_Ico.mp hn
        have hn1 : 1 ≤ n := le_trans ha1 han
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hnne : (n : ℝ) ≠ 0 := hn0.ne'
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hnN' : (n : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnN.le
        have hnQ : (n : ℝ) ≤ Q := by linarith
        have hwn1 : w (n + 1)
            = Real.log (((⌊Q / ((n : ℝ) + 1)⌋₊ : ℝ) + 1) * ((n : ℝ) + 1) / Q)
                / ((n : ℝ) + 1) := by
          rw [hw (n + 1), hcast]
        have hGn1 : G (n + 1) = ((⌊Q / ((n : ℝ) + 1)⌋₊ : ℕ) : ℝ) := by
          rw [hG (n + 1), hcast]
        have hE : |w (n + 1) - w n| ≤ 1 / (n : ℝ) ^ 2 + (G n - G (n + 1)) / Q := by
          rw [hwn1, hw n, hGn1, hG n]
          exact sawtooth_step_le hQpos hn1 hnQ
        have hdelta : 0 ≤ G n - G (n + 1) := by
          have hmono : ⌊Q / ((n : ℝ) + 1)⌋₊ ≤ ⌊Q / (n : ℝ)⌋₊ := by
            refine Nat.floor_mono ?_
            gcongr
            linarith
          have h : ((⌊Q / ((n : ℝ) + 1)⌋₊ : ℕ) : ℝ) ≤ ((⌊Q / (n : ℝ)⌋₊ : ℕ) : ℝ) := by
            exact_mod_cast hmono
          rw [hGn1, hG n]
          linarith
        have hmul : |(∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ))| * |w (n + 1) - w n|
            ≤ (D * (n : ℝ)) * (1 / (n : ℝ) ^ 2 + (G n - G (n + 1)) / Q) :=
          mul_le_mul (hMb n han) hE (abs_nonneg _) (by positivity)
        have hexp : (D * (n : ℝ)) * (1 / (n : ℝ) ^ 2 + (G n - G (n + 1)) / Q)
            = D * (1 / (n : ℝ)) + D * ((n : ℝ) / Q) * (G n - G (n + 1)) := by
          field_simp
          try ring
        have hbnd : D * ((n : ℝ) / Q) * (G n - G (n + 1))
            ≤ D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) * (G n - G (n + 1)) := by
          have h1 : (n : ℝ) / Q ≤ ((⌊Q⌋₊ : ℕ) : ℝ) / Q :=
            (div_le_div_iff_of_pos_right hQpos).mpr hnN'
          have h2 : D * ((n : ℝ) / Q) ≤ D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) :=
            mul_le_mul_of_nonneg_left h1 hD0
          exact mul_le_mul_of_nonneg_right h2 hdelta
        rw [abs_mul]
        linarith only [hmul, hexp.le, hexp.ge, hbnd]
      have hsum1 : ∑ n ∈ Finset.Ico a ⌊Q⌋₊, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log Q := by
        have hsub : Finset.Ico a ⌊Q⌋₊ ⊆ Finset.Icc 1 ⌊Q⌋₊ := by
          intro x hx
          rw [Finset.mem_Ico] at hx
          rw [Finset.mem_Icc]
          exact ⟨le_trans ha1 hx.1, hx.2.le⟩
        have h1 : ∑ n ∈ Finset.Ico a ⌊Q⌋₊, (1 : ℝ) / (n : ℝ)
            ≤ ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (1 : ℝ) / (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
        have h2 : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (1 : ℝ) / (n : ℝ)
            = ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, ((n : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun n _ => one_div _
        have h3 := sum_inv_le_one_add_log ⌊Q⌋₊
        have h4 : Real.log ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Real.log Q := Real.log_le_log (by linarith) hNQ
        rw [h2] at h1
        linarith only [h1, h3, h4]
      have hsum2 : ∑ n ∈ Finset.Ico a ⌊Q⌋₊, (G n - G (n + 1)) = G a - G ⌊Q⌋₊ :=
        sum_Ico_telescope G haN
      have hNQ' : ((⌊Q⌋₊ : ℕ) : ℝ) / Q ≤ 1 := by rw [div_le_one hQpos]; exact hNQ
      have hNQ0 : (0 : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) / Q := by positivity
      have hd1 : G a - G ⌊Q⌋₊ ≤ 2 * (K : ℝ) := by linarith [hGnn ⌊Q⌋₊]
      have hd0 : 0 ≤ G a - G ⌊Q⌋₊ := by
        have hle : Q / ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q / ((a : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hQpos.le haR0 (by exact_mod_cast haN)
        have h1 : G ⌊Q⌋₊ ≤ G a := by
          rw [hG, hG]
          exact_mod_cast Nat.floor_mono hle
        linarith
      calc ∑ n ∈ Finset.Ico a ⌊Q⌋₊,
            |(∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ)) * (w (n + 1) - w n)|
          ≤ ∑ n ∈ Finset.Ico a ⌊Q⌋₊,
              (D * (1 / (n : ℝ)) + D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) * (G n - G (n + 1))) :=
            Finset.sum_le_sum hterm
        _ = D * (∑ n ∈ Finset.Ico a ⌊Q⌋₊, (1 : ℝ) / (n : ℝ))
              + D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) * (G a - G ⌊Q⌋₊) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum2]
        _ ≤ D * (1 + Real.log Q + 2 * (K : ℝ)) := by
            have e1 : D * (∑ n ∈ Finset.Ico a ⌊Q⌋₊, (1 : ℝ) / (n : ℝ))
                ≤ D * (1 + Real.log Q) := mul_le_mul_of_nonneg_left hsum1 hD0
            have f2 : (0 : ℝ) ≤ D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) := mul_nonneg hD0 hNQ0
            have f1 : D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) ≤ D := by nlinarith [hD0, hNQ']
            have g1 : D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) * (G a - G ⌊Q⌋₊)
                ≤ D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) * (2 * (K : ℝ)) :=
              mul_le_mul_of_nonneg_left hd1 f2
            have g2 : D * (((⌊Q⌋₊ : ℕ) : ℝ) / Q) * (2 * (K : ℝ)) ≤ D * (2 * (K : ℝ)) :=
              mul_le_mul_of_nonneg_right f1 (by linarith only [hK0])
            linarith only [e1, g1, g2]
    -- assembly of the Abel range
    have hlargerange : |∑ n ∈ Finset.Ioc a ⌊Q⌋₊, (moebius n : ℝ) * w n|
        ≤ D * (3 + Real.log Q + 2 * (K : ℝ)) := by
      rw [habel]
      have hs : |∑ n ∈ Finset.Ico a ⌊Q⌋₊,
            (∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ)) * (w (n + 1) - w n)|
          ≤ ∑ n ∈ Finset.Ico a ⌊Q⌋₊,
              |(∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ)) * (w (n + 1) - w n)| :=
        Finset.abs_sum_le_sum_abs _ _
      have htri := abs_sub_sub_le
        ((∑ m ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius m : ℝ)) * w ⌊Q⌋₊)
        ((∑ m ∈ Finset.Icc 1 a, (moebius m : ℝ)) * w a)
        (∑ n ∈ Finset.Ico a ⌊Q⌋₊, (∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ)) * (w (n + 1) - w n))
      have hDbr : D * (3 + Real.log Q + 2 * (K : ℝ))
          = D + D + D * (1 + Real.log Q + 2 * (K : ℝ)) := by ring
      linarith only [hb1, hb2, hvar, hs, htri, hDbr.le, hDbr.ge]
    -- the numeric close
    have hLA1 : (1 : ℝ) ≤ Real.log (2 * Q) ^ (A + 1) := Real.one_le_rpow hL1 (by linarith)
    have hLL : Real.log (2 * Q) ≤ Real.log (2 * Q) ^ (A + 1) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ A + 1 by linarith)
      rwa [Real.rpow_one] at h
    have hLAle : Real.log (2 * Q) ^ A ≤ Real.log (2 * Q) ^ (A + 1) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hlogQ : Real.log Q ≤ Real.log (2 * Q) := Real.log_le_log hQpos (by linarith)
    have hbracket : 3 + Real.log Q + 2 * (K : ℝ) ≤ 8 * Real.log (2 * Q) ^ (A + 1) := by
      linarith only [hlogQ, hLL, hKb, hLAle, hLA1]
    have hBsplit : Real.log (2 * Q) ^ (2 * A + 1)
        = Real.log (2 * Q) ^ A * Real.log (2 * Q) ^ (A + 1) := by
      rw [← Real.rpow_add hlog2Q]
      congr 1
      ring
    have hLA1pos : (0 : ℝ) < Real.log (2 * Q) ^ (A + 1) := Real.rpow_pos_of_pos hlog2Q _
    have hDb : D * (8 * Real.log (2 * Q) ^ (A + 1))
        = 8 * CB * 2 ^ (2 * A + 1) / Real.log (2 * Q) ^ A := by
      rw [hD, hBsplit]
      field_simp
      try ring
    have hfin1 : (1 : ℝ) / (K : ℝ) ≤ 1 / Real.log (2 * Q) ^ A :=
      div_le_div_of_nonneg_left (by norm_num) hlog2QA hKgt'.le
    have hfin2 : D * (3 + Real.log Q + 2 * (K : ℝ))
        ≤ 8 * CB * 2 ^ (2 * A + 1) / Real.log (2 * Q) ^ A := by
      calc D * (3 + Real.log Q + 2 * (K : ℝ)) ≤ D * (8 * Real.log (2 * Q) ^ (A + 1)) :=
            mul_le_mul_of_nonneg_left hbracket hD0
        _ = _ := hDb
    have hfin3 : (1 + 8 * CB * 2 ^ (2 * A + 1)) / Real.log (2 * Q) ^ A
        = 1 / Real.log (2 * Q) ^ A + 8 * CB * 2 ^ (2 * A + 1) / Real.log (2 * Q) ^ A := by
      ring
    have hlast : |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) * w n|
        ≤ (1 + 8 * CB * 2 ^ (2 * A + 1)) / Real.log (2 * Q) ^ A := by
      rw [hsplit]
      have h := abs_add_le (∑ n ∈ Finset.Icc 1 a, (moebius n : ℝ) * w n)
        (∑ n ∈ Finset.Ioc a ⌊Q⌋₊, (moebius n : ℝ) * w n)
      linarith only [h, hsmallrange, hlargerange, hfin1, hfin2, hfin3.le, hfin3.ge]
    refine le_trans hlast ?_
    gcongr
    exact le_max_right _ _

/-! ### C3 — THE CONSTANT -/

/-- The telescoping `Σ_{m ≤ k}(log(m+1) − log m) = log(k+1)`. -/
private lemma sum_log_step_eq (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))
      = Real.log ((k : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1), ih]
    push_cast
    ring

/-- `H(k) = log(k+1) + Σ_{m ≤ k} δ_m` with `δ_m := 1/m − (log(m+1) − log m)`. -/
private lemma harmonic_eq_log_add_delta (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, (1 : ℝ) / m
      = Real.log ((k : ℝ) + 1)
        + ∑ m ∈ Finset.Icc 1 k, (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))) := by
  rw [Finset.sum_sub_distrib, sum_log_step_eq]
  ring

/-- `0 ≤ δ_m` for `m ≥ 1` (`log x ≤ x − 1` at `x = (m+1)/m`). -/
private lemma delta_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ 1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)
      = Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    rw [Real.log_div (by linarith) hm0.ne']
  rw [hdiv]
  have h := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < ((m : ℝ) + 1) / (m : ℝ) by positivity)
  have h2 : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
    field_simp
    ring
  linarith

/-- `δ_m ≤ 1/m²` for `m ≥ 1` (`1 − 1/x ≤ log x` at `x = (m+1)/m`, then
`1/m − 1/(m+1) = 1/(m(m+1)) ≤ 1/m²`). -/
private lemma delta_le_inv_sq {m : ℕ} (hm : 1 ≤ m) :
    1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) ≤ 1 / (m : ℝ) ^ 2 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)
      = Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    rw [Real.log_div (by linarith) hm0.ne']
  rw [hdiv]
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < ((m : ℝ) + 1) / (m : ℝ) by positivity)
  have h2 : 1 - (((m : ℝ) + 1) / (m : ℝ))⁻¹ = 1 / ((m : ℝ) + 1) := by
    rw [inv_div]
    field_simp
    ring
  rw [h2] at h
  have h4 : 1 / ((m : ℝ) * ((m : ℝ) + 1)) ≤ 1 / (m : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hm0] : (m : ℝ) ^ 2 ≤ (m : ℝ) * ((m : ℝ) + 1))
  have h5 : 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) = 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
    field_simp
    ring
  linarith

/-- The hyperbola swap `Σ_{n ≤ N} Σ_{m ≤ N/n} = Σ_{m ≤ N} Σ_{n ≤ N/m}` (both sides run over
the pairs with `n·m ≤ N`). -/
private lemma sum_hyperbola_swap (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / n), F n m
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / m), F n m := by
  refine Finset.sum_comm' ?_
  intro n m
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, _⟩, hm1, hmN⟩
    have hmul : m * n ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < n)).mp hmN
    have hmn : m ≤ m * n := Nat.le_mul_of_pos_right m (by omega)
    refine ⟨⟨hn1, ?_⟩, hm1, le_trans hmn hmul⟩
    refine (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr ?_
    rw [Nat.mul_comm]
    exact hmul
  · rintro ⟨⟨hn1, hnN⟩, hm1, _⟩
    have hmul : n * m ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp hnN
    have hmn : n ≤ n * m := Nat.le_mul_of_pos_right n (by omega)
    refine ⟨⟨hn1, le_trans hmn hmul⟩, hm1, ?_⟩
    refine (Nat.le_div_iff_mul_le (by omega : 0 < n)).mpr ?_
    rw [Nat.mul_comm]
    exact hmul

/-- `|(−x) − y| ≤ |x| + |y|`. -/
private lemma abs_neg_sub_le (x y : ℝ) : |(-x) - y| ≤ |x| + |y| := by
  have h : (-x) - y = -(x + y) := by ring
  rw [h, abs_neg]
  exact abs_add_le x y

/-- `log k ≤ log x` for a natural `k ≤ x` with `x ≥ 1` (the `k = 0` case uses
`Real.log 0 = 0`). -/
private lemma log_natCast_le_log {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : (k : ℝ) ≤ x) :
    Real.log (k : ℝ) ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg hx
  · exact Real.log_le_log (by exact_mod_cast hk0) hk

/-- The trivial bound `|Σ_{n ≤ k} μ(n)/n| ≤ 1 + log k`. -/
private lemma abs_sum_moebius_div_le_one_add_log (k : ℕ) :
    |∑ n ∈ Finset.Icc 1 k, (moebius n : ℝ) / n| ≤ 1 + Real.log (k : ℝ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 k, |(moebius n : ℝ) / (n : ℝ)| ≤ ((n : ℝ))⁻¹ := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_div, abs_of_nonneg hn0.le, inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hn0).mpr hmu
  calc |∑ n ∈ Finset.Icc 1 k, (moebius n : ℝ) / n|
      ≤ ∑ n ∈ Finset.Icc 1 k, |(moebius n : ℝ) / (n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 k, ((n : ℝ))⁻¹ := Finset.sum_le_sum hterm
    _ ≤ 1 + Real.log (k : ℝ) := sum_inv_le_one_add_log k

/-- `Σ_{m ≤ k} 1/m² ≤ 2`. -/
private lemma sum_inv_sq_le_two (k : ℕ) : ∑ m ∈ Finset.Icc 1 k, 1 / (m : ℝ) ^ 2 ≤ 2 := by
  have hset : Finset.Icc 1 k = Finset.Ioo 0 (k + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioo]; omega
  have h : ∑ i ∈ Finset.Ioo 0 (k + 1), (((i : ℝ)) ^ 2)⁻¹ ≤ 2 / ((0 : ℕ) + 1) :=
    sum_Ioo_inv_sq_le 0 (k + 1)
  rw [hset]
  refine le_trans (le_of_eq ?_) (le_trans h (by norm_num))
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

set_option maxHeartbeats 1600000 in
-- C3 is the exact identity `T = 1 − D − P` plus the near/far split of `D`, both in one
-- declaration; it exceeds the default elaboration budget.
/-- **C3 (THE CONSTANT).** `|Σ_{n ≤ Q}(μ(n)/n)·log(Q/n) − 1| ≤ C/(log 2Q)^A`.

`T = 1 − D − P` EXACTLY, from C1's harmonic identity and
`H(k) = log(k+1) + Σ_{m ≤ k} δ_m` with `δ_m := 1/m − log((m+1)/m) ∈ [0, 1/m²]`:
`log(Q/n) = H(⌊Q/n⌋₊) − Σ_{m ≤ ⌊Q/n⌋₊} δ_m − log((⌊Q/n⌋₊+1)n/Q)`. The `δ` double sum is
swapped on the hyperbola `nm ≤ ⌊Q⌋₊` into `D = Σ_{m ≤ Q} δ_m·f(Q/m)`; on `m ≤ √Q`,
`log(2Q/m) ≥ ½ log 2Q`, so H6b gives `|f| ≤ C_A 2^A(log 2Q)^{−A}` against `Σ δ_m ≤ 2`, and
on `m > √Q` the trivial `|f| ≤ 1 + log Q` runs against `Σ_{m > √Q} δ_m ≤ 2/√Q`, closed by
the A4 helper at `A` and `A + 1`. `P` is C2.

The constant is NON-EFFECTIVE (C2 and H6b both carry `mmuRate_holds`'s window).

The must-FAIL control (measured): with `− 1` → `− 0`, `T = 1.001035 / … / 0.999986` at
`Q = 10² … 10⁶`, so `|T|·(log 2Q)² = 28.1 / 57.8 / 98.1 / 149.0 / 210.5` — growing like
`(log 2Q)^A`, and no `C` closes it. -/
theorem abs_sum_moebius_div_mul_log_div_sub_one_le (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n * Real.log (Q / n) - 1|
      ≤ C / Real.log (2 * Q) ^ A := by
  classical
  obtain ⟨CP, hCP, hP⟩ := abs_sum_moebius_mul_log_floor_ratio_le A hA
  obtain ⟨Cf, hCf, hf⟩ := abs_sum_moebius_div_le_inv_log_pow A hA
  have h2A : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hk2 : (0 : ℝ) < (4 * (A + 1)) ^ (A + 1) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨CP + 2 * Cf * 2 ^ A + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)), by positivity, ?_⟩
  intro Q hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQne : Q ≠ 0 := hQpos.ne'
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : 0 < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hN1 : 1 ≤ ⌊Q⌋₊ := (Nat.one_le_floor_iff Q).mpr hQ
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
  -- the exact decomposition `T = 1 − D − P`
  have hC1 := sum_moebius_div_mul_harmonic_eq ⌊Q⌋₊ hN1
  have hpt : ∀ n ∈ Finset.Icc 1 ⌊Q⌋₊,
      (moebius n : ℝ) / n * Real.log (Q / (n : ℝ))
        = (moebius n : ℝ) / n * (∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / n), (1 : ℝ) / m)
          - (∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / n), (moebius n : ℝ) / n
              * (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))))
          - (moebius n : ℝ) / n
              * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q) := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hk : ⌊Q⌋₊ / n = ⌊Q / (n : ℝ)⌋₊ := (Nat.floor_div_natCast Q n).symm
    have hharm := harmonic_eq_log_add_delta (⌊Q⌋₊ / n)
    have hlogeq : Real.log (Q / (n : ℝ)) - Real.log (((⌊Q⌋₊ / n : ℕ) : ℝ) + 1)
        = -Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q) := by
      rw [hk, ← Real.log_div (by positivity) (by positivity), ← Real.log_inv]
      congr 1
      field_simp
    have hval : Real.log (Q / (n : ℝ))
        = (∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / n), (1 : ℝ) / m)
          - (∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / n),
              (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))))
          - Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q) := by
      linarith only [hharm, hlogeq]
    rw [hval, mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
  have hTsum : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n * Real.log (Q / (n : ℝ))
      = (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊,
          (moebius n : ℝ) / n * ∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / n), (1 : ℝ) / m)
        - (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / n),
            (moebius n : ℝ) / n * (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))))
        - (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n
            * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hswap := sum_hyperbola_swap ⌊Q⌋₊
    (fun n m => (moebius n : ℝ) / n
      * (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))))
  have hD : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / n),
        (moebius n : ℝ) / n * (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
      = ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
          (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
            * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n := by
    rw [hswap]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hmain : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n * Real.log (Q / (n : ℝ)) - 1
      = -(∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
            (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
              * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n)
        - (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n
            * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)) := by
    rw [hTsum, hD, hC1]
    ring
  rw [hmain]
  -- the split at `√Q`
  have hs0 : (0 : ℝ) < Q ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hs1 : (1 : ℝ) ≤ Q ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hspow : (Q ^ (1 / 2 : ℝ)) ^ 2 = Q := by
    rw [rpow_pow_nat hQpos.le, show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hQ12 : Q ^ (1 / 2 : ℝ) ≤ Q := by
    have h := Real.rpow_le_rpow_of_exponent_le hQ (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  set J : ℕ := ⌊Q ^ (1 / 2 : ℝ)⌋₊ with hJdef
  have hJN : J ≤ ⌊Q⌋₊ := by rw [hJdef]; exact Nat.floor_mono hQ12
  have hJle : ((J : ℕ) : ℝ) ≤ Q ^ (1 / 2 : ℝ) := Nat.floor_le hs0.le
  have hJgt : Q ^ (1 / 2 : ℝ) < ((J : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hIcc1 : Finset.Icc 1 ⌊Q⌋₊ = Finset.Ioc 0 ⌊Q⌋₊ := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIcc2 : Finset.Icc 1 J = Finset.Ioc 0 J := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hDsplit : ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
        (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
          * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n
      = (∑ m ∈ Finset.Icc 1 J,
          (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
            * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n)
        + ∑ m ∈ Finset.Ioc J ⌊Q⌋₊,
            (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
              * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n := by
    rw [hIcc1, hIcc2]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le J) hJN).symm
  -- the near range `m ≤ √Q`, by H6b
  have hnear : |∑ m ∈ Finset.Icc 1 J,
        (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
          * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
      ≤ 2 * Cf * 2 ^ A / Real.log (2 * Q) ^ A := by
    have hterm : ∀ m ∈ Finset.Icc 1 J,
        |(1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
            * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
          ≤ (1 / (m : ℝ) ^ 2) * (Cf * 2 ^ A / Real.log (2 * Q) ^ A) := by
      intro m hm
      obtain ⟨hm1, hmJ⟩ := Finset.mem_Icc.mp hm
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hmR : (m : ℝ) ≤ Q ^ (1 / 2 : ℝ) := le_trans (by exact_mod_cast hmJ) hJle
      have hQm : (1 : ℝ) ≤ Q / (m : ℝ) := by
        rw [le_div_iff₀ hm0]
        linarith only [hmR, hQ12]
      have hfl : ⌊Q / (m : ℝ)⌋₊ = ⌊Q⌋₊ / m := Nat.floor_div_natCast Q m
      have hfb := hf (Q / (m : ℝ)) hQm
      rw [hfl] at hfb
      have hbig : Q ^ (1 / 2 : ℝ) ≤ Q / (m : ℝ) := by
        rw [le_div_iff₀ hm0]
        nlinarith only [hmR, hspow, hs0, hm0]
      have hroot : (2 * Q) ^ (1 / 2 : ℝ) ≤ 2 * (Q / (m : ℝ)) := by
        refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
        have hh : ((2 * Q) ^ (1 / 2 : ℝ)) ^ 2 = 2 * Q := by
          rw [rpow_pow_nat (by positivity),
            show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
        rw [hh]
        nlinarith only [hbig, hs0, hspow]
      have hlogr : Real.log ((2 * Q) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log (2 * Q) :=
        Real.log_rpow (by linarith) _
      have hlogm : Real.log (2 * Q) / 2 ≤ Real.log (2 * (Q / (m : ℝ))) := by
        have h := Real.log_le_log (by positivity) hroot
        rw [hlogr] at h
        linarith
      have hhalf : (0 : ℝ) < Real.log (2 * Q) / 2 := by linarith
      have hpow0 : (0 : ℝ) < (Real.log (2 * Q) / 2) ^ A := Real.rpow_pos_of_pos hhalf _
      have hpow : (Real.log (2 * Q) / 2) ^ A ≤ Real.log (2 * (Q / (m : ℝ))) ^ A :=
        Real.rpow_le_rpow hhalf.le hlogm hA.le
      have hdiv : (Real.log (2 * Q) / 2) ^ A = Real.log (2 * Q) ^ A / 2 ^ A :=
        Real.div_rpow hlog2Q.le (by norm_num : (0 : ℝ) ≤ 2) A
      have hs1' : Cf / Real.log (2 * (Q / (m : ℝ))) ^ A ≤ Cf / (Real.log (2 * Q) / 2) ^ A :=
        div_le_div_of_nonneg_left hCf.le hpow0 hpow
      have hs2 : Cf / (Real.log (2 * Q) / 2) ^ A = Cf * 2 ^ A / Real.log (2 * Q) ^ A := by
        rw [hdiv]
        field_simp
      have hfin : |∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
          ≤ Cf * 2 ^ A / Real.log (2 * Q) ^ A := by
        linarith only [hfb, hs1', hs2.le, hs2.ge]
      have hd0 := delta_nonneg hm1
      have hd1 := delta_le_inv_sq hm1
      rw [abs_mul, abs_of_nonneg hd0]
      refine mul_le_mul hd1 hfin (abs_nonneg _) (by positivity)
    calc |∑ m ∈ Finset.Icc 1 J,
            (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
              * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
        ≤ ∑ m ∈ Finset.Icc 1 J,
            |(1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
              * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 J,
            (1 / (m : ℝ) ^ 2) * (Cf * 2 ^ A / Real.log (2 * Q) ^ A) := Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.Icc 1 J, 1 / (m : ℝ) ^ 2)
            * (Cf * 2 ^ A / Real.log (2 * Q) ^ A) := by rw [Finset.sum_mul]
      _ ≤ 2 * Cf * 2 ^ A / Real.log (2 * Q) ^ A := by
          have h1 := sum_inv_sq_le_two J
          have h2 : (0 : ℝ) ≤ Cf * 2 ^ A / Real.log (2 * Q) ^ A := by positivity
          have h3 := mul_le_mul_of_nonneg_right h1 h2
          have h4 : (2 : ℝ) * (Cf * 2 ^ A / Real.log (2 * Q) ^ A)
              = 2 * Cf * 2 ^ A / Real.log (2 * Q) ^ A := by ring
          linarith only [h3, h4.le, h4.ge]
  -- the far range `m > √Q`, by the trivial bound and the A4 helper
  have hfar : |∑ m ∈ Finset.Ioc J ⌊Q⌋₊,
        (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
          * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
      ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) / Real.log (2 * Q) ^ A := by
    have hterm : ∀ m ∈ Finset.Ioc J ⌊Q⌋₊,
        |(1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
            * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
          ≤ (1 / (m : ℝ) ^ 2) * (1 + Real.log Q) := by
      intro m hm
      obtain ⟨hmJ, hmN⟩ := Finset.mem_Ioc.mp hm
      have hm1 : 1 ≤ m := by omega
      have hd0 := delta_nonneg hm1
      have hd1 := delta_le_inv_sq hm1
      have htriv := abs_sum_moebius_div_le_one_add_log (⌊Q⌋₊ / m)
      have hle : ((⌊Q⌋₊ / m : ℕ) : ℝ) ≤ Q := by
        have h : (⌊Q⌋₊ / m : ℕ) ≤ ⌊Q⌋₊ := Nat.div_le_self _ _
        have h2 : ((⌊Q⌋₊ / m : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have hlogle : Real.log ((⌊Q⌋₊ / m : ℕ) : ℝ) ≤ Real.log Q := log_natCast_le_log hQ hle
      rw [abs_mul, abs_of_nonneg hd0]
      refine mul_le_mul hd1 (by linarith only [htriv, hlogle]) (abs_nonneg _) (by positivity)
    have htail : ∑ m ∈ Finset.Ioc J ⌊Q⌋₊, 1 / (m : ℝ) ^ 2 ≤ 2 / Q ^ (1 / 2 : ℝ) := by
      have hsub : Finset.Ioc J ⌊Q⌋₊ ⊆ Finset.Ioo J (⌊Q⌋₊ + 1) := by
        intro x hx
        rw [Finset.mem_Ioc] at hx
        rw [Finset.mem_Ioo]
        exact ⟨hx.1, by omega⟩
      have h1 : ∑ m ∈ Finset.Ioc J ⌊Q⌋₊, 1 / (m : ℝ) ^ 2
          ≤ ∑ m ∈ Finset.Ioo J (⌊Q⌋₊ + 1), 1 / (m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
      have h2 : ∑ m ∈ Finset.Ioo J (⌊Q⌋₊ + 1), 1 / (m : ℝ) ^ 2
          = ∑ m ∈ Finset.Ioo J (⌊Q⌋₊ + 1), (((m : ℝ)) ^ 2)⁻¹ :=
        Finset.sum_congr rfl fun m _ => one_div _
      have h3 : ∑ i ∈ Finset.Ioo J (⌊Q⌋₊ + 1), (((i : ℝ)) ^ 2)⁻¹ ≤ 2 / ((J : ℕ) + 1) :=
        sum_Ioo_inv_sq_le J (⌊Q⌋₊ + 1)
      have h4 : (2 : ℝ) / (((J : ℕ) : ℝ) + 1) ≤ 2 / Q ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hs0 hJgt.le
      rw [h2] at h1
      linarith only [h1, h3, h4]
    have hA4a := log_rpow_le_rpow_quarter A hA (show (1 : ℝ) ≤ 2 * Q by linarith)
    have hA4b := log_rpow_le_rpow_quarter (A + 1) (by linarith)
      (show (1 : ℝ) ≤ 2 * Q by linarith)
    have hsplit24 : (2 * Q) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 4 : ℝ) * Q ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hQpos.le
    have h2quarter : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 / 4 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hq40 : (0 : ℝ) < Q ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hq4s : Q ^ (1 / 4 : ℝ) ≤ Q ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
    have hL1 : Real.log (2 * Q) ^ (A + 1) = Real.log (2 * Q) ^ A * Real.log (2 * Q) := by
      rw [Real.rpow_add hlog2Q, Real.rpow_one]
    have hkey : (1 + Real.log Q) * 2 * Real.log (2 * Q) ^ A
        ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1 / 2 : ℝ) := by
      have hlq : Real.log Q ≤ Real.log (2 * Q) := Real.log_le_log hQpos (by linarith)
      have e1 : Real.log (2 * Q) ^ A ≤ (4 * A) ^ A * (2 * Q ^ (1 / 4 : ℝ)) := by
        refine le_trans hA4a ?_
        rw [hsplit24]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2quarter hq40.le) hk1.le
      have e2 : Real.log (2 * Q) ^ (A + 1) ≤ (4 * (A + 1)) ^ (A + 1) * (2 * Q ^ (1 / 4 : ℝ)) := by
        refine le_trans hA4b ?_
        rw [hsplit24]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2quarter hq40.le) hk2.le
      have e3 : Real.log (2 * Q) ^ A * Real.log (2 * Q) ≤ (4 * (A + 1)) ^ (A + 1)
          * (2 * Q ^ (1 / 4 : ℝ)) := by rw [← hL1]; exact e2
      have e4 : (0 : ℝ) ≤ Real.log (2 * Q) ^ A := hlog2QA.le
      have e5a : Real.log Q * Real.log (2 * Q) ^ A
          ≤ Real.log (2 * Q) * Real.log (2 * Q) ^ A := mul_le_mul_of_nonneg_right hlq e4
      have e5 : (1 + Real.log Q) * 2 * Real.log (2 * Q) ^ A
          ≤ 2 * Real.log (2 * Q) ^ A + 2 * (Real.log (2 * Q) ^ A * Real.log (2 * Q)) := by
        linarith only [e5a]
      have e6 : (4 : ℝ) * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1 / 4 : ℝ)
          ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hq4s (by positivity)
      linarith only [e1, e3, e5, e6]
    have hfinal : (2 / Q ^ (1 / 2 : ℝ)) * (1 + Real.log Q)
        ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) / Real.log (2 * Q) ^ A := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hs0 hlog2QA]
      linarith only [hkey]
    calc |∑ m ∈ Finset.Ioc J ⌊Q⌋₊,
            (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
              * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
        ≤ ∑ m ∈ Finset.Ioc J ⌊Q⌋₊,
            |(1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
              * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc J ⌊Q⌋₊, (1 / (m : ℝ) ^ 2) * (1 + Real.log Q) :=
          Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.Ioc J ⌊Q⌋₊, 1 / (m : ℝ) ^ 2) * (1 + Real.log Q) := by
          rw [Finset.sum_mul]
      _ ≤ (2 / Q ^ (1 / 2 : ℝ)) * (1 + Real.log Q) :=
          mul_le_mul_of_nonneg_right htail (by linarith)
      _ ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) / Real.log (2 * Q) ^ A := hfinal
  -- assembly
  have hPb := hP Q hQ
  have habs : |-(∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
        (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
          * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n)
      - (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n
          * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q))|
      ≤ |∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
          (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
            * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
        + |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n
            * Real.log (((⌊Q / (n : ℝ)⌋₊ : ℝ) + 1) * (n : ℝ) / Q)| := by
    exact abs_neg_sub_le _ _
  have hDb : |∑ m ∈ Finset.Icc 1 ⌊Q⌋₊,
        (1 / (m : ℝ) - (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
          * ∑ n ∈ Finset.Icc 1 (⌊Q⌋₊ / m), (moebius n : ℝ) / n|
      ≤ 2 * Cf * 2 ^ A / Real.log (2 * Q) ^ A
        + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) / Real.log (2 * Q) ^ A := by
    rw [hDsplit]
    exact le_trans (abs_add_le _ _) (add_le_add hnear hfar)
  have hsplitC : (CP + 2 * Cf * 2 ^ A + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)))
        / Real.log (2 * Q) ^ A
      = CP / Real.log (2 * Q) ^ A + 2 * Cf * 2 ^ A / Real.log (2 * Q) ^ A
        + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) / Real.log (2 * Q) ^ A := by ring
  linarith only [habs, hDb, hPb, hsplitC.le, hsplitC.ge]

/-- `|x − y| ≤ |x| + |y|`. -/
private lemma abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_neg]

/-- **H6c (the H freeze's row, verbatim).** `|Σ_{n ≤ Q} μ(n)·log n/n + 1| ≤ C/(log 2Q)^A`.

One line off C3 and H6b: `log(Q/n) = log Q − log n` splits the C3 sum as
`Σ μ(n)log n/n = log Q·f(Q) − T(Q)`, so `Σ μ(n)log n/n + 1 = log Q·f(Q) − (T(Q) − 1)`, and
H6b at the saving `A + 1` turns `log Q·f(Q)` into `C_{A+1}·log 2Q/(log 2Q)^{A+1}`.

The constant is NON-EFFECTIVE (C3 and H6b both carry `mmuRate_holds`'s window).

The must-FAIL control (measured): with `+ 1` → `+ 0`,
`|Σ_{n ≤ Q} μ(n)log n/n|·log²(2Q) = 24 … 210` over `Q = 10² … 10⁶` — UNBOUNDED. -/
theorem abs_sum_moebius_mul_log_div_add_one_le (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) * Real.log n / n + 1|
      ≤ C / Real.log (2 * Q) ^ A := by
  classical
  obtain ⟨CT, hCT, hT⟩ := abs_sum_moebius_div_mul_log_div_sub_one_le A hA
  obtain ⟨Cf, hCf, hf⟩ := abs_sum_moebius_div_le_inv_log_pow (A + 1) (by linarith)
  refine ⟨CT + Cf, by linarith, ?_⟩
  intro Q hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQne : Q ≠ 0 := hQpos.ne'
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : 0 < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hlq : Real.log Q ≤ Real.log (2 * Q) := Real.log_le_log hQpos (by linarith)
  have hLsplit : Real.log (2 * Q) ^ (A + 1) = Real.log (2 * Q) ^ A * Real.log (2 * Q) := by
    rw [Real.rpow_add hlog2Q, Real.rpow_one]
  have hid : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n * Real.log (Q / (n : ℝ))
      = Real.log Q * (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n)
        - ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) * Real.log (n : ℝ) / n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [Real.log_div hQne hn0.ne']
    ring
  have hTb := hT Q hQ
  have hfb := hf Q hQ
  have hgoal : ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) * Real.log (n : ℝ) / n + 1
      = Real.log Q * (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n)
        - (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n * Real.log (Q / (n : ℝ)) - 1) := by
    linarith only [hid]
  rw [hgoal]
  have hlogf : |Real.log Q * (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n)|
      ≤ Cf / Real.log (2 * Q) ^ A := by
    rw [abs_mul, abs_of_nonneg hlogQ0]
    have h1 : Real.log Q * |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n|
        ≤ Real.log (2 * Q) * (Cf / Real.log (2 * Q) ^ (A + 1)) :=
      mul_le_mul hlq hfb (abs_nonneg _) (by linarith)
    have h2 : Real.log (2 * Q) * (Cf / Real.log (2 * Q) ^ (A + 1))
        = Cf / Real.log (2 * Q) ^ A := by
      rw [hLsplit]
      field_simp
    linarith only [h1, h2.le, h2.ge]
  have htri := abs_sub_le_add (Real.log Q * (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n))
    (∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n * Real.log (Q / (n : ℝ)) - 1)
  have hsplitC : (CT + Cf) / Real.log (2 * Q) ^ A
      = Cf / Real.log (2 * Q) ^ A + CT / Real.log (2 * Q) ^ A := by ring
  linarith only [htri, hlogf, hTb, hsplitC.le, hsplitC.ge]

/-! ## IV. THE t-SMOOTH CONVOLUTION -/

open scoped Classical in
/-- The indicator of the `t`-smooth integers, as an arithmetic function. -/
private noncomputable def smoothInd (t : ℕ) : ArithmeticFunction ℤ where
  toFun n := if n = 0 then 0 else if n.primeFactors ⊆ t.primeFactors then 1 else 0
  map_zero' := by simp

private lemma smoothInd_apply (t : ℕ) {n : ℕ} (hn : n ≠ 0) :
    smoothInd t n = if n.primeFactors ⊆ t.primeFactors then 1 else 0 := by
  classical
  simp [smoothInd, hn]

private lemma smoothInd_one (t : ℕ) : smoothInd t 1 = 1 := by
  rw [smoothInd_apply t one_ne_zero, Nat.primeFactors_one]
  simp

private lemma isMultiplicative_smoothInd (t : ℕ) : (smoothInd t).IsMultiplicative := by
  classical
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨smoothInd_one t, fun {m n} hm hn hmn => ?_⟩
  rw [smoothInd_apply t (Nat.mul_ne_zero hm hn), smoothInd_apply t hm, smoothInd_apply t hn]
  have hun : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
    Nat.Coprime.primeFactors_mul hmn
  by_cases h1 : m.primeFactors ⊆ t.primeFactors
  · by_cases h2 : n.primeFactors ⊆ t.primeFactors
    · have hpf : (m * n).primeFactors ⊆ t.primeFactors := by
        rw [hun]
        exact Finset.union_subset h1 h2
      rw [if_pos hpf, if_pos h1, if_pos h2, mul_one]
    · have hpf : ¬ (m * n).primeFactors ⊆ t.primeFactors := by
        rw [hun]
        exact fun hcon => h2 fun x hx => hcon (Finset.mem_union_right _ hx)
      rw [if_neg hpf, if_pos h1, if_neg h2, mul_zero]
  · have hpf : ¬ (m * n).primeFactors ⊆ t.primeFactors := by
      rw [hun]
      exact fun hcon => h1 fun x hx => hcon (Finset.mem_union_left _ hx)
    rw [if_neg hpf, if_neg h1, zero_mul]

open scoped Classical in
/-- `n ↦ μ(n)·[(n,t) = 1]`, as an arithmetic function. -/
private noncomputable def coprimeMoebius (t : ℕ) : ArithmeticFunction ℤ where
  toFun n := if Nat.Coprime n t then moebius n else 0
  map_zero' := by
    classical
    by_cases h : Nat.Coprime 0 t
    · rw [if_pos h, ArithmeticFunction.map_zero]
    · rw [if_neg h]

private lemma coprimeMoebius_apply (t n : ℕ) :
    coprimeMoebius t n = if Nat.Coprime n t then moebius n else 0 := by
  classical
  simp [coprimeMoebius]

private lemma isMultiplicative_coprimeMoebius (t : ℕ) : (coprimeMoebius t).IsMultiplicative := by
  classical
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · rw [coprimeMoebius_apply, if_pos (Nat.coprime_one_left t),
      isMultiplicative_moebius.map_one]
  · intro m n _ _ hmn
    rw [coprimeMoebius_apply, coprimeMoebius_apply, coprimeMoebius_apply]
    by_cases h1 : Nat.Coprime m t
    · by_cases h2 : Nat.Coprime n t
      · rw [if_pos (Nat.Coprime.mul_left h1 h2), if_pos h1, if_pos h2,
          isMultiplicative_moebius.map_mul_of_coprime hmn]
      · have hne : ¬ Nat.Coprime (m * n) t := fun hcon =>
          h2 (Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) hcon)
        rw [if_neg hne, if_pos h1, if_neg h2, mul_zero]
    · have hne : ¬ Nat.Coprime (m * n) t := fun hcon =>
        h1 (Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) hcon)
      rw [if_neg hne, if_neg h1, zero_mul]

/-- `Σ_{k ∣ m} μ(k) = [m = 1]` over `ℤ`. -/
private lemma sum_divisors_moebius_int (m : ℕ) :
    ∑ k ∈ m.divisors, (moebius k) = if m = 1 then (1 : ℤ) else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]

/-- **The pointwise `t`-smooth convolution identity.**
`Σ_{d ∣ m, d t-smooth} μ(m/d) = μ(m)·[(m,t) = 1]`. Both sides are multiplicative, so
`IsMultiplicative.eq_iff_eq_on_prime_powers` reduces it to prime powers: at `p ∤ t` only
`d = 1` is smooth and the sum is `μ(p^i)`; at `p ∣ t` every `p^j` is smooth and the sum
telescopes to `[p^i = 1]`, exactly matching the coprimality indicator. -/
private lemma moebius_mul_smoothInd (t : ℕ) (ht : t ≠ 0) :
    (moebius * smoothInd t : ArithmeticFunction ℤ) = coprimeMoebius t := by
  classical
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_moebius.mul (isMultiplicative_smoothInd t)) _
    (isMultiplicative_coprimeMoebius t)]
  intro p i hp
  have hp0 : 0 < p := hp.pos
  have hexpand : (moebius * smoothInd t : ArithmeticFunction ℤ) (p ^ i)
      = ∑ j ∈ Finset.range (i + 1), (moebius (p ^ (i - j))) * smoothInd t (p ^ j) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal' (fun a b => (moebius a) * smoothInd t b),
      Nat.sum_divisors_prime_pow hp]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≤ i := by
      have := Finset.mem_range.mp hj
      omega
    rw [Nat.pow_div hji hp0]
  rw [hexpand, coprimeMoebius_apply]
  by_cases hpt : p ∈ t.primeFactors
  · -- every `p^j` is smooth
    have hsm : ∀ j : ℕ, smoothInd t (p ^ j) = 1 := by
      intro j
      rw [smoothInd_apply t (by positivity), if_pos ?_]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [pow_zero, Nat.primeFactors_one]
        exact Finset.empty_subset _
      · rw [Nat.primeFactors_pow p (by omega), hp.primeFactors]
        exact Finset.singleton_subset_iff.mpr hpt
    have hsum : ∑ j ∈ Finset.range (i + 1), (moebius (p ^ (i - j))) * smoothInd t (p ^ j)
        = ∑ j ∈ Finset.range (i + 1), (moebius (p ^ j)) := by
      have h1 : ∑ j ∈ Finset.range (i + 1), (moebius (p ^ (i - j))) * smoothInd t (p ^ j)
          = ∑ j ∈ Finset.range (i + 1), (moebius (p ^ (i + 1 - 1 - j))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsm j, mul_one, show i + 1 - 1 - j = i - j by omega]
      rw [h1, Finset.sum_range_reflect (fun k => (moebius (p ^ k)))]
    rw [hsum, ← Nat.sum_divisors_prime_pow hp, sum_divisors_moebius_int]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, if_pos rfl, if_pos (Nat.coprime_one_left t),
        isMultiplicative_moebius.map_one]
    · have hne : p ^ i ≠ 1 := by
        intro hcon
        have := Nat.pow_eq_one.mp hcon
        rcases this with h | h
        · exact hp.one_lt.ne' h
        · omega
      have hnc : ¬ Nat.Coprime (p ^ i) t := by
        intro hc
        have hpd : p ∣ t := (Nat.mem_primeFactors.mp hpt).2.1
        have hpp : p ∣ p ^ i := dvd_pow_self p (by omega)
        have : p ∣ Nat.gcd (p ^ i) t := Nat.dvd_gcd hpp hpd
        rw [hc] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      rw [if_neg hne, if_neg hnc]
  · -- only `d = 1` is smooth
    have hnd : ¬ p ∣ t := by
      intro hd
      exact hpt (Nat.mem_primeFactors.mpr ⟨hp, hd, ht⟩)
    have hzero : ∀ j ∈ Finset.range (i + 1), j ≠ 0 →
        (moebius (p ^ (i - j))) * smoothInd t (p ^ j) = 0 := by
      intro j _ hj
      rw [smoothInd_apply t (by positivity), if_neg ?_, mul_zero]
      rw [Nat.primeFactors_pow p hj, hp.primeFactors]
      exact fun hcon => hpt (Finset.singleton_subset_iff.mp hcon)
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) hzero, pow_zero,
      smoothInd_one, mul_one, Nat.sub_zero,
      if_pos (Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))]

/-- **S1 (the convolution).** `Σ_{m ≤ X, (m,t)=1} μ(m)G(m) = Σ_{d ≤ X smooth} Σ_{e ≤ X/d}
μ(e)G(de)` for `t ≥ 1`.

Undo the inner reindex (`sum_dvd_reindex` at level `d`), swap, and the inner sum becomes the
pointwise convolution identity above.

The must-FAIL control (measured, K34): the binder `1 ≤ t` is load-bearing — at `t = 0` and
`m = 2` the LHS is `0` (`Coprime m 0 ↔ m = 1`) while the RHS is `−1` (the smooth set at
level 0 is `{1}`, so the RHS is `Σ_{e ≤ X} μ(e)G(e)`). -/
theorem sum_coprime_moebius_eq_sum_smooth (t X : ℕ) (ht : 1 ≤ t) (G : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m t), (moebius m : ℝ) * G m
      = ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ t.primeFactors),
          ∑ e ∈ Finset.Icc 1 (X / d), (moebius e : ℝ) * G (d * e) := by
  classical
  have ht0 : t ≠ 0 := by omega
  have hRHS : ∀ d ∈ (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ t.primeFactors),
      (∑ e ∈ Finset.Icc 1 (X / d), (moebius e : ℝ) * G (d * e))
        = ∑ m ∈ (Finset.Icc 1 X).filter (fun m => d ∣ m), (moebius (m / d) : ℝ) * G m := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    rw [sum_dvd_reindex hd1 (fun m => (moebius (m / d) : ℝ) * G m)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Nat.mul_div_cancel_left e (by omega : 0 < d)]
  rw [Finset.sum_congr rfl hRHS]
  have hswap : ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ t.primeFactors),
        ∑ m ∈ (Finset.Icc 1 X).filter (fun m => d ∣ m), (moebius (m / d) : ℝ) * G m
      = ∑ m ∈ Finset.Icc 1 X,
          ∑ d ∈ m.divisors.filter (fun d => d.primeFactors ⊆ t.primeFactors),
            (moebius (m / d) : ℝ) * G m := by
    refine Finset.sum_comm' ?_
    intro d m
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hd1, hdX⟩, hsm⟩, ⟨hm1, hmX⟩, hdm⟩
      exact ⟨⟨⟨hdm, by omega⟩, hsm⟩, hm1, hmX⟩
    · rintro ⟨⟨⟨hdm, _⟩, hsm⟩, hm1, hmX⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm (by omega)
      have hdX : d ≤ X := le_trans (Nat.le_of_dvd (by omega) hdm) hmX
      exact ⟨⟨⟨hd1, hdX⟩, hsm⟩, ⟨hm1, hmX⟩, hdm⟩
  rw [hswap, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := by
    have := (Finset.mem_Icc.mp hm).1
    omega
  have hkey : ∑ d ∈ m.divisors.filter (fun d => d.primeFactors ⊆ t.primeFactors),
      (moebius (m / d) : ℤ) = if Nat.Coprime m t then moebius m else 0 := by
    have hconv : (moebius * smoothInd t : ArithmeticFunction ℤ) m
        = ∑ d ∈ m.divisors, (moebius (m / d)) * smoothInd t d := by
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal' (fun a b => (moebius a) * smoothInd t b)]
    rw [moebius_mul_smoothInd t ht0, coprimeMoebius_apply] at hconv
    rw [hconv, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := Nat.pos_of_mem_divisors hd |>.ne'
    rw [smoothInd_apply t hd0]
    by_cases hsm : d.primeFactors ⊆ t.primeFactors
    · rw [if_pos hsm, if_pos hsm, mul_one]
    · rw [if_neg hsm, if_neg hsm, mul_zero]
  have hcast : ∑ d ∈ m.divisors.filter (fun d => d.primeFactors ⊆ t.primeFactors),
        (moebius (m / d) : ℝ) * G m
      = ((∑ d ∈ m.divisors.filter (fun d => d.primeFactors ⊆ t.primeFactors),
          (moebius (m / d) : ℤ) : ℤ) : ℝ) * G m := by
    push_cast
    rw [Finset.sum_mul]
  rw [hcast, hkey]
  by_cases hc : Nat.Coprime m t
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, Int.cast_zero, zero_mul]


/-- The exact geometric partial sum `Σ_{a < n}(1/q)^a = (q/(q−1))(1 − (1/q)^n)`. -/
private lemma geom_partial_eq {q : ℝ} (hq : 2 ≤ q) (n : ℕ) :
    ∑ a ∈ Finset.range n, (1 / q) ^ a = (q / (q - 1)) * (1 - (1 / q) ^ n) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (q : ℝ) - 1 ≠ 0 := by intro h; linarith
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, div_pow, div_pow, one_pow, one_pow]
    have hqm : (q : ℝ) ^ m ≠ 0 := by positivity
    field_simp
    ring

/-- `Σ_{a < n}(1/q)^a ≤ q/(q − 1)` for `q ≥ 2`. -/
private lemma geom_partial_le {q : ℝ} (hq : 2 ≤ q) (n : ℕ) :
    ∑ a ∈ Finset.range n, (1 / q) ^ a ≤ q / (q - 1) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  rw [geom_partial_eq hq n]
  have h1 : (0 : ℝ) ≤ (1 / q) ^ n := by positivity
  have h2 : (0 : ℝ) ≤ q / (q - 1) := by positivity
  nlinarith [h1, h2]

/-- The smooth partial sum against the Euler product, over an arbitrary finite prime set:
`Σ_{d ≤ X, d S-smooth} 1/d ≤ ∏_{p ∈ S} p/(p − 1)`.

Induction on `S`. At the step `insert q S`, every `S'`-smooth `d ≤ X` is `q^a·e` with
`e = ordCompl[q] d` again `S`-smooth (`q ∤ e`, and every other prime of `e` divides `d`), so
`d ↦ (v_q(d), ordCompl[q] d)` is an INJECTION of the level-`S'` index set into
`range(X+1) ×ˢ (level S)`; only the injection is needed, never a bijection, because the
inequality goes the easy way. -/
private lemma sum_smooth_inv_le_prod (X : ℕ) :
    ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
      ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ S), (1 : ℝ) / d
        ≤ ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) := by
  classical
  intro S
  refine Finset.induction_on S ?_ ?_
  · intro _
    have hsub : (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ (∅ : Finset ℕ))
        ⊆ ({1} : Finset ℕ) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      have hemp : d.primeFactors = ∅ := Finset.subset_empty.mp hd.2
      rcases Nat.primeFactors_eq_empty.mp hemp with h | h
      · omega
      · simp [h]
    calc ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ (∅ : Finset ℕ)), (1 : ℝ) / d
        ≤ ∑ d ∈ ({1} : Finset ℕ), (1 : ℝ) / d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
      _ = 1 := by norm_num
      _ = ∏ p ∈ (∅ : Finset ℕ), ((p : ℝ) / ((p : ℝ) - 1)) := by rw [Finset.prod_empty]
  · intro q S hq ih hprime
    have hqp : Nat.Prime q := hprime q (Finset.mem_insert_self q S)
    have hSp : ∀ p ∈ S, Nat.Prime p := fun p hp => hprime p (Finset.mem_insert_of_mem hp)
    have hq2 : 2 ≤ q := hqp.two_le
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
    set T' := (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ insert q S) with hT'
    set TS := (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ S) with hTS
    set Φ : ℕ → ℕ × ℕ := fun d => (d.factorization q, d / q ^ d.factorization q) with hΦ
    have hrec : ∀ d : ℕ, q ^ (Φ d).1 * (Φ d).2 = d := fun d =>
      Nat.ordProj_mul_ordCompl_eq_self d q
    have hinj : Set.InjOn Φ (↑T' : Set ℕ) := by
      intro d₁ _ d₂ _ heq
      rw [← hrec d₁, ← hrec d₂, heq]
    have hmaps : ∀ d ∈ T', Φ d ∈ Finset.range (X + 1) ×ˢ TS := by
      intro d hd
      rw [hT', Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdX⟩, hsm⟩ := hd
      have hd0 : d ≠ 0 := by omega
      have hdvd : q ^ d.factorization q ∣ d := Nat.ordProj_dvd d q
      have hple : q ^ d.factorization q ≤ d := Nat.le_of_dvd (by omega) hdvd
      have hpow : 2 ^ d.factorization q ≤ q ^ d.factorization q := Nat.pow_le_pow_left hq2 _
      have haX : d.factorization q ≤ X :=
        le_trans (le_of_lt Nat.lt_two_pow_self) (le_trans hpow (le_trans hple hdX))
      have hediv : d / q ^ d.factorization q ∣ d := Nat.ordCompl_dvd d q
      have he1 : 1 ≤ d / q ^ d.factorization q := Nat.pos_of_dvd_of_pos hediv (by omega)
      have heX : d / q ^ d.factorization q ≤ X :=
        le_trans (Nat.le_of_dvd (by omega) hediv) hdX
      have hnq : ¬ q ∣ d / q ^ d.factorization q := Nat.not_dvd_ordCompl hqp hd0
      simp only [hΦ, Finset.mem_product]
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [hTS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨he1, heX⟩, fun p hp => ?_⟩
      have hpe : p ∣ d / q ^ d.factorization q := Nat.dvd_of_mem_primeFactors hp
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∈ d.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpprime, dvd_trans hpe hediv, hd0⟩
      have hpne : p ≠ q := fun hcon => hnq (hcon ▸ hpe)
      rcases Finset.mem_insert.mp (hsm hpd) with h | h
      · exact absurd h hpne
      · exact h
    have hTSnn : (0 : ℝ) ≤ ∑ e ∈ TS, (1 : ℝ) / e :=
      Finset.sum_nonneg fun e _ => by positivity
    calc ∑ d ∈ T', (1 : ℝ) / d
        = ∑ d ∈ T', (1 : ℝ) / ((q ^ (Φ d).1 * (Φ d).2 : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hrec d]
      _ = ∑ z ∈ T'.image Φ, (1 : ℝ) / ((q ^ z.1 * z.2 : ℕ) : ℝ) :=
          (Finset.sum_image (f := fun z : ℕ × ℕ => (1 : ℝ) / ((q ^ z.1 * z.2 : ℕ) : ℝ))
            hinj).symm
      _ ≤ ∑ z ∈ Finset.range (X + 1) ×ˢ TS, (1 : ℝ) / ((q ^ z.1 * z.2 : ℕ) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
          intro z hz
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
          exact hmaps d hd
      _ = (∑ a ∈ Finset.range (X + 1), ((1 : ℝ) / (q : ℝ)) ^ a) * ∑ e ∈ TS, (1 : ℝ) / e := by
          rw [Finset.sum_product, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          push_cast
          rw [div_pow, one_pow, div_mul_div_comm, one_mul]
      _ ≤ ((q : ℝ) / ((q : ℝ) - 1)) * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) :=
          mul_le_mul (geom_partial_le hqR _) (ih hSp) hTSnn
            (le_of_lt (div_pos hq0 (by linarith)))
      _ = ∏ p ∈ insert q S, ((p : ℝ) / ((p : ℝ) - 1)) :=
          (Finset.prod_insert (f := fun p : ℕ => (p : ℝ) / ((p : ℝ) - 1)) hq).symm

/-- **S2.** `Σ_{d ≤ X, d t-smooth} 1/d ≤ t/φ(t)` for `t ≥ 1`.

The smooth partial sum against the Euler product over `t.primeFactors`, and
`∏_{p ∣ t} p/(p − 1) = t/φ(t)` by the landed totient product.

The must-FAIL control (measured): with `t/φ(t)` → `φ(t)/t` at `(t, X) = (2, 10)` the LHS is
`1.875 > 0.5`. -/
theorem sum_smooth_inv_le (t X : ℕ) (ht : 1 ≤ t) :
    ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ t.primeFactors), (1 : ℝ) / d
      ≤ (t : ℝ) / Nat.totient t := by
  classical
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hU := prod_one_sub_pos t
  have h := sum_smooth_inv_le_prod X t.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp
  refine le_trans h (le_of_eq ?_)
  have hone : (∏ p ∈ t.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
      * ∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℝ) ≠ 0 := by linarith
    have h2 : (p : ℝ) - 1 ≠ 0 := by intro hcon; linarith
    field_simp
  have hprodeq : ∏ p ∈ t.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))
      = 1 / ∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [eq_div_iff hU.ne']
    exact hone
  have hcast : (t : ℝ) / (Nat.totient t : ℝ) = 1 / ∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hp := totient_div_eq_prod_one_sub t ht
    rw [div_eq_iff ht0.ne'] at hp
    rw [hp, div_eq_div_iff (mul_ne_zero hU.ne' ht0.ne') hU.ne']
    ring
  rw [hprodeq, hcast]

/-! ### S3 — the smooth tail, by a FINITE prime-step induction -/

/-- `(p^{−1/2})² = 1/p`. -/
private lemma rpow_neg_half_sq {p : ℕ} (hp : 1 ≤ p) :
    ((p : ℝ) ^ (-(1/2) : ℝ)) ^ 2 = 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [rpow_pow_nat hp0.le, show (-(1/2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num,
    Real.rpow_neg hp0.le, Real.rpow_one, one_div]

/-- `(p^{−1/4})⁴ = 1/p`. -/
private lemma rpow_neg_quarter_pow {p : ℕ} (hp : 1 ≤ p) :
    ((p : ℝ) ^ (-(1/4) : ℝ)) ^ 4 = 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [rpow_pow_nat hp0.le, show (-(1/4 : ℝ)) * ((4 : ℕ) : ℝ) = -1 by norm_num,
    Real.rpow_neg hp0.le, Real.rpow_one, one_div]

/-- `(p^{−1/4})² = p^{−1/2}`. -/
private lemma rpow_neg_quarter_sq {p : ℕ} (hp : 1 ≤ p) :
    ((p : ℝ) ^ (-(1/4) : ℝ)) ^ 2 = (p : ℝ) ^ (-(1/2) : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [rpow_pow_nat hp0.le, show (-(1/4 : ℝ)) * ((2 : ℕ) : ℝ) = -(1/2 : ℝ) by norm_num]

/-- `(q^a)^{−1/2} = (q^{−1/2})^a`. -/
private lemma rpow_natPow_neg_half {q : ℕ} (hq : 1 ≤ q) (a : ℕ) :
    ((q : ℝ) ^ a) ^ (-(1/2) : ℝ) = ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [rpow_pow_nat hq0.le (-(1/2) : ℝ) a, ← Real.rpow_natCast ((q : ℝ)) a,
    ← Real.rpow_mul hq0.le]
  congr 1
  ring

/-- `0 < p^{−1/2} < 1` for `p ≥ 2`. -/
private lemma rpow_neg_half_lt_one {p : ℕ} (hp : 2 ≤ p) :
    0 < (p : ℝ) ^ (-(1/2) : ℝ) ∧ (p : ℝ) ^ (-(1/2) : ℝ) < 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpos : 0 < (p : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_pos_of_pos hp0 _
  refine ⟨hpos, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hsq := rpow_neg_half_sq (show 1 ≤ p by omega)
  have hkey : (p : ℝ) * ((p : ℝ) ^ (-(1/2) : ℝ)) ^ 2 = 1 := by
    rw [hsq]
    field_simp
  have hv2 : (1 : ℝ) ≤ ((p : ℝ) ^ (-(1/2) : ℝ)) ^ 2 := by nlinarith only [hcon]
  nlinarith only [hv2, hkey, hp2]

/-- `p/(p−1) ≤ (1 − p^{−1/2})⁻¹` for `p ≥ 2` — with `v = p^{−1/2}` and `v² = 1/p`, both
reduce to `1 ≤ p·v`. -/
private lemma prime_ratio_le_inv_one_sub {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
  obtain ⟨hv0, hv1⟩ := rpow_neg_half_lt_one hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsq := rpow_neg_half_sq (show 1 ≤ p by omega)
  have h1 : (p : ℝ) * ((p : ℝ) ^ (-(1/2) : ℝ)) ^ 2 = 1 := by
    rw [hsq]
    field_simp
  have hpv : (1 : ℝ) ≤ (p : ℝ) * (p : ℝ) ^ (-(1/2) : ℝ) := by
    nlinarith only [h1, hv0, hv1, hp2]
  rw [div_le_iff₀ (by linarith), inv_eq_one_div, div_mul_eq_mul_div,
    le_div_iff₀ (by linarith)]
  nlinarith only [hpv, hp2, hv0, hv1]

/-- **The prime step for the smooth partial sum.** With `q^m > ⌊Y⌋₊`, every `insert q S`-smooth
`d ≤ Y` is uniquely `q^a·e` with `a ≤ m` and `e` an `S`-smooth integer `≤ Y/q^a`. -/
private lemma smooth_sum_step {q : ℕ} (hq : q.Prime) {S : Finset ℕ} (hqS : q ∉ S)
    (Y : ℝ) (hY : 0 < Y) (m : ℕ) (hm : ⌊Y⌋₊ < q ^ m) :
    ∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => d.primeFactors ⊆ insert q S), (1 : ℝ) / d
      = ∑ a ∈ Finset.range (m + 1), (1 / (q : ℝ)) ^ a
          * ∑ e ∈ (Finset.Icc 1 ⌊Y / (q : ℝ) ^ a⌋₊).filter (fun e => e.primeFactors ⊆ S),
              (1 : ℝ) / e := by
  classical
  have hq2 : 2 ≤ q := hq.two_le
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hbij : ∑ z ∈ (Finset.range (m + 1)).sigma
        (fun a => (Finset.Icc 1 ⌊Y / (q : ℝ) ^ a⌋₊).filter (fun e => e.primeFactors ⊆ S)),
        (1 : ℝ) / ((q ^ z.1 * z.2 : ℕ) : ℝ)
      = ∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => d.primeFactors ⊆ insert q S),
          (1 : ℝ) / (d : ℝ) := by
    refine Finset.sum_nbij' (i := fun z => q ^ z.1 * z.2)
      (j := fun d => ⟨d.factorization q, d / q ^ d.factorization q⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨a, e⟩ hz
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hz
      obtain ⟨_, ⟨he1, heY⟩, hesm⟩ := hz
      have he0 : e ≠ 0 := by omega
      have hqa0 : (0 : ℝ) < (q : ℝ) ^ a := by positivity
      have heR : (e : ℝ) ≤ Y / (q : ℝ) ^ a := by
        refine le_trans ?_ (Nat.floor_le (by positivity : (0 : ℝ) ≤ Y / (q : ℝ) ^ a))
        exact_mod_cast heY
      have hprod : ((q ^ a * e : ℕ) : ℝ) ≤ Y := by
        push_cast
        rw [← le_div_iff₀' hqa0]
        exact heR
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hqa1 : 1 ≤ q ^ a := Nat.one_le_pow a q hq0
      have hpos1 : 1 ≤ q ^ a * e := by
        calc (1 : ℕ) = 1 * 1 := by norm_num
          _ ≤ q ^ a * e := Nat.mul_le_mul hqa1 he1
      refine ⟨⟨hpos1, Nat.le_floor hprod⟩, ?_⟩
      intro x hx
      rw [Nat.primeFactors_mul (by positivity) he0] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Nat.eq_zero_or_pos a with rfl | ha0
        · simp at hx
        · rw [Nat.primeFactors_pow q (show a ≠ 0 by omega), hq.primeFactors,
            Finset.mem_singleton] at hx
          exact Finset.mem_insert.mpr (Or.inl hx)
      · exact Finset.mem_insert.mpr (Or.inr (hesm hx))
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdY⟩, hdsm⟩ := hd
      have hd0 : d ≠ 0 := by omega
      have hdvd : q ^ d.factorization q ∣ d := Nat.ordProj_dvd d q
      have hple : q ^ d.factorization q ≤ d := Nat.le_of_dvd (by omega) hdvd
      have halt : d.factorization q < m := by
        by_contra hcon
        rw [not_lt] at hcon
        have hstep : q ^ m ≤ q ^ d.factorization q := Nat.pow_le_pow_right (by omega) hcon
        omega
      have hediv : d / q ^ d.factorization q ∣ d := Nat.ordCompl_dvd d q
      have he1 : 1 ≤ d / q ^ d.factorization q := Nat.pos_of_dvd_of_pos hediv (by omega)
      have hnq : ¬ q ∣ d / q ^ d.factorization q := Nat.not_dvd_ordCompl hq hd0
      have hqa0 : (0 : ℝ) < (q : ℝ) ^ d.factorization q := by positivity
      have hrec : q ^ d.factorization q * (d / q ^ d.factorization q) = d :=
        Nat.ordProj_mul_ordCompl_eq_self d q
      have hdR : (d : ℝ) ≤ Y := le_trans (by exact_mod_cast hdY) (Nat.floor_le hY.le)
      have heR : ((d / q ^ d.factorization q : ℕ) : ℝ) ≤ Y / (q : ℝ) ^ d.factorization q := by
        rw [le_div_iff₀ hqa0]
        have hh : ((q ^ d.factorization q * (d / q ^ d.factorization q) : ℕ) : ℝ) ≤ Y := by
          rw [hrec]; exact hdR
        push_cast at hh
        linarith
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨by omega, ⟨he1, Nat.le_floor heR⟩, ?_⟩
      intro x hx
      have hxdvd : x ∣ d / q ^ d.factorization q := Nat.dvd_of_mem_primeFactors hx
      have hxp : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
      have hxd : x ∈ d.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hxp, dvd_trans hxdvd hediv, hd0⟩
      have hxne : x ≠ q := fun hcon => hnq (hcon ▸ hxdvd)
      rcases Finset.mem_insert.mp (hdsm hxd) with h | h
      · exact absurd h hxne
      · exact h
    · rintro ⟨a, e⟩ hz
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hz
      obtain ⟨_, ⟨he1, _⟩, hesm⟩ := hz
      have he0 : e ≠ 0 := by omega
      have hqe : ¬ q ∣ e := by
        intro hdvd
        exact hqS (hesm (Nat.mem_primeFactors.mpr ⟨hq, hdvd, he0⟩))
      have hfac : (q ^ a * e).factorization q = a := by
        rw [Nat.factorization_mul (by positivity) he0]
        simp [Nat.Prime.factorization_pow hq, Nat.factorization_eq_zero_of_not_dvd hqe]
      have h2 : q ^ a * e / q ^ (q ^ a * e).factorization q = e := by
        rw [hfac, Nat.mul_div_cancel_left e (by positivity)]
      rw [h2, hfac]
    · intro d _
      exact Nat.ordProj_mul_ordCompl_eq_self d q
    · intro z _
      rfl
  rw [← hbij, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  push_cast
  rw [div_pow, one_pow, div_mul_div_comm, one_mul]

/-- **The smooth tail.** For every finite set `S` of primes and every `Y > 0`,
`∏_{p ∈ S} p/(p−1) − Σ_{d ≤ Y, S-smooth} 1/d ≤ Y^{−1/2}·∏_{p ∈ S}(1 − p^{−1/2})⁻¹`.

Every step is FINITE (`smooth_sum_step` at `m = ⌊Y⌋₊ + 1`), and the induction closes BECAUSE
the statement is carried for every `Y > 0`, not only for `Y ≥ 1`: below `1` the smooth sum is
empty while `Y^{−1/2} ≥ 1`, which is exactly what pays for the geometric tail
`(q/(q−1))·q^{−(m+1)}` at the step. The two facts that close it are `P_S ≤ G_S` and
`q/(q−1) ≤ (1 − q^{−1/2})⁻¹`, both the per-prime `1 ≤ p·p^{−1/2}`. -/
private lemma smooth_tail_le :
    ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → ∀ Y : ℝ, 0 < Y →
      ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
        - ∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => d.primeFactors ⊆ S), (1 : ℝ) / d
      ≤ Y ^ (-(1/2) : ℝ) * ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
  classical
  intro S
  refine Finset.induction_on S ?_ ?_
  · intro _ Y hY
    rw [Finset.prod_empty, Finset.prod_empty, mul_one]
    have hpos : (0 : ℝ) < Y ^ (-(1/2) : ℝ) := Real.rpow_pos_of_pos hY _
    rcases lt_or_ge Y 1 with hY1 | hY1
    · have hfl : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr hY1
      rw [hfl]
      have hemp : (Finset.Icc 1 0).filter (fun d => d.primeFactors ⊆ (∅ : Finset ℕ)) = ∅ := by
        simp
      rw [hemp, Finset.sum_empty, sub_zero]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hY hY1.le (by norm_num)
    · have hN1 : 1 ≤ ⌊Y⌋₊ := (Nat.one_le_floor_iff Y).mpr hY1
      have hmem : (1 : ℕ) ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
          (fun d => d.primeFactors ⊆ (∅ : Finset ℕ)) := by
        rw [Finset.mem_filter, Finset.mem_Icc, Nat.primeFactors_one]
        exact ⟨⟨le_refl 1, hN1⟩, Finset.Subset.refl _⟩
      have hle := Finset.single_le_sum
        (f := fun d : ℕ => (1 : ℝ) / (d : ℝ)) (fun i _ => by positivity) hmem
      simp only [Nat.cast_one, div_one] at hle
      linarith
  · intro q S hqS ih hprime Y hY
    have hqp : Nat.Prime q := hprime q (Finset.mem_insert_self q S)
    have hSp : ∀ p ∈ S, Nat.Prime p := fun p hp => hprime p (Finset.mem_insert_of_mem hp)
    have hIH := ih hSp
    have hq2 : 2 ≤ q := hqp.two_le
    have hq0 : 0 < q := by omega
    have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    have hqR : (0 : ℝ) < (q : ℝ) := by linarith
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌊Y⌋₊ + 1 := ⟨_, rfl⟩
    have hm : ⌊Y⌋₊ < q ^ m := by
      have h1 : ⌊Y⌋₊ < 2 ^ ⌊Y⌋₊ := Nat.lt_two_pow_self
      have h2 : 2 ^ ⌊Y⌋₊ ≤ q ^ ⌊Y⌋₊ := Nat.pow_le_pow_left hq2 _
      have h3 : q ^ ⌊Y⌋₊ ≤ q ^ m := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hYq : Y ≤ (q : ℝ) ^ (m + 1) := by
      have h1 : Y < ((⌊Y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one Y
      have h2 : (⌊Y⌋₊ : ℕ) + 1 ≤ q ^ m := by omega
      have h3 : ((⌊Y⌋₊ : ℕ) : ℝ) + 1 ≤ ((q ^ m : ℕ) : ℝ) := by exact_mod_cast h2
      have h4 : ((q ^ m : ℕ) : ℝ) = (q : ℝ) ^ m := by push_cast; ring
      have h5 : (q : ℝ) ^ m ≤ (q : ℝ) ^ (m + 1) := by
        rw [pow_succ]
        nlinarith only [pow_pos hqR m, hqR2]
      rw [h4] at h3
      linarith
    obtain ⟨hr0, hr1⟩ := rpow_neg_half_lt_one hq2
    have hrsq := rpow_neg_half_sq (show 1 ≤ q by omega)
    have hii := prime_ratio_le_inv_one_sub hq2
    have hW0 : (0 : ℝ) < (1 - (q : ℝ) ^ (-(1/2) : ℝ))⁻¹ := inv_pos.mpr (by linarith)
    have hYhalf : (0 : ℝ) < Y ^ (-(1/2) : ℝ) := Real.rpow_pos_of_pos hY _
    have hYhalfsq : (Y ^ (-(1/2) : ℝ)) ^ 2 = 1 / Y := by
      rw [rpow_pow_nat hY.le, show (-(1/2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num,
        Real.rpow_neg hY.le, Real.rpow_one, one_div]
    have hP0 : (0 : ℝ) ≤ ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hSp p hp).two_le
      exact div_nonneg (by linarith) (by linarith)
    have hG0 : (0 : ℝ) < ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
      refine Finset.prod_pos fun p hp => ?_
      obtain ⟨h1, h2⟩ := rpow_neg_half_lt_one (hSp p hp).two_le
      exact inv_pos.mpr (by linarith)
    have hPG : ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
      refine Finset.prod_le_prod (fun p hp => ?_)
        (fun p hp => prime_ratio_le_inv_one_sub (hSp p hp).two_le)
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hSp p hp).two_le
      exact div_nonneg (by linarith) (by linarith)
    have hgeom1 : ∑ a ∈ Finset.range (m + 1), (1 / (q : ℝ)) ^ a
        = ((q : ℝ) / ((q : ℝ) - 1)) * (1 - (1 / (q : ℝ)) ^ (m + 1)) :=
      geom_partial_eq hqR2 (m + 1)
    have hgeom2 : ∑ a ∈ Finset.range (m + 1), ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a
        = (1 - ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1))
            * (1 - (q : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
      have hne : (1 : ℝ) - (q : ℝ) ^ (-(1/2) : ℝ) ≠ 0 := by intro h; linarith
      have hne2 : (q : ℝ) ^ (-(1/2) : ℝ) - 1 ≠ 0 := by intro h; linarith
      rw [geom_sum_eq (ne_of_lt hr1), inv_eq_one_div]
      field_simp
      ring
    have hrm : (1 / (q : ℝ)) ^ (m + 1) = (((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1)) ^ 2 := by
      rw [← hrsq, ← pow_mul, ← pow_mul, Nat.mul_comm]
    have hrm0 : (0 : ℝ) < ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1) := by positivity
    have hrmY : ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1) ≤ Y ^ (-(1/2) : ℝ) := by
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hYhalf.le ?_
      rw [← hrm, hYhalfsq, div_pow, one_pow]
      exact div_le_div_of_nonneg_left (by norm_num) hY hYq
    have hiii : (1 / (q : ℝ)) ^ (m + 1)
        ≤ Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1) := by
      rw [hrm, sq]
      exact mul_le_mul_of_nonneg_right hrmY hrm0.le
    have hd4 : ((q : ℝ) / ((q : ℝ) - 1)) * (1 / (q : ℝ)) ^ (m + 1)
          * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ (1 - (q : ℝ) ^ (-(1/2) : ℝ))⁻¹
            * (Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1))
            * ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
      have hstep : ((q : ℝ) / ((q : ℝ) - 1)) * (1 / (q : ℝ)) ^ (m + 1)
          ≤ (1 - (q : ℝ) ^ (-(1/2) : ℝ))⁻¹
              * (Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1)) :=
        mul_le_mul hii hiii (by positivity) hW0.le
      have e1 : ((q : ℝ) / ((q : ℝ) - 1)) * (1 / (q : ℝ)) ^ (m + 1)
            * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
          ≤ (1 - (q : ℝ) ^ (-(1/2) : ℝ))⁻¹
              * (Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1))
              * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right hstep hP0
      have e2 : (1 - (q : ℝ) ^ (-(1/2) : ℝ))⁻¹
              * (Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1))
              * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
          ≤ (1 - (q : ℝ) ^ (-(1/2) : ℝ))⁻¹
              * (Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ (m + 1))
              * ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hPG
          (mul_nonneg hW0.le (mul_nonneg hYhalf.le hrm0.le))
      linarith only [e1, e2]
    have hterm : ∀ a ∈ Finset.range (m + 1),
        (1 / (q : ℝ)) ^ a * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
            - Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a
              * ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹
          ≤ (1 / (q : ℝ)) ^ a
              * ∑ e ∈ (Finset.Icc 1 ⌊Y / (q : ℝ) ^ a⌋₊).filter (fun e => e.primeFactors ⊆ S),
                  (1 : ℝ) / e := by
      intro a _
      have hqa0 : (0 : ℝ) < (q : ℝ) ^ a := by positivity
      have hYa : (0 : ℝ) < Y / (q : ℝ) ^ a := by positivity
      have hIHa := hIH (Y / (q : ℝ) ^ a) hYa
      have hsplit : (Y / (q : ℝ) ^ a) ^ (-(1/2) : ℝ)
          = Y ^ (-(1/2) : ℝ) / ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a := by
        rw [Real.div_rpow hY.le (by positivity), rpow_natPow_neg_half (by omega) a]
      rw [hsplit] at hIHa
      have hra0 : (0 : ℝ) < ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a := by positivity
      have hmul := mul_le_mul_of_nonneg_left hIHa
        (by positivity : (0 : ℝ) ≤ (1 / (q : ℝ)) ^ a)
      have h1 : (1 / (q : ℝ)) ^ a = (((q : ℝ) ^ (-(1/2) : ℝ)) ^ a) ^ 2 := by
        rw [← hrsq, ← pow_mul, ← pow_mul, Nat.mul_comm]
      have hkey : (1 / (q : ℝ)) ^ a
            * (Y ^ (-(1/2) : ℝ) / ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a
                * ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹)
          = Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a
              * ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
        rw [h1, sq]
        field_simp
        try ring
      linarith only [hmul, hkey.le, hkey.ge]
    have hsum := Finset.sum_le_sum hterm
    have hLHS : ∑ a ∈ Finset.range (m + 1),
          ((1 / (q : ℝ)) ^ a * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
            - Y ^ (-(1/2) : ℝ) * ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a
              * ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹)
        = (∑ a ∈ Finset.range (m + 1), (1 / (q : ℝ)) ^ a)
            * ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1))
          - Y ^ (-(1/2) : ℝ) * (∏ p ∈ S, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹)
              * ∑ a ∈ Finset.range (m + 1), ((q : ℝ) ^ (-(1/2) : ℝ)) ^ a := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hgeom1, hgeom2] at hLHS
    rw [smooth_sum_step hqp hqS Y hY m hm, Finset.prod_insert hqS, Finset.prod_insert hqS]
    linarith only [hsum, hLHS.le, hLHS.ge, hd4]

/-- `p^{−1/4} ≤ c` from `1 ≤ p·c⁴`. -/
private lemma rpow_neg_quarter_le {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    (h : 1 ≤ (p : ℝ) * c ^ 4) : (p : ℝ) ^ (-(1/4) : ℝ) ≤ c := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hc ?_
  rw [rpow_neg_quarter_pow hp, div_le_iff₀ hp0]
  linarith

/-- `c ≤ p^{−1/4}` from `p·c⁴ ≤ 1`. -/
private lemma le_rpow_neg_quarter {p : ℕ} (hp : 1 ≤ p) {c : ℝ} (_hc : 0 ≤ c)
    (h : (p : ℝ) * c ^ 4 ≤ 1) : c ≤ (p : ℝ) ^ (-(1/4) : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (Real.rpow_nonneg hp0.le _) ?_
  rw [rpow_neg_quarter_pow hp, le_div_iff₀ hp0]
  linarith

/-- The algebraic core of the per-prime comparison: `(1 − v²)⁻¹ ≤ c·(1 + v)` as soon as
`1 ≤ c·(1 + v − v² − v³)`, because `(1 + v)(1 − v²) = 1 + v − v² − v³`. -/
private lemma inv_one_sub_sq_le {v cc : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (h : 1 ≤ cc * (1 + v - v ^ 2 - v ^ 3)) : (1 - v ^ 2)⁻¹ ≤ cc * (1 + v) := by
  have hpos : (0 : ℝ) < 1 - v ^ 2 := by nlinarith only [hv0, hv1]
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  nlinarith only [h]

/-- The per-prime weight of the smooth-series comparison: `1.88, 1.38, 1.10` at `2, 3, 5`
and `1` at every prime `≥ 7`. Their product is `≤ 3`. -/
private noncomputable def smoothC (p : ℕ) : ℝ :=
  if p = 2 then 188/100 else if p = 3 then 138/100 else if p = 5 then 110/100 else 1

private lemma one_le_smoothC (p : ℕ) : 1 ≤ smoothC p := by
  unfold smoothC
  split_ifs <;> norm_num

private lemma smoothC_eq_one {p : ℕ} (hp : 7 ≤ p) : smoothC p = 1 := by
  unfold smoothC
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The per-prime comparison.** `(1 − p^{−1/2})⁻¹ ≤ c_p·(1 + p^{−1/4})` for every prime.
At `p ≥ 7` the constant is `1`, i.e. `p^{−1/4} + p^{−1/2} ≤ 1` (true from `p = 7`, where the
two sides are `0.9927` and `1`); at `2, 3, 5` the measured ratios are `1.855, 1.345, 1.084`
and the constants carry a margin. -/
private lemma inv_one_sub_le_smoothC {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ ≤ smoothC p * (1 + (p : ℝ) ^ (-(1/4) : ℝ)) := by
  have h2 := hp.two_le
  have hp1 : 1 ≤ p := by omega
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    linarith
  have hvsq : ((p : ℝ) ^ (-(1/4) : ℝ)) ^ 2 = (p : ℝ) ^ (-(1/2) : ℝ) := rpow_neg_quarter_sq hp1
  have hv0 : (0 : ℝ) < (p : ℝ) ^ (-(1/4) : ℝ) := Real.rpow_pos_of_pos hp0 _
  rw [← hvsq]
  by_cases e2 : p = 2
  · subst e2
    have hvhi : ((2 : ℕ) : ℝ) ^ (-(1/4) : ℝ) ≤ 841/1000 :=
      rpow_neg_quarter_le (by norm_num) (by norm_num) (by norm_num)
    have hvlo : (840 : ℝ)/1000 ≤ ((2 : ℕ) : ℝ) ^ (-(1/4) : ℝ) :=
      le_rpow_neg_quarter (by norm_num) (by norm_num) (by norm_num)
    have hsC : smoothC 2 = 188/100 := by unfold smoothC; norm_num
    rw [hsC]
    refine inv_one_sub_sq_le hv0 (by linarith) ?_
    nlinarith only [hvlo, hvhi]
  · by_cases e3 : p = 3
    · subst e3
      have hvhi : ((3 : ℕ) : ℝ) ^ (-(1/4) : ℝ) ≤ 760/1000 :=
        rpow_neg_quarter_le (by norm_num) (by norm_num) (by norm_num)
      have hvlo : (759 : ℝ)/1000 ≤ ((3 : ℕ) : ℝ) ^ (-(1/4) : ℝ) :=
        le_rpow_neg_quarter (by norm_num) (by norm_num) (by norm_num)
      have hsC : smoothC 3 = 138/100 := by unfold smoothC; norm_num
      rw [hsC]
      refine inv_one_sub_sq_le hv0 (by linarith) ?_
      nlinarith only [hvlo, hvhi]
    · by_cases e5 : p = 5
      · subst e5
        have hvhi : ((5 : ℕ) : ℝ) ^ (-(1/4) : ℝ) ≤ 669/1000 :=
          rpow_neg_quarter_le (by norm_num) (by norm_num) (by norm_num)
        have hvlo : (668 : ℝ)/1000 ≤ ((5 : ℕ) : ℝ) ^ (-(1/4) : ℝ) :=
          le_rpow_neg_quarter (by norm_num) (by norm_num) (by norm_num)
        have hsC : smoothC 5 = 110/100 := by unfold smoothC; norm_num
        rw [hsC]
        refine inv_one_sub_sq_le hv0 (by linarith) ?_
        nlinarith only [hvlo, hvhi]
      · have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
        have h6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
        have hp7 : 7 ≤ p := by omega
        have hp7R : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp7
        have hvhi : (p : ℝ) ^ (-(1/4) : ℝ) ≤ 616/1000 := by
          refine rpow_neg_quarter_le hp1 (by norm_num) ?_
          nlinarith only [hp7R]
        rw [smoothC_eq_one hp7]
        refine inv_one_sub_sq_le hv0 (by linarith) ?_
        nlinarith only [hv0, hvhi]

/-- `∏_{p ∈ S} c_p ≤ 3` for any finite set of primes: only `2, 3, 5` contribute, and
`1.88·1.38·1.10 = 2.854`. -/
private lemma prod_smoothC_le_three {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    ∏ p ∈ S, smoothC p ≤ 3 := by
  classical
  have hsplit : ∏ p ∈ S, smoothC p = ∏ p ∈ S.filter (fun p => p < 7), smoothC p := by
    refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
    intro x hx hx'
    have h7 : 7 ≤ x := by
      by_contra hcon
      exact hx' (Finset.mem_filter.mpr ⟨hx, by omega⟩)
    exact smoothC_eq_one h7
  rw [hsplit]
  have hsub : S.filter (fun p => p < 7) ⊆ ({2, 3, 5} : Finset ℕ) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hp := hS x hx.1
    have h2 := hp.two_le
    have h4 : x ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    have h6 : x ≠ 6 := by rintro rfl; exact absurd hp (by decide)
    have hx7 := hx.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hsd := Finset.prod_sdiff (f := smoothC) hsub
  have hsd1 : (1 : ℝ) ≤ ∏ x ∈ ({2, 3, 5} : Finset ℕ) \ S.filter (fun p => p < 7), smoothC x := by
    have h := Finset.prod_le_prod
      (s := ({2, 3, 5} : Finset ℕ) \ S.filter (fun p => p < 7))
      (f := fun _ : ℕ => (1 : ℝ)) (g := smoothC)
      (fun i _ => zero_le_one) (fun i _ => one_le_smoothC i)
    simpa using h
  have hT0 : (0 : ℝ) ≤ ∏ x ∈ S.filter (fun p => p < 7), smoothC x :=
    Finset.prod_nonneg fun i _ => le_trans zero_le_one (one_le_smoothC i)
  have hval : ∏ p ∈ ({2, 3, 5} : Finset ℕ), smoothC p = (188/100) * ((138/100) * (110/100)) := by
    rw [show ({2, 3, 5} : Finset ℕ) = insert 2 (insert 3 ({5} : Finset ℕ)) by rfl,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    unfold smoothC
    norm_num
  rw [hval] at hsd
  nlinarith only [hsd, hsd1, hT0]

/-- `∏_{p ∣ t}(1 + p^{−1/4}) ≤ σ_{−1/4}(t)` — the product expands over the SUBSETS of
`t.primeFactors`, i.e. over the squarefree divisors of `t`, and every other divisor
contributes a nonnegative term. -/
private lemma prod_one_add_le_sigmaQ (t : ℕ) (ht : 1 ≤ t) :
    ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ)) ≤ sigmaQ t := by
  classical
  have ht0 : t ≠ 0 := by omega
  have hexp : ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ))
      = ∑ T ∈ t.primeFactors.powerset, ∏ p ∈ T, (p : ℝ) ^ (-(1/4) : ℝ) :=
    Finset.prod_one_add _
  have hsqf : ∑ e ∈ t.divisors.filter Squarefree, (e : ℝ) ^ (-(1/4 : ℝ))
      = ∑ T ∈ t.primeFactors.powerset, ∏ p ∈ T, (p : ℝ) ^ (-(1/4) : ℝ) := by
    rw [Nat.sum_divisors_filter_squarefree ht0]
    have hbridge : (UniqueFactorizationMonoid.normalizedFactors t).toFinset = t.primeFactors := by
      rw [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
    rw [hbridge]
    refine Finset.sum_congr rfl fun T _ => ?_
    have hval : T.val.prod = ∏ p ∈ T, p := Finset.prod_val T
    rw [hval, Nat.cast_prod]
    exact (Real.finsetProd_rpow T (fun p : ℕ => (p : ℝ))
      (fun p _ => Nat.cast_nonneg p) (-(1/4 : ℝ))).symm
  rw [hexp, ← hsqf, sigmaQ]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  positivity

/-- `t/φ(t) = ∏_{p ∣ t} p/(p−1)` for `t ≥ 1`. -/
private lemma div_totient_eq_prod_ratio (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ) / Nat.totient t = ∏ p ∈ t.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hU := prod_one_sub_pos t
  have hone : (∏ p ∈ t.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
      * ∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℝ) ≠ 0 := by linarith
    have h2 : (p : ℝ) - 1 ≠ 0 := by intro hcon; linarith
    field_simp
  have hprodeq : ∏ p ∈ t.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))
      = 1 / ∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [eq_div_iff hU.ne']
    exact hone
  have hcast : (t : ℝ) / (Nat.totient t : ℝ) = 1 / ∏ p ∈ t.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hp := totient_div_eq_prod_one_sub t ht
    rw [div_eq_iff ht0.ne'] at hp
    rw [hp, div_eq_div_iff (mul_ne_zero hU.ne' ht0.ne') hU.ne']
    ring
  rw [hcast, hprodeq]

/-- `∏_{p ∣ t}(1 − p^{−1/2})⁻¹ ≤ 3·σ_{−1/4}(t)` — the per-prime `c_p` comparison against
`∏ c_p ≤ 2.854`. -/
private lemma prod_inv_one_sub_le_three_sigmaQ (t : ℕ) (ht : 1 ≤ t) :
    ∏ p ∈ t.primeFactors, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ ≤ 3 * sigmaQ t := by
  have hprime : ∀ p ∈ t.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h1 : ∏ p ∈ t.primeFactors, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹
      ≤ ∏ p ∈ t.primeFactors, (smoothC p * (1 + (p : ℝ) ^ (-(1/4) : ℝ))) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => inv_one_sub_le_smoothC (hprime p hp))
    obtain ⟨ha, hb⟩ := rpow_neg_half_lt_one (hprime p hp).two_le
    exact le_of_lt (inv_pos.mpr (by linarith))
  have h2 : ∏ p ∈ t.primeFactors, (smoothC p * (1 + (p : ℝ) ^ (-(1/4) : ℝ)))
      = (∏ p ∈ t.primeFactors, smoothC p)
          * ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ)) := Finset.prod_mul_distrib
  have h3 := prod_smoothC_le_three hprime
  have h4 := prod_one_add_le_sigmaQ t ht
  have h5 : (0 : ℝ) ≤ ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ (p : ℝ) by positivity) (-(1/4) : ℝ)
    linarith
  have h6 : (0 : ℝ) ≤ ∏ p ∈ t.primeFactors, smoothC p :=
    Finset.prod_nonneg fun p _ => le_trans zero_le_one (one_le_smoothC p)
  have h7 : (∏ p ∈ t.primeFactors, smoothC p)
      * ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ)) ≤ 3 * sigmaQ t := by
    have e1 : (∏ p ∈ t.primeFactors, smoothC p)
        * ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ))
        ≤ 3 * ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ)) :=
      mul_le_mul_of_nonneg_right h3 h5
    have e2 : (3 : ℝ) * ∏ p ∈ t.primeFactors, (1 + (p : ℝ) ^ (-(1/4) : ℝ))
        ≤ 3 * sigmaQ t := by linarith only [h4]
    linarith only [e1, e2]
  linarith only [h1, h2.le, h2.ge, h7]

/-- **S3 (the tail).** `t/φ(t) − Σ_{d ≤ X, d t-smooth} 1/d ≤ 3·σ_{−1/4}(t)/√X`.

The smooth series in the HARD direction, by the finite prime-step induction
`smooth_tail_le`: the tail is `≤ X^{−1/2}·∏_{p ∣ t}(1 − p^{−1/2})⁻¹`, and the per-prime
comparison `(1 − p^{−1/2})⁻¹ ≤ c_p(1 + p^{−1/4})` with `∏ c_p ≤ 2.854 ≤ 3` turns the Euler
product into `3·∏(1 + p^{−1/4}) ≤ 3·σ_{−1/4}(t)`.

Measured: the true tails `t/φ(t) − partial(10⁴) = 1.450e−3 / 5.820e−3 / 1.510e−2` at
`t = 6/30/210` against the bound `8.78e−2 / 1.47e−1 / 2.37e−1`.

The must-FAIL control (measured): with the exponent `1/2` → `1` at `t = 6`, the mutant's
ratio `LHS/(3σ/X)` GROWS — `0.855 / 1.18 / 1.49 / 1.81` at `X = 10² / 10³ / 10⁴ / 10⁵` (it
PASSES at `X = 10²`, so the kill is the growth): a fixed prime set's smooth tail decays like
`(log X)^{ω−1}/X`, not `X^{−1/2}`, and no constant closes the mutant. -/
theorem div_totient_sub_sum_smooth_inv_le (t X : ℕ) (ht : 1 ≤ t) (hX : 1 ≤ X) :
    (t : ℝ) / Nat.totient t
      - ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d.primeFactors ⊆ t.primeFactors), (1 : ℝ) / d
      ≤ 3 * sigmaQ t / (X : ℝ) ^ (1/2 : ℝ) := by
  classical
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hfl : ⌊(X : ℝ)⌋₊ = X := Nat.floor_natCast X
  have hprime : ∀ p ∈ t.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have htail := smooth_tail_le t.primeFactors hprime (X : ℝ) hX0
  rw [hfl] at htail
  rw [div_totient_eq_prod_ratio t ht]
  have hEuler := prod_inv_one_sub_le_three_sigmaQ t ht
  -- the rpow bookkeeping
  have hneg : (X : ℝ) ^ (-(1/2) : ℝ) = ((X : ℝ) ^ (1/2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hX0.le]
  have hXhalf : (0 : ℝ) < (X : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hEuler0 : (0 : ℝ) ≤ ∏ p ∈ t.primeFactors, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
    refine Finset.prod_nonneg fun p hp => ?_
    obtain ⟨ha, hb⟩ := rpow_neg_half_lt_one (hprime p hp).two_le
    exact le_of_lt (inv_pos.mpr (by linarith))
  have hfinal : (X : ℝ) ^ (-(1/2) : ℝ)
        * ∏ p ∈ t.primeFactors, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹
      ≤ 3 * sigmaQ t / (X : ℝ) ^ (1/2 : ℝ) := by
    rw [hneg, inv_mul_eq_div, div_le_div_iff₀ hXhalf hXhalf]
    nlinarith only [hEuler, hXhalf]
  linarith only [htail, hfinal]

/-! ### S4 — the coprime Möbius sum -/

/-- The A4 helper's standard consequence:
`(1 + log Q)·(log 2Q)^A ≤ 2((4A)^A + (4(A+1))^{A+1})·Q^{1/4}` for `Q ≥ 1`. -/
private lemma one_add_log_mul_log_rpow_le (A : ℝ) (hA : 0 < A) {Q : ℝ} (hQ : 1 ≤ Q) :
    (1 + Real.log Q) * Real.log (2 * Q) ^ A
      ≤ 2 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1/4 : ℝ) := by
  have hQpos : (0 : ℝ) < Q := by linarith
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hlq : Real.log Q ≤ Real.log (2 * Q) := Real.log_le_log hQpos (by linarith)
  have hq40 : (0 : ℝ) < Q ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hk1 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hk2 : (0 : ℝ) < (4 * (A + 1)) ^ (A + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hA4a := log_rpow_le_rpow_quarter A hA (show (1 : ℝ) ≤ 2 * Q by linarith)
  have hA4b := log_rpow_le_rpow_quarter (A + 1) (by linarith)
    (show (1 : ℝ) ≤ 2 * Q by linarith)
  have hsplit24 : (2 * Q) ^ (1/4 : ℝ) = (2 : ℝ) ^ (1/4 : ℝ) * Q ^ (1/4 : ℝ) :=
    Real.mul_rpow (by norm_num) hQpos.le
  have h2quarter : (2 : ℝ) ^ (1/4 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1/4 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hLsplit : Real.log (2 * Q) ^ (A + 1) = Real.log (2 * Q) ^ A * Real.log (2 * Q) := by
    rw [Real.rpow_add hlog2Q, Real.rpow_one]
  have e1 : Real.log (2 * Q) ^ A ≤ (4 * A) ^ A * (2 * Q ^ (1/4 : ℝ)) := by
    refine le_trans hA4a ?_
    rw [hsplit24]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2quarter hq40.le) hk1.le
  have e2 : Real.log (2 * Q) ^ (A + 1) ≤ (4 * (A + 1)) ^ (A + 1) * (2 * Q ^ (1/4 : ℝ)) := by
    refine le_trans hA4b ?_
    rw [hsplit24]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2quarter hq40.le) hk2.le
  have e3 : Real.log (2 * Q) ^ A * Real.log (2 * Q)
      ≤ (4 * (A + 1)) ^ (A + 1) * (2 * Q ^ (1/4 : ℝ)) := by
    rw [← hLsplit]; exact e2
  have e5a : Real.log Q * Real.log (2 * Q) ^ A ≤ Real.log (2 * Q) * Real.log (2 * Q) ^ A :=
    mul_le_mul_of_nonneg_right hlq hlog2QA.le
  linarith only [e1, e3, e5a]

/-- `t/φ(t) ≤ 3·σ_{−1/4}(t)`. -/
private lemma div_totient_le_three_sigmaQ (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ) / Nat.totient t ≤ 3 * sigmaQ t := by
  have hprime : ∀ p ∈ t.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [div_totient_eq_prod_ratio t ht]
  have h1 : ∏ p ∈ t.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))
      ≤ ∏ p ∈ t.primeFactors, (1 - (p : ℝ) ^ (-(1/2) : ℝ))⁻¹ := by
    refine Finset.prod_le_prod (fun p hp => ?_)
      (fun p hp => prime_ratio_le_inv_one_sub (hprime p hp).two_le)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    exact div_nonneg (by linarith) (by linarith)
  linarith only [h1, prod_inv_one_sub_le_three_sigmaQ t ht]

/-- H6b re-windowed on `1 ≤ d ≤ √Q`: `log(2Q/d) ≥ ½ log 2Q`, so the saving costs `2^A`. -/
private lemma abs_sum_moebius_div_near {A : ℝ} (hA : 0 < A) {Cf : ℝ} (hCf : 0 < Cf)
    (hf : ∀ Q : ℝ, 1 ≤ Q → |∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius n : ℝ) / n|
        ≤ Cf / Real.log (2 * Q) ^ A)
    {Q : ℝ} (hQ : 1 ≤ Q) {d : ℕ} (hd1 : 1 ≤ d) (hdQ : (d : ℝ) ≤ Q ^ (1/2 : ℝ)) :
    |∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / e|
      ≤ Cf * 2 ^ A / Real.log (2 * Q) ^ A := by
  have hQpos : (0 : ℝ) < Q := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hs0 : (0 : ℝ) < Q ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hspow : (Q ^ (1/2 : ℝ)) ^ 2 = Q := by
    rw [rpow_pow_nat hQpos.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hbig : Q ^ (1/2 : ℝ) ≤ Q / (d : ℝ) := by
    rw [le_div_iff₀ hd0]
    nlinarith only [hdQ, hspow, hs0, hd0]
  have hQd : (1 : ℝ) ≤ Q / (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ Q ^ (1/2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
    linarith
  have hfl : ⌊Q / (d : ℝ)⌋₊ = ⌊Q⌋₊ / d := Nat.floor_div_natCast Q d
  have hfb := hf (Q / (d : ℝ)) hQd
  rw [hfl] at hfb
  have hroot : (2 * Q) ^ (1/2 : ℝ) ≤ 2 * (Q / (d : ℝ)) := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
    have hh : ((2 * Q) ^ (1/2 : ℝ)) ^ 2 = 2 * Q := by
      rw [rpow_pow_nat (by positivity),
        show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    rw [hh]
    nlinarith only [hbig, hs0, hspow]
  have hlogr : Real.log ((2 * Q) ^ (1/2 : ℝ)) = (1/2 : ℝ) * Real.log (2 * Q) :=
    Real.log_rpow (by linarith) _
  have hlogm : Real.log (2 * Q) / 2 ≤ Real.log (2 * (Q / (d : ℝ))) := by
    have h := Real.log_le_log (by positivity) hroot
    rw [hlogr] at h
    linarith
  have hhalf : (0 : ℝ) < Real.log (2 * Q) / 2 := by linarith
  have hpow0 : (0 : ℝ) < (Real.log (2 * Q) / 2) ^ A := Real.rpow_pos_of_pos hhalf _
  have hpow : (Real.log (2 * Q) / 2) ^ A ≤ Real.log (2 * (Q / (d : ℝ))) ^ A :=
    Real.rpow_le_rpow hhalf.le hlogm hA.le
  have hdiv : (Real.log (2 * Q) / 2) ^ A = Real.log (2 * Q) ^ A / 2 ^ A :=
    Real.div_rpow hlog2Q.le (by norm_num : (0 : ℝ) ≤ 2) A
  have hs1' : Cf / Real.log (2 * (Q / (d : ℝ))) ^ A ≤ Cf / (Real.log (2 * Q) / 2) ^ A :=
    div_le_div_of_nonneg_left hCf.le hpow0 hpow
  have hs2 : Cf / (Real.log (2 * Q) / 2) ^ A = Cf * 2 ^ A / Real.log (2 * Q) ^ A := by
    rw [hdiv]
    field_simp
  linarith only [hfb, hs1', hs2.le, hs2.ge]

/-- The trivial bound on a coprime-filtered Möbius sum: `|Σ| ≤ 1 + log Q`. -/
private lemma abs_coprime_sum_moebius_div_triv (t : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t), (moebius n : ℝ) / n|
      ≤ 1 + Real.log Q := by
  classical
  have hQpos : (0 : ℝ) < Q := by linarith
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊Q⌋₊, |(moebius n : ℝ) / (n : ℝ)| ≤ ((n : ℝ))⁻¹ := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_div, abs_of_nonneg hn0.le, inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hn0).mpr hmu
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => abs_nonneg _)) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  refine le_trans (sum_inv_le_one_add_log _) ?_
  linarith [log_natCast_le_log hQ hNQ]

set_option maxHeartbeats 1600000 in
-- S4 assembles the convolution, the near/far split of the smooth divisor and the two
-- regimes in a single declaration; it exceeds the default elaboration budget.
/-- **S4 (the coprime H6b; feeds H6f).**
`|Σ_{n ≤ Q, (n,t)=1} μ(n)/n| ≤ C·σ_{−1/4}(t)/(log 2Q)^A`.

S1 at `G = 1/m` writes the coprime sum as `Σ_{d ≤ Q smooth}(1/d)·f(Q/d)`. On `d ≤ √Q`,
`log(2Q/d) ≥ ½ log 2Q`, so H6b gives `|f| ≤ C_A 2^A(log 2Q)^{−A}` against S2's
`Σ 1/d ≤ t/φ(t) ≤ 3σ`; beyond `D = ⌊√Q⌋₊` the trivial `|f| ≤ 1 + log Q` runs against S3's
tail `3σ/√D`, closed by the A4 helper at `A` and `A + 1` (`√D ≥ Q^{1/4}/2` above `Q = 4`).
Below `Q = 4` the trivial `|Σ| ≤ 1 + log Q` is absorbed into `C`.

The constant is NON-EFFECTIVE (H6b carries `mmuRate_holds`'s window).

The must-FAIL control (measured): with the `σ(t)` weight DROPPED, at
`t = primorial(z)` and `Q = z` (only `n = 1` survives the coprimality filter, so `|Σ| = 1`),
`|Σ|·(log 2Q)² = 16.8 / 28.1 / 40.9 / 57.8 / 75.7` at `z = 30 / 100 / 300 / 1000 / 3000` —
UNBOUNDED, while the frozen RHS carries `σ(t) = 9.5e1 / 9.8e3 / 7.1e7 / 2.1e16 / 2.7e32`. -/
theorem abs_coprime_sum_moebius_div_le (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t → ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t), (moebius n : ℝ) / n|
      ≤ C * sigmaQ t / Real.log (2 * Q) ^ A := by
  classical
  obtain ⟨Cf, hCf, hf⟩ := abs_sum_moebius_div_le_inv_log_pow A hA
  have h2A : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hk2 : (0 : ℝ) < (4 * (A + 1)) ^ (A + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlog8 : (0 : ℝ) < Real.log 8 ^ A := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  refine ⟨(1 + Real.log 4) * Real.log 8 ^ A + 3 * Cf * 2 ^ A
    + 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)), by positivity, ?_⟩
  intro t ht Q hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hsig1 : (1 : ℝ) ≤ sigmaQ t := one_le_sigmaQ t ht
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
  have hCpos : (0 : ℝ) < (1 + Real.log 4) * Real.log 8 ^ A + 3 * Cf * 2 ^ A
      + 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) := by positivity
  rcases lt_or_ge Q 4 with hsmall | hbig
  -- ═══ the trivial regime `Q < 4` ═══
  · have htriv := abs_coprime_sum_moebius_div_triv t hQ
    have hmono : Real.log (2 * Q) ^ A ≤ Real.log 8 ^ A :=
      Real.rpow_le_rpow hlog2Q.le (Real.log_le_log (by linarith) (by linarith)) hA.le
    have hlq4 : Real.log Q ≤ Real.log 4 := Real.log_le_log hQpos (by linarith)
    refine le_trans htriv ?_
    rw [le_div_iff₀ hlog2QA]
    have h1 : (1 + Real.log Q) * Real.log (2 * Q) ^ A
        ≤ (1 + Real.log 4) * Real.log 8 ^ A := by
      have e1 : (1 + Real.log Q) * Real.log (2 * Q) ^ A
          ≤ (1 + Real.log 4) * Real.log (2 * Q) ^ A :=
        mul_le_mul_of_nonneg_right (by linarith) hlog2QA.le
      have e2 : (1 + Real.log 4) * Real.log (2 * Q) ^ A ≤ (1 + Real.log 4) * Real.log 8 ^ A :=
        mul_le_mul_of_nonneg_left hmono (by linarith)
      linarith only [e1, e2]
    have hC1 : (1 + Real.log 4) * Real.log 8 ^ A
        ≤ (1 + Real.log 4) * Real.log 8 ^ A + 3 * Cf * 2 ^ A
          + 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) := by
      nlinarith only [hCf, h2A, hk1, hk2]
    have hCsig : (1 + Real.log 4) * Real.log 8 ^ A + 3 * Cf * 2 ^ A
          + 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1))
        ≤ ((1 + Real.log 4) * Real.log 8 ^ A + 3 * Cf * 2 ^ A
          + 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1))) * sigmaQ t := by
      nlinarith only [hCpos, hsig1]
    linarith only [h1, hC1, hCsig]
  -- ═══ the main regime `Q ≥ 4` ═══
  · have hs0 : (0 : ℝ) < Q ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hspow : (Q ^ (1/2 : ℝ)) ^ 2 = Q := by
      rw [rpow_pow_nat hQpos.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have hQ12 : Q ^ (1/2 : ℝ) ≤ Q := by
      have h := Real.rpow_le_rpow_of_exponent_le hQ (show (1/2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hs2 : (2 : ℝ) ≤ Q ^ (1/2 : ℝ) := by
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hs0.le ?_
      rw [hspow]
      nlinarith only [hbig]
    set D : ℕ := ⌊Q ^ (1/2 : ℝ)⌋₊ with hDdef
    have hDle : ((D : ℕ) : ℝ) ≤ Q ^ (1/2 : ℝ) := Nat.floor_le hs0.le
    have hDgt : Q ^ (1/2 : ℝ) < ((D : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hDhalf : Q ^ (1/2 : ℝ) / 2 ≤ ((D : ℕ) : ℝ) := by linarith
    have hD1 : 1 ≤ D := by
      have h : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by linarith
      exact_mod_cast h
    have hDN : D ≤ ⌊Q⌋₊ := by rw [hDdef]; exact Nat.floor_mono hQ12
    have hS1 := sum_coprime_moebius_eq_sum_smooth t ⌊Q⌋₊ ht (fun m => (1 : ℝ) / (m : ℝ))
    have hL : ∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t), (moebius n : ℝ) / n
        = ∑ m ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun m => Nat.Coprime m t),
            (moebius m : ℝ) * ((1 : ℝ) / (m : ℝ)) :=
      Finset.sum_congr rfl fun m _ => by ring
    have hR : ∀ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors),
        (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) * ((1 : ℝ) / ((d * e : ℕ) : ℝ)))
          = (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ) := by
      intro d _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      push_cast
      ring
    rw [hL, hS1, Finset.sum_congr rfl hR]
    have hfe : ((Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D)
        = (Finset.Icc 1 D).filter (fun d => d.primeFactors ⊆ t.primeFactors) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, hsm⟩, hxD⟩
        exact ⟨⟨h1, hxD⟩, hsm⟩
      · rintro ⟨⟨h1, hxD⟩, hsm⟩
        exact ⟨⟨⟨h1, le_trans hxD hDN⟩, hsm⟩, hxD⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors))
      (fun d => d ≤ D)
      (fun d => (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ))
    have hCf0 : (0 : ℝ) ≤ Cf * 2 ^ A / Real.log (2 * Q) ^ A :=
      div_nonneg (mul_nonneg hCf.le h2A.le) hlog2QA.le
    -- the near range
    have hnear : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
          (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ)|
        ≤ 3 * sigmaQ t * (Cf * 2 ^ A / Real.log (2 * Q) ^ A) := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
          |(1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ)|
            ≤ (1 : ℝ) / (d : ℝ) * (Cf * 2 ^ A / Real.log (2 * Q) ^ A) := by
        intro d hd
        rw [hfe, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, hdD⟩, _⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hdR : (d : ℝ) ≤ Q ^ (1/2 : ℝ) := le_trans (by exact_mod_cast hdD) hDle
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (d : ℝ))]
        exact mul_le_mul_of_nonneg_left (abs_sum_moebius_div_near hA hCf hf hQ hd1 hdR)
          (by positivity)
      have hsum1 : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
            (1 : ℝ) / (d : ℝ) ≤ 3 * sigmaQ t := by
        have h1 : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
              (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
              (1 : ℝ) / (d : ℝ)
            ≤ ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors),
                (1 : ℝ) / (d : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => by positivity)
        have h2 := sum_smooth_inv_le t ⌊Q⌋₊ ht
        have h3 := div_totient_le_three_sigmaQ t ht
        linarith only [h1, h2, h3]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hsum1 hCf0
    -- the far range
    have hfar : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
          (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ)|
        ≤ (1 + Real.log Q) * (3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ)) := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
          |(1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ)|
            ≤ (1 : ℝ) / (d : ℝ) * (1 + Real.log Q) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨⟨hd1, hdN⟩, _⟩, _⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have htr := abs_sum_moebius_div_le_one_add_log (⌊Q⌋₊ / d)
        have hle : ((⌊Q⌋₊ / d : ℕ) : ℝ) ≤ Q := by
          have h : (⌊Q⌋₊ / d : ℕ) ≤ ⌊Q⌋₊ := Nat.div_le_self _ _
          have h2 : ((⌊Q⌋₊ / d : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
          linarith
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (d : ℝ))]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith only [htr, log_natCast_le_log hQ hle]
      have hsum1 : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
            (1 : ℝ) / (d : ℝ) ≤ 3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ) := by
        have hsp := Finset.sum_filter_add_sum_filter_not
          ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors))
          (fun d => d ≤ D) (fun d => (1 : ℝ) / (d : ℝ))
        have h2 := sum_smooth_inv_le t ⌊Q⌋₊ ht
        have h3 := div_totient_sub_sum_smooth_inv_le t D ht hD1
        rw [hfe] at hsp
        linarith only [hsp, h2, h3]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      have h := mul_le_mul_of_nonneg_right hsum1 (show (0 : ℝ) ≤ 1 + Real.log Q by linarith)
      linarith only [h]
    -- the far range against the A4 helper
    have hD0 : (0 : ℝ) < (D : ℝ) := by
      have h : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast hD1
      linarith
    have hq40 : (0 : ℝ) < Q ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hDpow0 : (0 : ℝ) < (D : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hD0 _
    have hDhalfpow : Q ^ (1/4 : ℝ) / 2 ≤ (D : ℝ) ^ (1/2 : ℝ) := by
      have e1 : (Q ^ (1/2 : ℝ) / 2) ^ (1/2 : ℝ) ≤ (D : ℝ) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hDhalf (by norm_num)
      have e2 : (Q ^ (1/2 : ℝ) / 2) ^ (1/2 : ℝ) = Q ^ (1/4 : ℝ) / (2 : ℝ) ^ (1/2 : ℝ) := by
        rw [Real.div_rpow hs0.le (by norm_num), ← Real.rpow_mul hQpos.le]
        norm_num
      have e3 : (2 : ℝ) ^ (1/2 : ℝ) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
          (show (1/2 : ℝ) ≤ 1 by norm_num)
        rwa [Real.rpow_one] at h
      have e4 : (0 : ℝ) < (2 : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have e5 : Q ^ (1/4 : ℝ) / 2 ≤ Q ^ (1/4 : ℝ) / (2 : ℝ) ^ (1/2 : ℝ) :=
        div_le_div_of_nonneg_left hq40.le e4 e3
      linarith only [e1, e2.le, e2.ge, e5]
    have hA4 := one_add_log_mul_log_rpow_le A hA hQ
    have hsig0 : (0 : ℝ) < sigmaQ t := by linarith
    have hfarC : (1 + Real.log Q) * (3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ))
        ≤ 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * sigmaQ t
            / Real.log (2 * Q) ^ A := by
      have hEq : (1 + Real.log Q) * (3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ))
          = (3 * sigmaQ t * (1 + Real.log Q)) / (D : ℝ) ^ (1/2 : ℝ) := by ring
      rw [hEq, div_le_div_iff₀ hDpow0 hlog2QA]
      have p1 : 3 * sigmaQ t * ((1 + Real.log Q) * Real.log (2 * Q) ^ A)
          ≤ 3 * sigmaQ t * (2 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hA4 (by linarith)
      have p2 : 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * sigmaQ t * (Q ^ (1/4 : ℝ) / 2)
          ≤ 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * sigmaQ t * (D : ℝ) ^ (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left hDhalfpow
          (mul_nonneg (by linarith only [hk1, hk2]) hsig0.le)
      linarith only [p1, p2]
    have hextra : (0 : ℝ) ≤ (1 + Real.log 4) * Real.log 8 ^ A * sigmaQ t
        / Real.log (2 * Q) ^ A :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith only [hlog4]) hlog8.le)
        (by linarith only [hsig1])) hlog2QA.le
    have habs := abs_add_le
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
        (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
        (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ))
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
        (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
        (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ) / (e : ℝ))
    rw [hsplit] at habs
    have hringid : ((1 + Real.log 4) * Real.log 8 ^ A + 3 * Cf * 2 ^ A
          + 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1))) * sigmaQ t / Real.log (2 * Q) ^ A
        = (1 + Real.log 4) * Real.log 8 ^ A * sigmaQ t / Real.log (2 * Q) ^ A
          + 3 * sigmaQ t * (Cf * 2 ^ A / Real.log (2 * Q) ^ A)
          + 12 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * sigmaQ t
              / Real.log (2 * Q) ^ A := by
      ring
    rw [hringid]
    linarith only [habs, hnear, hfar, hfarC, hextra]

/-! ### H6d — the coprime log-weighted sum -/

/-- The smooth index set below `D` is the smooth index set of `[1, D]`. -/
private lemma smooth_filter_le (t N D : ℕ) (hDN : D ≤ N) :
    ((Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ t.primeFactors)).filter
        (fun d => d ≤ D)
      = (Finset.Icc 1 D).filter (fun d => d.primeFactors ⊆ t.primeFactors) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, hsm⟩, hxD⟩
    exact ⟨⟨h1, hxD⟩, hsm⟩
  · rintro ⟨⟨h1, hxD⟩, hsm⟩
    exact ⟨⟨⟨h1, le_trans hxD hDN⟩, hsm⟩, hxD⟩

/-- `Σ_{d ≤ N smooth, d ≤ D} 1/d ≤ 3σ`. -/
private lemma sum_smooth_near_le (t N D : ℕ) (ht : 1 ≤ t) :
    ∑ d ∈ ((Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ t.primeFactors)).filter
        (fun d => d ≤ D), (1 : ℝ) / d ≤ 3 * sigmaQ t := by
  classical
  have h1 : ∑ d ∈ ((Finset.Icc 1 N).filter
        (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D), (1 : ℝ) / d
      ≤ ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ t.primeFactors),
          (1 : ℝ) / d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => by positivity)
  have h2 := sum_smooth_inv_le t N ht
  have h3 := div_totient_le_three_sigmaQ t ht
  linarith only [h1, h2, h3]

/-- `Σ_{d ≤ N smooth, d > D} 1/d ≤ 3σ/√D` — S2 above, S3 below. -/
private lemma sum_smooth_far_le (t N D : ℕ) (ht : 1 ≤ t) (hD1 : 1 ≤ D) (hDN : D ≤ N) :
    ∑ d ∈ ((Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ t.primeFactors)).filter
        (fun d => ¬ d ≤ D), (1 : ℝ) / d ≤ 3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ) := by
  classical
  have hsp := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ t.primeFactors))
    (fun d => d ≤ D) (fun d => (1 : ℝ) / (d : ℝ))
  have h2 := sum_smooth_inv_le t N ht
  have h3 := div_totient_sub_sum_smooth_inv_le t D ht hD1
  rw [smooth_filter_le t N D hDN] at hsp
  linarith only [hsp, h2, h3]

/-- On `1 ≤ d ≤ √Q`: `Q/d ≥ 1` and `log(2Q/d) ≥ ½ log 2Q`. -/
private lemma le_sqrt_div_log {Q : ℝ} (hQ : 1 ≤ Q) {d : ℕ} (hd1 : 1 ≤ d)
    (hdQ : (d : ℝ) ≤ Q ^ ((1 : ℝ) / 2)) :
    (1 : ℝ) ≤ Q / (d : ℝ) ∧ Real.log (2 * Q) / 2 ≤ Real.log (2 * (Q / (d : ℝ))) := by
  have hQpos : (0 : ℝ) < Q := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hs0 : (0 : ℝ) < Q ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hspow : (Q ^ (1/2 : ℝ)) ^ 2 = Q := by
    rw [rpow_pow_nat hQpos.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hbig : Q ^ (1/2 : ℝ) ≤ Q / (d : ℝ) := by
    rw [le_div_iff₀ hd0]
    nlinarith only [hdQ, hspow, hs0, hd0]
  have hQd : (1 : ℝ) ≤ Q / (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ Q ^ (1/2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
    linarith
  refine ⟨hQd, ?_⟩
  have hroot : (2 * Q) ^ (1/2 : ℝ) ≤ 2 * (Q / (d : ℝ)) := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
    have hh : ((2 * Q) ^ (1/2 : ℝ)) ^ 2 = 2 * Q := by
      rw [rpow_pow_nat (by positivity),
        show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    rw [hh]
    nlinarith only [hbig, hs0, hspow]
  have hlogr : Real.log ((2 * Q) ^ (1/2 : ℝ)) = (1/2 : ℝ) * Real.log (2 * Q) :=
    Real.log_rpow (by linarith) _
  have h := Real.log_le_log (by positivity) hroot
  rw [hlogr] at h
  linarith

/-- The near-range saving costs `2^A`: `C/(log 2Q/d)^A ≤ C·2^A/(log 2Q)^A` on `d ≤ √Q`. -/
private lemma div_log_pow_near {A : ℝ} (hA : 0 < A) {C : ℝ} (hC : 0 < C)
    {Q : ℝ} (hQ : 1 ≤ Q) {d : ℕ} (hd1 : 1 ≤ d) (hdQ : (d : ℝ) ≤ Q ^ ((1 : ℝ) / 2)) :
    C / Real.log (2 * (Q / (d : ℝ))) ^ A ≤ C * 2 ^ A / Real.log (2 * Q) ^ A := by
  have hQpos : (0 : ℝ) < Q := by linarith
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  obtain ⟨_, hlogm⟩ := le_sqrt_div_log hQ hd1 hdQ
  have hhalf : (0 : ℝ) < Real.log (2 * Q) / 2 := by linarith
  have hpow0 : (0 : ℝ) < (Real.log (2 * Q) / 2) ^ A := Real.rpow_pos_of_pos hhalf _
  have hpow : (Real.log (2 * Q) / 2) ^ A ≤ Real.log (2 * (Q / (d : ℝ))) ^ A :=
    Real.rpow_le_rpow hhalf.le hlogm hA.le
  have hdiv : (Real.log (2 * Q) / 2) ^ A = Real.log (2 * Q) ^ A / 2 ^ A :=
    Real.div_rpow hlog2Q.le (by norm_num : (0 : ℝ) ≤ 2) A
  have hs1' : C / Real.log (2 * (Q / (d : ℝ))) ^ A ≤ C / (Real.log (2 * Q) / 2) ^ A :=
    div_le_div_of_nonneg_left hC.le hpow0 hpow
  have hs2 : C / (Real.log (2 * Q) / 2) ^ A = C * 2 ^ A / Real.log (2 * Q) ^ A := by
    rw [hdiv]
    field_simp
  linarith only [hs1', hs2.le, hs2.ge]

/-- The A4 helper squared:
`(1 + log Q)²·(log 2Q)^A ≤ 2((4A)^A + 2(4(A+1))^{A+1} + (4(A+2))^{A+2})·Q^{1/4}`. -/
private lemma one_add_log_sq_mul_log_rpow_le (A : ℝ) (hA : 0 < A) {Q : ℝ} (hQ : 1 ≤ Q) :
    (1 + Real.log Q) ^ 2 * Real.log (2 * Q) ^ A
      ≤ 2 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
          * Q ^ (1/4 : ℝ) := by
  have hQpos : (0 : ℝ) < Q := by linarith
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hlq : Real.log Q ≤ Real.log (2 * Q) := Real.log_le_log hQpos (by linarith)
  have hq40 : (0 : ℝ) < Q ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hk1 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hk2 : (0 : ℝ) < (4 * (A + 1)) ^ (A + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hk3 : (0 : ℝ) < (4 * (A + 2)) ^ (A + 2) := Real.rpow_pos_of_pos (by linarith) _
  have hsplit24 : (2 * Q) ^ (1/4 : ℝ) = (2 : ℝ) ^ (1/4 : ℝ) * Q ^ (1/4 : ℝ) :=
    Real.mul_rpow (by norm_num) hQpos.le
  have h2quarter : (2 : ℝ) ^ (1/4 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1/4 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have step : ∀ B : ℝ, 0 < B → Real.log (2 * Q) ^ B ≤ (4 * B) ^ B * (2 * Q ^ (1/4 : ℝ)) := by
    intro B hB
    refine le_trans (log_rpow_le_rpow_quarter B hB (show (1 : ℝ) ≤ 2 * Q by linarith)) ?_
    rw [hsplit24]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2quarter hq40.le)
      (Real.rpow_pos_of_pos (by linarith) B).le
  have hL2 : Real.log (2 * Q) ^ ((2 : ℝ)) = Real.log (2 * Q) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log (2 * Q)) 2]
    norm_num
  have hA1 : Real.log (2 * Q) ^ (A + 1) = Real.log (2 * Q) ^ A * Real.log (2 * Q) := by
    rw [Real.rpow_add hlog2Q, Real.rpow_one]
  have hA2 : Real.log (2 * Q) ^ (A + 2)
      = Real.log (2 * Q) ^ A * Real.log (2 * Q) ^ (2 : ℕ) := by
    rw [Real.rpow_add hlog2Q, hL2]
  have e1 := step A hA
  have e2 := step (A + 1) (by linarith)
  have e3 := step (A + 2) (by linarith)
  rw [hA1] at e2
  rw [hA2] at e3
  have q1 : Real.log Q * Real.log (2 * Q) ^ A
      ≤ Real.log (2 * Q) * Real.log (2 * Q) ^ A :=
    mul_le_mul_of_nonneg_right hlq hlog2QA.le
  have q2 : Real.log Q ^ 2 * Real.log (2 * Q) ^ A
      ≤ Real.log (2 * Q) ^ 2 * Real.log (2 * Q) ^ A := by
    refine mul_le_mul_of_nonneg_right ?_ hlog2QA.le
    nlinarith only [hlq, hlogQ0]
  have hsq : (1 + Real.log Q) ^ 2 * Real.log (2 * Q) ^ A
      ≤ Real.log (2 * Q) ^ A + 2 * (Real.log (2 * Q) ^ A * Real.log (2 * Q))
        + Real.log (2 * Q) ^ A * Real.log (2 * Q) ^ (2 : ℕ) := by
    linarith only [q1, q2]
  linarith only [hsq, e1, e2, e3]

/-- `|x + y + z| ≤ |x| + |y| + |z|`. -/
private lemma abs_add_add_le (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| := by
  refine le_trans (abs_add_le _ _) ?_
  have h := abs_add_le x y
  linarith

/-- The trivial bound `Σ_{e ≤ y}|(μ(e)/e)log(y/e)| ≤ (1 + log y)²`. -/
private lemma sum_abs_moebius_div_log_le {y : ℝ} (hy : 1 ≤ y) :
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |(moebius e : ℝ) / e * Real.log (y / e)|
      ≤ (1 + Real.log y) ^ 2 := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hNy : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy0.le
  have hterm : ∀ e ∈ Finset.Icc 1 ⌊y⌋₊,
      |(moebius e : ℝ) / (e : ℝ) * Real.log (y / (e : ℝ))| ≤ ((e : ℝ))⁻¹ * Real.log y := by
    intro e he
    obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp he
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    have he1R : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
    have heY : (e : ℝ) ≤ y := le_trans (by exact_mod_cast heN) hNy
    have hye : (1 : ℝ) ≤ y / (e : ℝ) := (one_le_div he0).mpr heY
    have hlog0 : (0 : ℝ) ≤ Real.log (y / (e : ℝ)) := Real.log_nonneg hye
    have hlogle : Real.log (y / (e : ℝ)) ≤ Real.log y := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ he0]
      nlinarith only [he1R, hy0]
    have hmu : |((moebius e : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_mul, abs_div, abs_of_nonneg he0.le, abs_of_nonneg hlog0]
    have h1 : |((moebius e : ℤ) : ℝ)| / (e : ℝ) ≤ ((e : ℝ))⁻¹ := by
      rw [inv_eq_one_div]
      exact (div_le_div_iff_of_pos_right he0).mpr hmu
    exact mul_le_mul h1 hlogle hlog0 (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have h2 := sum_inv_le_one_add_log ⌊y⌋₊
  have h3 : Real.log ((⌊y⌋₊ : ℕ) : ℝ) ≤ Real.log y := log_natCast_le_log hy hNy
  nlinarith only [h2, h3, hlogy]

/-- The trivial bound `|Σ_{e ≤ y}(μ(e)/e)log(y/e)| ≤ (1 + log y)²`. -/
private lemma abs_sum_moebius_div_log_le {y : ℝ} (hy : 1 ≤ y) :
    |∑ e ∈ Finset.Icc 1 ⌊y⌋₊, (moebius e : ℝ) / e * Real.log (y / e)|
      ≤ (1 + Real.log y) ^ 2 :=
  le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_abs_moebius_div_log_le hy)

set_option maxHeartbeats 1600000 in
-- H6d assembles the convolution, the main term, the near/far split and the two regimes in a
-- single declaration; it exceeds the default elaboration budget.
/-- **H6d (the H freeze's row, verbatim).**
`|Σ_{n ≤ Q, (n,t)=1}(μ(n)/n)log(Q/n) − t/φ(t)| ≤ C·σ_{−1/4}(t)/(log 2Q)^A`.

S1 at `G(m) = (1/m)log(Q/m)` writes the coprime sum as `Σ_{d ≤ Q smooth}(1/d)·T(Q/d)`
(`log(Q/(de)) = log((Q/d)/e)`, `⌊Q⌋₊/d = ⌊Q/d⌋₊`). C3 supplies `T(Q/d) = 1 + O` on
`d ≤ D = ⌊√Q⌋₊` at the cost `2^A`; the main term `Σ_{d ≤ Q smooth} 1/d` is `t/φ(t)` up to
S3's tail `3σ/√D`; and beyond `D` the trivial `|T(y)| ≤ (1 + log y)²` runs against the same
tail, closed by the A4 helper at `A`, `A + 1` and `A + 2`. Below `Q = 4` the trivial bound
is absorbed into `C`.

The constant is NON-EFFECTIVE (C3 carries `mmuRate_holds`'s window through C2 and H6b).

Sanity (measured) at `(t, Q) = (2, 100)`: `Σ_{n ≤ 100 odd}(μ(n)/n)log(100/n) = 1.9721`
against `t/φ(t) = 2`.

The must-FAIL control (measured): with the main term `t/φ(t)` → `φ(t)/t` at `t = 2`,
`|Σ − ½|·(log 2Q)²/σ(2) = 22.45 / 46.99 / 79.90 / 121.40 / 171.52` at `Q = 10² … 10⁶`
against `0.4254 / 0.0839 / 0.0147 / 0.0036 / 0.0012` frozen — UNBOUNDED. -/
theorem coprime_sum_moebius_div_log_eq (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, Squarefree t →
    ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t), (moebius n : ℝ) / n
        * Real.log (Q / n) - (t : ℝ) / Nat.totient t| ≤ C * sigmaQ t / Real.log (2 * Q) ^ A := by
  classical
  obtain ⟨CT, hCT, hT⟩ := abs_sum_moebius_div_mul_log_div_sub_one_le A hA
  have h2A : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hk2 : (0 : ℝ) < (4 * (A + 1)) ^ (A + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hk3 : (0 : ℝ) < (4 * (A + 2)) ^ (A + 2) := Real.rpow_pos_of_pos (by linarith) _
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlog8 : (0 : ℝ) < Real.log 8 ^ A := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  refine ⟨((1 + Real.log 4) ^ 2 + 3) * Real.log 8 ^ A + 3 * CT * 2 ^ A
    + 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
    + 12 * (4 * A) ^ A, by positivity, ?_⟩
  intro t hts Q hQ
  have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr hts.ne_zero
  have hQpos : (0 : ℝ) < Q := by linarith
  have hsig1 : (1 : ℝ) ≤ sigmaQ t := one_le_sigmaQ t ht
  have hsig0 : (0 : ℝ) < sigmaQ t := by linarith
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
  have hCpos : (0 : ℝ) < ((1 + Real.log 4) ^ 2 + 3) * Real.log 8 ^ A + 3 * CT * 2 ^ A
      + 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
      + 12 * (4 * A) ^ A := by positivity
  rcases lt_or_ge Q 4 with hsmall | hbig
  -- ═══ the trivial regime `Q < 4` ═══
  · have htriv : |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) / n * Real.log (Q / n)| ≤ (1 + Real.log Q) ^ 2 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => abs_nonneg _)) ?_
      exact sum_abs_moebius_div_log_le hQ
    have hmain := div_totient_le_three_sigmaQ t ht
    have hmain0 : (0 : ℝ) ≤ (t : ℝ) / Nat.totient t := by positivity
    have hmono : Real.log (2 * Q) ^ A ≤ Real.log 8 ^ A :=
      Real.rpow_le_rpow hlog2Q.le (Real.log_le_log (by linarith) (by linarith)) hA.le
    have hlq4 : Real.log Q ≤ Real.log 4 := Real.log_le_log hQpos (by linarith)
    have habs := abs_sub_le_add (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
      (fun n => Nat.Coprime n t), (moebius n : ℝ) / n * Real.log (Q / n))
      ((t : ℝ) / Nat.totient t)
    rw [abs_of_nonneg hmain0] at habs
    refine le_trans habs ?_
    rw [le_div_iff₀ hlog2QA]
    have hK0 : (0 : ℝ) ≤ (1 + Real.log 4) ^ 2 + 3 := by positivity
    have p0 : (1 + Real.log Q) ^ 2 ≤ (1 + Real.log 4) ^ 2 := by
      nlinarith only [hlq4, hlogQ0, hlog4]
    have p1 : (1 + Real.log Q) ^ 2 + (t : ℝ) / Nat.totient t
        ≤ ((1 + Real.log 4) ^ 2 + 3) * sigmaQ t := by
      nlinarith only [p0, hmain, hsig1, hlog4, hlogQ0]
    have p2 : ((1 + Real.log 4) ^ 2 + 3) * sigmaQ t * Real.log (2 * Q) ^ A
        ≤ ((1 + Real.log 4) ^ 2 + 3) * sigmaQ t * Real.log 8 ^ A :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg hK0 hsig0.le)
    have p3 : ((1 + Real.log Q) ^ 2 + (t : ℝ) / Nat.totient t) * Real.log (2 * Q) ^ A
        ≤ ((1 + Real.log 4) ^ 2 + 3) * sigmaQ t * Real.log (2 * Q) ^ A :=
      mul_le_mul_of_nonneg_right p1 hlog2QA.le
    have p5 : (|∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          (moebius n : ℝ) / n * Real.log (Q / n)| + (t : ℝ) / Nat.totient t)
          * Real.log (2 * Q) ^ A
        ≤ ((1 + Real.log Q) ^ 2 + (t : ℝ) / Nat.totient t) * Real.log (2 * Q) ^ A :=
      mul_le_mul_of_nonneg_right (by linarith only [htriv]) hlog2QA.le
    have p4 : ((1 + Real.log 4) ^ 2 + 3) * Real.log 8 ^ A * sigmaQ t
        ≤ (((1 + Real.log 4) ^ 2 + 3) * Real.log 8 ^ A + 3 * CT * 2 ^ A
          + 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
          + 12 * (4 * A) ^ A) * sigmaQ t := by
      have hrest : (0 : ℝ) ≤ 3 * CT * 2 ^ A
          + 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
          + 12 * (4 * A) ^ A := by positivity
      nlinarith only [hrest, hsig0]
    linarith only [p2, p3, p4, p5]
  -- ═══ the main regime `Q ≥ 4` ═══
  · have hs0 : (0 : ℝ) < Q ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hspow : (Q ^ (1/2 : ℝ)) ^ 2 = Q := by
      rw [rpow_pow_nat hQpos.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have hQ12 : Q ^ (1/2 : ℝ) ≤ Q := by
      have h := Real.rpow_le_rpow_of_exponent_le hQ (show (1/2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hs2 : (2 : ℝ) ≤ Q ^ (1/2 : ℝ) := by
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hs0.le ?_
      rw [hspow]
      nlinarith only [hbig]
    set D : ℕ := ⌊Q ^ (1/2 : ℝ)⌋₊ with hDdef
    have hDle : ((D : ℕ) : ℝ) ≤ Q ^ (1/2 : ℝ) := Nat.floor_le hs0.le
    have hDgt : Q ^ (1/2 : ℝ) < ((D : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hDhalf : Q ^ (1/2 : ℝ) / 2 ≤ ((D : ℕ) : ℝ) := by linarith
    have hD1 : 1 ≤ D := by
      have h : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by linarith
      exact_mod_cast h
    have hDN : D ≤ ⌊Q⌋₊ := by rw [hDdef]; exact Nat.floor_mono hQ12
    have hD0 : (0 : ℝ) < (D : ℝ) := by
      have h : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast hD1
      linarith
    have hq40 : (0 : ℝ) < Q ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hDpow0 : (0 : ℝ) < (D : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hD0 _
    have hDhalfpow : Q ^ (1/4 : ℝ) / 2 ≤ (D : ℝ) ^ (1/2 : ℝ) := by
      have e1 : (Q ^ (1/2 : ℝ) / 2) ^ (1/2 : ℝ) ≤ (D : ℝ) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hDhalf (by norm_num)
      have e2 : (Q ^ (1/2 : ℝ) / 2) ^ (1/2 : ℝ) = Q ^ (1/4 : ℝ) / (2 : ℝ) ^ (1/2 : ℝ) := by
        rw [Real.div_rpow hs0.le (by norm_num), ← Real.rpow_mul hQpos.le]
        norm_num
      have e3 : (2 : ℝ) ^ (1/2 : ℝ) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
          (show (1/2 : ℝ) ≤ 1 by norm_num)
        rwa [Real.rpow_one] at h
      have e4 : (0 : ℝ) < (2 : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have e5 : Q ^ (1/4 : ℝ) / 2 ≤ Q ^ (1/4 : ℝ) / (2 : ℝ) ^ (1/2 : ℝ) :=
        div_le_div_of_nonneg_left hq40.le e4 e3
      linarith only [e1, e2.le, e2.ge, e5]
    -- the convolution
    have hS1 := sum_coprime_moebius_eq_sum_smooth t ⌊Q⌋₊ ht
      (fun m => (1 : ℝ) / (m : ℝ) * Real.log (Q / (m : ℝ)))
    have hL : ∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          (moebius n : ℝ) / n * Real.log (Q / n)
        = ∑ m ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun m => Nat.Coprime m t),
            (moebius m : ℝ) * ((1 : ℝ) / (m : ℝ) * Real.log (Q / (m : ℝ))) :=
      Finset.sum_congr rfl fun m _ => by ring
    have hR : ∀ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors),
        (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (moebius e : ℝ)
            * ((1 : ℝ) / ((d * e : ℕ) : ℝ) * Real.log (Q / ((d * e : ℕ) : ℝ))))
          = (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
              (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) := by
      intro d _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      push_cast
      rw [div_div]
      ring
    rw [hL, hS1, Finset.sum_congr rfl hR]
    -- the decomposition
    have hdecomp : ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors),
          (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
            (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ))
          - (t : ℝ) / Nat.totient t
        = (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
            (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
              (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1))
          + (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
            (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
              (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1))
          + ((∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
              (fun d => d.primeFactors ⊆ t.primeFactors), (1 : ℝ) / (d : ℝ))
            - (t : ℝ) / Nat.totient t) := by
      have h1 := Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors))
        (fun d => d ≤ D)
        (fun d => (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
          (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1))
      have h2 : ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors),
            (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
              (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1)
          = (∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
              (fun d => d.primeFactors ⊆ t.primeFactors),
              (1 : ℝ) / (d : ℝ) * ∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
                (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)))
            - ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
              (fun d => d.primeFactors ⊆ t.primeFactors), (1 : ℝ) / (d : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun d _ => by ring
      linarith only [h1, h2.le, h2.ge]
    rw [hdecomp]
    -- the three pieces
    have hCT0 : (0 : ℝ) ≤ CT * 2 ^ A / Real.log (2 * Q) ^ A :=
      div_nonneg (mul_nonneg hCT.le h2A.le) hlog2QA.le
    have hnear : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
          (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
            (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1)|
        ≤ 3 * sigmaQ t * (CT * 2 ^ A / Real.log (2 * Q) ^ A) := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
          |(1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
            (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1)|
            ≤ (1 : ℝ) / (d : ℝ) * (CT * 2 ^ A / Real.log (2 * Q) ^ A) := by
        intro d hd
        rw [smooth_filter_le t ⌊Q⌋₊ D hDN, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, hdD⟩, _⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hdR : (d : ℝ) ≤ Q ^ (1/2 : ℝ) := le_trans (by exact_mod_cast hdD) hDle
        obtain ⟨hQd, _⟩ := le_sqrt_div_log hQ hd1 hdR
        have hTb := hT (Q / (d : ℝ)) hQd
        rw [Nat.floor_div_natCast Q d] at hTb
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (d : ℝ))]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_trans hTb (div_log_pow_near hA hCT hQ hd1 hdR)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_smooth_near_le t ⌊Q⌋₊ D ht) hCT0
    have hfar : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
          (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
            (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1)|
        ≤ 2 * (1 + Real.log Q) ^ 2 * (3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ)) := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
            (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
          |(1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
            (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1)|
            ≤ (1 : ℝ) / (d : ℝ) * (2 * (1 + Real.log Q) ^ 2) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨⟨hd1, hdN⟩, _⟩, _⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
        have hdQ : (d : ℝ) ≤ Q := le_trans (by exact_mod_cast hdN) hNQ
        have hQd : (1 : ℝ) ≤ Q / (d : ℝ) := (one_le_div hd0).mpr hdQ
        have hTb := abs_sum_moebius_div_log_le hQd
        rw [Nat.floor_div_natCast Q d] at hTb
        have hlogd : Real.log (Q / (d : ℝ)) ≤ Real.log Q := by
          refine Real.log_le_log (by positivity) ?_
          rw [div_le_iff₀ hd0]
          nlinarith only [hd1R, hQpos]
        have hlogd0 : (0 : ℝ) ≤ Real.log (Q / (d : ℝ)) := Real.log_nonneg hQd
        have hsqle : (1 + Real.log (Q / (d : ℝ))) ^ 2 ≤ (1 + Real.log Q) ^ 2 := by
          nlinarith only [hlogd, hlogd0, hlogQ0]
        have hone : (1 : ℝ) ≤ (1 + Real.log Q) ^ 2 := by nlinarith only [hlogQ0]
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (d : ℝ))]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (abs_sub_le_add _ _) ?_
        rw [abs_one]
        linarith only [hTb, hsqle, hone]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      have h := mul_le_mul_of_nonneg_right (sum_smooth_far_le t ⌊Q⌋₊ D ht hD1 hDN)
        (show (0 : ℝ) ≤ 2 * (1 + Real.log Q) ^ 2 by positivity)
      linarith only [h]
    have hmaint : |(∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors), (1 : ℝ) / (d : ℝ))
          - (t : ℝ) / Nat.totient t| ≤ 3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ) := by
      have h2 := sum_smooth_inv_le t ⌊Q⌋₊ ht
      have h3 := div_totient_sub_sum_smooth_inv_le t D ht hD1
      have hsub : (Finset.Icc 1 D).filter (fun d => d.primeFactors ⊆ t.primeFactors)
          ⊆ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors) := by
        intro x hx
        rw [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
        exact ⟨⟨hx.1.1, le_trans hx.1.2 hDN⟩, hx.2⟩
      have h4 : ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d.primeFactors ⊆ t.primeFactors),
            (1 : ℝ) / (d : ℝ)
          ≤ ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => d.primeFactors ⊆ t.primeFactors),
            (1 : ℝ) / (d : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      rw [abs_le]
      constructor <;> linarith only [h2, h3, h4]
    -- the two tails against the A4 helper
    have hA4sq := one_add_log_sq_mul_log_rpow_le A hA hQ
    have hA4a := log_rpow_le_rpow_quarter A hA (show (1 : ℝ) ≤ 2 * Q by linarith)
    have hsplit24 : (2 * Q) ^ (1/4 : ℝ) = (2 : ℝ) ^ (1/4 : ℝ) * Q ^ (1/4 : ℝ) :=
      Real.mul_rpow (by norm_num) hQpos.le
    have h2quarter : (2 : ℝ) ^ (1/4 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1/4 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hLA : Real.log (2 * Q) ^ A ≤ (4 * A) ^ A * (2 * Q ^ (1/4 : ℝ)) := by
      refine le_trans hA4a ?_
      rw [hsplit24]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2quarter hq40.le) hk1.le
    have hfarC : 2 * (1 + Real.log Q) ^ 2 * (3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ))
        ≤ 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
            * sigmaQ t / Real.log (2 * Q) ^ A := by
      have hEq : 2 * (1 + Real.log Q) ^ 2 * (3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ))
          = (6 * sigmaQ t * (1 + Real.log Q) ^ 2) / (D : ℝ) ^ (1/2 : ℝ) := by ring
      rw [hEq, div_le_div_iff₀ hDpow0 hlog2QA]
      have p1 : 6 * sigmaQ t * ((1 + Real.log Q) ^ 2 * Real.log (2 * Q) ^ A)
          ≤ 6 * sigmaQ t * (2 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1)
              + (4 * (A + 2)) ^ (A + 2)) * Q ^ (1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hA4sq (by linarith)
      have p2 : 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
              * sigmaQ t * (Q ^ (1/4 : ℝ) / 2)
          ≤ 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
              * sigmaQ t * (D : ℝ) ^ (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left hDhalfpow
          (mul_nonneg (by linarith only [hk1, hk2, hk3]) hsig0.le)
      linarith only [p1, p2]
    have hmainC : 3 * sigmaQ t / (D : ℝ) ^ (1/2 : ℝ)
        ≤ 12 * (4 * A) ^ A * sigmaQ t / Real.log (2 * Q) ^ A := by
      rw [div_le_div_iff₀ hDpow0 hlog2QA]
      have p1 : 3 * sigmaQ t * Real.log (2 * Q) ^ A
          ≤ 3 * sigmaQ t * ((4 * A) ^ A * (2 * Q ^ (1/4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hLA (by linarith)
      have p2 : 12 * (4 * A) ^ A * sigmaQ t * (Q ^ (1/4 : ℝ) / 2)
          ≤ 12 * (4 * A) ^ A * sigmaQ t * (D : ℝ) ^ (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left hDhalfpow
          (mul_nonneg (by linarith only [hk1]) hsig0.le)
      linarith only [p1, p2]
    have hextra : (0 : ℝ) ≤ ((1 + Real.log 4) ^ 2 + 3) * Real.log 8 ^ A * sigmaQ t
        / Real.log (2 * Q) ^ A :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) hlog8.le)
        (by linarith only [hsig1])) hlog2QA.le
    have habs := abs_add_add_le
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
        (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => d ≤ D),
        (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
          (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1))
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
        (fun d => d.primeFactors ⊆ t.primeFactors)).filter (fun d => ¬ d ≤ D),
        (1 : ℝ) / (d : ℝ) * (∑ e ∈ Finset.Icc 1 (⌊Q⌋₊ / d),
          (moebius e : ℝ) / (e : ℝ) * Real.log (Q / (d : ℝ) / (e : ℝ)) - 1))
      ((∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
          (fun d => d.primeFactors ⊆ t.primeFactors), (1 : ℝ) / (d : ℝ))
        - (t : ℝ) / Nat.totient t)
    have hringid : (((1 + Real.log 4) ^ 2 + 3) * Real.log 8 ^ A + 3 * CT * 2 ^ A
          + 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
          + 12 * (4 * A) ^ A) * sigmaQ t / Real.log (2 * Q) ^ A
        = ((1 + Real.log 4) ^ 2 + 3) * Real.log 8 ^ A * sigmaQ t / Real.log (2 * Q) ^ A
          + 3 * sigmaQ t * (CT * 2 ^ A / Real.log (2 * Q) ^ A)
          + 24 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
              * sigmaQ t / Real.log (2 * Q) ^ A
          + 12 * (4 * A) ^ A * sigmaQ t / Real.log (2 * Q) ^ A := by
      ring
    rw [hringid]
    linarith only [habs, hnear, hfar, hfarC, hmaint, hmainC, hextra]

/-! ### The κ-expansion (H6f's and H6e's stone) -/

/-- `κ(∏ P) = ∏_{p ∈ P}(p + 1)` for a finite set of primes. -/
private lemma kappa_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, Nat.Prime p) :
    kappa (∏ p ∈ T, p) = ∏ p ∈ T, ((p : ℝ) + 1) := by
  have hpf : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod hT
  rw [kappa, hpf, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hT p hp).pos
  field_simp

/-- `Σ_{k ∣ r} μ(k)/κ(k) = ∏_{p ∣ r}(1 − 1/(p+1))` — only the squarefree divisors survive,
they are the subsets of `r.primeFactors`, and `Finset.prod_one_add` collects them. -/
private lemma sum_moebius_div_kappa_eq (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ r.divisors, (moebius k : ℝ) / kappa k
      = ∏ p ∈ r.primeFactors, (1 - 1 / ((p : ℝ) + 1)) := by
  classical
  have hr0 : r ≠ 0 := by omega
  have hfilter : ∑ k ∈ r.divisors, (moebius k : ℝ) / kappa k
      = ∑ k ∈ r.divisors.filter Squarefree, (moebius k : ℝ) / kappa k := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun k hk hk' => ?_).symm
    have hns : ¬ Squarefree k := fun hs => hk' (Finset.mem_filter.mpr ⟨hk, hs⟩)
    rw [moebius_eq_zero_of_not_squarefree hns, Int.cast_zero, zero_div]
  rw [hfilter, Nat.sum_divisors_filter_squarefree hr0]
  have hbridge : (UniqueFactorizationMonoid.normalizedFactors r).toFinset = r.primeFactors := by
    rw [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
  rw [hbridge]
  have hform : ∏ p ∈ r.primeFactors, (1 - 1 / ((p : ℝ) + 1))
      = ∏ p ∈ r.primeFactors, (1 + -(1 / ((p : ℝ) + 1))) :=
    Finset.prod_congr rfl fun p _ => by ring
  rw [hform, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hsub : T ⊆ r.primeFactors := Finset.mem_powerset.mp hT
  have hprime : ∀ p ∈ T, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
  have hpw : (↑T : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hne
  have hval : T.val.prod = ∏ p ∈ T, p := Finset.prod_val T
  rw [hval, isMultiplicative_moebius.map_prod (fun p : ℕ => p) T hpw,
    kappa_prod_primes hprime, Int.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [moebius_apply_prime (hprime p hp)]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hprime p hp).pos
  push_cast
  field_simp

/-- **The κ-expansion.** `μ(n)/κ(n) = (μ(n)/n)·Σ_{d ∣ n} μ(d)/κ(d)` — both sides vanish off
squarefree, and on squarefree `n` the divisor sum is `∏(1 − 1/(p+1)) = n/κ(n)`. -/
private lemma moebius_div_kappa_expand {n : ℕ} (hn : 1 ≤ n) :
    (moebius n : ℝ) / kappa n
      = (moebius n : ℝ) / n * ∑ d ∈ n.divisors, (moebius d : ℝ) / kappa d := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < kappa n := lt_of_lt_of_le hn0 (le_kappa n hn)
  by_cases hsqf : Squarefree n
  · rw [sum_moebius_div_kappa_eq n hn]
    have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqf]
    have hkap : kappa n = ∏ p ∈ n.primeFactors, ((p : ℝ) + 1) := by
      rw [kappa, hnR, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      field_simp
    have hprod : ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) + 1)) = (n : ℝ) / kappa n := by
      rw [hnR, hkap, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      field_simp
      ring
    rw [hprod]
    field_simp
  · rw [moebius_eq_zero_of_not_squarefree hsqf]
    simp

/-- The termwise identity behind the `κ`-expansion's swap. -/
private lemma kappa_swap_term (t : ℕ) {d f : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f) :
    (if Nat.Coprime (d * f) t then
        (moebius (d * f) : ℝ) / ((d * f : ℕ) : ℝ) * ((moebius d : ℝ) / kappa d) else 0)
      = (if Nat.Coprime d t then (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d) else 0)
        * (if Nat.Coprime f (d * t) then (moebius f : ℝ) / (f : ℝ) else 0) := by
  classical
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hkpos : (0 : ℝ) < kappa d := lt_of_lt_of_le hd0 (le_kappa d hd)
  by_cases hdsq : Squarefree d
  · by_cases hfsq : Squarefree f
    · by_cases hdf : Nat.Coprime d f
      · have hmu : (moebius (d * f) : ℝ) = (moebius d : ℝ) * (moebius f : ℝ) := by
          rw [isMultiplicative_moebius.map_mul_of_coprime hdf]
          push_cast
          ring
        have hcop : Nat.Coprime (d * f) t ↔ Nat.Coprime d t ∧ Nat.Coprime f t :=
          Nat.coprime_mul_iff_left
        have hcop2 : Nat.Coprime f (d * t) ↔ Nat.Coprime f t := by
          rw [Nat.coprime_mul_iff_right]
          exact ⟨fun h => h.2, fun h => ⟨Nat.coprime_comm.mp hdf, h⟩⟩
        by_cases hdt : Nat.Coprime d t
        · by_cases hft : Nat.Coprime f t
          · rw [if_pos (hcop.mpr ⟨hdt, hft⟩), if_pos hdt, if_pos (hcop2.mpr hft), hmu]
            have hdne : (d : ℝ) ≠ 0 := hd0.ne'
            have hfne : (f : ℝ) ≠ 0 := hf0.ne'
            have hkne : kappa d ≠ 0 := hkpos.ne'
            push_cast
            field_simp
          · rw [if_neg (fun h => hft (hcop.mp h).2), if_pos hdt,
              if_neg (fun h => hft (hcop2.mp h)), mul_zero]
        · rw [if_neg (fun h => hdt (hcop.mp h).1), if_neg hdt, zero_mul]
      · have hns : ¬ Squarefree (d * f) := by
          intro hsq
          obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (show Nat.gcd d f ≠ 1 from hdf)
          have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left d f)
          have hpf' : p ∣ f := hpg.trans (Nat.gcd_dvd_right d f)
          have hpp : p * p ∣ d * f := mul_dvd_mul hpd hpf'
          have hu := hsq p hpp
          exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)
        have hnc : ¬ Nat.Coprime f (d * t) := by
          intro h
          exact hdf (Nat.coprime_comm.mp ((Nat.coprime_mul_iff_right.mp h).1))
        rw [moebius_eq_zero_of_not_squarefree hns, if_neg hnc, mul_zero]
        split_ifs <;> simp
    · have hns : ¬ Squarefree (d * f) := fun hsq => hfsq (hsq.squarefree_of_dvd ⟨d, by ring⟩)
      rw [moebius_eq_zero_of_not_squarefree hns,
        moebius_eq_zero_of_not_squarefree hfsq]
      split_ifs <;> simp
  · have hns : ¬ Squarefree (d * f) := fun hsq => hdsq (hsq.squarefree_of_dvd ⟨f, rfl⟩)
    rw [moebius_eq_zero_of_not_squarefree hns,
      moebius_eq_zero_of_not_squarefree hdsq]
    split_ifs <;> simp

/-- **The κ-expansion's swap.** `Σ_{n ≤ N, (n,t)=1} μ(n)/κ(n) =
Σ_{d ≤ N, (d,t)=1} (μ²(d)/(dκ(d)))·Σ_{f ≤ N/d, (f,dt)=1} μ(f)/f`. -/
private lemma sum_coprime_moebius_div_kappa_swap (t N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n t), (moebius n : ℝ) / kappa n
      = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d t),
          (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ∑ f ∈ (Finset.Icc 1 (N / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) := by
  classical
  have hL : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n t), (moebius n : ℝ) / kappa n
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          (if Nat.Coprime n t then (moebius n : ℝ) / (n : ℝ)
            * ((moebius d : ℝ) / kappa d) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    by_cases hc : Nat.Coprime n t
    · rw [if_pos hc, moebius_div_kappa_expand hn1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => (if_pos hc).symm
    · rw [if_neg hc, Finset.sum_congr rfl (fun d (_ : d ∈ n.divisors) => if_neg hc),
        Finset.sum_const, smul_zero]
  have hR : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d t),
        (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (N / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, ∑ f ∈ Finset.Icc 1 (N / d),
          (if Nat.Coprime d t then (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d) else 0)
            * (if Nat.Coprime f (d * t) then (moebius f : ℝ) / (f : ℝ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_filter]
    by_cases hc : Nat.Coprime d t
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, zero_mul]
  rw [hL, hR, sum_divisors_swap N (fun d n => if Nat.Coprime n t then
    (moebius n : ℝ) / (n : ℝ) * ((moebius d : ℝ) / kappa d) else 0)]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  refine Finset.sum_congr rfl fun f hf => ?_
  obtain ⟨hf1, _⟩ := Finset.mem_Icc.mp hf
  exact kappa_swap_term t hd1 hf1

/-- **σ is submultiplicative** (K36): `σ_{−1/4}(d·t) ≤ σ_{−1/4}(d)·σ_{−1/4}(t)`, by the
injection `e ↦ (gcd(e,d), e/gcd(e,d))` of `(dt).divisors` into `d.divisors ×ˢ t.divisors`. -/
private lemma sigmaQ_mul_le (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    sigmaQ (d * t) ≤ sigmaQ d * sigmaQ t := by
  classical
  have hd0 : d ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  have hdt0 : d * t ≠ 0 := Nat.mul_ne_zero hd0 ht0
  have hrec : ∀ e ∈ (d * t).divisors, Nat.gcd e d * (e / Nat.gcd e d) = e :=
    fun e _ => Nat.mul_div_cancel' (Nat.gcd_dvd_left e d)
  have hmaps : ∀ e ∈ (d * t).divisors,
      (Nat.gcd e d, e / Nat.gcd e d) ∈ d.divisors ×ˢ t.divisors := by
    intro e he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hedt : e ∣ d * t := (Nat.mem_divisors.mp he).1
    have hg0 : 0 < Nat.gcd e d := Nat.gcd_pos_of_pos_left d he0
    have hgd : Nat.gcd e d ∣ d := Nat.gcd_dvd_right e d
    have hcop : Nat.Coprime (e / Nat.gcd e d) (d / Nat.gcd e d) :=
      Nat.coprime_div_gcd_div_gcd hg0
    have hbt : e / Nat.gcd e d ∣ t := by
      have hstep : Nat.gcd e d * (e / Nat.gcd e d) ∣ Nat.gcd e d * ((d / Nat.gcd e d) * t) := by
        calc Nat.gcd e d * (e / Nat.gcd e d) = e := hrec e he
          _ ∣ d * t := hedt
          _ = Nat.gcd e d * ((d / Nat.gcd e d) * t) := by
              rw [← mul_assoc, Nat.mul_div_cancel' hgd]
      have h2 : e / Nat.gcd e d ∣ (d / Nat.gcd e d) * t :=
        (Nat.mul_dvd_mul_iff_left hg0).mp hstep
      exact hcop.dvd_of_dvd_mul_left h2
    rw [Finset.mem_product]
    exact ⟨Nat.mem_divisors.mpr ⟨hgd, hd0⟩,
      Nat.mem_divisors.mpr ⟨hbt, ht0⟩⟩
  have hinj : Set.InjOn (fun e => (Nat.gcd e d, e / Nat.gcd e d)) ↑(d * t).divisors := by
    intro a ha b hb hab
    have h1 : Nat.gcd a d = Nat.gcd b d := congrArg Prod.fst hab
    have h2 : a / Nat.gcd a d = b / Nat.gcd b d := congrArg Prod.snd hab
    have ha' := hrec a (by simpa using ha)
    have hb' := hrec b (by simpa using hb)
    rw [← ha', ← hb', h2, h1]
  have hstep1 : sigmaQ (d * t)
      = ∑ z ∈ (d * t).divisors.image (fun e => (Nat.gcd e d, e / Nat.gcd e d)),
          ((z.1 * z.2 : ℕ) : ℝ) ^ (-(1/4 : ℝ)) := by
    rw [sigmaQ, Finset.sum_image (f := fun z : ℕ × ℕ => ((z.1 * z.2 : ℕ) : ℝ) ^ (-(1/4 : ℝ)))
      hinj]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hrec e he]
  rw [hstep1]
  have hsub : (d * t).divisors.image (fun e => (Nat.gcd e d, e / Nat.gcd e d))
      ⊆ d.divisors ×ˢ t.divisors := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    exact hmaps e he
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => Real.rpow_nonneg (by positivity) _)) ?_
  rw [Finset.sum_product, sigmaQ, sigmaQ, Finset.sum_mul]
  refine le_of_eq ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
  push_cast
  exact Real.mul_rpow ha0 hb0

/-- `Σ_{d ≤ D} σ_{−1/4}(d)/d² ≤ 4` — the divisor swap and `Σ 1/n² ≤ 2` twice. -/
private lemma sum_sigmaQ_div_sq_le (D : ℕ) :
    ∑ d ∈ Finset.Icc 1 D, sigmaQ d / (d : ℝ) ^ 2 ≤ 4 := by
  classical
  have hexp : ∑ d ∈ Finset.Icc 1 D, sigmaQ d / (d : ℝ) ^ 2
      = ∑ r ∈ Finset.Icc 1 D, ∑ e ∈ r.divisors,
          (e : ℝ) ^ (-(1/4 : ℝ)) / (r : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sigmaQ, Finset.sum_div]
  rw [hexp, sum_divisors_swap D (fun e r => (e : ℝ) ^ (-(1/4 : ℝ)) / (r : ℝ) ^ 2)]
  have hterm : ∀ e ∈ Finset.Icc 1 D,
      ∑ f ∈ Finset.Icc 1 (D / e), (e : ℝ) ^ (-(1/4 : ℝ)) / ((e * f : ℕ) : ℝ) ^ 2
        ≤ 2 / (e : ℝ) ^ 2 := by
    intro e he
    obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
    have hq : (e : ℝ) ^ (-(1/4 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg he0.le]
      have h1 : (1 : ℝ) ≤ (e : ℝ) ^ (1/4 : ℝ) := Real.one_le_rpow heR (by norm_num)
      rw [inv_le_one_iff₀]
      right
      exact h1
    have hstep : ∀ f ∈ Finset.Icc 1 (D / e),
        (e : ℝ) ^ (-(1/4 : ℝ)) / ((e * f : ℕ) : ℝ) ^ 2
          ≤ (1 / (e : ℝ) ^ 2) * (1 / (f : ℝ) ^ 2) := by
      intro f hf
      obtain ⟨hf1, _⟩ := Finset.mem_Icc.mp hf
      have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf1
      have hcast : ((e * f : ℕ) : ℝ) ^ 2 = (e : ℝ) ^ 2 * (f : ℝ) ^ 2 := by
        push_cast; ring
      rw [hcast]
      have hpos : (0 : ℝ) < (e : ℝ) ^ 2 * (f : ℝ) ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      have hone : (1 / (e : ℝ) ^ 2) * (1 / (f : ℝ) ^ 2) * ((e : ℝ) ^ 2 * (f : ℝ) ^ 2) = 1 := by
        field_simp
      rw [hone]
      exact hq
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have h2 := sum_inv_sq_le_two (D / e)
    have hinv : (0 : ℝ) ≤ 1 / (e : ℝ) ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hinv
    have h4 : (1 / (e : ℝ) ^ 2) * 2 = 2 / (e : ℝ) ^ 2 := by ring
    linarith only [h3, h4.le, h4.ge]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have h5 : ∑ e ∈ Finset.Icc 1 D, 2 / (e : ℝ) ^ 2
      = 2 * ∑ e ∈ Finset.Icc 1 D, 1 / (e : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [h5]
  linarith only [sum_inv_sq_le_two D]

/-- `|μ(n)/κ(n)| ≤ 1/n` for `n ≥ 1` (`κ(n) ≥ n`). -/
private lemma abs_moebius_div_kappa_le {n : ℕ} (hn : 1 ≤ n) :
    |(moebius n : ℝ) / kappa n| ≤ ((n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < kappa n := lt_of_lt_of_le hn0 (le_kappa n hn)
  have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [abs_div, abs_of_nonneg hkpos.le]
  have h1 : |((moebius n : ℤ) : ℝ)| / kappa n ≤ 1 / kappa n :=
    (div_le_div_iff_of_pos_right hkpos).mpr hmu
  have h2 : (1 : ℝ) / kappa n ≤ 1 / (n : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hn0 (le_kappa n hn)
  rw [inv_eq_one_div]
  linarith only [h1, h2]

set_option maxHeartbeats 1600000 in
-- H6f assembles the κ-expansion's swap, the near/far split and the two regimes in one
-- declaration; it exceeds the default elaboration budget.
/-- **H6f (the H freeze's row, verbatim).**
`|Σ_{n ≤ Q, (n,t)=1} μ(n)/κ(n)| ≤ C·σ_{−1/4}(t)/(log 2Q)^A`.

The κ-expansion `μ(n)/κ(n) = (μ(n)/n)·Σ_{d ∣ n} μ(d)/κ(d)` (both sides zero off squarefree;
on squarefree `n` the divisor sum is `∏(1 − 1/(p+1)) = n/κ(n)`) and the divisor swap turn
the coprime sum into `Σ_{d ≤ Q,(d,t)=1}(μ²(d)/(dκ(d)))·Σ_{f ≤ Q/d,(f,dt)=1} μ(f)/f`. On
`d ≤ D = ⌊√Q⌋₊` the inner sum is S4 at level `d·t`, with `σ(dt) ≤ σ(d)σ(t)` (K36) and
`Σ_{d ≤ D} σ(d)/d² ≤ 4`; beyond `D` the trivial `|Σ μ(f)/f| ≤ 1 + log Q` runs against
`Σ_{d > D} 1/d² ≤ 2/(D+1) ≤ 2/√Q`, closed by the A4 helper at `A` and `A + 1`. Below
`Q = 4` the trivial `|Σ| ≤ 1 + log Q` (from `κ(n) ≥ n`) is absorbed into `C`.

The constant is NON-EFFECTIVE (S4 carries `mmuRate_holds`'s window through H6b).

The must-FAIL control (measured): with the `σ(t)` weight DROPPED, at `t = primorial(z)` and
`Q = z` only `n = 1` survives the coprimality filter, so `|Σ| = 1` EXACTLY and
`|Σ|·(log 2Q)² = 16.8 / 28.1 / 40.9 / 57.8 / 75.7` at `z = 30 / 100 / 300 / 1000 / 3000` —
UNBOUNDED (the same mechanism as S4's control). -/
theorem coprime_sum_moebius_div_kappa_le (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, Squarefree t →
    ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t), (moebius n : ℝ) / kappa n|
      ≤ C * sigmaQ t / Real.log (2 * Q) ^ A := by
  classical
  obtain ⟨CS, hCS, hS⟩ := abs_coprime_sum_moebius_div_le A hA
  have h2A : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hk2 : (0 : ℝ) < (4 * (A + 1)) ^ (A + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlog8 : (0 : ℝ) < Real.log 8 ^ A := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  refine ⟨(1 + Real.log 4) * Real.log 8 ^ A + 4 * CS * 2 ^ A
    + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)), by positivity, ?_⟩
  intro t hts Q hQ
  have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr hts.ne_zero
  have hQpos : (0 : ℝ) < Q := by linarith
  have hsig1 : (1 : ℝ) ≤ sigmaQ t := one_le_sigmaQ t ht
  have hsig0 : (0 : ℝ) < sigmaQ t := by linarith
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
  have hCpos : (0 : ℝ) < (1 + Real.log 4) * Real.log 8 ^ A + 4 * CS * 2 ^ A
      + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) := by positivity
  rcases lt_or_ge Q 4 with hsmall | hbig
  -- ═══ the trivial regime `Q < 4` ═══
  · have htriv : |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) / kappa n| ≤ 1 + Real.log Q := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => abs_nonneg _)) ?_
      refine le_trans (Finset.sum_le_sum (fun n hn =>
        abs_moebius_div_kappa_le (Finset.mem_Icc.mp hn).1)) ?_
      refine le_trans (sum_inv_le_one_add_log _) ?_
      linarith [log_natCast_le_log hQ hNQ]
    have hmono : Real.log (2 * Q) ^ A ≤ Real.log 8 ^ A :=
      Real.rpow_le_rpow hlog2Q.le (Real.log_le_log (by linarith) (by linarith)) hA.le
    have hlq4 : Real.log Q ≤ Real.log 4 := Real.log_le_log hQpos (by linarith)
    refine le_trans htriv ?_
    rw [le_div_iff₀ hlog2QA]
    have h1 : (1 + Real.log Q) * Real.log (2 * Q) ^ A
        ≤ (1 + Real.log 4) * Real.log 8 ^ A := by
      have e1 : (1 + Real.log Q) * Real.log (2 * Q) ^ A
          ≤ (1 + Real.log 4) * Real.log (2 * Q) ^ A :=
        mul_le_mul_of_nonneg_right (by linarith) hlog2QA.le
      have e2 : (1 + Real.log 4) * Real.log (2 * Q) ^ A ≤ (1 + Real.log 4) * Real.log 8 ^ A :=
        mul_le_mul_of_nonneg_left hmono (by linarith)
      linarith only [e1, e2]
    have hC1 : (1 + Real.log 4) * Real.log 8 ^ A
        ≤ (1 + Real.log 4) * Real.log 8 ^ A + 4 * CS * 2 ^ A
          + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) := by
      nlinarith only [hCS, h2A, hk1, hk2]
    have hCsig : (1 + Real.log 4) * Real.log 8 ^ A + 4 * CS * 2 ^ A
          + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1))
        ≤ ((1 + Real.log 4) * Real.log 8 ^ A + 4 * CS * 2 ^ A
          + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1))) * sigmaQ t := by
      nlinarith only [hCpos, hsig1]
    linarith only [h1, hC1, hCsig]
  -- ═══ the main regime `Q ≥ 4` ═══
  · have hs0 : (0 : ℝ) < Q ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hspow : (Q ^ (1/2 : ℝ)) ^ 2 = Q := by
      rw [rpow_pow_nat hQpos.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have hQ12 : Q ^ (1/2 : ℝ) ≤ Q := by
      have h := Real.rpow_le_rpow_of_exponent_le hQ (show (1/2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    set D : ℕ := ⌊Q ^ (1/2 : ℝ)⌋₊ with hDdef
    have hDle : ((D : ℕ) : ℝ) ≤ Q ^ (1/2 : ℝ) := Nat.floor_le hs0.le
    have hDgt : Q ^ (1/2 : ℝ) < ((D : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hDN : D ≤ ⌊Q⌋₊ := by rw [hDdef]; exact Nat.floor_mono hQ12
    rw [sum_coprime_moebius_div_kappa_swap t ⌊Q⌋₊]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t))
      (fun d => d ≤ D)
      (fun d => (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
        * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
            (moebius f : ℝ) / (f : ℝ))
    -- the weight bound
    have hw : ∀ d : ℕ, 1 ≤ d → |(moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)| ≤ 1 / (d : ℝ) ^ 2 := by
      intro d hd1
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hkpos : (0 : ℝ) < kappa d := lt_of_lt_of_le hd0 (le_kappa d hd1)
      have hmu2 : (moebius d : ℝ) ^ 2 ≤ 1 := by
        have h := moebius_sq (n := d)
        by_cases hsq : Squarefree d
        · rw [if_pos hsq] at h
          have : ((moebius d : ℝ)) ^ 2 = 1 := by exact_mod_cast h
          linarith
        · rw [moebius_eq_zero_of_not_squarefree hsq]
          norm_num
      have hmu0 : (0 : ℝ) ≤ (moebius d : ℝ) ^ 2 := sq_nonneg _
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hmu2, hmu0, hd0, hkpos, le_kappa d hd1]
    -- the near range
    have hnear : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ)|
        ≤ 4 * (CS * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A) := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => d ≤ D),
          |(moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ)|
            ≤ sigmaQ d / (d : ℝ) ^ 2 * (CS * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨⟨hd1, _⟩, _⟩, hdD⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hdR : (d : ℝ) ≤ Q ^ (1/2 : ℝ) := le_trans (by exact_mod_cast hdD) hDle
        obtain ⟨hQd, _⟩ := le_sqrt_div_log hQ hd1 hdR
        have hdt1 : 1 ≤ d * t := Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by omega) (by omega))
        have hSb := hS (d * t) hdt1 (Q / (d : ℝ)) hQd
        rw [Nat.floor_div_natCast Q d] at hSb
        have hsigd : (1 : ℝ) ≤ sigmaQ d := one_le_sigmaQ d hd1
        have hsigdt : (1 : ℝ) ≤ sigmaQ (d * t) := one_le_sigmaQ (d * t) hdt1
        have hCsig : (0 : ℝ) < CS * sigmaQ (d * t) := by nlinarith only [hCS, hsigdt]
        have hmul := sigmaQ_mul_le d t hd1 ht
        have hnear1 : |∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter
              (fun f => Nat.Coprime f (d * t)), (moebius f : ℝ) / (f : ℝ)|
            ≤ CS * sigmaQ d * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A := by
          have h1 : CS * sigmaQ (d * t) / Real.log (2 * (Q / (d : ℝ))) ^ A
              ≤ CS * sigmaQ (d * t) * 2 ^ A / Real.log (2 * Q) ^ A :=
            div_log_pow_near hA hCsig hQ hd1 hdR
          have h2 : CS * sigmaQ (d * t) * 2 ^ A / Real.log (2 * Q) ^ A
              ≤ CS * sigmaQ d * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A := by
            rw [div_le_div_iff_of_pos_right hlog2QA]
            have hstep2 := mul_le_mul_of_nonneg_left hmul (mul_nonneg hCS.le h2A.le)
            nlinarith only [hstep2]
          linarith only [hSb, h1, h2]
        rw [abs_mul]
        have hwd := hw d hd1
        have hAbs0 : (0 : ℝ) ≤ |∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter
            (fun f => Nat.Coprime f (d * t)), (moebius f : ℝ) / (f : ℝ)| := abs_nonneg _
        have hrhs0 : (0 : ℝ) ≤ CS * sigmaQ d * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A :=
          div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCS.le (by linarith only [hsigd]))
            (by linarith only [hsig1])) h2A.le) hlog2QA.le
        have hstep := mul_le_mul hwd hnear1 hAbs0 (by positivity)
        refine le_trans hstep (le_of_eq ?_)
        field_simp
        try ring
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      have hsub : ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => d ≤ D) ⊆ Finset.Icc 1 D := by
        intro x hx
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hx
        rw [Finset.mem_Icc]
        exact ⟨hx.1.1.1, hx.2⟩
      have hsum : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => d ≤ D), sigmaQ d / (d : ℝ) ^ 2 ≤ 4 := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => ?_))
          (sum_sigmaQ_div_sq_le D)
        obtain ⟨hi1, _⟩ := Finset.mem_Icc.mp hi
        have := one_le_sigmaQ i hi1
        have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
        positivity
      refine mul_le_mul_of_nonneg_right hsum ?_
      exact div_nonneg (mul_nonneg (mul_nonneg hCS.le (by linarith only [hsig1])) h2A.le)
        hlog2QA.le
    -- the far range
    have hfar : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => ¬ d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ)|
        ≤ 2 / Q ^ (1/2 : ℝ) * (1 + Real.log Q) := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => ¬ d ≤ D),
          |(moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ)|
            ≤ 1 / (d : ℝ) ^ 2 * (1 + Real.log Q) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨⟨hd1, hdN⟩, _⟩, _⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
        have hdQ : (d : ℝ) ≤ Q := le_trans (by exact_mod_cast hdN) hNQ
        have hQd : (1 : ℝ) ≤ Q / (d : ℝ) := (one_le_div hd0).mpr hdQ
        have htr := abs_coprime_sum_moebius_div_triv (d * t) hQd
        rw [Nat.floor_div_natCast Q d] at htr
        have hlogd : Real.log (Q / (d : ℝ)) ≤ Real.log Q := by
          refine Real.log_le_log (by positivity) ?_
          rw [div_le_iff₀ hd0]
          nlinarith only [hd1R, hQpos]
        rw [abs_mul]
        have hwd := hw d hd1
        have hAbs0 : (0 : ℝ) ≤ |∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter
            (fun f => Nat.Coprime f (d * t)), (moebius f : ℝ) / (f : ℝ)| := abs_nonneg _
        exact mul_le_mul hwd (by linarith only [htr, hlogd]) hAbs0 (by positivity)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      have hsub : ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => ¬ d ≤ D) ⊆ Finset.Ioo D (⌊Q⌋₊ + 1) := by
        intro x hx
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hx
        rw [Finset.mem_Ioo]
        exact ⟨by omega, by omega⟩
      have hsum : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => ¬ d ≤ D), 1 / (d : ℝ) ^ 2 ≤ 2 / Q ^ (1/2 : ℝ) := by
        have h1 : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
              (fun d => ¬ d ≤ D), 1 / (d : ℝ) ^ 2
            ≤ ∑ d ∈ Finset.Ioo D (⌊Q⌋₊ + 1), 1 / (d : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        have h2 : ∑ d ∈ Finset.Ioo D (⌊Q⌋₊ + 1), 1 / (d : ℝ) ^ 2
            = ∑ d ∈ Finset.Ioo D (⌊Q⌋₊ + 1), (((d : ℝ)) ^ 2)⁻¹ :=
          Finset.sum_congr rfl fun d _ => one_div _
        have h3 : ∑ i ∈ Finset.Ioo D (⌊Q⌋₊ + 1), (((i : ℝ)) ^ 2)⁻¹ ≤ 2 / ((D : ℕ) + 1) :=
          sum_Ioo_inv_sq_le D (⌊Q⌋₊ + 1)
        have h4 : (2 : ℝ) / (((D : ℕ) : ℝ) + 1) ≤ 2 / Q ^ (1/2 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hs0 hDgt.le
        rw [h2] at h1
        linarith only [h1, h3, h4]
      exact mul_le_mul_of_nonneg_right hsum (by linarith)
    -- the far range against the A4 helper
    have hq40 : (0 : ℝ) < Q ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hq4s : Q ^ (1/4 : ℝ) ≤ Q ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
    have hA4 := one_add_log_mul_log_rpow_le A hA hQ
    have hfarC : 2 / Q ^ (1/2 : ℝ) * (1 + Real.log Q)
        ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * sigmaQ t
            / Real.log (2 * Q) ^ A := by
      have hEq : 2 / Q ^ (1/2 : ℝ) * (1 + Real.log Q)
          = (2 * (1 + Real.log Q)) / Q ^ (1/2 : ℝ) := by ring
      rw [hEq, div_le_div_iff₀ hs0 hlog2QA]
      have p1 : 2 * ((1 + Real.log Q) * Real.log (2 * Q) ^ A)
          ≤ 2 * (2 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hA4 (by norm_num)
      have p2 : 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1/4 : ℝ)
          ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left hq4s (by linarith only [hk1, hk2])
      have p3 : 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * Q ^ (1/2 : ℝ)
          ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * sigmaQ t * Q ^ (1/2 : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hsig1
          (show (0 : ℝ) ≤ 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) by
            linarith only [hk1, hk2])
        nlinarith only [h, hs0]
      linarith only [p1, p2, p3]
    have hextra : (0 : ℝ) ≤ (1 + Real.log 4) * Real.log 8 ^ A * sigmaQ t
        / Real.log (2 * Q) ^ A :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith only [hlog4]) hlog8.le)
        (by linarith only [hsig1])) hlog2QA.le
    have habs := abs_add_le
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
        (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
        * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
            (moebius f : ℝ) / (f : ℝ))
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
        (fun d => ¬ d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
        * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
            (moebius f : ℝ) / (f : ℝ))
    rw [hsplit] at habs
    have hringid : ((1 + Real.log 4) * Real.log 8 ^ A + 4 * CS * 2 ^ A
          + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1))) * sigmaQ t / Real.log (2 * Q) ^ A
        = (1 + Real.log 4) * Real.log 8 ^ A * sigmaQ t / Real.log (2 * Q) ^ A
          + 4 * (CS * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A)
          + 4 * ((4 * A) ^ A + (4 * (A + 1)) ^ (A + 1)) * sigmaQ t
              / Real.log (2 * Q) ^ A := by
      ring
    rw [hringid]
    linarith only [habs, hnear, hfar, hfarC, hextra]

/-! ### H6e — the κ-weighted log sum -/

/-- The telescoping step of `Σ f^{−3/2}`. -/
private lemma rpow_step_three_halves (t : ℝ) (ht : 1 ≤ t) :
    (t + 1) ^ (-(3/2) : ℝ) ≤ 2 * t ^ (-(1/2) : ℝ) - 2 * (t + 1) ^ (-(1/2) : ℝ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have ha0 : (0 : ℝ) < t ^ ((1/2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
  have hb0 : (0 : ℝ) < (t + 1) ^ ((1/2 : ℝ)) := Real.rpow_pos_of_pos ht1 _
  have ha2 : (t ^ ((1/2 : ℝ))) ^ 2 = t := by
    rw [rpow_pow_nat ht0.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hb2 : ((t + 1) ^ ((1/2 : ℝ))) ^ 2 = t + 1 := by
    rw [rpow_pow_nat ht1.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hb3 : ((t + 1) ^ ((1/2 : ℝ))) ^ 3 = (t + 1) ^ ((3/2 : ℝ)) := by
    rw [rpow_pow_nat ht1.le, show (1/2 : ℝ) * ((3 : ℕ) : ℝ) = (3/2 : ℝ) by norm_num]
  have hL : (t + 1) ^ (-(3/2) : ℝ) = 1 / ((t + 1) ^ ((1/2 : ℝ))) ^ 3 := by
    rw [hb3, Real.rpow_neg ht1.le]
    ring
  have hR1 : t ^ (-(1/2) : ℝ) = 1 / t ^ ((1/2 : ℝ)) := by
    rw [Real.rpow_neg ht0.le]
    ring
  have hR2 : (t + 1) ^ (-(1/2) : ℝ) = 1 / (t + 1) ^ ((1/2 : ℝ)) := by
    rw [Real.rpow_neg ht1.le]
    ring
  have hab : t ^ ((1/2 : ℝ)) < (t + 1) ^ ((1/2 : ℝ)) := by nlinarith only [ha2, hb2, ha0, hb0]
  have hidt : ((t + 1) ^ ((1/2 : ℝ)) - t ^ ((1/2 : ℝ)))
      * ((t + 1) ^ ((1/2 : ℝ)) + t ^ ((1/2 : ℝ))) = 1 := by
    nlinarith only [ha2, hb2]
  rw [hL, hR1, hR2, div_le_iff₀ (by positivity : (0 : ℝ) < ((t + 1) ^ ((1/2 : ℝ))) ^ 3)]
  have hid : (2 * (1 / t ^ ((1/2 : ℝ))) - 2 * (1 / (t + 1) ^ ((1/2 : ℝ))))
        * ((t + 1) ^ ((1/2 : ℝ))) ^ 3
      = (2 * ((t + 1) ^ ((1/2 : ℝ))) ^ 3
          - 2 * t ^ ((1/2 : ℝ)) * ((t + 1) ^ ((1/2 : ℝ))) ^ 2) / t ^ ((1/2 : ℝ)) := by
    field_simp
    try ring
  rw [hid, le_div_iff₀ ha0]
  have hsum0 : (0 : ℝ) < t ^ ((1/2 : ℝ)) + (t + 1) ^ ((1/2 : ℝ)) := by linarith
  have hkey : (t ^ ((1/2 : ℝ)) + (t + 1) ^ ((1/2 : ℝ))) * (1 * t ^ ((1/2 : ℝ)))
      ≤ (t ^ ((1/2 : ℝ)) + (t + 1) ^ ((1/2 : ℝ)))
        * (2 * ((t + 1) ^ ((1/2 : ℝ))) ^ 3
          - 2 * t ^ ((1/2 : ℝ)) * ((t + 1) ^ ((1/2 : ℝ))) ^ 2) := by
    have hexp : (t ^ ((1/2 : ℝ)) + (t + 1) ^ ((1/2 : ℝ)))
        * (2 * ((t + 1) ^ ((1/2 : ℝ))) ^ 3
          - 2 * t ^ ((1/2 : ℝ)) * ((t + 1) ^ ((1/2 : ℝ))) ^ 2)
        = 2 * ((t + 1) ^ ((1/2 : ℝ))) ^ 2
          * (((t + 1) ^ ((1/2 : ℝ)) - t ^ ((1/2 : ℝ)))
            * ((t + 1) ^ ((1/2 : ℝ)) + t ^ ((1/2 : ℝ)))) := by ring
    rw [hexp, hidt]
    nlinarith only [hab, ha0, hb0]
  exact le_of_mul_le_mul_left hkey hsum0

/-- `Σ_{D < n ≤ M} n^{−3/2} ≤ 2·D^{−1/2}` for `D ≥ 1`. -/
private lemma sum_Ioc_rpow_neg_three_halves_le {D : ℕ} (hD : 1 ≤ D) (M : ℕ) :
    ∑ n ∈ Finset.Ioc D M, (n : ℝ) ^ (-(3/2) : ℝ) ≤ 2 * (D : ℝ) ^ (-(1/2) : ℝ) := by
  rcases le_or_gt M D with hMD | hMD
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    have : (0 : ℝ) < (D : ℝ) ^ (-(1/2) : ℝ) := by
      refine Real.rpow_pos_of_pos ?_ _
      exact_mod_cast hD
    linarith
  · have hDM : D ≤ M := by omega
    have key : ∀ m : ℕ, D ≤ m →
        ∑ n ∈ Finset.Ioc D m, (n : ℝ) ^ (-(3/2) : ℝ)
          ≤ 2 * (D : ℝ) ^ (-(1/2) : ℝ) - 2 * (m : ℝ) ^ (-(1/2) : ℝ) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [Finset.sum_Ioc_succ_top hk]
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
          have : (1 : ℕ) ≤ k := le_trans hD hk
          exact_mod_cast this
        have hstep := rpow_step_three_halves (k : ℝ) hk1
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith only [ih, hstep]
    have h := key M hDM
    have hpos : (0 : ℝ) < (M : ℝ) ^ (-(1/2) : ℝ) := by
      refine Real.rpow_pos_of_pos ?_ _
      have : (1 : ℕ) ≤ M := le_trans hD hDM
      exact_mod_cast this
    linarith

/-- The `n^{−3/2}`-dominated tail: a series bounded termwise by `n^{−3/2}` differs from its
partial sum over `[1, D]` by at most `2·D^{−1/2}`. -/
private lemma abs_tsum_sub_sum_le_three_halves {g : ℕ → ℝ} (hg : Summable g)
    (hb : ∀ n : ℕ, |g n| ≤ (n : ℝ) ^ (-(3/2) : ℝ)) {D : ℕ} (hD : 1 ≤ D) :
    |(∑' n : ℕ, g n) - ∑ n ∈ Finset.Icc 1 D, g n| ≤ 2 * (D : ℝ) ^ (-(1/2) : ℝ) := by
  classical
  set b : ℕ → ℝ := fun n => if n ∈ Finset.Icc 1 D then 0 else (n : ℝ) ^ (-(3/2) : ℝ) with hbdef
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    rw [hbdef]
    dsimp only
    split_ifs
    · exact le_refl 0
    · exact Real.rpow_nonneg (by positivity) _
  have hbsum : Summable b := by
    refine Summable.of_nonneg_of_le hb0 (fun n => ?_)
      (Real.summable_one_div_nat_rpow.mpr (by norm_num) :
        Summable fun n : ℕ => 1 / (n : ℝ) ^ ((3/2 : ℝ)))
    rw [hbdef]
    dsimp only
    have hne : (n : ℝ) ^ (-(3/2) : ℝ) = 1 / (n : ℝ) ^ ((3/2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), one_div]
    split_ifs
    · positivity
    · rw [hne]
  have hbtsum : (∑' n : ℕ, b n) ≤ 2 * (D : ℝ) ^ (-(1/2) : ℝ) := by
    refine Real.tsum_le_of_sum_le hb0 fun s => ?_
    have hs' : ∑ n ∈ s, b n = ∑ n ∈ s.filter (fun n => D < n), b n := by
      refine (Finset.sum_filter_of_ne fun n _ hne => ?_).symm
      by_contra hcon
      rw [not_lt] at hcon
      refine hne ?_
      rw [hbdef]
      dsimp only
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [if_neg (by simp)]
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
      · rw [if_pos (Finset.mem_Icc.mpr ⟨hn0, hcon⟩)]
    have hsubset : s.filter (fun n => D < n) ⊆ Finset.Ioc D (s.sup id) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Finset.mem_Ioc]
      exact ⟨hn.2, Finset.le_sup (f := id) hn.1⟩
    rw [hs']
    calc ∑ n ∈ s.filter (fun n => D < n), b n
        ≤ ∑ n ∈ Finset.Ioc D (s.sup id), b n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i _ _ => hb0 i
      _ ≤ ∑ n ∈ Finset.Ioc D (s.sup id), (n : ℝ) ^ (-(3/2) : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [hbdef]
          dsimp only
          split_ifs
          · exact Real.rpow_nonneg (by positivity) _
          · exact le_refl _
      _ ≤ 2 * (D : ℝ) ^ (-(1/2) : ℝ) := sum_Ioc_rpow_neg_three_halves_le hD _
  have hg' : Summable (fun n : ℕ => if n ∈ Finset.Icc 1 D then g n else 0) :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 D) fun n hn => if_neg hn
  have hsum' : (∑' n : ℕ, (if n ∈ Finset.Icc 1 D then g n else 0))
      = ∑ n ∈ Finset.Icc 1 D, g n := by
    rw [tsum_eq_sum (s := Finset.Icc 1 D) fun n hn => if_neg hn]
    exact Finset.sum_congr rfl fun n hn => if_pos hn
  have hdiff : (∑' n : ℕ, g n) - ∑ n ∈ Finset.Icc 1 D, g n
      = ∑' n : ℕ, (g n - (if n ∈ Finset.Icc 1 D then g n else 0)) := by
    rw [hg.tsum_sub hg', hsum']
  have hpt : ∀ n : ℕ, |g n - (if n ∈ Finset.Icc 1 D then g n else 0)| ≤ b n := by
    intro n
    by_cases hn : n ∈ Finset.Icc 1 D
    · rw [if_pos hn, sub_self, abs_zero, hbdef]
      dsimp only
      rw [if_pos hn]
    · rw [if_neg hn, sub_zero, hbdef]
      dsimp only
      rw [if_neg hn]
      exact hb n
  have habs : Summable (fun n : ℕ => |g n - (if n ∈ Finset.Icc 1 D then g n else 0)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt hbsum
  rw [hdiff]
  calc |∑' n : ℕ, (g n - (if n ∈ Finset.Icc 1 D then g n else 0))|
      ≤ ∑' n : ℕ, |g n - (if n ∈ Finset.Icc 1 D then g n else 0)| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun n : ℕ => g n - (if n ∈ Finset.Icc 1 D then g n else 0)) (by simpa using habs)
        simpa using h
    _ ≤ ∑' n : ℕ, b n := Summable.tsum_le_tsum hpt habs hbsum
    _ ≤ 2 * (D : ℝ) ^ (-(1/2) : ℝ) := hbtsum

/-- **`1 ≤ c₀` (PUBLIC; the H2 wave consumes it).** The `n = 1` term of the series is `1`
and every term is nonnegative. -/
theorem one_le_c0 : 1 ≤ c0 := by
  have hs : Summable (fun n : ℕ => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) :=
    summable_moebius_sq_div_kappa_totient.of_abs
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (moebius j : ℝ) ^ 2 / (kappa j * (Nat.totient j : ℝ)) := by
    intro j
    refine div_nonneg (sq_nonneg _) (mul_nonneg ?_ (by positivity))
    rw [kappa]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun p _ => by positivity)
  have h1 : (moebius 1 : ℝ) ^ 2 / (kappa 1 * (Nat.totient 1 : ℝ)) = 1 := by
    rw [isMultiplicative_moebius.map_one, kappa, Nat.primeFactors_one]
    norm_num
  have h := hs.le_tsum 1 (fun j _ => hnn j)
  rw [h1] at h
  exact h

/-- `|μ(n)²/(κ(n)φ(n))| ≤ n^{−3/2}` — the bound behind T7's summability helper. -/
private lemma abs_moebius_sq_div_kappa_totient_le (n : ℕ) :
    |(moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))| ≤ (n : ℝ) ^ (-(3/2) : ℝ) := by
  have hrw : (n : ℝ) ^ (-(3/2) : ℝ) = 1 / (n : ℝ) ^ ((3/2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity)]
    ring
  rw [hrw]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · by_cases hsqf : Squarefree n
    · have hbound := rpow_three_halves_le_kappa_mul_totient n hn hsqf
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ ((3/2 : ℝ)) := Real.rpow_pos_of_pos hnR _
      have hkpos : (0 : ℝ) < kappa n * (Nat.totient n : ℝ) := lt_of_lt_of_le hpos hbound
      have hmu : ((moebius n : ℝ)) ^ 2 = 1 := by
        have h := moebius_sq (n := n)
        rw [if_pos hsqf] at h
        exact_mod_cast h
      rw [hmu, abs_of_nonneg (div_nonneg zero_le_one hkpos.le)]
      exact one_div_le_one_div_of_le hpos hbound
    · rw [moebius_eq_zero_of_not_squarefree hsqf, Int.cast_zero, zero_pow (by norm_num),
        zero_div, abs_zero]
      positivity

/-- `Σ_{e ≤ y} |(μ(e)/κ(e))·log(y/e)| ≤ (1 + log y)²` (`κ(e) ≥ e`). -/
private lemma sum_abs_moebius_div_kappa_log_le {y : ℝ} (hy : 1 ≤ y) :
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |(moebius e : ℝ) / kappa e * Real.log (y / e)|
      ≤ (1 + Real.log y) ^ 2 := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hNy : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy0.le
  have hterm : ∀ e ∈ Finset.Icc 1 ⌊y⌋₊,
      |(moebius e : ℝ) / kappa e * Real.log (y / (e : ℝ))| ≤ ((e : ℝ))⁻¹ * Real.log y := by
    intro e he
    obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp he
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    have he1R : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
    have heY : (e : ℝ) ≤ y := le_trans (by exact_mod_cast heN) hNy
    have hye : (1 : ℝ) ≤ y / (e : ℝ) := (one_le_div he0).mpr heY
    have hlog0 : (0 : ℝ) ≤ Real.log (y / (e : ℝ)) := Real.log_nonneg hye
    have hlogle : Real.log (y / (e : ℝ)) ≤ Real.log y := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ he0]
      nlinarith only [he1R, hy0]
    rw [abs_mul, abs_of_nonneg hlog0]
    exact mul_le_mul (abs_moebius_div_kappa_le he1) hlogle hlog0 (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have h2 := sum_inv_le_one_add_log ⌊y⌋₊
  have h3 : Real.log ((⌊y⌋₊ : ℕ) : ℝ) ≤ Real.log y := log_natCast_le_log hy hNy
  nlinarith only [h2, h3, hlogy]

/-- **The κ-expansion's swap, with a weight.** -/
private lemma sum_coprime_moebius_div_kappa_swap_mul (t N : ℕ) (G : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) / kappa n * G n
      = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d t),
          (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ∑ f ∈ (Finset.Icc 1 (N / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) * G (d * f) := by
  classical
  have hL : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) / kappa n * G n
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          (if Nat.Coprime n t then (moebius n : ℝ) / (n : ℝ)
            * ((moebius d : ℝ) / kappa d) * G n else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    by_cases hc : Nat.Coprime n t
    · rw [if_pos hc, moebius_div_kappa_expand hn1, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [if_pos hc]
    · rw [if_neg hc, Finset.sum_congr rfl (fun d (_ : d ∈ n.divisors) => if_neg hc),
        Finset.sum_const, smul_zero]
  have hR : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d t),
        (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (N / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ) * G (d * f)
      = ∑ d ∈ Finset.Icc 1 N, ∑ f ∈ Finset.Icc 1 (N / d),
          (if Nat.Coprime d t then (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d) else 0)
            * ((if Nat.Coprime f (d * t) then (moebius f : ℝ) / (f : ℝ) else 0)
              * G (d * f)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hinner : ∑ f ∈ Finset.Icc 1 (N / d),
          ((if Nat.Coprime f (d * t) then (moebius f : ℝ) / (f : ℝ) else 0) * G (d * f))
        = ∑ f ∈ (Finset.Icc 1 (N / d)).filter (fun f => Nat.Coprime f (d * t)),
            (moebius f : ℝ) / (f : ℝ) * G (d * f) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases hcf : Nat.Coprime f (d * t)
      · rw [if_pos hcf, if_pos hcf]
      · rw [if_neg hcf, if_neg hcf, zero_mul]
    rw [← Finset.mul_sum, hinner]
    by_cases hc : Nat.Coprime d t
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, zero_mul]
  rw [hL, hR, sum_divisors_swap N (fun d n => if Nat.Coprime n t then
    (moebius n : ℝ) / (n : ℝ) * ((moebius d : ℝ) / kappa d) * G n else 0)]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  refine Finset.sum_congr rfl fun f hf => ?_
  obtain ⟨hf1, _⟩ := Finset.mem_Icc.mp hf
  have hbase := kappa_swap_term t hd1 hf1
  have hsplit : (if Nat.Coprime (d * f) t then
        (moebius (d * f) : ℝ) / ((d * f : ℕ) : ℝ) * ((moebius d : ℝ) / kappa d) * G (d * f)
      else 0)
      = (if Nat.Coprime (d * f) t then
          (moebius (d * f) : ℝ) / ((d * f : ℕ) : ℝ) * ((moebius d : ℝ) / kappa d) else 0)
        * G (d * f) := by
    split_ifs
    · rfl
    · rw [zero_mul]
  rw [hsplit, hbase]
  ring

set_option maxHeartbeats 2000000 in
-- H6e assembles the κ-expansion's weighted swap, H6d at level `d·t`, T7's main term and its
-- series tail, and the two regimes in one declaration; it exceeds the default budget.
/-- **H6e, in the NAMED form (the H2 verdict's A1): the witness is the landed `c0`.**
`|Σ_{n ≤ Q,(n,t)=1}(μ(n)/κ(n))log(Q/n) − c₀·κ(t)/t| ≤ C·σ_{−1/4}(t)/(log 2Q)^A`.

The κ-expansion's weighted swap turns the sum into
`Σ_{d ≤ Q,(d,t)=1}(μ²(d)/(dκ(d)))·T_{d·t}(Q/d)`; on `d ≤ D = ⌊√Q⌋₊` the inner sum is H6d at
level `d·t` — `Squarefree (d·t)` by `Nat.squarefree_mul` on `Coprime d t`, and the terms with
`d` NOT squarefree carry `μ²(d) = 0` — whose main term `dt/φ(dt) = (d/φ(d))(t/φ(t))` makes
`Σ_{d ≤ D} (μ²(d)/(dκ(d)))·(dt/φ(dt)) = (t/φ(t))·Σ_{d ≤ D,(d,t)=1} μ²(d)/(κ(d)φ(d))`, which
is T7's `c₀·κ(t)/t` up to the series tail `2/√D` (`|μ²(n)/(κ(n)φ(n))| ≤ n^{−3/2}`). Beyond
`D` the trivial `|T(y)| ≤ (1 + log y)²` runs against `Σ_{d > D} 1/d² ≤ 2/√Q`, closed by the
A4 helper at `A`, `A + 1` and `A + 2`. Below `Q = 4` the trivial bound is absorbed into `C`.

The constant is NON-EFFECTIVE (H6d carries `mmuRate_holds`'s window through C3).

Sanity (measured) at `(t, Q) = (2, 100)`: `Σ_{n ≤ 100 odd}(μ(n)/κ(n))log(100/n) = 2.3446`
against `c₀·κ(2)/2 = 2.4674`.

The must-FAIL control (measured): with `c₀·κ(t)/t` → `c₀·t/κ(t)` at `t = 2`, the ratio is
`19.03 / 42.33 / 72.84 / 110.89 / 156.73` at `Q = 10² … 10⁶` against
`1.8728 / 0.6873 / 0.1954 / 0.0482 / 0.0109` frozen — UNBOUNDED. -/
theorem coprime_sum_moebius_div_kappa_log_eq (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, Squarefree t →
    ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) / kappa n * Real.log (Q / n)
        - c0 * kappa t / t| ≤ C * sigmaQ t / Real.log (2 * Q) ^ A := by
  classical
  obtain ⟨CD, hCD, hD6⟩ := coprime_sum_moebius_div_log_eq A hA
  have h2A : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : (0 : ℝ) < (4 * A) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hk2 : (0 : ℝ) < (4 * (A + 1)) ^ (A + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hk3 : (0 : ℝ) < (4 * (A + 2)) ^ (A + 2) := Real.rpow_pos_of_pos (by linarith) _
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlog8 : (0 : ℝ) < Real.log 8 ^ A := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  refine ⟨((1 + Real.log 4) ^ 2 + 9) * Real.log 8 ^ A + 4 * CD * 2 ^ A
    + 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
    + 24 * (4 * A) ^ A, by positivity, ?_⟩
  intro t hts Q hQ
  have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr hts.ne_zero
  have hQpos : (0 : ℝ) < Q := by linarith
  have hsig1 : (1 : ℝ) ≤ sigmaQ t := one_le_sigmaQ t ht
  have hsig0 : (0 : ℝ) < sigmaQ t := by linarith
  have hlog2Q : 0 < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hlog2QA : (0 : ℝ) < Real.log (2 * Q) ^ A := Real.rpow_pos_of_pos hlog2Q _
  have hlogQ0 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQpos.le
  have htphi := div_totient_le_three_sigmaQ t ht
  have htphi0 : (0 : ℝ) ≤ (t : ℝ) / Nat.totient t := by positivity
  have hCpos : (0 : ℝ) < ((1 + Real.log 4) ^ 2 + 9) * Real.log 8 ^ A + 4 * CD * 2 ^ A
      + 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
      + 24 * (4 * A) ^ A := by positivity
  -- the series and its tail
  have hgsum : Summable (fun n : ℕ => if Nat.Coprime n t then
      (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ)) else 0) :=
    summable_coprime_indicator summable_moebius_sq_div_kappa_totient t
  have hgb : ∀ n : ℕ, |if Nat.Coprime n t then
      (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ)) else 0|
      ≤ (n : ℝ) ^ (-(3/2) : ℝ) := by
    intro n
    by_cases hc : Nat.Coprime n t
    · rw [if_pos hc]
      exact abs_moebius_sq_div_kappa_totient_le n
    · rw [if_neg hc, abs_zero]
      exact Real.rpow_nonneg (by positivity) _
  have htail : ∀ E : ℕ, 1 ≤ E →
      |coprimeSeries (fun n => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) t
        - ∑ n ∈ (Finset.Icc 1 E).filter (fun n => Nat.Coprime n t),
            (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))|
      ≤ 2 * (E : ℝ) ^ (-(1/2) : ℝ) := by
    intro E hE
    have h := abs_tsum_sub_sum_le_three_halves hgsum hgb hE
    have hfil : ∑ n ∈ Finset.Icc 1 E, (if Nat.Coprime n t then
          (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ)) else 0)
        = ∑ n ∈ (Finset.Icc 1 E).filter (fun n => Nat.Coprime n t),
            (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ)) :=
      (Finset.sum_filter _ _).symm
    rw [hfil] at h
    exact h
  have hT7 := div_totient_mul_coprimeSeries_inv_kappa_totient t ht
  -- `S ≤ 3` from the tail at `E = 1`
  have hS3 : coprimeSeries (fun n => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) t
      ≤ 3 := by
    have h1set : (Finset.Icc 1 1).filter (fun n => Nat.Coprime n t) = {1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩
        omega
      · rintro rfl
        exact ⟨⟨le_refl 1, le_refl 1⟩, Nat.coprime_one_left t⟩
    have h1val : ∑ n ∈ (Finset.Icc 1 1).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ)) = 1 := by
      rw [h1set, Finset.sum_singleton, isMultiplicative_moebius.map_one, kappa,
        Nat.primeFactors_one]
      norm_num
    have h := htail 1 (le_refl 1)
    rw [h1val, Nat.cast_one, Real.one_rpow] at h
    have := abs_le.mp h
    linarith [this.2]
  have hc0kt : c0 * kappa t / t = (t : ℝ) / Nat.totient t
      * coprimeSeries (fun n => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) t :=
    hT7.symm
  rcases lt_or_ge Q 4 with hsmall | hbig
  -- ═══ the trivial regime `Q < 4` ═══
  · have htriv : |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) / kappa n * Real.log (Q / n)| ≤ (1 + Real.log Q) ^ 2 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => abs_nonneg _)) ?_
      exact sum_abs_moebius_div_kappa_log_le hQ
    have hS0 : (0 : ℝ) ≤ coprimeSeries
        (fun n => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) t := by
      unfold coprimeSeries
      refine tsum_nonneg fun n => ?_
      by_cases hc : Nat.Coprime n t
      · rw [if_pos hc]
        refine div_nonneg (sq_nonneg _) (mul_nonneg ?_ (by positivity))
        rw [kappa]
        exact mul_nonneg (by positivity) (Finset.prod_nonneg fun p _ => by positivity)
      · rw [if_neg hc]
    have hmain0 : (0 : ℝ) ≤ c0 * kappa t / t := by
      rw [hc0kt]
      exact mul_nonneg htphi0 hS0
    have hmain9 : c0 * kappa t / t ≤ 9 * sigmaQ t := by
      rw [hc0kt]
      have h := mul_le_mul htphi hS3 hS0 (by linarith)
      linarith only [h]
    have hmono : Real.log (2 * Q) ^ A ≤ Real.log 8 ^ A :=
      Real.rpow_le_rpow hlog2Q.le (Real.log_le_log (by linarith) (by linarith)) hA.le
    have hlq4 : Real.log Q ≤ Real.log 4 := Real.log_le_log hQpos (by linarith)
    have habs := abs_sub_le_add (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter
      (fun n => Nat.Coprime n t), (moebius n : ℝ) / kappa n * Real.log (Q / n))
      (c0 * kappa t / t)
    rw [abs_of_nonneg hmain0] at habs
    refine le_trans habs ?_
    rw [le_div_iff₀ hlog2QA]
    have hK0 : (0 : ℝ) ≤ (1 + Real.log 4) ^ 2 + 9 := by positivity
    have p0 : (1 + Real.log Q) ^ 2 ≤ (1 + Real.log 4) ^ 2 := by
      nlinarith only [hlq4, hlogQ0, hlog4]
    have p1 : (1 + Real.log Q) ^ 2 + c0 * kappa t / t
        ≤ ((1 + Real.log 4) ^ 2 + 9) * sigmaQ t := by
      nlinarith only [p0, hmain9, hsig1, hlog4, hlogQ0]
    have p2 : ((1 + Real.log 4) ^ 2 + 9) * sigmaQ t * Real.log (2 * Q) ^ A
        ≤ ((1 + Real.log 4) ^ 2 + 9) * sigmaQ t * Real.log 8 ^ A :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg hK0 hsig0.le)
    have p3 : ((1 + Real.log Q) ^ 2 + c0 * kappa t / t) * Real.log (2 * Q) ^ A
        ≤ ((1 + Real.log 4) ^ 2 + 9) * sigmaQ t * Real.log (2 * Q) ^ A :=
      mul_le_mul_of_nonneg_right p1 hlog2QA.le
    have p4 : ((1 + Real.log 4) ^ 2 + 9) * Real.log 8 ^ A * sigmaQ t
        ≤ (((1 + Real.log 4) ^ 2 + 9) * Real.log 8 ^ A + 4 * CD * 2 ^ A
          + 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
          + 24 * (4 * A) ^ A) * sigmaQ t := by
      have hrest : (0 : ℝ) ≤ 4 * CD * 2 ^ A
          + 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
          + 24 * (4 * A) ^ A := by positivity
      nlinarith only [hrest, hsig0]
    have p5 : (|∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          (moebius n : ℝ) / kappa n * Real.log (Q / n)| + c0 * kappa t / t)
          * Real.log (2 * Q) ^ A
        ≤ ((1 + Real.log Q) ^ 2 + c0 * kappa t / t) * Real.log (2 * Q) ^ A :=
      mul_le_mul_of_nonneg_right (by linarith only [htriv]) hlog2QA.le
    linarith only [p2, p3, p4, p5]
  -- ═══ the main regime `Q ≥ 4` ═══
  · have hs0 : (0 : ℝ) < Q ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hspow : (Q ^ (1/2 : ℝ)) ^ 2 = Q := by
      rw [rpow_pow_nat hQpos.le, show (1/2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have hQ12 : Q ^ (1/2 : ℝ) ≤ Q := by
      have h := Real.rpow_le_rpow_of_exponent_le hQ (show (1/2 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hs2 : (2 : ℝ) ≤ Q ^ (1/2 : ℝ) := by
      refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hs0.le ?_
      rw [hspow]
      nlinarith only [hbig]
    set D : ℕ := ⌊Q ^ (1/2 : ℝ)⌋₊ with hDdef
    have hDle : ((D : ℕ) : ℝ) ≤ Q ^ (1/2 : ℝ) := Nat.floor_le hs0.le
    have hDgt : Q ^ (1/2 : ℝ) < ((D : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hDhalf : Q ^ (1/2 : ℝ) / 2 ≤ ((D : ℕ) : ℝ) := by linarith
    have hD1 : 1 ≤ D := by
      have h : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by linarith
      exact_mod_cast h
    have hDN : D ≤ ⌊Q⌋₊ := by rw [hDdef]; exact Nat.floor_mono hQ12
    have hD0 : (0 : ℝ) < (D : ℝ) := by
      have h : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast hD1
      linarith
    have hq40 : (0 : ℝ) < Q ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hQpos _
    have hDpow0 : (0 : ℝ) < (D : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hD0 _
    have hDhalfpow : Q ^ (1/4 : ℝ) / 2 ≤ (D : ℝ) ^ (1/2 : ℝ) := by
      have e1 : (Q ^ (1/2 : ℝ) / 2) ^ (1/2 : ℝ) ≤ (D : ℝ) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hDhalf (by norm_num)
      have e2 : (Q ^ (1/2 : ℝ) / 2) ^ (1/2 : ℝ) = Q ^ (1/4 : ℝ) / (2 : ℝ) ^ (1/2 : ℝ) := by
        rw [Real.div_rpow hs0.le (by norm_num), ← Real.rpow_mul hQpos.le]
        norm_num
      have e3 : (2 : ℝ) ^ (1/2 : ℝ) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
          (show (1/2 : ℝ) ≤ 1 by norm_num)
        rwa [Real.rpow_one] at h
      have e4 : (0 : ℝ) < (2 : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have e5 : Q ^ (1/4 : ℝ) / 2 ≤ Q ^ (1/4 : ℝ) / (2 : ℝ) ^ (1/2 : ℝ) :=
        div_le_div_of_nonneg_left hq40.le e4 e3
      linarith only [e1, e2.le, e2.ge, e5]
    have hDinv : (D : ℝ) ^ (-(1/2) : ℝ) = 1 / (D : ℝ) ^ (1/2 : ℝ) := by
      rw [Real.rpow_neg hD0.le]
      ring
    -- the weighted swap
    rw [sum_coprime_moebius_div_kappa_swap_mul t ⌊Q⌋₊ (fun n => Real.log (Q / (n : ℝ)))]
    have hcongr : ∀ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t),
        (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ) * Real.log (Q / ((d * f : ℕ) : ℝ))
        = (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)) := by
      intro d _
      congr 1
      refine Finset.sum_congr rfl fun f _ => ?_
      congr 2
      push_cast
      rw [div_div]
    rw [Finset.sum_congr rfl hcongr]
    have hFD : ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter (fun d => d ≤ D)
        = (Finset.Icc 1 D).filter (fun d => Nat.Coprime d t) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, hc⟩, hxD⟩
        exact ⟨⟨h1, hxD⟩, hc⟩
      · rintro ⟨⟨h1, hxD⟩, hc⟩
        exact ⟨⟨⟨h1, le_trans hxD hDN⟩, hc⟩, hxD⟩
    have hw : ∀ d : ℕ, 1 ≤ d →
        |(moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)| ≤ 1 / (d : ℝ) ^ 2 := by
      intro d hd1
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hkpos : (0 : ℝ) < kappa d := lt_of_lt_of_le hd0 (le_kappa d hd1)
      have hmu2 : (moebius d : ℝ) ^ 2 ≤ 1 := by
        have h := moebius_sq (n := d)
        by_cases hsq : Squarefree d
        · rw [if_pos hsq] at h
          have hh : ((moebius d : ℝ)) ^ 2 = 1 := by exact_mod_cast h
          linarith
        · rw [moebius_eq_zero_of_not_squarefree hsq]
          norm_num
      have hmu0 : (0 : ℝ) ≤ (moebius d : ℝ) ^ 2 := sq_nonneg _
      rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hmu2, hmu0, hd0, hkpos, le_kappa d hd1]
    -- the decomposition
    have hdecomp : ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t),
          (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ))
          - c0 * kappa t / t
        = (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
              * ((∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                  (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
                - ((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)))
          + (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
              (fun d => ¬ d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
                * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                    (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
          + ((∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
              (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
                * (((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)))
            - c0 * kappa t / t) := by
      have h1 := Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)) (fun d => d ≤ D)
        (fun d => (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
      have h2 : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
              * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                  (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ))
          = (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
              (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
                * ((∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                    (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
                  - ((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)))
            + ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
              (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
                * (((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun d _ => by ring
      linarith only [h1, h2.le, h2.ge]
    rw [hdecomp]
    -- P3: the main term against T7
    have hWM : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * (((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ))
        = (t : ℝ) / Nat.totient t * ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d t),
            (moebius d : ℝ) ^ 2 / (kappa d * (Nat.totient d : ℝ)) := by
      rw [hFD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, hc⟩ := hd
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hkpos : (0 : ℝ) < kappa d := lt_of_lt_of_le hd0 (le_kappa d hd1)
      have hphid : (0 : ℝ) < (Nat.totient d : ℝ) := by
        have : 0 < Nat.totient d := Nat.totient_pos.mpr hd1
        exact_mod_cast this
      have hphit : (0 : ℝ) < (Nat.totient t : ℝ) := by
        have : 0 < Nat.totient t := Nat.totient_pos.mpr ht
        exact_mod_cast this
      have htot : (Nat.totient (d * t) : ℝ) = (Nat.totient d : ℝ) * (Nat.totient t : ℝ) := by
        rw [Nat.totient_mul hc]
        push_cast
        ring
      have hcast : ((d * t : ℕ) : ℝ) = (d : ℝ) * (t : ℝ) := by push_cast; ring
      rw [htot, hcast]
      field_simp
      try ring
    have hP3 : |(∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * (((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ))) - c0 * kappa t / t|
        ≤ 3 * sigmaQ t * (2 * (D : ℝ) ^ (-(1/2) : ℝ)) := by
      rw [hWM, hc0kt, ← mul_sub, abs_mul, abs_of_nonneg htphi0]
      have h1 := htail D hD1
      have h2 : |∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d t),
            (moebius d : ℝ) ^ 2 / (kappa d * (Nat.totient d : ℝ))
          - coprimeSeries (fun n => (moebius n : ℝ) ^ 2 / (kappa n * (Nat.totient n : ℝ))) t|
          ≤ 2 * (D : ℝ) ^ (-(1/2) : ℝ) := by
        rw [abs_sub_comm]
        exact h1
      exact mul_le_mul htphi h2 (abs_nonneg _) (by linarith)
    -- P1: H6d on the near range
    have hP1 : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ((∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
              - ((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ))|
        ≤ 4 * (CD * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A) := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => d ≤ D),
          |(moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ((∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
              - ((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ))|
            ≤ sigmaQ d / (d : ℝ) ^ 2 * (CD * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨⟨hd1, hdN⟩, hc⟩, hdD⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hdR : (d : ℝ) ≤ Q ^ (1/2 : ℝ) := le_trans (by exact_mod_cast hdD) hDle
        have hsigd : (1 : ℝ) ≤ sigmaQ d := one_le_sigmaQ d hd1
        have hrhs0 : (0 : ℝ) ≤ sigmaQ d / (d : ℝ) ^ 2
            * (CD * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A) := by
          refine mul_nonneg (div_nonneg (by linarith) (by positivity)) ?_
          exact div_nonneg (mul_nonneg (mul_nonneg hCD.le (by linarith only [hsig1])) h2A.le)
            hlog2QA.le
        by_cases hdsq : Squarefree d
        · have hdt1 : 1 ≤ d * t := Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by omega))
          have hsqdt : Squarefree (d * t) := (Nat.squarefree_mul hc).mpr ⟨hdsq, hts⟩
          obtain ⟨hQd, _⟩ := le_sqrt_div_log hQ hd1 hdR
          have hDb := hD6 (d * t) hsqdt (Q / (d : ℝ)) hQd
          rw [Nat.floor_div_natCast Q d] at hDb
          have hsigdt : (1 : ℝ) ≤ sigmaQ (d * t) := one_le_sigmaQ (d * t) hdt1
          have hCsig : (0 : ℝ) < CD * sigmaQ (d * t) := by nlinarith only [hCD, hsigdt]
          have hmul := sigmaQ_mul_le d t hd1 ht
          have hnear1 : |(∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter
                (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
              - ((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)|
              ≤ CD * sigmaQ d * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A := by
            have h1 : CD * sigmaQ (d * t) / Real.log (2 * (Q / (d : ℝ))) ^ A
                ≤ CD * sigmaQ (d * t) * 2 ^ A / Real.log (2 * Q) ^ A :=
              div_log_pow_near hA hCsig hQ hd1 hdR
            have h2 : CD * sigmaQ (d * t) * 2 ^ A / Real.log (2 * Q) ^ A
                ≤ CD * sigmaQ d * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A := by
              rw [div_le_div_iff_of_pos_right hlog2QA]
              have hstep2 := mul_le_mul_of_nonneg_left hmul (mul_nonneg hCD.le h2A.le)
              nlinarith only [hstep2]
            linarith only [hDb, h1, h2]
          rw [abs_mul]
          have hwd := hw d hd1
          have hAbs0 : (0 : ℝ) ≤ |(∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter
              (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
            - ((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)| := abs_nonneg _
          have hstep := mul_le_mul hwd hnear1 hAbs0 (by positivity)
          refine le_trans hstep (le_of_eq ?_)
          field_simp
          try ring
        · rw [moebius_eq_zero_of_not_squarefree hdsq, Int.cast_zero, zero_pow (by norm_num),
            zero_div, zero_mul, abs_zero]
          exact hrhs0
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      have hsub : ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => d ≤ D) ⊆ Finset.Icc 1 D := by
        intro x hx
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hx
        rw [Finset.mem_Icc]
        exact ⟨hx.1.1.1, hx.2⟩
      have hsum : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => d ≤ D), sigmaQ d / (d : ℝ) ^ 2 ≤ 4 := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => ?_))
          (sum_sigmaQ_div_sq_le D)
        obtain ⟨hi1, _⟩ := Finset.mem_Icc.mp hi
        have := one_le_sigmaQ i hi1
        have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
        positivity
      refine mul_le_mul_of_nonneg_right hsum ?_
      exact div_nonneg (mul_nonneg (mul_nonneg hCD.le (by linarith only [hsig1])) h2A.le)
        hlog2QA.le
    -- P2: the far range
    have hP2 : |∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => ¬ d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ))|
        ≤ 2 / Q ^ (1/2 : ℝ) * (1 + Real.log Q) ^ 2 := by
      have hterm : ∀ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => ¬ d ≤ D),
          |(moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
                (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ))|
            ≤ 1 / (d : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨⟨hd1, hdN⟩, _⟩, _⟩ := hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
        have hdQ : (d : ℝ) ≤ Q := le_trans (by exact_mod_cast hdN) hNQ
        have hQd : (1 : ℝ) ≤ Q / (d : ℝ) := (one_le_div hd0).mpr hdQ
        have htr := sum_abs_moebius_div_log_le hQd
        rw [Nat.floor_div_natCast Q d] at htr
        have hlogd : Real.log (Q / (d : ℝ)) ≤ Real.log Q := by
          refine Real.log_le_log (by positivity) ?_
          rw [div_le_iff₀ hd0]
          nlinarith only [hd1R, hQpos]
        have hlogd0 : (0 : ℝ) ≤ Real.log (Q / (d : ℝ)) := Real.log_nonneg hQd
        have hsqle : (1 + Real.log (Q / (d : ℝ))) ^ 2 ≤ (1 + Real.log Q) ^ 2 := by
          nlinarith only [hlogd, hlogd0, hlogQ0]
        have hTb : |∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
            (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ))|
            ≤ (1 + Real.log Q) ^ 2 := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => abs_nonneg _)) ?_
          linarith only [htr, hsqle]
        rw [abs_mul]
        exact mul_le_mul (hw d hd1) hTb (abs_nonneg _) (by positivity)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      have hsub : ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => ¬ d ≤ D) ⊆ Finset.Ioo D (⌊Q⌋₊ + 1) := by
        intro x hx
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hx
        rw [Finset.mem_Ioo]
        exact ⟨by omega, by omega⟩
      have hsum : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
            (fun d => ¬ d ≤ D), 1 / (d : ℝ) ^ 2 ≤ 2 / Q ^ (1/2 : ℝ) := by
        have h1 : ∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
              (fun d => ¬ d ≤ D), 1 / (d : ℝ) ^ 2
            ≤ ∑ d ∈ Finset.Ioo D (⌊Q⌋₊ + 1), 1 / (d : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        have h2 : ∑ d ∈ Finset.Ioo D (⌊Q⌋₊ + 1), 1 / (d : ℝ) ^ 2
            = ∑ d ∈ Finset.Ioo D (⌊Q⌋₊ + 1), (((d : ℝ)) ^ 2)⁻¹ :=
          Finset.sum_congr rfl fun d _ => one_div _
        have h3 : ∑ i ∈ Finset.Ioo D (⌊Q⌋₊ + 1), (((i : ℝ)) ^ 2)⁻¹ ≤ 2 / ((D : ℕ) + 1) :=
          sum_Ioo_inv_sq_le D (⌊Q⌋₊ + 1)
        have h4 : (2 : ℝ) / (((D : ℕ) : ℝ) + 1) ≤ 2 / Q ^ (1/2 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hs0 hDgt.le
        rw [h2] at h1
        linarith only [h1, h3, h4]
      exact mul_le_mul_of_nonneg_right hsum (by positivity)
    -- the two tails against the A4 helpers
    have hA4sq := one_add_log_sq_mul_log_rpow_le A hA hQ
    have hA4a := log_rpow_le_rpow_quarter A hA (show (1 : ℝ) ≤ 2 * Q by linarith)
    have hsplit24 : (2 * Q) ^ (1/4 : ℝ) = (2 : ℝ) ^ (1/4 : ℝ) * Q ^ (1/4 : ℝ) :=
      Real.mul_rpow (by norm_num) hQpos.le
    have h2quarter : (2 : ℝ) ^ (1/4 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1/4 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hLA : Real.log (2 * Q) ^ A ≤ (4 * A) ^ A * (2 * Q ^ (1/4 : ℝ)) := by
      refine le_trans hA4a ?_
      rw [hsplit24]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2quarter hq40.le) hk1.le
    have hq4s : Q ^ (1/4 : ℝ) ≤ Q ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
    have hP2C : 2 / Q ^ (1/2 : ℝ) * (1 + Real.log Q) ^ 2
        ≤ 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
            * sigmaQ t / Real.log (2 * Q) ^ A := by
      have hEq : 2 / Q ^ (1/2 : ℝ) * (1 + Real.log Q) ^ 2
          = (2 * (1 + Real.log Q) ^ 2) / Q ^ (1/2 : ℝ) := by ring
      rw [hEq, div_le_div_iff₀ hs0 hlog2QA]
      have p1 : 2 * ((1 + Real.log Q) ^ 2 * Real.log (2 * Q) ^ A)
          ≤ 2 * (2 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1)
              + (4 * (A + 2)) ^ (A + 2)) * Q ^ (1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hA4sq (by norm_num)
      have p2 : 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
            * Q ^ (1/4 : ℝ)
          ≤ 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
            * Q ^ (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left hq4s (by linarith only [hk1, hk2, hk3])
      have p3 : 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
            * Q ^ (1/2 : ℝ)
          ≤ 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
            * sigmaQ t * Q ^ (1/2 : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hsig1
          (show (0 : ℝ) ≤ 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1)
            + (4 * (A + 2)) ^ (A + 2)) by linarith only [hk1, hk2, hk3])
        nlinarith only [h, hs0]
      linarith only [p1, p2, p3]
    have hP3C : 3 * sigmaQ t * (2 * (D : ℝ) ^ (-(1/2) : ℝ))
        ≤ 24 * (4 * A) ^ A * sigmaQ t / Real.log (2 * Q) ^ A := by
      rw [hDinv]
      have hEq : 3 * sigmaQ t * (2 * (1 / (D : ℝ) ^ (1/2 : ℝ)))
          = (6 * sigmaQ t) / (D : ℝ) ^ (1/2 : ℝ) := by ring
      rw [hEq, div_le_div_iff₀ hDpow0 hlog2QA]
      have p1 : 6 * sigmaQ t * Real.log (2 * Q) ^ A
          ≤ 6 * sigmaQ t * ((4 * A) ^ A * (2 * Q ^ (1/4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hLA (by linarith)
      have p2 : 24 * (4 * A) ^ A * sigmaQ t * (Q ^ (1/4 : ℝ) / 2)
          ≤ 24 * (4 * A) ^ A * sigmaQ t * (D : ℝ) ^ (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left hDhalfpow
          (mul_nonneg (by linarith only [hk1]) hsig0.le)
      linarith only [p1, p2]
    have hextra : (0 : ℝ) ≤ ((1 + Real.log 4) ^ 2 + 9) * Real.log 8 ^ A * sigmaQ t
        / Real.log (2 * Q) ^ A :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) hlog8.le)
        (by linarith only [hsig1])) hlog2QA.le
    have habs := abs_add_add_le
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
        (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ((∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
            - ((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)))
      (∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
        (fun d => ¬ d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
          * ∑ f ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun f => Nat.Coprime f (d * t)),
              (moebius f : ℝ) / (f : ℝ) * Real.log (Q / (d : ℝ) / (f : ℝ)))
      ((∑ d ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Nat.Coprime d t)).filter
          (fun d => d ≤ D), (moebius d : ℝ) ^ 2 / ((d : ℝ) * kappa d)
            * (((d * t : ℕ) : ℝ) / (Nat.totient (d * t) : ℝ)))
        - c0 * kappa t / t)
    have hringid : (((1 + Real.log 4) ^ 2 + 9) * Real.log 8 ^ A + 4 * CD * 2 ^ A
          + 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
          + 24 * (4 * A) ^ A) * sigmaQ t / Real.log (2 * Q) ^ A
        = ((1 + Real.log 4) ^ 2 + 9) * Real.log 8 ^ A * sigmaQ t / Real.log (2 * Q) ^ A
          + 4 * (CD * sigmaQ t * 2 ^ A / Real.log (2 * Q) ^ A)
          + 4 * ((4 * A) ^ A + 2 * (4 * (A + 1)) ^ (A + 1) + (4 * (A + 2)) ^ (A + 2))
              * sigmaQ t / Real.log (2 * Q) ^ A
          + 24 * (4 * A) ^ A * sigmaQ t / Real.log (2 * Q) ^ A := by
      ring
    rw [hringid]
    linarith only [habs, hP1, hP2, hP2C, hP3, hP3C, hextra]

/-- **H6e in the frozen `∃ c₀` form** — a one-line corollary of the NAMED row, with the
witness `c0` and `0 < c0` from `one_le_c0`. The named form is the one the H2 wave consumes
(its row H7c reads H6e's main term AS `c0`); the `∃` form exports no witness and is kept only
because it is the shape the W6b-H freeze froze. -/
theorem coprime_sum_moebius_div_kappa_log_exists :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ t : ℕ, Squarefree t → ∀ Q : ℝ, 1 ≤ Q →
    |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
        (moebius n : ℝ) / kappa n * Real.log (Q / n)
        - c₀ * kappa t / t| ≤ C * sigmaQ t / Real.log (2 * Q) ^ A :=
  ⟨c0, lt_of_lt_of_le zero_lt_one one_le_c0,
    fun A hA => coprime_sum_moebius_div_kappa_log_eq A hA⟩

/-! ## §2(b) binder-shape rows

The off-line values are the sub-freeze's measured receipts. C1 at `N = 6` is the ONE EXACT
row (`49/20 − 11/12 − 1/2 − 1/5 + 1/6 = 1`). T6 at `r = 6` has both sides `ρ₀/2`; H5a at
`(6, 100)` has count `31`, main term `30.396` and RHS `4·10·3.2397 = 129.6`.

H6d at `(2, 100)` reads `Σ_{n ≤ 100 odd}(μ(n)/n)log(100/n) = 1.9721` against `t/φ(t) = 2`,
and H6e at `(2, 100)` reads `2.3446` against `c₀·κ(2)/2 = 2.4674`; both rows land in this
cut, so both binder-shape `example`s are written out below. -/

example : ∑ n ∈ Finset.Icc 1 6, (moebius n : ℝ) / n
    * ∑ m ∈ Finset.Icc 1 (6 / n), (1 : ℝ) / m = 1 := by
  have h1 : moebius 1 = 1 := isMultiplicative_moebius.map_one
  have h2 : moebius 2 = -1 := moebius_apply_prime Nat.prime_two
  have h3 : moebius 3 = -1 := moebius_apply_prime Nat.prime_three
  have h4 : moebius 4 = 0 := moebius_eq_zero_of_not_squarefree (by decide)
  have h5 : moebius 5 = -1 := moebius_apply_prime (by norm_num)
  have h6 : moebius 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num,
      isMultiplicative_moebius.map_mul_of_coprime (by decide), h2, h3]
    norm_num
  have e1 : Finset.Icc 1 1 = ({1} : Finset ℕ) := by decide
  have e2 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have e3 : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have e6 : Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) := by decide
  rw [e6]
  norm_num [e1, e2, e3, e6, h1, h2, h3, h4, h5, h6]

example : (Nat.totient 6 : ℝ) / ((6 : ℕ) : ℝ)
      * coprimeSeries (fun n => (moebius n : ℝ) / (n : ℝ) ^ 2) 6
    = rho0 * (((6 : ℕ) : ℝ) / kappa 6) :=
  totient_div_mul_coprimeSeries_moebius_div_sq 6 (by norm_num)

example : ∃ C : ℝ, 0 < C ∧
    |∑ m ∈ (Finset.Icc 1 ⌊(100 : ℝ)⌋₊).filter (fun m => Nat.Coprime m 6),
        (moebius m : ℝ) ^ 2 - rho0 * (((6 : ℕ) : ℝ) / kappa 6) * 100|
      ≤ C * (100 : ℝ) ^ (1/2 : ℝ) * sigmaQ 6 := by
  obtain ⟨C, hC, h⟩ := sqf_coprime_count_eq
  exact ⟨C, hC, h 6 (by norm_num) 100 (by norm_num)⟩

example (G : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 10).filter (fun m => Nat.Coprime m 2), (moebius m : ℝ) * G m
      = ∑ d ∈ (Finset.Icc 1 10).filter (fun d => d.primeFactors ⊆ (2 : ℕ).primeFactors),
          ∑ e ∈ Finset.Icc 1 (10 / d), (moebius e : ℝ) * G (d * e) :=
  sum_coprime_moebius_eq_sum_smooth 2 10 (by norm_num) G

example : ∃ C : ℝ, 0 < C ∧
    |∑ n ∈ (Finset.Icc 1 ⌊(100 : ℝ)⌋₊).filter (fun n => Nat.Coprime n 2),
        (moebius n : ℝ) / n * Real.log ((100 : ℝ) / n)
        - ((2 : ℕ) : ℝ) / Nat.totient 2|
      ≤ C * sigmaQ 2 / Real.log (2 * (100 : ℝ)) ^ (2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := coprime_sum_moebius_div_log_eq 2 (by norm_num)
  exact ⟨C, hC, h 2 Nat.prime_two.squarefree 100 (by norm_num)⟩

example : ∃ C : ℝ, 0 < C ∧
    |∑ n ∈ (Finset.Icc 1 ⌊(100 : ℝ)⌋₊).filter (fun n => Nat.Coprime n 2),
        (moebius n : ℝ) / kappa n * Real.log ((100 : ℝ) / n)
        - c0 * kappa 2 / ((2 : ℕ) : ℝ)|
      ≤ C * sigmaQ 2 / Real.log (2 * (100 : ℝ)) ^ (2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := coprime_sum_moebius_div_kappa_log_eq 2 (by norm_num)
  exact ⟨C, hC, h 2 Nat.prime_two.squarefree 100 (by norm_num)⟩

end Salt.SW
