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
  weighted partial summation. **These are two of the six flagged rows, now closed.**
* **C1** — the exact harmonic identity `Σ_{n ≤ N}(μ(n)/n)·H(⌊N/n⌋) = 1`.
* **S1** — the `t`-smooth convolution `Σ_{m ≤ X,(m,t)=1} μ(m)G(m) =
  Σ_{d ≤ X smooth} Σ_{e ≤ X/d} μ(e)G(de)` — and **S2**, the smooth partial sum against its
  Euler product, `Σ_{d ≤ X smooth} 1/d ≤ t/φ(t)`.
* Two PUBLIC helpers the next wave (H2) consumes: `summable_moebius_sq_div_kappa_totient`
  and `log_rpow_le_rpow_quarter` (`(log x)^A ≤ (4A)^A x^{1/4}`).

## ⚠ THE HONEST LABEL — what this file does NOT prove

**Eight of the cut's twenty-two frozen rows are ABSENT, and their absence is recorded rather
than implied** (`docs/blueprints/flags.md`, the 09-05 W6b-H1b entries). Rows ABSENT:
**C2** (`abs_sum_moebius_mul_log_floor_ratio_le`), **C3**
(`abs_sum_moebius_div_mul_log_div_sub_one_le`), **H6c**
(`abs_sum_moebius_mul_log_div_add_one_le`), **S3**
(`div_totient_sub_sum_smooth_inv_le`), **S4** (`abs_coprime_sum_moebius_div_le`), **H6d**
(`coprime_sum_moebius_div_log_eq`), **H6f** (`coprime_sum_moebius_div_kappa_le`), **H6e**
(`coprime_sum_moebius_div_kappa_log_eq`). Four of the six H-freeze rows therefore remain
open: only **H5a and H5c land here**. A consumer must read this file's declaration list, not
the wave's label, for what is available.

**The second input is still missing.** C2 (the sawtooth-log piece, by a blockwise discrete
Abel over the fibres of `n ↦ ⌊Q/n⌋₊`) is what C3 — and through C3, H6c, H6d and H6e — is
gated on; S3 needs the smooth series `Σ'_{d smooth} d^{−s} = ∏_{p ∣ t}(1 − p^{−s})^{−1}` in
the OTHER direction (S2's inequality goes the easy way and needs only an injection; S3 needs
the sum's exact value, hence a bijection and a limit), and S4/H6f are gated on it. None of
this is a statement
defect: **no frozen statement of this cut is believed false.** The flags record the cost,
not a contradiction.

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

**Two mutants were MEASURED and STRUCK** and are recorded in P2's and C2's — here, P2's —
docstring as NOT controls: P2 with `X^{1/4} → X^0`, and P2 with `σ(r) → 1`. C2's struck
mutant (dropping the `+ 1` in the log) is recorded in this wave's flag entry instead, since
C2 itself is absent.

**F6** (no net numerator log): every frozen statement here is log-free (T1–T7, P1, P2, S1,
C1) or carries its logs in a bounded one-variable pair (H5a's `√M·σ`, H5c's
`(1 + |log M + α|)(1 + |log M + β|)`). The route's numerator logs — `(1 + log Q)/√Q` in
C3's `D`-tail and `(1 + log Q)²` in H6d's far tail — belong to the absent rows.

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

/-! ## §2(b) binder-shape rows

The off-line values are the sub-freeze's measured receipts. C1 at `N = 6` is the ONE EXACT
row (`49/20 − 11/12 − 1/2 − 1/5 + 1/6 = 1`). T6 at `r = 6` has both sides `ρ₀/2`; H5a at
`(6, 100)` has count `31`, main term `30.396` and RHS `4·10·3.2397 = 129.6`.

The sub-freeze also asked for H6d at `(2, 100)` (`Σ_{n ≤ 100 odd}(μ(n)/n)log(100/n) =
1.9721` vs `t/φ(t) = 2`) and H6e at `(2, 100)` (`2.3446` vs `c₀·κ(2)/2 = 2.4674`). **Both
rows are ABSENT from this cut**, so those two example rows cannot be written; the numerals
are printed here so the receipts are not lost. -/

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

end Salt.SW
