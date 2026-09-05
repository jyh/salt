-- Salt/SW/GrahamHard2.lean (NEW; imports Salt.SW.GrahamHard)
import Salt.SW.GrahamHard

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

end Salt.SW
