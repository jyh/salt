/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.GrahamHard2

/-!
# B2 W2 — Jutila's Lemma 5 (L5), the `r`-average, as a UNIFORM lower bound

`(6/π²)·(φ(q)/q)·log R ≤ Σ'_{r ≤ R} 1/r` (the sum over square-free `r` coprime to `q`), for
every `q ≥ 1` and every real `R ≥ 1` — no `R₀`, no `log R ≥ (log q)^{1/2}`: the uniform
inequality is proved outright by the two injections below; Jutila's p.49 asymptotic is never
consumed. The two injections:
`log R ≤ Σ_{n ≤ R} 1/n ≤ (q/φ(q))·Σ_{(m,q)=1} 1/m ≤ (q/φ(q))·ζ(2)·Σ_{sf,(a,q)=1} 1/a`
(`n = d·m` with `d` `q`-smooth against the LANDED `sum_smooth_inv_le`; `m = b²·a` with `a`
square-free against `hasSum_zeta_two`). `sum_coprime_eq_moebius_multiples` is NOT consumed.

## The measured control (the design cut's §2)

At `q = 1`, `R = 10⁶`: the square-free harmonic sum is `9.4427` and `(6/π²)·log 10⁶ = 8.3988`,
so the inequality holds with room; the mutation `6/π² → 1` gives `13.8155 > 9.4427` and FAILS.
Over a 132-point grid (`q ∈ {1, 2, 3, 4, 6, 10, 12, 30, 210, 2310, 30030}` × `R` up to `10⁵`)
every point holds, the worst rhs/lhs ratio being `1.1491` at `(q, R) = (1, 10⁵)`.  The two
injections at `q = 30`, `N = 1000`: `log N = 6.9078 ≤ H = 7.4855 ≤ (q/φ)·H_cop = 9.1273` and
`H_cop = 2.4339 ≤ ζ(2)·H_sf = 3.9136`.

## The honest label

L5 is stated and proved here as a UNIFORM inequality with the explicit constant `6/π²`; no
asymptotic of Jutila's p.49 is consumed, and there is no additive constant and no threshold
`R₀`.  The binder `1 ≤ q` is load-bearing on the two injection rows (at `q = 0` the coprime
filter collapses to `{1}` and the smooth filter to `{1}`, and `(0 : ℝ)/φ(0) = 0`).
-/

open ArithmeticFunction

noncomputable section
namespace Salt.SW

theorem log_le_sum_inv_Icc_floor {R : ℝ} (hR : 1 ≤ R) :
    Real.log R ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, (1 : ℝ) / n := by
  have h := log_le_harmonic_floor R (by linarith)
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa only [one_div] using h

theorem exists_smooth_mul_coprime {q : ℕ} (hq : 1 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∃ d m : ℕ, d * m = n ∧ d.primeFactors ⊆ q.primeFactors ∧ Nat.Coprime m q := by
  have hq0 : q ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hqn0 : q ^ n ≠ 0 := pow_ne_zero n hq0
  have hdn : Nat.gcd n (q ^ n) ∣ n := Nat.gcd_dvd_left _ _
  have hdqn : Nat.gcd n (q ^ n) ∣ q ^ n := Nat.gcd_dvd_right _ _
  refine ⟨Nat.gcd n (q ^ n), n / Nat.gcd n (q ^ n), Nat.mul_div_cancel' hdn, ?_, ?_⟩
  · rw [← Nat.primeFactors_pow q hn0]
    exact Nat.primeFactors_mono hdqn hqn0
  · by_contra hnc
    obtain ⟨p, hp, hpm, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hvn : n.factorization p < n := Nat.factorization_lt p hn0
    have h3 : p ^ n.factorization p ∣ q ^ n :=
      (pow_dvd_pow p hvn.le).trans (pow_dvd_pow_of_dvd hpq n)
    have h4 : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have h5 : p ^ n.factorization p ∣ Nat.gcd n (q ^ n) := Nat.dvd_gcd h4 h3
    have h6 : Nat.gcd n (q ^ n) * p ∣ n := by
      obtain ⟨k, hk⟩ := hpm
      refine ⟨k, ?_⟩
      calc n = Nat.gcd n (q ^ n) * (n / Nat.gcd n (q ^ n)) := (Nat.mul_div_cancel' hdn).symm
        _ = Nat.gcd n (q ^ n) * (p * k) := by rw [hk]
        _ = Nat.gcd n (q ^ n) * p * k := (mul_assoc _ _ _).symm
    have h7 : p ^ (n.factorization p + 1) ∣ n := by
      rw [pow_succ]
      exact dvd_trans (mul_dvd_mul h5 dvd_rfl) h6
    have h8 := (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).mp h7
    omega

theorem sum_inv_Icc_le_coprime_mul_smooth {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n
      ≤ (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m)
        * ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ q.primeFactors),
            (1 : ℝ) / d := by
  set M := (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q) with hM
  set D := (Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ q.primeFactors) with hD
  have hsub : Finset.Icc 1 N ⊆ (M ×ˢ D).image (fun p : ℕ × ℕ => p.1 * p.2) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨d, m, hdm, hds, hmc⟩ := exists_smooth_mul_coprime hq hn.1
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp only [Nat.zero_mul] at hdm; omega
      · exact h
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp only [Nat.mul_zero] at hdm; omega
      · exact h
    have hddvd : d ∣ n := ⟨m, hdm.symm⟩
    have hmdvd : m ∣ n := ⟨d, by rw [← hdm]; ring⟩
    have hdN : d ≤ N := le_trans (Nat.le_of_dvd (by omega) hddvd) hn.2
    have hmN : m ≤ N := le_trans (Nat.le_of_dvd (by omega) hmdvd) hn.2
    refine Finset.mem_image.mpr ⟨(m, d), ?_, ?_⟩
    · rw [Finset.mem_product, hM, hD]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmN⟩, hmc⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hdN⟩, hds⟩⟩
    · simpa using (Nat.mul_comm m d).trans hdm
  calc ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n
      ≤ ∑ n ∈ (M ×ˢ D).image (fun p : ℕ × ℕ => p.1 * p.2), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
    _ ≤ ∑ p ∈ M ×ˢ D, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) :=
        Finset.sum_image_le_of_nonneg fun u _ => by positivity
    _ = (∑ m ∈ M, (1 : ℝ) / m) * ∑ d ∈ D, (1 : ℝ) / d := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun d _ => ?_
        dsimp only
        push_cast
        rw [← one_div_mul_one_div]

theorem sum_inv_Icc_le_div_totient_mul_coprime {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n
      ≤ (q : ℝ) / Nat.totient q
        * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m := by
  have hcop : (0 : ℝ) ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m :=
    Finset.sum_nonneg fun m _ => by positivity
  calc ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n
      ≤ (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m)
        * ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ q.primeFactors),
            (1 : ℝ) / d := sum_inv_Icc_le_coprime_mul_smooth hq N
    _ ≤ (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m)
        * ((q : ℝ) / Nat.totient q) :=
        mul_le_mul_of_nonneg_left (sum_smooth_inv_le q N hq) hcop
    _ = (q : ℝ) / Nat.totient q
        * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m := mul_comm _ _

theorem sum_coprime_inv_le_zeta_two_mul_sqf (q N : ℕ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m
      ≤ Real.pi ^ 2 / 6
        * ∑ a ∈ (Finset.Icc 1 N).filter (fun a => Squarefree a ∧ Nat.Coprime a q),
            (1 : ℝ) / a := by
  set A := (Finset.Icc 1 N).filter (fun a => Squarefree a ∧ Nat.Coprime a q) with hA
  have hzeta : ∑ b ∈ Finset.Icc 1 N, (1 : ℝ) / (b : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum (Finset.Icc 1 N) (fun b _ => by positivity) hasSum_zeta_two
  have hAnn : (0 : ℝ) ≤ ∑ a ∈ A, (1 : ℝ) / a := Finset.sum_nonneg fun a _ => by positivity
  have hsub : (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q)
      ⊆ (A ×ˢ Finset.Icc 1 N).image (fun p : ℕ × ℕ => p.2 ^ 2 * p.1) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmN⟩, hmc⟩ := hm
    obtain ⟨a, b, ha0, hb0, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < m)
    have hadvd : a ∣ m := ⟨b ^ 2, by rw [← hab]; ring⟩
    have hbdvd : b ∣ m := ⟨b * a, by rw [← hab]; ring⟩
    have haN : a ≤ N := le_trans (Nat.le_of_dvd (by omega) hadvd) hmN
    have hbN : b ≤ N := le_trans (Nat.le_of_dvd (by omega) hbdvd) hmN
    have hac : Nat.Coprime a q := Nat.Coprime.coprime_dvd_left hadvd hmc
    refine Finset.mem_image.mpr ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_product, hA]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha0, haN⟩, hsq, hac⟩,
        Finset.mem_Icc.mpr ⟨hb0, hbN⟩⟩
    · simpa using hab
  calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m
      ≤ ∑ m ∈ (A ×ˢ Finset.Icc 1 N).image (fun p : ℕ × ℕ => p.2 ^ 2 * p.1), (1 : ℝ) / m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
    _ ≤ ∑ p ∈ A ×ˢ Finset.Icc 1 N, (1 : ℝ) / ((p.2 ^ 2 * p.1 : ℕ) : ℝ) :=
        Finset.sum_image_le_of_nonneg fun u _ => by positivity
    _ = (∑ a ∈ A, (1 : ℝ) / a) * ∑ b ∈ Finset.Icc 1 N, (1 : ℝ) / (b : ℝ) ^ 2 := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        dsimp only
        push_cast
        rw [mul_comm ((b : ℝ) ^ 2) (a : ℝ), ← one_div_mul_one_div]
    _ ≤ (∑ a ∈ A, (1 : ℝ) / a) * (Real.pi ^ 2 / 6) := mul_le_mul_of_nonneg_left hzeta hAnn
    _ = Real.pi ^ 2 / 6 * ∑ a ∈ A, (1 : ℝ) / a := mul_comm _ _

theorem sum_sf_coprime_inv_ge (q : ℕ) (R : ℝ) (hq : 1 ≤ q) (hR : 1 ≤ R) :
    6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * Real.log R
      ≤ ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
          (1 : ℝ) / r := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi0 : (0 : ℝ) < (Nat.totient q : ℝ) := by
    have : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hpi2 : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have hne1 : (Real.pi : ℝ) ^ 2 ≠ 0 := hpi2.ne'
  have hne2 : (q : ℝ) ≠ 0 := hq0.ne'
  have hne3 : ((Nat.totient q : ℝ)) ≠ 0 := hphi0.ne'
  have h1 := log_le_sum_inv_Icc_floor hR
  have h2 := sum_inv_Icc_le_div_totient_mul_coprime hq ⌊R⌋₊
  have h3 := sum_coprime_inv_le_zeta_two_mul_sqf q ⌊R⌋₊
  set S := ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
      (1 : ℝ) / r with hS
  have hqf : (0 : ℝ) ≤ (q : ℝ) / Nat.totient q := by positivity
  have hkey : Real.log R ≤ (q : ℝ) / Nat.totient q * (Real.pi ^ 2 / 6 * S) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hqf))
  have hcoef : (0 : ℝ) < 6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) :=
    mul_pos (div_pos (by norm_num) hpi2) (div_pos hphi0 hq0)
  have hmul := mul_le_mul_of_nonneg_left hkey hcoef.le
  have hsimp : 6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q)
      * ((q : ℝ) / Nat.totient q * (Real.pi ^ 2 / 6 * S)) = S := by
    field_simp
  rw [hsimp] at hmul
  exact hmul

/-- The §2(a) smoke row for W2: the `R = 1` instance of the uniform bound (`0 ≤ 1`). -/
example : (6 : ℝ) / Real.pi ^ 2 * ((Nat.totient 1 : ℝ) / 1) * Real.log 1
    ≤ ∑ r ∈ (Finset.Icc 1 ⌊(1 : ℝ)⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r 1),
        (1 : ℝ) / r := by
  simpa only [Nat.cast_one] using sum_sf_coprime_inv_ge 1 1 le_rfl le_rfl

end Salt.SW
