/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TwinA1
import Salt.Chen.Hyp4
import Salt.BV.DispersionClose
import Salt.SW.Gate
import Salt.Maynard.PhiAtom

/-!
# C2c — discharge `hBV`: the summed remainder bound

Design: `docs/blueprints/chen.md`, the C2c row.  Discharges the `hBV` slot of C2a's
`twin_A1_lower`: the L¹ Rosser remainder

  `rosserRemainder (twinA1Sieve x P hP hPodd) (Q·D) ≤ x / (log x)^10`.

## Route

1. **Split** (`rosserRemainder_le_split`, FULL): the per-divisor pointwise bound
   `twinA1_abs_rem_le` (C2a) sums to
   `rosserRemainder ≤ Σ_{d∣P, d<QD} dispDisc(x−2) d + Σ_{d∣P, d<QD} dispDisc(x/2−1) d
      + Σ_{d∣P, d<QD} convTerm d`, where `convTerm d = ω(d)·(log(x−2)+log(x/2−1))/φ(d)`
   is the ψ_{χ₀}↔ψ conversion error.  The `d = 1` divisor contributes `|rem 1| = 0`.

2. **The two BV sums** (`dispDisc_filtered_le`, FULL modulo the level check): the filtered
   `d`-set `{d ∣ P : d < QD}` is a SUBSET of `Icc 1 ⌊√x/(log x)^B⌋₊` when the level condition
   `Q·D ≤ √x/(log x)^B` holds (a NAMED consumer obligation — the `Q` constant makes it hold at
   `D = x^{1/2−ε'}`, `x` large); `dispDisc ≥ 0` then gives, via
   `Finset.sum_le_sum_of_subset_of_nonneg`, the reduction to the full BV sum
   `psi_BV_of_siegelWalfisz' siegelWalfisz_holds` at the two endpoints `y = x−2`, `y = x/2−1`.

3. **The conversion sum** (`convSum_le`, FULL): `ω(d) ≤ log d/log 3` (all prime factors `≥ 3`,
   so `d ≥ 3^{ω(d)}`) and `d < QD` give `ω(d) ≤ log(QD)/log 3`; and
   `Σ_{d∣P} 1/φ(d) = ∏_{p∣P}(1+1/(p−1)) ≤ (∏_{p∣P}(1−ν(p)))⁻¹ ≤ (1+ε)·log z/log w₀`
   (`sum_inv_totient_le_Winv` + `vratio_prod_le` of C1d).  Hence
   `convSum ≤ 2·log x·(log(QD)/log 3)·(1+ε)·log z/log w₀`, a `(log x)^3`-polylog `≪ x/(log x)^10`.

4. **Assembly** (`twinA1_hBV`): instantiate the unconditional BV keystone
   `psi_BV_of_siegelWalfisz' siegelWalfisz_holds` at saving `11`, obtain `B, C`, and package
   the level check + the final numeric closing as the two consumer obligations (both hold at
   the frozen operating point for `x` large; flagged in `docs/blueprints/flags.md`, node C2c).
-/

open Finset ArithmeticFunction Salt.LS Salt.BV

namespace Salt.Chen

/-! ## Part A — the divisor-sum `∑ 1/φ(d)` bound via the V-ratio product -/

/-- For squarefree `P`: `∑_{d ∣ P} 1/φ(d) = ∏_{p ∣ P}(1 + (p−1)⁻¹)`.  The divisors of a
squarefree number are the subset products of its prime factors, and `1/φ` is multiplicative
(`∏_{p ∣ d}(p−1)⁻¹`). -/
theorem sum_inv_totient_eq_prod {P : ℕ} (hP : Squarefree P) :
    ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      = ∏ p ∈ P.primeFactors, (((p : ℝ) - 1)⁻¹ + 1) := by
  classical
  have hprime : ∀ p ∈ P.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- expand the product over subsets of the prime factors
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  -- each subset `t` contributes `1/φ(∏ t)`
  have hval : ∀ t ∈ P.primeFactors.powerset,
      ∏ p ∈ t, ((p : ℝ) - 1)⁻¹ = (1 : ℝ) / (Nat.totient (∏ p ∈ t, p)) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have hdvd : (∏ p ∈ t, p) ∣ P := by
      have h := Finset.prod_dvd_prod_of_subset t P.primeFactors (fun p => p) ht
      rwa [Nat.prod_primeFactors_of_squarefree hP] at h
    have hsq : Squarefree (∏ p ∈ t, p) := hP.squarefree_of_dvd hdvd
    have hpf : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod (fun p hp => hprime p (ht hp))
    rw [Salt.Maynard.totient_squarefree_cast hsq, hpf, one_div, ← Finset.prod_inv_distrib]
  rw [Finset.sum_congr rfl hval]
  -- reindex the powerset sum by the injective subset-product map onto the divisors
  have hinj : Set.InjOn (fun t => ∏ p ∈ t, p) (P.primeFactors.powerset : Set (Finset ℕ)) := by
    intro t1 h1 t2 h2 h12
    simp only [Finset.mem_coe, Finset.mem_powerset] at h1 h2
    simp only at h12
    have k1 : (∏ p ∈ t1, p).primeFactors = t1 :=
      Nat.primeFactors_prod (fun p hp => hprime p (h1 hp))
    have k2 : (∏ p ∈ t2, p).primeFactors = t2 :=
      Nat.primeFactors_prod (fun p hp => hprime p (h2 hp))
    rw [← k1, ← k2, h12]
  rw [← Finset.sum_image (f := fun d => (1 : ℝ) / (Nat.totient d)) (g := fun t => ∏ p ∈ t, p) hinj]
  congr 1
  -- `powerset.image (∏·) = divisors P` for squarefree `P`
  ext d
  simp only [Finset.mem_image, Finset.mem_powerset, Nat.mem_divisors]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨d.primeFactors, Nat.primeFactors_mono hdvd hP.ne_zero,
      Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hdvd)⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, hP.ne_zero⟩
    have h := Finset.prod_dvd_prod_of_subset t P.primeFactors (fun p => p) ht
    rwa [Nat.prod_primeFactors_of_squarefree hP] at h

/-- `a + 1 ≤ (1 − a)⁻¹` for `0 ≤ a < 1` (since `(a+1)(1−a) = 1 − a² ≤ 1`). -/
private lemma add_one_le_inv_one_sub {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    a + 1 ≤ (1 - a)⁻¹ := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hne : (1 : ℝ) - a ≠ 0 := ne_of_gt h1a
  have key : (a + 1) * (1 - a) ≤ 1 := by nlinarith [sq_nonneg a]
  calc a + 1 = ((a + 1) * (1 - a)) * (1 - a)⁻¹ := by field_simp
    _ ≤ 1 * (1 - a)⁻¹ := mul_le_mul_of_nonneg_right key (le_of_lt (inv_pos.mpr h1a))
    _ = (1 - a)⁻¹ := one_mul _

/-- **The `∑ 1/φ(d)` bound.**  For squarefree `P` with all prime factors `≥ 3`,
`∑_{d ∣ P} 1/φ(d) ≤ (∏_{p ∣ P}(1 − ν(p)))⁻¹`, the V-ratio product of `W`.  Termwise
`1 + 1/(p−1) ≤ (1 − 1/(p−1))⁻¹` (since `(1+a)(1−a) = 1 − a² ≤ 1`), the divisor sum being
`∏(1 + 1/(p−1))` by `sum_inv_totient_eq_prod`. -/
theorem sum_inv_totient_le_Winv {P : ℕ} (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (∏ p ∈ P.primeFactors, (1 - nuChen p))⁻¹ := by
  rw [sum_inv_totient_eq_prod hP, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hPodd p hp
    have : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    linarith
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hPodd p hp
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have ha0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (le_of_lt hp1)
    have ha12 : ((p : ℝ) - 1)⁻¹ ≤ 1 / 2 := by
      rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    rw [nuChen_prime hpp, one_div]
    exact add_one_le_inv_one_sub ha0 (by linarith)

/-! ## Part B — the number-of-prime-factors bound `ω(d) ≤ log d / log 3` -/

/-- For squarefree `d` with all prime factors `≥ 3`, `3^{ω(d)} ≤ d`
(`d = ∏_{p ∣ d} p ≥ ∏ 3`). -/
theorem three_pow_omega_le {d : ℕ} (hd : Squarefree d) (h3 : ∀ p ∈ d.primeFactors, 3 ≤ p) :
    3 ^ d.primeFactors.card ≤ d := by
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod' (fun p hp => h3 p hp)

/-- **`ω(d) ≤ log d / log 3`** for squarefree `d` with prime factors `≥ 3`.  From
`3^{ω(d)} ≤ d`, take logs. -/
theorem omega_le_log_div {d : ℕ} (hd : Squarefree d) (h3 : ∀ p ∈ d.primeFactors, 3 ≤ p) :
    (d.primeFactors.card : ℝ) ≤ Real.log d / Real.log 3 := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd.ne_zero
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog3]
  have hpow : (3 : ℝ) ^ d.primeFactors.card ≤ (d : ℝ) := by
    have := three_pow_omega_le hd h3
    calc (3 : ℝ) ^ d.primeFactors.card = ((3 ^ d.primeFactors.card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (d : ℝ) := by exact_mod_cast this
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) hpow

/-! ## Part C — the split of the Rosser remainder into the BV + conversion sums -/

/-- The ψ_{χ₀}↔ψ conversion term `ω(d)·(log(x−2) + log(x/2−1))/φ(d)` — the RHS conversion
part of C2a's `twinA1_abs_rem_le`. -/
noncomputable def convTerm (x d : ℕ) : ℝ :=
  (d.primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ) / (d.totient : ℝ)
    + (d.primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ) / (d.totient : ℝ)

lemma convTerm_nonneg (x d : ℕ) : 0 ≤ convTerm x d := by
  unfold convTerm
  have h1 : 0 ≤ Real.log ((x - 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h2 : 0 ≤ Real.log ((x / 2 - 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have := div_nonneg (mul_nonneg (by positivity) h1) (by positivity : (0:ℝ) ≤ (d.totient : ℝ))
  have := div_nonneg (mul_nonneg (by positivity) h2) (by positivity : (0:ℝ) ≤ (d.totient : ℝ))
  positivity

/-- `rem 1 = 0`: `1 ∣ n+2` always, so `multSum 1 = totalMass`, and `ν(1) = 1/φ(1) = 1`. -/
lemma twinA1_rem_one (x P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (twinA1Sieve x P hP hPodd).rem 1 = 0 := by
  rw [twinA1Sieve_rem]
  simp only [Nat.one_dvd, if_true, nuChen_apply, Nat.totient_one, Nat.cast_one, div_one, one_mul]
  ring

/-- Every divisor of `P` (all prime factors `≥ 3`) is either `1` or an odd `d ≥ 3`. -/
lemma divisor_cases {P d : ℕ} (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hd : d ∈ P.divisors) : d = 1 ∨ (3 ≤ d ∧ Odd d) := by
  have hdvd : d ∣ P := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hP0 : P ≠ 0 := hP.ne_zero
  have h2P : ¬ (2 ∣ P) := by
    intro h2
    have hmem : (2 : ℕ) ∈ P.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hP0⟩
    have := hPodd 2 hmem; omega
  have h2d : ¬ (2 ∣ d) := fun h => h2P (h.trans hdvd)
  have hodd2 : d % 2 = 1 := Nat.two_dvd_ne_zero.mp h2d
  rcases eq_or_ne d 1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨by omega, Nat.odd_iff.mpr hodd2⟩

/-- **The split** (FULL).  The Rosser remainder is bounded termwise — via C2a's
`twinA1_abs_rem_le` (odd `d ≥ 3`), `rem 1 = 0` (the `d = 1` divisor), and `dispDisc,
convTerm ≥ 0` — by the two endpoint BV discrepancy sums plus the conversion sum, all over
the level-restricted divisors `d < bound`. -/
lemma rosserRemainder_le_split (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (hx : 4 ≤ x) (bound : ℝ) :
    rosserRemainder (twinA1Sieve x P hP hPodd) bound
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (x - 2) d else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (x / 2 - 1) d else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm x d else 0) := by
  rw [rosserRemainder]
  simp only [twinA1Sieve_prodPrimes]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  by_cases hlt : (d : ℝ) < bound
  · simp only [if_pos hlt]
    rcases divisor_cases hP hPodd hd with rfl | ⟨hd3, hodd⟩
    · rw [twinA1_rem_one, abs_zero]
      have h1 := dispDisc_nonneg (x - 2) 1
      have h2 := dispDisc_nonneg (x / 2 - 1) 1
      have h3 := convTerm_nonneg x 1
      linarith
    · have h := twinA1_abs_rem_le x P hP hPodd d hd3 hodd hx
      unfold convTerm
      linarith [h]
  · simp only [if_neg hlt]
    simp

/-! ## Part D — the two BV endpoint sums (subset into the BV index set) -/

/-- **The level-restricted BV sum** (FULL modulo the level check).  When `bound ≤ M`, the
level-restricted divisor sum of `dispDisc y` is `≤` the full BV sum over `Icc 1 ⌊M⌋₊`: the
filtered `d`-set `{d ∣ P : d < bound}` lies in `Icc 1 ⌊M⌋₊`, and `dispDisc ≥ 0`. -/
lemma dispDisc_filtered_le_Icc {P : ℕ} (y : ℕ) {bound M : ℝ} (hlevel : bound ≤ M) :
    (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc y d else 0)
      ≤ ∑ q ∈ Finset.Icc 1 ⌊M⌋₊, dispDisc y q := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdmem, hdlt⟩ := hd
    rw [Finset.mem_Icc]
    refine ⟨Nat.pos_of_mem_divisors hdmem, ?_⟩
    exact Nat.le_floor (le_trans (le_of_lt hdlt) hlevel)
  · intro q _ _; exact dispDisc_nonneg y q

/-! ## Part E — the conversion sum bound -/

/-- **The conversion sum bound** (FULL).  `Σ_{d∣P, d<bound} convTerm x d
≤ 2·log x·(log bound/log 3)·Σ_{d∣P} 1/φ(d)`.  Uses `ω(d) ≤ log d/log 3 ≤ log bound/log 3`
(`omega_le_log_div`, `d < bound`) and `log(x−2), log(x/2−1) ≤ log x`, per divisor. -/
lemma convSum_le {x P : ℕ} (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hx : 4 ≤ x) {bound : ℝ} (hb1 : 1 ≤ bound) :
    (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm x d else 0)
      ≤ 2 * Real.log x * (Real.log bound / Real.log 3)
          * (∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)) := by
  have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogb : 0 ≤ Real.log bound := Real.log_nonneg hb1
  have hlogb3 : 0 ≤ Real.log bound / Real.log 3 := by positivity
  have hfac0 : 0 ≤ 2 * Real.log x * (Real.log bound / Real.log 3) := by positivity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdvd : d ∣ P := Nat.dvd_of_mem_divisors hd
  have hdsq : Squarefree d := hP.squarefree_of_dvd hdvd
  have hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p := fun p hp =>
    hPodd p (Nat.primeFactors_mono hdvd hP.ne_zero hp)
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hφpos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hdpos
  by_cases hlt : (d : ℝ) < bound
  · rw [if_pos hlt]
    have homega : (d.primeFactors.card : ℝ) ≤ Real.log bound / Real.log 3 := by
      calc (d.primeFactors.card : ℝ) ≤ Real.log d / Real.log 3 := omega_le_log_div hdsq hd3
        _ ≤ Real.log bound / Real.log 3 :=
            (div_le_div_iff_of_pos_right hlog3).mpr
              (Real.log_le_log (by exact_mod_cast hdpos) (le_of_lt hlt))
    have hA0 : (0 : ℝ) ≤ (d.primeFactors.card : ℝ) := by positivity
    have hL2 : 0 ≤ Real.log ((x - 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hL3 : 0 ≤ Real.log ((x / 2 - 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hlx2 : Real.log ((x - 2 : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < x - 2))
        (by exact_mod_cast (by omega : x - 2 ≤ x))
    have hlx3 : Real.log ((x / 2 - 1 : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < x / 2 - 1))
        (by exact_mod_cast (by omega : x / 2 - 1 ≤ x))
    have hnum : (d.primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ)
          + (d.primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ)
        ≤ 2 * Real.log x * (Real.log bound / Real.log 3) := by
      nlinarith [mul_le_mul homega hlx2 hL2 hlogb3, mul_le_mul homega hlx3 hL3 hlogb3]
    calc convTerm x d
        = ((d.primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ)
            + (d.primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ)) / (d.totient : ℝ) := by
          unfold convTerm; ring
      _ ≤ (2 * Real.log x * (Real.log bound / Real.log 3)) / (d.totient : ℝ) :=
          (div_le_div_iff_of_pos_right hφpos).mpr hnum
      _ = 2 * Real.log x * (Real.log bound / Real.log 3) * (1 / (d.totient : ℝ)) := by ring
  · rw [if_neg hlt]
    exact mul_nonneg hfac0 (by positivity)

/-! ## Part F — the assembly: discharge `hBV` -/

/-- **C2c — the summed remainder bound.**  Instantiating the unconditional Bombieri–Vinogradov
keystone `psi_BV_of_siegelWalfisz' siegelWalfisz_holds` at saving `11`, the Rosser remainder of
the twin `A₁` sieve is `≤ x/(log x)^10`, given two consumer obligations (both hold at the frozen
operating point `D = x^{1/2−ε'}`, `x` large; see `docs/blueprints/flags.md`, node C2c):

* the **level check** `Q·D ≤ √x/(log x)^B` (`B` the BV haircut) — the `Q` constant is
  asymptotically free against `x^{−ε'}`;
* the **numeric closing** `C·x/(log x)^11 + C·x/(log x)^11 + (log x)^3-polylog ≤ x/(log x)^10`.

The split (`rosserRemainder_le_split`), the two BV endpoint sums (`dispDisc_filtered_le_Icc` +
BV), and the conversion sum (`convSum_le` + `sum_inv_totient_le_Winv` + `vratio_prod_le`) are all
proved in full. -/
theorem twinA1_hBV (x z D P : ℕ) (ε Q : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 4 ≤ x) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
    (hwz : w0R ε ≤ (z : ℝ)) (hQ : 1 ≤ Q) (hD : 1 ≤ D) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ( (Q : ℝ) * D ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B →
        C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
          + 2 * Real.log x * (Real.log ((Q : ℝ) * D) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          ≤ (x : ℝ) / (Real.log x) ^ 10 →
        rosserRemainder (twinA1Sieve x P hP hPodd) (Q * D) ≤ (x : ℝ) / (Real.log x) ^ 10 ) := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, fun hlevel hclose => ?_⟩
  have hx2 : 2 ≤ x := by omega
  -- the split into two BV sums + the conversion sum
  have hsplit := rosserRemainder_le_split x P hP hPodd hx (Q * (D : ℝ))
  -- the two dispDisc endpoint sums: filtered ⊆ BV index set, then the BV bound
  have hbv1 := hbv x (x - 2) hx2 (by omega : x - 2 ≤ x)
  have hbv2 := hbv x (x / 2 - 1) hx2 (by omega : x / 2 - 1 ≤ x)
  have hS1 : (∑ d ∈ P.divisors, if (d : ℝ) < Q * (D : ℝ) then dispDisc (x - 2) d else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDisc_filtered_le_Icc (x - 2) hlevel) hbv1
  have hS2 : (∑ d ∈ P.divisors, if (d : ℝ) < Q * (D : ℝ) then dispDisc (x / 2 - 1) d else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDisc_filtered_le_Icc (x / 2 - 1) hlevel) hbv2
  -- the `∑ 1/φ(d)` bound via the V-ratio product (C1d's `vratio_prod_le`)
  have hb1 : (1 : ℝ) ≤ Q * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith [hQ, hD1]
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (twinA1Sieve x P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hPlow p hp,
        by exact_mod_cast hPz p hp, twinA1_hnu P p hp⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  -- the conversion sum
  have hlogQD : 0 ≤ Real.log (Q * (D : ℝ)) := Real.log_nonneg hb1
  have hconvfac : 0 ≤ 2 * Real.log x * (Real.log (Q * (D : ℝ)) / Real.log 3) := by
    have : 0 ≤ Real.log x := Real.log_natCast_nonneg x
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  have hConv : (∑ d ∈ P.divisors, if (d : ℝ) < Q * (D : ℝ) then convTerm x d else 0)
      ≤ 2 * Real.log x * (Real.log (Q * (D : ℝ)) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε)) :=
    le_trans (convSum_le hP hPodd hx hb1) (mul_le_mul_of_nonneg_left hMbound hconvfac)
  -- assemble
  linarith [hsplit, hS1, hS2, hConv, hclose]

end Salt.Chen
