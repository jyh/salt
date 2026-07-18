/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.M5BigO
import Salt.Mertens.TwinDensity

/-!
# HL-3b — the sharp-order twin upper bound

The landed Selberg wrapper (`Salt.HardyLittlewood.twinCounting_upper_order`) gives
`twinPrimeCounting N ≤ 25700·N/(log N)²`.  This file sharpens the constant to
`C = 90` (a factor ≈ 285) by rebuilding the Selberg sieve at the higher level
`yS N = N^(9/10)` (truncation `zS N = ⌊N^(9/20)⌋`), which changes three of the
lossy inputs identified in the loss-budget audit:

* the **level/truncation**: `z = N^(1/10)` → `N^(9/20)`, recovering most of the
  `(log z)²` grade (the classical Selberg uses `z ≈ N^(1/2)`; pushing further is
  gated only on `zS → N^(1/2)`, i.e. `C → 64`, at the cost of a larger threshold);
* the **harmonic-square constant**: `stepD`'s degraded `1/8` restored to the sharp
  `1/4` (`oddHarmonicSum(z.sqrt-1) ≥ (1/4)·log z − 1/2`), i.e. the denominator
  grade `1/64 → 1/16`;
* the **sieve remainder**: the crude termwise `6^ω(d) ≤ d³` (which capped the level
  at `N^(1/4)`) replaced by the **divisor-power mean value**
  `∑_{d≤L, sqfree} 6^ω(d) ≤ L·(1+log L)⁶` (`sum_six_pow_omega_le`), which lets the
  level rise to `N^(1−ε)`.

The classical order-sharp constants `8·Π₂ ≈ 5.3` (with the true singular-series
density `1/(8Π₂)` in place of the harmonic-square `1/16`) remain future work; the
harmonic-square method used here bottoms out at `C = 64` as `zS → N^(1/2)`.
-/

open Finset ArithmeticFunction Filter
open Salt.M5Assembly (primorial_squarefree)

namespace Salt.HardyLittlewood

/-- Sharp sieve level: `N^(9/10)`. -/
noncomputable def yS (N : ℕ) : ℝ := (N : ℝ) ^ (9 / 10 : ℝ)

/-- Sharp truncation parameter: `⌊N^(9/20)⌋₊`. -/
noncomputable def zS (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (9 / 20 : ℝ)⌋₊

/-- Sharp sift modulus. -/
noncomputable def PS (N : ℕ) : ℕ := primorial (zS N)

lemma PS_squarefree (N : ℕ) : Squarefree (PS N) := primorial_squarefree (zS N)

/-- The sharp twin Selberg sieve. -/
noncomputable def twinSieveSharp (N : ℕ) (hN : 1 ≤ N) : SelbergSieve where
  toBoundingSieve := Salt.TwinSieve.sieve N (PS N) (PS_squarefree N)
  level := yS N
  one_le_level := by
    unfold yS
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)

@[simp] lemma twinSieveSharp_prodPrimes (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSharp N hN).prodPrimes = PS N := rfl

@[simp] lemma twinSieveSharp_totalMass (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSharp N hN).totalMass = (N : ℝ) := rfl

@[simp] lemma twinSieveSharp_level (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSharp N hN).level = yS N := rfl

lemma twinSieveSharp_selbergTerms (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSharp N hN).selbergTerms
      = (Salt.TwinSieve.sieve N (PS N) (PS_squarefree N)).selbergTerms := rfl

lemma twinSieveSharp_rem (N : ℕ) (hN : 1 ≤ N) (d : ℕ) :
    (twinSieveSharp N hN).rem d = _root_.rem d N := by
  change (Salt.TwinSieve.sieve N (PS N) (PS_squarefree N)).rem d = _root_.rem d N
  exact Salt.TwinSieve.sieve_rem d

lemma twinSieveSharp_siftedSum (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSharp N hN).siftedSum
      = (Salt.TwinSieve.sieve N (PS N) (PS_squarefree N)).siftedSum := rfl

/-! ## The divisor-power mean value (linchpin) -/

/-- Convolution identity: for squarefree `d`, `∑_{e | d} k^ω(e) = (k+1)^ω(d)`. -/
lemma tau6_conv (k : ℕ) {d : ℕ} (hd : Squarefree d) :
    ∑ e ∈ d.divisors, (k : ℝ) ^ (e.primeFactors.card)
      = ((k : ℝ) + 1) ^ (d.primeFactors.card) := by
  have h1 : ∑ e ∈ d.divisors, (k : ℝ) ^ (e.primeFactors.card)
          = ∑ t ∈ d.primeFactors.powerset, (k : ℝ) ^ (t.card) := by
    refine Finset.sum_nbij' (fun e => e.primeFactors) (fun t => ∏ p ∈ t, p)
      ?_ ?_ ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors he) hd.ne_zero
    · intro t ht
      rw [Finset.mem_powerset] at ht
      rw [Nat.mem_divisors]
      refine ⟨(Finset.prod_dvd_prod_of_subset _ _ _ ht).trans ?_, hd.ne_zero⟩
      rw [Nat.prod_primeFactors_of_squarefree hd]
    · intro e he
      exact Nat.prod_primeFactors_of_squarefree
        (Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors he) hd)
    · intro t ht
      rw [Finset.mem_powerset] at ht
      exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (ht hp))
    · intro e he
      rfl
  rw [h1]
  have hpa := Finset.prod_add (fun _ : ℕ => (k : ℝ)) (fun _ => (1 : ℝ)) d.primeFactors
  simp only [Finset.prod_const, one_pow, mul_one] at hpa
  exact hpa.symm

/-- Harmonic tail bound. -/
lemma tau6_tail {L e : ℕ} (he : 1 ≤ e) {A : Finset ℕ}
    (hA : ∀ d ∈ A, d ∈ Finset.Icc 1 L ∧ e ∣ d) :
    ∑ d ∈ A, (1 : ℝ) / (d : ℝ) ≤ (1 / (e : ℝ)) * (1 + Real.log L) := by
  have step1 : ∑ d ∈ A, (1 : ℝ) / (d : ℝ)
             = (1 / (e : ℝ)) * ∑ d ∈ A, (1 : ℝ) / ((d / e : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨_, hde⟩ := hA d hd
    have hdiv : (d : ℝ) = (e : ℝ) * ((d / e : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hde]
    rw [hdiv, one_div_mul_one_div]
  rw [step1]
  have step2 : ∑ d ∈ A, (1 : ℝ) / ((d / e : ℕ) : ℝ) ≤ 1 + Real.log L := by
    have hinj : Set.InjOn (fun d => d / e) (↑A : Set ℕ) := by
      intro a ha b hb hab
      have hae := (hA a (Finset.mem_coe.mp ha)).2
      have hbe := (hA b (Finset.mem_coe.mp hb)).2
      have h : a / e = b / e := hab
      rw [← Nat.mul_div_cancel' hae, ← Nat.mul_div_cancel' hbe, h]
    calc ∑ d ∈ A, (1 : ℝ) / ((d / e : ℕ) : ℝ)
        = ∑ m ∈ A.image (fun d => d / e), (1 : ℝ) / (m : ℝ) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ m ∈ Finset.Icc 1 L, (1 : ℝ) / (m : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            rw [Finset.mem_image] at hm
            obtain ⟨d, hdA, rfl⟩ := hm
            obtain ⟨hd1, hde⟩ := hA d hdA
            rw [Finset.mem_Icc] at hd1 ⊢
            refine ⟨?_, ?_⟩
            · rw [Nat.one_le_div_iff (by omega : 0 < e)]
              exact Nat.le_of_dvd (by omega) hde
            · exact le_trans (Nat.div_le_self d e) hd1.2
          · intro m _ _; positivity
      _ = (harmonic L : ℝ) := by
          rw [harmonic_eq_sum_Icc]; push_cast
          apply Finset.sum_congr rfl; intro i _; rw [one_div]
      _ ≤ 1 + Real.log L := harmonic_le_one_add_log L
  apply mul_le_mul_of_nonneg_left step2
  positivity

/-- The weighted partial sum `∑_{d ≤ L, sqfree} k^ω(d) / d`. -/
noncomputable def tau6W (L k : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 L).filter Squarefree, (k : ℝ) ^ (d.primeFactors.card) / (d : ℝ)

lemma tau6W_zero_le (L : ℕ) : tau6W L 0 ≤ 1 := by
  unfold tau6W
  simp only [Nat.cast_zero]
  calc ∑ d ∈ (Finset.Icc 1 L).filter Squarefree,
          (0 : ℝ) ^ (d.primeFactors.card) / (d : ℝ)
      ≤ ∑ d ∈ (Finset.Icc 1 L).filter Squarefree, (if d = 1 then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        by_cases hdeq : d = 1
        · subst hdeq; simp
        · have hne : d.primeFactors ≠ ∅ := by
            rw [Ne, Nat.primeFactors_eq_empty]; rintro (h | h) <;> omega
          have hcard : d.primeFactors.card ≠ 0 := by
            rwa [Ne, Finset.card_eq_zero]
          rw [zero_pow hcard]
          simp [hdeq]
    _ ≤ 1 := by
        rw [Finset.sum_ite_eq']
        split_ifs <;> norm_num

lemma tau6W_step (L k : ℕ) : tau6W L (k + 1) ≤ (1 + Real.log L) * tau6W L k := by
  unfold tau6W
  set S := (Finset.Icc 1 L).filter Squarefree with hS
  calc ∑ d ∈ S, ((k + 1 : ℕ) : ℝ) ^ (d.primeFactors.card) / (d : ℝ)
      = ∑ d ∈ S, ∑ e ∈ d.divisors,
          (k : ℝ) ^ (e.primeFactors.card) / (d : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdsq : Squarefree d := (Finset.mem_filter.mp hd).2
        rw [Nat.cast_add, Nat.cast_one, ← tau6_conv k hdsq, Finset.sum_div]
    _ = ∑ e ∈ S, ∑ d ∈ S.filter (fun d => e ∣ d),
          (k : ℝ) ^ (e.primeFactors.card) / (d : ℝ) := by
        apply Finset.sum_comm'
        intro d e
        constructor
        · rintro ⟨hdS, hed⟩
          have hed' : e ∣ d := Nat.dvd_of_mem_divisors hed
          have hdmem := Finset.mem_filter.mp hdS
          have hdsq : Squarefree d := hdmem.2
          have hdIcc := Finset.mem_Icc.mp hdmem.1
          refine ⟨Finset.mem_filter.mpr ⟨hdS, hed'⟩, ?_⟩
          refine Finset.mem_filter.mpr ⟨?_, Squarefree.squarefree_of_dvd hed' hdsq⟩
          rw [Finset.mem_Icc]
          have hepos : 1 ≤ e := Nat.pos_of_mem_divisors hed
          have hed_le : e ≤ d := Nat.le_of_dvd (by omega) hed'
          exact ⟨hepos, le_trans hed_le hdIcc.2⟩
        · rintro ⟨hdf, _⟩
          rw [Finset.mem_filter] at hdf
          obtain ⟨hdS, hed'⟩ := hdf
          have hdIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hdS).1
          refine ⟨hdS, Nat.mem_divisors.mpr ⟨hed', by omega⟩⟩
    _ ≤ (1 + Real.log L) * ∑ d ∈ S, (k : ℝ) ^ (d.primeFactors.card) / (d : ℝ) := by
        have hbound : ∀ e ∈ S,
            ∑ d ∈ S.filter (fun d => e ∣ d),
              (k : ℝ) ^ (e.primeFactors.card) / (d : ℝ)
              ≤ (1 + Real.log L) * ((k : ℝ) ^ (e.primeFactors.card) / (e : ℝ)) := by
          intro e heS
          have hepos : 1 ≤ e :=
            (Finset.mem_Icc.mp (Finset.mem_filter.mp heS).1).1
          have hfac : ∑ d ∈ S.filter (fun d => e ∣ d),
                (k : ℝ) ^ (e.primeFactors.card) / (d : ℝ)
              = (k : ℝ) ^ (e.primeFactors.card)
                  * ∑ d ∈ S.filter (fun d => e ∣ d), (1 : ℝ) / (d : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _; rw [mul_one_div]
          rw [hfac]
          have ht : ∑ d ∈ S.filter (fun d => e ∣ d), (1 : ℝ) / (d : ℝ)
                  ≤ (1 / (e : ℝ)) * (1 + Real.log L) := by
            apply tau6_tail hepos
            intro d hd
            rw [Finset.mem_filter] at hd
            obtain ⟨hdS, hed⟩ := hd
            exact ⟨(Finset.mem_filter.mp hdS).1, hed⟩
          calc (k : ℝ) ^ (e.primeFactors.card)
                  * ∑ d ∈ S.filter (fun d => e ∣ d), (1 : ℝ) / (d : ℝ)
              ≤ (k : ℝ) ^ (e.primeFactors.card) * ((1 / (e : ℝ)) * (1 + Real.log L)) := by
                apply mul_le_mul_of_nonneg_left ht
                positivity
            _ = (1 + Real.log L) * ((k : ℝ) ^ (e.primeFactors.card) / (e : ℝ)) := by
                rw [div_eq_mul_one_div]; ring
        calc ∑ e ∈ S, ∑ d ∈ S.filter (fun d => e ∣ d),
                (k : ℝ) ^ (e.primeFactors.card) / (d : ℝ)
            ≤ ∑ e ∈ S, (1 + Real.log L) * ((k : ℝ) ^ (e.primeFactors.card) / (e : ℝ)) :=
              Finset.sum_le_sum hbound
          _ = (1 + Real.log L) * ∑ e ∈ S, (k : ℝ) ^ (e.primeFactors.card) / (e : ℝ) := by
              rw [Finset.mul_sum]

lemma tau6W_le (L k : ℕ) : tau6W L k ≤ (1 + Real.log L) ^ k := by
  induction k with
  | zero => rw [pow_zero]; exact tau6W_zero_le L
  | succ k ih =>
    have hlog : (0 : ℝ) ≤ 1 + Real.log L := by
      have := Real.log_natCast_nonneg L; linarith
    calc tau6W L (k + 1) ≤ (1 + Real.log L) * tau6W L k := tau6W_step L k
      _ ≤ (1 + Real.log L) * (1 + Real.log L) ^ k :=
          mul_le_mul_of_nonneg_left ih hlog
      _ = (1 + Real.log L) ^ (k + 1) := by rw [← pow_succ']

/-- **The divisor-power mean value.** `∑_{d≤L, sqfree} 6^ω(d) ≤ L·(1+log L)⁶`. -/
theorem sum_six_pow_omega_le (L : ℕ) :
    ∑ d ∈ (Finset.Icc 1 L).filter Squarefree, (6 : ℝ) ^ (d.primeFactors.card)
      ≤ (L : ℝ) * (1 + Real.log L) ^ 6 := by
  have h1 : ∑ d ∈ (Finset.Icc 1 L).filter Squarefree, (6 : ℝ) ^ (d.primeFactors.card)
          ≤ (L : ℝ) * tau6W L 6 := by
    unfold tau6W
    simp only [Nat.cast_ofNat]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hdL : d ≤ L := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hrw : (L : ℝ) * ((6 : ℝ) ^ (d.primeFactors.card) / (d : ℝ))
             = (6 : ℝ) ^ (d.primeFactors.card) * ((L : ℝ) / (d : ℝ)) := by ring
    rw [hrw]
    have hLd : (1 : ℝ) ≤ (L : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hdpos, one_mul]; exact_mod_cast hdL
    calc (6 : ℝ) ^ (d.primeFactors.card)
        = (6 : ℝ) ^ (d.primeFactors.card) * 1 := (mul_one _).symm
      _ ≤ (6 : ℝ) ^ (d.primeFactors.card) * ((L : ℝ) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hLd (by positivity)
  have h2 : (L : ℝ) * tau6W L 6 ≤ (L : ℝ) * (1 + Real.log L) ^ 6 :=
    mul_le_mul_of_nonneg_left (tau6W_le L 6) (by positivity)
  exact le_trans h1 h2

/-! ## Denominator lower bound -/

private lemma rpow_920_sq (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (9 / 20 : ℝ)) ^ 2 = x ^ (9 / 10 : ℝ) := by
  rw [← Real.rpow_natCast (x ^ (9 / 20 : ℝ)) 2, ← Real.rpow_mul hx]
  norm_num

/-- `(zS N)² ≤ yS N`. -/
lemma zS_sq_le_yS (N : ℕ) : ((zS N : ℝ)) ^ 2 ≤ yS N := by
  have hzR : (zS N : ℝ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := Nat.floor_le (by positivity)
  have hnn : (0 : ℝ) ≤ (zS N : ℝ) := Nat.cast_nonneg _
  calc ((zS N : ℝ)) ^ 2 ≤ ((N : ℝ) ^ (9 / 20 : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ hnn hzR
    _ = yS N := by rw [yS, rpow_920_sq (N : ℝ) (Nat.cast_nonneg N)]

/-- The sharp Selberg bounding sum dominates the twin main term at `zS N`. -/
lemma selbergBoundingSum_ge_mainTermSum_sharp (N : ℕ) (hN : 1 ≤ N) :
    Salt.SelbergPort.selbergBoundingSum (twinSieveSharp N hN)
      ≥ Salt.M3Assembly.mainTermSum (zS N) := by
  classical
  rw [ge_iff_le, Salt.SelbergPort.selbergBoundingSum, twinSieveSharp_prodPrimes,
    twinSieveSharp_level, ← Finset.sum_filter]
  rw [twinSieveSharp_selbergTerms]
  rw [Salt.M3Assembly.mainTermSum]
  set small : Finset ℕ := (Finset.range (zS N)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) with hsmall
  set big : Finset ℕ := (PS N).divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ yS N) with hbig
  have hsub : small ⊆ big := by
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    rw [hbig, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, (PS_squarefree N).ne_zero⟩, ?_⟩
    · -- ℓ ∣ PS N
      have h1 : ℓ ∣ primorial ℓ := Squarefree.dvd_primorial hℓsq
      have h2 : primorial ℓ ∣ primorial (zS N) := primorial_dvd_primorial (le_of_lt hℓz)
      exact h1.trans h2
    · -- (ℓ:ℝ)^2 ≤ yS N
      have hℓR : (ℓ : ℝ) ≤ (zS N : ℝ) := by exact_mod_cast (le_of_lt hℓz)
      have hℓnn : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
      have hstep : (ℓ : ℝ) ^ 2 ≤ (zS N : ℝ) ^ 2 := pow_le_pow_left₀ hℓnn hℓR 2
      exact le_trans hstep (zS_sq_le_yS N)
  have heq : ∑ ℓ ∈ small, Salt.M3Expansion.gTwin ℓ
      = ∑ ℓ ∈ small, (Salt.TwinSieve.sieve N (PS N) (PS_squarefree N)).selbergTerms ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    have hℓP : ℓ ∣ PS N := by
      have h1 : ℓ ∣ primorial ℓ := Squarefree.dvd_primorial hℓsq
      have h2 : primorial ℓ ∣ primorial (zS N) := primorial_dvd_primorial (le_of_lt hℓz)
      exact h1.trans h2
    exact (Salt.TwinSieve.selbergTerms_eq_gTwin hℓP hℓodd hℓsq).symm
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro l hl _
  rw [hbig, Finset.mem_filter, Nat.mem_divisors] at hl
  exact le_of_lt ((Salt.TwinSieve.sieve N (PS N) (PS_squarefree N)).selbergTerms_pos hl.1.1)

/-! ## Sharp harmonic constant: `oddHarmonicSum(z.sqrt-1) ≥ (1/4) log z - 1/2` -/

/-- The SHARP odd-harmonic bound (the `(1/4)` before the landed `stepD` degrades to `(1/8)`). -/
lemma oddHarmonicSum_sqrt_ge_sharp {z : ℕ} (hz : Salt.M3Assembly.z0 ≤ z) :
    oddHarmonicSum (z.sqrt - 1) ≥ (1 / 4 : ℝ) * Real.log z - 1 / 2 := by
  have hzge16 : (16 : ℕ) ≤ z := by unfold Salt.M3Assembly.z0 at hz; omega
  have hsqrt_ge4 : (4 : ℕ) ≤ z.sqrt := Nat.le_sqrt.mpr (by omega)
  have hsqrt_ge1 : (1 : ℕ) ≤ z.sqrt := by omega
  -- (z.sqrt : ℝ) > √z - 1
  have hD2 : (z.sqrt : ℝ) > Real.sqrt (z : ℝ) - 1 := by
    have := Salt.M3Assembly.sqrt_real_lt_nat_sqrt_succ z; linarith
  have hcast : ((z.sqrt - 1 : ℕ) : ℝ) = (z.sqrt : ℝ) - 1 := by
    have : (1 : ℕ) ≤ z.sqrt := hsqrt_ge1
    push_cast [Nat.cast_sub this]; ring
  have hsqrtR_ge4 : (4 : ℝ) ≤ Real.sqrt (z : ℝ) := by
    have h16 : (16 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzge16
    have := Real.sqrt_le_sqrt h16
    have h4 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at this
  have hhalf : Real.sqrt (z : ℝ) - 2 ≥ Real.sqrt (z : ℝ) / 2 := by linarith
  have hkey : ((z.sqrt - 1 : ℕ) : ℝ) ≥ Real.sqrt (z : ℝ) / 2 := by rw [hcast]; linarith
  have hhalfpos : (0 : ℝ) < Real.sqrt (z : ℝ) / 2 := by linarith
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    have hz100 : (100 : ℕ) ≤ z := by unfold Salt.M3Assembly.z0 at hz; omega
    have : (100 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz100
    linarith
  -- log(√z/2) = (1/2) log z - log 2
  have hlogsqrt : Real.log (Real.sqrt (z : ℝ)) = Real.log z / 2 := Real.log_sqrt hzpos.le
  have hlogdiv : Real.log (Real.sqrt (z : ℝ) / 2)
      = Real.log (Real.sqrt (z : ℝ)) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  have hmono : Real.log (Real.sqrt (z : ℝ) / 2) ≤ Real.log ((z.sqrt - 1 : ℕ) : ℝ) :=
    Real.log_le_log hhalfpos hkey
  have hoh := oddHarmonicSum_ge (z.sqrt - 1)
  -- oddHarmonicSum ≥ (log(z.sqrt-1))/2 - (1-log2)/2 ≥ (log(√z/2))/2 - (1-log2)/2 = (1/4)log z - 1/2
  rw [hlogdiv, hlogsqrt] at hmono
  linarith [hoh, hmono]

/-- Sharp lower bound on the twin main term: `mainTermSum z ≥ ((1/4)log z - 1/2)²`. -/
lemma mainTermSum_ge_sharp {z : ℕ} (hz : Salt.M3Assembly.z0 ≤ z) :
    Salt.M3Assembly.mainTermSum z ≥ ((1 / 4 : ℝ) * Real.log z - 1 / 2) ^ 2 := by
  have hzge16 : (16 : ℕ) ≤ z := by unfold Salt.M3Assembly.z0 at hz; omega
  have hsqrt_ge1 : (1 : ℕ) ≤ z.sqrt := by
    have : (4 : ℕ) ≤ z.sqrt := Nat.le_sqrt.mpr (by omega); omega
  have hlog4 : (4 : ℝ) ≤ Real.log z := Salt.M3Assembly.log_ge_four hz
  have hoh := oddHarmonicSum_sqrt_ge_sharp hz
  have hpos : (0 : ℝ) ≤ (1 / 4 : ℝ) * Real.log z - 1 / 2 := by linarith
  have hsq : ((1 / 4 : ℝ) * Real.log z - 1 / 2) ^ 2 ≤ (oddHarmonicSum (z.sqrt - 1)) ^ 2 :=
    pow_le_pow_left₀ hpos hoh 2
  have hchain := Salt.M3Assembly.mainTermSum_ge_oddHarmonicSum_sq (z := z) hsqrt_ge1
  linarith [hchain, hsq]

/-! ## Numeric threshold machinery -/

/-- Master threshold. -/
def N0S : ℕ := 2 ^ 240

lemma N0S_cast : (N0S : ℝ) = (2 : ℝ) ^ (240 : ℕ) := by unfold N0S; push_cast; ring

/-- `(N0S)^(9/20) = 2^108`, computed exactly. -/
lemma N0S_rpow_920 : (N0S : ℝ) ^ (9 / 20 : ℝ) = (2 : ℝ) ^ (108 : ℕ) := by
  rw [N0S_cast, ← Real.rpow_natCast (2 : ℝ) 240, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast (2 : ℝ) 108]
  norm_num

/-- `log N ≥ 240 log 2` for `N ≥ N0S`. -/
lemma logN_ge {N : ℕ} (hN : N0S ≤ N) : (240 : ℝ) * Real.log 2 ≤ Real.log N := by
  have hcast : (N0S : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N0S : ℝ) := by rw [N0S_cast]; positivity
  have hmono : Real.log (N0S : ℝ) ≤ Real.log N := Real.log_le_log hpos hcast
  have hlog : Real.log (N0S : ℝ) = 240 * Real.log 2 := by
    rw [N0S_cast, Real.log_pow]; push_cast; ring
  linarith [hlog ▸ hmono]

/-- `N^(9/20) ≥ 2^108` for `N ≥ N0S`. -/
lemma rpow920_ge {N : ℕ} (hN : N0S ≤ N) : (2 : ℝ) ^ (108 : ℕ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := by
  have hcast : (N0S : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (N0S:ℝ)) hcast (by norm_num : (0:ℝ) ≤ 9/20)
  rwa [N0S_rpow_920] at this

/-- `(zS N : ℝ) ≥ N^(9/20)/2` for `N ≥ N0S`. -/
lemma zS_lower {N : ℕ} (hN : N0S ≤ N) : (N : ℝ) ^ (9 / 20 : ℝ) / 2 ≤ (zS N : ℝ) := by
  have hlt : (N : ℝ) ^ (9 / 20 : ℝ) < (zS N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hge : (2 : ℝ) ^ (108 : ℕ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := rpow920_ge hN
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (108 : ℕ) := by norm_num
  linarith

/-- `100 ≤ zS N` for `N ≥ N0S`. -/
lemma zS_ge_100 {N : ℕ} (hN : N0S ≤ N) : Salt.M3Assembly.z0 ≤ zS N := by
  have hlow := zS_lower hN
  have hge : (2 : ℝ) ^ (108 : ℕ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := rpow920_ge hN
  have h135 : (200 : ℝ) ≤ (2 : ℝ) ^ (108 : ℕ) := by norm_num
  have : (100 : ℝ) ≤ (zS N : ℝ) := by linarith
  have h100 : (100 : ℕ) ≤ zS N := by exact_mod_cast this
  unfold Salt.M3Assembly.z0; omega

/-- `log(zS N) ≥ (9/20) log N - log 2` for `N ≥ N0S`. -/
lemma logZS_ge {N : ℕ} (hN : N0S ≤ N) :
    (9 / 20 : ℝ) * Real.log N - Real.log 2 ≤ Real.log (zS N) := by
  have hlow := zS_lower hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (N0S : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hp : (0 : ℝ) < (N0S : ℝ) := by rw [N0S_cast]; positivity
    linarith
  have hpos : (0 : ℝ) < (N : ℝ) ^ (9 / 20 : ℝ) / 2 := by positivity
  have hmono : Real.log ((N : ℝ) ^ (9 / 20 : ℝ) / 2) ≤ Real.log (zS N) :=
    Real.log_le_log hpos hlow
  have hlogdiv : Real.log ((N : ℝ) ^ (9 / 20 : ℝ) / 2)
      = (9 / 20) * Real.log N - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hNpos]
  linarith [hlogdiv ▸ hmono]

/-- **The sharp Selberg denominator bound.** For `N ≥ N0S`,
`selbergBoundingSum ≥ (log N)² / 88`. -/
lemma selbergBoundingSum_ge_final {N : ℕ} (hN0 : N0S ≤ N) (hN : 1 ≤ N) :
    Salt.SelbergPort.selbergBoundingSum (twinSieveSharp N hN) ≥ (Real.log N) ^ 2 / 88 := by
  have hz100 := zS_ge_100 hN0
  have hSge := selbergBoundingSum_ge_mainTermSum_sharp N hN
  have hmts := mainTermSum_ge_sharp hz100
  have hlogzs := logZS_ge hN0
  have hlogN := logN_ge hN0
  have hlog2lb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2ub : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  set L := Real.log N with hL
  set Lz := Real.log (zS N) with hLz
  have hL166 : (166 : ℝ) ≤ L := by nlinarith [hlogN, hlog2lb]
  -- A := (9/80)·L − (log2/4 + 1/2), nonneg and ≤ (1/4)Lz − 1/2
  have hApos : (0 : ℝ) ≤ (9 / 80) * L - (Real.log 2 / 4 + 1 / 2) := by
    nlinarith [hL166, hlog2ub]
  have hstep : (9 / 80) * L - (Real.log 2 / 4 + 1 / 2) ≤ (1 / 4) * Lz - 1 / 2 := by
    linarith [hlogzs]
  have hsq : ((9 / 80) * L - (Real.log 2 / 4 + 1 / 2)) ^ 2 ≤ ((1 / 4) * Lz - 1 / 2) ^ 2 :=
    pow_le_pow_left₀ hApos hstep 2
  have hfinal : ((9 / 80) * L - (Real.log 2 / 4 + 1 / 2)) ^ 2 ≥ L ^ 2 / 88 := by
    nlinarith [hL166, hlog2lb, hlog2ub, mul_nonneg (by linarith : (0:ℝ) ≤ L - 166)
      (by linarith : (0:ℝ) ≤ L)]
  linarith [hSge, hmts, hsq, hfinal]

/-! ## The counting bound (N5.2 analog), error sum left raw -/

/-- Every prime factor of `PS N` is `≤ zS N`. -/
lemma PS_prime_factors_le (N : ℕ) : ∀ q, q.Prime → q ∣ PS N → q ≤ zS N := by
  intro q hq hqP
  exact hq.dvd_primorial_iff.mp hqP

open Classical in
/-- **N5.2 (sharp).** `π₂(N) ≤ N/S + errorSum + (zS N + 1)`, where `S` is the sharp
Selberg bounding sum and `errorSum` is the raw `3^ω·|rem|` sum. -/
theorem N5_2_sharp (N : ℕ) (hN : 1 ≤ N) :
    (twinPrimeCounting N : ℝ) ≤
      (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSieveSharp N hN)
        + (∑ d ∈ (PS N).divisors,
            if (d : ℝ) ≤ yS N then
              (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N| else 0)
        + ((zS N : ℝ) + 1) := by
  have hcount : twinPrimeCounting N
      = ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card := by
    unfold twinPrimeCounting
    rw [Nat.count_eq_card_filter_range]
  set A := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime) with hAdef
  set A1 := A.filter (fun p => p ≤ zS N) with hA1def
  set A2 := A.filter (fun p => zS N < p) with hA2def
  have hAeq : A = A1 ∪ A2 := by
    rw [hA1def, hA2def]
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp; by_cases h : p ≤ zS N
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, by omega⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hAdisj : Disjoint A1 A2 := by
    rw [hA1def, hA2def, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    omega
  have hcard : A.card = A1.card + A2.card := by
    rw [hAeq, Finset.card_union_of_disjoint hAdisj]
  have hA1sub : A1 ⊆ Finset.range (zS N + 1) := by
    intro p hp
    rw [hA1def, Finset.mem_filter] at hp
    rw [Finset.mem_range]; omega
  have hA1card : A1.card ≤ zS N + 1 := by
    calc A1.card ≤ (Finset.range (zS N + 1)).card := Finset.card_le_card hA1sub
      _ = zS N + 1 := Finset.card_range _
  have hA2sub : A2 ⊆ (Finset.Icc 1 N).filter
      (fun n => zS N < n ∧ n.Prime ∧ (n + 2).Prime) := by
    intro p hp
    rw [hA2def, hAdef] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨⟨hpN, hpp, hp2⟩, hpz⟩ := hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, by omega⟩, hpz, hpp, hp2⟩
    have := hpp.pos; omega
  have hA2card_real : (A2.card : ℝ) ≤ (twinSieveSharp N hN).siftedSum := by
    rw [twinSieveSharp_siftedSum]
    have hstep1 : (A2.card : ℝ) ≤ (((Finset.Icc 1 N).filter
        (fun n => zS N < n ∧ n.Prime ∧ (n + 2).Prime)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hA2sub
    have hstep2 : (((Finset.Icc 1 N).filter
        (fun n => zS N < n ∧ n.Prime ∧ (n + 2).Prime)).card : ℝ)
        ≤ (Salt.TwinSieve.sieve N (PS N) (PS_squarefree N)).siftedSum :=
      Salt.TwinSieve.twin_count_le_siftedSum (PS_prime_factors_le N)
    exact le_trans hstep1 hstep2
  have hselberg := Salt.SelbergPort.selberg_bound_simple (twinSieveSharp N hN)
  rw [twinSieveSharp_totalMass, twinSieveSharp_prodPrimes, twinSieveSharp_level] at hselberg
  have hrem_eq : (∑ d ∈ (PS N).divisors,
      if (d : ℝ) ≤ yS N then
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |(twinSieveSharp N hN).rem d|
      else 0)
      = ∑ d ∈ (PS N).divisors,
          if (d : ℝ) ≤ yS N then
            (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N| else 0 := by
    apply Finset.sum_congr rfl
    intro d _
    rw [twinSieveSharp_rem]
  rw [hrem_eq] at hselberg
  have hcard_real : (A.card : ℝ) = (A1.card : ℝ) + (A2.card : ℝ) := by exact_mod_cast hcard
  rw [hcount, hcard_real]
  have hA1card_real : (A1.card : ℝ) ≤ (zS N : ℝ) + 1 := by exact_mod_cast hA1card
  linarith [hA1card_real, hA2card_real, hselberg]

/-! ## Small-order absorptions (isLittleO) -/

/-- **Small-prime tail absorption.** `(zS N)+1 ≤ N/(log N)²` eventually. -/
lemma zS_absorb : ∃ N₃ : ℕ, 2 ≤ N₃ ∧ ∀ N : ℕ, N₃ ≤ N →
    (zS N : ℝ) + 1 ≤ (N : ℝ) / (Real.log N) ^ 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (2:ℝ)) =o[atTop] fun x : ℝ => x ^ (11 / 20 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 11/20)
  have hbound := hlo.bound (show (0:ℝ) < 1/2 by norm_num)
  rw [eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max ⌈a⌉₊ 2, le_max_right _ _, ?_⟩
  intro N hN
  have hNa : a ≤ (N:ℝ) := by
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h2 : (⌈a⌉₊ : ℝ) ≤ (N:ℝ) := by
      have : ⌈a⌉₊ ≤ N := le_trans (le_max_left _ _) hN
      exact_mod_cast this
    linarith
  have hN2 : (2:ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hN2R : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
  have hkey := ha (N:ℝ) hNa
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogNpos : (0:ℝ) < Real.log N := Real.log_pos (by linarith)
  have habs1 : ‖Real.log N ^ (2:ℝ)‖ = Real.log N ^ (2:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habs2 : ‖(N:ℝ) ^ (11/20:ℝ)‖ = (N:ℝ) ^ (11/20:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [habs1, habs2] at hkey
  rw [Real.rpow_two] at hkey
  -- hkey : (log N)^2 ≤ (1/2) N^{11/20}
  have hzle : (zS N : ℝ) ≤ (N:ℝ) ^ (9/20:ℝ) := Nat.floor_le (by positivity)
  have hN920_ge1 : (1:ℝ) ≤ (N:ℝ) ^ (9/20:ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hzp1 : (zS N : ℝ) + 1 ≤ 2 * (N:ℝ) ^ (9/20:ℝ) := by linarith
  have hstep : 2 * (N:ℝ)^(9/20:ℝ) * (Real.log N)^2 ≤
      2 * (N:ℝ)^(9/20:ℝ) * ((1/2) * (N:ℝ)^(11/20:ℝ)) := by
    apply mul_le_mul_of_nonneg_left hkey; positivity
  have hadd : (N:ℝ)^(9/20:ℝ) * (N:ℝ)^(11/20:ℝ) = (N:ℝ) := by
    rw [← Real.rpow_add hNpos, show (9/20:ℝ) + (11/20:ℝ) = 1 by norm_num, Real.rpow_one]
  have hprod : 2 * (N:ℝ)^(9/20:ℝ) * ((1/2) * (N:ℝ)^(11/20:ℝ)) = (N:ℝ) := by
    rw [show (2:ℝ) * (N:ℝ)^(9/20:ℝ) * ((1/2) * (N:ℝ)^(11/20:ℝ))
        = (N:ℝ)^(9/20:ℝ) * (N:ℝ)^(11/20:ℝ) by ring]
    exact hadd
  rw [hprod] at hstep
  have hlogsqpos : (0:ℝ) < (Real.log N)^2 := pow_pos hlogNpos 2
  have hfinal : 2 * (N:ℝ)^(9/20:ℝ) ≤ (N:ℝ) / (Real.log N)^2 := by
    rw [le_div_iff₀ hlogsqpos]; linarith [hstep]
  linarith [hzp1, hfinal]

open Classical in
/-- **The sharp error bound.** The Selberg `3^ω·|rem|` sum is at most
`N^(9/10)·(1+log N)^6` — using the divisor-power mean value (linchpin) in place
of the crude termwise `6^ω ≤ d³`. -/
lemma sharpErrorSum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ (PS N).divisors,
        if (d : ℝ) ≤ yS N then
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N| else 0)
      ≤ (N : ℝ) ^ (9 / 10 : ℝ) * (1 + Real.log N) ^ 6 := by
  classical
  set L := ⌊yS N⌋₊ with hLdef
  have hyS1 : (1 : ℝ) ≤ yS N := by
    rw [yS]; exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Nat.le_floor (by exact_mod_cast hyS1)
  -- Subset of the mean-value index set.
  have hsub : (PS N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ yS N)
      ⊆ (Finset.Icc 1 L).filter Squarefree := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hdle⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdvd (PS_squarefree N)
    refine ⟨⟨hdsq.ne_zero.bot_lt, ?_⟩, hdsq⟩
    rw [hLdef]; exact Nat.le_floor hdle
  -- Rewrite the guarded sum as a filtered sum, then bound termwise by `6^ω`.
  rw [← Finset.sum_filter]
  calc ∑ d ∈ (PS N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ yS N),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N|
      ≤ ∑ d ∈ (PS N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ yS N),
          (6 : ℝ) ^ (d.primeFactors.card) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdvd, _⟩, _⟩ := hd
        have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdvd (PS_squarefree N)
        have hdne : d ≠ 0 := hdsq.ne_zero
        have hbridge : ArithmeticFunction.cardDistinctFactors d = d.primeFactors.card :=
          (Salt.M5Assembly.omega_eq_cardDistinctFactors d).symm
        have hrem : |_root_.rem d N| ≤ (2 : ℝ) ^ (d.primeFactors.card) := by
          have h1 : |_root_.rem d N| ≤ (rho d : ℝ) := rem_abs_le d N hdne
          have h2 : (rho d : ℝ) ≤ (2 : ℝ) ^ (_root_.omega d) := by
            exact_mod_cast rho_squarefree_le d hdsq
          have h3 : _root_.omega d = d.primeFactors.card := rfl
          rw [h3] at h2; linarith
        rw [hbridge]
        calc (3 : ℝ) ^ (d.primeFactors.card) * |_root_.rem d N|
            ≤ (3 : ℝ) ^ (d.primeFactors.card) * (2 : ℝ) ^ (d.primeFactors.card) := by
              apply mul_le_mul_of_nonneg_left hrem (by positivity)
          _ = (6 : ℝ) ^ (d.primeFactors.card) := by rw [← mul_pow]; norm_num
    _ ≤ ∑ d ∈ (Finset.Icc 1 L).filter Squarefree, (6 : ℝ) ^ (d.primeFactors.card) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
    _ ≤ (L : ℝ) * (1 + Real.log L) ^ 6 := sum_six_pow_omega_le L
    _ ≤ (N : ℝ) ^ (9 / 10 : ℝ) * (1 + Real.log N) ^ 6 := by
        -- bridge L = ⌊N^(9/10)⌋ ≤ N^(9/10) ≤ N
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hLle : (L : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by
          rw [hLdef, yS]; exact Nat.floor_le (by positivity)
        have hN910leN : (N : ℝ) ^ (9 / 10 : ℝ) ≤ (N : ℝ) := by
          calc (N : ℝ) ^ (9 / 10 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
            _ = (N : ℝ) := Real.rpow_one _
        have hLleN : (L : ℝ) ≤ (N : ℝ) := le_trans hLle hN910leN
        have hLpos : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
        have hlogLle : Real.log L ≤ Real.log N :=
          Real.log_le_log (by linarith) hLleN
        have hloglnn : (0 : ℝ) ≤ 1 + Real.log L := by
          have := Real.log_nonneg hLpos; linarith
        have hpow6 : (1 + Real.log L) ^ 6 ≤ (1 + Real.log N) ^ 6 :=
          pow_le_pow_left₀ hloglnn (by linarith) 6
        apply mul_le_mul hLle hpow6 (by positivity) (by positivity)

/-- **Error-term absorption.** `N^(9/10)·(1+log N)^6 ≤ N/(log N)²` eventually. -/
lemma err_absorb : ∃ N₄ : ℕ, 3 ≤ N₄ ∧ ∀ N : ℕ, N₄ ≤ N →
    (N : ℝ) ^ (9 / 10 : ℝ) * (1 + Real.log N) ^ 6 ≤ (N : ℝ) / (Real.log N) ^ 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (8:ℝ)) =o[atTop] fun x : ℝ => x ^ (1 / 10 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 8 (by norm_num : (0:ℝ) < 1/10)
  have hbound := hlo.bound (show (0:ℝ) < 1/64 by norm_num)
  rw [eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max ⌈a⌉₊ 3, le_max_right _ _, ?_⟩
  intro N hN
  have hNa : a ≤ (N:ℝ) := by
    have h1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have h2 : (⌈a⌉₊ : ℝ) ≤ (N:ℝ) := by
      have : ⌈a⌉₊ ≤ N := le_trans (le_max_left _ _) hN
      exact_mod_cast this
    linarith
  have hN3 : (3:ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hN3R : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
  have hkey := ha (N:ℝ) hNa
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogNpos : (0:ℝ) < Real.log N := Real.log_pos (by linarith)
  have hL1 : (1:ℝ) ≤ Real.log N := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have habs1 : ‖Real.log N ^ (8:ℝ)‖ = Real.log N ^ (8:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habs2 : ‖(N:ℝ) ^ (1/10:ℝ)‖ = (N:ℝ) ^ (1/10:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [habs1, habs2] at hkey
  -- hkey : (log N)^(8:ℝ) ≤ (1/64) N^{1/10}
  have hL8 : (Real.log N) ^ (8:ℕ) ≤ (1/64) * (N:ℝ)^(1/10:ℝ) := by
    rw [← Real.rpow_natCast (Real.log N) 8]; push_cast; exact hkey
  -- (1+L)^6 ≤ (2L)^6 = 64 L^6
  have h1L : (1 : ℝ) + Real.log N ≤ 2 * Real.log N := by linarith
  have hpow : (1 + Real.log N) ^ 6 ≤ 64 * (Real.log N) ^ 6 := by
    calc (1 + Real.log N) ^ 6 ≤ (2 * Real.log N) ^ 6 :=
          pow_le_pow_left₀ (by linarith) h1L 6
      _ = 64 * (Real.log N) ^ 6 := by ring
  have hlog6pos : (0:ℝ) ≤ (Real.log N) ^ 6 := by positivity
  have hN910pos : (0:ℝ) < (N:ℝ)^(9/10:ℝ) := by positivity
  -- N^{9/10}(1+L)^6 ≤ N^{9/10}·64 L^6 ; and 64 L^6·L² = 64 L^8 ≤ N^{1/10}
  have hlogsqpos : (0:ℝ) < (Real.log N)^2 := pow_pos hlogNpos 2
  have hadd : (N:ℝ)^(9/10:ℝ) * (N:ℝ)^(1/10:ℝ) = (N:ℝ) := by
    rw [← Real.rpow_add hNpos, show (9/10:ℝ) + (1/10:ℝ) = 1 by norm_num, Real.rpow_one]
  rw [le_div_iff₀ hlogsqpos]
  calc (N:ℝ)^(9/10:ℝ) * (1 + Real.log N)^6 * (Real.log N)^2
      ≤ (N:ℝ)^(9/10:ℝ) * (64 * (Real.log N)^6) * (Real.log N)^2 := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hlogsqpos)
        exact mul_le_mul_of_nonneg_left hpow (le_of_lt hN910pos)
    _ = (N:ℝ)^(9/10:ℝ) * (64 * (Real.log N)^(8:ℕ)) := by ring
    _ ≤ (N:ℝ)^(9/10:ℝ) * (64 * ((1/64) * (N:ℝ)^(1/10:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hN910pos)
        apply mul_le_mul_of_nonneg_left hL8 (by norm_num)
    _ = (N:ℝ)^(9/10:ℝ) * (N:ℝ)^(1/10:ℝ) := by ring
    _ = (N:ℝ) := hadd

/-! ## Final assembly -/

/-- **Sharp absorption.** `π₂(N) ≤ 90·N/(log N)²` for all large `N`. -/
lemma nat_absorb_sharp : ∃ N₁ : ℕ, ∀ N ≥ N₁,
    (twinPrimeCounting N : ℝ) ≤ 90 * (N : ℝ) / (Real.log N) ^ 2 := by
  obtain ⟨N₃, _, hN₃⟩ := zS_absorb
  obtain ⟨N₄, _, hN₄⟩ := err_absorb
  refine ⟨max N0S (max N₃ N₄), fun N hN => ?_⟩
  have hN0 : N0S ≤ N := le_trans (le_max_left _ _) hN
  have hN3' : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4' : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have h2N0 : (2 : ℕ) ≤ N0S := by rw [N0S]; norm_num
  have hN1 : 1 ≤ N := by omega
  have h2N : (2 : ℝ) ≤ (N : ℝ) := by
    have : (2 : ℕ) ≤ N := le_trans h2N0 hN0
    exact_mod_cast this
  have hlogNpos : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hlogsqpos : (0 : ℝ) < (Real.log N) ^ 2 := pow_pos hlogNpos 2
  set X : ℝ := (N : ℝ) / (Real.log N) ^ 2 with hXdef
  have hS := selbergBoundingSum_ge_final hN0 hN1
  have hLpos : (0 : ℝ) < (Real.log N) ^ 2 / 88 := by positivity
  have hcount := N5_2_sharp N hN1
  have herr := sharpErrorSum_le N hN1
  have herr2 := hN₄ N hN4'
  have hz2 := hN₃ N hN3'
  -- N / S ≤ 88 X
  have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ)) hLpos hS
  have hNS : (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSieveSharp N hN1) ≤ 88 * X := by
    have heq : (N : ℝ) / ((Real.log N) ^ 2 / 88) = 88 * X := by
      rw [hXdef]; field_simp
    linarith [heq ▸ hdiv]
  -- assemble
  have hfinal : 90 * (N : ℝ) / (Real.log N) ^ 2 = 90 * X := by rw [hXdef]; ring
  rw [hfinal]
  linarith [hcount, hNS, herr, herr2, hz2]

/-- **HL-3b — the sharp-order twin upper bound.** There is an explicit constant
`C ≤ 100` (here `C = 90`) with `twinPrimeCounting N ≤ C·N/(log N)²` for all large
`N`.  This improves the landed `C = 25700` by a factor ≈ 285, using the sharp
Selberg denominator (harmonic-square constant `1/16`) at level `N^(9/10)` together
with the divisor-power mean-value error bound. -/
theorem twinCounting_upper_sharp :
    ∃ C : ℝ, C ≤ 100 ∧ 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (twinPrimeCounting N : ℝ) ≤ C * (N : ℝ) / (Real.log N) ^ 2 := by
  obtain ⟨N₁, hN₁⟩ := nat_absorb_sharp
  refine ⟨90, by norm_num, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N₁] with N hN
  exact hN₁ N hN

end Salt.HardyLittlewood
