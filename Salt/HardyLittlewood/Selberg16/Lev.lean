/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16

/-! # HL-3c node M6a — the twin Selberg sieve at level `N^(1−δ)`

A copy of `Sharp.lean`'s sieve with the level exponent symbolic: level `y = N^(1−δ)`,
truncation `z = ⌊N^((1−δ)/2)⌋`. `Sharp.lean` itself is merged and is not edited.

* `twin_le_sel` — `π₂(N) ≤ N/S + η·N/(log N)²` eventually, for every `η > 0`
  (the remainder `Σ 3^ω|r_d|` via `sum_six_pow_omega_le`, plus the `z + 1` small primes).
* `selbergBoundingSum_sel_ge` — `S ≥ mainTermSum z + mainTermSum (z/2)`: odd `ℓ` and
  `2ℓ` both contribute `gTwin ℓ`, since `selbergTerms 2 = 1`.
-/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-- Sieve level `N^(1−δ)`. -/
noncomputable def ySel (δ : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (1 - δ)

/-- Truncation `⌊N^((1−δ)/2)⌋₊`. -/
noncomputable def zSel (δ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ ((1 - δ) / 2)⌋₊

/-- Sift modulus. -/
noncomputable def PSel (δ : ℝ) (N : ℕ) : ℕ := primorial (zSel δ N)

lemma PSel_squarefree (δ : ℝ) (N : ℕ) : Squarefree (PSel δ N) :=
  Salt.M5Assembly.primorial_squarefree (zSel δ N)

/-- The twin Selberg sieve at level `N^(1−δ)`. -/
noncomputable def twinSieveSel (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) : SelbergSieve where
  toBoundingSieve := Salt.TwinSieve.sieve N (PSel δ N) (PSel_squarefree δ N)
  level := ySel δ N
  one_le_level := by
    unfold ySel
    exact Real.one_le_rpow (by exact_mod_cast hN) (by linarith)

@[simp] lemma twinSieveSel_prodPrimes (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSel δ hδ N hN).prodPrimes = PSel δ N := rfl

@[simp] lemma twinSieveSel_totalMass (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSel δ hδ N hN).totalMass = (N : ℝ) := rfl

@[simp] lemma twinSieveSel_level (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSel δ hδ N hN).level = ySel δ N := rfl

lemma twinSieveSel_selbergTerms (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSel δ hδ N hN).selbergTerms
      = (Salt.TwinSieve.sieve N (PSel δ N) (PSel_squarefree δ N)).selbergTerms := rfl

lemma twinSieveSel_rem (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) (d : ℕ) :
    (twinSieveSel δ hδ N hN).rem d = _root_.rem d N := by
  change (Salt.TwinSieve.sieve N (PSel δ N) (PSel_squarefree δ N)).rem d = _root_.rem d N
  exact Salt.TwinSieve.sieve_rem d

lemma twinSieveSel_siftedSum (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (twinSieveSel δ hδ N hN).siftedSum
      = (Salt.TwinSieve.sieve N (PSel δ N) (PSel_squarefree δ N)).siftedSum := rfl

/-- `(zSel)² ≤ ySel`. -/
lemma zSel_sq_le_ySel (δ : ℝ) (N : ℕ) : ((zSel δ N : ℝ)) ^ 2 ≤ ySel δ N := by
  have hzR : (zSel δ N : ℝ) ≤ (N : ℝ) ^ ((1 - δ) / 2) := Nat.floor_le (by positivity)
  have hnn : (0 : ℝ) ≤ (zSel δ N : ℝ) := Nat.cast_nonneg _
  calc ((zSel δ N : ℝ)) ^ 2 ≤ ((N : ℝ) ^ ((1 - δ) / 2)) ^ 2 := pow_le_pow_left₀ hnn hzR 2
    _ = ySel δ N := by
      rw [ySel, ← Real.rpow_natCast ((N : ℝ) ^ ((1 - δ) / 2)) 2,
        ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1; push_cast; ring

/-- A squarefree `d < zSel` divides `PSel`. -/
lemma dvd_PSel_of_lt {δ : ℝ} {N d : ℕ} (hd : Squarefree d) (hdz : d < zSel δ N) :
    d ∣ PSel δ N :=
  (Squarefree.dvd_primorial hd).trans (primorial_dvd_primorial (le_of_lt hdz))

/-- `d < zSel` puts `d` in the Selberg range `d² ≤ ySel`. -/
lemma sq_le_ySel_of_lt {δ : ℝ} {N d : ℕ} (hdz : d < zSel δ N) :
    (d : ℝ) ^ 2 ≤ ySel δ N := by
  have hR : (d : ℝ) ≤ (zSel δ N : ℝ) := by exact_mod_cast (le_of_lt hdz)
  exact le_trans (pow_le_pow_left₀ (Nat.cast_nonneg d) hR 2) (zSel_sq_le_ySel δ N)

/-- Every prime factor of `PSel` is `≤ zSel`. -/
lemma PSel_prime_factors_le (δ : ℝ) (N : ℕ) :
    ∀ q, q.Prime → q ∣ PSel δ N → q ≤ zSel δ N := by
  intro q hq hqP
  exact hq.dvd_primorial_iff.mp hqP

open Classical in
/-- **N5.2 at level `N^(1−δ)`.** `π₂(N) ≤ N/S + errorSum + (zSel + 1)`. -/
theorem N5_2_sel (δ : ℝ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (twinPrimeCounting N : ℝ) ≤
      (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSieveSel δ hδ N hN)
        + (∑ d ∈ (PSel δ N).divisors,
            if (d : ℝ) ≤ ySel δ N then
              (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N| else 0)
        + ((zSel δ N : ℝ) + 1) := by
  have hcount : twinPrimeCounting N
      = ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card := by
    unfold twinPrimeCounting
    rw [Nat.count_eq_card_filter_range]
  set A := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime) with hAdef
  set A1 := A.filter (fun p => p ≤ zSel δ N) with hA1def
  set A2 := A.filter (fun p => zSel δ N < p) with hA2def
  have hAeq : A = A1 ∪ A2 := by
    rw [hA1def, hA2def]
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp; by_cases h : p ≤ zSel δ N
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
  have hA1sub : A1 ⊆ Finset.range (zSel δ N + 1) := by
    intro p hp
    rw [hA1def, Finset.mem_filter] at hp
    rw [Finset.mem_range]; omega
  have hA1card : A1.card ≤ zSel δ N + 1 := by
    calc A1.card ≤ (Finset.range (zSel δ N + 1)).card := Finset.card_le_card hA1sub
      _ = zSel δ N + 1 := Finset.card_range _
  have hA2sub : A2 ⊆ (Finset.Icc 1 N).filter
      (fun n => zSel δ N < n ∧ n.Prime ∧ (n + 2).Prime) := by
    intro p hp
    rw [hA2def, hAdef] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨⟨hpN, hpp, hp2⟩, hpz⟩ := hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, by omega⟩, hpz, hpp, hp2⟩
    have := hpp.pos; omega
  have hA2card_real : (A2.card : ℝ) ≤ (twinSieveSel δ hδ N hN).siftedSum := by
    rw [twinSieveSel_siftedSum]
    have hstep1 : (A2.card : ℝ) ≤ (((Finset.Icc 1 N).filter
        (fun n => zSel δ N < n ∧ n.Prime ∧ (n + 2).Prime)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hA2sub
    have hstep2 : (((Finset.Icc 1 N).filter
        (fun n => zSel δ N < n ∧ n.Prime ∧ (n + 2).Prime)).card : ℝ)
        ≤ (Salt.TwinSieve.sieve N (PSel δ N) (PSel_squarefree δ N)).siftedSum :=
      Salt.TwinSieve.twin_count_le_siftedSum (PSel_prime_factors_le δ N)
    exact le_trans hstep1 hstep2
  have hselberg := Salt.SelbergPort.selberg_bound_simple (twinSieveSel δ hδ N hN)
  rw [twinSieveSel_totalMass, twinSieveSel_prodPrimes, twinSieveSel_level] at hselberg
  have hrem_eq : (∑ d ∈ (PSel δ N).divisors,
      if (d : ℝ) ≤ ySel δ N then
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |(twinSieveSel δ hδ N hN).rem d|
      else 0)
      = ∑ d ∈ (PSel δ N).divisors,
          if (d : ℝ) ≤ ySel δ N then
            (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N| else 0 := by
    apply Finset.sum_congr rfl
    intro d _
    rw [twinSieveSel_rem]
  rw [hrem_eq] at hselberg
  have hcard_real : (A.card : ℝ) = (A1.card : ℝ) + (A2.card : ℝ) := by exact_mod_cast hcard
  rw [hcount, hcard_real]
  have hA1card_real : (A1.card : ℝ) ≤ (zSel δ N : ℝ) + 1 := by exact_mod_cast hA1card
  linarith [hA1card_real, hA2card_real, hselberg]

open Classical in
/-- **The error bound at level `N^(1−δ)`.** The `3^ω·|rem|` sum is at most
`N^(1−δ)·(1+log N)^6`, via the divisor-power mean value. -/
lemma selErrorSum_le {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ (PSel δ N).divisors,
        if (d : ℝ) ≤ ySel δ N then
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N| else 0)
      ≤ (N : ℝ) ^ (1 - δ) * (1 + Real.log N) ^ 6 := by
  classical
  set L := ⌊ySel δ N⌋₊ with hLdef
  have hy1 : (1 : ℝ) ≤ ySel δ N := by
    rw [ySel]; exact Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Nat.le_floor (by exact_mod_cast hy1)
  have hsub : (PSel δ N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ ySel δ N)
      ⊆ (Finset.Icc 1 L).filter Squarefree := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hdle⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdvd (PSel_squarefree δ N)
    refine ⟨⟨hdsq.ne_zero.bot_lt, ?_⟩, hdsq⟩
    rw [hLdef]; exact Nat.le_floor hdle
  rw [← Finset.sum_filter]
  calc ∑ d ∈ (PSel δ N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ ySel δ N),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) * |_root_.rem d N|
      ≤ ∑ d ∈ (PSel δ N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ ySel δ N),
          (6 : ℝ) ^ (d.primeFactors.card) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdvd, _⟩, _⟩ := hd
        have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdvd (PSel_squarefree δ N)
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
    _ ≤ (N : ℝ) ^ (1 - δ) * (1 + Real.log N) ^ 6 := by
        have hLle : (L : ℝ) ≤ (N : ℝ) ^ (1 - δ) := by
          rw [hLdef, ySel]; exact Nat.floor_le (by positivity)
        have hNleN : (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) := by
          calc (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
            _ = (N : ℝ) := Real.rpow_one _
        have hLleN : (L : ℝ) ≤ (N : ℝ) := le_trans hLle hNleN
        have hLpos : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
        have hlogLle : Real.log L ≤ Real.log N := Real.log_le_log (by linarith) hLleN
        have hloglnn : (0 : ℝ) ≤ 1 + Real.log L := by
          have := Real.log_nonneg hLpos; linarith
        have hpow6 : (1 + Real.log L) ^ 6 ≤ (1 + Real.log N) ^ 6 :=
          pow_le_pow_left₀ hloglnn (by linarith) 6
        exact mul_le_mul hLle hpow6 (by positivity) (by positivity)

/-- **Error-term absorption at level `N^(1−δ)`.**
`3·N^(1−δ)·(1+log N)^6 ≤ η·N/(log N)²` eventually. -/
lemma err_absorb_sel {δ η : ℝ} (hδ0 : 0 < δ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      3 * ((N : ℝ) ^ (1 - δ) * (1 + Real.log N) ^ 6) ≤ η * N / (Real.log N) ^ 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (8:ℝ)) =o[atTop] fun x : ℝ => x ^ δ :=
    isLittleO_log_rpow_rpow_atTop 8 hδ0
  have hbound := hlo.bound (show (0:ℝ) < η / 192 by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound
  filter_upwards [hnat, eventually_ge_atTop 3] with N hkey hN3
  have hN3R : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogNpos : (0:ℝ) < Real.log N := Real.log_pos (by linarith)
  have hL1 : (1:ℝ) ≤ Real.log N := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have habs1 : ‖Real.log N ^ (8:ℝ)‖ = Real.log N ^ (8:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habs2 : ‖(N:ℝ) ^ δ‖ = (N:ℝ) ^ δ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [habs1, habs2] at hkey
  have hL8 : (Real.log N) ^ (8:ℕ) ≤ (η / 192) * (N:ℝ) ^ δ := by
    rw [← Real.rpow_natCast (Real.log N) 8]; push_cast; exact hkey
  have h1L : (1 : ℝ) + Real.log N ≤ 2 * Real.log N := by linarith
  have hpow : (1 + Real.log N) ^ 6 ≤ 64 * (Real.log N) ^ 6 := by
    calc (1 + Real.log N) ^ 6 ≤ (2 * Real.log N) ^ 6 :=
          pow_le_pow_left₀ (by linarith) h1L 6
      _ = 64 * (Real.log N) ^ 6 := by ring
  have hNdpos : (0:ℝ) < (N:ℝ) ^ (1 - δ) := by positivity
  have hlogsqpos : (0:ℝ) < (Real.log N) ^ 2 := pow_pos hlogNpos 2
  have hadd : (N:ℝ) ^ (1 - δ) * (N:ℝ) ^ δ = (N:ℝ) := by
    rw [← Real.rpow_add hNpos, show (1 - δ) + δ = (1:ℝ) by ring, Real.rpow_one]
  rw [le_div_iff₀ hlogsqpos]
  calc 3 * ((N:ℝ) ^ (1 - δ) * (1 + Real.log N) ^ 6) * (Real.log N) ^ 2
      ≤ 3 * ((N:ℝ) ^ (1 - δ) * (64 * (Real.log N) ^ 6)) * (Real.log N) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hlogsqpos)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hpow (le_of_lt hNdpos)
    _ = 192 * (N:ℝ) ^ (1 - δ) * (Real.log N) ^ (8:ℕ) := by ring
    _ ≤ 192 * (N:ℝ) ^ (1 - δ) * ((η / 192) * (N:ℝ) ^ δ) := by
        apply mul_le_mul_of_nonneg_left hL8 (by positivity)
    _ = η * ((N:ℝ) ^ (1 - δ) * (N:ℝ) ^ δ) := by ring
    _ = η * N := by rw [hadd]

/-- The small-prime tail is dominated by the error shape: `zSel + 1 ≤ 2·N^(1−δ)(1+log N)^6`. -/
lemma zSel_add_one_le {δ : ℝ} (hδ1 : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (zSel δ N : ℝ) + 1 ≤ 2 * ((N : ℝ) ^ (1 - δ) * (1 + Real.log N) ^ 6) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hz : (zSel δ N : ℝ) ≤ (N : ℝ) ^ ((1 - δ) / 2) := Nat.floor_le (by positivity)
  have hmono : (N : ℝ) ^ ((1 - δ) / 2) ≤ (N : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - δ) := Real.one_le_rpow hN1 (by linarith)
  have hlog : (1 : ℝ) ≤ (1 + Real.log N) ^ 6 :=
    one_le_pow₀ (by have := Real.log_natCast_nonneg N; linarith)
  have hA : (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) ^ (1 - δ) * (1 + Real.log N) ^ 6 :=
    le_mul_of_one_le_right (by linarith) hlog
  linarith

/-- **M6a-1. The counting bound with the remainder absorbed.** -/
theorem twin_le_sel {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ hN : 1 ≤ N,
      (twinPrimeCounting N : ℝ) ≤
        (N : ℝ) / Salt.SelbergPort.selbergBoundingSum (twinSieveSel δ hδ1 N hN)
          + η * N / (Real.log N) ^ 2 := by
  filter_upwards [err_absorb_sel hδ0 hη] with N hE
  intro hN
  have hcount := N5_2_sel δ hδ1 N hN
  have herr := selErrorSum_le hδ0 hδ1 N hN
  have hz := zSel_add_one_le hδ1 N hN
  linarith

/-- **M6a-2. The even-divisor denominator bound.** -/
theorem selbergBoundingSum_sel_ge {δ : ℝ} (hδ1 : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    Salt.M3Assembly.mainTermSum (zSel δ N) + Salt.M3Assembly.mainTermSum (zSel δ N / 2)
      ≤ Salt.SelbergPort.selbergBoundingSum (twinSieveSel δ hδ1 N hN) := by
  classical
  set sv := Salt.TwinSieve.sieve N (PSel δ N) (PSel_squarefree δ N) with hsv
  rw [Salt.SelbergPort.selbergBoundingSum, twinSieveSel_prodPrimes, twinSieveSel_level,
    ← Finset.sum_filter, twinSieveSel_selbergTerms, ← hsv]
  rw [Salt.M3Assembly.mainTermSum, Salt.M3Assembly.mainTermSum]
  set z := zSel δ N with hz
  set small : Finset ℕ := (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) with hsmall
  set half : Finset ℕ := (Finset.range (z / 2)).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
    with hhalf
  set evens : Finset ℕ := half.image (fun ℓ => 2 * ℓ) with hevens
  set big : Finset ℕ := (PSel δ N).divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ ySel δ N)
    with hbig
  -- facts about the even members
  have hev : ∀ ℓ ∈ half, 2 * ℓ < z ∧ Squarefree (2 * ℓ) ∧ Odd ℓ ∧ Squarefree ℓ := by
    intro ℓ hℓ
    rw [hhalf, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hodd, hsq⟩ := hℓ
    refine ⟨by omega, ?_, hodd, hsq⟩
    exact Nat.squarefree_mul_iff.mpr ⟨Nat.coprime_two_left.mpr hodd, Nat.prime_two.squarefree, hsq⟩
  have hsmall_sub : small ⊆ big := by
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, _, hℓsq⟩ := hℓ
    rw [hbig, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_PSel_of_lt hℓsq hℓz, (PSel_squarefree δ N).ne_zero⟩, sq_le_ySel_of_lt hℓz⟩
  have hevens_sub : evens ⊆ big := by
    intro d hd
    rw [hevens, Finset.mem_image] at hd
    obtain ⟨ℓ, hℓ, rfl⟩ := hd
    obtain ⟨hlt, hsq2, _, _⟩ := hev ℓ hℓ
    rw [hbig, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_PSel_of_lt hsq2 hlt, (PSel_squarefree δ N).ne_zero⟩, sq_le_ySel_of_lt hlt⟩
  have hdisj : Disjoint small evens := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [hsmall, Finset.mem_filter] at hd1
    rw [hevens, Finset.mem_image] at hd2
    obtain ⟨ℓ, _, rfl⟩ := hd2
    exact (Nat.not_even_iff_odd.mpr hd1.2.1) (even_two_mul ℓ)
  have heq1 : ∑ ℓ ∈ small, Salt.M3Expansion.gTwin ℓ = ∑ ℓ ∈ small, sv.selbergTerms ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [hsmall, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓ
    exact (Salt.TwinSieve.selbergTerms_eq_gTwin (dvd_PSel_of_lt hℓsq hℓz) hℓodd hℓsq).symm
  have heq2 : ∑ ℓ ∈ half, Salt.M3Expansion.gTwin ℓ = ∑ d ∈ evens, sv.selbergTerms d := by
    rw [hevens, Finset.sum_image (fun a _ b _ h => by omega)]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    obtain ⟨hlt, hsq2, hodd, hsq⟩ := hev ℓ hℓ
    have hdvd2 : 2 * ℓ ∣ PSel δ N := dvd_PSel_of_lt hsq2 hlt
    have hℓP : ℓ ∣ PSel δ N := (Dvd.intro_left 2 rfl).trans hdvd2
    rw [sv.selbergTerms_isMultiplicative.map_mul_of_coprime (Nat.coprime_two_left.mpr hodd),
      hsv, Salt.TwinSieve.selbergTerms_two, one_mul,
      Salt.TwinSieve.selbergTerms_eq_gTwin hℓP hodd hsq]
  rw [heq1, heq2, ← Finset.sum_union hdisj]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hsmall_sub hevens_sub)
  intro l hl _
  rw [hbig, Finset.mem_filter, Nat.mem_divisors] at hl
  exact le_of_lt (sv.selbergTerms_pos hl.1.1)

end Salt.HardyLittlewood.Sel
