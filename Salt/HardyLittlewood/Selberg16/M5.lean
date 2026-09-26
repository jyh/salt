/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HardyLittlewood.Selberg16.M2
import Salt.HardyLittlewood.Selberg16.M3
import Salt.HardyLittlewood.Selberg16.M4

/-! # HL-3c nodes M5a, M5 — the dimension-2 mean value

Statements frozen at salt `66fd0d0d`. -/

open Finset Filter

namespace Salt.HardyLittlewood.Sel

/-! ## M5a helpers -/

lemma m5_card_antidiag (k : ℕ) : k.divisorsAntidiagonal.card = k.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

lemma m5_pow2Omega_div_nonneg (n : ℕ) : 0 ≤ pow2Omega n / n := by
  unfold pow2Omega
  split_ifs <;> positivity

/-- The pairs of `oddDivSum`. -/
lemma m5_oddDivSum_eq (Y : ℕ) :
    oddDivSum Y = ∑ p ∈ (((Icc 1 Y).filter Odd) ×ˢ ((Icc 1 Y).filter Odd)).filter
        (fun p => p.1 * p.2 ≤ Y), 1 / ((p.1 : ℝ) * p.2) := by
  rw [oddDivSum, ← Finset.sum_product', Finset.sum_filter]

/-- One fiber: the pairs `(a, b)` with `m·a·b = n` contribute at most `τ(n/m)·m/n`. -/
lemma m5_fiber_le (m n Y : ℕ) (hm : 0 < m) (hn : 0 < n) :
    betaT m / m * ∑ p ∈ ((((Icc 1 Y).filter Odd) ×ˢ ((Icc 1 Y).filter Odd)).filter
        (fun p => p.1 * p.2 ≤ Y)).filter (fun p => m * p.1 * p.2 = n),
        1 / ((p.1 : ℝ) * p.2)
      ≤ if m ∣ n then betaT m * ((n / m).divisors.card : ℝ) / n else 0 := by
  set F := ((((Icc 1 Y).filter Odd) ×ˢ ((Icc 1 Y).filter Odd)).filter
        (fun p => p.1 * p.2 ≤ Y)).filter (fun p => m * p.1 * p.2 = n) with hF
  by_cases hmn : m ∣ n
  · obtain ⟨k, rfl⟩ := hmn
    have hk : 0 < k := Nat.pos_of_mul_pos_left hn
    rw [if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm]
    have hconst : ∀ p ∈ F, 1 / ((p.1 : ℝ) * p.2) = 1 / (k : ℝ) := by
      intro p hp
      have h1 : m * p.1 * p.2 = m * k := (Finset.mem_filter.mp hp).2
      have h2 : p.1 * p.2 = k := by
        rw [mul_assoc] at h1; exact Nat.eq_of_mul_eq_mul_left hm h1
      rw [← h2]; push_cast; ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hsub : F ⊆ k.divisorsAntidiagonal := by
      intro p hp
      have h1 : m * p.1 * p.2 = m * k := (Finset.mem_filter.mp hp).2
      rw [mul_assoc] at h1
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.eq_of_mul_eq_mul_left hm h1, hk.ne'⟩
    have hcard : (F.card : ℝ) ≤ (k.divisors.card : ℝ) := by
      rw [← m5_card_antidiag]; exact_mod_cast Finset.card_le_card hsub
    have hb := betaT_nonneg m
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    rw [show betaT m / m * (F.card * (1 / (k : ℝ))) = betaT m * F.card / ((m * k : ℕ) : ℝ) by
      push_cast; field_simp]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hcard hb
  · rw [if_neg hmn]
    have hempty : F = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have h1 : m * p.1 * p.2 = n := (Finset.mem_filter.mp hp).2
      exact hmn ⟨p.1 * p.2, by rw [← h1, mul_assoc]⟩
    rw [hempty]; simp

/-! ## M5a — the convolution lower bound (M1 · M2 · a finite `m`-range) -/

/-- **M5a.** For odd `R`, `Σ_{n<x odd} 2^Ω(n)/n ≥ Σ_{m ∣ R} β(m)/m · oddDivSum((x−1)/m)`. -/
theorem oddOmegaSum_ge_conv (R x : ℕ) (hR : Odd R) :
    ∑ m ∈ R.divisors, betaT m / m * oddDivSum ((x - 1) / m) ≤ oddOmegaSum x := by
  set T := (Finset.range x).filter Odd with hT
  set g : ℕ → ℕ → ℝ := fun m n =>
    if m ∣ n then betaT m * ((n / m).divisors.card : ℝ) / n else 0 with hg
  -- step 1: each `m`-term is at most `Σ_{n ∈ T} g m n`
  have step1 : ∀ m ∈ R.divisors, betaT m / m * oddDivSum ((x - 1) / m) ≤ ∑ n ∈ T, g m n := by
    intro m hmR
    have hm : 0 < m := Nat.pos_of_mem_divisors hmR
    have hmodd : Odd m := hR.of_dvd_nat (Nat.dvd_of_mem_divisors hmR)
    set Y := (x - 1) / m with hY
    rw [m5_oddDivSum_eq]
    set P := (((Icc 1 Y).filter Odd) ×ˢ ((Icc 1 Y).filter Odd)).filter
        (fun p => p.1 * p.2 ≤ Y) with hP
    have hmaps : ∀ p ∈ P, m * p.1 * p.2 ∈ T := by
      intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨⟨ha1, _⟩, hao⟩, ⟨⟨hb1, _⟩, hbo⟩⟩, hab⟩ := hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, (hmodd.mul hao).mul hbo⟩
      have h1 : m * (p.1 * p.2) ≤ x - 1 :=
        le_trans (Nat.mul_le_mul_left m hab) (Nat.mul_div_le (x - 1) m)
      have h2 : 1 ≤ p.1 * p.2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h3 : 1 ≤ m * (p.1 * p.2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [mul_assoc]; omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : 0 < n := (Finset.mem_filter.mp hn).2.pos
    exact m5_fiber_le m n Y hm hn0
  -- step 2: swap and enlarge `R.divisors ∩ {m ∣ n}` to `n.divisors`
  have step2 : ∀ n ∈ T, ∑ m ∈ R.divisors, g m n ≤ pow2Omega n / n := by
    intro n hn
    have hnodd : Odd n := (Finset.mem_filter.mp hn).2
    have hn0 : n ≠ 0 := hnodd.pos.ne'
    rw [pow2Omega_eq_sum n hnodd, Finset.sum_div]
    have : ∑ m ∈ R.divisors, g m n
        = ∑ m ∈ R.divisors.filter (· ∣ n), betaT m * ((n / m).divisors.card : ℝ) / n := by
      rw [Finset.sum_filter]
    rw [this]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2, hn0⟩
    · intro m _ _
      have := betaT_nonneg m
      positivity
  calc ∑ m ∈ R.divisors, betaT m / m * oddDivSum ((x - 1) / m)
      ≤ ∑ m ∈ R.divisors, ∑ n ∈ T, g m n := Finset.sum_le_sum step1
    _ = ∑ n ∈ T, ∑ m ∈ R.divisors, g m n := Finset.sum_comm
    _ ≤ ∑ n ∈ T, pow2Omega n / n := Finset.sum_le_sum step2
    _ ≤ oddOmegaSum x := by
      rw [oddOmegaSum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => m5_pow2Omega_div_nonneg n)

/-! ## M5 — the dimension-2 mean value -/

/-- **M5. The mean value.** `mainTermSum z ≥ (1−η)·(log z)²/(8·Π₂)` for all large `z`. -/
theorem mainTermSum_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ z : ℕ in atTop,
      (1 - η) * (Real.log z) ^ 2 / (8 * Pi2) ≤ Salt.M3Assembly.mainTermSum z := by
  have hPi : 0 < Pi2 := pi2_pos
  obtain ⟨A, hA0, hA⟩ := oddDivSum_ge
  obtain ⟨R, hRodd, hRsum⟩ := betaSum_ge (half_pos hη)
  have hR1 : 1 ≤ R := hRodd.pos
  have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  set K := Real.log (2 * (R : ℝ)) with hK
  have hK0 : 0 ≤ K := Real.log_nonneg (by linarith)
  set M := max (max 1 K) (16 * (K / 4 + 2 * A) / η) with hM
  have hlog : ∀ᶠ z : ℕ in atTop, M ≤ Real.log z :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M
  filter_upwards [hlog, Filter.eventually_ge_atTop (R + 2)] with z hzlog hzR
  have hmain : oddOmegaSum z ≤ Salt.M3Assembly.mainTermSum z := mainTermSum_ge_oddOmegaSum z
  have hconv := oddOmegaSum_ge_conv R z hRodd
  have hoo : 0 ≤ oddOmegaSum z :=
    Finset.sum_nonneg (fun n _ => m5_pow2Omega_div_nonneg n)
  rcases le_or_gt 1 η with h1 | h1
  · have : (1 - η) * (Real.log z) ^ 2 / (8 * Pi2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    linarith
  set T := Real.log z with hTdef
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hzlog
  have hTK : K ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hzlog
  have hTη : 16 * (K / 4 + 2 * A) / η ≤ T := le_trans (le_max_right _ _) hzlog
  set L := (T - K) ^ 2 / 8 - A * (T + 1) with hL
  have hz0 : (0 : ℝ) < z := by
    have : (1 : ℕ) ≤ z := by omega
    exact_mod_cast this
  -- the per-`m` bound
  have hper : ∀ m ∈ R.divisors, L ≤ oddDivSum ((z - 1) / m) := by
    intro m hm
    have hm0 : 0 < m := Nat.pos_of_mem_divisors hm
    have hmR : m ≤ R := Nat.divisor_le hm
    set y := (z - 1) / m with hy
    have hy1 : 1 ≤ y := (Nat.le_div_iff_mul_le hm0).mpr (by omega)
    have hyz : y ≤ z := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
    have hdm := Nat.div_add_mod (z - 1) m
    have hmod := Nat.mod_lt (z - 1) hm0
    rw [← hy] at hdm
    have hzm : z ≤ m * y + m := by
      generalize m * y = q at hdm ⊢
      generalize (z - 1) % m = r at hdm hmod
      omega
    have hzle : z ≤ 2 * R * y := by
      nlinarith [Nat.mul_le_mul_right y hmR, Nat.mul_le_mul_left R hy1]
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy1
    have hzleR : (z : ℝ) ≤ 2 * (R : ℝ) * y := by exact_mod_cast hzle
    have hlo : T ≤ K + Real.log y := by
      rw [hTdef, hK, ← Real.log_mul (by positivity) hy0.ne']
      exact Real.log_le_log hz0 hzleR
    have hhi : Real.log y ≤ T := Real.log_le_log hy0 (by exact_mod_cast hyz)
    have hAy := hA y hy1
    have hsq : (T - K) ^ 2 ≤ (Real.log y) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hAm : A * (Real.log y + 1) ≤ A * (T + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hA0
    rw [hL]; linarith
  -- sum over `m ∣ R`
  have hsum : (∑ m ∈ R.divisors, betaT m / m) * L
      ≤ ∑ m ∈ R.divisors, betaT m / m * oddDivSum ((z - 1) / m) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m hm
    have := betaT_nonneg m
    exact mul_le_mul_of_nonneg_left (hper m hm) (by positivity)
  -- the arithmetic
  set E := T * K / 4 + A * T + A with hE
  have hE0 : 0 ≤ E := by positivity
  have hηT : 16 * (K / 4 + 2 * A) ≤ η * T := by
    rw [div_le_iff₀ hη] at hTη; linarith
  have hEle : E ≤ η * T ^ 2 / 16 := by
    have h1' : T * (16 * (K / 4 + 2 * A)) ≤ T * (η * T) :=
      mul_le_mul_of_nonneg_left hηT (by linarith)
    have h2' : A ≤ A * T := by nlinarith
    rw [hE]; nlinarith
  have hLeq : L = T ^ 2 / 8 + K ^ 2 / 8 - E := by rw [hL, hE]; ring
  have hL0 : 0 ≤ L := by
    rw [hLeq]; nlinarith [sq_nonneg K, sq_nonneg T]
  have hkey : (1 - η) * T ^ 2 / 8 ≤ (1 - η / 2) * L := by
    rw [hLeq]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ η / 2) hE0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - η / 2) (sq_nonneg K)]
  have hstep : (1 - η) * T ^ 2 / (8 * Pi2) ≤ (1 - η / 2) / Pi2 * L := by
    rw [show (1 - η) * T ^ 2 / (8 * Pi2) = ((1 - η) * T ^ 2 / 8) / Pi2 by
        field_simp,
      show (1 - η / 2) / Pi2 * L = ((1 - η / 2) * L) / Pi2 by ring]
    exact div_le_div_of_nonneg_right hkey hPi.le
  have hBL : (1 - η / 2) / Pi2 * L ≤ (∑ m ∈ R.divisors, betaT m / m) * L :=
    mul_le_mul_of_nonneg_right hRsum hL0
  linarith

end Salt.HardyLittlewood.Sel
