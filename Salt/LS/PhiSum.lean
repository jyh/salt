/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom
import Salt.LS.Conductor

/-!
# L8.1b — the standalone `∑ 1/φ` bound (`Salt/LS/PhiSum.lean`)

The residual analytic factor for the BDH conductor descent (L8.1): the classical
harmonic-type estimate

`∑_{m ∈ Icc 1 Q} 1/φ(m) ≤ 4·(1 + log Q)`.

Route (mapped from L8.1's PB-floor flag).

1. **General-`m` μ²/φ identity, one-sided.** For `m ≥ 1`,
   `(m:ℝ)/φ(m) ≤ ∑_{d ∣ m} μ²(d)/φ(d)` (`inv_totient_le_sum`, with `μ²(d)`
   realised as `if Squarefree d then 1 else 0`). Proved via the radical route:
   `m/φ(m) = rad(m)/φ(rad m)` (the ratio depends only on the prime factors,
   `Nat.totient_eq_mul_prod_factors`), then the squarefree identity
   `Salt.Maynard.sum_divisors_inv_totient_ge` at the squarefree `rad m`, whose
   divisors are exactly the squarefree divisors of `m`.

2. **The divisor swap.** `∑_{m ≤ Q} 1/φ(m) ≤ ∑_{m ≤ Q} (1/m)·∑_{d ∣ m} μ²(d)/φ(d)`
   is reindexed to `∑_{d ≤ Q} (μ²(d)/φ(d))·∑_{m ≤ Q, d ∣ m} 1/m` via
   `Finset.sum_comm` (extend the inner divisor sum to `Icc 1 Q` by an indicator).

3. **Close.** `∑_{m ≤ Q, d ∣ m} 1/m ≤ (1 + log Q)/d` (reindex `m = d·e`,
   `harmonic_le_one_add_log`) and `∑_{d ≤ Q} μ²(d)/(d·φ(d)) ≤ 4` (reuse
   `Salt.Maynard.sum_inv_mul_totient_le`).

The composed corollary `sum_inv_totient_dvd_le'` feeds L8.4 directly, discharging
the `hphi` hypothesis of `Salt.LS.sum_inv_totient_dvd_le`.
-/

open Salt.Maynard (sum_divisors_inv_totient_ge sum_inv_mul_totient_le sqfCop)
open Salt.M3Expansion (rad rad_squarefree rad_eq_primeFactors)

namespace Salt.LS

/-- Euler's product formula for the totient, cast to `ℝ`:
`φ(n) = n · ∏_{p ∣ n} (1 - 1/p)`. -/
private lemma totient_cast_eq (n : ℕ) :
    (Nat.totient n : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
  have h : ((Nat.totient n : ℚ) : ℝ)
      = (((n : ℚ) * ∏ p ∈ n.primeFactors, (1 - ((p : ℚ))⁻¹) : ℚ) : ℝ) := by
    rw [Nat.totient_eq_mul_prod_factors n]
  push_cast at h
  exact h

/-- **The general-`m` one-sided μ²/φ identity.** For `m ≥ 1`,
`1/φ(m) ≤ ∑_{d ∣ m} μ²(d)/(m·φ(d))` with `μ²(d) = if Squarefree d then 1 else 0`.
Route via the radical `rad m` (squarefree, same prime factors as `m`). -/
lemma inv_totient_le_sum (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / (Nat.totient m : ℝ)
      ≤ ∑ d ∈ m.divisors,
          (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  have hrad0 : rad m ≠ 0 := (rad_squarefree m).ne_zero
  have hraddvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  -- the totient ratio depends only on the prime factors, hence equals that of `rad m`
  have hpf : (rad m).primeFactors = m.primeFactors := (rad_eq_primeFactors rfl).symm
  have hφm := totient_cast_eq m
  have hφr := totient_cast_eq (rad m)
  rw [hpf] at hφr
  have hφm_pos : (0 : ℝ) < (Nat.totient m : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφr_pos : (0 : ℝ) < (Nat.totient (rad m) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hrad0)
  have hratio : (m : ℝ) / (Nat.totient m : ℝ) = (rad m : ℝ) / (Nat.totient (rad m) : ℝ) := by
    rw [div_eq_div_iff hφm_pos.ne' hφr_pos.ne', hφm, hφr]; ring
  -- squarefree identity at `rad m`
  have hge : (rad m : ℝ) / (Nat.totient (rad m) : ℝ)
      ≤ ∑ d ∈ (rad m).divisors, (1 : ℝ) / (Nat.totient d : ℝ) :=
    sum_divisors_inv_totient_ge (rad_squarefree m)
  -- `rad m`'s divisors are exactly the squarefree divisors of `m`
  have hconv : ∑ d ∈ (rad m).divisors, (1 : ℝ) / (Nat.totient d : ℝ)
      ≤ ∑ d ∈ m.divisors, (if Squarefree d then (1 : ℝ) else 0) / (Nat.totient d : ℝ) := by
    have hL : ∑ d ∈ (rad m).divisors, (1 : ℝ) / (Nat.totient d : ℝ)
        = ∑ d ∈ (rad m).divisors,
            (if Squarefree d then (1 : ℝ) else 0) / (Nat.totient d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have : Squarefree d := (rad_squarefree m).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      rw [if_pos this]
    rw [hL]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hm0 hraddvd)
    intro d _ _
    split_ifs <;> positivity
  -- combine the ratio, the squarefree identity and the divisor conversion
  have hstep : (m : ℝ) / (Nat.totient m : ℝ)
      ≤ ∑ d ∈ m.divisors, (if Squarefree d then (1 : ℝ) else 0) / (Nat.totient d : ℝ) := by
    rw [hratio]; exact hge.trans hconv
  -- divide the pointwise bound by `m`
  have hmR0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have key := mul_le_mul_of_nonneg_left hstep (show (0 : ℝ) ≤ 1 / (m : ℝ) by positivity)
  rw [show (1 / (m : ℝ)) * ((m : ℝ) / (Nat.totient m : ℝ)) = 1 / (Nat.totient m : ℝ) by
      field_simp] at key
  rw [Finset.mul_sum] at key
  refine key.trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_)))
  rw [div_mul_div_comm, one_mul]

/-- For `1 ≤ d ≤ Q`: `∑_{m ∈ Icc 1 Q, d ∣ m} 1/m ≤ (1 + log Q)/d`
(reindex `m = d·e`, `harmonic_le_one_add_log`). -/
lemma sum_inv_dvd_multiples_le (d Q : ℕ) (hd : 1 ≤ d) (hdQ : d ≤ Q) :
    ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => d ∣ m), (1 : ℝ) / m
      ≤ (1 + Real.log Q) / d := by
  have hd0 : 0 < d := hd
  have hset : (Finset.Icc 1 Q).filter (fun m => d ∣ m)
      = (Finset.Icc 1 (Q / d)).image (fun e => d * e) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hm1, hmQ⟩, e, rfl⟩
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with rfl | h
        · simp at hm1
        · exact h
      exact ⟨e, ⟨he1, by rw [Nat.le_div_iff_mul_le hd0, Nat.mul_comm]; exact hmQ⟩, rfl⟩
    · rintro ⟨e, ⟨he1, heQ⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le hd0] at heQ
      exact ⟨⟨Nat.mul_pos hd0 he1, by rw [Nat.mul_comm]; exact heQ⟩, e, rfl⟩
  rw [hset, Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hd0 hab)]
  simp only [Nat.cast_mul]
  have hfac : ∑ e ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / ((d : ℝ) * (e : ℝ))
      = (1 / (d : ℝ)) * ∑ e ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [one_div_mul_one_div]
  rw [hfac]
  have hEq : ((harmonic (Q / d) : ℚ) : ℝ)
      = ∑ e ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / e := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro e _
    rw [one_div]
  have hharm : ∑ e ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / e ≤ 1 + Real.log Q := by
    rw [← hEq]
    have hlog : Real.log ((Q / d : ℕ) : ℝ) ≤ Real.log Q := by
      apply Real.log_le_log
      · have h1 : 1 ≤ Q / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
      · exact_mod_cast Nat.div_le_self Q d
    calc ((harmonic (Q / d) : ℚ) : ℝ)
        ≤ 1 + Real.log ((Q / d : ℕ) : ℝ) := harmonic_le_one_add_log (Q / d)
      _ ≤ 1 + Real.log Q := by linarith
  calc (1 / (d : ℝ)) * ∑ e ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / e
      ≤ (1 / (d : ℝ)) * (1 + Real.log Q) :=
        mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = (1 + Real.log Q) / d := by rw [mul_comm, mul_one_div]

/-- **L8.1b — the standalone `∑ 1/φ` bound.** `∑_{m ∈ Icc 1 Q} 1/φ(m) ≤ 4·(1 + log Q)`. -/
theorem sum_inv_totient_le (Q : ℕ) (hQ : 1 ≤ Q) :
    ∑ m ∈ Finset.Icc 1 Q, (1 / (Nat.totient m : ℝ)) ≤ 4 * (1 + Real.log Q) := by
  -- Step 1: pointwise μ²/φ bound, summed over `m`
  have h1 : ∑ m ∈ Finset.Icc 1 Q, (1 / (Nat.totient m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 Q, ∑ d ∈ m.divisors,
          (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ)) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact inv_totient_le_sum m hm.1
  -- Step 2: the divisor swap
  have hstep1 : ∀ m ∈ Finset.Icc 1 Q,
      ∑ d ∈ m.divisors,
          (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ))
        = ∑ d ∈ Finset.Icc 1 Q,
            (if d ∈ m.divisors then
              (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ)) else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hd
      exact ⟨⟨Nat.pos_of_mem_divisors hd, (Nat.divisor_le hd).trans hm.2⟩, hd⟩
    · rintro ⟨_, hd⟩; exact hd
  have h2 : ∑ m ∈ Finset.Icc 1 Q, ∑ d ∈ m.divisors,
              (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ))
      = ∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => d ∣ m),
              (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ)) := by
    rw [Finset.sum_congr rfl hstep1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hiff : (d ∈ m.divisors) ↔ (d ∣ m) := by
      rw [Nat.mem_divisors]; exact and_iff_left (by omega : m ≠ 0)
    simp only [hiff]
  -- Step 3: bound each `d`-slice by `(1 + log Q)·μ²(d)/(d·φ(d))`
  have h3 : ∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => d ∣ m),
              (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ))
      ≤ (1 + Real.log Q) * ∑ d ∈ Finset.Icc 1 Q,
              (if Squarefree d then (1 : ℝ) else 0) / ((d : ℝ) * (Nat.totient d : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Icc] at hd
    obtain ⟨hd1, hdQ⟩ := hd
    have hd0R : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    by_cases hsf : Squarefree d
    · simp only [if_pos hsf]
      have hφpos : (0 : ℝ) < (Nat.totient d : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hφne : (Nat.totient d : ℝ) ≠ 0 := hφpos.ne'
      have hfac : ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => d ∣ m),
              (1 : ℝ) / ((m : ℝ) * (Nat.totient d : ℝ))
          = (1 / (Nat.totient d : ℝ))
              * ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => d ∣ m), (1 : ℝ) / m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [one_div_mul_one_div, mul_comm (Nat.totient d : ℝ) (m : ℝ)]
      rw [hfac]
      have hmul := sum_inv_dvd_multiples_le d Q hd1 hdQ
      have hrhs : (1 + Real.log Q) * (1 / ((d : ℝ) * (Nat.totient d : ℝ)))
          = (1 / (Nat.totient d : ℝ)) * ((1 + Real.log Q) / d) := by
        field_simp
      rw [hrhs]
      exact mul_le_mul_of_nonneg_left hmul (by positivity)
    · simp [if_neg hsf]
  -- Step 4: the squarefree `μ²/(d·φ(d))` sum is `≤ 4` (reuse the Maynard atom)
  have h4 : ∑ d ∈ Finset.Icc 1 Q,
        (if Squarefree d then (1 : ℝ) else 0) / ((d : ℝ) * (Nat.totient d : ℝ)) ≤ 4 := by
    have hset : (Finset.Icc 1 Q).filter Squarefree = sqfCop (Q + 1) 1 := by
      ext d
      simp only [sqfCop, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · rintro ⟨⟨hd1, hdQ⟩, hsf⟩
        exact ⟨by omega, hsf, Nat.coprime_one_right d⟩
      · rintro ⟨hdQ, hsf, _⟩
        refine ⟨⟨?_, by omega⟩, hsf⟩
        rcases Nat.eq_zero_or_pos d with rfl | h
        · exact absurd hsf not_squarefree_zero
        · exact h
    have step1 : ∑ d ∈ Finset.Icc 1 Q,
          (if Squarefree d then (1 : ℝ) else 0) / ((d : ℝ) * (Nat.totient d : ℝ))
        = ∑ d ∈ Finset.Icc 1 Q,
            if Squarefree d then (1 : ℝ) / ((d : ℝ) * (Nat.totient d : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    rw [step1, ← Finset.sum_filter, hset]
    exact sum_inv_mul_totient_le (Q + 1) 1
  -- assemble
  have hlogQ : (0 : ℝ) ≤ 1 + Real.log Q := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Q by exact_mod_cast hQ)
    linarith
  calc ∑ m ∈ Finset.Icc 1 Q, (1 / (Nat.totient m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 Q, ∑ d ∈ m.divisors,
          (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ)) := h1
    _ = ∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ (Finset.Icc 1 Q).filter (fun m => d ∣ m),
          (if Squarefree d then (1 : ℝ) else 0) / ((m : ℝ) * (Nat.totient d : ℝ)) := h2
    _ ≤ (1 + Real.log Q) * ∑ d ∈ Finset.Icc 1 Q,
          (if Squarefree d then (1 : ℝ) else 0) / ((d : ℝ) * (Nat.totient d : ℝ)) := h3
    _ ≤ (1 + Real.log Q) * 4 := mul_le_mul_of_nonneg_left h4 hlogQ
    _ = 4 * (1 + Real.log Q) := by ring

/-- **The composed corollary consumed by L8.4 (BDH).** Discharging the `hphi`
hypothesis of `Salt.LS.sum_inv_totient_dvd_le` with `sum_inv_totient_le`. -/
theorem sum_inv_totient_dvd_le' {f Q : ℕ} (hf : 1 ≤ f) (hQ : 1 ≤ Q) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (f ∣ ·), (1 / (Nat.totient q : ℝ))
      ≤ (4 / (Nat.totient f : ℝ)) * (1 + Real.log Q) :=
  sum_inv_totient_dvd_le hf (sum_inv_totient_le Q hQ)

end Salt.LS
