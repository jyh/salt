/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Entropy.Basic

/-!
# The prime window and residue datum (Chowla/Liouville spine, sprint-3 A-R2 wave I)

This file lands the modulus side of Tao arXiv:1509.05422v2 Lemma 3.1: the prime window
`𝒫_H` of primes in `(ε²H/2, ε²H]`, its product `P_H`, and the residue datum
`Y_H = n mod P_H`.  The key export for the entropy decrement is the ceiling
`H[Y_H ; μ] ≤ log P_H`, together with the size bound `log P_H ≤ ε²H · log 4`
(sharp, via the mathlib primorial bound `primorial ≤ 4^n`), a crude cardinality
bound, the empty-window corner `ε²H < 2 → P_H = 1 → H[Y_H] = 0`, and the
coprimality fact `a ≤ ε²H₋/2 → Coprime a P_H`.
-/

open MeasureTheory ProbabilityTheory

namespace Salt.Entropy.Chowla

/-- The prime window `𝒫_H`: the primes `p` with `ε²H/2 < p ≤ ε²H`. -/
def primeWindow (eps : ℚ) (H : ℕ) : Finset ℕ :=
  (Finset.Iic ⌊eps ^ 2 * (H : ℚ)⌋₊).filter
    (fun p => p.Prime ∧ eps ^ 2 * (H : ℚ) / 2 < (p : ℚ))

lemma mem_primeWindow {eps : ℚ} {H p : ℕ} :
    p ∈ primeWindow eps H ↔
      p ≤ ⌊eps ^ 2 * (H : ℚ)⌋₊ ∧ p.Prime ∧ eps ^ 2 * (H : ℚ) / 2 < (p : ℚ) := by
  simp only [primeWindow, Finset.mem_filter, Finset.mem_Iic]

lemma prime_of_mem_primeWindow {eps : ℚ} {H p : ℕ} (hp : p ∈ primeWindow eps H) :
    p.Prime := (mem_primeWindow.mp hp).2.1

/-- The prime modulus `P_H = ∏ 𝒫_H`. -/
def PH (eps : ℚ) (H : ℕ) : ℕ := ∏ p ∈ primeWindow eps H, p

lemma PH_pos (eps : ℚ) (H : ℕ) : 0 < PH eps H :=
  Finset.prod_pos (fun _ hp => (prime_of_mem_primeWindow hp).pos)

/-- `P_H ≥ 1` always: the empty product is `1` and every prime is `≥ 2`.  This
global instance makes `ZMod (PH eps H)` a `Fintype` (hence `FiniteRange` and the
log-card ceiling apply to the residue datum). -/
instance (eps : ℚ) (H : ℕ) : NeZero (PH eps H) := ⟨(PH_pos eps H).ne'⟩

/-- The residue datum `Y_H = n mod P_H`. -/
def residueWindow (eps : ℚ) (H : ℕ) (n : ℕ) : ZMod (PH eps H) := (n : ZMod (PH eps H))

/-- The residue datum is measurable (the domain `ℕ` carries the discrete
`⊤`-measurable structure). -/
lemma measurable_residueWindow (eps : ℚ) (H : ℕ) : Measurable (residueWindow eps H) :=
  measurable_of_countable _

/-- The residue datum has finite range: its codomain `ZMod (PH eps H)` is a
`Fintype` once `NeZero (PH eps H)` is registered. -/
example (eps : ℚ) (H : ℕ) : FiniteRange (residueWindow eps H) := inferInstance

/-! ## The residue entropy ceiling -/

/-- **The residue entropy ceiling.** `H[Y_H ; μ] ≤ log P_H` for any measure `μ`
on the domain (via `entropy_le_log_card` and `ZMod.card`). -/
lemma entropy_residueWindow_le_log_PH (eps : ℚ) (H : ℕ) (μ : Measure ℕ) :
    H[residueWindow eps H ; μ] ≤ Real.log (PH eps H) := by
  have h := entropy_le_log_card (residueWindow eps H) μ
  rwa [ZMod.card] at h

/-! ## Size bounds -/

lemma primeWindow_subset_primesLE (eps : ℚ) (H : ℕ) :
    primeWindow eps H ⊆ Nat.primesLE ⌊eps ^ 2 * (H : ℚ)⌋₊ := by
  intro p hp
  rw [mem_primeWindow] at hp
  rw [Nat.mem_primesLE]
  exact ⟨hp.1, hp.2.1⟩

/-- `P_H ≤ 4 ^ ⌊ε²H⌋₊`: the window is a subset of all primes `≤ ε²H`, whose
product is the primorial, bounded by `4^n` in mathlib. -/
lemma PH_le_four_pow (eps : ℚ) (H : ℕ) : PH eps H ≤ 4 ^ ⌊eps ^ 2 * (H : ℚ)⌋₊ := by
  calc PH eps H = ∏ p ∈ primeWindow eps H, p := rfl
    _ ≤ ∏ p ∈ Nat.primesLE ⌊eps ^ 2 * (H : ℚ)⌋₊, p :=
        Finset.prod_le_prod_of_subset_of_one_le' (primeWindow_subset_primesLE eps H)
          (fun _ hp _ => (Nat.one_lt_of_mem_primesLE hp).le)
    _ = primorial ⌊eps ^ 2 * (H : ℚ)⌋₊ := (primorial_eq_prod_primesLE _).symm
    _ ≤ 4 ^ ⌊eps ^ 2 * (H : ℚ)⌋₊ := primorial_le_four_pow _

/-- **The (3.10)-grade size bound.** `log P_H ≤ ε²H · log 4` (sharp constant
`c = log 4`). -/
lemma log_PH_le (eps : ℚ) (H : ℕ) :
    Real.log (PH eps H) ≤ ((eps : ℝ) ^ 2 * (H : ℝ)) * Real.log 4 := by
  have hk : (⌊eps ^ 2 * (H : ℚ)⌋₊ : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
    calc (⌊eps ^ 2 * (H : ℚ)⌋₊ : ℝ)
        = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
      _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
      _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc Real.log (PH eps H)
      ≤ Real.log ((4 : ℝ) ^ ⌊eps ^ 2 * (H : ℚ)⌋₊) := by
        apply Real.log_le_log (by exact_mod_cast PH_pos eps H)
        exact_mod_cast PH_le_four_pow eps H
    _ = (⌊eps ^ 2 * (H : ℚ)⌋₊ : ℝ) * Real.log 4 := by rw [Real.log_pow]
    _ ≤ ((eps : ℝ) ^ 2 * (H : ℝ)) * Real.log 4 := mul_le_mul_of_nonneg_right hk hlog4

/-- Crude cardinality bound: `|𝒫_H| ≤ ⌊ε²H⌋₊ + 1` (count every natural in the
window's `Iic` base).  The interval-length-grade; the sharp `log_PH_le` already
supplies the (3.10) need, so the factor-of-2 slack here is immaterial. -/
lemma primeWindow_card_le (eps : ℚ) (H : ℕ) :
    (primeWindow eps H).card ≤ ⌊eps ^ 2 * (H : ℚ)⌋₊ + 1 :=
  (Finset.card_filter_le _ _).trans_eq (Nat.card_Iic _)

/-! ## The empty-window corner -/

lemma primeWindow_eq_empty_of_lt_two {eps : ℚ} {H : ℕ} (h : eps ^ 2 * (H : ℚ) < 2) :
    primeWindow eps H = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [mem_primeWindow] at hp
  have hple : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
    le_trans (by exact_mod_cast hp.1) (Nat.floor_le (by positivity))
  have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.2.1.two_le
  linarith

/-- The empty-window corner on the modulus: `ε²H < 2 → P_H = 1`. -/
lemma PH_eq_one_of_lt_two {eps : ℚ} {H : ℕ} (h : eps ^ 2 * (H : ℚ) < 2) : PH eps H = 1 := by
  rw [PH, primeWindow_eq_empty_of_lt_two h, Finset.prod_empty]

/-- The empty-window corner on the entropy: an empty window forces `H[Y_H] = 0`
(`ZMod 1` is a singleton, so the log-card ceiling is `log 1 = 0`). -/
lemma entropy_residueWindow_eq_zero_of_empty {eps : ℚ} {H : ℕ}
    (h : primeWindow eps H = ∅) (μ : Measure ℕ) :
    H[residueWindow eps H ; μ] = 0 := by
  have hPH : PH eps H = 1 := by rw [PH, h, Finset.prod_empty]
  have hle := entropy_residueWindow_le_log_PH eps H μ
  have hlog : Real.log (PH eps H) = 0 := by rw [hPH]; simp
  rw [hlog] at hle
  exact le_antisymm hle (entropy_nonneg _ _)

/-! ## Coprimality -/

/-- **The coprimality fact** (regime `hcoprime` consumer).  If `a ≤ ε²H₋/2` and
`H₋ ≤ H`, then every prime of `𝒫_H` exceeds `a`, so `a` is coprime to `P_H`. -/
lemma coprime_PH_of_le {eps : ℚ} {a Hlo H : ℕ} (ha : 1 ≤ a)
    (hcop : (a : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2) (hH : Hlo ≤ H) :
    Nat.Coprime a (PH eps H) := by
  have ha0 : a ≠ 0 := by omega
  rw [PH, Nat.coprime_prod_right_iff]
  intro p hp
  rw [mem_primeWindow] at hp
  have hlt : (a : ℚ) < (p : ℚ) := by
    have hstep : eps ^ 2 * (Hlo : ℚ) / 2 ≤ eps ^ 2 * (H : ℚ) / 2 := by
      have hHle : (Hlo : ℚ) ≤ (H : ℚ) := by exact_mod_cast hH
      nlinarith [mul_nonneg (sq_nonneg eps) (sub_nonneg.mpr hHle)]
    calc (a : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2 := hcop
      _ ≤ eps ^ 2 * (H : ℚ) / 2 := hstep
      _ < (p : ℚ) := hp.2.2
  have hap : a < p := by exact_mod_cast hlt
  exact (Nat.coprime_of_lt_prime ha0 hap hp.2.1).symm

end Salt.Entropy.Chowla
