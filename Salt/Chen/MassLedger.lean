/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Tail

/-!
# MR1 — the A₂ mass-ledger reduction (first brick of the C1cσ numeric keystone)

On the A₂ grid `s ∈ [4/3, 3]` the odd Rosser-chain sum collapses to a scalar
ledger.  The key fact (the "mass ledger"): for an **odd** level `m = n+1 ≥ 3`
(so `n ≥ 2` even) on `s ∈ [1,3]`, the flat/tail window (BJS (16)/(17)) gives

  `fseq (n+1) s = (1/s)·∫_3^{n+3} fseq n (t−1) dt = (1/s)·∫_2^{n+2} fseq n u du`

(change of variables `u = t−1`), and `∫_2^{n+2} fseq n u` is the **full support
mass** of the even level `n` (since `fseq n` vanishes below `2` and above `n+1`).
Writing `massE n := ∫_2^{n+2} fseq n u` for that scalar, the odd sum of `Fchain`
becomes `(3 − s)/s` (from the `f₁` term) plus `(Σ massE)/s`.  On `[4/3,3]` the
whole expression `1 + (3 − s + M)/s` is decreasing in `s`, so its sup is at
`s = 4/3`, value `9/4 + (3/4)M`; hence `M ≤ 43/75 ⟹ Fchain ≤ 268/100`.

## The `Fchain` odd-level ↔ even-mass index correspondence (item 4)

`Fchain N s = 1 + Σ_{m ∈ (range (N+1)).filter Odd} fseq m s`.  The `m = 1` term
is `f₁(s) = (3 − s)/s`.  Each remaining odd `m` (i.e. `3 ≤ m ≤ N`) equals
`massE (m−1)/s` by `fseq_odd_eq_massE`.  Reindexing `m ↦ m−1` sends the odd set
`{3 ≤ m ≤ N}` bijectively onto the **even predecessors**
`K := (range N).filter (fun k => Even k ∧ 2 ≤ k) = {even k : 2 ≤ k ≤ N−1}`.
So `Fchain N s = 1 + (3 − s)/s + (Σ_{k ∈ K} massE k)/s` (needs `1 ≤ N` so the
`f₁` term is present).

## Crude mass-tail interface (item 6)

`massE n ≤ (5/3)·(99/100)^{n−1}` from the landed per-level bound
`fseq_le : fseq (k+1) s ≤ 2e²·(99/100)^k·hbar s` and the elementary majorant
integral `∫_2^{n+2} hbar ≤ (5/6)·e⁻²` (`intbound_hi`); the constant collapses as
`2·(5/6)·(e²·e⁻²) = 5/3`.  This is the crude tail the sharp cascade replaces.
-/

namespace Salt.Chen

open MeasureTheory intervalIntegral Set

/-! ### The even-level mass scalar -/

/-- The full support mass of the even level `n`: `∫_2^{n+2} fseq n u`.  The upper
limit `n+2` matches the window equation, and `fseq n` vanishes on `[n+1, n+2]`
(`fseq_eq_zero_of_ge`), so this is the entire mass of `fseq n`. -/
noncomputable def massE (n : ℕ) : ℝ := ∫ u in (2 : ℝ)..((n : ℝ) + 2), fseq n u

/-- `massE n ≥ 0` (integral of the nonnegative `fseq n` over a correctly-oriented
interval). -/
theorem massE_nonneg (n : ℕ) : 0 ≤ massE n := by
  unfold massE
  apply intervalIntegral.integral_nonneg
  · have := Nat.cast_nonneg (α := ℝ) n; linarith
  · intro u _; exact fseq_nonneg n u

/-! ### The odd-level → even-mass identity -/

/-- **The mass-ledger identity.**  For `n ≥ 2` even and `s ∈ [1,3]`, the odd level
`n+1` equals the even mass scaled by `1/s`: `fseq (n+1) s = massE n / s`.  Uses
the flat window (`s < 3`), the tail window (at `s = 3`), and the change of
variables `u = t − 1`. -/
theorem fseq_odd_eq_massE {n : ℕ} (hn0 : n ≠ 0) (hne : Even n) {s : ℝ}
    (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : fseq (n + 1) s = massE n / s := by
  have hodd : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not_intro hne
  -- both branches (flat for `s < 3`, tail at `s = 3`) give the SAME fixed integral
  have hcommon : fseq (n + 1) s = (1 / s) * ∫ t in (3 : ℝ)..((n : ℝ) + 3), fseq n (t - 1) := by
    rcases hs3.lt_or_eq with hlt | heq
    · exact fseq_odd_flat_window hn0 hodd hs1 hlt
    · subst heq; exact fseq_odd_tail_window hn0 hodd (le_refl (3 : ℝ))
  -- change of variables u = t − 1
  have e1 : (3 : ℝ) - 1 = 2 := by norm_num
  have e2 : (n : ℝ) + 3 - 1 = (n : ℝ) + 2 := by ring
  have hcv : (∫ t in (3 : ℝ)..((n : ℝ) + 3), fseq n (t - 1))
      = ∫ u in (2 : ℝ)..((n : ℝ) + 2), fseq n u := by
    rw [integral_comp_sub_right (fun u => fseq n u) 1, e1, e2]
  rw [hcommon, hcv]
  unfold massE
  ring

/-! ### The Fchain mass ledger and the A₂ closure -/

/-- **The mass-ledger form of `Fchain`.**  On `s ∈ [1,3]` (and `1 ≤ N`, so the
`f₁` term is present), `Fchain N s = 1 + (3 − s)/s + (Σ_{k ∈ K} massE k)/s`, where
`K = (range N).filter (fun k => Even k ∧ 2 ≤ k)` is the set of even predecessors
of the odd levels `3 ≤ m ≤ N` (correspondence `m ↦ m − 1`; see the module
docstring). -/
theorem Fchain_mass_ledger (N : ℕ) (hN : 1 ≤ N) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    Fchain N s = 1 + (3 - s) / s
      + (∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k) / s := by
  have h1mem : 1 ∈ (Finset.range (N + 1)).filter (fun n => Odd n) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), odd_one⟩
  -- peel the `f₁` term off the odd sum
  have hpeel : (∑ n ∈ (Finset.range (N + 1)).filter (fun n => Odd n), fseq n s)
      = fseq 1 s + ∑ m ∈ ((Finset.range (N + 1)).filter (fun n => Odd n)).erase 1, fseq m s :=
    (Finset.add_sum_erase _ (fun m => fseq m s) h1mem).symm
  -- each remaining odd level `m ≥ 3` is `massE (m−1)/s`
  have hcongr : (∑ m ∈ ((Finset.range (N + 1)).filter (fun n => Odd n)).erase 1, fseq m s)
      = ∑ m ∈ ((Finset.range (N + 1)).filter (fun n => Odd n)).erase 1, massE (m - 1) / s := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hm1, hmN, hmodd⟩ := hm
    have hm3 : 3 ≤ m := by rw [Nat.odd_iff] at hmodd; omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst hk
    have hkeven : Even k := by rw [Nat.even_iff]; rw [Nat.odd_iff] at hmodd; omega
    have hk0 : k ≠ 0 := by omega
    rw [Nat.add_sub_cancel]
    exact fseq_odd_eq_massE hk0 hkeven hs1 hs3
  -- reindex `m ↦ m − 1` onto the even predecessors `K`
  have hreindex : (∑ m ∈ ((Finset.range (N + 1)).filter (fun n => Odd n)).erase 1, massE (m - 1))
      = ∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k := by
    apply Finset.sum_nbij' (fun m => m - 1) (fun k => k + 1)
    · intro m hm
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Nat.odd_iff,
        Nat.even_iff] at hm ⊢
      omega
    · intro k hk
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Nat.odd_iff,
        Nat.even_iff] at hk ⊢
      omega
    · intro m hm
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at hm ⊢
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hk ⊢
      omega
    · intro m _; rfl
  unfold Fchain
  rw [hpeel, hcongr, ← Finset.sum_div, hreindex, fseq_one_window hs1 hs3]
  ring

/-- **The A₂ mass-ledger closure.**  If the total even mass over `K` is `≤ 43/75`,
then `Fchain N s ≤ 268/100` on the whole A₂ grid `[4/3, 3]`.  The sup of
`1 + (3 − s + M)/s` is at `s = 4/3` (value `9/4 + (3/4)M`); with `M ≤ 43/75` this
is exactly `268/100`. -/
theorem Fchain_le_A2_of_massSum (N : ℕ) (hN : 1 ≤ N)
    (hM : (∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k) ≤ 43 / 75) :
    ∀ s ∈ Set.Icc (4 / 3 : ℝ) 3, Fchain N s ≤ 268 / 100 := by
  intro s hs
  obtain ⟨hs43, hs3⟩ := hs
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  rw [Fchain_mass_ledger N hN hs1 hs3]
  set M := ∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k with hMdef
  have hM0 : (0 : ℝ) ≤ M := Finset.sum_nonneg (fun k _ => massE_nonneg k)
  have hcombine : 1 + (3 - s) / s + M / s = (s + (3 - s + M)) / s := by
    field_simp
    ring
  rw [hcombine, div_le_iff₀ hs0]
  linarith [hs43, hM]

/-! ### The crude mass-tail interface -/

/-- **Crude mass tail.**  `massE n ≤ (5/3)·(99/100)^{n−1}` for `n ≥ 1`, from the
landed per-level bound `fseq_le` and the majorant integral `∫_2^{n+2} hbar ≤
(5/6)·e⁻²`.  The constant collapses: `2·(5/6)·(e²·e⁻²) = 5/3`.  This is the crude
tail interface the sharp per-level cascade will replace. -/
theorem massE_le_crude (n : ℕ) (hn : 1 ≤ n) : massE n ≤ (5 / 3) * (99 / 100) ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold massE
  set U : ℝ := ((k + 1 : ℕ) : ℝ) + 2 with hU
  have hab : (2 : ℝ) ≤ U := by rw [hU]; push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hconst_nonneg : (0 : ℝ) ≤ 2 * Real.exp 2 * (99 / 100) ^ k := by positivity
  have hmono : (∫ u in (2 : ℝ)..U, fseq (k + 1) u)
      ≤ ∫ u in (2 : ℝ)..U, 2 * Real.exp 2 * (99 / 100) ^ k * hbar u :=
    intervalIntegral.integral_mono_on hab (fseq_intervalIntegrable (k + 1) _ _)
      ((continuous_const.mul hbar_continuous).intervalIntegrable _ _)
      (fun u _ => fseq_le k u)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hib : (∫ u in (2 : ℝ)..U, hbar u) ≤ (5 / 6) * Real.exp (-2) := by
    have := intbound_hi 2 U (le_refl (2 : ℝ))
    rwa [hbar_lo (le_refl (2 : ℝ))] at this
  have hprod : 2 * Real.exp 2 * (99 / 100 : ℝ) ^ k * ((5 / 6) * Real.exp (-2))
      = (5 / 3) * (99 / 100) ^ k := by
    have he : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
    have hrw : 2 * Real.exp 2 * (99 / 100 : ℝ) ^ k * ((5 / 6) * Real.exp (-2))
        = (5 / 3) * (99 / 100) ^ k * (Real.exp 2 * Real.exp (-2)) := by ring
    rw [hrw, he, mul_one]
  calc (∫ u in (2 : ℝ)..U, fseq (k + 1) u)
      ≤ 2 * Real.exp 2 * (99 / 100) ^ k * ∫ u in (2 : ℝ)..U, hbar u := hmono
    _ ≤ 2 * Real.exp 2 * (99 / 100) ^ k * ((5 / 6) * Real.exp (-2)) :=
        mul_le_mul_of_nonneg_left hib hconst_nonneg
    _ = (5 / 3) * (99 / 100) ^ k := hprod

end Salt.Chen
