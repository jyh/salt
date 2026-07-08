/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Diagonal
import Salt.Maynard.DiagonalS2
import Salt.Maynard.S2DiagLam
import Salt.Maynard.S2DiagRestricted
import Salt.Maynard.Rankin
import Salt.Maynard.CollisionQuant

/-!
# Maynard Lemma 5.3 — the `y^{(m)}` contraction (Maynard 1311.4600, §5)

Maynard's `y^{(m)}` (his (5.23)) is
`y^{(m)}_r = (∏ᵢ μ(rᵢ)g(rᵢ)) · ∑_{d : rᵢ∣dᵢ, dₘ=1} λ_d / ∏ᵢ φ(dᵢ)`,
packaged here as `yM = (∏ᵢ μ(rᵢ)g(rᵢ)) · lamPhiContractM` reusing the
`m`-restricted contraction `lamPhiContractM` from `S2DiagRestricted.lean`.

Lemma 5.3 states that for `rₘ = 1`, `y^{(m)}_r` equals the single 1-dimensional
`m`-coordinate sum `∑_{aₘ} y_{r; m→aₘ} / φ(aₘ)` up to an `O(log R / D₀)` error.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- **Maynard's `y^{(m)}` (his (5.23)).** For a sieve tuple `r`,
`y^{(m)}_r = (∏ᵢ μ(rᵢ)·g(rᵢ)) · lamPhiContractM r`, where `lamPhiContractM` is
the `m`-restricted (`dₘ = 1`) `λ`-weighted `φ`-density contraction. -/
noncomputable def yM (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) (r : Fin k → ℕ) : ℝ :=
  (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) * lamPhiContractM k R W m y r

/-! ## Step 1–3 — the exact `sigmaMu` collapse of `lamPhiContractM` -/

/-- **The `m`-pinned `sigmaMu` tensor (his (5.30), per-coordinate).** For a
squarefree tuple `a` with `rᵢ ∣ aᵢ` and `rₘ = 1`, the guarded Möbius/`d/φ`
product-sum over divisor tuples of `a`, with the `m`-coordinate *pinned* to
`dₘ = 1`, factorizes to `∏_{i≠m} μ(aᵢ)·rᵢ/φ(aᵢ)`.  The `i ≠ m` coordinates are
`sigmaMu`; the `m`-coordinate collapses to the single `dₘ = 1` term
`μ(1)·1/φ(1) = 1`. -/
theorem sigmaMuKpin {k : ℕ} (m : Fin k) {a r : Fin k → ℕ}
    (ha : ∀ i, Squarefree (a i)) (hra : ∀ i, r i ∣ a i) (hrm : r m = 1) :
    (∑ d ∈ Fintype.piFinset (fun i => (a i).divisors),
        if ((∀ i, r i ∣ d i) ∧ d m = 1) then
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
      = ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i)))) := by
  -- turn the guarded product into a product of per-coordinate guards
  have hpi : ∀ d : Fin k → ℕ,
      (∏ i, (if (r i ∣ d i ∧ (i = m → d i = 1)) then
          ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0))
        = if ((∀ i, r i ∣ d i) ∧ d m = 1) then
            ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0 := by
    intro d
    split_ifs with h
    · apply Finset.prod_congr rfl; intro i _
      rw [if_pos ⟨h.1 i, fun hi => hi ▸ h.2⟩]
    · rw [not_and] at h
      by_cases hall : ∀ i, r i ∣ d i
      · have hm : d m ≠ 1 := h hall
        exact Finset.prod_eq_zero (Finset.mem_univ m) (if_neg (fun hc => hm (hc.2 rfl)))
      · obtain ⟨i, hi⟩ := not_forall.mp hall
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (fun hc => hi hc.1))
  calc (∑ d ∈ Fintype.piFinset (fun i => (a i).divisors),
        if ((∀ i, r i ∣ d i) ∧ d m = 1) then
          ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
      = ∑ d ∈ Fintype.piFinset (fun i => (a i).divisors),
          ∏ i, (if (r i ∣ d i ∧ (i = m → d i = 1)) then
            ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0) := by
        apply Finset.sum_congr rfl; intro d _; rw [hpi d]
    _ = ∏ i, ∑ dᵢ ∈ (a i).divisors,
          (if (r i ∣ dᵢ ∧ (i = m → dᵢ = 1)) then
            ((μ dᵢ : ℤ) : ℝ) * ((dᵢ : ℝ) / (Nat.totient dᵢ)) else 0) :=
        (Finset.prod_univ_sum (fun i => (a i).divisors)
          (fun i dᵢ => if (r i ∣ dᵢ ∧ (i = m → dᵢ = 1)) then
            ((μ dᵢ : ℤ) : ℝ) * ((dᵢ : ℝ) / (Nat.totient dᵢ)) else 0)).symm
    _ = ∏ i, (if i = m then (1 : ℝ)
          else ((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i)))) := by
        apply Finset.prod_congr rfl; intro i _
        by_cases him : i = m
        · subst him
          rw [if_pos rfl]
          have hcond : ∀ dᵢ, (r i ∣ dᵢ ∧ (i = i → dᵢ = 1)) ↔ (dᵢ = 1) := by
            intro dᵢ; rw [hrm]; simp
          rw [show (∑ dᵢ ∈ (a i).divisors,
                if (r i ∣ dᵢ ∧ (i = i → dᵢ = 1)) then
                  ((μ dᵢ : ℤ) : ℝ) * ((dᵢ : ℝ) / (Nat.totient dᵢ)) else 0)
              = ∑ dᵢ ∈ (a i).divisors,
                if dᵢ = 1 then ((μ dᵢ : ℤ) : ℝ) * ((dᵢ : ℝ) / (Nat.totient dᵢ)) else 0 from ?_]
          · rw [Finset.sum_ite_eq' (a i).divisors 1
              (fun dᵢ => ((μ dᵢ : ℤ) : ℝ) * ((dᵢ : ℝ) / (Nat.totient dᵢ)))]
            rw [if_pos (Nat.one_mem_divisors.mpr (ha i).ne_zero)]
            simp
          · apply Finset.sum_congr rfl; intro dᵢ _
            by_cases hd : dᵢ = 1
            · rw [if_pos ((hcond dᵢ).mpr hd), if_pos hd]
            · rw [if_neg (fun h => hd ((hcond dᵢ).mp h)), if_neg hd]
        · rw [if_neg him, ← sigmaMu (ha i) (hra i)]
          apply Finset.sum_congr rfl; intro dᵢ _
          by_cases hd : r i ∣ dᵢ
          · rw [if_pos ⟨hd, fun hc => absurd hc him⟩, if_pos hd]
          · rw [if_neg (fun h => hd h.1), if_neg hd]
    _ = ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i)))) := by
        rw [← Finset.prod_erase Finset.univ
          (f := fun i => if i = m then (1 : ℝ)
            else ((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i))))
          (show (if m = m then (1 : ℝ)
            else ((μ (a m) : ℤ) : ℝ) * ((r m : ℝ) / (Nat.totient (a m)))) = 1 from by
            rw [if_pos rfl])]
        apply Finset.prod_congr rfl; intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi)]

/-- **Steps 1–3 (his (5.28)–(5.30)) — the exact `sigmaMu` collapse.** For any `r`
with `rₘ = 1`, Maynard's `lamPhiContractM` (the `dₘ=1`, `rᵢ∣dᵢ`-restricted
`λ`-weighted `φ`-density) equals the single `a`-sum with the inner `d`-sum
already contracted by `sigmaMu`:
`lamPhiContractM r = ∑_{a : rᵢ∣aᵢ} (y_a/∏φ(aᵢ))·∏_{i≠m} μ(aᵢ)·rᵢ/φ(aᵢ)`.
This is the arithmetic heart of Lemma 5.3 (no estimates, exact identity). -/
theorem lamPhiContractM_collapse (k R W : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (r : Fin k → ℕ) (hrm : r m = 1) :
    lamPhiContractM k R W m y r
      = ∑ a ∈ kSieveIndex k R W,
          (if (∀ i, r i ∣ a i) then
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i)))) else 0) := by
  -- per-`d` factorisation of `lam d / ∏ φ(dᵢ)` (identical to `wsum_lam_phi`)
  have hlam : ∀ d, lam k R W y d / (∏ i, (Nat.totient (d i) : ℝ))
      = (∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i)))) * wSum k R W y d := by
    intro d
    rw [lam, show (∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))))
          = (∏ i, ((μ (d i) : ℤ) : ℝ) * (d i : ℝ)) / (∏ i, (Nat.totient (d i) : ℝ)) from ?_]
    · ring
    · rw [← Finset.prod_div_distrib]; apply Finset.prod_congr rfl; intro i _; rw [mul_div_assoc]
  -- expand `lamPhiContractM` into a double `d,a`-sum
  have hstep : lamPhiContractM k R W m y r
      = ∑ d ∈ kSieveIndex k R W, ∑ a ∈ kSieveIndex k R W,
          (if ((∀ i, r i ∣ d i) ∧ d m = 1) then
            ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
          * (if (∀ i, d i ∣ a i) then y a / ∏ i, (Nat.totient (a i) : ℝ) else 0) := by
    rw [lamPhiContractM, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro d _
    by_cases hdm : d m = 1
    · rw [if_pos hdm]
      by_cases hrd : ∀ i, r i ∣ d i
      · rw [if_pos hrd, hlam d, wSum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        rw [if_pos (show (∀ i, r i ∣ d i) ∧ d m = 1 from ⟨hrd, hdm⟩)]
      · rw [if_neg hrd]; symm; apply Finset.sum_eq_zero; intro a _
        rw [if_neg (fun h => hrd h.1), zero_mul]
    · rw [if_neg hdm]; symm; apply Finset.sum_eq_zero; intro a _
      rw [if_neg (fun h => hdm h.2), zero_mul]
  rw [hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  by_cases hguard : ∀ i, r i ∣ a i
  · rw [if_pos hguard]
    have hsq : ∀ i, Squarefree (a i) := fun i => ((mem_kSieveIndex_iff a).mp ha).1 i
    calc (∑ d ∈ kSieveIndex k R W,
          (if ((∀ i, r i ∣ d i) ∧ d m = 1) then
            ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
          * (if (∀ i, d i ∣ a i) then y a / ∏ i, (Nat.totient (a i) : ℝ) else 0))
        = ∑ d ∈ kSieveIndex k R W,
            (if (∀ i, d i ∣ a i) then
              (if ((∀ i, r i ∣ d i) ∧ d m = 1) then
                ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
              * (y a / ∏ i, (Nat.totient (a i) : ℝ)) else 0) := by
          apply Finset.sum_congr rfl; intro d _; rw [mul_ite_zero]
      _ = ∑ d ∈ Fintype.piFinset (fun i => (a i).divisors),
            (if ((∀ i, r i ∣ d i) ∧ d m = 1) then
              ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
            * (y a / ∏ i, (Nat.totient (a i) : ℝ)) :=
          sum_ksieve_guarded_eq ha (fun d =>
            (if ((∀ i, r i ∣ d i) ∧ d m = 1) then
              ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0)
            * (y a / ∏ i, (Nat.totient (a i) : ℝ)))
      _ = (∑ d ∈ Fintype.piFinset (fun i => (a i).divisors),
            (if ((∀ i, r i ∣ d i) ∧ d m = 1) then
              ∏ i, ((μ (d i) : ℤ) : ℝ) * ((d i : ℝ) / (Nat.totient (d i))) else 0))
            * (y a / ∏ i, (Nat.totient (a i) : ℝ)) := by rw [Finset.sum_mul]
      _ = (∏ i ∈ Finset.univ.erase m,
            (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i)))))
            * (y a / ∏ i, (Nat.totient (a i) : ℝ)) := by
          rw [sigmaMuKpin m hsq hguard hrm]
      _ = (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i)))) := by ring
  · rw [if_neg hguard]
    apply Finset.sum_eq_zero; intro d _
    by_cases hc1 : (∀ i, r i ∣ d i) ∧ d m = 1
    · by_cases hc2 : ∀ i, d i ∣ a i
      · exact absurd (fun i => (hc1.1 i).trans (hc2 i)) hguard
      · rw [if_neg hc2, mul_zero]
    · rw [if_neg hc1, zero_mul]

end Salt.Maynard
