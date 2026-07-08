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

/-! ## D1–D2 — the genuine analytic tail atoms (Steps B–C)

Every bound below is discharged with named in-repo machinery
(`inv_sq_tele` copy / `euler_tail`), NOT hypothesised. -/

/-- Telescoping tail bound (local copy of the `private`
`CollisionQuant.inv_sq_tele`): `∑_{a<n≤b}(n−1)⁻² ≤ (a−1)⁻¹ − (b−1)⁻¹`
for `2 ≤ a ≤ b`. -/
private theorem inv_sq_tele53 (a : ℕ) (ha : 2 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      (∑ n ∈ Finset.Icc (a + 1) b, (((n : ℝ) - 1)⁻¹) ^ 2)
        ≤ ((a : ℝ) - 1)⁻¹ - ((b : ℝ) - 1)⁻¹ := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_trans ha hab
      have hstep : (((b + 1 : ℕ) : ℝ) - 1)⁻¹ ^ 2
          ≤ ((b : ℝ) - 1)⁻¹ - (((b + 1 : ℕ) : ℝ) - 1)⁻¹ := by
        push_cast
        have h1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
        rw [show ((b : ℝ) + 1 - 1) = (b : ℝ) by ring, ← sub_nonneg]
        have hexp : ((b : ℝ) - 1)⁻¹ - (b : ℝ)⁻¹ - ((b : ℝ)⁻¹) ^ 2
            = (((b : ℝ)) ^ 2 * ((b : ℝ) - 1))⁻¹ := by
          field_simp
          ring
        rw [hexp]
        have hposm : (0 : ℝ) < ((b : ℝ)) ^ 2 * ((b : ℝ) - 1) := by nlinarith
        exact inv_nonneg.mpr hposm.le
      linarith [ih]

/-- Weierstrass lower bound: `1 − ∑ xₚ ≤ ∏(1 − xₚ)` for `0 ≤ xₚ ≤ 1`. -/
private theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ p ∈ s, 0 ≤ x p) (hx1 : ∀ p ∈ s, x p ≤ 1) :
    1 - ∑ p ∈ s, x p ≤ ∏ p ∈ s, (1 - x p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
      have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
      have hx0' : ∀ p ∈ s, 0 ≤ x p := fun p hp => hx0 p (Finset.mem_insert_of_mem hp)
      have hx1' : ∀ p ∈ s, x p ≤ 1 := fun p hp => hx1 p (Finset.mem_insert_of_mem hp)
      have hih := ih hx0' hx1'
      have hpn : 0 ≤ ∏ p ∈ s, (1 - x p) :=
        Finset.prod_nonneg fun p hp => by linarith [hx1' p hp]
      have hsn : 0 ≤ ∑ p ∈ s, x p := Finset.sum_nonneg hx0'
      nlinarith [hih, hxa0, hxa1, hpn, hsn,
        mul_le_mul_of_nonneg_left hih (by linarith : (0 : ℝ) ≤ 1 - x a)]

/-- `|∏(1 − xₚ) − 1| ≤ ∑ xₚ` for `0 ≤ xₚ ≤ 1`. -/
private theorem abs_prod_one_sub_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ p ∈ s, 0 ≤ x p) (hx1 : ∀ p ∈ s, x p ≤ 1) :
    |(∏ p ∈ s, (1 - x p)) - 1| ≤ ∑ p ∈ s, x p := by
  have hle : ∏ p ∈ s, (1 - x p) ≤ 1 :=
    Finset.prod_le_one (fun p hp => by linarith [hx1 p hp])
      (fun p hp => by linarith [hx0 p hp])
  have hge := one_sub_sum_le_prod_one_sub s x hx0 hx1
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Per-coordinate factorization: for squarefree `r` with every prime factor
`≥ 3`, `g(r)·r/φ(r)² = ∏_{p∣r}(1 − (p−1)⁻²)`. -/
private theorem g_factor_prod {r : ℕ} (hr : Squarefree r)
    (hodd : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    (gMult r : ℝ) * (r : ℝ) / (Nat.totient r : ℝ) ^ 2
      = ∏ p ∈ r.primeFactors, (1 - (((p : ℝ) - 1)⁻¹) ^ 2) := by
  have hrprod : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  rw [gMult_cast hodd, hrprod, totient_squarefree_cast hr,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **D1 — `gProd_bound` (Step C, genuine via `inv_sq_tele`).** The `i ≠ m`
product of `g(rᵢ)rᵢ/φ(rᵢ)²` differs from `1` by at most `2/D₀ k`: each factor
is `∏_{p∣rᵢ}(1 − (p−1)⁻²)`, so the whole product is `∏_{p ∈ S}(1 − (p−1)⁻²)`
over the distinct primes `S` dividing the `i ≠ m` coordinates (pairwise
coprime), all `> D₀ k`; then `|∏(1−x) − 1| ≤ ∑ x ≤ ∑_{n>D₀}(n−1)⁻²
≤ (D₀−1)⁻¹ ≤ 2/D₀`. -/
theorem gProd_bound (k R : ℕ) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k)
    (r : Fin k → ℕ) (hrsupp : r ∈ kSieveIndex k R (W k)) (m : Fin k) :
    |(∏ i ∈ Finset.univ.erase m,
        ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)) - 1|
      ≤ (2 : ℝ) / (D₀ k : ℝ) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  have hD12 : 12 ≤ D₀ k := by
    have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by omega
    exact_mod_cast this
  -- every prime dividing a coordinate is `≥ 3` (indeed `> D₀ k ≥ 12`)
  have hodd : ∀ i, ∀ p ∈ (r i).primeFactors, 3 ≤ p := by
    intro i p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ r i := Nat.dvd_of_mem_primeFactors hp
    have hD0p : D₀ k < p := D₀_lt_of_prime_dvd_coord hrsupp hpp hpd
    omega
  set S : Finset ℕ :=
    (Finset.univ.erase m).biUnion (fun i => (r i).primeFactors) with hS
  -- primeFactors of distinct (coprime) coordinates are pairwise disjoint
  have hdisj : (↑(Finset.univ.erase m) : Set (Fin k)).PairwiseDisjoint
      (fun i => (r i).primeFactors) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have hp1 : p ∣ 1 :=
      hcop i j hij ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpi)
        (Nat.dvd_of_mem_primeFactors hpj)
    exact (Nat.prime_of_mem_primeFactors hpi).one_lt.ne' (Nat.dvd_one.mp hp1)
  -- merge the product into one over `S`
  have hprodeq : (∏ i ∈ Finset.univ.erase m,
        ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
      = ∏ p ∈ S, (1 - (((p : ℝ) - 1)⁻¹) ^ 2) := by
    rw [hS, Finset.prod_biUnion hdisj]
    exact Finset.prod_congr rfl (fun i _ => g_factor_prod (hsq i) (hodd i))
  -- membership facts for primes in `S`
  have hSmem : ∀ p ∈ S, p.Prime ∧ D₀ k < p ∧ p ≤ R := by
    intro p hp
    rw [hS, Finset.mem_biUnion] at hp
    obtain ⟨i, _, hpi⟩ := hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpi
    have hpd : p ∣ r i := Nat.dvd_of_mem_primeFactors hpi
    refine ⟨hpp, D₀_lt_of_prime_dvd_coord hrsupp hpp hpd, ?_⟩
    have hle : p ≤ r i := Nat.le_of_dvd (kSieveIndex_coord_pos hrsupp i) hpd
    have hlt : r i < R := kSieveIndex_coord_lt hrsupp i
    omega
  rw [hprodeq]
  refine le_trans (abs_prod_one_sub_le S (fun p => (((p : ℝ) - 1)⁻¹) ^ 2)
    (fun p _ => by positivity) ?_) ?_
  · -- `xₚ ≤ 1`
    intro p hp
    obtain ⟨hpp, hpD, -⟩ := hSmem p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (12 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_le_of_lt (by exact_mod_cast hD12) hpD
      linarith
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := by positivity
    have : ((p : ℝ) - 1)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; linarith
    nlinarith [this, h0]
  · -- `∑_{p∈S} (p−1)⁻² ≤ 2/D₀`
    have hsub : S ⊆ Finset.Icc (D₀ k + 1) R := by
      intro p hp
      obtain ⟨-, hpD, hpR⟩ := hSmem p hp
      rw [Finset.mem_Icc]; omega
    have hmono : ∑ p ∈ S, (((p : ℝ) - 1)⁻¹) ^ 2
        ≤ ∑ n ∈ Finset.Icc (D₀ k + 1) R, (((n : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    have hfrac : ((D₀ k : ℝ) - 1)⁻¹ ≤ 2 / (D₀ k : ℝ) := by
      have h1 : (0 : ℝ) < (D₀ k : ℝ) - 1 := by
        have : (12 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD12
        linarith
      rw [inv_eq_one_div, div_le_div_iff₀ h1 hDpos]
      have : (12 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD12
      linarith
    rcases Nat.lt_or_ge R (D₀ k) with hR' | hR'
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at hmono
      linarith [hmono, (by positivity : (0 : ℝ) ≤ 2 / (D₀ k : ℝ))]
    · have htele := inv_sq_tele53 (D₀ k) (by omega) R hR'
      have hRinv : (0 : ℝ) ≤ ((R : ℝ) - 1)⁻¹ := by
        have hR2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 2 ≤ R)
        rw [inv_nonneg]; linarith
      linarith [hmono, htele, hfrac]

/-- **D2 — `phiSq_tail_bound` (the μ²/φ² tail, genuine via `euler_tail`).** The
load-bearing tail fact: over squarefree moduli `> 1` with all prime factors
`> D₀ k`, `∑ μ²(c)/φ(c)² ≤ 12k²/D₀ k`. Termwise `μ²(c)/φ(c)² =
μ²(c)·∏(p−1)⁻² ≤ (3k²)^{ω(c)}·∏(p−1)⁻²`, then `euler_tail`. -/
theorem phiSq_tail_bound (k M : ℕ) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∑ c ∈ ((Finset.range M).filter
        (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1,
      ((μ c : ℤ) : ℝ) ^ 2 / (Nat.totient c : ℝ) ^ 2
      ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := by
  refine le_trans (Finset.sum_le_sum ?_) (euler_tail k M hk hD)
  intro c hc
  rw [Finset.mem_erase, Finset.mem_filter] at hc
  obtain ⟨-, -, hcsq, -⟩ := hc
  have hcpos : 0 < c := Nat.pos_of_ne_zero hcsq.ne_zero
  have hφpos : (0 : ℝ) < (Nat.totient c : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hcpos
  have hφsq : (0 : ℝ) < (Nat.totient c : ℝ) ^ 2 := by positivity
  have hμsq : ((μ c : ℤ) : ℝ) ^ 2 ≤ 1 := by
    have h := abs_moebius_real_le_one c
    calc ((μ c : ℤ) : ℝ) ^ 2 = |((μ c : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := by gcongr
      _ = 1 := one_pow 2
  -- `1/φ(c)² = ∏_{p∣c}(p−1)⁻²`
  have hrhs_inv : (∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
      = ((Nat.totient c : ℝ) ^ 2)⁻¹ := by
    rw [Finset.prod_pow, Finset.prod_inv_distrib, ← totient_squarefree_cast hcsq, inv_pow]
  have hprodnn : (0 : ℝ) ≤ ∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
    Finset.prod_nonneg (fun p _ => by positivity)
  have honele : (1 : ℝ) ≤ (3 * (k : ℝ) ^ 2) ^ c.primeFactors.card := by
    apply one_le_pow₀
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  calc ((μ c : ℤ) : ℝ) ^ 2 / (Nat.totient c : ℝ) ^ 2
      ≤ 1 / (Nat.totient c : ℝ) ^ 2 := by gcongr
    _ = ((Nat.totient c : ℝ) ^ 2)⁻¹ := one_div _
    _ = ∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 := hrhs_inv.symm
    _ ≤ (3 * (k : ℝ) ^ 2) ^ c.primeFactors.card
          * ∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
        le_mul_of_one_le_left hprodnn honele

/-! ## D3 — `stepB_identity` (exact algebra, no estimates) -/

/-- `μ(n)² = 1` (real-valued) for squarefree `n`. -/
private theorem moebius_sq_one {n : ℕ} (hn : Squarefree n) :
    ((μ n : ℤ) : ℝ) ^ 2 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  simp

/-- **D3 — `stepB_identity`.** The "all `aᵢ = rᵢ` for `i ≠ m`" part of
`(∏ᵢ μ(rᵢ)g(rᵢ))·lamPhiContractM` collapses (exactly, no estimates) to
`G · S`, where `G = ∏_{i≠m} g(rᵢ)rᵢ/φ(rᵢ)²` and `S = ∑_{aₘ<R} y_{r;m→aₘ}/φ(aₘ)`.
The `a`-sum reindexes via the bijection `a ↔ aₘ` (`a = update r m aₘ`); the range
extension to `range R` adds only zero terms (`y = 0` off `𝒟`); per coordinate
`μ(rᵢ)g(rᵢ)·μ(rᵢ)rᵢ/φ(rᵢ) = g(rᵢ)rᵢ/φ(rᵢ)²` since `μ(rᵢ)² = 1`. -/
theorem stepB_identity (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrsupp : r ∈ kSieveIndex k R (W k)) (hrm : r m = 1) :
    (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
      * (∑ a ∈ (kSieveIndex k R (W k)).filter
            (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))
      = (∏ i ∈ Finset.univ.erase m,
          ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
        * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  set INNER : (Fin k → ℕ) → ℝ := fun a =>
    (y a / ∏ i, (Nat.totient (a i) : ℝ))
      * ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))) with hINNER
  set 𝒟f := (kSieveIndex k R (W k)).filter
      (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i) with h𝒟f
  -- auto-guards: `update r m am` always satisfies the two filter conditions
  have hauto : ∀ am : ℕ, (∀ i, r i ∣ Function.update r m am i)
      ∧ ∀ i, i ≠ m → Function.update r m am i = r i := by
    intro am
    refine ⟨fun i => ?_, fun i hi => Function.update_of_ne hi _ _⟩
    rcases eq_or_ne i m with rfl | hne
    · rw [Function.update_self, hrm]; exact one_dvd _
    · rw [Function.update_of_ne hne]
  -- membership of `update r m am` in `𝒟f` is equivalent to being in `𝒟`
  have hmemf : ∀ am : ℕ, Function.update r m am ∈ 𝒟f
      ↔ Function.update r m am ∈ kSieveIndex k R (W k) := by
    intro am
    rw [h𝒟f, Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, hauto am⟩⟩
  -- reindex: `a ↦ a m` is injective on `𝒟f`, with inverse `am ↦ update r m am`
  have hupd : ∀ a ∈ 𝒟f, a = Function.update r m (a m) := by
    intro a ha
    rw [h𝒟f, Finset.mem_filter] at ha
    funext i
    rcases eq_or_ne i m with rfl | hne
    · rw [Function.update_self]
    · rw [Function.update_of_ne hne, ha.2.2 i hne]
  have hinj : Set.InjOn (fun a : Fin k → ℕ => a m) ↑𝒟f := by
    intro a ha b hb hab
    rw [hupd a ha, hupd b hb]
    simp only at hab
    rw [hab]
  -- image ⊆ range R, and `INNER (update r m am) = 0` for `am ∈ range R \ image`
  have hsubR : 𝒟f.image (fun a => a m) ⊆ Finset.range R := by
    intro am ham
    rw [Finset.mem_image] at ham
    obtain ⟨a, ha, rfl⟩ := ham
    rw [h𝒟f, Finset.mem_filter] at ha
    rw [Finset.mem_range]
    exact kSieveIndex_coord_lt ha.1 m
  have hzero : ∀ am ∈ Finset.range R, am ∉ 𝒟f.image (fun a => a m) →
      INNER (Function.update r m am) = 0 := by
    intro am _ ham
    have hnotf : Function.update r m am ∉ 𝒟f := by
      intro hmem
      exact ham (Finset.mem_image.mpr ⟨_, hmem, Function.update_self _ _ _⟩)
    have hnot𝒟 : Function.update r m am ∉ kSieveIndex k R (W k) :=
      fun h => hnotf ((hmemf am).mpr h)
    rw [hINNER]
    simp only
    rw [hysupp _ hnot𝒟, zero_div, zero_mul]
  have hreindex : (∑ a ∈ 𝒟f, INNER a)
      = ∑ am ∈ Finset.range R, INNER (Function.update r m am) := by
    rw [← Finset.sum_subset hsubR hzero, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun a ha => by rw [← hupd a ha])
  -- per-`am` algebra
  have halg : ∀ am : ℕ,
      (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) * INNER (Function.update r m am)
        = (∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
          * (y (Function.update r m am) / (Nat.totient am : ℝ)) := by
    intro am
    rw [hINNER]
    simp only
    -- rewrite the three products in terms of the `erase m` product + `m` factor
    have hφprod : (∏ i, (Nat.totient (Function.update r m am i) : ℝ))
        = (Nat.totient am : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => (Nat.totient (Function.update r m am i) : ℝ)) (Finset.mem_univ m),
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl (fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    have hmuprod : (∏ i ∈ Finset.univ.erase m,
          (((μ (Function.update r m am i) : ℤ) : ℝ)
            * ((r i : ℝ) / (Nat.totient (Function.update r m am i) : ℝ))))
        = ∏ i ∈ Finset.univ.erase m,
            (((μ (r i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (r i) : ℝ))) :=
      Finset.prod_congr rfl (fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    have hPprod : (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
        = ∏ i ∈ Finset.univ.erase m, (((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) (Finset.mem_univ m)]
      rw [hrm]
      simp [gMult, Nat.primeFactors_one]
    -- combine the three `erase m` products termwise into `∏ g·r/φ²`, using `μ²=1`
    have hcombine : (∏ i ∈ Finset.univ.erase m, (((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)))
          * (∏ i ∈ Finset.univ.erase m,
              (((μ (r i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (r i) : ℝ))))
          / (∏ i ∈ Finset.univ.erase m, (Nat.totient (r i) : ℝ))
        = ∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hmu2 := moebius_sq_one (hsq i)
      have h1 : (((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
            * (((μ (r i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (r i) : ℝ)))
            / (Nat.totient (r i) : ℝ)
          = ((μ (r i) : ℤ) : ℝ) ^ 2
            * ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) := by ring
      rw [h1, hmu2, one_mul]
    rw [hφprod, hmuprod, hPprod, ← hcombine]
    ring
  calc (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
        * (∑ a ∈ 𝒟f, INNER a)
      = ∑ am ∈ Finset.range R,
          (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)) * INNER (Function.update r m am) := by
        rw [hreindex, Finset.mul_sum]
    _ = ∑ am ∈ Finset.range R,
          (∏ i ∈ Finset.univ.erase m,
              ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
            * (y (Function.update r m am) / (Nat.totient am : ℝ)) :=
        Finset.sum_congr rfl (fun am _ => halg am)
    _ = (∏ i ∈ Finset.univ.erase m,
          ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2))
        * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)) := by
        rw [Finset.mul_sum]

/-! ## D4a — the `m`-coordinate main sum bound (genuine via `rankin_bound`) -/

/-- **`abs_mainSum_le`.** The 1-dimensional `m`-coordinate sum
`∑_{aₘ<R} y_{r; m→aₘ}/φ(aₘ)` is `O(log R)`: with `|y| ≤ 1` and `y` supported
on `𝒟`, only squarefree `aₘ < R` contribute, and `∑_{aₘ<R sqf} 1/φ(aₘ) ≤
C₁ log R` by `rankin_bound 1`. -/
theorem abs_mainSum_le (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hR : 2 ≤ R) :
    ∃ C : ℝ, 1 ≤ C ∧
      |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
        ≤ C * Real.log R := by
  classical
  obtain ⟨C₁, hC₁1, hC₁⟩ := rankin_bound 1
  refine ⟨C₁, hC₁1, ?_⟩
  have hRankin : ∑ q ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ C₁ * Real.log R := by
    have h := hC₁ R hR; simpa using h
  have hterm : ∀ am ∈ Finset.range R,
      |y (Function.update r m am) / (Nat.totient am : ℝ)|
        ≤ if Squarefree am then 1 / (Nat.totient am : ℝ) else 0 := by
    intro am _
    by_cases hsf : Squarefree am
    · have hampos : 0 < am := Nat.pos_of_ne_zero hsf.ne_zero
      have hφpos : (0 : ℝ) < (Nat.totient am : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hampos
      rw [if_pos hsf, abs_div, abs_of_nonneg hφpos.le]
      gcongr
      exact hy1 _
    · rw [if_neg hsf]
      have hnotmem : Function.update r m am ∉ kSieveIndex k R (W k) := fun hmem =>
        hsf (by
          have := ((mem_kSieveIndex_iff _).mp hmem).1 m
          rwa [Function.update_self] at this)
      rw [hysupp _ hnotmem, zero_div, abs_zero]
  calc |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ ∑ am ∈ Finset.range R, |y (Function.update r m am) / (Nat.totient am : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ am ∈ Finset.range R, (if Squarefree am then 1 / (Nat.totient am : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ am ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient am : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ ≤ C₁ * Real.log R := hRankin

/-! ## D4 — assembly of Lemma 5.3

`lemma53` takes ONLY the numeric hypotheses `hk`, `hD` plus the standard
`|y|≤1` / support / tuple hypotheses, and ONE precisely-scoped PORT-BLOCKER
`htail`: the Maynard (5.31) multi-index tail sum bound. `htail` is a bound on a
SPECIFIC finite sub-sum (the `∃ i≠m, aᵢ≠rᵢ` tail of the contraction), NOT on the
conclusion `|yM − S|`; the two `O(logR/D₀)` pieces that attempt 1 hypothesised
(the `|G−1|` step-C bound and the main-sum size) are here DISCHARGED via
`gProd_bound` (`inv_sq_tele`) and `abs_mainSum_le` (`rankin_bound`). -/

/-- **Lemma 5.3.** For `rₘ = 1`, `y^{(m)}_r` equals the single `m`-coordinate
sum `∑_{aₘ<R} y_{r;m→aₘ}/φ(aₘ)` up to an `O(log R / D₀)` error. Everything is
discharged from `stepB_identity` (exact algebra) + `gProd_bound` (Step C,
`inv_sq_tele`) + `abs_mainSum_le` (`rankin_bound`), leaving only the tail as the
`htail` port-blocker. -/
theorem lemma53 (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R (W k))
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k)
    (htail : ∃ Ctail : ℝ, 0 ≤ Ctail ∧
      |(∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
          * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
                ((kSieveIndex k R (W k)).filter
                  (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
              (y a / ∏ i, (Nat.totient (a i) : ℝ))
                * ∏ i ∈ Finset.univ.erase m,
                    (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))|
        ≤ Ctail * Real.log R / (D₀ k : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      |yM k R (W k) m y r
          - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
        ≤ C * Real.log R / (D₀ k : ℝ) := by
  classical
  obtain ⟨C₁, hC₁1, hSb⟩ := abs_mainSum_le k R m y hy1 hysupp r hR
  obtain ⟨Ctail, hCtail0, hTb⟩ := htail
  have hsub : (kSieveIndex k R (W k)).filter
        (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)
      ⊆ (kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1⟩
  -- split the collapse into MAIN (`aᵢ=rᵢ, i≠m`) + TAIL
  have hlpc : lamPhiContractM k R (W k) m y r
      = (∑ a ∈ (kSieveIndex k R (W k)).filter
            (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))
        + (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
              ((kSieveIndex k R (W k)).filter
                (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [lamPhiContractM_collapse k R (W k) m y r hrm, ← Finset.sum_filter, add_comm]
    exact (Finset.sum_sdiff hsub).symm
  -- yM − S = (G−1)·S + P·TAIL
  have hdiff : yM k R (W k) m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)
      = ((∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)) - 1)
          * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ))
        + (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
          * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
                ((kSieveIndex k R (W k)).filter
                  (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
              (y a / ∏ i, (Nat.totient (a i) : ℝ))
                * ∏ i ∈ Finset.univ.erase m,
                    (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [show yM k R (W k) m y r
          = (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
            * lamPhiContractM k R (W k) m y r from rfl,
      hlpc, mul_add, stepB_identity k R m y hysupp r hrsupp hrm]
    ring
  refine ⟨2 * C₁ + Ctail, by linarith [hC₁1, hCtail0], ?_⟩
  rw [hdiff]
  set G := ∏ i ∈ Finset.univ.erase m,
    ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) with hGdef
  set S := ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ) with hSdef
  set PT := (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
      * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
            ((kSieveIndex k R (W k)).filter
              (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) with hPTdef
  -- `|G−1| ≤ 2/D₀` via `gProd_bound` (inv_sq_tele); `|S| ≤ C₁ logR` via rankin
  have hG : |G - 1| ≤ 2 / (D₀ k : ℝ) := gProd_bound k R hk hD r hrsupp m
  have e2 : |G - 1| * |S| ≤ (2 / (D₀ k : ℝ)) * (C₁ * Real.log R) :=
    mul_le_mul hG hSb (abs_nonneg _) (by positivity)
  calc |(G - 1) * S + PT|
      ≤ |(G - 1) * S| + |PT| := abs_add_le _ _
    _ = |G - 1| * |S| + |PT| := by rw [abs_mul]
    _ ≤ (2 / (D₀ k : ℝ)) * (C₁ * Real.log R) + Ctail * Real.log R / (D₀ k : ℝ) :=
        add_le_add e2 hTb
    _ = (2 * C₁ + Ctail) * Real.log R / (D₀ k : ℝ) := by ring

end Salt.Maynard
