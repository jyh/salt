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
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
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

/-! ## D5 — the multi-index tail (Maynard's 5.31), discharging `htail`

The per-coordinate reciprocal-`φ²` sums, the coordinate factorization, and the
assembly into the `O(log R / D₀)` tail bound.  All constants are `R`-free. -/

/-- The per-coordinate index set for the `j`-deviating tail: squarefree `x < R`
with all prime factors `> D₀ k`, divisible by `r i`, and (only for the deviating
coordinate `i = j`) constrained to `x ≠ r j`. -/
noncomputable def tailCoordSet (k R : ℕ) (r : Fin k → ℕ) (j i : Fin k) : Finset ℕ :=
  (Finset.range R).filter
    (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ r i ∣ x ∧ (i = j → x ≠ r j))

/-- For a squarefree coordinate value `ρ` with all prime factors `≥ 3`,
`g(ρ)·ρ/φ(ρ)² ∈ [0,1]` (it is `∏_{p∣ρ}(1 − (p−1)⁻²)`). -/
private theorem gr_ratio_mem {ρ : ℕ} (hρ : Squarefree ρ)
    (hodd : ∀ p ∈ ρ.primeFactors, 3 ≤ p) :
    0 ≤ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2
      ∧ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2 ≤ 1 := by
  rw [g_factor_prod hρ hodd]
  refine ⟨Finset.prod_nonneg (fun p hp => ?_),
    Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)⟩
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · nlinarith [sq_nonneg (((p : ℝ) - 1)⁻¹)]

/-- **The deviating-coordinate tail (his 5.31, per coordinate).** Over squarefree
`x < R` with all prime factors `> D₀ k`, divisible by `ρ` but `≠ ρ`, the
reciprocal-`φ²` sum is `≤ (12k²/D₀ k)/φ(ρ)²`.  Reindex `x = ρ·c` (`c ≠ 1`,
coprime to `ρ`), so `φ(x) = φ(ρ)·φ(c)`, and apply `phiSq_tail_bound`. -/
private theorem phiSq_dvd_ne_bound (k R : ℕ) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k)
    (ρ : ℕ) (hρsq : Squarefree ρ) (_hρp : ∀ p ∈ ρ.primeFactors, D₀ k < p) :
    ∑ x ∈ (Finset.range R).filter
        (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x ∧ x ≠ ρ),
      1 / (Nat.totient x : ℝ) ^ 2
      ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) := by
  classical
  set S := (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x ∧ x ≠ ρ) with hSdef
  set T := ((Finset.range R).filter
      (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1 with hTdef
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρsq.ne_zero
  have hxmem : ∀ x ∈ S, ρ ∣ x ∧ Squarefree x ∧ x < R
      ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ x ≠ ρ := by
    intro x hx
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hx
    exact ⟨hx.2.2.2.1, hx.2.1, hx.1, hx.2.2.1, hx.2.2.2.2⟩
  have hφfac : ∀ x ∈ S, (Nat.totient x : ℝ) = (Nat.totient ρ : ℝ) * (Nat.totient (x / ρ) : ℝ) := by
    intro x hx
    obtain ⟨hdvd, hxsq, _, _, _⟩ := hxmem x hx
    have hxeq : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdvd
    have hcop : Nat.Coprime ρ (x / ρ) := by
      have hx' : Squarefree (ρ * (x / ρ)) := by rw [hxeq]; exact hxsq
      exact (Nat.squarefree_mul_iff.mp hx').1
    have hh := Nat.totient_mul hcop
    rw [hxeq] at hh
    rw [hh]; push_cast; ring
  have hinj : Set.InjOn (fun x => x / ρ) ↑S := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨hdx, _⟩ := hxmem x hx
    obtain ⟨hdy, _⟩ := hxmem y hy
    have e1 : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdx
    have e2 : ρ * (y / ρ) = y := Nat.mul_div_cancel' hdy
    simp only at hxy
    rw [← e1, ← e2, hxy]
  have himg : S.image (fun x => x / ρ) ⊆ T := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨hdvd, hxsq, hxR, hxp, hxne⟩ := hxmem x hx
    have hxeq : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdvd
    have hcdvd : (x / ρ) ∣ x := ⟨ρ, by rw [mul_comm]; exact hxeq.symm⟩
    rw [hTdef, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, lt_of_le_of_lt (Nat.div_le_self x ρ) hxR,
      hxsq.squarefree_of_dvd hcdvd, ?_⟩
    · intro h1
      exact hxne (by rw [← hxeq, h1, mul_one])
    · intro p hp
      exact hxp p (Nat.primeFactors_mono hcdvd hxsq.ne_zero hp)
  calc ∑ x ∈ S, 1 / (Nat.totient x : ℝ) ^ 2
      = ∑ x ∈ S, (1 / (Nat.totient ρ : ℝ) ^ 2) * (1 / (Nat.totient (x / ρ) : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [hφfac x hx, mul_pow]
        simp only [one_div, mul_inv]
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ x ∈ S, 1 / (Nat.totient (x / ρ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2)
          * ∑ c ∈ S.image (fun x => x / ρ), 1 / (Nat.totient c : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ c ∈ T, 1 / (Nat.totient c : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun c _ _ => by positivity)
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ c ∈ T, ((μ c : ℤ) : ℝ) ^ 2 / (Nat.totient c : ℝ) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl (fun c hc => ?_)
        rw [hTdef, Finset.mem_erase, Finset.mem_filter] at hc
        rw [moebius_sq_one hc.2.2.1]
    _ ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hTdef]
        exact phiSq_tail_bound k R hk hD

/-- **The non-deviating-coordinate tail.** Without the `x ≠ ρ` constraint, the
reciprocal-`φ²` sum is `≤ 2/φ(ρ)²` (the `x = ρ` term contributes `1/φ(ρ)²`, the
`x ≠ ρ` tail `≤ (12k²/D₀)/φ(ρ)² ≤ 1/φ(ρ)²` by `hD`). -/
private theorem phiSq_dvd_bound (k R : ℕ) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k)
    (ρ : ℕ) (hρsq : Squarefree ρ) (hρp : ∀ p ∈ ρ.primeFactors, D₀ k < p) (hρR : ρ < R) :
    ∑ x ∈ (Finset.range R).filter
        (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x),
      1 / (Nat.totient x : ℝ) ^ 2
      ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * 2 := by
  classical
  set B := (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x) with hBdef
  have hD0 : 0 < D₀ k := by
    have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega); omega
  have hρmem : ρ ∈ B := by
    rw [hBdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨hρR, hρsq, hρp, dvd_refl ρ⟩
  have hsplit : ∑ x ∈ B, 1 / (Nat.totient x : ℝ) ^ 2
      = 1 / (Nat.totient ρ : ℝ) ^ 2 + ∑ x ∈ B.erase ρ, 1 / (Nat.totient x : ℝ) ^ 2 :=
    (Finset.add_sum_erase B (fun x => 1 / (Nat.totient x : ℝ) ^ 2) hρmem).symm
  have hBerase : B.erase ρ = (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x ∧ x ≠ ρ) := by
    rw [hBdef]
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    tauto
  have htail := phiSq_dvd_ne_bound k R hk hD ρ hρsq hρp
  rw [← hBerase] at htail
  have h12 : (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hD0)]; exact_mod_cast hD
  have hnn : (0 : ℝ) ≤ 1 / (Nat.totient ρ : ℝ) ^ 2 := by positivity
  rw [hsplit]
  have hmul := mul_le_mul_of_nonneg_left h12 hnn
  nlinarith [htail, hmul]

/-- **The coordinate factorization (Step 3).** The divisor-guarded, `j`-deviating
tail sum over the coupled index set factorizes across coordinates: it is
dominated by the product of per-coordinate sums over `tailCoordSet`. -/
private theorem tail_factor_le (k R : ℕ) (j : Fin k) (r : Fin k → ℕ)
    (H : Fin k → ℕ → ℝ) (hH : ∀ i x, 0 ≤ H i x) :
    ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
        ∏ i, H i (a i)
      ≤ ∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haK, hguard, hdev⟩ := ha
    have hK := (mem_kSieveIndex_iff a).mp haK
    rw [Fintype.mem_piFinset]
    intro i
    simp only [tailCoordSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨kSieveIndex_coord_lt haK i, hK.1 i, ?_, hguard i, ?_⟩
    · intro p hp
      exact D₀_lt_of_prime_dvd_coord haK (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
    · intro hij; subst hij; exact hdev
  · intro a _ _
    exact Finset.prod_nonneg (fun i _ => hH i (a i))

/-- **Maynard's (5.31) multi-index tail bound.** The `∃ i ≠ m, aᵢ ≠ rᵢ` part of
the contraction is `O(log R / D₀)` with an `R`-free constant `Ctail`.  Signs are
stripped (`|y|,|μ| ≤ 1`), the sdiff is covered by the union over which coordinate
deviates, each `j`-term factorizes across coordinates (`tail_factor_le`), the
`m`-coordinate gives a `log R` (Rankin), the deviating coordinate `j` gives the
`12k²/D₀` decay (`phiSq_dvd_ne_bound`), the rest are `≤ 2` (`phiSq_dvd_bound`),
and `g(rᵢ)rᵢ/φ(rᵢ)² ≤ 1` (`gr_ratio_mem`) collapses the prefactor. -/
theorem htail_bound (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (_hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R (W k))
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧
      |(∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
          * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
                ((kSieveIndex k R (W k)).filter
                  (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
              (y a / ∏ i, (Nat.totient (a i) : ℝ))
                * ∏ i ∈ Finset.univ.erase m,
                    (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))|
        ≤ Ctail * Real.log R / (D₀ k : ℝ) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  obtain ⟨C₁, hC₁1, hC₁⟩ := rankin_bound 1
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D₀ k := by omega
  have hD0 : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0
  have hD0ne : (D₀ k : ℝ) ≠ 0 := hD0R.ne'
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hC₁0 : (0 : ℝ) ≤ C₁ := by linarith
  have hodd : ∀ i, ∀ p ∈ (r i).primeFactors, 3 ≤ p := by
    intro i p hp
    have := D₀_lt_of_prime_dvd_coord hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hrp : ∀ i, ∀ p ∈ (r i).primeFactors, D₀ k < p := fun i p hp =>
    D₀_lt_of_prime_dvd_coord hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hRankin : ∑ q ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ C₁ * Real.log R := by
    have h := hC₁ R hR; simpa using h
  set H : Fin k → ℕ → ℝ := fun i x =>
    if i = m then 1 / (Nat.totient x : ℝ) else (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 with hHdef
  have hHnn : ∀ i x, 0 ≤ H i x := by
    intro i x; simp only [hHdef]; split_ifs <;> positivity
  set P : ℝ := ∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ) with hPdef
  set INNER : (Fin k → ℕ) → ℝ := fun a =>
    (y a / ∏ i, (Nat.totient (a i) : ℝ))
      * ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))) with hINNERdef
  set FG := (kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i) with hFGdef
  set Df := (kSieveIndex k R (W k)).filter
      (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i) with hDfdef
  -- per-`a` pointwise bound `|INNER a| ≤ ∏ᵢ Hᵢ(aᵢ)`
  have hbound : ∀ a ∈ kSieveIndex k R (W k), |INNER a| ≤ ∏ i, H i (a i) := by
    intro a haK
    have hφa : ∀ i, (0 : ℝ) < (Nat.totient (a i) : ℝ) := fun i => by
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos haK i)
    have hΦsplit : (∏ i, (Nat.totient (a i) : ℝ))
        = (Nat.totient (a m) : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ) :=
      (Finset.mul_prod_erase Finset.univ (fun i => (Nat.totient (a i) : ℝ))
        (Finset.mem_univ m)).symm
    have hprodH : (∏ i, H i (a i))
        = (1 / (Nat.totient (a m) : ℝ))
          * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => H i (a i)) (Finset.mem_univ m)]
      congr 1
      · simp only [hHdef]; rw [if_true]
      · exact Finset.prod_congr rfl (fun i hi => by
          simp only [hHdef]; rw [if_neg (Finset.ne_of_mem_erase hi)])
    rw [hprodH]
    simp only [hINNERdef]
    rw [abs_mul, abs_div, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hφa i).le)),
      Finset.abs_prod]
    have hstep2 : ∀ i ∈ Finset.univ.erase m,
        |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
          ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by
      intro i _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ))]
      have h1 := abs_moebius_real_le_one (a i)
      have h2 : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by positivity
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - |((μ (a i) : ℤ) : ℝ)|) h2]
    calc |y a| / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
        ≤ 1 / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ)) := by
          apply mul_le_mul
          · rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
            calc |y a| * (∏ i, (Nat.totient (a i) : ℝ))⁻¹
                ≤ 1 * (∏ i, (Nat.totient (a i) : ℝ))⁻¹ :=
                  mul_le_mul_of_nonneg_right (hy1 a) (by positivity)
              _ = (∏ i, (Nat.totient (a i) : ℝ))⁻¹ := one_mul _
          · exact Finset.prod_le_prod (fun i _ => abs_nonneg _) hstep2
          · exact Finset.prod_nonneg (fun i _ => abs_nonneg _)
          · positivity
      _ = (1 / (Nat.totient (a m) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
          rw [hΦsplit, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_pow]
          have hPFne : (∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ)) ≠ 0 :=
            (Finset.prod_pos (fun i _ => hφa i)).ne'
          have hφamne : (Nat.totient (a m) : ℝ) ≠ 0 := (hφa m).ne'
          field_simp
  -- per-`j` product bound (all `R`-free except the single `log R`)
  have hjbound : ∀ j ∈ Finset.univ.erase m,
      |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ C₁ * Real.log R * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k := by
    intro j hj
    have hjm : j ≠ m := Finset.ne_of_mem_erase hj
    have hfact := tail_factor_le k R j r H hHnn
    set U : Fin k → ℝ := fun i =>
      (r i : ℝ) * (if i = j then (1 / (Nat.totient (r i) : ℝ) ^ 2) * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ))
        else (1 / (Nat.totient (r i) : ℝ) ^ 2) * 2) with hUdef
    -- factor bound per coordinate `i ≠ m`
    have hUbound : ∀ i ∈ Finset.univ.erase m, (∑ x ∈ tailCoordSet k R r j i, H i x) ≤ U i := by
      intro i hi
      have him : i ≠ m := Finset.ne_of_mem_erase hi
      have hHi : ∀ x, H i x = (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 := by
        intro x; simp only [hHdef]; rw [if_neg him]
      rw [Finset.sum_congr rfl (fun x _ => hHi x)]
      rw [show (∑ x ∈ tailCoordSet k R r j i, (r i : ℝ) / (Nat.totient x : ℝ) ^ 2)
            = (r i : ℝ) * ∑ x ∈ tailCoordSet k R r j i, 1 / (Nat.totient x : ℝ) ^ 2 from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by rw [mul_one_div])]
      simp only [hUdef]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hij : i = j
      · rw [if_pos hij]
        have hset : tailCoordSet k R r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ r i ∣ x ∧ x ≠ r i) := by
          simp only [tailCoordSet]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_ne_bound k R hk hD (r i) (hsq i) (hrp i)
      · rw [if_neg hij]
        have hset : tailCoordSet k R r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ r i ∣ x) := by
          simp only [tailCoordSet]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_bound k R hk hD (r i) (hsq i) (hrp i) (kSieveIndex_coord_lt hrsupp i)
    -- the `m`-coordinate factor `≤ C₁ log R`
    have hmfac : (∑ x ∈ tailCoordSet k R r j m, H m x) ≤ C₁ * Real.log R := by
      have hHm : ∀ x, H m x = 1 / (Nat.totient x : ℝ) := by
        intro x; simp only [hHdef]; rw [if_true]
      rw [Finset.sum_congr rfl (fun x _ => hHm x)]
      refine le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)) hRankin
      intro x hx
      simp only [tailCoordSet, Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hx.1, hx.2.1⟩
    -- `|P| ≤ ∏_{i≠m} g(rᵢ)`
    have hPabs : |P| ≤ ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
      rw [hPdef]
      calc |∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)|
          = ∏ i, |((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)| := Finset.abs_prod _ _
        _ ≤ ∏ i, (gMult (r i) : ℝ) := by
            refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gMult (r i) : ℝ))]
            calc |((μ (r i) : ℤ) : ℝ)| * (gMult (r i) : ℝ)
                ≤ 1 * (gMult (r i) : ℝ) := by
                  apply mul_le_mul_of_nonneg_right (abs_moebius_real_le_one _) (by positivity)
              _ = (gMult (r i) : ℝ) := one_mul _
        _ = ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
            rw [← Finset.mul_prod_erase Finset.univ (fun i => (gMult (r i) : ℝ))
              (Finset.mem_univ m), hrm]
            simp [gMult, Nat.primeFactors_one]
    -- combine per-coordinate factors
    have hprodU : (∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x)
        ≤ (∑ x ∈ tailCoordSet k R r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x ∈ tailCoordSet k R r j i, H i x)
        (Finset.mem_univ m)]
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun x _ => hHnn m x))
      exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun x _ => hHnn i x)) hUbound
    -- `(g·U) j ≤ 12k²/D₀`
    have hjfac : (gMult (r j) : ℝ) * U j ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := by
      simp only [hUdef]; rw [if_true]
      rw [show (gMult (r j) : ℝ) * ((r j : ℝ)
              * ((1 / (Nat.totient (r j) : ℝ) ^ 2) * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ))))
            = ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) from by ring]
      calc ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ))
          ≤ 1 * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) :=
            mul_le_mul_of_nonneg_right (gr_ratio_mem (hsq j) (hodd j)).2 (by positivity)
        _ = 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := one_mul _
    -- the rest of the coordinates `≤ 2^k`
    have hrestfac : ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) ≤ 2 ^ k := by
      have hcard : ((Finset.univ.erase m).erase j).card ≤ k := by
        calc ((Finset.univ.erase m).erase j).card
            ≤ (Finset.univ : Finset (Fin k)).card :=
              Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      calc ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i)
          ≤ ∏ _i ∈ (Finset.univ.erase m).erase j, (2 : ℝ) := by
            refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]; positivity
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]
              rw [show (gMult (r i) : ℝ) * ((r i : ℝ) * ((1 / (Nat.totient (r i) : ℝ) ^ 2) * 2))
                    = ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) * 2 from by
                    ring]
              nlinarith [(gr_ratio_mem (hsq i) (hodd i)).1, (gr_ratio_mem (hsq i) (hodd i)).2]
        _ = (2 : ℝ) ^ ((Finset.univ.erase m).erase j).card := by rw [Finset.prod_const]
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hcard
    have hrestnn : (0 : ℝ) ≤ ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) := by
      refine Finset.prod_nonneg (fun i hi => ?_)
      have hijne : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [hUdef]; rw [if_neg hijne]; positivity
    -- assemble
    calc |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ |P| * ∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x :=
          mul_le_mul_of_nonneg_left hfact (abs_nonneg _)
      _ ≤ |P| * ((∑ x ∈ tailCoordSet k R r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i) :=
          mul_le_mul_of_nonneg_left hprodU (abs_nonneg _)
      _ = (∑ x ∈ tailCoordSet k R r j m, H m x) * (|P| * ∏ i ∈ Finset.univ.erase m, U i) := by ring
      _ ≤ (C₁ * Real.log R) * ((12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k) := by
          refine mul_le_mul hmfac ?_ ?_ (mul_nonneg hC₁0 hlogR)
          · calc |P| * ∏ i ∈ Finset.univ.erase m, U i
                ≤ (∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
                    * ∏ i ∈ Finset.univ.erase m, U i := by
                  refine mul_le_mul_of_nonneg_right hPabs (Finset.prod_nonneg (fun i _ => ?_))
                  simp only [hUdef]; split_ifs <;> positivity
              _ = ∏ i ∈ Finset.univ.erase m, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.prod_mul_distrib).symm
              _ = ((gMult (r j) : ℝ) * U j)
                    * ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.mul_prod_erase (Finset.univ.erase m)
                    (fun i => (gMult (r i) : ℝ) * U i) hj).symm
              _ ≤ (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k :=
                  mul_le_mul hjfac hrestfac hrestnn (by positivity)
          · exact mul_nonneg (abs_nonneg _)
              (Finset.prod_nonneg (fun i _ => by simp only [hUdef]; split_ifs <;> positivity))
      _ = C₁ * Real.log R * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k := by ring
  -- main bound
  refine ⟨12 * (k : ℝ) ^ 3 * 2 ^ k * C₁, mul_nonneg (by positivity) hC₁0, ?_⟩
  rw [abs_mul]
  calc |P| * |∑ a ∈ FG \ Df, INNER a|
      ≤ |P| * ∑ a ∈ FG \ Df, |INNER a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |P| * ∑ a ∈ FG \ Df, ∏ i, H i (a i) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a ha => ?_)) (abs_nonneg _)
        rw [Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
        exact hbound a ha.1.1
    _ ≤ |P| * ∑ j ∈ Finset.univ.erase m,
          ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
            ∏ i, H i (a i) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hunion : ∀ a ∈ FG \ Df, (∏ i, H i (a i))
            ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
          intro a ha
          rw [Finset.mem_sdiff] at ha
          obtain ⟨haFG, haDf⟩ := ha
          rw [hFGdef, Finset.mem_filter] at haFG
          obtain ⟨j, hjmem, hjne⟩ : ∃ j ∈ Finset.univ.erase m, a j ≠ r j := by
            by_contra hcon
            apply haDf
            rw [hDfdef, Finset.mem_filter]
            refine ⟨haFG.1, haFG.2, fun i hi => ?_⟩
            by_contra hne
            exact hcon ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hne⟩
          calc (∏ i, H i (a i)) = if a j ≠ r j then ∏ i, H i (a i) else 0 := by rw [if_pos hjne]
            _ ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
                refine Finset.single_le_sum
                  (f := fun j => if a j ≠ r j then ∏ i, H i (a i) else 0) (fun j _ => ?_) hjmem
                split_ifs
                · exact Finset.prod_nonneg (fun i _ => hHnn i (a i))
                · exact le_refl 0
        calc ∑ a ∈ FG \ Df, ∏ i, H i (a i)
            ≤ ∑ a ∈ FG \ Df, ∑ j ∈ Finset.univ.erase m,
                (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_le_sum hunion
          _ = ∑ j ∈ Finset.univ.erase m, ∑ a ∈ FG \ Df,
                (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_comm
          _ ≤ ∑ j ∈ Finset.univ.erase m,
                ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
                  ∏ i, H i (a i) := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              rw [← Finset.sum_filter]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                (fun a _ _ => Finset.prod_nonneg (fun i _ => hHnn i (a i)))
              intro a ha
              rw [Finset.mem_filter, Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
              rw [Finset.mem_filter]
              exact ⟨ha.1.1.1, ha.1.1.2, ha.2⟩
    _ = ∑ j ∈ Finset.univ.erase m,
          |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
            ∏ i, H i (a i) := Finset.mul_sum _ _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase m, C₁ * Real.log R * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k :=
        Finset.sum_le_sum hjbound
    _ = ((Finset.univ.erase m).card : ℝ)
          * (C₁ * Real.log R * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 12 * (k : ℝ) ^ 3 * 2 ^ k * C₁ * Real.log R / (D₀ k : ℝ) := by
        have hcardle : ((Finset.univ.erase m).card : ℝ) ≤ (k : ℝ) := by
          have : (Finset.univ.erase m).card ≤ k := by
            calc (Finset.univ.erase m).card ≤ (Finset.univ : Finset (Fin k)).card :=
                  Finset.card_le_card (Finset.erase_subset _ _)
              _ = k := by rw [Finset.card_univ, Fintype.card_fin]
          exact_mod_cast this
        have hXnn : (0 : ℝ) ≤ C₁ * Real.log R * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k :=
          mul_nonneg (mul_nonneg (mul_nonneg hC₁0 hlogR) (by positivity)) (by positivity)
        have heq : (k : ℝ) * (C₁ * Real.log R * (12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)) * 2 ^ k)
            = 12 * (k : ℝ) ^ 3 * 2 ^ k * C₁ * Real.log R / (D₀ k : ℝ) := by
          field_simp
        exact le_trans (mul_le_mul_of_nonneg_right hcardle hXnn) (le_of_eq heq)

/-! ## D4 — assembly of Lemma 5.3 (UNCONDITIONAL)

`lemma53` now takes ONLY the numeric hypotheses `hk`, `hD` plus the standard
`|y|≤1` / support / tuple hypotheses. All three `O(logR/D₀)` pieces are
DISCHARGED in-repo: the `|G−1|` step-C bound via `gProd_bound` (`inv_sq_tele`),
the main-sum size via `abs_mainSum_le` (`rankin_bound`), and the Maynard (5.31)
multi-index tail (the `∃ i≠m, aᵢ≠rᵢ` sub-sum) via `htail_bound`
(`phiSq_tail_bound` + Rankin + the coordinate factorization `tail_factor_le`). -/

/-- **Lemma 5.3 (unconditional).** For `rₘ = 1`, `y^{(m)}_r` equals the single
`m`-coordinate sum `∑_{aₘ<R} y_{r;m→aₘ}/φ(aₘ)` up to an `O(log R / D₀)` error.
Everything is discharged from `stepB_identity` (exact algebra) + `gProd_bound`
(Step C, `inv_sq_tele`) + `abs_mainSum_le` (`rankin_bound`) + `htail_bound`
(Maynard 5.31 multi-index tail). The error constant is `R`-free. -/
theorem lemma53 (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R (W k))
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      |yM k R (W k) m y r
          - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
        ≤ C * Real.log R / (D₀ k : ℝ) := by
  classical
  obtain ⟨C₁, hC₁1, hSb⟩ := abs_mainSum_le k R m y hy1 hysupp r hR
  obtain ⟨Ctail, hCtail0, hTb⟩ := htail_bound k R m y hy1 hysupp r hrm hR hrsupp hk hD
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
