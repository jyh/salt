/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.KSieve
import Salt.Maynard.Diagonal
import Salt.Maynard.LamBound
import Salt.Maynard.Rankin
import Salt.Maynard.Mertens
import Salt.Maynard.PhiAtom

/-!
# Sharp per-tuple bound on the Selberg weight `λ` (endgame prerequisite)

The crude bound (`Salt.Maynard.lam_abs_le`) drops the divisibility guard in
`wSum`, leaving a factor `∏ᵢ dᵢ = D < R` which reintroduces an `R`-sized
factor: `|λ(d)| ≤ R·(C log R)^k ≫ N`. This file records the *sharp* bound

    `|λ(d)| ≤ C·(1 + log R)^(k+1)`

with `C` **explicit and independent of `R`** (it depends only on `k`,
through the power, and on the two absolute Mertens/Rankin constants). The
gain comes from *keeping* the divisibility guard: the per-coordinate sum
over `{s < R : dᵢ ∣ s, squarefree}` reindexes (via `s = dᵢ·t`) to
`(1/φ(dᵢ))·Σ_{t<R sqfree} 1/φ(t) ≤ (1/φ(dᵢ))·C₁ log R`, so that
`|wSum d| ≤ (∏ᵢ 1/φ(dᵢ))·(C₁ log R)^k`, and the leftover `∏ᵢ dᵢ / ∏ᵢ φ(dᵢ)
= D/φ(D) ≤ C₃ log R` is exactly a Mertens-type bound (never `≤ D`).

Constant: `C = C₃ · C₁^k`, where
* `C₁ ≥ 1` is Rankin's constant (`rankin_bound` at `L = 1`), and
* `C₃ = max (exp C₂) 1`, `C₂` the Mertens constant of
  `sum_inv_prime_sub_one_le`.

Both are absolute — no dependence on `R`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## Multiplicativity helpers for pairwise-coprime families -/

/-- `φ(∏ᵢ dᵢ) = ∏ᵢ φ(dᵢ)` for a pairwise-coprime family. -/
theorem prod_totient_coprime {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (d i) (d j)) :
    Nat.totient (∏ i ∈ s, d i) = ∏ i ∈ s, Nat.totient (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hca : Nat.Coprime (d a) (∏ i ∈ s, d i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact has hi)
    rw [Finset.prod_insert has, Finset.prod_insert has, Nat.totient_mul hca,
      ih (fun i hi j hj hij =>
        hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]

/-- A product of pairwise-coprime squarefrees is squarefree. -/
theorem squarefree_prod_coprime {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (hsf : ∀ i ∈ s, Squarefree (d i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (d i) (d j)) :
    Squarefree (∏ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact squarefree_one
  | @insert a s has ih =>
    have hca : Nat.Coprime (d a) (∏ i ∈ s, d i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact has hi)
    rw [Finset.prod_insert has, Nat.squarefree_mul hca]
    exact ⟨hsf a (Finset.mem_insert_self a s),
      ih (fun i hi => hsf i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij =>
          hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)⟩

/-! ## The `D/φ(D) ≤ C₃ log R` Mertens bound (step 5) -/

/-- **The Mertens ratio bound.** For any squarefree `D < R` (`R ≥ 2`),
`D/φ(D) ≤ C₃·(1 + log R)` with `C₃ = max (exp C₂) 1` an absolute constant.
The estimate `D/φ(D) = ∏_{p∣D}(1 + 1/(p−1)) ≤ exp(Σ_{p≤D} 1/(p−1))
≤ exp(loglog D + C₂) = exp(C₂)·log D ≤ C₃(1 + log R)`. -/
theorem phi_ratio_le :
    ∃ C₃ : ℝ, 1 ≤ C₃ ∧ ∀ {D R : ℕ}, Squarefree D → D < R → 2 ≤ R →
      (D : ℝ) / (Nat.totient D : ℝ) ≤ C₃ * (1 + Real.log R) := by
  obtain ⟨C₂, hC₂⟩ := sum_inv_prime_sub_one_le
  refine ⟨max (Real.exp C₂) 1, le_max_right _ _, ?_⟩
  intro D R hD hDR hR
  -- `log R ≥ 0`.
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hR
  have hlogR : 0 ≤ Real.log R := (Real.log_pos hR1).le
  have hlogR1 : (0 : ℝ) ≤ 1 + Real.log R := by linarith
  set C₃ : ℝ := max (Real.exp C₂) 1 with hC₃def
  have hC₃1 : (1 : ℝ) ≤ C₃ := le_max_right _ _
  by_cases hD1 : D = 1
  · -- `D = 1`: ratio is `1`.
    subst hD1
    simp only [Nat.totient_one, Nat.cast_one, div_one]
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ C₃ * (1 + Real.log R) := by
          apply mul_le_mul hC₃1 (by linarith) zero_le_one (le_trans zero_le_one hC₃1)
  · -- `D ≥ 2`.
    have hDpos : 0 < D := Nat.pos_of_ne_zero hD.ne_zero
    have hD2 : 2 ≤ D := by
      have h0 : D ≠ 0 := hD.ne_zero
      omega
    have hDR2 : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD2
    have hlogD : 0 < Real.log D := Real.log_pos (by exact_mod_cast hD2)
    -- Step A: `D/φ(D) = ∏_{p∣D} p/(p-1)`.
    have hnum : (D : ℝ) = ∏ p ∈ D.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hD]
    have hden : (Nat.totient D : ℝ) = ∏ p ∈ D.primeFactors, ((p : ℝ) - 1) :=
      totient_squarefree_cast hD
    have ratio_eq : (D : ℝ) / (Nat.totient D : ℝ)
        = ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
      rw [hnum, hden, ← Finset.prod_div_distrib]
    -- Step B: termwise `p/(p-1) ≤ exp(1/(p-1))`.
    have hStepB : ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∏ p ∈ D.primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        apply div_nonneg <;> linarith
      · intro p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have hsplit : (p : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) + 1 := by
          field_simp; ring
        rw [hsplit]
        linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
    -- Step C: `∏ exp = exp(∑)`.
    have hStepC : ∏ p ∈ D.primeFactors, Real.exp (1 / ((p : ℝ) - 1))
        = Real.exp (∑ p ∈ D.primeFactors, 1 / ((p : ℝ) - 1)) :=
      (Real.exp_sum _ _).symm
    -- Step D: extend the prime sum to all primes `≤ D`.
    have hsub : D.primeFactors ⊆ (Finset.range (D + 1)).filter Nat.Prime := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hDpos hp.2.1), hp.1⟩
    have hStepD : ∑ p ∈ D.primeFactors, 1 / ((p : ℝ) - 1)
        ≤ ∑ p ∈ (Finset.range (D + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      apply div_nonneg <;> linarith
    -- Step E: Mertens.
    have hMert := hC₂ D hD2
    -- Assemble.
    have hlogDR : Real.log D ≤ 1 + Real.log R := by
      have : Real.log D ≤ Real.log R :=
        Real.log_le_log (by exact_mod_cast hDpos) (by exact_mod_cast hDR.le)
      linarith
    have hexpC₂ : Real.exp C₂ ≤ C₃ := le_max_left _ _
    calc (D : ℝ) / (Nat.totient D : ℝ)
        = ∏ p ∈ D.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := ratio_eq
      _ ≤ ∏ p ∈ D.primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := hStepB
      _ = Real.exp (∑ p ∈ D.primeFactors, 1 / ((p : ℝ) - 1)) := hStepC
      _ ≤ Real.exp (∑ p ∈ (Finset.range (D + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)) :=
          Real.exp_le_exp.mpr hStepD
      _ ≤ Real.exp (Real.log (Real.log D) + C₂) := Real.exp_le_exp.mpr hMert
      _ = Real.log D * Real.exp C₂ := by
          rw [Real.exp_add, Real.exp_log hlogD]
      _ ≤ (1 + Real.log R) * C₃ := by
          apply mul_le_mul hlogDR hexpC₂ (Real.exp_pos _).le hlogR1
      _ = C₃ * (1 + Real.log R) := mul_comm _ _

/-! ## The per-coordinate reindex (step 4) -/

/-- **Per-coordinate divisor-sum bound.** For squarefree `a`,
`Σ_{s<R : a∣s, sqfree} 1/φ(s) ≤ (1/φ(a))·Σ_{t<R sqfree} 1/φ(t)`, via the
reindex `s = a·(s/a)` (`φ(s) = φ(a)·φ(s/a)`, `gcd(a, s/a) = 1`). -/
theorem coord_sum_le {a R : ℕ} (_ha : Squarefree a) :
    ∑ s ∈ (Finset.range R).filter (fun s => Squarefree s ∧ a ∣ s), 1 / (Nat.totient s : ℝ)
      ≤ (1 / (Nat.totient a : ℝ)) *
          ∑ t ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient t : ℝ) := by
  set T := (Finset.range R).filter (fun s => Squarefree s ∧ a ∣ s) with hT
  set U := (Finset.range R).filter Squarefree with hU
  -- Injectivity of `s ↦ s/a` on `T`.
  have hinj : Set.InjOn (fun s => s / a) (↑T : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hT, Finset.mem_filter] at hx hy
    obtain ⟨_, _, hxa⟩ := hx
    obtain ⟨_, _, hya⟩ := hy
    have hxy' : x / a = y / a := hxy
    calc x = a * (x / a) := (Nat.mul_div_cancel' hxa).symm
      _ = a * (y / a) := by rw [hxy']
      _ = y := Nat.mul_div_cancel' hya
  -- `T.image (·/a) ⊆ U`.
  have himg : T.image (fun s => s / a) ⊆ U := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [hT, Finset.mem_filter, Finset.mem_range] at hs
    obtain ⟨hsR, hssf, hadvd⟩ := hs
    rw [hU, Finset.mem_filter, Finset.mem_range]
    refine ⟨lt_of_le_of_lt (Nat.div_le_self s a) hsR, ?_⟩
    exact hssf.squarefree_of_dvd ⟨a, (Nat.div_mul_cancel hadvd).symm⟩
  -- Per-term factorization of `1/φ(s)`.
  have hterm : ∀ s ∈ T, (1 : ℝ) / (Nat.totient s : ℝ)
      = (1 / (Nat.totient a : ℝ)) * (1 / (Nat.totient (s / a) : ℝ)) := by
    intro s hs
    rw [hT, Finset.mem_filter] at hs
    obtain ⟨_, hssf, hadvd⟩ := hs
    have hsa : a * (s / a) = s := Nat.mul_div_cancel' hadvd
    have hcop : Nat.Coprime a (s / a) := by
      apply Nat.coprime_of_squarefree_mul; rw [hsa]; exact hssf
    have hφ : (Nat.totient s : ℝ) = (Nat.totient a : ℝ) * (Nat.totient (s / a) : ℝ) := by
      rw [← Nat.cast_mul, ← Nat.totient_mul hcop, hsa]
    rw [hφ, one_div_mul_one_div]
  calc ∑ s ∈ T, 1 / (Nat.totient s : ℝ)
      = (1 / (Nat.totient a : ℝ)) * ∑ s ∈ T, 1 / (Nat.totient (s / a) : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl hterm
    _ = (1 / (Nat.totient a : ℝ)) *
          ∑ t ∈ T.image (fun s => s / a), 1 / (Nat.totient t : ℝ) := by
        rw [Finset.sum_image hinj]
    _ ≤ (1 / (Nat.totient a : ℝ)) * ∑ t ∈ U, 1 / (Nat.totient t : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun t _ _ => by positivity)

/-! ## The guarded `wSum` bound (steps 2–3) -/

/-- **Guarded triangle bound on `wSum`.** With `|y| ≤ 1`, `|wSum d|` is
bounded by the divisor-*guarded* reciprocal-totient sum (guard kept). -/
theorem abs_wSum_le_guarded {k R W : ℕ} (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ r, |y r| ≤ 1) (d : Fin k → ℕ) :
    |wSum k R W y d|
      ≤ ∑ r ∈ kSieveIndex k R W,
          (if ∀ i, d i ∣ r i then (1 : ℝ) / ∏ i, (Nat.totient (r i) : ℝ) else 0) := by
  rw [wSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro r hr
  have hΦpos : (0 : ℝ) < ∏ i, (Nat.totient (r i) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have : 0 < Nat.totient (r i) := Nat.totient_pos.mpr (kSieveIndex_coord_pos hr i)
    exact_mod_cast this
  by_cases h : ∀ i, d i ∣ r i
  · rw [if_pos h, if_pos h, abs_div, abs_of_nonneg hΦpos.le]
    gcongr
    exact hy1 r
  · rw [if_neg h, if_neg h, abs_zero]

/-- **Guarded sum factorizes across coordinates.** The divisor-guarded
sum over the coupled index set `𝒟` is dominated by the product of the
per-coordinate (uncoupled) divisor sums. -/
theorem guarded_sum_le_prod {k R W : ℕ} (d : Fin k → ℕ) :
    ∑ r ∈ kSieveIndex k R W,
        (if ∀ i, d i ∣ r i then (1 : ℝ) / ∏ i, (Nat.totient (r i) : ℝ) else 0)
      ≤ ∏ i, ∑ s ∈ (Finset.range R).filter (fun s => Squarefree s ∧ d i ∣ s),
          1 / (Nat.totient s : ℝ) := by
  classical
  set T := fun i => (Finset.range R).filter (fun s => Squarefree s ∧ d i ∣ s) with hT
  -- Factorize the product of per-coordinate sums into a sum over `piFinset`.
  rw [Finset.prod_univ_sum T (fun _ s => 1 / (Nat.totient s : ℝ))]
  -- Turn the guarded `𝒟`-sum into a plain sum over the guarded subset.
  rw [← Finset.sum_filter]
  -- Rewrite each `1/∏φ(rᵢ)` as `∏ᵢ 1/φ(rᵢ)`.
  have hrw : ∀ r ∈ (kSieveIndex k R W).filter (fun r => ∀ i, d i ∣ r i),
      (1 : ℝ) / ∏ i, (Nat.totient (r i) : ℝ) = ∏ i, 1 / (Nat.totient (r i) : ℝ) := by
    intro r _
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
  rw [Finset.sum_congr rfl hrw]
  -- The guarded subset injects into `piFinset T`; nonnegativity closes it.
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr𝒟, hguard⟩ := hr
    rw [Fintype.mem_piFinset]
    intro i
    rw [hT, Finset.mem_filter, Finset.mem_range]
    rw [mem_kSieveIndex_iff] at hr𝒟
    exact ⟨kSieveIndex_coord_lt (mem_kSieveIndex_iff r |>.mpr hr𝒟) i, hr𝒟.1 i, hguard i⟩
  · intro r _ _
    exact Finset.prod_nonneg (fun i _ => by positivity)

/-! ## The sharp bound -/

/-- **Sharp per-tuple bound on the Selberg weight `λ`.** With `|y| ≤ 1`,
`|λ(d)| ≤ C·(1 + log R)^(k+1)` for all `d ∈ 𝒟`, where `C = C₃·C₁^k` is an
*explicit constant independent of `R`* (it depends only on `k` and on the
absolute Rankin/Mertens constants `C₁, C₃`). -/
theorem lam_abs_le_sharp (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ r, |y r| ≤ 1) (hR : 2 ≤ R) (_hW : W ≠ 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d ∈ kSieveIndex k R W,
      |lam k R W y d| ≤ C * (1 + Real.log R) ^ (k + 1) := by
  obtain ⟨C₁, hC₁1, hC₁⟩ := rankin_bound 1
  obtain ⟨C₃, hC₃1, hC₃⟩ := phi_ratio_le
  -- Real bookkeeping.
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hR
  have hlogR : 0 ≤ Real.log R := (Real.log_pos hR1).le
  have hlogR1 : (0 : ℝ) ≤ 1 + Real.log R := by linarith
  -- Rankin at `L = 1`: `Σ_{q<R sqfree} 1/φ(q) ≤ C₁ log R`.
  have hRankin : ∑ q ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ C₁ * Real.log R := by
    have h := hC₁ R hR
    simpa using h
  refine ⟨C₃ * C₁ ^ k, ?_, ?_⟩
  · calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ C₃ * C₁ ^ k := by
          apply mul_le_mul hC₃1 (one_le_pow₀ hC₁1) zero_le_one (le_trans zero_le_one hC₃1)
  intro d hd
  rw [mem_kSieveIndex_iff] at hd
  obtain ⟨hsf, hpair, _hcopW, hprodR⟩ := hd
  set D := ∏ i, d i with hDdef
  have hd𝒟 : d ∈ kSieveIndex k R W := (mem_kSieveIndex_iff d).mpr ⟨hsf, hpair, _hcopW, hprodR⟩
  -- `D` is squarefree and `< R`.
  have hDsf : Squarefree D :=
    squarefree_prod_coprime Finset.univ d (fun i _ => hsf i)
      (fun i _ j _ hij => hpair i j hij)
  have hDR : D < R := hprodR
  -- `φ(D) = ∏ᵢ φ(dᵢ)`, cast to `ℝ`.
  have hphiD : (Nat.totient D : ℝ) = ∏ i, (Nat.totient (d i) : ℝ) := by
    rw [hDdef, prod_totient_coprime Finset.univ d (fun i _ j _ hij => hpair i j hij),
      Nat.cast_prod]
  -- Positivity of the coordinate totients.
  have hφpos : ∀ i, (0 : ℝ) < (Nat.totient (d i) : ℝ) := by
    intro i
    have : 0 < Nat.totient (d i) := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hsf i).ne_zero)
    exact_mod_cast this
  -- Step 1: `|λ(d)| ≤ (∏ᵢ dᵢ)·|wSum|`.
  have hlam : |lam k R W y d| ≤ (∏ i, (d i : ℝ)) * |wSum k R W y d| := by
    rw [lam, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_prod_moebius_mul_le d) (abs_nonneg _)
  -- Step 2–4: `|wSum| ≤ (∏ᵢ 1/φ(dᵢ))·(C₁ log R)^k`.
  have hwsum : |wSum k R W y d|
      ≤ (∏ i, 1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) ^ k := by
    refine (abs_wSum_le_guarded y hy1 d).trans ((guarded_sum_le_prod d).trans ?_)
    calc ∏ i, ∑ s ∈ (Finset.range R).filter (fun s => Squarefree s ∧ d i ∣ s),
            1 / (Nat.totient s : ℝ)
        ≤ ∏ i, (1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) := by
          apply Finset.prod_le_prod
          · intro i _
            exact Finset.sum_nonneg (fun s _ => by positivity)
          · intro i _
            refine (coord_sum_le (hsf i)).trans ?_
            exact mul_le_mul_of_nonneg_left hRankin (by positivity)
      _ = (∏ i, 1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) ^ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
  -- Combine and simplify the leftover `D/φ(D)`.
  have hDphi : (∏ i, (d i : ℝ)) * (∏ i, 1 / (Nat.totient (d i) : ℝ))
      = (D : ℝ) / (Nat.totient D : ℝ) := by
    rw [hphiD, hDdef, Nat.cast_prod]
    rw [show (∏ i, 1 / (Nat.totient (d i) : ℝ))
          = (∏ i, (Nat.totient (d i) : ℝ))⁻¹ by
        simp_rw [one_div]; rw [Finset.prod_inv_distrib]]
    rw [div_eq_mul_inv]
  -- `D/φ(D) ≥ 0`.
  have hprodd_nn : (0 : ℝ) ≤ ∏ i, (d i : ℝ) := Finset.prod_nonneg (fun i _ => by positivity)
  have hClogR_nn : (0 : ℝ) ≤ (C₁ * Real.log R) ^ k := by
    apply pow_nonneg; positivity
  calc |lam k R W y d|
      ≤ (∏ i, (d i : ℝ)) * |wSum k R W y d| := hlam
    _ ≤ (∏ i, (d i : ℝ)) *
          ((∏ i, 1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) ^ k) :=
        mul_le_mul_of_nonneg_left hwsum hprodd_nn
    _ = ((D : ℝ) / (Nat.totient D : ℝ)) * (C₁ * Real.log R) ^ k := by
        rw [← mul_assoc, hDphi]
    _ ≤ (C₃ * (1 + Real.log R)) * (C₁ * Real.log R) ^ k :=
        mul_le_mul_of_nonneg_right (hC₃ hDsf hDR hR) hClogR_nn
    _ ≤ (C₃ * (1 + Real.log R)) * (C₁ ^ k * (1 + Real.log R) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ hlogR (by linarith) k
    _ = (C₃ * C₁ ^ k) * (1 + Real.log R) ^ (k + 1) := by ring

end Salt.Maynard
