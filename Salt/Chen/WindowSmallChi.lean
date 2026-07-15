/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WindowErrFold

/-!
# WBV7 — the χ-level interval-SW small-conductor inputs

Design: `docs/blueprints/flags.md`, the `2026-07-14 WBV5` entry ("THE ONE RESIDUAL").
This file discharges the two named slots that `Salt.Chen.general_BV_cutoff_closed` (WBV5)
still exposes — the window small-conductor cutoff-SW inputs:

* **`hSmallCut`** — `∑_{2≤f≤D0} (1/φf)·cutoffPrimEnergy α (blockPrimeInd N) X M T f ≤ Km·XM/L^{A+1}`
  (the small-conductor cutoff-energy input, at exponent `A+1`);
* the per-`e` **`hsmall`** — the same at the dilated scale `(⌊X/e⌋, M, ⌊T/e⌋)` with the
  `(4/φ(lcm e f))·(1+log D)` prefactor and a `1/e` on the target.

The cutoff twist does **not** factor into an `A(χ)·B(χ)` product, so the bilinear small
machinery does not route.  The discharge instead **transposes WBV3's per-`m` interval-SW
technique (`Salt.Chen.smallconductor_window_perd`) to the χ-level**: for a fixed primitive
`ψ mod f`, regroup `cutoffTwist` by fixed `m` (pulling `α m · ψ(m)` out, using
`ψ(mn) = ψ(m)ψ(n)`); each inner `n`-sum over the block primes of the clean interval
`(N, min M ⌊T/m⌋]` is exactly `bilinTwist (blockPrimeInd N) (min M ⌊T/m⌋) f ψ`, priced by the
LANDED `Salt.Chen.hβSW_of_prime_indicator` at the **sub-interval** (the upper bound of
`bilinTwist` is free — the interval-inheritance).  Summing over `m ≤ X` (`‖α‖ ≤ 1`), then over
the primitive ψ (`#prim ≤ φf`), then over `f ≤ D0` (the `D0`-absorption) with the SW-exponent
bookkeeping gives the target.

## What this file lands (all sorry-free, axiom-clean)

1. `cutoffTwist_le_sum_interval_twists` — the per-`m` regroup at a FIXED primitive `ψ`.
2. `interval_prime_twist_SW` — the per-`(m, ψ)` SW bound at the clean sub-interval.
3. `hSmallCut_discharge` — the summed form (the `hSmallCut` slot).
4. `hsmall_pere_discharge` — the per-`e` analog at the dilated `α`.
5. `general_BV_cutoff_unconditional` — `general_BV_cutoff_closed` with both slots fed: the
   fully-closed windowed BV at only the structural/operating-point thresholds.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The per-`m` regroup at a fixed primitive χ -/

open Classical in
/-- **Item 1 (FULL) — the χ-level per-`m` regroup.**  For a fixed character `ψ mod f`, the
windowed cutoff twist against the block prime indicator regroups by fixed `m`: pulling `α m`
out and using `ψ(mn) = ψ(m)ψ(n)`, each inner `n`-sum over `{n ≤ M : m·n ≤ T}` of the block
primes is exactly `bilinTwist (blockPrimeInd N) (min M ⌊T/m⌋) f ψ` (the clean sub-interval
`(N, min M ⌊T/m⌋]`).  With `‖ψ(m)‖ ≤ 1`, the triangle inequality gives the stated bound.  This
is the χ-level transpose of `smallconductor_window_perd`'s `hregroup`. -/
theorem cutoffTwist_le_sum_interval_twists (α : ℕ → ℂ) (N X M T f : ℕ)
    (ψ : DirichletCharacter ℂ f) :
    ‖cutoffTwist α (blockPrimeInd N) X M T f ψ‖
      ≤ ∑ m ∈ Finset.Icc 1 X,
          ‖α m‖ * ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖ := by
  classical
  -- regroup `cutoffTwist` by fixed `m` into `α m · ψ(m) · (inner block-prime twist)`.
  have hregroup : cutoffTwist α (blockPrimeInd N) X M T f ψ
      = ∑ m ∈ Finset.Icc 1 X,
          α m * ψ (m : ZMod f) * bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ := by
    unfold cutoffTwist
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    have hm0 : 0 < m := hm.1
    -- the filtered `Icc` collapses to `Icc 1 (min M ⌊T/m⌋)`.
    have hset : (Finset.Icc 1 M).filter (fun n => m * n ≤ T)
        = Finset.Icc 1 (min M (T / m)) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
      constructor
      · rintro ⟨⟨h1, hM⟩, hmn⟩
        exact ⟨h1, hM, (Nat.le_div_iff_mul_le hm0).mpr (by rw [Nat.mul_comm]; exact hmn)⟩
      · rintro ⟨h1, hM, hTm⟩
        exact ⟨⟨h1, hM⟩, by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hm0).mp hTm⟩
    rw [hset]
    unfold bilinTwist
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Nat.cast_mul, map_mul]
    ring
  rw [hregroup]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun m _ => ?_))
  rw [norm_mul, norm_mul]
  calc ‖α m‖ * ‖ψ (m : ZMod f)‖ * ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖
      ≤ ‖α m‖ * 1 * ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖ := by
        gcongr
        exact DirichletCharacter.norm_le_one ψ _
    _ = ‖α m‖ * ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖ := by ring

/-! ## 2. The per-`(m, ψ)` interval-SW bound -/

open Classical in
/-- **Item 2 (FULL) — the clean-interval χ-twisted prime SW bound.**  Each interval prime twist
`bilinTwist (blockPrimeInd N) (min M ⌊T/m⌋) f ψ` (`ψ ≠ 1`, conductor `f ≤ (log N)^C`) obeys the
LANDED `hβSW_of_prime_indicator` bound at the sub-interval `(N, min M ⌊T/m⌋]`.  The `bilinTwist`
upper bound is a free parameter, so the landed per-`χ` SW form applies verbatim at the
sub-interval (interval-inheritance); the degenerate case `min M ⌊T/m⌋ ≤ N` has an empty block, so
the twist vanishes. -/
theorem interval_prime_twist_SW {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (N M T m f : ℕ) (ψ : DirichletCharacter ℂ f),
        N₀ ≤ N → M ≤ 2 * N → 2 ≤ f → ((f : ℝ) ≤ (Real.log N) ^ C) → ψ ≠ 1 →
        ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖
          ≤ (f : ℝ) * (K * N / (Real.log N) ^ A) := by
  obtain ⟨K, N₀, hK0, hb⟩ := hβSW_of_prime_indicator hA hC
  refine ⟨K, max N₀ 2, hK0, fun N M T m f ψ hN hM2N hf2 hflog hψ => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  set U := min M (T / m) with hUdef
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hbnn : (0 : ℝ) ≤ (f : ℝ) * (K * N / (Real.log N) ^ A) := by positivity
  by_cases hNU : N < U
  · -- non-degenerate: apply the landed sub-interval SW bound with upper bound `U`.
    have hU2N : U ≤ 2 * N := le_trans (min_le_left _ _) hM2N
    exact hb N U f ψ hN0 (le_of_lt hNU) hU2N hf2 hflog hψ
  · -- degenerate `U ≤ N`: the block `(N, U]` is empty, so `bilinTwist = 0`.
    have hUN : U ≤ N := not_lt.mp hNU
    have hzero : bilinTwist (blockPrimeInd N) U f ψ = 0 := by
      unfold bilinTwist
      refine Finset.sum_eq_zero (fun n hn => ?_)
      rw [Finset.mem_Icc] at hn
      have hnN : ¬ N < n := by omega
      unfold blockPrimeInd
      rw [if_neg (fun h => hnN h.1), zero_mul]
    rw [hzero, norm_zero]
    exact hbnn

/-! ## 3. The summed `hSmallCut` discharge -/

open Classical in
/-- **The per-primitive-`ψ` cutoff-twist bound (shared by items 3 and 4).**  Feeding the per-`m`
regroup (item 1) into the interval SW bound (item 2, packaged as `hint`), for any `‖α‖ ≤ 1` and
`ψ ≠ 1` the primitive twist obeys `‖cutoffTwist‖ ≤ X·(f·K·N/(log N)^A)`.  Parametric in the α/X/T
triple, so it applies verbatim at both the plain (`α, X, T`) and dilated (`α∘(e·), ⌊X/e⌋, ⌊T/e⌋`)
scales. -/
private lemma cutoffTwist_prim_le {K A C : ℝ} {N₀ : ℕ}
    (hint : ∀ (N M T m f : ℕ) (ψ : DirichletCharacter ℂ f),
        N₀ ≤ N → M ≤ 2 * N → 2 ≤ f → ((f : ℝ) ≤ (Real.log N) ^ C) → ψ ≠ 1 →
        ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖
          ≤ (f : ℝ) * (K * N / (Real.log N) ^ A))
    (α : ℕ → ℂ) (N X M T f : ℕ) (ψ : DirichletCharacter ℂ f)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hN : N₀ ≤ N) (hM2N : M ≤ 2 * N) (hf2 : 2 ≤ f)
    (hflog : (f : ℝ) ≤ (Real.log N) ^ C) (hψ1 : ψ ≠ 1) :
    ‖cutoffTwist α (blockPrimeInd N) X M T f ψ‖
      ≤ (X : ℝ) * ((f : ℝ) * (K * N / (Real.log N) ^ A)) := by
  refine le_trans (cutoffTwist_le_sum_interval_twists α N X M T f ψ) ?_
  calc ∑ m ∈ Finset.Icc 1 X, ‖α m‖ * ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖
      ≤ ∑ _m ∈ Finset.Icc 1 X, ((f : ℝ) * (K * N / (Real.log N) ^ A)) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        calc ‖α m‖ * ‖bilinTwist (blockPrimeInd N) (min M (T / m)) f ψ‖
            ≤ 1 * ((f : ℝ) * (K * N / (Real.log N) ^ A)) :=
              mul_le_mul (hα m) (hint N M T m f ψ hN hM2N hf2 hflog hψ1) (norm_nonneg _)
                (by norm_num)
          _ = (f : ℝ) * (K * N / (Real.log N) ^ A) := one_mul _
    _ = (X : ℝ) * ((f : ℝ) * (K * N / (Real.log N) ^ A)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

open Classical in
/-- **Item 3 (FLOOR B, FULL) — the summed `hSmallCut` discharge.**  The χ-level transpose of
`smallconductor_window_sum`: for each conductor `2 ≤ f ≤ D0`, `(1/φf)·cutoffPrimEnergy ≤ X·E` with
`E = f·K·N/(log N)^{A+2C0}` (the primitive-count `#χ ≤ φf` collapse), then `f ≤ L^{C0}` and the SW
bookkeeping `K·L^{A+1+2C0} ≤ Kβ·(log N)^{A+2C0}` (with `N ≤ M`) give `≤ Kβ·XM/L^{A+1+C0}`; summing
over the `≤ D0 ≤ L^{C0}` conductors (the `D0`-absorption) lands `Kβ·XM/L^{A+1}` — exactly the
`hSmallCut` slot of `general_BV_cutoff_closed`. -/
theorem hSmallCut_discharge {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 : ℕ) (Kβ : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → N₀ ≤ N → M ≤ 2 * N →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0)
            ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        ∑ f ∈ Finset.Icc 2 D0,
            (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
          ≤ Kβ * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1) := by
  obtain ⟨K, N₀, hK0, hint⟩ :=
    interval_prime_twist_SW (A := A + 2 * C0) (C := C0) (by linarith) hC0
  refine ⟨K, max N₀ 3, hK0, fun α X N M T D0 Kβ hα hKβ hN hM2N hLpos hD0 hD0N hNM hscale => ?_⟩
  classical
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLApos : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
  have hLAC0pos : (0 : ℝ) < L ^ (A + 1 + C0) := Real.rpow_pos_of_pos hLpos _
  have hlogNpos : (0 : ℝ) < (Real.log N) ^ (A + 2 * C0) := Real.rpow_pos_of_pos hlogN _
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hLcomb : L ^ C0 * L ^ (A + 1 + C0) = L ^ (A + 1 + 2 * C0) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  -- per-`f` bound in the target shape `Kβ·XM/L^{A+1+C0}`.
  have hperf : ∀ f ∈ Finset.Icc 2 D0,
      (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
        ≤ Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1 + C0) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf2 : 2 ≤ f := hf.1
    have hfD0 : f ≤ D0 := hf.2
    haveI : NeZero f := ⟨by omega⟩
    have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hflogN : (f : ℝ) ≤ (Real.log N) ^ C0 := le_trans (by exact_mod_cast hfD0) hD0N
    have hfL : (f : ℝ) ≤ L ^ C0 := le_trans (by exact_mod_cast hfD0) hD0
    set E : ℝ := (f : ℝ) * (K * N / (Real.log N) ^ (A + 2 * C0)) with hEdef
    have hE0 : 0 ≤ E := by rw [hEdef]; positivity
    -- per-primitive-ψ bound.
    have hpsi : ∀ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive),
        ‖cutoffTwist α (blockPrimeInd N) X M T f ψ‖ ≤ (X : ℝ) * E := by
      intro ψ hψ
      rw [Finset.mem_filter] at hψ
      have hψprim := hψ.2
      have hψ1 : ψ ≠ 1 := by
        intro h
        rw [DirichletCharacter.isPrimitive_def] at hψprim
        rw [h, DirichletCharacter.conductor_one] at hψprim
        omega
      exact cutoffTwist_prim_le hint α N X M T f ψ hα hNN₀ hM2N hf2 hflogN hψ1
    -- collapse (1/φf)·cutoffPrimEnergy ≤ X·E.
    have hcard : ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card : ℝ)
        ≤ (f.totient : ℝ) := by
      have h1 : (Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card
          ≤ (Finset.univ : Finset (DirichletCharacter ℂ f)).card := Finset.card_filter_le _ _
      have h2 : (Finset.univ : Finset (DirichletCharacter ℂ f)).card = f.totient := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ f]
      rw [h2] at h1; exact_mod_cast h1
    have hcollapse : (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
        ≤ (X : ℝ) * E := by
      have hsum : cutoffPrimEnergy α (blockPrimeInd N) X M T f
          ≤ ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card : ℝ)
              * ((X : ℝ) * E) := by
        rw [cutoffPrimEnergy, ← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum hpsi
      calc (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
          ≤ (1 / (f.totient : ℝ))
              * (((Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card : ℝ)
                  * ((X : ℝ) * E)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ (1 / (f.totient : ℝ)) * ((f.totient : ℝ) * ((X : ℝ) * E)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (X : ℝ) * E := by field_simp
    refine le_trans hcollapse ?_
    -- X·E ≤ Kβ·XM/L^{A+1+C0}.
    have hEle : E ≤ Kβ * (M : ℝ) / L ^ (A + 1 + C0) := by
      have hE_le1 : E ≤ L ^ C0 * (K * N / (Real.log N) ^ (A + 2 * C0)) := by
        rw [hEdef]; exact mul_le_mul_of_nonneg_right hfL (by positivity)
      refine le_trans hE_le1 ?_
      rw [← mul_div_assoc, div_le_div_iff₀ hlogNpos hLAC0pos]
      calc L ^ C0 * (K * N) * L ^ (A + 1 + C0)
          = (N : ℝ) * (K * (L ^ C0 * L ^ (A + 1 + C0))) := by ring
        _ = (N : ℝ) * (K * L ^ (A + 1 + 2 * C0)) := by rw [hLcomb]
        _ ≤ (N : ℝ) * (Kβ * (Real.log N) ^ (A + 2 * C0)) :=
            mul_le_mul_of_nonneg_left hscale (by positivity)
        _ ≤ (M : ℝ) * (Kβ * (Real.log N) ^ (A + 2 * C0)) :=
            mul_le_mul_of_nonneg_right hNM (by positivity)
        _ = Kβ * (M : ℝ) * (Real.log N) ^ (A + 2 * C0) := by ring
    calc (X : ℝ) * E ≤ (X : ℝ) * (Kβ * (M : ℝ) / L ^ (A + 1 + C0)) :=
          mul_le_mul_of_nonneg_left hEle hXnn
      _ = Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1 + C0) := by rw [mul_div_assoc]; ring
  -- sum over the `≤ D0 ≤ L^{C0}` conductors.
  have hcardD0 : ((Finset.Icc 2 D0).card : ℝ) ≤ (D0 : ℝ) := by
    rw [Nat.card_Icc]; exact_mod_cast (by omega : D0 + 1 - 2 ≤ D0)
  have hVsmall0 : (0 : ℝ) ≤ Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1 + C0) := by positivity
  calc ∑ f ∈ Finset.Icc 2 D0,
          (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
      ≤ ∑ _f ∈ Finset.Icc 2 D0, Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1 + C0) :=
        Finset.sum_le_sum hperf
    _ = ((Finset.Icc 2 D0).card : ℝ) * (Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1 + C0)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D0 : ℝ) * (Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1 + C0)) :=
        mul_le_mul_of_nonneg_right hcardD0 hVsmall0
    _ ≤ L ^ C0 * (Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1 + C0)) :=
        mul_le_mul_of_nonneg_right hD0 hVsmall0
    _ = Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1) := by
        rw [Real.rpow_add hLpos (A + 1) C0]
        field_simp

/-! ## 4. The per-`e` `hsmall` discharge (dilated scale) -/

open Classical in
/-- **Item 4 (FULL) — the per-`e` `hsmall` discharge at the dilated scale.**  The χ-level
transpose of `efold_small_discharge` (which discharges the bilinear `hsmall` via
`efold_small_le`): fold `4/φ(lcm e f) ≤ 4/φf` into the `4(1+log D)` prefactor (`hstep1`), then
`hSmallCut_discharge` (item 3, at the raised exponent `A+1` and the **dilated** scale
`(⌊X/e⌋, M, ⌊T/e⌋)`) contracts the block energy to `Kβ·(⌊X/e⌋·M)/LE^{A+2}`; the identical scale
conversion (`⌊X/e⌋·M ≤ XM/e`, `1+log D ≤ 2·log(XM)`, `log(⌊X/e⌋M) ≥ (1/2)log(XM)`) delivers the
target with `Ksmall = 2^{A+5}·Kβ`.  Feeds `cutoffEfold_alpha_le`'s `hsmall` slot. -/
theorem hsmall_pere_discharge {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (N X M T D0 D e : ℕ) (Kβ : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → N₀ ≤ N → M ≤ 2 * N → 1 ≤ e → 1 ≤ D →
        (0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (Real.log ((X : ℝ) * (M : ℝ))
            ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
            ≤ Kβ * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ f ∈ Finset.Icc 2 D0,
            ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
              * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M (T / e) f
          ≤ ((2 : ℝ) ^ (A + 5) * Kβ)
              * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
  obtain ⟨K, N₀, hK0, hbody⟩ := hSmallCut_discharge (A := A + 1) (C0 := C0) (by linarith) hC0
  refine ⟨K, N₀, hK0, fun α N X M T D0 D e Kβ hα hKβ hN hM2N he1 hD1 hLEpos hD0E hD0N hNM
    hL1 hDXM hscale hbook => ?_⟩
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  set LE := Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) with hLEdef
  have hLpos : 0 < L := by linarith
  set xe : ℝ := ((X / e : ℕ) : ℝ) with hxe
  set E : ℕ → ℝ := fun f =>
    cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M (T / e) f with hEdef
  have h1logD : (0 : ℝ) ≤ 1 + Real.log D :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD1)]
  -- Step 1: fold `4/φ(lcm(e,f)) ≤ 4/φf` into the `4(1+log D)` prefactor.
  have hstep1 : ∑ f ∈ Finset.Icc 2 D0,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
      ≤ 4 * (1 + Real.log D) * ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * E f := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun f hf => ?_)
    rw [Finset.mem_Icc] at hf
    have hφf : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hlcmpos : 0 < Nat.lcm e f := by
      have : Nat.lcm e f ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
      omega
    have hφle : (f.totient : ℝ) ≤ ((Nat.lcm e f).totient : ℝ) := by
      have h : f.totient ∣ (Nat.lcm e f).totient :=
        Nat.totient_dvd_of_dvd (Nat.dvd_lcm_right e f)
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hlcmpos) h
    have hdiv : (4 : ℝ) / ((Nat.lcm e f).totient : ℝ) ≤ 4 / (f.totient : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hφf hφle
    have hEf : 0 ≤ E f := cutoffPrimEnergy_nonneg _ _ _ _ _ _
    calc ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
        ≤ ((4 / (f.totient : ℝ)) * (1 + Real.log D)) * E f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiv h1logD) hEf
      _ = 4 * (1 + Real.log D) * ((1 / (f.totient : ℝ)) * E f) := by ring
  -- Step 2: item 3 (`hSmallCut_discharge`) at exponent `A+1`, dilated scale.
  have hstep2 : ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * E f
      ≤ Kβ * (xe * (M : ℝ)) / LE ^ (A + 2) := by
    have h := hbody (fun m' => α (e * m')) (X / e) N M (T / e) D0 Kβ
      (norm_dilate_le hα e) hKβ hN hM2N hLEpos hD0E hD0N hNM hbook
    rw [show (A : ℝ) + 1 + 1 = A + 2 from by ring] at h
    exact h
  have h4logD : (0 : ℝ) ≤ 4 * (1 + Real.log D) := by positivity
  have hcombine : ∑ f ∈ Finset.Icc 2 D0,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
      ≤ 4 * (1 + Real.log D) * (Kβ * (xe * (M : ℝ)) / LE ^ (A + 2)) :=
    le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 h4logD)
  refine le_trans hcombine ?_
  -- Step 3: the scale conversion (verbatim `efold_small_discharge`).
  have hLEpow : (0 : ℝ) < LE ^ (A + 2) := Real.rpow_pos_of_pos hLEpos (A + 2)
  have hLpow1 : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos (A + 1)
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hxeM : xe * (M : ℝ) ≤ (X : ℝ) * (M : ℝ) / (e : ℝ) := by
    have h1 : xe ≤ (X : ℝ) / (e : ℝ) := Nat.cast_div_le
    calc xe * (M : ℝ) ≤ ((X : ℝ) / (e : ℝ)) * (M : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hMnn
      _ = (X : ℝ) * (M : ℝ) / (e : ℝ) := by ring
  have hlogDL : Real.log D ≤ L :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < D)) hDXM
  have h1logD2L : 1 + Real.log D ≤ 2 * L := by linarith
  have hrp1 : L * L ^ (A + 1) = L ^ (A + 2) := by
    have hh := Real.rpow_add hLpos 1 (A + 1)
    rw [Real.rpow_one] at hh
    rw [← hh]; congr 1; ring
  have hrp2 : (L / 2) ^ (A + 2) = L ^ (A + 2) / (2 : ℝ) ^ (A + 2) :=
    Real.div_rpow hLpos.le (by norm_num) (A + 2)
  have hrp3 : (2 : ℝ) ^ (A + 5) = (2 : ℝ) ^ (A + 2) * 8 := by
    rw [show (A : ℝ) + 5 = (A + 2) + 3 by ring, Real.rpow_add (by norm_num), show (3:ℝ) =
      ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (A + 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hLElo : (L / 2) ^ (A + 2) ≤ LE ^ (A + 2) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hXMnn : (0 : ℝ) ≤ (X : ℝ) * (M : ℝ) := by positivity
  have hpowdiv : (2 : ℝ) ^ (A + 5) / (2 : ℝ) ^ (A + 2) = 8 := by
    rw [hrp3, mul_comm, mul_div_assoc, div_self h2pow.ne']; ring
  have hLHSeq : 4 * (1 + Real.log D) * (Kβ * (xe * (M : ℝ)) / LE ^ (A + 2))
      = (4 * (1 + Real.log D) * Kβ * (xe * (M : ℝ))) / LE ^ (A + 2) := by ring
  have hRHSeq : ((2 : ℝ) ^ (A + 5) * Kβ) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)) * (1 / (e : ℝ))
      = ((2 : ℝ) ^ (A + 5) * Kβ * ((X : ℝ) * (M : ℝ))) / (L ^ (A + 1) * (e : ℝ)) := by ring
  rw [hLHSeq, hRHSeq, div_le_div_iff₀ hLEpow (by positivity : (0:ℝ) < L ^ (A + 1) * (e : ℝ))]
  have hxeMe : (xe * (M : ℝ)) * (e : ℝ) ≤ (X : ℝ) * (M : ℝ) := by
    have := mul_le_mul_of_nonneg_right hxeM heR.le
    rwa [div_mul_cancel₀ _ heR.ne'] at this
  have key : (4 * (1 + Real.log D) * Kβ * (xe * (M : ℝ))) * (L ^ (A + 1) * (e : ℝ))
      ≤ 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2) := by
    calc (4 * (1 + Real.log D) * Kβ * (xe * (M : ℝ))) * (L ^ (A + 1) * (e : ℝ))
        = (4 * (1 + Real.log D)) * (Kβ * ((xe * (M : ℝ)) * (e : ℝ))) * L ^ (A + 1) := by ring
      _ ≤ (8 * L) * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hLpow1.le
          refine mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hxeMe hKβ)
            (mul_nonneg hKβ (by positivity)) (by positivity)
      _ = 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * (L * L ^ (A + 1)) := by ring
      _ = 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2) := by rw [hrp1]
  refine le_trans key ?_
  have hle : 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2)
      = ((2 : ℝ) ^ (A + 5) * Kβ * ((X : ℝ) * (M : ℝ))) * (L / 2) ^ (A + 2) := by
    rw [hrp2]
    rw [show ((2 : ℝ) ^ (A + 5) * Kβ * ((X : ℝ) * (M : ℝ))) * (L ^ (A + 2) / (2 : ℝ) ^ (A + 2))
          = ((2 : ℝ) ^ (A + 5) / (2 : ℝ) ^ (A + 2)) * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2)
        by ring, hpowdiv]
  rw [hle]
  exact mul_le_mul_of_nonneg_left hLElo
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKβ) hXMnn)

/-! ## 5. `general_BV_cutoff_unconditional` — the fully-closed windowed BV

`general_BV_cutoff_closed` (WBV5) with **both** residual slots discharged by this wave:

* the `hSmallCut` slot by `hSmallCut_discharge` (item 3);
* the per-`e` envelope (`hGlue`/`hGsum`) by `cutoffEfold_alpha_le` fed with `hsmall_pere_discharge`
  (item 4), summed at the harmonic `1/e` (`sum_inv_Icc_le_log`).

**The terminal threshold list** (the catch-#54 resolution's final inputs; everything below is
structural / operating-point — no analytic slot remains).  `K := K₃ + K₄ + Kg` is the exposed
constant (`K₃`/`K₄`/`Kg` the item-3 / item-4 / `general_BV_cutoff_closed` existential constants).

* **Coefficient / block:** `‖α‖ ≤ 1`; `0 ≤ Kβ, Km, Kβ'`; `N₀ ≤ N`; `M ≤ 2N`; `D0 ≤ N`;
  `N ≤ M`; `Dset ⊆ [1,D]`, all coprime to `2`; `D < N`; `1 ≤ D`; `2 ≤ X, M`.
* **Scale / dyadic:** `1 ≤ L := log(XM)`; `D0 ≤ L^{C0}`, `D0 ≤ (log N)^{C0}` (`hD0N'`, the SW
  small-conductor range — exponent `C0`), `L^{A+2} ≤ 2·2^{k0}` (`hD0lo_main`, the T4-tail cut —
  exponent `A+2`, DECOUPLED from `C0`; coupling both rows at `C0` empties the `D0`-window at
  every boundary box: catch #64, `GlueFinal.catch64_op_boundary_infeasible`),
  `D0 = 2^{k0}`, `2 ≤ D0 ≤ D`; `A+2 ≤ B, C0`; `Klog = ⌊log₂ D⌋`; the level cut
  `D ≤ √(XM)/L^B`; `L^{A+3} ≤ √X, √M`; `D ≤ XM`.
* **Error-side (the `e`-fold):** `D·L^{A+5} ≤ √(XM)`, `L^{A+4} ≤ D0`, `L^{A+5} ≤ √M`, and per `e`:
  `#div(e)·L^{A+5} ≤ √X`, and — GUARDED to the live range `e ≤ X` (catch #69, node PRICE-0):
  `0 < log(⌊X/e⌋M)`, `D0 ≤ log(⌊X/e⌋M)^{C0}`, `L ≤ 2·log(⌊X/e⌋M)`.  Past the top (`e > X`,
  where `⌊X/e⌋ = 0` and these would demand `0 < 0`) the summand they bound is instead handled
  by `cutoffEfoldTerm_eq_zero_of_gt` (the `e`-fold term vanishes on the empty `⌊X/e⌋`-range).
* **SW couplings:** `K·L^{A+C0} ≤ Kβ·(log N)^{A+2C0}` (the shell),
  `K·L^{A+1+2C0} ≤ Km·(log N)^{A+2C0}` (the small-conductor `hSmallCut`), and per `e`
  `K·log(⌊X/e⌋M)^{A+1+1+2C0} ≤ Kβ'·(log N)^{A+1+2C0}` (the dilated per-`e` small core).

`Kerr = 2^{A+5}·Kβ' + 15360`; the target envelope is
`(Kβ + (6(Km+448+32√26) + Kerr))·XM/L^A`. -/
open Classical in
/-- **Item 5 (FULL) — `general_BV_cutoff_unconditional`.**  `general_BV_cutoff_closed` with the
two named cutoff-SW slots fed by `hSmallCut_discharge` (item 3) and `hsmall_pere_discharge`
(item 4, via `cutoffEfold_alpha_le` + the `1/e` harmonic envelope): the windowed `L¹`-over-`d`
AP discrepancy at residue `2` is bounded with **no analytic slot remaining** — only the
structural / operating-point thresholds and the three SW couplings (see the section header). -/
theorem general_BV_cutoff_unconditional {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (Kβ Km Kβ' B : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < N → 2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        -- error-side (`e`-fold) thresholds
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D →
            (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        -- SW couplings (in the exposed `K`)
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0) ≤ Km * (Real.log N) ^ (A + 2 * C0)) →
        (∀ e, 2 ≤ e → e ≤ D →
            K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
              ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ (A + 5) * Kβ' + 15360))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K₃, N₀₃, hK3pos, hbody3⟩ := hSmallCut_discharge (A := A) (C0 := C0) hA hC0
  obtain ⟨K₄, N₀₄, hK4pos, hbody4⟩ := hsmall_pere_discharge (A := A) (C0 := C0) hA hC0
  obtain ⟨Kg, N₀g, hKgpos, hbodyg⟩ := general_BV_cutoff_closed (A := A) (C0 := C0) hA hC0
  refine ⟨K₃ + K₄ + Kg, max (max N₀₃ N₀₄) N₀g, by positivity,
    fun α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hα hKβ hKm hKβ' hN hM2N hD0N hDge1 hcop2 hL1
      hD0 hD0N' hNM hD1 hDsetD hDN hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKlog hDscale hD0lo_main
      hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev herr_div herr_LEpos herr_D0E hDXM herr_scale
      hcoupG hcoup3 herr_book4 => ?_⟩
  set K := K₃ + K₄ + Kg with hKdef
  have hK3leK : K₃ ≤ K := by rw [hKdef]; linarith [hK4pos, hKgpos]
  have hK4leK : K₄ ≤ K := by rw [hKdef]; linarith [hK3pos, hKgpos]
  have hKgleK : Kg ≤ K := by rw [hKdef]; linarith [hK3pos, hK4pos]
  have hN₃ : N₀₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₄ : N₀₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNg : N₀g ≤ N := le_trans (le_max_right _ _) hN
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  have hLpos : (0 : ℝ) < L := by linarith
  have hXpos : 0 < X := by omega
  have hMpos : 0 < M := by omega
  have hLnn : (0 : ℝ) ≤ L := hLpos.le
  -- the item-4 output constant and the assembled envelope constant.
  set Ksm : ℝ := (2 : ℝ) ^ (A + 5) * Kβ' with hKsmdef
  set G : ℕ → ℝ := fun e => (Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)) * (1 / (e : ℝ))
    with hGdef
  -- Slot 29: `hSmallCut` via item 3.
  have hSmallCut : ∑ f ∈ Finset.Icc 2 D0,
        (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
      ≤ Km * ((X : ℝ) * (M : ℝ)) / L ^ (A + 1) :=
    hbody3 α X N M T D0 Km hα hKm hN₃ hM2N hLpos hD0 hD0N' hNM
      (le_trans (mul_le_mul_of_nonneg_right hK3leK (Real.rpow_nonneg hLnn _)) hcoup3)
  -- Slot 30: the per-`e` envelope via item 4 + `cutoffEfold_alpha_le`.
  have hGlue : ∀ e, 2 ≤ e → e ≤ D → cutoffEfoldTerm α N X M T D0 Dset e ≤ G e := by
    intro e he2 heD
    by_cases hleX : e ≤ X
    · -- `e ≤ X` (the live range): the guarded per-`e` rows apply verbatim.
      have hLE0 : (0 : ℝ) ≤ Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) :=
        (herr_LEpos e he2 heD hleX).le
      -- the dilated per-`e` small core (item 4), fed with the `K₄ ≤ K` coupling.
      have hbook4e : K₄ * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
          ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0) :=
        le_trans (mul_le_mul_of_nonneg_right hK4leK (Real.rpow_nonneg hLE0 _))
          (herr_book4 e he2 heD)
      have hsmall := hbody4 α N X M T D0 D e Kβ' hα hKβ' hN₄ hM2N (by omega) hD1
        (herr_LEpos e he2 heD hleX) (herr_D0E e he2 heD hleX) hD0N' hNM hL1 hDXM
        (herr_scale e he2 heD hleX) hbook4e
      -- feed into `cutoffEfold_alpha_le` (`Ksmall = Ksm = 2^{A+5}·Kβ'`).
      exact cutoffEfold_alpha_le α N X M T D0 D e k0 Klog Dset (A := A) (Ksmall := Ksm)
        hα he2 heD hD1 hDge1 hDsetD h2D0 hD0D hD0eq hKlog hMpos hXpos hA.le hL1 herr_lev herr_D0lo
        herr_Mlev (herr_div e he2 heD) hsmall
    · -- `e > X` (past the top): the `e`-fold term vanishes (`⌊X/e⌋ = 0`), and `G e ≥ 0`.
      have hgtX : X < e := by omega
      rw [cutoffEfoldTerm_eq_zero_of_gt α N X M T D0 Dset hgtX, hGdef]
      have hLA : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
      have hKsmnn : (0 : ℝ) ≤ Ksm := by rw [hKsmdef]; positivity
      have hmid : (0 : ℝ) ≤ (X : ℝ) * (M : ℝ) / L ^ (A + 1) := div_nonneg (by positivity) hLA.le
      exact mul_nonneg (mul_nonneg (by linarith) hmid) (by positivity)
  -- Slot 31: the harmonic sum `∑ G e ≤ Kerr·XM/L^A`.
  have hC0nn : (0 : ℝ) ≤ (Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)) := by
    have : (0 : ℝ) ≤ Ksm := by rw [hKsmdef]; positivity
    have hLA : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
    positivity
  have hlogDL : Real.log D ≤ L :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < D)) hDXM
  have hGsum : ∑ e ∈ Finset.Icc 2 D, G e
      ≤ ((2 : ℝ) ^ (A + 5) * Kβ' + 15360) * ((X : ℝ) * (M : ℝ)) / L ^ A := by
    calc ∑ e ∈ Finset.Icc 2 D, G e
        = ((Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)))
            * ∑ e ∈ Finset.Icc 2 D, (1 / (e : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ ((Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1))) * Real.log D :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log hD1) hC0nn
      _ ≤ ((Ksm + 15360) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1))) * L :=
          mul_le_mul_of_nonneg_left hlogDL hC0nn
      _ = ((2 : ℝ) ^ (A + 5) * Kβ' + 15360) * ((X : ℝ) * (M : ℝ)) / L ^ A := by
          rw [hKsmdef, Real.rpow_add hLpos A 1, Real.rpow_one]
          field_simp
  -- assemble via `general_BV_cutoff_closed`.
  exact hbodyg α X N M T D0 D k0 Klog Dset r Kβ Km ((2 : ℝ) ^ (A + 5) * Kβ' + 15360) B G
    hα hKβ hKm hNg hM2N hD0N hDge1 hcop2 hLpos hD0 hD0N' hNM
    (le_trans (mul_le_mul_of_nonneg_right hKgleK (Real.rpow_nonneg hLnn _)) hcoupG)
    hD1 hDsetD hDN hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKlog hDscale hD0lo_main hXsqrt hMsqrt
    hSmallCut hGlue hGsum

/-! ## Composition sanity -/

section CompositionSanity

#check @Salt.Chen.cutoffTwist_le_sum_interval_twists
#check @Salt.Chen.interval_prime_twist_SW
#check @Salt.Chen.hSmallCut_discharge
#check @Salt.Chen.hsmall_pere_discharge
#check @Salt.Chen.general_BV_cutoff_unconditional
#check @Salt.Chen.hHD_of_generalBV_window

end CompositionSanity

end Salt.Chen
