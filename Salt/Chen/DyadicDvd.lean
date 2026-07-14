/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.EnergyShellDvd

/-!
# Large sieve track, node PE3c-3 (Chen side): the δ-restricted dyadic engine

Design: `docs/blueprints/flags.md`, entries `2026-07-13 PE3c RECON` / `PE3c-1` / `PE3c-2`.
This file is the exact `δ`-copy of the landed dyadic chain of `Salt/Chen/EnergyClose.lean`
(`block_energy_le'`, `dyadic_large_reduction`, `geom_shell_sum_le`, `dyadic_term_bound`),
built on `Salt.Chen.energy_shell_dvd` (`Salt/Chen/EnergyShellDvd.lean`) in place of
`energy_shell`.  The copies change ONLY the modulus filter `δ ∣ f` and the sharpened
diagonal `Q²/δ` (via `shellBoundDvd` in place of `shellBound`); the block/weight structure
and every proof step are otherwise byte-identical to the un-restricted chain.

The chain (mirroring `Salt/Chen/EnergyClose.lean` §2):

* `dyadic_term_bound_dvd` — the elementary per-block √-split with the `Q²/δ` diagonal:
  `(1/F)·√((2F)²/δ + a)·√((2F)²/δ + b) ≤ 4F/δ + 2√a/√δ + 2√b/√δ + √a√b/F`.  The `√((2F)²/δ)
  = 2F/√δ` refinement is the ONLY change from the landed `dyadic_term_bound` (the main term
  gains `1/δ`, the cross terms gain `1/√δ`, the diagonal `√a√b/F` tail is unchanged).
* `block_energy_le_dvd` — the per-dyadic-block bound with the `δ ∣ f` filter and the
  `shellBoundDvd`-diagonal (mirror of `block_energy_le'`, the `Icc a b` form the reduction
  consumes; `energy_shell_dvd` in place of `energy_shell`).
* `dyadic_large_reduction_dvd` — the block decomposition of `∑_{D0<f≤D, δ∣f} (1/φf)·E(f)` into
  the dyadic blocks (the fibration `f ↦ ⌊log₂ f⌋`; only the filter threads through).
* `geom_shell_sum_le_dvd` — the geometric block-sum bound with the `Q²/δ` diagonals: the
  FOUR-TERM structure is kept explicit (main `4·2^{K+1}/δ`, cross `2(K+1)√(13(X+1))/√δ`, cross
  `2(K+1)√(13(Y+1))/√δ`, tail `√(13(X+1))√(13(Y+1))·2/2^{k0}`), exactly as the landed lemma —
  no fusion, so no `four_term_split_dvd` variant is needed.
* `dyadic_energy_le_dvd` — the RAW assembled form PE3c-4 consumes directly:
  `∑_{D0<f≤D, δ∣f} (1/φf)·bilinPrimEnergy α β X Y f ≤ [explicit four-term expression]`
  (mirror of `Salt.Chen.efold_large_fourterm`'s `dyadic_large_reduction + geom_shell_sum_le`
  composition, δ-restricted).  Per the item-4 catch-#44 lesson (the level cut
  `hDscale` dies at dilated/δ-shifted scales), the RAW form is provided in preference to a
  `four_term_scale_le_dvd` level-absorption analogue — PE3c-4 applies the level deficit to the
  explicit diagonal afterwards, per `δ` (exactly as PE3a's raw `efold_large_fourterm` is
  consumed by `efold_alpha_le`).

The `δ = 1` cases recover the landed `dyadic_large_reduction` / `geom_shell_sum_le` shapes
(`Nat.cast_one`, `div_one`, `Real.sqrt_one`, and `filter (1 ∣ ·) = id`); see the closing
`example`s.

Only `[propext, Classical.choice, Quot.sound]` are used (via `energy_shell_dvd`).

**Wiring.**  Add to `Salt/Chen/All.lean` next to the other bilinear-energy modules (after
`import Salt.Chen.EnergyShellDvd`).
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 0. The δ-restricted per-block √-split (mirror of `dyadic_term_bound`) -/

/-- **δ per-block √-split.**  `(1/F)·√((2F)²/δ + a)·√((2F)²/δ + b) ≤ 4F/δ + 2√a/√δ + 2√b/√δ
+ √a√b/F` for `F > 0`, `δ > 0`, `a, b ≥ 0` (via `√(P+q) ≤ √P+√q` and `√((2F)²/δ) = 2F/√δ`).
The `δ`-copy of `Salt.Chen.dyadic_term_bound`: the `Q²/δ` diagonal sharpens the main term to
`4F/δ` and the cross terms to `2√·/√δ`; the tail `√a√b/F` is unchanged. -/
lemma dyadic_term_bound_dvd {F a b δ : ℝ} (hF : 0 < F) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / F) * (Real.sqrt ((2 * F) ^ 2 / δ + a) * Real.sqrt ((2 * F) ^ 2 / δ + b))
      ≤ 4 * F / δ + 2 * Real.sqrt a / Real.sqrt δ + 2 * Real.sqrt b / Real.sqrt δ
          + Real.sqrt a * Real.sqrt b / F := by
  have hs0 : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsqrtF : Real.sqrt ((2 * F) ^ 2 / δ) = 2 * F / Real.sqrt δ := by
    rw [show (2 * F) ^ 2 / δ = (2 * F / Real.sqrt δ) ^ 2 by
          rw [div_pow, Real.sq_sqrt hδ.le], Real.sqrt_sq (by positivity)]
  have hsA : Real.sqrt ((2 * F) ^ 2 / δ + a) ≤ 2 * F / Real.sqrt δ + Real.sqrt a := by
    have h := sqrt_add_le_add_sqrt (by positivity : (0 : ℝ) ≤ (2 * F) ^ 2 / δ) ha
    rwa [hsqrtF] at h
  have hsB : Real.sqrt ((2 * F) ^ 2 / δ + b) ≤ 2 * F / Real.sqrt δ + Real.sqrt b := by
    have h := sqrt_add_le_add_sqrt (by positivity : (0 : ℝ) ≤ (2 * F) ^ 2 / δ) hb
    rwa [hsqrtF] at h
  have hprod : Real.sqrt ((2 * F) ^ 2 / δ + a) * Real.sqrt ((2 * F) ^ 2 / δ + b)
      ≤ (2 * F / Real.sqrt δ + Real.sqrt a) * (2 * F / Real.sqrt δ + Real.sqrt b) :=
    mul_le_mul hsA hsB (Real.sqrt_nonneg _) (by positivity)
  -- pure algebraic identity (√a, √b, s = √δ atoms), then `s·s = δ`.
  have key : ∀ s : ℝ, s ≠ 0 →
      (1 / F) * ((2 * F / s + Real.sqrt a) * (2 * F / s + Real.sqrt b))
        = 4 * F / (s * s) + 2 * Real.sqrt a / s + 2 * Real.sqrt b / s
            + Real.sqrt a * Real.sqrt b / F := by
    intro s hs
    field_simp
    ring
  calc (1 / F) * (Real.sqrt ((2 * F) ^ 2 / δ + a) * Real.sqrt ((2 * F) ^ 2 / δ + b))
      ≤ (1 / F) * ((2 * F / Real.sqrt δ + Real.sqrt a) * (2 * F / Real.sqrt δ + Real.sqrt b)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 4 * F / δ + 2 * Real.sqrt a / Real.sqrt δ + 2 * Real.sqrt b / Real.sqrt δ
          + Real.sqrt a * Real.sqrt b / F := by
        rw [key (Real.sqrt δ) hs0.ne', Real.mul_self_sqrt hδ.le]

/-! ## 1. The δ-restricted per-block consumption (mirror of `block_energy_le'`) -/

/-- **δ per-block consumption (mirror of `block_energy_le'`).**  On a block `[a, b]` (`1 ≤ a`,
`2 ≤ b`) restricted to conductors `δ ∣ f`, the `(1/φf)`-weight is `≤ (1/a)·(f/φf)`, so the
block energy is `≤ (1/a)·shellBoundDvd X Y b δ` (extend the filtered block to
`(Icc 1 b).filter (δ∣·)`, consume `energy_shell_dvd` at `Q = b`).  The `δ`-copy of
`block_energy_le'`; the dyadic reduction consumes this at `a = 2^k`, `b = 2^{k+1}`. -/
theorem block_energy_le_dvd {X Y a b δ : ℕ} (hδ1 : 1 ≤ δ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc a b).filter (fun f => δ ∣ f),
        (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (1 / (a : ℝ)) * shellBoundDvd X Y b δ := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hstep : ∀ f ∈ (Finset.Icc a b).filter (fun f => δ ∣ f),
      (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
        ≤ (1 / (a : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_Icc] at hf
    have hf1 : 1 ≤ f := by omega
    have haf : (a : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf.1.1
    have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hEnn : 0 ≤ bilinPrimEnergy α β X Y f := bilinPrimEnergy_nonneg _ _ _ _ _
    have hwle : (1 / (f.totient : ℝ)) ≤ (1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ)) := by
      have hrw : (1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ))
          = (f : ℝ) / ((a : ℝ) * (f.totient : ℝ)) := by field_simp
      rw [hrw, div_le_div_iff₀ hφpos (mul_pos haR hφpos)]
      nlinarith [haf, hφpos.le]
    calc (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
        ≤ ((1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ))) * bilinPrimEnergy α β X Y f :=
          mul_le_mul_of_nonneg_right hwle hEnn
      _ = (1 / (a : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- extend the filtered block `(Icc a b).filter (δ∣·)` to `(Icc 1 b).filter (δ∣·)`.
  have hsub : (Finset.Icc a b).filter (fun f => δ ∣ f)
      ⊆ (Finset.Icc 1 b).filter (fun f => δ ∣ f) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_Icc] at hf ⊢
    exact ⟨⟨by omega, hf.1.2⟩, hf.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => ?_)) ?_
  · exact mul_nonneg (by positivity) (bilinPrimEnergy_nonneg _ _ _ _ _)
  · exact energy_shell_dvd hδ1 hb hY α β hα hβ

/-! ## 2. The δ-restricted dyadic large-conductor reduction (mirror of
`dyadic_large_reduction`) -/

/-- **δ dyadic large-conductor reduction (mirror of `dyadic_large_reduction`).**  For
`D0 = 2^{k0}` and `K = ⌊log₂ D⌋`, the δ-restricted large-conductor energy
`∑_{D0 < f ≤ D, δ∣f} (1/φf)·E(f)` is bounded by the geometric block sum
`∑_{k=k0}^{K} (1/2^k)·shellBoundDvd X Y (2^{k+1}) δ` — the dyadic fibration `f ↦ ⌊log₂ f⌋`
(fibers land in `Icc k0 K`, each fiber sits in the `δ`-filtered block `[2^k, 2^{k+1}]`), only
the modulus filter threading through, consuming `block_energy_le_dvd`. -/
theorem dyadic_large_reduction_dvd {X Y D0 D δ k0 K : ℕ} (hδ1 : 1 ≤ δ) (hD0 : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => δ ∣ f),
        (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ ∑ k ∈ Finset.Icc k0 K, (1 / (2 ^ k : ℝ)) * shellBoundDvd X Y (2 ^ (k + 1)) δ := by
  have hmaps : ∀ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => δ ∣ f),
      Nat.log 2 f ∈ Finset.Icc k0 K := by
    intro f hf
    rw [Finset.mem_filter] at hf
    have hf' := hf.1
    rw [Finset.mem_Icc] at hf' ⊢
    refine ⟨?_, ?_⟩
    · apply Nat.le_log_of_pow_le (by norm_num)
      rw [← hD0]; omega
    · rw [hK]; exact Nat.log_mono_right hf'.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun f => (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f)]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [Finset.mem_Icc] at hk
  have hfibsub : ((Finset.Icc (D0 + 1) D).filter (fun f => δ ∣ f)).filter
        (fun f => Nat.log 2 f = k)
      ⊆ (Finset.Icc (2 ^ k) (2 ^ (k + 1))).filter (fun f => δ ∣ f) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hf
    obtain ⟨⟨⟨hf1, _⟩, hdvd⟩, hlog⟩ := hf
    have hf0 : f ≠ 0 := by omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hdvd⟩
    · have := Nat.pow_log_le_self 2 hf0; rwa [hlog] at this
    · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) f
      rw [hlog] at this; omega
  calc ∑ f ∈ ((Finset.Icc (D0 + 1) D).filter (fun f => δ ∣ f)).filter
          (fun f => Nat.log 2 f = k), (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ ∑ f ∈ (Finset.Icc (2 ^ k) (2 ^ (k + 1))).filter (fun f => δ ∣ f),
          (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hfibsub (fun f _ _ => ?_)
        exact mul_nonneg (by positivity) (bilinPrimEnergy_nonneg _ _ _ _ _)
    _ ≤ (1 / (2 ^ k : ℝ)) * shellBoundDvd X Y (2 ^ (k + 1)) δ := by
        have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have h2k1 : 2 ≤ 2 ^ (k + 1) := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
        have hbk := block_energy_le_dvd (X := X) (Y := Y) (a := 2 ^ k) (b := 2 ^ (k + 1))
          (δ := δ) hδ1 h2k h2k1 hY α β hα hβ
        rwa [hcast] at hbk

/-! ## 3. The δ-restricted dyadic geometric sum (mirror of `geom_shell_sum_le`) -/

/-- **δ dyadic geometric sum (mirror of `geom_shell_sum_le`).**  The geometric block sum
`∑_{k=k0}^{K} (1/2^k)·shellBoundDvd X Y (2^{k+1}) δ` is bounded by the explicit **four-term**
expression with the sharpened `Q²/δ` diagonals: `4·2^{K+1}/δ` (the `~D/δ` main term),
`2(K+1)√(13(X+1))/√δ`, `2(K+1)√(13(Y+1))/√δ` (the `~√X/√δ, √Y/√δ` cross terms), and
`√(13(X+1))√(13(Y+1))·2/2^{k0}` (the `~XY/D0` tail, `δ`-independent — the tail is the diagonal
`√a√b/F` term, which the `Q²/δ` refinement does not touch), all scaled by `2(1+log Y)√X√Y`.
The four terms are kept as an explicit sum (no fusion) so PE3c-4's fibered assembly sees them
separately. -/
theorem geom_shell_sum_le_dvd {X Y k0 K δ : ℕ} (hδ1 : 1 ≤ δ) (hY : 0 < Y) :
    ∑ k ∈ Finset.Icc k0 K, (1 / (2 ^ k : ℝ)) * shellBoundDvd X Y (2 ^ (k + 1)) δ
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ (K + 1) / (δ : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ)
            + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast (by omega : 0 < δ)
  have h1logY : (0 : ℝ) ≤ 1 + Real.log Y :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ Y by exact_mod_cast hY)]
  have hC : (0 : ℝ) ≤ 2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y := by positivity
  have hu : (0 : ℝ) ≤ Real.sqrt (13 * ((X : ℝ) + 1)) := Real.sqrt_nonneg _
  have hv : (0 : ℝ) ≤ Real.sqrt (13 * ((Y : ℝ) + 1)) := Real.sqrt_nonneg _
  -- Per-`k` bound via `dyadic_term_bound_dvd`.
  have hperk : ∀ k, (1 / (2 ^ k : ℝ)) * shellBoundDvd X Y (2 ^ (k + 1)) δ
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ k / (δ : ℝ)
              + 2 * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ)
              + 2 * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ)
              + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                  / (2 : ℝ) ^ k) := by
    intro k
    have hFk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hq : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ k := by push_cast; ring
    have hshell : shellBoundDvd X Y (2 ^ (k + 1)) δ
        = (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
            * (Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 / (δ : ℝ) + 13 * ((X : ℝ) + 1))
                * Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 / (δ : ℝ) + 13 * ((Y : ℝ) + 1))) := by
      unfold shellBoundDvd; rw [hq]; ring
    rw [hshell, mul_comm (1 / (2 ^ k : ℝ)) _, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hdt := dyadic_term_bound_dvd (F := (2 : ℝ) ^ k) (δ := (δ : ℝ))
      (a := 13 * ((X : ℝ) + 1)) (b := 13 * ((Y : ℝ) + 1)) hFk hδR (by positivity) (by positivity)
    rwa [mul_comm (Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 / (δ : ℝ) + 13 * ((X : ℝ) + 1))
          * Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 / (δ : ℝ) + 13 * ((Y : ℝ) + 1))) (1 / (2 : ℝ) ^ k)]
  refine le_trans (Finset.sum_le_sum (fun k _ => hperk k)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hC
  -- split the bracket sum into the four geometric/counting pieces.
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcard : (Finset.Icc k0 K).card ≤ K + 1 := by rw [Nat.card_Icc]; omega
  -- main term (with the `1/δ` diagonal).
  have hbase : ∑ k ∈ Finset.Icc k0 K, 4 * (2 : ℝ) ^ k ≤ 4 * (2 : ℝ) ^ (K + 1) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hsub : Finset.Icc k0 K ⊆ Finset.range (K + 1) := by
      intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    calc ∑ k ∈ Finset.Icc k0 K, (2 : ℝ) ^ k
        ≤ ∑ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
      _ = (2 : ℝ) ^ (K + 1) - 1 := by
          rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; ring
      _ ≤ (2 : ℝ) ^ (K + 1) := by linarith [show (0:ℝ) ≤ 1 from by norm_num]
  have hpow2 : ∑ k ∈ Finset.Icc k0 K, 4 * (2 : ℝ) ^ k / (δ : ℝ)
      ≤ 4 * (2 : ℝ) ^ (K + 1) / (δ : ℝ) := by
    rw [← Finset.sum_div, div_le_div_iff₀ hδR hδR]
    exact mul_le_mul_of_nonneg_right hbase hδR.le
  have hconstX : ∑ k ∈ Finset.Icc k0 K, 2 * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ)
      ≤ 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard' : ((Finset.Icc k0 K).card : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [show 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ)
          = ((K + 1 : ℕ) : ℝ) * (2 * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_right hcard' (by positivity)
  have hconstY : ∑ k ∈ Finset.Icc k0 K, 2 * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ)
      ≤ 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard' : ((Finset.Icc k0 K).card : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [show 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ)
          = ((K + 1 : ℕ) : ℝ) * (2 * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_right hcard' (by positivity)
  -- tail term (δ-independent — the diagonal `√a√b/F` piece; verbatim `geom_shell_sum_le`).
  have htail : ∑ k ∈ Finset.Icc k0 K,
        Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) / (2 : ℝ) ^ k
      ≤ Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0) := by
    have hfac : ∀ k, Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) / (2 : ℝ) ^ k
        = (Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)))
          * (1 / (2 : ℝ) ^ k) := by
      intro k; ring
    rw [Finset.sum_congr rfl (fun k _ => hfac k), ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hu hv)
    rw [show Finset.Icc k0 K = Finset.Ico k0 (K + 1) by
        ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    have hstep : ∀ j, (1 / (2 : ℝ) ^ (k0 + j)) = (1 / (2 : ℝ) ^ k0) * (1 / 2) ^ j := by
      intro j; rw [pow_add, div_pow, one_pow, div_mul_div_comm, one_mul]
    rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum]
    have hgeom : ∑ j ∈ Finset.range (K + 1 - k0), (1 / 2 : ℝ) ^ j ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (K + 1 - k0) := by positivity
      have heq : ((1 / 2 : ℝ) ^ (K + 1 - k0) - 1) / (1 / 2 - 1)
          = 2 - 2 * (1 / 2 : ℝ) ^ (K + 1 - k0) := by field_simp; ring
      rw [heq]; linarith [hpos]
    calc (1 / (2 : ℝ) ^ k0) * ∑ j ∈ Finset.range (K + 1 - k0), (1 / 2 : ℝ) ^ j
        ≤ (1 / (2 : ℝ) ^ k0) * 2 :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 2 / (2 : ℝ) ^ k0 := by ring
  linarith [hpow2, hconstX, hconstY, htail]

/-! ## 4. The raw assembled δ-dyadic energy bound (the shape PE3c-4 consumes) -/

/-- **PE3c-3 (FULL) — the raw δ-restricted dyadic energy bound.**  Composing
`dyadic_large_reduction_dvd` with `geom_shell_sum_le_dvd`: the δ-restricted large-conductor
block energy is bounded by the explicit **four-term** expression with the `Q²/δ` diagonal, at
the given scale `(X, Y)`, `D0 = 2^{k0}`, `K = ⌊log₂ D⌋`.  This is the exact analogue of
`Salt.Chen.efold_large_fourterm`'s `dyadic_large_reduction + geom_shell_sum_le` composition,
δ-restricted — the shape PE3c-4's `hlarge` assembly consumes directly (the level deficit
`D ≤ √(XY)/(log)^B` is applied to the explicit diagonal *afterwards*, per `δ`; per catch #44
no level cut is absorbed here).

The four-term shape (exactly the RHS below):
```
∑_{D0<f≤D, δ∣f} (1/φf)·bilinPrimEnergy α β X Y f
  ≤ 2(1+log Y)√X√Y · ( 4·2^{K+1}/δ                                    -- main  (~ D/δ)
                       + 2(K+1)·√(13(X+1))/√δ                          -- crossX (~ √X/√δ)
                       + 2(K+1)·√(13(Y+1))/√δ                          -- crossY (~ √Y/√δ)
                       + √(13(X+1))·√(13(Y+1))·2/2^{k0} ).             -- tail   (~ XY/D0)
```
-/
theorem dyadic_energy_le_dvd {X Y D0 D δ k0 K : ℕ} (hδ1 : 1 ≤ δ) (hD0 : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => δ ∣ f),
        (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ (K + 1) / (δ : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ)
            + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) :=
  le_trans (dyadic_large_reduction_dvd hδ1 hD0 hK hY α β hα hβ)
    (geom_shell_sum_le_dvd hδ1 hY)

/-! ## 5. `δ = 1` comparison examples (recovery of the landed chain) -/

/-- At `δ = 1`, `block_energy_le_dvd` recovers `block_energy_le'`'s shape (the filter is all of
`Icc a b`, and `shellBoundDvd _ _ _ 1 = shellBound`). -/
example {X Y a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc a b, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (1 / (a : ℝ)) * shellBound X Y b := by
  have h := block_energy_le_dvd (X := X) (Y := Y) (a := a) (b := b) (δ := 1)
    (le_refl 1) ha hb hY α β hα hβ
  rw [shellBoundDvd_one] at h
  have hf : (Finset.Icc a b).filter (fun f => (1 : ℕ) ∣ f) = Finset.Icc a b :=
    Finset.filter_true_of_mem (fun f _ => one_dvd f)
  rwa [hf] at h

/-- At `δ = 1`, `dyadic_energy_le_dvd` recovers the landed un-restricted four-term of
`Salt.Chen.efold_large_fourterm` / `geom_shell_sum_le` (the `Q²/1` diagonal collapses to `Q²`:
`/(1:ℝ)` and `/√(1:ℝ)` are identities, and `filter (1∣·) = id`). -/
example {X Y D0 D k0 K : ℕ} (hD0 : D0 = 2 ^ k0) (hK : K = Nat.log 2 D) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc (D0 + 1) D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ (K + 1)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1))
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
            + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) := by
  have h := dyadic_energy_le_dvd (X := X) (Y := Y) (D0 := D0) (D := D) (δ := 1) (k0 := k0) (K := K)
    (le_refl 1) hD0 hK hY α β hα hβ
  have hf : (Finset.Icc (D0 + 1) D).filter (fun f => (1 : ℕ) ∣ f) = Finset.Icc (D0 + 1) D :=
    Finset.filter_true_of_mem (fun f _ => one_dvd f)
  rw [hf] at h
  simpa only [Nat.cast_one, div_one, Real.sqrt_one] using h

end Salt.Chen
