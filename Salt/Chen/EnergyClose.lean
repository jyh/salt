/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.BilinearDescent

/-!
# C3c″ — discharging `hMainEnergy` + `hErrSum` (keystone 2's last two analytic cores)

Design: `docs/blueprints/chen.md`, the C3c row / the two named cores exposed by
`Salt.Chen.bilinear_hLargeDisc` (node C3c′).  `bilinear_hLargeDisc` reduced the
large-conductor bilinear character energy to two named hypotheses:

* **`hMainEnergy`** — the dyadic-in-conductor shell arithmetic on the FULL-`α`/`β`
  primitive block energy `∑_{f≤D} (1/φf)·bilinPrimEnergy α β X Y f`;
* **`hErrSum`** — the summed `α`-side coprimality `L¹` error.

## What this file lands (sorry-free)

1. **The `bilinPrimEnergy` shell** (`energy_shell`) — a restatement of
   `Salt.Chen.bilinTwist_energy_le` (`⇐ Salt.BV.bilinear_LS_shell`) in the
   `bilinPrimEnergy` form.  FULL.

2. **The per-block consumption** (`block_energy_le`, `block_energy_le'`) — the
   dyadic-block engine: on `[a, b]` the `(1/φf)`-weight is `≤ (1/a)·(f/φf)`, so the
   block energy is `≤ (1/a)·shellBound X Y b`.  The `1/F` per-block normalization the
   C3a flag prescribed.  FULL.

3. **The dyadic large-conductor reduction** (`dyadic_large_reduction`) — the fibration
   `f ↦ ⌊log₂ f⌋` bounds `∑_{D0<f≤D} (1/φf)·E` by the geometric sum
   `∑_{k=k0}^{K} (1/2^k)·shellBound(2^{k+1})`.  FULL.

4. **The dyadic geometric evaluation** (`dyadic_term_bound`, `geom_shell_sum_le`) —
   `√(4F²+13(X+1)) ≤ 2F+√(13(X+1))` + geometric/counting sums evaluate that to the
   classical `(D + √X + √Y + XY/D0)·√(XY)·log` four-term endgame.  FULL.

5. **The small-conductor SW consumption** (`smallConductor_energy_le`) — for
   `f ≤ D0 = (log XY)^{C0}`, the SW-regularity of `β` (named `hβSW`, the exact shape
   `general_BV_closed`/`hβSW_of_prime_indicator` supplies) gives `≤ Kβ·XY/(log XY)^A`.
   FULL.  (Mirrors `Salt.Chen.small_perd`.)

6. **The `hMainEnergy` reduction + discharge** (`mainEnergy_sum_le`,
   `four_term_scale_le`, **`hMainEnergy_discharge`**) — the two regimes assembled, the
   four-term scaled to `≤ (448+32√26)·XY/(log XY)^{A+1}` under the operating scale, and
   the `4(1+log D)` prefactor folded: **`hMainEnergy` is FULLY discharged**
   (`Kmain = 6(Kβ+448+32√26)`), the exact slot of `bilinear_hLargeDisc`.  FULL.

7. **The `hErrSum` α-side structure** (`bilinTwist_sub_primitive_eq`,
   `norm_bilinTwist_sub_primitive_le`) — the identity
   `A_d(χ) − A⋆ = −∑_{m≤X, (m,d)>1} α(m)·χ⋆(m)` (the BDH Möbius entry point) + its crude
   `L¹` bound.  FULL as far as the structure goes (the summation is the open core).

## Why `hMainEnergy` needs `β`-structure (the C3c″ finding)

`hMainEnergy` is **FALSE for a general pair `‖α‖,‖β‖ ≤ 1`**: take `α = β = χ₃` (Legendre
mod 3), then `bilinPrimEnergy α β X Y 3 ≈ (4/9)XY`, so the `f = 3` term alone is
`(8/9)(1+log D)·XY`, exceeding `Kmain·XY/(log XY)^A`.  The large sieve gives **no** saving
for a single small conductor.  It is satisfiable only for the actual consumer's
`β = blockPrimeInd N`, whose small-conductor twists have Siegel–Walfisz cancellation — so
the discharge is honestly gated on the named `hβSW` (exactly `hβSW_of_prime_indicator`).

## FLAG (Iron Rule 1 / STOP-AND-FLAG) — the one remaining core: `hErrSum`

`hErrSum` (keystone-2 core 2) is **not** discharged here.  The α-side error's crude `L¹`
bound `‖A_d−A⋆‖ ≤ #{m≤X:(m,d)>1}` makes the naive `d`-sum
`∑_{d≤D}(1/φd)·(∑_{p∣d}X/p)·Y ≈ XY·D` — **too big by `D`** (giving `(XY)^{3/2}/(log)^B`).
The honest fix is the BDH Möbius `e`-fold
`A_d − A⋆ = ∑_{e∣d,e>1} μ(e)ψ(e)·A^{(e)}(⌊X/e⌋)` (a `1/e`-weighted sum of shifted-scale
`X/e` energies, re-run through the `hMainEnergy` machinery, geometric in `e`) — the
remaining analytic core, recorded in `docs/blueprints/flags.md` (node C3c″).  Its entry
point (the difference identity) is landed above.  Consequently `general_BV_final`
(= `general_BV_closed` + `bilinear_hLargeDisc` with both cores) does **not** close: core 1
(`hMainEnergy_discharge`) is done, core 2 (`hErrSum`) remains.

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 0. A `√` helper -/

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0` (subadditivity of `Real.sqrt`). -/
lemma sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsum : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  rw [← Real.sqrt_sq hsum]
  apply Real.sqrt_le_sqrt
  have hcross : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  calc a + b ≤ a + b + 2 * (Real.sqrt a * Real.sqrt b) := by linarith
    _ = (Real.sqrt a) ^ 2 + (Real.sqrt b) ^ 2 + 2 * (Real.sqrt a * Real.sqrt b) := by
        rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
    _ = (Real.sqrt a + Real.sqrt b) ^ 2 := by ring

/-! ## 1. The `bilinPrimEnergy` shell -/

/-- The frozen balanced shell bound `2(1+log Y)·√(Q²+13(X+1))·√(Q²+13(Y+1))·√X·√Y`
(the RHS of `Salt.Chen.bilinTwist_energy_le`). -/
noncomputable def shellBound (X Y Q : ℕ) : ℝ :=
  2 * (1 + Real.log Y)
    * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((X : ℝ) + 1))
    * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((Y : ℝ) + 1))
    * Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ)

lemma shellBound_nonneg {X Y Q : ℕ} (hY : 0 < Y) : 0 ≤ shellBound X Y Q := by
  unfold shellBound
  have h1logY : (0 : ℝ) ≤ 1 + Real.log Y :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ Y by exact_mod_cast hY)]
  positivity

/-- **The `bilinPrimEnergy` shell (restatement of `bilinTwist_energy_le`).**  For
`‖α‖,‖β‖ ≤ 1`, the `(q/φq)`-weighted primitive block energy obeys the balanced
shell bound.  `bilinPrimEnergy = ∑_ψ ‖A‖·‖B‖` matches the shell's `∑_ψ ‖A·B‖`
term-by-term (`‖A·B‖ = ‖A‖·‖B‖`). -/
theorem energy_shell {X Y Q : ℕ} (hQ : 2 ≤ Q) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * bilinPrimEnergy α β X Y q
      ≤ shellBound X Y Q := by
  refine le_trans (le_of_eq ?_) (bilinTwist_energy_le hQ hY α β hα hβ)
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  unfold bilinPrimEnergy
  exact Finset.sum_congr rfl (fun ψ _ => (norm_mul _ _).symm)

/-! ## 2. The per-block dyadic consumption -/

/-- **The per-block consumption (the dyadic engine).**  On the dyadic block
`f ∈ (F, 2F]`, the `(1/φf)`-weight is `≤ (1/F)·(f/φf)` (since `1/f ≤ 1/F`), so the
block energy is `≤ (1/F)·shellBound X Y (2F)` (extend to `[1, 2F]`, consume
`energy_shell` at `Q = 2F`).  The `1/F` per-block normalization the C3a flag
prescribed. -/
theorem block_energy_le {X Y F : ℕ} (hF : 1 ≤ F) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc (F + 1) (2 * F), (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (1 / (F : ℝ)) * shellBound X Y (2 * F) := by
  have hFR : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hF
  -- weight step: `(1/φf) E ≤ (1/F)·(f/φf) E`.
  have hstep : ∀ f ∈ Finset.Icc (F + 1) (2 * F),
      (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
        ≤ (1 / (F : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf1 : 1 ≤ f := by omega
    have hFf : (F : ℝ) ≤ (f : ℝ) := by exact_mod_cast (by omega : F ≤ f)
    have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hEnn : 0 ≤ bilinPrimEnergy α β X Y f := bilinPrimEnergy_nonneg _ _ _ _ _
    have hwle : (1 / (f.totient : ℝ)) ≤ (1 / (F : ℝ)) * ((f : ℝ) / (f.totient : ℝ)) := by
      have hrw : (1 / (F : ℝ)) * ((f : ℝ) / (f.totient : ℝ))
          = (f : ℝ) / ((F : ℝ) * (f.totient : ℝ)) := by field_simp
      rw [hrw, div_le_div_iff₀ hφpos (mul_pos hFR hφpos)]
      nlinarith [hFf, hφpos.le]
    calc (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
          ≤ ((1 / (F : ℝ)) * ((f : ℝ) / (f.totient : ℝ))) * bilinPrimEnergy α β X Y f :=
            mul_le_mul_of_nonneg_right hwle hEnn
        _ = (1 / (F : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- extend `(F+1, 2F]` to `[1, 2F]` (nonneg terms), then consume the shell.
  have hsub : Finset.Icc (F + 1) (2 * F) ⊆ Finset.Icc 1 (2 * F) := by
    intro f hf; rw [Finset.mem_Icc] at hf ⊢; omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => ?_)) ?_
  · exact mul_nonneg (by positivity) (bilinPrimEnergy_nonneg _ _ _ _ _)
  · exact energy_shell (by omega) hY α β hα hβ

/-- **General block consumption** (`Icc a b` form of `block_energy_le`).  For any
block `[a, b]` with `1 ≤ a`, `2 ≤ b`: the `(1/φf)`-weight is `≤ (1/a)·(f/φf)`, so the
block energy is `≤ (1/a)·shellBound X Y b` (extend to `[1, b]`, consume `energy_shell`
at `Q = b`).  The dyadic reduction consumes this at `a = 2^k`, `b = 2^{k+1}`. -/
theorem block_energy_le' {X Y a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc a b, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (1 / (a : ℝ)) * shellBound X Y b := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hstep : ∀ f ∈ Finset.Icc a b,
      (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
        ≤ (1 / (a : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf1 : 1 ≤ f := by omega
    have haf : (a : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf.1
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
  have hsub : Finset.Icc a b ⊆ Finset.Icc 1 b := by
    intro f hf; rw [Finset.mem_Icc] at hf ⊢; omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => ?_)) ?_
  · exact mul_nonneg (by positivity) (bilinPrimEnergy_nonneg _ _ _ _ _)
  · exact energy_shell hb hY α β hα hβ

/-- **The dyadic large-conductor reduction (the dyadic-sum skeleton).**  For
`D0 = 2^{k0}` (`k0 ≥ 1`) and `K = ⌊log₂ D⌋`, the large-conductor energy
`∑_{D0 < f ≤ D} (1/φf)·E(f)` is bounded by the pure geometric sum
`∑_{k=k0}^{K} (1/2^k)·shellBound X Y (2^{k+1})` — a genuine consumption of the
per-block engine `block_energy_le'` via the dyadic fibration `f ↦ ⌊log₂ f⌋` (fibers
land in `Icc k0 K`, each fiber sits in the block `[2^k, 2^{k+1}]`).  This is the
`f > D0` regime reduced to a real geometric sum with **no** further character theory;
its evaluation to `XY/(log XY)^A` is the remaining analytic core (see the FLAG). -/
theorem dyadic_large_reduction {X Y D0 D k0 K : ℕ} (hD0 : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc (D0 + 1) D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ ∑ k ∈ Finset.Icc k0 K, (1 / (2 ^ k : ℝ)) * shellBound X Y (2 ^ (k + 1)) := by
  have hmaps : ∀ f ∈ Finset.Icc (D0 + 1) D, Nat.log 2 f ∈ Finset.Icc k0 K := by
    intro f hf
    rw [Finset.mem_Icc] at hf ⊢
    refine ⟨?_, ?_⟩
    · apply Nat.le_log_of_pow_le (by norm_num)
      rw [← hD0]; omega
    · rw [hK]; exact Nat.log_mono_right hf.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun f => (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f)]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [Finset.mem_Icc] at hk
  have hfibsub : (Finset.Icc (D0 + 1) D).filter (fun f => Nat.log 2 f = k)
      ⊆ Finset.Icc (2 ^ k) (2 ^ (k + 1)) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_Icc] at hf
    obtain ⟨⟨hf1, _⟩, hlog⟩ := hf
    have hf0 : f ≠ 0 := by omega
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have := Nat.pow_log_le_self 2 hf0; rwa [hlog] at this
    · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) f
      rw [hlog] at this; omega
  calc ∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => Nat.log 2 f = k),
          (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ ∑ f ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1)),
          (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hfibsub (fun f _ _ => ?_)
        exact mul_nonneg (by positivity) (bilinPrimEnergy_nonneg _ _ _ _ _)
    _ ≤ (1 / (2 ^ k : ℝ)) * shellBound X Y (2 ^ (k + 1)) := by
        have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have h2k1 : 2 ≤ 2 ^ (k + 1) := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
        have hbk := block_energy_le' (X := X) (Y := Y) (a := 2 ^ k) (b := 2 ^ (k + 1))
          h2k h2k1 hY α β hα hβ
        rwa [hcast] at hbk

/-- **Per-block √-split.**  `(1/F)·√((2F)²+a)·√((2F)²+b) ≤ 4F + 2√a + 2√b + √a√b/F`
for `F > 0`, `a, b ≥ 0` (via `√(P+q) ≤ √P+√q` and `√((2F)²) = 2F`).  The elementary
core of the dyadic geometric sum. -/
lemma dyadic_term_bound {F a b : ℝ} (hF : 0 < F) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / F) * (Real.sqrt ((2 * F) ^ 2 + a) * Real.sqrt ((2 * F) ^ 2 + b))
      ≤ 4 * F + 2 * Real.sqrt a + 2 * Real.sqrt b + Real.sqrt a * Real.sqrt b / F := by
  have hsA : Real.sqrt ((2 * F) ^ 2 + a) ≤ 2 * F + Real.sqrt a := by
    have h := sqrt_add_le_add_sqrt (sq_nonneg (2 * F)) ha
    rwa [Real.sqrt_sq (by positivity)] at h
  have hsB : Real.sqrt ((2 * F) ^ 2 + b) ≤ 2 * F + Real.sqrt b := by
    have h := sqrt_add_le_add_sqrt (sq_nonneg (2 * F)) hb
    rwa [Real.sqrt_sq (by positivity)] at h
  have hprod : Real.sqrt ((2 * F) ^ 2 + a) * Real.sqrt ((2 * F) ^ 2 + b)
      ≤ (2 * F + Real.sqrt a) * (2 * F + Real.sqrt b) :=
    mul_le_mul hsA hsB (Real.sqrt_nonneg _) (by positivity)
  calc (1 / F) * (Real.sqrt ((2 * F) ^ 2 + a) * Real.sqrt ((2 * F) ^ 2 + b))
      ≤ (1 / F) * ((2 * F + Real.sqrt a) * (2 * F + Real.sqrt b)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 4 * F + 2 * Real.sqrt a + 2 * Real.sqrt b + Real.sqrt a * Real.sqrt b / F := by
        field_simp; ring

/-- **The dyadic geometric sum (evaluation of the dyadic-in-conductor sum).**  The
pure geometric sum `∑_{k=k0}^{K} (1/2^k)·shellBound X Y (2^{k+1})` is bounded by the
classical `(D + √X + √Y + XY/D0)·√(XY)·log` four-term endgame in explicit form:
`4·2^{K+1}` (the `~D` main term), `2(K+1)√(13(X+1))`, `2(K+1)√(13(Y+1))` (the
`~√X, √Y` cross terms), and `√(13(X+1))√(13(Y+1))·2/2^{k0}` (the `~XY/D0` tail),
all scaled by `2(1+log Y)√X√Y`. -/
theorem geom_shell_sum_le {X Y k0 K : ℕ} (hY : 0 < Y) :
    ∑ k ∈ Finset.Icc k0 K, (1 / (2 ^ k : ℝ)) * shellBound X Y (2 ^ (k + 1))
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ (K + 1)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1))
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
            + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) := by
  have h1logY : (0 : ℝ) ≤ 1 + Real.log Y :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ Y by exact_mod_cast hY)]
  have hC : (0 : ℝ) ≤ 2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y := by positivity
  have hu : (0 : ℝ) ≤ Real.sqrt (13 * ((X : ℝ) + 1)) := Real.sqrt_nonneg _
  have hv : (0 : ℝ) ≤ Real.sqrt (13 * ((Y : ℝ) + 1)) := Real.sqrt_nonneg _
  -- Per-`k` bound via `dyadic_term_bound`.
  have hperk : ∀ k, (1 / (2 ^ k : ℝ)) * shellBound X Y (2 ^ (k + 1))
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ k + 2 * Real.sqrt (13 * ((X : ℝ) + 1))
              + 2 * Real.sqrt (13 * ((Y : ℝ) + 1))
              + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) / (2 : ℝ) ^ k) := by
    intro k
    have hFk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hq : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ k := by push_cast; ring
    have hshell : shellBound X Y (2 ^ (k + 1))
        = (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
            * (Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 + 13 * ((X : ℝ) + 1))
                * Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 + 13 * ((Y : ℝ) + 1))) := by
      unfold shellBound; rw [hq]; ring
    rw [hshell, mul_comm (1 / (2 ^ k : ℝ)) _, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hdt := dyadic_term_bound (F := (2 : ℝ) ^ k) (a := 13 * ((X : ℝ) + 1))
      (b := 13 * ((Y : ℝ) + 1)) hFk (by positivity) (by positivity)
    -- align `1/F * (√·√)` with `(√·√) * (1/F)`
    rwa [mul_comm (Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 + 13 * ((X : ℝ) + 1))
          * Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2 + 13 * ((Y : ℝ) + 1))) (1 / (2 : ℝ) ^ k)]
  refine le_trans (Finset.sum_le_sum (fun k _ => hperk k)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hC
  -- split the bracket sum into the four geometric/counting pieces.
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hpow2 : ∑ k ∈ Finset.Icc k0 K, 4 * (2 : ℝ) ^ k ≤ 4 * (2 : ℝ) ^ (K + 1) := by
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
  have hcard : (Finset.Icc k0 K).card ≤ K + 1 := by
    rw [Nat.card_Icc]; omega
  have hconstX : ∑ k ∈ Finset.Icc k0 K, 2 * Real.sqrt (13 * ((X : ℝ) + 1))
      ≤ 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.Icc k0 K).card : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    nlinarith [this, hu]
  have hconstY : ∑ k ∈ Finset.Icc k0 K, 2 * Real.sqrt (13 * ((Y : ℝ) + 1))
      ≤ 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.Icc k0 K).card : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    nlinarith [this, hv]
  have htail : ∑ k ∈ Finset.Icc k0 K,
        Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) / (2 : ℝ) ^ k
      ≤ Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0) := by
    have hfac : ∀ k, Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) / (2 : ℝ) ^ k
        = (Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)))
          * (1 / (2 : ℝ) ^ k) := by
      intro k; ring
    rw [Finset.sum_congr rfl (fun k _ => hfac k), ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hu hv)
    -- ∑_{Icc k0 K} (1/2)^k ≤ 2/2^{k0}
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

/-! ## 3. The small-conductor SW consumption -/

/-- The crude twisted-sum bound `‖A(χ)‖ ≤ X` (inlined port of `bilinTwist_norm_le`). -/
private lemma bilinTwist_norm_le' {d : ℕ} (α : ℕ → ℂ) (X : ℕ) (χ : DirichletCharacter ℂ d)
    (hα : ∀ m, ‖α m‖ ≤ 1) : ‖bilinTwist α X d χ‖ ≤ (X : ℝ) := by
  unfold bilinTwist
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ Finset.Icc 1 X, ‖α m * χ (m : ZMod d)‖
      ≤ ∑ _m ∈ Finset.Icc 1 X, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [norm_mul]
        calc ‖α m‖ * ‖χ (m : ZMod d)‖ ≤ 1 * 1 :=
              mul_le_mul (hα m) (DirichletCharacter.norm_le_one χ _) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
    _ = (X : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

open Classical in
/-- **The small-conductor SW consumption (mirrors `Salt.Chen.small_perd`).**  For
conductors `f ≤ D0 = (log XY)^{C0}`, the SW-regularity of `β` (`hβSW`, in the exact
shape `general_BV_closed` derives from `hβSW_of_prime_indicator`) contracts each
`(1/φf)·bilinPrimEnergy` to `Kβ·XY/(log XY)^{A+C0}`; summing over the `≤ D0`
conductors gives `≤ Kβ·XY/(log XY)^A`.  This is the `f ≤ D0` regime of the
`hMainEnergy` two-regime discharge (the small-conductor blocks that arise as
conductors of the imprimitive characters of the large moduli `d > D0`). -/
theorem smallConductor_energy_le {X Y D0 : ℕ} {A C0 Kβ : ℝ} (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hKβ : 0 ≤ Kβ)
    (hLpos : 0 < Real.log ((X : ℝ) * (Y : ℝ)))
    (hD0 : (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (Y : ℝ))) ^ C0)
    (hβSW : ∀ f : ℕ, 2 ≤ f → f ≤ D0 → ∀ ψ : DirichletCharacter ℂ f, ψ ≠ 1 →
        ‖bilinTwist β Y f ψ‖ ≤ Kβ * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + C0)) :
    ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  classical
  set L := Real.log ((X : ℝ) * (Y : ℝ)) with hLdef
  have hLA : (0 : ℝ) < L ^ (A + C0) := Real.rpow_pos_of_pos hLpos _
  set V : ℝ := Kβ * (Y : ℝ) / L ^ (A + C0) with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  -- Per-conductor: `(1/φf)·bilinPrimEnergy ≤ X·V`.
  have hperf : ∀ f ∈ Finset.Icc 2 D0,
      (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f ≤ (X : ℝ) * V := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf2 : 2 ≤ f := hf.1
    haveI : NeZero f := ⟨by omega⟩
    have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    -- each primitive ψ ≠ 1 and obeys `‖A‖ ≤ X`, `‖B‖ ≤ V`.
    have hbound : ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive),
          ‖bilinTwist α X f ψ‖ * ‖bilinTwist β Y f ψ‖
        ≤ ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card : ℝ)
            * ((X : ℝ) * V) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum (fun ψ hψ => ?_)
      rw [Finset.mem_filter] at hψ
      have hψprim : ψ.IsPrimitive := hψ.2
      have hψ1 : ψ ≠ 1 := by
        intro h
        rw [DirichletCharacter.isPrimitive_def] at hψprim
        rw [h, DirichletCharacter.conductor_one] at hψprim
        omega
      have hA : ‖bilinTwist α X f ψ‖ ≤ (X : ℝ) := bilinTwist_norm_le' α X ψ hα
      have hB : ‖bilinTwist β Y f ψ‖ ≤ V := hβSW f hf2 hf.2 ψ hψ1
      exact mul_le_mul hA hB (norm_nonneg _) (by positivity)
    have hcard : ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card : ℝ)
        ≤ (f.totient : ℝ) := by
      have h1 : (Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card
          ≤ (Finset.univ : Finset (DirichletCharacter ℂ f)).card := Finset.card_filter_le _ _
      have h2 : (Finset.univ : Finset (DirichletCharacter ℂ f)).card = f.totient := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ f]
      rw [h2] at h1; exact_mod_cast h1
    calc (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
        ≤ (1 / (f.totient : ℝ))
            * (((Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive)).card : ℝ)
                * ((X : ℝ) * V)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hbound
      _ ≤ (1 / (f.totient : ℝ)) * ((f.totient : ℝ) * ((X : ℝ) * V)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (X : ℝ) * V := by field_simp
  -- Sum over the `≤ D0` conductors.
  have hcardD0 : ((Finset.Icc 2 D0).card : ℝ) ≤ (D0 : ℝ) := by
    rw [Nat.card_Icc]; exact_mod_cast (by omega : D0 + 1 - 2 ≤ D0)
  calc ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ ∑ _f ∈ Finset.Icc 2 D0, ((X : ℝ) * V) := Finset.sum_le_sum hperf
    _ = ((Finset.Icc 2 D0).card : ℝ) * ((X : ℝ) * V) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D0 : ℝ) * ((X : ℝ) * V) := by
        refine mul_le_mul_of_nonneg_right hcardD0 ?_; positivity
    _ ≤ L ^ C0 * ((X : ℝ) * V) := by
        refine mul_le_mul_of_nonneg_right hD0 ?_; positivity
    _ = Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ A := by
        rw [hVdef, Real.rpow_add hLpos A C0]; field_simp

/-- **The four-term scale arithmetic (the classical `choose B vs A` endgame) — FULL.**
Under the honest operating scale — `X, Y ≥ 2`, `1 ≤ D`, level cut `D ≤ √(XY)/(log XY)^B`
with `B ≥ A+2`, dyadic bottom `D0 = 2^{k0}` with `(log XY)^{A+2} ≤ 2·2^{k0}` (the T4 tail
exponent — DECOUPLED from the SW exponent `C0`, the catch-#64 repair: the proof only ever
needed the `A+2` power here, and demanding `L^{C0}` jointly with `D0 ≤ (log N)^{C0}` empties
the `D0`-window at every boundary box), `C0 ≥ A+2`,
and the mild `X, Y ≥ (log XY)^{2A+6}` (as `(log XY)^{A+3} ≤ √X, √Y`) — the explicit
four-term dyadic bound `2(1+log Y)√X√Y·(4·2^{K+1} + 2(K+1)√(13(X+1)) + 2(K+1)√(13(Y+1))
+ √(13(X+1))√(13(Y+1))·2/2^{k0})` (with `K = ⌊log₂ D⌋`) is `≤ (448+32√26)·XY/(log XY)^{A+1}`.
The four contributions land as `32` (`~D√(XY)` main), `16√26` twice (the `~√X·Y`, `~X·√Y`
cross terms, needing `X,Y ≥ (log)^{2A+6}`), and `416` (the `~XY/D0` tail).  This closes the
`f > D0` regime of `hMainEnergy` (via `dyadic_large_reduction` + `geom_shell_sum_le`). -/
theorem four_term_scale_le {X Y D k0 K : ℕ} {A B C0 : ℝ}
    (hA : 0 ≤ A) (hX2 : 2 ≤ X) (hY2 : 2 ≤ Y) (h1D : 1 ≤ D)
    (hB : A + 2 ≤ B) (hC0 : A + 2 ≤ C0)
    (hD : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ B)
    (hK : K = Nat.log 2 D)
    (hD0 : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0)
    (hXsqrt : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 3) ≤ Real.sqrt X)
    (hYsqrt : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 3) ≤ Real.sqrt Y) :
    (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
        * (4 * (2 : ℝ) ^ (K + 1)
          + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1))
          + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
          + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0))
      ≤ (448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ))
          / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1) := by
  -- catch-#64 repair: `hD0` is now consumed at the decoupled `A+2` exponent, so `hC0` is
  -- no longer needed by this proof; it is retained in the signature (the D0W warrant is a
  -- row-only statement change) and referenced here for the unused-variable linter.
  have _ := hC0
  set L := Real.log ((X : ℝ) * (Y : ℝ)) with hLdef
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
  have hXY4 : (4 : ℝ) ≤ (X : ℝ) * (Y : ℝ) := by nlinarith [hXR, hYR]
  have hXYpos : (0 : ℝ) < (X : ℝ) * (Y : ℝ) := by linarith
  have hXYnn : (0 : ℝ) ≤ (X : ℝ) * (Y : ℝ) := le_of_lt hXYpos
  have hL1 : (1 : ℝ) ≤ L := by
    have hexp : Real.exp 1 ≤ (X : ℝ) * (Y : ℝ) := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos 1) hexp
  have hLpos : (0 : ℝ) < L := by linarith
  have hlogY_le : Real.log Y ≤ L := by
    apply Real.log_le_log (by linarith [hYR] : (0:ℝ) < (Y:ℝ))
    calc (Y : ℝ) = 1 * (Y : ℝ) := (one_mul _).symm
      _ ≤ (X : ℝ) * (Y : ℝ) := by
          apply mul_le_mul_of_nonneg_right (by linarith [hXR]) (by linarith [hYR])
  have h1logY : (0 : ℝ) ≤ 1 + Real.log Y := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ (Y:ℝ) by linarith [hYR])]
  have h1logY2L : 1 + Real.log Y ≤ 2 * L := by linarith
  have hsxy : Real.sqrt X * Real.sqrt Y = Real.sqrt ((X : ℝ) * (Y : ℝ)) :=
    (Real.sqrt_mul (by positivity) _).symm
  have hsqrtXYsq : Real.sqrt ((X : ℝ) * (Y : ℝ)) * Real.sqrt ((X : ℝ) * (Y : ℝ))
      = (X : ℝ) * (Y : ℝ) := Real.mul_self_sqrt hXYnn
  have hsX : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hsY : (0 : ℝ) ≤ Real.sqrt Y := Real.sqrt_nonneg _
  have hsXY : (0 : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) := Real.sqrt_nonneg _
  have hu26 : Real.sqrt (13 * ((X : ℝ) + 1)) ≤ Real.sqrt 26 * Real.sqrt X := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 26)]
    apply Real.sqrt_le_sqrt; nlinarith [hXR]
  have hv26 : Real.sqrt (13 * ((Y : ℝ) + 1)) ≤ Real.sqrt 26 * Real.sqrt Y := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 26)]
    apply Real.sqrt_le_sqrt; nlinarith [hYR]
  have hs26 : (0 : ℝ) ≤ Real.sqrt 26 := Real.sqrt_nonneg _
  have hs26sq : Real.sqrt 26 * Real.sqrt 26 = 26 := Real.mul_self_sqrt (by norm_num)
  have huv : Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
      ≤ 26 * Real.sqrt ((X : ℝ) * (Y : ℝ)) := by
    calc Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
        ≤ (Real.sqrt 26 * Real.sqrt X) * (Real.sqrt 26 * Real.sqrt Y) :=
          mul_le_mul hu26 hv26 (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt 26 * Real.sqrt 26) * (Real.sqrt X * Real.sqrt Y) := by ring
      _ = 26 * Real.sqrt ((X : ℝ) * (Y : ℝ)) := by rw [hs26sq, hsxy]
  have hLB1 : (1 : ℝ) ≤ L ^ B := Real.one_le_rpow hL1 (by linarith)
  have hDsqrt : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) := by
    calc (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) / L ^ B := hD
      _ ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) / 1 := by
          apply div_le_div_of_nonneg_left hsXY (by norm_num) hLB1
      _ = Real.sqrt ((X : ℝ) * (Y : ℝ)) := by rw [div_one]
  have h2K : (2 : ℝ) ^ K ≤ (D : ℝ) := by
    have hp := Nat.pow_log_le_self 2 (by omega : D ≠ 0)
    rw [hK]
    calc ((2:ℝ)) ^ (Nat.log 2 D) = ((2 ^ Nat.log 2 D : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (D : ℝ) := by exact_mod_cast hp
  have hKL : (K : ℝ) ≤ L := by
    have hlog2 : (1:ℝ)/2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hstep : (K : ℝ) * Real.log 2 ≤ L / 2 := by
      have h1 : Real.log ((2:ℝ)^K) ≤ Real.log (Real.sqrt ((X:ℝ)*(Y:ℝ))) :=
        Real.log_le_log (by positivity) (le_trans h2K hDsqrt)
      rw [Real.log_pow, Real.log_sqrt hXYnn] at h1
      linarith
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hprod : (0 : ℝ) ≤ (K : ℝ) * (Real.log 2 - 1 / 2) := mul_nonneg hKnn (by linarith)
    nlinarith [hstep, hprod]
  have hK1_2L : ((K + 1 : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith
  have h2K1 : (2 : ℝ) ^ (K + 1) ≤ 2 * (D : ℝ) := by
    rw [pow_succ]; nlinarith [h2K, (by positivity : (0:ℝ) ≤ (2:ℝ)^K)]
  have hLApos : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
  have hCnn : (0 : ℝ) ≤ 2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1logY) hsX) hsY
  -- collapse helper: L * L^(A+1) = L^(A+2)
  have hcollapse : L * L ^ (A + 1) = L ^ (A + 2) := by
    have hh := Real.rpow_add hLpos 1 (A + 1)
    rw [Real.rpow_one] at hh
    rw [← hh, show (1 : ℝ) + (A + 1) = A + 2 by ring]
  -- rpow bookkeeping
  have hrp_B : L / L ^ B ≤ 1 / L ^ (A + 1) := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos _) hLApos, one_mul, hcollapse]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hB
  have hrp_C0 : L * (2 / (2 : ℝ) ^ k0) ≤ 4 / L ^ (A + 1) := by
    have h2k0 : (0 : ℝ) < (2 : ℝ) ^ k0 := by positivity
    -- catch-#64 repair: the tail cut is consumed DIRECTLY at the `A+2` exponent.
    have hstep : (2 : ℝ) / (2 : ℝ) ^ k0 ≤ 4 / L ^ (A + 2) := by
      rw [div_le_div_iff₀ h2k0 (Real.rpow_pos_of_pos hLpos _)]; linarith [hD0]
    calc L * (2 / (2 : ℝ) ^ k0)
        ≤ L * (4 / L ^ (A + 2)) := mul_le_mul_of_nonneg_left hstep (le_of_lt hLpos)
      _ = 4 * (L / L ^ (A + 2)) := by ring
      _ = 4 * (1 / L ^ (A + 1)) := by
          have h : L / L ^ (A + 2) = 1 / L ^ (A + 1) := by
            rw [div_eq_div_iff (Real.rpow_pos_of_pos hLpos _).ne' hLApos.ne', one_mul, hcollapse]
          rw [h]
      _ = 4 / L ^ (A + 1) := by ring
  -- distribute
  rw [mul_add, mul_add, mul_add]
  -- T1
  have hT1 : (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y) * (4 * (2 : ℝ) ^ (K + 1))
      ≤ 32 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by
    calc (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y) * (4 * (2 : ℝ) ^ (K + 1))
        ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y) * (4 * (2 * (D : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hCnn
          apply mul_le_mul_of_nonneg_left h2K1 (by norm_num)
      _ ≤ (2 * (2 * L) * Real.sqrt X * Real.sqrt Y)
            * (4 * (2 * (Real.sqrt ((X:ℝ)*(Y:ℝ)) / L ^ B))) := by
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · apply mul_le_mul_of_nonneg_right _ hsY
            apply mul_le_mul_of_nonneg_right _ hsX
            linarith [h1logY2L]
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = 32 * L * (Real.sqrt X * Real.sqrt Y) * (Real.sqrt ((X:ℝ)*(Y:ℝ)) / L ^ B) := by ring
      _ = 32 * L * (Real.sqrt ((X:ℝ)*(Y:ℝ)) * Real.sqrt ((X:ℝ)*(Y:ℝ))) / L ^ B := by
          rw [hsxy]; ring
      _ = 32 * ((X:ℝ)*(Y:ℝ)) * (L / L ^ B) := by rw [hsqrtXYsq]; ring
      _ ≤ 32 * ((X:ℝ)*(Y:ℝ)) * (1 / L ^ (A + 1)) := by
          apply mul_le_mul_of_nonneg_left hrp_B (by positivity)
      _ = 32 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by ring
  -- sqrt-square helpers
  have hsXX : Real.sqrt X * Real.sqrt X = (X : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg X)
  have hsYY : Real.sqrt Y * Real.sqrt Y = (Y : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg Y)
  have hXYsq : (Real.sqrt X * Real.sqrt Y) * (Real.sqrt X * Real.sqrt Y) = (X : ℝ) * (Y : ℝ) := by
    rw [show (Real.sqrt X * Real.sqrt Y) * (Real.sqrt X * Real.sqrt Y)
          = (Real.sqrt X * Real.sqrt X) * (Real.sqrt Y * Real.sqrt Y) by ring, hsXX, hsYY]
  -- L * L^e = L^(e+1)
  have hLmul : ∀ e : ℝ, L * L ^ e = L ^ (e + 1) := by
    intro e
    have hh := Real.rpow_add hLpos 1 e
    rw [Real.rpow_one] at hh
    rw [← hh, show (1 : ℝ) + e = e + 1 by ring]
  have hLcol3 : L * L * L ^ (A + 1) = L ^ (A + 3) := by
    rw [mul_assoc, hLmul, show (A : ℝ) + 1 + 1 = A + 2 by ring, hLmul,
      show (A : ℝ) + 2 + 1 = A + 3 by ring]
  -- L² √Y ≤ Y / L^{A+1},  L² √X ≤ X / L^{A+1}
  have hsub2 : (L * L) * Real.sqrt Y ≤ (Y : ℝ) / L ^ (A + 1) := by
    rw [le_div_iff₀ hLApos]
    calc (L * L) * Real.sqrt Y * L ^ (A + 1) = (L * L * L ^ (A + 1)) * Real.sqrt Y := by ring
      _ = L ^ (A + 3) * Real.sqrt Y := by rw [hLcol3]
      _ ≤ Real.sqrt Y * Real.sqrt Y := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hYsqrt hsY
      _ = (Y : ℝ) := hsYY
  have hsub3 : (L * L) * Real.sqrt X ≤ (X : ℝ) / L ^ (A + 1) := by
    rw [le_div_iff₀ hLApos]
    calc (L * L) * Real.sqrt X * L ^ (A + 1) = (L * L * L ^ (A + 1)) * Real.sqrt X := by ring
      _ = L ^ (A + 3) * Real.sqrt X := by rw [hLcol3]
      _ ≤ Real.sqrt X * Real.sqrt X := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hXsqrt hsX
      _ = (X : ℝ) := hsXX
  -- T2
  have hT2 : (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
        * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)))
      ≤ 16 * Real.sqrt 26 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by
    calc (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)))
        ≤ (2 * (2 * L) * Real.sqrt X * Real.sqrt Y)
            * (2 * (2 * L) * (Real.sqrt 26 * Real.sqrt X)) := by
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · apply mul_le_mul_of_nonneg_right _ hsY
            apply mul_le_mul_of_nonneg_right _ hsX
            linarith [h1logY2L]
          · apply mul_le_mul _ hu26 (by positivity) (by positivity)
            apply mul_le_mul_of_nonneg_left hK1_2L (by norm_num)
      _ = 16 * Real.sqrt 26 * ((L * L) * Real.sqrt Y) * (Real.sqrt X * Real.sqrt X) := by ring
      _ = 16 * Real.sqrt 26 * ((L * L) * Real.sqrt Y) * (X : ℝ) := by rw [hsXX]
      _ ≤ 16 * Real.sqrt 26 * ((Y : ℝ) / L ^ (A + 1)) * (X : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hsub2 (by positivity)
      _ = 16 * Real.sqrt 26 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by ring
  -- T3
  have hT3 : (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
        * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)))
      ≤ 16 * Real.sqrt 26 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by
    calc (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)))
        ≤ (2 * (2 * L) * Real.sqrt X * Real.sqrt Y)
            * (2 * (2 * L) * (Real.sqrt 26 * Real.sqrt Y)) := by
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · apply mul_le_mul_of_nonneg_right _ hsY
            apply mul_le_mul_of_nonneg_right _ hsX
            linarith [h1logY2L]
          · apply mul_le_mul _ hv26 (by positivity) (by positivity)
            apply mul_le_mul_of_nonneg_left hK1_2L (by norm_num)
      _ = 16 * Real.sqrt 26 * ((L * L) * Real.sqrt X) * (Real.sqrt Y * Real.sqrt Y) := by ring
      _ = 16 * Real.sqrt 26 * ((L * L) * Real.sqrt X) * (Y : ℝ) := by rw [hsYY]
      _ ≤ 16 * Real.sqrt 26 * ((X : ℝ) / L ^ (A + 1)) * (Y : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hsub3 (by positivity)
      _ = 16 * Real.sqrt 26 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by ring
  -- T4
  have hT4 : (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
        * (Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0))
      ≤ 416 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by
    calc (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0))
        ≤ (2 * (2 * L) * Real.sqrt X * Real.sqrt Y)
            * ((26 * Real.sqrt ((X : ℝ) * (Y : ℝ))) * (2 / (2 : ℝ) ^ k0)) := by
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · apply mul_le_mul_of_nonneg_right _ hsY
            apply mul_le_mul_of_nonneg_right _ hsX
            linarith [h1logY2L]
          · apply mul_le_mul_of_nonneg_right huv (by positivity)
      _ = 104 * ((Real.sqrt X * Real.sqrt Y) * (Real.sqrt X * Real.sqrt Y))
            * (L * (2 / (2 : ℝ) ^ k0)) := by rw [← hsxy]; ring
      _ = 104 * ((X : ℝ) * (Y : ℝ)) * (L * (2 / (2 : ℝ) ^ k0)) := by rw [hXYsq]
      _ ≤ 104 * ((X : ℝ) * (Y : ℝ)) * (4 / L ^ (A + 1)) := by
          apply mul_le_mul_of_nonneg_left hrp_C0 (by positivity)
      _ = 416 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by ring
  -- combine
  have hrhs : (448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)
      = 32 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)
        + 16 * Real.sqrt 26 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)
        + 16 * Real.sqrt 26 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)
        + 416 * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by ring
  rw [hrhs]
  exact add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4

/-! ## 4. The `hMainEnergy` reduction (small SW + dyadic large, assembled) -/

open Classical in
/-- **The `hMainEnergy` energy sum, reduced to the explicit four-term endgame.**  The
full primitive block energy `∑_{2≤f≤D} (1/φf)·bilinPrimEnergy` splits at the SW
threshold `D0 = 2^{k0}` into the SW-controlled small part (`smallConductor_energy_le`,
`≤ Kβ·XY/(log XY)^A`) and the dyadic large part (`dyadic_large_reduction` +
`geom_shell_sum_le`, the classical `(D + √X + √Y + XY/D0)·√(XY)·log` four-term bound).
This is the entire character-theoretic + dyadic content of `hMainEnergy`; what remains
is the purely real scale arithmetic bounding the four-term expression by `XY/(log XY)^A`
under `D ≤ √(XY)/(log XY)^B`, `D0 ≍ (log XY)^{C0}`, `X,Y ≥ (log XY)^K` (see the FLAG). -/
theorem mainEnergy_sum_le {X Y D0 D k0 K : ℕ} {A C0 Kβ : ℝ} (hD0eq : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (h2D0 : 2 ≤ D0) (hD0D : D0 ≤ D) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) (hKβ : 0 ≤ Kβ)
    (hLpos : 0 < Real.log ((X : ℝ) * (Y : ℝ)))
    (hD0log : (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (Y : ℝ))) ^ C0)
    (hβSW : ∀ f : ℕ, 2 ≤ f → f ≤ D0 → ∀ ψ : DirichletCharacter ℂ f, ψ ≠ 1 →
        ‖bilinTwist β Y f ψ‖ ≤ Kβ * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + C0)) :
    ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A
        + (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
            * (4 * (2 : ℝ) ^ (K + 1)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1))
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
              + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0)) := by
  have hsplit : ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      = ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
        + ∑ f ∈ Finset.Icc (D0 + 1) D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f := by
    rw [show Finset.Icc 2 D = Finset.Ioc 1 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc 2 D0 = Finset.Ioc 1 D0 by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc (D0 + 1) D = Finset.Ioc D0 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    exact (Finset.sum_Ioc_consecutive _ (by omega : 1 ≤ D0) hD0D).symm
  rw [hsplit]
  refine add_le_add ?_ ?_
  · exact smallConductor_energy_le α β hα hKβ hLpos hD0log hβSW
  · exact le_trans (dyadic_large_reduction hD0eq hK hY α β hα hβ) (geom_shell_sum_le hY)

open Classical in
/-- **The `hMainEnergy` discharge (KEYSTONE 2, core 1 — FULL under the operating scale).**
Assembling `mainEnergy_sum_le` (SW small part at `L^{A+1}` + dyadic four-term) with
`four_term_scale_le` (four-term `≤ (448+32√26)·XY/L^{A+1}`) and folding the `4(1+log D)`
prefactor (`4(1+log D) ≤ 6L` since `log D ≤ (1/2)log(XY)`, `L·1/L^{A+1} = 1/L^A`) gives
exactly the `hMainEnergy` slot of `bilinear_hLargeDisc`:
```
4(1+log D)·∑_{2≤f≤D} (1/φf)·bilinPrimEnergy α β X Y f ≤ Kmain·XY/(log XY)^A
```
with `Kmain = 6(Kβ + 448 + 32√26)`.  Honest operating scale: `X,Y ≥ 2`, `1 ≤ D`,
`D ≤ √(XY)/(log XY)^B` (`B ≥ A+2`), `D0 = 2^{k0}` with `(log XY)^{C0} ≤ 2·2^{k0}` and
`D0 ≤ (log XY)^{C0}` (i.e. `D0 ≍ (log XY)^{C0}`, `C0 ≥ A+2`), `X,Y ≥ (log XY)^{2A+6}`, and
the named SW-regularity `hβSW` of `β` (exactly what `hβSW_of_prime_indicator` supplies for
`β = blockPrimeInd`). -/
theorem hMainEnergy_discharge {X Y D0 D k0 K : ℕ} {A B C0 Kβ : ℝ}
    (hA : 0 ≤ A) (hX2 : 2 ≤ X) (hY2 : 2 ≤ Y) (h1D : 1 ≤ D)
    (hB : A + 2 ≤ B) (hC0 : A + 2 ≤ C0)
    (hD0eq : D0 = 2 ^ k0) (h2D0 : 2 ≤ D0) (hD0D : D0 ≤ D)
    (hK : K = Nat.log 2 D)
    (hDscale : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ B)
    (hD0lo : (Real.log ((X : ℝ) * (Y : ℝ))) ^ C0 ≤ 2 * (2 : ℝ) ^ k0)
    (hD0hi : (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (Y : ℝ))) ^ C0)
    (hXsqrt : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 3) ≤ Real.sqrt X)
    (hYsqrt : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 3) ≤ Real.sqrt Y)
    (hKβ : 0 ≤ Kβ) (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1)
    (hβSW : ∀ f : ℕ, 2 ≤ f → f ≤ D0 → ∀ ψ : DirichletCharacter ℂ f, ψ ≠ 1 →
        ‖bilinTwist β Y f ψ‖
          ≤ Kβ * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ ((A + 1) + C0)) :
    4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (6 * (Kβ + 448 + 32 * Real.sqrt 26)) * ((X : ℝ) * (Y : ℝ))
          / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
  have hYpos : 0 < Y := by omega
  have hXY4 : (4 : ℝ) ≤ (X : ℝ) * (Y : ℝ) := by nlinarith [hXR, hYR]
  have hXYnn : (0 : ℝ) ≤ (X : ℝ) * (Y : ℝ) := by positivity
  have hL1 : (1 : ℝ) ≤ Real.log ((X : ℝ) * (Y : ℝ)) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hLpos : (0 : ℝ) < Real.log ((X : ℝ) * (Y : ℝ)) := by linarith
  have hsum := mainEnergy_sum_le (A := A + 1) (C0 := C0) (Kβ := Kβ) hD0eq hK h2D0 hD0D
    hYpos α β hα hβ hKβ hLpos hD0hi hβSW
  -- catch-#64: `four_term_scale_le` now takes the decoupled `A+2`-exponent tail cut;
  -- this discharge keeps its landed `L^{C0} ≤ 2·2^{k0}` row and weakens it here
  -- (`L^{A+2} ≤ L^{C0}` from `1 ≤ L`, `A+2 ≤ C0`).
  have hD0lo' : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hL1 hC0) hD0lo
  have hft := four_term_scale_le (A := A) (B := B) (C0 := C0) hA hX2 hY2 h1D hB hC0
    hDscale hK hD0lo' hXsqrt hYsqrt
  set L := Real.log ((X : ℝ) * (Y : ℝ)) with hLdef
  have hLApos : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
  have hLAApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos _
  have hC'nn : (0 : ℝ) ≤ Kβ + 448 + 32 * Real.sqrt 26 := by positivity
  -- Step 1: ∑ ≤ (Kβ + 448 + 32√26) · XY / L^{A+1}.
  have hsum2 : ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ (Kβ + 448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by
    have hcomb : Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)
          + (448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)
        = (Kβ + 448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1) := by ring
    linarith [hsum, hft, hcomb]
  -- Step 2: prefactor `4(1+log D) ≤ 6L`.
  have hlogDnn : (0 : ℝ) ≤ Real.log D := Real.log_nonneg (by exact_mod_cast h1D)
  have hlogD : Real.log D ≤ L / 2 := by
    have hDsqrt : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) := by
      calc (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) / L ^ B := hDscale
        _ ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) / 1 := by
            apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num)
              (Real.one_le_rpow hL1 (by linarith))
        _ = Real.sqrt ((X : ℝ) * (Y : ℝ)) := div_one _
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    calc Real.log D ≤ Real.log (Real.sqrt ((X : ℝ) * (Y : ℝ))) := Real.log_le_log hDpos hDsqrt
      _ = L / 2 := by rw [Real.log_sqrt hXYnn]
  have hpref : 4 * (1 + Real.log D) ≤ 6 * L := by linarith [hlogD, hL1]
  -- Step 3: `L / L^{A+1} = 1 / L^A`.
  have hLdiv : L / L ^ (A + 1) = 1 / L ^ A := by
    rw [div_eq_div_iff hLApos.ne' hLAApos.ne', one_mul]
    have hh := Real.rpow_add hLpos 1 A
    rw [Real.rpow_one] at hh
    rw [← hh, show (1 : ℝ) + A = A + 1 by ring]
  -- Assemble.
  calc 4 * (1 + Real.log D)
          * ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ 4 * (1 + Real.log D)
          * ((Kβ + 448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)) := by
        apply mul_le_mul_of_nonneg_left hsum2
        have : (0 : ℝ) ≤ 1 + Real.log D := by linarith
        positivity
    _ ≤ (6 * L)
          * ((Kβ + 448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)) := by
        apply mul_le_mul_of_nonneg_right hpref
        exact div_nonneg (mul_nonneg hC'nn hXYnn) (le_of_lt hLApos)
    _ = 6 * (Kβ + 448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) * (L / L ^ (A + 1)) := by ring
    _ = 6 * (Kβ + 448 + 32 * Real.sqrt 26) * ((X : ℝ) * (Y : ℝ)) * (1 / L ^ A) := by rw [hLdiv]
    _ = (6 * (Kβ + 448 + 32 * Real.sqrt 26)) * ((X : ℝ) * (Y : ℝ)) / L ^ A := by ring

/-! ## 5. The `hErrSum` α-side error structure (the BDH entry point) -/

open Classical in
/-- **The coprimality-error identity (`hErrSum`'s α-side structure).**  The
imprimitive-vs-primitive difference is exactly the (negated) FULL-`α` twist
**restricted to the non-coprime residues** mod `d`:
```
A_d(χ) − A⋆_f(χ⋆) = − ∑_{m≤X, gcd(m,d)>1} α(m)·χ⋆(m).
```
(Via the fold `bilinTwist_coprimeRestrict_primitive`: on units the two twists agree,
off units `A⋆` keeps `α(m)` while `A_d` drops it.)  This is the exact term the BDH
Möbius `e`-fold `[gcd(m,d)>1] = −∑_{e∣d, e>1, e∣m} μ(e)` acts on to turn the α-side
error into a weighted sum of shifted-scale energies — the remaining `hErrSum` core
(see the FLAG). -/
theorem bilinTwist_sub_primitive_eq {d : ℕ} [NeZero d] (α : ℕ → ℂ) (X : ℕ)
    (χ : DirichletCharacter ℂ d) :
    bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter
      = - ∑ m ∈ (Finset.Icc 1 X).filter (fun m => ¬ IsUnit ((m : ℕ) : ZMod d)),
          α m * χ.primitiveCharacter ((m : ℕ) : ZMod χ.conductor) := by
  have key : ∀ m, coprimeRestrict α d m * χ.primitiveCharacter ((m : ℕ) : ZMod χ.conductor)
          - α m * χ.primitiveCharacter ((m : ℕ) : ZMod χ.conductor)
        = -(if ¬ IsUnit ((m : ℕ) : ZMod d)
            then α m * χ.primitiveCharacter ((m : ℕ) : ZMod χ.conductor) else 0) := by
    intro m; unfold coprimeRestrict; by_cases h : IsUnit ((m : ℕ) : ZMod d) <;> simp [h]
  rw [bilinTwist_coprimeRestrict_primitive α X χ]
  unfold bilinTwist
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun m _ => key m),
    Finset.sum_neg_distrib, Finset.sum_filter]

/-- **The crude α-side `L¹` bound.**  `‖A_d(χ) − A⋆‖ ≤ #{m≤X : gcd(m,d)>1}` (the
count of non-coprime residues).  Direct from `bilinTwist_sub_primitive_eq` +
`‖α‖,‖χ⋆‖ ≤ 1`.  **This is where the honest obstruction bites:** the naive `d`-sum
`∑_{d≤D}(1/φd)·#{m≤X:(m,d)>1}·Y ≈ ∑_{d≤D}(∑_{p∣d}X/p)·Y = XY·∑_{p}(1/p)⌊D/p⌋ ≈ XY·D`
is `(XY)^{3/2}/(log)^B` — **too big by `D`** (the `hErrSum` FLAG).  The fix is the BDH
Möbius `e`-fold, not this crude bound. -/
theorem norm_bilinTwist_sub_primitive_le {d : ℕ} [NeZero d] (α : ℕ → ℂ) (X : ℕ)
    (χ : DirichletCharacter ℂ d) (hα : ∀ m, ‖α m‖ ≤ 1) :
    ‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
      ≤ (((Finset.Icc 1 X).filter (fun m => ¬ IsUnit ((m : ℕ) : ZMod d))).card : ℝ) := by
  rw [bilinTwist_sub_primitive_eq, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ (Finset.Icc 1 X).filter (fun m => ¬ IsUnit ((m : ℕ) : ZMod d)),
          ‖α m * χ.primitiveCharacter ((m : ℕ) : ZMod χ.conductor)‖
      ≤ ∑ _m ∈ (Finset.Icc 1 X).filter (fun m => ¬ IsUnit ((m : ℕ) : ZMod d)), (1 : ℝ) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [norm_mul]
        calc ‖α m‖ * ‖χ.primitiveCharacter ((m : ℕ) : ZMod χ.conductor)‖
            ≤ 1 * 1 :=
              mul_le_mul (hα m) (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
    _ = (((Finset.Icc 1 X).filter (fun m => ¬ IsUnit ((m : ℕ) : ZMod d))).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end Salt.Chen
