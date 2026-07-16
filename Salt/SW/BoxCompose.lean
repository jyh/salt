/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.BoxCount
import Salt.SW.BoxFold

/-!
# The SW rung, node A1 — effective local zero density for `ζ`

Design: `docs/exploration/s2-trackA-design.md`, node A1. This module **composes** the two
landed halves into the registered A1 theorem:

* **`Salt/SW/BoxCount.lean`** (node A1-ab) — the *half*-box count: the zeros of `Zc = (s−1)·ζ`
  in the disk `closedBall (2+t·i) (37/20)` (which contains the half-box `{Re ∈ [1/2,1),
  |Im−t| ≤ 1}`), counted with multiplicity by the divisor finsum, number `≤ C·log(|t|+2)` with
  `C = zetaBoxConst = 11/log(39/37)`.
* **`Salt/SW/BoxFold.lean`** (node A1-c) — the functional-equation fold: *parametric* in a
  half-box count (`hfin`/`hhalf`), the *full*-box count `zBoxCount (zBoxFull t)` (the
  with-multiplicity divisor finsum over `{Re ∈ (0,1), |Im−t| ≤ 1}`) is `≤ 2·C·log(|t|+2)`.

## The three bridge steps

The two halves speak different dialects of "the count": BoxFold counts with `zZeroMult ρ =
(analyticOrderAt ζ ρ).toNat`, BoxCount with the `Zc`-divisor over the disk. Composition is:

1. **Count-spelling bridge** (`zZeroMult_eq_divisor`). On the half-box (so `ρ ≠ 1`, hence the
   pole factor `s−1` is analytic and nonvanishing at `ρ`), `analyticOrderAt Zc ρ =
   analyticOrderAt ζ ρ` (`Zc_order_eq_zeta`, the product rule for `analyticOrderAt`), and the
   box `⊆` the disk (`zBoxHi_subset_disk`), so `zZeroMult ρ = divisor Zc (disk) ρ` there.
2. **Finiteness** (`zBoxHi_finite`, `zBoxFull_finite`). The box zeros are finite: a box `⊆` a
   compact ball, and `IsCompact.inter_riemannZetaZeros_finite`.
3. **The fold** (`zeta_full_box_count`). `BoxFold.zeta_box_count_full` fed `hfin :=
   zBoxHi_finite` and `hhalf := zeta_half_box_count` (the uniform-in-`u` half-box count, from
   steps 1–2 plus `BoxCount.zeta_box_divisor_le`).

## The registered A1

`zeta_local_density` : `∃ C, ∀ t, zBoxCount (zBoxFull t) ≤ C·log(|t|+2)` with `C = 2·zetaBoxConst`
— the first effective *local* zero-density bound for `ζ` in a proof assistant. Its cardinality
face `zeta_local_density_card` bounds any finite set of distinct box zeros.
-/

namespace Salt.SW

open Complex Metric MeromorphicOn Filter
open scoped Topology

/-! ## 1. The count-spelling bridge: `Zc` and `ζ` agree on the box -/

/-- On any point off the pole `s = 1`, `Zc = (s−1)·ζ` has the same vanishing order as `ζ`:
the extra factor `s ↦ s − 1` is analytic and nonzero at `ρ ≠ 1`, so contributes order `0`. -/
lemma Zc_order_eq_zeta {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderAt Zc ρ = analyticOrderAt riemannZeta ρ := by
  have hev : Zc =ᶠ[𝓝 ρ] (fun s => s - 1) * riemannZeta := by
    filter_upwards [eventually_ne_nhds hρ1] with s hs
    simp only [Pi.mul_apply, Zc_eq_of_ne hs]
  rw [analyticOrderAt_congr hev]
  have hg : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := by fun_prop
  have hz : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  have hgne : (fun s : ℂ => s - 1) ρ ≠ 0 := by simpa using sub_ne_zero.mpr hρ1
  rw [analyticOrderAt_mul hg hz, hg.analyticOrderAt_eq_zero.mpr hgne, zero_add]

/-- The half-box `{Re ∈ [1/2,1), |Im−t| ≤ 1}` sits in `closedBall (2+t·i) (37/20)` (farthest
corner `(1/2, t±1)` at distance `√(13/4) ≈ 1.803 < 37/20`), uniformly in `t`. -/
lemma zBoxHi_subset_disk (u : ℝ) :
    zBoxHi u ⊆ closedBall (2 + (u : ℂ) * I) (37 / 20) := by
  rintro ρ ⟨hζ, hlo, hhi, him⟩
  rw [mem_closedBall, dist_eq_norm]
  have hdecomp : ρ - (2 + (u : ℂ) * I)
      = ((ρ.re - 2 : ℝ) : ℂ) + ((ρ.im - u : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im]
  rw [hdecomp, Complex.norm_add_mul_I]
  have hsq : (ρ.re - 2) ^ 2 + (ρ.im - u) ^ 2 ≤ (37 / 20) ^ 2 := by
    nlinarith [abs_le.mp him, hlo, hhi]
  calc Real.sqrt ((ρ.re - 2) ^ 2 + (ρ.im - u) ^ 2)
      ≤ Real.sqrt ((37 / 20) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 37 / 20 := Real.sqrt_sq (by norm_num)

/-- A half-box point is a zero of the entire `Zc` (`Zc ρ = (ρ−1)·ζ ρ` and `ζ ρ = 0`). -/
lemma zBoxHi_Zc_zero {ρ : ℂ} {u : ℝ} (hρ : ρ ∈ zBoxHi u) : Zc ρ = 0 := by
  obtain ⟨hζ, _, hhi, _⟩ := hρ
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
  rw [Zc_eq_of_ne hρ1, hζ, mul_zero]

/-- **The count-spelling bridge.** On the half-box, BoxFold's with-multiplicity summand
`zZeroMult ρ = (analyticOrderAt ζ ρ).toNat` equals BoxCount's `Zc`-divisor over the disk. -/
lemma zZeroMult_eq_divisor {ρ : ℂ} {u : ℝ} (hρ : ρ ∈ zBoxHi u) :
    zZeroMult ρ = ((divisor Zc (closedBall (2 + (u : ℂ) * I) (37 / 20)) ρ : ℤ) : ℝ) := by
  have hρ1 : ρ ≠ 1 := by
    obtain ⟨_, _, hhi, _⟩ := hρ; intro h; rw [h] at hhi; simp at hhi
  have hana : AnalyticOnNhd ℂ Zc (closedBall (2 + (u : ℂ) * I) (37 / 20)) :=
    (Zc_differentiable.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hρU := zBoxHi_subset_disk u hρ
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (Zc_analyticOrderAt_ne_top ρ)
  have hdiv : divisor Zc (closedBall (2 + (u : ℂ) * I) (37 / 20)) ρ = (k : ℤ) := by
    rw [hana.divisor_apply hρU, ← hk]; simp
  have hζk : analyticOrderAt riemannZeta ρ = (k : ℕ∞) := by
    rw [← Zc_order_eq_zeta hρ1, ← hk]
  simp only [zZeroMult, hζk, hdiv, ENat.toNat_coe, Int.cast_natCast]

/-- A zero of `ζ` on the open strip contributes multiplicity `≥ 1`: its analytic order is
nonzero (`ζ ρ = 0`) and finite (`≠ ⊤`, via `Zc_analyticOrderAt_ne_top` and `Zc_order_eq_zeta`),
so `(analyticOrderAt ζ ρ).toNat ≥ 1`. Used by the cardinality corollary. -/
lemma one_le_zZeroMult {ρ : ℂ} (_h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hζ : riemannZeta ρ = 0) :
    (1 : ℝ) ≤ zZeroMult ρ := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hana : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := hana.analyticOrderAt_ne_zero.mpr hζ
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← Zc_order_eq_zeta hρ1]; exact Zc_analyticOrderAt_ne_top ρ
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hnetop
  have hk0 : k ≠ 0 := by rintro rfl; exact hne0 (by rw [← hk]; simp)
  simp only [zZeroMult, ← hk, ENat.toNat_coe]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0

/-! ## 2. Finiteness of the box zero-sets -/

/-- The half-box zeros are finite: they lie in a compact ball, and the zeros of `ζ` in any
compact set are finite (`IsCompact.inter_riemannZetaZeros_finite`). -/
lemma zBoxHi_finite (u : ℝ) : (zBoxHi u).Finite := by
  apply ((isCompact_closedBall (2 + (u : ℂ) * I) (37 / 20)).inter_riemannZetaZeros_finite).subset
  intro ρ hρ
  exact ⟨zBoxHi_subset_disk u hρ, mem_riemannZetaZeros.mpr hρ.1⟩

/-- The full-box zeros are finite: the box `{Re ∈ (0,1), |Im−t| ≤ 1}` lies in
`closedBall (2+t·i) 3` (farthest corner `(0, t±1)` at distance `√5 ≈ 2.236 < 3`). -/
lemma zBoxFull_finite (t : ℝ) : (zBoxFull t).Finite := by
  apply ((isCompact_closedBall (2 + (t : ℂ) * I) 3).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨hζ, h0, h1, him⟩
  refine ⟨?_, mem_riemannZetaZeros.mpr hζ⟩
  rw [mem_closedBall, dist_eq_norm]
  have hdecomp : ρ - (2 + (t : ℂ) * I)
      = ((ρ.re - 2 : ℝ) : ℂ) + ((ρ.im - t : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im]
  rw [hdecomp, Complex.norm_add_mul_I]
  have hsq : (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 ≤ (3 : ℝ) ^ 2 := by
    nlinarith [abs_le.mp him, h0, h1]
  calc Real.sqrt ((ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2)
      ≤ Real.sqrt ((3 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 3 := Real.sqrt_sq (by norm_num)

/-! ## 3. The with-multiplicity half-box count (the `hhalf` hypothesis) -/

/-- **The with-multiplicity half-box count.** BoxFold's `zBoxCount (zBoxHi u)` is bounded by
BoxCount's disk divisor bound: each box zero's `zZeroMult` equals its `Zc`-divisor
(`zZeroMult_eq_divisor`), the box injects into the (nonneg) disk divisor support, and the total
is `≤ zetaBoxConst·log(|u|+2)` by `zeta_box_divisor_le`. -/
theorem zeta_half_box_count (u : ℝ) :
    zBoxCount (zBoxHi u) ≤ zetaBoxConst * Real.log (|u| + 2) := by
  set U : Set ℂ := closedBall (2 + (u : ℂ) * I) (37 / 20) with hU
  have hana : AnalyticOnNhd ℂ Zc U :=
    (Zc_differentiable.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hfin : (zBoxHi u).Finite := zBoxHi_finite u
  have hsupp : (Function.support fun ρ => divisor Zc U ρ).Finite :=
    (divisor Zc U).finiteSupport (by rw [hU]; exact isCompact_closedBall _ _)
  have hsub : hfin.toFinset ⊆ hsupp.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have h1 := one_le_divisor_Zc hana (by rw [hU]; exact zBoxHi_subset_disk u hρ)
      (zBoxHi_Zc_zero hρ)
    omega
  have hfs : (∑ᶠ ρ, divisor Zc U ρ) = ∑ ρ ∈ hsupp.toFinset, divisor Zc U ρ :=
    finsum_eq_finsetSum_of_support_subset _ (by rw [Set.Finite.coe_toFinset])
  have hcast : ∑ ρ ∈ hsupp.toFinset, ((divisor Zc U ρ : ℤ) : ℝ)
      = ((∑ᶠ ρ, divisor Zc U ρ : ℤ) : ℝ) := by rw [hfs]; push_cast; ring
  calc zBoxCount (zBoxHi u)
      = ∑ ρ ∈ hfin.toFinset, zZeroMult ρ := by
        simp only [zBoxCount]; rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    _ = ∑ ρ ∈ hfin.toFinset, ((divisor Zc U ρ : ℤ) : ℝ) := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [Set.Finite.mem_toFinset] at hρ
        rw [hU]; exact zZeroMult_eq_divisor hρ
    _ ≤ ∑ ρ ∈ hsupp.toFinset, ((divisor Zc U ρ : ℤ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ρ _ _ => by exact_mod_cast hana.divisor_nonneg ρ)
    _ = ((∑ᶠ ρ, divisor Zc U ρ : ℤ) : ℝ) := hcast
    _ ≤ zetaBoxConst * Real.log (|u| + 2) := by
        have hb := zeta_box_divisor_le u; rw [← hU] at hb; exact hb

/-! ## 4. The fold — the registered A1 theorem -/

/-- **The full strip-box count (A1, explicit `C`).** Folding the half-box count
(`zeta_half_box_count`) with `BoxFold.zeta_box_count_full`: the with-multiplicity zero count of
`ζ` in the full box `{Re ∈ (0,1), |Im−t| ≤ 1}` is `≤ 2·zetaBoxConst·log(|t|+2)`. -/
theorem zeta_full_box_count (t : ℝ) :
    zBoxCount (zBoxFull t) ≤ 2 * zetaBoxConst * Real.log (|t| + 2) :=
  zeta_box_count_full zBoxHi_finite zeta_half_box_count t

/-- **The registered A1 theorem — effective local zero density for `ζ`.** There is a constant
`C` (here `2·zetaBoxConst = 22/log(39/37)`) with, for every ordinate `t`, the with-multiplicity
zero count of `riemannZeta` in the box `{Re ∈ (0,1), |Im−t| ≤ 1}` at most `C·log(|t|+2)`. The
first effective local zero-density bound for `ζ` in a proof assistant. -/
theorem zeta_local_density :
    ∃ C : ℝ, ∀ t : ℝ, zBoxCount (zBoxFull t) ≤ C * Real.log (|t| + 2) :=
  ⟨2 * zetaBoxConst, zeta_full_box_count⟩

/-- **The cardinality corollary of A1.** Any finite set `S` of distinct zeros of `ζ` in the box
`{Re ∈ (0,1), |Im−t| ≤ 1}` has `#S ≤ C·log(|t|+2)`, `C = 2·zetaBoxConst` — each zero contributes
multiplicity `≥ 1` to the with-multiplicity count bounded by `zeta_full_box_count`. -/
theorem zeta_local_density_card :
    ∃ C : ℝ, ∀ (t : ℝ) (S : Finset ℂ),
      (∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1) →
      (S.card : ℝ) ≤ C * Real.log (|t| + 2) := by
  refine ⟨2 * zetaBoxConst, fun t S hS => ?_⟩
  have hfull := zBoxFull_finite t
  have hSsub : S ⊆ hfull.toFinset := by
    intro ρ hρ; rw [Set.Finite.mem_toFinset]; exact hS ρ hρ
  refine le_trans ?_ (zeta_full_box_count t)
  simp only [zBoxCount]; rw [finsum_mem_eq_finite_toFinset_sum _ hfull]
  calc (S.card : ℝ) = ∑ _ρ ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ ρ ∈ S, zZeroMult ρ := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        obtain ⟨hζ, h0, h1, _⟩ := hS ρ hρ
        exact one_le_zZeroMult h0 h1 hζ
    _ ≤ ∑ ρ ∈ hfull.toFinset, zZeroMult ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun ρ _ _ => zZeroMult_nonneg ρ)

end Salt.SW
