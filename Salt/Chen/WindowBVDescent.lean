/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WindowBV
import Salt.Chen.DyadicDvd

/-!
# WBV2 — the cutoff (window) descent port

Design: `docs/blueprints/flags.md`, the `2026-07-14 WBV1` entry (the cutoff carrier layer)
and the `2026-07-13 C54-RECON … FROZEN` freeze (route (i), the one-sided cutoff carrier).
This is the second WBV node: the *windowed* analogue of the landed large-conductor
dyadic-in-conductor descent (`Salt.Chen.EnergyClose` §2), obtained by riding the sharp
cutoff `m·n ≤ T` through the block/dyadic machinery at the `cutoffPrimEnergy` interface.

The port's whole premise (recon-verified in WBV1): `Salt.Chen.energy_shell_cutoff` has RHS
= the existing `Salt.Chen.shellBound X Y Q` **VERBATIM** (the windowed twist IS the shell's
inner cutoff character sum, so no `bilin_cutoff_eq` re-factoring intervenes).  Because the
RHS shape is identical to the landed `energy_shell`, the entire large-conductor descent
(`block_energy_le'`, `dyadic_large_reduction`, `geom_shell_sum_le`) ports near-verbatim: the
ONLY change is `bilinPrimEnergy α β X Y f ↦ cutoffPrimEnergy α β X Y T f` and consuming
`energy_shell_cutoff` in place of `energy_shell` (the geometric sum is cutoff-agnostic —
it only touches `shellBound`).

## What this file lands (all FULL, sorry-free)

1. `block_energy_le_cutoff` — the per-`[a,b]`-block bound at `cutoffPrimEnergy` (mirror of
   `block_energy_le'`; `energy_shell_cutoff` in place of `energy_shell`).
2. `dyadic_large_reduction_cutoff` — the dyadic block decomposition of
   `∑_{D0<f≤D} (1/φf)·cutoffPrimEnergy` (mirror of `dyadic_large_reduction`, consuming
   `block_energy_le_cutoff`).
3. `geom_shell_sum_le_cutoff` — the geometric block-sum with the four terms explicit.  The
   geometric sum touches only `shellBound` (no energy), so this is **cutoff-agnostic**: it is
   the landed `geom_shell_sum_le`, restated under a parallel name so WBV4's assembly mirrors
   the `dvd` chain's `geom_shell_sum_le_dvd`.
4. `dyadic_energy_le_cutoff` — the RAW composed four-term (mirror of
   `Salt.Chen.efold_large_fourterm` / `Salt.Chen.dyadic_energy_le_dvd`):
   `dyadic_large_reduction_cutoff` ∘ `geom_shell_sum_le_cutoff`, diagonal `4·2^{K+1}` kept
   **explicit and rational**, **no**
   level cut `D ≤ √(XY)/(log)^B` absorbed (the catch-#44 lesson: that cut dies at the window's
   shifted `T`-cutoffs).  This is the large-conductor input WBV4 combines with WBV3's small side;
   the level deficit is applied to the diagonal afterwards, per window.

## The δ-restricted co-extension (item 5)

`Salt.BV.bilinear_LS_shell_dvd` carries BOTH the sharp cutoff `Y` (native, as in the
un-restricted shell) AND the `δ ∣ q` modulus filter with the sharpened `Q²/δ` diagonal.  The
two extensions — the window (skip `bilin_cutoff_eq`) and the δ-restriction (`shellBoundDvd`) —
are orthogonal and compose mechanically.  So the δ-fibered `cutoffPrimEnergy` descent is also
provided, in case WBV4's windowed imprimitivity handling reintroduces a gcd/`lcm`-fibered
density (as the landed α-side `hlarge` e-fold did — `Salt.Chen.AlphaClose`):

* `energy_shell_cutoff_dvd` — the δ-shell at `cutoffPrimEnergy` (mirror of `energy_shell_dvd`,
  consuming `bilinear_LS_shell_dvd` at the free cutoff `T`, skipping the re-factoring).
* `block_energy_le_cutoff_dvd`, `dyadic_large_reduction_cutoff_dvd` — the δ-restricted block /
  dyadic mirrors (`shellBoundDvd` diagonal; reuse the landed `geom_shell_sum_le_dvd`).
* `dyadic_energy_le_cutoff_dvd` — the raw δ+cutoff four-term with the `Q²/δ` diagonal.

**δ-compatibility finding** (see the closing remark): the landed β-side MAIN-energy path
(`Salt.Chen.mainEnergy_sum_le` / `general_BV_alpha_final`'s `hMainEnergy` slot) consumes the
descent in PLAIN form (`∑_{f∈Icc 2 D}`, no δ); the δ-fibered form is consumed ONLY by the
FACTORED α-side error e-fold (`hlarge`, `Salt.Chen.efold_large_reduce`).  The window's
`cutoffTwist` does **not** factor and `apDiscBilinCutoff_orthogonality` is EXACT, so the plain
form (items 1–4) is what mirrors the window's main descent; the δ-variant is a de-risking
co-extension for WBV4, not a requirement of the main path.

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The per-block cutoff consumption (mirror of `block_energy_le'`) -/

/-- **Per-block cutoff consumption (mirror of `block_energy_le'`).**  On a block `[a, b]`
(`1 ≤ a`, `2 ≤ b`), the `(1/φf)`-weight is `≤ (1/a)·(f/φf)`, so the windowed block energy is
`≤ (1/a)·shellBound X Y b` (extend to `[1, b]`, consume `energy_shell_cutoff` at `Q = b`).
The cutoff `T` threads inertly through `cutoffPrimEnergy`; the RHS is the SAME `shellBound` the
landed lemma produces, so the proof is byte-identical to `block_energy_le'` up to the
`bilinPrimEnergy ↦ cutoffPrimEnergy` / `energy_shell ↦ energy_shell_cutoff` substitution.  The
dyadic reduction consumes this at `a = 2^k`, `b = 2^{k+1}`. -/
theorem block_energy_le_cutoff {X Y T a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc a b, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ (1 / (a : ℝ)) * shellBound X Y b := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hstep : ∀ f ∈ Finset.Icc a b,
      (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
        ≤ (1 / (a : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf1 : 1 ≤ f := by omega
    have haf : (a : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf.1
    have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hEnn : 0 ≤ cutoffPrimEnergy α β X Y T f := cutoffPrimEnergy_nonneg _ _ _ _ _ _
    have hwle : (1 / (f.totient : ℝ)) ≤ (1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ)) := by
      have hrw : (1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ))
          = (f : ℝ) / ((a : ℝ) * (f.totient : ℝ)) := by field_simp
      rw [hrw, div_le_div_iff₀ hφpos (mul_pos haR hφpos)]
      nlinarith [haf, hφpos.le]
    calc (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
        ≤ ((1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ))) * cutoffPrimEnergy α β X Y T f :=
          mul_le_mul_of_nonneg_right hwle hEnn
      _ = (1 / (a : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : Finset.Icc a b ⊆ Finset.Icc 1 b := by
    intro f hf; rw [Finset.mem_Icc] at hf ⊢; omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => ?_)) ?_
  · exact mul_nonneg (by positivity) (cutoffPrimEnergy_nonneg _ _ _ _ _ _)
  · exact energy_shell_cutoff hb hY α β hα hβ

/-! ## 2. The dyadic large-conductor cutoff reduction (mirror of `dyadic_large_reduction`) -/

/-- **Dyadic large-conductor cutoff reduction (mirror of `dyadic_large_reduction`).**  For
`D0 = 2^{k0}` and `K = ⌊log₂ D⌋`, the windowed large-conductor energy
`∑_{D0 < f ≤ D} (1/φf)·cutoffPrimEnergy α β X Y T f` is bounded by the geometric block sum
`∑_{k=k0}^{K} (1/2^k)·shellBound X Y (2^{k+1})` via the dyadic fibration `f ↦ ⌊log₂ f⌋`
(fibers land in `Icc k0 K`, each fiber sits in the block `[2^k, 2^{k+1}]`), consuming
`block_energy_le_cutoff`.  Only the energy interface changed from `dyadic_large_reduction`. -/
theorem dyadic_large_reduction_cutoff {X Y T D0 D k0 K : ℕ} (hD0 : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc (D0 + 1) D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ ∑ k ∈ Finset.Icc k0 K, (1 / (2 ^ k : ℝ)) * shellBound X Y (2 ^ (k + 1)) := by
  have hmaps : ∀ f ∈ Finset.Icc (D0 + 1) D, Nat.log 2 f ∈ Finset.Icc k0 K := by
    intro f hf
    rw [Finset.mem_Icc] at hf ⊢
    refine ⟨?_, ?_⟩
    · apply Nat.le_log_of_pow_le (by norm_num)
      rw [← hD0]; omega
    · rw [hK]; exact Nat.log_mono_right hf.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun f => (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f)]
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
          (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ ∑ f ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1)),
          (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hfibsub (fun f _ _ => ?_)
        exact mul_nonneg (by positivity) (cutoffPrimEnergy_nonneg _ _ _ _ _ _)
    _ ≤ (1 / (2 ^ k : ℝ)) * shellBound X Y (2 ^ (k + 1)) := by
        have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have h2k1 : 2 ≤ 2 ^ (k + 1) := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
        have hbk := block_energy_le_cutoff (X := X) (Y := Y) (T := T) (a := 2 ^ k)
          (b := 2 ^ (k + 1)) h2k h2k1 hY α β hα hβ
        rwa [hcast] at hbk

/-! ## 3. The dyadic geometric sum (cutoff-agnostic restatement of `geom_shell_sum_le`) -/

/-- **Dyadic geometric cutoff sum (cutoff-agnostic; = `geom_shell_sum_le`).**  The geometric
block sum `∑_{k=k0}^{K} (1/2^k)·shellBound X Y (2^{k+1})` is bounded by the classical four-term
endgame in explicit form.  This lemma touches ONLY `shellBound` (no energy at all), so it is
identical to the landed `geom_shell_sum_le`; it is restated under a WBV-parallel name so the
window assembly (WBV4) mirrors the `dvd` chain's `geom_shell_sum_le_dvd`. -/
theorem geom_shell_sum_le_cutoff {X Y k0 K : ℕ} (hY : 0 < Y) :
    ∑ k ∈ Finset.Icc k0 K, (1 / (2 ^ k : ℝ)) * shellBound X Y (2 ^ (k + 1))
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ (K + 1)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1))
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
            + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) :=
  geom_shell_sum_le hY

/-! ## 4. The raw composed cutoff four-term (the shape WBV4 consumes) -/

/-- **WBV2 (FULL) — the raw windowed dyadic energy four-term.**  Composing
`dyadic_large_reduction_cutoff` with `geom_shell_sum_le_cutoff`: the windowed large-conductor
block energy is bounded by the explicit **four-term** expression at the given scale `(X, Y)`,
`D0 = 2^{k0}`, `K = ⌊log₂ D⌋`, with the diagonal `4·2^{K+1}` term **kept explicit and rational**
— **no** level cut `D ≤ √(XY)/(log)^B` absorbed (catch #44: the cut dies at the window's shifted
`T`-cutoffs).  This is the exact analogue of `Salt.Chen.efold_large_fourterm`'s
`dyadic_large_reduction + geom_shell_sum_le` composition (and of `dyadic_energy_le_dvd`), at
`cutoffPrimEnergy` — the large-conductor input WBV4 combines with WBV3's small-conductor side;
the level deficit is applied to the explicit diagonal afterwards, per window.

The four-term shape (exactly the RHS below):
```
∑_{D0<f≤D} (1/φf)·cutoffPrimEnergy α β X Y T f
  ≤ 2(1+log Y)√X√Y · ( 4·2^{K+1}                          -- main   (~ D)
                       + 2(K+1)·√(13(X+1))                 -- crossX (~ √X)
                       + 2(K+1)·√(13(Y+1))                 -- crossY (~ √Y)
                       + √(13(X+1))·√(13(Y+1))·2/2^{k0} ). -- tail   (~ XY/D0)
```
-/
theorem dyadic_energy_le_cutoff {X Y T D0 D k0 K : ℕ} (hD0 : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc (D0 + 1) D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ (K + 1)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1))
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
            + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) :=
  le_trans (dyadic_large_reduction_cutoff hD0 hK hY α β hα hβ) (geom_shell_sum_le_cutoff hY)

/-! ## 5. The δ-restricted co-extension (window + δ-fibered, orthogonal composition) -/

open Classical in
/-- **The δ-restricted windowed twist shell (mirror of `bilinTwist_energy_le_dvd`, cutoff KEPT).**
`bilinear_LS_shell_dvd` carries the sharp cutoff `Y := T` natively AND the `δ ∣ q` filter with the
sharpened `Q²/δ` diagonal, so — exactly as WBV1's `cutoffTwist_energy_le` skips `bilin_cutoff_eq`
— the windowed twist IS the shell's inner cutoff character sum, and no re-factoring intervenes:
```
∑_{q≤Q, δ∣q} (q/φq) ∑_{χ prim mod q} ‖cutoffTwist α β X Y T q χ‖ ≤ shellBoundDvd X Y Q δ.
```
The `L²` masses `∑‖α‖², ∑‖β‖²` are bounded by `X, Y` (verbatim WBV1). -/
theorem cutoffTwist_energy_le_dvd {X Y T Q δ : ℕ} (hδ1 : 1 ≤ δ) (hQ : 2 ≤ Q) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q), ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖cutoffTwist α β X Y T q χ‖
      ≤ shellBoundDvd X Y Q δ := by
  classical
  simp only [cutoffTwist, shellBoundDvd]
  refine le_trans (bilinear_LS_shell_dvd (M := X) (H := Y) hδ1 hQ hY α β T) ?_
  have hmassα : Real.sqrt (∑ m ∈ Finset.Icc 1 X, ‖α m‖ ^ 2) ≤ Real.sqrt (X : ℝ) := by
    apply Real.sqrt_le_sqrt
    calc ∑ m ∈ Finset.Icc 1 X, ‖α m‖ ^ 2 ≤ ∑ _m ∈ Finset.Icc 1 X, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun m _ => ?_); nlinarith [hα m, norm_nonneg (α m)]
      _ = (X : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hmassβ : Real.sqrt (∑ n ∈ Finset.Icc 1 Y, ‖β n‖ ^ 2) ≤ Real.sqrt (Y : ℝ) := by
    apply Real.sqrt_le_sqrt
    calc ∑ n ∈ Finset.Icc 1 Y, ‖β n‖ ^ 2 ≤ ∑ _n ∈ Finset.Icc 1 Y, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun n _ => ?_); nlinarith [hβ n, norm_nonneg (β n)]
      _ = (Y : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have h1logY : (0 : ℝ) ≤ 1 + Real.log Y :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ Y by exact_mod_cast hY)]
  set P : ℝ := 2 * (1 + Real.log Y)
      * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((X : ℝ) + 1))
      * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((Y : ℝ) + 1)) with hP_def
  have hP : 0 ≤ P := by
    rw [hP_def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1logY)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine mul_le_mul ?_ hmassβ (Real.sqrt_nonneg _) (mul_nonneg hP (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_left hmassα hP

open Classical in
/-- **The δ-restricted `cutoffPrimEnergy` shell (mirror of `energy_shell_dvd`).**  Restatement of
`cutoffTwist_energy_le_dvd` at `cutoffPrimEnergy` (a single norm per character, so — unlike
`energy_shell_dvd` — no `norm_mul` bridge is needed; `cutoffPrimEnergy` IS the ψ-sum by def):
```
∑_{f≤Q, δ∣f} (f/φf)·cutoffPrimEnergy α β X Y T f ≤ shellBoundDvd X Y Q δ.
```
This is the missing analytic input the window's δ-fibered assembly (if WBV4 needs it) consumes. -/
theorem energy_shell_cutoff_dvd {X Y T Q δ : ℕ} (hδ1 : 1 ≤ δ) (hQ : 2 ≤ Q) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q),
        ((f : ℝ) / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ shellBoundDvd X Y Q δ := by
  refine le_trans (le_of_eq ?_) (cutoffTwist_energy_le_dvd (X := X) (T := T) hδ1 hQ hY α β hα hβ)
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp only [cutoffPrimEnergy]

/-- **δ per-block cutoff consumption (mirror of `block_energy_le_dvd`).**  The `δ`+cutoff copy of
`block_energy_le_cutoff`: `energy_shell_cutoff_dvd` in place of `energy_shell_cutoff`, the
`δ ∣ f`-filtered block extended to `(Icc 1 b).filter (δ∣·)`. -/
theorem block_energy_le_cutoff_dvd {X Y T a b δ : ℕ} (hδ1 : 1 ≤ δ) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (hY : 0 < Y) (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc a b).filter (fun f => δ ∣ f),
        (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ (1 / (a : ℝ)) * shellBoundDvd X Y b δ := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hstep : ∀ f ∈ (Finset.Icc a b).filter (fun f => δ ∣ f),
      (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
        ≤ (1 / (a : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_Icc] at hf
    have hf1 : 1 ≤ f := by omega
    have haf : (a : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf.1.1
    have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hEnn : 0 ≤ cutoffPrimEnergy α β X Y T f := cutoffPrimEnergy_nonneg _ _ _ _ _ _
    have hwle : (1 / (f.totient : ℝ)) ≤ (1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ)) := by
      have hrw : (1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ))
          = (f : ℝ) / ((a : ℝ) * (f.totient : ℝ)) := by field_simp
      rw [hrw, div_le_div_iff₀ hφpos (mul_pos haR hφpos)]
      nlinarith [haf, hφpos.le]
    calc (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
        ≤ ((1 / (a : ℝ)) * ((f : ℝ) / (f.totient : ℝ))) * cutoffPrimEnergy α β X Y T f :=
          mul_le_mul_of_nonneg_right hwle hEnn
      _ = (1 / (a : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : (Finset.Icc a b).filter (fun f => δ ∣ f)
      ⊆ (Finset.Icc 1 b).filter (fun f => δ ∣ f) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_Icc] at hf ⊢
    exact ⟨⟨by omega, hf.1.2⟩, hf.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => ?_)) ?_
  · exact mul_nonneg (by positivity) (cutoffPrimEnergy_nonneg _ _ _ _ _ _)
  · exact energy_shell_cutoff_dvd hδ1 hb hY α β hα hβ

/-- **δ dyadic large-conductor cutoff reduction (mirror of `dyadic_large_reduction_dvd`).**  The
`δ`+cutoff copy of `dyadic_large_reduction_cutoff`, consuming `block_energy_le_cutoff_dvd`; only
the `δ ∣ f` modulus filter threads through the fibration `f ↦ ⌊log₂ f⌋`. -/
theorem dyadic_large_reduction_cutoff_dvd {X Y T D0 D δ k0 K : ℕ} (hδ1 : 1 ≤ δ) (hD0 : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => δ ∣ f),
        (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
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
        (fun f => (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f)]
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
          (fun f => Nat.log 2 f = k), (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ ∑ f ∈ (Finset.Icc (2 ^ k) (2 ^ (k + 1))).filter (fun f => δ ∣ f),
          (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hfibsub (fun f _ _ => ?_)
        exact mul_nonneg (by positivity) (cutoffPrimEnergy_nonneg _ _ _ _ _ _)
    _ ≤ (1 / (2 ^ k : ℝ)) * shellBoundDvd X Y (2 ^ (k + 1)) δ := by
        have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have h2k1 : 2 ≤ 2 ^ (k + 1) := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
        have hbk := block_energy_le_cutoff_dvd (X := X) (Y := Y) (T := T) (a := 2 ^ k)
          (b := 2 ^ (k + 1)) (δ := δ) hδ1 h2k h2k1 hY α β hα hβ
        rwa [hcast] at hbk

/-- **WBV2 δ-variant (FULL) — the raw δ+cutoff dyadic energy four-term.**  Composing
`dyadic_large_reduction_cutoff_dvd` with the landed `geom_shell_sum_le_dvd` (which is
cutoff-agnostic — it touches only `shellBoundDvd`): the δ-restricted windowed large-conductor
block energy is bounded by the explicit four-term with the `Q²/δ` diagonal.  The two extensions
(the window's kept cutoff and the δ-restriction) compose orthogonally; the RHS is the
`dyadic_energy_le_dvd` four-term at `cutoffPrimEnergy`.  No level cut is absorbed (catch #44). -/
theorem dyadic_energy_le_cutoff_dvd {X Y T D0 D δ k0 K : ℕ} (hδ1 : 1 ≤ δ) (hD0 : D0 = 2 ^ k0)
    (hK : K = Nat.log 2 D) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => δ ∣ f),
        (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
          * (4 * (2 : ℝ) ^ (K + 1) / (δ : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1)) / Real.sqrt (δ : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (δ : ℝ)
            + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) :=
  le_trans (dyadic_large_reduction_cutoff_dvd hδ1 hD0 hK hY α β hα hβ)
    (geom_shell_sum_le_dvd hδ1 hY)

end Salt.Chen
