/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.EnergyClose
import Salt.BV.BilinearLSDvd

/-!
# Large sieve track, node PE3c-2 (Chen side): the δ-restricted `bilinPrimEnergy` shell

Design: `docs/blueprints/flags.md`, entries `2026-07-13 PE3c RECON` / `PE3c-1`;
the target shape is the C3c″ FLAG of `Salt/Chen/AlphaSide.lean` (lines 87–89):
`∑_{f ≤ Q, δ∣f} (f/φf)·bilinPrimEnergy ≤ [shell with the Q²/δ diagonal]`.

This file is the exact `δ`-copy of `Salt.Chen.energy_shell` (`Salt/Chen/EnergyClose.lean`),
built on `Salt.BV.bilinear_LS_shell_dvd` (`Salt/BV/BilinearLSDvd.lean`) exactly as
`energy_shell` is built on `Salt.BV.bilinear_LS_shell` via the intermediate
`Salt.Chen.bilinTwist_energy_le`.  The two steps:

* `bilinTwist_energy_le_dvd` — the `bilinTwist`-form δ-shell (mirror of
  `bilinTwist_energy_le`): the sharp cutoff `X·Y` makes the shell's bilinear
  character sum exactly `A(χ)·B(χ)`, the `L²` masses are `≤ X, Y`.
* `energy_shell_dvd` — the `bilinPrimEnergy` restatement (mirror of `energy_shell`):
  `bilinPrimEnergy = ∑_ψ ‖A‖·‖B‖` matches the shell's `∑_ψ ‖A·B‖` term-by-term.

The frozen shell constant is `shellBoundDvd X Y Q δ := 2(1+log Y)·√(Q²/δ+13(X+1))·
√(Q²/δ+13(Y+1))·√X·√Y` — the `δ`-copy of `Salt.Chen.shellBound`.  The `δ = 1` case
is NOT defeq to `shellBound` (it carries `Q²/((1:ℕ):ℝ)`, not `Q²`), so a comparison
lemma `shellBoundDvd_one` is provided; the `δ = 1` `example` recovers `energy_shell`.

The private helper `bilin_cutoff_eq` of `Salt/Chen/GeneralBV.lean` is reproved here
(identical proof) as it is not exported.

Only `[propext, Classical.choice, Quot.sound]` are used (via `bilinear_LS_shell_dvd`).

**Wiring.**  Add to `Salt/Chen/All.lean` next to the other bilinear-energy modules
(after `import Salt.Chen.EnergyClose`).
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 0. The vacuous-cutoff identity (reproof of `GeneralBV`'s private lemma) -/

/-- With the cutoff taken at `X·Y` the sharp-cutoff bilinear character sum is
vacuously unrestricted and equals the split product `A(χ)·B(χ)`.  Reproof of the
private `Salt.Chen.bilin_cutoff_eq`. -/
private lemma bilin_cutoff_eq' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (α β : ℕ → ℂ) (X Y : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ X * Y),
        α m * β n * χ ((m * n : ℕ) : ZMod q))
      = bilinTwist α X q χ * bilinTwist β Y q χ := by
  have hstep : (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ X * Y),
        α m * β n * χ ((m * n : ℕ) : ZMod q))
      = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
          α m * β n * χ ((m * n : ℕ) : ZMod q) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.filter_true_of_mem
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact Nat.mul_le_mul hm.2 hn.2
  rw [hstep]
  unfold bilinTwist
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Salt.LS.chi_cast_mul]; ring

/-! ## 1. The `bilinTwist`-form δ-shell -/

open Classical in
/-- **δ-restricted bilinear large-sieve energy (mirror of `bilinTwist_energy_le`).**
For `1 ≤ δ`, restricting the modulus sum to multiples of `δ` sharpens the frozen
`√(Q²+13·)` factors to `√(Q²/δ+13·)`:
```
∑_{q≤Q, δ∣q} (q/φq) ∑_{χ prim mod q} ‖A(χ)·B(χ)‖
  ≤ 2(1+log Y)·√(Q²/δ+13(X+1))·√(Q²/δ+13(Y+1))·√X·√Y.
```
Consumes `Salt.BV.bilinear_LS_shell_dvd` at the vacuous cutoff `X·Y` (so the shell's
bilinear character sum is exactly `A(χ)·B(χ)` by `bilin_cutoff_eq'`), the `L²` masses
`∑‖α‖², ∑‖β‖²` bounded by `X, Y`. -/
theorem bilinTwist_energy_le_dvd {X Y Q δ : ℕ} (hδ1 : 1 ≤ δ) (hQ : 2 ≤ Q) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q), ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖bilinTwist α X q χ * bilinTwist β Y q χ‖
      ≤ 2 * (1 + Real.log Y)
          * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((X : ℝ) + 1))
          * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((Y : ℝ) + 1))
          * Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ) := by
  classical
  -- Rewrite the LHS into the shell's sharp-cutoff form.
  have hrw : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q), ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖bilinTwist α X q χ * bilinTwist β Y q χ‖
      = ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q), ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ X * Y),
              α m * β n * χ ((m * n : ℕ) : ZMod q)‖ := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    have hq1 : 1 ≤ q := hq.1.1
    haveI : NeZero q := ⟨by omega⟩
    congr 1
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [bilin_cutoff_eq' χ α β X Y]
  rw [hrw]
  refine le_trans (bilinear_LS_shell_dvd hδ1 hQ hY α β (X * Y)) ?_
  -- The `L²` masses are ≤ X, Y.
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
  -- Chain the two mass replacements (associativity: `P * √mass_α * √mass_β`).
  calc P * Real.sqrt (∑ m ∈ Finset.Icc 1 X, ‖α m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 Y, ‖β n‖ ^ 2)
      ≤ P * Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ) := by
        apply mul_le_mul _ hmassβ (Real.sqrt_nonneg _) (mul_nonneg hP (Real.sqrt_nonneg _))
        exact mul_le_mul_of_nonneg_left hmassα hP

/-! ## 2. The `bilinPrimEnergy` δ-shell -/

/-- The δ-restricted frozen shell bound `2(1+log Y)·√(Q²/δ+13(X+1))·√(Q²/δ+13(Y+1))·
√X·√Y` (the `δ`-copy of `Salt.Chen.shellBound`; the RHS of `bilinTwist_energy_le_dvd`). -/
noncomputable def shellBoundDvd (X Y Q δ : ℕ) : ℝ :=
  2 * (1 + Real.log Y)
    * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((X : ℝ) + 1))
    * Real.sqrt ((Q : ℝ) ^ 2 / δ + 13 * ((Y : ℝ) + 1))
    * Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ)

lemma shellBoundDvd_nonneg {X Y Q δ : ℕ} (hY : 0 < Y) : 0 ≤ shellBoundDvd X Y Q δ := by
  unfold shellBoundDvd
  have h1logY : (0 : ℝ) ≤ 1 + Real.log Y :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ Y by exact_mod_cast hY)]
  positivity

/-- **The δ = 1 comparison** — `shellBoundDvd X Y Q 1 = shellBound X Y Q` (the `Q²/1`
diagonal collapses to `Q²`).  The `δ = 1` shell is not defeq-compatible with the
un-restricted `shellBound`, so this bridges the two. -/
lemma shellBoundDvd_one (X Y Q : ℕ) : shellBoundDvd X Y Q 1 = shellBound X Y Q := by
  unfold shellBoundDvd shellBound
  simp only [Nat.cast_one, div_one]

/-- **PE3c-2 (Chen side) — the `bilinPrimEnergy` δ-shell (mirror of `energy_shell`).**
For `‖α‖,‖β‖ ≤ 1` and `1 ≤ δ`, the `(f/φf)`-weighted primitive block energy summed
over conductors `f ≤ Q` divisible by `δ` obeys the balanced shell bound with the
sharpened `Q²/δ` diagonal:
```
∑_{f≤Q, δ∣f} (f/φf)·bilinPrimEnergy α β X Y f ≤ shellBoundDvd X Y Q δ.
```
This is exactly the missing analytic input flagged in `Salt/Chen/AlphaSide.lean` (the
C3c″ FLAG): the `δ`-restricted / gcd-weighted large-sieve mean value.
`bilinPrimEnergy = ∑_ψ ‖A‖·‖B‖` matches the shell's `∑_ψ ‖A·B‖` term-by-term
(`‖A·B‖ = ‖A‖·‖B‖`). -/
theorem energy_shell_dvd {X Y Q δ : ℕ} (hδ1 : 1 ≤ δ) (hQ : 2 ≤ Q) (hY : 0 < Y)
    (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q),
        ((f : ℝ) / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ shellBoundDvd X Y Q δ := by
  refine le_trans (le_of_eq ?_) (bilinTwist_energy_le_dvd hδ1 hQ hY α β hα hβ)
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  unfold bilinPrimEnergy
  exact Finset.sum_congr rfl (fun ψ _ => (norm_mul _ _).symm)

/-! ## 3. Sanity: `δ = 1` recovers the landed `energy_shell`. -/

/-- At `δ = 1`, `energy_shell_dvd` recovers `Salt.Chen.energy_shell`'s shape (the
filter is all of `Icc 1 Q`, and `shellBoundDvd _ _ _ 1 = shellBound`). -/
example {X Y Q : ℕ} (hQ : 2 ≤ Q) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ f ∈ Finset.Icc 1 Q, ((f : ℝ) / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ shellBound X Y Q := by
  have h := energy_shell_dvd (X := X) (Y := Y) (Q := Q) (δ := 1) (le_refl 1) hQ hY α β hα hβ
  rw [shellBoundDvd_one] at h
  have hf : (Finset.Icc 1 Q).filter (fun q => (1 : ℕ) ∣ q) = Finset.Icc 1 Q :=
    Finset.filter_true_of_mem (fun q _ => one_dvd q)
  rwa [hf] at h

end Salt.Chen
