/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.EnergyClose

/-!
# WBV1 — the cutoff (window) carrier layer

Design: `docs/blueprints/flags.md`, the `2026-07-13 C54-RECON` freeze (route (i),
"the one-sided cutoff carrier") and the WBV-wave list.  This is the first WBV node:
the *windowed* analogues of the `Salt.Chen.GeneralBV` carriers, obtained by riding a
sharp cutoff `m·n ≤ T` through the character machinery WITHOUT ever factoring the
convolution.

The load-bearing fact (the recon): `Salt.BV.bilinear_LS_shell` (`BilinearLS.lean`)
NATIVELY carries the sharp cutoff `m·n ≤ Y` inside its character sum with an *identical*
energy bound; the landed general-BV pipeline discards it one layer up (via
`Salt.Chen.bilin_cutoff_eq`).  Here we KEEP it — the window will later be the
difference of the `T = x` and `T = x/2+1` cutoffs (WBV2/WBV3).

## What this file lands (all FULL, sorry-free)

1. `cutoffTwist` — the bilinear twisted double sum
   `∑_{m≤X} ∑_{n≤Y, mn≤T} α_m β_n χ(mn)` (the shell's inner character sum, with the
   cutoff `T` a free parameter).  Unlike `bilinTwist α · * bilinTwist β ·` this does
   NOT factor: the cutoff couples `m, n`.
2. `apDiscBilinCutoff` — `apDiscBilin` with the guard `m·n ≤ T` inserted into BOTH the
   residue-class sum and the `(1/φd)`-unit main term.
3. `apDiscBilinCutoff_orthogonality` — the exact character reduction
   `apDiscBilinCutoff = (1/φd)·∑_{χ≠1} χ(N₀⁻¹)·cutoffTwist`.  The orthogonality is
   per-`(m,n)`-term, so the guard rides through untouched (the cutoff stays UNfactored
   inside `cutoffTwist`).  Mirrors `apDiscBilin_orthogonality`; strictly simpler — no
   `sum_mul_sum` split, since `cutoffTwist` is already the double sum.
4. `norm_apDiscBilinCutoff_le` — the per-`d` triangle bound to
   `(1/φd)·∑_{χ≠1} ‖cutoffTwist‖`.
5. `cutoffTwist_energy_le` — the shell consumption KEEPING the cutoff:
   `∑_{q≤Q} (q/φq)·∑_{χ prim} ‖cutoffTwist α β X Y T q χ‖ ≤ shellBound X Y Q`.  Mirrors
   `bilinTwist_energy_le` but SKIPS `bilin_cutoff_eq`: the cutoff character sum IS the
   shell's inner sum, so this is strictly easier than the landed lemma.  Packaged also
   as `cutoffPrimEnergy` + `energy_shell_cutoff` (mirroring `EnergyClose.energy_shell`)
   — the interface WBV2's dyadic descent consumes.
6. δ/T-degeneracy sanity `example`s: for `X·Y ≤ T` the guard is vacuous and both
   carriers collapse to their `GeneralBV` shapes (`cutoffTwist = bilinTwist·bilinTwist`,
   `apDiscBilinCutoff = apDiscBilin`).

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The windowed carriers -/

/-- **The windowed bilinear character sum.**  The shell's inner character sum
`∑_{m≤X} ∑_{n≤Y, mn≤T} α_m β_n χ(mn)` with the sharp cutoff `m·n ≤ T` a free
parameter.  The cutoff couples `m, n`, so — unlike the landed
`bilinTwist α X d χ * bilinTwist β Y d χ` (`A(χ)·B(χ)`) — this does NOT factor: the
window rides UNfactored inside the twisted sum. -/
noncomputable def cutoffTwist (α β : ℕ → ℂ) (X Y T n₀ : ℕ) (χ : DirichletCharacter ℂ n₀) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
    α m * β n * χ ((m * n : ℕ) : ZMod n₀)

open Classical in
/-- **The windowed fixed-residue bilinear AP discrepancy.**  `apDiscBilin` with the
guard `m·n ≤ T` inserted into BOTH the residue-class count and the `(1/φd)`-unit main
term. -/
noncomputable def apDiscBilinCutoff (α β : ℕ → ℂ) (X Y N₀ d T : ℕ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
      (if ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m * β n else 0))
    - (1 / (d.totient : ℂ)) *
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
        (if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0))

/-! ## 2. The exact character reduction -/

/-- The principal-character factorization of the windowed coprime mean term:
`cutoffTwist α β X Y T d χ₀ = ∑_{m,n : mn≤T, (mn,d)=1} α_m β_n`.  Cleaner than the
landed `principal_mean_eq` — `cutoffTwist` uses `χ(mn)` directly, so no `IsUnit`-split
into `IsUnit m ∧ IsUnit n` is needed. -/
private lemma principal_mean_cutoff_eq {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y T : ℕ) :
    cutoffTwist α β X Y T d (1 : DirichletCharacter ℂ d)
      = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0) := by
  classical
  unfold cutoffTwist
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hu : IsUnit ((m * n : ℕ) : ZMod d)
  · rw [if_pos hu, MulChar.one_apply hu]; ring
  · rw [if_neg hu, MulChar.map_nonunit _ hu]; ring

open Classical in
/-- **The exact windowed character reduction (bilinear orthogonality) — FULL.**  For
`N₀` coprime to `d`, the windowed fixed-residue discrepancy equals a `(1/φd)`-weighted
sum over the *non-principal* characters of the UNfactored windowed twist:
```
apDiscBilinCutoff α β X Y N₀ d T = (1/φd)·∑_{χ ≠ χ₀ mod d} χ(N₀⁻¹)·cutoffTwist α β X Y T d χ.
```
Mirrors `apDiscBilin_orthogonality`; the orthogonality argument is per-`(m,n)`-term, so
the extra guard `m·n ≤ T` rides through the character sum untouched — no factoring of
`cutoffTwist` into an `A(χ)·B(χ)` product. -/
theorem apDiscBilinCutoff_orthogonality {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y N₀ T : ℕ)
    (hN₀ : Nat.Coprime N₀ d) :
    apDiscBilinCutoff α β X Y N₀ d T
      = (1 / (d.totient : ℂ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            χ (N₀ : ZMod d)⁻¹ * cutoffTwist α β X Y T d χ := by
  classical
  have hunit : IsUnit ((N₀ : ℕ) : ZMod d) := by
    rw [ZMod.isUnit_iff_coprime]; exact hN₀
  have hunitinv : IsUnit (((N₀ : ℕ) : ZMod d)⁻¹) := by
    rw [isUnit_iff_exists]
    exact ⟨(N₀ : ZMod d), ZMod.inv_mul_of_unit _ hunit, ZMod.mul_inv_of_unit _ hunit⟩
  have htot_pos : (0 : ℝ) < (d.totient : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d)); exact_mod_cast this
  have htot_ne : (d.totient : ℂ) ≠ 0 := by
    have h : (d.totient : ℝ) ≠ 0 := ne_of_gt htot_pos; exact_mod_cast h
  -- Step 1: expand the full character sum via orthogonality → φd · (windowed residue sum).
  have key : (∑ χ : DirichletCharacter ℂ d,
        χ (N₀ : ZMod d)⁻¹ * cutoffTwist α β X Y T d χ)
      = (d.totient : ℂ) * ∑ m ∈ Finset.Icc 1 X,
          ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m * β n else 0) := by
    calc (∑ χ : DirichletCharacter ℂ d,
            χ (N₀ : ZMod d)⁻¹ * cutoffTwist α β X Y T d χ)
        = ∑ χ : DirichletCharacter ℂ d, ∑ m ∈ Finset.Icc 1 X,
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (α m * β n) * (χ (N₀ : ZMod d)⁻¹ * χ ((m * n : ℕ) : ZMod d)) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          unfold cutoffTwist
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          ring
      _ = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (α m * β n) *
            ∑ χ : DirichletCharacter ℂ d, χ (N₀ : ZMod d)⁻¹ * χ ((m * n : ℕ) : ZMod d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (α m * β n) *
            (if (N₀ : ZMod d) = ((m * n : ℕ) : ZMod d) then (d.totient : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hunit ((m * n : ℕ) : ZMod d)]
      _ = (d.totient : ℂ) * ∑ m ∈ Finset.Icc 1 X,
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m * β n else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          by_cases hc : ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)
          · rw [if_pos hc.symm, if_pos hc]; ring
          · rw [if_neg (fun h => hc h.symm), if_neg hc]; ring
  -- Step 2: isolate the principal character.
  have hone : (1 : DirichletCharacter ℂ d) (N₀ : ZMod d)⁻¹ = 1 := MulChar.one_apply hunitinv
  have split : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        χ (N₀ : ZMod d)⁻¹ * cutoffTwist α β X Y T d χ
      = (d.totient : ℂ) * (∑ m ∈ Finset.Icc 1 X,
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m * β n else 0))
        - cutoffTwist α β X Y T d (1 : DirichletCharacter ℂ d) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : DirichletCharacter ℂ d)), key, hone,
      one_mul]
  -- Step 3: divide by φd and unfold `apDiscBilinCutoff`.
  rw [split, principal_mean_cutoff_eq α β X Y T]
  unfold apDiscBilinCutoff
  field_simp

open Classical in
/-- **The per-`d` windowed triangle bound — FULL.**  `‖apDiscBilinCutoff‖ ≤
(1/φd)·∑_{χ≠χ₀} ‖cutoffTwist‖`.  Direct from `apDiscBilinCutoff_orthogonality` +
`‖χ(N₀⁻¹)‖ ≤ 1`.  Simpler than `norm_apDiscBilin_le` — a single norm per character
(the windowed twist does not split into an `A·B` product). -/
theorem norm_apDiscBilinCutoff_le {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y N₀ T : ℕ)
    (hN₀ : Nat.Coprime N₀ d) :
    ‖apDiscBilinCutoff α β X Y N₀ d T‖
      ≤ (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α β X Y T d χ‖ := by
  classical
  rw [apDiscBilinCutoff_orthogonality α β X Y N₀ T hN₀, norm_mul]
  have hnormfac : ‖(1 / (d.totient : ℂ))‖ = 1 / (d.totient : ℝ) := by
    rw [norm_div, norm_one]; congr 1; exact Complex.norm_natCast d.totient
  rw [hnormfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun χ _ => ?_)
  calc ‖χ (N₀ : ZMod d)⁻¹ * cutoffTwist α β X Y T d χ‖
      = ‖χ (N₀ : ZMod d)⁻¹‖ * ‖cutoffTwist α β X Y T d χ‖ := norm_mul _ _
    _ ≤ 1 * ‖cutoffTwist α β X Y T d χ‖ :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
    _ = ‖cutoffTwist α β X Y T d χ‖ := one_mul _

/-! ## 3. The windowed large-sieve energy (shell consumption, cutoff KEPT) -/

open Classical in
/-- **Windowed large-sieve energy — FULL (consumes `Salt.BV.bilinear_LS_shell`).**  For
`‖α‖,‖β‖ ≤ 1`, the `(q/φq)`-weighted primitive-character `L¹` energy of the windowed
twist obeys the balanced shell bound
```
∑_{q≤Q} (q/φq) ∑_{χ prim mod q} ‖cutoffTwist α β X Y T q χ‖ ≤ shellBound X Y Q.
```
Mirrors `bilinTwist_energy_le` but SKIPS the `bilin_cutoff_eq` step: the windowed twist
IS the shell's inner cutoff character sum (with the shell's cutoff `Y` set to `T`), so
the LHS reduces to the shell LHS by *unfolding* `cutoffTwist` — strictly easier than
the landed lemma, which first had to discard the cutoff and re-factor into `A(χ)·B(χ)`.
The `L²` masses `∑‖α‖², ∑‖β‖²` are bounded by `X, Y`. -/
theorem cutoffTwist_energy_le {X Y T Q : ℕ} (hQ : 2 ≤ Q) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖cutoffTwist α β X Y T q χ‖
      ≤ shellBound X Y Q := by
  classical
  -- Unfold both the windowed twist (LHS → shell inner sum) and the shell bound (RHS).
  simp only [cutoffTwist, shellBound]
  refine le_trans (bilinear_LS_shell (M := X) (H := Y) hQ hY α β T) ?_
  -- The `L²` masses are ≤ X, Y (verbatim from `bilinTwist_energy_le`).
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
      * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((X : ℝ) + 1))
      * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((Y : ℝ) + 1)) with hP_def
  have hP : 0 ≤ P := by
    rw [hP_def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1logY)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine mul_le_mul ?_ hmassβ (Real.sqrt_nonneg _) (mul_nonneg hP (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_left hmassα hP

open Classical in
/-- The windowed primitive-pair energy: the `bilinPrimEnergy` analogue for the windowed
twist, `sum over primitive psi mod f of the norm of cutoffTwist`. A single norm per
character (the window does not factor into an `A * B` product), so this matches the
shell's per-character norm term directly, with no `norm_mul` bridge. This is the
interface WBV2's dyadic descent consumes. -/
noncomputable def cutoffPrimEnergy (α β : ℕ → ℂ) (X Y T f : ℕ) : ℝ :=
  ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive),
    ‖cutoffTwist α β X Y T f ψ‖

lemma cutoffPrimEnergy_nonneg (α β : ℕ → ℂ) (X Y T f : ℕ) : 0 ≤ cutoffPrimEnergy α β X Y T f :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

open Classical in
/-- **The `cutoffPrimEnergy` shell (restatement of `cutoffTwist_energy_le`).**  For
`‖α‖,‖β‖ ≤ 1`, the `(q/φq)`-weighted windowed primitive block energy obeys the balanced
shell bound.  Mirrors `EnergyClose.energy_shell`; the WBV2-consumable packaging. -/
theorem energy_shell_cutoff {X Y T Q : ℕ} (hQ : 2 ≤ Q) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * cutoffPrimEnergy α β X Y T q
      ≤ shellBound X Y Q := by
  refine le_trans (le_of_eq ?_) (cutoffTwist_energy_le (X := X) (T := T) hQ hY α β hα hβ)
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp only [cutoffPrimEnergy]

/-! ## 4. δ/T-degeneracy sanity (`T ≥ X·Y` recovers the `GeneralBV` shapes) -/

/-- With the cutoff vacuous (`X·Y ≤ T`), the windowed twist collapses to the landed
split product `A(χ)·B(χ) = bilinTwist α X d χ · bilinTwist β Y d χ` (mirrors
`bilin_cutoff_eq`, which is the `T = X·Y` instance). -/
example {d : ℕ} (α β : ℕ → ℂ) (X Y T : ℕ) (χ : DirichletCharacter ℂ d) (hT : X * Y ≤ T) :
    cutoffTwist α β X Y T d χ = bilinTwist α X d χ * bilinTwist β Y d χ := by
  have hstep : cutoffTwist α β X Y T d χ
      = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, α m * β n * χ ((m * n : ℕ) : ZMod d) := by
    unfold cutoffTwist
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.filter_true_of_mem
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact le_trans (Nat.mul_le_mul hm.2 hn.2) hT
  rw [hstep]
  unfold bilinTwist
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Salt.LS.chi_cast_mul]; ring

open Classical in
/-- With the cutoff vacuous (`X·Y ≤ T`), the windowed discrepancy collapses to the
landed `apDiscBilin` (both guarded sums become the full ranges). -/
example {d : ℕ} (α β : ℕ → ℂ) (X Y N₀ T : ℕ) (hT : X * Y ≤ T) :
    apDiscBilinCutoff α β X Y N₀ d T = apDiscBilin α β X Y N₀ d := by
  unfold apDiscBilinCutoff apDiscBilin
  have hfull : ∀ m ∈ Finset.Icc 1 X,
      (Finset.Icc 1 Y).filter (fun n => m * n ≤ T) = Finset.Icc 1 Y := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    apply Finset.filter_true_of_mem
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact le_trans (Nat.mul_le_mul hm.2 hn.2) hT
  congr 1
  · exact Finset.sum_congr rfl (fun m hm => by rw [hfull m hm])
  · congr 1
    exact Finset.sum_congr rfl (fun m hm => by rw [hfull m hm])

end Salt.Chen
