/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.BilinearLS

/-!
# C3a — the general Bombieri–Vinogradov, weak form (KEYSTONE 2 of the `chen` rung)

Design: `docs/blueprints/chen.md`, the "general-BV freeze discipline" section and
the C3a row. This lands the **weak form** of BJS Lemma 32 (arXiv:2207.09452v6
p. 28) — the bilinear (convolution) upgrade of the corpus' single-linear BV
pipeline, in the frozen shape the A₃ switch consumes:

* **fixed scale** — supports baked in as `Finset.Icc 1 X`, `Finset.Icc 1 Y`;
* **fixed residue** — the discrepancy is at a single class `N₀ mod d` (BJS's
  `np ≡ N (mod d)`), *not* a max over reduced residues;
* **`L¹` in the modulus** `d` — no max-over-`y`; the maximal (`V2.LS-bil`) form
  is deliberately avoided (the struck trap);
* **SW-regularity of the convolution factor `β` as a NAMED HYPOTHESIS**
  (`hβSW` below) — the derivation of that regularity from the gate is its own
  node (C3b).

## What this file lands (the reusable BV→convolution upgrade)

1. **The bilinear AP-discrepancy carrier** `apDiscBilin` (mirroring the corpus'
   `dispDisc` at a fixed residue) and its **exact character reduction**
   `apDiscBilin_orthogonality` — the identity
   `apDiscBilin = (1/φd)·∑_{χ≠χ₀ mod d} χ(N₀⁻¹)·A(χ)·B(χ)` where `A(χ), B(χ)` are
   the character-twisted coefficient sums.  This is the bilinear analogue of
   `Salt.BV.psiAP_discrepancy_le`; **the convolution SPLITS over `χ`**
   (`A(χ)·B(χ)`), which is exactly where bilinearity pays.  Fully proven.
   The norm form `norm_apDiscBilin_le` gives the per-`d` triangle bound.

2. **The bilinear large-sieve energy** `bilinTwist_energy_le` — a genuine
   consumption of the landed shell `Salt.BV.bilinear_LS_shell`: with `‖α‖,‖β‖ ≤ 1`
   the `(q/φq)`-weighted primitive-character `L¹` product energy
   `∑_{q≤Q}(q/φq)∑_{χ prim}‖A(χ)·B(χ)‖` obeys the balanced
   `√(Q²+13X)·√(Q²+13Y)·√X·√Y` bound (the cutoff taken vacuous so the bilinear
   character sum equals `A(χ)·B(χ)`).  Fully proven.

3. **The headline** `general_BV_weak` — the `L¹`-over-`d` discrepancy bound in the
   frozen weak shape, assembled from (1) with the small-conductor branch **full**
   (via `hβSW`) and the large-conductor branch consuming (2)/`bilinear_LS_shell`
   through named dyadic-glue hypotheses (the conductor descent + dyadic
   reassembly, deferred to C3b/C3c — see the flag below).

## FLAG (Iron Rule 1, the weight mismatch) — recorded in `docs/blueprints/flags.md`

`bilinear_LS_shell` carries the `(q/φq)` weight; the discrepancy's character
reduction carries `(1/φd)`.  After the conductor fold these differ by a factor of
the modulus, so consuming the shell *without* a dyadic-in-conductor decomposition
is lossy by `~√(XY)` (produces `(XY)^{3/2}` in place of `XY/log^A`).  The tight
route recovers the `1/f` per dyadic block (`~1-2` glue hypotheses — the C3c
"fine-partition bookkeeping").  Hence the large-conductor branch is discharged
through the named glue `hLargeDisc`, whose engine `bilinTwist_energy_le` is landed
here; the dyadic reassembly is C3c.

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The bilinear AP-discrepancy carrier and its character reduction -/

/-- The character-twisted coefficient sum `A(χ) = ∑_{m∈[1,X]} α(m)·χ(m)` (the
`m`-side factor of the convolution). -/
noncomputable def bilinTwist (α : ℕ → ℂ) (X d : ℕ) (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, α m * χ (m : ZMod d)

open Classical in
/-- **The fixed-residue bilinear AP discrepancy** (BJS Lemma 32's carrier at a
single class).  For coefficient sequences `α, β` supported (via the ranges) on
`[1,X]`, `[1,Y]`, this is the count of product-pairs `m·n ≡ N₀ (mod d)` minus its
expected `1/φ(d)` share over the pairs with `m·n` coprime to `d`.  The bilinear
analogue of `Salt.BV.dispDisc` at a fixed residue. -/
noncomputable def apDiscBilin (α β : ℕ → ℂ) (X Y N₀ d : ℕ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
      (if ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m * β n else 0))
    - (1 / (d.totient : ℂ)) *
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
        (if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0))

/-- The principal-character factorization of the coprime mean term:
`A(χ₀)·B(χ₀) = ∑_{m,n : (mn,d)=1} α(m)·β(n)`. -/
private lemma principal_mean_eq {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y : ℕ) :
    bilinTwist α X d (1 : DirichletCharacter ℂ d) * bilinTwist β Y d (1 : DirichletCharacter ℂ d)
      = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
          (if IsUnit ((m * n : ℕ) : ZMod d) then α m * β n else 0) := by
  classical
  unfold bilinTwist
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hu : IsUnit ((m * n : ℕ) : ZMod d)
  · rw [if_pos hu]
    have hm : IsUnit ((m : ℕ) : ZMod d) := by
      rw [Nat.cast_mul] at hu; exact (isUnit_of_mul_isUnit_left hu)
    have hn : IsUnit ((n : ℕ) : ZMod d) := by
      rw [Nat.cast_mul] at hu; exact (isUnit_of_mul_isUnit_right hu)
    rw [MulChar.one_apply hm, MulChar.one_apply hn]; ring
  · rw [if_neg hu]
    have hnu : ¬ (IsUnit ((m : ℕ) : ZMod d) ∧ IsUnit ((n : ℕ) : ZMod d)) := by
      intro ⟨hm, hn⟩; exact hu (by rw [Nat.cast_mul]; exact hm.mul hn)
    by_cases hm : IsUnit ((m : ℕ) : ZMod d)
    · have hn : ¬ IsUnit ((n : ℕ) : ZMod d) := fun hn => hnu ⟨hm, hn⟩
      rw [MulChar.map_nonunit _ hn]; ring
    · rw [MulChar.map_nonunit _ hm]; ring

open Classical in
/-- **The exact character reduction (bilinear orthogonality) — FULL.**  For
`N₀` coprime to `d`, the fixed-residue bilinear discrepancy equals a `(1/φd)`-
weighted sum over the *non-principal* characters of the split product
`A(χ)·B(χ)`:
```
apDiscBilin α β X Y N₀ d = (1/φd)·∑_{χ ≠ χ₀ mod d} χ(N₀⁻¹)·A(χ)·B(χ).
```
This is the bilinear analogue of `Salt.BV.psiAP_discrepancy_le`; the convolution
`∑_{m,n : mn≡N₀} α(m)β(n)` splits as the *product* `A(χ)·B(χ)` because
`χ(mn) = χ(m)·χ(n)`. -/
theorem apDiscBilin_orthogonality {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y N₀ : ℕ)
    (hN₀ : Nat.Coprime N₀ d) :
    apDiscBilin α β X Y N₀ d
      = (1 / (d.totient : ℂ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            χ (N₀ : ZMod d)⁻¹ * (bilinTwist α X d χ * bilinTwist β Y d χ) := by
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
  -- Step 1: expand the full character sum via orthogonality → φd · (residue sum).
  have key : (∑ χ : DirichletCharacter ℂ d,
        χ (N₀ : ZMod d)⁻¹ * (bilinTwist α X d χ * bilinTwist β Y d χ))
      = (d.totient : ℂ) * ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
          (if ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m * β n else 0) := by
    calc (∑ χ : DirichletCharacter ℂ d,
            χ (N₀ : ZMod d)⁻¹ * (bilinTwist α X d χ * bilinTwist β Y d χ))
        = ∑ χ : DirichletCharacter ℂ d, ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
            (α m * β n) * (χ (N₀ : ZMod d)⁻¹ * χ ((m * n : ℕ) : ZMod d)) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          unfold bilinTwist
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Salt.LS.chi_cast_mul]; ring
      _ = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, (α m * β n) *
            ∑ χ : DirichletCharacter ℂ d, χ (N₀ : ZMod d)⁻¹ * χ ((m * n : ℕ) : ZMod d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, (α m * β n) *
            (if (N₀ : ZMod d) = ((m * n : ℕ) : ZMod d) then (d.totient : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hunit ((m * n : ℕ) : ZMod d)]
      _ = (d.totient : ℂ) * ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
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
        χ (N₀ : ZMod d)⁻¹ * (bilinTwist α X d χ * bilinTwist β Y d χ)
      = (d.totient : ℂ) * (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
            (if ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d) then α m * β n else 0))
        - bilinTwist α X d (1 : DirichletCharacter ℂ d)
            * bilinTwist β Y d (1 : DirichletCharacter ℂ d) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : DirichletCharacter ℂ d)), key, hone,
      one_mul]
  -- Step 3: divide by φd and unfold `apDiscBilin`.
  rw [split, principal_mean_eq α β X Y]
  unfold apDiscBilin
  field_simp

open Classical in
/-- **The per-`d` triangle bound — FULL.**  `‖apDiscBilin‖ ≤ (1/φd)·∑_{χ≠χ₀}
‖A(χ)‖·‖B(χ)‖`.  Direct from `apDiscBilin_orthogonality` + `‖χ(N₀⁻¹)‖ ≤ 1`. -/
theorem norm_apDiscBilin_le {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y N₀ : ℕ)
    (hN₀ : Nat.Coprime N₀ d) :
    ‖apDiscBilin α β X Y N₀ d‖
      ≤ (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖ := by
  classical
  rw [apDiscBilin_orthogonality α β X Y N₀ hN₀, norm_mul]
  have hnormfac : ‖(1 / (d.totient : ℂ))‖ = 1 / (d.totient : ℝ) := by
    rw [norm_div, norm_one]; congr 1; exact Complex.norm_natCast d.totient
  rw [hnormfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun χ _ => ?_)
  calc ‖χ (N₀ : ZMod d)⁻¹ * (bilinTwist α X d χ * bilinTwist β Y d χ)‖
      = ‖χ (N₀ : ZMod d)⁻¹‖ * (‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖) := by
        rw [norm_mul, norm_mul]
    _ ≤ 1 * (‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖) :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
    _ = ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖ := one_mul _

/-! ## 2. The bilinear large-sieve energy (genuine `bilinear_LS_shell` consumption) -/

/-- With the cutoff taken at `X·Y` the sharp-cutoff bilinear character sum is
vacuously unrestricted and equals the split product `A(χ)·B(χ)`. -/
private lemma bilin_cutoff_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
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

open Classical in
/-- **Bilinear large-sieve energy — FULL (consumes `Salt.BV.bilinear_LS_shell`).**
For `‖α‖, ‖β‖ ≤ 1`, the `(q/φq)`-weighted primitive-character `L¹` product energy
obeys the balanced bound
```
∑_{q≤Q} (q/φq) ∑_{χ prim mod q} ‖A(χ)·B(χ)‖
  ≤ 2(1+log Y)·√(Q²+13(X+1))·√(Q²+13(Y+1))·√X·√Y,
```
the cutoff taken vacuous (`X·Y`) so the shell's bilinear character sum is exactly
`A(χ)·B(χ)`, and the `L²` masses `∑‖α‖², ∑‖β‖²` bounded by `X, Y`.  This is the
per-block **engine** the large-conductor discharge (C3c) sums dyadically. -/
theorem bilinTwist_energy_le {X Y Q : ℕ} (hQ : 2 ≤ Q) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖bilinTwist α X q χ * bilinTwist β Y q χ‖
      ≤ 2 * (1 + Real.log Y)
          * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((X : ℝ) + 1))
          * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((Y : ℝ) + 1))
          * Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ) := by
  classical
  -- Rewrite the LHS into the shell's sharp-cutoff form.
  have hrw : ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖bilinTwist α X q χ * bilinTwist β Y q χ‖
      = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ X * Y),
              α m * β n * χ ((m * n : ℕ) : ZMod q)‖ := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    congr 1
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [bilin_cutoff_eq χ α β X Y]
  rw [hrw]
  refine le_trans (bilinear_LS_shell hQ hY α β (X * Y)) ?_
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
      * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((X : ℝ) + 1))
      * Real.sqrt ((Q : ℝ) ^ 2 + 13 * ((Y : ℝ) + 1)) with hP_def
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

/-! ## 3. The headline `general_BV_weak` -/

/-- The crude twisted-sum bound `‖A(χ)‖ ≤ X` (from `‖α‖ ≤ 1`, `‖χ‖ ≤ 1`). -/
private lemma bilinTwist_norm_le {d : ℕ} (α : ℕ → ℂ) (X : ℕ) (χ : DirichletCharacter ℂ d)
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
/-- **Small-conductor per-`d` bound.**  For `d` below the SW threshold, the per-`d`
character energy is `≤ Kβ·(XY)/L^{A+C0}`, using the crude `‖A(χ)‖ ≤ X` and the
named SW-regularity of `β` (`hβd`).  Full. -/
private lemma small_perd {d : ℕ} [NeZero d] (α β : ℕ → ℂ) (X Y : ℕ) {A C0 Kβ : ℝ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hKβ : 0 ≤ Kβ)
    (hLpos : 0 < Real.log ((X : ℝ) * (Y : ℝ)))
    (hβd : 2 ≤ d → ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 →
        ‖bilinTwist β Y d χ‖ ≤ Kβ * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + C0)) :
    (1 / (d.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + C0) := by
  classical
  set L := Real.log ((X : ℝ) * (Y : ℝ)) with hLdef
  have hLA : (0 : ℝ) < L ^ (A + C0) := Real.rpow_pos_of_pos hLpos _
  set V : ℝ := Kβ * (Y : ℝ) / L ^ (A + C0) with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  have hφpos : (0 : ℝ) < (d.totient : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d)); exact_mod_cast this
  by_cases hd2 : 2 ≤ d
  · -- `2 ≤ d`: apply `hβd`.
    have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ d)).card ≤ d.totient := by
      calc (Finset.univ.erase (1 : DirichletCharacter ℂ d)).card
          ≤ (Finset.univ : Finset (DirichletCharacter ℂ d)).card := Finset.card_erase_le
        _ = d.totient := by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d]
    have hcardR : ((Finset.univ.erase (1 : DirichletCharacter ℂ d)).card : ℝ) ≤ (d.totient : ℝ) :=
      by exact_mod_cast hcard
    have hsum : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
        ≤ ((Finset.univ.erase (1 : DirichletCharacter ℂ d)).card : ℝ) * ((X : ℝ) * V) := by
      calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
          ≤ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1, ((X : ℝ) * V) := by
            refine Finset.sum_le_sum (fun χ hχ => ?_)
            have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
            have hA : ‖bilinTwist α X d χ‖ ≤ (X : ℝ) := bilinTwist_norm_le α X χ hα
            have hB : ‖bilinTwist β Y d χ‖ ≤ V := hβd hd2 χ hχ1
            exact mul_le_mul hA hB (norm_nonneg _) (by positivity)
        _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ d)).card : ℝ) * ((X : ℝ) * V) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
        ≤ (1 / (d.totient : ℝ)) *
            (((Finset.univ.erase (1 : DirichletCharacter ℂ d)).card : ℝ) * ((X : ℝ) * V)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (1 / (d.totient : ℝ)) * ((d.totient : ℝ) * ((X : ℝ) * V)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = (X : ℝ) * V := by field_simp
      _ = Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + C0) := by rw [hVdef]; ring
  · -- `d = 1`: the character group is trivial, `erase 1` is empty.
    have hdpos : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hd1' : d = 1 := by omega
    subst hd1'
    have hempty : (Finset.univ : Finset (DirichletCharacter ℂ 1)).erase 1 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun χ hχ => ?_)
      exact (Finset.mem_erase.mp hχ).1 (Subsingleton.elim χ 1)
    rw [hempty, Finset.sum_empty, mul_zero]
    positivity

open Classical in
/-- **C3a — the general Bombieri–Vinogradov, weak form (KEYSTONE 2).**  The
`L¹`-over-`d` bilinear AP-discrepancy at a fixed residue `N₀`, split at the SW
threshold `D0` into a **fully-proven** small-conductor branch (via the named
SW-regularity `hβSW` of the convolution factor `β`) and a large-conductor branch
discharged through the named dyadic-glue `hLargeDisc` (the conductor-fold + dyadic
reassembly whose per-block engine `bilinTwist_energy_le`/`bilinear_LS_shell` is
landed above; see the module FLAG on the `(q/φq)`↔`(1/φd)` weight mismatch).

Frozen weak shape: fixed scale (`Finset.Icc 1 X/Y`), fixed residue (`N₀ mod d`),
`L¹` in the modulus over the consumer-supplied squarefree set `Dset`, SW-regularity
named — *not* the maximal `max-over-y` form. -/
theorem general_BV_weak (α β : ℕ → ℂ) (X Y N₀ D0 : ℕ) (Dset : Finset ℕ)
    {A C0 Kβ Klarge : ℝ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hKβ : 0 ≤ Kβ)
    (hDge1 : ∀ d ∈ Dset, 1 ≤ d)
    (hcop : ∀ d ∈ Dset, Nat.Coprime N₀ d)
    (hLpos : 0 < Real.log ((X : ℝ) * (Y : ℝ)))
    (hD0 : (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (Y : ℝ))) ^ C0)
    (hβSW : ∀ (d : ℕ), 2 ≤ d → d ≤ D0 → ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 →
        ‖bilinTwist β Y d χ‖ ≤ Kβ * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + C0))
    (hLargeDisc : ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
          (1 / (d.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
        ≤ Klarge * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) :
    ∑ d ∈ Dset, ‖apDiscBilin α β X Y N₀ d‖
      ≤ (Kβ + Klarge) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  classical
  set L := Real.log ((X : ℝ) * (Y : ℝ)) with hLdef
  have hLApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos _
  have hLC0pos : (0 : ℝ) < L ^ C0 := Real.rpow_pos_of_pos hLpos _
  have hLAC0pos : (0 : ℝ) < L ^ (A + C0) := Real.rpow_pos_of_pos hLpos _
  -- Split at the threshold.
  rw [← Finset.sum_filter_add_sum_filter_not Dset (fun d => d ≤ D0)
        (fun d => ‖apDiscBilin α β X Y N₀ d‖)]
  -- The small-conductor branch (full).
  have hsmall : ∑ d ∈ Dset.filter (fun d => d ≤ D0), ‖apDiscBilin α β X Y N₀ d‖
      ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ A := by
    have hVsmall0 : (0 : ℝ) ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + C0) := by positivity
    have hstep : ∑ d ∈ Dset.filter (fun d => d ≤ D0), ‖apDiscBilin α β X Y N₀ d‖
        ≤ ∑ _d ∈ Dset.filter (fun d => d ≤ D0),
            Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + C0) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      rw [Finset.mem_filter] at hd
      have hd1 : 1 ≤ d := hDge1 d hd.1
      haveI : NeZero d := ⟨by omega⟩
      calc ‖apDiscBilin α β X Y N₀ d‖
          ≤ (1 / (d.totient : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖ :=
            norm_apDiscBilin_le α β X Y N₀ (hcop d hd.1)
        _ ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + C0) := by
            refine small_perd α β X Y hα hKβ hLpos (fun hd2 χ hχ => ?_)
            exact hβSW d hd2 hd.2 χ hχ
    -- card of the small block ≤ D0 ≤ L^C0.
    have hsub : Dset.filter (fun d => d ≤ D0) ⊆ Finset.Icc 1 D0 := by
      intro d hd; rw [Finset.mem_filter] at hd; rw [Finset.mem_Icc]
      exact ⟨hDge1 d hd.1, hd.2⟩
    have hcardsmall : ((Dset.filter (fun d => d ≤ D0)).card : ℝ) ≤ (D0 : ℝ) := by
      have h1 : (Dset.filter (fun d => d ≤ D0)).card ≤ (Finset.Icc 1 D0).card :=
        Finset.card_le_card hsub
      have h2 : (Finset.Icc 1 D0).card = D0 := by rw [Nat.card_Icc]; omega
      rw [h2] at h1; exact_mod_cast h1
    calc ∑ d ∈ Dset.filter (fun d => d ≤ D0), ‖apDiscBilin α β X Y N₀ d‖
        ≤ ((Dset.filter (fun d => d ≤ D0)).card : ℝ)
            * (Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + C0)) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]; exact hstep
      _ ≤ (D0 : ℝ) * (Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + C0)) :=
          mul_le_mul_of_nonneg_right hcardsmall hVsmall0
      _ ≤ L ^ C0 * (Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + C0)) :=
          mul_le_mul_of_nonneg_right hD0 hVsmall0
      _ = Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ A := by
          rw [Real.rpow_add hLpos A C0]
          field_simp
  -- The large-conductor branch (named dyadic glue).
  have hlarge : ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0), ‖apDiscBilin α β X Y N₀ d‖
      ≤ Klarge * ((X : ℝ) * (Y : ℝ)) / L ^ A := by
    refine le_trans (Finset.sum_le_sum (fun d hd => ?_)) hLargeDisc
    rw [Finset.mem_filter] at hd
    have hd1 : 1 ≤ d := hDge1 d hd.1
    haveI : NeZero d := ⟨by omega⟩
    -- `norm_apDiscBilin_le` produces the `FunLike` erase-instance; the goal (from
    -- `hLargeDisc`) carries the `Classical` one — bridge by instance-subsingleton.
    refine (norm_apDiscBilin_le α β X Y N₀ (hcop d hd.1)).trans_eq ?_
    congr 1
    exact Finset.sum_congr
      (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
        (Subsingleton.elim _ _))
      (fun _ _ => rfl)
  -- Assemble.
  calc ∑ d ∈ Dset.filter (fun d => d ≤ D0), ‖apDiscBilin α β X Y N₀ d‖
        + ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0), ‖apDiscBilin α β X Y N₀ d‖
      ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ A + Klarge * ((X : ℝ) * (Y : ℝ)) / L ^ A :=
        add_le_add hsmall hlarge
    _ = (Kβ + Klarge) * ((X : ℝ) * (Y : ℝ)) / L ^ A := by ring

end Salt.Chen
