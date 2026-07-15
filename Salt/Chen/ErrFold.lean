/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.EnergyClose
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# C3c‴ — discharging `hErrSum` (keystone 2's LAST analytic core)

Design: `docs/blueprints/chen.md`, the C3c row.  `Salt.Chen.bilinear_hLargeDisc` (C3c′)
reduced the large-conductor bilinear energy to two named cores; C3c″
(`Salt.Chen.hMainEnergy_discharge`) closed the first.  This file lands the honest
structure of the second — `hErrSum`, the summed α/β coprimality error — via the
**Barban–Davenport–Halberstam Möbius `e`-fold**.

## The obstruction (from the C3c″ flag)

The crude bound `‖A_d − A⋆‖ ≤ #{m ≤ X : gcd(m,d) > 1}` makes the naive `d`-sum
`∑_{d≤D}(1/φd)(∑_{p∣d}X/p)·Y ≈ XY·D` — **too big by `D`** (giving `(XY)^{3/2}/(log)^B`).
The honest fix is the `e`-fold, which this file lands.

## What this file lands (sorry-free)

1. **The `e`-fold identity** (`bilinTwist_efold`) — FULL.  From
   `Salt.Chen.bilinTwist_sub_primitive_eq` + the Möbius inclusion–exclusion
   `[gcd(m,d)>1] = −∑_{e∣d, e>1, e∣m} μ(e)` + reindexing `m = e·m'` and the complete
   multiplicativity of `χ⋆`:
   ```
   A_d(χ) − A⋆ = ∑_{e∣d, e>1} μ(e)·χ⋆(e)·A^{(e)}(χ⋆),   A^{(e)}(ψ) = ∑_{m'≤⌊X/e⌋} α(e·m')·ψ(m').
   ```
   Each term is a shifted-scale (`⌊X/e⌋`) twist of the dilated coefficient
   `α^{(e)}(m') = α(e·m')` (still `‖·‖ ≤ 1`) — the exact BDH replacement of the crude
   count.  Its `L¹` bound `norm_bilinTwist_sub_le_efold` follows (`|μ(e)| ≤ 1`,
   `‖χ⋆(e)‖ ≤ 1`).

2. **The reorganization** (`hErrSum_reorg`) — FULL.  The exact `hErrSum` slot of
   `bilinear_hLargeDisc` is bounded by `∑_{e=2}^{D} EfoldTerm e`: per `(d,χ)` the
   `e`-fold `L¹` bound replaces both imprimitive-minus-primitive differences (α- and
   β-side) by their `e`-fold sums, then the finite `(χ,e)` and `(d,e)` sums are swapped
   (`Finset.sum_comm`, `Finset.sum_comm'`) to pull `e` outermost over the global index
   `[2,D]`, with the modulus constraint `e ∣ d` collected into `EfoldTerm`.

3. **The `e`-sum convergence envelope** (`sum_inv_sq_Icc_le`, `sum_inv_sq_Icc_le_one`) —
   FULL.  `∑_{e=2}^{N} 1/e² ≤ 1 − 1/N ≤ 1` (telescoping induction) — the arithmetic
   certifying that a `1/e²`-decaying per-`e` glue sums to `O(1)`, the real content behind
   the BDH `∑_e 1/(e·φe)`-type convergence.

4. **The discharge** (`hErrSum_discharge`) — the exact `hErrSum` slot, closed modulo a
   single **named per-`e` glue** `hGlue : EfoldTerm e ≤ G e` and its convergent sum
   `hGsum : ∑_{e} G e ≤ Kerr·XY/(log)^A`.  This is the honest PB-floor deliverable: the
   identity + the reorganization + the convergence, with the per-`e` shifted-scale energy
   bound (a re-run of the C3c″ energy machinery at scale `(⌊X/e⌋, Y)` with the `e ∣ d`
   density) exposed as the one remaining glue — mirroring how `bilinear_hLargeDisc` itself
   exposes `hMainEnergy`/`hErrSum`, and `general_BV_closed` exposes `hLargeDisc`.

## FLAG (Iron Rule 4 / PB-floor) — the per-`e` energy glue

`hErrSum_discharge` takes the per-`e` bound `hGlue` as a **named hypothesis** (the single
remaining analytic core).  `EfoldTerm e` is another instance of the C3c″ energy machinery
(`hMainEnergy_discharge`) at the shifted scale `(⌊X/e⌋, Y)` restricted to moduli `d` with
`e ∣ d`; its honest bound `EfoldTerm e ≤ (c/φe)·(⌊X/e⌋)·Y/(log)^{A+1}` (via the `swapPhi`
`e ∣ d` density `∑_{d:e∣d}1/φd ≤ (c/φe)(1+log D)` + the per-`d` shell) sums by
`∑_e 1/(e·φe) < ∞` — the `1/e²` envelope `sum_inv_sq_Icc_le_one` is the representative
convergent shape.  Re-running the full dyadic energy engine per `e` with the scale
bookkeeping is the deferred research core, recorded in `docs/blueprints/flags.md` (C3c‴).
Consequently `general_BV_final` closes modulo this single per-`e` glue (both structural
cores — identity and reorganization — are landed here).

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

/-- **Reindex over multiples (`e ∣ m`).**  `∑_{m∈[1,X], e∣m} g(m) = ∑_{m'∈[1,⌊X/e⌋]} g(e·m')`
(the bijection `m ↦ m/e`, `m' ↦ e·m'`).  The scale contraction `X ↦ ⌊X/e⌋` of the e-fold. -/
lemma reindex_mult (e X : ℕ) (he : 1 ≤ e) (g : ℕ → ℂ) :
    ∑ m ∈ (Finset.Icc 1 X).filter (fun m => e ∣ m), g m
      = ∑ m' ∈ Finset.Icc 1 (X / e), g (e * m') := by
  refine Finset.sum_nbij' (fun m => m / e) (fun m' => e * m') ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmX⟩, hem⟩ := hm
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hmX⟩
    exact Nat.one_le_div_iff (by omega) |>.mpr (Nat.le_of_dvd (by omega) hem)
  · intro m' hm'
    rw [Finset.mem_Icc] at hm'
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith [hm'.1], ?_⟩, Dvd.intro _ rfl⟩
    calc e * m' ≤ e * (X / e) := by exact Nat.mul_le_mul_left e hm'.2
      _ ≤ X := Nat.mul_div_le X e
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro m' hm'
    exact Nat.mul_div_cancel_left m' (by omega)
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Nat.mul_div_cancel' hm.2]

/-- **The Möbius coprimality indicator.**  `[IsUnit(m mod d)] = ∑_{e∣d, e∣m} μ(e)`
(`∑_{e∣gcd(m,d)} μ(e) = [gcd=1]`, `coe_mul_zeta_apply` + `moebius_mul_coe_zeta`). -/
lemma isUnit_eq_sum_moebius (d m : ℕ) [NeZero d] :
    (if IsUnit ((m : ℕ) : ZMod d) then (1 : ℂ) else 0)
      = ∑ e ∈ (d.divisors).filter (fun e => e ∣ m), (ArithmeticFunction.moebius e : ℂ) := by
  have hd : d ≠ 0 := NeZero.ne d
  have hfilter : (d.divisors).filter (fun e => e ∣ m) = (Nat.gcd m d).divisors := by
    rw [show (d.divisors).filter (fun e => e ∣ m)
          = (d.divisors).filter (fun e => e ∣ Nat.gcd m d) from ?_]
    · exact Nat.divisors_filter_dvd_of_dvd hd (Nat.gcd_dvd_right m d)
    · apply Finset.filter_congr
      intro e he
      rw [Nat.mem_divisors] at he
      constructor
      · intro hem; exact Nat.dvd_gcd hem he.1
      · intro heg; exact heg.trans (Nat.gcd_dvd_left m d)
  rw [hfilter]
  have hsum : ∑ e ∈ (Nat.gcd m d).divisors, (ArithmeticFunction.moebius e : ℂ)
      = if Nat.gcd m d = 1 then (1 : ℂ) else 0 := by
    have := ArithmeticFunction.coe_mul_zeta_apply (R := ℤ)
      (f := (ArithmeticFunction.moebius)) (x := Nat.gcd m d)
    rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply] at this
    have hcast : ((if Nat.gcd m d = 1 then (1 : ℤ) else 0 : ℤ) : ℂ)
        = if Nat.gcd m d = 1 then (1 : ℂ) else 0 := by
      split <;> simp
    calc ∑ e ∈ (Nat.gcd m d).divisors, (ArithmeticFunction.moebius e : ℂ)
        = ((∑ e ∈ (Nat.gcd m d).divisors, ArithmeticFunction.moebius e : ℤ) : ℂ) := by
          push_cast; ring
      _ = ((if Nat.gcd m d = 1 then (1 : ℤ) else 0 : ℤ) : ℂ) := by rw [← this]
      _ = if Nat.gcd m d = 1 then (1 : ℂ) else 0 := hcast
  rw [hsum]
  by_cases h : IsUnit ((m : ℕ) : ZMod d)
  · rw [if_pos h, if_pos ((ZMod.isUnit_iff_coprime m d).mp h)]
  · rw [if_neg h, if_neg (fun hg => h ((ZMod.isUnit_iff_coprime m d).mpr hg))]

/-- The `e > 1` divisor index set (BDH e-fold support). -/
noncomputable def efoldSet (d : ℕ) : Finset ℕ := (d.divisors).filter (fun e => 1 < e)

/-- Combined indicator: `[¬IsUnit(m mod d)] = -∑_{e>1, e∣d, e∣m} μ(e)`. -/
lemma notUnit_eq_neg_sum_moebius (d m : ℕ) [NeZero d] :
    (if ¬ IsUnit ((m : ℕ) : ZMod d) then (1 : ℂ) else 0)
      = - ∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0) := by
  have hd : d ≠ 0 := NeZero.ne d
  -- split the full-divisor filtered moebius sum at e = 1
  have hsplit : ∑ e ∈ (d.divisors).filter (fun e => e ∣ m), (ArithmeticFunction.moebius e : ℂ)
      = 1 + ∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0) := by
    rw [Finset.sum_filter]
    rw [← Finset.sum_filter_add_sum_filter_not (d.divisors) (fun e => 1 < e)
          (fun e => if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0)]
    have hpart2 : ∑ e ∈ (d.divisors).filter (fun e => ¬ 1 < e),
          (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0) = 1 := by
      have hset : (d.divisors).filter (fun e => ¬ 1 < e) = {1} := by
        ext e
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hed, _⟩, hle⟩
          have : 1 ≤ e :=
            Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hd (Nat.eq_zero_of_zero_dvd hed))
          omega
        · rintro rfl; exact ⟨⟨one_dvd d, hd⟩, by omega⟩
      rw [hset, Finset.sum_singleton, if_pos (one_dvd m)]
      simp
    rw [hpart2, add_comm]
    congr 1
  -- combine with the IsUnit form
  have hkey : (if IsUnit ((m : ℕ) : ZMod d) then (1 : ℂ) else 0)
      = 1 + ∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0) :=
    (isUnit_eq_sum_moebius d m).trans hsplit
  by_cases h : IsUnit ((m : ℕ) : ZMod d)
  · rw [if_neg (not_not.mpr h), if_pos h] at *
    linear_combination -hkey
  · rw [if_pos h, if_neg h] at *
    linear_combination -hkey

/-- **The BDH Möbius e-fold identity (α-side).**  The imprimitive-minus-primitive
difference is a `μ`-weighted, `χ⋆`-modulated sum of shifted-scale (`X/e`) twists of
the dilated coefficient `α^{(e)}(m') = α(e·m')` — the honest replacement for the crude
`#{m : gcd(m,d)>1}` bound. -/
theorem bilinTwist_efold {d : ℕ} [NeZero d] (α : ℕ → ℂ) (X : ℕ)
    (χ : DirichletCharacter ℂ d) :
    bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter
      = ∑ e ∈ efoldSet d,
          (ArithmeticFunction.moebius e : ℂ)
            * χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)
            * bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter := by
  rw [bilinTwist_sub_primitive_eq]
  set f := χ.conductor with hf
  set ψ := χ.primitiveCharacter with hpsi
  set S : ℕ → ℂ := fun m => α m * ψ ((m : ℕ) : ZMod f) with hSdef
  -- rewrite -∑_{filter ¬IsUnit} S as double sum
  have hstep1 : (∑ m ∈ (Finset.Icc 1 X).filter (fun m => ¬ IsUnit ((m : ℕ) : ZMod d)), S m)
      = ∑ m ∈ Finset.Icc 1 X, (if ¬ IsUnit ((m : ℕ) : ZMod d) then (1 : ℂ) else 0) * S m := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases h : ¬ IsUnit ((m : ℕ) : ZMod d) <;> simp [h]
  rw [hstep1]
  have hstep2 : ∀ m, (if ¬ IsUnit ((m : ℕ) : ZMod d) then (1 : ℂ) else 0) * S m
      = - ∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0) * S m := by
    intro m
    rw [notUnit_eq_neg_sum_moebius d m, neg_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun m _ => hstep2 m), Finset.sum_neg_distrib, neg_neg,
    Finset.sum_comm]
  -- per-e evaluation
  refine Finset.sum_congr rfl (fun e he => ?_)
  simp only [efoldSet, Finset.mem_filter, Nat.mem_divisors] at he
  have he1 : 1 ≤ e := by omega
  have step_ite : ∀ m, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0) * S m
      = if e ∣ m then (ArithmeticFunction.moebius e : ℂ) * S m else 0 := by
    intro m; split <;> ring
  rw [Finset.sum_congr rfl (fun m _ => step_ite m), ← Finset.sum_filter, ← Finset.mul_sum,
    reindex_mult e X he1 S]
  -- ∑_{m'} S(e*m') = ψ(e) * bilinTwist^{(e)}
  have hinner : ∑ m' ∈ Finset.Icc 1 (X / e), S (e * m')
      = ψ ((e : ℕ) : ZMod f) * bilinTwist (fun m' => α (e * m')) (X / e) f ψ := by
    unfold bilinTwist
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    simp only [hSdef]
    rw [Nat.cast_mul, map_mul]
    ring
  rw [hinner, ← mul_assoc]

/-- **The e-fold `L¹` bound (α-side).**  `‖A_d − A⋆‖ ≤ ∑_{e∣d, e>1} ‖A^{(e)}(χ⋆)‖`, the
triangle bound on the e-fold identity (`|μ(e)| ≤ 1`, `‖χ⋆(e)‖ ≤ 1`). -/
theorem norm_bilinTwist_sub_le_efold {d : ℕ} [NeZero d] (α : ℕ → ℂ) (X : ℕ)
    (χ : DirichletCharacter ℂ d) :
    ‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
      ≤ ∑ e ∈ efoldSet d,
          ‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖ := by
  rw [bilinTwist_efold]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun e _ => ?_)
  rw [norm_mul, norm_mul]
  have hμ : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    have := ArithmeticFunction.abs_moebius_le_one (n := e)
    exact_mod_cast this
  have hψ : ‖χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)‖ ≤ 1 :=
    DirichletCharacter.norm_le_one _ _
  have hT : (0 : ℝ)
      ≤ ‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖ :=
    norm_nonneg _
  calc ‖(ArithmeticFunction.moebius e : ℂ)‖ * ‖χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)‖
          * ‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
      ≤ 1 * 1 * ‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖ := by
        apply mul_le_mul _ (le_refl _) hT (by positivity)
        exact mul_le_mul hμ hψ (norm_nonneg _) (by norm_num)
    _ = ‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖ := by ring

/-- **The e-sum convergence envelope.**  `∑_{e=2}^{N} 1/e² ≤ 1 − 1/N` (induction,
`1/(n+1)² ≤ 1/n − 1/(n+1)`).  Certifies that a `1/e²`-decaying per-`e` glue sums to
`O(1)` — the arithmetic behind the BDH `∑_e 1/(e·φe)`-type convergence. -/
theorem sum_inv_sq_Icc_le (N : ℕ) :
    ∑ e ∈ Finset.Icc 2 N, (1 / (e : ℝ) ^ 2) ≤ 1 - 1 / (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hn1pos : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
      have hkey : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hnpos) (ne_of_gt hn1pos),
          div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        nlinarith [hn1]
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      calc (∑ e ∈ Finset.Icc 2 n, (1 / (e : ℝ) ^ 2)) + 1 / ((n : ℝ) + 1) ^ 2
          ≤ (1 - 1 / (n : ℝ)) + (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :=
            add_le_add ih hkey
        _ = 1 - 1 / ((n : ℝ) + 1) := by ring

/-- `∑_{e=2}^{N} 1/e² ≤ 1`. -/
theorem sum_inv_sq_Icc_le_one (N : ℕ) : ∑ e ∈ Finset.Icc 2 N, (1 / (e : ℝ) ^ 2) ≤ 1 := by
  refine (sum_inv_sq_Icc_le N).trans ?_
  have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  linarith

/-! ## The reorganized per-`e` error term and the `hErrSum` discharge -/

/-- Pull a scalar through a double sum and swap the order: `c·∑_i∑_j P = ∑_j c·∑_i P`. -/
lemma mul_double_sum_comm {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ℝ) (P : ι → κ → ℝ) :
    c * ∑ i ∈ s, ∑ j ∈ t, P i j = ∑ j ∈ t, c * ∑ i ∈ s, P i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

open Classical in
/-- **The per-`e` BDH error term.**  The `e`-shifted-scale (`X/e`, `Y/e`) energy over the
large moduli `d` that are multiples of `e`: the `α`-side pairs the dilated twist
`A^{(e)}(χ⋆) = ∑_{m'≤X/e} α(e·m')·χ⋆(m')` against the imprimitive `B_d(χ)`; the `β`-side
pairs the primitive `A⋆(χ⋆)` against the dilated `B^{(e)}(χ⋆)`.  Reorganizing
`hErrSum`'s `d`-sum via the `e`-fold produces `∑_{e=2}^{D} EfoldTerm e`. -/
noncomputable def EfoldTerm (α β : ℕ → ℂ) (X Y D0 : ℕ) (Dset : Finset ℕ) (e : ℕ) : ℝ :=
  ∑ d ∈ (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d),
    (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        (‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β Y d χ‖
          + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist (fun n' => β (e * n')) (Y / e) χ.conductor χ.primitiveCharacter‖)

open Classical in
/-- **The `hErrSum` reorganization (BDH `e`-fold, FULL).**  The exact `hErrSum` slot of
`bilinear_hLargeDisc` is bounded by the reorganized per-`e` sum `∑_{e=2}^{D} EfoldTerm e`.
Mechanism: per `(d,χ)` the `e`-fold `L¹` bound `norm_bilinTwist_sub_le_efold` replaces each
imprimitive-minus-primitive difference by `∑_{e∣d, e>1} ‖·^{(e)}‖`; the finite `(χ,e)` and
`(d,e)` sums are then swapped (`sum_comm`, `sum_comm'`) to pull `e` outermost over the
global index `[2,D]`.  This is the honest replacement of the crude `#{m:gcd>1}` bound that
was "too big by `D`". -/
theorem hErrSum_reorg (α β : ℕ → ℂ) (X Y D D0 : ℕ) (Dset : Finset ℕ)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ‖
                + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
      ≤ ∑ e ∈ Finset.Icc 2 D, EfoldTerm α β X Y D0 Dset e := by
  classical
  set Dset' := Dset.filter (fun d => ¬ d ≤ D0) with hDset'def
  -- the per-(d,e) summand
  set f : ℕ → ℕ → ℝ := fun d e =>
    (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        (‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β Y d χ‖
          + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist (fun n' => β (e * n')) (Y / e) χ.conductor χ.primitiveCharacter‖)
    with hfdef
  calc ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ‖
                + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
      ≤ ∑ d ∈ Dset', ∑ e ∈ efoldSet d, f d e := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [hDset'def, Finset.mem_filter] at hd
        have hd1 : 1 ≤ d := hDset1 d hd.1
        -- per-(d,χ) e-fold bound  (NeZero scoped inside so the outer erase-sums keep the
        -- goal's `propDecidable` instance — avoids the `FunLike` instance split)
        have step1 : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ‖
                + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖
              ≤ ∑ e ∈ efoldSet d,
                  (‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
                        * ‖bilinTwist β Y d χ‖
                    + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                        * ‖bilinTwist (fun n' => β (e * n')) (Y / e) χ.conductor
                            χ.primitiveCharacter‖) := by
          intro χ _
          haveI : NeZero d := ⟨by omega⟩
          have hAsub := norm_bilinTwist_sub_le_efold α X χ
          have hBsub := norm_bilinTwist_sub_le_efold β Y χ
          have hBd : (0 : ℝ) ≤ ‖bilinTwist β Y d χ‖ := norm_nonneg _
          have hAs : (0 : ℝ) ≤ ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖ := norm_nonneg _
          calc ‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                    * ‖bilinTwist β Y d χ‖
                  + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                    * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖
              ≤ (∑ e ∈ efoldSet d,
                    ‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖)
                      * ‖bilinTwist β Y d χ‖
                + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                      * (∑ e ∈ efoldSet d,
                          ‖bilinTwist (fun n' => β (e * n')) (Y / e) χ.conductor
                            χ.primitiveCharacter‖) := by
                  apply add_le_add
                  · exact mul_le_mul_of_nonneg_right hAsub hBd
                  · exact mul_le_mul_of_nonneg_left hBsub hAs
            _ = ∑ e ∈ efoldSet d,
                    (‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
                          * ‖bilinTwist β Y d χ‖
                      + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                          * ‖bilinTwist (fun n' => β (e * n')) (Y / e) χ.conductor
                              χ.primitiveCharacter‖) := by
                  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        calc (1 / (d.totient : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                  (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                        * ‖bilinTwist β Y d χ‖
                      + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                        * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
            ≤ (1 / (d.totient : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                  ∑ e ∈ efoldSet d,
                    (‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
                          * ‖bilinTwist β Y d χ‖
                      + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                          * ‖bilinTwist (fun n' => β (e * n')) (Y / e) χ.conductor
                              χ.primitiveCharacter‖) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum step1) (by positivity)
          _ = ∑ e ∈ efoldSet d, f d e := by
              rw [mul_double_sum_comm]
    _ = ∑ e ∈ Finset.Icc 2 D, ∑ d ∈ Dset'.filter (fun d => e ∣ d), f d e := by
        refine Finset.sum_comm' ?_
        intro d e
        constructor
        · rintro ⟨hd, he⟩
          have hdmem : d ∈ Dset := by rw [hDset'def, Finset.mem_filter] at hd; exact hd.1
          have hd1 : 1 ≤ d := hDset1 d hdmem
          have hdD : d ≤ D := hDsetD d hdmem
          simp only [efoldSet, Finset.mem_filter, Nat.mem_divisors] at he
          have hed : e ≤ d := Nat.le_of_dvd (by omega) he.1.1
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_filter]; exact ⟨hd, he.1.1⟩
          · rw [Finset.mem_Icc]; omega
        · rintro ⟨hd, he⟩
          rw [Finset.mem_filter] at hd
          rw [Finset.mem_Icc] at he
          have hdmem : d ∈ Dset := by rw [hDset'def, Finset.mem_filter] at hd; exact hd.1.1
          have hd1 : 1 ≤ d := hDset1 d hdmem
          refine ⟨hd.1, ?_⟩
          simp only [efoldSet, Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨hd.2, by omega⟩, by omega⟩
    _ = ∑ e ∈ Finset.Icc 2 D, EfoldTerm α β X Y D0 Dset e := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        simp only [EfoldTerm, hfdef, hDset'def]

open Classical in
/-- **C3c‴ — the `hErrSum` discharge (BDH `e`-fold), the LAST core of keystone 2.**
The exact `hErrSum` slot of `bilinear_hLargeDisc`, discharged by the BDH Möbius `e`-fold:
`hErrSum_reorg` reorganizes the α/β coprimality error into `∑_{e=2}^{D} EfoldTerm e` (the
honest fix for the crude bound that was "too big by `D`"); the per-`e` glue `hGlue`
supplies the shifted-scale (`X/e`, `Y/e`) energy bound and `hGsum` its convergent sum
(certified in the `1/e²` envelope by `sum_inv_sq_Icc_le_one`).  Composes with
`hMainEnergy_discharge` (C3c″) to close both cores of `bilinear_hLargeDisc`. -/
theorem hErrSum_discharge (α β : ℕ → ℂ) (X Y D D0 : ℕ) (Dset : Finset ℕ) {A Kerr : ℝ}
    (G : ℕ → ℝ)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hGlue : ∀ e, 2 ≤ e → e ≤ D → EfoldTerm α β X Y D0 Dset e ≤ G e)
    (hGsum : ∑ e ∈ Finset.Icc 2 D, G e
        ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ‖
                + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
      ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  refine le_trans (hErrSum_reorg α β X Y D D0 Dset hDset1 hDsetD) ?_
  refine le_trans (Finset.sum_le_sum (fun e he => ?_)) hGsum
  rw [Finset.mem_Icc] at he
  exact hGlue e he.1 he.2

end Salt.Chen
