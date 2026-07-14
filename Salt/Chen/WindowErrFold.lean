/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WindowClose
import Salt.Chen.AlphaClose

/-!
# WBV5 — discharging WindowClose's two named slots (`hMainEnergy` + `hErrSum`)

Design: `docs/blueprints/flags.md`, the `2026-07-14 WBV4`/`WBV2`/`WBV1` entries and the
`2026-07-13 C54-RECON … FROZEN` freeze (route (i), the one-sided cutoff carrier).  This file
closes the two named analytic slots that `Salt.Chen.cutoff_hLargeDisc` /
`Salt.Chen.general_BV_cutoff_final` (WBV4) expose:

* **`hMainEnergy`** — the dyadic-in-conductor shell arithmetic on the FULL-`α`/`β` primitive
  windowed block energy `∑_{2≤f≤D} (1/φf)·cutoffPrimEnergy α β X Y T f`;
* **`hErrSum`** — the summed `α`-side coprimality `L¹` error of the cutoff twist.

Both are mirrors of the landed *bilinear* discharges (`Salt.Chen.hMainEnergy_discharge`,
`Salt.Chen.ErrFold`/`Salt.Chen.AlphaSide`/`Salt.Chen.AlphaClose`) transported to the *cutoff*
carrier, riding the sharp cutoff `m·n ≤ T` through the machinery.

## What this file lands (all sorry-free, axiom-clean)

1. `hMainEnergy_cutoff_discharge` — the mechanical half.  Mirror of
   `hMainEnergy_discharge` at `dyadic_energy_le_cutoff`: split `[2,D]` at `D0`, the small part
   named (`hSmallCut`, the window small-conductor SW input — the cutoff twist does not factor,
   so the SW cancellation is packaged at the `cutoffPrimEnergy` level, exactly as the landed
   discharge names `hβSW`), the large part the WBV2 four-term (`dyadic_energy_le_cutoff` +
   `four_term_scale_le`), the `4(1+log D)` prefactor folded.  `Kmain = 6(Kβ+448+32√26)`.

2. The cutoff `e`-fold chain (`β = blockPrimeInd N`, `d < N`):
   * `cutoffTwist_sub_efold_blockPrimeInd` — the BDH Möbius `e`-fold identity for the cutoff
     twist difference: the imprimitive-vs-primitive difference is a `μ`-weighted, `χ⋆`-modulated
     sum of *dilated-and-shrunk* cutoff twists at scale `(⌊X/e⌋, Y, ⌊T/e⌋)`.  The β-side never
     appears — `blockPrimeInd N` is coprime-supported (`coprimeRestrict_blockPrimeInd`), so the
     cutoff difference is purely `α`-side (mirrors the recon's "no second error" finding).
   * `norm_cutoffTwist_sub_le_efold_blockPrimeInd` — the triangle `L¹` bound.
   * `cutoffEfoldTerm` + `cutoffEfoldTerm_reorg` — the per-`e` term and the reorganization of
     `hErrSum`'s `d`-sum into `∑_{e=2}^{D} cutoffEfoldTerm e` (single-norm mirror of
     `hErrSum_reorg`).
   * `hErrSum_cutoff_discharge` — the `hErrSum` slot closed modulo a named per-`e` glue
     `hGlue`/`hGsum` (mirror of `hErrSum_discharge`; the `1/e` harmonic envelope
     `sum_inv_Icc_le_log`).

3. `general_BV_cutoff_closed` — `general_BV_cutoff_final` with both slots fed, mirroring
   `general_BV_alpha_final`'s final shape: the residual inputs are the operating-point pieces
   (`hSmallCut`, the per-`e` envelope) plus the structural set.  See the section header for the
   exact threshold list the H-glue must supply.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. `hMainEnergy_cutoff_discharge` — the mechanical half (`hMainEnergy_discharge` mirror) -/

open Classical in
/-- **WBV5 (item 1, FULL) — the `hMainEnergy` cutoff discharge.**  Mirror of
`hMainEnergy_discharge` at the cutoff carrier: the FULL windowed primitive block energy
`∑_{2≤f≤D} (1/φf)·cutoffPrimEnergy α β X Y T f` splits at `D0 = 2^{k0}` into the small part
(named `hSmallCut` — the window small-conductor SW input, at `L^{A+1}`; the cutoff twist does
not factor so the SW cancellation is packaged at the energy level, exactly as the landed
discharge names `hβSW`) and the large part `∑_{D0<f≤D}` priced by WBV2's four-term
(`dyadic_energy_le_cutoff`) scaled by `four_term_scale_le` to `(448+32√26)·XY/L^{A+1}`; folding
the `4(1+log D) ≤ 6L` prefactor gives the exact `hMainEnergy` slot with `Kmain = 6(Kβ+448+32√26)`.
Honest operating scale identical to `hMainEnergy_discharge` (`X,Y ≥ 2`, `1 ≤ D`,
`D ≤ √(XY)/L^B`, `B ≥ A+2`, `D0 = 2^{k0}` with `L^{C0} ≤ 2·2^{k0}`, `C0 ≥ A+2`,
`X,Y ≥ L^{2A+6}`) — no `hdiv` (no `e`-dilation on the plain window path). -/
theorem hMainEnergy_cutoff_discharge {X Y T D0 D k0 K : ℕ} {A B C0 Kβ : ℝ}
    (hA : 0 ≤ A) (hX2 : 2 ≤ X) (hY2 : 2 ≤ Y) (h1D : 1 ≤ D)
    (hB : A + 2 ≤ B) (hC0 : A + 2 ≤ C0)
    (hD0eq : D0 = 2 ^ k0) (h2D0 : 2 ≤ D0) (hD0D : D0 ≤ D)
    (hK : K = Nat.log 2 D)
    (hDscale : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ B)
    (hD0lo : (Real.log ((X : ℝ) * (Y : ℝ))) ^ C0 ≤ 2 * (2 : ℝ) ^ k0)
    (hXsqrt : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 3) ≤ Real.sqrt X)
    (hYsqrt : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 3) ≤ Real.sqrt Y)
    (hKβ : 0 ≤ Kβ) (α β : ℕ → ℂ) (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1)
    (hSmallCut : ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
        ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) :
    4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
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
  -- Step 0: split `[2,D]` at `D0` into small (`hSmallCut`) + large (WBV2 four-term).
  have hsplit : ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      = ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
        + ∑ f ∈ Finset.Icc (D0 + 1) D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f := by
    rw [show Finset.Icc 2 D = Finset.Ioc 1 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc 2 D0 = Finset.Ioc 1 D0 by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc (D0 + 1) D = Finset.Ioc D0 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    exact (Finset.sum_Ioc_consecutive _ (by omega : 1 ≤ D0) hD0D).symm
  set L := Real.log ((X : ℝ) * (Y : ℝ)) with hLdef
  -- `hsum` : the same shape `mainEnergy_sum_le` produces (small `Kβ·XY/L^{A+1}` + four-term).
  have hsum : ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
      ≤ Kβ * ((X : ℝ) * (Y : ℝ)) / L ^ (A + 1)
        + (2 * (1 + Real.log Y) * Real.sqrt X * Real.sqrt Y)
            * (4 * (2 : ℝ) ^ (K + 1)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((X : ℝ) + 1))
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
              + Real.sqrt (13 * ((X : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0)) := by
    rw [hsplit]
    exact add_le_add hSmallCut (dyadic_energy_le_cutoff hD0eq hK hYpos α β hα hβ)
  have hft := four_term_scale_le (A := A) (B := B) (C0 := C0) hA hX2 hY2 h1D hB hC0
    hDscale hK hD0lo hXsqrt hYsqrt
  have hLApos : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
  have hLAApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos _
  have hC'nn : (0 : ℝ) ≤ Kβ + 448 + 32 * Real.sqrt 26 := by positivity
  -- Step 1: `∑ ≤ (Kβ + 448 + 32√26)·XY/L^{A+1}`.
  have hsum2 : ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
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
          * ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α β X Y T f
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

/-! ## 2. The cutoff `e`-fold identity (`β = blockPrimeInd N`, `d < N`) -/

open Classical in
/-- **WBV5 — the BDH Möbius `e`-fold identity for the cutoff twist (FULL).**  For `d < N` the
imprimitive-vs-primitive difference of the windowed twist is a `μ`-weighted, `χ⋆`-modulated sum
of *dilated-and-shrunk* cutoff twists at scale `(⌊X/e⌋, Y, ⌊T/e⌋)`:
```
cutoffTwist α β X Y T d χ − cutoffTwist α β X Y T (conductor χ) χ⋆
  = ∑_{e∣d, e>1} μ(e)·χ⋆(e)·cutoffTwist (α∘(e·)) β (⌊X/e⌋) Y (⌊T/e⌋) (conductor χ) χ⋆.
```
The β-side never appears: `β = blockPrimeInd N` is coprime-supported mod `d < N`
(`coprimeRestrict_blockPrimeInd`), so the fold collapses the difference to the `α`-side only
(the recon's "no second error" finding).  Then `notUnit_eq_neg_sum_moebius` folds the
non-coprimality indicator, and `reindex_mult` (on `m`) plus the cutoff reindex
`e·m'·n ≤ T ⟺ m'·n ≤ ⌊T/e⌋` (`Nat.le_div_iff_mul_le`) and `χ⋆` multiplicativity produce the
dilated cutoff twists.  Mirror of `bilinTwist_efold` at the cutoff carrier. -/
theorem cutoffTwist_sub_efold_blockPrimeInd {d N : ℕ} [NeZero d] (hd : d < N)
    (α : ℕ → ℂ) (X Y T : ℕ) (χ : DirichletCharacter ℂ d) :
    cutoffTwist α (blockPrimeInd N) X Y T d χ
        - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter
      = ∑ e ∈ efoldSet d,
          (ArithmeticFunction.moebius e : ℂ)
            * χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)
            * cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                χ.conductor χ.primitiveCharacter := by
  classical
  set β : ℕ → ℂ := blockPrimeInd N with hβ
  set f := χ.conductor with hf
  set ψ := χ.primitiveCharacter with hpsi
  -- fold + coprimeRestrict_blockPrimeInd: the difference is purely α-side.
  have hfold : cutoffTwist α β X Y T d χ = cutoffTwist (coprimeRestrict α d) β X Y T f ψ := by
    rw [cutoffTwist_coprimeRestrict_primitive α β X Y T χ, coprimeRestrict_blockPrimeInd hd]
  rw [hfold]
  -- Step 1: rewrite the difference as `∑_m (∑_e [e∣m]μe) · Inner(m)`.
  have hstep1 : cutoffTwist (coprimeRestrict α d) β X Y T f ψ - cutoffTwist α β X Y T f ψ
      = ∑ m ∈ Finset.Icc 1 X,
          (∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0))
            * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
                α m * β n * ψ ((m * n : ℕ) : ZMod f) := by
    unfold cutoffTwist
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hcoeff : coprimeRestrict α d m - α m
        = (∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0)) * α m := by
      have hnu := notUnit_eq_neg_sum_moebius d m
      have hS : (∑ e ∈ efoldSet d, (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0))
          = -(if ¬ IsUnit ((m : ℕ) : ZMod d) then (1 : ℂ) else 0) := by rw [hnu]; ring
      rw [hS]; unfold coprimeRestrict
      by_cases hu : IsUnit ((m : ℕ) : ZMod d) <;> simp [hu]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show coprimeRestrict α d m * β n * ψ ((m * n : ℕ) : ZMod f)
            - α m * β n * ψ ((m * n : ℕ) : ZMod f)
          = (coprimeRestrict α d m - α m) * (β n * ψ ((m * n : ℕ) : ZMod f)) by ring, hcoeff]
    ring
  rw [hstep1]
  -- Step 2: distribute the `∑_e` and swap to pull `e` outermost.
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have he0 : 0 < e := by
    simp only [efoldSet, Finset.mem_filter, Nat.mem_divisors] at he; omega
  have he1 : 1 ≤ e := he0
  -- collapse `(if e∣m then μe else 0)·Inner` to a filtered `μe·Inner`, then reindex m = e·m'.
  have hmob : ∀ m,
      (if e ∣ m then (ArithmeticFunction.moebius e : ℂ) else 0)
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
              α m * β n * ψ ((m * n : ℕ) : ZMod f)
        = if e ∣ m then (ArithmeticFunction.moebius e : ℂ)
            * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
                α m * β n * ψ ((m * n : ℕ) : ZMod f) else 0 := by
    intro m; split <;> ring
  rw [Finset.sum_congr rfl (fun m _ => hmob m), ← Finset.sum_filter, ← Finset.mul_sum,
    reindex_mult e X he1 (fun m => ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
      α m * β n * ψ ((m * n : ℕ) : ZMod f))]
  -- per m': the cutoff reindex `e·m'·n ≤ T ⟺ m'·n ≤ T/e` and `ψ` multiplicativity.
  have hInner : ∀ m' : ℕ,
      (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => e * m' * n ≤ T),
          α (e * m') * β n * ψ ((e * m' * n : ℕ) : ZMod f))
        = ψ ((e : ℕ) : ZMod f) * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m' * n ≤ T / e),
            α (e * m') * β n * ψ ((m' * n : ℕ) : ZMod f) := by
    intro m'
    have hfe : (Finset.Icc 1 Y).filter (fun n => e * m' * n ≤ T)
        = (Finset.Icc 1 Y).filter (fun n => m' * n ≤ T / e) := by
      refine Finset.filter_congr (fun n _ => ?_)
      rw [show e * m' * n = m' * n * e by ring]
      exact (Nat.le_div_iff_mul_le he0).symm
    rw [hfe, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show (e * m' * n : ℕ) = (e * (m' * n) : ℕ) by ring, Nat.cast_mul, map_mul]
    ring
  rw [Finset.sum_congr rfl (fun m' _ => hInner m'), ← Finset.mul_sum]
  -- reassemble the cutoff twist and reorder the scalars.
  rw [show cutoffTwist (fun m' => α (e * m')) β (X / e) Y (T / e) f ψ
        = ∑ m' ∈ Finset.Icc 1 (X / e),
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m' * n ≤ T / e),
              α (e * m') * β n * ψ ((m' * n : ℕ) : ZMod f) from rfl]
  ring

open Classical in
/-- **WBV5 — the cutoff `e`-fold `L¹` bound (FULL).**  Triangle bound on
`cutoffTwist_sub_efold_blockPrimeInd`: `‖A_d − A⋆‖ ≤ ∑_{e∣d, e>1} ‖A^{(e)}‖` where `A^{(e)}` is
the dilated-and-shrunk cutoff twist (`|μ(e)| ≤ 1`, `‖χ⋆(e)‖ ≤ 1`).  Mirror of
`norm_bilinTwist_sub_le_efold`. -/
theorem norm_cutoffTwist_sub_le_efold_blockPrimeInd {d N : ℕ} [NeZero d] (hd : d < N)
    (α : ℕ → ℂ) (X Y T : ℕ) (χ : DirichletCharacter ℂ d) :
    ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
        - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ ∑ e ∈ efoldSet d,
          ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
              χ.conductor χ.primitiveCharacter‖ := by
  rw [cutoffTwist_sub_efold_blockPrimeInd hd]
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
      ≤ ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
          χ.conductor χ.primitiveCharacter‖ := norm_nonneg _
  calc ‖(ArithmeticFunction.moebius e : ℂ)‖ * ‖χ.primitiveCharacter ((e : ℕ) : ZMod χ.conductor)‖
          * ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
              χ.conductor χ.primitiveCharacter‖
      ≤ 1 * 1 * ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
          χ.conductor χ.primitiveCharacter‖ := by
        apply mul_le_mul _ (le_refl _) hT (by positivity)
        exact mul_le_mul hμ hψ (norm_nonneg _) (by norm_num)
    _ = ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
          χ.conductor χ.primitiveCharacter‖ := by ring

/-! ## 3. The per-`e` cutoff error term and the `hErrSum` reorganization -/

open Classical in
/-- **The per-`e` cutoff BDH error term.**  The `e`-shifted-scale (`⌊X/e⌋, Y, ⌊T/e⌋`) primitive
windowed energy over the large moduli `d` that are multiples of `e`.  Because the cutoff twist
does not factor, this is a *single* norm per character (no α-product/β-product split — the
β-side vanished at the fold).  Reorganizing `hErrSum`'s `d`-sum via the `e`-fold produces
`∑_{e=2}^{D} cutoffEfoldTerm e`.  Single-norm mirror of `EfoldTerm`. -/
noncomputable def cutoffEfoldTerm (α : ℕ → ℂ) (N X Y T D0 : ℕ) (Dset : Finset ℕ) (e : ℕ) : ℝ :=
  ∑ d ∈ (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d),
    (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
            χ.conductor χ.primitiveCharacter‖

open Classical in
/-- **WBV5 — the `hErrSum` cutoff reorganization (BDH `e`-fold, FULL).**  The exact `hErrSum`
slot of `cutoff_hLargeDisc` (for `β = blockPrimeInd N`, `D < N`) is bounded by the reorganized
per-`e` sum `∑_{e=2}^{D} cutoffEfoldTerm e`.  Per `(d,χ)` the cutoff `e`-fold `L¹` bound
`norm_cutoffTwist_sub_le_efold_blockPrimeInd` replaces the imprimitive-minus-primitive difference
by `∑_{e∣d, e>1} ‖A^{(e)}‖`; the finite `(χ,e)` and `(d,e)` sums are then swapped (`sum_comm`,
`sum_comm'`) to pull `e` outermost over `[2,D]`.  Single-norm mirror of `hErrSum_reorg`. -/
theorem cutoffEfoldTerm_reorg (α : ℕ → ℂ) (N X Y T D D0 : ℕ) (Dset : Finset ℕ)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D) (hDN : D < N) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
              - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ ∑ e ∈ Finset.Icc 2 D, cutoffEfoldTerm α N X Y T D0 Dset e := by
  classical
  set Dset' := Dset.filter (fun d => ¬ d ≤ D0) with hDset'def
  set f : ℕ → ℕ → ℝ := fun d e =>
    (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
            χ.conductor χ.primitiveCharacter‖
    with hfdef
  calc ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
              - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ ∑ d ∈ Dset', ∑ e ∈ efoldSet d, f d e := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [hDset'def, Finset.mem_filter] at hd
        have hd1 : 1 ≤ d := hDset1 d hd.1
        have hdD : d ≤ D := hDsetD d hd.1
        have hdN : d < N := by omega
        have step1 : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
                - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
              ≤ ∑ e ∈ efoldSet d,
                  ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                      χ.conductor χ.primitiveCharacter‖ := by
          intro χ _
          haveI : NeZero d := ⟨by omega⟩
          exact norm_cutoffTwist_sub_le_efold_blockPrimeInd hdN α X Y T χ
        calc (1 / (d.totient : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                  ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
                    - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
            ≤ (1 / (d.totient : ℝ)) *
                ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                  ∑ e ∈ efoldSet d,
                    ‖cutoffTwist (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e)
                        χ.conductor χ.primitiveCharacter‖ :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum step1) (by positivity)
          _ = ∑ e ∈ efoldSet d, f d e := by rw [mul_double_sum_comm]
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
    _ = ∑ e ∈ Finset.Icc 2 D, cutoffEfoldTerm α N X Y T D0 Dset e := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        simp only [cutoffEfoldTerm, hfdef, hDset'def]

open Classical in
/-- **WBV5 (item 2, FULL) — the `hErrSum` cutoff discharge (BDH `e`-fold).**  The exact `hErrSum`
slot of `cutoff_hLargeDisc`, discharged modulo a single named per-`e` glue `hGlue`
(`cutoffEfoldTerm e ≤ G e`) and its convergent sum `hGsum`.  `cutoffEfoldTerm_reorg` reorganizes
the cutoff coprimality error into `∑_{e=2}^{D} cutoffEfoldTerm e`; the glue supplies the
shifted-scale energy bound.  Single-norm mirror of `hErrSum_discharge`. -/
theorem hErrSum_cutoff_discharge (α : ℕ → ℂ) (N X Y T D D0 : ℕ) (Dset : Finset ℕ) {A Kerr : ℝ}
    (G : ℕ → ℝ)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D) (hDN : D < N)
    (hGlue : ∀ e, 2 ≤ e → e ≤ D → cutoffEfoldTerm α N X Y T D0 Dset e ≤ G e)
    (hGsum : ∑ e ∈ Finset.Icc 2 D, G e
        ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
              - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  refine le_trans (cutoffEfoldTerm_reorg α N X Y T D D0 Dset hDset1 hDsetD hDN) ?_
  refine le_trans (Finset.sum_le_sum (fun e he => ?_)) hGsum
  rw [Finset.mem_Icc] at he
  exact hGlue e he.1 he.2

/-! ## 3b. The α-side per-`e` reduction (`cutoffEfoldTerm_reduce_dense`)

The FLOOR-C structural start toward discharging the per-`e` glue: the honest `(e,f)`-density
reduction of `cutoffEfoldTerm` (mirror of `efold_alpha_reduce_dense`).  The cutoff is *simpler*
than the bilinear α-side — `cutoffEfoldTerm` is already a primitive single-norm energy, so there
is **no** primitive×primitive collapse (`EfoldTermAlpha_eq_prim`); the conductor regroup
`regroup_cutoff` (WBV4) applies directly, and the kept `e ∣ d` moduli fiber via the same
`sum_inv_totient_dvd_le'` gcd density.  The four-term discharge that consumes this (via
`dyadic_energy_le_cutoff_dvd` + the four thresholds, à la `efold_large_discharge`) is the one
remaining analytic core — see the module header. -/

open Classical in
/-- **WBV5 (FLOOR C start, FULL) — the honest `(e,f)`-density reduction of `cutoffEfoldTerm`.**
The regroup + kept-`e∣d` density, byte-for-byte the `efold_alpha_reduce_dense` route at the
cutoff carrier (`regroup_cutoff` in place of `regroup_bilin`, `cutoffPrimEnergy` in place of
`bilinPrimEnergy`, and — crucially — no primitive×primitive collapse, since `cutoffEfoldTerm` is
already primitive):
```
cutoffEfoldTerm α N X Y T D0 Dset e
    ≤ ∑_{2≤f≤D} (4/φ(lcm e f))·(1+log D)·cutoffPrimEnergy (α∘(e·)) β ⌊X/e⌋ Y ⌊T/e⌋ f
```
This is the honest form the (deferred) large-conductor four-term assembly must consume. -/
theorem cutoffEfoldTerm_reduce_dense (α : ℕ → ℂ) (N X Y T D0 D e : ℕ) (Dset : Finset ℕ)
    (hD1 : 1 ≤ D) (he1 : 1 ≤ e) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D) :
    cutoffEfoldTerm α N X Y T D0 Dset e
      ≤ ∑ f ∈ Finset.Icc 2 D,
          ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
            * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f := by
  classical
  unfold cutoffEfoldTerm
  set a : ℕ → ℂ := fun m' => α (e * m') with ha
  set β : ℕ → ℂ := blockPrimeInd N with hβ
  set XX : ℕ := X / e with hXX
  set TT : ℕ := T / e with hTT
  set S := (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d) with hS
  set G := (Finset.Icc 1 D).filter (fun d => e ∣ d) with hG
  have hsubset : S ⊆ G := by
    intro d hd
    rw [hS, Finset.mem_filter, Finset.mem_filter] at hd
    rw [hG, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hDset1 d hd.1.1, hDsetD d hd.1.1⟩, hd.2⟩
  calc ∑ d ∈ S, (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist a β XX Y TT χ.conductor χ.primitiveCharacter‖
      ≤ ∑ d ∈ S, (1 / (d.totient : ℝ)) *
          ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), cutoffPrimEnergy a β XX Y TT f := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [hS, Finset.mem_filter, Finset.mem_filter] at hd
        have hdD : d ≤ D := hDsetD d hd.1.1
        haveI : NeZero d := ⟨by have := hDset1 d hd.1.1; omega⟩
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Eq.trans_le ?_ (regroup_cutoff hdD a β XX Y TT)
        exact Finset.sum_congr
          (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
            (Subsingleton.elim _ _)) (fun _ _ => rfl)
    _ ≤ ∑ d ∈ G, (1 / (d.totient : ℝ)) *
          ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), cutoffPrimEnergy a β XX Y TT f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => ?_)
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg (fun f _ => cutoffPrimEnergy_nonneg _ _ _ _ _ _))
    _ = ∑ d ∈ G, ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d),
          (1 / (d.totient : ℝ)) * cutoffPrimEnergy a β XX Y TT f := by
        refine Finset.sum_congr rfl (fun d _ => ?_); rw [Finset.mul_sum]
    _ = ∑ f ∈ Finset.Icc 2 D, ∑ d ∈ G.filter (fun d => f ∣ d),
          (1 / (d.totient : ℝ)) * cutoffPrimEnergy a β XX Y TT f := by
        refine Finset.sum_comm' ?_
        intro d f
        simp only [hG, Finset.mem_filter, Finset.mem_Icc]; tauto
    _ = ∑ f ∈ Finset.Icc 2 D,
          (∑ d ∈ G.filter (fun d => f ∣ d), (1 / (d.totient : ℝ)))
            * cutoffPrimEnergy a β XX Y TT f := by
        refine Finset.sum_congr rfl (fun f _ => ?_); rw [Finset.sum_mul]
    _ ≤ ∑ f ∈ Finset.Icc 2 D,
          ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
            * cutoffPrimEnergy a β XX Y TT f := by
        refine Finset.sum_le_sum (fun f hf => ?_)
        rw [Finset.mem_Icc] at hf
        refine mul_le_mul_of_nonneg_right ?_ (cutoffPrimEnergy_nonneg _ _ _ _ _ _)
        have hlcm1 : 1 ≤ Nat.lcm e f := by
          have : Nat.lcm e f ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
          omega
        have hfilter : G.filter (fun d => f ∣ d)
            = (Finset.Icc 1 D).filter (fun d => Nat.lcm e f ∣ d) := by
          rw [hG, Finset.filter_filter]
          refine Finset.filter_congr (fun d _ => ?_)
          rw [Nat.lcm_dvd_iff]
        rw [hfilter]
        exact Salt.LS.sum_inv_totient_dvd_le' hlcm1 hD1

/-! ## 3c. The large-conductor four-term discharge (`efold_large_*` mirrors)

Porting the bilinear `hlarge` discharge chain to the cutoff carrier.  The gcd fibering
(`cutoffEfold_large_fibered`) is energy-agnostic; the four-term reduction
(`cutoffEfold_large_reduce`) consumes WBV2's δ-fibered cutoff four-term
`dyadic_energy_le_cutoff_dvd` (whose RHS is `T`-independent, hence *identical* to
`dyadic_energy_le_dvd`); the threshold assembly (`cutoffEfold_large_discharge`) is verbatim the
`efold_large_discharge` arithmetic at `Y` in place of `M`.  `Klarge = 15360`. -/

open Classical in
/-- **The gcd/fibering reduction (mirror of `efold_large_fibered`).**  Energy-agnostic totient
algebra: `4/φ(lcm e f) = 4φ(gcd e f)/(φe·φf)`, `φ(gcd) ≤ gcd = ∑_{g∣gcd}φg`, fibered over
`g ∣ e`.  Verbatim the bilinear route at `cutoffPrimEnergy`. -/
theorem cutoffEfold_large_fibered (α : ℕ → ℂ) (N X Y T D0 D e : ℕ) (he1 : 1 ≤ e) :
    ∑ f ∈ Finset.Icc (D0 + 1) D,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f
      ≤ (4 * (1 + Real.log D) / (e.totient : ℝ)) *
          ∑ g ∈ e.divisors, (g.totient : ℝ) *
            ∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => g ∣ f),
              (1 / (f.totient : ℝ)) *
                cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f := by
  classical
  set E : ℕ → ℝ := fun f =>
    cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f with hE
  have he0 : e ≠ 0 := by omega
  have hφe : (0 : ℝ) < (e.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < e)
  have h1logD : (0 : ℝ) ≤ 1 + Real.log D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · rw [hD, Nat.cast_zero, Real.log_zero]; norm_num
    · linarith [Real.log_nonneg (show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD)]
  have hstep1 : ∀ f ∈ Finset.Icc (D0 + 1) D,
      ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
        ≤ (4 * (1 + Real.log D) / (e.totient : ℝ))
            * ((Nat.gcd e f : ℝ) * ((1 / (f.totient : ℝ)) * E f)) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf0 : f ≠ 0 := by omega
    have hφf : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hgcdpos : 0 < Nat.gcd e f := Nat.gcd_pos_of_pos_left f (by omega)
    have hlcmpos : 0 < Nat.lcm e f := by
      have : Nat.lcm e f ≠ 0 := Nat.lcm_ne_zero he0 hf0
      omega
    have hφlcm : (0 : ℝ) < ((Nat.lcm e f).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hlcmpos
    have hEf : 0 ≤ E f := cutoffPrimEnergy_nonneg _ _ _ _ _ _
    have hlcmgcd : ((Nat.lcm e f).totient : ℝ) * ((Nat.gcd e f).totient : ℝ)
        = (e.totient : ℝ) * (f.totient : ℝ) := by
      exact_mod_cast totient_lcm_mul_totient_gcd e f
    have hdensity : (4 / ((Nat.lcm e f).totient : ℝ))
        = (4 / (e.totient : ℝ)) * (((Nat.gcd e f).totient : ℝ) / (f.totient : ℝ)) := by
      have hpos : (0 : ℝ) < (e.totient : ℝ) * (f.totient : ℝ) := by positivity
      rw [div_mul_div_comm, div_eq_div_iff hφlcm.ne' hpos.ne']
      linear_combination -4 * hlcmgcd
    have hφgcdle : ((Nat.gcd e f).totient : ℝ) ≤ (Nat.gcd e f : ℝ) := by
      exact_mod_cast Nat.totient_le (Nat.gcd e f)
    rw [hdensity]
    have hle : ((Nat.gcd e f).totient : ℝ) / (f.totient : ℝ)
        ≤ (Nat.gcd e f : ℝ) / (f.totient : ℝ) :=
      div_le_div_of_nonneg_right hφgcdle hφf.le
    calc ((4 / (e.totient : ℝ)) * (((Nat.gcd e f).totient : ℝ) / (f.totient : ℝ)))
            * (1 + Real.log D) * E f
        ≤ ((4 / (e.totient : ℝ)) * ((Nat.gcd e f : ℝ) / (f.totient : ℝ)))
            * (1 + Real.log D) * E f := by
          apply mul_le_mul_of_nonneg_right _ hEf
          apply mul_le_mul_of_nonneg_right _ h1logD
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (4 * (1 + Real.log D) / (e.totient : ℝ))
            * ((Nat.gcd e f : ℝ) * ((1 / (f.totient : ℝ)) * E f)) := by ring
  refine le_trans (Finset.sum_le_sum hstep1) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hgcdsum : ∀ f ∈ Finset.Icc (D0 + 1) D,
      (Nat.gcd e f : ℝ) * ((1 / (f.totient : ℝ)) * E f)
        = ∑ g ∈ e.divisors,
            (if g ∣ f then (g.totient : ℝ) else 0) * ((1 / (f.totient : ℝ)) * E f) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf0 : f ≠ 0 := by omega
    rw [← Finset.sum_mul]
    congr 1
    have hdiv : (Nat.gcd e f).divisors = e.divisors.filter (fun g => g ∣ f) := by
      ext g
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hge, hgf⟩, _⟩; exact ⟨⟨hge, he0⟩, hgf⟩
      · rintro ⟨⟨hge, _⟩, hgf⟩
        exact ⟨⟨hge, hgf⟩, by
          have : Nat.gcd e f ≠ 0 := by
            have := Nat.gcd_pos_of_pos_left (m := e) f (by omega); omega
          exact this⟩
    have : (Nat.gcd e f : ℝ) = ∑ g ∈ e.divisors.filter (fun g => g ∣ f), (g.totient : ℝ) := by
      rw [← hdiv, ← Nat.cast_sum]
      exact_mod_cast (sum_totient_divisors (Nat.gcd e f)).symm
    rw [this, Finset.sum_filter]
  rw [Finset.sum_congr rfl hgcdsum, Finset.sum_comm]
  refine Finset.sum_le_sum (fun g hg => ?_)
  rw [Finset.sum_filter]
  refine le_of_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases hgf : g ∣ f
  · rw [if_pos hgf, if_pos hgf]
  · rw [if_neg hgf, if_neg hgf, zero_mul, mul_zero]

open Classical in
/-- **The four-term reduction (mirror of `efold_large_reduce`).**  Composes
`cutoffEfold_large_fibered` with WBV2's δ-fibered cutoff four-term `dyadic_energy_le_cutoff_dvd`
per common divisor `g ∣ e` (at `δ = g`, scale `(⌊X/e⌋, Y, ⌊T/e⌋)`) and the three totient sums,
collapsing to the explicit bounded four-term.  `d(e) = e.divisors.card`. -/
theorem cutoffEfold_large_reduce (α : ℕ → ℂ) (N X Y T D0 D e k0 K : ℕ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (he2 : 2 ≤ e) (hD1 : 1 ≤ D)
    (hD0pow : D0 = 2 ^ k0) (hK : K = Nat.log 2 D) (hYpos : 0 < Y) :
    ∑ f ∈ Finset.Icc (D0 + 1) D,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f
      ≤ (4 * (1 + Real.log D) / (e.totient : ℝ)) *
          ((2 * (1 + Real.log Y) * Real.sqrt ((X / e : ℕ) : ℝ) * Real.sqrt (Y : ℝ)) *
            ( 4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (((X / e : ℕ) : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
            + Real.sqrt (13 * (((X / e : ℕ) : ℝ) + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) := by
  classical
  set E : ℕ → ℝ := fun f =>
    cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f with hE
  refine le_trans (cutoffEfold_large_fibered α N X Y T D0 D e (by omega)) ?_
  have h1logD : (0 : ℝ) ≤ 1 + Real.log D :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD1)]
  have hφe : (0 : ℝ) < (e.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < e)
  have hPf : (0 : ℝ) ≤ 4 * (1 + Real.log D) / (e.totient : ℝ) := by
    apply div_nonneg (by linarith) hφe.le
  refine mul_le_mul_of_nonneg_left ?_ hPf
  set xe : ℝ := ((X / e : ℕ) : ℝ) with hxe
  set C0 : ℝ := 2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ) with hC0
  have h1logY : (0 : ℝ) ≤ 1 + Real.log Y := by
    have : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hYpos
    linarith [Real.log_nonneg this]
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1logY) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hβ1 : ∀ n, ‖blockPrimeInd N n‖ ≤ 1 := by
    intro n; unfold blockPrimeInd
    by_cases h : N < n ∧ n.Prime
    · rw [if_pos h, norm_one]
    · rw [if_neg h, norm_zero]; norm_num
  have hdil : ∀ m', ‖(fun m' => α (e * m')) m'‖ ≤ 1 := fun m' => hα (e * m')
  have hpg : ∀ g ∈ e.divisors,
      (g.totient : ℝ) *
          (∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => g ∣ f), (1 / (f.totient : ℝ)) * E f)
        ≤ (g.totient : ℝ) *
            (C0 * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (g : ℝ)
              + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0))) := by
    intro g hg
    have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
    have hφg : (0 : ℝ) ≤ (g.totient : ℝ) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hφg
    exact dyadic_energy_le_cutoff_dvd (X := X / e) (Y := Y) (T := T / e) (D0 := D0) (D := D)
      (δ := g) (k0 := k0) (K := K) hg1 hD0pow hK hYpos (fun m' => α (e * m')) (blockPrimeInd N)
      hdil hβ1
  refine le_trans (Finset.sum_le_sum hpg) ?_
  have hpullC0 :
      ∑ g ∈ e.divisors, (g.totient : ℝ) *
          (C0 * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (g : ℝ)
            + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0)))
        = C0 * ∑ g ∈ e.divisors, (g.totient : ℝ) *
            (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (g : ℝ)
              + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun g _ => by ring)
  rw [hpullC0]
  refine mul_le_mul_of_nonneg_left ?_ hC0nn
  have hsplit :
      ∑ g ∈ e.divisors, (g.totient : ℝ) *
          (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (g : ℝ)
            + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0))
        = (∑ g ∈ e.divisors, (g.totient : ℝ) * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)))
          + (∑ g ∈ e.divisors, (g.totient : ℝ) *
              (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)))
          + (∑ g ∈ e.divisors, (g.totient : ℝ) *
              (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (g : ℝ)))
          + (∑ g ∈ e.divisors, (g.totient : ℝ) *
              (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0))) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have ht1 : ∑ g ∈ e.divisors, (g.totient : ℝ) * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ))
      ≤ 4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ) := by
    have heq : ∑ g ∈ e.divisors, (g.totient : ℝ) * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ))
        = 4 * (2 : ℝ) ^ (K + 1) * ∑ g ∈ e.divisors, (g.totient : ℝ) / (g : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun g _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left (sum_totient_div_self_le e) (by positivity)
  have ht2 : ∑ g ∈ e.divisors, (g.totient : ℝ) *
        (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ))
      ≤ 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
          * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) := by
    have heq : ∑ g ∈ e.divisors, (g.totient : ℝ) *
          (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ))
        = 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
            * ∑ g ∈ e.divisors, (g.totient : ℝ) / Real.sqrt (g : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun g _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left (sum_totient_div_sqrt_le e (by omega)) (by positivity)
  have ht3 : ∑ g ∈ e.divisors, (g.totient : ℝ) *
        (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (g : ℝ))
      ≤ 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
          * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) := by
    have heq : ∑ g ∈ e.divisors, (g.totient : ℝ) *
          (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) / Real.sqrt (g : ℝ))
        = 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
            * ∑ g ∈ e.divisors, (g.totient : ℝ) / Real.sqrt (g : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun g _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left (sum_totient_div_sqrt_le e (by omega)) (by positivity)
  have ht4 : ∑ g ∈ e.divisors, (g.totient : ℝ) *
        (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0))
      = Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
          * (2 / (2 : ℝ) ^ k0) * (e : ℝ) := by
    have hsum : ∑ g ∈ e.divisors, (g.totient : ℝ) = (e : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast sum_totient_divisors e
    rw [← Finset.sum_mul, hsum]; ring
  rw [ht4]
  have hcombine := add_le_add (add_le_add ht1 ht2) ht3
  linarith [hcombine]

set_option maxHeartbeats 1600000 in
-- The four-term threshold assembly (~30 shared facts + 4 nested `calc`s with `gcongr`/`ring`
-- over large sqrt/rpow expressions) exceeds the 200000-heartbeat default during elaboration.
open Classical in
/-- **WBV5 (FLOOR C) — the cutoff `hlarge` slot, discharged.**  Mirror of
`efold_large_discharge`.  The large-conductor contribution
meets the target envelope `Klarge·(XY/L^{A+1})·(1/e)` (`Klarge = 15360`, `L = log(XY)`) under
the four coupled operating-point thresholds:
* `hlev  : D·L^{A+5} ≤ √(XY)`      — closes the **main** diagonal `D·√(XY)`;
* `hD0lo : L^{A+4} ≤ D0`            — closes the **tail** `√(XY)/D0`;
* `hMlev : L^{A+5} ≤ √Y`           — closes **cross-X** (`X·√Y = XY/√Y`);
* `hdiv  : d(e)·L^{A+5} ≤ √X`      — closes **cross-Y** (`Y·√X·d(e)`); see the module FLAG.

Route: `cutoffEfold_large_reduce` (the fibered four bounded terms) + the term-wise threshold
bookkeeping (`(1+log D), (1+log Y), (K+1) ≤ 2L`, `e/φe ≤ 3L`, `d(e) ≤ 2√e`, the α-scale
pairing `√⌊X/e⌋·√(13(⌊X/e⌋+1)) ≤ 6(X/e)` and `√Y·√(13(Y+1)) ≤ 6M`, `√⌊X/e⌋·√e ≤ √X`). -/
theorem cutoffEfold_large_discharge (α : ℕ → ℂ) (N X Y T D0 D e k0 K : ℕ) {A : ℝ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (he2 : 2 ≤ e) (heD : e ≤ D)
    (hD0pow : D0 = 2 ^ k0) (hK : K = Nat.log 2 D) (hYpos : 0 < Y) (hXpos : 0 < X)
    (hA : 0 ≤ A) (hD1 : 1 ≤ D) (hL1 : 1 ≤ Real.log ((X : ℝ) * (Y : ℝ)))
    (hlev : (D : ℝ) * (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)))
    (hD0lo : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 4) ≤ (D0 : ℝ))
    (hMlev : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt (Y : ℝ))
    (hdiv : (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ)) :
    ∑ f ∈ Finset.Icc (D0 + 1) D,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f
      ≤ 15360 * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
  refine le_trans (cutoffEfold_large_reduce α N X Y T D0 D e k0 K hα he2 hD1 hD0pow hK hYpos) ?_
  -- abbreviations (only `L` and `xe`; other casts stay raw to match external lemmas)
  set L := Real.log ((X : ℝ) * (Y : ℝ)) with hLdef
  set xe : ℝ := ((X / e : ℕ) : ℝ) with hxedef
  have hLpos : 0 < L := by linarith
  have hXr1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
  have hMr1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hYpos
  have herpos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hφinv : (0 : ℝ) < (e.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < e)
  have hxenn : (0 : ℝ) ≤ xe := by rw [hxedef]; positivity
  have hXYpos : 0 < (X : ℝ) * (Y : ℝ) := by positivity
  have hXYnn : (0 : ℝ) ≤ (X : ℝ) * (Y : ℝ) := hXYpos.le
  have hXY1 : (1 : ℝ) ≤ (X : ℝ) * (Y : ℝ) := by nlinarith [hXr1, hMr1]
  have hsqXY : Real.sqrt ((X : ℝ) * (Y : ℝ)) = Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ) :=
    Real.sqrt_mul (by linarith) _
  have hsqXYsq :
      Real.sqrt ((X : ℝ) * (Y : ℝ)) * Real.sqrt ((X : ℝ) * (Y : ℝ)) = (X : ℝ) * (Y : ℝ) :=
    Real.mul_self_sqrt hXYnn
  have hMsq : Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) = (Y : ℝ) := Real.mul_self_sqrt (by linarith)
  have hXsq : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := Real.mul_self_sqrt (by linarith)
  have h1sqXY : (1 : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt hXY1
  have hsqle : Real.sqrt ((X : ℝ) * (Y : ℝ)) ≤ (X : ℝ) * (Y : ℝ) := by nlinarith [hsqXYsq, h1sqXY]
  -- rpow bookkeeping
  have hL5 : (0 : ℝ) < L ^ (A + 5) := Real.rpow_pos_of_pos hLpos _
  have hL1p : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
  have hL4p : (0 : ℝ) < L ^ (A + 4) := Real.rpow_pos_of_pos hLpos _
  have hLpow3 : L ^ ((3 : ℕ) : ℝ) = L * L * L := by rw [Real.rpow_natCast]; ring
  have hLpow4 : L ^ ((4 : ℕ) : ℝ) = L * L * L * L := by rw [Real.rpow_natCast]; ring
  have hL1ge : (1 : ℝ) ≤ L ^ (A + 5) := by
    rw [show (1 : ℝ) = L ^ (0 : ℝ) by rw [Real.rpow_zero]]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hmain_eq : (L * L * L) * L ^ (A + 1) = L ^ (A + 4) := by
    rw [← hLpow3, ← Real.rpow_add hLpos]; congr 1; push_cast; ring
  have hmain_pow : (L * L * L) * L ^ (A + 1) ≤ L ^ (A + 5) := by
    rw [hmain_eq]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hcross_eq : (L * L * L * L) * L ^ (A + 1) = L ^ (A + 5) := by
    rw [← hLpow4, ← Real.rpow_add hLpos]; congr 1; push_cast; ring
  -- D ≤ √(XY), D·√(XY) ≤ XY/L^{A+5}
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDsqrtXY : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) := by
    calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D : ℝ) * L ^ (A + 5) := by apply mul_le_mul_of_nonneg_left hL1ge hDpos.le
      _ ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) := hlev
  have hDXY : (D : ℝ) ≤ (X : ℝ) * (Y : ℝ) := le_trans hDsqrtXY hsqle
  have hDsqdiv : (D : ℝ) * Real.sqrt ((X : ℝ) * (Y : ℝ)) ≤ (X : ℝ) * (Y : ℝ) / L ^ (A + 5) := by
    rw [le_div_iff₀ hL5]
    calc (D : ℝ) * Real.sqrt ((X : ℝ) * (Y : ℝ)) * L ^ (A + 5)
        = ((D : ℝ) * L ^ (A + 5)) * Real.sqrt ((X : ℝ) * (Y : ℝ)) := by ring
      _ ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)) * Real.sqrt ((X : ℝ) * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_right hlev (Real.sqrt_nonneg _)
      _ = (X : ℝ) * (Y : ℝ) := hsqXYsq
  -- log bounds
  have hlogD2 : 1 + Real.log D ≤ 2 * L := by
    have : Real.log D ≤ L := by rw [hLdef]; exact Real.log_le_log hDpos hDXY
    linarith
  have hlogM2 : 1 + Real.log Y ≤ 2 * L := by
    have hMXY : (Y : ℝ) ≤ (X : ℝ) * (Y : ℝ) := le_mul_of_one_le_left (by linarith) hXr1
    have : Real.log Y ≤ L := by rw [hLdef]; exact Real.log_le_log (by linarith) hMXY
    linarith
  -- (K+1) ≤ 2L
  have h2K : (2 : ℝ) ^ K ≤ (D : ℝ) := by
    have := Nat.pow_log_le_self 2 (show D ≠ 0 by omega)
    rw [← hK] at this; exact_mod_cast this
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hlog2K : (K : ℝ) * Real.log 2 ≤ L / 2 := by
    have h := Real.log_le_log (by positivity) (le_trans h2K hDsqrtXY)
    rw [Real.log_pow, Real.log_sqrt hXYnn, ← hLdef] at h; linarith
  have hKL : (K : ℝ) ≤ L := by
    nlinarith [hlog2K,
        mul_nonneg hKnn (by linarith [Real.log_two_gt_d9] : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]
  have hK2 : ((K + 1 : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith
  -- 1/φe ≤ 3L/e
  have hφe3 : (1 : ℝ) / (e.totient : ℝ) ≤ 3 * L / (e : ℝ) := by
    rw [div_le_div_iff₀ hφinv herpos]
    rcases eq_or_lt_of_le he2 with he2' | he3
    · have hee : e = 2 := he2'.symm
      have hφ2 : (e.totient : ℝ) = 1 := by rw [hee]; norm_num
      rw [hφ2, hee]; push_cast; nlinarith [hL1]
    · have hratio := totient_ratio_le_log e he3
      rw [div_le_iff₀ hφinv] at hratio
      have hlogeL : Real.log (e : ℝ) ≤ L := by
        rw [hLdef]; refine Real.log_le_log (by exact_mod_cast (by omega : 0 < e)) ?_
        exact le_trans (by exact_mod_cast heD) hDXY
      nlinarith [hratio,
        mul_nonneg (show (0 : ℝ) ≤ L - Real.log (e : ℝ) by linarith) hφinv.le]
  -- d(e) ≤ 2√e, and √e·d(e) ≤ 2e
  have hd2 : (e.divisors.card : ℝ) ≤ 2 * Real.sqrt (e : ℝ) := card_divisors_le_two_sqrt e (by omega)
  have hSed : Real.sqrt (e : ℝ) * (e.divisors.card : ℝ) ≤ 2 * (e : ℝ) := by
    calc Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)
        ≤ Real.sqrt (e : ℝ) * (2 * Real.sqrt (e : ℝ)) :=
          mul_le_mul_of_nonneg_left hd2 (Real.sqrt_nonneg _)
      _ = 2 * (Real.sqrt (e : ℝ) * Real.sqrt (e : ℝ)) := by ring
      _ = 2 * (e : ℝ) := by rw [Real.mul_self_sqrt (by positivity)]
  -- 2^{K+1} ≤ 2D
  have hpow2 : (2 : ℝ) ^ (K + 1) ≤ 2 * (D : ℝ) := by rw [pow_succ]; linarith [h2K]
  -- √xe·√e ≤ √X
  have hS2 : Real.sqrt xe * Real.sqrt (e : ℝ) ≤ Real.sqrt (X : ℝ) := by
    rw [← Real.sqrt_mul hxenn]
    apply Real.sqrt_le_sqrt
    rw [hxedef]
    calc ((X / e : ℕ) : ℝ) * (e : ℝ) = (((X / e) * e : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (X : ℝ) := by exact_mod_cast Nat.div_mul_le_self X e
  -- pairings
  have hPX : Real.sqrt xe * Real.sqrt (13 * (xe + 1)) ≤ 6 * ((X : ℝ) / (e : ℝ)) := by
    rw [← Real.sqrt_mul hxenn]
    have hq : xe ≤ (X : ℝ) / (e : ℝ) := by rw [hxedef]; exact Nat.cast_div_le
    calc Real.sqrt (xe * (13 * (xe + 1))) ≤ Real.sqrt ((6 * ((X : ℝ) / (e : ℝ))) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rcases Nat.eq_zero_or_pos (X / e) with h0 | hpos
          · have hz : xe = 0 := by rw [hxedef, h0]; norm_num
            rw [hz, zero_mul]; positivity
          · have hxe1 : (1 : ℝ) ≤ xe := by rw [hxedef]; exact_mod_cast hpos
            nlinarith [hq, hxe1, hxenn, le_trans hxe1 hq]
      _ = 6 * ((X : ℝ) / (e : ℝ)) := Real.sqrt_sq (by positivity)
  have hPM : Real.sqrt (Y : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)) ≤ 6 * (Y : ℝ) := by
    rw [← Real.sqrt_mul (by linarith)]
    calc Real.sqrt ((Y : ℝ) * (13 * ((Y : ℝ) + 1))) ≤ Real.sqrt ((6 * (Y : ℝ)) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith [hMr1]
      _ = 6 * (Y : ℝ) := Real.sqrt_sq (by positivity)
  -- threshold conversions to XY/L^{A+5}
  have hXsqMdiv : (X : ℝ) * Real.sqrt (Y : ℝ) ≤ (X : ℝ) * (Y : ℝ) / L ^ (A + 5) := by
    rw [le_div_iff₀ hL5]
    calc (X : ℝ) * Real.sqrt (Y : ℝ) * L ^ (A + 5) = (X : ℝ) * (Real.sqrt (Y : ℝ) * L ^ (A + 5))
        := by ring
      _ ≤ (X : ℝ) * (Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hMlev (Real.sqrt_nonneg _)
      _ = (X : ℝ) * (Y : ℝ) := by rw [hMsq]
  have hMXddiv : (Y : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)
      ≤ (X : ℝ) * (Y : ℝ) / L ^ (A + 5) := by
    rw [le_div_iff₀ hL5]
    calc (Y : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ) * L ^ (A + 5)
        = (Y : ℝ) * Real.sqrt (X : ℝ) * ((e.divisors.card : ℝ) * L ^ (A + 5)) := by ring
      _ ≤ (Y : ℝ) * Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) := by
          apply mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (X : ℝ) * (Y : ℝ) := by rw [mul_assoc, hXsq]; ring
  -- 1/D0 ≤ 1/L^{A+4}
  have hD0inv : (1 : ℝ) / (D0 : ℝ) ≤ 1 / L ^ (A + 4) := one_div_le_one_div_of_le hL4p hD0lo
  -- distribute the reduction RHS into the four pieces
  have hlogDnn : (0 : ℝ) ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD1)
  have hAnn : (0 : ℝ) ≤ 4 * (1 + Real.log D) / (e.totient : ℝ) := by
    apply div_nonneg (by linarith) hφinv.le
  set A0 : ℝ := 4 * (1 + Real.log D) / (e.totient : ℝ) with hA0
  set G : ℝ := (X : ℝ) * (Y : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)) with hG
  have hGnn : (0 : ℝ) ≤ G := by rw [hG]; positivity
  -- MAIN term
  have hTmain : A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
        * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ))) ≤ 1536 * G := by
    have hMainSqrt : Real.sqrt xe * Real.sqrt (Y : ℝ) * (e.divisors.card : ℝ)
        ≤ 2 * Real.sqrt ((X : ℝ) * (Y : ℝ)) := by
      calc Real.sqrt xe * Real.sqrt (Y : ℝ) * (e.divisors.card : ℝ)
          ≤ Real.sqrt xe * Real.sqrt (Y : ℝ) * (2 * Real.sqrt (e : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hd2; positivity
        _ = 2 * (Real.sqrt xe * Real.sqrt (e : ℝ)) * Real.sqrt (Y : ℝ) := by ring
        _ ≤ 2 * Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            apply mul_le_mul_of_nonneg_left hS2; norm_num
        _ = 2 * Real.sqrt ((X : ℝ) * (Y : ℝ)) := by rw [hsqXY]; ring
    calc A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)))
        = A0 * (2 * (1 + Real.log Y)) * (4 * (2 : ℝ) ^ (K + 1))
            * (Real.sqrt xe * Real.sqrt (Y : ℝ) * (e.divisors.card : ℝ)) := by ring
      _ ≤ A0 * (2 * (1 + Real.log Y)) * (4 * (2 * (D : ℝ)))
            * (2 * Real.sqrt ((X : ℝ) * (Y : ℝ))) := by
          gcongr
      _ = 128 * (1 + Real.log D) * (1 + Real.log Y) * ((D : ℝ) * Real.sqrt ((X : ℝ) * (Y : ℝ)))
            * (1 / (e.totient : ℝ)) := by rw [hA0]; ring
      _ ≤ 128 * (2 * L) * (2 * L) * ((X : ℝ) * (Y : ℝ) / L ^ (A + 5)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 1536 * (L * L * L) * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 5) * (e : ℝ)) := by ring
      _ ≤ 1536 * G := by
          rw [hG, show 1536 * ((X : ℝ) * (Y : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 1536 * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 1536 * (L * L * L) * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (1536 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * ((L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (1536 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * L ^ (A + 5) :=
                mul_le_mul_of_nonneg_left hmain_pow (by positivity)
            _ = 1536 * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 5) * (e : ℝ)) := by ring
  -- CROSS-X term
  have hTcrossX : A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
        * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)))) ≤ 4608 * G := by
    have hGX : Real.sqrt xe * Real.sqrt (13 * (xe + 1))
          * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) * Real.sqrt (Y : ℝ)
        ≤ 12 * ((X : ℝ) * Real.sqrt (Y : ℝ)) := by
      calc Real.sqrt xe * Real.sqrt (13 * (xe + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) * Real.sqrt (Y : ℝ)
          ≤ (6 * ((X : ℝ) / (e : ℝ))) * (2 * (e : ℝ)) * Real.sqrt (Y : ℝ) := by
            gcongr
        _ = 12 * ((X : ℝ) * Real.sqrt (Y : ℝ)) := by field_simp; ring
    calc A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        = A0 * (2 * (1 + Real.log Y)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (Real.sqrt xe * Real.sqrt (13 * (xe + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) * Real.sqrt (Y : ℝ)) := by ring
      _ ≤ A0 * (2 * (1 + Real.log Y)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (12 * ((X : ℝ) * Real.sqrt (Y : ℝ))) := by gcongr
      _ = 192 * (1 + Real.log D) * (1 + Real.log Y) * ((K + 1 : ℕ) : ℝ)
            * ((X : ℝ) * Real.sqrt (Y : ℝ)) * (1 / (e.totient : ℝ)) := by rw [hA0]; ring
      _ ≤ 192 * (2 * L) * (2 * L) * (2 * L)
            * ((X : ℝ) * (Y : ℝ) / L ^ (A + 5)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 4608 * (L * L * L * L) * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 5) * (e : ℝ)) := by ring
      _ ≤ 4608 * G := by
          rw [hG, show 4608 * ((X : ℝ) * (Y : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 4608 * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 4608 * (L * L * L * L) * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (4608 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * ((L * L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (4608 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * L ^ (A + 5) :=
                mul_le_mul_of_nonneg_left (le_of_eq hcross_eq) (by positivity)
            _ = 4608 * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 5) * (e : ℝ)) := by ring
  -- CROSS-Y term
  have hTcrossM : A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
        * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)))) ≤ 2304 * G := by
    have hGM : Real.sqrt xe * Real.sqrt (Y : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
          * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
        ≤ 6 * ((Y : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)) := by
      calc Real.sqrt xe * Real.sqrt (Y : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
          = (Real.sqrt xe * Real.sqrt (e : ℝ))
              * (Real.sqrt (Y : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)))
              * (e.divisors.card : ℝ) := by ring
        _ ≤ Real.sqrt (X : ℝ) * (6 * (Y : ℝ)) * (e.divisors.card : ℝ) := by
            gcongr
        _ = 6 * ((Y : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)) := by ring
    calc A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        = A0 * (2 * (1 + Real.log Y)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (Real.sqrt xe * Real.sqrt (Y : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))) := by ring
      _ ≤ A0 * (2 * (1 + Real.log Y)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (6 * ((Y : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ))) := by gcongr
      _ = 96 * (1 + Real.log D) * (1 + Real.log Y) * ((K + 1 : ℕ) : ℝ)
            * ((Y : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)) * (1 / (e.totient : ℝ)) := by
          rw [hA0]; ring
      _ ≤ 96 * (2 * L) * (2 * L) * (2 * L)
            * ((X : ℝ) * (Y : ℝ) / L ^ (A + 5)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 2304 * (L * L * L * L) * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 5) * (e : ℝ)) := by ring
      _ ≤ 2304 * G := by
          rw [hG, show 2304 * ((X : ℝ) * (Y : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 2304 * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 2304 * (L * L * L * L) * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (2304 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * ((L * L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (2304 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * L ^ (A + 5) :=
                mul_le_mul_of_nonneg_left (le_of_eq hcross_eq) (by positivity)
            _ = 2304 * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 5) * (e : ℝ)) := by ring
  -- TAIL term
  have hTtail : A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
        * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
            * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) ≤ 6912 * G := by
    have hD0R : (D0 : ℝ) = (2 : ℝ) ^ k0 := by rw [hD0pow]; push_cast; ring
    have hGT : Real.sqrt xe * Real.sqrt (Y : ℝ)
          * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
              * (2 / (2 : ℝ) ^ k0) * (e : ℝ))
        ≤ 72 * ((X : ℝ) * (Y : ℝ)) * (1 / (D0 : ℝ)) := by
      have hD0pos : (0 : ℝ) < (D0 : ℝ) := by rw [hD0R]; positivity
      calc Real.sqrt xe * Real.sqrt (Y : ℝ)
            * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ))
          = (Real.sqrt xe * Real.sqrt (13 * (xe + 1)))
              * (Real.sqrt (Y : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1)))
              * (2 / (2 : ℝ) ^ k0) * (e : ℝ) := by ring
        _ ≤ (6 * ((X : ℝ) / (e : ℝ))) * (6 * (Y : ℝ)) * (2 / (2 : ℝ) ^ k0) * (e : ℝ) := by
            gcongr
        _ = 72 * ((X : ℝ) * (Y : ℝ)) * (1 / (D0 : ℝ)) := by rw [hD0R]; field_simp; ring
    calc A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ)))
        = A0 * (2 * (1 + Real.log Y))
            * (Real.sqrt xe * Real.sqrt (Y : ℝ)
                * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                    * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) := by ring
      _ ≤ A0 * (2 * (1 + Real.log Y)) * (72 * ((X : ℝ) * (Y : ℝ)) * (1 / (D0 : ℝ))) := by gcongr
      _ = 576 * (1 + Real.log D) * (1 + Real.log Y) * ((X : ℝ) * (Y : ℝ))
            * (1 / (D0 : ℝ)) * (1 / (e.totient : ℝ)) := by rw [hA0]; ring
      _ ≤ 576 * (2 * L) * (2 * L) * ((X : ℝ) * (Y : ℝ))
            * (1 / L ^ (A + 4)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 6912 * (L * L * L) * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 4) * (e : ℝ)) := by ring
      _ ≤ 6912 * G := by
          rw [hG, show 6912 * ((X : ℝ) * (Y : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 6912 * ((X : ℝ) * (Y : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 6912 * (L * L * L) * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (6912 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * ((L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (6912 * ((X : ℝ) * (Y : ℝ)) * (e : ℝ)) * L ^ (A + 4) :=
                mul_le_mul_of_nonneg_left (le_of_eq hmain_eq) (by positivity)
            _ = 6912 * ((X : ℝ) * (Y : ℝ)) * (L ^ (A + 4) * (e : ℝ)) := by ring
  -- combine the four terms
  calc A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
        * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)
          + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
              * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
          + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
              * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
          + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
              * (2 / (2 : ℝ) ^ k0) * (e : ℝ)))
      = A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)))
        + A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        + A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        + A0 * ((2 * (1 + Real.log Y) * Real.sqrt xe * Real.sqrt (Y : ℝ))
            * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((Y : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) := by
        ring
    _ ≤ 1536 * G + 4608 * G + 2304 * G + 6912 * G :=
        add_le_add (add_le_add (add_le_add hTmain hTcrossX) hTcrossM) hTtail
    _ = 15360 * ((X : ℝ) * (Y : ℝ) / L ^ (A + 1)) * (1 / (e : ℝ)) := by rw [hG]; ring

open Classical in
/-- **WBV5 (FLOOR C, FULL) — the α-side per-`e` cutoff bound.**  The two-regime assembly:
`cutoffEfoldTerm_reduce_dense` (regroup + density) then the conductor split at `D0` into the
small part (named `hsmall`, the window small-conductor cutoff-SW input at the dilated scale — the
cutoff twist does not factor, so it stays named, exactly as `general_BV_alpha_final` keeps
`hsmall`) and the large part discharged by `cutoffEfold_large_discharge` (the four coupled
thresholds `hlev`/`hD0lo`/`hMlev`/`hdiv`, `Klarge = 15360`).  This is the cutoff analogue of
`efold_alpha_le` with `hlarge` already filled — the per-`e` glue of `hErrSum_cutoff_discharge`,
dischargeable to `hsmall` + the four thresholds. -/
theorem cutoffEfold_alpha_le (α : ℕ → ℂ) (N X Y T D0 D e k0 K : ℕ) (Dset : Finset ℕ) {A Ksmall : ℝ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (he2 : 2 ≤ e) (heD : e ≤ D) (hD1 : 1 ≤ D)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (h2D0 : 2 ≤ D0) (hD0D : D0 ≤ D) (hD0pow : D0 = 2 ^ k0) (hK : K = Nat.log 2 D)
    (hYpos : 0 < Y) (hXpos : 0 < X) (hA : 0 ≤ A) (hL1 : 1 ≤ Real.log ((X : ℝ) * (Y : ℝ)))
    (hlev : (D : ℝ) * (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)))
    (hD0lo : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 4) ≤ (D0 : ℝ))
    (hMlev : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt (Y : ℝ))
    (hdiv : (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ))
    (hsmall : ∑ f ∈ Finset.Icc 2 D0,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f
      ≤ Ksmall * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) * (1 / (e : ℝ))) :
    cutoffEfoldTerm α N X Y T D0 Dset e
      ≤ (Ksmall + 15360)
          * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
  refine le_trans
    (cutoffEfoldTerm_reduce_dense α N X Y T D0 D e Dset hD1 (by omega) hDset1 hDsetD) ?_
  set g : ℕ → ℝ := fun f => ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
    * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f with hg
  have hsplit : ∑ f ∈ Finset.Icc 2 D, g f
      = ∑ f ∈ Finset.Icc 2 D0, g f + ∑ f ∈ Finset.Icc (D0 + 1) D, g f := by
    rw [show Finset.Icc 2 D = Finset.Ioc 1 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc 2 D0 = Finset.Ioc 1 D0 by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc (D0 + 1) D = Finset.Ioc D0 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    exact (Finset.sum_Ioc_consecutive g (by omega : 1 ≤ D0) hD0D).symm
  rw [hsplit]
  calc ∑ f ∈ Finset.Icc 2 D0, g f + ∑ f ∈ Finset.Icc (D0 + 1) D, g f
      ≤ Ksmall * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) * (1 / (e : ℝ))
        + 15360 * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) :=
        add_le_add hsmall
          (cutoffEfold_large_discharge α N X Y T D0 D e k0 K hα he2 heD hD0pow hK hYpos hXpos
            hA hD1 hL1 hlev hD0lo hMlev hdiv)
    _ = (Ksmall + 15360)
          * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
        ring

open Classical in
/-- **WBV5 (FLOOR C, FULL) — the `hErrSum` cutoff discharge at the honest `1/e` envelope.**
Mirror of `hErrSum_final'`: with the per-`e` slot at the honest decay
`cutoffEfoldTerm e ≤ Kerr·(XY/L^{A+1})·(1/e)` (supplied by `cutoffEfold_alpha_le`), the harmonic
sum `∑_{e=2}^{D} 1/e ≤ log D` (`sum_inv_Icc_le_log`) and the side condition `log D ≤ log(XY)`
collapse `(log XY)^{A+1}` back to `(log XY)^A`, yielding the exact `hErrSum` slot at exponent `A`.
Composing with `cutoffEfold_alpha_le` closes the error side down to the per-`e` small
cutoff-SW input `hsmall` + the four thresholds (mirror of `general_BV_alpha_final`). -/
theorem hErrSum_cutoff_final' (α : ℕ → ℂ) (N X Y T D D0 : ℕ) (Dset : Finset ℕ) {A Kerr : ℝ}
    (hD1 : 1 ≤ D)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D) (hDN : D < N)
    (hKerr : 0 ≤ Kerr) (hLpos : 0 < Real.log ((X : ℝ) * (Y : ℝ)))
    (hlogD : Real.log D ≤ Real.log ((X : ℝ) * (Y : ℝ)))
    (hPerE : ∀ e, 2 ≤ e → e ≤ D →
        cutoffEfoldTerm α N X Y T D0 Dset e
          ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1))
              * (1 / (e : ℝ))) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
              - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  have hc0 : 0 ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) :=
    mul_nonneg hKerr (div_nonneg (by positivity) (Real.rpow_pos_of_pos hLpos (A + 1)).le)
  refine hErrSum_cutoff_discharge α N X Y T D D0 Dset
      (fun e => Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1))
        * (1 / (e : ℝ)))
      hDset1 hDsetD hDN hPerE ?_
  calc ∑ e ∈ Finset.Icc 2 D,
          Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) * (1 / (e : ℝ))
      = (Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)))
          * ∑ e ∈ Finset.Icc 2 D, (1 / (e : ℝ)) := by rw [← Finset.mul_sum]
    _ ≤ (Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1))) * Real.log D :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log hD1) hc0
    _ ≤ (Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)))
          * Real.log ((X : ℝ) * (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogD hc0
    _ = Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
        rw [Real.rpow_add hLpos A 1, Real.rpow_one]
        field_simp

open Classical in
/-- **WBV5 (FLOOR C, FULL) — the `hErrSum` slot discharged to the four thresholds + per-`e`
small.**  The end-to-end error-side closure: `cutoffEfold_alpha_le` (per `e`) filled into
`hErrSum_cutoff_final'` (the `1/e` harmonic envelope).  Discharges the `hErrSum` slot of
`cutoff_hLargeDisc` down to exactly the residual inputs of `general_BV_alpha_final`'s shape —
the per-`e` small cutoff-SW input `hsmall` and the four coupled operating-point thresholds
`hlev`/`hD0lo`/`hMlev`/`hdiv` (the H-glue supplies them).  `Kerr = Ksmall + 15360`. -/
theorem hErrSum_cutoff_of_thresholds (α : ℕ → ℂ) (N X Y T D0 D k0 K : ℕ) (Dset : Finset ℕ)
    {A Ksmall : ℝ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hD1 : 1 ≤ D) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hDN : D < N) (h2D0 : 2 ≤ D0) (hD0D : D0 ≤ D) (hD0pow : D0 = 2 ^ k0) (hK : K = Nat.log 2 D)
    (hYpos : 0 < Y) (hXpos : 0 < X) (hA : 0 ≤ A) (hKsmall : 0 ≤ Ksmall)
    (hL1 : 1 ≤ Real.log ((X : ℝ) * (Y : ℝ)))
    (hlogD : Real.log D ≤ Real.log ((X : ℝ) * (Y : ℝ)))
    (hlev : (D : ℝ) * (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (Y : ℝ)))
    (hD0lo : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 4) ≤ (D0 : ℝ))
    (hMlev : (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt (Y : ℝ))
    (hdiv : ∀ e, 2 ≤ e → e ≤ D →
        (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ))
    (hsmall : ∀ e, 2 ≤ e → e ≤ D →
        ∑ f ∈ Finset.Icc 2 D0,
            ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
              * cutoffPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) Y (T / e) f
          ≤ Ksmall * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1))
              * (1 / (e : ℝ))) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X Y T d χ
              - cutoffTwist α (blockPrimeInd N) X Y T χ.conductor χ.primitiveCharacter‖
      ≤ (Ksmall + 15360) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  refine hErrSum_cutoff_final' α N X Y T D D0 Dset hD1 hDset1 hDsetD hDN (by positivity)
    (by linarith) hlogD ?_
  intro e he2 heD
  exact cutoffEfold_alpha_le α N X Y T D0 D e k0 K Dset hα he2 heD hD1 hDset1 hDsetD h2D0 hD0D
    hD0pow hK hYpos hXpos hA hL1 hlev hD0lo hMlev (hdiv e he2 heD) (hsmall e he2 heD)

/-! ## 4. `general_BV_cutoff_closed` — the fully-fed windowed BV (item 3)

`general_BV_cutoff_final` (WBV4) with BOTH named slots discharged, mirroring the final shape of
`general_BV_alpha_final`.  The residual inputs (exactly analogous to `general_BV_alpha_final`'s
retained `hMainEnergy`/`hsmall`) are:

* **`hSmallCut`** — the window small-conductor cutoff energy input (`∑_{2≤f≤D0} (1/φf)·
  cutoffPrimEnergy ≤ Km·XM/L^{A+1}`); it feeds `hMainEnergy_cutoff_discharge`'s named small half.
  (The cutoff twist does not factor, so — unlike the bilinear `hβSW` — the SW cancellation is
  packaged at the `cutoffPrimEnergy` level.)
* **`hGlue` + `hGsum`** — the per-`e` envelope of the `α`-side error e-fold
  (`cutoffEfoldTerm e ≤ G e`, `∑_e G e ≤ Kerr·XM/L^A`); it feeds `hErrSum_cutoff_discharge`.
  Its discharge to the four coupled operating-point thresholds (`hlev`/`hD0lo`/`hMlev`/`hdiv`, à
  la `efold_large_discharge`) via `cutoffEfoldTerm`'s regroup + `dyadic_energy_le_cutoff_dvd`
  fibering is the one remaining analytic core — the exact cutoff analogue of the bilinear
  `hlarge`; see the module header.

**The operating-point threshold list (for the H-glue).**  Beyond the structural/scale set of
`general_BV_cutoff_final` (the SW coupling `K·L^{A+C0} ≤ Kβ·(log N)^{A+2C0}`, `D0 ≍ L^{C0}`,
`N ≤ M ≤ 2N`, `D < N`), the `hMainEnergy` discharge wants: `2 ≤ X,M`; `A+2 ≤ B ≤`, the level cut
`D ≤ √(XM)/L^B`; `A+2 ≤ C0` with `L^{C0} ≤ 2·2^{k0}` (`D0 = 2^{k0}`); and `L^{A+3} ≤ √X,√M`.
`Kmain = 6(Km+448+32√26)`. -/
open Classical in
/-- **WBV5 (item 3, FULL) — `general_BV_cutoff_closed`.**  `general_BV_cutoff_final` with both
named slots fed: `hMainEnergy` by `hMainEnergy_cutoff_discharge` (small half named `hSmallCut`)
and `hErrSum` by `hErrSum_cutoff_discharge` (per-`e` envelope named `hGlue`/`hGsum`).  Mirror of
`general_BV_alpha_final`'s final shape (which likewise retains `hMainEnergy`/`hsmall`).  The
windowed `L¹`-over-`d` AP discrepancy at residue `2` meets the target envelope
`(Kβ + (6(Km+448+32√26) + Kerr))·XM/L^A`. -/
theorem general_BV_cutoff_closed {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ) (Kβ Km Kerr B : ℝ)
        (G : ℕ → ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime 2 d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < N →
        -- operating-point thresholds for the `hMainEnergy` discharge
        2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ C0 ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        (∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
            ≤ Km * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) →
        -- per-`e` envelope for the `hErrSum` discharge
        (∀ e, 2 ≤ e → e ≤ D → cutoffEfoldTerm α N X M T D0 Dset e ≤ G e) →
        (∑ e ∈ Finset.Icc 2 D, G e
            ≤ Kerr * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M 2 d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26) + Kerr)) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_cutoff_final (A := A) (C0 := C0) hA hC0
  refine ⟨K, N₀, hK0, fun α X N M T D0 D k0 Klog Dset Kβ Km Kerr B G hα hKβ hKm hN hM2N hD0N
    hDge1 hcop2 hLpos hD0 hD0N' hNM hscale hD1 hDsetD hDN hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKeq
    hDscale hD0lo hXsqrt hMsqrt hSmallCut hGlue hGsum => ?_⟩
  have hβ1 : ∀ n, ‖blockPrimeInd N n‖ ≤ 1 := by
    intro n; unfold blockPrimeInd
    by_cases h : N < n ∧ n.Prime
    · rw [if_pos h, norm_one]
    · rw [if_neg h, norm_zero]; norm_num
  -- discharge `hMainEnergy` (`Kmain = 6(Km+448+32√26)`).
  have hMainEnergy : 4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * cutoffPrimEnergy α (blockPrimeInd N) X M T f
      ≤ (6 * (Km + 448 + 32 * Real.sqrt 26)) * ((X : ℝ) * (M : ℝ))
          / (Real.log ((X : ℝ) * (M : ℝ))) ^ A :=
    hMainEnergy_cutoff_discharge hA.le hX2 hM2 hD1 hBge hCge hD0eq h2D0 hD0D hKeq hDscale hD0lo
      hXsqrt hMsqrt hKm α (blockPrimeInd N) hα hβ1 hSmallCut
  -- discharge `hErrSum` via the per-`e` envelope.
  have hErrSum : ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖cutoffTwist α (blockPrimeInd N) X M T d χ
              - cutoffTwist α (blockPrimeInd N) X M T χ.conductor χ.primitiveCharacter‖
      ≤ Kerr * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A :=
    hErrSum_cutoff_discharge α N X M T D D0 Dset G hDge1 hDsetD hDN hGlue hGsum
  exact hbody α X N M T D0 D Dset Kβ (6 * (Km + 448 + 32 * Real.sqrt 26)) Kerr hα hKβ hN hM2N
    hD0N hDge1 hcop2 hLpos hD0 hD0N' hNM hscale hD1 hDsetD hMainEnergy hErrSum

/-! ## 5. Composition sanity (item 4) — the end-to-end chain elaborates

`general_BV_cutoff_closed` supplies the windowed `L¹`-over-`d` carrier price at each cutoff `T`
(the `hprice_hi`/`hprice_lo` inputs of WBV4's `hHD_of_generalBV_window`, at `T = x` and
`T = x/2+1`), which prices the per-`(j, box)` honest discrepancy end-to-end. -/

section CompositionSanity

#check @Salt.Chen.hMainEnergy_cutoff_discharge
#check @Salt.Chen.cutoffTwist_sub_efold_blockPrimeInd
#check @Salt.Chen.cutoffEfoldTerm_reduce_dense
#check @Salt.Chen.cutoffEfold_large_discharge
#check @Salt.Chen.cutoffEfold_alpha_le
#check @Salt.Chen.hErrSum_cutoff_final'
#check @Salt.Chen.hErrSum_cutoff_of_thresholds
#check @Salt.Chen.hErrSum_cutoff_discharge
#check @Salt.Chen.general_BV_cutoff_closed
#check @Salt.Chen.hHD_of_generalBV_window

end CompositionSanity

end Salt.Chen
