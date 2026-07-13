/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ErrFold
import Salt.Chen.ConductorDescent

/-!
# C3c⁗ — the per-`e` energy glue (keystone 2's final composition)

Design: `docs/blueprints/chen.md`, the C3c row.  `Salt.Chen.hErrSum_discharge` (C3c‴)
reorganised the α/β coprimality error of `bilinear_hLargeDisc`'s `hErrSum` slot into
`∑_{e=2}^{D} EfoldTerm e` and exposed the single remaining analytic core as a named
per-`e` glue.  This file lands the **density fold** it rests on, packages the glue into
the `1/e²` convergence envelope, and **composes the entire keystone-2 stack** —
`hErrSum_discharge` (C3c‴) + `hMainEnergy_discharge` (C3c″) + `bilinear_hLargeDisc`
(C3c′) + `general_BV_closed` (C3c) — into `general_BV_final`, closed for
`β = blockPrimeInd N` modulo the operating-scale side conditions, `‖α‖ ≤ 1`, and the
single named per-`e` energy glue `hPerE`.

## What this file lands (sorry-free)

1. **The `e ∣ d` density fold** (`efold_density_fold`) — FULL.  For the large moduli
   `d` that are multiples of `e`, `∑_{d} (1/φd)·W(d) ≤ M·(4/φe)(1+log D)` whenever
   `W(d) ≤ M`.  A direct offset-`e` instance of `Salt.LS.sum_inv_totient_dvd_le'`
   (`∑_{q≤Q, e∣q} 1/φq ≤ (4/φe)(1+log Q)`): the reusable BDH density the per-`e`
   shifted-scale energy consumes.  This is step 1 of the design route (the `swapPhi`
   pattern at offset `e`).

2. **The `hErrSum` discharge via the `1/e²` envelope** (`hErrSum_final`) — the exact
   `hErrSum` slot of `bilinear_hLargeDisc`, discharged from the single named per-`e`
   glue `hPerE : EfoldTerm e ≤ Kerr·(XY/(log XY)^A)·(1/e²)`: `hErrSum_discharge` with
   `G e = Kerr·(XY/(log XY)^A)·(1/e²)`, whose sum telescopes by `sum_inv_sq_Icc_le_one`
   (`∑_{e=2}^{N} 1/e² ≤ 1`).  This packages the per-`e` glue into the convergent shape.

3. **The `hLargeDisc` discharge** (`hLargeDisc_of_perE`) — the exact `hLargeDisc` slot
   of `general_BV_closed`, discharged from the named `hMainEnergy` (core 1, dischargeable
   by `hMainEnergy_discharge`) and the named per-`e` glue `hPerE` (core 2's remaining
   piece): `bilinear_hLargeDisc` fed by `hErrSum_final`.

4. **The composed keystone** (`general_BV_final`) — `general_BV_closed` with `hLargeDisc`
   discharged for `β = blockPrimeInd N` via `hLargeDisc_of_perE`.  Keystone 2's whole
   analytic stack, closed modulo: the operating-scale side conditions, `‖α‖ ≤ 1`, the
   named main-energy bound `hMainEnergy` (its own C3c″ discharge), and the single named
   per-`e` energy glue `hPerE`.

## FLAG (Iron Rule 1 / STOP-AND-FLAG / PB-floor A) — the per-`e` energy glue `hPerE`

`hPerE` is **not** discharged here; it remains the single named analytic core, exposed
as a hypothesis of `hErrSum_final`/`hLargeDisc_of_perE`/`general_BV_final`.  `EfoldTerm e`
is a per-`e` re-run of the C3c″ dyadic energy engine at the shifted scale `(⌊X/e⌋, Y)`
(α-side) and `(X, ⌊Y/e⌋)` (β-side), restricted to moduli `d` with `e ∣ d`.  The honest
obstruction (recorded in `docs/blueprints/flags.md`, C3c⁗): the α-side pairs the *dilated
primitive* twist `A^{(e)}(χ⋆)` against the *imprimitive* full twist `B_d(χ)`, which is
**not** a clean primitive block energy — a second full copy of the Cauchy–Schwarz +
two-regime (small conductor via `hβSW`, large via the dyadic shell) treatment with
delicate scale bookkeeping.  Moreover the naive `large-e` trivial branch does **not**
close crudely: the α-side threshold `e ≷ X/(log)^{2A+6}` controls `⌊X/e⌋`, but the β-side
`A⋆` sits at the *full* scale `X` (only `B^{(e)}` dilates to `Y/e`), so a single threshold
leaves the β-side crude total `~ D·XY/e²` uncontrolled when `Y ≫ X` — the two sides need
independent `X`- and `Y`-scale thresholds and their own energy engines.  The density fold
(step 1 above, the reusable convergent weight) is landed; re-running both engines is the
deferred research core.  Consequently `general_BV_final` closes modulo this single
`hPerE` glue (all four structural layers — identity, reorganisation, envelope, and the
full keystone composition — are landed).

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The `e ∣ d` density fold (the `swapPhi`-at-offset pattern) -/

/-- **The `e ∣ d` density fold (BDH offset-`e` density) — FULL.**  Over the large
moduli `d` (in `Dset`, `d > D0`) that are multiples of `e`, a per-`d` weight `W(d)`
uniformly bounded by `M ≥ 0` gives
`∑_d (1/φd)·W(d) ≤ M·(4/φe)·(1+log D)`.  This is the offset-`e` instance of
`Salt.LS.sum_inv_totient_dvd_le'` (`∑_{q ∈ [1,Q], e∣q} 1/φq ≤ (4/φe)(1+log Q)`) — the
reusable convergent density the per-`e` shifted-scale energy consumes (step 1 of the
per-`e` route). -/
lemma efold_density_fold {e D D0 : ℕ} (Dset : Finset ℕ) (he : 1 ≤ e) (hD : 1 ≤ D)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (W : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hWM : ∀ d ∈ (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d), W d ≤ M) :
    ∑ d ∈ (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d),
        (1 / (d.totient : ℝ)) * W d
      ≤ M * ((4 / (e.totient : ℝ)) * (1 + Real.log D)) := by
  classical
  set S := (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d) with hSdef
  have hsub : S ⊆ (Finset.Icc 1 D).filter (fun d => e ∣ d) := by
    intro d hd
    simp only [hSdef, Finset.mem_filter] at hd
    obtain ⟨⟨hdset, _⟩, hed⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hDset1 d hdset, hDsetD d hdset⟩, hed⟩
  calc ∑ d ∈ S, (1 / (d.totient : ℝ)) * W d
      ≤ ∑ d ∈ S, (1 / (d.totient : ℝ)) * M := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        exact mul_le_mul_of_nonneg_left (hWM d hd) (by positivity)
    _ = M * ∑ d ∈ S, (1 / (d.totient : ℝ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ M * ∑ d ∈ (Finset.Icc 1 D).filter (fun d => e ∣ d), (1 / (d.totient : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
    _ ≤ M * ((4 / (e.totient : ℝ)) * (1 + Real.log D)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        exact Salt.LS.sum_inv_totient_dvd_le' he hD

/-! ## 2. The `hErrSum` discharge via the `1/e²` envelope -/

open Classical in
/-- **The `hErrSum` discharge (C3c⁗, the per-`e` glue packaged).**  The exact `hErrSum`
slot of `bilinear_hLargeDisc`, discharged from the single named per-`e` glue
`hPerE : EfoldTerm e ≤ Kerr·(XY/(log XY)^A)·(1/e²)`.  `hErrSum_discharge` (C3c‴) with
`G e = Kerr·(XY/(log XY)^A)·(1/e²)`; the `∑_e G e` telescopes by `sum_inv_sq_Icc_le_one`
(`∑_{e=2}^{D} 1/e² ≤ 1`) to `Kerr·XY/(log XY)^A`.  This packages the per-`e` glue into the
convergent shape — the honest deliverable modulo the (deferred) energy discharge of
`hPerE`. -/
theorem hErrSum_final (α β : ℕ → ℂ) (X Y D D0 : ℕ) (Dset : Finset ℕ) {A Kerr : ℝ}
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hKerr : 0 ≤ Kerr) (hXY1 : (1 : ℝ) ≤ (X : ℝ) * (Y : ℝ))
    (hPerE : ∀ e, 2 ≤ e → e ≤ D →
        EfoldTerm α β X Y D0 Dset e
          ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) * (1 / (e : ℝ) ^ 2)) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ‖
                + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
      ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  have hL0 : (0 : ℝ) ≤ Real.log ((X : ℝ) * (Y : ℝ)) := Real.log_nonneg hXY1
  have hLA0 : (0 : ℝ) ≤ (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := Real.rpow_nonneg hL0 A
  have hc0 : 0 ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) :=
    mul_nonneg hKerr (div_nonneg (by positivity) hLA0)
  refine hErrSum_discharge α β X Y D D0 Dset
      (fun e => Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) * (1 / (e : ℝ) ^ 2))
      hDset1 hDsetD hPerE ?_
  calc ∑ e ∈ Finset.Icc 2 D,
          Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) * (1 / (e : ℝ) ^ 2)
      = (Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A))
          * ∑ e ∈ Finset.Icc 2 D, (1 / (e : ℝ) ^ 2) := by rw [← Finset.mul_sum]
    _ ≤ (Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A)) * 1 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le_one D) hc0
    _ = Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by rw [mul_one]; ring

/-! ## 3. The `hLargeDisc` discharge (both cores composed) -/

open Classical in
/-- **The `hLargeDisc` discharge (C3c⁗, both cores composed).**  The exact `hLargeDisc`
slot of `general_BV_closed`, discharged from the named main-energy bound `hMainEnergy`
(keystone-2 core 1, itself discharged by `hMainEnergy_discharge` under the operating
scale) and the single named per-`e` glue `hPerE` (core 2's remaining piece):
`bilinear_hLargeDisc` (C3c′) fed by `hErrSum_final`.  `Klarge = Kmain + Kerr`. -/
theorem hLargeDisc_of_perE (α β : ℕ → ℂ) (X Y D D0 : ℕ) (Dset : Finset ℕ)
    {A Kmain Kerr : ℝ}
    (hD1 : 1 ≤ D) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hKerr : 0 ≤ Kerr) (hXY1 : (1 : ℝ) ≤ (X : ℝ) * (Y : ℝ))
    (hMainEnergy : 4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A)
    (hPerE : ∀ e, 2 ≤ e → e ≤ D →
        EfoldTerm α β X Y D0 Dset e
          ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) * (1 / (e : ℝ) ^ 2)) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ (Kmain + Kerr) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A :=
  bilinear_hLargeDisc α β X Y D D0 Dset hD1 hDsetD hMainEnergy
    (hErrSum_final α β X Y D D0 Dset hDset1 hDsetD hKerr hXY1 hPerE)

/-! ## 4. The composed keystone `general_BV_final` -/

open Classical in
/-- **C3c⁗ — general BV, the FULL keystone-2 composition.**  `general_BV_closed` (C3c)
with the `hLargeDisc` slot discharged for `β = blockPrimeInd N` via `hLargeDisc_of_perE`
(= `bilinear_hLargeDisc` + `hErrSum_final`).  The `L¹`-over-`d` bilinear AP-discrepancy at
a fixed residue for the interval prime indicator is bounded by `(Kβ + (Kmain + Kerr))·
XM/(log XM)^A`, closed modulo: the operating-scale side conditions, `‖α‖ ≤ 1`, the named
main-energy bound `hMainEnergy` (its own C3c″ discharge `hMainEnergy_discharge`), and the
single named per-`e` energy glue `hPerE` (the deferred research core; see the module FLAG).
This is the entire analytic stack of keystone 2 assembled — the last structural gap of the
A₃ switch closed down to `hPerE`. -/
theorem general_BV_final {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M R₀ D0 D : ℕ) (Dset : Finset ℕ) (Kβ Kmain Kerr : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 3 ≤ N → N₀ ≤ N → N ≤ M → M ≤ 2 * N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime R₀ d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2 * C0)
            ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → 0 ≤ Kerr → (1 : ℝ) ≤ (X : ℝ) * (M : ℝ) →
        (4 * (1 + Real.log D) *
            ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α (blockPrimeInd N) X M f
          ≤ Kmain * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        (∀ e, 2 ≤ e → e ≤ D →
            EfoldTerm α (blockPrimeInd N) X M D0 Dset e
              ≤ Kerr * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A)
                  * (1 / (e : ℝ) ^ 2)) →
        ∑ d ∈ Dset, ‖apDiscBilin α (blockPrimeInd N) X M R₀ d‖
          ≤ (Kβ + (Kmain + Kerr)) * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_closed (A := A) (C0 := C0) hA hC0
  refine ⟨K, N₀, hK0, fun α X N M R₀ D0 D Dset Kβ Kmain Kerr hα hKβ hN3 hN hNM hM2N
    hDge1 hcop hLpos hD0 hD0N hscale hD1 hDsetD hKerr hXM1 hMainEnergy hPerE => ?_⟩
  refine hbody α X N M R₀ D0 Dset Kβ (Kmain + Kerr) hα hKβ hN3 hN hNM hM2N hDge1 hcop
    hLpos hD0 hD0N hscale ?_
  exact hLargeDisc_of_perE α (blockPrimeInd N) X M D D0 Dset hD1 hDge1 hDsetD hKerr hXM1
    hMainEnergy hPerE

end Salt.Chen
