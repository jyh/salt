/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PerEEngine

/-!
# PE1 + PE2 — the reshaped keystone-2 composition (honest `1/e` envelope) + the β-side vanishing

Design: `docs/blueprints/chen.md`, "THE PE ARC" section, and `docs/blueprints/flags.md`,
"2026-07-13 THE hPerE RECON — CATCH #43".

**Why this file exists (catch #43).**  The landed keystone-2 composition
(`Salt.Chen.general_BV_final`, in `PerEEngine.lean`) packages the per-`e` energy glue
`hPerE` through the pointwise envelope `EfoldTerm e ≤ Kerr·(XM/(log XM)^A)·(1/e²)`.  That
envelope is **numerically false**: `EfoldTerm` is a cancellation-free sum of norm-products
and small-scale computation shows the honest decay is `~1/e`, not `1/e²` — no fixed `Kerr`
works.  The landed `general_BV_final` (true, but resting on an *undischargeable* hypothesis)
is left untouched and superseded; this file provides the **reshaped** composition at the
honest `1/e` envelope.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

**PE2 — the β-side collapse (self-contained):**

1. `EfoldTermAlpha` / `EfoldTermBeta` — the two halves of `EfoldTerm`'s inner bracket
   (the α-product `‖A^{(e)}‖·‖B_d‖` and the β-product `‖A⋆‖·‖B^{(e)}‖`), and
   `EfoldTerm_split` : `EfoldTerm = EfoldTermAlpha + EfoldTermBeta`.
2. `blockPrimeInd_dilated_eq_zero` — for `2 ≤ e ≤ N`, `blockPrimeInd N (e·n') = 0`:
   `e·n'` is composite for `n' ≥ 2` (divisor `e` with `1 < e < e·n'`), and for `n' ∈ {0,1}`
   the block condition `N < e·n'` fails (`e·n' ≤ e ≤ N`).
3. `EfoldTermBeta_eq_zero` — under `2 ≤ e ≤ N` and `β = blockPrimeInd N`, the β-side vanishes
   (every dilated coefficient `β(e·n')` is `0`, so the twist is `0`, so the norm is `0`).

**PE1 — the mirror at the honest `1/e` envelope:**

4. `sum_inv_Icc_le_log` — the harmonic bound `∑_{e=2}^{D} 1/e ≤ log D` (telescoping the
   `1/(k+1) ≤ log(k+1) − log k` step via `Real.log_le_sub_one_of_pos`).
5. `hErrSum_final'` — the mirror of `hErrSum_final` with the per-`e` slot at the honest
   `(1/e)` decay.  See the ENVELOPE-SHAPE note below for the chosen delta.
6. `hLargeDisc_of_perE'` / `general_BV_final'` — the mirrored composition, feeding the
   landed `bilinear_hLargeDisc` / `general_BV_closed` **unchanged** (their consumer shape is
   preserved exactly), with the new side condition `D < N` threaded through.
7. `hPerE_reduces_to_alpha` — under `2 ≤ e ≤ D < N`, `EfoldTerm = EfoldTermAlpha` (from 3+
   `EfoldTerm_split`): the shape PE3 will discharge.

## ENVELOPE-SHAPE CHOICE (item 6's documented delta vs the landed `general_BV_final`)

The honest per-`e` decay is `1/e`, and `∑_{e=2}^{D} 1/e ≤ log D` (item 4).  To keep the
downstream consumer (`bilinear_hLargeDisc`'s `hErrSum` slot, and hence `general_BV_closed`)
**byte-for-byte identical** to the landed form, the `log D` is absorbed by *raising the
per-`e` input exponent by one*:

* **landed** per-`e` input: `EfoldTerm e ≤ Kerr·(XM/(log XM)^A)·(1/e²)`, output at `A`;
* **here** per-`e` input:  `EfoldTerm e ≤ Kerr·(XM/(log XM)^{A+1})·(1/e)`, output at `A`.

Summing the honest envelope gives
`∑_e Kerr·(XM/(log XM)^{A+1})·(1/e) ≤ Kerr·(XM/(log XM)^{A+1})·log D`, and the side
condition `log D ≤ log(XM)` (derived from `D < N ≤ M ≤ XM`, i.e. the threaded `D < N`)
collapses `(log XM)^{A+1}` back to `(log XM)^A`:
`≤ Kerr·(XM/(log XM)^{A+1})·log(XM) = Kerr·XM/(log XM)^A`.
So the OUTPUT shape and the whole `general_BV_final'` conclusion are **exactly** the landed
`general_BV_final` conclusion; the only deltas SW3 sees are (a) the per-`e` hypothesis is now
at exponent `A+1` (was `A`) with `1/e` (was `1/e²`), and (b) the new side condition `D < N`.
This is the "A → A+1" absorption of catch #43's recon — a threshold-level shift, adversarially
verified safe (no interaction with the fixed-margin E₁/S-row ledger).

All proofs are within default `maxHeartbeats`; no `native_decide`, no new axioms
(`[propext, Classical.choice, Quot.sound]` only).
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## PE2.1 — the α/β split of `EfoldTerm`'s inner bracket -/

open Classical in
/-- The **α-half** of `EfoldTerm`'s inner bracket: the dilated α-twist `A^{(e)}(χ⋆)` paired
against the imprimitive β-twist `B_d(χ)`, summed over the large moduli `d` with `e ∣ d`. -/
noncomputable def EfoldTermAlpha (α β : ℕ → ℂ) (X Y D0 : ℕ) (Dset : Finset ℕ) (e : ℕ) : ℝ :=
  ∑ d ∈ (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d),
    (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        (‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β Y d χ‖)

open Classical in
/-- The **β-half** of `EfoldTerm`'s inner bracket: the primitive α-twist `A⋆(χ⋆)` paired
against the dilated β-twist `B^{(e)}(χ⋆)`, summed over the large moduli `d` with `e ∣ d`. -/
noncomputable def EfoldTermBeta (α β : ℕ → ℂ) (X Y D0 : ℕ) (Dset : Finset ℕ) (e : ℕ) : ℝ :=
  ∑ d ∈ (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d),
    (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        (‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist (fun n' => β (e * n')) (Y / e) χ.conductor χ.primitiveCharacter‖)

open Classical in
/-- **The α/β split (FULL).**  `EfoldTerm = EfoldTermAlpha + EfoldTermBeta` — distributing the
`(α-product + β-product)` bracket over the `χ`- and `d`-sums (`Finset.sum_add_distrib` +
`mul_add`). -/
theorem EfoldTerm_split (α β : ℕ → ℂ) (X Y D0 : ℕ) (Dset : Finset ℕ) (e : ℕ) :
    EfoldTerm α β X Y D0 Dset e
      = EfoldTermAlpha α β X Y D0 Dset e + EfoldTermBeta α β X Y D0 Dset e := by
  unfold EfoldTerm EfoldTermAlpha EfoldTermBeta
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]

/-! ## PE2.2 — the β-side vanishes (`β = blockPrimeInd N`, `D < N`) -/

/-- **The dilated interval-prime indicator vanishes.**  For `2 ≤ e ≤ N`,
`blockPrimeInd N (e·n') = 0` for every `n'`: if `n' ≥ 2` then `e·n'` is composite (divisor
`e` with `1 < e < e·n'`), and if `n' ∈ {0, 1}` the block condition `N < e·n'` fails
(`e·n' ≤ e ≤ N`). -/
theorem blockPrimeInd_dilated_eq_zero {N e n' : ℕ} (he : 2 ≤ e) (heN : e ≤ N) :
    blockPrimeInd N (e * n') = 0 := by
  unfold blockPrimeInd
  rw [if_neg]
  rintro ⟨hlt, hp⟩
  rcases hp.eq_one_or_self_of_dvd e (dvd_mul_right e n') with h1 | h2
  · omega
  · have hn' : n' = 1 :=
      (Nat.eq_of_mul_eq_mul_left (by omega : 0 < e) (by rw [mul_one]; exact h2)).symm
    subst hn'
    rw [mul_one] at hlt
    omega

/-- The dilated β-twist vanishes for the interval-prime indicator (`2 ≤ e ≤ N`): every
coefficient `blockPrimeInd N (e·n')` is `0`. -/
theorem bilinTwist_blockPrimeInd_dilated_eq_zero {N e Z c : ℕ} (he : 2 ≤ e) (heN : e ≤ N)
    (ψ : DirichletCharacter ℂ c) :
    bilinTwist (fun n' => blockPrimeInd N (e * n')) Z c ψ = 0 := by
  unfold bilinTwist
  apply Finset.sum_eq_zero
  intro m _
  change blockPrimeInd N (e * m) * ψ (m : ZMod c) = 0
  rw [blockPrimeInd_dilated_eq_zero he heN, zero_mul]

open Classical in
/-- **PE2 — the β-side vanishes (FULL).**  Under `2 ≤ e ≤ N`, for `β = blockPrimeInd N` the
β-half `EfoldTermBeta` is identically `0`: the dilated β-twist `B^{(e)}(χ⋆)` is `0` (every
`blockPrimeInd N (e·n') = 0`), so every summand `‖A⋆‖·‖B^{(e)}‖` vanishes.  Combined with
`e ≤ D < N` at the operating point, this removes the flag's uncontrolled β-side entirely. -/
theorem EfoldTermBeta_eq_zero (α : ℕ → ℂ) (N X Y D0 e : ℕ) (Dset : Finset ℕ)
    (he : 2 ≤ e) (heN : e ≤ N) :
    EfoldTermBeta α (blockPrimeInd N) X Y D0 Dset e = 0 := by
  unfold EfoldTermBeta
  apply Finset.sum_eq_zero
  intro d _
  have hinner : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
      (‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
          * ‖bilinTwist (fun n' => blockPrimeInd N (e * n')) (Y / e)
              χ.conductor χ.primitiveCharacter‖) = 0 := by
    apply Finset.sum_eq_zero
    intro χ _
    rw [bilinTwist_blockPrimeInd_dilated_eq_zero he heN, norm_zero, mul_zero]
  rw [hinner, mul_zero]

/-! ## PE1.1 — the harmonic bound `∑_{e=2}^{D} 1/e ≤ log D` -/

/-- **The harmonic bound (FULL).**  `∑_{e=2}^{D} 1/e ≤ log D` for `1 ≤ D`, telescoping the
per-step bound `1/(k+1) ≤ log(k+1) − log k` (from `Real.log_le_sub_one_of_pos` at
`x = k/(k+1)`).  The honest `∑ 1/e ~ log D` convergence shape that replaces the (false)
`∑ 1/e² ≤ 1` envelope of catch #43. -/
theorem sum_inv_Icc_le_log {D : ℕ} (hD : 1 ≤ D) :
    ∑ e ∈ Finset.Icc 2 D, (1 / (e : ℝ)) ≤ Real.log D := by
  induction D, hD using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
    have hn1 : (0 : ℝ) < (n : ℝ) := by
      have h : 0 < n := by omega
      exact_mod_cast h
    have hn1' : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hx : (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) := div_pos hn1 hn1'
    have hlog := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div hn1.ne' hn1'.ne'] at hlog
    have hkey : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
      have heq : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [heq] at hlog
      linarith
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, hkey]

/-! ## PE1.2 — the `hErrSum` discharge at the honest `1/e` envelope -/

open Classical in
/-- **PE1 — the `hErrSum` discharge at the honest `1/e` envelope.**  Mirror of
`hErrSum_final` (in `PerEEngine.lean`) with the per-`e` glue at the honest decay:
`EfoldTerm e ≤ Kerr·(XY/(log XY)^{A+1})·(1/e)` (was the false `(1/e²)` at exponent `A`).
`hErrSum_discharge` with `G e = Kerr·(XY/(log XY)^{A+1})·(1/e)`, whose sum bounds by
`sum_inv_Icc_le_log` (`∑_{e=2}^{D} 1/e ≤ log D`), then the side condition
`log D ≤ log(XY)` collapses `(log XY)^{A+1}` back to `(log XY)^A` — so the OUTPUT is the exact
`hErrSum` slot of `bilinear_hLargeDisc` at exponent `A`, unchanged.  See the module
ENVELOPE-SHAPE note. -/
theorem hErrSum_final' (α β : ℕ → ℂ) (X Y D D0 : ℕ) (Dset : Finset ℕ) {A Kerr : ℝ}
    (hD1 : 1 ≤ D)
    (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hKerr : 0 ≤ Kerr) (hLpos : 0 < Real.log ((X : ℝ) * (Y : ℝ)))
    (hlogD : Real.log D ≤ Real.log ((X : ℝ) * (Y : ℝ)))
    (hPerE : ∀ e, 2 ≤ e → e ≤ D →
        EfoldTerm α β X Y D0 Dset e
          ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1))
              * (1 / (e : ℝ))) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ‖
                + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                  * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
      ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  have hc0 : 0 ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1)) :=
    mul_nonneg hKerr (div_nonneg (by positivity) (Real.rpow_pos_of_pos hLpos (A + 1)).le)
  refine hErrSum_discharge α β X Y D D0 Dset
      (fun e => Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1))
        * (1 / (e : ℝ)))
      hDset1 hDsetD hPerE ?_
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
        have hLne : Real.log ((X : ℝ) * (Y : ℝ)) ≠ 0 := hLpos.ne'
        have hLAne : (Real.log ((X : ℝ) * (Y : ℝ))) ^ A ≠ 0 :=
          (Real.rpow_pos_of_pos hLpos A).ne'
        rw [Real.rpow_add hLpos A 1, Real.rpow_one]
        field_simp

/-! ## PE1.3 — the `hLargeDisc` discharge and the composed keystone `general_BV_final'` -/

open Classical in
/-- **PE1 — the `hLargeDisc` discharge (both cores, honest `1/e` envelope).**  Mirror of
`hLargeDisc_of_perE`: `bilinear_hLargeDisc` fed by `hErrSum_final'` (the honest envelope) and
the named `hMainEnergy`.  Consumer (`bilinear_hLargeDisc`) unchanged; `Klarge = Kmain + Kerr`,
output at exponent `A`.  The `hErrSum` per-`e` slot is now at `(1/e)` with exponent `A+1` and
carries the side condition `log D ≤ log(XY)` (see the module ENVELOPE-SHAPE note). -/
theorem hLargeDisc_of_perE' (α β : ℕ → ℂ) (X Y D D0 : ℕ) (Dset : Finset ℕ)
    {A Kmain Kerr : ℝ}
    (hD1 : 1 ≤ D) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hKerr : 0 ≤ Kerr) (hLpos : 0 < Real.log ((X : ℝ) * (Y : ℝ)))
    (hlogD : Real.log D ≤ Real.log ((X : ℝ) * (Y : ℝ)))
    (hMainEnergy : 4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A)
    (hPerE : ∀ e, 2 ≤ e → e ≤ D →
        EfoldTerm α β X Y D0 Dset e
          ≤ Kerr * ((X : ℝ) * (Y : ℝ) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ (A + 1))
              * (1 / (e : ℝ))) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ (Kmain + Kerr) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A :=
  bilinear_hLargeDisc α β X Y D D0 Dset hD1 hDsetD hMainEnergy
    (hErrSum_final' α β X Y D D0 Dset hD1 hDset1 hDsetD hKerr hLpos hlogD hPerE)

open Classical in
/-- **PE1 — general BV, the reshaped keystone-2 composition (honest `1/e` envelope).**
Mirror of the landed `general_BV_final` (in `PerEEngine.lean`) with the per-`e` slot at the
HONEST envelope `EfoldTerm e ≤ Kerr·(XM/(log XM)^{A+1})·(1/e)` (catch #43: the landed
`(1/e²)` at exponent `A` is undischargeable) and the NEW side condition `D < N` threaded
through.  The `D < N` gives `log D ≤ log(XM)` (from `D < N ≤ M ≤ XM`, `X ≥ 1` from `hXM1`),
which absorbs the `log D` from the harmonic sum back into exponent `A` — so the CONCLUSION is
byte-for-byte the landed `general_BV_final` conclusion, and this feeds `general_BV_closed`
(and hence SW3) at the identical output shape.  See the module ENVELOPE-SHAPE note for the
full delta. -/
theorem general_BV_final' {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M R₀ D0 D : ℕ) (Dset : Finset ℕ) (Kβ Kmain Kerr : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 3 ≤ N → N₀ ≤ N → N ≤ M → M ≤ 2 * N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime R₀ d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2 * C0)
            ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < N → 0 ≤ Kerr →
        (1 : ℝ) ≤ (X : ℝ) * (M : ℝ) →
        (4 * (1 + Real.log D) *
            ∑ f ∈ Finset.Icc 2 D,
              (1 / (f.totient : ℝ)) * bilinPrimEnergy α (blockPrimeInd N) X M f
          ≤ Kmain * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        (∀ e, 2 ≤ e → e ≤ D →
            EfoldTerm α (blockPrimeInd N) X M D0 Dset e
              ≤ Kerr * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1))
                  * (1 / (e : ℝ))) →
        ∑ d ∈ Dset, ‖apDiscBilin α (blockPrimeInd N) X M R₀ d‖
          ≤ (Kβ + (Kmain + Kerr)) * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_closed (A := A) (C0 := C0) hA hC0
  refine ⟨K, N₀, hK0, fun α X N M R₀ D0 D Dset Kβ Kmain Kerr hα hKβ hN3 hN hNM hM2N
    hDge1 hcop hLpos hD0 hD0N hscale hD1 hDsetD hDN hKerr hXM1 hMainEnergy hPerE => ?_⟩
  refine hbody α X N M R₀ D0 Dset Kβ (Kmain + Kerr) hα hKβ hN3 hN hNM hM2N hDge1 hcop
    hLpos hD0 hD0N hscale ?_
  -- Derive `log D ≤ log (X·M)` from `D < N ≤ M ≤ X·M` (`X ≥ 1` from `hXM1`).
  have hX1 : 1 ≤ X := by
    rcases Nat.eq_zero_or_pos X with hX0 | hX0
    · exfalso; rw [hX0, Nat.cast_zero, zero_mul] at hXM1; linarith
    · omega
  have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hDM : (D : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le hDN hNM)
  have hMXM : (M : ℝ) ≤ (X : ℝ) * (M : ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg M) hX1R
  have hDXM : (D : ℝ) ≤ (X : ℝ) * (M : ℝ) := le_of_lt (lt_of_lt_of_le hDM hMXM)
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h : 0 < D := by omega
    exact_mod_cast h
  have hlogD : Real.log D ≤ Real.log ((X : ℝ) * (M : ℝ)) := Real.log_le_log hDpos hDXM
  exact hLargeDisc_of_perE' α (blockPrimeInd N) X M D D0 Dset hD1 hDge1 hDsetD hKerr
    hLpos hlogD hMainEnergy hPerE

/-! ## PE bonus — the per-`e` slot reduces to the α-side under `D < N` -/

open Classical in
/-- **BONUS — `hPerE` reduces to the α-side.**  Under `2 ≤ e ≤ D < N` and
`β = blockPrimeInd N`, `EfoldTerm = EfoldTermAlpha` (from `EfoldTerm_split` +
`EfoldTermBeta_eq_zero`).  So `general_BV_final'`'s per-`e` slot may be stated directly on
`EfoldTermAlpha` — the exact shape PE3 will discharge. -/
theorem hPerE_reduces_to_alpha (α : ℕ → ℂ) (N X Y D0 D e : ℕ) (Dset : Finset ℕ)
    (he : 2 ≤ e) (heD : e ≤ D) (hDN : D < N) :
    EfoldTerm α (blockPrimeInd N) X Y D0 Dset e
      = EfoldTermAlpha α (blockPrimeInd N) X Y D0 Dset e := by
  rw [EfoldTerm_split, EfoldTermBeta_eq_zero α N X Y D0 e Dset he (by omega), add_zero]

end Salt.Chen
