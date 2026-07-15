/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AlphaSide
import Salt.Chen.DyadicDvd
import Salt.Chen.TotientHelpers

/-!
# PE3c-4 — the `hlarge` assembly (the last analytic estimate of the Chen arc)

Design: `docs/blueprints/flags.md`, "2026-07-13 THE PE3c-4 GATE" (the FROZEN RECIPE),
"PE3c-3", "PE3c-4a", "PE3c RECON", "CATCH #45".

This file discharges the `hlarge` slot named by `Salt.Chen.efold_alpha_le` /
`general_BV_alpha_discharged`: the large-conductor contribution
```
∑_{D0<f≤D} (4/φ(lcm e f))·(1+log D)·bilinPrimEnergy (α∘(e·)) (blockPrimeInd N) (X/e) M f
    ≤ Klarge·(XM/(log XM)^{A+1})·(1/e).
```

## The frozen recipe (implemented here)

* **The gcd density.**  `4/φ(lcm e f) = 4·φ(gcd e f)/(φe·φf)`
  (`totient_lcm_mul_totient_gcd`), and `φ(gcd e f) ≤ gcd e f = ∑_{g ∣ gcd e f} φ g`
  (`totient_le` + `sum_totient_divisors`).  [NB: the gate note's "`φ(gcd) = ∑φ(g)`" is a
  slip — `∑_{g∣n}φg = n`, not `φ n`; the honest step is `φ(gcd) ≤ gcd = ∑φg`, a harmless
  upper bound in an upper-bound estimate.]
* **The fibering.**  `∑_{g ∣ gcd e f} φ g = ∑_{g ∣ e, g ∣ f} φ g`
  (`(gcd e f).divisors = e.divisors.filter (·∣f)`), so swapping the `(f, g)` sums the
  `f`-sum at fixed `g` is the `δ = g`-restricted energy sum, consumed by
  `dyadic_energy_le_dvd` (PE3c-3) at scale `(⌊X/e⌋, M)`.  This is `efold_large_fibered`
  (floor A — an exact reduction).
* **The four-term accounting** (`efold_large_discharge`).  Under the fibering the four
  `dyadic_energy_le_dvd` terms weight by `∑_{g∣e} φ g·(per-g)`; the totient sums
  `∑φg/g ≤ d(e)` (`sum_totient_div_self_le`), `∑φg/√g ≤ √e·d(e)` (`sum_totient_div_sqrt_le`),
  `∑φg = e` (`sum_totient_divisors`) collapse them, and the target closes term-by-term:
  - **main** (`∝ 2^{K+1}/g ~ D/g`): via `hlev : D·L^{C0} ≤ √(XM)` (`C0 = A+5`) and
    `d(e)/√e ≤ 2` (`card_divisors_le_two_sqrt`) — the diagonal `D·√(XM)` closes.
  - **tail** (`g-independent, ∝ √(XM)/D0`): `∑φg = e` cancels the `1/e`; via `D0 ≥ L^{A+4}`
    (`hD0lo`) and `e/φe ≤ 3L` (`totient_ratio_le_log`).
  - **cross-X** (`∝ √(⌊X/e⌋)/√g`): via `hMlev : L^{A+5} ≤ √M` (the `√M`-side sibling of
    `hlev`, coupled at the same `A+5`; holds at the balanced operating point `M ≍ √x`).
  - **cross-M** (`∝ √M/√g`): via `hdiv : d(e)·C·L^{A+5} ≤ √X` — see the FLAG below.

## FLAG (CATCH #49 — the cross-M term needs a sub-`√e` divisor bound)

The exact fibered arithmetic surfaces an asymmetry the gate's four-term bookkeeping did not
foresee: the **dilation is on the α-side only** (`X ↦ ⌊X/e⌋`), so the β-cross (`cross-M`)
pairs the *shrunk* scale `√(⌊X/e⌋)` against the *full* `√M`, and the `∑_{g∣e}φg/√g` weight
must keep its divisor count `d(e)` uncollapsed:
```
cross-M / target  ≤  C·(log XM)^{A+5}·d(e)/√X.
```
With only the corpus bound `d(e) ≤ 2√e` (`card_divisors_le_two_sqrt`), `d(e)/√X` reduces to
`√e/√X` and the term closes **only for `A ≤ 1`** at the balanced operating point
`X ≍ M ≍ √x`, `e ≍ D ≍ √x/L^{A+5}` (there `√e ≍ √X`, so `√e/√X ≍ 1` and the leftover
`L^{A+5-(A+5)/2}=L^{(A+5)/2}` diverges — cf. CATCH #47's `A=1` boundary).  It **does** close
for all `A` once `d(e)` is treated by its true sub-polynomial size (`d(e) ≤ e^{o(1)} ≪ √X`),
which is a genuine strong-divisor bound *not in the landed corpus* (only `d(e) ≤ 2√e` is).

Rather than deviate from the frozen recipe (which would need re-gating), `efold_large_discharge`
carries this exact requirement as the **named, operating-point hypothesis `hdiv`**
(`d(e)·Kcross·L^{A+5} ≤ √X` for every `e` in range) — the coupled sibling of `hlev`/`hMlev`,
discharged by the H-glue via the divisor bound at the operating point.  All four thresholds
(`hlev`, `hD0lo`, `hMlev`, `hdiv`) are stated explicitly, no numeric values hardcoded.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 0. A totient/divisor sum helper (the cross-term `∑ φg/√g` weight) -/

/-- `∑_{g ∣ e} φ(g)/√g ≤ √e·d(e)`: each `φ(g)/√g ≤ √g ≤ √e`, over `d(e)` divisors.
The cross-term totient weight (companion to `sum_totient_div_self_le` for `∑φg/g ≤ d(e)`
and `sum_totient_divisors` for `∑φg = e`). -/
theorem sum_totient_div_sqrt_le (e : ℕ) (he : 1 ≤ e) :
    ∑ g ∈ e.divisors, (Nat.totient g : ℝ) / Real.sqrt (g : ℝ)
      ≤ Real.sqrt (e : ℝ) * (e.divisors.card : ℝ) := by
  have hsqrte : (0 : ℝ) ≤ Real.sqrt (e : ℝ) := Real.sqrt_nonneg _
  calc ∑ g ∈ e.divisors, (Nat.totient g : ℝ) / Real.sqrt (g : ℝ)
      ≤ ∑ _g ∈ e.divisors, Real.sqrt (e : ℝ) := by
        apply Finset.sum_le_sum
        intro g hg
        have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
        have hgdvd : g ∣ e := Nat.dvd_of_mem_divisors hg
        have hge : g ≤ e := Nat.le_of_dvd (by omega) hgdvd
        have hsg : (0 : ℝ) < Real.sqrt (g : ℝ) :=
          Real.sqrt_pos.mpr (by exact_mod_cast hgpos)
        -- φ(g)/√g ≤ √g ≤ √e
        have hφg : (Nat.totient g : ℝ) ≤ (g : ℝ) := by exact_mod_cast Nat.totient_le g
        have h1 : (Nat.totient g : ℝ) / Real.sqrt (g : ℝ) ≤ Real.sqrt (g : ℝ) := by
          rw [div_le_iff₀ hsg, Real.mul_self_sqrt (by exact_mod_cast hgpos.le)]
          exact hφg
        have h2 : Real.sqrt (g : ℝ) ≤ Real.sqrt (e : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hge)
        exact le_trans h1 h2
    _ = Real.sqrt (e : ℝ) * (e.divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ## 1. Floor A — the exact gcd/fibering reduction to the `δ = g` energy sums -/

open Classical in
/-- **Floor A (the sum-exchange, exact).**  The large-conductor density regroups by the
gcd identity and fibers over the common divisors `g ∣ e`:
```
∑_{D0<f≤D} (4/φ(lcm e f))·(1+log D)·E f
    ≤ (4(1+log D)/φe)·∑_{g ∣ e} φg·(∑_{D0<f≤D, g∣f} (1/φf)·E f).
```
Route: `4/φ(lcm e f) = 4φ(gcd e f)/(φe·φf)` (`totient_lcm_mul_totient_gcd`);
`φ(gcd e f) ≤ gcd e f` (`totient_le`); `gcd e f = ∑_{g∣gcd e f} φg` (`sum_totient_divisors`);
`(gcd e f).divisors = e.divisors.filter (·∣f)` (`dvd_gcd_iff`); then swap the `(f,g)` sums.
The inner `g`-sum is the `δ=g`-restricted energy sum that `dyadic_energy_le_dvd` prices. -/
theorem efold_large_fibered (α : ℕ → ℂ) (N X M D0 D e : ℕ) (he1 : 1 ≤ e) :
    ∑ f ∈ Finset.Icc (D0 + 1) D,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ (4 * (1 + Real.log D) / (e.totient : ℝ)) *
          ∑ g ∈ e.divisors, (g.totient : ℝ) *
            ∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => g ∣ f),
              (1 / (f.totient : ℝ)) *
                bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f := by
  classical
  set E : ℕ → ℝ := fun f =>
    bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f with hE
  have he0 : e ≠ 0 := by omega
  have hφe : (0 : ℝ) < (e.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < e)
  have h1logD : (0 : ℝ) ≤ 1 + Real.log D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · rw [hD, Nat.cast_zero, Real.log_zero]; norm_num
    · linarith [Real.log_nonneg (show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD)]
  -- Step 1: per-`f`, bound `4/φ(lcm e f)·(1+logD)·E f ≤ (4(1+logD)/φe)·gcd(e,f)·(1/φf)·E f`.
  have hstep1 : ∀ f ∈ Finset.Icc (D0 + 1) D,
      ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
        ≤ (4 * (1 + Real.log D) / (e.totient : ℝ))
            * ((Nat.gcd e f : ℝ) * ((1 / (f.totient : ℝ)) * E f)) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf1 : 1 ≤ f := by omega
    have hf0 : f ≠ 0 := by omega
    have hφf : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hgcdpos : 0 < Nat.gcd e f := Nat.gcd_pos_of_pos_left f (by omega)
    have hφgcd : (0 : ℝ) < ((Nat.gcd e f).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hgcdpos
    have hlcmpos : 0 < Nat.lcm e f := by
      have : Nat.lcm e f ≠ 0 := Nat.lcm_ne_zero he0 hf0
      omega
    have hφlcm : (0 : ℝ) < ((Nat.lcm e f).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hlcmpos
    have hEf : 0 ≤ E f := bilinPrimEnergy_nonneg _ _ _ _ _
    -- gcd identity: `4/φ(lcm) = 4·φ(gcd)/(φe·φf)`.
    have hlcmgcd : ((Nat.lcm e f).totient : ℝ) * ((Nat.gcd e f).totient : ℝ)
        = (e.totient : ℝ) * (f.totient : ℝ) := by
      exact_mod_cast totient_lcm_mul_totient_gcd e f
    have hdensity : (4 / ((Nat.lcm e f).totient : ℝ))
        = (4 / (e.totient : ℝ)) * (((Nat.gcd e f).totient : ℝ) / (f.totient : ℝ)) := by
      have hpos : (0 : ℝ) < (e.totient : ℝ) * (f.totient : ℝ) := by positivity
      rw [div_mul_div_comm, div_eq_div_iff hφlcm.ne' hpos.ne']
      linear_combination -4 * hlcmgcd
    -- φ(gcd) ≤ gcd
    have hφgcdle : ((Nat.gcd e f).totient : ℝ) ≤ (Nat.gcd e f : ℝ) := by
      exact_mod_cast Nat.totient_le (Nat.gcd e f)
    rw [hdensity]
    have hchain : ((4 / (e.totient : ℝ)) * (((Nat.gcd e f).totient : ℝ) / (f.totient : ℝ)))
          * (1 + Real.log D) * E f
        ≤ (4 * (1 + Real.log D) / (e.totient : ℝ))
            * ((Nat.gcd e f : ℝ) * ((1 / (f.totient : ℝ)) * E f)) := by
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
    exact hchain
  refine le_trans (Finset.sum_le_sum hstep1) ?_
  -- Step 2: pull out the `(4(1+logD)/φe)` factor and fiber `gcd = ∑_{g∣e, g∣f} φg`.
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- Now: `∑_f gcd(e,f)·((1/φf)·E f) = ∑_g φg·∑_{f:g∣f} (1/φf)·E f`.
  have hgcdsum : ∀ f ∈ Finset.Icc (D0 + 1) D,
      (Nat.gcd e f : ℝ) * ((1 / (f.totient : ℝ)) * E f)
        = ∑ g ∈ e.divisors,
            (if g ∣ f then (g.totient : ℝ) else 0) * ((1 / (f.totient : ℝ)) * E f) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    have hf0 : f ≠ 0 := by omega
    rw [← Finset.sum_mul]
    congr 1
    -- gcd(e,f) = ∑_{g ∈ e.divisors} if g ∣ f then φg else 0
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
      rw [← hdiv]
      rw [← Nat.cast_sum]
      exact_mod_cast (sum_totient_divisors (Nat.gcd e f)).symm
    rw [this, Finset.sum_filter]
  rw [Finset.sum_congr rfl hgcdsum]
  -- swap the (f, g) sums
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun g hg => ?_)
  -- per g: ∑_f (if g∣f then φg else 0)·w f = φg·∑_{f:g∣f} w f
  rw [Finset.sum_filter]
  refine le_of_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases hgf : g ∣ f
  · rw [if_pos hgf, if_pos hgf]
  · rw [if_neg hgf, if_neg hgf, zero_mul, mul_zero]

/-! ## 2. Floors A→B — the reduction to the four bounded terms -/

open Classical in
/-- **The four-term reduction.**  Composes `efold_large_fibered` (floor A) with
`dyadic_energy_le_dvd` per common divisor `g ∣ e` (at `δ = g`, scale `(⌊X/e⌋, M)`) and the
three totient sums (`sum_totient_div_self_le`, `sum_totient_div_sqrt_le`,
`sum_totient_divisors`), collapsing the `∑_{g∣e} φg·(per-g four term)` weight to the explicit
bounded four-term RHS.  `d(e) = e.divisors.card`, `xe = ⌊X/e⌋`. -/
theorem efold_large_reduce (α : ℕ → ℂ) (N X M D0 D e k0 K : ℕ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (he2 : 2 ≤ e) (hD1 : 1 ≤ D)
    (hD0pow : D0 = 2 ^ k0) (hK : K = Nat.log 2 D) (hMpos : 0 < M) :
    ∑ f ∈ Finset.Icc (D0 + 1) D,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ (4 * (1 + Real.log D) / (e.totient : ℝ)) *
          ((2 * (1 + Real.log M) * Real.sqrt ((X / e : ℕ) : ℝ) * Real.sqrt (M : ℝ)) *
            ( 4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (((X / e : ℕ) : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
            + Real.sqrt (13 * (((X / e : ℕ) : ℝ) + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) := by
  classical
  set E : ℕ → ℝ := fun f =>
    bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f with hE
  refine le_trans (efold_large_fibered α N X M D0 D e (by omega)) ?_
  have h1logD : (0 : ℝ) ≤ 1 + Real.log D :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD1)]
  have hφe : (0 : ℝ) < (e.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < e)
  have hPf : (0 : ℝ) ≤ 4 * (1 + Real.log D) / (e.totient : ℝ) := by
    apply div_nonneg (by linarith) hφe.le
  refine mul_le_mul_of_nonneg_left ?_ hPf
  -- abbreviations
  set xe : ℝ := ((X / e : ℕ) : ℝ) with hxe
  set C0 : ℝ := 2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ) with hC0
  have h1logM : (0 : ℝ) ≤ 1 + Real.log M := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
    linarith [Real.log_nonneg this]
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1logM) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  -- block-prime indicator bound + dilated α bound
  have hβ1 : ∀ n, ‖blockPrimeInd N n‖ ≤ 1 := by
    intro n; unfold blockPrimeInd
    by_cases h : N < n ∧ n.Prime
    · rw [if_pos h, norm_one]
    · rw [if_neg h, norm_zero]; norm_num
  have hdil : ∀ m', ‖(fun m' => α (e * m')) m'‖ ≤ 1 := fun m' => hα (e * m')
  -- per-g dyadic bound
  have hpg : ∀ g ∈ e.divisors,
      (g.totient : ℝ) *
          (∑ f ∈ (Finset.Icc (D0 + 1) D).filter (fun f => g ∣ f), (1 / (f.totient : ℝ)) * E f)
        ≤ (g.totient : ℝ) *
            (C0 * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) / Real.sqrt (g : ℝ)
              + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0))) := by
    intro g hg
    have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
    have hφg : (0 : ℝ) ≤ (g.totient : ℝ) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hφg
    exact dyadic_energy_le_dvd (X := X / e) (Y := M) (D0 := D0) (D := D) (δ := g)
      (k0 := k0) (K := K) hg1 hD0pow hK hMpos (fun m' => α (e * m')) (blockPrimeInd N) hdil hβ1
  refine le_trans (Finset.sum_le_sum hpg) ?_
  -- pull C0 out and split the bracket into four totient sums
  have hpullC0 :
      ∑ g ∈ e.divisors, (g.totient : ℝ) *
          (C0 * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) / Real.sqrt (g : ℝ)
            + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0)))
        = C0 * ∑ g ∈ e.divisors, (g.totient : ℝ) *
            (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
              + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) / Real.sqrt (g : ℝ)
              + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun g _ => by ring)
  rw [hpullC0]
  refine mul_le_mul_of_nonneg_left ?_ hC0nn
  -- split the bracket sum into four pieces
  have hsplit :
      ∑ g ∈ e.divisors, (g.totient : ℝ) *
          (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) / Real.sqrt (g : ℝ)
            + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0))
        = (∑ g ∈ e.divisors, (g.totient : ℝ) * (4 * (2 : ℝ) ^ (K + 1) / (g : ℝ)))
          + (∑ g ∈ e.divisors, (g.totient : ℝ) *
              (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1)) / Real.sqrt (g : ℝ)))
          + (∑ g ∈ e.divisors, (g.totient : ℝ) *
              (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) / Real.sqrt (g : ℝ)))
          + (∑ g ∈ e.divisors, (g.totient : ℝ) *
              (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                  * (2 / (2 : ℝ) ^ k0))) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  -- bound each of the four totient sums
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
        (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) / Real.sqrt (g : ℝ))
      ≤ 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
          * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) := by
    have heq : ∑ g ∈ e.divisors, (g.totient : ℝ) *
          (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) / Real.sqrt (g : ℝ))
        = 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
            * ∑ g ∈ e.divisors, (g.totient : ℝ) / Real.sqrt (g : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun g _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left (sum_totient_div_sqrt_le e (by omega)) (by positivity)
  have ht4 : ∑ g ∈ e.divisors, (g.totient : ℝ) *
        (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1)) * (2 / (2 : ℝ) ^ k0))
      = Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
          * (2 / (2 : ℝ) ^ k0) * (e : ℝ) := by
    have hsum : ∑ g ∈ e.divisors, (g.totient : ℝ) = (e : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast sum_totient_divisors e
    rw [← Finset.sum_mul, hsum]; ring
  rw [ht4]
  have hcombine := add_le_add (add_le_add ht1 ht2) ht3
  linarith [hcombine]

/-! ## 3. FULL — the `hlarge` discharge (`efold_large_discharge`) -/

set_option maxHeartbeats 1600000 in
-- The four-term threshold assembly (~30 shared facts + 4 nested `calc`s with `gcongr`/`ring`
-- over large sqrt/rpow expressions) exceeds the 200000-heartbeat default during elaboration.
open Classical in
/-- **PE3c-4 (FULL) — the `hlarge` slot, discharged.**  The large-conductor contribution
meets the target envelope `Klarge·(XM/L^{A+1})·(1/e)` (`Klarge = 15360`, `L = log(XM)`) under
the four coupled operating-point thresholds:
* `hlev  : D·L^{A+5} ≤ √(XM)`      — closes the **main** diagonal `D·√(XM)`;
* `hD0lo : L^{A+4} ≤ D0`            — closes the **tail** `√(XM)/D0`;
* `hMlev : L^{A+5} ≤ √M`           — closes **cross-X** (`X·√M = XM/√M`);
* `hdiv  : d(e)·L^{A+5} ≤ √X`      — closes **cross-M** (`M·√X·d(e)`); see the module FLAG.

Route: `efold_large_reduce` (the fibered four bounded terms) + the term-wise threshold
bookkeeping (`(1+log D), (1+log M), (K+1) ≤ 2L`, `e/φe ≤ 3L`, `d(e) ≤ 2√e`, the α-scale
pairing `√⌊X/e⌋·√(13(⌊X/e⌋+1)) ≤ 6(X/e)` and `√M·√(13(M+1)) ≤ 6M`, `√⌊X/e⌋·√e ≤ √X`). -/
theorem efold_large_discharge (α : ℕ → ℂ) (N X M D0 D e k0 K : ℕ) {A : ℝ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (he2 : 2 ≤ e) (heD : e ≤ D)
    (hD0pow : D0 = 2 ^ k0) (hK : K = Nat.log 2 D) (hMpos : 0 < M) (hXpos : 0 < X)
    (hA : 0 ≤ A) (hD1 : 1 ≤ D) (hL1 : 1 ≤ Real.log ((X : ℝ) * (M : ℝ)))
    (hlev : (D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)))
    (hD0lo : (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ))
    (hMlev : (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ))
    (hdiv : (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ)) :
    ∑ f ∈ Finset.Icc (D0 + 1) D,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ 15360 * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
  refine le_trans (efold_large_reduce α N X M D0 D e k0 K hα he2 hD1 hD0pow hK hMpos) ?_
  -- abbreviations (only `L` and `xe`; other casts stay raw to match external lemmas)
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  set xe : ℝ := ((X / e : ℕ) : ℝ) with hxedef
  have hLpos : 0 < L := by linarith
  have hXr1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
  have hMr1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
  have herpos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hφinv : (0 : ℝ) < (e.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < e)
  have hxenn : (0 : ℝ) ≤ xe := by rw [hxedef]; positivity
  have hXMpos : 0 < (X : ℝ) * (M : ℝ) := by positivity
  have hXMnn : (0 : ℝ) ≤ (X : ℝ) * (M : ℝ) := hXMpos.le
  have hXM1 : (1 : ℝ) ≤ (X : ℝ) * (M : ℝ) := by nlinarith [hXr1, hMr1]
  have hsqXM : Real.sqrt ((X : ℝ) * (M : ℝ)) = Real.sqrt (X : ℝ) * Real.sqrt (M : ℝ) :=
    Real.sqrt_mul (by linarith) _
  have hsqXMsq :
      Real.sqrt ((X : ℝ) * (M : ℝ)) * Real.sqrt ((X : ℝ) * (M : ℝ)) = (X : ℝ) * (M : ℝ) :=
    Real.mul_self_sqrt hXMnn
  have hMsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (by linarith)
  have hXsq : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := Real.mul_self_sqrt (by linarith)
  have h1sqXM : (1 : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt hXM1
  have hsqle : Real.sqrt ((X : ℝ) * (M : ℝ)) ≤ (X : ℝ) * (M : ℝ) := by nlinarith [hsqXMsq, h1sqXM]
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
  -- D ≤ √(XM), D·√(XM) ≤ XM/L^{A+5}
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDsqrtXM : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) := by
    calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D : ℝ) * L ^ (A + 5) := by apply mul_le_mul_of_nonneg_left hL1ge hDpos.le
      _ ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) := hlev
  have hDXM : (D : ℝ) ≤ (X : ℝ) * (M : ℝ) := le_trans hDsqrtXM hsqle
  have hDsqdiv : (D : ℝ) * Real.sqrt ((X : ℝ) * (M : ℝ)) ≤ (X : ℝ) * (M : ℝ) / L ^ (A + 5) := by
    rw [le_div_iff₀ hL5]
    calc (D : ℝ) * Real.sqrt ((X : ℝ) * (M : ℝ)) * L ^ (A + 5)
        = ((D : ℝ) * L ^ (A + 5)) * Real.sqrt ((X : ℝ) * (M : ℝ)) := by ring
      _ ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) * Real.sqrt ((X : ℝ) * (M : ℝ)) :=
          mul_le_mul_of_nonneg_right hlev (Real.sqrt_nonneg _)
      _ = (X : ℝ) * (M : ℝ) := hsqXMsq
  -- log bounds
  have hlogD2 : 1 + Real.log D ≤ 2 * L := by
    have : Real.log D ≤ L := by rw [hLdef]; exact Real.log_le_log hDpos hDXM
    linarith
  have hlogM2 : 1 + Real.log M ≤ 2 * L := by
    have hMXM : (M : ℝ) ≤ (X : ℝ) * (M : ℝ) := le_mul_of_one_le_left (by linarith) hXr1
    have : Real.log M ≤ L := by rw [hLdef]; exact Real.log_le_log (by linarith) hMXM
    linarith
  -- (K+1) ≤ 2L
  have h2K : (2 : ℝ) ^ K ≤ (D : ℝ) := by
    have := Nat.pow_log_le_self 2 (show D ≠ 0 by omega)
    rw [← hK] at this; exact_mod_cast this
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hlog2K : (K : ℝ) * Real.log 2 ≤ L / 2 := by
    have h := Real.log_le_log (by positivity) (le_trans h2K hDsqrtXM)
    rw [Real.log_pow, Real.log_sqrt hXMnn, ← hLdef] at h; linarith
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
        exact le_trans (by exact_mod_cast heD) hDXM
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
  have hPM : Real.sqrt (M : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)) ≤ 6 * (M : ℝ) := by
    rw [← Real.sqrt_mul (by linarith)]
    calc Real.sqrt ((M : ℝ) * (13 * ((M : ℝ) + 1))) ≤ Real.sqrt ((6 * (M : ℝ)) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith [hMr1]
      _ = 6 * (M : ℝ) := Real.sqrt_sq (by positivity)
  -- threshold conversions to XM/L^{A+5}
  have hXsqMdiv : (X : ℝ) * Real.sqrt (M : ℝ) ≤ (X : ℝ) * (M : ℝ) / L ^ (A + 5) := by
    rw [le_div_iff₀ hL5]
    calc (X : ℝ) * Real.sqrt (M : ℝ) * L ^ (A + 5) = (X : ℝ) * (Real.sqrt (M : ℝ) * L ^ (A + 5))
        := by ring
      _ ≤ (X : ℝ) * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hMlev (Real.sqrt_nonneg _)
      _ = (X : ℝ) * (M : ℝ) := by rw [hMsq]
  have hMXddiv : (M : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)
      ≤ (X : ℝ) * (M : ℝ) / L ^ (A + 5) := by
    rw [le_div_iff₀ hL5]
    calc (M : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ) * L ^ (A + 5)
        = (M : ℝ) * Real.sqrt (X : ℝ) * ((e.divisors.card : ℝ) * L ^ (A + 5)) := by ring
      _ ≤ (M : ℝ) * Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) := by
          apply mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (X : ℝ) * (M : ℝ) := by rw [mul_assoc, hXsq]; ring
  -- 1/D0 ≤ 1/L^{A+4}
  have hD0inv : (1 : ℝ) / (D0 : ℝ) ≤ 1 / L ^ (A + 4) := one_div_le_one_div_of_le hL4p hD0lo
  -- distribute the reduction RHS into the four pieces
  have hlogDnn : (0 : ℝ) ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD1)
  have hAnn : (0 : ℝ) ≤ 4 * (1 + Real.log D) / (e.totient : ℝ) := by
    apply div_nonneg (by linarith) hφinv.le
  set A0 : ℝ := 4 * (1 + Real.log D) / (e.totient : ℝ) with hA0
  set G : ℝ := (X : ℝ) * (M : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)) with hG
  have hGnn : (0 : ℝ) ≤ G := by rw [hG]; positivity
  -- MAIN term
  have hTmain : A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
        * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ))) ≤ 1536 * G := by
    have hMainSqrt : Real.sqrt xe * Real.sqrt (M : ℝ) * (e.divisors.card : ℝ)
        ≤ 2 * Real.sqrt ((X : ℝ) * (M : ℝ)) := by
      calc Real.sqrt xe * Real.sqrt (M : ℝ) * (e.divisors.card : ℝ)
          ≤ Real.sqrt xe * Real.sqrt (M : ℝ) * (2 * Real.sqrt (e : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hd2; positivity
        _ = 2 * (Real.sqrt xe * Real.sqrt (e : ℝ)) * Real.sqrt (M : ℝ) := by ring
        _ ≤ 2 * Real.sqrt (X : ℝ) * Real.sqrt (M : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            apply mul_le_mul_of_nonneg_left hS2; norm_num
        _ = 2 * Real.sqrt ((X : ℝ) * (M : ℝ)) := by rw [hsqXM]; ring
    calc A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)))
        = A0 * (2 * (1 + Real.log M)) * (4 * (2 : ℝ) ^ (K + 1))
            * (Real.sqrt xe * Real.sqrt (M : ℝ) * (e.divisors.card : ℝ)) := by ring
      _ ≤ A0 * (2 * (1 + Real.log M)) * (4 * (2 * (D : ℝ)))
            * (2 * Real.sqrt ((X : ℝ) * (M : ℝ))) := by
          gcongr
      _ = 128 * (1 + Real.log D) * (1 + Real.log M) * ((D : ℝ) * Real.sqrt ((X : ℝ) * (M : ℝ)))
            * (1 / (e.totient : ℝ)) := by rw [hA0]; ring
      _ ≤ 128 * (2 * L) * (2 * L) * ((X : ℝ) * (M : ℝ) / L ^ (A + 5)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 1536 * (L * L * L) * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 5) * (e : ℝ)) := by ring
      _ ≤ 1536 * G := by
          rw [hG, show 1536 * ((X : ℝ) * (M : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 1536 * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 1536 * (L * L * L) * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (1536 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * ((L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (1536 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * L ^ (A + 5) :=
                mul_le_mul_of_nonneg_left hmain_pow (by positivity)
            _ = 1536 * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 5) * (e : ℝ)) := by ring
  -- CROSS-X term
  have hTcrossX : A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
        * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)))) ≤ 4608 * G := by
    have hGX : Real.sqrt xe * Real.sqrt (13 * (xe + 1))
          * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) * Real.sqrt (M : ℝ)
        ≤ 12 * ((X : ℝ) * Real.sqrt (M : ℝ)) := by
      calc Real.sqrt xe * Real.sqrt (13 * (xe + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) * Real.sqrt (M : ℝ)
          ≤ (6 * ((X : ℝ) / (e : ℝ))) * (2 * (e : ℝ)) * Real.sqrt (M : ℝ) := by
            gcongr
        _ = 12 * ((X : ℝ) * Real.sqrt (M : ℝ)) := by field_simp; ring
    calc A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        = A0 * (2 * (1 + Real.log M)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (Real.sqrt xe * Real.sqrt (13 * (xe + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)) * Real.sqrt (M : ℝ)) := by ring
      _ ≤ A0 * (2 * (1 + Real.log M)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (12 * ((X : ℝ) * Real.sqrt (M : ℝ))) := by gcongr
      _ = 192 * (1 + Real.log D) * (1 + Real.log M) * ((K + 1 : ℕ) : ℝ)
            * ((X : ℝ) * Real.sqrt (M : ℝ)) * (1 / (e.totient : ℝ)) := by rw [hA0]; ring
      _ ≤ 192 * (2 * L) * (2 * L) * (2 * L)
            * ((X : ℝ) * (M : ℝ) / L ^ (A + 5)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 4608 * (L * L * L * L) * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 5) * (e : ℝ)) := by ring
      _ ≤ 4608 * G := by
          rw [hG, show 4608 * ((X : ℝ) * (M : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 4608 * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 4608 * (L * L * L * L) * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (4608 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * ((L * L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (4608 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * L ^ (A + 5) :=
                mul_le_mul_of_nonneg_left (le_of_eq hcross_eq) (by positivity)
            _ = 4608 * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 5) * (e : ℝ)) := by ring
  -- CROSS-M term
  have hTcrossM : A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
        * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ)))) ≤ 2304 * G := by
    have hGM : Real.sqrt xe * Real.sqrt (M : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
          * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
        ≤ 6 * ((M : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)) := by
      calc Real.sqrt xe * Real.sqrt (M : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
            * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
          = (Real.sqrt xe * Real.sqrt (e : ℝ))
              * (Real.sqrt (M : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)))
              * (e.divisors.card : ℝ) := by ring
        _ ≤ Real.sqrt (X : ℝ) * (6 * (M : ℝ)) * (e.divisors.card : ℝ) := by
            gcongr
        _ = 6 * ((M : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)) := by ring
    calc A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        = A0 * (2 * (1 + Real.log M)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (Real.sqrt xe * Real.sqrt (M : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))) := by ring
      _ ≤ A0 * (2 * (1 + Real.log M)) * (2 * ((K + 1 : ℕ) : ℝ))
            * (6 * ((M : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ))) := by gcongr
      _ = 96 * (1 + Real.log D) * (1 + Real.log M) * ((K + 1 : ℕ) : ℝ)
            * ((M : ℝ) * Real.sqrt (X : ℝ) * (e.divisors.card : ℝ)) * (1 / (e.totient : ℝ)) := by
          rw [hA0]; ring
      _ ≤ 96 * (2 * L) * (2 * L) * (2 * L)
            * ((X : ℝ) * (M : ℝ) / L ^ (A + 5)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 2304 * (L * L * L * L) * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 5) * (e : ℝ)) := by ring
      _ ≤ 2304 * G := by
          rw [hG, show 2304 * ((X : ℝ) * (M : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 2304 * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 2304 * (L * L * L * L) * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (2304 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * ((L * L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (2304 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * L ^ (A + 5) :=
                mul_le_mul_of_nonneg_left (le_of_eq hcross_eq) (by positivity)
            _ = 2304 * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 5) * (e : ℝ)) := by ring
  -- TAIL term
  have hTtail : A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
        * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
            * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) ≤ 6912 * G := by
    have hD0R : (D0 : ℝ) = (2 : ℝ) ^ k0 := by rw [hD0pow]; push_cast; ring
    have hGT : Real.sqrt xe * Real.sqrt (M : ℝ)
          * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
              * (2 / (2 : ℝ) ^ k0) * (e : ℝ))
        ≤ 72 * ((X : ℝ) * (M : ℝ)) * (1 / (D0 : ℝ)) := by
      have hD0pos : (0 : ℝ) < (D0 : ℝ) := by rw [hD0R]; positivity
      calc Real.sqrt xe * Real.sqrt (M : ℝ)
            * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ))
          = (Real.sqrt xe * Real.sqrt (13 * (xe + 1)))
              * (Real.sqrt (M : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1)))
              * (2 / (2 : ℝ) ^ k0) * (e : ℝ) := by ring
        _ ≤ (6 * ((X : ℝ) / (e : ℝ))) * (6 * (M : ℝ)) * (2 / (2 : ℝ) ^ k0) * (e : ℝ) := by
            gcongr
        _ = 72 * ((X : ℝ) * (M : ℝ)) * (1 / (D0 : ℝ)) := by rw [hD0R]; field_simp; ring
    calc A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ)))
        = A0 * (2 * (1 + Real.log M))
            * (Real.sqrt xe * Real.sqrt (M : ℝ)
                * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                    * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) := by ring
      _ ≤ A0 * (2 * (1 + Real.log M)) * (72 * ((X : ℝ) * (M : ℝ)) * (1 / (D0 : ℝ))) := by gcongr
      _ = 576 * (1 + Real.log D) * (1 + Real.log M) * ((X : ℝ) * (M : ℝ))
            * (1 / (D0 : ℝ)) * (1 / (e.totient : ℝ)) := by rw [hA0]; ring
      _ ≤ 576 * (2 * L) * (2 * L) * ((X : ℝ) * (M : ℝ))
            * (1 / L ^ (A + 4)) * (3 * L / (e : ℝ)) := by
          gcongr
      _ = 6912 * (L * L * L) * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 4) * (e : ℝ)) := by ring
      _ ≤ 6912 * G := by
          rw [hG, show 6912 * ((X : ℝ) * (M : ℝ) / L ^ (A + 1) * (1 / (e : ℝ)))
                = 6912 * ((X : ℝ) * (M : ℝ)) / (L ^ (A + 1) * (e : ℝ)) by ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
          calc 6912 * (L * L * L) * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 1) * (e : ℝ))
              = (6912 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * ((L * L * L) * L ^ (A + 1)) := by ring
            _ ≤ (6912 * ((X : ℝ) * (M : ℝ)) * (e : ℝ)) * L ^ (A + 4) :=
                mul_le_mul_of_nonneg_left (le_of_eq hmain_eq) (by positivity)
            _ = 6912 * ((X : ℝ) * (M : ℝ)) * (L ^ (A + 4) * (e : ℝ)) := by ring
  -- combine the four terms
  calc A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
        * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)
          + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
              * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
          + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
              * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))
          + Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
              * (2 / (2 : ℝ) ^ k0) * (e : ℝ)))
      = A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (4 * (2 : ℝ) ^ (K + 1) * (e.divisors.card : ℝ)))
        + A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (xe + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        + A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (Real.sqrt (e : ℝ) * (e.divisors.card : ℝ))))
        + A0 * ((2 * (1 + Real.log M) * Real.sqrt xe * Real.sqrt (M : ℝ))
            * (Real.sqrt (13 * (xe + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0) * (e : ℝ))) := by
        ring
    _ ≤ 1536 * G + 4608 * G + 2304 * G + 6912 * G :=
        add_le_add (add_le_add (add_le_add hTmain hTcrossX) hTcrossM) hTtail
    _ = 15360 * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)) * (1 / (e : ℝ)) := by rw [hG]; ring

/-! ## 4. THE COMPLETED KEYSTONE 2 — general BV with the per-`e` slot fully discharged -/

open Classical in
/-- **PE3c-4 (FULL) — `general_BV_alpha_final`: KEYSTONE 2, no per-`e` slot, no `hlarge`.**
`general_BV_alpha_discharged` with the flagged large-conductor core `hlarge` FILLED by
`efold_large_discharge` (`Klarge = 15360`), at the gate's coupled operating point `C0 = A + 5`.
The remaining inputs are the small-conductor core `hsmall` (discharged for all `e` by
`efold_small_discharge` upstream) and the four explicit operating-point thresholds
`hlev`/`hD0lo`/`hMlev`/`hdiv` (the H-glue supplies them; see the module FLAG for `hdiv`).
This is the general bilinear-BV `L¹`-over-`d` AP-discrepancy bound for the interval-prime
indicator with **no analytic slot remaining** — the last analytic estimate of the Chen arc. -/
theorem general_BV_alpha_final {A : ℝ} (hA : 0 < A) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M R₀ D0 D k0 Kdy : ℕ) (Dset : Finset ℕ) (Kβ Kmain Ksmall : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 3 ≤ N → N₀ ≤ N → N ≤ M → M ≤ 2 * N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime R₀ d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)) →
        ((D0 : ℝ) ≤ (Real.log N) ^ (A + 5)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2 * (A + 5))
            ≤ Kβ * (Real.log N) ^ (A + 2 * (A + 5))) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < N → 2 ≤ D0 → D0 ≤ D →
        0 ≤ Ksmall → (1 : ℝ) ≤ (X : ℝ) * (M : ℝ) →
        -- the operating-point choices + thresholds discharging `hlarge`
        D0 = 2 ^ k0 → Kdy = Nat.log 2 D →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
            ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D →
            (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
              ≤ Real.sqrt (X : ℝ)) →
        (4 * (1 + Real.log D) *
            ∑ f ∈ Finset.Icc 2 D,
              (1 / (f.totient : ℝ)) * bilinPrimEnergy α (blockPrimeInd N) X M f
          ≤ Kmain * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        (∀ e, 2 ≤ e → e ≤ D →
            ∑ f ∈ Finset.Icc 2 D0,
                ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
                  * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
              ≤ Ksmall * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1))
                  * (1 / (e : ℝ))) →
        ∑ d ∈ Dset, ‖apDiscBilin α (blockPrimeInd N) X M R₀ d‖
          ≤ (Kβ + (Kmain + (Ksmall + 15360))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_alpha_discharged (A := A) (C0 := A + 5) hA (by linarith)
  refine ⟨K, N₀, hK0, fun α X N M R₀ D0 D k0 Kdy Dset Kβ Kmain Ksmall hα hKβ hN3 hN hNM hM2N
    hDge1 hcop hLpos hL1 hD0 hD0N hscale hD1 hDsetD hDN h2D0 hD0D hKs hXM1 hD0pow hKeq
    hlev hD0lo hMlev hdiv hMainEnergy hsmall => ?_⟩
  have hMpos : 0 < M := by omega
  have hXpos : 0 < X := by
    rcases Nat.eq_zero_or_pos X with hX0 | hX0
    · exfalso; rw [hX0, Nat.cast_zero, zero_mul] at hXM1; linarith
    · exact hX0
  refine hbody α X N M R₀ D0 D Dset Kβ Kmain Ksmall 15360 hα hKβ hN3 hN hNM hM2N hDge1 hcop
    hLpos hD0 hD0N hscale hD1 hDsetD hDN h2D0 hD0D hKs (by norm_num) hXM1 hMainEnergy hsmall ?_
  intro e he2 heD
  exact efold_large_discharge α N X M D0 D e k0 Kdy hα he2 heD hD0pow hKeq hMpos hXpos
    hA.le hD1 hL1 hlev hD0lo hMlev (hdiv e he2 heD)

-- Composition sanity (SW3 switch line): `general_BV_alpha_final` is the completed KEYSTONE 2,
-- filling the per-`e`/`hlarge` slot that `SwitchBV.hBVswitch_of_generalBV` ultimately depends on
-- (through `SwitchPricing.box_price_of_apDiscBilin` → `general_BV_final'` / this discharge).
-- `#check @Salt.Chen.general_BV_alpha_final` and `#check @Salt.Chen.hBVswitch_of_generalBV`
-- both elaborate; the apDiscBilin `L¹`-over-`d` bound produced here is exactly the per-box
-- price that switch line consumes.

end Salt.Chen
