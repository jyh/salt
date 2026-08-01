/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE FLAT (3.11) STEP INEQUALITY (freeze item F-4)

The landed `step_ineq_3_11` (`Step.lean`) carries the shift error in the slot
`1/(4·log H·logloglog H)`; the flat road carries `1/(4·A·log H)`.  FLAT-REF's
census found the third log SEMANTIC on exactly two lines of the landed pair
(`condEntropy_shift_le`, `step_ineq_3_11`): positivity, and the single import of
`budget_real`.  Everything else is opaque carriage.  So this file is the LEAF
REWIRE the freeze names — `budget_real`'s and `condEntropy_shift_le`'s flat twins
(both landed originals have ZERO external consumers of their denominators
outside this cone), plus the assembled flat (3.11).

## The Fannes face, honestly

The flat budget `(3/2)·H·log2/L² + log 2 ≤ H/(4·A·L)` is SUFFICIENT under
`12·A·log 2 ≤ L` (FLAT-REF probe F2) — and that hypothesis is DOMINATED by the
flat design law: `λ₋ ≥ 3.2·A` gives `L₋ = e^{λ₋} ≥ e^{3A} ≥ 12·A·log 2` for every
`A ≥ 1` (probe F3, landed as `flat_fannes_dominated`).  The face never binds.

## The step-to-drop exchange

At the flat multiplier `m = ⌊2·A·L⌋₊` the two error terms fit inside the flat
per-step drop `1/(2·A·L)`: `flat_hkey` (`TowerFlat.lean`) plus the halving.
That is `DecrementFlat.lean`'s business; here the error slot is merely carried.

Everything is ADDITIVE: `Step.lean` and `InvarianceHead.lean` are untouched, and
the budget-parametric Fannes bridge `condEntropy_shift_le_of_l1_gen` is the
landed `condEntropy_shift_le_of_l1`'s proof with its budget slot opened (the
landed proof closes with `linarith [hred, hdiff, hbudget]` — the slot is already
opaque there).
-/
import Salt.Entropy.Chowla.Step
import Salt.Entropy.Chowla.TowerFlatRegime

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### Section 1 — the flat Fannes budget -/

private lemma flat_log_le_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 2 := by
  have hsqrt : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hls : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht.le
  have hle : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hsqrt
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  nlinarith [sq_nonneg (Real.sqrt t - 2), hls, hle, hsq]

/-- `(log t)² ≤ t` for `t ≥ 1` (two applications of `log s ≤ s/2`, one per level). -/
theorem flat_log_sq_le {t : ℝ} (ht : 1 ≤ t) : (Real.log t) ^ 2 ≤ t := by
  have htpos : (0 : ℝ) < t := by linarith
  have hspos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hls : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt htpos.le
  have hhalf : Real.log (Real.sqrt t) ≤ Real.sqrt t / 2 := flat_log_le_half hspos
  have hlog_le : Real.log t ≤ Real.sqrt t := by rw [hls] at hhalf; linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt htpos.le
  nlinarith [hlog_le, hlog_nn, hsq, Real.sqrt_nonneg t]

/-- **THE FLAT FANNES BUDGET, abstract reals** (FLAT-REF probe F2).  The
    sufficiency direction: at `12·A·log 2 ≤ L` and `L² ≤ H` the joint-support
    budget fits the flat shift slot `H/(4·A·L)`. -/
theorem flat_budget_real {H L A : ℝ} (hL : 0 < L) (hApos : 0 < A)
    (hLH : L ^ 2 ≤ H) (hkey : 12 * A * Real.log 2 ≤ L) :
    (3 / 2) * H * Real.log 2 / L ^ 2 + Real.log 2 ≤ H / (4 * A * L) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hH : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hLH
  have hAL : (0 : ℝ) < A * L := mul_pos hApos hL
  have h1 : (3 / 2) * H * Real.log 2 / L ^ 2 ≤ H / (8 * (A * L)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ H * L), hH, hL]
  have h2 : Real.log 2 ≤ H / (8 * (A * L)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hLH, mul_le_mul_of_nonneg_right hkey hL.le, hL, hl2, hApos]
  have h3 : H / (8 * (A * L)) + H / (8 * (A * L)) = H / (4 * A * L) := by
    field_simp; ring
  linarith

/-- **`budget_real`'s FLAT TWIN.**  The landed `budget_real` reads its
    denominator's value at `logloglog H`; the flat twin reads it at the design
    constant `A`, under the Fannes ceiling `12·A·log 2 ≤ log H` (which the design
    law supplies free — `fannes_ceiling_of_design`). -/
theorem budget_realFlat {A : ℝ} (hApos : 0 < A) {H : ℕ} (hH : 4000000 ≤ H)
    (hkey : 12 * A * Real.log 2 ≤ Real.log H) :
    (3 / 2) * (H : ℝ) * Real.log 2 / (Real.log H) ^ 2 + Real.log 2
      ≤ (H : ℝ) / (4 * A * Real.log H) := by
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH : (15 : ℝ) ≤ Real.log (H : ℝ) := (tower_log_bounds hH).1
  have hLpos : (0 : ℝ) < Real.log (H : ℝ) := by linarith
  have hLH : (Real.log (H : ℝ)) ^ 2 ≤ (H : ℝ) := flat_log_sq_le (by linarith)
  exact flat_budget_real hLpos hApos hLH hkey

/-! ### Section 2 — the budget-parametric Fannes bridge -/

/-- **The Fannes bridge with its budget slot OPEN.**  Byte-for-byte the landed
    `condEntropy_shift_le_of_l1`, with the budget value `B` a parameter (the
    landed proof already treats it opaquely: it closes with
    `linarith [hred, hdiff, hbudget]`).  This is what lets the flat twin reuse
    the landed Fannes machinery without touching it. -/
theorem condEntropy_shift_le_of_l1_gen (R : ChowlaRegime) (H j : ℕ) (d B : ℝ)
    (hd : d = ∑ s ∈ jointSupport R.eps H,
      |(((logMeasure R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)).real {s}
        - ((logMeasure R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
    (hd1 : d ≤ Real.exp (-1))
    (hbudget : d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d ≤ B) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω] + B := by
  set μ := logMeasure R.x R.ω with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_logMeasure R.hx R.hω
  haveI : IsProbabilityMeasure (μ.map (fun n => n + j * H)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  set ν' := μ.map (jointWindow R.eps H 0) with hν'
  set μ' := (μ.map (fun n => n + j * H)).map (jointWindow R.eps H 0) with hμ'
  haveI : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map (measurable_jointWindow R.eps H 0).aemeasurable
  haveI : IsProbabilityMeasure μ' :=
    Measure.isProbabilityMeasure_map (measurable_jointWindow R.eps H 0).aemeasurable
  have hν'null : ν' ((jointSupport R.eps H : Set _))ᶜ = 0 := by
    rw [hν', Measure.map_apply (measurable_jointWindow R.eps H 0) (Finset.measurableSet _).compl]
    convert measure_empty (μ := μ)
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun n hn => hn (jointWindow_mem_jointSupport R.eps H 0 n)
  have hμ'null : μ' ((jointSupport R.eps H : Set _))ᶜ = 0 := by
    rw [hμ', Measure.map_apply (measurable_jointWindow R.eps H 0) (Finset.measurableSet _).compl,
      Measure.map_apply (measurable_of_countable _)
        ((measurable_jointWindow R.eps H 0) (Finset.measurableSet _).compl)]
    convert measure_empty (μ := μ)
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun n hn => hn (jointWindow_mem_jointSupport R.eps H 0 (n + j * H))
  have hfannes := entropy_sub_le_of_l1 μ' ν' (jointSupport R.eps H) hμ'null hν'null d hd hd1
  have hdiff : Hm[μ'] - Hm[ν'] ≤
      d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d :=
    (le_abs_self _).trans hfannes
  have hred := condEntropy_shift_reduction R H j
  rw [← hμ] at hred
  rw [← hμ', ← hν'] at hred
  linarith [hred, hdiff, hbudget]

/-! ### Section 3 — the flat D-d headline -/

/-- **`condEntropy_shift_le`'s FLAT TWIN.**  Identical to the landed headline in
    every binder; the per-shift conditional-entropy gap is charged to the FLAT
    Fannes slot `H/(4·A·log H)`.  The `ℓ¹` half (`joint_l1_le`, `hheadroom'`) and
    the joint-support half (`log_jointSupport_card_le`) are the LANDED ones,
    reached through `R.toChowlaRegime`. -/
theorem condEntropy_shift_leFlat (R : ChowlaRegimeFlat) {H k j : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (hj : j < k) (_ha : R.a ∣ H) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
        + (H : ℝ) / (4 * R.A * Real.log H) := by
  set d : ℝ := ∑ s ∈ jointSupport R.eps H,
      |(((logMeasure R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)).real {s}
        - ((logMeasure R.x R.ω).map (jointWindow R.eps H 0)).real {s}| with hd_def
  have hd0 : 0 ≤ d := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hjl1 : d ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by
    rw [hd_def]; exact joint_l1_le R.toChowlaRegime H j
  have hk1 : 1 ≤ k := by omega
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHpos : 0 < H := by omega
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHfloor
  have hjHle : j * H ≤ R.Hhi := by
    have hle : j * H ≤ k * H := by gcongr
    omega
  have hHhile : H ≤ R.Hhi := by
    have hle : H ≤ k * H := by
      calc H = 1 * H := (one_mul H).symm
        _ ≤ k * H := by gcongr
    omega
  have hHhipos : 0 < R.Hhi := by omega
  have hxR : (0 : ℝ) < R.x := by exact_mod_cast (show 0 < R.x from by have := R.hx; omega)
  have hωR : (0 : ℝ) < R.ω := by exact_mod_cast (show 0 < R.ω from by have := R.hω; omega)
  have hlogH : (0 : ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hlogHhi : (0 : ℝ) < Real.log R.Hhi :=
    Real.log_pos (by exact_mod_cast (show 1 < R.Hhi by omega))
  have hlogle : Real.log H ≤ Real.log R.Hhi :=
    Real.log_le_log (by exact_mod_cast hHpos) (by exact_mod_cast hHhile)
  -- `d ≤ 1/(log H)²` (the landed `hheadroom'` route, verbatim)
  have hd_small : d ≤ 1 / (Real.log H) ^ 2 := by
    have h1 : d ≤ 8 * (R.Hhi : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by
      refine le_trans hjl1 ?_
      gcongr
    have hkey : 8 * (R.Hhi : ℝ) * (Real.log R.Hhi) ^ 2 ≤ (R.x : ℝ) / (R.ω : ℝ) := by
      have hhr := R.hheadroom'
      have hdivle : ((R.x / R.ω : ℕ) : ℝ) ≤ (R.x : ℝ) / (R.ω : ℝ) := Nat.cast_div_le
      calc 8 * (R.Hhi : ℝ) * (Real.log R.Hhi) ^ 2
          = 8 * (R.Hhi : ℝ) * Real.log R.Hhi * Real.log R.Hhi := by ring
        _ ≤ ((R.x / R.ω : ℕ) : ℝ) := hhr
        _ ≤ (R.x : ℝ) / (R.ω : ℝ) := hdivle
    have h2 : 8 * (R.Hhi : ℝ) * (R.ω : ℝ) / (R.x : ℝ) ≤ 1 / (Real.log R.Hhi) ^ 2 := by
      rw [div_le_div_iff₀ hxR (pow_pos hlogHhi 2)]
      have hm := mul_le_mul_of_nonneg_right hkey hωR.le
      have hxω : (R.x : ℝ) / (R.ω : ℝ) * (R.ω : ℝ) = (R.x : ℝ) := by field_simp
      rw [hxω] at hm
      nlinarith [hm]
    have hsqle : (Real.log H) ^ 2 ≤ (Real.log R.Hhi) ^ 2 := by nlinarith [hlogle, hlogH]
    have h3 : 1 / (Real.log R.Hhi) ^ 2 ≤ 1 / (Real.log H) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos hlogH 2) hsqle
    linarith [h1, h2, h3]
  -- `d ≤ e⁻¹`
  have hd1 : d ≤ Real.exp (-1) := by
    have hlogH2 : (2 : ℝ) ≤ Real.log H := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast hHpos)]
      have hexp2 : Real.exp 2 ≤ 8 := by
        have h := Real.exp_one_lt_d9
        have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [he2]; nlinarith [Real.exp_pos 1, h]
      linarith [hexp2, hHR]
    have hsq : (4 : ℝ) ≤ (Real.log H) ^ 2 := by nlinarith [hlogH2]
    have hq : 1 / (Real.log H) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq
    have he : (1 : ℝ) / 4 ≤ Real.exp (-1) := by
      have hexp1 : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 1) hexp1
    linarith [hd_small, hq, he]
  -- the FLAT budget
  have hbudget : d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
      ≤ (H : ℝ) / (4 * R.A * Real.log H) := by
    have hL0 : 0 ≤ Real.log ((jointSupport R.eps H).card : ℝ) := by
      apply Real.log_nonneg
      rw [jointSupport_card]; push_cast
      have h2H : (1 : ℝ) ≤ (2 : ℝ) ^ H := one_le_pow₀ (by norm_num)
      have hPH1 : (1 : ℝ) ≤ (PH R.eps H : ℝ) := by exact_mod_cast PH_pos R.eps H
      nlinarith [h2H, hPH1]
    have hLub := log_jointSupport_card_le R.toChowlaRegime H
    have hbin : Real.binEntropy d ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hdL : d * Real.log ((jointSupport R.eps H).card : ℝ)
        ≤ (3 / 2) * (H : ℝ) * Real.log 2 / (Real.log H) ^ 2 := by
      calc d * Real.log ((jointSupport R.eps H).card : ℝ)
          ≤ (1 / (Real.log H) ^ 2) * Real.log ((jointSupport R.eps H).card : ℝ) :=
            mul_le_mul_of_nonneg_right hd_small hL0
        _ ≤ (1 / (Real.log H) ^ 2) * ((3 / 2) * (H : ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hLub (by positivity)
        _ = (3 / 2) * (H : ℝ) * Real.log 2 / (Real.log H) ^ 2 := by ring
    calc d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
        ≤ (3 / 2) * (H : ℝ) * Real.log 2 / (Real.log H) ^ 2 + Real.log 2 := by linarith
      _ ≤ (H : ℝ) / (4 * R.A * Real.log H) :=
          budget_realFlat R.hApos hHfloor (R.hfannes_at hH)
  exact condEntropy_shift_le_of_l1_gen R.toChowlaRegime H j d _ hd_def hd1 hbudget

/-! ### Section 4 — the flat (3.11) step inequality -/

/-- **`step_ineq_3_11`'s FLAT TWIN** (freeze F-4).  The (3.11) assembly with the
    shift error in the FLAT slot `1/(4·A·log H)`.  Every other ingredient — the
    conditional concatenation subadditivity `condEntropy_kwindow_le`, the chain
    rule, `mutualInfo_eq_entropy_sub_condEntropy`, the `ℍ(Y_H) ≤ ε²H·log 4`
    ceiling — is the LANDED one, reached through `R.toChowlaRegime`. -/
theorem step_ineq_3_11Flat (R : ChowlaRegimeFlat) {H k : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (ha : R.a ∣ H) (hk : 1 ≤ k) :
    H[liouvilleWindow (k * H) ; logMeasure R.x R.ω] / ((k : ℝ) * H)
      ≤ H[liouvilleWindow H ; logMeasure R.x R.ω] / (H : ℝ)
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] / (H : ℝ)
        + ((R.eps : ℝ) ^ 2 * Real.log 4) / (k : ℝ)
        + 1 / (4 * R.A * Real.log H) := by
  haveI : IsProbabilityMeasure (logMeasure R.x R.ω) := isProbabilityMeasure_logMeasure R.hx R.hω
  have hYmeas : Measurable (residueWindow R.eps H) := measurable_residueWindow R.eps H
  have hXkHmeas : Measurable (liouvilleWindow (k * H)) := measurable_liouvilleWindow (k * H)
  have hXwinmeas : Measurable (liouvilleWindow H) := measurable_liouvilleWindow H
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHpos : 0 < H := by omega
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkH : (0 : ℝ) < (k : ℝ) * H := mul_pos hkpos hHR
  have hlogH : (0 : ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hApos : (0 : ℝ) < R.A := R.hApos
  have hDpos : (0 : ℝ) < 4 * R.A * Real.log H := by positivity
  -- Step 1: `ℍ(X_{kH}|Y) ≤ k·ℍ(X_H|Y) + k·(H/D)`
  have hstep1 : H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ (k : ℝ) * H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
        + (k : ℝ) * ((H : ℝ) / (4 * R.A * Real.log H)) := by
    have hkw := condEntropy_kwindow_le R.toChowlaRegime H k
    have hbound : ∀ b ∈ Finset.range k,
        H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasure R.x R.ω]
          ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
            + (H : ℝ) / (4 * R.A * Real.log H) :=
      fun b hb => condEntropy_shift_leFlat R hH hcpl (Finset.mem_range.mp hb) ha
    calc H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasure R.x R.ω]
        ≤ ∑ b ∈ Finset.range k,
            H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasure R.x R.ω] := hkw
      _ ≤ ∑ _b ∈ Finset.range k,
            (H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
              + (H : ℝ) / (4 * R.A * Real.log H)) :=
          Finset.sum_le_sum hbound
      _ = (k : ℝ) * (H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
              + (H : ℝ) / (4 * R.A * Real.log H)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = _ := by ring
  -- Step 2: `ℍ(X_{kH}) ≤ ℍ(Y) + ℍ(X_{kH}|Y)`
  have hstep2 : H[liouvilleWindow (k * H) ; logMeasure R.x R.ω]
      ≤ H[residueWindow R.eps H ; logMeasure R.x R.ω]
        + H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasure R.x R.ω] := by
    have hcr := chain_rule (logMeasure R.x R.ω) hXkHmeas hYmeas
    have hcr' := chain_rule' (logMeasure R.x R.ω) hXkHmeas hYmeas
    have hnn := condEntropy_nonneg (residueWindow R.eps H) (liouvilleWindow (k * H))
      (logMeasure R.x R.ω)
    linarith [hcr, hcr', hnn]
  -- Step 3: `ℍ(X_H|Y) = ℍ(X_H) − 𝕀`
  have hstep3 : H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
      = H[liouvilleWindow H ; logMeasure R.x R.ω]
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
    have := mutualInfo_eq_entropy_sub_condEntropy hXwinmeas hYmeas (logMeasure R.x R.ω)
    linarith [this]
  -- Step 4: `ℍ(Y) ≤ ε²·H·log 4`
  have hstep4 : H[residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) * Real.log 4 := by
    have h1 := entropy_residueWindow_le_log_PH R.eps H (logMeasure R.x R.ω)
    have h2 := log_PH_le R.eps H
    linarith [h1, h2]
  rw [hstep3] at hstep1
  have hmain : H[liouvilleWindow (k * H) ; logMeasure R.x R.ω]
      ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) * Real.log 4
        + (k : ℝ) * (H[liouvilleWindow H ; logMeasure R.x R.ω]
            - I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω])
        + (k : ℝ) * ((H : ℝ) / (4 * R.A * Real.log H)) := by
    linarith [hstep1, hstep2, hstep4]
  rw [div_le_iff₀ hkH]
  refine hmain.trans (le_of_eq ?_)
  have hHne : (H : ℝ) ≠ 0 := hHR.ne'
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hDne : (4 * R.A * Real.log H) ≠ 0 := hDpos.ne'
  field_simp
  ring

end Salt.Entropy.Chowla

