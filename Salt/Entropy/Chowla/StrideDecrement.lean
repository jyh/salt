/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F4a — THE DECREMENT AT THE STRIDE MEASURE (the D-block)

Tao arXiv:1509.05422 Lemma 3.1 (the entropy decrement along the tower) at the pushforward
measure `logMeasureAff a x ω := (logMeasure x ω).map (a * ·)` (`StrideFork.lean:75`): the twins
of `Step` / `InvarianceHead` / `Tower` / `Endpoints` / `Decrement`, stated at a plain
`ChowlaRegime` whose stride `R.a` is read INTO THE MEASURE.  The consumer is the affine shell
(`StrideShell.lean`), whose `hI` slot is this file's headline `entropy_decrementAff`.

THE DESIGN (price brief `2026-09-04-math-PRICE-lbv-w2S-F4-entropy-half.md` §3, D-block).  Of the
78 declarations of the nine landed files, 11 proofs touch a `logMeasure`-named lemma and 9 of
those only the probability instance (`isProbabilityMeasure_logMeasure` ↦
`isProbabilityMeasure_logMeasureAff`, `StrideFork.lean:104`); the two structural ones are
`base_l1_le` (`Step.lean:89`) and `joint_l1_le` (`Step.lean:255`).  ⭐ THE ONE DESIGN LEMMA:
`logMeasureAff_map_shift` — a shift by `t` with `a ∣ t` of the stride measure IS the plain
measure shifted by `t/a` and then pushed along `a * ·` (`a·(n + t/a) = a·n + t`).  So the joint
`ℓ¹` value at the stride measure is the generic pushforward contraction `map_real_l1_le`
(`Step.lean:70`, `P Q : Measure ℕ`-generic) at `g := jointWindow ∘ (a * ·)` composed with
`base_l1_le` VERBATIM at the shift `t/a` and `harmonic_shift_l1_le` verbatim: `base_l1_le` needs
NO twin, and the bound `8·(jH/a)·ω/x ≤ 8·jH·ω/x` lets `R.hheadroom'` discharge the Fannes
budget exactly as at stride `1`.  `R.a ∣ H` is CONSUMED here (F1's B7) where the landed lane
carries and discards it (`Step.lean:418` `_ha`, `Tower.lean:161`).  Everything else — the
concatenation `condEntropy_kwindow_le` (`liouvilleWindow_block` + chain rules), the reduction
spine, the tower arithmetic, the endpoints (`entropy_liouvilleWindow_le` is already `∀ μ`,
`Windows.lean:62`) — is a copy with the measure renamed.

⛔ Degenerate values (the W4 law): `a = 0` makes `logMeasureAff 0 x ω` the Dirac mass at `0`;
every statement below reads the stride as `R.a` with `R.ha : 1 ≤ R.a`, and the free-`a` lemmas
(`logMeasureAff_map_shift`, the instance) are true at `a = 0` as stated (`0 ∣ t ↔ t = 0`).
`H = 0` inherits the landed lane's degeneracy (the tower never produces it: `hHlo_floor`).
At `R.a = 1` every statement is the landed one through `logMeasureAff_one`
(`entropy_decrementAff_one` is the receipt).

HONEST LABEL.  Nothing here produces a door, proves an estimate about the affine correlation,
or bears on twin primes.  Every declaration below except the instance is statement-only at the
freeze (sorry-bodied, recipe in the docstring), built as a module through `../saltbuild.sh`; NO
executor fires before the helm's refuter verdict.  ⛔ MERGE FENCE (iron rule 2):
`math/lbv-w2s-f4a` never reaches `main` until every obligation in the four F4a files lands
sorry-free.
-/
import Salt.Entropy.Chowla.StridePair
import Salt.Entropy.Chowla.Decrement
import Mathlib

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## F4-D0 — the two plumbing facts every twin needs -/

/-- **F4-D0a (class A, LANDED AT THE FREEZE — an `instance`).**  The stride measure has finite
support: `finiteSupport_of_comp` (`Salt/Entropy/Measure.lean:150`, a LEMMA, not an instance —
so this declaration is mandatory: without it every `integrable_of_finiteSupport _` at
`logMeasureAff` fails to resolve) at the landed `instFiniteSupport (logMeasure x ω)`
(`LogMeasure.lean:80`).  ⛔ It gives `FiniteSupport` ONLY, not `IsFiniteMeasure`:
`integrable_of_finiteSupport _` demands BOTH, and the latter comes only through
`isProbabilityMeasure_logMeasureAff` under the ambient `hx hω` instance (v1.1, verdict A3). -/
instance finiteSupport_logMeasureAff (a x ω : ℕ) : FiniteSupport (logMeasureAff a x ω) := by
  unfold logMeasureAff
  exact finiteSupport_of_comp (measurable_from_nat)

/-- **F4-D0b (class B) — THE DESIGN LEMMA: a shift pulls through the pushforward.**  For
`a ∣ t`, shifting the stride measure by `t` is shifting the plain measure by `t / a` and then
pushing along `a * ·`, because `a * (n + t / a) = a * n + t` (`Nat.mul_add`,
`Nat.mul_div_cancel' hdvd`).  Recipe: `unfold logMeasureAff; rw [Measure.map_map
(measurable_of_countable _) measurable_from_nat, Measure.map_map measurable_from_nat
(measurable_of_countable _)]; congr 1; funext n; simp only [Function.comp]; rw [Nat.mul_add,
Nat.mul_div_cancel' hdvd]`.  True at `a = 0` (then `t = 0`). -/
theorem logMeasureAff_map_shift (a x ω t : ℕ) (hdvd : a ∣ t) :
    (logMeasureAff a x ω).map (fun n => n + t)
      = ((logMeasure x ω).map (fun n => n + t / a)).map (fun n => a * n) := by
  unfold logMeasureAff
  rw [Measure.map_map (measurable_from_nat) (measurable_from_nat),
    Measure.map_map (measurable_from_nat) (measurable_from_nat)]
  congr 1
  funext n
  simp only [Function.comp_apply]
  rw [Nat.mul_add, Nat.mul_div_cancel' hdvd]

/-! ## F4-D1 — the joint-law `ℓ¹` value at the stride measure (the one twin with content) -/

/-- **F4-D1 (class B) — the joint `ℓ¹` estimate at the stride measure.**  The twin of
`joint_l1_le` (`Step.lean:255`) with the SAME bound `8·(jH)·ω/x`; `R.a ∣ H` is CONSUMED.
Recipe: set `t' := j * H / R.a` (so `R.a ∣ j * H` by `Dvd.dvd.mul_left`, and `t' ≤ j * H`);
rewrite the shifted joint law by `logMeasureAff_map_shift` and `Measure.map_map` into
`((logMeasure R.x R.ω).map (· + t')).map (jointWindow R.eps H 0 ∘ (R.a * ·))`, and the base
joint law into `(logMeasure R.x R.ω).map (jointWindow R.eps H 0 ∘ (R.a * ·))` (`unfold
logMeasureAff; Measure.map_map`); then the landed body of `joint_l1_le` VERBATIM with `g :=
jointWindow R.eps H 0 ∘ (R.a * ·)` (measurable by `measurable_of_countable`; its range sits in
`jointSupport` by `jointWindow_mem_jointSupport`), `A := Finset.Ioc 0 (R.x + t')`, the two
nullities from `logMeasure_apply` as at `Step.lean:266-284`; `map_real_l1_le` (`Step.lean:70`),
then `base_l1_le R.hx R.hω R.hωx` at `t'` and `harmonic_shift_l1_le R.hx R.hω R.hωx` at `t'`,
finally `8·t'·ω/x ≤ 8·(jH)·ω/x` by `Nat.div_le_self` and `gcongr`. -/
theorem joint_l1_le_aff (R : ChowlaRegime) (H j : ℕ) (hdvd : R.a ∣ H) :
    (∑ s ∈ jointSupport R.eps H,
      |(((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map
            (jointWindow R.eps H 0)).real {s}
        - ((logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
      ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by
  haveI hμprob : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  have hdvd' : R.a ∣ j * H := hdvd.mul_left j
  haveI hPprob : IsProbabilityMeasure
      ((logMeasure R.x R.ω).map (fun n => n + j * H / R.a)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  -- the shifted stride law IS the plain law shifted by `jH/a` and pushed along `a·`
  have hshiftmap : ((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map
        (jointWindow R.eps H 0)
      = ((logMeasure R.x R.ω).map (fun n => n + j * H / R.a)).map
          (fun n => jointWindow R.eps H 0 (R.a * n)) := by
    rw [logMeasureAff_map_shift R.a R.x R.ω (j * H) hdvd',
      Measure.map_map (measurable_jointWindow R.eps H 0) measurable_from_nat]
    rfl
  have hbasemap : (logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)
      = (logMeasure R.x R.ω).map (fun n => jointWindow R.eps H 0 (R.a * n)) := by
    unfold logMeasureAff
    rw [Measure.map_map (measurable_jointWindow R.eps H 0) measurable_from_nat]
    rfl
  rw [hshiftmap, hbasemap]
  -- name the pulled-back shift `t = jH/a` so the window arithmetic sees an opaque `ℕ`
  obtain ⟨t, hteq⟩ : ∃ t : ℕ, t = j * H / R.a := ⟨_, rfl⟩
  have hcast : (t : ℝ) ≤ ((j * H : ℕ) : ℝ) := by
    rw [hteq]; exact_mod_cast Nat.div_le_self (j * H) R.a
  rw [← hteq]
  have hm1 : 1 ≤ R.x / R.ω := Nat.div_pos R.hωx (by have := R.hω; omega)
  have hshift : Measurable (fun n : ℕ => n + t) := measurable_of_countable _
  have hμwin : (logMeasure R.x R.ω) ((Finset.Ioc (R.x / R.ω) R.x : Set ℕ)ᶜ) = 0 := by
    rw [logMeasure_apply]
    have hz : (∑ m ∈ Finset.Ioc (R.x / R.ω) R.x,
        (m : ℝ≥0∞)⁻¹ * (Measure.dirac m) ((Finset.Ioc (R.x / R.ω) R.x : Set ℕ)ᶜ)) = 0 :=
      Finset.sum_eq_zero (fun m hm => by
        rw [Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hm), mul_zero])
    rw [hz, mul_zero]
  have hQA : (logMeasure R.x R.ω) ((Finset.Ioc 0 (R.x + t) : Set ℕ)ᶜ) = 0 := by
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  have hPA : ((logMeasure R.x R.ω).map (fun n => n + t))
      ((Finset.Ioc 0 (R.x + t) : Set ℕ)ᶜ) = 0 := by
    rw [Measure.map_apply hshift (Finset.measurableSet _).compl]
    apply measure_mono_null _ hμwin
    intro n hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Ioc] at hn ⊢
    omega
  calc (∑ s ∈ jointSupport R.eps H,
        |(((logMeasure R.x R.ω).map (fun n => n + t)).map
              (fun n => jointWindow R.eps H 0 (R.a * n))).real {s}
          - ((logMeasure R.x R.ω).map
              (fun n => jointWindow R.eps H 0 (R.a * n))).real {s}|)
      ≤ ∑ n ∈ Finset.Ioc 0 (R.x + t),
          |((logMeasure R.x R.ω).map (fun n => n + t)).real {n}
            - (logMeasure R.x R.ω).real {n}| :=
        map_real_l1_le ((logMeasure R.x R.ω).map (fun n => n + t)) (logMeasure R.x R.ω)
          (fun n => jointWindow R.eps H 0 (R.a * n)) (measurable_of_countable _)
          (jointSupport R.eps H) (Finset.Ioc 0 (R.x + t)) hPA hQA
          (fun n _ => jointWindow_mem_jointSupport R.eps H 0 (R.a * n))
    _ ≤ 2 * (∑ m ∈ Finset.Ioc (R.x / R.ω) (R.x / R.ω + t), (m : ℝ)⁻¹)
          / (∑ n ∈ Finset.Ioc (R.x / R.ω) R.x, (n : ℝ)⁻¹) :=
        base_l1_le R.hx R.hω R.hωx
    _ ≤ 8 * (t : ℝ) * (R.ω : ℝ) / (R.x : ℝ) :=
        harmonic_shift_l1_le R.hx R.hω R.hωx
    _ ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by gcongr

/-! ## F4-D2 — the reduction spine and the Fannes bridge at the stride measure -/

/-- **F4-D2a (class A).**  `condEntropy_shift_reduction` (`InvarianceHead.lean:108`) with the
measure renamed: its only `logMeasure` use is the probability instance (`:114`), supplied here
by `haveI : IsProbabilityMeasure (logMeasure R.x R.ω) := isProbabilityMeasure_logMeasure R.hx
R.hω` and the instance `isProbabilityMeasure_logMeasureAff`; the body (`chain_rule`,
`jointWindow_zero`, `entropy_comp_of_injective` + `jointRelabel_injective`,
`jointWindow_zero_comp_shift`, `entropy_def`, `Measure.map_map`) is measure-generic. -/
theorem condEntropy_shift_reduction_aff (R : ChowlaRegime) (H j : ℕ) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      - H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
    = Hm[((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)]
      - Hm[(logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)] := by
  haveI hprob : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  set μ := logMeasureAff R.a R.x R.ω with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_logMeasureAff R.a R.x R.ω
  have hj_cr := chain_rule μ (measurable_liouvilleWindowShift H j)
    (measurable_residueWindow R.eps H)
  have h0_cr := chain_rule μ (measurable_liouvilleWindow H) (measurable_residueWindow R.eps H)
  have hCEj : H[liouvilleWindowShift H j | residueWindow R.eps H ; μ]
      = H[jointWindow R.eps H j ; μ] - H[residueWindow R.eps H ; μ] := by
    rw [show H[jointWindow R.eps H j ; μ]
        = H[(fun n => (liouvilleWindowShift H j n, residueWindow R.eps H n)) ; μ] from rfl,
      hj_cr]; ring
  have hCE0 : H[liouvilleWindow H | residueWindow R.eps H ; μ]
      = H[jointWindow R.eps H 0 ; μ] - H[residueWindow R.eps H ; μ] := by
    rw [jointWindow_zero, h0_cr]; ring
  rw [hCEj, hCE0]
  have hcancel : H[jointWindow R.eps H j ; μ] - H[residueWindow R.eps H ; μ]
      - (H[jointWindow R.eps H 0 ; μ] - H[residueWindow R.eps H ; μ])
      = H[jointWindow R.eps H j ; μ] - H[jointWindow R.eps H 0 ; μ] := by ring
  rw [hcancel]
  have hrelabel : H[jointWindow R.eps H j ; μ]
      = H[(fun n => jointWindow R.eps H 0 (n + j * H)) ; μ] := by
    rw [← entropy_comp_of_injective μ (measurable_jointWindow R.eps H j)
        (jointRelabel R.eps H j) (jointRelabel_injective R.eps H j)]
    congr 1
    rw [jointWindow_zero_comp_shift]
  rw [hrelabel, entropy_def, entropy_def,
    show Measure.map (jointWindow R.eps H 0) (μ.map (fun n => n + j * H))
        = Measure.map (fun n => jointWindow R.eps H 0 (n + j * H)) μ from by
      rw [Measure.map_map (measurable_jointWindow R.eps H 0)
          (measurable_of_countable (fun n : ℕ => n + j * H))]; rfl]

/-- **F4-D2b (class A).**  `condEntropy_shift_le_of_l1` (`InvarianceHead.lean:150`) with the
measure renamed (in `hd` too): the two nullities from `jointWindow_mem_jointSupport` and
`Measure.map_apply`, the Fannes bridge `entropy_sub_le_of_l1` (`Fannes.lean:190`, `μ ν`-generic),
and `condEntropy_shift_reduction_aff`; the only `logMeasure` use was the instance (`:161`). -/
theorem condEntropy_shift_le_of_l1_aff (R : ChowlaRegime) (H j : ℕ) (d : ℝ)
    (hd : d = ∑ s ∈ jointSupport R.eps H,
      |(((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map
            (jointWindow R.eps H 0)).real {s}
        - ((logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
    (hd1 : d ≤ Real.exp (-1))
    (hbudget : d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
        ≤ (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        + (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  haveI hprob : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  set μ := logMeasureAff R.a R.x R.ω with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_logMeasureAff R.a R.x R.ω
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
  have hred := condEntropy_shift_reduction_aff R H j
  rw [← hμ] at hred
  rw [← hμ', ← hν'] at hred
  linarith [hred, hdiff, hbudget]

/-- **F4-D2c (class A) — the D-d headline at the stride measure.**  `condEntropy_shift_le`
(`Step.lean:417`) with `joint_l1_le_aff` (which CONSUMES `ha`) in place of `joint_l1_le` and
`condEntropy_shift_le_of_l1_aff` in place of `condEntropy_shift_le_of_l1`; the budget arithmetic
(`budget_real`, `log_jointSupport_card_le`, `R.hheadroom'`) is verbatim — the bound is the
landed `8·(jH)·ω/x`. -/
theorem condEntropy_shift_le_aff (R : ChowlaRegime) {H k j : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (hj : j < k) (ha : R.a ∣ H) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        + (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  set d : ℝ := ∑ s ∈ jointSupport R.eps H,
      |(((logMeasureAff R.a R.x R.ω).map (fun n => n + j * H)).map
            (jointWindow R.eps H 0)).real {s}
        - ((logMeasureAff R.a R.x R.ω).map (jointWindow R.eps H 0)).real {s}| with hd_def
  have hd0 : 0 ≤ d := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hjl1 : d ≤ 8 * ((j * H : ℕ) : ℝ) * (R.ω : ℝ) / (R.x : ℝ) := by
    rw [hd_def]; exact joint_l1_le_aff R H j ha
  have hk1 : 1 ≤ k := by omega
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHpos : 0 < H := by omega
  have hHR : (4000000:ℝ) ≤ (H:ℝ) := by exact_mod_cast hHfloor
  have hjHle : j * H ≤ R.Hhi := by
    have hle : j * H ≤ k * H := by gcongr
    omega
  have hHhile : H ≤ R.Hhi := by
    have hle : H ≤ k * H := by
      calc H = 1 * H := (one_mul H).symm
        _ ≤ k * H := by gcongr
    omega
  have hHhipos : 0 < R.Hhi := by omega
  have hxR : (0:ℝ) < R.x := by exact_mod_cast (show 0 < R.x from by have := R.hx; omega)
  have hωR : (0:ℝ) < R.ω := by exact_mod_cast (show 0 < R.ω from by have := R.hω; omega)
  have hlogH : (0:ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hlogHhi : (0:ℝ) < Real.log R.Hhi :=
    Real.log_pos (by exact_mod_cast (show 1 < R.Hhi by omega))
  have hlogle : Real.log H ≤ Real.log R.Hhi :=
    Real.log_le_log (by exact_mod_cast hHpos) (by exact_mod_cast hHhile)
  have hd_small : d ≤ 1 / (Real.log H)^2 := by
    have h1 : d ≤ 8 * (R.Hhi:ℝ) * (R.ω:ℝ) / (R.x:ℝ) := by
      refine le_trans hjl1 ?_
      gcongr
    have hkey : 8 * (R.Hhi:ℝ) * (Real.log R.Hhi)^2 ≤ (R.x:ℝ)/(R.ω:ℝ) := by
      have hhr := R.hheadroom'
      have hdivle : ((R.x / R.ω : ℕ):ℝ) ≤ (R.x:ℝ)/(R.ω:ℝ) := Nat.cast_div_le
      calc 8 * (R.Hhi:ℝ) * (Real.log R.Hhi)^2
          = 8 * (R.Hhi:ℝ) * Real.log R.Hhi * Real.log R.Hhi := by ring
        _ ≤ ((R.x / R.ω : ℕ):ℝ) := hhr
        _ ≤ (R.x:ℝ)/(R.ω:ℝ) := hdivle
    have h2 : 8 * (R.Hhi:ℝ) * (R.ω:ℝ) / (R.x:ℝ) ≤ 1/(Real.log R.Hhi)^2 := by
      rw [div_le_div_iff₀ hxR (pow_pos hlogHhi 2)]
      have hm := mul_le_mul_of_nonneg_right hkey hωR.le
      have hxω : (R.x:ℝ)/(R.ω:ℝ) * (R.ω:ℝ) = (R.x:ℝ) := by field_simp
      rw [hxω] at hm
      nlinarith [hm]
    have hsqle : (Real.log H)^2 ≤ (Real.log R.Hhi)^2 := by nlinarith [hlogle, hlogH]
    have h3 : 1/(Real.log R.Hhi)^2 ≤ 1/(Real.log H)^2 :=
      one_div_le_one_div_of_le (pow_pos hlogH 2) hsqle
    linarith [h1, h2, h3]
  have hd1 : d ≤ Real.exp (-1) := by
    have hlogH2 : (2:ℝ) ≤ Real.log H := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast hHpos)]
      have hexp2 : Real.exp 2 ≤ 8 := by
        have h := Real.exp_one_lt_d9
        have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [he2]; nlinarith [Real.exp_pos 1, h]
      linarith [hexp2, hHR]
    have hsq : (4:ℝ) ≤ (Real.log H)^2 := by nlinarith [hlogH2]
    have hq : 1/(Real.log H)^2 ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hsq
    have he : (1:ℝ)/4 ≤ Real.exp (-1) := by
      have hexp1 : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 1) hexp1
    linarith [hd_small, hq, he]
  have hbudget : d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
      ≤ (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
    have hL0 : 0 ≤ Real.log ((jointSupport R.eps H).card : ℝ) := by
      apply Real.log_nonneg
      rw [jointSupport_card]; push_cast
      have h2H : (1:ℝ) ≤ (2:ℝ)^H := one_le_pow₀ (by norm_num)
      have hPH1 : (1:ℝ) ≤ (PH R.eps H : ℝ) := by exact_mod_cast PH_pos R.eps H
      nlinarith [h2H, hPH1]
    have hLub := log_jointSupport_card_le R H
    have hbin : Real.binEntropy d ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hdL : d * Real.log ((jointSupport R.eps H).card : ℝ)
        ≤ (3/2) * (H:ℝ) * Real.log 2 / (Real.log H)^2 := by
      calc d * Real.log ((jointSupport R.eps H).card : ℝ)
          ≤ (1/(Real.log H)^2) * Real.log ((jointSupport R.eps H).card : ℝ) :=
            mul_le_mul_of_nonneg_right hd_small hL0
        _ ≤ (1/(Real.log H)^2) * ((3/2) * (H:ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hLub (by positivity)
        _ = (3/2) * (H:ℝ) * Real.log 2 / (Real.log H)^2 := by ring
    calc d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
        ≤ (3/2) * (H:ℝ) * Real.log 2 / (Real.log H)^2 + Real.log 2 := by linarith
      _ ≤ (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := budget_real hHfloor
  exact condEntropy_shift_le_of_l1_aff R H j d hd_def hd1 hbudget

/-- **F4-D2d (class A) — conditional concatenation subadditivity at the stride measure.**
`condEntropy_kwindow_le` (`Step.lean:641`): `liouvilleWindow_block` (a pointwise identity in the
sample), `condEntropy_comp_of_injective` and `condEntropy_finPi_le` (both `μ`-generic,
`Step.lean:513/566`); the only `logMeasure` use was the instance (`:647`). -/
theorem condEntropy_kwindow_le_aff (R : ChowlaRegime) (H k : ℕ) :
    H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ ∑ b ∈ Finset.range k,
          H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] := by
  haveI hprob : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  set μ := logMeasureAff R.a R.x R.ω with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_logMeasureAff R.a R.x R.ω
  have hφ_inj : Function.Injective
      (fun F : Fin k → (Fin H → ℤ) =>
        fun i => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) := by
    intro F G h
    funext b j
    have hcong := congrFun h (finProdFinEquiv (b, j))
    simpa [Equiv.symm_apply_apply] using hcong
  haveI hfrX : FiniteRange (fun n : ℕ => (fun b : Fin k => liouvilleWindowShift H (b : ℕ) n)) := by
    apply finiteRange_of_finset _
      (Fintype.piFinset (fun _ : Fin k =>
        Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ))))
    intro n
    rw [Fintype.mem_piFinset]
    intro b
    exact liouvilleWindowShift_mem_piFinset H (b : ℕ) n
  have hkey : liouvilleWindow (k * H)
      = fun n => (fun F : Fin k → (Fin H → ℤ) =>
          fun i => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
            (fun b : Fin k => liouvilleWindowShift H (b : ℕ) n) := by
    funext n i
    change liouvilleWindow (k * H) n i
        = liouvilleWindowShift H ((finProdFinEquiv.symm i).1 : ℕ) n (finProdFinEquiv.symm i).2
    calc liouvilleWindow (k * H) n i
        = liouvilleWindow (k * H) n (finProdFinEquiv (finProdFinEquiv.symm i)) := by
          rw [finProdFinEquiv.apply_symm_apply]
      _ = liouvilleWindow H
            (n + ((finProdFinEquiv.symm i).1 : ℕ) * H) (finProdFinEquiv.symm i).2 :=
          liouvilleWindow_block k H n (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
      _ = liouvilleWindowShift H ((finProdFinEquiv.symm i).1 : ℕ) n (finProdFinEquiv.symm i).2 :=
          rfl
  rw [hkey]
  rw [condEntropy_comp_of_injective μ
      (measurable_of_countable (fun n : ℕ => (fun b : Fin k => liouvilleWindowShift H (b : ℕ) n)))
      (measurable_residueWindow R.eps H)
      (fun F : Fin k → (Fin H → ℤ) =>
        fun i => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
      hφ_inj]
  rw [← Fin.sum_univ_eq_sum_range
      (fun b => H[liouvilleWindowShift H b | residueWindow R.eps H ; μ]) k]
  exact condEntropy_finPi_le μ (measurable_residueWindow R.eps H) k
    (fun b : Fin k => liouvilleWindowShift H (b : ℕ))
    (fun b => measurable_liouvilleWindowShift H (b : ℕ))
    (fun b => instFiniteRangeShift H (b : ℕ))

/-- **F4-D2e (class A) — the (3.11) per-step inequality at the stride measure.**
`step_ineq_3_11` (`Step.lean:696`) with `condEntropy_kwindow_le_aff` and
`condEntropy_shift_le_aff` (`ha` forwarded, now consumed); the residue ceiling
`entropy_residueWindow_le_log_PH` (`PrimeWindow.lean:65`) is `∀ μ`. -/
theorem step_ineq_3_11_aff (R : ChowlaRegime) {H k : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : k * H ≤ R.Hhi) (ha : R.a ∣ H) (hk : 1 ≤ k) :
    H[liouvilleWindow (k * H) ; logMeasureAff R.a R.x R.ω] / ((k : ℝ) * H)
      ≤ H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ)
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] / (H : ℝ)
        + ((R.eps : ℝ) ^ 2 * Real.log 4) / (k : ℝ)
        + 1 / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  haveI hprob : IsProbabilityMeasure (logMeasure R.x R.ω) :=
    isProbabilityMeasure_logMeasure R.hx R.hω
  haveI : IsProbabilityMeasure (logMeasureAff R.a R.x R.ω) :=
    isProbabilityMeasure_logMeasureAff R.a R.x R.ω
  have hYmeas : Measurable (residueWindow R.eps H) := measurable_residueWindow R.eps H
  have hXkHmeas : Measurable (liouvilleWindow (k * H)) := measurable_liouvilleWindow (k * H)
  have hXwinmeas : Measurable (liouvilleWindow H) := measurable_liouvilleWindow H
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHpos : 0 < H := by omega
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hHpos
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkH : (0:ℝ) < (k:ℝ) * H := mul_pos hkpos hHR
  have hlogH : (0:ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hlogloglog_pos : 0 < Real.log (Real.log (Real.log H)) := by
    have hlogH3 : (3:ℝ) < Real.log H := by
      rw [Real.lt_log_iff_exp_lt hHR]
      have hexp3 : Real.exp 3 ≤ 21 := by
        have h := Real.exp_one_lt_d9
        have he3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; norm_num
        rw [he3]; nlinarith [Real.exp_pos 1, h]
      have h21 : (21:ℝ) < (H:ℝ) := by
        have : (4000000:ℝ) ≤ (H:ℝ) := by exact_mod_cast hHfloor
        linarith
      linarith
    have hloglogH1 : (1:ℝ) < Real.log (Real.log H) := by
      have hlt : Real.exp 1 < Real.log H := by have := Real.exp_one_lt_d9; linarith
      have hll := Real.log_lt_log (Real.exp_pos 1) hlt
      rwa [Real.log_exp] at hll
    calc (0:ℝ) = Real.log 1 := Real.log_one.symm
      _ < Real.log (Real.log (Real.log H)) := Real.log_lt_log (by norm_num) hloglogH1
  have hDpos : (0:ℝ) < 4 * Real.log H * Real.log (Real.log (Real.log H)) := by positivity
  have hstep1 : H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ (k:ℝ) * H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        + (k:ℝ) * ((H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) := by
    have hkw := condEntropy_kwindow_le_aff R H k
    have hbound : ∀ b ∈ Finset.range k,
        H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
          ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
            + (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) :=
      fun b hb => condEntropy_shift_le_aff R hH hcpl (Finset.mem_range.mp hb) ha
    calc H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        ≤ ∑ b ∈ Finset.range k,
            H[liouvilleWindowShift H b | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] := hkw
      _ ≤ ∑ _b ∈ Finset.range k,
            (H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
              + (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) :=
          Finset.sum_le_sum hbound
      _ = (k:ℝ) * (H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
              + (H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = _ := by ring
  have hstep2 : H[liouvilleWindow (k * H) ; logMeasureAff R.a R.x R.ω]
      ≤ H[residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        + H[liouvilleWindow (k * H) | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] := by
    have hcr := chain_rule (logMeasureAff R.a R.x R.ω) hXkHmeas hYmeas
    have hcr' := chain_rule' (logMeasureAff R.a R.x R.ω) hXkHmeas hYmeas
    have hnn := condEntropy_nonneg (residueWindow R.eps H) (liouvilleWindow (k * H))
      (logMeasureAff R.a R.x R.ω)
    linarith [hcr, hcr', hnn]
  have hstep3 : H[liouvilleWindow H | residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      = H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω]
        - I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] := by
    have := mutualInfo_eq_entropy_sub_condEntropy hXwinmeas hYmeas (logMeasureAff R.a R.x R.ω)
    linarith [this]
  have hstep4 : H[residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      ≤ (R.eps:ℝ)^2 * (H:ℝ) * Real.log 4 := by
    have h1 := entropy_residueWindow_le_log_PH R.eps H (logMeasureAff R.a R.x R.ω)
    have h2 := log_PH_le R.eps H
    linarith [h1, h2]
  rw [hstep3] at hstep1
  have hmain : H[liouvilleWindow (k * H) ; logMeasureAff R.a R.x R.ω]
      ≤ (R.eps:ℝ)^2 * (H:ℝ) * Real.log 4
        + (k:ℝ) * (H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω]
            - I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω])
        + (k:ℝ) * ((H:ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) := by
    linarith [hstep1, hstep2, hstep4]
  rw [div_le_iff₀ hkH]
  refine hmain.trans (le_of_eq ?_)
  have hHne : (H:ℝ) ≠ 0 := hHR.ne'
  have hkne : (k:ℝ) ≠ 0 := hkpos.ne'
  have hDne : (4 * Real.log H * Real.log (Real.log (Real.log H))) ≠ 0 := hDpos.ne'
  field_simp
  ring

/-! ## F4-D3 — the tower at the stride measure -/

/-- **F4-D3a (def).**  The per-symbol window entropy at tower level `j`, at the stride measure:
`towerEntropy` (`Tower.lean:137`) with the measure renamed. -/
noncomputable def towerEntropyAff (R : ChowlaRegime) (j : ℕ) : ℝ :=
  H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo j) ; logMeasureAff R.a R.x R.ω]
    / (chowlaTower R.C0 R.a R.Hlo j : ℝ)

/-- **F4-D3b (def).**  The mutual information at tower level `j`, at the stride measure:
`towerMI` (`Tower.lean:142`) with the measure renamed. -/
noncomputable def towerMIAff (R : ChowlaRegime) (j : ℕ) : ℝ :=
  I[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo j)
      : residueWindow R.eps (chowlaTower R.C0 R.a R.Hlo j) ; logMeasureAff R.a R.x R.ω]

/-- **F4-D3c (class A) — the abstract per-step drop.**  `tower_step_of` (`Tower.lean:152`) with
`step_ineq_3_11_aff`; the multiplier arithmetic is verbatim (measure-free). -/
lemma tower_step_of_aff (R : ChowlaRegime) {H m : ℕ}
    (hH : R.Hlo ≤ H) (hcpl : m * H ≤ R.Hhi) (ha : R.a ∣ H) (hm : 2 ≤ m)
    (hmL : (R.C0 : ℝ) * Real.log H * Real.log (Real.log (Real.log H)) - 1 < (m : ℝ))
    (hdec : (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))
        < I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]) :
    H[liouvilleWindow (m * H) ; logMeasureAff R.a R.x R.ω] / ((m : ℝ) * H)
        - H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ)
      ≤ -(1 / (2 * Real.log H * Real.log (Real.log (Real.log H)))) := by
  have hk1 : 1 ≤ m := le_trans (by norm_num) hm
  have hstep := step_ineq_3_11_aff R hH hcpl ha hk1
  have hHfloor : 4000000 ≤ H := le_trans R.hHlo_floor hH
  have hHRle : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHfloor
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  obtain ⟨hlogH15, hlll⟩ := tower_log_bounds hHfloor
  set L3 := Real.log (Real.log (Real.log (H : ℝ))) with hL3def
  set lg := Real.log (H : ℝ) with hlgdef
  have hlgpos : (0 : ℝ) < lg := by linarith [hlogH15]
  have hL3pos : (0 : ℝ) < L3 := by linarith [hlll]
  have hLpos : (0 : ℝ) < lg * L3 := mul_pos hlgpos hL3pos
  have hLge : (7.5 : ℝ) ≤ lg * L3 := by
    nlinarith [mul_le_mul hlogH15 hlll (by norm_num : (0 : ℝ) ≤ 1 / 2) hlgpos.le]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hC0R : (2 : ℝ) ≤ (R.C0 : ℝ) := by exact_mod_cast R.hC0
  have heps2 : (R.eps : ℝ) ^ 2 ≤ 1 / 4 := by
    have hq : R.eps ^ 2 ≤ 1 / 4 := by nlinarith [R.heps, R.heps1]
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc; linarith [hc]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4e : (R.eps : ℝ) ^ 2 * Real.log 4 ≤ (1 / 2) * Real.log 2 := by
    rw [hlog4]
    nlinarith [heps2, hlog2pos, mul_le_mul_of_nonneg_right heps2 hlog2pos.le]
  have hprod : (lg * L3) * Real.log 2 ≤ (lg * L3) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hlog2.le hLpos.le
  have hlog2L : 2 * Real.log 2 * (lg * L3) ≤ 2 * (lg * L3) - 1 := by nlinarith [hprod, hLge]
  have h2lgm : 2 * (lg * L3) - 1 < (m : ℝ) := by nlinarith [hmL, hC0R, hLpos]
  have h4lgpos : (0 : ℝ) < 4 * lg * L3 := mul_pos (mul_pos (by norm_num) hlgpos) hL3pos
  have hkey : (R.eps : ℝ) ^ 2 * Real.log 4 / (m : ℝ) ≤ 1 / (4 * lg * L3) := by
    rw [div_le_div_iff₀ hmpos h4lgpos]
    nlinarith [mul_le_mul_of_nonneg_right h4e h4lgpos.le, hlog2L, h2lgm]
  have hMH : 1 / (lg * L3)
      < I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] / (H : ℝ) := by
    rw [div_lt_iff₀ hLpos] at hdec
    rw [div_lt_div_iff₀ hLpos hHpos, one_mul]; exact hdec
  have hlgne : lg ≠ 0 := ne_of_gt hlgpos
  have hL3ne : L3 ≠ 0 := ne_of_gt hL3pos
  have he1 : 1 / (lg * L3) = 2 * (1 / (2 * lg * L3)) := by field_simp
  have he2 : 1 / (4 * lg * L3) = (1 / 2) * (1 / (2 * lg * L3)) := by field_simp; norm_num
  linarith [hstep, hkey, hMH, he1, he2]

/-- **F4-D3d (class A) — the telescope step.**  `tower_step` (`Tower.lean:210`) with
`tower_step_of_aff`; `dvd_chowlaTower R.C0 R.a R.Hlo j` supplies `ha` (`Tower.lean:234`),
`chowlaTower_ge`/`chowlaTower_le_Hhi`/`tower_mult_ge_two`/`chowlaTower_succ` verbatim. -/
lemma tower_step_aff (R : ChowlaRegime) {j : ℕ} (hj : j < R.J)
    (hdecj : (chowlaTower R.C0 R.a R.Hlo j : ℝ)
        / (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
      < towerMIAff R j) :
    towerEntropyAff R (j + 1) - towerEntropyAff R j
      ≤ -(1 / (2 * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
            * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))) := by
  simp only [towerMIAff] at hdecj
  have hHj : R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j := chowlaTower_ge R j
  have hfloor : 4000000 ≤ chowlaTower R.C0 R.a R.Hlo j := le_trans R.hHlo_floor hHj
  have hmult := tower_mult_ge_two R.hC0 hfloor
  have hrec : chowlaTower R.C0 R.a R.Hlo (j + 1)
      = (⌊(R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
          * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)))⌋₊)
        * chowlaTower R.C0 R.a R.Hlo j := by
    rw [chowlaTower_succ]; ring
  have hcpl : (⌊(R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)))⌋₊)
        * chowlaTower R.C0 R.a R.Hlo j ≤ R.Hhi := by
    rw [← hrec]; exact chowlaTower_le_Hhi R (by omega)
  have hmL := Nat.sub_one_lt_floor
      ((R.C0 : ℝ) * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
  have key := tower_step_of_aff R hHj hcpl (dvd_chowlaTower R.C0 R.a R.Hlo j) hmult hmL hdecj
  simp only [towerEntropyAff]
  rw [hrec, Nat.cast_mul]
  exact key

/-- **F4-D3e (class A) — the conditional telescoped bound.**  `tower_telescope`
(`Tower.lean:246`) with `tower_step_aff`: `Finset.sum_range_sub`, `Finset.sum_le_sum`,
`towerDropSum` unfolded — measure-free. -/
theorem tower_telescope_aff (R : ChowlaRegime)
    (hdec : ∀ j, j < R.J →
      (chowlaTower R.C0 R.a R.Hlo j : ℝ)
          / (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))
        < towerMIAff R j) :
    towerEntropyAff R R.J ≤ towerEntropyAff R 0 - towerDropSum R.C0 R.a R.Hlo R.J := by
  have hstep : ∀ j ∈ Finset.range R.J,
      towerEntropyAff R (j + 1) - towerEntropyAff R j
        ≤ -(1 / (2 * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ))))) :=
    fun j hj => tower_step_aff R (Finset.mem_range.mp hj) (hdec j (Finset.mem_range.mp hj))
  have htel := Finset.sum_range_sub (towerEntropyAff R) R.J
  have hsum := Finset.sum_le_sum hstep
  have hneg : ∑ j ∈ Finset.range R.J,
        -(1 / (2 * Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)
              * Real.log (Real.log (Real.log (chowlaTower R.C0 R.a R.Hlo j : ℝ)))))
      = - towerDropSum R.C0 R.a R.Hlo R.J := by
    simp only [towerDropSum, Finset.sum_neg_distrib]
  rw [htel, hneg] at hsum
  linarith [hsum]

/-! ## F4-D4 — the endpoints at the stride measure -/

/-- **F4-D4a (class A).**  `entropy_per_symbol_le` (`Endpoints.lean:41`):
`entropy_liouvilleWindow_le H (logMeasureAff R.a R.x R.ω)` — the landed lemma is `∀ μ`
(`Windows.lean:62`). -/
theorem entropy_per_symbol_le_aff (R : ChowlaRegime) (H : ℕ) (hH : 1 ≤ H) :
    H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ) ≤ Real.log 2 := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  rw [div_le_iff₀ hHpos, mul_comm]
  exact entropy_liouvilleWindow_le H (logMeasureAff R.a R.x R.ω)

/-- **F4-D4b (class A).**  `entropy_nonneg_per_symbol` (`Endpoints.lean:51`):
`div_nonneg (entropy_nonneg _ _) (Nat.cast_nonneg _)`. -/
theorem entropy_nonneg_per_symbol_aff (R : ChowlaRegime) (H : ℕ) :
    0 ≤ H[liouvilleWindow H ; logMeasureAff R.a R.x R.ω] / (H : ℝ) := by
  exact div_nonneg (entropy_nonneg _ _) (Nat.cast_nonneg _)

/-- **F4-D4c (class A).**  `mutualInfo_window_nonneg` (`Endpoints.lean:61`):
`mutualInfo_nonneg (measurable_liouvilleWindow H) (measurable_residueWindow R.eps H) _`. -/
theorem mutualInfo_window_nonneg_aff (R : ChowlaRegime) (H : ℕ) :
    0 ≤ I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω] := by
  exact mutualInfo_nonneg (measurable_liouvilleWindow H) (measurable_residueWindow R.eps H)
    (logMeasureAff R.a R.x R.ω)

/-- **F4-D4d (class A) — the mutual information is symmetric at the stride measure.**  The
consumer (`StrideShell`) states `hI` with the residue window FIRST, as `outer_combine_h` does
(`OuterCombine.lean:632`), while the decrement produces it window-first; `mutualInfo_comm
(measurable_liouvilleWindow H) (measurable_residueWindow R.eps H) _` (the twin of the private
`mutualInfo_window_comm_flat`, `SpineFlat.lean:54`). -/
theorem mutualInfo_window_comm_aff (R : ChowlaRegime) (H : ℕ) :
    I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      = I[residueWindow R.eps H : liouvilleWindow H ; logMeasureAff R.a R.x R.ω] := by
  simp only [mutualInfo_def]
  rw [entropy_comm (measurable_liouvilleWindow H) (measurable_residueWindow R.eps H)
    (logMeasureAff R.a R.x R.ω)]
  ring

/-- The per-tower-level mutual-information bound predicate at the stride measure
(`Endpoints.lean:82`'s `MIbound` with the measure renamed); reducible, hence defeq to the
explicit inequality of `entropy_decrementAff`. -/
private abbrev MIboundAff (R : ChowlaRegime) (H : ℕ) : Prop :=
  I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
    ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))

/-- **F4-D4e (class A) — the contradiction assembly.**  `decrement_exists_of_tower`
(`Endpoints.lean:98`) with `entropy_per_symbol_le_aff`, `entropy_nonneg_per_symbol_aff`,
`R.hJcon`, `decrement_of_not_forall`, `dvd_chowlaTower` — the `towerEntropyAff`/`towerMIAff`
spellings unfold (defeq) to the raw `H[…]`/`I[…]` this statement uses, as at stride `1`.
⭐ The witness's range is exported at TAO'S RANGE `R.a * R.Hlo ≤ H` (the tower's base is
`a·Hlo`, `Regime.lean:38`; the affine seam `contradiction_of_mrtDoorXiL2AffW` reads
`R.a * R.Hlo ≤ H`, `StridePair.lean:390`), which the landed `R.Hlo ≤ H` does not give: `hmono`
carries it, from `chowlaTower_eq_base_one` + `chowlaTower_ge_base R.hC0 (4·10⁶ ≤ R.a * R.Hlo) j`
(the `StridePair.lean:150-156` script). -/
theorem decrement_exists_of_tower_aff (R : ChowlaRegime)
    (htele :
      (∀ j < R.J, ¬ MIboundAff R (chowlaTower R.C0 R.a R.Hlo j)) →
        H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo R.J); logMeasureAff R.a R.x R.ω]
            / (chowlaTower R.C0 R.a R.Hlo R.J : ℝ)
          ≤ H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo 0); logMeasureAff R.a R.x R.ω]
              / (chowlaTower R.C0 R.a R.Hlo 0 : ℝ)
            - towerDropSum R.C0 R.a R.Hlo R.J)
    (hmono : ∀ j, j < R.J →
      R.a * R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j ∧ chowlaTower R.C0 R.a R.Hlo j ≤ R.Hhi) :
    ∃ H, R.a * R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
  have hbase : 1 ≤ chowlaTower R.C0 R.a R.Hlo 0 := by
    have ha := R.ha
    have hlo := R.hHlo_floor
    change 1 ≤ R.a * R.Hlo
    exact Nat.mul_pos (by omega) (by omega)
  have hnotall : ¬ ∀ j < R.J, ¬ MIboundAff R (chowlaTower R.C0 R.a R.Hlo j) := by
    intro hall
    have hdrop := htele hall
    have hceil := entropy_per_symbol_le_aff R (chowlaTower R.C0 R.a R.Hlo 0) hbase
    have hfloor := entropy_nonneg_per_symbol_aff R (chowlaTower R.C0 R.a R.Hlo R.J)
    have hcon := R.hJcon
    linarith
  obtain ⟨j, hjJ, hb⟩ := decrement_of_not_forall hnotall
  exact ⟨chowlaTower R.C0 R.a R.Hlo j, (hmono j hjJ).1, (hmono j hjJ).2,
    dvd_chowlaTower R.C0 R.a R.Hlo j, hb⟩

/-! ## F4-D5 — THE HEADLINE: Lemma 3.1 at the stride measure -/

/-- **F4-D5 (class A) — THE AFFINE DECREMENT (Tao Lemma 3.1 at the tuple `(λ(a·n + j))_j`).**
In any Chowla regime there is an admissible window width `H ∈ [H₋, H₊]` with `a ∣ H` at which
the window/residue mutual information UNDER THE STRIDE MEASURE is below the decrement
threshold.  Term-mode, as `entropy_decrement` (`Decrement.lean:49`):
`decrement_exists_of_tower_aff R (fun hfail => tower_telescope_aff R (fun j hj => not_le.mp
(hfail j hj))) (fun j hj => ⟨hbase j, chowlaTower_le_Hhi R (le_of_lt hj)⟩)` with `hbase j :
R.a * R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j` by `chowlaTower_eq_base_one` + `chowlaTower_ge_base`
(the range is TAO'S, `R.a * R.Hlo ≤ H`, not the landed `R.Hlo ≤ H` — see F4-D4e).
The regime is the crown's `Ra` (`StridePairReceipt.lean:2121`), a plain regime with a fitting,
crossing tower at stride `a` — nothing flat is read. -/
theorem entropy_decrementAff (R : ChowlaRegime) :
    ∃ H : ℕ, R.a * R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
        ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
  have hbase4 : 4000000 ≤ R.a * R.Hlo :=
    le_trans R.hHlo_floor (Nat.le_mul_of_pos_left _ R.ha)
  have hbase : ∀ j : ℕ, R.a * R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j := by
    intro j
    have h := chowlaTower_ge_base R.hC0 hbase4 j
    rw [← chowlaTower_eq_base_one R.C0 R.a R.Hlo j] at h
    exact h
  exact decrement_exists_of_tower_aff R
    (fun hfail => tower_telescope_aff R (fun j hj => not_le.mp (hfail j hj)))
    (fun j hj => ⟨hbase j, chowlaTower_le_Hhi R (le_of_lt hj)⟩)

/-- **F4-D5a (class A) — the stride-`1` receipt, RESTATED v1.1 (verdict A2(d)) at the MEASURE
level.**  At `R.a = 1` the mutual information at the stride measure IS the landed one, at every
`H`: `rw [hR1, logMeasureAff_one]`.  The v1 form was an `Iff` between the two decrement theorems'
conclusions — two landed-or-frozen theorems, unable to fail; here `logMeasureAff_one` is
LOAD-BEARING and the receipt is the object the decrement's twin actually changes. -/
theorem entropy_decrementAff_one (R : ChowlaRegime) (hR1 : R.a = 1) (H : ℕ) :
    I[liouvilleWindow H : residueWindow R.eps H ; logMeasureAff R.a R.x R.ω]
      = I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
  rw [hR1, logMeasureAff_one]

end Salt.Entropy.Chowla
