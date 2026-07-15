/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.MassLedger
import Salt.Chen.PLCascade

/-!
# MR2 — certifying the A₂ mass sum (the mass recursion + flat split + `c_flat`)

Design: `docs/blueprints/chen.md` (C1cσ / MR rows); flags `2026-07-13 MR1`, `VC2`, `C1b″`.

`MassLedger.Fchain_le_A2_of_massSum` reduces the whole A₂ ledger row (`Fchain ≤ 268/100` on
`[4/3,3]`) to a single scalar inequality on the even-level masses:

  `Σ_{k even, 2 ≤ k ≤ N−1} massE k ≤ 43/75`   (true value `0.5623`, slack `0.0113`).

This file certifies the load-bearing STRUCTURE of that sum: the **mass recursion** that turns the
even-mass sequence into a scalar cascade.

## The mass recursion (the crux)

For **even** `k = m+1` (`m` odd), the even window `fseq (m+1) s = (1/s)∫_s^{m+3} fseq m (t−1) dt`
integrates, by an integration-by-parts identity (the log weight is `∫_2^s du/u = log(s/2)`), to

  `massE (m+1) = ∫_2^{m+3} fseq m (s−1) · log(s/2) ds`.

The IBP takes `u = F(s) := ∫_s^{m+3} fseq m (t−1) dt` (continuous), `v = log(·/2)` (`v' = 1/s`);
both boundary terms vanish (`F(m+3)=0`, `log(2/2)=0`), and `F' = −fseq m (s−1)` by the FTC (needs
`fseq m` **continuous** at interior points — proved here for odd `m` via the `max`-formula, since
`fseq_props` only gives measurability/integrability).

## The flat split

For even `k = m+1 ≥ 4` (`m` odd `≥ 3`) the odd predecessor is `fseq m (u) = massE (m−1)/u` on the
flat window `[1,3]` (`MassLedger.fseq_odd_eq_massE`).  Splitting the recursion at `s = 4`
(`s−1 = 3`):

  `massE (m+1) = massE (m−1) · cflatI + Tail`,   `cflatI := ∫_2^4 log(s/2)/(s−1) ds`,
  `Tail := ∫_4^{m+3} fseq m (s−1) · log(s/2) ds ≥ 0`.

So the even masses obey a scalar recursion with the flat coefficient `cflatI ≈ 0.3554` (NOTE: the
MR2 mandate's `c_flat ≈ 0.2126 = ∫_2^3` DROPPED the `[1,2]` flat contribution; the honest
coefficient over the full flat window `[1,3]` — equivalently `∫_2^4 log(s/2)/(s−1)` in `s` — is
`0.3554`; see the flag) plus a nonnegative tail.  The two-level ratio is `cflatI + Tail/massE(m−1)`,
`→ 0.52239` as `k → ∞`.

## Status (Iron Rule 4): FLOOR A landed; the head+tail certification is the remaining C1cσ debt.

Landed here (sorry-free, axiom-clean): the mass recursion identity (`massE_recursion`), the flat
split (`massE_flat_split`), `cflatI`'s certified rational bound (`cflatI_le_half`), the level-2
head anchor (`massE_two_le` : `≤ 2 − (3/2)log 3 ≈ 0.352`, true `0.294`), and the TAIL MACHINERY —
the reindex `massSum_reindex` (`Σ_{k even} massE k = Σ_j massE (2j)`) and the head+geometric-tail
split `massSum_le_head_add_geomtail`, keyed on an abstract two-level mass contraction
`massE (2(j+1)) ≤ r·massE (2j)` fed through `PLCascade.geom_tail_ratio`.

Remaining C1cσ debt (multi-session): (1) the sharp head masses `massE 4..K*` as tight rationals —
each `= cflatI·massE(k−2) + Tail_k` needs a tight bound on `Tail_k`, and (2) the contraction
constant `r ≤ 0.55` (the hypothesis of `massSum_le_head_add_geomtail`).  Both need the odd-tail
profile decay: `Tail_k = ∫_2^{m} fseq (m−1)(w)·Φ(w) dw`, `Φ(w)=∫_3^{w+1} log((u+1)/2)/u du` (a
second Fubini of the recursion), which the VC2 support-growth wall shows requires fine-knot
profiles.  With cflatI ≈ 0.36 (tighter cubic-log bound) and `Tail_k/massE(k−2) → 0.167`, the true
two-level ratio is `→ 0.52239`; head to `2J = K* ≈ 12–14` then closes the sum `≤ 43/75`.
-/

open intervalIntegral MeasureTheory Set

namespace Salt.Chen

/-! ## The odd-level continuity lemma (the FTC input the recursion needs)

`fseq_props` gives only measurability/boundedness/integrability.  For the IBP recursion we need
`fseq m` continuous (odd `m`) on `[1, m+2]`.  On that interval the odd window collapses to the
single formula `fseq m s = (1/s)·∫_{max s 3}^{m+2} fseq (m−1)(t−1) dt` (flat for `s ≤ 3`, tail for
`s ≥ 3`, agreeing at the `s = 3` junction), a composition of the continuous primitive with the
continuous `max`, hence continuous. -/

/-- The shifted odd integrand `t ↦ fseq (m−1)(t−1)` is interval-integrable everywhere (used as the
primitive's integrand). -/
theorem fseq_shift_ii (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => fseq n (t - 1)) volume a b :=
  fseq_shift_intervalIntegrable n a b

/-- **Odd-level continuity.**  For odd `m`, `fseq m` is continuous on `[1, m+2]`.  (For `m = 1`,
`fseq 1 = (3−s)/s`; for `m ≥ 3`, the `max`-formula.) -/
theorem fseq_odd_continuousOn {m : ℕ} (hm : Odd m) :
    ContinuousOn (fseq m) (Set.Icc 1 ((m : ℝ) + 2)) := by
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact (by decide : ¬ Odd 0) hm)
  rcases eq_or_lt_of_le hmpos with hm1 | hm3
  · -- m = 1 : fseq 1 = (3 − s)/s on [1,3]
    subst hm1
    have hcast : ((1 : ℕ) : ℝ) + 2 = 3 := by norm_num
    rw [hcast]
    apply ContinuousOn.congr (f := fun s => (3 - s) / s)
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro s hs; have := hs.1; intro h; rw [h] at this; norm_num at this
    · intro s hs
      exact fseq_one_window hs.1 hs.2
  · -- m ≥ 3 odd
    have hm3' : 3 ≤ m := by
      rcases hm with ⟨j, hj⟩; omega
    have hn0 : (m - 1) ≠ 0 := by omega
    have hodd : ¬ Even ((m - 1) + 1) := by
      have : (m - 1) + 1 = m := by omega
      rw [this]; exact Nat.not_even_iff_odd.mpr hm
    -- the single formula on [1, m+2]
    set c : ℝ := (m : ℝ) + 2 with hc
    have hmm : ((m - 1 : ℕ) : ℝ) + 3 = c := by
      have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have := Nat.cast_sub (by omega : 1 ≤ m) (R := ℝ); simpa using this
      rw [this, hc]; ring
    have key : ∀ s ∈ Set.Icc (1 : ℝ) c,
        fseq m s = (1 / s) * ∫ t in (max s 3)..c, fseq (m - 1) (t - 1) := by
      intro s hs
      obtain ⟨hs1, hsc⟩ := hs
      have hmrw : (m - 1) + 1 = m := by omega
      rcases le_or_gt s 3 with h3 | h3
      · rw [max_eq_right h3]
        rcases eq_or_lt_of_le h3 with heq | hlt
        · -- s = 3 : tail window at 3
          have := fseq_odd_tail_window (n := m - 1) hn0 hodd (s := s) (by rw [heq])
          rw [hmrw, hmm] at this; rw [this, heq]
        · -- s < 3 : flat window
          have := fseq_odd_flat_window (n := m - 1) hn0 hodd (s := s) hs1 hlt
          rw [hmrw, hmm] at this; exact this
      · rw [max_eq_left h3.le]
        have := fseq_odd_tail_window (n := m - 1) hn0 hodd (s := s) h3.le
        rw [hmrw, hmm] at this; exact this
    apply ContinuousOn.congr (f := fun s => (1 / s) * ∫ t in (max s 3)..c, fseq (m - 1) (t - 1))
    · apply ContinuousOn.mul
      · apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro s hs; have := hs.1; intro h; rw [h] at this; norm_num at this
      · -- composition of continuous primitive with max
        have hprim : Continuous (fun a => ∫ t in a..c, fseq (m - 1) (t - 1)) := by
          have h1 : Continuous (fun a => ∫ t in c..a, fseq (m - 1) (t - 1)) :=
            intervalIntegral.continuous_primitive (fun a b => fseq_shift_ii (m - 1) a b) c
          have heq : (fun a => ∫ t in a..c, fseq (m - 1) (t - 1))
              = (fun a => - ∫ t in c..a, fseq (m - 1) (t - 1)) := by
            funext a; exact intervalIntegral.integral_symm c a
          rw [heq]; exact h1.neg
        exact (hprim.comp (continuous_id.max continuous_const)).continuousOn
    · intro s hs; exact key s hs

/-! ## The mass recursion (via integration by parts)

`massE (m+1) = ∫_2^{m+3} fseq m (s−1)·log(s/2) ds` for odd `m`.  IBP with `u = ∫_s^{m+3} fseq m`
(continuous), `v = log(·/2)` (`v' = 1/·`); both boundary terms vanish and `u' = −fseq m (·−1)`
by the FTC (needs `fseq_odd_continuousOn`). -/

/-- **The mass recursion.**  For odd `m`, the even mass `massE (m+1)` equals the log-weighted
integral of its odd predecessor `fseq m`. -/
theorem massE_recursion {m : ℕ} (hm : Odd m) :
    massE (m + 1)
      = ∫ s in (2 : ℝ)..((m : ℝ) + 3), fseq m (s - 1) * Real.log (s / 2) := by
  have hev : Even (m + 1) := hm.add_one
  have hble : (2 : ℝ) ≤ (m : ℝ) + 3 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  -- continuity of the shifted odd integrand on [2, m+3]
  have hcont_fm : ContinuousOn (fseq m) (Set.Icc 1 ((m : ℝ) + 2)) := fseq_odd_continuousOn hm
  have hmaps : Set.MapsTo (fun s : ℝ => s - 1)
      (Set.Icc 2 ((m : ℝ) + 3)) (Set.Icc 1 ((m : ℝ) + 2)) := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hshift_cont : ContinuousOn (fun s => fseq m (s - 1)) (Set.Icc 2 ((m : ℝ) + 3)) :=
    hcont_fm.comp (by fun_prop) hmaps
  -- rewrite massE as ∫_2^{m+3} (1/s)·F(s)
  have hmass : massE (m + 1)
      = ∫ s in (2 : ℝ)..((m : ℝ) + 3), (1 / s) * ∫ t in s..((m : ℝ) + 3), fseq m (t - 1) := by
    unfold massE
    have hup : (((m + 1 : ℕ) : ℝ) + 2) = (m : ℝ) + 3 := by push_cast; ring
    rw [hup]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hble] at hs
    have hs2 : (2 : ℝ) ≤ s := hs.1
    have := fseq_even_window (n := m) hev hs2
    simpa using this
  -- IBP
  have hu : ContinuousOn (fun s => ∫ t in s..((m : ℝ) + 3), fseq m (t - 1))
      (Set.uIcc 2 ((m : ℝ) + 3)) := by
    have hprim : Continuous (fun s => ∫ t in s..((m : ℝ) + 3), fseq m (t - 1)) := by
      have h1 : Continuous (fun s => ∫ t in ((m : ℝ) + 3)..s, fseq m (t - 1)) :=
        intervalIntegral.continuous_primitive (fun a b => fseq_shift_ii m a b) _
      have heq : (fun s => ∫ t in s..((m : ℝ) + 3), fseq m (t - 1))
          = (fun s => - ∫ t in ((m : ℝ) + 3)..s, fseq m (t - 1)) := by
        funext s; exact intervalIntegral.integral_symm _ s
      rw [heq]; exact h1.neg
    exact hprim.continuousOn
  have hv : ContinuousOn (fun s => Real.log (s / 2)) (Set.uIcc 2 ((m : ℝ) + 3)) := by
    apply ContinuousOn.log (by fun_prop)
    intro s hs; rw [Set.uIcc_of_le hble] at hs
    have : (2 : ℝ) ≤ s := hs.1; positivity
  have hminmax : Set.Ioo (min (2 : ℝ) ((m : ℝ) + 3)) (max (2 : ℝ) ((m : ℝ) + 3))
      = Set.Ioo 2 ((m : ℝ) + 3) := by
    rw [min_eq_left hble, max_eq_right hble]
  have huu' : ∀ s ∈ Set.Ioo (min (2 : ℝ) ((m : ℝ) + 3)) (max (2 : ℝ) ((m : ℝ) + 3)),
      HasDerivWithinAt (fun s => ∫ t in s..((m : ℝ) + 3), fseq m (t - 1))
        (-fseq m (s - 1)) (Set.Ioi s) s := by
    rw [hminmax]; intro s hs
    have hci : IntervalIntegrable (fun t => fseq m (t - 1)) volume s ((m : ℝ) + 3) :=
      fseq_shift_ii m s _
    have hIcc : Set.Icc (2 : ℝ) ((m : ℝ) + 3) ∈ nhds s := Icc_mem_nhds hs.1 hs.2
    have hcs : ContinuousAt (fun t => fseq m (t - 1)) s := hshift_cont.continuousAt hIcc
    have hmeas : StronglyMeasurableAtFilter (fun t => fseq m (t - 1)) (nhds s) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hshift_cont.mono Set.Ioo_subset_Icc_self) s hs
    exact (integral_hasDerivAt_left hci hmeas hcs).hasDerivWithinAt
  have hvv' : ∀ s ∈ Set.Ioo (min (2 : ℝ) ((m : ℝ) + 3)) (max (2 : ℝ) ((m : ℝ) + 3)),
      HasDerivWithinAt (fun s => Real.log (s / 2)) (1 / s) (Set.Ioi s) s := by
    rw [hminmax]; intro s hs
    have hne : s / 2 ≠ 0 := by have : (2 : ℝ) < s := hs.1; positivity
    have hg : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
    have hcomp : HasDerivAt (fun s => Real.log (s / 2)) ((1 / 2) / (s / 2)) s := hg.log hne
    have hval : (1 / 2) / (s / 2) = 1 / s := by
      have : (2 : ℝ) < s := hs.1; field_simp
    rw [hval] at hcomp
    exact hcomp.hasDerivWithinAt
  have hu' : IntervalIntegrable (fun s => -fseq m (s - 1)) volume 2 ((m : ℝ) + 3) :=
    (fseq_shift_ii m 2 _).neg
  have hv' : IntervalIntegrable (fun s => 1 / s) volume 2 ((m : ℝ) + 3) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs; rw [Set.uIcc_of_le hble] at hs
    have : (2 : ℝ) ≤ s := hs.1; positivity
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv huu' hvv' hu' hv'
  -- simplify boundary terms
  have hFb : (∫ t in ((m : ℝ) + 3)..((m : ℝ) + 3), fseq m (t - 1)) = 0 :=
    intervalIntegral.integral_same
  have hlog1 : Real.log ((2 : ℝ) / 2) = 0 := by norm_num
  rw [hFb, hlog1] at hibp
  simp only [zero_mul, mul_zero, sub_zero, zero_sub] at hibp
  -- assemble
  rw [hmass]
  calc (∫ s in (2 : ℝ)..((m : ℝ) + 3), (1 / s) * ∫ t in s..((m : ℝ) + 3), fseq m (t - 1))
      = ∫ s in (2 : ℝ)..((m : ℝ) + 3), (∫ t in s..((m : ℝ) + 3), fseq m (t - 1)) * (1 / s) := by
        apply intervalIntegral.integral_congr; intro s _; exact mul_comm _ _
    _ = -∫ s in (2 : ℝ)..((m : ℝ) + 3), -fseq m (s - 1) * Real.log (s / 2) := hibp
    _ = ∫ s in (2 : ℝ)..((m : ℝ) + 3), fseq m (s - 1) * Real.log (s / 2) := by
        rw [← intervalIntegral.integral_neg]; apply intervalIntegral.integral_congr
        intro s _; ring

/-! ## The flat coefficient `cflatI` and its certified bound

`cflatI = ∫_2^4 log(s/2)/(s−1) ds ≈ 0.3554` is the flat-window coefficient of the mass recursion
(the log-weighted mass of the `1/u` flat profile on `[1,3]`, in `s = u+1` coordinates).  Bounded
`≤ 1/2` via `log(s/2) ≤ (s−2)/2` (`log x ≤ x−1`), whose exact integral is `1 − (log 3)/2 < 1/2`.
(The load-bearing value for FULL closure is `≈0.36`, reachable with a tighter log majorant — the
flagged debt.) -/

/-- The flat-window coefficient `∫_2^4 log(s/2)/(s−1) ds` (true value `≈ 0.3554`). -/
noncomputable def cflatI : ℝ := ∫ s in (2 : ℝ)..4, Real.log (s / 2) / (s - 1)

/-- `cflatI ≥ 0` (nonnegative integrand on `[2,4]`). -/
theorem cflatI_nonneg : 0 ≤ cflatI := by
  unfold cflatI
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s hs
  have hs2 : (2 : ℝ) ≤ s := hs.1
  have hs4 : s ≤ 4 := hs.2
  apply div_nonneg
  · have : (1 : ℝ) ≤ s / 2 := by linarith
    exact Real.log_nonneg this
  · linarith

/-- **The certified flat coefficient bound.**  `cflatI ≤ 1/2`. -/
theorem cflatI_le_half : cflatI ≤ 1 / 2 := by
  have hint_log : IntervalIntegrable (fun s => Real.log (s / 2) / (s - 1)) volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
    · intro s hs; rw [Set.uIcc_of_le (by norm_num)] at hs
      have hs2 : (2:ℝ) ≤ s := hs.1; exact (show (0:ℝ) < s / 2 by linarith).ne'
    · intro s hs; rw [Set.uIcc_of_le (by norm_num)] at hs
      have hs2 : (2:ℝ) ≤ s := hs.1; intro h; rw [sub_eq_zero] at h; linarith
  have hint_rat : IntervalIntegrable (fun s => (s - 2) / (2 * (s - 1))) volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro s hs; rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs2 : (2:ℝ) ≤ s := hs.1; intro h; have : (2:ℝ)*(s-1) = 0 := h; nlinarith
  have hmono : cflatI ≤ ∫ s in (2 : ℝ)..4, (s - 2) / (2 * (s - 1)) := by
    unfold cflatI
    apply intervalIntegral.integral_mono_on (by norm_num) hint_log hint_rat
    intro s hs
    obtain ⟨hs2, hs4⟩ := hs
    have hs1 : (0 : ℝ) < s - 1 := by linarith
    have hlog2 : Real.log (s / 2) ≤ (s - 2) / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < s / 2 by linarith); linarith
    rw [div_le_div_iff₀ hs1 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hlog2 hs1.le]
  have hval : (∫ s in (2 : ℝ)..4, (s - 2) / (2 * (s - 1))) = 1 - Real.log 3 / 2 := by
    have hderiv : ∀ s ∈ Set.uIcc (2 : ℝ) 4,
        HasDerivAt (fun u => u / 2 - Real.log (u - 1) / 2) ((s - 2) / (2 * (s - 1))) s := by
      intro s hs; rw [Set.uIcc_of_le (by norm_num)] at hs
      have hs1 : (0 : ℝ) < s - 1 := by linarith [hs.1]
      have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
      have h2 : HasDerivAt (fun u : ℝ => Real.log (u - 1) / 2) ((1 / (s - 1)) / 2) s := by
        have := (((hasDerivAt_id s).sub_const 1).log hs1.ne')
        simpa using this.div_const 2
      have hcomb := h1.sub h2
      have hval2 : (1 / 2 - (1 / (s - 1)) / 2) = (s - 2) / (2 * (s - 1)) := by
        field_simp; ring
      rwa [hval2] at hcomb
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_rat]
    have e1 : Real.log ((4 : ℝ) - 1) = Real.log 3 := by norm_num
    have e2 : Real.log ((2 : ℝ) - 1) = 0 := by norm_num
    rw [e1, e2]; ring
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
  linarith [hmono, hval, hlog3]

/-! ## The flat split of the mass recursion

For even `k = m+1 ≥ 4` (`m` odd `≥ 3`), the odd predecessor `fseq m` is `massE (m−1)/u` on the
flat window `[1,3]` (`MassLedger.fseq_odd_eq_massE`).  Splitting the recursion at `s = 4`:
`massE (m+1) = massE (m−1)·cflatI + Tail`, `Tail = ∫_4^{m+3} fseq m (s−1)·log(s/2) ≥ 0`. -/

/-- The log-weighted odd integrand is interval-integrable on `[a,b]` when `0 < a ≤ b`. -/
theorem massInt_ii {m : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => fseq m (s - 1) * Real.log (s / 2)) volume a b := by
  apply (fseq_shift_ii m a b).mul_continuousOn
  apply ContinuousOn.log (by fun_prop)
  intro s hs; rw [Set.uIcc_of_le hab] at hs
  have hs' : 0 < s := lt_of_lt_of_le ha hs.1
  exact (show (0:ℝ) < s / 2 by linarith).ne'

/-- **The flat split.**  For odd `m ≥ 3`, `massE (m+1) = massE (m−1)·cflatI + Tail`, with the tail
`Tail = ∫_4^{m+3} fseq m (s−1)·log(s/2)` a nonnegative remainder. -/
theorem massE_flat_split {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    massE (m + 1) = massE (m - 1) * cflatI
      + ∫ s in (4 : ℝ)..((m : ℝ) + 3), fseq m (s - 1) * Real.log (s / 2) := by
  have hmc : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hbc3 : (4 : ℝ) ≤ (m : ℝ) + 3 := by linarith
  rw [massE_recursion hm]
  -- split at s = 4
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (massInt_ii (a := 2) (b := 4) (by norm_num) (by norm_num))
    (massInt_ii (a := 4) (b := (m : ℝ) + 3) (by norm_num) hbc3)]
  congr 1
  -- the flat part on [2,4] equals massE (m−1) · cflatI
  have hn0 : (m - 1) ≠ 0 := by omega
  have hne : Even (m - 1) := by
    rcases hm with ⟨j, hj⟩; rw [Nat.even_iff]; omega
  have hmrw : (m - 1) + 1 = m := by omega
  have hflat : (∫ s in (2 : ℝ)..4, fseq m (s - 1) * Real.log (s / 2))
      = ∫ s in (2 : ℝ)..4, massE (m - 1) * (Real.log (s / 2) / (s - 1)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs1 : (1 : ℝ) ≤ s - 1 := by linarith [hs.1]
    have hs3 : s - 1 ≤ 3 := by linarith [hs.2]
    have hval := fseq_odd_eq_massE (n := m - 1) hn0 hne hs1 hs3
    rw [hmrw] at hval
    change fseq m (s - 1) * Real.log (s / 2) = massE (m - 1) * (Real.log (s / 2) / (s - 1))
    rw [hval]; ring
  rw [hflat, intervalIntegral.integral_const_mul]
  rfl

/-! ## The level-2 head anchor `massE 2`

`massE 2 = ∫_2^4 (4−s)/(s−1)·log(s/2) ds` (the recursion with the explicit `f₁` predecessor).
Bounded by the same `log(s/2) ≤ (s−2)/2` majorant: `massE 2 ≤ 2 − (3/2)log 3 ≈ 0.352` (true
`0.2936`), and `≤ 1/2` rationally. -/

/-- **The level-2 head mass.**  `massE 2 ≤ 2 − (3/2)·log 3` (`≈ 0.352`, true `0.294`). -/
theorem massE_two_le : massE 2 ≤ 2 - 3 * Real.log 3 / 2 := by
  have h2 : massE 2 = ∫ s in (2 : ℝ)..4, fseq 1 (s - 1) * Real.log (s / 2) := by
    have h := massE_recursion (m := 1) (by decide)
    norm_num at h; exact h
  rw [h2]
  have hrat_ii : IntervalIntegrable (fun s => (4 - s) * (s - 2) / (2 * (s - 1))) volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro s hs; rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs2 : (2:ℝ) ≤ s := hs.1; intro h; have : (2:ℝ)*(s-1) = 0 := h; nlinarith
  have hmono : (∫ s in (2 : ℝ)..4, fseq 1 (s - 1) * Real.log (s / 2))
      ≤ ∫ s in (2 : ℝ)..4, (4 - s) * (s - 2) / (2 * (s - 1)) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (massInt_ii (m := 1) (by norm_num) (by norm_num)) hrat_ii
    intro s hs
    obtain ⟨hs2, hs4⟩ := hs
    have hs1 : (1 : ℝ) ≤ s - 1 := by linarith
    have hs1' : (0 : ℝ) < s - 1 := by linarith
    rw [fseq_one_window hs1 (by linarith)]
    have hc : (0 : ℝ) ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) (by linarith)
    have hlog2 : Real.log (s / 2) ≤ (s - 2) / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < s / 2 by linarith); linarith
    calc (3 - (s - 1)) / (s - 1) * Real.log (s / 2)
        = (4 - s) / (s - 1) * Real.log (s / 2) := by ring
      _ ≤ (4 - s) / (s - 1) * ((s - 2) / 2) := mul_le_mul_of_nonneg_left hlog2 hc
      _ = (4 - s) * (s - 2) / (2 * (s - 1)) := by rw [div_mul_div_comm]; ring_nf
  have hval : (∫ s in (2 : ℝ)..4, (4 - s) * (s - 2) / (2 * (s - 1))) = 2 - 3 * Real.log 3 / 2 := by
    have hderiv : ∀ s ∈ Set.uIcc (2 : ℝ) 4,
        HasDerivAt (fun u => 5 * u / 2 - u ^ 2 / 4 - 3 * Real.log (u - 1) / 2)
          ((4 - s) * (s - 2) / (2 * (s - 1))) s := by
      intro s hs; rw [Set.uIcc_of_le (by norm_num)] at hs
      have hs1 : (0 : ℝ) < s - 1 := by linarith [hs.1]
      have h1 : HasDerivAt (fun u : ℝ => 5 * u / 2) (5 / 2) s := by
        simpa using ((hasDerivAt_id s).const_mul 5).div_const 2
      have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 4) ((2 * s) / 4) s := by
        simpa using ((hasDerivAt_pow 2 s)).div_const 4
      have h3 : HasDerivAt (fun u : ℝ => 3 * Real.log (u - 1) / 2) ((3 * (1 / (s - 1))) / 2) s := by
        have := (((hasDerivAt_id s).sub_const 1).log hs1.ne').const_mul 3
        simpa using this.div_const 2
      have hcomb := (h1.sub h2).sub h3
      have hval2 : (5 / 2 - 2 * s / 4 - 3 * (1 / (s - 1)) / 2)
          = (4 - s) * (s - 2) / (2 * (s - 1)) := by
        field_simp; ring
      rwa [hval2] at hcomb
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hrat_ii]
    have e1 : Real.log ((4 : ℝ) - 1) = Real.log 3 := by norm_num
    have e2 : Real.log ((2 : ℝ) - 1) = 0 := by norm_num
    rw [e1, e2]; ring
  linarith [hmono, hval]

/-- **The level-2 head mass, rational form.**  `massE 2 ≤ 1/2` (via `log 3 > 1`). -/
theorem massE_two_le_half : massE 2 ≤ 1 / 2 := by
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
  linarith [massE_two_le, hlog3]

/-! ## The tail machinery: reindexing to `massE (2j)` and the self-certified geometric tail

The A₂ target sum `Σ_{k even, 2 ≤ k < N} massE k` reindexes onto the even sub-sequence
`j ↦ massE (2j)` (`j ≥ 1`), on which a two-level mass contraction `massE (2(j+1)) ≤ r·massE (2j)`
feeds the landed `PLCascade.geom_tail_ratio`.  This packages the FULL closure into: certified head
masses `+` a certified contraction constant `r` (the flagged debt). -/

/-- **The mass-sum reindex.**  `Σ_{k even, 2 ≤ k < N} massE k = Σ_{1 ≤ j < ⌈N/2⌉} massE (2j)`. -/
theorem massSum_reindex (N : ℕ) :
    (∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k)
      = ∑ j ∈ Finset.Ico 1 ((N + 1) / 2), massE (2 * j) := by
  apply Finset.sum_nbij' (fun k => k / 2) (fun j => 2 * j)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.even_iff] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hk
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hk
    congr 1; omega

/-- **The self-certified mass tail.**  A two-level contraction `massE (2(j+1)) ≤ r·massE (2j)` on
`[J, L)` (`0 ≤ r < 1`) gives `Σ_{j ∈ [J,L)} massE (2j) ≤ massE (2J)/(1−r)`, uniform in `L`.
Direct specialization of `PLCascade.geom_tail_ratio` to `b j := massE (2j)`. -/
theorem massEvenSum_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {J L : ℕ}
    (hstep : ∀ j, J ≤ j → j < L → massE (2 * (j + 1)) ≤ r * massE (2 * j)) :
    (∑ j ∈ Finset.Ico J L, massE (2 * j)) ≤ massE (2 * J) / (1 - r) :=
  geom_tail_ratio (b := fun j => massE (2 * j)) hr0 hr1 (fun _ => massE_nonneg _) hstep

/-- **The A₂ mass sum: head + self-certified geometric tail.**  With a two-level mass contraction
from depth `2J`, the whole A₂ sum splits into a finite head `Σ_{1 ≤ j < J} massE (2j)` and a
geometric tail `≤ massE (2J)/(1−r)`.  A fine-knot cascade discharges the contraction at its terminal
depth; the numeric plan targets `r ≈ 0.5224` (certifiable `≤ 0.55`), head to `2J ≈ K* ≈ 12–14`. -/
theorem massSum_le_head_add_geomtail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N J : ℕ) (hJ : 1 ≤ J)
    (hstep : ∀ j, J ≤ j → j < (N + 1) / 2 → massE (2 * (j + 1)) ≤ r * massE (2 * j)) :
    (∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k)
      ≤ (∑ j ∈ Finset.Ico 1 J, massE (2 * j)) + massE (2 * J) / (1 - r) := by
  rw [massSum_reindex]
  rcases le_total J ((N + 1) / 2) with hJL | hLJ
  · rw [← Finset.sum_Ico_consecutive (fun j => massE (2 * j)) hJ hJL]
    have htail := massEvenSum_tail_le hr0 hr1 (J := J) (L := (N + 1) / 2) hstep
    linarith
  · -- head already covers the whole reindexed sum
    have hsub : Finset.Ico 1 ((N + 1) / 2) ⊆ Finset.Ico 1 J :=
      Finset.Ico_subset_Ico (le_refl 1) hLJ
    have h1 : (∑ j ∈ Finset.Ico 1 ((N + 1) / 2), massE (2 * j))
        ≤ ∑ j ∈ Finset.Ico 1 J, massE (2 * j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => massE_nonneg _)
    have htail : (0 : ℝ) ≤ massE (2 * J) / (1 - r) :=
      div_nonneg (massE_nonneg _) (by linarith)
    linarith

end Salt.Chen
