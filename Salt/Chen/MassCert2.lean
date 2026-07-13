/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.MassLedger
import Salt.Chen.MassLedgerA1
import Salt.Chen.MassCert
import Salt.Chen.PLCascade

/-!
# MR2b — the A₂ mass-sum close: the Φ-moment structural layer (+ the certified contraction, flagged)

Design: `docs/blueprints/chen.md` (C1cσ / MR rows); flags `2026-07-13 MR2` (catch #36 + the
Φ-moment route), `MR3` (catch #35), `VC2`, `C1cσ`.

`MassLedger.Fchain_le_A2_of_massSum` reduces the whole A₂ ledger row to the scalar
`Σ_{k even, 2 ≤ k < N} massE k ≤ 43/75` (true `0.5623`, slack `0.0113`).  `MassCert` landed the
mass recursion `massE (m+1) = cflatI·massE (m−1) + Tail_{m+1}` (`massE_flat_split`,
`Tail_{m+1} = ∫_4^{m+3} fseq m (s−1)·log(s/2) ds`) and the head+geometric-tail split
`massSum_le_head_add_geomtail`, keyed on an abstract two-level contraction
`massE (2(j+1)) ≤ r·massE (2j)`.

## What this file lands (the structural Φ-moment layer, all exact/rational, axiom-clean)

1. **The sub-interval mass bounds** (`fseq_odd_le_massE_div`, `fseq_even_le_massO_div`) — the clean
   rational envelope of the deep profile from the window recursion:
   * `fseq (p+1) w ≤ massE p / w` for `w ≥ 3` (odd level; the tail window integrates a
     sub-interval of `massE p`'s support), and
   * `fseq k u ≤ massO (k−1) / u` for `u ≥ 4` (even level; the even window integrates a
     sub-interval of `massO (k−1)`'s support, since `u−1 ≥ 3`).
   Both are *immediate and rational* (nonnegative integrand over a sub-interval), and MR4's
   `massO` ledger reuses `fseq_even_le_massO_div`.
2. **Even-level continuity** (`fseq_even_continuousOn`) — the FTC input the Φ-moment IBP needs
   (MR2 landed only the odd-level `fseq_odd_continuousOn`).
3. **The Φ-moment identity** (`massTail_eq_phiMoment`) — the *second Fubini* of MR2's `Tail`,
   done here honestly by **integration by parts** (no measure-theoretic Fubini): with
   `Φ v := ∫_3^{v+1} log((w+1)/2)/w dw`,

     `Tail_{m+1} = ∫_2^{m+1} fseq (m−1) (v) · Φ v dv`   (odd `m ≥ 3`),

   i.e. the tail is a `Φ`-weighted moment of the **even predecessor** `fseq (m−1)`.  IBP with
   `A(w) = ∫_w^{m+2} fseq (m−1) (t−1) dt` (continuous, `A' = −fseq (m−1) (w−1)`) and
   `B(w) = ∫_3^w log((τ+1)/2)/τ dτ` (`B' = log((w+1)/2)/w`, `B(3)=0`, `Φ v = B (v+1)`); both
   boundary terms vanish (`A(m+2)=0`, `B(3)=0`).
4. **The `[2,4]` closed evaluation** (`phiMoment_split_at_four`) — on `[2,4]` MR3's
   `fseq_even_eq_masses` makes `fseq (m−1)` an exact scalar, so

     `∫_2^4 fseq (m−1) (v)·Φ v dv = massE (m−3)·Cφ1 + massO (m−2)·Cφ2`,

   with the FIXED constants `Cφ1 = ∫_2^4 Φ v·(log 3 − log (v−1))/v dv`, `Cφ2 = ∫_2^4 Φ v/v dv`
   (certified nonnegative + rational upper bounds `Cφ1 ≤ 4/5`, `Cφ2 ≤ 2/5`; true `0.04403`,
   `0.14127` — the loose rational log majorant suffices, these constants are not load-bearing
   given the flagged contraction).  The `[2,4]` split identity itself is left to the keystone.

## The certified contraction is FLAGGED (Iron Rule 4) — `flags.md 2026-07-13 MR2b`

The FULL close `massSum_le_A2` needs a **uniform two-level contraction** `massE (2(j+1)) ≤
r·massE (2j)` (`r ≈ 0.5224`), the hypothesis of `MassCert.massSum_le_head_add_geomtail`.  From the
Φ-moment identity, `r = cflatI + κ` with `κ = sup_p Tail_{p+2}/massE p → 0.16698`; the residual is
bounding `κ`.  **This is provably NOT reachable from the landed lemmas by elementary bounds:**
`Tail = ∫ fseq (m−1)·Φ` and `massE (m−1) = ∫ fseq (m−1)`, so `Tail ≤ κ·massE (m−1)` pointwise would
need `Φ v ≤ κ`, but `Φ` is unbounded (`Φ v ~ (log v)²/2`).  Every surrogate weight (`ψ v =
log((v+1)/3)` for `massO`, or the first moment) is *also* unbounded and grows super-linearly
relative to the next — a machine check (numeric plan) shows `Φ v ≤ α + β·ψ v` forces `α → ∞`, so no
finite coupled-moment system closes.  A uniform `κ` genuinely requires the **sharp per-level profile
decay** (`fseq p (v) ≤ D·massE p·(fixed exponential envelope)`), which is exactly the C1cσ/VC2
fine-knot cascade keystone: the landed `fseq_le` has ratio `(99/100)² ≈ 0.98`, not the required
`≈ 0.52`, so it is exponentially too loose.  The exact closure arithmetic (which *does* close once a
certified `r` exists) is recorded in the flag: head to `k = 4` + tail `massE 6/(1−r)` closes at
`r ≤ 0.524`.
-/

open intervalIntegral MeasureTheory Set

namespace Salt.Chen

/-! ## The sub-interval mass bounds (the clean rational envelope of the deep profile) -/

/-- `massE n` rewritten as the shifted-argument integral `∫_3^{n+3} fseq n (t−1) dt`
(change of variables `v = t−1`; the sibling `∫_2^{n+2} fseq n v` is the definition). -/
theorem massE_shift_form (n : ℕ) :
    massE n = ∫ t in (3 : ℝ)..((n : ℝ) + 3), fseq n (t - 1) := by
  unfold massE
  have e1 : (3 : ℝ) - 1 = 2 := by norm_num
  have e2 : ((n : ℝ) + 3) - 1 = (n : ℝ) + 2 := by ring
  rw [intervalIntegral.integral_comp_sub_right (fun v => fseq n v) 1, e1, e2]

/-- `massO n` rewritten as the shifted-argument integral `∫_4^{n+3} fseq n (t−1) dt`
(change of variables `v = t−1`). -/
theorem massO_shift_form (n : ℕ) :
    massO n = ∫ t in (4 : ℝ)..((n : ℝ) + 3), fseq n (t - 1) := by
  unfold massO
  have e1 : (4 : ℝ) - 1 = 3 := by norm_num
  have e2 : ((n : ℝ) + 3) - 1 = (n : ℝ) + 2 := by ring
  rw [intervalIntegral.integral_comp_sub_right (fun v => fseq n v) 1, e1, e2]

/-- **Odd-level sub-interval bound.**  For an odd level `p+1` and `w ≥ 3`, the tail window makes
`fseq (p+1) w` an average of `fseq p` over `[w−1, p+2] ⊆ [2, p+2]`, hence `≤ massE p / w`.
Immediate and rational (nonnegative integrand over a sub-interval). -/
theorem fseq_odd_le_massE_div {p : ℕ} (hpe : Even p) {w : ℝ} (hw : 3 ≤ w) :
    fseq (p + 1) w ≤ massE p / w := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hodd : ¬ Even (p + 1) := by rw [Nat.even_add_one]; exact not_not_intro hpe
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · -- p = 0: fseq 1 is supported on [1,3], zero for w ≥ 3
    subst hp0
    have hz : fseq 1 w = 0 := fseq_eq_zero_of_ge 1 w (by push_cast; linarith)
    rw [hz]; exact div_nonneg (massE_nonneg 0) hw0.le
  · have hp0' : p ≠ 0 := hppos.ne'
    -- tail window
    rw [fseq_odd_tail_window hp0' hodd hw]
    rw [massE_shift_form]
    -- (1/w)·∫_w^{p+3} ≤ (1/w)·∫_3^{p+3}
    have hmono : (∫ t in w..((p : ℝ) + 3), fseq p (t - 1))
        ≤ ∫ t in (3 : ℝ)..((p : ℝ) + 3), fseq p (t - 1) := by
      have hsplit : (∫ t in (3 : ℝ)..((p : ℝ) + 3), fseq p (t - 1))
          = (∫ t in (3 : ℝ)..w, fseq p (t - 1)) + ∫ t in w..((p : ℝ) + 3), fseq p (t - 1) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (fseq_shift_intervalIntegrable p 3 w) (fseq_shift_intervalIntegrable p w _)).symm
      have hnn : 0 ≤ ∫ t in (3 : ℝ)..w, fseq p (t - 1) :=
        intervalIntegral.integral_nonneg hw (fun t _ => fseq_nonneg p (t - 1))
      linarith
    calc (1 / w) * ∫ t in w..((p : ℝ) + 3), fseq p (t - 1)
        = (∫ t in w..((p : ℝ) + 3), fseq p (t - 1)) / w := by ring
      _ ≤ (∫ t in (3 : ℝ)..((p : ℝ) + 3), fseq p (t - 1)) / w := by gcongr

/-- **Even-level sub-interval bound.**  For an even level `k` and `u ≥ 4`, the even window makes
`fseq k u` an average of `fseq (k−1)` over `[u−1, k+1] ⊆ [3, k+1]` (`u−1 ≥ 3`), hence
`≤ massO (k−1) / u`.  Immediate and rational; **reused by MR4's `massO` ledger**. -/
theorem fseq_even_le_massO_div {k : ℕ} (hke : Even k) {u : ℝ} (hu : 4 ≤ u) :
    fseq k u ≤ massO (k - 1) / u := by
  have hu0 : (0 : ℝ) < u := by linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; rw [fseq_zero]
    have : massO (0 - 1) = 0 := by norm_num [massO]
    rw [this]; positivity
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hn0 : n ≠ 0 := by rintro rfl; simp at hke
    have hu2 : (2 : ℝ) ≤ u := by linarith
    rw [fseq_even_window hke hu2]
    have hkm1 : n + 1 - 1 = n := by omega
    rw [hkm1, massO_shift_form]
    have hmono : (∫ t in u..((n : ℝ) + 3), fseq n (t - 1))
        ≤ ∫ t in (4 : ℝ)..((n : ℝ) + 3), fseq n (t - 1) := by
      have hsplit : (∫ t in (4 : ℝ)..((n : ℝ) + 3), fseq n (t - 1))
          = (∫ t in (4 : ℝ)..u, fseq n (t - 1)) + ∫ t in u..((n : ℝ) + 3), fseq n (t - 1) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (fseq_shift_intervalIntegrable n 4 u) (fseq_shift_intervalIntegrable n u _)).symm
      have hnn : 0 ≤ ∫ t in (4 : ℝ)..u, fseq n (t - 1) :=
        intervalIntegral.integral_nonneg hu (fun t _ => fseq_nonneg n (t - 1))
      linarith
    calc (1 / u) * ∫ t in u..((n : ℝ) + 3), fseq n (t - 1)
        = (∫ t in u..((n : ℝ) + 3), fseq n (t - 1)) / u := by ring
      _ ≤ (∫ t in (4 : ℝ)..((n : ℝ) + 3), fseq n (t - 1)) / u := by gcongr

/-! ## Even-level continuity (the FTC input the Φ-moment IBP needs)

`fseq_props` gives only measurability/integrability.  MR2 landed the *odd*-level continuity
(`fseq_odd_continuousOn`); the Φ-moment IBP needs the *even* predecessor continuous.  On `[2, k+2]`
the even level collapses to the single window formula `(1/s)·∫_s^{k+2} fseq (k−1) (t−1) dt`
(no flat/tail split — even levels have one formula on `[2,∞)`), a product of the continuous `1/s`
with the continuous primitive, hence continuous. -/

/-- **Even-level continuity.**  For even `k ≥ 2`, `fseq k` is continuous on `[2, k+2]`. -/
theorem fseq_even_continuousOn {k : ℕ} (hk2 : 2 ≤ k) (hke : Even k) :
    ContinuousOn (fseq k) (Set.Icc 2 ((k : ℝ) + 2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set c : ℝ := (n : ℝ) + 3 with hc
  have hcast : ((n + 1 : ℕ) : ℝ) + 2 = c := by rw [hc]; push_cast; ring
  rw [hcast]
  have key : ∀ s ∈ Set.Icc (2 : ℝ) c, fseq (n + 1) s = (1 / s) * ∫ t in s..c, fseq n (t - 1) := by
    intro s hs; exact fseq_even_window hke hs.1
  apply ContinuousOn.congr (f := fun s => (1 / s) * ∫ t in s..c, fseq n (t - 1))
  · apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro s hs; have h2 := hs.1; intro h; rw [h] at h2; norm_num at h2
    · have hprim : Continuous (fun s => ∫ t in s..c, fseq n (t - 1)) := by
        have h1 : Continuous (fun s => ∫ t in c..s, fseq n (t - 1)) :=
          intervalIntegral.continuous_primitive (fun a b => fseq_shift_ii n a b) c
        have heq : (fun s => ∫ t in s..c, fseq n (t - 1))
            = (fun s => - ∫ t in c..s, fseq n (t - 1)) := by
          funext s; exact intervalIntegral.integral_symm c s
        rw [heq]; exact h1.neg
      exact hprim.continuousOn
  · intro s hs; exact key s hs

/-! ## The Φ-moment: the second Fubini of MR2's `Tail`, via integration by parts -/

/-- `Φ v = ∫_3^{v+1} log((w+1)/2)/w dw` — the log-weighted moment kernel of the tail.  On the
even predecessor, `Tail_{m+1} = ∫_2^{m+1} fseq (m−1) (v)·Φ v dv`. -/
noncomputable def Phi (v : ℝ) : ℝ := ∫ w in (3 : ℝ)..(v + 1), Real.log ((w + 1) / 2) / w

/-- `Φ v ≥ 0` for `v ≥ 2` (nonnegative integrand `log((w+1)/2)/w` on `[3, v+1]`). -/
theorem Phi_nonneg {v : ℝ} (hv : 2 ≤ v) : 0 ≤ Phi v := by
  unfold Phi
  apply intervalIntegral.integral_nonneg (by linarith)
  intro w hw
  have hw3 : (3 : ℝ) ≤ w := hw.1
  apply div_nonneg
  · apply Real.log_nonneg; rw [le_div_iff₀ (by norm_num)]; linarith
  · linarith

/-- **The Φ-moment identity.**  For odd `m ≥ 3`, MR2's `Tail` equals the `Φ`-weighted moment of the
even predecessor `fseq (m−1)`:

  `∫_4^{m+3} fseq m (s−1)·log(s/2) ds = ∫_2^{m+1} fseq (m−1) (v)·Φ v dv`.

Honest integration by parts (no Fubini): `u(w) = ∫_w^{m+2} fseq (m−1) (t−1) dt` (continuous,
`u' = −fseq (m−1) (w−1)`), `v(w) = ∫_3^w log((τ+1)/2)/τ dτ = Φ (w−1)` (`v' = log((w+1)/2)/w`);
both boundary terms vanish (`u(m+2)=0`, `v(3)=0`). -/
theorem massTail_eq_phiMoment {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    (∫ s in (4 : ℝ)..((m : ℝ) + 3), fseq m (s - 1) * Real.log (s / 2))
      = ∫ v in (2 : ℝ)..((m : ℝ) + 1), fseq (m - 1) v * Phi v := by
  have hmc : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hbc3 : (3 : ℝ) ≤ (m : ℝ) + 2 := by linarith
  have hp0 : (m - 1) ≠ 0 := by omega
  have hpe : Even (m - 1) := by rcases hm with ⟨j, hj⟩; rw [Nat.even_iff]; omega
  have hodd : ¬ Even m := Nat.not_even_iff_odd.mpr hm
  have hmrw : (m - 1) + 1 = m := by omega
  have hcastm : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have := Nat.cast_sub (by omega : 1 ≤ m) (R := ℝ); simpa using this
  have hM2 : ((m - 1 : ℕ) : ℝ) + 3 = (m : ℝ) + 2 := by rw [hcastm]; ring
  have hM1 : ((m - 1 : ℕ) : ℝ) + 2 = (m : ℝ) + 1 := by rw [hcastm]; ring
  -- the log-weight `k` and its continuity/integrability (on the positive axis)
  set k : ℝ → ℝ := fun τ => Real.log ((τ + 1) / 2) / τ with hk
  have hk_ioi : ContinuousOn k (Set.Ioi (0 : ℝ)) := by
    rw [hk]
    apply ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
    · intro τ hτ; have hτ0 : (0 : ℝ) < τ := hτ; exact (by positivity : (0 : ℝ) < (τ + 1) / 2).ne'
    · intro τ hτ; exact (show (0 : ℝ) < τ from hτ).ne'
  have hIccsub : Set.Icc (3 : ℝ) ((m : ℝ) + 2) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1
  have hIoosub : Set.Ioo (3 : ℝ) ((m : ℝ) + 2) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1.le
  have hk_cont : ContinuousOn k (Set.uIcc 3 ((m : ℝ) + 2)) := by
    rw [Set.uIcc_of_le hbc3]; exact hk_ioi.mono hIccsub
  have hk_int : MeasureTheory.IntegrableOn k (Set.Icc 3 ((m : ℝ) + 2)) volume :=
    (hk_ioi.mono hIccsub).integrableOn_Icc
  have hk_ii : IntervalIntegrable k volume 3 ((m : ℝ) + 2) := hk_cont.intervalIntegrable
  -- even-predecessor continuity, shifted onto [3, m+2]
  have hcont_pred : ContinuousOn (fseq (m - 1)) (Set.Icc 2 ((m : ℝ) + 1)) := by
    have := fseq_even_continuousOn (k := m - 1) (by omega) hpe
    rwa [hM1] at this
  have hmaps : Set.MapsTo (fun w : ℝ => w - 1)
      (Set.Icc 3 ((m : ℝ) + 2)) (Set.Icc 2 ((m : ℝ) + 1)) := by
    intro w hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hshift_cont : ContinuousOn (fun w => fseq (m - 1) (w - 1)) (Set.Icc 3 ((m : ℝ) + 2)) :=
    hcont_pred.comp (by fun_prop) hmaps
  -- Step 1: change of variables s ↦ w = s − 1
  have hchange : (∫ s in (4 : ℝ)..((m : ℝ) + 3), fseq m (s - 1) * Real.log (s / 2))
      = ∫ w in (3 : ℝ)..((m : ℝ) + 2), fseq m w * Real.log ((w + 1) / 2) := by
    have hcongr : (∫ s in (4 : ℝ)..((m : ℝ) + 3), fseq m (s - 1) * Real.log (s / 2))
        = ∫ s in (4 : ℝ)..((m : ℝ) + 3),
            (fun w => fseq m w * Real.log ((w + 1) / 2)) (s - 1) := by
      apply intervalIntegral.integral_congr; intro s _
      have hs2 : ((s - 1) + 1) / 2 = s / 2 := by ring
      simp only [hs2]
    rw [hcongr, intervalIntegral.integral_comp_sub_right
        (fun w => fseq m w * Real.log ((w + 1) / 2)) 1,
      show (4 : ℝ) - 1 = 3 by norm_num, show ((m : ℝ) + 3) - 1 = (m : ℝ) + 2 by ring]
  -- Step 2: rewrite fseq m (odd tail window) into u(w)·v'(w) shape
  have htail : (∫ w in (3 : ℝ)..((m : ℝ) + 2), fseq m w * Real.log ((w + 1) / 2))
      = ∫ w in (3 : ℝ)..((m : ℝ) + 2),
          (∫ t in w..((m : ℝ) + 2), fseq (m - 1) (t - 1)) * k w := by
    apply intervalIntegral.integral_congr; intro w hw
    rw [Set.uIcc_of_le hbc3] at hw
    have hw3 : (3 : ℝ) ≤ w := hw.1
    have hfm : fseq m w = (1 / w) * ∫ t in w..((m : ℝ) + 2), fseq (m - 1) (t - 1) := by
      have h := fseq_odd_tail_window (n := m - 1) hp0 (by rw [hmrw]; exact hodd) hw3
      rw [hmrw, hM2] at h; exact h
    simp only [hk]; rw [hfm]; ring
  -- Step 3: IBP.  u = A(w) = ∫_w^{m+2} fseq(m−1)(t−1), v = B(w) = ∫_3^w k
  have hu : ContinuousOn (fun w => ∫ t in w..((m : ℝ) + 2), fseq (m - 1) (t - 1))
      (Set.uIcc 3 ((m : ℝ) + 2)) := by
    have hprim : Continuous (fun w => ∫ t in w..((m : ℝ) + 2), fseq (m - 1) (t - 1)) := by
      have h1 : Continuous (fun w => ∫ t in ((m : ℝ) + 2)..w, fseq (m - 1) (t - 1)) :=
        intervalIntegral.continuous_primitive (fun a b => fseq_shift_ii (m - 1) a b) _
      have heq : (fun w => ∫ t in w..((m : ℝ) + 2), fseq (m - 1) (t - 1))
          = (fun w => - ∫ t in ((m : ℝ) + 2)..w, fseq (m - 1) (t - 1)) := by
        funext w; exact intervalIntegral.integral_symm _ w
      rw [heq]; exact h1.neg
    exact hprim.continuousOn
  have hv : ContinuousOn (fun w => ∫ τ in (3 : ℝ)..w, k τ) (Set.uIcc 3 ((m : ℝ) + 2)) := by
    apply intervalIntegral.continuousOn_primitive_interval
    rw [Set.uIcc_of_le hbc3]; exact hk_int
  have hminmax : Set.Ioo (min (3 : ℝ) ((m : ℝ) + 2)) (max (3 : ℝ) ((m : ℝ) + 2))
      = Set.Ioo 3 ((m : ℝ) + 2) := by rw [min_eq_left hbc3, max_eq_right hbc3]
  have huu' : ∀ w ∈ Set.Ioo (min (3 : ℝ) ((m : ℝ) + 2)) (max (3 : ℝ) ((m : ℝ) + 2)),
      HasDerivWithinAt (fun w => ∫ t in w..((m : ℝ) + 2), fseq (m - 1) (t - 1))
        (-fseq (m - 1) (w - 1)) (Set.Ioi w) w := by
    rw [hminmax]; intro w hw
    have hci : IntervalIntegrable (fun t => fseq (m - 1) (t - 1)) volume w ((m : ℝ) + 2) :=
      fseq_shift_ii (m - 1) w _
    have hIcc : Set.Icc (3 : ℝ) ((m : ℝ) + 2) ∈ nhds w := Icc_mem_nhds hw.1 hw.2
    have hcs : ContinuousAt (fun t => fseq (m - 1) (t - 1)) w := hshift_cont.continuousAt hIcc
    have hmeas : StronglyMeasurableAtFilter (fun t => fseq (m - 1) (t - 1)) (nhds w) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hshift_cont.mono Set.Ioo_subset_Icc_self) w hw
    exact (integral_hasDerivAt_left hci hmeas hcs).hasDerivWithinAt
  have hvv' : ∀ w ∈ Set.Ioo (min (3 : ℝ) ((m : ℝ) + 2)) (max (3 : ℝ) ((m : ℝ) + 2)),
      HasDerivWithinAt (fun w => ∫ τ in (3 : ℝ)..w, k τ) (k w) (Set.Ioi w) w := by
    rw [hminmax]; intro w hw
    have hwpos : (0 : ℝ) < w := by linarith [hw.1]
    have hsubw : Set.uIcc (3 : ℝ) w ⊆ Set.Ioi (0 : ℝ) := by
      rw [Set.uIcc_of_le hw.1.le]; intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1
    have hci : IntervalIntegrable k volume 3 w := (hk_ioi.mono hsubw).intervalIntegrable
    have hcw : ContinuousAt k w := hk_ioi.continuousAt (isOpen_Ioi.mem_nhds hwpos)
    have hmeas : StronglyMeasurableAtFilter k (nhds w) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hk_ioi.mono hIoosub) w hw
    exact (integral_hasDerivAt_right hci hmeas hcw).hasDerivWithinAt
  have hu' : IntervalIntegrable (fun w => -fseq (m - 1) (w - 1)) volume 3 ((m : ℝ) + 2) :=
    (fseq_shift_ii (m - 1) 3 _).neg
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv huu' hvv' hu' hk_ii
  -- boundary terms vanish
  have hAtop : (∫ t in ((m : ℝ) + 2)..((m : ℝ) + 2), fseq (m - 1) (t - 1)) = 0 :=
    intervalIntegral.integral_same
  have hBbot : (∫ τ in (3 : ℝ)..(3 : ℝ), k τ) = 0 := intervalIntegral.integral_same
  rw [hAtop, hBbot] at hibp
  simp only [zero_mul, mul_zero, sub_zero, zero_sub] at hibp
  -- assemble
  rw [hchange, htail, hibp]
  -- RHS: -∫ (-fseq(m−1)(w−1))·B(w) = ∫ fseq(m−1)(w−1)·Φ(w−1) → sub v = w−1
  have hBphi : ∀ w, (∫ τ in (3 : ℝ)..w, k τ) = Phi (w - 1) := by
    intro w; unfold Phi; rw [hk]; congr 1; ring
  -- the change of variables v = w − 1 on the Φ-moment
  have hCV : (∫ w in (3 : ℝ)..((m : ℝ) + 2), fseq (m - 1) (w - 1) * Phi (w - 1))
      = ∫ v in (2 : ℝ)..((m : ℝ) + 1), fseq (m - 1) v * Phi v := by
    have h := intervalIntegral.integral_comp_sub_right
      (fun v => fseq (m - 1) v * Phi v) (1 : ℝ) (a := 3) (b := (m : ℝ) + 2)
    rw [show (3 : ℝ) - 1 = 2 by norm_num, show ((m : ℝ) + 2) - 1 = (m : ℝ) + 1 by ring] at h
    exact h
  -- fold the inner primitive into Φ and pull out the sign
  have hinner : (∫ w in (3 : ℝ)..((m : ℝ) + 2),
        -fseq (m - 1) (w - 1) * ∫ τ in (3 : ℝ)..w, k τ)
      = -(∫ w in (3 : ℝ)..((m : ℝ) + 2), fseq (m - 1) (w - 1) * Phi (w - 1)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr; intro w _
    simp only [hBphi]; ring
  rw [hinner, hCV, neg_neg]

/-- **The mass recursion in Φ-moment form.**  Composing `MassCert.massE_flat_split` with the
Φ-moment identity: for odd `m ≥ 3`,

  `massE (m+1) = massE (m−1)·cflatI + ∫_2^{m+1} fseq (m−1) (v)·Φ v dv`.

The even mass is the flat coefficient on its even predecessor's mass, plus a `Φ`-weighted moment of
that same predecessor. -/
theorem massE_eq_flat_phiMoment {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    massE (m + 1) = massE (m - 1) * cflatI
      + ∫ v in (2 : ℝ)..((m : ℝ) + 1), fseq (m - 1) v * Phi v := by
  rw [massE_flat_split hm hm3, massTail_eq_phiMoment hm hm3]

/-! ## The `[2,4]` closed evaluation: the fixed constants `Cφ1`, `Cφ2` -/

/-- Continuity of the integrand of `Φ` on the positive axis. -/
private theorem phi_k_cont :
    ContinuousOn (fun τ : ℝ => Real.log ((τ + 1) / 2) / τ) (Set.Ioi (0 : ℝ)) := by
  apply ContinuousOn.div (ContinuousOn.log (by fun_prop) ?_) (by fun_prop) ?_
  · intro τ hτ; have hτ0 : (0 : ℝ) < τ := hτ; exact (by positivity : (0 : ℝ) < (τ + 1) / 2).ne'
  · intro τ hτ; exact (show (0 : ℝ) < τ from hτ).ne'

/-- `Φ` is continuous on `[2,4]` (a primitive of the continuous integrand, composed with `·+1`). -/
theorem Phi_continuousOn : ContinuousOn Phi (Set.Icc (2 : ℝ) 4) := by
  have hint : MeasureTheory.IntegrableOn
      (fun τ : ℝ => Real.log ((τ + 1) / 2) / τ) (Set.Icc 3 5) volume :=
    (phi_k_cont.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1)).integrableOn_Icc
  have hprim : ContinuousOn (fun x => ∫ τ in (3 : ℝ)..x, Real.log ((τ + 1) / 2) / τ)
      (Set.uIcc 3 5) :=
    intervalIntegral.continuousOn_primitive_interval
      (by rw [Set.uIcc_of_le (by norm_num)]; exact hint)
  have hPhi : Phi = fun v => (fun x => ∫ τ in (3 : ℝ)..x, Real.log ((τ + 1) / 2) / τ) (v + 1) := by
    funext v; rfl
  rw [hPhi]
  exact hprim.comp (by fun_prop)
    (fun v hv => by rw [Set.uIcc_of_le (by norm_num)]
                    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩)

/-- **The `[2,4]` flat-log constant.**  `Cφ1 = ∫_2^4 Φ v·(log 3 − log (v−1))/v dv` (true `0.04403`),
the coefficient of `massE (m−3)` in the `Φ`-moment's `[2,4]` piece. -/
noncomputable def Cphi1 : ℝ := ∫ v in (2 : ℝ)..4, Phi v * (Real.log 3 - Real.log (v - 1)) / v

/-- **The `[2,4]` tail-mass constant.**  `Cφ2 = ∫_2^4 Φ v/v dv` (true `0.14127`), the coefficient of
`massO (m−2)` in the `Φ`-moment's `[2,4]` piece. -/
noncomputable def Cphi2 : ℝ := ∫ v in (2 : ℝ)..4, Phi v / v

/-- **A rational linear majorant of `Φ` on `[2,4]`.**  `Φ v ≤ (2/5)·(v−2)`, from
`log((w+1)/2)/w ≤ (w−1)/(2w) ≤ 2/5` on `[3,5]` (`log x ≤ x−1`, then `w ≤ 5`). -/
theorem Phi_le_lin {v : ℝ} (hv2 : 2 ≤ v) (hv4 : v ≤ 4) : Phi v ≤ (2 / 5) * (v - 2) := by
  have hb : (3 : ℝ) ≤ v + 1 := by linarith
  have hsub : Set.uIcc (3 : ℝ) (v + 1) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hb]; intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1
  have hii : IntervalIntegrable (fun w => Real.log ((w + 1) / 2) / w) volume 3 (v + 1) :=
    (phi_k_cont.mono hsub).intervalIntegrable
  have hmono : Phi v ≤ ∫ _w in (3 : ℝ)..(v + 1), (2 / 5 : ℝ) := by
    unfold Phi
    apply intervalIntegral.integral_mono_on hb hii _root_.intervalIntegrable_const
    intro w hw
    have hw3 : (3 : ℝ) ≤ w := hw.1
    have hw5 : w ≤ 5 := by linarith [hw.2]
    have hw0 : (0 : ℝ) < w := by linarith
    have hlog : Real.log ((w + 1) / 2) ≤ (w - 1) / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (w + 1) / 2 by linarith); linarith
    rw [div_le_iff₀ hw0]; nlinarith [hlog, hw5, hw3]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  nlinarith [hmono]

/-- `Cφ1 ≥ 0` (nonnegative integrand on `[2,4]`). -/
theorem Cphi1_nonneg : 0 ≤ Cphi1 := by
  unfold Cphi1
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro v hv
  have hv2 : (2 : ℝ) ≤ v := hv.1
  have hv4 : v ≤ 4 := hv.2
  apply div_nonneg (mul_nonneg (Phi_nonneg hv2) ?_) (by linarith)
  have : Real.log (v - 1) ≤ Real.log 3 :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

/-- `Cφ2 ≥ 0` (nonnegative integrand on `[2,4]`). -/
theorem Cphi2_nonneg : 0 ≤ Cphi2 := by
  unfold Cphi2
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro v hv
  exact div_nonneg (Phi_nonneg hv.1) (by linarith [hv.1])

/-- The integral of the linear majorant, `∫_2^4 c·(v−2) dv = 2c`. -/
private theorem integral_lin (c : ℝ) : (∫ v in (2 : ℝ)..4, c * (v - 2)) = 2 * c := by
  have hcongr : (∫ v in (2 : ℝ)..4, c * (v - 2)) = ∫ v in (2 : ℝ)..4, (c * v - 2 * c) := by
    apply intervalIntegral.integral_congr; intro v _; simp only []; ring
  have h1 : IntervalIntegrable (fun v : ℝ => c * v) volume 2 4 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun _ : ℝ => 2 * c) volume 2 4 := _root_.intervalIntegrable_const
  rw [hcongr, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    _root_.integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]; ring

/-- **Certified rational bound.**  `Cφ2 ≤ 2/5` (true `0.14127`; the loose majorant `Φ v/v ≤
(1/5)(v−2)` suffices — these constants are not load-bearing given the flagged contraction). -/
theorem Cphi2_le : Cphi2 ≤ 2 / 5 := by
  unfold Cphi2
  have hintP : IntervalIntegrable (fun v => Phi v / v) volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    refine Phi_continuousOn.div continuousOn_id ?_
    intro v hv; exact (show (0 : ℝ) < v by linarith [hv.1]).ne'
  have hintL : IntervalIntegrable (fun v => (1 / 5 : ℝ) * (v - 2)) volume 2 4 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hmono : (∫ v in (2 : ℝ)..4, Phi v / v) ≤ ∫ v in (2 : ℝ)..4, (1 / 5 : ℝ) * (v - 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hintP hintL
    intro v hv
    have hv2 : (2 : ℝ) ≤ v := hv.1
    have hv4 : v ≤ 4 := hv.2
    have hv0 : (0 : ℝ) < v := by linarith
    rw [div_le_iff₀ hv0]
    nlinarith [Phi_le_lin hv2 hv4, sq_nonneg (v - 2)]
  rw [integral_lin (1 / 5)] at hmono; linarith

/-- **Certified rational bound.**  `Cφ1 ≤ 4/5` (true `0.04403`).  Via `Φ v ≤ (2/5)(v−2)`,
`log 3 − log (v−1) ≤ 2` (`log 3 ≤ 2`), `1/v ≤ 1/2`, integrated against the linear majorant. -/
theorem Cphi1_le : Cphi1 ≤ 4 / 5 := by
  unfold Cphi1
  have hintP : IntervalIntegrable (fun v => Phi v * (Real.log 3 - Real.log (v - 1)) / v)
      volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    refine ContinuousOn.div (Phi_continuousOn.mul (continuousOn_const.sub ?_)) continuousOn_id ?_
    · apply ContinuousOn.log (by fun_prop)
      intro v hv; have hv2 : (2 : ℝ) ≤ v := hv.1
      intro h; rw [sub_eq_zero] at h; linarith
    · intro v hv; exact (show (0 : ℝ) < v by linarith [hv.1]).ne'
  have hintL : IntervalIntegrable (fun v => (2 / 5 : ℝ) * (v - 2)) volume 2 4 := by
    apply ContinuousOn.intervalIntegrable; fun_prop
  have hmono : (∫ v in (2 : ℝ)..4, Phi v * (Real.log 3 - Real.log (v - 1)) / v)
      ≤ ∫ v in (2 : ℝ)..4, (2 / 5 : ℝ) * (v - 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hintP hintL
    intro v hv
    have hv2 : (2 : ℝ) ≤ v := hv.1
    have hv4 : v ≤ 4 := hv.2
    have hv0 : (0 : ℝ) < v := by linarith
    have hp := Phi_nonneg hv2
    have hpl := Phi_le_lin hv2 hv4
    have hlog0 : 0 ≤ Real.log 3 - Real.log (v - 1) := by
      have : Real.log (v - 1) ≤ Real.log 3 := Real.log_le_log (by linarith) (by linarith)
      linarith
    have hlog2 : Real.log 3 - Real.log (v - 1) ≤ 2 := by
      have h3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
      have hv1 : 0 ≤ Real.log (v - 1) := Real.log_nonneg (by linarith)
      linarith
    rw [div_le_iff₀ hv0]
    nlinarith [mul_le_mul hpl hlog2 hlog0 (show (0 : ℝ) ≤ (2 / 5) * (v - 2) by nlinarith),
      sq_nonneg (v - 2), hp, hlog0]
  rw [integral_lin (2 / 5)] at hmono; linarith

end Salt.Chen
