/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# C1a — The Rosser-chain `fₙ` definitions and the elementary recursion

This file formalises the elementary Rosser-chain series `fₙ` of Bordignon,
Johnston, Starichkova (*An explicit version of Chen's theorem and the linear
sieve*, arXiv:2207.09452v6, henceforth **BJS**), their equations (13)–(20),
as **plain real functions** — no sieve dependency.  The two linear-sieve
functions `F, f` are then the truncated chains `Fchain`, `fchain`.

## The recursion (BJS (15)–(17), transcribed at page-image level)

* (15)  `s·f₁(s) := 3 − s`   for `1 ≤ s ≤ 3`;   `0` for `s > 3`.
* (16)  for `n ≥ 2` even and `s ≥ 2`, or `n ≥ 3` odd and `s ≥ 3`:
        `s·fₙ(s) := ∫_s^∞ f_{n−1}(t − 1) dt`.
* (17)  odd-`n` flattening: for `n ≥ 3` odd and `1 ≤ s ≤ 3`,
        `s·fₙ(s) := 3·fₙ(3) = ∫_3^∞ f_{n−1}(t − 1) dt`  (constant on `[1,3]`).

The improper `∫_s^∞` is realised as a finite `intervalIntegral` with upper
endpoint `n + 2` (for `fseq n`), because `fₙ` vanishes for `s ≥ n + 2`
(`fseq_eq_zero_of_ge`), so the integrand `f_{n−1}(t−1)` vanishes for
`t ≥ (n−1) + 2 + 1 = n + 2`.  Concretely, `fseq (n+1)` integrates up to
`(n : ℝ) + 3 = (n+1) + 2`.

## Indexing / junk-value conventions

`fseq n` is BJS's `fₙ` (index starts at 1); `fseq 0 = 0` is an unused padding
value (never enters either parity sum).  Each `fseq n` is **total**: outside its
`s`-window the value is the junk constant `0` (documented in every branch).  The
window is `s ≥ 1` for odd `n` (flattened on `[1,3]`), `s ≥ 2` for even `n`.

## Catch #24 (the parity fix)

BJS's *printed* eq. (14) sums over `n` **odd** — the same parity as (13) —
which would force `F + f ≡ 2`, contradicting their (8).  The **correct**
definition sums over `n` **even**:
`f(s) = 1 − Σ_{n even} fₙ(s)`.  `fchain` below uses the even-`n` sum;
`Fchain` uses the odd-`n` sum.  `Fchain_add_fchain` and
`Fchain_add_fchain_one_ne_two` document the fix as a regression witness.
-/

namespace Salt.Chen

open intervalIntegral MeasureTheory Set

/-- The Rosser chain `fₙ` of BJS (13)–(17), realised as a total real function.
`fseq 0 = 0` (unused padding); `fseq 1 = f₁` from (15); `fseq (n+1)` for `n ≥ 1`
is the integral recursion (16)/(17), with the improper upper limit realised as
`(n : ℝ) + 3 = (n+1) + 2` (the support bound of `fseq n (·-1)`).  Junk value `0`
outside the `s`-window in every branch. -/
noncomputable def fseq : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | (n + 1) => fun s =>
      if n = 0 then
        -- f₁, BJS (15)
        if 1 ≤ s ∧ s ≤ 3 then (3 - s) / s else 0
      else if Even (n + 1) then
        -- even n+1 ≥ 2, window s ≥ 2, BJS (16)
        if 2 ≤ s then (1 / s) * ∫ t in s..((n : ℝ) + 3), fseq n (t - 1) else 0
      else
        -- odd n+1 ≥ 3, window s ≥ 1, BJS (16) on [3,∞), (17) flattening on [1,3]
        if 3 ≤ s then (1 / s) * ∫ t in s..((n : ℝ) + 3), fseq n (t - 1)
        else if 1 ≤ s then (1 / s) * ∫ t in (3 : ℝ)..((n : ℝ) + 3), fseq n (t - 1)
        else 0

/-! ### Unfolding lemmas -/

@[simp] theorem fseq_zero (s : ℝ) : fseq 0 s = 0 := rfl

/-- `f₁` in raw `if` form (BJS (15)). -/
theorem fseq_one_eq (s : ℝ) :
    fseq 1 s = if 1 ≤ s ∧ s ≤ 3 then (3 - s) / s else 0 := rfl

/-- `f₁` on its window `[1,3]`: `f₁(s) = (3 − s)/s`. -/
theorem fseq_one_window {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    fseq 1 s = (3 - s) / s := by
  rw [fseq_one_eq, if_pos ⟨hs1, hs3⟩]

/-- Even step (BJS (16)) on the window `s ≥ 2`. -/
theorem fseq_even_window {n : ℕ} (hn : Even (n + 1)) {s : ℝ} (hs : 2 ≤ s) :
    fseq (n + 1) s = (1 / s) * ∫ t in s..((n : ℝ) + 3), fseq n (t - 1) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  simp only [fseq]
  rw [if_neg hn0, if_pos hn, if_pos hs]

/-- Even step below the window (`s < 2`): junk value `0`. -/
theorem fseq_even_below {n : ℕ} (hn : Even (n + 1)) {s : ℝ} (hs : s < 2) :
    fseq (n + 1) s = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  simp only [fseq]
  rw [if_neg hn0, if_pos hn, if_neg (not_le.mpr hs)]

/-- Odd step (BJS (16)) on the tail `s ≥ 3`. -/
theorem fseq_odd_tail_window {n : ℕ} (hn0 : n ≠ 0) (hodd : ¬ Even (n + 1))
    {s : ℝ} (hs : 3 ≤ s) :
    fseq (n + 1) s = (1 / s) * ∫ t in s..((n : ℝ) + 3), fseq n (t - 1) := by
  simp only [fseq]
  rw [if_neg hn0, if_neg hodd, if_pos hs]

/-- Odd step, the (17) flattening on `[1,3)`: constant `= 3·fₙ(3)`. -/
theorem fseq_odd_flat_window {n : ℕ} (hn0 : n ≠ 0) (hodd : ¬ Even (n + 1))
    {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s < 3) :
    fseq (n + 1) s = (1 / s) * ∫ t in (3 : ℝ)..((n : ℝ) + 3), fseq n (t - 1) := by
  simp only [fseq]
  rw [if_neg hn0, if_neg hodd, if_neg (not_le.mpr hs3), if_pos hs1]

/-- Odd step below the window (`s < 1`): junk value `0`. -/
theorem fseq_odd_below {n : ℕ} (hn0 : n ≠ 0) (hodd : ¬ Even (n + 1))
    {s : ℝ} (hs : s < 1) :
    fseq (n + 1) s = 0 := by
  simp only [fseq]
  rw [if_neg hn0, if_neg hodd, if_neg (not_le.mpr (by linarith : s < 3)),
    if_neg (not_le.mpr hs)]

/-! ### Support bound: `fₙ` vanishes past `n + 2` -/

/-- `fₙ(s) = 0` for `s ≥ n + 2` (each iterate is supported on `[·, n+2]`).
This makes the finite `intervalIntegral` upper limit `(n : ℝ) + 3` faithful to
BJS's improper `∫_s^∞`. -/
theorem fseq_eq_zero_of_ge : ∀ (n : ℕ) (s : ℝ), (n : ℝ) + 2 ≤ s → fseq n s = 0 := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ m ih =>
    intro s hs
    have hs' : (m : ℝ) + 3 ≤ s := by push_cast at hs; linarith
    -- the integral over `[s, m+3]` (backwards, since `s ≥ m+3`) is zero
    have hzero : (∫ t in s..((m : ℝ) + 3), fseq m (t - 1)) = 0 := by
      have hcongr : (∫ t in s..((m : ℝ) + 3), fseq m (t - 1))
          = ∫ _t in s..((m : ℝ) + 3), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hs'] at ht
        exact ih (t - 1) (by have := ht.1; linarith)
      rw [hcongr, intervalIntegral.integral_zero]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- m = 0 : this is f₁, and s ≥ 3
      subst hm
      rw [fseq_one_eq]
      have hs3 : (3 : ℝ) ≤ s := by push_cast at hs'; linarith
      split_ifs with h
      · have : s = 3 := le_antisymm h.2 hs3
        rw [this]; norm_num
      · rfl
    · -- m ≥ 1
      have hm0 : m ≠ 0 := hm.ne'
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      by_cases hev : Even (m + 1)
      · rw [fseq_even_window hev (by linarith), hzero, mul_zero]
      · rw [fseq_odd_tail_window hm0 hev (by linarith), hzero, mul_zero]

/-! ### Nonnegativity -/

/-- Every iterate is nonnegative (junk `0` outside its window is `≥ 0`; on the
window `f₁ = (3−s)/s ≥ 0` and each integral is of a nonnegative integrand). -/
theorem fseq_nonneg : ∀ (n : ℕ) (s : ℝ), 0 ≤ fseq n s := by
  intro n
  induction n with
  | zero => intro s; rw [fseq_zero]
  | succ m ih =>
    intro s
    by_cases hle : s ≤ (m : ℝ) + 3
    · -- s ≤ m+3 : bulk region, integrals are correctly oriented
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [fseq_one_eq]
        split_ifs with h
        · exact div_nonneg (by linarith [h.2]) (by linarith [h.1])
        · rfl
      · have hm0 : m ≠ 0 := hm.ne'
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        by_cases hev : Even (m + 1)
        · by_cases hs2 : 2 ≤ s
          · rw [fseq_even_window hev hs2]
            have hspos : (0 : ℝ) < s := by linarith
            exact mul_nonneg (div_nonneg zero_le_one hspos.le)
              (intervalIntegral.integral_nonneg hle (fun t _ => ih (t - 1)))
          · rw [fseq_even_below hev (not_le.mp hs2)]
        · by_cases hs3 : 3 ≤ s
          · rw [fseq_odd_tail_window hm0 hev hs3]
            have hspos : (0 : ℝ) < s := by linarith
            exact mul_nonneg (div_nonneg zero_le_one hspos.le)
              (intervalIntegral.integral_nonneg hle (fun t _ => ih (t - 1)))
          · by_cases hs1 : 1 ≤ s
            · rw [fseq_odd_flat_window hm0 hev hs1 (not_le.mp hs3)]
              have hspos : (0 : ℝ) < s := by linarith
              exact mul_nonneg (div_nonneg zero_le_one hspos.le)
                (intervalIntegral.integral_nonneg (by linarith) (fun t _ => ih (t - 1)))
            · rw [fseq_odd_below hm0 hev (not_le.mp hs1)]
    · -- s > m+3 = (m+1)+2 : the iterate is already zero
      have hgt : (m : ℝ) + 3 < s := not_le.mp hle
      rw [fseq_eq_zero_of_ge (m + 1) s (by push_cast; linarith)]

/-! ### First values in closed form

`fseq 1` is already `(3 − s)/s` on `[1,3]` (`fseq_one_window`).  Here is
`fseq 2` (BJS (19)) from one integration — the gate's spot-check anchor. -/

/-- `f₂` on its window `[2,4]` (BJS (19)):
`f₂(s) = (s − 3·log(s−1) + 3·log 3 − 4)/s`.  Obtained from one `intervalIntegral`
of `f₁`. -/
theorem fseq_two_window {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    fseq 2 s = (s - 3 * Real.log (s - 1) + 3 * Real.log 3 - 4) / s := by
  have hev : Even (1 + 1) := by decide
  change fseq (1 + 1) s = (s - 3 * Real.log (s - 1) + 3 * Real.log 3 - 4) / s
  rw [fseq_even_window hev hs2]
  have hup : ((1 : ℕ) : ℝ) + 3 = 4 := by norm_num
  rw [hup]
  have hcongr : (∫ t in s..(4 : ℝ), fseq 1 (t - 1))
      = ∫ t in s..(4 : ℝ), (4 - t) / (t - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hs4] at ht
    have ht1 : (1 : ℝ) ≤ t - 1 := by have := ht.1; linarith
    have ht3 : t - 1 ≤ 3 := by have := ht.2; linarith
    change fseq 1 (t - 1) = (4 - t) / (t - 1)
    rw [fseq_one_window ht1 ht3]
    congr 1; ring
  rw [hcongr]
  have hderiv : ∀ t ∈ uIcc s (4 : ℝ),
      HasDerivAt (fun u => 3 * Real.log (u - 1) - u) ((4 - t) / (t - 1)) t := by
    intro t ht
    rw [uIcc_of_le hs4] at ht
    have ht1 : (0 : ℝ) < t - 1 := by have := ht.1; linarith
    have h1ne : (t - 1) ≠ 0 := ht1.ne'
    have hd1 : HasDerivAt (fun u : ℝ => u - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have hlog : HasDerivAt (fun u : ℝ => Real.log (u - 1)) (1 / (t - 1)) t := by
      simpa using hd1.log h1ne
    have hval : (3 : ℝ) * (1 / (t - 1)) - 1 = (4 - t) / (t - 1) := by field_simp; ring
    have hcomb : HasDerivAt (fun u => 3 * Real.log (u - 1) - u) (3 * (1 / (t - 1)) - 1) t :=
      (hlog.const_mul 3).sub (hasDerivAt_id t)
    rw [hval] at hcomb
    exact hcomb
  have hint : IntervalIntegrable (fun t => (4 - t) / (t - 1)) volume s 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact (continuous_id.sub continuous_const).continuousOn
    · intro t ht
      rw [uIcc_of_le hs4] at ht
      have := ht.1
      intro h; nlinarith
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hspos : (0 : ℝ) < s := by linarith
  have h43 : (4 : ℝ) - 1 = 3 := by norm_num
  simp only [h43]
  field_simp
  ring

/-! ### A monotonicity witness

`f₁` is antitone on its window (`f₁(s) = 3/s − 1`).  The general iterate
`s ↦ s·fₙ(s)` is antitone on its window too — its integral form
`∫_s^{n+2} fₙ₋₁(t−1) dt` decreases in `s` because the integrand is nonnegative
(`fseq_nonneg`) and integrable (`fseq_shift_intervalIntegrable`) — but that fact
is not needed downstream, so only the base witness is recorded here. -/
theorem fseq_one_antitoneOn : AntitoneOn (fseq 1) (Set.Icc 1 3) := by
  intro x hx y hy hxy
  rw [fseq_one_window hx.1 hx.2, fseq_one_window hy.1 hy.2]
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have expand : (3 - x) / x - (3 - y) / y = 3 * (y - x) / (x * y) := by
    field_simp; ring
  have hge : 0 ≤ (3 - x) / x - (3 - y) / y := by
    rw [expand]
    exact div_nonneg (by nlinarith) (mul_pos hx0 hy0).le
  linarith

/-! ### Structural facts: measurability, boundedness, integrability

Bundled joint induction, then the three consumer-facing projections plus the
shifted form `fₙ(·−1)` that the *next* level's `intervalIntegral` integrates. -/

/-- Joint induction: each iterate is measurable, globally bounded, and interval
integrable on every interval.  (These are coupled: the primitive of `fₙ(·−1)` is
continuous only once `fₙ` is interval integrable, which in turn needs `fₙ`
measurable and bounded.) -/
theorem fseq_props : ∀ (n : ℕ),
    Measurable (fseq n)
    ∧ (∃ C, 0 ≤ C ∧ ∀ s, |fseq n s| ≤ C)
    ∧ (∀ a b, IntervalIntegrable (fseq n) volume a b) := by
  intro n
  induction n with
  | zero =>
    refine ⟨measurable_const, ⟨0, le_refl _, ?_⟩, ?_⟩
    · intro s; rw [fseq_zero]; simp
    · intro a b; exact _root_.intervalIntegrable_const
  | succ m ih =>
    obtain ⟨hMeas, ⟨C, hC0, hC⟩, hII⟩ := ih
    have hshift : ∀ a b, IntervalIntegrable (fun t => fseq m (t - 1)) volume a b := by
      intro a b
      simpa using (hII (a - 1) (b - 1)).comp_sub_right 1
    have hprim : Continuous (fun s => ∫ t in ((m : ℝ) + 3)..s, fseq m (t - 1)) :=
      intervalIntegral.continuous_primitive hshift ((m : ℝ) + 3)
    have hIntMeas : Measurable (fun s => ∫ t in s..((m : ℝ) + 3), fseq m (t - 1)) := by
      have heq : (fun s => ∫ t in s..((m : ℝ) + 3), fseq m (t - 1))
          = (fun s => - ∫ t in ((m : ℝ) + 3)..s, fseq m (t - 1)) := by
        funext s; exact intervalIntegral.integral_symm ((m : ℝ) + 3) s
      rw [heq]; exact hprim.neg.measurable
    have hV : Measurable (fun s => (1 / s) * ∫ t in s..((m : ℝ) + 3), fseq m (t - 1)) :=
      (measurable_const.div measurable_id).mul hIntMeas
    have hVflat :
        Measurable (fun s : ℝ => (1 / s) * ∫ t in (3 : ℝ)..((m : ℝ) + 3), fseq m (t - 1)) :=
      (measurable_const.div measurable_id).mul measurable_const
    -- (1) measurability
    have hMeas1 : Measurable (fseq (m + 1)) := by
      by_cases hm0 : m = 0
      · subst hm0
        have hfun : fseq 1 = fun s => if 1 ≤ s ∧ s ≤ 3 then (3 - s) / s else 0 :=
          funext fseq_one_eq
        rw [hfun]
        refine Measurable.ite ?_ ((measurable_const.sub measurable_id).div measurable_id)
          measurable_const
        exact measurableSet_Icc
      · by_cases hev : Even (m + 1)
        · have hfun : fseq (m + 1) = fun s =>
              if 2 ≤ s then (1 / s) * ∫ t in s..((m : ℝ) + 3), fseq m (t - 1)
              else 0 := by
            funext s
            by_cases hs : 2 ≤ s
            · rw [fseq_even_window hev hs, if_pos hs]
            · rw [fseq_even_below hev (not_le.mp hs), if_neg hs]
          rw [hfun]
          exact Measurable.ite measurableSet_Ici hV measurable_const
        · have hfun : fseq (m + 1)
              = fun s => if 3 ≤ s then (1 / s) * ∫ t in s..((m : ℝ) + 3), fseq m (t - 1)
                  else if 1 ≤ s then (1 / s) * ∫ t in (3 : ℝ)..((m : ℝ) + 3), fseq m (t - 1)
                  else 0 := by
            funext s
            by_cases hs3 : 3 ≤ s
            · rw [fseq_odd_tail_window hm0 hev hs3, if_pos hs3]
            · by_cases hs1 : 1 ≤ s
              · rw [fseq_odd_flat_window hm0 hev hs1 (not_le.mp hs3), if_neg hs3, if_pos hs1]
              · rw [fseq_odd_below hm0 hev (not_le.mp hs1), if_neg hs3, if_neg hs1]
          rw [hfun]
          exact Measurable.ite measurableSet_Ici hV
            (Measurable.ite measurableSet_Ici hVflat measurable_const)
    -- (2) global bound
    have hBnd1 : ∃ C', 0 ≤ C' ∧ ∀ s, |fseq (m + 1) s| ≤ C' := by
      have hbnd : ∀ (lo : ℝ), 0 ≤ lo → lo ≤ (m : ℝ) + 3 →
          |∫ t in lo..((m : ℝ) + 3), fseq m (t - 1)| ≤ C * ((m : ℝ) + 3) := by
        intro lo hlo0 hlohi
        have hnb : ‖∫ t in lo..((m : ℝ) + 3), fseq m (t - 1)‖
            ≤ C * |((m : ℝ) + 3) - lo| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun t _ => by rw [Real.norm_eq_abs]; exact hC (t - 1))
        rw [Real.norm_eq_abs] at hnb
        refine hnb.trans ?_
        apply mul_le_mul_of_nonneg_left _ hC0
        rw [abs_of_nonneg (by linarith)]
        linarith
      by_cases hm0 : m = 0
      · subst hm0
        refine ⟨2, by norm_num, fun s => ?_⟩
        rw [fseq_one_eq]
        split_ifs with h
        · rw [abs_le]
          have hs0 : (0 : ℝ) < s := by linarith [h.1]
          have hnn : 0 ≤ (3 - s) / s := div_nonneg (by linarith [h.2]) hs0.le
          refine ⟨by linarith, ?_⟩
          rw [div_le_iff₀ hs0]; linarith [h.1]
        · simp
      · refine ⟨C * ((m : ℝ) + 3), mul_nonneg hC0 (by positivity), fun s => ?_⟩
        by_cases hbig : (m : ℝ) + 3 ≤ s
        · rw [fseq_eq_zero_of_ge (m + 1) s (by push_cast; linarith)]
          simpa using mul_nonneg hC0 (by positivity : (0 : ℝ) ≤ (m : ℝ) + 3)
        · replace hbig := not_le.mp hbig
          by_cases hev : Even (m + 1)
          · by_cases hs2 : 2 ≤ s
            · have hs0 : (0 : ℝ) < s := by linarith
              rw [fseq_even_window hev hs2, abs_mul]
              have h1s : |1 / s| ≤ 1 := by
                rw [abs_of_pos (one_div_pos.mpr hs0), div_le_one hs0]; linarith
              calc |1 / s| * |∫ t in s..((m : ℝ) + 3), fseq m (t - 1)|
                  ≤ 1 * (C * ((m : ℝ) + 3)) :=
                    mul_le_mul h1s (hbnd s (by linarith) hbig.le) (abs_nonneg _) zero_le_one
                _ = C * ((m : ℝ) + 3) := one_mul _
            · rw [fseq_even_below hev (not_le.mp hs2)]
              simpa using mul_nonneg hC0 (by positivity : (0 : ℝ) ≤ (m : ℝ) + 3)
          · by_cases hs3 : 3 ≤ s
            · have hs0 : (0 : ℝ) < s := by linarith
              rw [fseq_odd_tail_window hm0 hev hs3, abs_mul]
              have h1s : |1 / s| ≤ 1 := by
                rw [abs_of_pos (one_div_pos.mpr hs0), div_le_one hs0]; linarith
              calc |1 / s| * |∫ t in s..((m : ℝ) + 3), fseq m (t - 1)|
                  ≤ 1 * (C * ((m : ℝ) + 3)) :=
                    mul_le_mul h1s (hbnd s (by linarith) hbig.le) (abs_nonneg _) zero_le_one
                _ = C * ((m : ℝ) + 3) := one_mul _
            · by_cases hs1 : 1 ≤ s
              · have hs0 : (0 : ℝ) < s := by linarith
                rw [fseq_odd_flat_window hm0 hev hs1 (not_le.mp hs3), abs_mul]
                have h1s : |1 / s| ≤ 1 := by
                  rw [abs_of_pos (one_div_pos.mpr hs0), div_le_one hs0]; linarith
                calc |1 / s| * |∫ t in (3 : ℝ)..((m : ℝ) + 3), fseq m (t - 1)|
                    ≤ 1 * (C * ((m : ℝ) + 3)) :=
                      mul_le_mul h1s (hbnd 3 (by norm_num)
                        (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
                        (abs_nonneg _) zero_le_one
                  _ = C * ((m : ℝ) + 3) := one_mul _
              · rw [fseq_odd_below hm0 hev (not_le.mp hs1)]
                simpa using mul_nonneg hC0 (by positivity : (0 : ℝ) ≤ (m : ℝ) + 3)
    -- (3) interval integrability from measurable + bounded
    refine ⟨hMeas1, hBnd1, fun a b => ?_⟩
    obtain ⟨C', _, hC'⟩ := hBnd1
    rw [intervalIntegrable_iff]
    apply Measure.integrableOn_of_bounded _ hMeas1.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun s => by rw [Real.norm_eq_abs]; exact hC' s))
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top

/-- Each iterate is Borel measurable. -/
theorem fseq_measurable (n : ℕ) : Measurable (fseq n) := (fseq_props n).1

/-- Each iterate is globally bounded. -/
theorem fseq_bounded (n : ℕ) : ∃ C, 0 ≤ C ∧ ∀ s, |fseq n s| ≤ C := (fseq_props n).2.1

/-- Each iterate is interval integrable on every interval (needed to form the
next level's `intervalIntegral`). -/
theorem fseq_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fseq n) volume a b := (fseq_props n).2.2 a b

/-- The shifted iterate `fₙ(·−1)` — the exact integrand of the level-`n+1`
recursion — is interval integrable on every interval. -/
theorem fseq_shift_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => fseq n (t - 1)) volume a b := by
  simpa using (fseq_intervalIntegrable n (a - 1) (b - 1)).comp_sub_right 1

/-! ### The truncated linear-sieve chains `F` and `f` (catch #24 parity)

BJS (13)/(14) as **finite** truncations at level `N` (the infinite series never
appear as Lean objects — C1b bounds the tails).  `Fchain` sums the **odd**-index
iterates; `fchain` subtracts the **even**-index iterates — the catch-#24
correction (the printed (14) wrongly sums odd, which would force `F + f ≡ 2`). -/

/-- `F_N(s) = 1 + Σ_{n ≤ N, n odd} fₙ(s)` — BJS (13), truncated at `N`. -/
noncomputable def Fchain (N : ℕ) (s : ℝ) : ℝ :=
  1 + ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Odd n), fseq n s

/-- `f_N(s) = 1 − Σ_{n ≤ N, n even} fₙ(s)` — BJS (14) **with the catch-#24
even-`n` parity** (`fseq 0 = 0` makes the `n = 0` term vacuous). -/
noncomputable def fchain (N : ℕ) (s : ℝ) : ℝ :=
  1 - ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Even n), fseq n s

/-- `F_N + f_N = 2 + (odd sum) − (even sum)`.  With the **correct** (even) parity
of `fchain` the two sums differ, so `F_N + f_N ≢ 2` in general; the printed-(14)
odd parity would collapse this to `≡ 2` (catch #24). -/
theorem Fchain_add_fchain (N : ℕ) (s : ℝ) :
    Fchain N s + fchain N s
      = 2 + (∑ n ∈ (Finset.range (N + 1)).filter (fun n => Odd n), fseq n s)
          - (∑ n ∈ (Finset.range (N + 1)).filter (fun n => Even n), fseq n s) := by
  simp only [Fchain, fchain]; ring

/-- Concrete regression witness for catch #24: `F₁(2) + f₁(2) = 5/2 ≠ 2`.
Under the printed odd-`n` (14) it would instead be `1 + f₁(2) + (1 − f₁(2)) = 2`.
The even-`n` correction makes the identity `F + f ≡ 2` genuinely fail. -/
theorem Fchain_add_fchain_one_ne_two : Fchain 1 2 + fchain 1 2 ≠ 2 := by
  have hodd : (Finset.range (1 + 1)).filter (fun n => Odd n) = {1} := by decide
  have heven : (Finset.range (1 + 1)).filter (fun n => Even n) = {0} := by decide
  have hf1 : fseq 1 2 = 1 / 2 := by rw [fseq_one_window (by norm_num) (by norm_num)]; norm_num
  simp only [Fchain, fchain, hodd, heven, Finset.sum_singleton, fseq_zero, hf1]
  norm_num

end Salt.Chen
