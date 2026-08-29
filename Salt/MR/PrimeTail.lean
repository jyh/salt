/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PrimeSigmaShift
import Salt.Mertens.Third

/-!
# MR-gate S8/R0.2 — discharging the prime `σ`-shift tail (`PrimeTailShiftBounded`)

This file closes the ONE analytic residual of `Salt/MR/PrimeSigmaShift.lean`, namely
`PrimeTailShiftBounded` : `∃ C, ∀ x ≥ e, ∑'_{p>x} p^{-1-1/log x} ≤ C`.

Route (dyadic, S8-E1 scout's recommended first route).  Fix `x ≥ e`, `L = log x ≥ 1`,
`δ = 1/L`.  The tail `∑_{p>x} p^{-1-δ} = ∑_{p>x} p^{-δ}·(1/p)` is partitioned into the
half-open dyadic windows `(2^k x, 2^{k+1} x]`, `k = 0, 1, 2, …`, indexed by
`blockIdx x p = ⌈(log p − log x)/log 2⌉ − 1`.  On window `k`:

* **decay**: `p ≥ 2^k x ⟹ p^{-δ} ≤ (2^k x)^{-δ} = e^{-1}·r^k`, `r = e^{-log 2 / L} ∈ (0,1)`;
* **Mertens**: the half-open tiling makes `∑ 1/p ≤ SPartial(2^{k+1} x) − SPartial(2^k x)`
  with NO boundary correction, and the sharp real Mertens-2
  (`Salt.Mertens.mertens_second_sharp_real`) at the two scales bounds this difference by
  `(log 2 + 24)/L` — the Meissel constant cancels, the `loglog` difference telescopes.

Summing the geometric series `∑_k r^k ≤ 1/(1−r) ≤ 2L/log 2` (from `1 − e^{-y} ≥ y e^{-y}`)
gives the absolute bound `primeTailConst = 2·e^{-1}·(log 2 + 24)/log 2 ≈ 26.2`.  The tsum is
reduced to these finite window sums by `Real.tsum_le_of_sum_range_le`.

Discharging the residual upgrades the H0 exit stones (`log_euler_osc_zeta`,
`euler_osc_bridge_le`, `euler_osc_bridge`) to UNCONDITIONAL, exported here as the
`*_unconditional` wrappers (the landed conditional stones applied to `prime_tail_shift`).
-/

namespace Salt.MR

open scoped BigOperators

/-- The dyadic block index of a prime `p` relative to base point `x`: the unique `k` with
`2^k x < p ≤ 2^{k+1} x`, i.e. `⌈(log p − log x)/log 2⌉ − 1`.  (`ℕ`-valued, so the fibers
`filter (blockIdx x · = k)` have a decidable predicate.) -/
noncomputable def blockIdx (x : ℝ) (p : ℕ) : ℕ :=
  ⌈(Real.log p - Real.log x) / Real.log 2⌉₊ - 1

/-- The certified absolute constant of the R0.2 tail bound,
`2·e^{-1}·(log 2 + 24)/log 2 ≈ 26.2`. -/
noncomputable def primeTailConst : ℝ :=
  Real.exp (-1) * (Real.log 2 + 24) * 2 / Real.log 2

/-- **A crude absolute majorant for `primeTailConst`: `≤ 27`.**

The true value is `2·e^{-1}·(log 2 + 24)/log 2 ≈ 26.21`.  Route: `e^{-1} ≤ 0.37` from
`Real.exp_one_gt_d9`, and the two-sided `log 2` bounds `Real.log_two_gt_d9` /
`Real.log_two_lt_d9`.  The LOWER bound on `log 2` is the load-bearing one — `log 2` sits
in the DENOMINATOR, so an upper bound alone does not close it.

WHY A CRUDE BOUND IS THE RIGHT ONE HERE.  Together with `cpeel_le_two` this is one of the
two numeral stones under the EFFECTIVE arms (`Kvk`, `Kbulk`) of the `cffKVt` pricing max;
the budget at that pricing site is of order `10^222`, so the ~0.8 of absolute slack is
free by ~180 orders of magnitude.  Sharpening to `≈ 26.22` is available from the same
three mathlib bounds at higher `nlinarith` cost and buys nothing. -/
theorem primeTailConst_le_27 : primeTailConst ≤ 27 := by
  have hlb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hub : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL : (0 : ℝ) < Real.log 2 := by linarith
  have hexp : Real.exp (-1) ≤ 0.37 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 0.37)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have hexp0 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  unfold primeTailConst
  rw [div_le_iff₀ hL]
  nlinarith [mul_nonneg (sub_nonneg.mpr hexp) hL.le, hexp0, hlb]

/-- `log (2^m · x) = m·log 2 + log x`, the workhorse cut-point identity. -/
theorem log_two_pow_mul {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.log ((2:ℝ)^m * x) = m * Real.log 2 + Real.log x := by
  rw [Real.log_mul (by positivity) hx.ne', Real.log_pow]

/-! ## Lemma 1 — the per-block Mertens difference bound -/

/-- **The dyadic block Mertens bound.**  For `e ≤ x` and every `k`,
`SPartial(2^{k+1} x) − SPartial(2^k x) ≤ (log 2 + 24)/log x`.  From the sharp real
Mertens-2 at the two scales: the Meissel constant cancels and the `loglog` difference
`≤ log 2 / log(2^k x) ≤ log 2 / log x`. -/
theorem mertens_block_diff_le {x : ℝ} (hx : Real.exp 1 ≤ x) (k : ℕ) :
    Salt.Mertens.SPartial ((2:ℝ)^(k+1) * x) - Salt.Mertens.SPartial ((2:ℝ)^k * x)
      ≤ (Real.log 2 + 24) / Real.log x := by
  have h2e : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hx2 : (2:ℝ) ≤ x := le_trans h2e hx
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0:ℝ) < Real.log x := by linarith
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1k : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  -- the two scales and their logs
  have ha2 : (2:ℝ) ≤ (2:ℝ)^k * x := by nlinarith [h1k, hx2, hxpos]
  have hb2 : (2:ℝ) ≤ (2:ℝ)^(k+1) * x := by
    have : (1:ℝ) ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    nlinarith [this, hx2, hxpos]
  have hLa : Real.log ((2:ℝ)^k * x) = k * Real.log 2 + Real.log x := log_two_pow_mul hxpos k
  have hLb : Real.log ((2:ℝ)^(k+1) * x) = ((k:ℝ) + 1) * Real.log 2 + Real.log x := by
    rw [log_two_pow_mul hxpos (k+1)]; push_cast; ring
  have hLapos : (0:ℝ) < Real.log ((2:ℝ)^k * x) := by
    rw [hLa]; have : (0:ℝ) ≤ (k:ℝ) * Real.log 2 := by positivity
    linarith
  have hLbeq : Real.log ((2:ℝ)^(k+1) * x) = Real.log ((2:ℝ)^k * x) + Real.log 2 := by
    rw [hLa, hLb]; ring
  have hLbpos : (0:ℝ) < Real.log ((2:ℝ)^(k+1) * x) := by rw [hLbeq]; linarith
  have hLage : Real.log x ≤ Real.log ((2:ℝ)^k * x) := by
    rw [hLa]; have : (0:ℝ) ≤ (k:ℝ) * Real.log 2 := by positivity
    linarith
  have hLbge : Real.log x ≤ Real.log ((2:ℝ)^(k+1) * x) := by rw [hLbeq]; linarith
  -- loglog difference ≤ log 2 / log(2^k x)
  have hratio : Real.log ((2:ℝ)^(k+1) * x) / Real.log ((2:ℝ)^k * x) - 1
      = Real.log 2 / Real.log ((2:ℝ)^k * x) := by
    rw [hLbeq, add_div, div_self hLapos.ne']; ring
  have hloglog : Real.log (Real.log ((2:ℝ)^(k+1) * x)) - Real.log (Real.log ((2:ℝ)^k * x))
      ≤ Real.log 2 / Real.log ((2:ℝ)^k * x) := by
    have hpos : (0:ℝ) < Real.log ((2:ℝ)^(k+1) * x) / Real.log ((2:ℝ)^k * x) :=
      div_pos hLbpos hLapos
    have := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div hLbpos.ne' hLapos.ne', hratio] at this
    exact this
  -- transfer to log x scale
  have hll : Real.log (Real.log ((2:ℝ)^(k+1) * x)) - Real.log (Real.log ((2:ℝ)^k * x))
      ≤ Real.log 2 / Real.log x := by
    refine le_trans hloglog ?_
    exact div_le_div_of_nonneg_left hlog2pos.le hLpos hLage
  have h12a : 12 / Real.log ((2:ℝ)^k * x) ≤ 12 / Real.log x :=
    div_le_div_of_nonneg_left (by norm_num) hLpos hLage
  have h12b : 12 / Real.log ((2:ℝ)^(k+1) * x) ≤ 12 / Real.log x :=
    div_le_div_of_nonneg_left (by norm_num) hLpos hLbge
  -- Mertens at the two scales
  have hMa := abs_le.mp (Salt.Mertens.mertens_second_sharp_real ha2)
  have hMb := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hb2)
  -- arithmetic assembly
  have hsplit : (Real.log 2 + 24) / Real.log x
      = Real.log 2 / Real.log x + 12 / Real.log x + 12 / Real.log x := by
    field_simp; ring
  linarith [hMa.1, hMa.2, hMb.1, hMb.2, hll, h12a, h12b, hsplit.ge, hsplit.le]

/-! ## Lemma 2a — the window characterization of `blockIdx` -/

/-- **Window characterization.**  If `x < p` and `blockIdx x p = k`, then
`2^k x < p ≤ 2^{k+1} x`. -/
theorem blockIdx_window {x : ℝ} (hx : Real.exp 1 ≤ x) {p k : ℕ}
    (hp : x < (p : ℝ)) (hk : blockIdx x p = k) :
    (2:ℝ)^k * x < (p : ℝ) ∧ (p : ℝ) ≤ (2:ℝ)^(k+1) * x := by
  have h2e : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hx1 : (1:ℝ) ≤ x := le_trans (by linarith : (1:ℝ) ≤ 2) (le_trans h2e hx)
  have hxpos : (0:ℝ) < x := by linarith
  have hppos : (0:ℝ) < (p:ℝ) := by linarith
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlp : Real.log x < Real.log p := Real.log_lt_log hxpos hp
  set y : ℝ := (Real.log p - Real.log x) / Real.log 2 with hy
  have hypos : (0:ℝ) < y := div_pos (by linarith) hlog2pos
  have hceilpos : 1 ≤ ⌈y⌉₊ := Nat.one_le_ceil_iff.mpr hypos
  have hceileq : ⌈y⌉₊ = k + 1 := by
    have : blockIdx x p = ⌈y⌉₊ - 1 := rfl
    omega
  have hiff := (Nat.ceil_eq_iff (n := k+1) (by omega)).mp hceileq
  simp only [Nat.add_sub_cancel] at hiff
  obtain ⟨hklt, hkle⟩ := hiff
  -- lower: 2^k x < p
  have hlower : (2:ℝ)^k * x < (p:ℝ) := by
    have hklt' : (k:ℝ) * Real.log 2 < Real.log p - Real.log x :=
      (lt_div_iff₀ hlog2pos).mp hklt
    have : Real.log ((2:ℝ)^k * x) < Real.log p := by
      rw [log_two_pow_mul hxpos k]; linarith
    exact (Real.log_lt_log_iff (by positivity) hppos).mp this
  -- upper: p ≤ 2^{k+1} x
  have hupper : (p:ℝ) ≤ (2:ℝ)^(k+1) * x := by
    have hkle' : Real.log p - Real.log x ≤ (k+1 : ℝ) * Real.log 2 := by
      rw [hy] at hkle
      calc Real.log p - Real.log x
          = y * Real.log 2 := by rw [hy]; field_simp
        _ ≤ (k+1 : ℝ) * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right _ hlog2pos.le
            exact_mod_cast hkle
    have hle : Real.log p ≤ Real.log ((2:ℝ)^(k+1) * x) := by
      rw [log_two_pow_mul hxpos (k+1)]; push_cast; linarith
    calc (p:ℝ) = Real.exp (Real.log p) := (Real.exp_log hppos).symm
      _ ≤ Real.exp (Real.log ((2:ℝ)^(k+1) * x)) := by exact Real.exp_le_exp.mpr hle
      _ = (2:ℝ)^(k+1) * x := Real.exp_log (by positivity)
  exact ⟨hlower, hupper⟩

/-! ## Lemma 2b — the full per-window bound (decay × Mertens) -/

/-- **The full window bound.**  For `e ≤ x`, every `k`, and any Finset `G` of primes in the
half-open window `(2^k x, 2^{k+1} x]`, the shifted sum over `G` is bounded by
`e^{-1}·((log 2 + 24)/log x)·r^k`, `r = e^{-log 2/log x}`.  Decay
`p^{-δ} ≤ (2^k x)^{-δ} = e^{-1} r^k`, reciprocal sum `≤ SPartial(2^{k+1}x) − SPartial(2^k x)`
(half-open tiling, no boundary term), Mertens difference `≤ (log 2 + 24)/log x`. -/
theorem block_full_le {x : ℝ} (hx : Real.exp 1 ≤ x) (k : ℕ) (G : Finset ℕ)
    (hG : ∀ p ∈ G, Nat.Prime p ∧ (2 : ℝ) ^ k * x < (p : ℝ) ∧ (p : ℝ) ≤ (2 : ℝ) ^ (k + 1) * x) :
    ∑ p ∈ G, (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)
      ≤ Real.exp (-1) * ((Real.log 2 + 24) / Real.log x)
          * (Real.exp (-(Real.log 2) / Real.log x)) ^ k := by
  have h2e : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hx2 : (2:ℝ) ≤ x := le_trans h2e hx
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0:ℝ) < Real.log x := by linarith
  have hapos : (0:ℝ) < (2:ℝ)^k * x := by positivity
  have hdnn : (0:ℝ) ≤ 1 / Real.log x := le_of_lt (div_pos one_pos hLpos)
  -- (d) the decay constant equals e^{-1} r^k
  have hpow_eq : ((2:ℝ)^k * x) ^ (-(1 / Real.log x) : ℝ)
      = Real.exp (-1) * (Real.exp (-(Real.log 2) / Real.log x)) ^ k := by
    rw [Real.rpow_def_of_pos hapos, log_two_pow_mul hxpos k, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    field_simp
    ring
  -- (a) termwise decay bound
  have hterm : ∀ p ∈ G, (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)
      ≤ ((2:ℝ)^k * x) ^ (-(1 / Real.log x) : ℝ) * ((1:ℝ) / (p : ℝ)) := by
    intro p hp
    obtain ⟨_, hplt, _⟩ := hG p hp
    have hppos : (0:ℝ) < (p : ℝ) := by linarith
    have hdecay : (p : ℝ) ^ (-(1 / Real.log x) : ℝ)
        ≤ ((2:ℝ)^k * x) ^ (-(1 / Real.log x) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hapos (le_of_lt hplt) (neg_nonpos.mpr hdnn)
    have hsplit : (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)
        = (p : ℝ) ^ (-(1 / Real.log x) : ℝ) * (1 / (p : ℝ)) := by
      rw [one_div (p : ℝ),
          show (-1 - 1 / Real.log x : ℝ) = (-(1 / Real.log x)) + (-1) from by ring,
          Real.rpow_add hppos, Real.rpow_neg_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hdecay (by positivity)
  -- (b) reciprocal sum ≤ SPartial difference
  have hrecip : ∑ p ∈ G, (1:ℝ) / (p : ℝ)
      ≤ Salt.Mertens.SPartial ((2:ℝ)^(k+1) * x) - Salt.Mertens.SPartial ((2:ℝ)^k * x) := by
    have hab : (2:ℝ)^k * x ≤ (2:ℝ)^(k+1) * x :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)) hxpos.le
    have hsub : (Finset.range (⌊(2:ℝ)^k * x⌋₊ + 1)).filter Nat.Prime
        ⊆ (Finset.range (⌊(2:ℝ)^(k+1) * x⌋₊ + 1)).filter Nat.Prime := by
      apply Finset.filter_subset_filter
      intro m hm
      rw [Finset.mem_range] at hm ⊢
      have : ⌊(2:ℝ)^k * x⌋₊ ≤ ⌊(2:ℝ)^(k+1) * x⌋₊ := Nat.floor_mono hab
      omega
    have hGsub : G ⊆ (Finset.range (⌊(2:ℝ)^(k+1) * x⌋₊ + 1)).filter Nat.Prime
        \ (Finset.range (⌊(2:ℝ)^k * x⌋₊ + 1)).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpr, hplt, hple⟩ := hG p hp
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hpr⟩, ?_⟩
      · have : p ≤ ⌊(2:ℝ)^(k+1) * x⌋₊ := Nat.le_floor hple
        omega
      · rw [Finset.mem_filter, Finset.mem_range]
        rintro ⟨hlt, _⟩
        have : ⌊(2:ℝ)^k * x⌋₊ < p := (Nat.floor_lt (by positivity)).mpr hplt
        omega
    have hsd := Finset.sum_sdiff (f := fun p : ℕ => (1:ℝ) / (p : ℝ)) hsub
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hGsub
      (fun p _ _ => by positivity : ∀ p ∈ _, p ∉ G → (0:ℝ) ≤ (1:ℝ) / (p : ℝ))
    have hSb : Salt.Mertens.SPartial ((2:ℝ)^(k+1) * x)
        = ∑ p ∈ (Finset.range (⌊(2:ℝ)^(k+1) * x⌋₊ + 1)).filter Nat.Prime, (1:ℝ) / (p : ℝ) := rfl
    have hSa : Salt.Mertens.SPartial ((2:ℝ)^k * x)
        = ∑ p ∈ (Finset.range (⌊(2:ℝ)^k * x⌋₊ + 1)).filter Nat.Prime, (1:ℝ) / (p : ℝ) := rfl
    rw [hSb, hSa]; linarith [hle, hsd]
  -- assemble
  calc ∑ p ∈ G, (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)
      ≤ ∑ p ∈ G, ((2:ℝ)^k * x) ^ (-(1 / Real.log x) : ℝ) * ((1:ℝ) / (p : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ((2:ℝ)^k * x) ^ (-(1 / Real.log x) : ℝ) * ∑ p ∈ G, (1:ℝ) / (p : ℝ) := by
        rw [← Finset.mul_sum]
    _ ≤ ((2:ℝ)^k * x) ^ (-(1 / Real.log x) : ℝ)
          * (Salt.Mertens.SPartial ((2:ℝ)^(k+1) * x) - Salt.Mertens.SPartial ((2:ℝ)^k * x)) :=
        mul_le_mul_of_nonneg_left hrecip (Real.rpow_nonneg hapos.le _)
    _ ≤ ((2:ℝ)^k * x) ^ (-(1 / Real.log x) : ℝ) * ((Real.log 2 + 24) / Real.log x) :=
        mul_le_mul_of_nonneg_left (mertens_block_diff_le hx k) (Real.rpow_nonneg hapos.le _)
    _ = Real.exp (-1) * ((Real.log 2 + 24) / Real.log x)
          * (Real.exp (-(Real.log 2) / Real.log x)) ^ k := by rw [hpow_eq]; ring

/-! ## The finite window sum bound -/

/-- **The finite tail bound.**  For `e ≤ x` and any Finset `P` of primes all `> x`,
`∑_{p ∈ P} p^{-1-1/log x} ≤ primeTailConst`.  Partition `P` by `blockIdx x`, bound each
fiber by `block_full_le`, sum the geometric series `∑_k r^k ≤ (1−r)⁻¹ ≤ 2 log x/log 2`. -/
theorem prime_tail_finite_le {x : ℝ} (hx : Real.exp 1 ≤ x) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, Nat.Prime p) (hPx : ∀ p ∈ P, x < (p : ℝ)) :
    ∑ p ∈ P, (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) ≤ primeTailConst := by
  have h2e : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hx2 : (2:ℝ) ≤ x := le_trans h2e hx
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0:ℝ) < Real.log x := by linarith
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set r := Real.exp (-(Real.log 2) / Real.log x) with hrdef
  have hrpos : (0:ℝ) < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff, neg_div]
    have : 0 < Real.log 2 / Real.log x := div_pos hlog2pos hLpos
    linarith
  -- maps-to: every block index lands in range (P.sup id + 1)
  have hmaps : ∀ p ∈ P, blockIdx x p ∈ Finset.range (P.sup id + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have hp2 : 2 ≤ p := (hPp p hp).two_le
    have hppos : (0:ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hpow : (p : ℝ) ≤ (2:ℝ) ^ p := by
      have h := Nat.lt_two_pow_self (n := p)
      calc (p : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast le_of_lt h
        _ = (2:ℝ) ^ p := by push_cast; ring
    have hlogp_le : Real.log p ≤ (p : ℝ) * Real.log 2 := by
      calc Real.log p ≤ Real.log ((2:ℝ) ^ p) := Real.log_le_log hppos hpow
        _ = (p : ℝ) * Real.log 2 := by rw [Real.log_pow]
    have hylep : (Real.log p - Real.log x) / Real.log 2 ≤ (p : ℝ) := by
      rw [div_le_iff₀ hlog2pos]; nlinarith [hlogp_le, hLpos]
    have hceil_le : ⌈(Real.log p - Real.log x) / Real.log 2⌉₊ ≤ p := Nat.ceil_le.mpr hylep
    have hbi : blockIdx x p ≤ p := by
      have : blockIdx x p = ⌈(Real.log p - Real.log x) / Real.log 2⌉₊ - 1 := rfl
      omega
    have hpK : p ≤ P.sup id := Finset.le_sup (f := id) hp
    omega
  -- geometric sum bound
  have hgeomsum : ∑ j ∈ Finset.range (P.sup id + 1), r ^ j ≤ (1 - r)⁻¹ := by
    have hsummable := summable_geometric_of_lt_one hrpos.le hr1
    have hle := hsummable.sum_le_tsum (Finset.range (P.sup id + 1))
      (fun j _ => pow_nonneg hrpos.le j)
    rwa [tsum_geometric_of_lt_one hrpos.le hr1] at hle
  -- (1-r)⁻¹ ≤ 2 log x / log 2  via  1-r ≥ log2/(2 log x)
  have hwpos : (0:ℝ) < Real.log 2 / Real.log x := div_pos hlog2pos hLpos
  have hwle : Real.log 2 / Real.log x ≤ Real.log 2 := by
    rw [div_le_iff₀ hLpos]; nlinarith [hlog2pos, hlogx1]
  have hexp_ge_half : (1:ℝ) / 2 ≤ r := by
    rw [hrdef, neg_div]
    have h1 : Real.exp (-(Real.log 2)) ≤ Real.exp (-(Real.log 2 / Real.log x)) :=
      Real.exp_le_exp.mpr (by linarith [hwle])
    have h2 : Real.exp (-(Real.log 2)) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
    linarith
  have hkey : (Real.log 2 / Real.log x + 1) * r ≤ 1 := by
    rw [hrdef, neg_div]
    have hle := Real.add_one_le_exp (Real.log 2 / Real.log x)
    have hmul : (Real.log 2 / Real.log x + 1) * Real.exp (-(Real.log 2 / Real.log x))
        ≤ Real.exp (Real.log 2 / Real.log x) * Real.exp (-(Real.log 2 / Real.log x)) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
  have hgeom : Real.log 2 / Real.log x / 2 ≤ 1 - r := by
    have hprod : (0:ℝ) ≤ (Real.log 2 / Real.log x) * (r - 1 / 2) :=
      mul_nonneg hwpos.le (by linarith [hexp_ge_half])
    nlinarith [hkey, hprod]
  have hinv : (1 - r)⁻¹ ≤ 2 * Real.log x / Real.log 2 := by
    have hposq : (0:ℝ) < Real.log 2 / Real.log x / 2 := div_pos hwpos (by norm_num)
    have heq : (Real.log 2 / Real.log x / 2)⁻¹ = 2 * Real.log x / Real.log 2 := by
      field_simp
    calc (1 - r)⁻¹ ≤ (Real.log 2 / Real.log x / 2)⁻¹ := inv_anti₀ hposq hgeom
      _ = 2 * Real.log x / Real.log 2 := heq
  have hAnn : (0:ℝ) ≤ Real.exp (-1) * ((Real.log 2 + 24) / Real.log x) :=
    mul_nonneg (Real.exp_pos _).le (div_nonneg (by linarith [hlog2pos]) hLpos.le)
  -- fiberwise assembly
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ))]
  calc ∑ j ∈ Finset.range (P.sup id + 1),
          ∑ p ∈ P with blockIdx x p = j, (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)
      ≤ ∑ j ∈ Finset.range (P.sup id + 1),
          Real.exp (-1) * ((Real.log 2 + 24) / Real.log x) * r ^ j := by
        apply Finset.sum_le_sum
        intro j _
        rw [hrdef]
        apply block_full_le hx j
        intro p hp
        rw [Finset.mem_filter] at hp
        exact ⟨hPp p hp.1, blockIdx_window hx (hPx p hp.1) hp.2⟩
    _ = Real.exp (-1) * ((Real.log 2 + 24) / Real.log x)
          * ∑ j ∈ Finset.range (P.sup id + 1), r ^ j := by rw [← Finset.mul_sum]
    _ ≤ Real.exp (-1) * ((Real.log 2 + 24) / Real.log x) * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeomsum hAnn
    _ ≤ Real.exp (-1) * ((Real.log 2 + 24) / Real.log x) * (2 * Real.log x / Real.log 2) :=
        mul_le_mul_of_nonneg_left hinv hAnn
    _ = primeTailConst := by rw [primeTailConst]; field_simp

/-! ## The discharge and the unconditional exports -/

/-- **R0.2 discharged (`prime_tail_shift`).**  `PrimeTailShiftBounded` holds with the
certified constant `primeTailConst ≈ 26.2`.  The tsum over `p > x` is reduced to the finite
window sums by `Real.tsum_le_of_sum_range_le`, each bounded by `prime_tail_finite_le`. -/
theorem prime_tail_shift : PrimeTailShiftBounded := by
  refine ⟨primeTailConst, fun x hx => ?_⟩
  have h2e : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  unfold primeTailShift
  set N := ⌊x⌋₊ + 1 with hN
  apply Real.tsum_le_of_sum_range_le
  · intro i
    exact Set.indicator_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) _
  · intro n
    have hinj : Set.InjOn (· + N) ↑(Finset.range n) := by
      intro a _ b _ h; simpa using h
    have hstep1 : ∑ i ∈ Finset.range n, Set.indicator {p : ℕ | Nat.Prime p}
          (fun p => (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)) (i + N)
        = ∑ m ∈ (Finset.range n).image (· + N), Set.indicator {p : ℕ | Nat.Prime p}
          (fun p => (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)) m := (Finset.sum_image hinj).symm
    have hstep2 : ∑ m ∈ (Finset.range n).image (· + N), Set.indicator {p : ℕ | Nat.Prime p}
          (fun p => (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ)) m
        = ∑ p ∈ ((Finset.range n).image (· + N)).filter Nat.Prime,
          (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl
        (fun m _ => by rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq])
    rw [hstep1, hstep2]
    apply prime_tail_finite_le hx
    · exact fun p hp => (Finset.mem_filter.mp hp).2
    · intro p hp
      obtain ⟨hpimg, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hpimg
      have hNlt : x < (N : ℝ) := by rw [hN]; push_cast; exact Nat.lt_floor_add_one x
      have : (N : ℝ) ≤ ((i + N : ℕ) : ℝ) := by push_cast; linarith
      linarith

/-- **Unconditional exit stone — `log_euler_osc_zeta_unconditional`.**  The R0.2 discharge
turns the H0 λ-side Euler-oscillation ζ-bridge unconditional. -/
theorem log_euler_osc_zeta_unconditional :
    ∃ K : ℝ, ∀ x t : ℝ, Real.exp 1 ≤ x →
      (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
            Real.cos (t * Real.log p) / (p : ℝ))
        ≤ Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ)
            + (t : ℝ) * Complex.I)‖ + K :=
  log_euler_osc_zeta prime_tail_shift

/-- **Unconditional exit stone — `euler_osc_bridge_le_unconditional`.**  The R0.2 discharge
turns the H0 `D(1)`-side Euler-oscillation ζ-bridge unconditional. -/
theorem euler_osc_bridge_le_unconditional :
    ∃ K : ℝ, ∀ x t : ℝ, Real.exp 1 ≤ x →
      Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
              Real.cos (t * Real.log p) / (p : ℝ)) + K :=
  euler_osc_bridge_le prime_tail_shift

/-- **Unconditional two-sided bridge — `euler_osc_bridge_unconditional`.**  The full
two-sided H0 Euler-oscillation ζ-bridge, now unconditional. -/
theorem euler_osc_bridge_unconditional :
    ∃ K : ℝ, ∀ x t : ℝ, Real.exp 1 ≤ x →
      |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
            Real.cos (t * Real.log p) / (p : ℝ))
          - Real.log ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖|
        ≤ K :=
  euler_osc_bridge prime_tail_shift

end Salt.MR
