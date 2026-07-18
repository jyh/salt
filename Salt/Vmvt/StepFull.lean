/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Step
import Salt.Vmvt.Transversal3

/-!
# Theorem 24.5 — the transversal-dominant (`S₁`) step (VMVT node R4-`S₁`)

This file closes the transversal branch of the one-step Linnik–Karatsuba
recursion, feeding `vmvt_step_of_transversal_dominant` (`Step.lean`) with the
quantitative bound produced by `transBox_Ncount_le` (`Transversal3.lean`), the
IH, and the prime pigeonhole.

## The collector (the load-bearing exponent bookkeeping — PROVEN here)

One Linnik step at level `r+1` produces, per transversal prime `p`,
`Ncount(D₄(p)) ≤ p^{2kr}·(x^k·k!·p^{k(k−1)/2})·J_k(x/p+1, kr)`
(`transBox_Ncount_le`).  Consuming the IH `J_k(x/p+1, kr) ≤ D(k,r)·(x/p+1)^{E(k,r)}`
and collecting the `p`-powers into `x`-powers, the residual **prime** exponent is
`B(k,r) = 2kr + k(k−1)/2 − E(k,r) = k² − η(k,r) ∈ [½k², k²)` (`vmvtResid_eq`),
and the `x`-exponent lands **exactly** on `E(k,r+1)` (`collector_rpow`, keyed to
the kernel-verified `vmvtExp_succ`):

  `x^k · p^{2kr + k(k−1)/2} · (x/p)^{E(k,r)} = (p/x^{1/k})^{B(k,r)} · x^{E(k,r+1)}`.

The leftover constant `(p/x^{1/k})^{B}` is `≤ 2^{k²}·(1+1/x^{1/k})^{k²}` for
`p ∈ (x^{1/k}, 2·x^{1/k}]`, and in the large-`x` regime `(1+tiny)^{k²} ≤ √3`, so
the per-step constant fits under `C₀(k) = k⁶·k!·2^{k²}·3` (the `#P² ≤ ¼k⁶` prime
count fills the `k⁶`, the two `√3` corrections fill the `3`).
-/

namespace Salt.Vmvt

open Finset

/-! ## The collector arithmetic (pure `ℝ`, keyed to `vmvtExp_succ`) -/

/-- The residual prime exponent `B(k,r) = k² − η(k,r)` produced by one Linnik
step (it lands in `[½k², k²)` since `η(k,r) ∈ (0, ½k²]`). -/
noncomputable def vmvtResidExp (k r : ℕ) : ℝ := (k : ℝ) ^ 2 - vmvtEta k r

/-- **The exponent step-difference.** `E(k,r+1) = E(k,r) + (2k − η(k,r)/k)`. -/
theorem vmvtExp_step_diff (k r : ℕ) (hk : (k : ℝ) ≠ 0) :
    vmvtExp k (r + 1) = vmvtExp k r + (2 * (k : ℝ) - vmvtEta k r / (k : ℝ)) := by
  unfold vmvtExp
  rw [vmvtEta_succ]
  push_cast
  field_simp
  ring

/-- **The residual-exponent identity (the collector's heart).**
`2kr + k(k−1)/2 − E(k,r) = k² − η(k,r) = B(k,r)`. -/
theorem vmvtResid_eq (k r : ℕ) :
    2 * (k : ℝ) * (r : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2 - vmvtExp k r = vmvtResidExp k r := by
  unfold vmvtExp vmvtResidExp
  ring

/-- The collector's `x`-exponent identity: `k + B(k,r)/k + E(k,r) = E(k,r+1)`. -/
theorem vmvt_collect_exp (k r : ℕ) (hk : (k : ℝ) ≠ 0) :
    (k : ℝ) + vmvtResidExp k r / (k : ℝ) + vmvtExp k r = vmvtExp k (r + 1) := by
  rw [vmvtExp_step_diff k r hk]
  unfold vmvtResidExp
  field_simp
  ring

/-- **The collector identity (rpow form).**  The load-bearing exponent
rearrangement of one Linnik step: the `x`-freedom `x^k`, the combined `p`-power
`p^{2kr + k(k−1)/2}`, and the IH box `(x/p)^{E(k,r)}` collect into the residual
constant `(p/x^{1/k})^{B(k,r)}` times exactly `x^{E(k,r+1)}`. -/
theorem collector_rpow (xr pr : ℝ) (hx : 0 < xr) (hp : 0 < pr) (k r : ℕ)
    (hk : (k : ℝ) ≠ 0) :
    xr ^ (k : ℝ) * pr ^ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2)
        * (xr / pr) ^ (vmvtExp k r)
      = (pr / xr ^ ((1 : ℝ) / (k : ℝ))) ^ (vmvtResidExp k r) * xr ^ (vmvtExp k (r + 1)) := by
  set N : ℝ := 2 * (k : ℝ) * (r : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2 with hN
  set E : ℝ := vmvtExp k r with hE
  set B : ℝ := vmvtResidExp k r with hB
  set t : ℝ := xr ^ ((1 : ℝ) / (k : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx _
  have hNE : N - E = B := vmvtResid_eq k r
  have hexp : (k : ℝ) + E = vmvtExp k (r + 1) - B / (k : ℝ) := by
    have h := vmvt_collect_exp k r hk; rw [← hB] at h; linarith [h]
  have hL : xr ^ (k : ℝ) * pr ^ N * (xr / pr) ^ E = pr ^ B * xr ^ ((k : ℝ) + E) := by
    rw [← hNE, Real.div_rpow hx.le hp.le, Real.rpow_sub hp, Real.rpow_add hx]
    field_simp
  have htB : t ^ B = xr ^ (B / (k : ℝ)) := by
    rw [ht, ← Real.rpow_mul hx.le]; congr 1; ring
  have hR : (pr / t) ^ B * xr ^ (vmvtExp k (r + 1)) = pr ^ B * xr ^ ((k : ℝ) + E) := by
    rw [Real.div_rpow hp.le ht0.le, htB, hexp, Real.rpow_sub hx]
    field_simp
  rw [hL, hR]

/-! ## The IH-consumption bridge (`Jk` on the residue interval `= JkI`) -/

/-- `Finset.Icc (1:ℤ) N = Finset.Ioc (0:ℤ) N` — the residue interval is the
`JkI` interval object. -/
lemma Icc_one_eq_Ioc_zero (N : ℤ) : Finset.Icc (1 : ℤ) N = Finset.Ioc (0 : ℤ) N := by
  ext z; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- **The residue-box `J_k` is the interval `J_k` at scale `x/p+1`.**  The
`transBox_Ncount_le` output `J_k(Icc 1 (⌊x/p⌋+1))` is `JkI k b (⌊x/p⌋+1)`, the
inductive-hypothesis object at the dropped scale. -/
lemma Jk_Icc_eq_JkI (k b : ℕ) (M : ℕ) :
    Jk k b (Finset.Icc (1 : ℤ) ((M : ℤ) + 1)) = JkI k b (M + 1) := by
  unfold JkI
  rw [Icc_one_eq_Ioc_zero]
  norm_num

/-! ## The per-prime transcription (R3 output + IH, faithful) -/

/-- **The per-prime transversal bound, IH consumed.**  `transBox_Ncount_le` at
level `r+1` (rest block `k·r`), with the interval `J_k` rewritten to `JkI` at the
dropped scale `⌊x/p⌋+1` and the inductive hypothesis `hIH` substituted, gives the
per-prime bound in `ℝ`, still carrying the raw `p`-powers and the residue box. -/
theorem transBox_le_ih {k r : ℕ} (x p : ℕ) (e : Fin k → Fin (k * (r + 1)))
    (he : Function.Injective e) (hp : p.Prime) (hkp : k < p) (hk : 0 < k)
    (hpx : x < p ^ k)
    (hIH : (JkI k (k * r) (x / p + 1) : ℝ)
             ≤ vmvtConst k r * ((x / p + 1 : ℕ) : ℝ) ^ (vmvtExp k r)) :
    (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ)
      ≤ (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * ((x : ℝ) ^ k * (k.factorial : ℝ)
          * (p : ℝ) ^ (k * (k - 1) / 2))
        * (vmvtConst k r * ((x / p + 1 : ℕ) : ℝ) ^ (vmvtExp k r)) := by
  have hnat := transBox_Ncount_le (k := k) (r := r + 1) x p e he hp hkp hk (by omega) hpx
  rw [Nat.add_sub_cancel, Jk_Icc_eq_JkI] at hnat
  have hcast : (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ)
      ≤ (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * ((x : ℝ) ^ k * (k.factorial : ℝ)
          * (p : ℝ) ^ (k * (k - 1) / 2)) * (JkI k (k * r) (x / p + 1) : ℝ) := by
    exact_mod_cast hnat
  refine hcast.trans ?_
  exact mul_le_mul_of_nonneg_left hIH (by positivity)

/-! ## The scale `y = ⌈x^{1/k}⌉₊` (the transversal-prime interval anchor) -/

/-- The scale `y = ⌈x^{1/k}⌉₊`: the least integer with `y^k ≥ x`. -/
noncomputable def vmvtScale (k x : ℕ) : ℕ := ⌈(x : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌉₊

/-- `x^{1/k} ≤ y` (the ceiling is above). -/
lemma rpow_le_scale {k x : ℕ} : (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) ≤ (vmvtScale k x : ℝ) :=
  Nat.le_ceil _

/-- `x ≤ y^k`: the scale's `k`-th power dominates `x`. -/
lemma le_scale_pow {k x : ℕ} (hk : 0 < k) : x ≤ (vmvtScale k x) ^ k := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have h1 : ((x : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ (k : ℕ) ≤ (vmvtScale k x : ℝ) ^ (k : ℕ) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hx0 _) rpow_le_scale k
  rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / (k : ℝ))) k, ← Real.rpow_mul hx0,
    one_div_mul_cancel hk0, Real.rpow_one] at h1
  have h2 : (x : ℝ) ≤ ((vmvtScale k x) ^ k : ℕ) := by rw [Nat.cast_pow]; exact h1
  exact_mod_cast h2

/-- `y < x^{1/k} + 1` (the ceiling is within one). -/
lemma scale_lt {k x : ℕ} : (vmvtScale k x : ℝ) < (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) + 1 :=
  Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `1 ≤ x^{1/k}` for `x ≥ 1` (the anchor is `≥ 1`). -/
lemma one_le_rpow_scale {k x : ℕ} (hx : 1 ≤ x) : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
  apply Real.one_le_rpow (by exact_mod_cast hx)
  positivity

/-! ## Sign facts for the exponent `E(k,r)` -/

/-- `0 ≤ η(k,r)`: the decay term is nonnegative (`1 − 1/k ≥ 0` for `k ≥ 1`). -/
lemma vmvtEta_nonneg {k : ℕ} (hk : 1 ≤ k) (r : ℕ) : 0 ≤ vmvtEta k r := by
  unfold vmvtEta
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hk1
  positivity

/-- **`k ≤ E(k,r)` for `r ≥ 1`.**  The exponent is at least `k` (hence positive):
`E(k,1) = k` and the step-difference `2k − η/k ≥ 0` keeps it non-decreasing. -/
theorem vmvtExp_ge_k {k : ℕ} (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r) : (k : ℝ) ≤ vmvtExp k r := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  induction r, hr using Nat.le_induction with
  | base => rw [vmvtExp_one k hk0]
  | succ n hn ih =>
    rw [vmvtExp_step_diff k n hk0]
    have hη : vmvtEta k n ≤ (1 / 2) * (k : ℝ) * ((k : ℝ) - 1) := vmvtEta_le (by omega) hn
    have hη0 : 0 ≤ vmvtEta k n := vmvtEta_nonneg (by omega) n
    have hstep : 0 ≤ 2 * (k : ℝ) - vmvtEta k n / (k : ℝ) := by
      rw [sub_nonneg, div_le_iff₀ hkpos]; nlinarith [hη, hkpos]
    linarith [ih, hstep]

/-- `0 ≤ E(k,r)` for `r ≥ 1`, `k ≥ 2`. -/
lemma vmvtExp_nonneg {k : ℕ} (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r) : 0 ≤ vmvtExp k r := by
  have := vmvtExp_ge_k hk hr
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## The collector applied: the bracket bound and the regime constant -/

lemma cast_choose2 {k : ℕ} (hk : 1 ≤ k) :
    ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  have hdvd : 2 ∣ k * (k - 1) := by
    have h := Nat.even_mul_succ_self (k - 1)
    rw [Nat.sub_add_cancel hk] at h
    rw [mul_comm]
    exact h.two_dvd
  rw [Nat.cast_div hdvd (by norm_num)]
  rw [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one]
  norm_num

lemma cast_N1 (k r : ℕ) : ((2 * (k * (r + 1)) - 2 * k : ℕ) : ℝ) = 2 * (k : ℝ) * (r : ℝ) := by
  rw [show 2 * (k * (r + 1)) - 2 * k = 2 * k * r by ring_nf; omega]
  push_cast; ring

/-- **The bracket bound.**  The collector `collector_rpow` applied through the
IH-box `+1` correction: the raw `x^k·p^{2kr+k(k−1)/2}·(⌊x/p⌋+1)^{E(k,r)}` product
is `≤ (p/x^{1/k})^{B}·(1+p/x)^{E(k,r)}·x^{E(k,r+1)}`. -/
theorem bracket_le {k r : ℕ} (x p : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) (hx1 : 1 ≤ x) (hp1 : 1 ≤ p) :
    (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * (x : ℝ) ^ k * (p : ℝ) ^ (k * (k - 1) / 2)
        * (((x / p : ℕ) : ℝ) + 1) ^ (vmvtExp k r)
      ≤ ((p : ℝ) / (x : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ (vmvtResidExp k r)
        * (1 + (p : ℝ) / (x : ℝ)) ^ (vmvtExp k r) * (x : ℝ) ^ (vmvtExp k (r + 1)) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hEr0 : 0 ≤ vmvtExp k r := vmvtExp_nonneg hk hr
  set Er : ℝ := vmvtExp k r with hErdef
  have hcomb : (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * (x : ℝ) ^ k * (p : ℝ) ^ (k * (k - 1) / 2)
      = (x : ℝ) ^ (k : ℝ)
        * (p : ℝ) ^ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2) := by
    rw [show (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * (x : ℝ) ^ k * (p : ℝ) ^ (k * (k - 1) / 2)
          = (x : ℝ) ^ k * ((p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * (p : ℝ) ^ (k * (k - 1) / 2))
          by ring, ← pow_add]
    rw [← Real.rpow_natCast (x : ℝ) k, ← Real.rpow_natCast (p : ℝ)
        (2 * (k * (r + 1)) - 2 * k + k * (k - 1) / 2)]
    congr 2
    push_cast [cast_N1 k r, cast_choose2 (by omega : 1 ≤ k)]
    ring
  have hdivle : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ) := Nat.cast_div_le
  have hfac : (x : ℝ) / (p : ℝ) + 1 = ((x : ℝ) / (p : ℝ)) * (1 + (p : ℝ) / (x : ℝ)) := by
    field_simp
  have hbase0 : (0 : ℝ) ≤ ((x / p : ℕ) : ℝ) + 1 := by positivity
  have hcorr : (((x / p : ℕ) : ℝ) + 1) ^ Er
      ≤ ((x : ℝ) / (p : ℝ)) ^ Er * (1 + (p : ℝ) / (x : ℝ)) ^ Er := by
    calc (((x / p : ℕ) : ℝ) + 1) ^ Er
        ≤ ((x : ℝ) / (p : ℝ) + 1) ^ Er :=
          Real.rpow_le_rpow hbase0 (by linarith [hdivle]) hEr0
      _ = (((x : ℝ) / (p : ℝ)) * (1 + (p : ℝ) / (x : ℝ))) ^ Er := by rw [hfac]
      _ = ((x : ℝ) / (p : ℝ)) ^ Er * (1 + (p : ℝ) / (x : ℝ)) ^ Er :=
          Real.mul_rpow (by positivity) (by positivity)
  have hcollect := collector_rpow (x : ℝ) (p : ℝ) hx0 hp0 k r hk0
  calc (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * (x : ℝ) ^ k * (p : ℝ) ^ (k * (k - 1) / 2)
        * (((x / p : ℕ) : ℝ) + 1) ^ Er
      = ((x : ℝ) ^ (k : ℝ)
          * (p : ℝ) ^ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2))
          * (((x / p : ℕ) : ℝ) + 1) ^ Er := by rw [hcomb]
    _ ≤ ((x : ℝ) ^ (k : ℝ)
          * (p : ℝ) ^ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2))
          * (((x : ℝ) / (p : ℝ)) ^ Er * (1 + (p : ℝ) / (x : ℝ)) ^ Er) := by
        apply mul_le_mul_of_nonneg_left hcorr; positivity
    _ = ((x : ℝ) ^ (k : ℝ)
          * (p : ℝ) ^ (2 * (k : ℝ) * (r : ℝ) + (k : ℝ) * ((k : ℝ) - 1) / 2)
          * ((x : ℝ) / (p : ℝ)) ^ Er) * (1 + (p : ℝ) / (x : ℝ)) ^ Er := by ring
    _ = ((p : ℝ) / (x : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ (vmvtResidExp k r)
          * (x : ℝ) ^ (vmvtExp k (r + 1)) * (1 + (p : ℝ) / (x : ℝ)) ^ Er := by
        rw [hErdef, hcollect]
    _ = ((p : ℝ) / (x : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ (vmvtResidExp k r)
          * (1 + (p : ℝ) / (x : ℝ)) ^ (vmvtExp k r) * (x : ℝ) ^ (vmvtExp k (r + 1)) := by
        rw [hErdef]; ring

/-- `(1+u)^E ≤ exp(u·E)` for `u ≥ 0`, `E ≥ 0`.  The regime-correction workhorse. -/
lemma one_add_rpow_le_exp {u E : ℝ} (hu : 0 ≤ u) (hE : 0 ≤ E) :
    (1 + u) ^ E ≤ Real.exp (u * E) := by
  have h1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  calc (1 + u) ^ E ≤ (Real.exp u) ^ E := Real.rpow_le_rpow (by linarith) h1 hE
    _ = Real.exp (u * E) := by rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]

/-- `0 ≤ B(k,r)`: the residual prime exponent is nonnegative (`η ≤ ½k(k−1) < k²`). -/
lemma vmvtResidExp_nonneg {k : ℕ} (hk : 2 ≤ k) {r : ℕ} (hr : 1 ≤ r) :
    0 ≤ vmvtResidExp k r := by
  unfold vmvtResidExp
  have hη := vmvtEta_le (k := k) (r := r) (by omega) hr
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [hη]

/-- `B(k,r) ≤ k²`: the residual prime exponent never exceeds `k²` (`η ≥ 0`). -/
lemma vmvtResidExp_le {k : ℕ} (hk : 2 ≤ k) (r : ℕ) : vmvtResidExp k r ≤ (k : ℝ) ^ 2 := by
  unfold vmvtResidExp
  have := vmvtEta_nonneg (k := k) (by omega) r
  linarith

/-- **The per-step constant bound (the regime analysis).**  In the large-`x`
regime `x^{1/k} ≥ k² + 4·E(k,r)`, with `p ≤ 2y` (`y = ⌈x^{1/k}⌉₊`), the leftover
`(p/x^{1/k})^{B}·(1+p/x)^{E(k,r)}` fits under `2^{k²}·3`.  The `(1+1/t)^{k²}` and
`(1+p/x)^{E}` corrections combine to `exp((k²+4E)/t) ≤ e < 3`. -/
theorem correction_le {k r : ℕ} (x p : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) (hx1 : 1 ≤ x)
    (hp1 : 1 ≤ p) (hp_le : (p : ℝ) ≤ 2 * (vmvtScale k x : ℝ))
    (hreg : (k : ℝ) ^ 2 + 4 * vmvtExp k r ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ))) :
    ((p : ℝ) / (x : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ (vmvtResidExp k r)
        * (1 + (p : ℝ) / (x : ℝ)) ^ (vmvtExp k r)
      ≤ (2 : ℝ) ^ (k ^ 2) * 3 := by
  set t : ℝ := (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) with htdef
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ht1 : (1 : ℝ) ≤ t := one_le_rpow_scale hx1
  have ht0 : (0 : ℝ) < t := by linarith
  have hEr0 : 0 ≤ vmvtExp k r := vmvtExp_nonneg hk hr
  have hB0 : 0 ≤ vmvtResidExp k r := vmvtResidExp_nonneg hk hr
  have hBk : vmvtResidExp k r ≤ (k : ℝ) ^ 2 := vmvtResidExp_le hk r
  have htk : t ^ (k : ℕ) = (x : ℝ) := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, one_div_mul_cancel hk0, Real.rpow_one]
  have hscale : (vmvtScale k x : ℝ) < t + 1 := scale_lt
  have hpb : (p : ℝ) ≤ 2 * (t + 1) := by nlinarith [hp_le, hscale]
  have hpt : (p : ℝ) / t ≤ 2 + 2 / t := by
    rw [div_le_iff₀ ht0]
    have he : (2 + 2 / t) * t = 2 * t + 2 := by field_simp
    rw [he]; linarith [hpb]
  have h1le : (1 : ℝ) ≤ 2 + 2 / t := by
    have h2t : (0 : ℝ) ≤ 2 / t := by positivity
    linarith
  have hF1 : ((p : ℝ) / t) ^ (vmvtResidExp k r)
      ≤ (2 : ℝ) ^ ((k : ℝ) ^ 2) * Real.exp ((k : ℝ) ^ 2 / t) := by
    calc ((p : ℝ) / t) ^ (vmvtResidExp k r)
        ≤ (2 + 2 / t) ^ (vmvtResidExp k r) := Real.rpow_le_rpow (by positivity) hpt hB0
      _ ≤ (2 + 2 / t) ^ ((k : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le h1le hBk
      _ = (2 : ℝ) ^ ((k : ℝ) ^ 2) * (1 + 1 / t) ^ ((k : ℝ) ^ 2) := by
          rw [show (2 : ℝ) + 2 / t = 2 * (1 + 1 / t) by ring,
            Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ (2 : ℝ) ^ ((k : ℝ) ^ 2) * Real.exp ((1 / t) * (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (one_add_rpow_le_exp (by positivity) (by positivity))
            (by positivity)
      _ = (2 : ℝ) ^ ((k : ℝ) ^ 2) * Real.exp ((k : ℝ) ^ 2 / t) := by
          rw [div_mul_eq_mul_div, one_mul]
  have hpx4 : (p : ℝ) / (x : ℝ) ≤ 4 / t := by
    rw [div_le_div_iff₀ hx0 ht0]
    have hp4t : (p : ℝ) ≤ 4 * t := by nlinarith [hp_le, hscale, ht1]
    have htt : t ^ 2 ≤ t ^ (k : ℕ) := pow_le_pow_right₀ ht1 hk
    rw [pow_two] at htt
    nlinarith [hp4t, htt, htk, ht0]
  have hF2 : (1 + (p : ℝ) / (x : ℝ)) ^ (vmvtExp k r) ≤ Real.exp (4 * vmvtExp k r / t) := by
    calc (1 + (p : ℝ) / (x : ℝ)) ^ (vmvtExp k r)
        ≤ Real.exp (((p : ℝ) / (x : ℝ)) * vmvtExp k r) := one_add_rpow_le_exp (by positivity) hEr0
      _ ≤ Real.exp ((4 / t) * vmvtExp k r) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hpx4 hEr0)
      _ = Real.exp (4 * vmvtExp k r / t) := by rw [div_mul_eq_mul_div]
  have hkey : Real.exp ((k : ℝ) ^ 2 / t) * Real.exp (4 * vmvtExp k r / t) ≤ 3 := by
    rw [← Real.exp_add]
    have hsum : (k : ℝ) ^ 2 / t + 4 * vmvtExp k r / t ≤ 1 := by
      rw [← add_div, div_le_one ht0]; linarith [hreg]
    calc Real.exp ((k : ℝ) ^ 2 / t + 4 * vmvtExp k r / t) ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
      _ ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h2cast : (2 : ℝ) ^ ((k : ℝ) ^ 2) = (2 : ℝ) ^ (k ^ 2) := by
    rw [show ((k : ℝ) ^ 2) = ((k ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  calc ((p : ℝ) / t) ^ (vmvtResidExp k r) * (1 + (p : ℝ) / (x : ℝ)) ^ (vmvtExp k r)
      ≤ ((2 : ℝ) ^ ((k : ℝ) ^ 2) * Real.exp ((k : ℝ) ^ 2 / t)) * Real.exp (4 * vmvtExp k r / t) :=
        mul_le_mul hF1 hF2 (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = (2 : ℝ) ^ ((k : ℝ) ^ 2)
          * (Real.exp ((k : ℝ) ^ 2 / t) * Real.exp (4 * vmvtExp k r / t)) := by ring
    _ ≤ (2 : ℝ) ^ ((k : ℝ) ^ 2) * 3 := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 : ℝ) ^ (k ^ 2) * 3 := by rw [h2cast]

/-! ## The per-prime regime bound (R3 + IH + collector + constant, glued) -/

/-- `0 ≤ D(k,r)`. -/
lemma vmvtConst_nonneg (k r : ℕ) : 0 ≤ vmvtConst k r := by
  unfold vmvtConst vmvtC0; positivity

/-- **The per-prime transversal bound, closed.**  Combining `transBox_le_ih`
(R3 + IH), `bracket_le` (the collector), and `correction_le` (the regime
constant), each transversal prime `p ∈ (y, 2y]` contributes
`Ncount(D₄(p)) ≤ k!·D(k,r)·(2^{k²}·3)·x^{E(k,r+1)}` in the large-`x` regime. -/
theorem transBox_le_const {k r : ℕ} (x p : ℕ) (e : Fin k → Fin (k * (r + 1)))
    (he : Function.Injective e) (hp : p.Prime) (hkp : k < p) (hk : 2 ≤ k)
    (hpx : x < p ^ k) (hx1 : 1 ≤ x) (hr : 1 ≤ r)
    (hp_le : (p : ℝ) ≤ 2 * (vmvtScale k x : ℝ))
    (hreg : (k : ℝ) ^ 2 + 4 * vmvtExp k r ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
    (hIH : (JkI k (k * r) (x / p + 1) : ℝ)
             ≤ vmvtConst k r * ((x / p + 1 : ℕ) : ℝ) ^ (vmvtExp k r)) :
    (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ)
      ≤ (k.factorial : ℝ) * vmvtConst k r * ((2 : ℝ) ^ (k ^ 2) * 3)
        * (x : ℝ) ^ (vmvtExp k (r + 1)) := by
  have hp1 : 1 ≤ p := hp.pos
  have h1 := transBox_le_ih x p e he hp hkp (by omega) hpx hIH
  have hcast_xp : ((x / p + 1 : ℕ) : ℝ) = ((x / p : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast_xp] at h1
  refine h1.trans ?_
  have hbr := bracket_le (k := k) (r := r) x p hk hr hx1 hp1
  have hcorr := correction_le (k := k) (r := r) x p hk hr hx1 hp1 hp_le hreg
  have hxE : (0 : ℝ) ≤ (x : ℝ) ^ (vmvtExp k (r + 1)) := Real.rpow_nonneg (by positivity) _
  have hbracket_bound :
      (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * (x : ℝ) ^ k * (p : ℝ) ^ (k * (k - 1) / 2)
          * (((x / p : ℕ) : ℝ) + 1) ^ (vmvtExp k r)
        ≤ ((2 : ℝ) ^ (k ^ 2) * 3) * (x : ℝ) ^ (vmvtExp k (r + 1)) :=
    hbr.trans (mul_le_mul_of_nonneg_right hcorr hxE)
  have hfacnn : (0 : ℝ) ≤ (k.factorial : ℝ) * vmvtConst k r := by
    have := vmvtConst_nonneg k r; positivity
  calc (p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k)
          * ((x : ℝ) ^ k * (k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2))
          * (vmvtConst k r * (((x / p : ℕ) : ℝ) + 1) ^ (vmvtExp k r))
      = (k.factorial : ℝ) * vmvtConst k r
          * ((p : ℝ) ^ (2 * (k * (r + 1)) - 2 * k) * (x : ℝ) ^ k * (p : ℝ) ^ (k * (k - 1) / 2)
              * (((x / p : ℕ) : ℝ) + 1) ^ (vmvtExp k r)) := by ring
    _ ≤ (k.factorial : ℝ) * vmvtConst k r
          * (((2 : ℝ) ^ (k ^ 2) * 3) * (x : ℝ) ^ (vmvtExp k (r + 1))) :=
        mul_le_mul_of_nonneg_left hbracket_bound hfacnn
    _ = (k.factorial : ℝ) * vmvtConst k r * ((2 : ℝ) ^ (k ^ 2) * 3)
          * (x : ℝ) ^ (vmvtExp k (r + 1)) := by ring

/-! ## The large-`x` transversal step (sum over the pigeonhole prime set)

The transversal branch: select a **`k`-bounded** prime subset
`P₀ ⊆ {p ∈ (y, 2y] : prime}` of size `n₀ = ⌊k²(k−1)/2⌋+1` (just over the
pigeonhole threshold), so `#P₀² ≤ ¼k⁶` fits under `C₀`'s `k⁶`.  The pigeonhole
`distinctBox_le_card_mul_sum` gives `S₁ ≤ #P₀·∑_p Ncount(D₄(p))`, each term is
`transBox_le_const`, and the double `#P₀` folds into `k⁶`. -/

/-- The prime-count budget for the `k`-bounded transversal set:
`k²(k−1) < 2n₀` (pigeonhole surplus) and `4n₀² ≤ k⁶` (fits under `C₀`). -/
lemma n0_bounds {k : ℕ} (hk : 2 ≤ k) :
    k * k * (k - 1) < 2 * (k * k * (k - 1) / 2 + 1) ∧
    4 * (k * k * (k - 1) / 2 + 1) ^ 2 ≤ k ^ 6 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have he : (j + 2) - 1 = j + 1 := by omega
  rw [he]
  refine ⟨by omega, ?_⟩
  have hm : (j + 2) * (j + 2) * (j + 1) + 2 ≤ (j + 2) ^ 3 := by nlinarith [Nat.zero_le j]
  have hle : 2 * ((j + 2) * (j + 2) * (j + 1) / 2 + 1) ≤ (j + 2) ^ 3 := by omega
  calc 4 * ((j + 2) * (j + 2) * (j + 1) / 2 + 1) ^ 2
      = (2 * ((j + 2) * (j + 2) * (j + 1) / 2 + 1)) ^ 2 := by ring
    _ ≤ ((j + 2) ^ 3) ^ 2 := Nat.pow_le_pow_left hle 2
    _ = (j + 2) ^ 6 := by ring

/-- `m < 2C ⟹ ⌊m/2⌋+1 ≤ C` (the pigeonhole subset-size arithmetic). -/
lemma card_ge_of_pig {m C : ℕ} (h : m < 2 * C) : m / 2 + 1 ≤ C := by omega

/-- **The large-`x` transversal step.**  Given the pigeonhole prime supply in
`(y, 2y]` (`y = ⌈x^{1/k}⌉₊`), the large-`x` regime `x^{1/k} ≥ k²+4E(k,r)`, and the
inductive hypothesis at every dropped scale, one Linnik–Karatsuba step lands
`VmvtBound k (r+1) x`.  The degenerate `S₂` case is handled internally by
`vmvt_step_of_transversal_dominant`; the transversal `S₁` case is closed by the
per-prime `transBox_le_const` summed over the `k`-bounded set `P₀`, whose `#P₀²`
folds into `C₀`'s `k⁶`. -/
theorem vmvt_step_transversal_large {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * (r + 1)))
    (hk : 2 ≤ k) (hr : 1 ≤ r) (hinj : Function.Injective e)
    (hrange : ((k * (r + 1) : ℕ) : ℝ) ≤ vmvtExp k (r + 1)) (hx1 : 1 ≤ x)
    (hyk : k ≤ vmvtScale k x) (hy2 : 2 ≤ vmvtScale k x)
    (hpig : k * k * (k - 1)
      < 2 * ((Finset.Ioc (vmvtScale k x) (2 * vmvtScale k x)).filter Nat.Prime).card)
    (hreg : (k : ℝ) ^ 2 + 4 * vmvtExp k r ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
    (hIH : ∀ x', 1 ≤ x' → VmvtBound k r x') :
    VmvtBound k (r + 1) x := by
  classical
  refine vmvt_step_of_transversal_dominant x e hk hx1 hinj hrange (fun htransdom => ?_)
  set y := vmvtScale k x with hy
  obtain ⟨n0lt, n0sq⟩ := n0_bounds hk
  have hpigy : k * k * (k - 1)
      < 2 * ((Finset.Ioc y (2 * y)).filter Nat.Prime).card := by rw [hy]; exact hpig
  have hn0card : k * k * (k - 1) / 2 + 1
      ≤ ((Finset.Ioc y (2 * y)).filter Nat.Prime).card := card_ge_of_pig hpigy
  obtain ⟨P0, hP0sub, hP0card⟩ := Finset.exists_subset_card_eq hn0card
  have hP0prime : ∀ p ∈ P0, p.Prime := fun p hp => (Finset.mem_filter.mp (hP0sub hp)).2
  have hP0mem : ∀ p ∈ P0, p ∈ Finset.Ioc y (2 * y) :=
    fun p hp => (Finset.mem_filter.mp (hP0sub hp)).1
  have hP0gt : ∀ p ∈ P0, y < p := fun p hp => (Finset.mem_Ioc.mp (hP0mem p hp)).1
  have hP0le : ∀ p ∈ P0, p ≤ 2 * y := fun p hp => (Finset.mem_Ioc.mp (hP0mem p hp)).2
  have hP0pig : k * k * (k - 1) < 2 * P0.card := by rw [hP0card]; exact n0lt
  have hyx : x ≤ y ^ k := le_scale_pow (by omega)
  -- the pigeonhole covering (nat), cast to ℝ
  have hcov := distinctBox_le_card_mul_sum (k := k) (r := r + 1) x y e hy2 hyx P0
    hP0prime hP0gt hP0pig
  -- the uniform per-prime constant K
  set D : ℝ := vmvtConst k r with hDdef
  set K : ℝ := (k.factorial : ℝ) * D * ((2 : ℝ) ^ (k ^ 2) * 3) * (x : ℝ) ^ (vmvtExp k (r + 1))
    with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef, hDdef]
    have := vmvtConst_nonneg k r
    positivity
  have hper : ∀ p ∈ P0, (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ) ≤ K := by
    intro p hp
    have hpp := hP0prime p hp
    have hkp : k < p := lt_of_le_of_lt hyk (hP0gt p hp)
    have hxp : x < p ^ k := by
      have h1 : y ^ k < p ^ k := Nat.pow_lt_pow_left (hP0gt p hp) (by omega)
      omega
    have hp_le : (p : ℝ) ≤ 2 * (vmvtScale k x : ℝ) := by
      have := hP0le p hp; rw [← hy]; exact_mod_cast this
    have hIHp := hIH (x / p + 1) (Nat.le_add_left 1 (x / p))
    rw [VmvtBound] at hIHp
    exact transBox_le_const x p e hinj hpp hkp hk hxp hx1 hr hp_le hreg hIHp
  -- sum bound: ∑_p Ncount ≤ #P₀·K
  have hsum : (∑ p ∈ P0, (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ))
      ≤ (P0.card : ℝ) * K := by
    calc (∑ p ∈ P0, (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ))
        ≤ ∑ _p ∈ P0, K := Finset.sum_le_sum hper
      _ = (P0.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
  -- S₁ ≤ #P₀²·K
  have hS1 : (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e) : ℝ)
      ≤ (P0.card : ℝ) ^ 2 * K := by
    have hcovR : (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e) : ℝ)
        ≤ (P0.card : ℝ) * ∑ p ∈ P0,
            (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ) := by
      calc (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e) : ℝ)
          ≤ ((P0.card * ∑ p ∈ P0,
              Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℕ) : ℝ) := by
            exact_mod_cast hcov
        _ = (P0.card : ℝ) * ∑ p ∈ P0,
              (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ) := by push_cast; ring
    calc (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e) : ℝ)
        ≤ (P0.card : ℝ) * ∑ p ∈ P0,
            (Ncount k (k * (r + 1)) 0 (transBox x e p) (transBox x e p) : ℝ) := hcovR
      _ ≤ (P0.card : ℝ) * ((P0.card : ℝ) * K) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (P0.card : ℝ) ^ 2 * K := by ring
  -- fold #P₀² into k⁶ and conclude
  have h4sq : (4 : ℝ) * (P0.card : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 := by
    rw [hP0card]
    have : (4 : ℝ) * ((k * k * (k - 1) / 2 + 1 : ℕ) : ℝ) ^ 2 ≤ ((k ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast n0sq
    push_cast at this ⊢; linarith [this]
  rw [VmvtBound, vmvtConst_succ, ← hDdef]
  calc (JkI k (k * (r + 1)) x : ℝ)
      ≤ 4 * (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e) : ℝ) := htransdom
    _ ≤ 4 * ((P0.card : ℝ) ^ 2 * K) := by linarith [hS1]
    _ = (4 * (P0.card : ℝ) ^ 2) * ((k.factorial : ℝ) * ((2 : ℝ) ^ (k ^ 2) * 3))
          * (D * (x : ℝ) ^ (vmvtExp k (r + 1))) := by rw [hKdef]; ring
    _ ≤ (k : ℝ) ^ 6 * ((k.factorial : ℝ) * ((2 : ℝ) ^ (k ^ 2) * 3))
          * (D * (x : ℝ) ^ (vmvtExp k (r + 1))) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4sq (by positivity))
        rw [hDdef]; have := vmvtConst_nonneg k r; positivity
    -- re-grade: the old fixed value `k⁶·k!·2^{k²}·3` fits under `vmvtC0 = k^{8k²}`
    _ ≤ vmvtC0 k * (D * (x : ℝ) ^ (vmvtExp k (r + 1))) := by
        have hbridge := old_c0_le hk
        have hDx : (0 : ℝ) ≤ D * (x : ℝ) ^ (vmvtExp k (r + 1)) := by
          rw [hDdef]; have := vmvtConst_nonneg k r; positivity
        have hrw : (k : ℝ) ^ 6 * ((k.factorial : ℝ) * ((2 : ℝ) ^ (k ^ 2) * 3))
            = (k : ℝ) ^ 6 * (k.factorial : ℝ) * (2 : ℝ) ^ (k ^ 2) * 3 := by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_right hbridge hDx
    _ = vmvtC0 k * D * (x : ℝ) ^ (vmvtExp k (r + 1)) := by ring

end Salt.Vmvt
