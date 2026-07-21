/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PerronTrunc
import Salt.MR.ParsevalSL

/-!
# S8 MR-CORE, node A3a-R4 — the truncated-Perron assembly toward MR Lemma 14

Source pin: **MR arXiv v4** (`docs/sources/1501.04585v4.pdf`), §7 "Parseval bound",
pp. 21–23 (Lemma 14; frozen statement transcribed verbatim in `Salt.MR.ParsevalSL`).

This file assembles the *truncated* (finite-`T`) Perron representation the `Uⱼ`/`Vⱼ`
split of Lemma 14 consumes, on top of the landed discontinuous truncated-Perron core
`Salt.MR.perron_trunc` (`PerronTrunc.lean`) and its geometry.

## The R4 ladder

* **R4a — `perron_trunc_trivial`** (THE named small lemma): the *unconditional
  no-residue crossover bound* `‖perronContour y c T‖ ≤ 4·yᶜ·log(1 + T/c)`, valid for
  **all** `y > 0` (in particular across the `y ≈ 1` band where `perron_trunc`'s
  `1/|log y|` factor blows up).  Proven by the vertical-segment estimate
  `‖yˢ/s‖ = yᶜ/√(c²+t²) ≤ 2yᶜ/(c+|t|)` integrated over `Im s ∈ [−T,T]`; no `|log y|`
  anywhere.  The `log`-grade (not linear-in-`T`) shape is exactly what the summed
  error's crossover zone needs.

The residue-carrying decay bound (`perron_trunc`) and this residue-free bound
(`perron_trunc_trivial`) are the two branches of the per-term `min`-device that drive
the summed-error assembly.

All results are axiom-clean (`propext, Classical.choice, Quot.sound`); no
`native_decide`, no new axioms, no `sorry`.
-/

open MeasureTheory Complex Set intervalIntegral Filter Topology
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## Helper: the vertical-segment weight integral `∫_{−T}^T 1/(c+|t|)`. -/

/-- `∫_{−T}^T 1/(c+|t|) dt = 2·(log(c+T) − log c)` for `c > 0`, `T > 0`.  The two halves
are equal: on `[0,T]` the integrand is `1/(c+t)` (antiderivative `log(c+t)`); on `[−T,0]`
it is `1/(c−t)`, mapped to `[0,T]` by `t ↦ −t` (`integral_comp_neg`). -/
private lemma integral_inv_c_abs {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    (∫ t in (-T)..T, 1 / (c + |t|)) = 2 * (Real.log (c + T) - Real.log c) := by
  have hcT : (0 : ℝ) < c + T := by linarith
  have hR : (∫ t in (0:ℝ)..T, 1 / (c + |t|)) = Real.log (c + T) - Real.log c := by
    rw [intervalIntegral.integral_congr (g := fun t => 1 / (c + t)) ?_]
    · have hderiv : ∀ x ∈ uIcc (0:ℝ) T,
          HasDerivAt (fun t : ℝ => Real.log (c + t)) (1 / (c + x)) x := by
        intro x hx
        rw [uIcc_of_le hT.le, mem_Icc] at hx
        exact ((hasDerivAt_id x).const_add c).log (by simpa using (by linarith : c + x ≠ 0))
      have hcont : IntervalIntegrable (fun t : ℝ => 1 / (c + t)) volume 0 T := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro x hx; rw [uIcc_of_le hT.le, mem_Icc] at hx; nlinarith [hx.1]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]; simp
    · intro t ht; rw [uIcc_of_le hT.le, mem_Icc] at ht
      dsimp only; rw [abs_of_nonneg ht.1]
  have hL : (∫ t in (-T)..(0:ℝ), 1 / (c + |t|)) = Real.log (c + T) - Real.log c := by
    rw [intervalIntegral.integral_congr (g := fun t => 1 / (c + (-t))) ?_]
    · have hcn := intervalIntegral.integral_comp_neg (a := -T) (b := 0)
        (f := fun u => 1 / (c + u))
      simp only [neg_neg, neg_zero] at hcn
      rw [hcn, ← hR]
      apply intervalIntegral.integral_congr
      intro t ht; rw [uIcc_of_le hT.le, mem_Icc] at ht
      dsimp only; rw [abs_of_nonneg ht.1]
    · intro t ht; rw [uIcc_of_le (by linarith : -T ≤ (0:ℝ)), mem_Icc] at ht
      dsimp only; rw [abs_of_nonpos ht.2]
  have hInt : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => 1 / (c + |t|)) volume a b := by
    intro a b
    apply Continuous.intervalIntegrable
    fun_prop (disch := intro t; positivity)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hInt (-T) 0) (hInt 0 T), hL, hR]
  ring

/-- Continuity of `v ↦ yˢ/s` along the vertical segment `s = c + vi` (`c > 0`,
base `z > 0`) — mirrors `PerronTrunc.horiz_edge_norm`'s continuity argument.  Used for
interval integrability in the assembly. -/
private lemma pk_vert_cont {z c : ℝ} (hz : 0 < z) (hc : 0 < c) :
    Continuous (fun v : ℝ => pk z ((c : ℂ) + (v : ℂ) * I)) := by
  have hzC : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hne : ∀ v : ℝ, ((c : ℂ) + (v : ℂ) * I) ≠ 0 := by
    intro v hv
    have h1 : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    rw [hv] at h1; simp at h1; linarith
  refine Continuous.div ?_ ?_ hne
  · exact (continuous_id.const_cpow (Or.inl hzC)).comp (by fun_prop)
  · fun_prop

/-- The positive-real cpow division law `((y/m)ᵣ)ˢ = yˢ/mˢ` (`y, m > 0`), the algebra
behind the Dirichlet-polynomial per-term split `aₘ/mˢ · yˢ = aₘ·(y/m)ˢ`. -/
private lemma ofReal_div_cpow {y m : ℝ} (hy : 0 < y) (hm : 0 < m) (s : ℂ) :
    ((y / m : ℝ) : ℂ) ^ s = (y : ℂ) ^ s / (m : ℂ) ^ s := by
  have harg : (m : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hm.le]; exact Real.pi_pos.ne
  rw [div_eq_mul_inv y m, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hy.le (inv_nonneg.2 hm.le),
    Complex.ofReal_inv, Complex.inv_cpow (m : ℂ) s harg, div_eq_mul_inv]

/-! ## R4a — the unconditional no-residue crossover bound. -/

/-- **Truncated Perron, trivial (residue-free) bound** — `A3a-R4a`, THE named stone.
For `y > 0`, `c > 0`, `T > 0`, with no restriction `y ≠ 1`,
`‖perronContour y c T‖ ≤ 4·yᶜ·log(1 + T/c)`.

Unlike `perron_trunc` (whose `2yᶜ/(T·|log y|)` bound blows up as `y → 1`), this bound
carries no `|log y|` and so covers the `y ≈ 1` crossover band.  Proof: bound the
vertical segment `Im s ∈ [−T,T]` of `perronContour` by
`∫_{−T}^T ‖yˢ/s‖ = ∫_{−T}^T yᶜ/√(c²+t²) ≤ ∫_{−T}^T 2yᶜ/(c+|t|) = 4yᶜ·log(1+T/c)`
(via `‖s‖ = √(c²+t²) ≥ (c+|t|)/2`). -/
theorem perron_trunc_trivial {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronContour y c T‖ ≤ 4 * (y : ℝ) ^ c * Real.log (1 + T / c) := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hcT : (0 : ℝ) < c + T := by linarith
  have hne : ∀ v : ℝ, ((c : ℂ) + (v : ℂ) * I) ≠ 0 := by
    intro v hv
    have h1 : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    rw [hv] at h1; simp at h1; linarith
  have hpk_cont : Continuous (fun v : ℝ => pk y ((c : ℂ) + (v : ℂ) * I)) := by
    refine Continuous.div ?_ ?_ hne
    · exact (continuous_id.const_cpow (Or.inl hyC)).comp (by fun_prop)
    · fun_prop
  have hnorm : ∀ v : ℝ,
      ‖pk y ((c : ℂ) + (v : ℂ) * I)‖ = y ^ c / Real.sqrt (c ^ 2 + v ^ 2) := by
    intro v
    rw [pk, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : ((c : ℂ) + (v : ℂ) * I).re = c := by simp
    rw [hre, Complex.norm_add_mul_I]
  have hpt : ∀ v : ℝ, ‖pk y ((c : ℂ) + (v : ℂ) * I)‖ ≤ 2 * y ^ c / (c + |v|) := by
    intro v
    rw [hnorm v]
    have hden : (0 : ℝ) < c + |v| := by positivity
    have hsqrt : (0 : ℝ) < Real.sqrt (c ^ 2 + v ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hbnd : c + |v| ≤ 2 * Real.sqrt (c ^ 2 + v ^ 2) := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ c + |v|)]
      have h4X : (2:ℝ) * Real.sqrt (c ^ 2 + v ^ 2) = Real.sqrt (4 * (c ^ 2 + v ^ 2)) := by
        rw [show (4:ℝ) * (c ^ 2 + v ^ 2) = 2 ^ 2 * (c ^ 2 + v ^ 2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      rw [h4X]; apply Real.sqrt_le_sqrt
      nlinarith [sq_abs v, sq_nonneg (c - |v|), abs_nonneg v]
    rw [div_le_div_iff₀ hsqrt hden]
    have hyc : (0:ℝ) ≤ y ^ c := (Real.rpow_pos_of_pos hy c).le
    nlinarith [mul_le_mul_of_nonneg_left hbnd hyc]
  have hstep1 : ‖perronContour y c T‖ ≤ ∫ v in (-T)..T, ‖pk y ((c : ℂ) + (v : ℂ) * I)‖ := by
    rw [perronContour, norm_mul, Complex.norm_I, one_mul]
    exact intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hb_cont : Continuous (fun v : ℝ => 2 * y ^ c / (c + |v|)) := by
    fun_prop (disch := intro v; positivity)
  have hstep2 : (∫ v in (-T)..T, ‖pk y ((c : ℂ) + (v : ℂ) * I)‖)
      ≤ ∫ v in (-T)..T, 2 * y ^ c / (c + |v|) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hpk_cont.norm.intervalIntegrable (-T) T) (hb_cont.intervalIntegrable (-T) T)
    intro v _; exact hpt v
  have hstep3 : (∫ v in (-T)..T, 2 * y ^ c / (c + |v|))
      = 4 * y ^ c * (Real.log (c + T) - Real.log c) := by
    have hconst : (∫ v in (-T)..T, 2 * y ^ c / (c + |v|))
        = (2 * y ^ c) * ∫ v in (-T)..T, 1 / (c + |v|) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v _; dsimp only; ring
    rw [hconst, integral_inv_c_abs hc hT]; ring
  have hlogconv : Real.log (1 + T / c) = Real.log (c + T) - Real.log c := by
    rw [show (1:ℝ) + T / c = (c + T) / c by field_simp, Real.log_div hcT.ne' hc.ne']
  rw [hlogconv]
  calc ‖perronContour y c T‖
      ≤ ∫ v in (-T)..T, ‖pk y ((c : ℂ) + (v : ℂ) * I)‖ := hstep1
    _ ≤ ∫ v in (-T)..T, 2 * y ^ c / (c + |v|) := hstep2
    _ = 4 * y ^ c * (Real.log (c + T) - Real.log c) := hstep3

/-! ## R4b — the per-term `min`-device. -/

/-- **Truncated Perron, per-term `min` form** — `A3a-R4b`.  For `y > 0`, `y ≠ 1`,
`c > 0`, `T > 0`, the per-term truncated-Perron error obeys
`‖perronContour y c T − 2πi·𝟙(y>1)‖ ≤ 2·yᶜ·min(π + 2·log(1+T/c), 1/(T·|log y|))`.

The two branches: the decay branch `1/(T·|log y|)` is `perron_trunc`; the crossover
branch `π + 2·log(1+T/c)` (finite as `y → 1`) is `perron_trunc_trivial` plus the
residue triangle inequality (`‖2πi‖ = 2π ≤ 2π·yᶜ` when `y > 1`, since `yᶜ ≥ 1`).  This
is the classical `min{BIG, 1/(T|log y|)}` device: `BIG` covers the `y ≈ 1` band that
the summed error's crossover zone lives in, while `1/(T|log y|)` gains for `m` far from
`x`.  Feeds the summed-error assembly with `y = x/m`. -/
theorem perron_trunc_min {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronContour y c T - 2 * (Real.pi : ℂ) * I * (if 1 < y then (1 : ℂ) else 0)‖
      ≤ 2 * (y : ℝ) ^ c
          * min (Real.pi + 2 * Real.log (1 + T / c)) (1 / (T * |Real.log y|)) := by
  have hyc_pos : (0 : ℝ) < y ^ c := Real.rpow_pos_of_pos hy c
  have hTc : (0 : ℝ) < T / c := div_pos hT hc
  have hlog_nn : (0 : ℝ) ≤ Real.log (1 + T / c) := Real.log_nonneg (by linarith)
  have h_triv := perron_trunc_trivial hy hc hT
  -- the crossover (residue-free) branch
  have h_big : ‖perronContour y c T - 2 * (Real.pi : ℂ) * I * (if 1 < y then (1 : ℂ) else 0)‖
      ≤ 2 * y ^ c * (Real.pi + 2 * Real.log (1 + T / c)) := by
    by_cases hgt : 1 < y
    · rw [if_pos hgt, mul_one]
      have hrho : ‖2 * (Real.pi : ℂ) * I‖ = 2 * Real.pi := by
        simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      have hy1c : (1 : ℝ) ≤ y ^ c := Real.one_le_rpow hgt.le hc.le
      calc ‖perronContour y c T - 2 * (Real.pi : ℂ) * I‖
          ≤ ‖perronContour y c T‖ + ‖2 * (Real.pi : ℂ) * I‖ := norm_sub_le _ _
        _ ≤ 4 * y ^ c * Real.log (1 + T / c) + 2 * Real.pi := by rw [hrho]; linarith
        _ ≤ 2 * y ^ c * (Real.pi + 2 * Real.log (1 + T / c)) := by
            nlinarith [hy1c, hlog_nn, Real.pi_pos]
    · rw [if_neg hgt, mul_zero, sub_zero]
      calc ‖perronContour y c T‖ ≤ 4 * y ^ c * Real.log (1 + T / c) := h_triv
        _ ≤ 2 * y ^ c * (Real.pi + 2 * Real.log (1 + T / c)) := by
            nlinarith [hyc_pos, hlog_nn, Real.pi_pos]
  -- the decay branch
  have h_perron := perron_trunc hy hy1 hc hT
  have h_dec : ‖perronContour y c T - 2 * (Real.pi : ℂ) * I * (if 1 < y then (1 : ℂ) else 0)‖
      ≤ 2 * y ^ c * (1 / (T * |Real.log y|)) := h_perron.trans_eq (by ring)
  rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 * y ^ c)]
  exact le_min h_big h_dec

/-! ## R4c — the summed-error assembly (per-term `min`-device over the range). -/

/-- **Truncated Perron, summed error over the Dirichlet range** — `A3a-R4c`.  For a
finite index set `s0` of positive integers `m` with `(m:ℝ) ≠ y` (so `y/m ≠ 1`),
coefficients `a m`, and `y, c, T > 0`, the summed truncated-Perron error is controlled
term-by-term by the `min`-device:
`‖∑ₘ aₘ·(perronContour (y/m) c T − 2πi·𝟙(y/m>1))‖`
`  ≤ ∑ₘ ‖aₘ‖·2·(y/m)ᶜ·min(π + 2·log(1+T/c), 1/(T·|log(y/m)|))`.

This is the "summed-error assembly" backbone: `∑ₘ aₘ·perronContour (y/m)` is the
truncated integral `(1/2πi)∫_{c−iT}^{c+iT} A(s)·yˢ/s ds` (per-term linearity), and
`∑ₘ aₘ·𝟙(y/m>1) = ∑_{m<y} aₘ` is the arithmetic partial sum; the difference is the
error `E(y,T)` bounded here.  Reduction of this `min`-sum to the classical
`(y/T)·log`-grade bound (the three-zone `δ ~ 1/T` optimization) is recorded in the
node NOTES; with `‖aₘ‖ ≤ 1` and `c = 1` each `(y/m)ᶜ` is `O(1)` on the MR range. -/
theorem perron_sum_error_bound (a : ℕ → ℂ) (s0 : Finset ℕ) {y c T : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hpos : ∀ m ∈ s0, 0 < m) (hne : ∀ m ∈ s0, (m : ℝ) ≠ y) :
    ‖∑ m ∈ s0, a m * (perronContour (y / m) c T
        - 2 * (Real.pi : ℂ) * I * (if 1 < y / m then (1 : ℂ) else 0))‖
      ≤ ∑ m ∈ s0, ‖a m‖ * (2 * (y / m) ^ c
          * min (Real.pi + 2 * Real.log (1 + T / c)) (1 / (T * |Real.log (y / m)|))) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hpos m hm
  have hym0 : 0 < y / m := div_pos hy hmpos
  have hym1 : y / m ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq hmpos.ne'] at h
    exact hne m hm h.symm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (perron_trunc_min hym0 hym1 hc hT) (norm_nonneg _)

/-! ## R4d — the finite-`T` truncated-Perron representation. -/

/-- **Per-term linearity of the truncated A-integral** — the assembly identity.  For
`A(s) = ∑_{m ∈ s0} aₘ/mˢ` (positive integer indices) and `y > 0`, `c > 0`, the truncated
contour value factors over the Dirichlet sum:
`(1/2πi)∫_{c−iT}^{c+iT} A(s)·yˢ/s ds` (i.e. `I·∫_{−T}^T (∑ₘ aₘ/mˢ)·yˢ/s dv`) equals
`∑_{m ∈ s0} aₘ·perronContour (y/m) c T`.  Pulls the finite sum out of the integral
(`integral_finsetSum`) after the per-term split `aₘ/mˢ·yˢ = aₘ·(y/m)ˢ`
(`ofReal_div_cpow`). -/
theorem Aperron_eq_sum (a : ℕ → ℂ) (s0 : Finset ℕ) {y c T : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hpos : ∀ m ∈ s0, 0 < m) :
    I * ∫ v in (-T)..T, (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
        * (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I)
      = ∑ m ∈ s0, a m * perronContour (y / m) c T := by
  have hpt : ∀ v : ℝ,
      (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
          * (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I)
        = ∑ m ∈ s0, a m * pk (y / m) ((c : ℂ) + (v : ℂ) * I) := by
    intro v
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hpos m hm
    rw [pk, ofReal_div_cpow hy hmpos, Complex.ofReal_natCast]; ring
  have hint : ∀ m ∈ s0, IntervalIntegrable
      (fun v : ℝ => a m * pk (y / m) ((c : ℂ) + (v : ℂ) * I)) volume (-T) T := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hpos m hm
    exact (continuous_const.mul (pk_vert_cont (div_pos hy hmpos) hc)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun v _ => hpt v),
    intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_const_mul, perronContour]; ring

/-- **The finite-`T` truncated-Perron representation with explicit error** — `A3a-R4d`.
The truncated contour integral `∫_{c−iT}^{c+iT} A(s)·yˢ/s ds` (`= I·∫_{−T}^T (…) dv`,
un-normalized: `2πi` times the `(1/2πi)∫` of Perron) equals the residue sum
`2πi·∑_{m<y} aₘ` (here `2πi·∑ₘ aₘ·𝟙(y/m>1)`) up to an error `E(y,T)` with
`‖E(y,T)‖ ≤ ∑ₘ ‖aₘ‖·2(y/m)ᶜ·min(π + 2·log(1+T/c), 1/(T·|log(y/m)|))`.

Taking `y = x+hⱼ` and `y = x` and subtracting realises MR's
`Sⱼ(x) = (1/2πi)∫ A(s)((x+hⱼ)ˢ−xˢ)/s ds + E` (v4 p. 21) at finite `T`; the residue
difference is the interval count `∑_{x<m≤x+hⱼ} aₘ = Sⱼ(x)`.  Combines `Aperron_eq_sum`
(the linearity identity) with `perron_sum_error_bound` (the summed `min`-device). -/
theorem Aperron_representation (a : ℕ → ℂ) (s0 : Finset ℕ) {y c T : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hpos : ∀ m ∈ s0, 0 < m) (hne : ∀ m ∈ s0, (m : ℝ) ≠ y) :
    ‖(I * ∫ v in (-T)..T, (∑ m ∈ s0, a m / (m : ℂ) ^ ((c : ℂ) + (v : ℂ) * I))
          * (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I))
        - 2 * (Real.pi : ℂ) * I * ∑ m ∈ s0, a m * (if 1 < y / m then (1 : ℂ) else 0)‖
      ≤ ∑ m ∈ s0, ‖a m‖ * (2 * (y / m) ^ c
          * min (Real.pi + 2 * Real.log (1 + T / c)) (1 / (T * |Real.log (y / m)|))) := by
  rw [Aperron_eq_sum a s0 hy hc hpos]
  have hsplit : (∑ m ∈ s0, a m * perronContour (y / m) c T)
        - 2 * (Real.pi : ℂ) * I * ∑ m ∈ s0, a m * (if 1 < y / m then (1 : ℂ) else 0)
      = ∑ m ∈ s0, a m * (perronContour (y / m) c T
          - 2 * (Real.pi : ℂ) * I * (if 1 < y / m then (1 : ℂ) else 0)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_; ring
  rw [hsplit]
  exact perron_sum_error_bound a s0 hy hc hT hpos hne

end Salt.MR
