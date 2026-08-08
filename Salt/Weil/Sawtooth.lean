/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.Completion
import Salt.MR.Sawtooth
import Mathlib

/-!
# WEIL-TRIO W5 — the sawtooth kit (HB 1983, §7)

Governing design: `docs/exploration/weil-trio-design-0806.md` (v2 §D5 — the degenerate-case
discipline and the sixth exit row).  Source math: `docs/sources/hb1983-notes.md:747-770`.

This module is a **supply depot**: it delivers the three harmonic-analysis inputs that N7
(Lemma 10) assembles (7.6)–(7.8) from.  N7 itself does **not** live here.

* **S1 — (7.2), the sawtooth Fourier expansion.**  For `ψ θ = Int.fract θ − 1/2` and `K ≥ 1`,
  `ψ θ = −∑_{0<|m|≤K} e(mθ)/(2πim) + R_K θ` with the explicit majorant
  `‖R_K θ‖ ≤ (5/2) · Min(1/(K·‖θ‖), 1)`, in the §D5 degenerate-split form (the arm
  `dist₁ θ 0 = 0` carries the value `1`, not a junk `⊤`).  No `O(·)`.
* **S2 — (7.3)/(7.4), the majorant's own Fourier coefficients.**  **Both arms**:
  `integral_sawtoothMajorant_eq` (the `L¹` mass, exactly `2(1 + log(K/2))/K`),
  `norm_majorantCoeff_le` (`‖a_m‖ ≤ 2(1 + log K)/K` for every `m`, `a₀` included), and
  `norm_majorantCoeff_le_sq` (`‖a_m‖ ≤ K/(π²m²)` for `m ≠ 0`), and — from the two arms together —
  the `L¹` row `tsum_norm_majorantCoeff_le` (`∑_{m∈ℤ} ‖a_m‖ ≤ 6(1 + log K)`, also in the source's
  literal shape as `tsum_norm_majorantCoeff_le_log`) with its load-bearing
  `summable_norm_majorantCoeff`.  (7.3) itself, which is downstream of the second arm, is still
  banked in `docs/blueprints/flags.md`.
* **S3 — the sixth exit row, the congruence-restricted completion.**  For `q ∣ k` and any
  `b, s`, `‖∑_{n ∈ (A,B], n ≡ b (q)} e(−s·n/k)‖ ≤ Min(B−A, (2·dist₁(sq/k, 0))⁻¹)`, again with
  the degenerate arm (`k ∣ sq`) split off.

Conventions, both load-bearing (`hb1983-notes.md:883-903`, the notation hazard sheet):

* `e x = exp(2πi x)` is `Salt.LS.e` (`Salt/LS/Defs.lean:31`) — the same additive character the
  completion kernel `Salt.BV.sum_e_eq` (`Salt/BV/Completion.lean:76`) is built on.
* `‖θ‖` (distance to the nearest integer) is `Salt.LS.dist₁ θ 0` (`Salt/LS/Dist.lean:29`), the
  corpus's `dist₁` apparatus reused verbatim.
-/

namespace Salt.Weil

open scoped BigOperators
open Salt.LS Salt.BV

/-! ### `e`- and `dist₁`-arithmetic (local re-derivations of the completion kernel's privates) -/

/-- `e (n·x) = (e x)^n` for `n : ℕ`. -/
private lemma e_natMul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = (e x) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h : ((m + 1 : ℕ) : ℝ) * x = (m : ℝ) * x + x := by push_cast; ring
      rw [h, e_add, ih, pow_succ]

/-- `dist₁` only sees the difference: `dist₁ x y = dist₁ (x − y) 0`. -/
lemma dist₁_sub_zero (x y : ℝ) : dist₁ x y = dist₁ (x - y) 0 := by
  unfold dist₁; rw [sub_zero]

/-- `dist₁` is negation-symmetric at `0`: `dist₁ (−x) 0 = dist₁ x 0`. -/
lemma dist₁_neg_zero (x : ℝ) : dist₁ (-x) 0 = dist₁ x 0 := by
  have h : dist₁ (-x) 0 = dist₁ 0 x := by unfold dist₁; simp only [sub_zero, zero_sub]
  rw [h, dist₁_comm]

/-! ## S1 — (7.2), the sawtooth Fourier expansion

HB p.221: `ψ(θ) = −∑_{0<|m|≤K} e(mθ)/(2πim) + O(Min(1/(K‖θ‖), 1))`.  The `O(·)` is replaced
here by the explicit constant `5/2`.

**Corpus reuse (the VK-forgetting lesson, `flags.md:21016`).**  The analytic core is already in
the corpus and is *not* re-proved here:

* `Salt.MR.tendsto_sum_sin_div_nat` (`Salt/MR/Sawtooth.lean:358`) — the sawtooth Fourier series
  `∑_{n≥1} sin(2πnx)/n → π(1/2 − x)` on `(0,1)`, the conditionally convergent identity mathlib
  lacks (it was landed for the Hurwitz-zeta `k = 0` case of `LandauOdd`);
* `Salt.MR.abs_sum_sin_le` (`:329`) — `|∑_{n<N} sin(2πnx)| ≤ 1/sin(πx)`;
* `Salt.MR.abs_sum_shift_mul_le_of_bounded` (`:100`) — Abel's inequality in tail form.

What is new here is only the *rate*: the tail `∑_{n>K}` is Abel-summed against `1/n`, giving
`|R_K θ| ≤ (π(K+1)‖θ‖)⁻¹` off the integers, and a direct `|sin| ≤ 2π‖·‖` estimate gives the
uniform arm `|R_K θ| ≤ 1/2 + 2K‖θ‖`.
-/

/-- The sawtooth `ψ θ = θ − ⌊θ⌋ − 1/2` (`Int.fract θ − 1/2`). -/
noncomputable def sawtooth (θ : ℝ) : ℝ := Int.fract θ - 1 / 2

/-- The truncated Fourier sum of (7.2): `−∑_{0<|m|≤K} e(mθ)/(2πim)`. -/
noncomputable def sawtoothFourier (K : ℕ) (θ : ℝ) : ℂ :=
  -∑ m ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0,
      e ((m : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))

/-- The (7.2) remainder `R_K`, defined as the exact defect of the truncated series. -/
noncomputable def sawtoothRem (K : ℕ) (θ : ℝ) : ℂ := (sawtooth θ : ℂ) - sawtoothFourier K θ

/-- The (7.2) majorant `Min(1/(K‖θ‖), 1)`, in the §D5 **degenerate-split** form: on the
integers (`dist₁ θ 0 = 0`) the value is the honest `1`, never a junk `⊤` or `0`. -/
noncomputable def sawtoothMajorant (K : ℕ) (θ : ℝ) : ℝ :=
  if dist₁ θ 0 = 0 then 1 else min (((K : ℝ) * dist₁ θ 0)⁻¹) 1

/-- **(7.2), the identity half.**  N7 quotes this as (7.2): the sawtooth *equals* its truncated
Fourier sum plus `R_K`, with no hypotheses at all.  The size of `R_K` is
`norm_sawtoothRem_le`. -/
theorem sawtooth_fourier_expansion (K : ℕ) (θ : ℝ) :
    (sawtooth θ : ℂ) = sawtoothFourier K θ + sawtoothRem K θ := by
  unfold sawtoothRem; ring

/-! ### The complex truncation collapses to a real sine sum -/

/-- `e` in Cartesian form. -/
private lemma e_eq_cos_add_sin (x : ℝ) :
    e x = (Real.cos (2 * Real.pi * x) : ℂ) + (Real.sin (2 * Real.pi * x) : ℂ) * Complex.I := by
  unfold e
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
        = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- The `±m` pair of (7.2) collapses to the real term `sin(2πmθ)/(πm)`. -/
private lemma e_pair (θ : ℝ) {m : ℤ} (hm : m ≠ 0) :
    e ((m : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
      + e (((-m : ℤ) : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (((-m : ℤ)) : ℂ))
      = ((Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : 2 * Real.pi * ((m : ℝ) * θ) = 2 * Real.pi * θ * (m : ℝ) := by ring
  have h2 : 2 * Real.pi * ((((-m : ℤ)) : ℝ) * θ) = -(2 * Real.pi * θ * (m : ℝ)) := by
    push_cast; ring
  rw [e_eq_cos_add_sin, e_eq_cos_add_sin, h1, h2, Real.cos_neg, Real.sin_neg]
  push_cast
  field_simp
  ring

/-- The `K = 0` .. `K` induction collapsing (7.2)'s two-sided sum to a one-sided sine sum. -/
private lemma icc_erase_succ (K : ℕ) :
    (Finset.Icc (-((K : ℤ) + 1)) ((K : ℤ) + 1)).erase 0
      = insert ((K : ℤ) + 1)
          (insert (-((K : ℤ) + 1)) ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0)) := by
  ext m
  simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
  omega

private lemma sum_pair_eq (K : ℕ) (θ : ℝ) :
    ∑ m ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0,
        e ((m : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
      = ((∑ m ∈ Finset.range (K + 1),
            Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hcast : ((K + 1 : ℕ) : ℤ) = (K : ℤ) + 1 := by push_cast; ring
      have hnm1 : ((K : ℤ) + 1) ∉
          insert (-((K : ℤ) + 1)) ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0) := by
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
        omega
      have hnm2 : (-((K : ℤ) + 1)) ∉ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 := by
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [hcast, icc_erase_succ K, Finset.sum_insert hnm1, Finset.sum_insert hnm2,
        Finset.sum_range_succ]
      have hpair := e_pair θ (m := (K : ℤ) + 1) (by omega)
      push_cast at hpair ⊢
      rw [ih] at *
      push_cast
      rw [← hpair]
      ring

private lemma sawtoothFourier_eq (K : ℕ) (θ : ℝ) :
    sawtoothFourier K θ
      = ((-∑ m ∈ Finset.range (K + 1),
            Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) := by
  unfold sawtoothFourier
  rw [sum_pair_eq]
  push_cast
  ring

/-- The real remainder behind `sawtoothRem`. -/
private noncomputable def remReal (K : ℕ) (θ : ℝ) : ℝ :=
  sawtooth θ + ∑ m ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)

private lemma norm_sawtoothRem_eq (K : ℕ) (θ : ℝ) : ‖sawtoothRem K θ‖ = |remReal K θ| := by
  unfold sawtoothRem remReal
  rw [sawtoothFourier_eq]
  rw [show ((sawtooth θ : ℝ) : ℂ)
        - ((-∑ m ∈ Finset.range (K + 1),
              Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ)
      = ((sawtooth θ + ∑ m ∈ Finset.range (K + 1),
              Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-! ### The uniform arm: `|R_K θ| ≤ 1/2 + 2K‖θ‖` -/

/-- `|sin (2π y)| ≤ 2π·dist₁(y, 0)`: reduce `y` mod `1` and use `|sin t| ≤ |t|`. -/
private lemma abs_sin_le_two_pi_dist (y : ℝ) :
    |Real.sin (2 * Real.pi * y)| ≤ 2 * Real.pi * dist₁ y 0 := by
  have hred : Real.sin (2 * Real.pi * y)
      = Real.sin (2 * Real.pi * (y - (round y : ℝ))) := by
    rw [show 2 * Real.pi * (y - (round y : ℝ))
          = 2 * Real.pi * y + (-(round y) : ℤ) * (2 * Real.pi) by push_cast; ring,
      Real.sin_add_int_mul_two_pi]
  have hd : dist₁ y 0 = |y - (round y : ℝ)| := by unfold dist₁; simp only [sub_zero]
  rw [hred, hd]
  calc |Real.sin (2 * Real.pi * (y - (round y : ℝ)))| ≤ |2 * Real.pi * (y - (round y : ℝ))| :=
        Real.abs_sin_le_abs
    _ = 2 * Real.pi * |y - (round y : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- Subadditivity of `dist₁` along `ℕ`-multiples: `‖nθ‖ ≤ n‖θ‖`. -/
private lemma dist₁_natMul_le (θ : ℝ) : ∀ i : ℕ,
    dist₁ (θ * ((i : ℝ) + 1)) 0 ≤ ((i : ℝ) + 1) * dist₁ θ 0 := by
  intro i
  induction i with
  | zero => simp
  | succ j ihj =>
      have hstep : dist₁ (θ * (((j : ℝ) + 1) + 1)) 0
          ≤ dist₁ (θ * (((j : ℝ) + 1) + 1)) (θ * ((j : ℝ) + 1)) + dist₁ (θ * ((j : ℝ) + 1)) 0 :=
        dist₁_triangle _ _ _
      have heq : dist₁ (θ * (((j : ℝ) + 1) + 1)) (θ * ((j : ℝ) + 1)) = dist₁ θ 0 := by
        rw [dist₁_sub_zero, show θ * (((j : ℝ) + 1) + 1) - θ * ((j : ℝ) + 1) = θ from by ring]
      rw [heq] at hstep
      have hd0 : (0 : ℝ) ≤ dist₁ θ 0 := dist₁_nonneg _ _
      push_cast
      nlinarith [hstep, ihj, hd0]

/-- Each `m`-term of the truncation is `≤ 2‖θ‖` in modulus (`m ≥ 1`). -/
private lemma abs_term_le (θ : ℝ) (i : ℕ) :
    |Real.sin (2 * Real.pi * θ * ((i : ℝ) + 1)) / (Real.pi * ((i : ℝ) + 1))|
      ≤ 2 * dist₁ θ 0 := by
  have hpos : (0 : ℝ) < Real.pi * ((i : ℝ) + 1) := by positivity
  have hkey : |Real.sin (2 * Real.pi * (θ * ((i : ℝ) + 1)))|
      ≤ 2 * Real.pi * ((i : ℝ) + 1) * dist₁ θ 0 := by
    refine le_trans (abs_sin_le_two_pi_dist (θ * ((i : ℝ) + 1))) ?_
    nlinarith [dist₁_nonneg θ 0, dist₁_natMul_le θ i, Real.pi_pos]
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos,
    show 2 * Real.pi * θ * ((i : ℝ) + 1) = 2 * Real.pi * (θ * ((i : ℝ) + 1)) by ring]
  nlinarith [hkey, Real.pi_pos, dist₁_nonneg θ 0]

/-- **The uniform arm of (7.2).**  `|R_K θ| ≤ 1/2 + 2K‖θ‖`, valid at every real `θ`
(including the integers, where it reads `|R_K θ| = 1/2`). -/
theorem norm_sawtoothRem_le_linear (K : ℕ) (θ : ℝ) :
    ‖sawtoothRem K θ‖ ≤ 1 / 2 + 2 * (K : ℝ) * dist₁ θ 0 := by
  rw [norm_sawtoothRem_eq]
  unfold remReal
  have hpsi : |sawtooth θ| ≤ 1 / 2 := by
    unfold sawtooth
    rw [abs_le]
    constructor
    · linarith [Int.fract_nonneg θ]
    · linarith [Int.fract_lt_one θ]
  have hsum : |∑ m ∈ Finset.range (K + 1),
      Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)| ≤ 2 * (K : ℝ) * dist₁ θ 0 := by
    rw [Finset.sum_range_succ' (fun m : ℕ => Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)) K]
    simp only [Nat.cast_zero, mul_zero, Real.sin_zero, mul_zero, zero_div, add_zero]
    calc |∑ i ∈ Finset.range K,
            Real.sin (2 * Real.pi * θ * ((i : ℕ) + 1 : ℕ)) / (Real.pi * ((i : ℕ) + 1 : ℕ))|
        ≤ ∑ i ∈ Finset.range K,
            |Real.sin (2 * Real.pi * θ * ((i : ℕ) + 1 : ℕ)) / (Real.pi * ((i : ℕ) + 1 : ℕ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range K, 2 * dist₁ θ 0 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have := abs_term_le θ i
          push_cast
          exact this
      _ = 2 * (K : ℝ) * dist₁ θ 0 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc |sawtooth θ + ∑ m ∈ Finset.range (K + 1),
          Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)|
      ≤ |sawtooth θ| + |∑ m ∈ Finset.range (K + 1),
          Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)| := abs_add_le _ _
    _ ≤ 1 / 2 + 2 * (K : ℝ) * dist₁ θ 0 := add_le_add hpsi hsum

/-! ### The sharp arm: `|R_K θ| ≤ (π(K+1)‖θ‖)⁻¹` off the integers -/

/-- Jordan's inequality in the form `2‖x‖ ≤ sin(πx)` on `[0,1]`. -/
private lemma two_dist_le_sin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    2 * dist₁ x 0 ≤ Real.sin (Real.pi * x) := by
  have hle_x : dist₁ x 0 ≤ x := by
    have := dist₁_le_abs x 0
    rwa [sub_zero, abs_of_nonneg hx0] at this
  have hle_1x : dist₁ x 0 ≤ 1 - x := by
    have h1 : dist₁ x 0 = dist₁ x 1 := by
      have := dist₁_add_int_right x 0 1
      simpa using this.symm
    have h2 := dist₁_le_abs x 1
    rw [← h1] at h2
    rcases le_or_gt x 1 with h | h
    · rwa [abs_of_nonpos (by linarith), neg_sub] at h2
    · linarith [dist₁_nonneg x 0]
  rcases le_or_gt x (1 / 2) with hhalf | hhalf
  · have hj := Real.mul_le_sin (x := Real.pi * x) (by positivity)
      (by nlinarith [Real.pi_pos])
    have : 2 / Real.pi * (Real.pi * x) = 2 * x := by
      field_simp
    rw [this] at hj
    linarith
  · have hsym : Real.sin (Real.pi * x) = Real.sin (Real.pi * (1 - x)) := by
      rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring, Real.sin_pi_sub]
    have hj := Real.mul_le_sin (x := Real.pi * (1 - x)) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
    have hcalc : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [hcalc] at hj
    rw [hsym]
    linarith

/-- The tail block of the sine series, in the form Abel's inequality consumes. -/
private lemma sum_tail_eq (x : ℝ) (K M : ℕ) :
    ∑ i ∈ Finset.range M,
        Real.sin (2 * Real.pi * x * ((i + K + 1 : ℕ) : ℝ)) * (1 / (((i + K : ℕ) : ℝ) + 1))
      = (∑ n ∈ Finset.range (K + 1 + M), Real.sin (2 * Real.pi * x * n) / n)
        - ∑ n ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * x * n) / n := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, show K + 1 + (M + 1) = K + 1 + M + 1 from rfl,
        Finset.sum_range_succ (fun n : ℕ => Real.sin (2 * Real.pi * x * n) / n) (K + 1 + M)]
      have h1 : ((M + K + 1 : ℕ) : ℝ) = ((K + 1 + M : ℕ) : ℝ) := by push_cast; ring
      have h2 : ((M + K : ℕ) : ℝ) + 1 = ((K + 1 + M : ℕ) : ℝ) := by push_cast; ring
      rw [h1, h2]
      ring

/-- `dist₁` is invariant under passing to the fractional part. -/
private lemma dist₁_fract (θ : ℝ) : dist₁ (Int.fract θ) 0 = dist₁ θ 0 := by
  have h := dist₁_add_int_left θ 0 (-⌊θ⌋)
  have hf := Int.floor_add_fract θ
  have he : θ + (((-⌊θ⌋ : ℤ)) : ℝ) = Int.fract θ := by push_cast; linarith
  rwa [he] at h

/-- `sin` is invariant under passing to the fractional part in `2πθm`. -/
private lemma sin_fract (θ : ℝ) (m : ℕ) :
    Real.sin (2 * Real.pi * Int.fract θ * m) = Real.sin (2 * Real.pi * θ * m) := by
  have hf := Int.floor_add_fract θ
  have hfe : Int.fract θ = θ - (⌊θ⌋ : ℝ) := by linarith
  rw [hfe, show 2 * Real.pi * (θ - (⌊θ⌋ : ℝ)) * (m : ℝ)
        = 2 * Real.pi * θ * (m : ℝ) + ((-(⌊θ⌋ * (m : ℕ))) : ℤ) * (2 * Real.pi) by push_cast; ring,
    Real.sin_add_int_mul_two_pi]

/-- `a/(π·m) = (1/π)·(a/m)`, unconditionally (also at `m = 0`). -/
private lemma div_pi_mul (a : ℝ) (m : ℕ) : a / (Real.pi * m) = (1 / Real.pi) * (a / m) := by
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **The sharp arm of (7.2).**  Off the integers, `|R_K θ| ≤ (π(K+1)‖θ‖)⁻¹`.  This is where
the corpus's `tendsto_sum_sin_div_nat` (the conditionally convergent sawtooth Fourier series)
and Abel's inequality do the work. -/
theorem norm_sawtoothRem_le_dist (K : ℕ) {θ : ℝ} (hθ : dist₁ θ 0 ≠ 0) :
    ‖sawtoothRem K θ‖ ≤ (Real.pi * ((K : ℝ) + 1) * dist₁ θ 0)⁻¹ := by
  have hdx : dist₁ (Int.fract θ) 0 = dist₁ θ 0 := dist₁_fract θ
  have hx0 : 0 < Int.fract θ := by
    rcases lt_or_eq_of_le (Int.fract_nonneg θ) with h | h
    · exact h
    · exact absurd (by rw [← hdx, ← h]; exact dist₁_self 0) hθ
  have hx1 : Int.fract θ < 1 := Int.fract_lt_one θ
  have hxIoo : Int.fract θ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hsin : 0 < Real.sin (Real.pi * Int.fract θ) := Salt.MR.sin_pi_mul_pos hxIoo
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hdpos : 0 < dist₁ θ 0 := lt_of_le_of_ne (dist₁_nonneg _ _) (Ne.symm hθ)
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hpin : Real.pi ≠ 0 := hpi.ne'
  have hsn : Real.sin (Real.pi * Int.fract θ) ≠ 0 := hsin.ne'
  have hkn : ((K : ℝ) + 1) ≠ 0 := hK1.ne'
  have hsin2 : 2 * dist₁ θ 0 ≤ Real.sin (Real.pi * Int.fract θ) := by
    rw [← hdx]; exact two_dist_le_sin (le_of_lt hx0) (le_of_lt hx1)
  -- Abel's inequality on the tail of the (conditionally convergent) sine series
  have hS : ∀ N, |∑ i ∈ Finset.range N,
      Real.sin (2 * Real.pi * Int.fract θ * ((i + 1 : ℕ) : ℝ))|
        ≤ 1 / Real.sin (Real.pi * Int.fract θ) := by
    intro N
    rw [show ∑ i ∈ Finset.range N,
          Real.sin (2 * Real.pi * Int.fract θ * ((i + 1 : ℕ) : ℝ))
        = ∑ n ∈ Finset.range (N + 1), Real.sin (2 * Real.pi * Int.fract θ * n) by
      rw [Finset.sum_range_succ' (fun n : ℕ => Real.sin (2 * Real.pi * Int.fract θ * n)) N]
      simp]
    exact Salt.MR.abs_sum_sin_le hxIoo (N + 1)
  have hb0 : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by intro n; positivity
  have hbanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro i j hij
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    simp only [one_div]
    exact inv_anti₀ (by positivity) hij'
  have hblock : ∀ M, |(∑ n ∈ Finset.range (K + 1 + M),
          Real.sin (2 * Real.pi * Int.fract θ * n) / n)
        - ∑ n ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * Int.fract θ * n) / n|
      ≤ 2 * (1 / Real.sin (Real.pi * Int.fract θ)) * (1 / ((K : ℝ) + 1)) := by
    intro M
    have habel := Salt.MR.abs_sum_shift_mul_le_of_bounded hS hb0 hbanti K M
    rwa [sum_tail_eq (Int.fract θ) K M] at habel
  -- pass to the limit with the corpus's sawtooth Fourier series
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
      Real.sin (2 * Real.pi * Int.fract θ * n) / n) Filter.atTop
      (nhds (Real.pi * (1 / 2 - Int.fract θ))) := Salt.MR.tendsto_sum_sin_div_nat hxIoo
  have hshift : Filter.Tendsto (fun M => ∑ n ∈ Finset.range (K + 1 + M),
      Real.sin (2 * Real.pi * Int.fract θ * n) / n) Filter.atTop
      (nhds (Real.pi * (1 / 2 - Int.fract θ))) := by
    have h := hlim.comp (Filter.tendsto_add_atTop_nat (K + 1))
    refine h.congr (fun M => ?_)
    simp only [Function.comp_apply]
    rw [show M + (K + 1) = K + 1 + M from by omega]
  have hfinal : |Real.pi * (1 / 2 - Int.fract θ)
        - ∑ n ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * Int.fract θ * n) / n|
      ≤ 2 * (1 / Real.sin (Real.pi * Int.fract θ)) * (1 / ((K : ℝ) + 1)) :=
    le_of_tendsto ((hshift.sub_const _).abs) (Filter.Eventually.of_forall hblock)
  -- assemble
  rw [norm_sawtoothRem_eq]
  have hsum : ∑ m ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)
      = (1 / Real.pi) * ∑ n ∈ Finset.range (K + 1),
          Real.sin (2 * Real.pi * Int.fract θ * n) / n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← sin_fract θ m, div_pi_mul]
  have hval : remReal K θ
      = (1 / Real.pi) * ((∑ n ∈ Finset.range (K + 1),
            Real.sin (2 * Real.pi * Int.fract θ * n) / n)
          - Real.pi * (1 / 2 - Int.fract θ)) := by
    unfold remReal sawtooth
    rw [hsum]
    field_simp
    ring
  rw [hval, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi), abs_sub_comm]
  refine le_trans (mul_le_mul_of_nonneg_left hfinal (by positivity)) ?_
  have hA : (0 : ℝ) < Real.pi * Real.sin (Real.pi * Int.fract θ) * ((K : ℝ) + 1) :=
    mul_pos (mul_pos hpi hsin) hK1
  have hB : (0 : ℝ) < Real.pi * ((K : ℝ) + 1) * dist₁ θ 0 :=
    mul_pos (mul_pos hpi hK1) hdpos
  rw [inv_eq_one_div,
    show (1 / Real.pi) * (2 * (1 / Real.sin (Real.pi * Int.fract θ)) * (1 / ((K : ℝ) + 1)))
      = 2 / (Real.pi * Real.sin (Real.pi * Int.fract θ) * ((K : ℝ) + 1)) by field_simp,
    div_le_div_iff₀ hA hB]
  nlinarith [mul_le_mul_of_nonneg_left hsin2 (le_of_lt (mul_pos hpi hK1))]

/-- **(7.2), the majorant half.**  N7 quotes this as (7.2)'s error term: for `K ≥ 1` and every
real `θ`,

`‖R_K θ‖ ≤ (5/2) · Min(1/(K‖θ‖), 1)`

with the majorant in the §D5 degenerate-split form (`sawtoothMajorant`).  The constant `5/2` is
explicit and unconditional; the two arms are `norm_sawtoothRem_le_dist` (which gives the sharper
`(π(K+1)‖θ‖)⁻¹`) and `norm_sawtoothRem_le_linear`. -/
theorem norm_sawtoothRem_le {K : ℕ} (hK : 1 ≤ K) (θ : ℝ) :
    ‖sawtoothRem K θ‖ ≤ (5 / 2) * sawtoothMajorant K θ := by
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hd0 : 0 ≤ dist₁ θ 0 := dist₁_nonneg _ _
  have hdhalf : dist₁ θ 0 ≤ 1 / 2 := dist₁_le_half θ 0
  unfold sawtoothMajorant
  by_cases hz : dist₁ θ 0 = 0
  · rw [if_pos hz, mul_one]
    have h := norm_sawtoothRem_le_linear K θ
    rw [hz] at h
    linarith
  · rw [if_neg hz]
    have hdpos : 0 < dist₁ θ 0 := lt_of_le_of_ne hd0 (Ne.symm hz)
    have hpos : (0 : ℝ) < (K : ℝ) * dist₁ θ 0 := by nlinarith
    have hinv : ((K : ℝ) * dist₁ θ 0)⁻¹ * ((K : ℝ) * dist₁ θ 0) = 1 := inv_mul_cancel₀ hpos.ne'
    have hinvpos : (0 : ℝ) < ((K : ℝ) * dist₁ θ 0)⁻¹ := inv_pos.mpr hpos
    rcases le_or_gt ((K : ℝ) * dist₁ θ 0) 1 with hsmall | hbig
    · -- the `min` is `1`
      have hmin : min (((K : ℝ) * dist₁ θ 0)⁻¹) 1 = 1 := by
        refine min_eq_right ?_
        nlinarith [hinv, mul_nonneg (le_of_lt hinvpos) (sub_nonneg.mpr hsmall)]
      rw [hmin, mul_one]
      have h := norm_sawtoothRem_le_linear K θ
      linarith
    · -- the `min` is `(K‖θ‖)⁻¹`
      have hmin : min (((K : ℝ) * dist₁ θ 0)⁻¹) 1 = ((K : ℝ) * dist₁ θ 0)⁻¹ := by
        refine min_eq_left ?_
        nlinarith [hinv, mul_nonneg (le_of_lt hinvpos) (le_of_lt (sub_pos.mpr hbig))]
      rw [hmin]
      refine le_trans (norm_sawtoothRem_le_dist K hz) ?_
      have hp3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have h1 : ((2 : ℝ) / 5) * (K : ℝ) ≤ Real.pi * ((K : ℝ) + 1) := by nlinarith
      have hgoal : ((2 : ℝ) / 5) * ((K : ℝ) * dist₁ θ 0)
          ≤ Real.pi * ((K : ℝ) + 1) * dist₁ θ 0 := by
        calc ((2 : ℝ) / 5) * ((K : ℝ) * dist₁ θ 0) = (((2 : ℝ) / 5) * (K : ℝ)) * dist₁ θ 0 := by
              ring
          _ ≤ (Real.pi * ((K : ℝ) + 1)) * dist₁ θ 0 := mul_le_mul_of_nonneg_right h1 hd0
          _ = Real.pi * ((K : ℝ) + 1) * dist₁ θ 0 := by ring
      have h25 : (5 / 2 : ℝ) * ((K : ℝ) * dist₁ θ 0)⁻¹
          = (((2 : ℝ) / 5) * ((K : ℝ) * dist₁ θ 0))⁻¹ := by
        simp only [mul_inv]
        rw [show ((2 : ℝ) / 5)⁻¹ = 5 / 2 by norm_num]
      rw [h25]
      exact inv_anti₀ (by nlinarith) hgoal

/-! ## S2 — (7.3)/(7.4), the majorant's own Fourier coefficients  ⚠️ **PARTIAL**

HB p.221: `Min(1/(K‖θ‖),1) = ∑_m a_m e(mθ)` (7.3) with `a_m ≪ Min((log K)/K, K/m²)` (7.4).

**What lands here** is the `(log K)/K` arm, for `a₀` and for every `a_m` alike, off the exact
`L¹` mass of the majorant:

`∫₀¹ Min(1/(K‖θ‖),1) dθ = 2(1 + log(K/2))/K ≤ 2(1 + log K)/K`,   `‖a_m‖ ≤ 2(1 + log K)/K`.

**What does NOT land**: the `K/m²` arm (two integrations by parts across the corner `‖θ‖ = 1/K`)
and hence (7.3) itself (the inversion needs summable coefficients).  Banked in
`docs/blueprints/flags.md`.

The key normal form is `sawtoothMajorant_eq_inv_max`: the §D5 degenerate-split `if` is exactly
`(max (K‖θ‖) 1)⁻¹`, which is **continuous** — that is what makes every integrability side
condition a `ContinuousOn.congr`.
-/

/-- `dist₁ θ 0 = θ` on `[0, 1/2]`. -/
private lemma dist₁_eq_self {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) : dist₁ θ 0 = θ := by
  have hle : dist₁ θ 0 ≤ θ := by
    have h := dist₁_le_abs θ 0
    rwa [sub_zero, abs_of_nonneg h0] at h
  have hge : θ ≤ dist₁ θ 0 := by
    have hd : dist₁ θ 0 = |θ - (round θ : ℝ)| := by unfold dist₁; simp only [sub_zero]
    rw [hd]
    rcases le_or_gt ((round θ : ℤ) : ℝ) 0 with hr | hr
    · rw [abs_of_nonneg (by linarith)]; linarith
    · have hone : (1 : ℝ) ≤ ((round θ : ℤ) : ℝ) := by
        have : (0 : ℤ) < round θ := by exact_mod_cast hr
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]; linarith
  linarith

/-- **The majorant's continuous normal form.**  The §D5 degenerate-split `if` is literally
`(max (K‖θ‖) 1)⁻¹` — no case split, and continuous wherever `dist₁` is. -/
theorem sawtoothMajorant_eq_inv_max {K : ℕ} (hK : 1 ≤ K) (θ : ℝ) :
    sawtoothMajorant K θ = (max ((K : ℝ) * dist₁ θ 0) 1)⁻¹ := by
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hd : 0 ≤ dist₁ θ 0 := dist₁_nonneg _ _
  unfold sawtoothMajorant
  by_cases hz : dist₁ θ 0 = 0
  · rw [if_pos hz, hz, mul_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1), inv_one]
  · rw [if_neg hz]
    have hdpos : 0 < dist₁ θ 0 := lt_of_le_of_ne hd (Ne.symm hz)
    have hpos : 0 < (K : ℝ) * dist₁ θ 0 := mul_pos (by linarith) hdpos
    have hinv : ((K : ℝ) * dist₁ θ 0)⁻¹ * ((K : ℝ) * dist₁ θ 0) = 1 := inv_mul_cancel₀ hpos.ne'
    have hinvpos : (0 : ℝ) < ((K : ℝ) * dist₁ θ 0)⁻¹ := inv_pos.mpr hpos
    rcases le_or_gt ((K : ℝ) * dist₁ θ 0) 1 with h | h
    · rw [max_eq_right h, inv_one]
      refine min_eq_right ?_
      nlinarith [hinv, mul_nonneg (le_of_lt hinvpos) (sub_nonneg.mpr h)]
    · rw [max_eq_left (le_of_lt h)]
      refine min_eq_left ?_
      nlinarith [hinv, mul_nonneg (le_of_lt hinvpos) (le_of_lt (sub_pos.mpr h))]

/-- The majorant is symmetric about `1/2`. -/
private lemma sawtoothMajorant_one_sub (K : ℕ) (θ : ℝ) :
    sawtoothMajorant K (1 - θ) = sawtoothMajorant K θ := by
  have hd : dist₁ (1 - θ) 0 = dist₁ θ 0 := by
    have h := dist₁_add_int_left (-θ) 0 1
    rw [show -θ + ((1 : ℤ) : ℝ) = 1 - θ by push_cast; ring] at h
    rw [h, dist₁_neg_zero]
  simp only [sawtoothMajorant, hd]

/-- The continuous comparison function on the lower half-period. -/
private noncomputable def majPiece (K : ℕ) (θ : ℝ) : ℝ := (max ((K : ℝ) * θ) 1)⁻¹

private lemma continuous_majPiece (K : ℕ) : Continuous (majPiece K) := by
  refine Continuous.inv₀ (by fun_prop) (fun θ => ?_)
  have : (1 : ℝ) ≤ max ((K : ℝ) * θ) 1 := le_max_right _ _
  linarith

private lemma majorant_eqOn_lower {K : ℕ} (hK : 1 ≤ K) :
    Set.EqOn (sawtoothMajorant K) (majPiece K) (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro θ hθ
  rw [sawtoothMajorant_eq_inv_max hK, dist₁_eq_self hθ.1 hθ.2]
  rfl

private lemma intervalIntegrable_majorant_lower {K : ℕ} (hK : 1 ≤ K) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1 / 2) (hab : a ≤ b) :
    IntervalIntegrable (sawtoothMajorant K) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.congr ((continuous_majPiece K).continuousOn) ?_
  intro θ hθ
  rw [Set.uIcc_of_le hab] at hθ
  exact majorant_eqOn_lower hK ⟨le_trans ha hθ.1, le_trans hθ.2 hb⟩

/-- **The `L¹` mass of the (7.3) majorant, exactly.** -/
theorem integral_sawtoothMajorant_eq {K : ℕ} (hK : 2 ≤ K) :
    ∫ θ in (0 : ℝ)..1, sawtoothMajorant K θ = 2 * (1 + Real.log ((K : ℝ) / 2)) / K := by
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hinvK : 1 / (K : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hKpos (by norm_num)]; linarith
  have hinvK0 : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  -- the lower half splits at `1/K`
  have hi1 : IntervalIntegrable (sawtoothMajorant K) MeasureTheory.volume 0 (1 / (K : ℝ)) :=
    intervalIntegrable_majorant_lower hK1 le_rfl hinvK (le_of_lt hinvK0)
  have hi2 : IntervalIntegrable (sawtoothMajorant K) MeasureTheory.volume (1 / (K : ℝ)) (1 / 2) :=
    intervalIntegrable_majorant_lower hK1 (le_of_lt hinvK0) le_rfl hinvK
  have h1 : ∫ θ in (0 : ℝ)..(1 / (K : ℝ)), sawtoothMajorant K θ = 1 / (K : ℝ) := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1 : ℝ)) ?_]
    · simp
    · intro θ hθ
      rw [Set.uIcc_of_le (le_of_lt hinvK0)] at hθ
      rw [sawtoothMajorant_eq_inv_max hK1,
        dist₁_eq_self hθ.1 (le_trans hθ.2 hinvK)]
      have hle : (K : ℝ) * θ ≤ 1 := by
        have h := hθ.2
        rw [le_div_iff₀ hKpos] at h
        linarith [h, mul_comm (K : ℝ) θ]
      rw [max_eq_right hle, inv_one]
  have h2 : ∫ θ in (1 / (K : ℝ))..(1 / 2), sawtoothMajorant K θ
      = Real.log ((K : ℝ) / 2) / (K : ℝ) := by
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ => (1 / (K : ℝ)) * θ⁻¹) ?_]
    · rw [intervalIntegral.integral_const_mul, integral_inv ?_]
      · rw [show (1 / 2 : ℝ) / (1 / (K : ℝ)) = (K : ℝ) / 2 by field_simp]
        ring
      · rw [Set.uIcc_of_le hinvK]
        intro hmem
        exact absurd hmem.1 (not_le.mpr hinvK0)
    · intro θ hθ
      rw [Set.uIcc_of_le hinvK] at hθ
      have hθ0 : 0 < θ := lt_of_lt_of_le hinvK0 hθ.1
      rw [sawtoothMajorant_eq_inv_max hK1, dist₁_eq_self (le_of_lt hθ0) hθ.2]
      have hge : (1 : ℝ) ≤ (K : ℝ) * θ := by
        have h := hθ.1
        rw [div_le_iff₀ hKpos] at h
        linarith [h, mul_comm θ (K : ℝ)]
      rw [max_eq_left hge, mul_inv, one_div]
  -- the two halves are equal
  have hsym : ∫ θ in (1 / 2 : ℝ)..1, sawtoothMajorant K θ
      = ∫ θ in (0 : ℝ)..(1 / 2), sawtoothMajorant K θ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1 / 2)
      (sawtoothMajorant K) 1
    rw [intervalIntegral.integral_congr
      (g := sawtoothMajorant K) (fun θ _ => sawtoothMajorant_one_sub K θ),
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) - 0 = 1 by norm_num] at h
    exact h.symm
  have hilo : IntervalIntegrable (sawtoothMajorant K) MeasureTheory.volume 0 (1 / 2) :=
    intervalIntegrable_majorant_lower hK1 le_rfl le_rfl (by norm_num)
  have hihi : IntervalIntegrable (sawtoothMajorant K) MeasureTheory.volume (1 / 2) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.congr (f := fun θ : ℝ => majPiece K (1 - θ))
      (((continuous_majPiece K).comp (continuous_const.sub continuous_id)).continuousOn) ?_
    intro θ hθ
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hθ
    rw [← sawtoothMajorant_one_sub K θ]
    exact majorant_eqOn_lower hK1 ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have htot : (∫ θ in (0 : ℝ)..(1 / 2), sawtoothMajorant K θ)
      + ∫ θ in (1 / 2 : ℝ)..1, sawtoothMajorant K θ = ∫ θ in (0 : ℝ)..1, sawtoothMajorant K θ :=
    intervalIntegral.integral_add_adjacent_intervals hilo hihi
  have hhalf : ∫ θ in (0 : ℝ)..(1 / 2), sawtoothMajorant K θ
      = 1 / (K : ℝ) + Real.log ((K : ℝ) / 2) / (K : ℝ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2]
  have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
  rw [← htot, hsym, hhalf]
  field_simp
  try ring

/-- **The `(log K)/K` arm of (7.4), for the mass.** -/
theorem integral_sawtoothMajorant_le {K : ℕ} (hK : 2 ≤ K) :
    ∫ θ in (0 : ℝ)..1, sawtoothMajorant K θ ≤ 2 * (1 + Real.log K) / K := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  rw [integral_sawtoothMajorant_eq hK]
  have hlog : Real.log ((K : ℝ) / 2) ≤ Real.log K :=
    Real.log_le_log (by linarith) (by linarith)
  rw [div_le_div_iff₀ hKpos hKpos]
  nlinarith [hlog, hKpos]

/-- The (7.3) Fourier coefficient `a_m = ∫₀¹ Min(1/(K‖θ‖),1)·e(−mθ) dθ` of the majorant. -/
noncomputable def majorantCoeff (K : ℕ) (m : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..1, (sawtoothMajorant K θ : ℂ) * e (-((m : ℝ) * θ))

/-- **(7.4), the `(log K)/K` arm.**  N7 quotes this as the `a₀`-row of (7.4) and as the
uniform half of the `a_m`-row: *every* coefficient (including `m = 0`, per §D5's `a₀`-separate
discipline) obeys `‖a_m‖ ≤ 2(1 + log K)/K`.  The complementary `K/m²` arm is
`norm_majorantCoeff_le_sq`, below. -/
theorem norm_majorantCoeff_le {K : ℕ} (hK : 2 ≤ K) (m : ℤ) :
    ‖majorantCoeff K m‖ ≤ 2 * (1 + Real.log K) / K := by
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  unfold majorantCoeff
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)) ?_
  have hnorm : ∀ θ : ℝ, ‖(sawtoothMajorant K θ : ℂ) * e (-((m : ℝ) * θ))‖
      = sawtoothMajorant K θ := by
    intro θ
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by
        rw [sawtoothMajorant_eq_inv_max hK1]
        exact inv_nonneg.mpr (le_trans zero_le_one (le_max_right _ _)))]
  rw [intervalIntegral.integral_congr (g := sawtoothMajorant K) (fun θ _ => hnorm θ)]
  exact integral_sawtoothMajorant_le hK

/-! ### The `K/m²` arm of (7.4)

The route (verified numerically before it was formalised): `a_m` is real and even in `m`, so
`a_m = 2∫₀^{1/2} M(θ)cos(2πmθ)dθ`.  Split at the corner `θ = 1/K`.  On `[0, 1/K]` the majorant
is `≡ 1`, so that piece is the closed form `sin(2πm/K)/(πm)` — **no integration by parts**.  One
IBP on `[1/K, 1/2]` produces a boundary term at `θ = 1/K` that **cancels that closed form
exactly**, and the whole coefficient collapses to
`a_m = (πmK)⁻¹ ∫_{1/K}^{1/2} sin(2πmθ)/θ² dθ`.  The `θ = 1/2` boundary term is *exactly* zero by
`Real.sin_int_mul_pi` — bounding it by `1/(πm)` instead would silently revert the estimate to the
very `1/m` this route exists to beat.  A second IBP plus `|sin| ≤ 1`, `|cos| ≤ 1` and
`∫_{1/K}^{1/2} θ⁻³ dθ = (K²−4)/2` gives `|J| ≤ K²/(πm)`, whence `C = 1/π²`.  The `+4` and `−4`
cancel exactly, so there is no triangle-inequality slop. -/

/-- Triangle inequality in the `A − B − C` shape the second IBP produces. -/
private lemma abs_sub_sub_le (A B C : ℝ) : |A - B - C| ≤ |A| + |B| + |C| :=
  abs_le.mpr ⟨by linarith [neg_abs_le A, le_abs_self B, le_abs_self C],
    by linarith [le_abs_self A, neg_abs_le B, neg_abs_le C]⟩

/-- `2sin(wθ)/w` is an antiderivative of `2cos(wθ)`. -/
private lemma hasDerivAt_two_sin {w : ℝ} (hw : w ≠ 0) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => 2 * Real.sin (w * t) / w) (2 * Real.cos (w * θ)) θ := by
  have h1 : HasDerivAt (fun t : ℝ => w * t) w θ := by
    simpa using (hasDerivAt_id θ).const_mul w
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (w * t)) (Real.cos (w * θ) * w) θ :=
    (Real.hasDerivAt_sin (w * θ)).comp θ h1
  exact ((h2.const_mul (2 : ℝ)).div_const w).congr_deriv (by field_simp; try ring)

/-- `−cos(wθ)/w` is an antiderivative of `sin(wθ)`. -/
private lemma hasDerivAt_neg_cos {w : ℝ} (hw : w ≠ 0) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => -Real.cos (w * t) / w) (Real.sin (w * θ)) θ := by
  have h1 : HasDerivAt (fun t : ℝ => w * t) w θ := by
    simpa using (hasDerivAt_id θ).const_mul w
  have h2 : HasDerivAt (fun t : ℝ => Real.cos (w * t)) (-Real.sin (w * θ) * w) θ :=
    (Real.hasDerivAt_cos (w * θ)).comp θ h1
  exact (h2.neg.div_const w).congr_deriv (by field_simp; try ring)

/-- `∫_{1/K}^{1/2} θ⁻³ dθ = (K²−4)/2`.  At `K = 2` the interval degenerates and both sides are
`0` — that is why the `K/m²` arm needs no special case at `K = 2`. -/
private lemma integral_inv_cube {K : ℕ} (hK : 2 ≤ K) :
    (∫ θ in (1 / (K : ℝ))..(1 / 2 : ℝ), (θ ^ 3)⁻¹) = ((K : ℝ) ^ 2 - 4) / 2 := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hKne : (K : ℝ) ≠ 0 := hK0.ne'
  have hL0 : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  have hL2 : 1 / (K : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hK0 (by norm_num)]; linarith
  have hd : ∀ x ∈ Set.uIcc (1 / (K : ℝ)) (1 / 2 : ℝ),
      HasDerivAt (fun t : ℝ => -(2 * t ^ 2)⁻¹) ((x ^ 3)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hL2] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hL0 hx.1)
    have h1 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (2 * (2 * x ^ 1)) x :=
      (hasDerivAt_pow 2 x).const_mul 2
    exact (h1.inv (by positivity)).neg.congr_deriv (by field_simp; try ring)
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 3)⁻¹) MeasureTheory.volume
      (1 / (K : ℝ)) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL2]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le hL0 hx.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
-- two integrations by parts with their side conditions in one declaration
/-- **The analytic core of the `K/m²` arm.**  The two explicit pieces of
`2∫₀^{1/2} M(θ)cos(2πmθ)dθ` — `M ≡ 1` on `[0, 1/K]`, `M = 1/(Kθ)` on `[1/K, 1/2]` — obey the
`K/(π²m²)` bound.  This is where the two integrations by parts and the exact cancellation
live. -/
private lemma majorantCoeff_core_bound {K : ℕ} (hK : 2 ≤ K) {m : ℤ} (hm : m ≠ 0) :
    |(∫ θ in (0 : ℝ)..(1 / (K : ℝ)), 2 * Real.cos (2 * Real.pi * (m : ℝ) * θ))
      + (∫ θ in (1 / (K : ℝ))..(1 / 2 : ℝ),
          1 / ((K : ℝ) * θ) * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)))|
      ≤ (K : ℝ) / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have hm0 : ((m : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hKne : (K : ℝ) ≠ 0 := hK0.ne'
  set w : ℝ := 2 * Real.pi * (m : ℝ) with hwdef
  have hw : w ≠ 0 := by rw [hwdef]; exact mul_ne_zero (by positivity) hm0
  have hWpos : (0 : ℝ) < |w| := abs_pos.mpr hw
  set L : ℝ := 1 / (K : ℝ) with hLdef
  have hL0 : (0 : ℝ) < L := by rw [hLdef]; positivity
  have hL2 : L ≤ 1 / 2 := by rw [hLdef, div_le_div_iff₀ hK0 (by norm_num)]; linarith
  have huIcc : Set.uIcc L (1 / 2 : ℝ) = Set.Icc L (1 / 2) := Set.uIcc_of_le hL2
  have hne : ∀ x ∈ Set.Icc L (1 / 2 : ℝ), x ≠ 0 :=
    fun x hx => ne_of_gt (lt_of_lt_of_le hL0 hx.1)
  -- (i) the `[0, 1/K]` piece: closed form, no IBP
  have hI1 : (∫ θ in (0 : ℝ)..L, 2 * Real.cos (w * θ)) = 2 * Real.sin (w * L) / w := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_two_sin hw x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp
  -- the `θ = 1/2` boundary sine is EXACTLY zero (`Real.sin_int_mul_pi`), not merely `≤ 1`
  have hsinhalf : Real.sin (w * (1 / 2 : ℝ)) = 0 := by
    have hx : w * (1 / 2 : ℝ) = ((m : ℤ) : ℝ) * Real.pi := by rw [hwdef]; ring
    rw [hx, Real.sin_int_mul_pi]
  -- (ii) first IBP on `[1/K, 1/2]`; its `θ = 1/K` boundary term cancels (i) exactly
  set J : ℝ := ∫ θ in L..(1 / 2 : ℝ), (θ ^ 2)⁻¹ * Real.sin (w * θ) with hJdef
  have hu : ∀ x ∈ Set.uIcc L (1 / 2 : ℝ),
      HasDerivAt (fun t : ℝ => 1 / ((K : ℝ) * t)) (-(1 / ((K : ℝ) * x ^ 2))) x := by
    intro x hx
    rw [huIcc] at hx
    have hx0 : x ≠ 0 := hne x hx
    have h1 : HasDerivAt (fun t : ℝ => (K : ℝ) * t) (K : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul ((K : ℝ))
    have heq : (fun t : ℝ => 1 / ((K : ℝ) * t)) = fun t : ℝ => ((K : ℝ) * t)⁻¹ := by
      funext t; rw [one_div]
    rw [heq]
    exact (h1.inv (mul_ne_zero hKne hx0)).congr_deriv (by field_simp; try ring)
  have hu' : IntervalIntegrable (fun x : ℝ => -(1 / ((K : ℝ) * x ^ 2)))
      MeasureTheory.volume L (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    apply ContinuousOn.neg
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact mul_ne_zero hKne (pow_ne_zero 2 (hne x hx))
  have hv' : IntervalIntegrable (fun x : ℝ => 2 * Real.cos (w * x))
      MeasureTheory.volume L (1 / 2) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hIBP1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu
    (fun x (_ : x ∈ Set.uIcc L (1 / 2 : ℝ)) => hasDerivAt_two_sin hw x) hu' hv'
  have hJrw : (∫ x in L..(1 / 2 : ℝ),
      -(1 / ((K : ℝ) * x ^ 2)) * (2 * Real.sin (w * x) / w))
      = -(2 / ((K : ℝ) * w)) * J := by
    rw [hJdef, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [huIcc] at hx
    have hx0 : x ≠ 0 := hne x hx
    simp only
    field_simp
    try ring
  have huL : 1 / ((K : ℝ) * L) = 1 := by rw [hLdef]; field_simp
  have hI2 : (∫ θ in L..(1 / 2 : ℝ), 1 / ((K : ℝ) * θ) * (2 * Real.cos (w * θ)))
      = -(2 * Real.sin (w * L) / w) + 2 / ((K : ℝ) * w) * J := by
    rw [hIBP1, hJrw, hsinhalf, huL]
    ring
  -- (iii) second IBP on `J`
  set P : ℝ := ∫ θ in L..(1 / 2 : ℝ), (θ ^ 3)⁻¹ * Real.cos (w * θ) with hPdef
  have hu2 : ∀ x ∈ Set.uIcc L (1 / 2 : ℝ),
      HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-(2 / x ^ 3)) x := by
    intro x hx
    rw [huIcc] at hx
    have hx0 : x ≠ 0 := hne x hx
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x ^ 1) x := hasDerivAt_pow 2 x
    exact (h1.inv (pow_ne_zero 2 hx0)).congr_deriv (by field_simp; try ring)
  have hu2' : IntervalIntegrable (fun x : ℝ => -(2 / x ^ 3))
      MeasureTheory.volume L (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    apply ContinuousOn.neg
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact pow_ne_zero 3 (hne x hx)
  have hv2' : IntervalIntegrable (fun x : ℝ => Real.sin (w * x))
      MeasureTheory.volume L (1 / 2) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hIBP2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu2
    (fun x (_ : x ∈ Set.uIcc L (1 / 2 : ℝ)) => hasDerivAt_neg_cos hw x) hu2' hv2'
  have hPrw : (∫ x in L..(1 / 2 : ℝ), -(2 / x ^ 3) * (-Real.cos (w * x) / w))
      = 2 / w * P := by
    rw [hPdef, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [huIcc] at hx
    have hx0 : x ≠ 0 := hne x hx
    simp only
    field_simp
    try ring
  have hLsq : ((L : ℝ) ^ 2)⁻¹ = (K : ℝ) ^ 2 := by rw [hLdef]; field_simp
  have hJval : J = 4 * (-Real.cos (w * (1 / 2 : ℝ)) / w)
      - (K : ℝ) ^ 2 * (-Real.cos (w * L) / w) - 2 / w * P := by
    rw [hJdef, hIBP2, hPrw, hLsq]
    norm_num
  -- crude bounds: `|cos| ≤ 1` and `∫_{1/K}^{1/2} θ⁻³ = (K²−4)/2`; the `±4` cancel
  have hK24 : (0 : ℝ) ≤ (K : ℝ) ^ 2 - 4 := by nlinarith
  have hPbound : |P| ≤ ((K : ℝ) ^ 2 - 4) / 2 := by
    have hint1 : IntervalIntegrable (fun x : ℝ => |(x ^ 3)⁻¹ * Real.cos (w * x)|)
        MeasureTheory.volume L (1 / 2) := by
      apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      apply ContinuousOn.abs
      refine ContinuousOn.mul (ContinuousOn.inv₀ (by fun_prop) ?_) (by fun_prop)
      intro x hx
      exact pow_ne_zero 3 (hne x hx)
    have hint2 : IntervalIntegrable (fun x : ℝ => (x ^ 3)⁻¹) MeasureTheory.volume L (1 / 2) := by
      apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      intro x hx
      exact pow_ne_zero 3 (hne x hx)
    have h1 : |P| ≤ ∫ x in L..(1 / 2 : ℝ), |(x ^ 3)⁻¹ * Real.cos (w * x)| := by
      rw [hPdef]
      exact intervalIntegral.abs_integral_le_integral_abs hL2
    have h2 : (∫ x in L..(1 / 2 : ℝ), |(x ^ 3)⁻¹ * Real.cos (w * x)|)
        ≤ ∫ x in L..(1 / 2 : ℝ), (x ^ 3)⁻¹ := by
      refine intervalIntegral.integral_mono_on hL2 hint1 hint2 ?_
      intro x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hL0 hx.1
      have hxp : (0 : ℝ) < (x ^ 3)⁻¹ := by positivity
      rw [abs_mul, abs_of_pos hxp]
      nlinarith [Real.abs_cos_le_one (w * x), abs_nonneg (Real.cos (w * x))]
    have h3 : (∫ x in L..(1 / 2 : ℝ), (x ^ 3)⁻¹) = ((K : ℝ) ^ 2 - 4) / 2 := by
      rw [hLdef]; exact integral_inv_cube hK
    linarith
  have hJbound : |J| ≤ 2 * (K : ℝ) ^ 2 / |w| := by
    have b1 : |4 * (-Real.cos (w * (1 / 2 : ℝ)) / w)| ≤ 4 / |w| := by
      have he : |4 * (-Real.cos (w * (1 / 2 : ℝ)) / w)|
          = 4 * |Real.cos (w * (1 / 2 : ℝ))| / |w| := by
        rw [abs_mul, abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (4 : ℝ))]
        ring
      rw [he, div_le_div_iff₀ hWpos hWpos]
      nlinarith [Real.abs_cos_le_one (w * (1 / 2 : ℝ)), hWpos]
    have b2 : |(K : ℝ) ^ 2 * (-Real.cos (w * L) / w)| ≤ (K : ℝ) ^ 2 / |w| := by
      have he : |(K : ℝ) ^ 2 * (-Real.cos (w * L) / w)|
          = (K : ℝ) ^ 2 * |Real.cos (w * L)| / |w| := by
        rw [abs_mul, abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ) ^ 2)]
        ring
      rw [he, div_le_div_iff₀ hWpos hWpos]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ((K : ℝ))) hWpos.le)
        (sub_nonneg.mpr (Real.abs_cos_le_one (w * L)))]
    have b3 : |2 / w * P| ≤ ((K : ℝ) ^ 2 - 4) / |w| := by
      have he : |2 / w * P| = 2 * |P| / |w| := by
        rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        ring
      rw [he, div_le_div_iff₀ hWpos hWpos]
      nlinarith [hPbound, hWpos]
    have htri := abs_sub_sub_le (4 * (-Real.cos (w * (1 / 2 : ℝ)) / w))
      ((K : ℝ) ^ 2 * (-Real.cos (w * L) / w)) (2 / w * P)
    rw [hJval]
    have hsum : 4 / |w| + (K : ℝ) ^ 2 / |w| + ((K : ℝ) ^ 2 - 4) / |w|
        = 2 * (K : ℝ) ^ 2 / |w| := by field_simp; try ring
    linarith
  -- assemble: the closed form and the first boundary term cancel, leaving `2J/(Kw)`
  have htot : (∫ θ in (0 : ℝ)..L, 2 * Real.cos (w * θ))
      + (∫ θ in L..(1 / 2 : ℝ), 1 / ((K : ℝ) * θ) * (2 * Real.cos (w * θ)))
      = 2 / ((K : ℝ) * w) * J := by
    rw [hI1, hI2]; ring
  rw [htot]
  have habs : |2 / ((K : ℝ) * w) * J| = 2 / ((K : ℝ) * |w|) * |J| := by
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
      abs_of_nonneg (le_of_lt hK0)]
  rw [habs]
  have hstep : 2 / ((K : ℝ) * |w|) * |J| ≤ 2 / ((K : ℝ) * |w|) * (2 * (K : ℝ) ^ 2 / |w|) :=
    mul_le_mul_of_nonneg_left hJbound (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  have hfold : 2 / ((K : ℝ) * |w|) * (2 * (K : ℝ) ^ 2 / |w|) = 4 * (K : ℝ) / |w| ^ 2 := by
    field_simp; try ring
  have hw2 : |w| ^ 2 = 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 := by rw [sq_abs, hwdef]; ring
  rw [hfold, hw2]
  field_simp
  try ring

/-- `e` kills integers: `e(r) = 1` for `r : ℤ`. -/
private lemma e_intCast (r : ℤ) : e ((r : ℝ)) = 1 := by
  unfold e
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((r : ℝ) : ℂ))
        = (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I r

/-- The `±x` pair of characters is the real cosine: `e(x) + e(−x) = 2cos(2πx)`. -/
private lemma e_add_e_neg (x : ℝ) :
    e x + e (-x) = ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
  rw [e_eq_cos_add_sin x, e_eq_cos_add_sin (-x),
    show 2 * Real.pi * (-x) = -(2 * Real.pi * x) by ring, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
-- realification, reflection and the corner split in one declaration
/-- **(7.4), the `K/m²` arm.**  For `m ≠ 0` the majorant's Fourier coefficient obeys
`‖a_m‖ ≤ K/(π²m²)`, the complement of `norm_majorantCoeff_le`'s uniform `(log K)/K` bound: it is
the arm that makes the tail `|m| > K` of `∑_m ‖a_m‖‖S_m‖` converge, so N7 needs both.

`hm : m ≠ 0` is **load-bearing, not cosmetic**: in Lean `K/0² = 0`, while
`majorantCoeff K 0 = 2(1 + log(K/2))/K > 0`, so dropping it makes the row false rather than
vacuous.  `hK : 2 ≤ K` is kept so the row composes with the landed ones; `K = 2` needs no special
case, since then `[1/K, 1/2]` degenerates to a point and the interior integral vanishes.

The constant is `C = 1/π² = 0.1013…`; a dense numerical scan (every integer `m`, `K = 2…512`)
puts the true worst case at `sup |a_m|m²/K = 0.07318` at `(K, m) = (3, 2877)`, so this row has
`1.385×` headroom and the sharper-looking `K/(2π²m²)` is **false**.  Composing this arm with
`norm_majorantCoeff_le` into a `min` is the consumer's business, not this row's. -/
theorem norm_majorantCoeff_le_sq {K : ℕ} (hK : 2 ≤ K) {m : ℤ} (hm : m ≠ 0) :
    ‖majorantCoeff K m‖ ≤ (K : ℝ) / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hL0 : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  have hLhalf : 1 / (K : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hK0 (by norm_num)]; linarith
  -- integrability of the complex integrand on the two half-periods
  have hMlo : ContinuousOn (sawtoothMajorant K) (Set.uIcc (0 : ℝ) (1 / 2)) := by
    refine ContinuousOn.congr ((continuous_majPiece K).continuousOn) ?_
    intro θ hθ
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hθ
    exact majorant_eqOn_lower hK1 hθ
  have hMhi : ContinuousOn (sawtoothMajorant K) (Set.uIcc (1 / 2 : ℝ) 1) := by
    refine ContinuousOn.congr (f := fun θ : ℝ => majPiece K (1 - θ))
      (((continuous_majPiece K).comp (continuous_const.sub continuous_id)).continuousOn) ?_
    intro θ hθ
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hθ
    rw [← sawtoothMajorant_one_sub K θ]
    exact majorant_eqOn_lower hK1 ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hilo : IntervalIntegrable
      (fun θ : ℝ => ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ)))
      MeasureTheory.volume 0 (1 / 2) :=
    ContinuousOn.intervalIntegrable
      ((Complex.continuous_ofReal.comp_continuousOn hMlo).mul (by fun_prop))
  have hilo2 : IntervalIntegrable
      (fun θ : ℝ => ((sawtoothMajorant K θ : ℝ) : ℂ) * e ((m : ℝ) * θ))
      MeasureTheory.volume 0 (1 / 2) :=
    ContinuousOn.intervalIntegrable
      ((Complex.continuous_ofReal.comp_continuousOn hMlo).mul (by fun_prop))
  have hihi : IntervalIntegrable
      (fun θ : ℝ => ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ)))
      MeasureTheory.volume (1 / 2) 1 :=
    ContinuousOn.intervalIntegrable
      ((Complex.continuous_ofReal.comp_continuousOn hMhi).mul (by fun_prop))
  have hsplit : majorantCoeff K m
      = (∫ θ in (0 : ℝ)..(1 / 2), ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ)))
        + (∫ θ in (1 / 2 : ℝ)..1, ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ))) := by
    unfold majorantCoeff
    exact (intervalIntegral.integral_add_adjacent_intervals hilo hihi).symm
  -- the reflection `θ ↦ 1 − θ` turns the upper half into the conjugate character
  have hpt : ∀ θ : ℝ, ((sawtoothMajorant K (1 - θ) : ℝ) : ℂ) * e (-((m : ℝ) * (1 - θ)))
      = ((sawtoothMajorant K θ : ℝ) : ℂ) * e ((m : ℝ) * θ) := by
    intro θ
    rw [sawtoothMajorant_one_sub]
    congr 1
    rw [show -((m : ℝ) * (1 - θ)) = (((-m : ℤ)) : ℝ) + (m : ℝ) * θ by push_cast; ring,
      e_add, e_intCast, one_mul]
  have hrefl : (∫ θ in (1 / 2 : ℝ)..1, ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ)))
      = ∫ θ in (0 : ℝ)..(1 / 2), ((sawtoothMajorant K θ : ℝ) : ℂ) * e ((m : ℝ) * θ) := by
    have h1 : (∫ θ in (0 : ℝ)..(1 / 2 : ℝ),
        ((sawtoothMajorant K (1 - θ) : ℝ) : ℂ) * e (-((m : ℝ) * (1 - θ))))
        = ∫ θ in (1 / 2 : ℝ)..1, ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ)) := by
      have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
        (fun θ : ℝ => ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ))) 1
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) - 0 = 1 by norm_num] at h
      exact h
    rw [← h1]
    exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
  -- `e(−x) + e(x) = 2cos(2πx)`: the coefficient is real
  have hcomb : (∫ θ in (0 : ℝ)..(1 / 2), ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ)))
      + (∫ θ in (0 : ℝ)..(1 / 2), ((sawtoothMajorant K θ : ℝ) : ℂ) * e ((m : ℝ) * θ))
      = ∫ θ in (0 : ℝ)..(1 / 2),
          ((sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_add hilo hilo2]
    refine intervalIntegral.integral_congr ?_
    intro θ _
    have hE : e (-((m : ℝ) * θ)) + e ((m : ℝ) * θ)
        = ((2 * Real.cos (2 * Real.pi * (m : ℝ) * θ) : ℝ) : ℂ) := by
      rw [add_comm, e_add_e_neg ((m : ℝ) * θ),
        show 2 * Real.pi * ((m : ℝ) * θ) = 2 * Real.pi * (m : ℝ) * θ from by ring]
    change ((sawtoothMajorant K θ : ℝ) : ℂ) * e (-((m : ℝ) * θ))
        + ((sawtoothMajorant K θ : ℝ) : ℂ) * e ((m : ℝ) * θ) = _
    rw [← mul_add, hE, ← Complex.ofReal_mul]
  have hval : majorantCoeff K m
      = ((∫ θ in (0 : ℝ)..(1 / 2),
          sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)) : ℝ) : ℂ) := by
    rw [hsplit, hrefl, hcomb, intervalIntegral.integral_ofReal]
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  -- split the real integral at the corner `1/K` and read off the two explicit pieces
  have hMint : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 / 2 → a ≤ b →
      IntervalIntegrable
        (fun θ : ℝ => sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)))
        MeasureTheory.volume a b := by
    intro a b ha hb hab
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ (by fun_prop)
    refine ContinuousOn.congr ((continuous_majPiece K).continuousOn) ?_
    intro θ hθ
    rw [Set.uIcc_of_le hab] at hθ
    exact majorant_eqOn_lower hK1 ⟨le_trans ha hθ.1, le_trans hθ.2 hb⟩
  have hsp : (∫ θ in (0 : ℝ)..(1 / 2),
        sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)))
      = (∫ θ in (0 : ℝ)..(1 / (K : ℝ)),
          sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)))
        + (∫ θ in (1 / (K : ℝ))..(1 / 2 : ℝ),
          sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ))) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hMint 0 (1 / (K : ℝ)) le_rfl hLhalf hL0.le)
      (hMint (1 / (K : ℝ)) (1 / 2) hL0.le le_rfl hLhalf)).symm
  have hc1 : (∫ θ in (0 : ℝ)..(1 / (K : ℝ)),
        sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)))
      = ∫ θ in (0 : ℝ)..(1 / (K : ℝ)), 2 * Real.cos (2 * Real.pi * (m : ℝ) * θ) := by
    refine intervalIntegral.integral_congr ?_
    intro θ hθ
    rw [Set.uIcc_of_le hL0.le] at hθ
    have hMone : sawtoothMajorant K θ = 1 := by
      rw [sawtoothMajorant_eq_inv_max hK1, dist₁_eq_self hθ.1 (le_trans hθ.2 hLhalf)]
      have hle : (K : ℝ) * θ ≤ 1 := by
        have h := hθ.2
        rw [le_div_iff₀ hK0] at h
        linarith [h, mul_comm (K : ℝ) θ]
      rw [max_eq_right hle, inv_one]
    change sawtoothMajorant K θ * _ = _
    rw [hMone, one_mul]
  have hc2 : (∫ θ in (1 / (K : ℝ))..(1 / 2 : ℝ),
        sawtoothMajorant K θ * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)))
      = ∫ θ in (1 / (K : ℝ))..(1 / 2 : ℝ),
          1 / ((K : ℝ) * θ) * (2 * Real.cos (2 * Real.pi * (m : ℝ) * θ)) := by
    refine intervalIntegral.integral_congr ?_
    intro θ hθ
    rw [Set.uIcc_of_le hLhalf] at hθ
    have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le hL0 hθ.1
    have hMinv : sawtoothMajorant K θ = 1 / ((K : ℝ) * θ) := by
      rw [sawtoothMajorant_eq_inv_max hK1, dist₁_eq_self hθ0.le hθ.2]
      have hge : (1 : ℝ) ≤ (K : ℝ) * θ := by
        have h := hθ.1
        rw [div_le_iff₀ hK0] at h
        linarith [h, mul_comm θ (K : ℝ)]
      rw [max_eq_left hge, one_div]
    change sawtoothMajorant K θ * _ = _
    rw [hMinv]
  rw [hsp, hc1, hc2]
  exact majorantCoeff_core_bound hK hm

/-! ## S3 — the congruence-restricted completion (the sixth exit row)

HB p.222: `∑_{n ∈ I₀, q ∣ n−b} e(−sn/k) ≪ Min(E, ‖sq/k‖^{−1})`.  The route is the one the
paper leaves implicit: the congruence class is an arithmetic progression of common difference
`q`, so the sum is a **geometric** sum of ratio `e(−sq/k)`, and `Salt.BV.geom_e_bound` applies.
-/

/-- The congruence-restricted exponential sum `∑_{n ∈ (A,B], n ≡ b (mod q)} e(−s·n/k)`. -/
noncomputable def congrExpSum (k : ℕ) (s b : ℤ) (q : ℕ) (A B : ℤ) : ℂ :=
  ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b),
      e (-((s : ℝ) * (n : ℝ)) / (k : ℝ))

/-- The trivial (length) bound: at most `B − A` terms, each of modulus one. -/
theorem norm_congrExpSum_le_length (k : ℕ) (s b : ℤ) (q : ℕ) (A B : ℤ) :
    ‖congrExpSum k s b q A B‖ ≤ ((B - A).toNat : ℝ) := by
  unfold congrExpSum
  calc ‖∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b),
            e (-((s : ℝ) * (n : ℝ)) / (k : ℝ))‖
      ≤ ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b),
            ‖e (-((s : ℝ) * (n : ℝ)) / (k : ℝ))‖ := norm_sum_le _ _
    _ = (((Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b)).card : ℝ) := by
        simp [norm_e]
    _ ≤ ((Finset.Ioc A B).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = ((B - A).toNat : ℝ) := by rw [Int.card_Ioc]

/-- **The progression normal form.**  For `q ≥ 1`, the residue class `b (mod q)` inside `(A,B]`
is exactly the image of an initial segment of `ℕ` under `i ↦ b + q·(c+1+i)`, where
`c = (A−b)/q` (Euclidean division). -/
private lemma filter_Ioc_dvd_eq_image {q : ℕ} (hq : 0 < q) (b A B : ℤ) :
    (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b)
      = (Finset.range (((B - b) / (q : ℤ) - (A - b) / (q : ℤ)).toNat)).image
          (fun i : ℕ => b + (q : ℤ) * ((A - b) / (q : ℤ) + 1 + (i : ℤ))) := by
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  set c : ℤ := (A - b) / (q : ℤ) with hc
  set d : ℤ := (B - b) / (q : ℤ) with hd
  have hAc : A - b < (q : ℤ) * (c + 1) := by
    have h1 : (q : ℤ) * c + (A - b) % (q : ℤ) = A - b := Int.mul_ediv_add_emod (A - b) (q : ℤ)
    have h2 : (A - b) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hq'
    have : (q : ℤ) * (c + 1) = (q : ℤ) * c + (q : ℤ) := by ring
    omega
  have hBd : (q : ℤ) * d ≤ B - b := by
    have h1 : (q : ℤ) * d + (B - b) % (q : ℤ) = B - b := Int.mul_ediv_add_emod (B - b) (q : ℤ)
    have h2 : 0 ≤ (B - b) % (q : ℤ) := Int.emod_nonneg _ hq'.ne'
    omega
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hAn, hnB⟩, m, hm⟩
    -- `n - b = q * m`; show `c < m ≤ d`.
    have hcm : c < m := by
      rw [hc]
      refine (Int.ediv_lt_iff_lt_mul hq').mpr ?_
      have : A - b < (q : ℤ) * m := by omega
      linarith [this, mul_comm (q : ℤ) m]
    have hmd : m ≤ d := by
      rw [hd]
      refine (Int.le_ediv_iff_mul_le hq').mpr ?_
      have : (q : ℤ) * m ≤ B - b := by omega
      linarith [this, mul_comm (q : ℤ) m]
    refine ⟨(m - c - 1).toNat, ?_, ?_⟩
    · have : m - c - 1 < d - c := by omega
      omega
    · have hcast : ((m - c - 1).toNat : ℤ) = m - c - 1 := Int.toNat_of_nonneg (by omega)
      rw [hcast]
      have : c + 1 + (m - c - 1) = m := by ring
      rw [this]
      omega
  · rintro ⟨i, hi, rfl⟩
    have hidlt : (i : ℤ) < d - c := by
      have := Int.toNat_of_nonneg (a := d - c)
      omega
    refine ⟨⟨?_, ?_⟩, ⟨c + 1 + (i : ℤ), by ring⟩⟩
    · have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
      nlinarith [hAc, hq']
    · have hle : c + 1 + (i : ℤ) ≤ d := by omega
      nlinarith [hBd, hq']

/-- **The geometric arm.**  Off the degenerate locus `k ∣ sq` (equivalently
`dist₁ (sq/k) 0 ≠ 0`) the congruence-restricted sum is bounded by `(2·dist₁(sq/k, 0))⁻¹`,
**uniformly in the interval `(A,B]`, in `b` and in the length**. -/
theorem norm_congrExpSum_le_dist {q k : ℕ} (hq : 0 < q) (s b A B : ℤ)
    (hd : 0 < dist₁ ((s : ℝ) * (q : ℝ) / (k : ℝ)) 0) :
    ‖congrExpSum k s b q A B‖ ≤ 1 / (2 * dist₁ ((s : ℝ) * (q : ℝ) / (k : ℝ)) 0) := by
  set c : ℤ := (A - b) / (q : ℤ) with hc
  set d : ℤ := (B - b) / (q : ℤ) with hdd
  set t : ℕ := (d - c).toNat with ht
  set n₀ : ℤ := b + (q : ℤ) * (c + 1) with hn₀
  set θ : ℝ := -((s : ℝ) * (q : ℝ)) / (k : ℝ) with hθ
  have hθeq : dist₁ θ 0 = dist₁ ((s : ℝ) * (q : ℝ) / (k : ℝ)) 0 := by
    rw [hθ, show -((s : ℝ) * (q : ℝ)) / (k : ℝ) = -((s : ℝ) * (q : ℝ) / (k : ℝ)) by ring,
      dist₁_neg_zero]
  have hθd : 0 < dist₁ θ 0 := by rw [hθeq]; exact hd
  have hstep : congrExpSum k s b q A B
      = e (-((s : ℝ) * (n₀ : ℝ)) / (k : ℝ)) * ∑ i ∈ Finset.range t, (e θ) ^ i := by
    unfold congrExpSum
    rw [filter_Ioc_dvd_eq_image hq b A B]
    rw [Finset.sum_image (by
      intro x _ y _ hxy
      have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
      have : (x : ℤ) = (y : ℤ) := by
        have := hxy
        nlinarith [this]
      exact_mod_cast this)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have harg : (-((s : ℝ) * ((b + (q : ℤ) * (c + 1 + (i : ℤ)) : ℤ) : ℝ)) / (k : ℝ))
        = (-((s : ℝ) * (n₀ : ℝ)) / (k : ℝ)) + ((i : ℝ) * θ) := by
      rw [hn₀, hθ]; push_cast; ring
    rw [harg, e_add, e_natMul]
  rw [hstep, norm_mul, norm_e, one_mul, ← hθeq]
  exact geom_e_bound θ t hθd

/-- **(S3) The sixth exit row — the congruence-restricted completion.**  N7 quotes this as the
inner-sum input to (7.7): for `q ∣ k` (the hypothesis is carried for the caller's bookkeeping;
the bound itself does not need it), any `b` and any `s`,

`‖∑_{n ∈ (A,B], n ≡ b (q)} e(−s·n/k)‖ ≤ Min(B−A, (2·dist₁(sq/k, 0))⁻¹)`,

with the §D5 degenerate split: on `dist₁(sq/k, 0) = 0` (i.e. `k ∣ sq` — every term equals a
single fixed root of unity) only the length arm survives.  `C′ = 1/2`. -/
theorem norm_congrExpSum_le {q k : ℕ} (hq : 0 < q) (hqk : q ∣ k) (s b A B : ℤ) :
    ‖congrExpSum k s b q A B‖
      ≤ (if dist₁ ((s : ℝ) * (q : ℝ) / (k : ℝ)) 0 = 0 then ((B - A).toNat : ℝ)
         else min ((B - A).toNat : ℝ) (1 / (2 * dist₁ ((s : ℝ) * (q : ℝ) / (k : ℝ)) 0))) := by
  have _hqk := hqk
  by_cases h0 : dist₁ ((s : ℝ) * (q : ℝ) / (k : ℝ)) 0 = 0
  · rw [if_pos h0]; exact norm_congrExpSum_le_length k s b q A B
  · rw [if_neg h0]
    refine le_min (norm_congrExpSum_le_length k s b q A B)
      (norm_congrExpSum_le_dist hq s b A B ?_)
    exact lt_of_le_of_ne (dist₁_nonneg _ _) (Ne.symm h0)

/-- The degenerate locus is exactly the divisibility `k ∣ s·q` (for `k ≥ 1`) — the shape N7
tests when it splits the `s`-sum in (7.7). -/
theorem dist₁_mul_div_eq_zero_iff {k : ℕ} (hk : 0 < k) (s q : ℤ) :
    dist₁ ((s : ℝ) * (q : ℝ) / (k : ℝ)) 0 = 0 ↔ (k : ℤ) ∣ s * q := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  rw [dist₁_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [sub_zero] at hn
    refine ⟨n, ?_⟩
    have : ((s * q : ℤ) : ℝ) = ((k : ℤ) : ℝ) * (n : ℝ) := by
      push_cast
      field_simp at hn
      linarith [hn]
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [sub_zero]
    have : ((s : ℝ) * (q : ℝ)) = (k : ℝ) * (n : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hn
    rw [this]
    field_simp

/-! ### The `L¹` row of (7.4): `∑_{m ∈ ℤ} ‖a_m‖ ≪ log K`

The two arms above are complementary, and this is what they were for: the uniform
`(log K)/K` arm carries the `2K+1` terms with `|m| ≤ K`, the `K/m²` arm carries the tail
`|m| > K`, and neither alone gives a finite total.

Architecture: `summable_of_sum_le` and `Real.tsum_le_of_sum_le` take the **same** two inputs
(nonnegativity, and a bound on every finite partial sum), so one finset lemma discharges both
the summability and the bound.

**Measured, so nobody sharpens the wrong thing.**  The true total is *bounded*, not
logarithmic: a dense scan over every integer `K = 2…300` (two independent quadratures agreeing
to `1.7e-15`) puts `sup_K ∑_m ‖a_m‖ = 1.2582` at `K = 5`, with `∑_m ‖a_m‖ → 1.22306` as
`K → ∞`.  The `log K` here is an artefact of the split, not of the object.  It is nevertheless
the right row to prove: N7 consumes `∑_m ‖a_m‖‖S_m‖` and only ever needs `≪ log K` (HB's third
log in `(log Kk)³` comes from the (7.2) truncation's harmonic weights), and the `O(1)` version
is strictly harder — it needs the decay `a_m ≈ (2/K)log(K/2πm)` in `m` rather than a uniform
bound.  **Chasing it would buy the consumer nothing.** -/

/-- Tail of `∑ 1/m²` over any finite set of integers of modulus `> K`, via mathlib's
`sum_Ioo_inv_sq_le` on each sign separately (`Int.natAbs` is injective on each). -/
private lemma sum_inv_sq_of_natAbs_gt {K : ℕ} (v : Finset ℤ) (hv : ∀ m ∈ v, K < m.natAbs) :
    ∑ m ∈ v, ((m : ℝ) ^ 2)⁻¹ ≤ 4 / ((K : ℝ) + 1) := by
  classical
  set N := v.sup (fun m => m.natAbs) + 1 with hN
  have hltN : ∀ m ∈ v, m.natAbs < N := by
    intro m hm
    have := Finset.le_sup (f := fun m : ℤ => m.natAbs) hm
    omega
  have key : ∀ w : Finset ℤ, (∀ m ∈ w, K < m.natAbs) → (∀ m ∈ w, m.natAbs < N) →
      (∀ x ∈ w, ∀ y ∈ w, x.natAbs = y.natAbs → x = y) →
      ∑ m ∈ w, ((m : ℝ) ^ 2)⁻¹ ≤ 2 / ((K : ℝ) + 1) := by
    intro w h1 h2 hinj
    have heq : ∑ m ∈ w, ((m : ℝ) ^ 2)⁻¹ = ∑ n ∈ w.image Int.natAbs, ((n : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun m _ => by
        simp [Nat.cast_natAbs, Int.cast_abs, sq_abs])
    have hsub : w.image Int.natAbs ⊆ Finset.Ioo K N := by
      intro n hn
      simp only [Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      exact Finset.mem_Ioo.mpr ⟨h1 m hm, h2 m hm⟩
    rw [heq]
    calc ∑ n ∈ w.image Int.natAbs, ((n : ℝ) ^ 2)⁻¹
        ≤ ∑ n ∈ Finset.Ioo K N, ((n : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 / ((K : ℝ) + 1) := sum_Ioo_inv_sq_le K N
  rw [← Finset.sum_filter_add_sum_filter_not v (fun m => 0 < m)]
  have hpos := key (v.filter (fun m => 0 < m))
    (fun m hm => hv m (Finset.mem_filter.mp hm).1)
    (fun m hm => hltN m (Finset.mem_filter.mp hm).1)
    (fun x hx y hy h => by
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      omega)
  have hneg := key (v.filter (fun m => ¬ 0 < m))
    (fun m hm => hv m (Finset.mem_filter.mp hm).1)
    (fun m hm => hltN m (Finset.mem_filter.mp hm).1)
    (fun x hx y hy h => by
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have hx'' := hv x (Finset.mem_filter.mp hx).1
      have hy'' := hv y (Finset.mem_filter.mp hy).1
      omega)
  have hsplit : (2 : ℝ) / ((K : ℝ) + 1) + 2 / ((K : ℝ) + 1) = 4 / ((K : ℝ) + 1) := by ring
  linarith

/-- Every finite partial sum of `‖a_m‖` over `ℤ`, at the raw constant the split produces. -/
private lemma sum_norm_majorantCoeff_finset_le_raw {K : ℕ} (hK : 2 ≤ K) (u : Finset ℤ) :
    ∑ m ∈ u, ‖majorantCoeff K m‖ ≤ 5 * (1 + Real.log K) + 4 / Real.pi ^ 2 := by
  classical
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hlog : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
  rw [← Finset.sum_filter_add_sum_filter_not u (fun m => m.natAbs ≤ K)]
  -- inner block `|m| ≤ K`: at most `2K+1` terms, each at the `(log K)/K` arm
  have h1 : ∑ m ∈ u.filter (fun m => m.natAbs ≤ K), ‖majorantCoeff K m‖
      ≤ (2 * (K : ℝ) + 1) * (2 * (1 + Real.log K) / K) := by
    have hsub : u.filter (fun m => m.natAbs ≤ K) ⊆ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro m hm
      have := (Finset.mem_filter.mp hm).2
      exact Finset.mem_Icc.mpr (by omega)
    have hcard : ((u.filter (fun m => m.natAbs ≤ K)).card : ℝ) ≤ 2 * (K : ℝ) + 1 := by
      have hc := Finset.card_le_card hsub
      have hIcc : (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
        rw [Int.card_Icc]; omega
      rw [hIcc] at hc
      have : ((u.filter (fun m => m.natAbs ≤ K)).card : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by
        exact_mod_cast hc
      push_cast at this
      linarith
    calc ∑ m ∈ u.filter (fun m => m.natAbs ≤ K), ‖majorantCoeff K m‖
        ≤ ∑ _m ∈ u.filter (fun m => m.natAbs ≤ K), (2 * (1 + Real.log K) / K) :=
          Finset.sum_le_sum (fun m _ => norm_majorantCoeff_le hK m)
      _ = ((u.filter (fun m => m.natAbs ≤ K)).card : ℝ) * (2 * (1 + Real.log K) / K) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (K : ℝ) + 1) * (2 * (1 + Real.log K) / K) := by
          apply mul_le_mul_of_nonneg_right hcard
          positivity
  -- outer block `|m| > K`: the `K/m²` arm against the `1/m²` tail
  have h2 : ∑ m ∈ u.filter (fun m => ¬ (m.natAbs ≤ K)), ‖majorantCoeff K m‖
      ≤ 4 / Real.pi ^ 2 := by
    have hgt : ∀ m ∈ u.filter (fun m => ¬ (m.natAbs ≤ K)), K < m.natAbs := by
      intro m hm
      have := (Finset.mem_filter.mp hm).2
      omega
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    calc ∑ m ∈ u.filter (fun m => ¬ (m.natAbs ≤ K)), ‖majorantCoeff K m‖
        ≤ ∑ m ∈ u.filter (fun m => ¬ (m.natAbs ≤ K)),
            (K : ℝ) / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
          refine Finset.sum_le_sum (fun m hm => norm_majorantCoeff_le_sq hK ?_)
          have := hgt m hm
          omega
      _ = ((K : ℝ) / Real.pi ^ 2) *
            ∑ m ∈ u.filter (fun m => ¬ (m.natAbs ≤ K)), ((m : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun m _ => by field_simp)
      _ ≤ ((K : ℝ) / Real.pi ^ 2) * (4 / ((K : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sq_of_natAbs_gt _ hgt)
          positivity
      _ ≤ 4 / Real.pi ^ 2 := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg Real.pi, hpi, hK0]
  -- The close.  `(2K+1)·2/K = 4 + 2/K ≤ 5` is an **equality** at `K = 2`, which is exactly why
  -- the round constant `5(1 + log K)` is not provable on this route: the tail's `4/π²` has
  -- nowhere to go.  (The *theorem* at `5` is true — the truth is `≤ 1.26` — so `5` is a
  -- route-break, not a false statement.  Recorded to keep the two apart.)
  have hp1 : (2 * (K : ℝ) + 1) * (2 * (1 + Real.log K) / K) ≤ 5 * (1 + Real.log K) := by
    have hre : (2 * (K : ℝ) + 1) * (2 * (1 + Real.log K) / K)
        = (4 * (K : ℝ) + 2) * (1 + Real.log K) / K := by ring
    rw [hre, div_le_iff₀ hK0]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Real.log K)
      (by linarith : (0:ℝ) ≤ (K : ℝ) - 2)]
  linarith

/-- `4/π² < 0.406`, the numeral both closes below spend. -/
private lemma four_div_pi_sq_lt : (4 : ℝ) / Real.pi ^ 2 < 0.406 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hpi, Real.pi_pos]

private lemma sum_norm_majorantCoeff_finset_le {K : ℕ} (hK : 2 ≤ K) (u : Finset ℤ) :
    ∑ m ∈ u, ‖majorantCoeff K m‖ ≤ 6 * (1 + Real.log K) := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlog : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
  have := sum_norm_majorantCoeff_finset_le_raw hK u
  have := four_div_pi_sq_lt
  linarith

private lemma sum_norm_majorantCoeff_finset_le_log {K : ℕ} (hK : 2 ≤ K) (u : Finset ℤ) :
    ∑ m ∈ u, ‖majorantCoeff K m‖ ≤ 13 * Real.log K := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogK : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hKR
  have := sum_norm_majorantCoeff_finset_le_raw hK u
  have := four_div_pi_sq_lt
  linarith

/-- **Summability of the majorant's Fourier coefficients.**  This is what makes the `tsum` rows
below statements about a convergent series rather than vacuous ones: in Lean `∑' m, f m = 0` by
definition when `f` is not summable, so without this the bounds would be true and empty —
`hm : m ≠ 0`'s role in `norm_majorantCoeff_le_sq`, one level up.

It is also exactly the hypothesis `AddCircle.hasSum_fourier_series_of_summable` wants for the
majorant's continuous 1-periodic lift, i.e. the last missing input to **(7.3)**.  (7.3) itself
is deliberately **not** assembled here. -/
theorem summable_norm_majorantCoeff {K : ℕ} (hK : 2 ≤ K) :
    Summable (fun m : ℤ => ‖majorantCoeff K m‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (sum_norm_majorantCoeff_finset_le hK)

/-- **The `L¹` row of (7.4).**  `∑_{m ∈ ℤ} ‖a_m‖ ≤ 6(1 + log K)`, the form that composes with
`norm_majorantCoeff_le`'s own `2(1 + log K)/K`. -/
theorem tsum_norm_majorantCoeff_le {K : ℕ} (hK : 2 ≤ K) :
    ∑' m : ℤ, ‖majorantCoeff K m‖ ≤ 6 * (1 + Real.log K) :=
  Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (sum_norm_majorantCoeff_finset_le hK)

/-- The same row in the literal `C log K` shape the source asks for (`C = 13`).

**Not** a consequence of `tsum_norm_majorantCoeff_le`: at `K = 2`,
`6(1 + log 2) = 10.16 > 13 log 2 = 9.01`, so the two rows are incomparable and this one is
taken off the raw finset bound directly.  Chaining them in the obvious order does not typecheck,
and that is the point of recording it. -/
theorem tsum_norm_majorantCoeff_le_log {K : ℕ} (hK : 2 ≤ K) :
    ∑' m : ℤ, ‖majorantCoeff K m‖ ≤ 13 * Real.log K :=
  Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (sum_norm_majorantCoeff_finset_le_log hK)

end Salt.Weil
