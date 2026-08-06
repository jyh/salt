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
* **S2 — (7.3)/(7.4), the majorant's own Fourier coefficients.**  See the flag row: only the
  `(log K)/K` arm landed here (`sawtoothMajorant` and its `L¹` mass); the `K/m²` arm is banked.
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

end Salt.Weil
