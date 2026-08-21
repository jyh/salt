/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# W3-F-A / HBUDGET — the error budget `|∫F − ∑_p (H/p)·X| ≤ (1/4)·SP·H·ε`

The turnkey discharge of `hreduce_holds`'s `hbudget` binder
(`docs/exploration/s3-a3-design.md`, "HBUDGET STEP-0").  The F-bridge integral,
unfolded at the Liouville model (`fBridgeF_liouville_apply`, POST-GATE-FIX gate
`((n+j+1:ℕ):ZMod p) = 0`), is the residue-gated double product
`∑_{p∈𝒫_H} ∑_{j<H} T(p,j)` with `T(p,j) = ∫ [gate]·λ(n+j+1)·λ(n+j+p+1)`.  Each
non-boundary `T(p,j)` (i.e. `j+p<H`) collapses to `(1/p)·X` up to three defects:

* **collapse** `2r/p²/Z`               (`perPair_collapse`),
* **swap** `(2·log p + 6)/(p·Z)`       (`dilated_window_stability` ÷ p),
* **shift** `(1/p + H/p²)·3ω/(x·Z)`    (`corr_shift_le` telescoped `k ≤ 1+H/p`),

with `Z = ∑_{(x/ω,x]} 1/n`.  Summed over `p, j` and combined with the
boundary deficit (`Σ_p |X| = |𝒫_H|·|X|` from the `p` values of `j` with
`j+p ≥ H`), the three totals fall below `1/8`, `1/16`, `1/16` of `SP·H·ε` at the
adopted regime:

* **hωbig** `log ω ≥ (16/ε)·log(ε²H) + 64/ε + 1`  (via `Z ≥ log ω − 1`),
* **hxbig** `x ≥ 48·ω·(1 + 2/ε²)/ε`               (the shift `x`-floor, refined),
* **heps_small** `ε ≤ c/(32·log 4)`               (`c` = D3's Mertens constant).

`hbudget_holds` mirrors D3's `∃c>0·∃H₀·∀` idiom (it consumes D3's `c, H₀`), so
`hreduce_holds_final` instantiates it at the tower's `H` and composes through
`hreduce_holds`.
-/
import Salt.Entropy.Chowla.HMainAssembly
import Salt.Entropy.Chowla.DilationStability
import Salt.Entropy.Chowla.ShiftCorr
import Salt.Entropy.Chowla.Prop26
import Salt.Entropy.Chowla.WindowMertensLower
import Salt.Entropy.Chowla.WindowCount
import Salt.Entropy.Chowla.ChowlaFailure
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- Abbreviation: the shifted single correlation `S(k) = ∫ λ(n+k)·λ(n+k+1)`. -/
private noncomputable def shiftCorr (x ω k : ℕ) : ℝ :=
  ∫ n, (ArithmeticFunction.liouville (n + k) : ℝ)
      * (ArithmeticFunction.liouville (n + k + 1) : ℝ) ∂(logMeasure x ω)

/-- **Shift telescoping.**  `|S(k) − S(0)| ≤ k·(3ω/x/Z)`, by iterating the single
shift bound `corr_shift_le` (each step moves the base offset by one). -/
private theorem shiftCorr_le (x ω : ℕ) (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (k : ℕ) :
    |shiftCorr x ω k - shiftCorr x ω 0|
      ≤ (k : ℝ) * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
  set D : ℝ := 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) with hD
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : |shiftCorr x ω (k + 1) - shiftCorr x ω k| ≤ D := by
      have h := corr_shift_le k (k + 1) hx hω hωx
      have e1 : shiftCorr x ω (k + 1)
          = ∫ n, (ArithmeticFunction.liouville (n + 1 + k) : ℝ)
              * (ArithmeticFunction.liouville (n + 1 + (k + 1)) : ℝ) ∂(logMeasure x ω) := by
        unfold shiftCorr
        refine congrArg _ (funext fun n => ?_)
        rw [show n + 1 + k = n + (k + 1) from by ring,
            show n + 1 + (k + 1) = n + (k + 1) + 1 from by ring]
      have e2 : shiftCorr x ω k
          = ∫ n, (ArithmeticFunction.liouville (n + k) : ℝ)
              * (ArithmeticFunction.liouville (n + (k + 1)) : ℝ) ∂(logMeasure x ω) := by
        unfold shiftCorr
        refine congrArg _ (funext fun n => ?_)
        rw [show n + k + 1 = n + (k + 1) from by ring]
      rw [e1, e2]; exact h
    calc |shiftCorr x ω (k + 1) - shiftCorr x ω 0|
        ≤ |shiftCorr x ω (k + 1) - shiftCorr x ω k|
            + |shiftCorr x ω k - shiftCorr x ω 0| := by
          have := abs_sub_le (shiftCorr x ω (k + 1)) (shiftCorr x ω k) (shiftCorr x ω 0)
          linarith
      _ ≤ D + (k : ℝ) * D := add_le_add hstep ih
      _ = ((k : ℝ) + 1) * D := by ring
      _ = ((k + 1 : ℕ) : ℝ) * D := by push_cast; ring

/-- `shiftCorr x ω 0 = X`, the base single correlation. -/
private theorem shiftCorr_zero (x ω : ℕ) :
    shiftCorr x ω 0 = ∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω) := by
  unfold shiftCorr
  refine congrArg _ (funext fun n => ?_)
  simp only [Nat.add_zero]

/-- The harmonic window normalizer `Z = ∑_{(x/ω,x]} 1/n` is positive (`x` itself is in
the window and contributes `1/x > 0`). -/
private theorem window_Z_pos {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  apply Finset.sum_pos
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
      exact_mod_cast this
    exact inv_pos.mpr hnR
  · refine ⟨x, ?_⟩
    rw [Finset.mem_Ioc]
    exact ⟨Nat.div_lt_self (by omega) (by omega), le_refl x⟩

/-- `|X| ≤ 1` for the single correlation `X = ∫ λ(n)·λ(n+1) ∂logMeasure`: the measure
is a probability measure and `|λ·λ| ≤ 1`. -/
private theorem absX_le_one {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    |∫ n, (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + 1) : ℝ)
        ∂(logMeasure x ω)| ≤ 1 := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  have hZpos : 0 < Z := window_Z_pos hx hω
  rw [integral_logMeasure_eq]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Z⁻¹)]
  have hbound : |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + 1) : ℝ)
        * (n : ℝ)⁻¹| ≤ Z := by
    calc |∑ n ∈ Finset.Ioc (x / ω) x,
            (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + 1) : ℝ)
              * (n : ℝ)⁻¹|
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x,
            |(ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + 1) : ℝ)
              * (n : ℝ)⁻¹| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹), abs_mul]
          have h1 : |(ArithmeticFunction.liouville n : ℝ)|
              * |(ArithmeticFunction.liouville (n + 1) : ℝ)| ≤ 1 :=
            mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)
          nlinarith [inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hfin : Z⁻¹ * |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + 1) : ℝ)
        * (n : ℝ)⁻¹| ≤ Z⁻¹ * Z :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  rwa [inv_mul_cancel₀ hZpos.ne'] at hfin

/-- **Crude window Mertens.**  `∑_{p∈𝒫_H} log p / p ≤ log(ε²H)·SP` since every window
prime satisfies `p ≤ ε²H`, hence `log p ≤ log(ε²H)`. -/
private theorem window_sum_log_div (eps : ℚ) (H : ℕ) :
    ∑ p ∈ primeWindow eps H, Real.log p / (p : ℝ)
      ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : 1 ≤ p := (prime_of_mem_primeWindow hp).one_lt.le
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hple : (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have hmem := mem_primeWindow.mp hp
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast hmem.1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hlogp : Real.log p ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) :=
    Real.log_le_log hpR hple
  rw [div_eq_mul_inv, one_div]
  exact mul_le_mul_of_nonneg_right hlogp (inv_nonneg.mpr hpR.le)

/-- **The `SP₂` bound.**  `∑_{p∈𝒫_H} 1/p² ≤ (2/(ε²H))·SP` from the window lower bound
`ε²H/2 < p`, i.e. `1/p ≤ 2/(ε²H)`. -/
private theorem window_sum_inv_sq (eps : ℚ) (H : ℕ) :
    ∑ p ∈ primeWindow eps H, (1 / (p : ℝ) ^ 2)
      ≤ (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : 1 ≤ p := (prime_of_mem_primeWindow hp).one_lt.le
  have hlb : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (p : ℝ) := window_lb eps H ⟨p, hp⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hple : (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hEH : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := lt_of_lt_of_le hpR hple
  have hinv : 1 / (p : ℝ) ≤ 2 / ((eps : ℝ) ^ 2 * (H : ℝ)) := by
    rw [div_le_div_iff₀ hpR hEH]; nlinarith [hlb]
  have key : (1 / (p : ℝ)) * (1 / (p : ℝ))
      ≤ (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * (1 / (p : ℝ)) :=
    mul_le_mul_of_nonneg_right hinv (by positivity)
  calc (1 : ℝ) / (p : ℝ) ^ 2 = (1 / (p : ℝ)) ^ 2 := by rw [div_pow, one_pow]
    _ = (1 / (p : ℝ)) * (1 / (p : ℝ)) := pow_two (1 / (p : ℝ))
    _ ≤ (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * (1 / (p : ℝ)) := key

/-- **Gate → residue class.**  The gate `((n+j+1):ZMod p) = 0` selects exactly the
residue class `n % p = r` where `r = (-(j+1) mod p)`, and `p ∣ (r+j+1)`.  This is the
bridge from `fBridgeF_liouville_apply`'s gate to `perPair_collapse`'s filter. -/
private theorem gate_residue (p j : ℕ) (hp : 2 ≤ p) :
    ∃ r : ℕ, r < p ∧ p ∣ (r + j + 1) ∧
      ∀ n : ℕ, ((n + j + 1 : ℕ) : ZMod p) = 0 ↔ n % p = r := by
  haveI : NeZero p := ⟨by omega⟩
  set c : ZMod p := -((j + 1 : ℕ) : ZMod p) with hc
  have hrc : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_rightInverse c
  have hlt : c.val < p := ZMod.val_lt c
  have hdvd : p ∣ (c.val + j + 1) := by
    rw [← ZMod.natCast_eq_zero_iff,
        show ((c.val + j + 1 : ℕ) : ZMod p) = ((c.val : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p)
          by push_cast; ring, hrc, hc]
    ring
  have hc0 : (c.val + j + 1) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdvd
  refine ⟨c.val, hlt, hdvd, ?_⟩
  intro n
  rw [ZMod.natCast_eq_zero_iff, ← Nat.modEq_zero_iff_dvd]
  constructor
  · intro h
    have h2 : n + j + 1 ≡ c.val + j + 1 [MOD p] := h.trans hc0.symm
    have hn : n ≡ c.val [MOD p] :=
      Nat.ModEq.add_right_cancel' j (Nat.ModEq.add_right_cancel' 1 h2)
    unfold Nat.ModEq at hn
    rw [hn, Nat.mod_eq_of_lt hlt]
  · intro h
    have hn : n ≡ c.val [MOD p] := by
      unfold Nat.ModEq; rw [h, Nat.mod_eq_of_lt hlt]
    exact ((hn.add_right j).add_right 1).trans hc0

/-- **The per-pair bound (non-boundary `j+p < H`).**  Chains `perPair_collapse` (collapse
defect `2r/p²`), `dilated_window_stability` ÷ p (swap defect `(2·log p+6)/p`), and
`shiftCorr_le` ÷ p (shift defect `(k·3ω/x)/p`, `k = (r+j+1)/p ≤ 1+H/p`).  Bounds the
residue-class term `T(p,j)` around `(1/p)·X`. -/
private theorem perPair_bound {x ω : ℕ} (H : ℕ) (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (p j r : ℕ) (hp : 2 ≤ p) (hrp : r < p) (hdvd : p ∣ (r + j + 1))
    (hrx : r ≤ x / ω) (hB : 1 ≤ x / ω) (hkH : r + j + 1 ≤ p + H) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (n + j + p + 1) : ℝ) / (n : ℝ))
         / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
       - (1 / (p : ℝ)) * shiftCorr x ω 0|
      ≤ (2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
            * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZdef
  set S : ℝ := 3 * (ω : ℝ) / (x : ℝ) / Z with hSdef
  have hZpos : 0 < Z := window_Z_pos hx hω
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hSdef]; positivity
  -- the collapsed correlation `g`
  set g : ℕ → ℝ := fun m => (ArithmeticFunction.liouville (m + (r + j + 1) / p) : ℝ)
      * (ArithmeticFunction.liouville (m + (r + j + 1) / p + 1) : ℝ) with hgdef
  have hg : ∀ n : ℕ, |g n| ≤ 1 := fun n => by
    rw [hgdef]
    exact (abs_mul _ _).trans_le
      (mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _))
  -- step 1: collapse (perPair_collapse's image sum is exactly `∑ g/m`)
  have hcol := perPair_collapse (x := x) (ω := ω) (p := p) (r := r) (j := j)
    (by omega : 1 ≤ p) hrx hdvd hZpos
  -- step 2: swap
  have hswap0 := dilated_window_stability (x := x) (ω := ω) (p := p) (r := r) hp hrp hB hg hZpos
  -- identify the base window sum with `shiftCorr`
  have hshift_eq : (∑ n ∈ Finset.Ioc (x / ω) x, g n / (n : ℝ)) / Z
      = shiftCorr x ω ((r + j + 1) / p) := by
    unfold shiftCorr
    rw [integral_logMeasure_eq,
        Finset.sum_congr rfl (fun n _ => (div_eq_mul_inv (g n) (n : ℝ))), div_eq_mul_inv]
    exact mul_comm _ _
  have hshiftle := shiftCorr_le x ω hx hω hωx ((r + j + 1) / p)
  -- name the three transport quantities
  set A : ℝ := (∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
      (ArithmeticFunction.liouville (n + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (n + j + p + 1) : ℝ) / (n : ℝ)) / Z with hAdef
  set IMG : ℝ := (∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image
      (fun n => n / p), g m / (m : ℝ)) / Z with hIMGdef
  -- `hcol : |A - 1/p * IMG| ≤ 2r/p²/Z`, `hswap0 : |IMG - (Σ_Ioc g/·)/Z| ≤ (2log p+6)/Z`
  have hBC : |(1 / (p : ℝ)) * IMG - (1 / (p : ℝ)) * shiftCorr x ω ((r + j + 1) / p)|
      ≤ (1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z) := by
    rw [← hshift_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hswap0 (by positivity)
  have hCD : |(1 / (p : ℝ)) * shiftCorr x ω ((r + j + 1) / p) - (1 / (p : ℝ)) * shiftCorr x ω 0|
      ≤ (1 / (p : ℝ)) * (((r + j + 1) / p : ℕ) * S) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hshiftle (by positivity)
  -- arithmetic simplification of the three defects
  have hrle : (r : ℝ) ≤ (p : ℝ) := by exact_mod_cast hrp.le
  have hkp : (((r + j + 1) / p : ℕ) : ℝ) * (p : ℝ) ≤ (p : ℝ) + (H : ℝ) := by
    have h2 : (r + j + 1) / p * p ≤ p + H := le_trans (Nat.div_mul_le_self _ _) hkH
    exact_mod_cast h2
  have hb1a : 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z ≤ 2 / ((p : ℝ) * Z) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hrle) hpR.le) hZpos.le]
  have hb1b : (1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z)
      = (2 * Real.log p + 6) / ((p : ℝ) * Z) := by
    field_simp
  have hsplit : (2 * Real.log p + 8) / ((p : ℝ) * Z)
      = 2 / ((p : ℝ) * Z) + (2 * Real.log p + 6) / ((p : ℝ) * Z) := by
    rw [← add_div]; congr 1; ring
  have hbound2 : (1 / (p : ℝ)) * (((r + j + 1) / p : ℕ) * S)
      ≤ ((1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2) * S := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hSnn
    have hRHS : (1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2 = ((p : ℝ) + H) / (p : ℝ) ^ 2 := by
      field_simp
    rw [mul_comm, mul_one_div, hRHS, div_le_div_iff₀ hpR (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkp hpR.le]
  -- assemble via the triangle inequality
  calc |A - (1 / (p : ℝ)) * shiftCorr x ω 0|
      ≤ |A - (1 / (p : ℝ)) * IMG|
          + (|(1 / (p : ℝ)) * IMG - (1 / (p : ℝ)) * shiftCorr x ω ((r + j + 1) / p)|
            + |(1 / (p : ℝ)) * shiftCorr x ω ((r + j + 1) / p)
                - (1 / (p : ℝ)) * shiftCorr x ω 0|) := by
        have h1 := abs_sub_le A ((1 / (p : ℝ)) * IMG) ((1 / (p : ℝ)) * shiftCorr x ω 0)
        have h2 := abs_sub_le ((1 / (p : ℝ)) * IMG)
          ((1 / (p : ℝ)) * shiftCorr x ω ((r + j + 1) / p)) ((1 / (p : ℝ)) * shiftCorr x ω 0)
        linarith
    _ ≤ 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z
          + ((1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z)
            + (1 / (p : ℝ)) * (((r + j + 1) / p : ℕ) * S)) := by
        linarith [hcol, hBC, hCD]
    _ ≤ (2 * Real.log p + 8) / ((p : ℝ) * Z)
          + ((1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2) * S := by
        rw [hsplit, hb1b]
        linarith [hb1a, hbound2]

/-- **The F-bridge integral unfolds to the per-pair double sum.**  `∫F = ∑_p ∑_{j<H} T'(p,j)`
where `T'(p,j) = ∫ [gate]·λ(n+j+1)·windowVal(j+p)`.  Proved through `integral_logMeasure_eq`
(no integrability side-conditions) + `fBridgeF_liouville_apply` + a triple-sum reindex. -/
private theorem IF_unfold (eps : ℚ) (H : ℕ) {x ω : ℕ} :
    (∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)
            else 0) ∂(logMeasure x ω) := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  rw [integral_logMeasure_eq]
  simp_rw [fBridgeF_liouville_apply eps H, integral_logMeasure_eq]
  have hR : ∑ n ∈ Finset.Ioc (x / ω) x,
        (∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0)) * (n : ℝ)⁻¹
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H, ∑ n ∈ Finset.Ioc (x / ω) x,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) * (n : ℝ)⁻¹ := by
    have step1 : ∀ n : ℕ,
        (∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0)) * (n : ℝ)⁻¹
        = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) * (n : ℝ)⁻¹ := by
      intro n
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_mul _ _ _)
    rw [Finset.sum_congr rfl (fun n _ => step1 n), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]

/-- **Per-pair bound with boundary term.**  Each pair term `T'(p,j)` obeys
`|T'(p,j) − (1/p)·X| ≤ B_p + [H ≤ j+p]·(1/p)|X|`, where `B_p` is the transport bound.
Non-boundary (`j+p<H`): `T' = A` and `perPair_bound` applies.  Boundary (`j+p≥H`):
`windowVal = 0` so `T' = 0` and the deficit is `(1/p)|X|`. -/
private theorem per_term (eps : ℚ) (H : ℕ) {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hxωH : H ≤ x / ω) (p : ℕ) (hp : p ∈ primeWindow eps H) (j : ℕ) (hj : j < H) :
    |(∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
      - (1 / ((p : ℕ) : ℝ)) * (∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω))|
      ≤ ((2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
          + (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
              * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
        + (if H ≤ j + (p : ℕ) then (1 / ((p : ℕ) : ℝ)) * |∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0) := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  set X : ℝ := ∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω) with hXdef
  have hp2 : 2 ≤ (p : ℕ) := (prime_of_mem_primeWindow hp).two_le
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (p : ℕ))
  have hlogp : (0 : ℝ) ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega))
  have hZpos : 0 < Z := window_Z_pos hx hω
  have hBp_nonneg : (0 : ℝ) ≤ (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ) * Z)
      + (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2) * (3 * (ω : ℝ) / (x : ℝ) / Z) := by
    apply add_nonneg
    · exact div_nonneg (by linarith [hlogp]) (by positivity)
    · exact mul_nonneg (by positivity) (by positivity)
  by_cases hbd : H ≤ j + (p : ℕ)
  · rw [if_pos hbd]
    have hwv0 : ∀ n : ℕ, (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) = 0 := fun n => by
      simp only [windowVal, dif_neg (show ¬ j + (p : ℕ) < H by omega), Int.cast_zero]
    have hT0 : (∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0)
        ∂(logMeasure x ω)) = 0 := by
      rw [show (fun n => if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0)
          = (fun _ => (0 : ℝ)) from funext (fun n => by rw [hwv0 n, mul_zero, ite_self]),
          integral_zero]
    have hp_inv : (0 : ℝ) ≤ 1 / ((p : ℕ) : ℝ) := by positivity
    rw [hT0, zero_sub, abs_neg, abs_mul, abs_of_nonneg hp_inv]
    linarith [hBp_nonneg]
  · rw [if_neg hbd, add_zero]
    rw [not_le] at hbd
    obtain ⟨r, hrp, hdvd, hgate⟩ := gate_residue (p : ℕ) j hp2
    have hT_eq : (∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
        = (∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % (p : ℕ) = r),
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (ArithmeticFunction.liouville (n + j + (p : ℕ) + 1) : ℝ) / (n : ℝ)) / Z := by
      rw [show (fun n => if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0)
          = (fun n => if n % (p : ℕ) = r then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (ArithmeticFunction.liouville (n + j + (p : ℕ) + 1) : ℝ) else 0)
          from funext (fun n => by
            rw [windowVal_liouvilleWindow H n (j + (p : ℕ)) (by omega),
                show n + (j + (p : ℕ)) + 1 = n + j + (p : ℕ) + 1 from by ring]
            simp only [hgate n])]
      rw [integral_logMeasure_eq, div_eq_mul_inv, mul_comm]
      congr 1
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun n _ => by rw [ite_mul, zero_mul, div_eq_mul_inv])
    rw [hT_eq, hXdef, ← shiftCorr_zero x ω]
    exact perPair_bound H hx hω hωx (p : ℕ) j r hp2 hrp hdvd
      (le_trans hrp.le (le_trans (by omega : (p : ℕ) ≤ H) hxωH))
      (by omega) (by omega)

/-- Boundary-count bound: at most `p` of the `j < H` are boundary (`H ≤ j+p`). -/
private theorem boundary_card_le (H p : ℕ) :
    ((Finset.range H).filter (fun j => H ≤ j + p)).card ≤ p := by
  have hsub : (Finset.range H).filter (fun j => H ≤ j + p) ⊆ Finset.Ico (H - p) H := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_Ico]
    omega
  calc ((Finset.range H).filter (fun j => H ≤ j + p)).card
      ≤ (Finset.Ico (H - p) H).card := Finset.card_le_card hsub
    _ = H - (H - p) := Nat.card_Ico _ _
    _ ≤ p := by omega

/-! ### The `c`-ceiling rider (W-F3 §15 repair 2 — lands in Lean with B-5) -/

/-- **The `c`-ceiling rider.**  W-F3 §14's gate `hεh' : ε·h ≤ c/(32·log 4)` is the binder the
tree actually enforces at shift `h` (it is `hT3`'s gate, `:607-625`, carrying one factor `h`).
§14.2 claimed it *implies* K1's `ε²·h < 1` — but that step needs an UPPER bound on `c`, and
`hbudget_holds` binds `c` existentially exposing only `0 < c`.  This lemma makes the implication
explicit and honest, with the ceiling as a named hypothesis rather than an assumed one.

`ε²h = ε·(ε h) ≤ ε·c/(32 log 4) ≤ (1/2)·(1/32) = 1/64 < 1`, using `1 ≤ log 4` (i.e. `e ≤ 4`).
Any ceiling `c ≤ 88` would do; `c ≤ 1` is stated because it is the one the tree can pin cheaply. -/
theorem epsh_gate_implies_epssq_h {eps c : ℝ} {h : ℕ}
    (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 2) (hc1 : c ≤ 1)
    (hgate : eps * (h : ℝ) ≤ c / (32 * Real.log 4)) :
    eps ^ 2 * (h : ℝ) < 1 := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have h32 : (32 : ℝ) ≤ 32 * Real.log 4 := by nlinarith [hlog4]
  have hcle : c / (32 * Real.log 4) ≤ 1 / 32 := by
    calc c / (32 * Real.log 4) ≤ 1 / (32 * Real.log 4) := by gcongr
      _ ≤ 1 / 32 := one_div_le_one_div_of_le (by norm_num) h32
  have hepsh : eps * (h : ℝ) ≤ 1 / 32 := le_trans hgate hcle
  have hrw : eps ^ 2 * (h : ℝ) = eps * (eps * (h : ℝ)) := by ring
  rw [hrw]
  nlinarith [hepsh, heps0, heps1]

set_option maxHeartbeats 1600000 in
-- The budget aggregation (∫F unfold + three window totals + double-sum reduction) is a
-- large single elaboration; raise the heartbeat ceiling to accommodate it.
/-- **HBUDGET (`hbudget_holds`).**  The error budget
`|∫F − ∑_p (H/p)·X| ≤ (1/4)·SP·H·ε` at the adopted regime, mirroring D3's
`∃c>0·∃H₀·∀` idiom (it consumes D3's Mertens constant `c` and threshold `H₀`).  The
`hxbig` floor `ω·H + 48ω(1+2/ε²)/ε ≤ x` is the predecessor's "weakest clean" form
refined to also fund `x/ω ≥ H`. -/
theorem hbudget_holds :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
  obtain ⟨c, hc, H₀, hD3⟩ := primeWindow_sum_inv_ge
  refine ⟨c, hc, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
  -- abbreviations kept raw (they interface with the window lemmas via linarith)
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := window_Z_pos hx hω
  have hZlb : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    (harmonic_window_bounds hx hω hωx).1
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hε2H0 : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by linarith
  have hSP_lb : c / Real.log H ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    hD3 eps H hH0 hsqrt hepssq
  have hSPpos : (0 : ℝ) < ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    lt_of_lt_of_le (by positivity) hSP_lb
  have habsX : |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| ≤ 1 := absX_le_one hx hω
  have hcard : ((primeWindow eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime eps H hsqrt hH3
  have hxωH : H ≤ x / ω := by
    have hpos : (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) := by positivity
    have h2 : ω * H ≤ x := by
      have : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ω), Nat.mul_comm]; exact h2
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast (by omega : 0 < ω)
  have hε_le1 : (eps : ℝ) ≤ 1 := by nlinarith [hepssq, hepsR]
  have hlogε2H : (0 : ℝ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hple : ∀ p ∈ primeWindow eps H, (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    intro p hp
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hZbig' : 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64
      ≤ (eps : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    have h2 : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hepsR.le
    have hlhs : (eps : ℝ) * ((16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ))
        = 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 := by field_simp
    rw [hlhs] at h3; exact h3
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    nlinarith [hZbig', hlogε2H, hε_le1, hZpos, mul_le_mul_of_nonneg_right hε_le1 hZpos.le]
  -- === total 1: the Z-controlled (collapse+swap) slice ≤ (1/8)·SP·H·ε ===
  have hZεbound : (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
      / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) ≤ (eps : ℝ) / 8 := by
    rw [div_le_div_iff₀ hZpos (by norm_num)]
    nlinarith [hZbig']
  have hT1 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
        * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have hstep : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      have hle : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          ≤ ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < (p : ℕ))
        have hlogle : Real.log (p : ℕ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) :=
          Real.log_le_log hpR (hple p hp)
        gcongr
      have heq : ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (((p : ℕ) : ℝ) * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          = (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [div_mul_eq_mul_div, mul_one_div, div_div]
      linarith [hle, heq.le, heq.ge]
    calc (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (H : ℝ) * ((2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hHR.le
      _ ≤ (H : ℝ) * ((eps : ℝ) / 8 * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hHR.le
          exact mul_le_mul_of_nonneg_right hZεbound hSPpos.le
      _ = (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by ring
  -- === total 2: the shift slice ≤ (1/16)·SP·H·ε ===
  have key2 : ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      = ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
  have hHsq : (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2)
      ≤ (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left (window_sum_inv_sq eps H) hHR.le
    have h2 : (H : ℝ) * ((2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        = (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hSpos2 : (0 : ℝ) ≤ 3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    positivity
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hle : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by
      nlinarith [hxbig, (show (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        by positivity)]
    nlinarith [hle, mul_pos hωR hHR]
  have hxbound : 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (eps : ℝ) / (16 * (1 + 2 / (eps : ℝ) ^ 2)) := by
    have hxZ : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
      have hx1 : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := by
        nlinarith [hxbig, (show (0 : ℝ) ≤ (ω : ℝ) * (H : ℝ) by positivity)]
      calc 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := hx1
        _ = (x : ℝ) * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hZ1 hxpos.le
    rw [div_le_iff₀ hepsR] at hxZ
    rw [div_div, div_le_div_iff₀ (mul_pos hxpos hZpos) (by positivity)]
    nlinarith [hxZ]
  have hT2 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    rw [key2]
    have hfac : ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ ((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hHsq]) hSpos2
    have hmul : (H : ℝ) * (((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
      have hCbound := hxbound
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (1 + 2 / (eps : ℝ) ^ 2))] at hCbound
      nlinarith [mul_le_mul_of_nonneg_left hCbound
        (mul_nonneg (mul_nonneg hHR.le hSPpos.le) (by norm_num : (0:ℝ) ≤ (1:ℝ)/16))]
    exact le_trans (mul_le_mul_of_nonneg_left hfac hHR.le) hmul
  -- === total 3: the boundary slice ≤ (1/16)·SP·H·ε ===
  have hT3 : ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have h32 : (eps : ℝ) * (32 * Real.log 4) ≤ c := (le_div_iff₀ (by positivity)).mp heps_small
    have hkey3' : 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))
        ≤ (1 / 16) * c * (H : ℝ) * (eps : ℝ) := by
      nlinarith [h32, mul_nonneg (mul_nonneg hepsR.le hHR.le) hepsR.le, hlog4]
    calc ((primeWindow eps H).card : ℝ) * |_|
        ≤ ((primeWindow eps H).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left habsX (Nat.cast_nonneg _)
      _ = ((primeWindow eps H).card : ℝ) := mul_one _
      _ ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) := hcard
      _ = (2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))) / Real.log H := by ring
      _ ≤ ((1 / 16) * c * (H : ℝ) * (eps : ℝ)) / Real.log H := by
          gcongr
      _ = (1 / 16) * (c / Real.log H) * (H : ℝ) * (eps : ℝ) := by ring
      _ ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSP_lb (by norm_num)) hHR.le) hepsR.le
  -- === the reduction: |IF − MAIN| ≤ H·ΣB + card·|X| ≤ T1 + T2 + T3 ===
  have hIF : (∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)
            else 0) ∂(logMeasure x ω) := by
    rw [IF_unfold eps H]
    exact Finset.sum_coe_sort (primeWindow eps H)
      (fun p => ∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod p) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + p) : ℝ) else 0) ∂(logMeasure x ω))
  have hMAIN : (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
          (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hIF, hMAIN, ← Finset.sum_sub_distrib]
  have hcombine : ∀ p ∈ primeWindow eps H,
      (∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
        - ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω))
      = ∑ j ∈ Finset.range H,
          ((∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
              (ArithmeticFunction.liouville (n + j + 1) : ℝ)
                * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
            - (1 / (p : ℝ)) * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω))) :=
    fun p _ => by rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hcombine]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun j hj =>
    per_term eps H hx hω hωx hxωH p hp j (Finset.mem_range.mp hj)))).trans ?_
  -- split the inner sum (per-pair bound j-independent; boundary term counted separately)
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hbnd_total : ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
      (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0)
      ≤ ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
    have hbnd : ∀ p ∈ primeWindow eps H, (∑ j ∈ Finset.range H,
        (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0))
        ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < p)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcardp : (((Finset.range H).filter (fun j => H ≤ j + p)).card : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast boundary_card_le H p
      calc (((Finset.range H).filter (fun j => H ≤ j + p)).card : ℝ) * ((1 / (p : ℝ)) * |_|)
          ≤ (p : ℝ) * ((1 / (p : ℝ)) * |_|) :=
            mul_le_mul_of_nonneg_right hcardp (by positivity)
        _ = |_| := by rw [← mul_assoc, mul_one_div, div_self hpR.ne', one_mul]
    calc ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0)
        ≤ ∑ p ∈ primeWindow eps H, |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| :=
          Finset.sum_le_sum hbnd
      _ = ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hT1, hT2, hT3, hbnd_total]

/-- **The capstone.**  Composing `hbudget_holds` through `hreduce_holds`: at the adopted
regime, the single-correlation seed `hseed : ε/2 ≤ |X|` forces the frozen `hreduce`
conclusion `(1/2)·SP·H·|X| ≤ |∫F|` (the `h211` producer's terminal inequality).  This is
the consumable form for W3E-FINAL — instantiate at the tower's `H`. -/
theorem hreduce_holds_final :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  obtain ⟨c, hc, H₀, hbud⟩ := hbudget_holds
  refine ⟨c, hc, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig hseed
  exact hreduce_holds eps H hseed
    (hbud eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig)

/-! ### W-F3 B-5 — THE SHIFT-`h` PORT OF THE BUDGET

The `h`-family beside the landed `h = 1` objects.  Nothing below edits a landed
declaration.  Three things are worth stating before the code, because they are what the
port MEASURED rather than what it assumed:

* **THE NEW DEFINITION IS THE GAP.**  `shiftCorr` (`:46`) hardcodes its gap to `1`
  (`λ(n+k)·λ(n+k+1)`); `k` is the BASE offset and telescopes.  `shiftCorrH` below opens the
  GAP as a second parameter.  It is `private`, exactly as its three frozen siblings are —
  see the visibility note on `shiftCorrH` itself.
* **`boundary_card_le` NEEDS NO PORT.**  It is stated at an arbitrary second argument, so
  `boundary_card_le H (p * h)` already IS the shifted boundary count `≤ p·h`.
* **`0 < h` IS FORCED, and `per_term_h` is where it is forced.**  At `h = 0` the shifted
  boundary gate `j + p·h < H` degenerates to `j < H` and no longer bounds `p`, so the
  residue bound `r ≤ x/ω` — which the `h = 1` script gets free from `j + p < H` — fails.
  This matches `ShiftFork`'s own "`h = 0` is degenerate" header note. -/

/-- **The gap-`h` correlation family** (THE node's one new definition):
`S_h(k) = ∫ λ(n+k)·λ(n+k+h) ∂logMeasure`.  The landed `shiftCorr x ω k` is the `h = 1`
member (`shiftCorrH_one`); `k` is the base offset, which telescopes, and `h` is the GAP,
which does not.

⚠️ VISIBILITY, REPORTED NOT DECIDED.  This is `private`, mirroring `shiftCorr`,
`shiftCorr_le`, `shiftCorr_zero` — all three of which are `private` to this file.  Nothing
outside `HBudget.lean` can name it.  That is the right default for a purely additive port
(it keeps the footprint identical to the frozen sibling's), but if a downstream node needs
the gap-`h` family, UN-PRIVATING IS A VISIBILITY CHANGE and belongs to a session that owns
the decision, not to this one. -/
private noncomputable def shiftCorrH (x ω k h : ℕ) : ℝ :=
  ∫ n, (ArithmeticFunction.liouville (n + k) : ℝ)
      * (ArithmeticFunction.liouville (n + k + h) : ℝ) ∂(logMeasure x ω)

/-- **Shift telescoping at gap `h`.**  `|S_h(k) − S_h(0)| ≤ k·(3ω/x/Z)`, the `h`-family port
of `shiftCorr_le`.  The step is `corr_shift_le k (k + h)` — the landed carrier ALREADY takes
TWO INDEPENDENT OFFSETS (`ShiftCorr.lean:276`), so opening the gap costs no new analysis:
the bound `3ω/x/Z` is `h`-INDEPENDENT, and only the base offset `k` multiplies it. -/
private theorem shiftCorrH_le (x ω : ℕ) (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (k h : ℕ) :
    |shiftCorrH x ω k h - shiftCorrH x ω 0 h|
      ≤ (k : ℝ) * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
  set D : ℝ := 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) with hD
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : |shiftCorrH x ω (k + 1) h - shiftCorrH x ω k h| ≤ D := by
      have hc := corr_shift_le k (k + h) hx hω hωx
      have e1 : shiftCorrH x ω (k + 1) h
          = ∫ n, (ArithmeticFunction.liouville (n + 1 + k) : ℝ)
              * (ArithmeticFunction.liouville (n + 1 + (k + h)) : ℝ) ∂(logMeasure x ω) := by
        unfold shiftCorrH
        refine congrArg _ (funext fun n => ?_)
        rw [show n + 1 + k = n + (k + 1) from by ring,
            show n + 1 + (k + h) = n + (k + 1) + h from by ring]
      have e2 : shiftCorrH x ω k h
          = ∫ n, (ArithmeticFunction.liouville (n + k) : ℝ)
              * (ArithmeticFunction.liouville (n + (k + h)) : ℝ) ∂(logMeasure x ω) := by
        unfold shiftCorrH
        refine congrArg _ (funext fun n => ?_)
        rw [show n + k + h = n + (k + h) from by ring]
      rw [e1, e2]; exact hc
    calc |shiftCorrH x ω (k + 1) h - shiftCorrH x ω 0 h|
        ≤ |shiftCorrH x ω (k + 1) h - shiftCorrH x ω k h|
            + |shiftCorrH x ω k h - shiftCorrH x ω 0 h| := by
          have := abs_sub_le (shiftCorrH x ω (k + 1) h) (shiftCorrH x ω k h)
            (shiftCorrH x ω 0 h)
          linarith
      _ ≤ D + (k : ℝ) * D := add_le_add hstep ih
      _ = ((k : ℝ) + 1) * D := by ring
      _ = ((k + 1 : ℕ) : ℝ) * D := by push_cast; ring

/-- `shiftCorrH x ω 0 h = X_h`, the base gap-`h` correlation. -/
private theorem shiftCorrH_zero (x ω h : ℕ) :
    shiftCorrH x ω 0 h = ∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω) := by
  unfold shiftCorrH
  refine congrArg _ (funext fun n => ?_)
  simp only [Nat.add_zero]

/-- **C1 — the `h = 1` compat for the new definition, `rfl`-grade.**  `shiftCorrH x ω k 1`
IS the landed `shiftCorr x ω k`: substituting the literal `1` for the GAP yields `n + k + 1`
syntactically.

⚠️ CONTRAST WITH THE OFFSET.  This is `rfl` because the gap enters as `_ + h` (`Nat.add`
recurses on its second argument, and `1` is a literal there).  The window OFFSET enters as
`(p : ℕ) * h`, which is STUCK at `h = 1` for a variable `p` — hence
`fBridgeF_h_liouville_apply_one` (`Prop26.lean`) cannot be `rfl` and must route through
`fBridgeF_h_one`.  The two "`h = 1` compats" of this node are NOT the same shape. -/
private theorem shiftCorrH_one (x ω k : ℕ) : shiftCorrH x ω k 1 = shiftCorr x ω k := rfl

/-- `|X_h| ≤ 1` for the gap-`h` correlation.  The `h = 1` script (`absX_le_one`) never reads
the second Liouville index, so it survives verbatim. -/
private theorem absXh_le_one (h : ℕ) {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    |∫ n, (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + h) : ℝ)
        ∂(logMeasure x ω)| ≤ 1 := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  have hZpos : 0 < Z := window_Z_pos hx hω
  rw [integral_logMeasure_eq]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Z⁻¹)]
  have hbound : |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + h) : ℝ)
        * (n : ℝ)⁻¹| ≤ Z := by
    calc |∑ n ∈ Finset.Ioc (x / ω) x,
            (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + h) : ℝ)
              * (n : ℝ)⁻¹|
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x,
            |(ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + h) : ℝ)
              * (n : ℝ)⁻¹| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹), abs_mul]
          have h1 : |(ArithmeticFunction.liouville n : ℝ)|
              * |(ArithmeticFunction.liouville (n + h) : ℝ)| ≤ 1 :=
            mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)
          nlinarith [inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hfin : Z⁻¹ * |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.liouville (n + h) : ℝ)
        * (n : ℝ)⁻¹| ≤ Z⁻¹ * Z :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  rwa [inv_mul_cancel₀ hZpos.ne'] at hfin

/-- `λ(p)² = 1` for `p ≠ 0`.

⛔ DUPLICATION, REPORTED.  `DilationStability.lean` has `liouville_sq` and
`collapse_identity`, and `ShiftFork.lean:434` has the gap-`h` identity itself
(`liouville_collapse_h`) — but the first two are `private` to their file and `ShiftFork`
is NOT in this file's import closure (it imports `ChowlaFailure`, which this file also
imports; neither imports the other).  Reaching the existing lemma would mean ADDING AN
IMPORT to a landed file, which is a structural change, so the identity is re-proved here
as a `private` local instead.  Flagged rather than silently either way. -/
private lemma liouville_sq_h {p : ℕ} (hp : p ≠ 0) :
    (ArithmeticFunction.liouville p : ℝ) ^ 2 = 1 := by
  rw [ArithmeticFunction.liouville_apply hp]; push_cast
  rw [← pow_mul]
  exact Even.neg_one_pow ⟨ArithmeticFunction.cardFactors p, by ring⟩

/-- **The collapse identity at gap `h`.**  For `p ≠ 0`, `λ(p·N)·λ(p·N + p·h) = λ(N)·λ(N+h)`:
both arguments carry the factor `p` (`p·N + p·h = p·(N+h)`) and `λ(p)² = 1` erases it.  This
is what makes the gap-`h` port free — the collapse does not care how far apart the two
arguments are, only that BOTH are multiples of `p`. -/
private lemma collapse_identity_h {p : ℕ} (hp : p ≠ 0) (h N : ℕ) :
    (ArithmeticFunction.liouville (p * N) : ℝ)
        * (ArithmeticFunction.liouville (p * N + p * h) : ℝ)
      = (ArithmeticFunction.liouville N : ℝ)
          * (ArithmeticFunction.liouville (N + h) : ℝ) := by
  have hpN : p * N + p * h = p * (N + h) := by ring
  rw [hpN, ArithmeticFunction.liouville_apply_mul, ArithmeticFunction.liouville_apply_mul]
  have hsq := liouville_sq_h hp
  push_cast
  linear_combination (ArithmeticFunction.liouville N : ℝ)
    * (ArithmeticFunction.liouville (N + h) : ℝ) * hsq

/-- **Collapse before dilate, at gap `h`** — the `h`-family port of `perPair_collapse`.  On
the residue class `{n : n % p = r}` with `p ∣ r+j+1`, the gated correlation
`λ(n+j+1)·λ(n+j+p·h+1)` reduces to `1/p` times the clean GAP-`h` correlation
`λ(m+k)·λ(m+k+h)` at the collapsed base offset `k = (r+j+1)/p`, up to the SAME `2r/p²/Z`
dilation defect: the defect comes from `dilation_error_div`, which is generic in `f`, so it
does not see the gap. -/
private theorem perPair_collapse_h {x ω p r j h : ℕ} (hp : 1 ≤ p) (hr : r ≤ x / ω)
    (hdvd : p ∣ (r + j + 1)) {Z : ℝ} (hZ : 0 < Z) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (n + j + p * h + 1) : ℝ) / (n : ℝ)) / Z
       - 1 / (p : ℝ) *
         ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
            (ArithmeticFunction.liouville (m + (r + j + 1) / p) : ℝ)
              * (ArithmeticFunction.liouville (m + (r + j + 1) / p + h) : ℝ) / (m : ℝ)) / Z)|
      ≤ 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z := by
  set k := (r + j + 1) / p with hk
  have hpk : r + j + 1 = p * k := (Nat.mul_div_cancel' hdvd).symm
  have hkey := perPair_dilation_h (x := x) (ω := ω) h p j r hp hr hZ
  have hcongr : ∀ m ∈
      ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
      ((ArithmeticFunction.liouville (p * m + r + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (p * m + r + j + p * h + 1) : ℝ)) / (m : ℝ)
      = (ArithmeticFunction.liouville (m + k) : ℝ)
        * (ArithmeticFunction.liouville (m + k + h) : ℝ) / (m : ℝ) := by
    intro m _
    have e1 : p * m + r + j + 1 = p * (m + k) := by rw [Nat.mul_add]; omega
    have e2 : p * m + r + j + p * h + 1 = p * (m + k) + p * h := by rw [Nat.mul_add]; omega
    rw [e1, e2, collapse_identity_h (by omega) h (m + k)]
  rw [show (∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
        (ArithmeticFunction.liouville (m + k) : ℝ)
          * (ArithmeticFunction.liouville (m + k + h) : ℝ) / (m : ℝ))
      = ∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
          ((ArithmeticFunction.liouville (p * m + r + j + 1) : ℝ)
            * (ArithmeticFunction.liouville (p * m + r + j + p * h + 1) : ℝ)) / (m : ℝ)
      from Finset.sum_congr rfl (fun m hm => (hcongr m hm).symm)]
  calc |_| ≤ 2 * 1 * (r : ℝ) / (p : ℝ) ^ 2 / Z := hkey
    _ = 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z := by ring

private theorem perPair_bound_h {x ω : ℕ} (H h : ℕ) (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (p j r : ℕ) (hp : 2 ≤ p) (hrp : r < p) (hdvd : p ∣ (r + j + 1))
    (hrx : r ≤ x / ω) (hB : 1 ≤ x / ω) (hkH : r + j + 1 ≤ p + H) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (n + j + p * h + 1) : ℝ) / (n : ℝ))
         / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
       - (1 / (p : ℝ)) * shiftCorrH x ω 0 h|
      ≤ (2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
            * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZdef
  set S : ℝ := 3 * (ω : ℝ) / (x : ℝ) / Z with hSdef
  have hZpos : 0 < Z := window_Z_pos hx hω
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hSdef]; positivity
  -- the collapsed correlation `g`
  set g : ℕ → ℝ := fun m => (ArithmeticFunction.liouville (m + (r + j + 1) / p) : ℝ)
      * (ArithmeticFunction.liouville (m + (r + j + 1) / p + h) : ℝ) with hgdef
  have hg : ∀ n : ℕ, |g n| ≤ 1 := fun n => by
    rw [hgdef]
    exact (abs_mul _ _).trans_le
      (mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _))
  -- step 1: collapse (perPair_collapse's image sum is exactly `∑ g/m`)
  have hcol := perPair_collapse_h (x := x) (ω := ω) (p := p) (r := r) (j := j) (h := h)
    (by omega : 1 ≤ p) hrx hdvd hZpos
  -- step 2: swap
  have hswap0 := dilated_window_stability (x := x) (ω := ω) (p := p) (r := r) hp hrp hB hg hZpos
  -- identify the base window sum with `shiftCorr`
  have hshift_eq : (∑ n ∈ Finset.Ioc (x / ω) x, g n / (n : ℝ)) / Z
      = shiftCorrH x ω ((r + j + 1) / p) h := by
    unfold shiftCorrH
    rw [integral_logMeasure_eq,
        Finset.sum_congr rfl (fun n _ => (div_eq_mul_inv (g n) (n : ℝ))), div_eq_mul_inv]
    exact mul_comm _ _
  have hshiftle := shiftCorrH_le x ω hx hω hωx ((r + j + 1) / p) h
  -- name the three transport quantities
  set A : ℝ := (∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
      (ArithmeticFunction.liouville (n + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (n + j + p * h + 1) : ℝ) / (n : ℝ)) / Z with hAdef
  set IMG : ℝ := (∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image
      (fun n => n / p), g m / (m : ℝ)) / Z with hIMGdef
  -- `hcol : |A - 1/p * IMG| ≤ 2r/p²/Z`, `hswap0 : |IMG - (Σ_Ioc g/·)/Z| ≤ (2log p+6)/Z`
  have hBC : |(1 / (p : ℝ)) * IMG - (1 / (p : ℝ)) * shiftCorrH x ω ((r + j + 1) / p) h|
      ≤ (1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z) := by
    rw [← hshift_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hswap0 (by positivity)
  have hCD : |(1 / (p : ℝ)) * shiftCorrH x ω ((r + j + 1) / p) h
        - (1 / (p : ℝ)) * shiftCorrH x ω 0 h|
      ≤ (1 / (p : ℝ)) * (((r + j + 1) / p : ℕ) * S) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hshiftle (by positivity)
  -- arithmetic simplification of the three defects
  have hrle : (r : ℝ) ≤ (p : ℝ) := by exact_mod_cast hrp.le
  have hkp : (((r + j + 1) / p : ℕ) : ℝ) * (p : ℝ) ≤ (p : ℝ) + (H : ℝ) := by
    have h2 : (r + j + 1) / p * p ≤ p + H := le_trans (Nat.div_mul_le_self _ _) hkH
    exact_mod_cast h2
  have hb1a : 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z ≤ 2 / ((p : ℝ) * Z) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hrle) hpR.le) hZpos.le]
  have hb1b : (1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z)
      = (2 * Real.log p + 6) / ((p : ℝ) * Z) := by
    field_simp
  have hsplit : (2 * Real.log p + 8) / ((p : ℝ) * Z)
      = 2 / ((p : ℝ) * Z) + (2 * Real.log p + 6) / ((p : ℝ) * Z) := by
    rw [← add_div]; congr 1; ring
  have hbound2 : (1 / (p : ℝ)) * (((r + j + 1) / p : ℕ) * S)
      ≤ ((1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2) * S := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hSnn
    have hRHS : (1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2 = ((p : ℝ) + H) / (p : ℝ) ^ 2 := by
      field_simp
    rw [mul_comm, mul_one_div, hRHS, div_le_div_iff₀ hpR (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkp hpR.le]
  -- assemble via the triangle inequality
  calc |A - (1 / (p : ℝ)) * shiftCorrH x ω 0 h|
      ≤ |A - (1 / (p : ℝ)) * IMG|
          + (|(1 / (p : ℝ)) * IMG - (1 / (p : ℝ)) * shiftCorrH x ω ((r + j + 1) / p) h|
            + |(1 / (p : ℝ)) * shiftCorrH x ω ((r + j + 1) / p) h
                - (1 / (p : ℝ)) * shiftCorrH x ω 0 h|) := by
        have h1 := abs_sub_le A ((1 / (p : ℝ)) * IMG) ((1 / (p : ℝ)) * shiftCorrH x ω 0 h)
        have h2 := abs_sub_le ((1 / (p : ℝ)) * IMG)
          ((1 / (p : ℝ)) * shiftCorrH x ω ((r + j + 1) / p) h) ((1 / (p : ℝ)) * shiftCorrH x ω 0 h)
        linarith
    _ ≤ 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z
          + ((1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z)
            + (1 / (p : ℝ)) * (((r + j + 1) / p : ℕ) * S)) := by
        linarith [hcol, hBC, hCD]
    _ ≤ (2 * Real.log p + 8) / ((p : ℝ) * Z)
          + ((1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2) * S := by
        rw [hsplit, hb1b]
        linarith [hb1a, hbound2]

private theorem IF_unfold_h (h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ} :
    (∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ)
            else 0) ∂(logMeasure x ω) := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  rw [integral_logMeasure_eq]
  simp_rw [fBridgeF_h_liouville_apply h eps H, integral_logMeasure_eq]
  have hR : ∑ n ∈ Finset.Ioc (x / ω) x,
        (∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0)) * (n : ℝ)⁻¹
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H, ∑ n ∈ Finset.Ioc (x / ω) x,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0) * (n : ℝ)⁻¹ := by
    have step1 : ∀ n : ℕ,
        (∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0)) * (n : ℝ)⁻¹
        = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0) * (n : ℝ)⁻¹ := by
      intro n
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_mul _ _ _)
    rw [Finset.sum_congr rfl (fun n _ => step1 n), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]

private theorem per_term_h (h : ℕ) (hh : 0 < h) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hxωH : H ≤ x / ω) (p : ℕ) (hp : p ∈ primeWindow eps H) (j : ℕ) (hj : j < H) :
    |(∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0) ∂(logMeasure x ω))
      - (1 / ((p : ℕ) : ℝ)) * (∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω))|
      ≤ ((2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
          + (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
              * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
        + (if H ≤ j + (p : ℕ) * h then (1 / ((p : ℕ) : ℝ)) * |∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| else 0) := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  set X : ℝ := ∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω) with hXdef
  have hp2 : 2 ≤ (p : ℕ) := (prime_of_mem_primeWindow hp).two_le
  have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (p : ℕ))
  have hlogp : (0 : ℝ) ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega))
  have hZpos : 0 < Z := window_Z_pos hx hω
  have hBp_nonneg : (0 : ℝ) ≤ (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ) * Z)
      + (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2) * (3 * (ω : ℝ) / (x : ℝ) / Z) := by
    apply add_nonneg
    · exact div_nonneg (by linarith [hlogp]) (by positivity)
    · exact mul_nonneg (by positivity) (by positivity)
  by_cases hbd : H ≤ j + (p : ℕ) * h
  · rw [if_pos hbd]
    have hwv0 : ∀ n : ℕ, (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) = 0 :=
        fun n => by
      simp only [windowVal, dif_neg (Nat.not_lt.mpr hbd), Int.cast_zero]
    have hT0 : (∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0)
        ∂(logMeasure x ω)) = 0 := by
      rw [show (fun n => if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0)
          = (fun _ => (0 : ℝ)) from funext (fun n => by rw [hwv0 n, mul_zero, ite_self]),
          integral_zero]
    have hp_inv : (0 : ℝ) ≤ 1 / ((p : ℕ) : ℝ) := by positivity
    rw [hT0, zero_sub, abs_neg, abs_mul, abs_of_nonneg hp_inv]
    linarith [hBp_nonneg]
  · rw [if_neg hbd, add_zero]
    rw [not_le] at hbd
    obtain ⟨r, hrp, hdvd, hgate⟩ := gate_residue (p : ℕ) j hp2
    have hT_eq : (∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0) ∂(logMeasure x ω))
        = (∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % (p : ℕ) = r),
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (ArithmeticFunction.liouville (n + j + (p : ℕ) * h + 1) : ℝ) / (n : ℝ)) / Z := by
      rw [show (fun n => if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0)
          = (fun n => if n % (p : ℕ) = r then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (ArithmeticFunction.liouville (n + j + (p : ℕ) * h + 1) : ℝ) else 0)
          from funext (fun n => by
            rw [windowVal_liouvilleWindow H n (j + (p : ℕ) * h) hbd,
                show n + (j + (p : ℕ) * h) + 1 = n + j + (p : ℕ) * h + 1 from by ring]
            simp only [hgate n])]
      rw [integral_logMeasure_eq, div_eq_mul_inv, mul_comm]
      congr 1
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun n _ => by rw [ite_mul, zero_mul, div_eq_mul_inv])
    rw [hT_eq, hXdef, ← shiftCorrH_zero x ω h]
    -- `p ≤ p·h` needs `0 < h`: at `h = 0` the shifted boundary gate `j + p·h < H` no longer
    -- bounds `p`, and `hrx : r ≤ x/ω` fails.  This is where the port acquires `hh`.
    have hpmul : (p : ℕ) ≤ (p : ℕ) * h := by
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hlt : (p : ℕ) * h < H := Nat.lt_of_le_of_lt (Nat.le_add_left _ j) hbd
    have hpH : (p : ℕ) ≤ H := le_of_lt (Nat.lt_of_le_of_lt hpmul hlt)
    exact perPair_bound_h H h hx hω hωx (p : ℕ) j r hp2 hrp hdvd
      (le_trans hrp.le (le_trans hpH hxωH))
      (by omega) (by omega)


set_option maxHeartbeats 1600000 in
-- As at `h = 1`: the budget aggregation is a single large elaboration.
/-- **HBUDGET AT SHIFT `h` (`hbudget_holds_h`).**  The error budget
`|∫F_h − ∑_p (H/p)·X_h| ≤ (1/4)·SP·H·ε` at the adopted regime, with
`X_h = ∫ λ(n)λ(n+h)` the gap-`h` correlation and `∫F_h` the `fBridgeF_h` integral.

⭐ **WHERE THE SHIFT IS PAID — ONE SLICE OF THREE, AND THE GATE IS LINEAR IN `ε·h`.**
The `1/8 + 1/16 + 1/16 = 1/4` decomposition is UNCHANGED and carries no new term (there is
no slack in that sum, so a new term would have been a design act, not a port):

* total 1 (collapse + swap, `1/8`) — `h`-FREE.  `perPair_collapse_h`'s defect comes from
  `dilation_error_div`, generic in `f`; `dilated_window_stability` is generic in `g`.
* total 2 (shift, `1/16`) — `h`-FREE.  `corr_shift_le` already takes two independent
  offsets, so its `3ω/x/Z` does not see the gap; only the BASE offset `k` multiplies it,
  and `k = (r+j+1)/p` is `h`-free.
* total 3 (boundary, `1/16`) — **THIS is the whole cost.**  The boundary set is
  `{j < H : H ≤ j + p·h}`, so `boundary_card_le H (p·h)` gives `card ≤ p·h` and the slice
  gains EXACTLY ONE factor `h`.  Chasing it through the same `card ≤ 2·log4·ε²H/log H` and
  `SP ≥ c/log H` turns the landed gate `ε ≤ c/(32·log 4)` into

      hεh :  ε·h ≤ c/(32·log 4)      — LINEAR in `ε·h`, NOT `ε²·h`.

`0 < h` is required (see `per_term_h`).  The rider `epsh_gate_implies_epssq_h` (above) is
what converts this gate into K1's `ε²·h < 1` given a ceiling on `c`; the seam is
`hbudget_h_gate_implies_epssq_h` below. -/
theorem hbudget_holds_h :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (h : ℕ) (eps : ℚ) (H x ω : ℕ),
      0 < h → 2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) * (h : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
  obtain ⟨c, hc, H₀, hD3⟩ := primeWindow_sum_inv_ge
  refine ⟨c, hc, H₀, ?_⟩
  intro h eps H x ω hh hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
  -- abbreviations kept raw (they interface with the window lemmas via linarith)
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := window_Z_pos hx hω
  have hZlb : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    (harmonic_window_bounds hx hω hωx).1
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hε2H0 : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by linarith
  have hSP_lb : c / Real.log H ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    hD3 eps H hH0 hsqrt hepssq
  have hSPpos : (0 : ℝ) < ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    lt_of_lt_of_le (by positivity) hSP_lb
  have habsX : |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| ≤ 1 := absXh_le_one h hx hω
  have hcard : ((primeWindow eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime eps H hsqrt hH3
  have hxωH : H ≤ x / ω := by
    have hpos : (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) := by positivity
    have h2 : ω * H ≤ x := by
      have : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ω), Nat.mul_comm]; exact h2
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast (by omega : 0 < ω)
  have hε_le1 : (eps : ℝ) ≤ 1 := by nlinarith [hepssq, hepsR]
  have hlogε2H : (0 : ℝ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hple : ∀ p ∈ primeWindow eps H, (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    intro p hp
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hZbig' : 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64
      ≤ (eps : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    have h2 : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hepsR.le
    have hlhs : (eps : ℝ) * ((16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ))
        = 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 := by field_simp
    rw [hlhs] at h3; exact h3
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    nlinarith [hZbig', hlogε2H, hε_le1, hZpos, mul_le_mul_of_nonneg_right hε_le1 hZpos.le]
  -- === total 1: the Z-controlled (collapse+swap) slice ≤ (1/8)·SP·H·ε ===
  have hZεbound : (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
      / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) ≤ (eps : ℝ) / 8 := by
    rw [div_le_div_iff₀ hZpos (by norm_num)]
    nlinarith [hZbig']
  have hT1 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
        * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have hstep : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      have hle : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          ≤ ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < (p : ℕ))
        have hlogle : Real.log (p : ℕ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) :=
          Real.log_le_log hpR (hple p hp)
        gcongr
      have heq : ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (((p : ℕ) : ℝ) * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          = (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [div_mul_eq_mul_div, mul_one_div, div_div]
      linarith [hle, heq.le, heq.ge]
    calc (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (H : ℝ) * ((2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hHR.le
      _ ≤ (H : ℝ) * ((eps : ℝ) / 8 * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hHR.le
          exact mul_le_mul_of_nonneg_right hZεbound hSPpos.le
      _ = (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by ring
  -- === total 2: the shift slice ≤ (1/16)·SP·H·ε ===
  have key2 : ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      = ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
  have hHsq : (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2)
      ≤ (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left (window_sum_inv_sq eps H) hHR.le
    have h2 : (H : ℝ) * ((2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        = (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hSpos2 : (0 : ℝ) ≤ 3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    positivity
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hle : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by
      nlinarith [hxbig, (show (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        by positivity)]
    nlinarith [hle, mul_pos hωR hHR]
  have hxbound : 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (eps : ℝ) / (16 * (1 + 2 / (eps : ℝ) ^ 2)) := by
    have hxZ : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
      have hx1 : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := by
        nlinarith [hxbig, (show (0 : ℝ) ≤ (ω : ℝ) * (H : ℝ) by positivity)]
      calc 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := hx1
        _ = (x : ℝ) * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hZ1 hxpos.le
    rw [div_le_iff₀ hepsR] at hxZ
    rw [div_div, div_le_div_iff₀ (mul_pos hxpos hZpos) (by positivity)]
    nlinarith [hxZ]
  have hT2 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    rw [key2]
    have hfac : ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ ((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hHsq]) hSpos2
    have hmul : (H : ℝ) * (((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
      have hCbound := hxbound
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (1 + 2 / (eps : ℝ) ^ 2))] at hCbound
      nlinarith [mul_le_mul_of_nonneg_left hCbound
        (mul_nonneg (mul_nonneg hHR.le hSPpos.le) (by norm_num : (0:ℝ) ≤ (1:ℝ)/16))]
    exact le_trans (mul_le_mul_of_nonneg_left hfac hHR.le) hmul
  -- === total 3: the boundary slice ≤ (1/16)·SP·H·ε ===
  have hT3 : ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have hhR : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    -- THE GATE IS LINEAR IN `ε·h`, NOT `ε²·h`: the boundary count gains exactly one factor
    -- `h` (`boundary_card_le H (p·h)`), and it multiplies the SAME `ε²H/log H` card bound.
    have h32 : (eps : ℝ) * (h : ℝ) * (32 * Real.log 4) ≤ c :=
      (le_div_iff₀ (by positivity)).mp heps_small
    have hkey3' : 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) * (h : ℝ)
        ≤ (1 / 16) * c * (H : ℝ) * (eps : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right h32
        (by positivity : (0 : ℝ) ≤ (eps : ℝ) * (H : ℝ) / 16)]
    calc ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
        ≤ ((primeWindow eps H).card : ℝ) * ((h : ℝ) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habsX hhR) (Nat.cast_nonneg _)
      _ = ((primeWindow eps H).card : ℝ) * (h : ℝ) := by rw [mul_one]
      _ ≤ ((2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) * (h : ℝ) :=
          mul_le_mul_of_nonneg_right hcard hhR
      _ = (2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) * (h : ℝ)) / Real.log H := by ring
      _ ≤ ((1 / 16) * c * (H : ℝ) * (eps : ℝ)) / Real.log H := by
          gcongr
      _ = (1 / 16) * (c / Real.log H) * (H : ℝ) * (eps : ℝ) := by ring
      _ ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSP_lb (by norm_num)) hHR.le) hepsR.le
  -- === the reduction: |IF − MAIN| ≤ H·ΣB + card·|X| ≤ T1 + T2 + T3 ===
  have hIF : (∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
        ∂(logMeasure x ω))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ)
            else 0) ∂(logMeasure x ω) := by
    rw [IF_unfold_h h eps H]
    exact Finset.sum_coe_sort (primeWindow eps H)
      (fun p => ∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod p) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + p * h) : ℝ) else 0) ∂(logMeasure x ω))
  have hMAIN : (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
          (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hIF, hMAIN, ← Finset.sum_sub_distrib]
  have hcombine : ∀ p ∈ primeWindow eps H,
      (∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0) ∂(logMeasure x ω))
        - ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω))
      = ∑ j ∈ Finset.range H,
          ((∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
              (ArithmeticFunction.liouville (n + j + 1) : ℝ)
                * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) else 0)
            ∂(logMeasure x ω))
            - (1 / (p : ℝ)) * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω))) :=
    fun p _ => by rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hcombine]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun j hj =>
    per_term_h h hh eps H hx hω hωx hxωH p hp j (Finset.mem_range.mp hj)))).trans ?_
  -- split the inner sum (per-pair bound j-independent; boundary term counted separately)
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hbnd_total : ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
      (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| else 0)
      ≤ ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
          (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|) := by
    have hbnd : ∀ p ∈ primeWindow eps H, (∑ j ∈ Finset.range H,
        (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| else 0))
        ≤ (h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < p)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      -- `boundary_card_le` is ALREADY `h`-general: it is stated at an arbitrary second
      -- argument, so `boundary_card_le H (p * h)` IS the shifted boundary count.  No port.
      have hcardp : (((Finset.range H).filter (fun j => H ≤ j + p * h)).card : ℝ)
          ≤ (p : ℝ) * (h : ℝ) := by
        have hnat := boundary_card_le H (p * h)
        have hR : ((((Finset.range H).filter (fun j => H ≤ j + p * h)).card : ℕ) : ℝ)
            ≤ ((p * h : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast at hR
        exact hR
      calc (((Finset.range H).filter (fun j => H ≤ j + p * h)).card : ℝ)
              * ((1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
          ≤ ((p : ℝ) * (h : ℝ))
              * ((1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                  * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|) :=
            mul_le_mul_of_nonneg_right hcardp (by positivity)
        _ = (h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| := by
            rw [show ((p : ℝ) * (h : ℝ))
                    * ((1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                        * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
                  = ((p : ℝ) * (1 / (p : ℝ)))
                    * ((h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
                        * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|)
                from by ring, mul_one_div, div_self hpR.ne', one_mul]
    calc ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| else 0)
        ≤ ∑ p ∈ primeWindow eps H, (h : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| :=
          Finset.sum_le_sum hbnd
      _ = ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hT1, hT2, hT3, hbnd_total]
/-- **Seam kill-check: the `c`-ceiling rider consumes `hbudget_holds_h`'s OWN gate binder.**
`hgate` below is BYTE-IDENTICAL to `hbudget_holds_h`'s `(eps : ℝ) * (h : ℝ) ≤ c / (32 * Real.log 4)`
binder, and the conclusion is K1's `ε²·h < 1`.  Elaboration is the proof that the rider
landed ahead of B-5 (`epsh_gate_implies_epssq_h`) applies to the gate the tree ACTUALLY
enforces at shift `h`, rather than to a paraphrase of it — the rider is used, not re-derived. -/
theorem hbudget_h_gate_implies_epssq_h (h : ℕ) (eps : ℚ) {c : ℝ}
    (heps0 : 0 < (eps : ℝ)) (heps1 : (eps : ℝ) ≤ 1 / 2) (hc1 : c ≤ 1)
    (hgate : (eps : ℝ) * (h : ℝ) ≤ c / (32 * Real.log 4)) :
    (eps : ℝ) ^ 2 * (h : ℝ) < 1 :=
  epsh_gate_implies_epssq_h heps0 heps1 hc1 hgate

/-- **C1 — the `h = 1` compat for the budget: the `h`-family RE-PROVES the landed node.**
The statement is `hbudget_holds`'s, character for character; the proof instantiates
`hbudget_holds_h` at `h := 1`.  This is the strongest available kill-check that the port did
not weaken anything: if any hypothesis of the `h`-family were stronger than the landed one at
`h = 1`, this would not elaborate.

TWO COMPAT REWRITE SITES, TWO DIFFERENT TACTICS — measured, not assumed:
* the GATE `ε·(1:ℕ) ≤ c/(32 log 4)` vs `ε ≤ c/(32 log 4)`: `push_cast` (for `Nat.cast_one`)
  then `linarith` (for `ε * 1 = ε`).  A bare `exact heps_small` FAILS — the cast is real.
* the BRIDGE `fBridgeF_h eps H 1` vs `fBridgeF`: `simp only [fBridgeF_h_one]`.  Plain
  `rw [fBridgeF_h_one]` FAILS here — every occurrence sits under the integral binder
  `∫ n, …`, which `rw` cannot enter.  (Same shape B-4 measured on `outer_badMass_h_eq`.) -/
theorem hbudget_holds_h_one :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
  obtain ⟨c, hc, H₀, hbud⟩ := hbudget_holds_h
  refine ⟨c, hc, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
  have hone := hbud 1 eps H x ω (by norm_num) hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0
    (by push_cast; linarith) hωbig hxbig
  simpa only [fBridgeF_h_one] using hone

/-- **The capstone at shift `h`.**  Composing `hbudget_holds_h` through `hreduce_holds_h`:
at the adopted regime WITH the `ε·h` gate, the gap-`h` seed `hseed : ε/2 ≤ |X_h|` forces the
shift-`h` frozen `hreduce` conclusion `(1/2)·SP·H·|X_h| ≤ |∫F_h|`.  This is the consumable
`h`-family form of `hreduce_holds_final`. -/
theorem hreduce_holds_final_h :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (h : ℕ) (eps : ℚ) (H x ω : ℕ),
      0 < h → 2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) * (h : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  obtain ⟨c, hc, H₀, hbud⟩ := hbudget_holds_h
  refine ⟨c, hc, H₀, ?_⟩
  intro h eps H x ω hh hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
    hseed
  exact hreduce_holds_h h eps H hseed
    (hbud h eps H x ω hh hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig)

-- **B-5 axiom audit, file-private arm.**  The ten other new `private` declarations
-- (`shiftCorrH`, `shiftCorrH_le`, `shiftCorrH_zero`, `absXh_le_one`, `liouville_sq_h`,
-- `collapse_identity_h`, `perPair_collapse_h`, `perPair_bound_h`, `IF_unfold_h`,
-- `per_term_h`) are all CONSUMED by `hbudget_holds_h`, so `Salt/Entropy/All.lean`'s
-- `#audit_axioms` on that name covers them transitively.  `shiftCorrH_one` is a standalone
-- compat that nothing consumes — a name-based audit outside this file cannot see it at all
-- (it is private), so it is audited HERE, where it is nameable.
#print axioms shiftCorrH_one

end Salt.Entropy.Chowla
