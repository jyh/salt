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

end Salt.Entropy.Chowla
