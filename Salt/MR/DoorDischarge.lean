/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.Regime

/-!
# MR-gate wave 1, stone S10a — the W-headroom door discharge

`regime_W_headroom_of_floor` : the `(log X)^{1/125}` arm of Tao arXiv:1509.05422v2
Prop 2.4's W-constraint `W = log⁵ H ≪ min(A, (log X)^{1/125})`, landable now
from the EXISTING regime field `hPHheadroom` (`Regime.lean:116`).

Rung card (MR freeze, S10a): `hPHheadroom` ⇒ `log X_min ≥ 4·log2·ε²·H₊ − 2·log2`
`≥ (log H₊)^625` once `H₊ ≥ T(ε)`, where `T(ε)` is the threshold
`625·loglog h + log(1/(4·log2·ε²)) + 3 ≤ log h` (the `+3` is the slack repair).

Since `W = (log H₊)^5`, the bound `(log H₊)^625 = W^125 ≤ log X_min` is exactly
`W ≤ (log X_min)^{1/125}`, the smallest dyadic `X_min = x/(2ω)` being the worst
case (`log` monotone covers every `X ∈ [x/2ω, 2x]`).

Arithmetic trace (all constants exact):
* `hPHheadroom`: `8·(4^m)²·ω ≤ x`, `m = ⌊ε²H₊⌋₊`.
* ⇒ `log(x/2ω) ≥ log8 + 2·log(4^m) − log2 = (4m+2)·log2` (the `ω` cancels).
* `m ≥ ε²H₊ − 1` ⇒ `(4m+2)·log2 ≥ 4·log2·ε²·H₊ − 2·log2`.
* threshold ⇒ `exp(log H₊) = H₊ ≥ e³·(log H₊)^625 / (4·log2·ε²)`,
  i.e. `4·log2·ε²·H₊ ≥ e³·(log H₊)^625`.
* `(e³ − 1)·(log H₊)^625 ≥ 2·log2` (since `log H₊ ≥ 1`, `e³ − 1 ≥ 3 ≥ 2·log2`),
  closing `4·log2·ε²·H₊ − 2·log2 ≥ (log H₊)^625`.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **S10a — the W-headroom door discharge (the `(log X)^{1/125}` arm).**
From the regime field `hPHheadroom` alone, once the upper endpoint `H₊` clears
the threshold `T(ε)` (stated as `hthr`), the smallest dyadic scale `X_min = x/(2ω)`
satisfies `(log H₊)^625 ≤ log X_min`.  Equivalently `W = (log H₊)^5 ≤ (log X_min)^{1/125}`,
Tao's W-constraint. -/
theorem regime_W_headroom_of_floor (R : ChowlaRegime)
    (hthr : 625 * Real.log (Real.log (R.Hhi : ℝ))
        + Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
        ≤ Real.log (R.Hhi : ℝ)) :
    (Real.log (R.Hhi : ℝ)) ^ (625 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) := by
  -- basic positivity of the scale parameters
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hHhi_ge : (4000000 : ℝ) ≤ (R.Hhi : ℝ) := by
    have : (4000000 : ℕ) ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    exact_mod_cast this
  have hHhi_pos : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hωpos : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℕ) ≤ R.ω := R.hω
    have : (0 : ℕ) < R.ω := by omega
    exact_mod_cast this
  have hepspos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepssq : (0 : ℝ) < (R.eps : ℝ) ^ 2 := by positivity
  set A : ℝ := 4 * Real.log 2 * (R.eps : ℝ) ^ 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set L : ℝ := Real.log (R.Hhi : ℝ) with hLdef
  -- `L = log H₊ ≥ 1` (since `H₊ ≥ 4·10⁶ ≥ e`)
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < L := by linarith
  -- STEP 1 : `4·log2·ε²·H₊ ≥ e³·L^625` from the threshold.
  have hstep1 : Real.exp 3 * L ^ (625 : ℕ) ≤ A * (R.Hhi : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hthr
    -- expand the exponential of the sum
    have hlhs : Real.exp (625 * Real.log L
        + Real.log (1 / A) + 3)
        = L ^ (625 : ℕ) * (1 / A) * Real.exp 3 := by
      rw [Real.exp_add, Real.exp_add]
      congr 1
      · congr 1
        · rw [show (625 : ℝ) * Real.log L = ((625 : ℕ) : ℝ) * Real.log L by norm_num,
            Real.exp_nat_mul, Real.exp_log hLpos]
        · rw [Real.exp_log (by positivity)]
    have hrhs : Real.exp L = (R.Hhi : ℝ) := by rw [hLdef, Real.exp_log hHhi_pos]
    rw [hlhs, hrhs] at hexp
    -- `L^625·(1/A)·e³ ≤ H₊` ⇒ `e³·L^625 ≤ A·H₊` (multiply through by `A > 0`)
    have hAne : A ≠ 0 := ne_of_gt hApos
    have hmul := mul_le_mul_of_nonneg_left hexp hApos.le
    have hrw : A * (L ^ (625 : ℕ) * (1 / A) * Real.exp 3) = Real.exp 3 * L ^ (625 : ℕ) := by
      field_simp
    rw [hrw] at hmul
    exact hmul
  -- STEP 2 : `(e³ − 1)·L^625 ≥ 2·log2`, closing `A·H₊ − 2·log2 ≥ L^625`.
  have hLpow1 : (1 : ℝ) ≤ L ^ (625 : ℕ) := one_le_pow₀ hL1
  have hexp3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have hlog2lt1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hstep2 : L ^ (625 : ℕ) ≤ A * (R.Hhi : ℝ) - 2 * Real.log 2 := by
    have : Real.exp 3 * L ^ (625 : ℕ) - 2 * Real.log 2 ≥ L ^ (625 : ℕ) := by
      nlinarith [hLpow1, hexp3, hlog2lt1]
    linarith [hstep1, this]
  -- STEP 3 : `log(x/2ω) ≥ A·H₊ − 2·log2` from `hPHheadroom`.
  set m : ℕ := ⌊(R.eps : ℚ) ^ 2 * (R.Hhi : ℚ)⌋₊ with hmdef
  have hm_ge : (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) - 1 ≤ (m : ℝ) := by
    have hlt : ((R.eps : ℚ) ^ 2 * (R.Hhi : ℚ)) < (m : ℚ) + 1 := by
      rw [hmdef]; exact Nat.lt_floor_add_one _
    have : ((R.eps : ℚ) ^ 2 * (R.Hhi : ℚ) : ℝ) < (m : ℝ) + 1 := by exact_mod_cast hlt
    push_cast at this
    linarith
  -- the field, rewritten with `4^m` cast to ℝ
  set M4 : ℝ := ((4 ^ m : ℕ) : ℝ) with hM4def
  have hM4eq : M4 = (4 : ℝ) ^ m := by rw [hM4def]; push_cast; ring
  have hM4pos : 0 < M4 := by rw [hM4eq]; positivity
  have hfield : 8 * M4 ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := R.hPHheadroom
  have hxpos : 0 < (R.x : ℝ) := lt_of_lt_of_le (by positivity) hfield
  -- `log(x/2ω) = log x − log2 − log ω`
  have h2ωpos : (0 : ℝ) < 2 * (R.ω : ℝ) := by positivity
  have hlogdiv : Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ)))
      = Real.log (R.x : ℝ) - Real.log 2 - Real.log (R.ω : ℝ) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt h2ωpos),
        Real.log_mul (by norm_num) (ne_of_gt hωpos)]
    ring
  -- `log x ≥ log8 + 2m·log2 + log ω`
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlogM4 : Real.log M4 = (m : ℝ) * (2 * Real.log 2) := by
    rw [hM4eq, Real.log_pow, hlog4]
  have hlogfield : Real.log (8 * M4 ^ 2 * (R.ω : ℝ))
      = 3 * Real.log 2 + 4 * (m : ℝ) * Real.log 2 + Real.log (R.ω : ℝ) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hωpos),
        Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, hlog8, hlogM4]
    push_cast; ring
  have hlogx : 3 * Real.log 2 + 4 * (m : ℝ) * Real.log 2 + Real.log (R.ω : ℝ)
      ≤ Real.log (R.x : ℝ) := by
    rw [← hlogfield]
    exact Real.log_le_log (by positivity) hfield
  -- assemble : `log(x/2ω) ≥ (4m+2)·log2 ≥ A·H₊ − 2·log2`
  have hchain : A * (R.Hhi : ℝ) - 2 * Real.log 2
      ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) := by
    rw [hlogdiv]
    have h1 : A * (R.Hhi : ℝ) - 2 * Real.log 2 ≤ (4 * (m : ℝ) + 2) * Real.log 2 := by
      rw [hAdef]
      nlinarith [hm_ge, hlog2pos, hepssq, hHhi_pos]
    nlinarith [h1, hlogx, hlog2pos]
  linarith [hstep2, hchain]

/-! ## S10b — the OTHER arm of the same `W`-constraint, `W ≤ H^{1/250}` -/

/-- **S10b — the `H`-relative arm of Prop 2.4's `W`-constraint** (`regime_W_cap_of_floor`).

Tao arXiv:1509.05422v2 Prop 2.4 constrains `W = log⁵ H ≪ min(A, (log X)^{1/125})`.  S10a above
discharges the `(log X)^{1/125}` arm.  This is the OTHER one, `W ≤ H^{1/250}`, stated the way the
corpus states the first: **expanded, with no `W` and no `rpow`.**  Raising both sides to the 250th
power turns `W ≤ H^{1/250}` into

    `(log H)^{1250} ≤ H` ,

an inequality in `H` ALONE — no `ε` anywhere — which is why the scoping brief calls it *"an ε-free
`H₋` floor"*.

📐 **WHY THIS ARM READS `H₋` WHERE S10a READS `H₊`, AND IT IS NOT AN INCONSISTENCY.**  `W` is
increasing in `H`, so each arm is worst at the end that makes it hardest.  S10a compares `W` against
an `H`-independent quantity (`log X_min`), so its worst case is the LARGEST `H` — `R.Hhi`.  Here
both sides grow with `H` and the right side eventually wins, so the constraint is a FLOOR and its
worst case is the SMALLEST `H` — `R.Hlo`.  *Same constraint, opposite endpoints, for the same
reason.*

`hthr` is taken as a hypothesis, exactly as S10a takes its own and for the same reason: the numeral
belongs to whoever builds the regime, not to the arm.

⚠️⚠️ **AND THE NUMERAL IS NOT THE ONE THE BRIEF QUOTES — MEASURED, BECAUSE A ROUNDED THRESHOLD IS
ROUNDED IN AN UNKNOWN DIRECTION.**  `hthr` is `1250·loglog H ≤ log H`; with `L = log H` that is
`1250·log L ≤ L`, whose upper root is

    `L* = 11710.2777…`

The scoping brief (`2026-08-21-mrt-port-scoping-BRIEF-v2.md:117`) records the floor as
`log H ≳ 1.17e4`.  **`1.17e4 = 11700` lies BELOW that root: there `L − 1250·log L = −9.18` and the
inequality FAILS.**  The first integer that works is **`log H ≥ 11711`** (margin `+0.65`).  The
brief's `≳` is honest to two significant figures; a reader who instantiates AT the quoted figure is
not.  ⇒ ***A THRESHOLD QUOTED TO TWO FIGURES IS A THRESHOLD WHOSE DIRECTION YOU HAVE NOT BEEN
TOLD — re-solve it before you instantiate it.***

📌 The regime clears this with room that is not close: `log H₊ ≳ 10⁵⁹` is already measured
(v2 §3c) against a demand of ~1.2 × 10⁴. **The floor is cheap; the point of landing it is that it
was missing from every regime field, not that it is tight.** -/
theorem regime_W_cap_of_floor (R : ChowlaRegime)
    (hthr : 1250 * Real.log (Real.log (R.Hlo : ℝ)) ≤ Real.log (R.Hlo : ℝ)) :
    (Real.log (R.Hlo : ℝ)) ^ (1250 : ℕ) ≤ (R.Hlo : ℝ) := by
  have hHlo_ge : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHpos : (0 : ℝ) < (R.Hlo : ℝ) := by linarith
  -- `L = log H₋ ≥ 1` (since `H₋ ≥ 4·10⁶ ≥ e`), exactly as S10a establishes its own `L ≥ 1`
  have hL1 : (1 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : (0 : ℝ) < Real.log (R.Hlo : ℝ) := by linarith
  have hpow_pos : (0 : ℝ) < Real.log (R.Hlo : ℝ) ^ (1250 : ℕ) := by positivity
  -- the whole content is one `log_pow`: the threshold IS the logged form of the conclusion
  have hkey : Real.log (Real.log (R.Hlo : ℝ) ^ (1250 : ℕ)) ≤ Real.log ((R.Hlo : ℝ)) := by
    rw [Real.log_pow]
    push_cast
    exact hthr
  exact (Real.log_le_log_iff hpow_pos hHpos).mp hkey

end Salt.MR
