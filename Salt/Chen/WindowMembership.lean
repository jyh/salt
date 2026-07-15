/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.StepBound2

/-!
# M4F — the operating-point window memberships (the H-glue's rounding lemmas)

The two deferred halves of the M-recon node M4, restated at the now-frozen shapes
(`docs/blueprints/chen.md`: the `C0 AMENDMENT 4`/catch-#51 arc; `docs/blueprints/flags.md`:
the `2026-07-13 M134` and `2026-07-14 FPC` entries).  Both are the same floor-bracketing
computation on `logRatio z D = log D / log z` at rpow operating points.

## Convention (documented; the H-glue instantiates `z / y / Dlev` from these)

Both targets use the **`Nat.floor`-of-`Real.rpow`** shape — for `x : ℕ`,
`z, D, y, Dlev := ⌊(x : ℝ) ^ γ⌋₊` with the `HPow ℝ ℝ ℝ` instance (`Real.rpow`), matching the
`z = x^{1/8}`, `D = x^{1/2−ε′}`, `y = x^{1/3}`, `Dlev = x^{1/2}` design.  The argument order of
`logRatio z D = log D / log z` puts the **cutoff** first (denominator) and the **level** second
(numerator), exactly as the consumers `SwitchSieve.mainA3_of_hBVswitch` /
`FchainPoint.Fchain_switch_le` (`logRatio y Dlev`) and `TwinA1.twin_A1_lower_B`
(`logRatio z D`) take them.

* **`logRatio_A1_mem`** — the A₁ site at **Amendment 4** (`ε′ = 9/100000`): the un-floored point is
  `(1/2 − ε′)/(1/8) = 4 − 8ε′ = 3.99928`, landing in the frozen `fchain_A1_final` window
  `[39992/10000, 4] = [3.9992, 4]` (margin `8·10⁻⁵` above the left edge, `7.2·10⁻⁴` below `4`).

* **`logRatio_A3_mem`** — the switch window (FPC's consumer): the un-floored point is
  `(1/2)/(1/3) = 3/2 = 1.5`, landing in `[149/100, 151/100]` (margins `0.01` both sides).

Both discharge honestly: the floor `t − 1 < ⌊t⌋ ≤ t` gives, after `log`,
`γ·log x − 1/(x^γ − 1) ≤ log⌊x^γ⌋ ≤ γ·log x`, and the `1/(x^γ − 1)` perturbation — bounded by the
uniform `1/999999` once `x^γ ≥ 10⁶` — is dwarfed by the window margins times `log x` (which grows).
A single threshold `x₁ = 10⁴⁸` (with `48` divisible by `8, 3, 2`) serves both, with wide slack.

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Salt.Chen

/-- **The uniform floor-bracketing bound.**  For `x ≥ 10⁴⁸` and any exponent `γ ≥ 1/8`, the
`Nat.floor` of `(x : ℝ) ^ γ` is at least `10⁶`, and its log is squeezed within `1/999999` of the
un-floored `γ · log x`.  The `10⁶` lower bound comes from `x^γ ≥ x^{1/8} ≥ (10⁴⁸)^{1/8} = 10⁶`;
the log squeeze from `t − 1 < ⌊t⌋ ≤ t` and `Real.log_le_sub_one_of_pos`. -/
private lemma window_floor_bounds (x : ℕ) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) {γ : ℝ}
    (hγ : (1 / 8 : ℝ) ≤ γ) :
    (10 : ℝ) ^ 6 ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ)
      ∧ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ γ * Real.log (x : ℝ)
      ∧ γ * Real.log (x : ℝ) - 1 / 999999 ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
  have hX1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx
  have hXpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  -- `x^γ ≥ 10^6`
  have hpow48 : ((10 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 8) = (10 : ℝ) ^ 6 := by
    have h6 : ((48 : ℕ) : ℝ) * (1 / 8) = ((6 : ℕ) : ℝ) := by norm_num
    rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10), h6,
      Real.rpow_natCast]
  have hstep1 : (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← hpow48]; exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hstep2 : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hX1 hγ
  have hApow : (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ γ := le_trans hstep1 hstep2
  have hA6 : (1000000 : ℝ) ≤ (x : ℝ) ^ γ := le_trans (by norm_num) hApow
  have hXγnn : (0 : ℝ) ≤ (x : ℝ) ^ γ := Real.rpow_nonneg hXpos.le γ
  -- floor brackets
  have hfloor_ge : (10 : ℝ) ^ 6 ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    have h1 : ((1000000 : ℕ) : ℝ) ≤ (x : ℝ) ^ γ := by
      rw [show ((1000000 : ℕ) : ℝ) = (10 : ℝ) ^ 6 by norm_num]; exact hApow
    have h2 : (1000000 : ℕ) ≤ ⌊(x : ℝ) ^ γ⌋₊ := Nat.le_floor h1
    calc (10 : ℝ) ^ 6 = ((1000000 : ℕ) : ℝ) := by norm_num
      _ ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by exact_mod_cast h2
  have hfloor_le : (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ (x : ℝ) ^ γ := Nat.floor_le hXγnn
  have hfloor_gt : (x : ℝ) ^ γ - 1 < (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one ((x : ℝ) ^ γ)]
  have hzfpos : (0 : ℝ) < (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := lt_of_lt_of_le (by norm_num) hfloor_ge
  have hXγ1pos : (0 : ℝ) < (x : ℝ) ^ γ - 1 := by linarith [hA6]
  -- the un-floored log value
  have hlogXγ : Real.log ((x : ℝ) ^ γ) = γ * Real.log (x : ℝ) := Real.log_rpow hXpos γ
  -- upper: `log⌊x^γ⌋ ≤ log(x^γ) = γ·log x`
  have hlog_le : Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ γ * Real.log (x : ℝ) := by
    rw [← hlogXγ]; exact Real.log_le_log hzfpos hfloor_le
  -- lower: `log⌊x^γ⌋ ≥ log(x^γ − 1) ≥ γ·log x − 1/(x^γ−1) ≥ γ·log x − 1/999999`
  have hratio : (x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1) ≤ 1000000 / 999999 := by
    rw [div_le_div_iff₀ hXγ1pos (by norm_num : (0 : ℝ) < 999999)]
    nlinarith [hA6]
  have hcorr : Real.log ((x : ℝ) ^ γ) - Real.log ((x : ℝ) ^ γ - 1) ≤ 1 / 999999 := by
    have h1 : Real.log ((x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1)) ≤ (x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (ne_of_gt hXγ1pos)] at h1
    linarith [h1, hratio]
  have hlog_ge : γ * Real.log (x : ℝ) - 1 / 999999 ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    have hlog_floor_ge : Real.log ((x : ℝ) ^ γ - 1) ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) :=
      Real.log_le_log hXγ1pos (le_of_lt hfloor_gt)
    rw [hlogXγ] at hcorr
    linarith [hlog_floor_ge, hcorr]
  exact ⟨hfloor_ge, hlog_le, hlog_ge⟩

/-- `log 10 ≥ 2`, hence `log(x) ≥ 96` for `x ≥ 10⁴⁸`. -/
private lemma log_ge_96 (x : ℕ) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) : (96 : ℝ) ≤ Real.log (x : ℝ) := by
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hmono : Real.log ((10 : ℝ) ^ 48) ≤ Real.log (x : ℝ) := Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at hmono
  push_cast at hmono
  linarith [hmono, hlog10]

/-- **M4a at Amendment 4 (`ε′ = 9/100000`).**  The A₁ operating point
`s = log⌊x^{1/2−ε′}⌋ / log⌊x^{1/8}⌋` lands in the frozen `fchain_A1_final` window
`[39992/10000, 4]` for all large `x`.  Un-floored value `4 − 8ε′ = 3.99928`; threshold `10⁴⁸`. -/
theorem logRatio_A1_mem :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
      logRatio ⌊(x : ℝ) ^ (1 / 8 : ℝ)⌋₊ ⌊(x : ℝ) ^ (1 / 2 - 9 / 100000 : ℝ)⌋₊
        ∈ Set.Icc (39992 / 10000 : ℝ) 4 := by
  refine ⟨10 ^ 48, fun x hx => ?_⟩
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx
  obtain ⟨hz6, hz_le, hz_ge⟩ := window_floor_bounds x hxR (γ := 1 / 8) (by norm_num)
  obtain ⟨_hD6, hD_le, hD_ge⟩ := window_floor_bounds x hxR (γ := 1 / 2 - 9 / 100000) (by norm_num)
  have hL96 := log_ge_96 x hxR
  have hlogz_pos : (0 : ℝ) < Real.log (⌊(x : ℝ) ^ (1 / 8 : ℝ)⌋₊ : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < (10 : ℝ) ^ 6) hz6)
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · rw [logRatio, le_div_iff₀ hlogz_pos]
    linarith [hz_le, hD_ge, hL96]
  · rw [logRatio, div_le_iff₀ hlogz_pos]
    linarith [hD_le, hz_ge, hL96]

/-- **The switch window (FPC's consumer).**  The A₃ operating point
`s = log⌊x^{1/2}⌋ / log⌊x^{1/3}⌋` lands in `[149/100, 151/100]` for all large `x`.  Un-floored
value `(1/2)/(1/3) = 3/2 = 1.5`; threshold `10⁴⁸`.  This is the exact `logRatio y Dlev` shape
`FchainPoint.Fchain_switch_le` / `SwitchSieve.mainA3_of_hBVswitch` consume. -/
theorem logRatio_A3_mem :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
      logRatio ⌊(x : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(x : ℝ) ^ (1 / 2 : ℝ)⌋₊
        ∈ Set.Icc (149 / 100 : ℝ) (151 / 100 : ℝ) := by
  refine ⟨10 ^ 48, fun x hx => ?_⟩
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx
  obtain ⟨hy6, hy_le, hy_ge⟩ := window_floor_bounds x hxR (γ := 1 / 3) (by norm_num)
  obtain ⟨_hD6, hD_le, hD_ge⟩ := window_floor_bounds x hxR (γ := 1 / 2) (by norm_num)
  have hL96 := log_ge_96 x hxR
  have hlogy_pos : (0 : ℝ) < Real.log (⌊(x : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < (10 : ℝ) ^ 6) hy6)
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · rw [logRatio, le_div_iff₀ hlogy_pos]
    linarith [hy_le, hD_ge, hL96]
  · rw [logRatio, div_le_iff₀ hlogy_pos]
    linarith [hD_le, hy_ge, hL96]

end Salt.Chen
