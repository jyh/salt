/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TauNumeric

/-!
# C1cσ — the decaying per-level constants: the honest finding that the geometric factor
does NOT rescue the numeric τ-row

C1cσ was scoped (`docs/blueprints/chen.md`, the C1cσ row) to **re-run the two comparison
endgames of `SharpStep.hf_of_window` / `DecayMass.hh_of_window` carrying the landed geometric
decay** `fseq_le : fseq (n+1) s ≤ 2·e²·(99/100)ⁿ·hbar s` (Tail.lean), the hope being
`c_f(n), c_h(n) ≤ K·(99/100)ⁿ`-shape so the τ-recursion `τ_{n+1} ≥ c_f/(εe²) + c_h·τ_n`
contracts and `Lemma11.tau_sum_le_of_recursion` closes at an explicit `C₁'/C₂'`.

This file lands the **machine-checked finding that the proposed fix does not achieve
contraction**, for two independent, quantified reasons — the honest Iron-Rule-1 outcome
(precise flag in `docs/blueprints/flags.md`, C1cσ).

## FINDING 1 — the geometric factor touches only the `f`-side; the `h`-side has no `fseq`

The two Stieltjes comparisons `AbelStep.stepHyp_of_comparisons` reduces `StepHyp` to are

  `hf : Σ_p ν(p)·V(p)·fₙ(σ_p) ≤ W·(fₙ₊₁(σ_z) + c_f·h(σ_z))`     (the `f`-part),
  `hh : Σ_p ν(p)·V(p)·h(σ_p)  ≤ W·(c_h·h(σ_z))`                  (the `h`-part).

Only `hf` carries an `fₙ` factor, so only there does the geometric decay
`fseq_le`/`fseq_geom_uniform` apply.  `hh` is a pure `h`-sum with **no `fₙ`** — the geometric
factor is simply *not present* to be carried.  But the τ-recursion's *multiplier* is exactly
`β = c_h` (`AbelStep.ledger_collect`: `c_f + ε·e²·c_h·τₙ ≤ ε·e²·τₙ₊₁`), so it is the `h`-side
that must contract (`c_h < 1`).  The `f`-side geometric decay, real as it is
(`fseq_geom_uniform`), cannot help the multiplier at all.

## FINDING 2 — even applied to *both* sides, `(99/100)ⁿ·c_h ≥ 24`; the recursion still blows up

The landed `h`-coefficient (`DecayMass.ch_const`) is `c_h = (1+ε)·Cabs·(n+3)·e^{n+3}` — the
`e^{n+3}` is the **window-conversion factor** `one_le_window_hBJS`
(`1 ≤ (n+3)·e^{n+3}·h(S)` on the operating window `S ≤ n+3`): the crude `decay_mass_le`
produces an *absolute* mass `Cabs`, and expressing it in `h(S)`-units at the worst operating
point `S = n+3` (where `h(S) = 3(n+3)⁻¹e^{−(n+3)}`) costs `e^{n+3}`.  The geometric decay
`(99/100)ⁿ` does **not** beat it:

  `(99/100)ⁿ·c_h ≥ 3·e³·((99/100)·e)ⁿ ≥ 3·e³ ≥ 24`   (`ch_const_geom_ge`),

because `(99/100)·e ≈ 2.69 > 1` — the exponential `e^{n+3}` dominates the geometric
`(99/100)ⁿ`.  (The same holds against `hbar`: `(99/100)·e^{6/5} ≈ 3.29 > 1`, so *no*
fixed-rate majorant floor for `h` on `[1, n+3]` avoids it.)  Consequently the *optimistically
fully-decayed* recursion `tauDec` — where we grant the geometric factor to **both** `c_f` and
`c_h` — still satisfies `2·τₙ ≤ τₙ₊₁` (`tauDec_double`), hence `3·2^m ≤ τ_{m+1}`
(`tauDec_ge_geom`) and the τ-sum is `≥ 3·2^{2m}` (`tauDecSum_odd_ge`): the achievable `C₁'`
is `≥ 3·2^{~π(z)}`, astronomically large.  **No usable `C₁'/C₂'` exists**, and the bound is
`ε`-uniform, so no ledger re-freeze (the pre-verified `1/100000` row included) rescues it —
exactly `TauNumeric`'s C1cτ Findings 1–2, now made specific to C1cσ's geometric-factor fix.

## The genuine fix (out of this node's scope; C1c⁵ / `StepBound` finding, corroborated)

Contraction (`c_h < 1`) requires the **sharp discrete→integral comparison** (BJS §2.4): the
loglog-density pushforward turning `Σ_p ν(p)V(p)h(σ_p)` into `∫ h`, closed by
`Tail.hbar_funcbound` (ratio `99/100 < 1`) or `StepBound.hBJS_funcbound` (`κ₃ = 1`).  This is
`AbelStep`/`StepBound`'s explicitly-deferred "multi-hundred-line real analysis, its own
session" hypothesis — it is **not** obtainable by re-running the crude `decay_mass_le`
endgame (which is all C1cσ's mandate re-runs).  Moreover, even the sharp *elementary*
funcbound floors at `c_h ≈ (1+ε)·(99/100)·s/(s−1) ≈ 1.98 > 1` (the `s/(s−1)` density factor
at `s = 2`); the genuine `κ₃ ≈ 0.96 < 1` needs the `3u⁻¹e⁻ᵘ`-tail exponential integral `E₁`,
not elementary in mathlib.  So the numeric row genuinely requires the sharp BJS constants,
confirming the C1c⁵ `κ₃ = 1 ⟹ β ≥ 1` finding.

## What is proved here (sorry-free, axiom-clean)

* `fseq_geom_uniform` — the `f`-side geometric decay *is* real: `fₙ(s) ≤ 2·(99/100)ⁿ⁻¹`
  (`1 ≤ n`, all `s`), the `fseq_le_two` bound with the geometric factor retained.
* `one_le_geom_mul_exp` / `geom_mul_exp_pow_ge_one` / `exp_nat_eq` — the arithmetic wall
  `(99/100)·e ≥ 1`.
* `ch_const_ge_exp` / `ch_const_defeats_geom` / `ch_const_geom_ge` — Finding 2's core:
  `(99/100)ⁿ·ch_const n ε ≥ 24` for every `n`, `ε ≥ 0`.
* `tauDec` + `tauDec_double` / `tauDec_ge_geom` / `tauDecSum_odd_ge` — the optimistically
  fully-decayed recursion still blows up (`≥ 3·2^{2m}`), `ε`-uniformly.

`maxHeartbeats`: default (200000); all proofs are elementary `nlinarith`/`calc`/induction.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the `f`-side geometric decay is real (`fseq_geom_uniform`) -/

/-- **The uniform geometric decay of `fₙ`** (`1 ≤ n`, all `s`): `fₙ(s) ≤ 2·(99/100)ⁿ⁻¹`.
This is `SharpStep.fseq_le_two` with the geometric factor **retained** (via `Tail.fseq_le` and
`hbar s ≤ e⁻²`) — the real content of C1cσ's "carry the geometric factor" on the `f`-side.
The `hf`-comparison could be re-derived against this, giving `c_f(n) = (99/100)ⁿ⁻¹·cf_const n ε`;
but that still carries `inv_S_le`'s `(n+3)·e^{n+3}` window-conversion, which the geometric
factor does not beat (Finding 2) — so it does not contract, and is not the node's payoff. -/
theorem fseq_geom_uniform {n : ℕ} (hn : 1 ≤ n) (s : ℝ) :
    fseq n s ≤ 2 * (99 / 100 : ℝ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : fseq (m + 1) s ≤ 2 * Real.exp 2 * (99 / 100) ^ m * hbar s := fseq_le m s
  have h2 : hbar s ≤ Real.exp (-2) := by
    unfold hbar; exact Real.exp_le_exp.mpr (by nlinarith [le_max_right s (2 : ℝ)])
  have hpre : (0 : ℝ) ≤ 2 * Real.exp 2 * (99 / 100 : ℝ) ^ m := by positivity
  have he : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
  calc fseq (m + 1) s ≤ 2 * Real.exp 2 * (99 / 100) ^ m * hbar s := h1
    _ ≤ 2 * Real.exp 2 * (99 / 100) ^ m * Real.exp (-2) :=
        mul_le_mul_of_nonneg_left h2 hpre
    _ = 2 * (99 / 100) ^ m * (Real.exp 2 * Real.exp (-2)) := by ring
    _ = 2 * (99 / 100) ^ m := by rw [he]; ring

/-! ## Part B — the arithmetic wall `(99/100)·e ≥ 1` (the geometric factor loses to `e^{n}`) -/

/-- `1 ≤ (99/100)·e` (`(99/100)·e ≈ 2.69`).  The exponential `e^n` out-grows the geometric
`(99/100)^n`, so the geometric factor cannot cancel the window-conversion `e^{n+3}`. -/
theorem one_le_geom_mul_exp : (1 : ℝ) ≤ (99 / 100) * Real.exp 1 := by
  nlinarith [Real.exp_one_gt_d9]

/-- `1 ≤ ((99/100)·e)ⁿ` for every `n`. -/
theorem geom_mul_exp_pow_ge_one (n : ℕ) : (1 : ℝ) ≤ ((99 / 100) * Real.exp 1) ^ n :=
  one_le_pow₀ one_le_geom_mul_exp

/-- `e^n = (e^1)^n`. -/
theorem exp_nat_eq (n : ℕ) : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
  rw [← Real.exp_nat_mul, mul_one]

/-! ## Part C — the `h`-side obstruction: `(99/100)ⁿ·ch_const ≥ 24` -/

/-- **The `h`-coefficient grows exponentially** (`ε ≥ 0`): `3·e^{n+3} ≤ ch_const n ε`.
`ch_const n ε = (1+ε)·Cabs·(n+3)·e^{n+3}` with `1+ε ≥ 1`, `Cabs ≥ 1` (`TauNumeric.Cabs_ge_one`),
`n+3 ≥ 3`.  The `e^{n+3}` is the mandatory window-conversion factor of `one_le_window_hBJS`. -/
theorem ch_const_ge_exp {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (3 : ℝ) * Real.exp ((n : ℝ) + 3) ≤ ch_const n ε := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hCabs : (1 : ℝ) ≤ Cabs := Cabs_ge_one
  have hexp : (0 : ℝ) < Real.exp ((n : ℝ) + 3) := Real.exp_pos _
  have h3 : (3 : ℝ) ≤ (1 + ε) * Cabs * ((n : ℝ) + 3) := by
    have hA : (1 : ℝ) ≤ (1 + ε) * Cabs := by
      nlinarith [mul_nonneg hε (show (0 : ℝ) ≤ Cabs by linarith), hCabs]
    have hAnn : (0 : ℝ) ≤ (1 + ε) * Cabs := by linarith
    have := mul_le_mul hA (show (3 : ℝ) ≤ (n : ℝ) + 3 by linarith) (by norm_num) hAnn
    linarith [this]
  unfold ch_const
  calc (3 : ℝ) * Real.exp ((n : ℝ) + 3)
      ≤ ((1 + ε) * Cabs * ((n : ℝ) + 3)) * Real.exp ((n : ℝ) + 3) :=
        mul_le_mul_of_nonneg_right h3 hexp.le
    _ = (1 + ε) * Cabs * ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) := by ring

/-- **The geometric factor does not beat the window-conversion.**  For `ε ≥ 0`,
`3·e³·((99/100)·e)ⁿ ≤ (99/100)ⁿ·ch_const n ε` — the geometrically-decayed `h`-coefficient is
`≥ 3·e³·((99/100)e)ⁿ`, and `((99/100)e)ⁿ ≥ 1` grows, so it is unbounded. -/
theorem ch_const_defeats_geom {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (3 : ℝ) * Real.exp 3 * ((99 / 100) * Real.exp 1) ^ n
      ≤ (99 / 100 : ℝ) ^ n * ch_const n ε := by
  have h1 := ch_const_ge_exp hε n
  have hpow : (0 : ℝ) ≤ (99 / 100 : ℝ) ^ n := by positivity
  have hstep := mul_le_mul_of_nonneg_left h1 hpow
  have hrw : (99 / 100 : ℝ) ^ n * (3 * Real.exp ((n : ℝ) + 3))
      = 3 * Real.exp 3 * ((99 / 100) * Real.exp 1) ^ n := by
    rw [show Real.exp ((n : ℝ) + 3) = Real.exp (n : ℝ) * Real.exp 3 from by rw [← Real.exp_add],
      exp_nat_eq]
    ring
  rw [← hrw]; exact hstep

/-- **Finding 2 (core).**  For every `n` and `ε ≥ 0`, `24 ≤ (99/100)ⁿ·ch_const n ε`: the
`h`-side recursion multiplier, *even after* applying the geometric decay factor `(99/100)ⁿ`,
stays `≥ 24 > 1`.  So no contraction (`c_h < 1`) is possible on the crude route. -/
theorem ch_const_geom_ge {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (24 : ℝ) ≤ (99 / 100 : ℝ) ^ n * ch_const n ε := by
  have hdef := ch_const_defeats_geom hε n
  have hp : (1 : ℝ) ≤ ((99 / 100) * Real.exp 1) ^ n := geom_mul_exp_pow_ge_one n
  have hge : 3 * Real.exp 3 ≤ 3 * Real.exp 3 * ((99 / 100) * Real.exp 1) ^ n := by
    have := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 3 * Real.exp 3 by positivity)
    rwa [mul_one] at this
  have h24 : (24 : ℝ) ≤ 3 * Real.exp 3 := by linarith [eight_le_exp_three]
  linarith [hdef, hge, h24]

/-! ## Part D — the optimistically fully-decayed recursion still blows up (`tauDec`)

The strongest form of the finding: grant the geometric factor `(99/100)ⁿ` to **both** the
forcing term `c_f` and the multiplier `c_h` (the h-side has no legitimate `fseq` factor, so
this is over-generous), take the recursion in the *closing* (equality) direction, and it still
doubles — hence the τ-sum is astronomically large regardless of `ε`. -/

/-- The optimistically fully-decayed Chen τ-sequence: `τ₀ = 0`, `τ₁ = 3`, and
`τ_{n+2} = (99/100)^{n+1}·cf_const (n+1)/(ε·e²) + (99/100)^{n+1}·ch_const (n+1)·τ_{n+1}`. -/
noncomputable def tauDec (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 3
  | (n + 2) => (99 / 100) ^ (n + 1) * cf_const (n + 1) ε / (ε * Real.exp 2)
      + (99 / 100) ^ (n + 1) * ch_const (n + 1) ε * tauDec ε (n + 1)

@[simp] theorem tauDec_zero (ε : ℝ) : tauDec ε 0 = 0 := rfl

@[simp] theorem tauDec_one (ε : ℝ) : tauDec ε 1 = 3 := rfl

theorem tauDec_succ_succ (ε : ℝ) (n : ℕ) :
    tauDec ε (n + 2)
      = (99 / 100) ^ (n + 1) * cf_const (n + 1) ε / (ε * Real.exp 2)
        + (99 / 100) ^ (n + 1) * ch_const (n + 1) ε * tauDec ε (n + 1) := rfl

/-- `0 ≤ tauDec ε n` for `ε ≥ 0`. -/
theorem tauDec_nonneg {ε : ℝ} (hε : 0 ≤ ε) : ∀ n, 0 ≤ tauDec ε n
  | 0 => by rw [tauDec_zero]
  | 1 => by rw [tauDec_one]; norm_num
  | (n + 2) => by
      rw [tauDec_succ_succ]
      exact add_nonneg
        (div_nonneg (mul_nonneg (by positivity) (cf_const_nonneg _ hε)) (by positivity))
        (mul_nonneg (mul_nonneg (by positivity) (ch_const_nonneg _ hε))
          (tauDec_nonneg hε (n + 1)))

/-- **The fully-decayed recursion still doubles.**  `2·τₙ ≤ τₙ₊₁` for `n ≥ 1`, from
`(99/100)ⁿ·ch_const ≥ 24 ≥ 2` (`ch_const_geom_ge`) and the nonnegative forcing term. -/
theorem tauDec_double {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    2 * tauDec ε n ≤ tauDec ε (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [tauDec_succ_succ]
  have hch : (2 : ℝ) ≤ (99 / 100) ^ (m + 1) * ch_const (m + 1) ε := by
    have := ch_const_geom_ge hε.le (m + 1); linarith
  have hτ : 0 ≤ tauDec ε (m + 1) := tauDec_nonneg hε.le (m + 1)
  have hcf : 0 ≤ (99 / 100 : ℝ) ^ (m + 1) * cf_const (m + 1) ε / (ε * Real.exp 2) :=
    div_nonneg (mul_nonneg (by positivity) (cf_const_nonneg _ hε.le)) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hch hτ, hcf]

/-- **Geometric blow-up.**  `3·2^m ≤ τ_{m+1}` — the fully-decayed τ-sequence blows up
geometrically in the depth `m`, `ε`-uniformly. -/
theorem tauDec_ge_geom {ε : ℝ} (hε : 0 < ε) (m : ℕ) : 3 * 2 ^ m ≤ tauDec ε (m + 1) := by
  induction m with
  | zero => rw [tauDec_one]; norm_num
  | succ k ih =>
      have hd : 2 * tauDec ε (k + 1) ≤ tauDec ε (k + 2) := tauDec_double hε (k + 1) (by omega)
      calc 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
        _ ≤ 2 * tauDec ε (k + 1) := by linarith [ih]
        _ ≤ tauDec ε (k + 2) := hd

/-- **The fully-decayed τ-sum blow-up.**  The odd-filtered τ-sum over `range (2m+3)` is
`≥ 3·2^{2m}` — a single odd term forces it.  As the range grows to `maxDepth s + 1 = π(z) + 1`,
the achievable `C₁'` is `≥ 3·2^{~π(z)}`: **no usable `C₁'` (in particular not `106`) exists**,
`ε`-uniformly, even with the geometric factor on both sides.  The even side is identical. -/
theorem tauDecSum_odd_ge {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    3 * 2 ^ (2 * m)
      ≤ ∑ n ∈ (Finset.range (2 * m + 3)).filter (fun n => Odd n), tauDec ε n := by
  have hmem : (2 * m + 1) ∈ (Finset.range (2 * m + 3)).filter (fun n => Odd n) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨m, by ring⟩⟩
  have hsingle : tauDec ε (2 * m + 1)
      ≤ ∑ n ∈ (Finset.range (2 * m + 3)).filter (fun n => Odd n), tauDec ε n :=
    Finset.single_le_sum (fun i _ => tauDec_nonneg hε.le i) hmem
  have hge : 3 * 2 ^ (2 * m) ≤ tauDec ε (2 * m + 1) := tauDec_ge_geom hε (2 * m)
  linarith

end Salt.Chen
