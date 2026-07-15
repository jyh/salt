/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.DecayMass

/-!
# C1cτ — the numeric τ-row: the explicit `tauChen`, and the honest un-closeability finding

The landed windowed keystones (`WindowedStep.bjs_theorem6_windowed_{upper,lower}`, and
transitively `TwinA1.twin_A1_lower`) leave three τ-shaped named hypotheses, all in terms of the
**landed per-level comparison constants** `SharpStep.cf_const` and `DecayMass.ch_const`:

* `htau1 : tau 1 = 3`               (the base anchor, `Lemma11.hlevel_one_upper`'s `τ₁ = 3`);
* `hτ0 : ∀ n, 0 ≤ tau n`;
* `hτrec : ∀ n, cf_const n ε + ε·e²·ch_const n ε·tau n ≤ ε·e²·tau (n+1)`   (**global** `∀ n`);
* `htau : ∑_{n ≤ maxDepth, parity} tau n ≤ Cᵢ`, over
  `Finset.range (maxDepth s + 1)`, `maxDepth s = s.prodPrimes.primeFactors.card` = `π(z)`.

This node was scoped as "supply the concrete `tauChen` and close the numeric row `C₁ = 106,
C₂ = 108`".  The **investigation** (recorded in `docs/blueprints/flags.md`, C1cτ) found that the
numeric row is **NOT achievable against the landed elementary constants**, for two independent,
machine-checked reasons.  This file lands the honest, sorry-free artifact.

## The two constants (landed, elementary, crude)

  `cf_const n ε = 2·(1+ε)·(n+3)·(log(n+3) + 19/log 2 + 2)·((n+3)·e^{n+3})`   (`SharpStep`)
  `ch_const n ε = (1+ε)·Cabs·(n+3)·e^{n+3}`,  `Cabs = 3(19/log2+2)·e·(e/(e−2))`  (`DecayMass`)

Both are the *crude* elementary majorants (`fseq ≤ 2`, the loglog window mass, `h ≤ e^{−u}`,
the dyadic geometric tail) — the `κ₃ = 1` regime of the C1c⁵ finding.  Neither is small: as
`ε → 0` both tend to a positive constant (`cf_const 0 ε ≥ 3168`, `ch_const n ε ≥ 24`), so the
recursion `τ_{n+1} ≥ cf_const n/(ε·e²) + ch_const n·τ_n` has **both** a blowing-up forcing term
`cf/(ε·e²) → ∞` and a super-unit multiplier `ch_const n ≥ 24 ≫ 1`.

## FINDING 1 — the global `hτrec` is un-instantiable with `τ₁ = 3` (`hτrec_zero_impossible`)

At `n = 0` the global recursion demands `cf_const 0 ε + ε·e²·ch_const 0 ε·τ₀ ≤ ε·e²·τ₁`.  With
`τ₁ = 3`, `τ₀ ≥ 0`, and `0 ≤ ε ≤ 1` this needs `cf_const 0 ε ≤ 3·ε·e² ≤ 24`, but
`cf_const 0 ε ≥ 3168` (`cf_const_zero_ge`).  So **no** non-negative `τ` with `τ₁ = 3` satisfies
the global `hτrec` — the keystones are un-instantiable *as stated*.  This is an interface
**over-demand**: the windowed induction `WindowedStep.T_le_of_peel_step_w` only ever *uses*
`hτrec m` at depths `m ≥ 1` (its base case `hlevel_one_upper` hardcodes `τ₁ = 3` and does not
recurse).  The sound fix is a catch-#28-style amendment restricting `hτrec` to `1 ≤ n` (a
Fable/design decision — see the flag; `tauChen_rec` below is exactly the `n ≥ 1` recursion the
amended keystones would consume).

## FINDING 2 — super-exponential blow-up × astronomical `maxDepth` (the κ₃=1 wall, quantified)

Even with the `n ≥ 1` amendment, the recursion forces `τ_{n+1} ≥ ch_const n·τ_n ≥ 24·τ_n`, so
`τ_{n+1} ≥ 2·τ_n` (`tauChen_double`) and `τ_{m+1} ≥ 3·2^m` (`tauChen_ge_geom`).  The τ-sum runs
over `range (maxDepth s + 1)` with `maxDepth s = π(z)` (astronomical), so the achievable `Cᵢ`
is `≥ 3·2^{π(z)-ish}` (`tauSum_odd_ge`): **no usable `C₁`/`C₂` exists**, certainly not `106/108`.
The slack `ε·Cᵢ·e²·h(σ)` then dwarfs the main term and the C0 ledger (S1/S2/S3 caps ≈ 0.002·M)
fails by dozens of orders of magnitude.  A smaller `ε` does **not** help — it enlarges the
forcing `cf/(ε·e²)` — so no ledger re-freeze (Table-1's 1/100000 row included) rescues it.  The
numeric row genuinely requires the **sharp** BJS constants (`κ₃ < 1` via the `E₁` exponential
integral, `c_f ∝ ε`), which are not elementary in mathlib.  This is the C1c⁵ `κ₃ = 1 ⟹ β ≥ 1`
finding made fully quantitative against the actually-landed `cf_const`/`ch_const`.

## What is proved here (sorry-free, axiom-clean)

* `tauChen ε` — the explicit τ-sequence (the equality recursion; `τ₀ = 0`, `τ₁ = 3`), with
  `tauChen_one`, `tauChen_nonneg`, and `tauChen_rec` (the recursion **on the window `n ≥ 1`** —
  what the amended keystones would consume); this is the "finite τ-table with the recursion
  proven on the window" the node's PB-floor asks for.
* `hτrec_zero_impossible` — Finding 1, from `cf_const_zero_ge` (`3168 ≤ cf_const 0 ε`).
* `tauChen_double` / `tauChen_ge_geom` / `tauSum_odd_ge` — Finding 2 (the quantified blow-up).

`maxHeartbeats`: default (200000); the proofs are elementary `nlinarith`/`calc` closes.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — positivity of the landed per-level constants -/

/-- `0 ≤ cf_const n ε` for `ε ≥ 0` (every factor of the product is nonnegative). -/
theorem cf_const_nonneg (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ cf_const n ε := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog : (0 : ℝ) ≤ Real.log ((n : ℝ) + 3) := Real.log_nonneg (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmid : (0 : ℝ) ≤ Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2 := by
    have : (0 : ℝ) < 19 / Real.log 2 := by positivity
    linarith
  unfold cf_const
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
    (by linarith)) hmid) (by positivity)

/-- `0 ≤ ch_const n ε` for `ε ≥ 0` (using `DecayMass.Cabs_nonneg`). -/
theorem ch_const_nonneg (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ ch_const n ε := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold ch_const
  refine mul_nonneg (mul_nonneg (mul_nonneg (by linarith) Cabs_nonneg) (by linarith))
    (by positivity)

/-! ## Part B — the explicit τ-sequence `tauChen` (the equality recursion on `n ≥ 1`)

`tauChen ε` is defined by the τ-recursion in the *closing* direction with **equality**: for
`n ≥ 1`, `ε·e²·τ_{n+1} = cf_const n ε + ε·e²·ch_const n ε·τ_n`, i.e.
`τ_{n+1} = cf_const n/(ε·e²) + ch_const n·τ_n`, anchored at `τ₁ = 3` (the base
`Lemma11.hlevel_one_upper` value).  `τ₀ := 0` is a placeholder (the base does not recurse). -/

/-- The explicit Chen τ-sequence: `τ₀ = 0`, `τ₁ = 3`,
`τ_{n+2} = cf_const (n+1) ε/(ε·e²) + ch_const (n+1) ε·τ_{n+1}`. -/
noncomputable def tauChen (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 3
  | (n + 2) => cf_const (n + 1) ε / (ε * Real.exp 2) + ch_const (n + 1) ε * tauChen ε (n + 1)

@[simp] theorem tauChen_zero (ε : ℝ) : tauChen ε 0 = 0 := rfl

@[simp] theorem tauChen_one (ε : ℝ) : tauChen ε 1 = 3 := rfl

theorem tauChen_succ_succ (ε : ℝ) (n : ℕ) :
    tauChen ε (n + 2)
      = cf_const (n + 1) ε / (ε * Real.exp 2) + ch_const (n + 1) ε * tauChen ε (n + 1) := rfl

/-- `0 ≤ tauChen ε n` for `ε ≥ 0`. -/
theorem tauChen_nonneg {ε : ℝ} (hε : 0 ≤ ε) : ∀ n, 0 ≤ tauChen ε n
  | 0 => by rw [tauChen_zero]
  | 1 => by rw [tauChen_one]; norm_num
  | (n + 2) => by
      rw [tauChen_succ_succ]
      exact add_nonneg (div_nonneg (cf_const_nonneg _ hε) (by positivity))
        (mul_nonneg (ch_const_nonneg _ hε) (tauChen_nonneg hε (n + 1)))

/-- **The τ-recursion, on the window `n ≥ 1`.**  `tauChen` satisfies the keystone's `hτrec`
inequality for every `n ≥ 1` (by construction, with equality).  This is exactly the recursion
the amended (`1 ≤ n`) windowed keystones would consume — see Finding 1 in the module header. -/
theorem tauChen_rec {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    cf_const n ε + ε * Real.exp 2 * ch_const n ε * tauChen ε n
      ≤ ε * Real.exp 2 * tauChen ε (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [tauChen_succ_succ]
  have he2 : ε * Real.exp 2 ≠ 0 := mul_ne_zero (ne_of_gt hε) (Real.exp_pos 2).ne'
  apply le_of_eq
  field_simp

/-! ## Part C — Finding 1: the global (`n = 0`) recursion is unsatisfiable with `τ₁ = 3` -/

/-- `Real.exp 2 < 8` (`e² ≈ 7.389`). -/
theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have hx : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hh := Real.exp_one_lt_d9
  rw [hx]; nlinarith [hh, Real.exp_pos 1]

/-- `8 ≤ Real.exp 3` (`e³ ≈ 20.09`). -/
theorem eight_le_exp_three : (8 : ℝ) ≤ Real.exp 3 := by
  have hh := Real.exp_one_gt_d9
  have hx : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [hx]; nlinarith [hh, Real.exp_pos 1]

/-- **`3168 ≤ cf_const 0 ε`** for `ε ≥ 0`.  The crude landed `f`-comparison constant is a large
absolute number at `n = 0` — independent of how small `ε` is (`(1+ε) ≥ 1`).  Bounds used:
`log 3 > 1`, `19/log 2 ≥ 19` (`log 2 < 1`), `e³ ≥ 8`. -/
theorem cf_const_zero_ge {ε : ℝ} (hε : 0 ≤ ε) : (3168 : ℝ) ≤ cf_const 0 ε := by
  have e : cf_const 0 ε
      = 2 * (1 + ε) * 3 * (Real.log 3 + 19 / Real.log 2 + 2) * (3 * Real.exp 3) := by
    simp only [cf_const, Nat.cast_zero, zero_add]
  rw [e]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have h19 : (19 : ℝ) ≤ 19 / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]; nlinarith [hlog2lt]
  have hmid : (22 : ℝ) ≤ Real.log 3 + 19 / Real.log 2 + 2 := by linarith
  have hlast : (24 : ℝ) ≤ 3 * Real.exp 3 := by linarith [eight_le_exp_three]
  have hf1 : (6 : ℝ) ≤ 2 * (1 + ε) * 3 := by nlinarith [hε]
  have hpos1 : (0 : ℝ) ≤ 2 * (1 + ε) * 3 := by nlinarith [hε]
  have hstep1 : (132 : ℝ) ≤ 2 * (1 + ε) * 3 * (Real.log 3 + 19 / Real.log 2 + 2) := by
    calc (132 : ℝ) = 6 * 22 := by norm_num
      _ ≤ 2 * (1 + ε) * 3 * (Real.log 3 + 19 / Real.log 2 + 2) :=
          mul_le_mul hf1 hmid (by norm_num) hpos1
  calc (3168 : ℝ) = 132 * 24 := by norm_num
    _ ≤ 2 * (1 + ε) * 3 * (Real.log 3 + 19 / Real.log 2 + 2) * (3 * Real.exp 3) :=
        mul_le_mul hstep1 hlast (by norm_num) (by linarith [hstep1])

/-- **Finding 1.**  The global keystone hypothesis `hτrec` is un-instantiable with `τ₁ = 3` and
`τ₀ ≥ 0`: its `n = 0` instance is impossible (`cf_const 0 ε ≥ 3168 > 24 ≥ 3·ε·e²`).  Hence no
non-negative `τ` with `τ₁ = 3` satisfies `WindowedStep.bjs_theorem6_windowed_*`'s global
`hτrec` — the keystone needs the `1 ≤ n` amendment (module header, Finding 1). -/
theorem hτrec_zero_impossible {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (tau : ℕ → ℝ)
    (hτ0 : 0 ≤ tau 0) (htau1 : tau 1 = 3) :
    ¬ (cf_const 0 ε + ε * Real.exp 2 * ch_const 0 ε * tau 0 ≤ ε * Real.exp 2 * tau 1) := by
  rw [htau1]
  intro h
  have hcf : (3168 : ℝ) ≤ cf_const 0 ε := cf_const_zero_ge hε0
  have h1 : ε * Real.exp 2 ≤ 1 * 8 :=
    mul_le_mul hε1 exp_two_lt_eight.le (Real.exp_pos 2).le (by norm_num)
  have hsmall : ε * Real.exp 2 * 3 < 3168 := by nlinarith [h1]
  have hnn : 0 ≤ ε * Real.exp 2 * ch_const 0 ε * tau 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg hε0 (Real.exp_pos 2).le) (ch_const_nonneg 0 hε0)) hτ0
  nlinarith [h, hcf, hsmall, hnn]

/-! ## Part D — Finding 2: super-exponential growth (the κ₃ = 1 wall, quantified) -/

/-- `1 ≤ Cabs` (in fact `≥ 12`): `3(19/log2+2) ≥ 6`, `e ≥ 2`, `e/(e−2) ≥ 1`. -/
theorem Cabs_ge_one : (1 : ℝ) ≤ Cabs := by
  unfold Cabs
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he := Real.exp_one_gt_d9
  have hden : (0 : ℝ) < Real.exp 1 - 2 := by linarith
  have hf1 : (6 : ℝ) ≤ 3 * (19 / Real.log 2 + 2) := by
    have : (0 : ℝ) < 19 / Real.log 2 := by positivity
    nlinarith [this]
  have hf2 : (2 : ℝ) ≤ Real.exp 1 := by linarith
  have hf3 : (1 : ℝ) ≤ Real.exp 1 / (Real.exp 1 - 2) := by
    rw [le_div_iff₀ hden]; linarith
  have hstep : (12 : ℝ) ≤ 3 * (19 / Real.log 2 + 2) * Real.exp 1 := by
    calc (12 : ℝ) = 6 * 2 := by norm_num
      _ ≤ 3 * (19 / Real.log 2 + 2) * Real.exp 1 := mul_le_mul hf1 hf2 (by norm_num) (by linarith)
  have hprod :
      (12 : ℝ) ≤ 3 * (19 / Real.log 2 + 2) * Real.exp 1 * (Real.exp 1 / (Real.exp 1 - 2)) := by
    calc (12 : ℝ) = 12 * 1 := by norm_num
      _ ≤ 3 * (19 / Real.log 2 + 2) * Real.exp 1 * (Real.exp 1 / (Real.exp 1 - 2)) :=
          mul_le_mul hstep hf3 (by norm_num) (by linarith [hstep])
  linarith

/-- **`2 ≤ ch_const n ε`** for `ε ≥ 0` (in fact `≥ 24`): `Cabs ≥ 1`, `(n+3) ≥ 3`, `e^{n+3} ≥ 8`.
So the recursion multiplier never contracts. -/
theorem ch_const_ge_two (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : (2 : ℝ) ≤ ch_const n ε := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold ch_const
  have h1e : (1 : ℝ) ≤ 1 + ε := by linarith
  have hn3 : (3 : ℝ) ≤ (n : ℝ) + 3 := by linarith
  have hexp : (8 : ℝ) ≤ Real.exp ((n : ℝ) + 3) :=
    le_trans eight_le_exp_three (Real.exp_le_exp.mpr (by linarith))
  have s1 : (1 : ℝ) ≤ (1 + ε) * Cabs := by
    have h := mul_le_mul h1e Cabs_ge_one (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ 1 + ε)
    linarith [h]
  have s2 : (3 : ℝ) ≤ (1 + ε) * Cabs * ((n : ℝ) + 3) := by
    calc (3 : ℝ) = 1 * 3 := by norm_num
      _ ≤ (1 + ε) * Cabs * ((n : ℝ) + 3) := mul_le_mul s1 hn3 (by norm_num) (by linarith [s1])
  have hprod : (24 : ℝ) ≤ (1 + ε) * Cabs * ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) := by
    calc (24 : ℝ) = 3 * 8 := by norm_num
      _ ≤ (1 + ε) * Cabs * ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) :=
          mul_le_mul s2 hexp (by norm_num) (by linarith [s2])
  linarith

/-- **The τ-doubling.**  `2·τ_n ≤ τ_{n+1}` for `n ≥ 1` (from `ch_const ≥ 2` and the nonnegative
forcing term).  The recursion is expansive, not contracting. -/
theorem tauChen_double {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    2 * tauChen ε n ≤ tauChen ε (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [tauChen_succ_succ]
  have hch : (2 : ℝ) ≤ ch_const (m + 1) ε := ch_const_ge_two (m + 1) hε.le
  have hτ : 0 ≤ tauChen ε (m + 1) := tauChen_nonneg hε.le (m + 1)
  have hcf : 0 ≤ cf_const (m + 1) ε / (ε * Real.exp 2) :=
    div_nonneg (cf_const_nonneg _ hε.le) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hch hτ, hcf]

/-- **The geometric lower bound.**  `3·2^m ≤ τ_{m+1}` — the τ-sequence blows up super-linearly
(in fact geometrically) in the depth `m`. -/
theorem tauChen_ge_geom {ε : ℝ} (hε : 0 < ε) (m : ℕ) : 3 * 2 ^ m ≤ tauChen ε (m + 1) := by
  induction m with
  | zero => rw [tauChen_one]; norm_num
  | succ k ih =>
      have hd : 2 * tauChen ε (k + 1) ≤ tauChen ε (k + 2) := tauChen_double hε (k + 1) (by omega)
      calc 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
        _ ≤ 2 * tauChen ε (k + 1) := by linarith [ih]
        _ ≤ tauChen ε (k + 2) := hd

/-- **The τ-sum blow-up (the un-closeable numeric row).**  The odd-filtered τ-sum over
`Finset.range (2m+3)` is `≥ 3·2^{2m}` — the single odd term at `n = 2m+1` already forces it.
As the range grows to `maxDepth s + 1 = π(z) + 1`, the achievable `C₁` is `≥ 3·2^{~π(z)}`,
astronomically large: **no usable `C₁` (in particular not `106`) exists** for the landed
constants.  The even-side dual is identical. -/
theorem tauSum_odd_ge {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    3 * 2 ^ (2 * m) ≤ ∑ n ∈ (Finset.range (2 * m + 3)).filter (fun n => Odd n), tauChen ε n := by
  have hmem : (2 * m + 1) ∈ (Finset.range (2 * m + 3)).filter (fun n => Odd n) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨m, by ring⟩⟩
  have hsingle : tauChen ε (2 * m + 1)
      ≤ ∑ n ∈ (Finset.range (2 * m + 3)).filter (fun n => Odd n), tauChen ε n :=
    Finset.single_le_sum (fun i _ => tauChen_nonneg hε.le i) hmem
  have hge : 3 * 2 ^ (2 * m) ≤ tauChen ε (2 * m + 1) := tauChen_ge_geom hε (2 * m)
  linarith

end Salt.Chen
