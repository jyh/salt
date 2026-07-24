/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Mertens.Second

/-!
# MR-gate wave 1, stone S1 — the pretentious-distance bookkeeping (`Dist`)

The pretentious distance `𝔻(f, g; x)² = ∑_{p≤x} (1 − Re(f(p)·conj g(p)))/p`
(Tao 1509.05422 / Granville–Soundararajan) and its evaluation lemmas.

Rung card (MR freeze, S1): `𝔻(λ, χ·n^{it}; x)² = loglog x + Re log L(1+1/logx+it, χ)
+ O_Q(1)`; the Euler `k≥2` prime-power tail is `O(1)` (`≤ 0.78`, first term
`p=2,k=2 = 1/4`), the Mertens shift is `O(1)` (`mertens_second_sharp`,
`Second.lean:216`).

WHAT THIS FILE LANDS (the tractable, load-bearing core):
* `pretDistSq` — the distance definition.
* `pretDistSq_principal` — the algebraic unfolding at the principal diagonal
  (`χ = 1`, `t = 0`, `g ≡ 1`): every prime contributes exactly `2/p` when
  `Re f(p) = −1` (the Liouville value).  This is the small-`t` coverage the MR
  map flags (`mr_map_region.md §4`, `𝔻(λ,1;x)² = ∑ 2/p = 2 loglog x`).
* `pretDistSq_principal_eval` — its Mertens evaluation with the SHARP `O(1/log)`
  error (so the additive `O(1)` collapses to `2·M` at large scale) — the
  `2·loglog x` divergence the MR gate needs at `t = 0`.
* `prime_power_tail_le` — the Euler `k≥2` tail, telescoped to `≤ 1` per prime
  (design audit target `0.78 = Σ_p 1/(p(p−1))`, first term `p=2,k=2 → 1/4`;
  the telescoping majorant is what ships).

RESIDUAL (`χ ≠ 1` only — the `q = 1` half CLOSED 2026-07-19): for `χ = 1`,
`t ≠ 0` the identity `𝔻² = loglog x + Re log ζ(1+1/logx+it) + O(1)` is landed —
`euler_osc_truncation` (`Salt/MR/PrimeSigmaShift.lean`) +
`euler_osc_bridge_unconditional` (`Salt/MR/PrimeTail.lean`) control both the
`p > x` truncation and the `σ = 1 vs 1+1/logx` shift, yielding UNCONDITIONAL
`lambda_nonpret` (`Salt/MR/NonPretClose.lean`).  What is left is the `χ ≠ 1`
twist.  CORRECTION (2026-07-24): the log-Euler product for characters IS in
mathlib — `DirichletCharacter.LSeries_eulerProduct_exp_log`
(`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean:137`,
`exp(Σ'_p −log(1−χ(p)p^{−s})) = L(s,χ)`), the exact analogue of the
`riemannZeta_eulerProduct_exp_log` this corpus already rides; the earlier claim
that only the log-DERIVATIVE bridge (`Salt.SW.logDeriv_LFunction_eq`,
`EulerBridge.lean:145`) was available was WRONG.  The remaining `χ ≠ 1` work is
therefore transporting the truncation / `σ`-shift estimates across the twist,
not supplying a missing Euler bridge.  Constant audit — the "chain-G additive =
5.00 EXACT" is the total `O(1)` of that full chain; it cannot be pinned here
until the twisted chain is closed.  See `docs/blueprints/flags.md` (MR-W1 entry
and the 2026-07-24 supersession pointer).
-/

namespace Salt.MR

open scoped BigOperators

/-- **The pretentious distance squared** (Granville–Soundararajan / Tao).
`𝔻(f, g; x)² = ∑_{p≤x} (1 − Re(f(p)·conj g(p)))/p`, the sum over primes `p ≤ x`
of `(1 − Re f(p)\overline{g(p)})/p`. -/
noncomputable def pretDistSq (f g : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
    (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ)

/-- **The principal diagonal unfolding** (`χ = 1`, `t = 0`, `g ≡ 1`).  When
`Re f(p) = −1` on every prime `p ≤ x` (the Liouville value `λ(p) = −1`), each
term of `𝔻(f, 1; x)²` is exactly `2/p`. -/
theorem pretDistSq_principal (f : ℕ → ℂ) (x : ℝ)
    (hf : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (f p).re = -1) :
    pretDistSq f (fun _ => 1) x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (2 : ℝ) / (p : ℝ) := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hconj : (starRingEnd ℂ) (1 : ℂ) = 1 := by simp
  rw [hconj, mul_one, hf p hp]
  norm_num

/-- **The Liouville split** (any twist `g`).  When `f(p) = −1` on every prime
`p ≤ x` (the Liouville value `λ(p) = −1`, as a complex number), the pretentious
distance separates the divergent Mertens part from the twist:
`𝔻(λ, g; x)² = ∑_{p≤x} (1 + Re g(p))/p`.  For `g(p) = χ(p)·p^{it}` this is the
starting point of the freeze's `𝔻² = loglog x + Re log L(1+1/logx+it,χ) + O(1)`
identity — the `Re g(p)/p` sum is the part that (via the Euler-log-of-`L` bridge,
flagged residual) becomes `Re log L`. -/
theorem pretDistSq_liouville_split (f g : ℕ → ℂ) (x : ℝ)
    (hf : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, f p = -1) :
    pretDistSq f g x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 + (g p).re) / (p : ℝ) := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [hf p hp, neg_one_mul, Complex.neg_re, Complex.conj_re, sub_neg_eq_add]

/-- **The principal Mertens evaluation.**  At the diagonal, `𝔻(f, 1; x)²
= 2·loglog⌊x⌋ + 2M + O(1/log⌊x⌋)` (`M` the Meissel–Mertens constant), so the
additive `O(1)` decays at large scale — the `2·loglog x` divergence the MR gate
needs at `t = 0`.  The error constant is threaded from `mertens_second_sharp`. -/
theorem pretDistSq_principal_eval (f : ℕ → ℂ) (x : ℝ) (hx : 2 ≤ ⌊x⌋₊)
    (hf : ∀ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (f p).re = -1) :
    ∃ M C : ℝ, 0 ≤ C ∧
      |pretDistSq f (fun _ => 1) x - 2 * (Real.log (Real.log (⌊x⌋₊ : ℝ)) + M)|
        ≤ 2 * C / Real.log (⌊x⌋₊ : ℝ) := by
  obtain ⟨M, C, hCnn, hM⟩ := Salt.Mertens.mertens_second_sharp
  refine ⟨M, C, hCnn, ?_⟩
  rw [pretDistSq_principal f x hf]
  have hsum2 : (∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (2 : ℝ) / (p : ℝ))
      = 2 * ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hsum2]
  have hbase := hM ⌊x⌋₊ hx
  rw [show
      (2 : ℝ) * ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
          - 2 * (Real.log (Real.log (⌊x⌋₊ : ℝ)) + M)
        = 2 * ((∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            - (Real.log (Real.log (⌊x⌋₊ : ℝ)) + M)) by ring]
  rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  calc 2 * |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          - (Real.log (Real.log (⌊x⌋₊ : ℝ)) + M)|
      ≤ 2 * (C / Real.log (⌊x⌋₊ : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = 2 * C / Real.log (⌊x⌋₊ : ℝ) := by ring

/-- **The Euler `k ≥ 2` prime-power tail** (the `O(1)` shift of `S1`).  For each
`p ≥ 2` and truncation `Mtr`, `∑_{2 ≤ k ≤ Mtr} p^{-k} ≤ 1/(p(p−1))` — a per-prime
geometric-tail majorant.  Summed over any finite prime set this is the Euler
`k≥2` remainder; over ALL primes it converges to the design audit value
`Σ_p 1/(p(p−1)) ≈ 0.773 ≤ 0.78` (first term `p=2 → 1/(2·1)`, and the `k=2` term
alone is `1/p²`, `= 1/4` at `p = 2`).

Proof: with `r = 1/p ∈ [0,1)`, telescope the finite geometric sum by induction —
`(1−r)·∑ r^k = r² − r^{Mtr+1} ≤ r²`, then `r²/(1−r) = 1/(p(p−1))`. -/
theorem prime_power_tail_le {p : ℕ} (hp : 2 ≤ p) (Mtr : ℕ) :
    (∑ k ∈ Finset.Icc 2 Mtr, (1 : ℝ) / (p : ℝ) ^ k)
      ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  set r : ℝ := (p : ℝ)⁻¹ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, inv_lt_one_iff₀]; right; linarith
  have h1r : 0 < 1 - r := by linarith
  have hterm : ∀ k, (1 : ℝ) / (p : ℝ) ^ k = r ^ k := by
    intro k; rw [hrdef, one_div, inv_pow]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  -- the exact telescoping identity `(1−r)·∑_{k∈Icc 2 Mtr} r^k = r² − r^{Mtr+1}`
  -- for `Mtr ≥ 1`, by induction on `Mtr`.
  have htel : ∀ n : ℕ, 1 ≤ n →
      (1 - r) * (∑ k ∈ Finset.Icc 2 n, r ^ k) = r ^ 2 - r ^ (n + 1) := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · subst hm0
        have hemp : Finset.Icc 2 1 = (∅ : Finset ℕ) := by rw [Finset.Icc_eq_empty]; omega
        rw [hemp, Finset.sum_empty, mul_zero]; ring
      · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1), mul_add, ih (by omega)]
        ring
  have hkey : (1 - r) * (∑ k ∈ Finset.Icc 2 Mtr, r ^ k) ≤ r ^ 2 := by
    rcases Nat.eq_zero_or_pos Mtr with hM0 | hM1
    · subst hM0
      rw [show Finset.Icc 2 0 = (∅ : Finset ℕ) from by rw [Finset.Icc_eq_empty]; omega,
          Finset.sum_empty, mul_zero]
      positivity
    · rw [htel Mtr hM1]; nlinarith [pow_nonneg hr0 (Mtr + 1)]
  have hdiv : (∑ k ∈ Finset.Icc 2 Mtr, r ^ k) ≤ r ^ 2 / (1 - r) := by
    rw [le_div_iff₀ h1r]
    linarith [hkey, mul_comm (1 - r) (∑ k ∈ Finset.Icc 2 Mtr, r ^ k)]
  refine le_trans hdiv (le_of_eq ?_)
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hpm1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpm1
  have h1rne : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
  rw [hrdef] at h1rne ⊢
  field_simp

end Salt.MR
