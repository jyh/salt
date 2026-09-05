/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.TwinBar.TwinParitySieveLog

/-!
# The sifted harmonic count — `hcount` discharged (λ-BV, P1 fill (E), 2026-09-05)

Council 09/05 item 3 fired the scout's option (E): discharge the `hcount` hypothesis of the
direct road's win condition (`logSifted_lower_of_count_and_atoms`, `TwinParitySieve.lean`) and its
composition `twinLogWeight_support_infinite_of_rate`.  Class B, no new mathematics.

## What is proved, and from what

The per-divisor count `C_d = ∑_{n ≤ N, d ∣ n(n+2)} 1/n` is `Clog N d` of the log lane
(`TwinParitySieveLog.lean`, 09/03), and that lane already holds the two-sided estimate
`|Clog N d − ν(d)·H_N| ≤ 4·ρ(d)` (`remLogCount_abs_le`: `ρ(d)` residue classes of `Rnat d`, each
within `4` of `(1/d)·H_N` by `abs_class_sub_harmonic_le`).  So the SIGNED Möbius sum obeys

    `(∑_{d∣P} μ(d)ν(d))·H_N − 4·∑_{d∣P} ρ(d)  ≤  ∑_{d∣P} μ(d)·C_d` ,

which is exactly `hcount` at `Hmain N := W·H_N − 4·∑_{d∣P} ρ(d)`, with `W = ∑ μν`
(`sum_divisors_moebius_twinNu_eq_W`) and `W > 0` (`W_pos`); `hgrow` is `log N ≤ H_N` at `c := W`.
The terminal `twinLogWeight_support_infinite_of_atom` therefore takes `hatom` ALONE, and its
sibling `_of_atom_rate` takes `hatom` at the SOURCE's strength (`|atom N| ≤ ε·log N + A`, `ε < W`).

## The record of the re-cut (find first, then author)

A first freeze of this module (`4187b622`) carried NINE statements, five of which re-derived at
`log N`, with constant `3`, the per-class count the log lane had landed two days earlier at `H_N`
with constant `4`.  Caught while drafting the audit rows, before any proof was paid; re-cut to the
FIVE below on the landed estimate.  The `4` is the log lane's majorant (its docstring: the honest
per-class sup is `≈ 2.4`), inherited, not chosen here.

## Honest label

No new unconditional theorem.  `hatom` — the full-range log-averaged two-point at every class
mod `P` at a COMMON `N` — is the ONE remaining hypothesis on the direct road, and nothing here
produces it (fixed `z`: Tao Thm 1.2's quantifier; growing `z`: the literature census's binder C,
held by nobody).  The uniform-`A` terminal over-demanded what that source supplies (Tao's theorem
gives `o(log x)`, the corpus's spine an `ε·log`-scale floor, never `O(1)`); `_of_atom_rate` is
the consumer's binder re-cut to the producer's conclusion.  Nothing bears on twin primes.
-/

namespace Salt.TwinBar

open Finset

/-! ## `log N ≤ H_N` — the bridge from the harmonic sum to the growth rate -/

/-- **`log N ≤ H_N`** for every natural `N` (at `N = 0` both sides are `0`).

Recipe (class A): `cases N with | zero => simp | succ m => ?_`; in the `succ` case
`log_succ_le_sum_inv_Icc (m + 1)` (`TwinParitySieve.lean:907`, summand `(n : ℝ)⁻¹` — match by
`simp only [one_div]`) gives `Real.log ((m + 1 : ℕ) + 1) ≤ H_{m+1}`, and
`Real.log_le_log (by positivity) (by linarith)` gives `Real.log (m + 1) ≤ Real.log ((m + 1) + 1)`;
mind the casts (`push_cast`). -/
theorem log_natCast_le_sum_inv_Icc (N : ℕ) :
    Real.log (N : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := by
  sorry

/-! ## `hcount` discharged — the signed Möbius sum from below -/

/-- ⭐ **`hcount`, DISCHARGED.**  For every `P` and `N`,

    `(∑_{d∣P} μ(d)ν(d))·H_N − 4·∑_{d∣P} ρ(d)  ≤  ∑_{d∣P} μ(d)·∑_{n ≤ N, d ∣ n(n+2)} 1/n` .

This is the consumer's binder `hcount` (`twinLogWeight_support_infinite_of_rate`,
`logSifted_lower_of_count_and_atoms`) at `Hmain N := (∑ μν)·H_N − 4·∑ ρ`.  No squarefreeness is
needed: every `d ∈ P.divisors` is positive (`Nat.pos_of_mem_divisors`) and `|μ(d)| ≤ 1`.

Recipe (class B): `rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`;
`refine Finset.sum_le_sum fun d hd => ?_`; `have hd0 := Nat.pos_of_mem_divisors hd`;
`have h := remLogCount_abs_le (N := N) hd0` (`TwinParitySieveLog.lean:291`,
`|remLogCount d N| ≤ 4 * rho d`); `rw [remLogCount, Clog_one] at h; unfold Clog at h` (now
`h : |C_d − ν(d) * H_N| ≤ 4 * ρ(d)` with `C_d` the filtered sum, syntactically the goal's);
`have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by exact_mod_cast
ArithmeticFunction.abs_moebius_le_one` (the integer statement `|μ n| ≤ 1`; `Int.cast_abs`);
then `μ d * ν d * H_N − 4 * ρ d ≤ μ d * C_d` from
`μ d * (C_d − ν d * H_N) ≥ −|μ d| * |C_d − ν d * H_N| ≥ −4 ρ d`
(`neg_abs_le`, `abs_mul`, `mul_le_mul` on nonnegatives, `abs_nonneg`); close by `nlinarith`
or an explicit `le_trans` chain. -/
theorem moebius_sum_inv_dvd_ge (P N : ℕ) :
    (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d)
          * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ))
        - 4 * ∑ d ∈ P.divisors, (rho d : ℝ)
      ≤ ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ) := by
  sorry

/-- **The growth constant is positive**: `0 < ∑_{d∣P} μ(d)ν(d)` for squarefree `P`, because the
sum IS the twin sieve's `W` (`sum_divisors_moebius_twinNu_eq_W`, at any `N`) and `W > 0`
(`Salt.BrunLower.W_pos`).

Recipe (class A): `rw [sum_divisors_moebius_twinNu_eq_W 1 P hP]; exact Salt.BrunLower.W_pos _`. -/
theorem sum_divisors_moebius_twinNu_pos (P : ℕ) (hP : Squarefree P) :
    0 < ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d := by
  sorry

/-! ## The terminal — one hypothesis left on the direct road -/

/-- ⭐⭐ **THE DIRECT ROAD AT ONE HYPOTHESIS.**  Given the Tao atom mass as a uniform bound —
`hatom` alone — the `P`-rough parity survivors are INFINITE.  `hcount` is
`moebius_sum_inv_dvd_ge`; `hgrow` is `W·log N − 4∑ρ ≤ W·H_N − 4∑ρ` from
`log_natCast_le_sum_inv_Icc` at `c := W` (positive by `sum_divisors_moebius_twinNu_pos`).

⛔ **Honest label.**  `hatom` — the full-range log-averaged two-point at every class mod `P` at a
common `N` — has NO producer in the corpus, so this is the prize SHAPE with its last elementary
gap closed, not the prize.  Nothing bears on twin primes.

Recipe (class A/B): `have hW := sum_divisors_moebius_twinNu_pos P hP`;
`exact twinLogWeight_support_infinite_of_rate hP (c := ∑ d ∈ P.divisors, (μ d : ℝ) * nu d)
  (C := 4 * ∑ d ∈ P.divisors, (rho d : ℝ)) hW
  (Hmain := fun N => (∑ …) * (∑ n ∈ Icc 1 N, 1/n) - 4 * ∑ …) (fun N => moebius_sum_inv_dvd_ge P N)
  hatom (fun N => by have := mul_le_mul_of_nonneg_left (log_natCast_le_sum_inv_Icc N) hW.le;
  linarith)` (binder order of `_of_rate`: `{P} hP {A c C} hc {Hmain} hcount hatom hgrow`). -/
theorem twinLogWeight_support_infinite_of_atom {P : ℕ} (hP : Squarefree P) {A : ℝ}
    (hatom : ∀ N : ℕ, |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)| ≤ A) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  sorry

/-! ## The terminal at the SOURCE's strength — a demand-side finding, flagged

`twinLogWeight_support_infinite_of_atom` reads `hatom` as a UNIFORM bound `|atom N| ≤ A`.  That
is STRONGER than what the road's source supplies: Tao's logarithmic two-point theorem gives
`∑_{n ≤ x} λ(n)λ(n+h)/n = o(log x)`, and the corpus's own spine concludes an `ε·log`-scale floor
(`logChowla2_v7_rated`: `≤ ε·log ω` on windows), never `O(1)`.  Since `Hmain N` grows like
`W·H_N ≥ W·log N`, the composition only needs `|atom N| ≤ ε·log N + A` with `ε < W` — the
consumer's binder re-cut to the producer's conclusion (demand side first).  ⚖️ ADDED BEYOND THE
commissioned discharge, on the branch, for the helm to keep or strike: no new mathematics, one
re-composition. -/

/-- ⭐ **THE DIRECT ROAD AT ONE HYPOTHESIS, AT THE SOURCE's STRENGTH.**  If the atom mass is
`≤ ε·log N + A` with `ε < W = ∑_{d∣P} μ(d)ν(d)`, the `P`-rough parity survivors are INFINITE.
`twinLogWeight_support_infinite_of_atom` is the case `ε = 0`.

Recipe (class B — mirror the five-line body of `twinLogWeight_support_infinite_of_win`,
`TwinParitySieve.lean:1332`): `have hW := sum_divisors_moebius_twinNu_pos P hP`;
`refine support_infinite_of_partialSums_unbounded (twinLogWeight_nonneg P) fun M => ?_`;
`obtain ⟨N, hN⟩ := hdiv_of_log_growth (sub_pos.mpr hε) (A := 0)
  (Hmain := fun N => (W - ε) * Real.log N - (4 * ∑ρ + A)) (fun N => le_rfl) M`
(`hdiv_of_log_growth`, `TwinParitySieve.lean:1410`: `{c C A} (hc : 0 < c) {Hmain}
(hgrow : ∀ N, c * log N - C ≤ Hmain N) : ∀ M, ∃ N, M < Hmain N - A`); `refine ⟨N + 1, ?_⟩`;
`rw [sum_twinLogWeight_range]`; then
`logSifted_lower_of_count_and_atoms hP (moebius_sum_inv_dvd_ge P N) (hatom N)` (its `A` is
generic — it instantiates at `ε * Real.log N + A`) gives `W·H_N − 4∑ρ − (ε·log N + A) ≤ sifted`,
and `W·log N ≤ W·H_N` (`mul_le_mul_of_nonneg_left (log_natCast_le_sum_inv_Icc N) hW.le`) closes
by `linarith`. -/
theorem twinLogWeight_support_infinite_of_atom_rate {P : ℕ} (hP : Squarefree P) {ε A : ℝ}
    (hε : ε < ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d)
    (hatom : ∀ N : ℕ, |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)|
          ≤ ε * Real.log N + A) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  sorry

end Salt.TwinBar
