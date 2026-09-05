/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.TwinBar.TwinParitySieve

/-!
# The sifted harmonic count — `hcount` discharged (λ-BV, P1 fill (E), 2026-09-05)

Council 09/05 item 3 fired the scout's option (E): discharge the `hcount` hypothesis of the
direct road's win condition (`logSifted_lower_of_count_and_atoms`, `TwinParitySieve.lean`) and its
composition `twinLogWeight_support_infinite_of_rate`.  Class B, no new mathematics: everything
here is elementary counting on top of the landed per-class atoms.

## What is proved

For `d ≥ 1` and a residue `r < d`, the class sum `S_r(N) = ∑_{n ≤ N, n ≡ r (d)} 1/n` is
`(1/d)·log N` up to a bounded error (`|S_r(N) − (1/d)·log N| ≤ 3`).  Summing over the `ρ(d)`
classes of `Rnat d` (`dvd_iff_mem_Rnat`), the divisor count
`C_d = ∑_{n ≤ N, d ∣ n(n+2)} 1/n` is `ν(d)·log N` up to `3·ρ(d)`, so the SIGNED Möbius sum obeys

    `(∑_{d∣P} μ(d)ν(d))·log N − 3·∑_{d∣P} ρ(d)  ≤  ∑_{d∣P} μ(d)·C_d` ,

which is exactly `hcount` with `Hmain N := W·log N − 3·∑_{d∣P} ρ(d)` and `W = ∑ μν`
(`sum_divisors_moebius_twinNu_eq_W`), and `hgrow` holds with `c := W > 0` (`W_pos`).  The
terminal `twinLogWeight_support_infinite_of_atom` therefore takes `hatom` ALONE.

## The one numeral

The per-class error `3` is CHOSEN crude, not forced: from above the landed `sum_inv_class_le`
gives `1 + 1/d ≤ 2`; from below the landed ADDITIVE lemma `sum_inv_affine_sub_harmonic` costs
`2/d` and the scale change `M ≈ N/d` costs `(log 2d)/d ≤ 2 − 1/d` (`log x ≤ x − 1`), so
`(log 2d + 2)/d ≤ 2 + 1/d ≤ 3`.  A sharper constant buys nothing: the consumer reads
`Hmain N = W·log N − O_P(1)` and only the growth rate `W` matters.

## Honest label

No new unconditional theorem.  `hatom` — the full-range log-averaged two-point at every class
mod `P` at a COMMON `N` — is the ONE remaining hypothesis on the direct road, and nothing here
produces it (fixed `z`: Tao Thm 1.2's quantifier; growing `z`: the literature census's binder C,
held by nobody).  Nothing bears on twin primes.
-/

namespace Salt.TwinBar

open Finset

/-! ## The per-class sum against `(1/d)·log N`, from above and from below -/

/-- **The class sum from above.**  From the landed `sum_inv_class_le`
(`S_r(N) ≤ 1 + (1/d)(1 + log N)`): `S_r(N) − (1/d)·log N ≤ 1 + 1/d`.

Recipe (class A): `have h := sum_inv_class_le hd hr N`; `rw [mul_add, mul_one] at h`;
`linarith`. -/
theorem sum_inv_class_sub_log_le {d r : ℕ} (hd : 0 < d) (hr : r < d) (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ))
        - (1 / (d : ℝ)) * Real.log N ≤ 1 + 1 / (d : ℝ) := by
  sorry

/-- **The class sum from below.**  `(1/d)·log N − (log(2d) + 2)/d ≤ S_r(N)`.

Recipe (class C, two cases on `2·d ≤ N`).
* `N < 2·d`: the sum is `≥ 0` (`Finset.sum_nonneg`, `positivity`) and the left side is `≤ 0`:
  `Real.log N ≤ Real.log (2d)` (for `N = 0` use `Real.log_zero` and `Real.log_nonneg`; for
  `0 < N` use `Real.log_le_log` with `(N : ℝ) ≤ 2d` by `exact_mod_cast`), so
  `(1/d)·(log N − log 2d) ≤ 0` and `−2/d < 0`.
* `2·d ≤ N`: set `M := (N - r) / d`.  The map `m ↦ d * m + r` sends `Finset.Icc 1 M` INTO the
  class (`d ≤ d*m + r ≤ N`: `Nat.div_mul_le_self`, and `(d*m + r) % d = r` by
  `Nat.mul_add_mod` + `Nat.mod_eq_of_lt hr`), injectively (`omega` from `Nat.add_right_cancel`
  / `Nat.eq_of_mul_eq_mul_left`), so by `Finset.sum_image` + `Finset.sum_le_sum_of_subset_of_nonneg`
  (with `push_cast` on `((d * m + r : ℕ) : ℝ)`)
  `∑_{m ∈ Icc 1 M} 1/(d·m + r) ≤ S_r(N)`.  Then
  `(sum_inv_affine_sub_harmonic hd hr.le M).2` gives `(1/d)·H_M − 2/d ≤ ∑_{m ≤ M} 1/(d·m+r)`;
  `log_succ_le_sum_inv_Icc M` gives `Real.log (M + 1) ≤ H_M` (its summand is `(m : ℝ)⁻¹`:
  `simp only [one_div]`); and `Nat.lt_div_mul_add hd : N - r < (N - r) / d * d + d` cast to ℝ
  (`Nat.cast_sub (by omega : r ≤ N)`) gives `d·(M + 1) > N − r ≥ N − d ≥ N/2`, hence
  `M + 1 > N/(2d)` and `Real.log (N/(2d)) ≤ Real.log (M + 1)` (`Real.log_le_log`, `positivity`),
  with `Real.log (N/(2d)) = Real.log N − Real.log (2d)` (`Real.log_div`, both nonzero).
  Combine by `linarith` / `nlinarith` after clearing `1/d` with `div_le_iff₀`/`field_simp`. -/
theorem sum_inv_class_sub_log_ge {d r : ℕ} (hd : 0 < d) (hr : r < d) (N : ℕ) :
    (1 / (d : ℝ)) * Real.log N - (Real.log (2 * (d : ℝ)) + 2) / (d : ℝ)
      ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ) := by
  sorry

/-- **The class sum two-sided, at the crude constant.**  `|S_r(N) − (1/d)·log N| ≤ 3`.

Recipe (class B): `abs_le.mpr ⟨_, _⟩`.  Upper arm: `sum_inv_class_sub_log_le` and `1/d ≤ 1`
(`div_le_one_of_le₀`; `(1 : ℝ) ≤ d` by `exact_mod_cast hd`).  Lower arm:
`sum_inv_class_sub_log_ge` and `(Real.log (2d) + 2)/d ≤ 3`, from
`Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * d)` (`log 2d ≤ 2d − 1`) and
`div_le_iff₀ (by positivity)`, then `linarith`. -/
theorem abs_sum_inv_class_sub_log_le {d r : ℕ} (hd : 0 < d) (hr : r < d) (N : ℕ) :
    |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ))
        - (1 / (d : ℝ)) * Real.log N| ≤ 3 := by
  sorry

/-! ## The divisor count as `ρ(d)` class sums, and its two-sided estimate -/

/-- **The fiberwise split.**  `∑_{n ≤ N, d ∣ n(n+2)} 1/n = ∑_{r ∈ Rnat d} S_r(N)`, by
`dvd_iff_mem_Rnat` (`d ∣ n(n+2) ↔ n % d ∈ Rnat d`).

Recipe (class B): `symm`; `rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % d)
(t := Rnat d) (fun n hn => ?_)]` where the maps-to obligation is
`(dvd_iff_mem_Rnat d n).mp (Finset.mem_filter.mp hn).2`; then
`Finset.sum_congr rfl fun r hr => ?_` with the inner index sets equal by `ext n`,
`simp only [Finset.mem_filter]`, and `dvd_iff_mem_Rnat` again (`n % d = r ∈ Rnat d ⇒ d ∣ n(n+2)`).
If the fiberwise lemma is spelled differently in this mathlib, `Finset.sum_biUnion` over the
pairwise-disjoint classes (`Finset.filter_biUnion`-shaped ext) is the fallback. -/
theorem sum_inv_dvd_eq_sum_Rnat (d : ℕ) [NeZero d] (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ))
      = ∑ r ∈ Rnat d,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ) := by
  sorry

/-- **The divisor count two-sided.**  `|C_d − ν(d)·log N| ≤ 3·ρ(d)`, with
`ν(d) = ρ(d)/d` (`Salt.TwinSieve.nu_apply`) and `ρ(d) = |Rnat d|` (`Rnat_card`).

Recipe (class B): `haveI : NeZero d := ⟨hd.ne'⟩`;
`rw [sum_inv_dvd_eq_sum_Rnat, Salt.TwinSieve.nu_apply, ← Rnat_card]`; write
`((Rnat d).card : ℝ) / d * log N = ∑ r ∈ Rnat d, (1/d) * log N`
(`Finset.sum_const`, `nsmul_eq_mul`, `div_mul_eq_mul_div`, `ring`); `← Finset.sum_sub_distrib`;
`Finset.abs_sum_le_sum_abs` then `Finset.sum_le_sum` with `abs_sum_inv_class_sub_log_le hd`
at `r < d` from `Rnat_subset_range d hr` (`Finset.mem_range`); finish with
`Finset.sum_const`, `nsmul_eq_mul`, `mul_comm`. -/
theorem abs_sum_inv_dvd_sub_nu_log_le {d : ℕ} (hd : 0 < d) (N : ℕ) :
    |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ))
        - Salt.TwinSieve.nu d * Real.log N| ≤ 3 * (rho d : ℝ) := by
  sorry

/-! ## `hcount` discharged — the signed Möbius sum from below -/

/-- ⭐ **`hcount`, DISCHARGED.**  For every `P` and `N`,

    `(∑_{d∣P} μ(d)ν(d))·log N − 3·∑_{d∣P} ρ(d)  ≤  ∑_{d∣P} μ(d)·∑_{n ≤ N, d ∣ n(n+2)} 1/n` .

This is the consumer's binder `hcount` (`twinLogWeight_support_infinite_of_rate`,
`logSifted_lower_of_count_and_atoms`) at `Hmain N := (∑ μν)·log N − 3·∑ ρ`.  No squarefreeness is
needed: every `d ∈ P.divisors` is positive (`Nat.pos_of_mem_divisors`) and `|μ(d)| ≤ 1`.

Recipe (class B): `rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`;
`Finset.sum_le_sum fun d hd => ?_`; with `hd0 := Nat.pos_of_mem_divisors hd`,
`h := abs_sum_inv_dvd_sub_nu_log_le hd0 N` and `hμ : |(μ d : ℝ)| ≤ 1`
(`ArithmeticFunction.abs_moebius_le_one` cast: `Int.cast_abs`, `exact_mod_cast`), the goal
`μ d * ν d * log N − 3 * ρ d ≤ μ d * C_d` follows from
`μ d * (C_d − ν d * log N) ≥ −|μ d| * |C_d − ν d * log N| ≥ −3 ρ d`
(`neg_abs_le`, `abs_mul`, `mul_le_mul` on nonnegatives); `nlinarith [abs_nonneg …]` or the
explicit `le_trans` chain. -/
theorem moebius_sum_inv_dvd_ge (P N : ℕ) :
    (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d) * Real.log N
        - 3 * ∑ d ∈ P.divisors, (rho d : ℝ)
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
`moebius_sum_inv_dvd_ge`, `hgrow` is `le_rfl` at `c := ∑ μν` (positive by
`sum_divisors_moebius_twinNu_pos`) and `C := 3·∑ ρ`.

⛔ **Honest label.**  `hatom` — the full-range log-averaged two-point at every class mod `P` at a
common `N` — has NO producer in the corpus (fixed `z`: Tao Thm 1.2's quantifier; growing `z`: the
census's binder C, held by nobody), so this is the prize SHAPE with its last elementary gap
closed, not the prize.  Nothing bears on twin primes.

Recipe (class A):
`twinLogWeight_support_infinite_of_rate hP (c := ∑ d ∈ P.divisors, (μ d : ℝ) * nu d)
  (C := 3 * ∑ d ∈ P.divisors, (rho d : ℝ)) (sum_divisors_moebius_twinNu_pos P hP)
  (Hmain := fun N => (∑ …) * Real.log N - 3 * ∑ …) (fun N => moebius_sum_inv_dvd_ge P N) hatom
  (fun N => le_rfl)`. -/
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
`W·log N`, the composition only needs `|atom N| ≤ ε·log N + A` with `ε < W` — the consumer's
binder re-cut to the producer's conclusion (demand side first).  ⚖️ ADDED BEYOND THE EIGHT
commissioned rows, on the branch, for the helm to keep or strike: no new mathematics, one
re-composition. -/

/-- ⭐ **THE DIRECT ROAD AT ONE HYPOTHESIS, AT THE SOURCE's STRENGTH.**  If the atom mass is
`≤ ε·log N + A` with `ε < W = ∑_{d∣P} μ(d)ν(d)`, the `P`-rough parity survivors are INFINITE.
`twinLogWeight_support_infinite_of_atom` is the case `ε = 0`.

Recipe (class B — mirror `twinLogWeight_support_infinite_of_win`'s body): for each `N`,
`logSifted_lower_of_count_and_atoms hP (moebius_sum_inv_dvd_ge P N) (hatom N)` (its `A` is
generic, instantiate it at `ε * Real.log N + A`) gives
`W·log N − 3·∑ρ − (ε·log N + A) ≤ (sifted log mass at N)`, i.e. `(W − ε)·log N − (3∑ρ + A)`,
which is unbounded above by `hdiv_of_log_growth (sub_pos.mpr hε)` at `hgrow := le_rfl`; then
feed `support_infinite_of_partialSums_unbounded` exactly as `_of_win` does (the weight extended
by zero off the sifted set, the `n = 0` term vanishing, `N + 1` as the witness). -/
theorem twinLogWeight_support_infinite_of_atom_rate {P : ℕ} (hP : Squarefree P) {ε A : ℝ}
    (hε : ε < ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d)
    (hatom : ∀ N : ℕ, |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)|
          ≤ ε * Real.log N + A) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  sorry

end Salt.TwinBar
