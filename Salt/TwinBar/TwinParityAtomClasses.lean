/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.TwinBar.TwinParityCount

/-!
# The direct road's `hatom`, reduced to Tao Theorem 1.2 at full range — the demand side
(QUEUE P3 item 11, the design block of 2026-09-05; STATEMENT-ONLY at the freeze)

`twinLogWeight_support_infinite_of_atom_rate` (`TwinParityCount.lean`) carries ONE hypothesis,

    `hatom : ∀ N, |∑_{d∣P} μ(d)·∑_{n≤N, d∣n(n+2)} λ(n(n+2))/n| ≤ ε·log N + A`   (`ε < W`).

This module reduces it to the object the corpus's spine is built to produce — a logarithmically
averaged two-point Liouville correlation at an affine form — and states exactly what the supply
must deliver.  Three facts do the work, all elementary:

1. **The Möbius skeleton is the coprime set** (`sum_twinCoprime_eq_moebius_divisors`, reversed):
   the atom IS `∑_{n≤N, (n(n+2),P)=1} λ(n(n+2))/n`, and coprimality to `P` depends on `n mod P`
   alone, so the sum splits over the `|Adm(P)|` ADMISSIBLE CLASSES `r < P`, `(r(r+2),P) = 1`
   (`admClasses`, `sum_twinCoprime_eq_sum_admClasses`) — every piece at the SAME stride `P`,
   the same shift `2`, the same tolerance.  ⇒ the decomposition over divisors `d ∣ P` and their
   `ρ(d)` classes (the shape the 08/26 flag priced) is NOT the one to feed — but NOT because it
   overspends.  A class atom at stride `d` costs `ε_d/d`, not `ε_d`: on `n = dm + r` the weight
   `1/n` is `(1/d)·(1/m)` (§1(2), D4 below; the corpus's class-index normalisation,
   `AffineFork.lean:69`).  So the multi-stride spend is `S′(z) = (1/1000)·∏_{p≤z}(1 + ρ(p)/p²)`,
   and against `W = ∏(1 − ρ(p)/p)` it PASSES throughout the reachable range —
   `z = 7`: `W 0.071429`, `S′ 0.0017173`, ratio `41.6`; `11`: `0.058442 / 0.0017457 / 33.5`;
   `31`: `0.031046 / 0.0018033 / 17.2`; `97`: `0.019149 / 0.0018191 / 10.5`;
   `127`: `0.017141 / 0.0018209 / 9.41`; `131`: `0.016880 / 0.0018211 / 9.27` — and first fails
   only at `z = 3 607 187`.  ⚠ An earlier draft of this block priced each atom at `ε_d` rather
   than `ε_d/d` and reported a crossing at `z = 131`: every entry of that table reproduced, and
   the MEANING was wrong — the budget column used the corpus's normalisation and the table a
   counterfactual `1/(am+b)` one, which D4 two sections down refutes.  It also ran `d` out to
   `d ∣ primorial 131`, while beyond `d = 548` no atom has a supplier at all (the head that
   EXPORTS the pin carries `hah7 : log(a·h) ≤ 7`, `StrideEntropyReceipt.lean:74`).
   ⇒ THE REASON IS SHAPE, NOT BUDGET.  The class decomposition needs ONE stride, ONE tolerance
   and ONE common `N` across the `|Adm(P)|` classes; the divisor decomposition needs
   `2·3^{π(z)−1}` atoms at strides that mostly violate `hah7`.  Its own spend is
   `|Adm|·(1/(1000P))/P = W/(1000·P)` — below `W` at EVERY `P`
   (`card_admClasses_eq_mul_W`, `admClasses_budget_lt_W`), and `3.4·10⁻⁷` at `P = 210`.
2. **A class atom is Tao's affine form up to `O(1/P)`** (`class_sum_le_affine_form`): on
   `n = P·m + r` the weight `1/n` is `(1/P)·(1/m)` up to `∑_m r/(P·m·(Pm+r)) ≤ 2/P`, and the
   `m = 0` term is one summand of size `≤ 1`.  So the road reads Tao's normalisation
   `∑_m λ(Pm+r)λ(Pm+r+2)/m` with a `1/P` in front — the pinned `ε = 1/(500·P·2)` of the
   stride lane arrives as `1/(1000·P²)` per class.
3. **The demand object** (`AffFullRangeAt`): Tao 1.2 at `ω(x) = x` — the FULL-RANGE bound
   `|∑_{m≤M} λ(am+b)λ(am+b+h)/m| ≤ ε·log M + A` at one `(a,b,h)`, one `ε`, one `A`, every `M`
   (or, for the consumer, infinitely many `M` —
   `twinLogWeight_support_infinite_of_atom_rate_frequently` re-cuts the road to that).

`abs_sum_Icc_le_of_windows` is the bridge the supply will walk: windows `(x/ω, x]` at ONE width
`ω`, each bounded by `ε·log ω` at every scale `x ∈ [x₀, N]`, tile `[1, N]` with the tail below
`x₀` paid trivially — `|∑_{n≤N} f(n)/n| ≤ ε·log N + (ε·log ω + log x₀ + 1)`.  The corpus's
`¬ logChowlaFailsAff a b h ε x ω` IS the window bound at scale `x`; what the supply lacks today
is the SCALE quantifier (`∀ x` in a band, against the landed `∃ R`) — the design block's §3.

## Honest label

Every statement here is elementary (class A/B) and conditional or definitional; NONE produces
`hatom`.  The terminal this file aims at — `{n | twinLogWeight P n ≠ 0}.Infinite` at
`P = primorial z` — is the content the crown road ALREADY lands unconditionally at
`primorial z ≤ 548` (`zRough_oddOmega_infinite_primorial`, one class, no `hatom`): at fixed `z`
the direct road buys a SECOND PROOF and a kernel cross-check of the two roads, not new ground.
Nothing here bears on twin primes.  STATEMENT-ONLY at the freeze; `sorry` bodies carry the
recipes; the refuter pass precedes any executor.
-/

namespace Salt.TwinBar

open Finset

/-! ## §1 — the admissible classes and the class decomposition of the coprime set -/

/-- **D0 (def).**  The admissible classes mod `P`: residues `r < P` with `(r(r+2), P) = 1`.
At `P = 210` there are `15`; in general `|admClasses P| = P·W` (`card_admClasses_eq_mul_W`). -/
def admClasses (P : ℕ) : Finset ℕ :=
  (Finset.range P).filter (fun r => Nat.Coprime (r * (r + 2)) P)

/-- **D1 (class A).**  Coprimality of `n(n+2)` to `P` is a property of `n mod P`.

Recipe: `Nat.coprime_mul_iff_left` splits both sides into `Coprime n P ∧ Coprime (n+2) P` /
`Coprime (n % P) P ∧ Coprime (n % P + 2) P`; write `n = P * (n / P) + n % P` (`Nat.div_add_mod`)
and `n + 2 = P * (n / P) + (n % P + 2)`; each factor is `Nat.coprime_mul_left_add_left`
(an `Iff`: `Coprime (n * k + m) n ↔ Coprime m n`, the move of `coprime_twinProd_of_affine`,
`AffineFork.lean:225`). -/
theorem coprime_twinProd_iff_mod (P n : ℕ) :
    Nat.Coprime (n * (n + 2)) P ↔ Nat.Coprime ((n % P) * (n % P + 2)) P := by
  sorry

/-- **D2 (class B).**  The coprime-filtered sum splits over the admissible classes, fiberwise by
`n % P`.

Recipe: the idiom of `remLogCount_abs_le` (`TwinParitySieveLog.lean:291`, its `hfib`):
`Finset.sum_fiberwise_of_maps_to` with `g := (· % P)`, `t := admClasses P` (`maps_to` from
`Nat.mod_lt` + D1), then `Finset.sum_congr` and, per fiber, `ext n; simp only [Finset.mem_filter]`
with D1 closing `Coprime (n(n+2)) P ∧ n % P = r ↔ n % P = r ∧ r ∈ admClasses P`. -/
theorem sum_twinCoprime_eq_sum_admClasses (N P : ℕ) (hP : 0 < P) (w : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P), w n)
      = ∑ r ∈ admClasses P, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % P = r), w n := by
  sorry

/-- **D3 (class B/C) — THE COUNT, the finding's own statement.**  `|Adm(P)| = P·W` with
`W = ∑_{d∣P} μ(d)ν(d)`, for squarefree `P`.

Recipe: D2 at `N := P`, `w := 1` — each class has EXACTLY one member in `Icc 1 P`
(`P·0 + r` for `r ≥ 1`, and `P` itself for `r = 0`), so the left side is `|Adm|`; the skeleton
`sum_twinCoprime_eq_moebius_divisors P P hP 1` turns it into `∑_{d∣P} μ(d)·#{n ≤ P : d ∣ n(n+2)}`;
for `d ∣ P` each of the `ρ(d)` classes of `Rnat d` (`dvd_iff_mem_Rnat`, `Rnat_card`,
`Salt/Brun/M2.lean`) has exactly `P/d` members in `Icc 1 P`, so the count is `ρ(d)·P/d = P·ν(d)`
(`Salt.TwinSieve.nu d = rho d / d`).  Optional for the road (D7 uses only the bound D3′);
it is the statement of the budget identity `|Adm|·(1/(1000P))/P = W/(1000P)`. -/
theorem card_admClasses_eq_mul_W {P : ℕ} (hP : Squarefree P) :
    ((admClasses P).card : ℝ)
      = (P : ℝ) * ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d := by
  sorry

/-- **D3′ (class B).**  `W ≥ 1/P` for squarefree `P`: every factor `1 − ν(p) = 1 − ρ(p)/p` is at
least `1/p` (`ρ(2) = 1`, `ρ(p) = 2` at odd primes: `rho_two`, `rho_odd_prime`, `M2.lean:57,61`),
and `∏_{p∣P} 1/p = 1/P` at squarefree `P` (mathlib's product of `primeFactors` for a squarefree
number).

Recipe: `sum_divisors_moebius_twinNu_eq_W 1 P hP` (`TwinParitySieve.lean:1055`), unfold
`Salt.BrunLower.W` (`BrunLower/Defs.lean:274`: `∏_{p ∈ prodPrimes.primeFactors} (1 − nu p)`,
`twinParitySieve_prodPrimes : prodPrimes = P`), `Finset.prod_le_prod` termwise against
`fun p => 1 / (p : ℝ)`, then the squarefree product identity, cast. -/
theorem moebius_twinNu_sum_ge_inv {P : ℕ} (hP : Squarefree P) :
    1 / (P : ℝ) ≤ ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d := by
  sorry

/-- **D8 (class B) — THE BUDGET.**  At any per-class tolerance `ε < 1/P` (in Tao's `1/m`
normalisation), the classes' total `|Adm|·(ε/P)` sits below `W`.  At the stride lane's pin
`ε = 1/(500·P·2) = 1/(1000P)` this is `W/(1000P) < W` — with `1000·P` to spare, at EVERY `P`.

Recipe: `|Adm| ≤ P` (`Finset.card_filter_le`, `Finset.card_range`), so the left side is
`≤ P·(ε/P) = ε < 1/P ≤ W` (D3′). -/
theorem admClasses_budget_lt_W {P : ℕ} (hP : Squarefree P) {ε : ℝ} (hε : 0 ≤ ε)
    (hεP : ε < 1 / (P : ℝ)) :
    ((admClasses P).card : ℝ) * (ε / (P : ℝ))
      < ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d := by
  sorry

/-! ## §2 — a class atom is Tao's affine form, up to `O(1/P)` -/

/-- **D4 (class B — the hardest B here).**  On the class `n ≡ r (mod P)`, `n = P·m + r`: the sum
with weight `1/n` is `(1/P)·` the sum with weight `1/m`, up to `2/P + 1`.

Recipe: the class `{n ∈ Icc 1 N : n % P = r}` is the image of `{m : 1 ≤ P·m + r ≤ N}` under the
injective `m ↦ P·m + r` (`Finset.sum_image`; the range is `Icc 0 ((N − r)/P)` when `r ≤ N`,
empty otherwise — case on `r ≤ N`); the `m = 0` term (present iff `1 ≤ r`) has `|g r / r| ≤ 1`;
for `m ≥ 1`: `g(Pm+r)/(Pm+r) = (1/P)·g(Pm+r)/m − g(Pm+r)·r/(P·m·(Pm+r))` and
`∑_{m ≤ M} r/(P·m·(Pm+r)) ≤ (r/P²)·∑_{m≤M} 1/m² ≤ (r/P²)·2 ≤ 2/P` (`1/m² ≤ 1/(m−1) − 1/m` for
`m ≥ 2`, telescoping; `r < P`).  Triangle inequality (`abs_sub_le`, `Finset.abs_sum_le_sum_abs`). -/
theorem class_sum_le_affine_form {P r : ℕ} (hr : r < P) (N : ℕ) (g : ℕ → ℝ)
    (hg : ∀ n, |g n| ≤ 1) :
    |∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % P = r), g n / (n : ℝ)|
      ≤ (1 / (P : ℝ)) * |∑ m ∈ Finset.Icc 1 ((N - r) / P), g (P * m + r) / (m : ℝ)|
        + 2 / (P : ℝ) + 1 := by
  sorry

/-! ## §3 — the demand object: Tao Theorem 1.2 at `ω(x) = x` -/

/-- **D5 (def) — THE DEMAND.**  Tao 1509.05422 Theorem 1.2 at the affine forms `(am+b, am+b+h)`,
Liouville model, in its FULL-RANGE specialisation `ω(x) := x` (Tao's own, p. 3): the
logarithmically weighted two-point correlation over `m ≤ M` is at most `ε·log M + A`.  One
`(a, b, h)`, one tolerance `ε`, one constant `A`, one range `M`; the consumer quantifies `M`.
The corpus's spine states the WINDOWED form `¬ logChowlaFailsAff a b h ε x ω`
(`|∑_{x/ω<n≤x} … /n| ≤ ε·log ω`, `AffineFork.lean:69`) at ONE produced regime; this def is what
the windows must be assembled into (`abs_sum_Icc_le_of_windows`). -/
def AffFullRangeAt (a b h : ℕ) (ε A : ℝ) (M : ℕ) : Prop :=
  |∑ m ∈ Finset.Icc 1 M,
      (ArithmeticFunction.liouville (a * m + b) : ℝ)
        * (ArithmeticFunction.liouville (a * m + b + h) : ℝ) / (m : ℝ)|
    ≤ ε * Real.log (M : ℝ) + A

/-- **D6 (class B).**  A class atom of the road from the demand object at its class: on
`n = P·m + r`, `λ(n(n+2)) = λ(n)·λ(n+2)` (`ArithmeticFunction.liouville_apply_mul`, the move at
`TwinParitySieve.lean:857`) is the summand of `AffFullRangeAt P r 2` at `m`, and D4 pays the
weight change.  `log ((N − r)/P) ≤ log N` (`Nat.div_le_self`, `Nat.sub_le`, `Real.log_le_log`;
at `N = 0` both sides read `0 ≤ A/P + 2/P + 1`).  `|λ(k)| ≤ 1` for every `k`
(`ArithmeticFunction.liouville_apply`: `(−1)^Ω(k)` at `k ≠ 0`, `0` at `k = 0`). -/
theorem class_atom_le_of_affFullRange {P r : ℕ} (hr : r < P) {ε A : ℝ}
    (hε : 0 ≤ ε) (N : ℕ) (hfr : AffFullRangeAt P r 2 ε A ((N - r) / P)) :
    |∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % P = r),
        ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)|
      ≤ (ε / (P : ℝ)) * Real.log (N : ℝ) + (A / (P : ℝ) + 2 / (P : ℝ) + 1) := by
  sorry

/-- **D7 (class B) — `hatom` FROM THE DEMAND AT EVERY ADMISSIBLE CLASS, AT ONE `N`.**

Recipe: `← sum_twinCoprime_eq_moebius_divisors N P hP (fun n => λ(n(n+2))/n)`
(`TwinParitySieve.lean:723`), D2 (`Nat.pos_of_ne_zero hP.ne_zero`), `Finset.abs_sum_le_sum_abs`,
D6 per class
(`Rnat`-free: `r < P` from `Finset.mem_range` via `Finset.mem_filter`), `Finset.sum_le_sum`,
`Finset.sum_const`, `nsmul_eq_mul`. -/
theorem atom_abs_le_of_affFullRange_classes {P : ℕ} (hP : Squarefree P) {ε A : ℝ} (hε : 0 ≤ ε)
    (N : ℕ) (hall : ∀ r ∈ admClasses P, AffFullRangeAt P r 2 ε A ((N - r) / P)) :
    |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)|
      ≤ ((admClasses P).card : ℝ)
          * ((ε / (P : ℝ)) * Real.log (N : ℝ) + (A / (P : ℝ) + 2 / (P : ℝ) + 1)) := by
  sorry

/-! ## §4 — the consumer re-cut: infinitely many `N` suffice -/

/-- **D9 (class B) — THE CONSUMER, WEAKENED TO AN INFINITE SET OF SCALES.**
`twinLogWeight_support_infinite_of_atom_rate` reads `hatom` at ONE `N` per target `M` — the `N`
that `hdiv_of_log_growth` returns.  Since `N ↦ (W − ε)·log N − C` is monotone, every `N` past that
threshold serves, so `hatom` is needed only on an INFINITE set `S` of scales.  This is the
consumer's binder read against what a windowed supply can produce: a regime family gives a
scale per design constant, not every scale.

Recipe: mirror `_of_atom_rate` (`TwinParityCount.lean:186`):
`support_infinite_of_partialSums_unbounded` (`TwinParitySieve.lean:607`); for `M`,
`hdiv_of_log_growth (sub_pos.mpr hε) (A := 0)` gives `N₀` with `M < Hmain N₀`;
`hS.exists_gt N₀` (`Set.Infinite.exists_gt`, mathlib) gives `N ∈ S` with `N₀ < N`;
`Hmain N₀ ≤ Hmain N` by `Real.log_le_log`; then
`logSifted_lower_of_count_and_atoms hP (moebius_sum_inv_dvd_ge P N) (hatom N hN)` and
`log_natCast_le_sum_inv_Icc N`, `nlinarith`. -/
theorem twinLogWeight_support_infinite_of_atom_rate_frequently {P : ℕ} (hP : Squarefree P)
    {ε A : ℝ}
    (hε : ε < ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d)
    {S : Set ℕ} (hS : S.Infinite)
    (hatom : ∀ N ∈ S, |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)|
          ≤ ε * Real.log N + A) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  sorry

/-- **D10 (class B) — THE DEMAND, ASSEMBLED.**  Tao 1.2's full-range object at the stride `P`,
shift `2`, EVERY admissible class, at a common scale `N` along an infinite set of scales, at any
per-class tolerance `ε < 1/P` — the direct road's terminal follows.  At the stride lane's pin
`ε = 1/(1000P)` the hypothesis `hεP : ε < 1/P` holds with `1000×` to spare (`500×` for
`2/(1000P)`); the `1000·P` factor is `W` against the SPEND — that is D8's, at `:122`.

Recipe: D9 at `ε := |Adm|·(ε/P)`, `A := |Adm|·(A/P + 2/P + 1)`, `hε` from D8, `hatom` from D7. -/
theorem twinLogWeight_support_infinite_of_affFullRange {P : ℕ} (hP : Squarefree P) {ε A : ℝ}
    (hε : 0 ≤ ε) (hεP : ε < 1 / (P : ℝ)) {S : Set ℕ} (hS : S.Infinite)
    (hall : ∀ N ∈ S, ∀ r ∈ admClasses P, AffFullRangeAt P r 2 ε A ((N - r) / P)) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  sorry

/-- **D11 (class A).**  The `∀ N` form: D10 at `S := Set.univ` (`Set.infinite_univ`). -/
theorem twinLogWeight_support_infinite_of_affFullRange_all {P : ℕ} (hP : Squarefree P)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεP : ε < 1 / (P : ℝ))
    (hall : ∀ N : ℕ, ∀ r ∈ admClasses P, AffFullRangeAt P r 2 ε A ((N - r) / P)) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  sorry

/-! ## §5 — the bridge the supply walks: windows at one width tile the full range -/

/-- **D12 (class B) — WINDOWS TILE THE RANGE.**  If every window `(x/ω, x]` with `x ∈ [x₀, N]`
carries `|∑ f(n)/n| ≤ ε·log ω`, then the full range `[1, N]` carries `ε·log N` plus a constant:
the windows `x₀' = N, x₁ = N/ω, …` (ℕ-division) descend until the first `x_K < x₀`; there are
at most `log N / log ω + 1` of them (`ω^(K−1) ≤ N/x₀` since `x_{K−1} ≥ x₀`), and the tail
`∑_{n ≤ x_K} 1/n ≤ 1 + log x₀`.

Recipe: an auxiliary by induction on `K`: `∀ N, N < x₀ * ω ^ K → |S N| ≤ ε * K * log ω + (log x₀ +
1)` — at `K + 1`, either `N < x₀` (the tail, `Salt.TwinBar.sum_inv_Icc_le`, `Wall.lean:220`, `|f|
≤ 1`) or split `Icc 1 N = Icc 1 (N/ω) ∪ Ioc (N/ω) N` via `Finset.sum_Ioc_consecutive` (the
`to_additive` of `prod_Ioc_consecutive`, `BigOperators/Intervals.lean:61`) at `0 ≤ N/ω ≤ N`,
after `Finset.Icc 1 N = Finset.Ioc 0 N` in ℕ; the window bound at `x := N`, and the
hypothesis at `N/ω < x₀ * ω ^ K`
(`Nat.div_lt_iff_lt_mul`).  Then `K := Nat.log ω (N / x₀) + 1` (`Nat.lt_pow_succ_log_self`), and
`Nat.log ω (N/x₀) * log ω ≤ log (N/x₀) ≤ log N` (`Nat.pow_log_le_self`, `Real.log_le_log`). `N =
0`: the left side is `0`. -/
theorem abs_sum_Icc_le_of_windows {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {ω x₀ : ℕ} (hω : 2 ≤ ω)
    (hx₀ : 1 ≤ x₀) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
    (hwin : ∀ x : ℕ, x₀ ≤ x → x ≤ N →
      |∑ n ∈ Finset.Ioc (x / ω) x, f n / (n : ℝ)| ≤ ε * Real.log (ω : ℝ)) :
    |∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)|
      ≤ ε * Real.log (N : ℝ) + (ε * Real.log (ω : ℝ) + Real.log (x₀ : ℝ) + 1) := by
  sorry

end Salt.TwinBar
