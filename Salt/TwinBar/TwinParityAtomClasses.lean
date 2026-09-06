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
Nothing here bears on twin primes.  (Frozen statement-only 2026-09-05 18:1x; the lead's refuter
pass signed REPAIR-THEN-FIRE, no statement false; all 14 obligations PROVED 2026-09-05 21:3x, every
name `[propext, Classical.choice, Quot.sound]` and `coprime_twinProd_iff_mod` stronger still at
`[propext, Quot.sound]`.)
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
  have hn : P * (n / P) + n % P = n := Nat.div_add_mod n P
  have h1 : Nat.Coprime n P ↔ Nat.Coprime (n % P) P := by
    calc Nat.Coprime n P
        ↔ Nat.Coprime (P * (n / P) + n % P) P := by rw [hn]
      _ ↔ Nat.Coprime (n % P) P := Nat.coprime_mul_left_add_left (n % P) P (n / P)
  have h2 : Nat.Coprime (n + 2) P ↔ Nat.Coprime (n % P + 2) P := by
    calc Nat.Coprime (n + 2) P
        ↔ Nat.Coprime (P * (n / P) + (n % P + 2)) P := by rw [← Nat.add_assoc, hn]
      _ ↔ Nat.Coprime (n % P + 2) P := Nat.coprime_mul_left_add_left (n % P + 2) P (n / P)
  rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_left, h1, h2]

/-- **D2 (class B).**  The coprime-filtered sum splits over the admissible classes, fiberwise by
`n % P`.

Recipe: the idiom of `remLogCount_abs_le` (`TwinParitySieveLog.lean:291`, its `hfib`):
`Finset.sum_fiberwise_of_maps_to` with `g := (· % P)`, `t := admClasses P` (`maps_to` from
`Nat.mod_lt` + D1), then `Finset.sum_congr` and, per fiber, `ext n; simp only [Finset.mem_filter]`
with D1 closing `Coprime (n(n+2)) P ∧ n % P = r ↔ n % P = r ∧ r ∈ admClasses P`. -/
theorem sum_twinCoprime_eq_sum_admClasses (N P : ℕ) (hP : 0 < P) (w : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P), w n)
      = ∑ r ∈ admClasses P, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % P = r), w n := by
  classical
  have hmaps : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P),
      n % P ∈ admClasses P := by
    intro n hn
    rw [Finset.mem_filter] at hn
    simp only [admClasses, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hP, (coprime_twinProd_iff_mod P n).mp hn.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  refine Finset.sum_congr rfl fun r hr => ?_
  congr 1
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have hr' := hr
    simp only [admClasses, Finset.mem_filter, Finset.mem_range] at hr'
    rw [coprime_twinProd_iff_mod P n, h2]
    exact hr'.2

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
  classical
  have hP0 : P ≠ 0 := hP.ne_zero
  have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
  -- each admissible class meets `[1, P]` exactly once
  have hclass : ∀ r ∈ admClasses P,
      ((Finset.Icc 1 P).filter (fun n => n % P = r)) = {if r = 0 then P else r} := by
    intro r hr
    have hr' := hr
    simp only [admClasses, Finset.mem_filter, Finset.mem_range] at hr'
    have hrP : r < P := hr'.1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hn : n = P
      · subst hn
        rw [Nat.mod_self] at h3
        rw [if_pos h3.symm]
      · have hmod : n % P = n := Nat.mod_eq_of_lt (by omega)
        rw [hmod] at h3
        subst h3
        rw [if_neg (by omega)]
    · intro h
      subst h
      by_cases h0 : r = 0
      · rw [if_pos h0]
        exact ⟨⟨hPpos, le_rfl⟩, by rw [Nat.mod_self]; exact h0.symm⟩
      · rw [if_neg h0]
        exact ⟨⟨by omega, by omega⟩, Nat.mod_eq_of_lt hrP⟩
  have hD2 := sum_twinCoprime_eq_sum_admClasses P P hPpos (fun _ => (1 : ℝ))
  have hLHS := sum_twinCoprime_eq_moebius_divisors P P hP (fun _ => (1 : ℝ))
  have hRHS : (∑ r ∈ admClasses P,
      ∑ _n ∈ (Finset.Icc 1 P).filter (fun n => n % P = r), (1 : ℝ))
      = ((admClasses P).card : ℝ) := by
    have hone : ∀ r ∈ admClasses P,
        (∑ _n ∈ (Finset.Icc 1 P).filter (fun n => n % P = r), (1 : ℝ)) = 1 := by
      intro r hr
      rw [hclass r hr, Finset.sum_singleton]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcount : ∀ d ∈ P.divisors,
      (∑ _n ∈ (Finset.Icc 1 P).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ))
        = (P : ℝ) * Salt.TwinSieve.nu d := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    haveI : NeZero d := ⟨hd0.ne'⟩
    have hdvd : d ∣ P := (Nat.mem_divisors.mp hd).1
    have hset : (Finset.Icc 1 P).filter (fun n => d ∣ n * (n + 2))
        = (Finset.Icc 1 P).filter (fun n => n % d ∈ Rnat d) :=
      Finset.filter_congr (fun n _ => by
        simpa using dvd_iff_mem_Rnat d n)
    have h1 := congCount_telescoping d (Rnat d) hd0 (P / d) 0
    rw [Nat.add_zero, Nat.div_mul_cancel hdvd] at h1
    have h2 : congCount d (Rnat d) 0 = 0 := by
      unfold congCount
      rw [Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0)]
      simp
    rw [h2, Nat.add_zero] at h1
    unfold congCount at h1
    have hinter : Rnat d ∩ Finset.range d = Rnat d :=
      Finset.inter_eq_left.mpr (Rnat_subset_range d)
    rw [hinter, Rnat_card] at h1
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
    have hdivR : (((P / d : ℕ)) : ℝ) = (P : ℝ) / (d : ℝ) := Nat.cast_div hdvd hdR
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hset, h1, Nat.cast_mul, hdivR,
      Salt.TwinSieve.nu_apply]
    ring
  have hmain : ∀ d ∈ P.divisors,
      (ArithmeticFunction.moebius d : ℝ)
          * (∑ _n ∈ (Finset.Icc 1 P).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ))
        = (P : ℝ) * ((ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d) := by
    intro d hd
    rw [hcount d hd]; ring
  rw [← hRHS, ← hD2, hLHS, Finset.sum_congr rfl hmain, ← Finset.mul_sum]

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
  classical
  rw [sum_divisors_moebius_twinNu_eq_W 1 P hP]
  unfold Salt.BrunLower.W
  rw [twinParitySieve_prodPrimes, twinParitySieve_nu]
  have hprodP : ∏ p ∈ P.primeFactors, (p : ℝ) = (P : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hP]
  have hstep : ∀ p ∈ P.primeFactors, 1 / (p : ℝ) ≤ 1 - Salt.TwinSieve.nu p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    rw [Salt.TwinSieve.nu_apply]
    rcases eq_or_ne p 2 with rfl | hodd
    · rw [rho_two]; norm_num
    · rw [rho_odd_prime hpp hodd]
      have h3 : 3 ≤ p := by
        have h2 := hpp.two_le
        rcases hpp.eq_two_or_odd' with h | h
        · exact absurd h hodd
        · obtain ⟨k, hk⟩ := h; omega
      have h3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
      have hrw : (1 : ℝ) / (p : ℝ) + ((2 : ℕ) : ℝ) / (p : ℝ) = 3 / (p : ℝ) := by
        push_cast; ring
      rw [le_sub_iff_add_le, hrw, div_le_one hp0]
      linarith
  calc 1 / (P : ℝ) = ∏ p ∈ P.primeFactors, 1 / (p : ℝ) := by
        rw [Finset.prod_div_distrib, Finset.prod_const_one, hprodP]
    _ ≤ ∏ p ∈ P.primeFactors, (1 - Salt.TwinSieve.nu p) :=
        Finset.prod_le_prod (fun p _ => by positivity) hstep

/-- **D8 (class B) — THE BUDGET.**  At any per-class tolerance `ε < 1/P` (in Tao's `1/m`
normalisation), the classes' total `|Adm|·(ε/P)` sits below `W`.  At the stride lane's pin
`ε = 1/(500·P·2) = 1/(1000P)` this is `W/(1000P) < W` — with `1000·P` to spare, at EVERY `P`.

Recipe: `|Adm| ≤ P` (`Finset.card_filter_le`, `Finset.card_range`), so the left side is
`≤ P·(ε/P) = ε < 1/P ≤ W` (D3′). -/
theorem admClasses_budget_lt_W {P : ℕ} (hP : Squarefree P) {ε : ℝ} (hε : 0 ≤ ε)
    (hεP : ε < 1 / (P : ℝ)) :
    ((admClasses P).card : ℝ) * (ε / (P : ℝ))
      < ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * Salt.TwinSieve.nu d := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  have hcard : ((admClasses P).card : ℝ) ≤ (P : ℝ) := by
    have hle : (admClasses P).card ≤ P := by
      calc (admClasses P).card ≤ (Finset.range P).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = P := Finset.card_range P
    exact_mod_cast hle
  have h1 : ((admClasses P).card : ℝ) * (ε / (P : ℝ)) ≤ (P : ℝ) * (ε / (P : ℝ)) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have h2 : (P : ℝ) * (ε / (P : ℝ)) = ε := by field_simp
  have h3 := moebius_twinNu_sum_ge_inv hP
  linarith

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
  have hP : 0 < P := lt_of_le_of_lt (Nat.zero_le r) hr
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hrPR : (r : ℝ) ≤ (P : ℝ) := by exact_mod_cast hr.le
  set M : ℕ := (N - r) / P with hMdef
  set A : Finset ℕ := (Finset.Icc 1 M).image (fun m => P * m + r) with hAdef
  set C : Finset ℕ := (Finset.Icc 1 N).filter (fun n => n % P = r) with hCdef
  have hAC : A ⊆ C := by
    intro n hn
    rw [hAdef, Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    rw [Finset.mem_Icc] at hm
    have hmpos : 1 ≤ m := hm.1
    have hmM : m ≤ M := hm.2
    have hM1 : 1 ≤ M := le_trans hmpos hmM
    have hNr : P ≤ N - r := by
      rw [hMdef] at hM1
      exact (Nat.one_le_div_iff hP).mp hM1
    have hPM : P * M ≤ N - r := by
      calc P * M = M * P := Nat.mul_comm _ _
        _ = (N - r) / P * P := by rw [hMdef]
        _ ≤ N - r := Nat.div_mul_le_self _ _
    rw [hCdef, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc 1 = 1 * 1 := by norm_num
        _ ≤ P * m := Nat.mul_le_mul hP hmpos
        _ ≤ P * m + r := Nat.le_add_right _ _
    · calc P * m + r ≤ P * M + r := Nat.add_le_add_right (Nat.mul_le_mul (le_refl P) hmM) r
        _ ≤ (N - r) + r := Nat.add_le_add_right hPM r
        _ = N := by omega
    · rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hr
  have hdiff : C \ A ⊆ {r} := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨hnC, hnA⟩ := hn
    have hnC' := hnC
    rw [hCdef, Finset.mem_filter, Finset.mem_Icc] at hnC'
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hnC'
    rw [Finset.mem_singleton]
    have hne : P * (n / P) + n % P = n := Nat.div_add_mod n P
    rw [hn3] at hne
    by_contra hcon
    have hq1 : 1 ≤ n / P := by
      rcases Nat.eq_zero_or_pos (n / P) with h0 | h0
      · exfalso; apply hcon
        rw [h0, Nat.mul_zero, Nat.zero_add] at hne
        exact hne.symm
      · exact h0
    have hPq : P * (n / P) ≤ N - r := by
      refine Nat.le_sub_of_add_le ?_
      rw [hne]; exact hn2
    have hqM : n / P ≤ M := by
      rw [hMdef, Nat.le_div_iff_mul_le hP]
      calc n / P * P = P * (n / P) := Nat.mul_comm _ _
        _ ≤ N - r := hPq
    exact hnA (by
      rw [hAdef, Finset.mem_image]
      exact ⟨n / P, Finset.mem_Icc.mpr ⟨hq1, hqM⟩, hne⟩)
  have htail : |∑ n ∈ C \ A, g n / (n : ℝ)| ≤ 1 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hb : ∀ n ∈ C \ A, |g n / (n : ℝ)| ≤ 1 := by
      intro n hn
      have hnC := (Finset.mem_sdiff.mp hn).1
      rw [hCdef, Finset.mem_filter, Finset.mem_Icc] at hnC
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnC.1.1
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      rw [abs_div, abs_of_nonneg hnpos.le, div_le_one hnpos]
      have := hg n
      linarith
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hb) ?_
    have hcard : (C \ A).card ≤ 1 := by
      calc (C \ A).card ≤ ({r} : Finset ℕ).card := Finset.card_le_card hdiff
        _ = 1 := Finset.card_singleton r
    simp only [nsmul_eq_mul, mul_one]
    exact_mod_cast hcard
  have hinj : ∀ x ∈ Finset.Icc 1 M, ∀ y ∈ Finset.Icc 1 M,
      P * x + r = P * y + r → x = y := by
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left hP (Nat.add_right_cancel h)
  have hAsum : ∑ n ∈ A, g n / (n : ℝ)
      = ∑ m ∈ Finset.Icc 1 M, g (P * m + r) / ((P * m + r : ℕ) : ℝ) := by
    rw [hAdef]
    exact Finset.sum_image hinj
  have hsqbound : ∀ K : ℕ,
      ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 - 1 / (K : ℝ) := by
    intro K
    induction K with
    | zero =>
      rw [Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0), Finset.sum_empty]
      norm_num
    | succ K ih =>
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), hcast]
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · subst hK0
        rw [Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0), Finset.sum_empty]
        norm_num
      · have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
        have hK0' : (0 : ℝ) < (K : ℝ) := by linarith
        have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by linarith
        have hstep : (1 : ℝ) / ((K : ℝ) + 1) ^ 2
            ≤ 1 / (K : ℝ) - 1 / ((K : ℝ) + 1) := by
          rw [div_sub_div _ _ (ne_of_gt hK0') (ne_of_gt hK1),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  have hsq : ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
    have h := hsqbound M
    have h2 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  have hcompare : |(∑ m ∈ Finset.Icc 1 M, g (P * m + r) / ((P * m + r : ℕ) : ℝ))
      - 1 / (P : ℝ) * ∑ m ∈ Finset.Icc 1 M, g (P * m + r) / (m : ℝ)| ≤ 2 / (P : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ m ∈ Finset.Icc 1 M,
        |g (P * m + r) / ((P * m + r : ℕ) : ℝ) - 1 / (P : ℝ) * (g (P * m + r) / (m : ℝ))|
          ≤ (r : ℝ) / ((P : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
      have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
      have hcast : ((P * m + r : ℕ) : ℝ) = (P : ℝ) * (m : ℝ) + (r : ℝ) := by push_cast; ring
      have hd1 : (0 : ℝ) < (P : ℝ) * (m : ℝ) + (r : ℝ) := by positivity
      have hd2 : (0 : ℝ) < ((P : ℝ) * (m : ℝ) + (r : ℝ)) * ((P : ℝ) * (m : ℝ)) := by positivity
      have hpos2 : (0 : ℝ) < (P : ℝ) ^ 2 * (m : ℝ) ^ 2 := by positivity
      have hne1 : ((P : ℝ) * (m : ℝ) + (r : ℝ)) ≠ 0 := ne_of_gt hd1
      have hnePR : (P : ℝ) ≠ 0 := ne_of_gt hPR
      have hnemR : (m : ℝ) ≠ 0 := ne_of_gt hmpos
      rw [hcast]
      have hkey : g (P * m + r) / ((P : ℝ) * (m : ℝ) + (r : ℝ))
            - 1 / (P : ℝ) * (g (P * m + r) / (m : ℝ))
          = g (P * m + r)
              * (-(r : ℝ) / (((P : ℝ) * (m : ℝ) + (r : ℝ)) * ((P : ℝ) * (m : ℝ)))) := by
        field_simp
        ring
      rw [hkey, abs_mul]
      have habs : |(-(r : ℝ) / (((P : ℝ) * (m : ℝ) + (r : ℝ)) * ((P : ℝ) * (m : ℝ))))|
          = (r : ℝ) / (((P : ℝ) * (m : ℝ) + (r : ℝ)) * ((P : ℝ) * (m : ℝ))) := by
        rw [abs_div, abs_neg, abs_of_nonneg hr0, abs_of_nonneg hd2.le]
      rw [habs]
      have hb2 : (r : ℝ) / (((P : ℝ) * (m : ℝ) + (r : ℝ)) * ((P : ℝ) * (m : ℝ)))
          ≤ (r : ℝ) / ((P : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hd2 hpos2]
        nlinarith [mul_nonneg (mul_nonneg hr0 hPR.le) hmpos.le, hr0, hPR.le, hmpos.le,
          mul_pos hPR hmpos]
      calc |g (P * m + r)|
            * ((r : ℝ) / (((P : ℝ) * (m : ℝ) + (r : ℝ)) * ((P : ℝ) * (m : ℝ))))
          ≤ 1 * ((r : ℝ) / ((P : ℝ) ^ 2 * (m : ℝ) ^ 2)) :=
            mul_le_mul (hg _) hb2 (by positivity) (by norm_num)
        _ = (r : ℝ) / ((P : ℝ) ^ 2 * (m : ℝ) ^ 2) := one_mul _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hrewrite : ∑ m ∈ Finset.Icc 1 M, (r : ℝ) / ((P : ℝ) ^ 2 * (m : ℝ) ^ 2)
        = ((r : ℝ) / (P : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hrewrite]
    have h1 : ((r : ℝ) / (P : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ^ 2
        ≤ ((r : ℝ) / (P : ℝ) ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : ((r : ℝ) / (P : ℝ) ^ 2) * 2 ≤ 2 / (P : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hPR]
      nlinarith
    linarith
  have hsplitC : ∑ n ∈ C, g n / (n : ℝ)
      = (∑ n ∈ C \ A, g n / (n : ℝ)) + ∑ n ∈ A, g n / (n : ℝ) :=
    (Finset.sum_sdiff hAC).symm
  rw [hsplitC, hAsum]
  set X : ℝ := ∑ m ∈ Finset.Icc 1 M, g (P * m + r) / ((P * m + r : ℕ) : ℝ) with hXdef
  set Y : ℝ := ∑ m ∈ Finset.Icc 1 M, g (P * m + r) / (m : ℝ) with hYdef
  set T : ℝ := ∑ n ∈ C \ A, g n / (n : ℝ) with hTdef
  have habs1 : |X| - |1 / (P : ℝ) * Y| ≤ |X - 1 / (P : ℝ) * Y| :=
    abs_sub_abs_le_abs_sub _ _
  have habs2 : |1 / (P : ℝ) * Y| = 1 / (P : ℝ) * |Y| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (P : ℝ))]
  have hfinal : |T + X| ≤ |T| + |X| := abs_add_le _ _
  rw [habs2] at habs1
  linarith [htail, hcompare, habs1, hfinal]

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
  have hP : 0 < P := lt_of_le_of_lt (Nat.zero_le r) hr
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hD4 := class_sum_le_affine_form hr N
    (fun n => ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ))
    (fun n => liouville_real_abs_le _)
  unfold AffFullRangeAt at hfr
  have heqsum : (∑ m ∈ Finset.Icc 1 ((N - r) / P),
        ((ArithmeticFunction.liouville ((P * m + r) * (P * m + r + 2)) : ℤ) : ℝ) / (m : ℝ))
      = ∑ m ∈ Finset.Icc 1 ((N - r) / P),
        ((ArithmeticFunction.liouville (P * m + r) : ℤ) : ℝ)
          * ((ArithmeticFunction.liouville (P * m + r + 2) : ℤ) : ℝ) / (m : ℝ) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ArithmeticFunction.liouville_apply_mul, Int.cast_mul]
  rw [heqsum] at hD4
  have hMN : (N - r) / P ≤ N := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlog : Real.log ((((N - r) / P : ℕ)) : ℝ) ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos ((N - r) / P) with h | h
    · rw [h]; simpa using hlogN
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hMN)
  have hstep := mul_le_mul_of_nonneg_left hlog hε
  have hbound : |∑ m ∈ Finset.Icc 1 ((N - r) / P),
        ((ArithmeticFunction.liouville (P * m + r) : ℤ) : ℝ)
          * ((ArithmeticFunction.liouville (P * m + r + 2) : ℤ) : ℝ) / (m : ℝ)|
      ≤ ε * Real.log (N : ℝ) + A := by linarith
  have hkey : 1 / (P : ℝ) * |∑ m ∈ Finset.Icc 1 ((N - r) / P),
        ((ArithmeticFunction.liouville (P * m + r) : ℤ) : ℝ)
          * ((ArithmeticFunction.liouville (P * m + r + 2) : ℤ) : ℝ) / (m : ℝ)|
      ≤ ε / (P : ℝ) * Real.log (N : ℝ) + A / (P : ℝ) := by
    calc 1 / (P : ℝ) * |∑ m ∈ Finset.Icc 1 ((N - r) / P),
            ((ArithmeticFunction.liouville (P * m + r) : ℤ) : ℝ)
              * ((ArithmeticFunction.liouville (P * m + r + 2) : ℤ) : ℝ) / (m : ℝ)|
        ≤ 1 / (P : ℝ) * (ε * Real.log (N : ℝ) + A) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ε / (P : ℝ) * Real.log (N : ℝ) + A / (P : ℝ) := by ring
  linarith

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
  classical
  have hP0 : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
  rw [← sum_twinCoprime_eq_moebius_divisors N P hP,
    sum_twinCoprime_eq_sum_admClasses N P hP0]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hb : ∀ r ∈ admClasses P,
      |∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % P = r),
          ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)|
        ≤ (ε / (P : ℝ)) * Real.log (N : ℝ) + (A / (P : ℝ) + 2 / (P : ℝ) + 1) := by
    intro r hr
    have hr' := hr
    simp only [admClasses, Finset.mem_filter, Finset.mem_range] at hr'
    exact class_atom_le_of_affFullRange hr'.1 hε N (hall r hr)
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

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
  have hW := sum_divisors_moebius_twinNu_pos P hP
  refine support_infinite_of_partialSums_unbounded (twinLogWeight_nonneg P) fun M => ?_
  obtain ⟨N₀, hN₀⟩ := hdiv_of_log_growth (sub_pos.mpr hε) (A := 0)
    (Hmain := fun N => (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * Salt.TwinSieve.nu d - ε) * Real.log (N : ℝ)
      - (4 * ∑ d ∈ P.divisors, (rho d : ℝ) + A)) (fun N => le_rfl) M
  obtain ⟨N, hNS, hNgt⟩ := hS.exists_gt N₀
  refine ⟨N + 1, ?_⟩
  rw [sum_twinLogWeight_range]
  have h := logSifted_lower_of_count_and_atoms hP (moebius_sum_inv_dvd_ge P N) (hatom N hNS)
  have hlog := mul_le_mul_of_nonneg_left (log_natCast_le_sum_inv_Icc N) hW.le
  have hmono : Real.log (N₀ : ℝ) ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N₀ with h0 | h0
    · have hN1 : 1 ≤ N := by omega
      rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast hN1)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hNgt.le)
  have hprod := mul_le_mul_of_nonneg_left hmono (sub_pos.mpr hε).le
  simp only [sub_zero] at hN₀
  linarith

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
  refine twinLogWeight_support_infinite_of_atom_rate_frequently hP
    (ε := ((admClasses P).card : ℝ) * (ε / (P : ℝ)))
    (A := ((admClasses P).card : ℝ) * (A / (P : ℝ) + 2 / (P : ℝ) + 1))
    (admClasses_budget_lt_W hP hε hεP) hS ?_
  intro N hN
  calc |∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ)
        * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
            ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)|
      ≤ ((admClasses P).card : ℝ)
          * ((ε / (P : ℝ)) * Real.log (N : ℝ) + (A / (P : ℝ) + 2 / (P : ℝ) + 1)) :=
        atom_abs_le_of_affFullRange_classes hP hε N (hall N hN)
    _ = ((admClasses P).card : ℝ) * (ε / (P : ℝ)) * Real.log (N : ℝ)
          + ((admClasses P).card : ℝ) * (A / (P : ℝ) + 2 / (P : ℝ) + 1) := by ring

/-- **D11 (class A).**  The `∀ N` form: D10 at `S := Set.univ` (`Set.infinite_univ`). -/
theorem twinLogWeight_support_infinite_of_affFullRange_all {P : ℕ} (hP : Squarefree P)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεP : ε < 1 / (P : ℝ))
    (hall : ∀ N : ℕ, ∀ r ∈ admClasses P, AffFullRangeAt P r 2 ε A ((N - r) / P)) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  exact twinLogWeight_support_infinite_of_affFullRange hP hε hεP Set.infinite_univ
    (fun N _ => hall N)

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
  have hω0 : 0 < ω := by omega
  have hω1 : 1 < ω := by omega
  have hωR : (1 : ℝ) < (ω : ℝ) := by exact_mod_cast hω1
  have hlogω : (0 : ℝ) ≤ Real.log (ω : ℝ) := Real.log_nonneg hωR.le
  have hx₀R : (1 : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast hx₀
  have hlogx₀ : (0 : ℝ) ≤ Real.log (x₀ : ℝ) := Real.log_nonneg hx₀R
  have hIcc : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := by
    intro n; ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have htail : ∀ n : ℕ, |∑ k ∈ Finset.Icc 1 n, f k / (k : ℝ)| ≤ 1 + Real.log (n : ℝ) := by
    intro n
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) (Salt.TwinBar.sum_inv_Icc_le n)
    rw [Finset.mem_Icc] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have h1 : |f k / (k : ℝ)| = |f k| * ((k : ℝ))⁻¹ := by
      rw [abs_div, abs_of_nonneg hk0.le, div_eq_mul_inv]
    rw [h1]
    have h2 : |f k| * ((k : ℝ))⁻¹ ≤ 1 * ((k : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right (hf k) (by positivity)
    linarith
  have hlogmono : ∀ a b : ℕ, a ≤ b → Real.log (a : ℝ) ≤ Real.log (b : ℝ) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      rcases Nat.eq_zero_or_pos b with h1 | h1
      · rw [h1]; simp
      · exact Real.log_nonneg (by exact_mod_cast h1)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hab)
  have aux : ∀ K : ℕ, ∀ N' : ℕ, N' ≤ N → N' < x₀ * ω ^ K →
      |∑ n ∈ Finset.Icc 1 N', f n / (n : ℝ)|
        ≤ ε * (K : ℝ) * Real.log (ω : ℝ) + (Real.log (x₀ : ℝ) + 1) := by
    intro K
    induction K with
    | zero =>
      intro N' _ hlt
      rw [pow_zero, Nat.mul_one] at hlt
      have h1 := htail N'
      have h2 : Real.log (N' : ℝ) ≤ Real.log (x₀ : ℝ) := hlogmono _ _ hlt.le
      simp only [Nat.cast_zero, mul_zero, zero_mul]
      linarith
    | succ K ih =>
      intro N' hN'N hlt
      by_cases hcase : N' < x₀
      · have h1 := htail N'
        have h2 : Real.log (N' : ℝ) ≤ Real.log (x₀ : ℝ) := hlogmono _ _ hcase.le
        have h3 : (0 : ℝ) ≤ ε * ((K : ℝ) + 1) * Real.log (ω : ℝ) :=
          mul_nonneg (mul_nonneg hε (by positivity)) hlogω
        push_cast
        linarith
      · replace hcase : x₀ ≤ N' := Nat.not_lt.mp hcase
        have hdivlt : N' / ω < x₀ * ω ^ K := by
          rw [Nat.div_lt_iff_lt_mul hω0]
          calc N' < x₀ * ω ^ (K + 1) := hlt
            _ = x₀ * ω ^ K * ω := by ring
        have hdivle : N' / ω ≤ N := le_trans (Nat.div_le_self _ _) hN'N
        have hih := ih (N' / ω) hdivle hdivlt
        rw [hIcc (N' / ω)] at hih
        have hw := hwin N' hcase hN'N
        have hsplit : ((∑ n ∈ Finset.Ioc 0 (N' / ω), f n / (n : ℝ))
            + ∑ n ∈ Finset.Ioc (N' / ω) N', f n / (n : ℝ))
            = ∑ n ∈ Finset.Ioc 0 N', f n / (n : ℝ) :=
          Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.div_le_self _ _)
        rw [hIcc N', ← hsplit]
        refine le_trans (abs_add_le _ _) ?_
        push_cast
        linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [hN0, Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0), Finset.sum_empty, abs_zero]
    simp only [Nat.cast_zero, Real.log_zero, mul_zero, zero_add]
    have := mul_nonneg hε hlogω
    linarith
  · have hNlt : N < x₀ * ω ^ (Nat.log ω (N / x₀) + 1) := by
      have h1 : N / x₀ < ω ^ (Nat.log ω (N / x₀) + 1) :=
        Nat.lt_pow_succ_log_self hω1 (N / x₀)
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < x₀)] at h1
      calc N < ω ^ (Nat.log ω (N / x₀) + 1) * x₀ := h1
        _ = x₀ * ω ^ (Nat.log ω (N / x₀) + 1) := by ring
    have haux := aux (Nat.log ω (N / x₀) + 1) N le_rfl hNlt
    have hLlog : ((Nat.log ω (N / x₀) : ℕ) : ℝ) * Real.log (ω : ℝ) ≤ Real.log (N : ℝ) := by
      rcases Nat.eq_zero_or_pos (N / x₀) with h0 | h0
      · rw [h0, Nat.log_zero_right]
        simp only [Nat.cast_zero, zero_mul]
        exact Real.log_nonneg (by exact_mod_cast hNpos)
      · have hple : ω ^ Nat.log ω (N / x₀) ≤ N / x₀ :=
          Nat.pow_log_le_self ω h0.ne'
        have hple2 : ω ^ Nat.log ω (N / x₀) ≤ N :=
          le_trans hple (Nat.div_le_self _ _)
        have h1 := hlogmono _ _ hple2
        rw [Nat.cast_pow, Real.log_pow] at h1
        exact h1
    have hfin : ε * (((Nat.log ω (N / x₀) : ℕ) : ℝ) + 1) * Real.log (ω : ℝ)
        ≤ ε * Real.log (N : ℝ) + ε * Real.log (ω : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hLlog hε
      nlinarith [h]
    push_cast at haux
    linarith

end Salt.TwinBar
