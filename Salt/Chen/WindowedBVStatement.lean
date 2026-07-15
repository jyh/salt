/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SqrtDFold

/-!
# Q4 — the windowed Bombieri–Vinogradov variant, stated for an outside reader

This file is a **STATEMENT-AND-DOCSTRING** repackaging (part of the salt exploration sprint,
`docs/exploration/preregistration.md`, question Q4).  It introduces **no new mathematics**: the
two theorems below are proved by a *single direct application* (`exact`) of the two landed
terminals of the windowed/cutoff Bombieri–Vinogradov chain,

* `Salt.Chen.general_BV_cutoff_sqrtD`          (`Salt/Chen/SqrtDFold.lean`, the √D-fold form), and
* `Salt.Chen.general_BV_cutoff_unconditional`  (`Salt/Chen/WindowSmallChi.lean`, the `D < N` form).

The point is a clean, literature-facing restatement — one theorem carries the honest general
mechanism (the √D structural level), the other is the recognizable textbook-shape corollary at the
smaller level `D < N` — so the variant can be compared against the published Bombieri–Vinogradov
literature.

## What the chain proves, in classical notation

Fix `A > 0`.  Let `α = (α_m)_{m≥1}` be a bounded coefficient sequence, `‖α‖_∞ ≤ 1`, and let

  `1_{P>N}(n) := [ n prime and n > N ]`      (the **block-prime indicator** on `(N, ∞)`)

be the inner factor.  Form the **bilinear, windowed** sequence indexed by the product `mn`, carrying
the *sharp window cutoff* `mn ≤ T` inside the summation.  For a modulus `d` and a residue class
`a = r(d)` coprime to `d`, the windowed arithmetic-progression discrepancy at residue `a mod d` is

```
  Δ(d) :=   ∑_{m≤X} ∑_{n≤M : mn≤T,  mn ≡ a (mod d)}  α_m · 1_{P>N}(n)
          − (1/φ(d)) · ∑_{m≤X} ∑_{n≤M : mn≤T,  gcd(mn,d)=1}  α_m · 1_{P>N}(n)
```

(this is `apDiscBilinCutoff α (blockPrimeInd N) X M a d T`).  The theorems bound the level-`D`
mean of `|Δ(d)|` over a set `𝒟 ⊆ [1, D]` of moduli:

```
  ∑_{d ∈ 𝒟}  |Δ(d)|   ≤   C_A · X·M / (log(XM))^A ,
```

with a **fully explicit** constant (no `O`/`≪` — see below), valid at level

```
  D  ≤  √(XM) / (log(XM))^B          (any B ≥ A + 2).
```

### The four distinctive features (the combination is the Q4 question)

1. **Windowed / cutoff carrier (native `mn ≤ T`).**  The sharp window rides *unfactored* inside the
   twisted character sum.  A classical bilinear form `∑ α_m β_n χ(m)χ(n)` factors as `A(χ)·B(χ)`;
   here the cutoff couples `m` and `n`, so the twist `cutoffTwist` does **not** factor.  The whole
   machinery (`WindowBV`…`WindowSmallChi`) is built to price the *unfactored* windowed twist.

2. **Explicit constants.**  The envelope constant is the closed form
   `Kβ + ( 6·(Km + 448 + 32·√26) + Kerr )`, with the error-side constant
   `Kerr = 2^{A+5}·Kβ' + 15360 (+ 1)` — the `+ 1` present only in the √D form (the absorbed
   β-crumb).  `Kβ, Km, Kβ'` are the explicit Siegel–Walfisz coupling constants supplied at the three
   `hcoupG / hcoup3 / herr_book4` slots.  `448`, `32√26`, `15360` are the frozen slack-budget
   constants of the cutoff/e-fold assembly (the Chen `C0`-doctrine budget ledger).

3. **The √D structural level (`D < (N+1)²`, replacing `D < N`).**  The honest mechanism is not the
   naive `D < N` but the block-prime fact that *at most one* prime `> √d` divides any `d ≤ D`
   (`two_sqrt_primes_not_both_dvd`): under `D < (N+1)²` the imprimitive→primitive fold leaves a
   *single-term* β-crumb, absorbed by the extra row `4(1+log D)·D ≤ N·M/(log XM)^A` at cost `+1`.
   This lets the level reach `√(XM)/(log)^B` with the block primes living only up to `N ≈ √D`.

4. **The `D0`-window at decoupled exponents.**  Small conductors `f ≤ D0` are handled by a
   χ-level interval-Siegel–Walfisz transpose (`hSmallCut_discharge`) at the small-conductor exponent
   `C0`, *decoupled* from the T4-tail exponent `A+2` (the two are coupled only through
   `D0 = 2^{k0}`, `(log XM)^{A+2} ≤ 2·2^{k0}`, `D0 ≤ (log XM)^{C0}`, `D0 ≤ (log N)^{C0}`).  Coupling
   both at `C0` empties the `D0`-window at boundary boxes — this decoupling is catch #64.

### The sequence class

`α_m · 1_{P>N}(n)` is exactly the **Type-II (bilinear) shape** that drives Chen's theorem and the
linear sieve remainder: a bounded coefficient times a *prime* indicator, i.e. an almost-prime /
semiprime-flavored sequence — **not** the von Mangoldt function `Λ` itself.  This is the sequence
class the classical "BV for bilinear forms / BV for sequences" literature addresses; the Q4
literature sweep compares against Bombieri–Friedlander–Iwaniec, Fouvry(–Iwaniec), Fouvry–Radziwiłł,
Drappeau, and the explicit-constants line (Akbary–Hambrook).
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-- **The windowed bilinear Bombieri–Vinogradov theorem — general form (√D level).**

A clean restatement of `Salt.Chen.general_BV_cutoff_sqrtD`, proved by direct application (no new
math).  For a bounded coefficient sequence `α` and the block-prime indicator `blockPrimeInd N`
(primes in `(N, ∞)`), the level-`D` mean of the windowed AP discrepancy
`apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T` — with the sharp window `mn ≤ T` unfactored
inside the twist — is bounded by `C_A · XM/(log XM)^A`, at level `D ≤ √(XM)/(log XM)^B`, with the
**explicit** constant `Kβ + (6(Km + 448 + 32√26) + (2^{A+5}Kβ' + 15360 + 1))`.

This is the *honest* form: the level condition is the block-prime structural bound `D < (N+1)²`
(feature 3), and the extra row `4(1+log D)·D ≤ N·M/(log XM)^A` (`habs`) absorbs the single-term
β-crumb — the two hypotheses that carry the "block-prime support" structure and make this the
general, but hypothesis-heavy, statement.  For the recognizable textbook shape at the smaller level
`D < N` (no crumb row, constant without the `+ 1`) see `windowed_bilinear_BV_below_N` below.

All hypotheses beyond `hA, hC0` are structural / operating-point thresholds and the three
Siegel–Walfisz couplings (in the exposed constant `K`); no analytic slot remains open. -/
theorem windowed_bilinear_BV_sqrtD {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (Kβ Km Kβ' B : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < (N + 1) * (N + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ (N : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D →
            (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0) ≤ Km * (Real.log N) ^ (A + 2 * C0)) →
        (∀ e, 2 ≤ e → e ≤ D →
            K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
              ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ (A + 5) * Kβ' + 15360 + 1))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A :=
  general_BV_cutoff_sqrtD hA hC0

/-- **The windowed bilinear Bombieri–Vinogradov theorem — clean corollary (level `D < N`).**

A clean restatement of `Salt.Chen.general_BV_cutoff_unconditional`, proved by direct application.
Identical in shape to `windowed_bilinear_BV_sqrtD`, but at the recognizable textbook level condition
`D < N` (feature 3 in its simplest form).  At this level *no* block prime `> N` can divide any
modulus `d ≤ D`, so the imprimitive→primitive fold is purely α-side: the β-crumb vanishes, the extra
absorption row is dropped, and the explicit constant loses the `+ 1`, becoming
`Kβ + (6(Km + 448 + 32√26) + (2^{A+5}Kβ' + 15360))`.

This is the specialized clean corollary of the general √D form: mathematically
`D < N ⟹ D < (N+1)²` with an empty crumb, so the two agree on their common range.  It is the
statement whose hypothesis list is free of the block-prime support conditions, and is the natural
object for the literature comparison against classical Bombieri–Vinogradov mean-value bounds. -/
theorem windowed_bilinear_BV_below_N {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (Kβ Km Kβ' B : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < N → 2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D →
            (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → e ≤ X →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0) ≤ Km * (Real.log N) ^ (A + 2 * C0)) →
        (∀ e, 2 ≤ e → e ≤ D →
            K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
              ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ (A + 5) * Kβ' + 15360))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A :=
  general_BV_cutoff_unconditional hA hC0

/-! ## Composition sanity — both restatements are the landed terminals verbatim -/

section CompositionSanity

#check @Salt.Chen.windowed_bilinear_BV_sqrtD
#check @Salt.Chen.windowed_bilinear_BV_below_N
#check @Salt.Chen.general_BV_cutoff_sqrtD
#check @Salt.Chen.general_BV_cutoff_unconditional

end CompositionSanity

end Salt.Chen
