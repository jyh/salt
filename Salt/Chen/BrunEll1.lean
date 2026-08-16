/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Buchstab
import Salt.HB.RosserDim4

/-!
# ⟦BRUN-ELL1⟧ — the `ℓ¹` exit on the block-Brun lower bound

`brun_lower` (`Salt/BrunLower/Pair.lean`) leaves the H-R sieve through the **(2.12)
remainder product**.  That exit demands a *pointwise* majorant at every modulus —
`hR : |R_d| ≤ ω(d)` for all `d ∣ P(z)`, with `ω` multiplicative and `ω(p) ≤ A` — and
discharges it as a product of prime-counting factors.  A remainder slot of that shape
can only ever be fed pointwise.

This file exits through the **`ℓ¹` functional** instead:
`rosserRemainder s (Q·D) = Σ_{d ∣ P(z), d < Q·D} |r(d)|`
(`Salt/Chen/LinearSieve.lean`), the sum an *average*-form input discharges — one budget
spent over a whole range of moduli rather than a bound imposed at each one.  The whole
majorant apparatus (`ω`, `A`, `hA`, `hωnn`, `hωA`, `hωprod`, `hR`) leaves the hypothesis
list; every surviving hypothesis of `brun_lower` is carried unweakened, and the two new
binders `(Q : ℝ) (hQ : 1 ≤ Q)` only widen the cut.

## What the exit buys

Not a sharper almost-prime bound.  `twin_almost_prime`
(`Salt/BrunLower/TwinInstance.lean`) already reaches `Ω(n(n+2)) ≤ 20` through the
pointwise slot, at a higher sifting level than anything this route reaches; on that
axis the `ℓ¹` program is the weaker one and is not offered as an improvement.

What the `ℓ¹` slot uniquely admits is an **average-dischargeable remainder**: the door
through which a Bombieri–Vinogradov-shaped input can be spent, hence the door to the
`λ`-twisted BV inputs and to a **parity-pinned survivor** (`Ω(n)` odd).  The pointwise
slot cannot serve that discharge at all — no choice of `ω` turns a mean-value statement
into a bound at every modulus.  The riders that would consume the slot — the `ρ`-weighted
BV sum, the `λ`-BV dispersion half — are NAMED here and consumed nowhere; neither is in
the corpus, and nothing below claims them.

## The three pieces

* `blockTruncSieve₂` — the H-R block predicate `χ₂` as a lower (`ν = 2`) `TruncSieve`,
  the mirror of `blockTruncSieve` (`LinearSieve.lean`, `ν = 1`).  Its Rosser weight
  `μ·[χ₂]` is *definitionally* the weight `brun_lower`'s main-term chain is stated at,
  which is what lets the two engines compose without a bridge lemma.
* `chi_lower_lt` — the support bound the `ℓ¹` cut needs: every `d ∣ P(z)` kept by `χ₂`
  satisfies `d < D` with `D = exp((2b−1 + 2/(e^Λ−1))·log z)·2^{2b−2+2r−1}`,
  `r = minLevel Λ z`.  The exponent is the landed block-Brun level exponent
  (`Salt.HB.chi_log_le_level`, `levelExp Λ 2 b = 2b − 1 + 2/(e^Λ−1)`) written in the
  `exp∘log` form the corpus uses for this quantity (`remainder_upper`); the power of two
  is slack, present so the bound is STRICT — `rosserRemainder` cuts on `(d:ℝ) < bound`.
* `brun_lower_ell1` — the composition: H-R Théorème 2's lower bound with the main term
  untouched and the remainder read off the `ℓ¹` functional at level `Q·D`.
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.Chen

open BoundingSieve

/-! ## The lower block-sieve witness -/

/-- The H-R block predicate (`Salt.BrunLower.chi`) as a **lower** (`ν = 2`) truncation
sieve — the mirror of `blockTruncSieve` (`LinearSieve.lean`, `ν = 1`).  The `TruncSieve`
field lemmas `chi_one`/`chi_dvd_closed`/`chi_add_smaller_prime` are side-generic; only
`side := 2` and `hside := Or.inr rfl` change.

The point of the witness is definitional: `(blockTruncSieve₂ Λ z b hb).lam` reduces to
`fun d => μ(d)·[χ₂(d)]` by `rfl`, the exact weight at which the `Salt/BrunLower`
main-term chain (`mainSum_ge_of_lower'`) is stated, so `linear_sieve_lower_div` consumes
that chain with no bridge. -/
noncomputable def blockTruncSieve₂ (Lam z : ℝ) (b : ℕ) (hb : 1 ≤ b) : TruncSieve where
  P := fun d => Salt.BrunLower.chi Lam z 2 b d
  decP := fun d => Salt.BrunLower.instDecidableChi Lam z 2 b d
  side := 2
  hside := Or.inr rfl
  one_mem := Salt.BrunLower.chi_one Lam z hb (by norm_num : (2:ℕ) ≤ 2)
  dvd_closed := @fun _d _t hd htd hchi => Salt.BrunLower.chi_dvd_closed Lam z hd htd hchi
  add_prime := @fun _p _t hp ht hlt hpar hchi =>
    Salt.BrunLower.chi_add_smaller_prime Lam z hp ht hlt hpar hchi

/-- The seam, as a kernel check: the witness's Rosser weight is the block weight of
`Salt/BrunLower` **on the nose**.  A change to either side that broke the reduction would
stop the build here rather than at the composition below. -/
theorem blockTruncSieve₂_lam (Lam z : ℝ) (b : ℕ) (hb : 1 ≤ b) :
    (blockTruncSieve₂ Lam z b hb).lam
      = fun d => (μ d : ℝ) * (if Salt.BrunLower.chi Lam z 2 b d then (1:ℝ) else 0) := rfl

/-! ## The support bound for the `ℓ¹` cut -/

/-- **The `χ₂` support bound at the `ℓ¹` cut.**  Every divisor `d` of `P(z)` kept by the
block predicate at `ν = 2` obeys the STRICT bound
`d < exp((2b−1 + 2/(e^Λ−1))·log z) · 2^{2b−2+2r−1}`, `r = minLevel Λ z`.

The exponent is the landed block-Brun level exponent: `Salt.HB.chi_log_le_level` gives
`log d ≤ log z · levelExp Λ 2 b` with `levelExp Λ 2 b = 2b − 3 + 2e^Λ/(e^Λ−1)`, and
`2e^Λ/(e^Λ−1) = 2 + 2/(e^Λ−1)` rewrites that as `2b − 1 + 2/(e^Λ−1)`; the statement
carries it in the `exp∘log` form the corpus uses for this quantity (`remainder_upper`,
`TwinInstance.lean`) rather than as an `rpow`.  The exponent is sharp for the predicate:
the extremal `d` takes two primes per ladder layer.

Every hypothesis is consumed.  `hLam`/`hz` are the ladder's own (at `Λ = 0` the geometric
factor diverges and `minLevel` is junk); `hzprimes` transports through `d ∣ P(z)` to the
smoothness the level bound needs; `hb` fixes the `ℕ`-truncated `2b − 2 + 1 = 2b − 1`.
**Squarefreeness is used twice**: `χ` counts DISTINCT primes (`χ(2^k)` holds for every
`k`, so no bound on `d` survives without it), and `log d = Σ_{p ∣ d} log p` is what the
ladder sum bounds — both come from `d ∣ prodPrimes` against
`s.prodPrimes_squarefree`.

The factor `2^{2b−2+2r−1}` is slack, not arithmetic: it is `≥ 2`, which turns the level
bound's `≤` into the `<` that `rosserRemainder`'s cut (`if (d:ℝ) < bound`) reads. -/
theorem chi_lower_lt (s : BoundingSieve) {Lam z : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hLam : 0 < Lam) (hz : 1 < z)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    ∀ d, d ∣ s.prodPrimes → Salt.BrunLower.chi Lam z 2 b d →
      (d : ℝ) < Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z)
        * 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 : ℕ) := by
  intro d hdvd hchi
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd hdvd)
  -- squarefreeness, use 1: `χ` only ever sees distinct primes
  have hsq : Squarefree d := s.prodPrimes_squarefree.squarefree_of_dvd hdvd
  -- the smoothness the level bound consumes, transported along `d ∣ P(z)`
  have hdz : ∀ p ∈ d.primeFactors, (p : ℝ) < z := fun p hp =>
    hzprimes p (Nat.primeFactors_mono hdvd hP0 hp)
  have hexp1 : (1 : ℝ) < Real.exp Lam := by
    rw [show (1:ℝ) = Real.exp 0 by simp]; exact Real.exp_lt_exp.mpr hLam
  -- `2b − 2 + 1 = 2b − 1` in `ℕ` (needs `hb`), as one cast
  have hcast : ((2 * b - 2 + 1 : ℕ) : ℝ) = 2 * (b : ℝ) - 1 := by
    have h1 : 2 * b - 2 + 1 = 2 * b - 1 := by omega
    have h2 : (1 : ℕ) ≤ 2 * b := by omega
    rw [h1, Nat.cast_sub h2]
    push_cast
    ring
  -- `levelExp Λ 2 b = 2b − 3 + 2e^Λ/(e^Λ−1) = (2b−1) + 2/(e^Λ−1)`
  have hid : Salt.HB.levelExp Lam 2 b
      = ((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹ := by
    rw [Salt.HB.levelExp, hcast]
    have hne : Real.exp Lam - 1 ≠ 0 := by linarith
    field_simp
    ring
  -- squarefreeness, use 2: `log d = Σ_{p ∣ d} log p`, inside the landed ladder bound
  have hlog := Salt.HB.chi_log_le_level (side := 2) hLam hz hsq hdz hchi
  rw [hid] at hlog
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hle : (d : ℝ)
      ≤ Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z) := by
    rw [← Real.exp_log hdpos]
    apply Real.exp_le_exp.mpr
    linarith [hlog, mul_comm (Real.log z)
      ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹))]
  -- the slack factor is `≥ 2`, so the `≤` becomes the `<` the cut reads
  have hr1 : 1 ≤ Salt.BrunLower.minLevel Lam z := (Salt.BrunLower.minLevel_mem hLam hz).1
  have hk : 2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 ≠ 0 := by omega
  have h2k : (1 : ℝ) < 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 : ℕ) := by
    have : (1 : ℕ) < 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1) :=
      Nat.one_lt_two_pow_iff.mpr hk
    exact_mod_cast this
  have hEpos : (0 : ℝ)
      < Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z) :=
    Real.exp_pos _
  nlinarith [hle, h2k, hEpos]

/-! ## The exit -/

/-- **`brun_lower_ell1` — H-R Théorème 2's lower bound, exiting through the `ℓ¹`
remainder.**  `brun_lower` with the majorant apparatus deleted (the binders `ω`, `A` and
the hypotheses `hA`, `hωnn`, `hωA`, `hωprod`, `hR`) and its (2.12) remainder product
replaced by `rosserRemainder s (Q·D)`, the sum `Σ_{d ∣ P(z), d < Q·D} |r(d)|`.  No
surviving hypothesis is weakened: `hb`, `hlam`, `h12`, `hLam`, `hz`, `htotalMass`,
`hzprimes`, `hkappa`, `hMert` are `brun_lower`'s own, and the main term
`X·W(z)·(1 − 2λ^{2b}e^{2λ}/(1 − λ²e^{2+2λ}))` is the same object it always was.

`Q ≥ 1` widens the cut (the shape of the Rosser twin, `linear_sieve_lower_rosser`), so a
consumer may take the level at whatever `Q·D` its average-form input is stated at.

Composition: `linear_sieve_lower_div` at `blockTruncSieve₂`, with the support bound
`chi_lower_lt` and the main-term chain `mainSum_ge_of_lower'` — the very chain
`brun_lower` runs, reached here without a bridge because the witness's weight is
`μ·[χ₂]` definitionally.

The value of this exit is the SLOT, not the numerics: `rosserRemainder` is what an
average-form (BV-shaped) remainder input discharges, and it is the only one of the two
exits that a `λ`-twisted BV rider or a parity-pinned survivor could enter.  Those riders
are named, not consumed — nothing here supplies them. -/
theorem brun_lower_ell1 (s : BoundingSieve) {lam Lam z kappa : ℝ} {b : ℕ}
    (Q : ℝ) (hQ : 1 ≤ Q)
    (hb : 1 ≤ b) (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1)
    (hLam : 0 < Lam) (hz : 1 < z) (htotalMass : 0 ≤ s.totalMass)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hkappa : kappa ≤ 2 * lam)
    (hMert : ∀ n ∈ Finset.Icc 1 (Salt.BrunLower.minLevel Lam z),
      Real.log (Salt.BrunLower.Wratio s Lam z n) ≤ (n : ℝ) * kappa) :
    s.totalMass * Salt.BrunLower.W s * (1 - 2 * lam ^ (2 * b) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        - rosserRemainder s (Q *
            (Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z)
              * 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 : ℕ)))
      ≤ s.siftedSum := by
  -- the main term: `brun_lower`'s own composed lower endpoint, at `μ·[χ₂]`
  have hmain := Salt.BrunLower.mainSum_ge_of_lower' s hb hlam h12
    (Salt.BrunLower.windowPrimes s Lam z) (Salt.BrunLower.windowPrimes_subset s Lam z)
    (Salt.BrunLower.Wratio s Lam z) (fun n _ => (Salt.BrunLower.Wratio_pos s Lam z n).le)
    (Salt.BrunLower.Wratio_le_exp s hkappa hMert) (Salt.BrunLower.windowSum_le s hkappa hMert)
    (Salt.BrunLower.hcorr_lower s hLam hz hb hzprimes)
  -- the support bound at the widened cut `Q·D`
  have hsupp : ∀ d, d ∣ s.prodPrimes → (blockTruncSieve₂ Lam z b hb).P d →
      (d : ℝ) < Q *
        (Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z)
          * 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 : ℕ)) := by
    intro d hdvd hPd
    calc (d : ℝ)
        < Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z)
            * 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 : ℕ) :=
          chi_lower_lt s hb hLam hz hzprimes d hdvd hPd
      _ = 1 * (Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z)
            * 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 : ℕ)) := (one_mul _).symm
      _ ≤ Q * (Real.exp ((((2 * b - 2 + 1 : ℕ) : ℝ) + 2 * (Real.exp Lam - 1)⁻¹) * Real.log z)
            * 2 ^ (2 * b - 2 + 2 * Salt.BrunLower.minLevel Lam z - 1 : ℕ)) :=
          mul_le_mul_of_nonneg_right hQ (by positivity)
  rw [mul_assoc]
  exact linear_sieve_lower_div s (blockTruncSieve₂ Lam z b hb) rfl hsupp htotalMass hmain

end Salt.Chen
