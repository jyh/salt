/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WindowedStep
import Salt.Chen.SharpFuncbound
import Salt.Chen.Lemma11

/-!
# E₁b — the τ-RELATIVE bookkeeping and the numeric τ-close (the sharp constants)

C1cτ (`TauNumeric`) and C1cσ (`SharpTau`) PROVED, machine-checked, that **no** numeric τ-row
closes against the landed *absolute* per-level constants `SharpStep.cf_const` and
`DecayMass.ch_const`: both carry the mandatory window-conversion factor `e^{n+3}`
(`inv_S_le` / `one_le_window_hBJS`), so `ch_const n ε ≥ 24` never contracts, the recursion
doubles (`τ_{n+1} ≥ 2τ_n`), and the achievable `Cᵢ` is `≥ 3·2^{π(z)}` — astronomically large,
`ε`-uniformly (a smaller `ε` only *enlarges* the forcing `cf_const/(εe²) → ∞`).  That is the
`κ₃ = 1 ⟹ β ≥ 1` wall of the elementary route.

This file lands the **τ-RELATIVE** reformulation that evades those refutations, using E₁a's
sharp functional bound `SharpFuncbound.hBJS_funcbound_sharp`
(`∫_{s−1}^c h ≤ (49/50)·s·h(s)` on `s ≥ 2`, i.e. `κ₃ = 49/50 < 1`).

## Why the τ-relative form works where the absolute form failed

The BJS (35)–(38) four-way split measures the level-`n` error in units of `ε·τₙ·e²·h(s)`
*at the current operating point `s`* — NOT in absolute `h(s₀)`-units at a fixed worst point.
Two consequences, both fatal to the absolute route and both fixed here:

* **The `h`-side contracts.**  The `h`-part comparison, done with the *sharp*
  discrete→integral pushforward (the loglog density `d(loglog p) = −du/u` turning
  `Σ_p (1/(p−1))·(log z/log p)·h(σ_p)` into `(1/s)·∫_{s−1} h`), is closed by E₁a **at the same
  `s`**: `(1/s)·∫_{s−1}^c h ≤ (49/50)·h(s)` (`sharp_h_contract`).  So the multiplier is
  `c_h = (1+ε)·(49/50) = chSharp ε < 1` (`chSharp_lt_one`, `ε < 1/49`) — NO `e^{n+3}` window
  conversion.  Contrast `ch_const ≥ 24`.

* **The `ε` CANCELS in the forcing.**  BJS's `f`-cross terms carry the `(K−1) ≤ ε` factor
  *already*, so the level-`n` forcing is `ε·(f-to-h conversion) = ε·e²·(f-side geometric)`.
  Dividing by the τ-unit `ε·e²` (`AbelStep.ledger_collect`: `τ_{n+1} ≥ cf/(εe²) + c_h·τₙ`)
  the `ε` cancels: the forcing is `cfSharp n ε / (ε·e²) = 3·rf^n`, a GEOMETRIC, `ε`-FREE
  term (`rf = 99/100`, the landed `Tail.fseq_le` decay; `3` envelopes both the honest
  cross-term `2e²·rf^{n−1}/(e²) = 2/rf ≈ 2.02` and the base anchor `τ₁ = 3`).  Contrast the
  absolute `cf_const/(εe²) → ∞`.

## The concrete τSharp and the sums

`tauSharp ε` solves the *closing* recursion (with equality, for ALL `n` — dissolving catch #29,
since `cfSharp 0 ε = 3εe²` is tiny, not `≥ 3168`):

  `τ₀ = 0`,  `τ_{n+1} = 3·rf^n + chSharp ε·τₙ`,   so `τ₁ = 3`.

It satisfies the keystone's `hτrec` GLOBALLY (`tauSharp_hτrec`, by construction), and — because
`rf < 1` and `chSharp ε < 1` — `Lemma11.tau_sum_le_of_recursion` gives the uniform sum bound

  `Στ ≤ Csharp ε := 300 / (1 − chSharp ε)`   (`tauSharp_sum_le`, both parities),

with the concrete `Csharp (1/10000) ≤ 15074` (`Csharp_frozen`).  Crucially `Csharp ε` is
**bounded** as `ε → 0` (`→ 15000`, since `1 − chSharp ε = (1 − 49ε)/50 → 1/50`): so
`ε·Csharp ε → 0`.  This is the whole difference from C1cτ/C1cσ, where `ε·Cᵢ` was unbounded.

## THE LEDGER VERDICT (honest arithmetic; `Csharp ε ≈ 15000`, `ε`-independent)

The three sieve-slack rows scale as `ε·Csharp ε·(row factor)`; with `Csharp ε ≈ 15000`:

| row | slack `ε·C·(factor)` | factor | cap (M-abs) | closes at |
|---|---|---|---|---|
| S1 | `ε·C₂'·e²h(4)` | `(3/4)e⁻² = 0.10150` | 0.0022 | `ε ≤ 1.4·10⁻⁶` |
| S2 | `ε·C₁'·e²·J` (`J = 0.0949632`) | `0.70170` | 0.0055 | `ε ≤ 5.2·10⁻⁷` |
| S3 | `ε·C₁'·3/(4e^γ)` | `0.42109` | 0.0015 | `ε ≤ 2.4·10⁻⁷` |

**S3 binds: the ledger CLOSES by re-freezing `ε_sieve ≈ 2·10⁻⁷`** (round to `10⁻⁷` for a 2.4×
S3 margin).  Downstream: `Hyp4.w0R ε = exp(40/log(1+ε)) ≈ exp(2·10⁸)` is still a constant (fine
for the `Infinite` conclusion), and every other `ε`-site (the `(1+ε)` factors) only IMPROVES.
This is a re-freeze the C0 ledger's `ε_sieve` from `1/10000` to `≈ 10⁻⁷` — a Fable decision to
ratify; the arithmetic above is the honest input.  Contrast C1cτ/C1cσ: the absolute route
closed at **no** `ε`.

## Composition status (reported, not composed — Floor A)

* `stepHyp_sharp_of_comparisons` discharges `hτrec` at the sharp `(cfSharp, chSharp)` and
  produces `StepBound2.StepHyp` from the two *sharp* Stieltjes comparisons `hf`/`hh`.
* `bjs_theorem6_sharp_{upper,lower}` compose that with the sums to BJS Theorem 6 (5)/(6),
  with **both** `hτrec` and `htau` DISCHARGED — the entire numeric τ-layer closed — leaving
  only the two sharp comparisons `hf`/`hh` (with the sharp `cfSharp`/`chSharp` coefficients)
  and the structural sieve-class inputs (`hσ1`/`hσ3`/`h4`).

The one piece NOT landed here is the **sharp discrete→integral comparison itself** (the loglog
pushforward with `s`-dependent error control producing `hf`/`hh` at the sharp coefficients).
`sharp_h_contract` lands E₁a's role in it exactly (the `(49/50)` factor), but the pushforward
`Σ_p (1/(p−1))(log z/log p)h(σ_p) ≤ (1/s)∫_{s−1}h` is the multi-page real analysis
(`AbelStep`/`SharpStep`/`DecayMass` flagged "its own session"): the landed `decay_mass_le`
produces the ABSOLUTE `Cabs`, throwing away the `s`-dependence; recovering `(1/s)∫` needs the
sharp keeping-of-`s`.  And the real A₁ operating point is `s ≈ 4`, which needs the *windowed*
induction (`WindowedStep.T_le_of_peel_step_w`); that keystone HARDCODES `cf_const`/`ch_const`,
so composing the sharp coefficients to it additionally needs a Fable-tier parametrization of
`WindowedStep`'s `hτrec` over `(cf, ch)`.  Both are out of this node's tier and flagged.

`maxHeartbeats`: default (200000); all proofs are elementary `calc`/`nlinarith`/`ring` and one
application each of E₁a and `tau_sum_le_of_recursion`.
-/

open Finset MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-! ## Part A — the sharp per-level coefficients (τ-relative) -/

/-- The `f`-side geometric ratio (`Tail.fseq_le`'s certified `99/100`). -/
noncomputable def rf : ℝ := 99 / 100

theorem rf_nonneg : (0 : ℝ) ≤ rf := by norm_num [rf]

theorem rf_lt_one : rf < 1 := by norm_num [rf]

/-- **The sharp `f`-forcing** `cfSharp n ε = 3·ε·e²·rf^n`.  The `ε` is the `(K−1) ≤ ε`
cross-factor of BJS's (35)/(36); dividing by the τ-unit `ε·e²` leaves the GEOMETRIC, `ε`-FREE
forcing `3·rf^n` (the ε-cancellation).  The `3` envelopes both the honest `f`-to-`h` cross-term
(`≈ 2/rf`) and the base anchor `τ₁ = 3`. -/
noncomputable def cfSharp (n : ℕ) (ε : ℝ) : ℝ := 3 * ε * Real.exp 2 * rf ^ n

/-- **The sharp `h`-side multiplier** `chSharp ε = (1+ε)·(49/50)`: the E₁a contraction constant
`κ₃ = 49/50` (`hBJS_funcbound_sharp`) with the `(1+ε)` of the hypothesis-(4) pushforward.
Contracts (`< 1`) for `ε < 1/49` — NO `e^{n+3}` window conversion.  Contrast `ch_const ≥ 24`. -/
noncomputable def chSharp (ε : ℝ) : ℝ := (1 + ε) * (49 / 50)

theorem cfSharp_nonneg (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ cfSharp n ε := by
  unfold cfSharp
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (Real.exp_pos 2).le)
    (pow_nonneg rf_nonneg n)

theorem chSharp_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ chSharp ε := by
  unfold chSharp; exact mul_nonneg (by linarith) (by norm_num)

/-- **The contraction** `chSharp ε < 1` for `ε < 1/49` (`(1+ε)·49/50 < 1 ⟺ 49ε < 1`).  This
is exactly the `κ₃ < 1` that the elementary route (`κ₃ = 1`) could not achieve. -/
theorem chSharp_lt_one {ε : ℝ} (hε49 : ε < 1 / 49) : chSharp ε < 1 := by
  unfold chSharp; nlinarith [hε49]

/-! ## Part B — the E₁a consumption (the `(49/50)` contraction from the sharp funcbound) -/

/-- **E₁a consumption (the τ-relative `h`-contraction).**  For `s ≥ 2`, the loglog-integral of
`h` over `[s−1, c]`, scaled by the density factor `1/s`, is `≤ (49/50)·h(s)`.  Directly
consumes `SharpFuncbound.hBJS_funcbound_sharp` (`∫_{s−1}^c h ≤ (49/50)·s·h(s)`): dividing by
`s > 0` cancels the `s`.  This is the sharp `h`-part multiplier BJS's τ-recursion contracts on:
the `s`-relative integral is what the crude `decay_mass_le` (absolute `Cabs`) threw away. -/
theorem sharp_h_contract (s c : ℝ) (hs : 2 ≤ s) :
    (1 / s) * (∫ u in (s - 1)..c, hBJS u) ≤ (49 / 50) * hBJS s := by
  have hs0 : 0 < s := by linarith
  have hsne : s ≠ 0 := ne_of_gt hs0
  have h := hBJS_funcbound_sharp s c hs
  have hinv : (0 : ℝ) ≤ 1 / s := by positivity
  calc (1 / s) * (∫ u in (s - 1)..c, hBJS u)
      ≤ (1 / s) * ((49 / 50) * s * hBJS s) := mul_le_mul_of_nonneg_left h hinv
    _ = (49 / 50) * hBJS s := by field_simp

/-- **The full sharp `h`-side multiplier `chSharp`.**  With the hypothesis-(4) pushforward
factor `(1+ε)`, `(1+ε)·(1/s)·∫_{s−1}^c h ≤ chSharp ε·h(s)` on `s ≥ 2`.  This is the exact shape
`AbelStep.stepHyp_of_comparisons`'s `hh` slot needs, with the CONTRACTING coefficient
`chSharp ε < 1` in place of the un-closeable `ch_const`. -/
theorem chSharp_h_contract (s c ε : ℝ) (hs : 2 ≤ s) (hε : 0 ≤ ε) :
    (1 + ε) * ((1 / s) * (∫ u in (s - 1)..c, hBJS u)) ≤ chSharp ε * hBJS s := by
  have h := sharp_h_contract s c hs
  have h1e : (0 : ℝ) ≤ 1 + ε := by linarith
  calc (1 + ε) * ((1 / s) * (∫ u in (s - 1)..c, hBJS u))
      ≤ (1 + ε) * ((49 / 50) * hBJS s) := mul_le_mul_of_nonneg_left h h1e
    _ = chSharp ε * hBJS s := by unfold chSharp; ring

/-! ## Part C — the explicit τ-sequence `tauSharp` (the closing recursion, all `n`) -/

/-- **The sharp Chen τ-sequence**: `τ₀ = 0`, `τ_{n+1} = 3·rf^n + chSharp ε·τₙ`.  The closing
recursion at the sharp coefficients, taken with EQUALITY for every `n`.  Anchored at `τ₁ = 3`
(the `Lemma11.hlevel_one_upper` base). -/
noncomputable def tauSharp (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => 3 * rf ^ n + chSharp ε * tauSharp ε n

@[simp] theorem tauSharp_zero (ε : ℝ) : tauSharp ε 0 = 0 := rfl

theorem tauSharp_succ (ε : ℝ) (n : ℕ) :
    tauSharp ε (n + 1) = 3 * rf ^ n + chSharp ε * tauSharp ε n := rfl

@[simp] theorem tauSharp_one (ε : ℝ) : tauSharp ε 1 = 3 := by
  rw [tauSharp_succ, tauSharp_zero]; simp

theorem tauSharp_nonneg {ε : ℝ} (hε : 0 ≤ ε) : ∀ n, 0 ≤ tauSharp ε n
  | 0 => by rw [tauSharp_zero]
  | (n + 1) => by
      rw [tauSharp_succ]
      exact add_nonneg (mul_nonneg (by norm_num) (pow_nonneg rf_nonneg n))
        (mul_nonneg (chSharp_nonneg hε) (tauSharp_nonneg hε n))

/-- **The keystone's `hτrec`, GLOBAL (all `n`), DISCHARGED.**  `tauSharp` satisfies the closing
recursion `cfSharp n ε + ε·e²·chSharp ε·τₙ ≤ ε·e²·τ_{n+1}` for EVERY `n` — with equality, by
construction.  This dissolves catch #29 (the C1cτ finding that the global `hτrec` was
un-instantiable at `n = 0`): there `cf_const 0 ε ≥ 3168 > 24 ≥ 3εe²`, but `cfSharp 0 ε = 3εe²`
matches `εe²·τ₁ = 3εe²` exactly.  The ε-cancellation is visible: `cfSharp n / (εe²) = 3·rf^n`. -/
theorem tauSharp_hτrec {ε : ℝ} (n : ℕ) :
    cfSharp n ε + ε * Real.exp 2 * chSharp ε * tauSharp ε n
      ≤ ε * Real.exp 2 * tauSharp ε (n + 1) := by
  have heq : cfSharp n ε + ε * Real.exp 2 * chSharp ε * tauSharp ε n
      = ε * Real.exp 2 * tauSharp ε (n + 1) := by
    rw [tauSharp_succ]; unfold cfSharp; ring
  linarith [heq]

/-! ## Part D — the sums (the numeric τ-close: `Στ ≤ Csharp ε`, CONTRACTING) -/

/-- The explicit finite `Cᵢ'` of the sharp τ-close: `Csharp ε = 300/(1 − chSharp ε)`.
Bounded as `ε → 0` (`→ 15000`), so `ε·Csharp ε → 0` — the property C1cτ/C1cσ's `Cᵢ` lacked. -/
noncomputable def Csharp (ε : ℝ) : ℝ := 300 / (1 - chSharp ε)

/-- **The numeric τ-close (both parities), DISCHARGED.**  `Σ_{n<M} tauSharp ε n ≤ Csharp ε`,
uniform in `M`, via `Lemma11.tau_sum_le_of_recursion` at `a = 3`, `r = rf = 99/100`,
`β = chSharp ε < 1`.  This is the finite `Cᵢ'` that the crude route (`τ_{n+1} ≥ 2τ_n`) could
never produce. -/
theorem tauSharp_sum_le {ε : ℝ} (hε : 0 ≤ ε) (hε49 : ε < 1 / 49) (M : ℕ) :
    ∑ n ∈ Finset.range M, tauSharp ε n ≤ Csharp ε := by
  have h := tau_sum_le_of_recursion (tauSharp ε) 3 rf (chSharp ε)
    rf_nonneg rf_lt_one (chSharp_nonneg hε) (chSharp_lt_one hε49) (by norm_num)
    (tauSharp_nonneg hε) (fun n => le_of_eq (tauSharp_succ ε n)) M
  have heq : (tauSharp ε 0 + 3 / (1 - rf)) / (1 - chSharp ε) = Csharp ε := by
    rw [tauSharp_zero, Csharp]; norm_num [rf]
  rwa [heq] at h

/-- **The odd-filtered τ-close** (`htau` slot, upper): `Σ_{n<N, odd} tauSharp ε n ≤ Csharp ε`. -/
theorem tauSharp_sum_odd_le {ε : ℝ} (hε : 0 ≤ ε) (hε49 : ε < 1 / 49) (N : ℕ) :
    ∑ n ∈ (Finset.range N).filter (fun n => Odd n), tauSharp ε n ≤ Csharp ε :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => tauSharp_nonneg hε i)) (tauSharp_sum_le hε hε49 N)

/-- **The even-filtered τ-close** (`htau` slot, lower): `Σ_{n<N, even} tauSharp ε n ≤ Csharp ε`. -/
theorem tauSharp_sum_even_le {ε : ℝ} (hε : 0 ≤ ε) (hε49 : ε < 1 / 49) (N : ℕ) :
    ∑ n ∈ (Finset.range N).filter (fun n => Even n), tauSharp ε n ≤ Csharp ε :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => tauSharp_nonneg hε i)) (tauSharp_sum_le hε hε49 N)

/-- **The concrete achieved constant** at the (old) frozen `ε_sieve = 1/10000`:
`Csharp (1/10000) ≤ 15074`.  (Exactly `150000000/9951 = 15073.86…`.)  This is `C₁' = C₂'` for
the sharp route — finite and explicit, where the crude route had `Cᵢ ≥ 3·2^{π(z)}`. -/
theorem Csharp_frozen : Csharp (1 / 10000) ≤ 15074 := by
  unfold Csharp chSharp; norm_num

/-! ## Part E — the parametric consumers (`hτrec` + `htau` DISCHARGED; the sharp `hf`/`hh`
remain as the one deferred analytic input) -/

/-- **`StepHyp` from the two SHARP Stieltjes comparisons.**  `AbelStep.stepHyp_of_comparisons`
at the sharp coefficients `cf = cfSharp`, `ch = chSharp` and `tau = tauSharp ε`, with `hτrec`
DISCHARGED (`tauSharp_hτrec`).  The only remaining inputs are the two sharp comparisons `hf`
(the exact `f`-recursion integral, forcing `cfSharp`) and `hh` (the E₁a integral, multiplier
`chSharp`) — the deferred discrete→integral real analysis; `sharp_h_contract` lands E₁a's role
in `hh` exactly. -/
theorem stepHyp_sharp_of_comparisons (σ : ℕ → ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * fseq n (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (fseq (n + 1) (σ z D') + cfSharp n ε * hBJS (σ z D')))
    (hh : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * hBJS (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (chSharp ε * hBJS (σ z D'))) :
    StepHyp σ ε (tauSharp ε) :=
  stepHyp_of_comparisons σ ε (tauSharp ε) (fun n => cfSharp n ε) (fun _ => chSharp ε)
    hε (tauSharp_nonneg hε) (fun n => tauSharp_hτrec n) hf hh

/-- **BJS Theorem 6 (5), sharp-τ (upper).**  The explicit upper main-term comparison with the
ENTIRE numeric τ-layer discharged: `hτrec` (via `tauSharp_hτrec`, inside `stepHyp_sharp`) and
`htau` (via `tauSharp_sum_odd_le`, at `C₁ = Csharp ε`).  The remaining inputs are the two sharp
Stieltjes comparisons `hf`/`hh` (deferred real analysis) and the structural sieve-class inputs
(`hσ1`/`hσ3`/`h4`; note the operating window `hσ3 : σ ≤ 3` — the real A₁ point `s ≈ 4` needs the
windowed path, see the module header). -/
theorem bjs_theorem6_sharp_upper (s : BoundingSieve) (zTop D : ℕ) (hD : 1 ≤ D)
    (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (σ : ℕ → ℕ → ℝ) (ε K : ℝ)
    (hε : 0 ≤ ε) (hε49 : ε < 1 / 49) (hKe : K ≤ 1 + ε)
    (hσ1 : ∀ (z D' : ℕ), 1 ≤ D' → 1 ≤ σ z D')
    (hσ3 : ∀ (z D' : ℕ), 1 ≤ D' → σ z D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ z D') * Salt.BrunLower.W s')
    (hf : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * fseq n (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (fseq (n + 1) (σ z D') + cfSharp n ε * hBJS (σ z D')))
    (hh : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * hBJS (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (chSharp ε * hBJS (σ z D'))) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (σ zTop D) + ε * Csharp ε * Real.exp 2 * hBJS (σ zTop D)) :=
  bjs_theorem6_upper' s zTop D hD hzTop σ ε K (Csharp ε) (tauSharp ε)
    hε hKe (tauSharp_one ε) hσ1 hσ3 h4
    (stepHyp_sharp_of_comparisons σ ε hε hf hh)
    (tauSharp_sum_odd_le hε hε49 (maxDepth s + 1))

/-- **BJS Theorem 6 (6), sharp-τ (lower).**  The dual lower main-term comparison, `hτrec` and
`htau` (`tauSharp_sum_even_le`) both DISCHARGED. -/
theorem bjs_theorem6_sharp_lower (s : BoundingSieve) (zTop D : ℕ) (hD : 1 ≤ D)
    (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (σ : ℕ → ℕ → ℝ) (ε K : ℝ)
    (hε : 0 ≤ ε) (hε49 : ε < 1 / 49) (hKe : K ≤ 1 + ε)
    (hσ1 : ∀ (z D' : ℕ), 1 ≤ D' → 1 ≤ σ z D')
    (hσ3 : ∀ (z D' : ℕ), 1 ≤ D' → σ z D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ z D') * Salt.BrunLower.W s')
    (hf : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * fseq n (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (fseq (n + 1) (σ z D') + cfSharp n ε * hBJS (σ z D')))
    (hh : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * Vbelow s' p * hBJS (σ p (cdiv D' p)))
          ≤ Salt.BrunLower.W s' * (chSharp ε * hBJS (σ z D'))) :
    Salt.BrunLower.W s *
        (fchain (maxDepth s) (σ zTop D) - ε * Csharp ε * Real.exp 2 * hBJS (σ zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  bjs_theorem6_lower' s zTop D hD hzTop σ ε K (Csharp ε) (tauSharp ε)
    hε hKe (le_of_eq (tauSharp_zero ε)) (tauSharp_one ε) hσ1 hσ3 h4
    (stepHyp_sharp_of_comparisons σ ε hε hf hh)
    (tauSharp_sum_even_le hε hε49 (maxDepth s + 1))

end Salt.Chen
