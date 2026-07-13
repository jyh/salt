/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.StepBound

/-!
# C1c⁶ — the cutoff-threaded Buchstab skeleton and the *statable* `hstep'` (catch #27)

This file executes the **catch-#27 amendment** adjudicated at the end of C1c⁵
(`docs/blueprints/flags.md`).  C1c⁴/C1c⁵ built the Buchstab induction skeleton
(`Peeling.T_le_of_peel_step`) around an operating-point map `σ : BoundingSieve → ℕ → ℝ`,
and discovered that this map **cannot recover the sub-sieve cutoff `p`** from `sieveBelow s p`
(whose `prodPrimes = ∏_{q<p} q` forgets `p`).  Consequently BJS's change of variables
`t = log D / log p ↦ s'_p = t − 1` — the entire discrete→integral mechanism of the per-step
comparison — was **not statable**: any attempt to isolate a clean `hsum` degenerated into
restating the whole `hstep`.  The C1c⁵ executor isolated this as an architectural obstruction
(catch #27) and the amendment was sanctioned: *generalise the skeleton so the bound carries
the cutoff explicitly.*

## What is amended (the skeleton is an internal scaffold, not a frozen blueprint statement)

* **`T_le_of_peel_step'`** — the cutoff-threaded induction engine.  The abstract target family
  gains an explicit cutoff argument, `B : BoundingSieve → ℕ → ℕ → ℕ → ℕ → ℝ` with signature
  `B s' z side D n` (`z` the cutoff for `s'`).  The per-step comparison `hstep'` now feeds the
  cutoff `p` of each sub-sieve `sieveBelow s' p` directly into `B (sieveBelow s' p) p …`.  The
  induction is re-derived from `Peeling.T_peel` exactly as before; the only new obligation is
  that the sub-sieve's cutoff hypothesis `∀ q ∈ (sieveBelow s' p).primeFactors, q < p` holds,
  which is immediate (`belowPrimes s' p` are all `< p`).

* **`fseqBound'`** — the cutoff-threaded target family, keyed on an abstract
  `σ : ℕ → ℕ → ℝ` **of the cutoff `z` and level `D`** (not the sieve): `B s' z _side D n =
  W s'·(fₙ(σ z D) + ε·τₙ·e²·h(σ z D))`.  The intended concrete map is `σ z D = log D / log z`
  (`logRatio`).  Under this parameterisation `hstep'`'s sub-term is
  `W(sieveBelow s' p)·(fₙ(σ p (⌈D/p⌉)) + …)` with the cutoff `p` **explicit in the operating
  point** — exactly BJS's summand.  The architectural obstruction is removed:
  **`hstep'` (BJS (34)–(38)) is now a statable hypothesis.**

* **`hbase'_of`, `hlevel'_{upper,lower}_of_step'`, `bjs_theorem6_{upper,lower}'`** and the
  `_sifted'` forms — the payoff re-assembled on the new skeleton, discharging the base case
  through `Lemma11.hlevel_one_upper` (unchanged: the base does not recurse) and feeding the
  produced `hlevel` shape through C1c‴'s `hmain_{upper,lower}_of_levels` /
  `linear_sieve_{upper,lower}_rosser_assembled_final`.  The remaining hypothesis list is:
  the per-step comparison `hstep'` (now statable), hypothesis (4) (`h4` V-ratio + σ-window),
  and the parametric τ-close `htau`.

## The `κ₃` constants issue (orthogonal to catch #27; stays parametric per the C0 ledger)

BJS's τ-recursion (their (31)) contracts (`β = Kκ₃ + (K−1)γ₃ < 1`) only because their
`H(s) ≤ κ₃·s·h(s)` has `κ₃ ≈ 0.96 < 1`.  The elementary `StepBound.hBJS_funcbound` gives
`κ₃ = 1` (tight at `s = 2`), forcing `β ≥ 1`.  Sharpening the tail `∫_3^∞ 3u⁻¹e⁻ᵘ`
by integrating by parts **twice** (`= 3a⁻¹e⁻ᵃ − 3∫u⁻²e⁻ᵘ`, then bound the correction below by
`a⁻²e⁻ᵃ(1−2/a)`) yields `∫_3^∞ 3u⁻¹e⁻ᵘ ≤ (8/9)e⁻³`, hence `∫_1^∞ h ≤ 2e⁻² − (1/9)e⁻³ ≈
0.98·2e⁻²`, i.e. `κ₃ ≤ 0.98` at the tight point — the "route (I)" sharpening.  This affects
only the numeric `htau` close (`C₁ = 106, C₂ = 108`), which the C0-ledger doctrine keeps
parametric regardless; it does **not** gate catch #27.  Left as a named `htau` hypothesis and
the `StepBound.tauSum_{odd,even}_le` dischargers.  See `docs/blueprints/flags.md`.

The per-step comparison `hstep'` (BJS's (34)–(38) partial summation, the genuine
discrete→integral real analysis) remains the one named hypothesis of the payoff — but it is
now **statable**, which is precisely what catch #27 required.  Every combinatorial piece (the
peel, the induction, the base, the assembly) is proved sorry-free and axiom-clean.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the cutoff-threaded induction skeleton `T_le_of_peel_step'`

The C1c⁴ skeleton `Peeling.T_le_of_peel_step` with the abstract target family `B` gaining an
explicit cutoff argument.  The recursion (`Peeling.T_peel`) is unchanged; the induction now
threads the cutoff `z` and, at each peel, hands the sub-sieve `sieveBelow s' p` its own cutoff
`p` (a valid cutoff, since `belowPrimes s' p` are all `< p`). -/

/-- **The cutoff-threaded Buchstab induction skeleton** (BJS Lemma 11, catch-#27 amendment).
With `B : BoundingSieve → ℕ → ℕ → ℕ → ℕ → ℝ` (sieve, **cutoff `z`**, side, level, depth) the
abstract target family, `hbase` the depth-1 bound, and the per-step comparison `hstep'`
`Σ_p ν(p)·B(sieveBelow s' p) p … ≤ B s' z …` — where the sub-sieve's cutoff `p` is threaded
explicitly — we get `Tₙ ≤ B s' z side D n` for every depth `n ≥ 1`, sieve `s'`, valid cutoff
`z` (`∀ q ∈ s'.primeFactors, q < z`), level, and side. -/
theorem T_le_of_peel_step' (B : BoundingSieve → ℕ → ℕ → ℕ → ℕ → ℝ)
    (hbase : ∀ (s' : BoundingSieve) (z side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ B s' z side' D' 1)
    (hstep' : ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * B (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
          ≤ B s' z side' D' (n + 1)) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (s' : BoundingSieve) (z side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
      (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
      T s' side' D' n ≤ B s' z side' D' n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro _ s' z side' D' hside' hD' hz
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; exact hbase s' z side' D' hside' hD'
    · have hm1 : 1 ≤ m := hm
      rw [T_peel s' side' D' m hside' hm1 hD']
      refine le_trans (Finset.sum_le_sum (fun p hp => ?_))
        (hstep' s' z side' D' m hside' hD' hm1 hz)
      obtain ⟨hp_pf, _⟩ := Finset.mem_filter.mp hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
      have hp_dvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hp_pf
      have hnu_pos : 0 ≤ s'.nu p := (s'.nu_pos_of_prime p hp_prime hp_dvd).le
      have hflip : 3 - side' = 1 ∨ 3 - side' = 2 := by rcases hside' with rfl | rfl <;> omega
      have hzsub : ∀ q ∈ (sieveBelow s' p).prodPrimes.primeFactors, q < p := by
        intro q hq
        simp only [sieveBelow_primeFactors, belowPrimes, Finset.mem_filter] at hq
        exact hq.2
      exact mul_le_mul_of_nonneg_left
        (ih hm1 (sieveBelow s' p) p (3 - side') (cdiv D' p) hflip (one_le_cdiv D' p) hzsub) hnu_pos

/-! ## Part B — the cutoff-threaded target family `fseqBound'`

The C1c⁴ family `Peeling.fseqBound` with the operating-point map keyed on the explicit cutoff
`z` (via an abstract `σ : ℕ → ℕ → ℝ` of `(z, D)`) rather than the sieve.  The intended concrete
map is `logRatio z D = log D / log z`, which — now that `z` is an explicit argument — is
statable through the recursion (catch #27 resolved). -/

/-- The intended concrete operating-point map `σ(z, D) = log D / log z` (BJS's `s = log D/log z`
at cutoff `z`).  Offered as the intended instantiation of the abstract `σ` below; its
`[1,3]`-window remains a hypothesis (the operating regime), exactly as in the unprimed design. -/
noncomputable def logRatio (z D : ℕ) : ℝ := Real.log D / Real.log z

/-- **The cutoff-threaded `fₙ`/`h`/`τ` target family** of BJS Lemma 11: identical to
`Peeling.fseqBound` but with the operating point `σ z D` keyed on the explicit cutoff `z`
(and level `D`) instead of the sieve. -/
noncomputable def fseqBound' (σ : ℕ → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ)
    (s' : BoundingSieve) (z _side D n : ℕ) : ℝ :=
  Salt.BrunLower.W s' * (fseq n (σ z D) + ε * tau n * Real.exp 2 * hBJS (σ z D))

/-- **The per-step comparison `hstep'`** (BJS (34)–(38)), now *statable* with the cutoff `z`
explicit.  The sub-term `fseqBound' σ ε τ (sieveBelow s' p) p …` reads
`W(sieveBelow s' p)·(fₙ(σ p (⌈D'/p⌉)) + …)`: the discrete→integral change of variables
`t = log D'/log p ↦ σ p (⌈D'/p⌉)` is written directly, since `p` no longer has to be recovered
from the cutoff-forgetting `sieveBelow s' p`.  This is the genuine real-analysis heart (the
partial summation turning the head `p`-sum into the `fseq` recursion integral); it is the one
named hypothesis of the payoff, kept as a `Prop` for the shared statement below. -/
def StepHyp (σ : ℕ → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ) : Prop :=
  ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
    (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * fseqBound' σ ε tau (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
      ≤ fseqBound' σ ε tau s' z side' D' (n + 1)

/-! ## Part C — the base bound `hbase'_of` (cutoff-threaded, BJS (39))

The depth-1 slot of the payoff, discharged exactly as `StepBound.hbase_of` (the base case does
not recurse, so the cutoff plays no combinatorial role): upper via `Lemma11.hlevel_one_upper`,
even/lower via `T_two_one_zero`.  The operating point is `σ z D'` (cutoff-keyed). -/

/-- **`hbase'` (BJS (39), both sides).**  Discharges the base hypothesis of the cutoff-threaded
skeleton for the `fseqBound' σ ε τ` family, from the σ-window (`1 ≤ σ z D' ≤ 3`), hypothesis
(4) in the V-ratio form (`h4 : Vlow ≤ (3K/σ z D')·W`), `0 ≤ ε`, `K ≤ 1+ε`, `τ₁ = 3`. -/
theorem hbase'_of (σ : ℕ → ℕ → ℝ) (ε K : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (z D' : ℕ), 1 ≤ D' → 1 ≤ σ z D')
    (hσ3 : ∀ (z D' : ℕ), 1 ≤ D' → σ z D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ z D') * Salt.BrunLower.W s') :
    ∀ (s' : BoundingSieve) (z side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
      T s' side' D' 1 ≤ fseqBound' σ ε tau s' z side' D' 1 := by
  intro s' z side' D' hside hD'
  rcases hside with h1 | h2
  · subst h1
    have h := hlevel_one_upper s' D' (σ z D') ε K (hσ1 z D' hD') (hσ3 z D' hD') hε hKe
      (h4 s' z D' hD')
    simp only [fseqBound', htau1]
    exact h
  · subst h2
    rw [T_two_one_zero]
    simp only [fseqBound', htau1]
    have hW := Salt.BrunLower.W_pos s'
    have hnn : 0 ≤ fseq 1 (σ z D') + ε * 3 * Real.exp 2 * hBJS (σ z D') := by
      have hf := fseq_nonneg 1 (σ z D')
      have hh : 0 ≤ ε * 3 * Real.exp 2 * hBJS (σ z D') :=
        mul_nonneg (mul_nonneg (mul_nonneg hε (by norm_num)) (Real.exp_pos 2).le) (hBJS_pos _).le
      linarith
    exact mul_nonneg hW.le hnn

/-! ## Part D — the `hlevel'` plugs (cutoff-threaded, Lemma 11 shape)

Instantiating the cutoff-threaded skeleton at the top sieve `s` and its top cutoff `zTop`
(`∀ q ∈ s.primeFactors, q < zTop`) produces Lemma11's exact `hlevel` shape at
`sparam = σ zTop D`, which flows through C1c‴'s `hmain_{upper,lower}_of_levels`. -/

/-- **`hlevel'`, upper (BJS Theorem 6 (5)).**  From the base and the statable `hstep'`, the
cutoff-threaded skeleton yields Lemma11's exact upper `hlevel` shape at `sparam = σ zTop D`. -/
theorem hlevel'_upper_of_step' (s : BoundingSieve) (zTop D : ℕ) (hD : 1 ≤ D)
    (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (σ : ℕ → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ)
    (hbase : ∀ (s' : BoundingSieve) (z side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ fseqBound' σ ε tau s' z side' D' 1)
    (hstep' : StepHyp σ ε tau) :
    ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
      T s 1 D n
        ≤ Salt.BrunLower.W s * (fseq n (σ zTop D) + ε * tau n * Real.exp 2 * hBJS (σ zTop D)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hn1 : 1 ≤ n := by rcases hn.2 with ⟨k, rfl⟩; omega
  have h := T_le_of_peel_step' (fseqBound' σ ε tau) hbase hstep' n hn1 s zTop 1 D (Or.inl rfl) hD
    hzTop
  simpa [fseqBound'] using h

/-- **`hlevel'`, lower (BJS Theorem 6 (6)).**  The even/lower mirror; the even filter's `n = 0`
term (`T s 2 D 0 = 0`, `fseq 0 = 0`) is handled directly (needs `0 ≤ ε`, `0 ≤ τ 0`). -/
theorem hlevel'_lower_of_step' (s : BoundingSieve) (zTop D : ℕ) (hD : 1 ≤ D)
    (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (σ : ℕ → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ) (hε : 0 ≤ ε) (htau0 : 0 ≤ tau 0)
    (hbase : ∀ (s' : BoundingSieve) (z side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ fseqBound' σ ε tau s' z side' D' 1)
    (hstep' : StepHyp σ ε tau) :
    ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n),
      T s 2 D n
        ≤ Salt.BrunLower.W s * (fseq n (σ zTop D) + ε * tau n * Real.exp 2 * hBJS (σ zTop D)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [T_zero, fseq_zero]
    have hW := Salt.BrunLower.W_pos s
    have hh := (hBJS_pos (σ zTop D)).le
    have hnn : 0 ≤ ε * tau 0 * Real.exp 2 * hBJS (σ zTop D) :=
      mul_nonneg (mul_nonneg (mul_nonneg hε htau0) (Real.exp_pos 2).le) hh
    nlinarith [hnn, hW]
  · have h := T_le_of_peel_step' (fseqBound' σ ε tau) hbase hstep' n hn1 s zTop 2 D (Or.inr rfl) hD
      hzTop
    simpa [fseqBound'] using h

/-! ## Part E — the payoff: BJS Theorem 6 (5)/(6) on the cutoff-threaded skeleton

`hbase'` discharged (`hbase'_of`); the remaining named hypotheses are the **statable** per-step
comparison `hstep'`, the parametric τ-close `htau`, and the hypothesis-(4) family (`h4`, the
σ-window).  This is BJS Theorem 6 (5)/(6) with catch #27 removed — one statable analytic
hypothesis (`hstep'`) from unconditional-modulo-(hyp-4 + numeric-τ). -/

/-- **BJS Theorem 6 (5), main-term form** (upper), cutoff-threaded. -/
theorem bjs_theorem6_upper' (s : BoundingSieve) (zTop D : ℕ) (hD : 1 ≤ D)
    (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (σ : ℕ → ℕ → ℝ) (ε K C₁ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (z D' : ℕ), 1 ≤ D' → 1 ≤ σ z D')
    (hσ3 : ∀ (z D' : ℕ), 1 ≤ D' → σ z D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ z D') * Salt.BrunLower.W s')
    (hstep' : StepHyp σ ε tau)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (σ zTop D) + ε * C₁ * Real.exp 2 * hBJS (σ zTop D)) :=
  hmain_upper_of_levels s D (σ zTop D) ε C₁ tau hε
    (hlevel'_upper_of_step' s zTop D hD hzTop σ ε tau
      (hbase'_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep') htau

/-- **BJS Theorem 6 (6), main-term form** (lower), cutoff-threaded. -/
theorem bjs_theorem6_lower' (s : BoundingSieve) (zTop D : ℕ) (hD : 1 ≤ D)
    (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (σ : ℕ → ℕ → ℝ) (ε K C₂ : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau0 : 0 ≤ tau 0) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (z D' : ℕ), 1 ≤ D' → 1 ≤ σ z D')
    (hσ3 : ∀ (z D' : ℕ), 1 ≤ D' → σ z D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ z D') * Salt.BrunLower.W s')
    (hstep' : StepHyp σ ε tau)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    Salt.BrunLower.W s * (fchain (maxDepth s) (σ zTop D) - ε * C₂ * Real.exp 2 * hBJS (σ zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  hmain_lower_of_levels s D (σ zTop D) ε C₂ tau hε
    (hlevel'_lower_of_step' s zTop D hD hzTop σ ε tau hε htau0
      (hbase'_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep') htau

/-- **BJS Theorem 6 (5), sifted-sum form** (upper), cutoff-threaded: the full explicit upper
linear sieve modulo `hstep'`, `htau`, and the hypothesis-(4) family. -/
theorem bjs_theorem6_upper_sifted' (s : BoundingSieve) (zTop D : ℕ) (hD : 2 ≤ D)
    (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (htm : 0 ≤ s.totalMass) (σ : ℕ → ℕ → ℝ) (ε K C₁ Q : ℝ) (hQ : 1 ≤ Q)
    (tau : ℕ → ℝ) (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (z D' : ℕ), 1 ≤ D' → 1 ≤ σ z D')
    (hσ3 : ∀ (z D' : ℕ), 1 ≤ D' → σ z D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ z D') * Salt.BrunLower.W s')
    (hstep' : StepHyp σ ε tau)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.siftedSum
      ≤ s.totalMass * (Salt.BrunLower.W s *
          (Fchain (maxDepth s) (σ zTop D) + ε * C₁ * Real.exp 2 * hBJS (σ zTop D)))
        + rosserRemainder s (Q * D) :=
  linear_sieve_upper_rosser_assembled_final s D hD htm (σ zTop D) ε C₁ Q hQ hε tau
    (hlevel'_upper_of_step' s zTop D (by omega) hzTop σ ε tau
      (hbase'_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep') htau

/-- **BJS Theorem 6 (6), sifted-sum form** (lower), cutoff-threaded.  The sieve's sifting limit
`zTop` (`hzTop : ∀ p ∈ s.primeFactors, p < zTop`) serves as both the assembly's `z` and the
operating cutoff. -/
theorem bjs_theorem6_lower_sifted' (s : BoundingSieve) (D zTop : ℕ) (hz2 : 2 ≤ zTop)
    (hzD : zTop ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop) (htm : 0 ≤ s.totalMass)
    (σ : ℕ → ℕ → ℝ) (ε K C₂ Q : ℝ) (hQ : 1 ≤ Q)
    (tau : ℕ → ℝ) (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau0 : 0 ≤ tau 0) (htau1 : tau 1 = 3)
    (hσ1 : ∀ (z D' : ℕ), 1 ≤ D' → 1 ≤ σ z D')
    (hσ3 : ∀ (z D' : ℕ), 1 ≤ D' → σ z D' ≤ 3)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / σ z D') * Salt.BrunLower.W s')
    (hstep' : StepHyp σ ε tau)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    s.totalMass * (Salt.BrunLower.W s *
        (fchain (maxDepth s) (σ zTop D) - ε * C₂ * Real.exp 2 * hBJS (σ zTop D)))
      - rosserRemainder s (Q * D) ≤ s.siftedSum :=
  linear_sieve_lower_rosser_assembled_final s D zTop hz2 hzD hzTop htm (σ zTop D) ε C₂ Q hQ hε tau
    (hlevel'_lower_of_step' s zTop D (by omega) hzTop σ ε tau hε htau0
      (hbase'_of σ ε K tau hε hKe htau1 hσ1 hσ3 h4) hstep') htau

end Salt.Chen
