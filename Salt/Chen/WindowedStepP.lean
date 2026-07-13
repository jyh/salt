/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TauSharp

/-!
# E₁d — the windowed Buchstab keystone, PARAMETRIZED over the per-level constants `(cf, ch)`

`WindowedStep` Parts D–F land the windowed keystone but HARDCODE the *absolute* per-level
constants `SharpStep.cf_const n ε` / `DecayMass.ch_const n ε` in their `hτrec` slots.  C1cτ/C1cσ
(catches #29/#30) proved, machine-checked, that no numeric τ-row closes against those absolute
constants: they carry the `e^{n+3}` window-conversion factor, so `ch_const ≥ 24`, the recursion
doubles, and the achievable `Cᵢ` is astronomically large.  `TauSharp` (E₁b) landed the
τ-RELATIVE sharp coefficients `cfSharp n ε = 3εe²·rf^n`, `chSharp ε = (1+ε)·(49/50)` and the
τ-sequence `tauSharp ε` that DO close (`tauSharp_hτrec`, `tauSharp_sum_{odd,even}_le` at
`Csharp ε`), but they were stranded: the windowed keystone — the only route to the real A₁
operating point `s ≈ 4` — could not consume them because its `hτrec` slot was frozen at the
absolute constants.

This file removes that freeze.  It re-runs `WindowedStep` Parts D–F **verbatim** with the
`hτrec` premise generalized over abstract coefficient sequences `(cf ch : ℕ → ℝ)`.  Parts A–C
of `WindowedStep` (`loBnd`, `T_vanish`, `logRatio_child_ge/lower`, `fseqBound'_nonneg`) are
already parameter-free and are REUSED, not duplicated.

* **`StepHypWP cf ch ε tau`** — `WindowedStep.StepHypW` with its `hτrec` premise
  `cf_const n ε + εe²·ch_const n ε·τₙ ≤ εe²·τ_{n+1}` replaced by
  `cf n + εe²·ch n·τₙ ≤ εe²·τ_{n+1}`; every other hypothesis and the conclusion byte-identical.
* **`stepHypWP_const`** — the landed instance `StepHypWP (cf_const ·) (ch_const ·) ε tau`,
  discharged by `DecayMass.stepHyp_pointwise` (mirrors `stepHypW_holds`).
* **`T_le_of_peel_step_wp`** — the windowed induction, parametric; the landed proof threads
  `hstepW`/`hτrec` without using what `cf`/`ch` ARE, so it ports near-verbatim.
* **`hlevel_wp_{upper,lower}`**, **`bjs_theorem6_windowed_p_{upper,lower}`** — the parametric
  `hlevel` plugs and keystones.
* **`bjs_theorem6_windowed_{upper,lower}_via_p`** — a *faithfulness* regression: the landed
  keystones' EXACT statements re-derived from the parametric ones at `(cf_const ·, ch_const ·)`
  + `stepHypWP_const` (does NOT edit `WindowedStep`).
* **`bjs_theorem6_windowed_sharp_{upper,lower}`** — the point of the node: the parametric
  keystones instantiated at the SHARP coefficients `cfSharp`/`chSharp`/`tauSharp ε`, `hτrec`
  discharged by `tauSharp_hτrec`, `htau` by `tauSharp_sum_{odd,even}_le` at `C = Csharp ε`, the
  base anchors by `tauSharp_one`/`tauSharp_nonneg`.  The ONLY remaining per-step hypothesis is
  `StepHypWP (cfSharp ·) (chSharp ·) ε (tauSharp ε)` — the slot node E₁c discharges — plus the
  structural sieve-class/window inputs the landed keystone already carries.  Unlike `TauSharp`'s
  unwindowed consumers there is NO `hσ3 : σ ≤ 3` restriction: working at the real A₁ point
  `s ≈ 4` is exactly why the windowed route (and this parametrization) exists.

`maxHeartbeats`: default; every proof is a verbatim port of a landed `WindowedStep` proof.
-/

open Finset

namespace Salt.Chen

/-! ## Part D — the parametric windowed contract `StepHypWP` -/

/-- **The parametric windowed per-step contract.**  `WindowedStep.StepHypW` with its `hτrec`
premise generalized from the absolute constants `cf_const`/`ch_const` to abstract coefficient
sequences `(cf ch : ℕ → ℝ)`.  Every other hypothesis and the conclusion are byte-identical to
`StepHypW`. -/
def StepHypWP (cf ch : ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ) : Prop :=
  ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
    0 ≤ tau n →
    (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
    (∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
    (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
    1 ≤ logRatio z D' → logRatio z D' ≤ (n : ℝ) + 3 →
    (cf n + ε * Real.exp 2 * ch n * tau n ≤ ε * Real.exp 2 * tau (n + 1)) →
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * fseqBound' logRatio ε tau (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
      ≤ fseqBound' logRatio ε tau s' z side' D' (n + 1)

/-- **`StepHypWP` at the absolute constants holds** — the landed instance, discharged pointwise
by `DecayMass.stepHyp_pointwise` (mirrors `WindowedStep.stepHypW_holds`).  This is the instance
that `bjs_theorem6_windowed_{upper,lower}_via_p` uses to re-derive the landed keystones. -/
theorem stepHypWP_const (ε : ℝ) (hε : 0 ≤ ε) (tau : ℕ → ℝ) :
    StepHypWP (fun n => cf_const n ε) (fun n => ch_const n ε) ε tau :=
  fun s' z side' D' n hside hD hn hτ0 hz hguard hnu hS1 hSn hτrec =>
    stepHyp_pointwise s' ε tau z side' D' n hε hn hD hτ0 hside hz hguard hnu hS1 hSn hτrec

/-! ## Part E — the parametric windowed Buchstab induction -/

/-- **The parametric windowed cutoff-threaded induction.**  `WindowedStep.T_le_of_peel_step_w`
verbatim, with the per-step contract and `hτrec` generalized over `(cf ch : ℕ → ℝ)`.  The landed
induction threads `hstepW`/`hτrec` without using what the coefficients ARE, so this is a
line-for-line port. -/
theorem T_le_of_peel_step_wp (cf ch : ℕ → ℝ) (ε K : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hstepW : StepHypWP cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1)) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (s' : BoundingSieve) (z side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
      (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
      (∀ q ∈ s'.prodPrimes.primeFactors,
          3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
      (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
      loBnd side' ≤ logRatio z D' →
      T s' side' D' n ≤ fseqBound' logRatio ε tau s' z side' D' n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro _ s' z side' D' hside' hD' hz hguard hnu hlow
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- base case: depth 1
      subst hm
      rcases hside' with rfl | rfl
      · -- side' = 1
        by_cases h3 : logRatio z D' ≤ 3
        · have hs1 : 1 ≤ logRatio z D' := le_trans (le_of_eq loBnd_one.symm) hlow
          have h := hlevel_one_upper s' D' (logRatio z D') ε K hs1 h3 hε hKe (h4 s' z D' hD')
          simp only [fseqBound', htau1]
          exact h
        · rw [T_vanish s' 1 D' 1 z hD' hz (by push_cast; linarith [not_le.mp h3])]
          exact fseqBound'_nonneg ε tau hε s' z 1 D' 1 (hτ0 1)
      · -- side' = 2
        rw [T_two_one_zero]
        exact fseqBound'_nonneg ε tau hε s' z 2 D' 1 (hτ0 1)
    · -- inductive case: depth m+1, m ≥ 1
      have hm1 : 1 ≤ m := hm
      by_cases hupper : logRatio z D' ≤ (m : ℝ) + 3
      · -- inside the window: peel + StepHypWP
        have hS1 : 1 ≤ logRatio z D' := le_trans (one_le_loBnd side') hlow
        rw [T_peel s' side' D' m hside' hm1 hD']
        refine le_trans (Finset.sum_le_sum (fun p hp => ?_))
          (hstepW s' z side' D' m hside' hD' hm1 (hτ0 m) hz hguard hnu hS1 hupper (hτrec m))
        obtain ⟨hp_pf, hp_win⟩ := Finset.mem_filter.mp hp
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
        have hp_dvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hp_pf
        have hnu_pos : 0 ≤ s'.nu p := (s'.nu_pos_of_prime p hp_prime hp_dvd).le
        have hflip : 3 - side' = 1 ∨ 3 - side' = 2 := by rcases hside' with rfl | rfl <;> omega
        have hsub : (sieveBelow s' p).prodPrimes.primeFactors ⊆ s'.prodPrimes.primeFactors := by
          rw [sieveBelow_primeFactors]; exact Finset.filter_subset _ _
        have hzsub : ∀ q ∈ (sieveBelow s' p).prodPrimes.primeFactors, q < p := by
          intro q hq
          rw [sieveBelow_primeFactors, belowPrimes, Finset.mem_filter] at hq
          exact hq.2
        have hguardsub : ∀ q ∈ (sieveBelow s' p).prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
          fun q hq => hguard q (hsub hq)
        have hnusub : ∀ q ∈ (sieveBelow s' p).prodPrimes.primeFactors,
            (sieveBelow s' p).nu q ≤ 1 / ((q : ℝ) - 1) := by
          intro q hq; rw [sieveBelow_nu]; exact hnu q (hsub hq)
        have hlowsub : loBnd (3 - side') ≤ logRatio p (cdiv D' p) :=
          logRatio_child_lower hD' hside' hp_pf hp_win hz hlow
        exact mul_le_mul_of_nonneg_left
          (ih hm1 (sieveBelow s' p) p (3 - side') (cdiv D' p) hflip (one_le_cdiv D' p)
            hzsub hguardsub hnusub hlowsub) hnu_pos
      · -- above the window: T_vanish
        rw [T_vanish s' side' D' (m + 1) z hD' hz (by push_cast; linarith [not_le.mp hupper])]
        exact fseqBound'_nonneg ε tau hε s' z side' D' (m + 1) (hτ0 (m + 1))

/-! ## Part F — the parametric `hlevel` plugs and the keystone `bjs_theorem6_windowed_p` -/

/-- **Parametric windowed `hlevel`, upper.**  `WindowedStep.hlevel_w_upper` with the per-step
contract taken as a hypothesis `hstepW : StepHypWP cf ch ε tau` (in place of the hardcoded
`stepHypW_holds`) and the parametric `hτrec`. -/
theorem hlevel_wp_upper (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ) (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWP cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D) :
    ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
      T s 1 D n
        ≤ Salt.BrunLower.W s * (fseq n (logRatio zTop D)
            + ε * tau n * Real.exp 2 * hBJS (logRatio zTop D)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hn1 : 1 ≤ n := by rcases hn.2 with ⟨k, rfl⟩; omega
  have hlow : loBnd 1 ≤ logRatio zTop D := by rw [loBnd_one]; exact hStop
  have h := T_le_of_peel_step_wp cf ch ε K tau hε hKe htau1 hτ0 h4 hstepW hτrec
    n hn1 s zTop 1 D (Or.inl rfl) hD hzTop hguard hnu hlow
  simpa [fseqBound'] using h

/-- **Parametric windowed `hlevel`, lower.**  `WindowedStep.hlevel_w_lower` with the same
hypothesis surgery. -/
theorem hlevel_wp_lower (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ) (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWP cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 2 ≤ logRatio zTop D) :
    ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n),
      T s 2 D n
        ≤ Salt.BrunLower.W s * (fseq n (logRatio zTop D)
            + ε * tau n * Real.exp 2 * hBJS (logRatio zTop D)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [T_zero, fseq_zero, zero_add]
    exact mul_nonneg (Salt.BrunLower.W_pos s).le
      (mul_nonneg (mul_nonneg (mul_nonneg hε (hτ0 0)) (Real.exp_pos 2).le)
        (hBJS_pos (logRatio zTop D)).le)
  · have hlow : loBnd 2 ≤ logRatio zTop D := by rw [loBnd_two]; exact hStop
    have h := T_le_of_peel_step_wp cf ch ε K tau hε hKe htau1 hτ0 h4 hstepW hτrec
      n hn1 s zTop 2 D (Or.inr rfl) hD hzTop hguard hnu hlow
    simpa [fseqBound'] using h

/-- **BJS Theorem 6 (5), windowed & PARAMETRIC (upper) — KEYSTONE.**  `WindowedStep`'s upper
keystone with the per-step contract taken as `hstepW : StepHypWP cf ch ε tau` and the parametric
`hτrec`. -/
theorem bjs_theorem6_windowed_p_upper (s : BoundingSieve) (zTop D : ℕ) (ε K C₁ : ℝ)
    (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWP cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (logRatio zTop D) + ε * C₁ * Real.exp 2 * hBJS (logRatio zTop D)) :=
  hmain_upper_of_levels s D (logRatio zTop D) ε C₁ tau hε
    (hlevel_wp_upper s zTop D ε K cf ch tau hD hzTop hguard hnu hε hKe htau1 hτ0 hstepW hτrec h4
      hStop) htau

/-- **BJS Theorem 6 (6), windowed & PARAMETRIC (lower) — KEYSTONE.** -/
theorem bjs_theorem6_windowed_p_lower (s : BoundingSieve) (zTop D : ℕ) (ε K C₂ : ℝ)
    (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWP cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 2 ≤ logRatio zTop D)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    Salt.BrunLower.W s *
        (fchain (maxDepth s) (logRatio zTop D) - ε * C₂ * Real.exp 2 * hBJS (logRatio zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  hmain_lower_of_levels s D (logRatio zTop D) ε C₂ tau hε
    (hlevel_wp_lower s zTop D ε K cf ch tau hD hzTop hguard hnu hε hKe htau1 hτ0 hstepW hτrec h4
      hStop) htau

/-! ## Part G — faithfulness regression: the landed keystones re-derived from the parametric
route (does NOT edit `WindowedStep`) -/

/-- **Faithfulness (upper).**  `WindowedStep.bjs_theorem6_windowed_upper`'s EXACT statement,
re-derived from the parametric keystone at `(cf_const ·, ch_const ·)` + `stepHypWP_const`. -/
theorem bjs_theorem6_windowed_upper_via_p (s : BoundingSieve) (zTop D : ℕ) (ε K C₁ : ℝ)
    (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (logRatio zTop D) + ε * C₁ * Real.exp 2 * hBJS (logRatio zTop D)) :=
  bjs_theorem6_windowed_p_upper s zTop D ε K C₁ (fun n => cf_const n ε) (fun n => ch_const n ε)
    tau hD hzTop hguard hnu hε hKe htau1 hτ0 (stepHypWP_const ε hε tau) hτrec h4 hStop htau

/-- **Faithfulness (lower).**  `WindowedStep.bjs_theorem6_windowed_lower`'s EXACT statement,
re-derived from the parametric keystone. -/
theorem bjs_theorem6_windowed_lower_via_p (s : BoundingSieve) (zTop D : ℕ) (ε K C₂ : ℝ)
    (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 2 ≤ logRatio zTop D)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    Salt.BrunLower.W s *
        (fchain (maxDepth s) (logRatio zTop D) - ε * C₂ * Real.exp 2 * hBJS (logRatio zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  bjs_theorem6_windowed_p_lower s zTop D ε K C₂ (fun n => cf_const n ε) (fun n => ch_const n ε)
    tau hD hzTop hguard hnu hε hKe htau1 hτ0 (stepHypWP_const ε hε tau) hτrec h4 hStop htau

/-! ## Part H — the sharp plugs (the point of the node): the parametric keystones at the SHARP
coefficients `cfSharp`/`chSharp`/`tauSharp` -/

/-- **BJS Theorem 6 (5), windowed & SHARP (upper) — the E₁d payoff.**  The parametric keystone
instantiated at the sharp coefficients `cf = cfSharp`, `ch = chSharp`, `tau = tauSharp ε`,
`C₁ = Csharp ε`.  The entire numeric τ-layer is DISCHARGED: `hτrec` by `tauSharp_hτrec`, `htau`
by `tauSharp_sum_odd_le`, `τ₁ = 3` by `tauSharp_one`, nonneg by `tauSharp_nonneg`.  The ONLY
remaining per-step hypothesis is `hstepWP : StepHypWP (cfSharp ·) (chSharp ·) ε (tauSharp ε)` —
node E₁c's slot — plus the structural sieve-class/window inputs (`hguard`/`hnu`/`h4`/`hStop`).
There is NO `hσ3 : σ ≤ 3` restriction: this route works at the real A₁ operating point
`s ≈ 4`. -/
theorem bjs_theorem6_windowed_sharp_upper (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hε49 : ε < 1 / 49) (hKe : K ≤ 1 + ε)
    (hstepWP : StepHypWP (fun n => cfSharp n ε) (fun _ => chSharp ε) ε (tauSharp ε))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (logRatio zTop D)
          + ε * Csharp ε * Real.exp 2 * hBJS (logRatio zTop D)) :=
  bjs_theorem6_windowed_p_upper s zTop D ε K (Csharp ε)
    (fun n => cfSharp n ε) (fun _ => chSharp ε) (tauSharp ε)
    hD hzTop hguard hnu hε hKe (tauSharp_one ε) (tauSharp_nonneg hε) hstepWP
    (fun n => tauSharp_hτrec n) h4 hStop (tauSharp_sum_odd_le hε hε49 (maxDepth s + 1))

/-- **BJS Theorem 6 (6), windowed & SHARP (lower) — the E₁d payoff.**  The dual lower keystone
at the sharp coefficients, `htau` via `tauSharp_sum_even_le`. -/
theorem bjs_theorem6_windowed_sharp_lower (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hε49 : ε < 1 / 49) (hKe : K ≤ 1 + ε)
    (hstepWP : StepHypWP (fun n => cfSharp n ε) (fun _ => chSharp ε) ε (tauSharp ε))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 2 ≤ logRatio zTop D) :
    Salt.BrunLower.W s *
        (fchain (maxDepth s) (logRatio zTop D)
          - ε * Csharp ε * Real.exp 2 * hBJS (logRatio zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  bjs_theorem6_windowed_p_lower s zTop D ε K (Csharp ε)
    (fun n => cfSharp n ε) (fun _ => chSharp ε) (tauSharp ε)
    hD hzTop hguard hnu hε hKe (tauSharp_one ε) (tauSharp_nonneg hε) hstepWP
    (fun n => tauSharp_hτrec n) h4 hStop (tauSharp_sum_even_le hε hε49 (maxDepth s + 1))

end Salt.Chen
