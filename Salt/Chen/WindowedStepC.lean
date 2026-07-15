/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WindowedStepP

/-!
# E₁d′ — the CONDITIONED parametric windowed layer + the B-mirror (FREEZE V2, catches #32/#33)

`WindowedStepP` (E₁d) parametrized the windowed Buchstab keystone over `(cf, ch)` but left its
per-step contract `StepHypWP` unconditioned.  Catch #32 (a machine-verified counterexample)
showed `StepHypWP` is UNDISCHARGEABLE at ε-order coefficients: it carries only
`1 ≤ σ ≤ n+3`, no `loBnd side' ≤ σ` and no parity structure, so at `(side'=2, n=1, S ∈ [1,2))`
the RHS collapses to `O(εW)` (`fseq 2 = 0` below 2) while the LHS is `Θ(W)`.  BJS's induction
NEVER peels naively there — (39) reroutes through `V(D^{1/3}) ≤ (3K/s)V(z)` exactly so
even-index `fseq` is never evaluated below 2.  The discrete analog is already encoded in our
`T_peel`: the `p³ < D'` side-1 filter forces `σ_child ≥ 2` (`logRatio_child_lower`).

FREEZE V2 exposes that structure in the CONTRACT and threads it as an invariant:

* **`StepHypWPC cf ch ε tau`** — `StepHypWP` PLUS two premises: the loBnd invariant
  `loBnd side' ≤ logRatio z D'` and the parity coupling `side' % 2 ≠ n % 2` (child-depth form).
  `StepHypWP → StepHypWPC` is trivial (more premises), so the const instance is free.
* **`T_le_of_peel_step_wpc`** — the E₁d induction with the parity invariant `side' % 2 = n % 2`
  threaded.  The descent `(side', n+1) → (3−side', n)` flips BOTH parities, preserving the
  invariant; the per-step call supplies `hlow` and the parity premise.  The base (`n = 1`) is
  forced to side 1 by the invariant (side 2 excluded — it was `T_two_one_zero = 0` anyway).
* **`hlevel_wpc_{upper,lower}`**, **`bjs_theorem6_windowed_c_{upper,lower}`** — the conditioned
  plugs and keystones.  The upper sums ODD depths at side 1, the lower EVEN at side 2 (matching
  `hTbound_{upper,lower}_of_levels`, verified to consume `hlevel` only at the coupled parities:
  odd@1 / even@2 — no top-parity side condition needed).
* **The B-mirror** (`cfSharpB`/`chSharpB`/`tauSharpB`/`CsharpB` + sums) — the boundary-padded
  sharp coefficients of the gate: `cfSharpB` envelopes the odd-flat `f`-boundary (factor 20),
  `chSharpB = (1+ε)(49/50) + 4ε` the `h`-boundary (`γ₃ʰ`), contraction at `ε < 1/249`.
* **The B-plugs** (`bjs_theorem6_windowed_cB_{upper,lower}`) — the conditioned keystones at the
  B-coefficients, with `hτrec`/`htau`/`τ₁`/nonneg all discharged; the ONLY remaining per-step
  slot is `hstepWPC : StepHypWPC (cfSharpB ·) (chSharpB ·) ε (tauSharpB ε)` (nodes E₁c-hh/hf).

`maxHeartbeats`: default; every induction/keystone proof is a conditioned port of a landed
`WindowedStepP` proof, and the B-mirror is a `tauSharp`-style case-split.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the conditioned parametric windowed contract `StepHypWPC` -/

/-- **The CONDITIONED parametric windowed per-step contract.**  `StepHypWP` (WindowedStepP)
with TWO extra premises inserted after the `1 ≤ σ ≤ n+3` window pair: the loBnd invariant
`loBnd side' ≤ logRatio z D'` and the PARITY COUPLING `side' % 2 ≠ n % 2` (the child-depth form
of `side' % 2 = depth % 2`).  These make the contract dischargeable at ε-order coefficients
(catch #32): with them the odd-flat regime — where `fseq` would be evaluated below its window —
is provably out of range. -/
def StepHypWPC (cf ch : ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ) : Prop :=
  ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
    0 ≤ tau n →
    (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
    (∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
    (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
    1 ≤ logRatio z D' → logRatio z D' ≤ (n : ℝ) + 3 →
    loBnd side' ≤ logRatio z D' → side' % 2 ≠ n % 2 →
    (cf n + ε * Real.exp 2 * ch n * tau n ≤ ε * Real.exp 2 * tau (n + 1)) →
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * fseqBound' logRatio ε tau (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
      ≤ fseqBound' logRatio ε tau s' z side' D' (n + 1)

/-- **`StepHypWP → StepHypWPC`** (trivial: drop the two extra premises).  So every discharge of
the unconditioned contract yields the conditioned one. -/
theorem stepHypWPC_of_wp (cf ch : ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ) :
    StepHypWP cf ch ε tau → StepHypWPC cf ch ε tau :=
  fun h s' z side' D' n hside hD hn hτ0 hz hguard hnu hS1 hSn _hlow _hpar hτrec =>
    h s' z side' D' n hside hD hn hτ0 hz hguard hnu hS1 hSn hτrec

/-- **`StepHypWPC` at the absolute constants** — via `stepHypWP_const` + `stepHypWPC_of_wp`. -/
theorem stepHypWPC_const (ε : ℝ) (hε : 0 ≤ ε) (tau : ℕ → ℝ) :
    StepHypWPC (fun n => cf_const n ε) (fun n => ch_const n ε) ε tau :=
  stepHypWPC_of_wp _ _ ε tau (stepHypWP_const ε hε tau)

/-! ## Part B — the conditioned parametric windowed Buchstab induction (parity invariant) -/

/-- **The conditioned windowed cutoff-threaded induction.**  `T_le_of_peel_step_wp` with the
per-step contract conditioned (`StepHypWPC`) and the PARITY INVARIANT `side' % 2 = n % 2`
threaded through the recursion.  The descent step `(side', n+1) → (3−side', n)` flips both
parities, preserving the invariant (`(3−side') % 2 = m % 2` from `side' % 2 = (m+1) % 2`); the
per-step call supplies the loBnd invariant `hlow` and the parity premise `side' % 2 ≠ m % 2`.
The base `n = 1` is forced to side 1 by the invariant (`side' % 2 = 1`); the side-2 branch is
EXCLUDED (it was `T_two_one_zero = 0` anyway). -/
theorem T_le_of_peel_step_wpc (cf ch : ℕ → ℝ) (ε K : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hstepW : StepHypWPC cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1)) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (s' : BoundingSieve) (z side' D' : ℕ), side' = 1 ∨ side' = 2 →
      side' % 2 = n % 2 → 1 ≤ D' →
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
    intro _ s' z side' D' hside' hpar hD' hz hguard hnu hlow
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- base case: depth 1; the parity invariant forces side' = 1
      subst hm
      rcases hside' with rfl | rfl
      · -- side' = 1
        by_cases h3 : logRatio z D' ≤ 3
        · have hs1 : 1 ≤ logRatio z D' := le_trans (le_of_eq loBnd_one.symm) hlow
          have h := hlevel_one_upper s' D' (logRatio z D') ε K hs1 h3 hε hKe
            (h4 s' z D' hD' hz hguard hnu hs1 h3)
          simp only [fseqBound', htau1]
          exact h
        · rw [T_vanish s' 1 D' 1 z hD' hz (by push_cast; linarith [not_le.mp h3])]
          exact fseqBound'_nonneg ε tau hε s' z 1 D' 1 (hτ0 1)
      · -- side' = 2: EXCLUDED by the parity invariant (2 % 2 ≠ (0+1) % 2)
        exact absurd hpar (by omega)
    · -- inductive case: depth m+1, m ≥ 1
      have hm1 : 1 ≤ m := hm
      by_cases hupper : logRatio z D' ≤ (m : ℝ) + 3
      · -- inside the window: peel + StepHypWPC (supplying hlow + the parity premise)
        have hS1 : 1 ≤ logRatio z D' := le_trans (one_le_loBnd side') hlow
        have hstep_par : side' % 2 ≠ m % 2 := by omega
        rw [T_peel s' side' D' m hside' hm1 hD']
        refine le_trans (Finset.sum_le_sum (fun p hp => ?_))
          (hstepW s' z side' D' m hside' hD' hm1 (hτ0 m) hz hguard hnu hS1 hupper hlow hstep_par
            (hτrec m))
        obtain ⟨hp_pf, hp_win⟩ := Finset.mem_filter.mp hp
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
        have hp_dvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hp_pf
        have hnu_pos : 0 ≤ s'.nu p := (s'.nu_pos_of_prime p hp_prime hp_dvd).le
        have hflip : 3 - side' = 1 ∨ 3 - side' = 2 := by rcases hside' with rfl | rfl <;> omega
        have hpar_child : (3 - side') % 2 = m % 2 := by omega
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
          (ih hm1 (sieveBelow s' p) p (3 - side') (cdiv D' p) hflip hpar_child (one_le_cdiv D' p)
            hzsub hguardsub hnusub hlowsub) hnu_pos
      · -- above the window: T_vanish
        rw [T_vanish s' side' D' (m + 1) z hD' hz (by push_cast; linarith [not_le.mp hupper])]
        exact fseqBound'_nonneg ε tau hε s' z side' D' (m + 1) (hτ0 (m + 1))

/-! ## Part C — the conditioned `hlevel` plugs -/

/-- **Conditioned windowed `hlevel`, upper.**  `hlevel_wp_upper` consuming the conditioned
induction: the odd filter supplies the parity invariant `1 % 2 = n % 2` (`Odd n`). -/
theorem hlevel_wpc_upper (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ) (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWPC cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D) :
    ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
      T s 1 D n
        ≤ Salt.BrunLower.W s * (fseq n (logRatio zTop D)
            + ε * tau n * Real.exp 2 * hBJS (logRatio zTop D)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hn1 : 1 ≤ n := by rcases hn.2 with ⟨k, rfl⟩; omega
  have hpar : 1 % 2 = n % 2 := by have h := Nat.odd_iff.mp hn.2; omega
  have hlow : loBnd 1 ≤ logRatio zTop D := by rw [loBnd_one]; exact hStop
  have h := T_le_of_peel_step_wpc cf ch ε K tau hε hKe htau1 hτ0 h4 hstepW hτrec
    n hn1 s zTop 1 D (Or.inl rfl) hpar hD hzTop hguard hnu hlow
  simpa [fseqBound'] using h

/-- **Conditioned windowed `hlevel`, lower.**  The even mirror: the `n = 0` term is direct
(`T_zero`), and each `n ≥ 2` even supplies the parity invariant `2 % 2 = n % 2`. -/
theorem hlevel_wpc_lower (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ) (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWPC cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
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
  · have hpar : 2 % 2 = n % 2 := by have h := Nat.even_iff.mp hn.2; omega
    have hlow : loBnd 2 ≤ logRatio zTop D := by rw [loBnd_two]; exact hStop
    have h := T_le_of_peel_step_wpc cf ch ε K tau hε hKe htau1 hτ0 h4 hstepW hτrec
      n hn1 s zTop 2 D (Or.inr rfl) hpar hD hzTop hguard hnu hlow
    simpa [fseqBound'] using h

/-! ## Part D — the conditioned keystones `bjs_theorem6_windowed_c` -/

/-- **BJS Theorem 6 (5), windowed, PARAMETRIC & CONDITIONED (upper) — KEYSTONE.**  As
`bjs_theorem6_windowed_p_upper` but with the conditioned contract `hstepW : StepHypWPC`.  The
upper sums ODD depths at side 1 (matching `hTbound_upper_of_levels`); no top-parity side
condition is needed (the odd filter handles the top automatically). -/
theorem bjs_theorem6_windowed_c_upper (s : BoundingSieve) (zTop D : ℕ) (ε K C₁ : ℝ)
    (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWPC cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (logRatio zTop D) + ε * C₁ * Real.exp 2 * hBJS (logRatio zTop D)) :=
  hmain_upper_of_levels s D (logRatio zTop D) ε C₁ tau hε
    (hlevel_wpc_upper s zTop D ε K cf ch tau hD hzTop hguard hnu hε hKe htau1 hτ0 hstepW hτrec h4
      hStop) htau

/-- **BJS Theorem 6 (6), windowed, PARAMETRIC & CONDITIONED (lower) — KEYSTONE.**  The lower
sums EVEN depths at side 2 (matching `hTbound_lower_of_levels`). -/
theorem bjs_theorem6_windowed_c_lower (s : BoundingSieve) (zTop D : ℕ) (ε K C₂ : ℝ)
    (cf ch : ℕ → ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hstepW : StepHypWPC cf ch ε tau)
    (hτrec : ∀ n, cf n + ε * Real.exp 2 * ch n * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 2 ≤ logRatio zTop D)
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    Salt.BrunLower.W s *
        (fchain (maxDepth s) (logRatio zTop D) - ε * C₂ * Real.exp 2 * hBJS (logRatio zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  hmain_lower_of_levels s D (logRatio zTop D) ε C₂ tau hε
    (hlevel_wpc_lower s zTop D ε K cf ch tau hD hzTop hguard hnu hε hKe htau1 hτ0 hstepW hτrec h4
      hStop) htau

/-! ## Part E — the B-mirror: the boundary-padded sharp coefficients (FREEZE V2 gate) -/

/-- **The boundary-padded sharp `f`-forcing** `cfSharpB`.  `n = 0` anchor `3εe²` (matching
`τ₁ = 3`); `n ≥ 1` forcing `20εe²(99/100)ⁿ` — the factor 20 envelopes the odd-flat (BJS (39))
`f`-boundary `3K(K−1)f-edge` on top of the honest K-excess/z-edge terms (gate: ~2.5× cushion). -/
noncomputable def cfSharpB (n : ℕ) (ε : ℝ) : ℝ :=
  if n = 0 then 3 * ε * Real.exp 2 else 20 * ε * Real.exp 2 * (99 / 100) ^ n

/-- **The boundary-padded sharp `h`-multiplier** `chSharpB ε = (1+ε)(49/50) + 4ε`.  The `4ε`
pad envelopes the (36)-boundary defect `(K−1)g(s−1) ≤ ε·γ₃ʰ·g(s)` (`γ₃ʰ ≤ 4`) on top of E₁a's
`(1+ε)(49/50)`.  Contracts (`< 1`) exactly for `ε < 1/249` (NOT `ε < 1/49`). -/
noncomputable def chSharpB (ε : ℝ) : ℝ := (1 + ε) * (49 / 50) + 4 * ε

theorem cfSharpB_zero (ε : ℝ) : cfSharpB 0 ε = 3 * ε * Real.exp 2 := by
  unfold cfSharpB; rw [if_pos rfl]

theorem cfSharpB_of_pos {n : ℕ} (hn : n ≠ 0) (ε : ℝ) :
    cfSharpB n ε = 20 * ε * Real.exp 2 * (99 / 100) ^ n := by
  unfold cfSharpB; rw [if_neg hn]

theorem cfSharpB_nonneg (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ cfSharpB n ε := by
  unfold cfSharpB
  split
  · exact mul_nonneg (mul_nonneg (by norm_num) hε) (Real.exp_pos 2).le
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (Real.exp_pos 2).le)
      (by positivity)

theorem chSharpB_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ chSharpB ε := by
  unfold chSharpB; nlinarith [hε]

/-- **The contraction** `chSharpB ε < 1` for `ε < 1/249` (the gate-computed exact threshold:
`(49/50 + 4)ε < 1/50 ⟺ 249ε < 1`).  Do NOT use `1/49`. -/
theorem chSharpB_lt_one {ε : ℝ} (h : ε < 1 / 249) : chSharpB ε < 1 := by
  unfold chSharpB; nlinarith [h]

/-- **The B-mirror sharp τ-sequence** `tauSharpB`: `τ₀ = 0`, `τ_{n+1} = (n=0 ? 3 : 20(99/100)ⁿ)
+ chSharpB ε·τₙ`, so `τ₁ = 3` exactly (the keystones' `htau1`).  The `n = 0` forcing anchor is
`3` (not `20`) — the case split the gate flagged. -/
noncomputable def tauSharpB (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => (if n = 0 then 3 else 20 * (99 / 100) ^ n) + chSharpB ε * tauSharpB ε n

@[simp] theorem tauSharpB_zero (ε : ℝ) : tauSharpB ε 0 = 0 := rfl

theorem tauSharpB_succ (ε : ℝ) (n : ℕ) :
    tauSharpB ε (n + 1)
      = (if n = 0 then 3 else 20 * (99 / 100) ^ n) + chSharpB ε * tauSharpB ε n := rfl

/-- `τ₁ = 3` exactly (the keystones' base anchor `htau1`). -/
@[simp] theorem tauSharpB_one (ε : ℝ) : tauSharpB ε 1 = 3 := by
  have h := tauSharpB_succ ε 0
  rw [tauSharpB_zero] at h
  simpa using h

/-- `τ_{n+1} = 20(99/100)ⁿ + chSharpB ε·τₙ` for `n ≥ 1` (the else branch of the forcing). -/
theorem tauSharpB_succ_of_pos {n : ℕ} (hn : n ≠ 0) (ε : ℝ) :
    tauSharpB ε (n + 1) = 20 * (99 / 100) ^ n + chSharpB ε * tauSharpB ε n := by
  rw [tauSharpB_succ, if_neg hn]

theorem tauSharpB_nonneg {ε : ℝ} (hε : 0 ≤ ε) : ∀ n, 0 ≤ tauSharpB ε n
  | 0 => by rw [tauSharpB_zero]
  | (n + 1) => by
      rw [tauSharpB_succ]
      refine add_nonneg ?_ (mul_nonneg (chSharpB_nonneg hε) (tauSharpB_nonneg hε n))
      split
      · norm_num
      · positivity

/-- **The keystone's `hτrec`, GLOBAL (all `n`), DISCHARGED — the case-split of the gate.**
`cfSharpB n ε + εe²·chSharpB ε·τₙ ≤ εe²·τ_{n+1}`, an EQUALITY for every `n` by construction:
`n = 0` gives `3εe² = εe²·τ₁ = 3εe²`; `n ≥ 1` gives `20εe²(99/100)ⁿ` on both sides.  (Catch
#29 dissolves as for `tauSharp`: `cfSharpB 0 ε = 3εe²` is tiny, not `≥ 3168`.) -/
theorem tauSharpB_hτrec {ε : ℝ} (n : ℕ) :
    cfSharpB n ε + ε * Real.exp 2 * chSharpB ε * tauSharpB ε n
      ≤ ε * Real.exp 2 * tauSharpB ε (n + 1) := by
  refine le_of_eq ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cfSharpB_zero, tauSharpB_zero, tauSharpB_one]; ring
  · rw [cfSharpB_of_pos hn.ne', tauSharpB_succ_of_pos hn.ne']; ring

/-! ## Part F — the B-mirror sums (`Στ ≤ CsharpB`, the finite achieved constant) -/

/-- The B-mirror achieved constant `CsharpB ε = 2000/(1 − chSharpB ε)` (→ 100000 as ε → 0). -/
noncomputable def CsharpB (ε : ℝ) : ℝ := 2000 / (1 - chSharpB ε)

/-- **The numeric τ-close (both parities), DISCHARGED.**  `Σ_{n<M} tauSharpB ε n ≤ CsharpB ε`,
uniform in `M`, via `tau_sum_le_of_recursion` at `a = 20`, `r = 99/100`, `β = chSharpB ε < 1`.
The `hrec` slot is the gate-flagged case split: `n = 0` is the INEQUALITY `3 ≤ 20`; `n ≥ 1` is
the equality. -/
theorem tauSharpB_sum_le {ε : ℝ} (hε : 0 ≤ ε) (h249 : ε < 1 / 249) (M : ℕ) :
    ∑ n ∈ Finset.range M, tauSharpB ε n ≤ CsharpB ε := by
  have hrec : ∀ n, tauSharpB ε (n + 1) ≤ 20 * (99 / 100) ^ n + chSharpB ε * tauSharpB ε n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [tauSharpB_succ, tauSharpB_zero]; norm_num
    · exact le_of_eq (tauSharpB_succ_of_pos hn.ne' ε)
  have h := tau_sum_le_of_recursion (tauSharpB ε) 20 (99 / 100) (chSharpB ε)
    (by norm_num) (by norm_num) (chSharpB_nonneg hε) (chSharpB_lt_one h249) (by norm_num)
    (tauSharpB_nonneg hε) hrec M
  have heq : (tauSharpB ε 0 + 20 / (1 - 99 / 100)) / (1 - chSharpB ε) = CsharpB ε := by
    rw [tauSharpB_zero, CsharpB]; congr 1; norm_num
  rwa [heq] at h

/-- **The odd-filtered τ-close** (`htau` slot, upper): `Σ_{n<N, odd} tauSharpB ε n ≤ CsharpB ε`. -/
theorem tauSharpB_sum_odd_le {ε : ℝ} (hε : 0 ≤ ε) (h249 : ε < 1 / 249) (N : ℕ) :
    ∑ n ∈ (Finset.range N).filter (fun n => Odd n), tauSharpB ε n ≤ CsharpB ε :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => tauSharpB_nonneg hε i)) (tauSharpB_sum_le hε h249 N)

/-- **Even-filtered τ-close** (`htau`, lower): `Σ_{n<N, even} tauSharpB ε n ≤ CsharpB ε`. -/
theorem tauSharpB_sum_even_le {ε : ℝ} (hε : 0 ≤ ε) (h249 : ε < 1 / 249) (N : ℕ) :
    ∑ n ∈ (Finset.range N).filter (fun n => Even n), tauSharpB ε n ≤ CsharpB ε :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => tauSharpB_nonneg hε i)) (tauSharpB_sum_le hε h249 N)

/-- **The concrete achieved constant** at the Amendment-3 `ε_sieve = 2·10⁻⁸`:
`CsharpB (2/10⁸) ≤ 100001` (exactly `≈ 100000.498`). -/
theorem CsharpB_frozen : CsharpB (2 / 100000000) ≤ 100001 := by
  unfold CsharpB chSharpB; norm_num

/-! ## Part G — the B-plugs: the conditioned keystones at the B-coefficients -/

/-- **BJS Theorem 6 (5), windowed, CONDITIONED & B-INSTANTIATED (upper) — the E₁d′ payoff.**
`bjs_theorem6_windowed_c_upper` at `(cfSharpB ·, chSharpB ·, tauSharpB ε, CsharpB ε)` with the
entire numeric τ-layer DISCHARGED (`hτrec` by `tauSharpB_hτrec`, `htau` by
`tauSharpB_sum_odd_le`, `τ₁` by `tauSharpB_one`, nonneg by `tauSharpB_nonneg`).  The ONLY
remaining per-step slot is `hstepWPC : StepHypWPC (cfSharpB ·) (chSharpB ·) ε (tauSharpB ε)` —
nodes E₁c-hh/hf. -/
theorem bjs_theorem6_windowed_cB_upper (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (h249 : ε < 1 / 249) (hKe : K ≤ 1 + ε)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop D) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (logRatio zTop D)
          + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio zTop D)) :=
  bjs_theorem6_windowed_c_upper s zTop D ε K (CsharpB ε)
    (fun n => cfSharpB n ε) (fun _ => chSharpB ε) (tauSharpB ε)
    hD hzTop hguard hnu hε hKe (tauSharpB_one ε) (tauSharpB_nonneg hε) hstepWPC
    (fun n => tauSharpB_hτrec n) h4 hStop (tauSharpB_sum_odd_le hε h249 (maxDepth s + 1))

/-- **BJS Theorem 6 (6), windowed, CONDITIONED & B-INSTANTIATED (lower) — the E₁d′ payoff.**
The dual lower B-plug, `htau` via `tauSharpB_sum_even_le`. -/
theorem bjs_theorem6_windowed_cB_lower (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (h249 : ε < 1 / 249) (hKe : K ≤ 1 + ε)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 2 ≤ logRatio zTop D) :
    Salt.BrunLower.W s *
        (fchain (maxDepth s) (logRatio zTop D)
          - ε * CsharpB ε * Real.exp 2 * hBJS (logRatio zTop D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  bjs_theorem6_windowed_c_lower s zTop D ε K (CsharpB ε)
    (fun n => cfSharpB n ε) (fun _ => chSharpB ε) (tauSharpB ε)
    hD hzTop hguard hnu hε hKe (tauSharpB_one ε) (tauSharpB_nonneg hε) hstepWPC
    (fun n => tauSharpB_hτrec n) h4 hStop (tauSharpB_sum_even_le hε h249 (maxDepth s + 1))

end Salt.Chen
