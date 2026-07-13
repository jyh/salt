/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.DecayMass

/-!
# C1c¹⁰ — the windowed `StepHyp` contract and the keystone composition (catch #28)

C1c⁹ (`DecayMass.stepHyp_pointwise`) composed the two sharp Stieltjes comparisons at every
*operating point inside the window*, but `StepBound2.StepHyp` is a **bare `∀`** ranging over
points *outside* the window where the comparisons are false as stated (catch #28).  The
Fable adjudication: those out-of-window points are **trivial, not false** — a first-violation
chain `p₁ > ⋯ > pₙ` has `(p₁⋯pₙ)·pₙ² ≥ D` with every `pᵢ < z`, so `D ≤ z^{n+2}`, hence
`T = 0` whenever `log D / log z > n + 2` (`T_vanish`).

This file executes the windowed redesign:

* **`T_vanish`** (the key lemma): the out-of-window (above) combinatorial vanishing.  The
  honest offset is `n + 2` (each of the `n` chain primes and the squared minimal prime is
  `< z`), exactly tiling the pointwise window `logRatio z D' ≤ n + 3` at parent depth `n + 1`.

* **`StepHypW`** (the windowed contract): `StepHyp`-shaped but restricted to the sieve-class
  side conditions (`hguard`/`hnu`) and the operating window `1 ≤ logRatio z D' ≤ n + 3`.
  `stepHyp_pointwise` discharges it directly (`stepHypW_holds`).

* **`T_le_of_peel_step_w`** (the windowed induction): re-runs `StepBound2.T_le_of_peel_step'`
  carrying a *side-dependent lower window* `loBnd side' ≤ logRatio z D'`
  (`loBnd 1 = 1`, `loBnd 2 = 2`).  At each level the operating point is either
  above the window (`T_vanish`: `T = 0 ≤ B`) or inside it (peel + `StepHypW`).  The
  **below-window case never arises**: the window is *maintained* by the recursion — the
  odd-side peel filter `p³ < D'` forces every even child to `σ ≥ 2`, and an even parent with
  `σ ≥ 2` forces every odd child to `σ ≥ 1` (both via `⌈D'/p⌉ ≥ D'/p` and `p < z`).  So no
  named below-window hypothesis is needed; see the design note below and the report.

* **The composition**: `stepHypW_holds → T_le_of_peel_step_w → hlevel_w_{upper,lower}`,
  re-threaded through `Lemma11.hmain_{upper,lower}_of_levels` to
  **`bjs_theorem6_windowed_{upper,lower}`** — BJS Theorem 6 (5)/(6) at the top operating
  point `logRatio zTop D`, with the per-step comparison now a *proven theorem*
  (`stepHyp_pointwise`) rather than a named `∀`-hypothesis.  The only remaining named
  hypotheses are the parametric τ-recursion `hτrec` and τ-sum `htau` (deferred per the C0
  ledger), plus the structural sieve-class inputs (`hguard`/`hnu`/`h4`).  **Keystone 1 (the
  linear-sieve per-step comparison, catch #27/#28) is analytically complete.**

## The below-window investigation (resolved: children never carry below-window mass)

A below-window node (`σ = logRatio z D' < 1`, i.e. `D' < z`) *can* have `T > 0` (e.g. a
length-1 odd chain `p` with `D' ≤ p³`), so the universal windowed bound is genuinely false
there and cannot be forced.  The resolution is that such nodes never occur inside the
recursion from an in-window top: the induction carries `loBnd side' ≤ logRatio z D'` as an
invariant, and the peel maps it to the children —

* odd → even: the filter `p³ < D'` gives `log D'/log p > 3`, so
  `σ_child ≥ log D'/log p − 1 > 2` (`logRatio_child_lower`, `side' = 1` branch);
* even → odd: `σ_parent ≥ 2` and `p < z` give `log D'/log p ≥ σ_parent ≥ 2`, so
  `σ_child ≥ log D'/log p − 1 ≥ 1` (`side' = 2` branch).

Thus every child lands in its side's window, the induction hypothesis applies, and the
below-window branch is provably vacuous — no fallback mass bound, no named hypothesis.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the side-dependent lower window `loBnd` -/

/-- The side-dependent lower edge of the operating window: odd side (position 1 is the
`p³ < D'` check) needs `σ ≥ 1`, even side needs `σ ≥ 2` (so that its odd children, which the
unfiltered even peel produces, still satisfy `σ ≥ 1`). -/
def loBnd (side : ℕ) : ℝ := if side % 2 = 1 then 1 else 2

theorem loBnd_one : loBnd 1 = 1 := by norm_num [loBnd]

theorem loBnd_two : loBnd 2 = 2 := by norm_num [loBnd]

theorem one_le_loBnd (side : ℕ) : (1 : ℝ) ≤ loBnd side := by
  unfold loBnd; split <;> norm_num

/-- `fseqBound' logRatio` is nonnegative (`W > 0`, `fₙ ≥ 0`, `h > 0`, `ε, τₙ ≥ 0`). -/
theorem fseqBound'_nonneg (ε : ℝ) (tau : ℕ → ℝ) (hε : 0 ≤ ε)
    (s' : BoundingSieve) (z side' D' n : ℕ) (hτ0 : 0 ≤ tau n) :
    0 ≤ fseqBound' logRatio ε tau s' z side' D' n := by
  simp only [fseqBound']
  refine mul_nonneg (Salt.BrunLower.W_pos s').le (add_nonneg (fseq_nonneg n (logRatio z D')) ?_)
  exact mul_nonneg (mul_nonneg (mul_nonneg hε hτ0) (Real.exp_pos 2).le) (hBJS_pos _).le

/-! ## Part B — `T_vanish`, the out-of-window (above) combinatorial vanishing -/

/-- **`T_vanish` (the key lemma).**  A first-violation chain `c = p₁ > ⋯ > pₙ` of depth `n`
satisfies `D ≤ c·(rmin c)²` while every prime of `c` is `< z`, hence `D < z^{n+2}`, i.e.
`logRatio z D < n + 2`.  Contrapositive: if `logRatio z D > n + 2` the chain set is empty,
so `T s side D n = 0`.  This is the out-of-window branch of the windowed induction. -/
theorem T_vanish (s : BoundingSieve) (side D n z : ℕ) (hD : 1 ≤ D)
    (hz : ∀ q ∈ s.prodPrimes.primeFactors, q < z)
    (hσ : (n : ℝ) + 2 < logRatio z D) :
    T s side D n = 0 := by
  rw [T]
  apply Finset.sum_eq_zero
  intro c hc
  exfalso
  obtain ⟨hcdvd, hviol, hlen⟩ := Finset.mem_filter.mp hc
  have hcdvd' : c ∣ s.prodPrimes := (Nat.mem_divisors.mp hcdvd).1
  have hcsf : Squarefree c := s.prodPrimes_squarefree.squarefree_of_dvd hcdvd'
  have hn1 : 1 ≤ n := by rw [← hlen]; exact hviol.1
  have hsub : c.primeFactors ⊆ s.prodPrimes.primeFactors :=
    Nat.primeFactors_mono hcdvd' s.prodPrimes_squarefree.ne_zero
  have hcard : c.primeFactors.card = n := by rw [← rlist_length, hlen]
  have hne : c.primeFactors.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  -- the violation inequality `D ≤ c · (rmin c)²`
  have hviolineq : D ≤ rprefix c (rlist c).length * (relem c ((rlist c).length - 1)) ^ 2 :=
    hviol.2.2.1
  rw [rprefix_full hcsf] at hviolineq
  have hDcr_nat : D ≤ c * (rmin c) ^ 2 := hviolineq
  have hDcr : (D : ℝ) ≤ (c : ℝ) * (rmin c : ℝ) ^ 2 := by exact_mod_cast hDcr_nat
  -- `rmin c` is a prime factor of `c`, hence `< z`
  have hrmem : rmin c ∈ c.primeFactors := by
    have hlt : (rlist c).length - 1 < (rlist c).length := by rw [rlist_length, hcard]; omega
    have hrfl : rmin c = (rlist c).getD ((rlist c).length - 1) 1 := rfl
    rw [hrfl, List.getD_eq_getElem _ _ hlt]
    exact rlist_mem.mp (List.getElem_mem _)
  have hrlt : (rmin c : ℝ) < (z : ℝ) := by exact_mod_cast hz (rmin c) (hsub hrmem)
  have hr2 : (2 : ℝ) ≤ (rmin c : ℝ) := by
    have := (Nat.prime_of_mem_primeFactors hrmem).two_le; exact_mod_cast this
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  -- `c < z^n`
  have hcprod : (c : ℝ) = ∏ p ∈ c.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hcsf]
  have hcz : (c : ℝ) < (z : ℝ) ^ n := by
    rw [hcprod]
    calc ∏ p ∈ c.primeFactors, (p : ℝ)
        < ∏ _p ∈ c.primeFactors, (z : ℝ) := by
          refine Finset.prod_lt_prod_of_nonempty (fun p hp => ?_) (fun p hp => ?_) hne
          · have h2 : (2 : ℝ) ≤ (p : ℝ) := by
              have := (Nat.prime_of_mem_primeFactors hp).two_le; exact_mod_cast this
            linarith
          · exact_mod_cast hz p (hsub hp)
      _ = (z : ℝ) ^ n := by rw [Finset.prod_const, hcard]
  -- `(rmin c)² < z²`
  have hr2z : (rmin c : ℝ) ^ 2 < (z : ℝ) ^ 2 := by nlinarith [hrlt, hr2]
  -- `D < z^{n+2}`
  have hDz : (D : ℝ) < (z : ℝ) ^ (n + 2) := by
    calc (D : ℝ) ≤ (c : ℝ) * (rmin c : ℝ) ^ 2 := hDcr
      _ < (z : ℝ) ^ n * (z : ℝ) ^ 2 :=
          mul_lt_mul'' hcz hr2z (Nat.cast_nonneg c) (by positivity)
      _ = (z : ℝ) ^ (n + 2) := by rw [pow_add]
  -- `log D < (n+2) log z`, hence `logRatio z D < n+2`, contradicting `hσ`
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hlogD : Real.log D < ((n : ℝ) + 2) * Real.log z := by
    have h := Real.log_lt_log hDpos hDz
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlt : logRatio z D < (n : ℝ) + 2 := by
    rw [logRatio, div_lt_iff₀ hlogz]; linarith
  linarith

/-! ## Part C — the window-propagation lemmas (children stay in-window) -/

/-- **The child operating-point lower bound.**  From `⌈D'/p⌉ ≥ D'/p`, the child point
`logRatio p ⌈D'/p⌉ = log⌈D'/p⌉/log p ≥ log D'/log p − 1`. -/
theorem logRatio_child_ge {D' p : ℕ} (hD : 1 ≤ D') (hp : p.Prime) :
    Real.log D' / Real.log p - 1 ≤ logRatio p (cdiv D' p) := by
  have hp1 : 1 ≤ p := hp.one_le
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hDpos : (0 : ℝ) < (D' : ℝ) := by exact_mod_cast hD
  have hDlemul : (D' : ℝ) ≤ (p : ℝ) * (cdiv D' p : ℝ) := by
    have h := (mul_lt_iff_lt_cdiv hp1 hD (cdiv D' p)).not.mpr (lt_irrefl (cdiv D' p))
    have hnat : D' ≤ p * cdiv D' p := Nat.not_lt.mp h
    exact_mod_cast hnat
  have hlogcdiv : Real.log D' - Real.log p ≤ Real.log (cdiv D' p) := by
    have hle : (D' : ℝ) / (p : ℝ) ≤ (cdiv D' p : ℝ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ))]; linarith
    have hdivpos : (0 : ℝ) < (D' : ℝ) / (p : ℝ) := by positivity
    have hlog := Real.log_le_log hdivpos hle
    rwa [Real.log_div (ne_of_gt hDpos) (by linarith : (p : ℝ) ≠ 0)] at hlog
  rw [logRatio]
  have heq : Real.log D' / Real.log p - 1 = (Real.log D' - Real.log p) / Real.log p := by
    field_simp
  rw [heq]
  gcongr

/-- **Window propagation.**  If the parent operating point satisfies `loBnd side'`, then every
peeled child (side `3 − side'`, cutoff `p`, level `⌈D'/p⌉`) satisfies `loBnd (3 − side')`.  Odd
parents use the filter `p³ < D'` (`σ_child > 2`); even parents use `σ_parent ≥ 2` and `p < z`
(`σ_child ≥ 1`). -/
theorem logRatio_child_lower {s' : BoundingSieve} {z side' D' p : ℕ}
    (hD : 1 ≤ D') (hside' : side' = 1 ∨ side' = 2)
    (hp_pf : p ∈ s'.prodPrimes.primeFactors)
    (hp_win : side' % 2 = 1 → p ^ 3 < D')
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hlow : loBnd side' ≤ logRatio z D') :
    loBnd (3 - side') ≤ logRatio p (cdiv D' p) := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hkey : Real.log D' / Real.log p - 1 ≤ logRatio p (cdiv D' p) := logRatio_child_ge hD hp
  rcases hside' with rfl | rfl
  · -- side' = 1, child even: `p³ < D'` ⟹ `log D'/log p > 3`
    have hpD : p ^ 3 < D' := hp_win (by norm_num)
    have hpDR : (p : ℝ) ^ 3 < (D' : ℝ) := by exact_mod_cast hpD
    have hlogpow : Real.log ((p : ℝ) ^ 3) < Real.log D' := Real.log_lt_log (by positivity) hpDR
    rw [Real.log_pow] at hlogpow
    push_cast at hlogpow
    have h3 : (3 : ℝ) < Real.log D' / Real.log p := by rw [lt_div_iff₀ hlogp]; linarith
    rw [show (3 : ℕ) - 1 = 2 from rfl, loBnd_two]
    linarith
  · -- side' = 2, child odd: `σ_parent ≥ 2` and `p < z` ⟹ `log D'/log p ≥ 2`
    rw [show (3 : ℕ) - 2 = 1 from rfl, loBnd_one]
    rw [loBnd_two, logRatio] at hlow
    have hpz : (p : ℝ) < (z : ℝ) := by exact_mod_cast hz p hp_pf
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    have hlogpz : Real.log p ≤ Real.log z := Real.log_le_log (by linarith) hpz.le
    have hlogD : 0 < Real.log D' := by
      have h2z : (2 : ℝ) * Real.log z ≤ Real.log D' := (le_div_iff₀ hlogz).mp hlow
      linarith
    have hdiv : Real.log D' / Real.log z ≤ Real.log D' / Real.log p :=
      div_le_div_of_nonneg_left hlogD.le hlogp hlogpz
    linarith

/-! ## Part D — the windowed contract `StepHypW` -/

/-- **The windowed per-step contract** (`StepBound2.StepHyp`-shaped, restricted to the
operating window + sieve-class conditions).  Exactly `DecayMass.stepHyp_pointwise`'s statement,
so it is discharged directly (`stepHypW_holds`). -/
def StepHypW (ε : ℝ) (tau : ℕ → ℝ) : Prop :=
  ∀ (s' : BoundingSieve) (z side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
    0 ≤ tau n →
    (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
    (∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
    (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
    1 ≤ logRatio z D' → logRatio z D' ≤ (n : ℝ) + 3 →
    (cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n ≤ ε * Real.exp 2 * tau (n + 1)) →
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * fseqBound' logRatio ε tau (sieveBelow s' p) p (3 - side') (cdiv D' p) n)
      ≤ fseqBound' logRatio ε tau s' z side' D' (n + 1)

/-- **`StepHypW` holds** — discharged pointwise by `DecayMass.stepHyp_pointwise`.  This is the
catch-#28 fix: the per-step comparison is a *proven theorem* on the window, not a hypothesis. -/
theorem stepHypW_holds (ε : ℝ) (hε : 0 ≤ ε) (tau : ℕ → ℝ) : StepHypW ε tau :=
  fun s' z side' D' n hside hD hn hτ0 hz hguard hnu hS1 hSn hτrec =>
    stepHyp_pointwise s' ε tau z side' D' n hε hn hD hτ0 hside hz hguard hnu hS1 hSn hτrec

/-! ## Part E — the windowed Buchstab induction -/

/-- **The windowed cutoff-threaded induction.**  `StepBound2.T_le_of_peel_step'` re-run with
the operating window carried as a side-dependent invariant `loBnd side' ≤ logRatio z D'`.  At
each level the point is above the window (`T_vanish`: `T = 0 ≤ B`) or inside it (peel +
`StepHypW`); the below-window branch is vacuous because the peel maps the invariant to the
children (`logRatio_child_lower`).  The base uses `Lemma11.hlevel_one_upper`
(`1 ≤ σ ≤ 3`) / `T_vanish` (`σ > 3`) / `T_two_one_zero` (even). -/
theorem T_le_of_peel_step_w (ε K : ℝ) (tau : ℕ → ℝ)
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hstepW : StepHypW ε tau)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
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
      · -- inside the window: peel + StepHypW
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

/-! ## Part F — the windowed `hlevel` plugs and the keystone `bjs_theorem6_windowed` -/

/-- **Windowed `hlevel`, upper.**  The top odd sieve `(s, zTop, 1, D)` with the operating
window `1 ≤ logRatio zTop D` produces `Lemma11`'s exact upper `hlevel` shape. -/
theorem hlevel_w_upper (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
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
  have h := T_le_of_peel_step_w ε K tau hε hKe htau1 hτ0 h4 (stepHypW_holds ε hε tau) hτrec
    n hn1 s zTop 1 D (Or.inl rfl) hD hzTop hguard hnu hlow
  simpa [fseqBound'] using h

/-- **Windowed `hlevel`, lower.**  The top even sieve `(s, zTop, 2, D)` with the operating
window `2 ≤ logRatio zTop D` produces `Lemma11`'s exact lower `hlevel` shape (the `n = 0` term
is handled directly). -/
theorem hlevel_w_lower (s : BoundingSieve) (zTop D : ℕ) (ε K : ℝ) (tau : ℕ → ℝ)
    (hD : 1 ≤ D) (hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ s.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
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
    have h := T_le_of_peel_step_w ε K tau hε hKe htau1 hτ0 h4 (stepHypW_holds ε hε tau) hτrec
      n hn1 s zTop 2 D (Or.inr rfl) hD hzTop hguard hnu hlow
    simpa [fseqBound'] using h

/-- **BJS Theorem 6 (5), windowed (upper) — KEYSTONE.**  The explicit upper main-term
comparison at the top operating point `logRatio zTop D`, with the per-step comparison
*discharged* (`stepHyp_pointwise`, not a hypothesis).  Remaining named inputs: the sieve-class
conditions (`hguard`/`hnu`/`h4`), `ε ≥ 0`, `K ≤ 1+ε`, `τ₁ = 3`, the parametric τ-recursion
`hτrec`, the τ-sum `htau`, and the operating window `1 ≤ logRatio zTop D`. -/
theorem bjs_theorem6_windowed_upper (s : BoundingSieve) (zTop D : ℕ) (ε K C₁ : ℝ) (tau : ℕ → ℝ)
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
  hmain_upper_of_levels s D (logRatio zTop D) ε C₁ tau hε
    (hlevel_w_upper s zTop D ε K tau hD hzTop hguard hnu hε hKe htau1 hτ0 hτrec h4 hStop) htau

/-- **BJS Theorem 6 (6), windowed (lower) — KEYSTONE.**  The explicit lower main-term
comparison at the top operating point `logRatio zTop D`, per-step comparison discharged. -/
theorem bjs_theorem6_windowed_lower (s : BoundingSieve) (zTop D : ℕ) (ε K C₂ : ℝ) (tau : ℕ → ℝ)
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
  hmain_lower_of_levels s D (logRatio zTop D) ε C₂ tau hε
    (hlevel_w_lower s zTop D ε K tau hD hzTop hguard hnu hε hKe htau1 hτ0 hτrec h4 hStop) htau

end Salt.Chen
