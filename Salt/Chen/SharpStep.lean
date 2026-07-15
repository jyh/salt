/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.AbelStep
import Salt.Chen.Tail
import Salt.BrunLower.MertensWindow

/-!
# C1c⁸ — the sharp Stieltjes comparisons `hf`/`hh` (BJS (32)–(34), PM1-density form)

`AbelStep.stepHyp_of_comparisons` reduces `StepHyp σ ε τ` to two *primitive-Stieltjes*
comparisons — the `f`-part `hf` and the `h`-part `hh`:

  `Σ_{p ∈ window} ν(p)·V(p)·g(σ_p) ≤ W·(fₙ₊₁(σ_z) + c_f·h(σ_z))`   (`g = fₙ`, `hf`)
  `Σ_{p ∈ window} ν(p)·V(p)·h(σ_p) ≤ W·(c_h·h(σ_z))`              (`hh`)

with `σ_p = σ p (⌈D'/p⌉)`, `σ_z = σ z D'`, `V(p) = Vbelow s' p`.  AbelStep's *finding*: the
pushforward comparison is **mandatory** — no crude uniform bound closes, because the total
Stieltjes mass `1 − ∏` has no uniform ratio to the target `W·fₙ₊₁` (`W → 0` along the sieve).

## The route (the PM1-density formulation)

The `W → 0` obstruction is dissolved by hypothesis (4): `V(p) = W·(∏_{q ≥ p}(1−ν q))⁻¹`, and
`(∏_{q ≥ p}(1−ν q))⁻¹ ≤ (1+ε)·log z/log p` (`Hyp4.vratio_window_le` at threshold `u = p`), so

  **`V(p) ≤ (1+ε)·(log z/log p)·W`**   (`Vbelow_le_ratio`, the mandatory pushforward),

which *factors `W` out*.  With `ν(p) ≤ 1/(p−1)` the `f`-comparison becomes a pure prime sum

  `Σ_p ν(p)V(p)fₙ(σ_p) ≤ (1+ε)W·Σ_p (1/(p−1))·(log z/log p)·fₙ(σ_p)`.

The **loglog identity** `d(loglog p) = −du/u` under `u = log D'/log p` (PM1 IS this density)
then compares the remaining prime sum to a loglog-length.  For the `f`-part the key structural
fact is that `fₙ` has *compact support* `[1, n+2)`:

  `fₙ(σ_p) ≠ 0  ⟹  1 ≤ σ_p < n+2  ⟹  D'^{1/(n+3)} < p < D'`,

a prime window of **loglog-length `≤ log(n+3)`, uniform in `D', z`** — so PM1
(`sum_inv_prime_window_le`, `C₃ = 19`) bounds `Σ_{support} 1/(p−1) ≤ log(n+3) + 19/log 2 + 2`
(`prime_support_mass_le`), and the `sup` of `(log z/log p)·fₙ(σ_p) ≤ ((n+3)/S)·2` on the
support closes `hf` with an explicit `c_f`.

## Status / floor (honest; precise flag in `docs/blueprints/flags.md`)

This file lands the **reusable pushforward core** and the **full `f`-comparison for all `n`**:
the mandatory `Vbelow_le_ratio`, the support helpers, the PM1 loglog-length mass bound
`prime_support_mass_le`, the operating-window slack `inv_S_le`, and the assembled `hf_of_window`
(conditional on the sieve-class inputs BJS's Theorem 6 already carries: `ν p ≤ 1/(p−1)`, the
primes past the catch-#22 threshold `w₀` — supplied as the per-prime guard `hguard` — and the
operating window `1 ≤ σ z D' ≤ n+3`).  Its conclusion is exactly `stepHyp_of_comparisons`'s `hf`
slot at `σ = logRatio`, `c_f = cf_const n ε`, an explicit function of `(n, ε)` (the τ-recursion
absorbs any per-`n` value, AbelStep's `ledger_collect`).  The `h`-part is reduced to its isolated
remainder by `hh_reduced` (the same pushforward factors `W` out); the full `hh` is NOT closed by
the support route (`h > 0` has no compact support) — it needs the antitone dyadic-piece integral
comparison, flagged and left for the follow-up.  The bare `hf`/`hh` of `stepHyp_of_comparisons`
are unconditional in `s'`; ours carry the sieve-class hypotheses, so the composition to
`StepHyp` is conditional (the ambient Theorem-6 context supplies them).
-/

open Finset

namespace Salt.Chen

/-! ## Part A — support and boundedness helpers for `fseq` -/

/-- `fₙ(s) = 0` for `s < 1` and `n ≥ 1` (below every parity window: `[1,3]` odd/`f₁`,
`[2,·]` even). -/
theorem fseq_eq_zero_of_lt_one {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : s < 1) : fseq n s = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [fseq_one_eq, if_neg (fun h => absurd h.1 (not_le.mpr hs))]
  · have hm0 : m ≠ 0 := hm.ne'
    by_cases hev : Even (m + 1)
    · exact fseq_even_below hev (by linarith)
    · exact fseq_odd_below hm0 hev hs

/-- `fₙ(s) ≤ 2` for `n ≥ 1`, all `s` (from `Tail.fseq_le` and `hbar ≤ e⁻²`, `(99/100)ⁿ ≤ 1`). -/
theorem fseq_le_two {n : ℕ} (hn : 1 ≤ n) (s : ℝ) : fseq n s ≤ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : fseq (m + 1) s ≤ 2 * Real.exp 2 * (99 / 100) ^ m * hbar s := fseq_le m s
  have h2 : hbar s ≤ Real.exp (-2) := by
    unfold hbar; exact Real.exp_le_exp.mpr (by nlinarith [le_max_right s (2 : ℝ)])
  have h3 : (99 / 100 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hid : (2 : ℝ) * Real.exp 2 * 1 * Real.exp (-2) = 2 := by
    rw [mul_one, mul_assoc, ← Real.exp_add]; norm_num
  calc fseq (m + 1) s ≤ 2 * Real.exp 2 * (99 / 100) ^ m * hbar s := h1
    _ ≤ 2 * Real.exp 2 * 1 * Real.exp (-2) := by
        apply mul_le_mul _ h2 (hbar_pos s).le (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 := hid

/-! ## Part B — the mandatory pushforward `V(p) ≤ (1+ε)·(log z/log p)·W` (hypothesis (4)) -/

/-- **The pushforward comparison** (AbelStep's mandatory step, BJS (32)).  For a sifting prime
`p` past the catch-#22 threshold (`3 ≤ p`, the guard `19/log p + 4/(p−1) ≤ log(1+ε)`), with the
dimension-1 density `ν q ≤ 1/(q−1)` and cutoff `z`, hypothesis (4) at `u = p` gives
`Vbelow s p ≤ (1+ε)·(log z/log p)·W s`.  This factors `W` out of the Stieltjes sum. -/
theorem Vbelow_le_ratio (s : BoundingSieve) {ε z : ℝ} {p : ℕ}
    (hε : 0 ≤ ε) (hp3 : 3 ≤ (p : ℝ)) (hpz : (p : ℝ) ≤ z)
    (hthresh : 19 / Real.log p + 4 / ((p : ℝ) - 1) ≤ Real.log (1 + ε))
    (hz : ∀ q ∈ s.prodPrimes.primeFactors, (q : ℝ) < z)
    (hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1)) :
    Vbelow s p ≤ (1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s := by
  have hW := Salt.BrunLower.W_pos s
  set Phi := ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q : ℕ => (p : ℝ) ≤ (q : ℝ)),
      (1 - s.nu q) with hPhi
  have hPpos : 0 < Phi := by
    apply Finset.prod_pos
    intro q hq
    rw [Finset.mem_filter] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    have hqd : q ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hq.1
    have := s.nu_lt_one_of_prime q hqp hqd; linarith
  have hfeq : s.prodPrimes.primeFactors.filter (fun q => ¬ q < p)
      = s.prodPrimes.primeFactors.filter (fun q : ℕ => (p : ℝ) ≤ (q : ℝ)) := by
    apply Finset.filter_congr
    intro q _
    simp only [not_lt]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  have hWsplit : Salt.BrunLower.W s = Vbelow s p * Phi := by
    rw [Salt.BrunLower.W, Vbelow, belowPrimes, hPhi, ← hfeq,
      Finset.prod_filter_mul_prod_filter_not s.prodPrimes.primeFactors (fun q => q < p)]
  have hVeq : Salt.BrunLower.W s * Phi⁻¹ = Vbelow s p := by
    rw [hWsplit, mul_inv_cancel_right₀ (ne_of_gt hPpos)]
  have hvr : Phi⁻¹ ≤ (1 + ε) * Real.log z / Real.log p :=
    vratio_window_le s hε hp3 hpz hthresh hz hnu
  calc Vbelow s p = Salt.BrunLower.W s * Phi⁻¹ := hVeq.symm
    _ ≤ Salt.BrunLower.W s * ((1 + ε) * Real.log z / Real.log p) :=
        mul_le_mul_of_nonneg_left hvr hW.le
    _ = (1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s := by ring

/-! ## Part C — the loglog-length prime mass bound (PM1 + the change of variables) -/

/-- **The support mass bound** (the reusable comparison lemma; the loglog identity in force).
For a finite set `T` of primes `p` in the `fseq`-support window `D'^{1/(n+3)} < p < D'`
(stated as `p < D'` and `log D' < (n+3)·log p`), the reciprocal mass is uniformly bounded:
`Σ_{p∈T} 1/(p−1) ≤ log(n+3) + 19/log 2 + 2`, **independent of `D'`**.  This is the
`d(loglog p) = −du/u` cancellation: the window's loglog-length is `log(n+3)`, whatever `D'`.
PM1 (`sum_inv_le_of_prime_window`, `C₃ = 19`) supplies the loglog bound (two regimes, base
`D'^{1/(n+3)}` when `≥ 2`, else base `2`); the `1/(p−1)`-vs-`1/p` bridge and the `Σ 1/p²`
telescope supply `+19/log 2 + 2`. -/
theorem prime_support_mass_le (D' n : ℕ) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ (p : ℝ) < D' ∧ Real.log D' < ((n : ℝ) + 3) * Real.log p) :
    ∑ p ∈ T, 1 / ((p : ℝ) - 1) ≤ Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn3pos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hlogn3 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 3) := Real.log_nonneg (by linarith)
  -- (1) the PM1 loglog bound  Σ 1/p ≤ log(n+3) + 19/log 2
  have hLn : ∑ p ∈ T, (1 : ℝ) / p ≤ Real.log ((n : ℝ) + 3) + 19 / Real.log 2 := by
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · rw [hTe, Finset.sum_empty]; positivity
    · obtain ⟨p0, hp0⟩ := hTne
      obtain ⟨hp0p, hp0D, _⟩ := hT p0 hp0
      have hp02R : (2 : ℝ) ≤ (p0 : ℝ) := by exact_mod_cast hp0p.two_le
      have hD3R : (3 : ℝ) ≤ (D' : ℝ) := by
        have hD2 : 2 < D' := by exact_mod_cast (lt_of_le_of_lt hp02R hp0D)
        have : 3 ≤ D' := hD2
        exact_mod_cast this
      have hlogD : 0 < Real.log D' := Real.log_pos (by linarith)
      set L := Real.log D' with hLdef
      by_cases hcase : ((n : ℝ) + 3) * Real.log 2 ≤ L
      · -- large-D' regime: base w = exp(L/(n+3)) ≥ 2
        set w := Real.exp (L / ((n : ℝ) + 3)) with hwdef
        have hwpos : 0 < w := Real.exp_pos _
        have hlogw : Real.log w = L / ((n : ℝ) + 3) := by rw [hwdef, Real.log_exp]
        have hwlog2 : Real.log 2 ≤ Real.log w := by
          rw [hlogw, le_div_iff₀ hn3pos]; linarith [hcase]
        have hw2 : (2 : ℝ) ≤ w := by
          have h := Real.exp_le_exp.mpr hwlog2
          rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hwpos] at h
        have hwD : w ≤ (D' : ℝ) := by
          have h1 : L / ((n : ℝ) + 3) ≤ L := by rw [div_le_iff₀ hn3pos]; nlinarith [hlogD]
          have h := Real.exp_le_exp.mpr h1
          rw [hLdef] at h
          rwa [Real.exp_log (show (0 : ℝ) < (D' : ℝ) by linarith)] at h
        have hpm := Salt.BrunLower.sum_inv_le_of_prime_window (w := w) (z := (D' : ℝ)) hw2 hwD
          (S := T) (fun p hp => by
            obtain ⟨hpp, hpD, hplog⟩ := hT p hp
            have hppos : (0 : ℝ) < (p : ℝ) := by
              have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
              linarith
            refine ⟨hpp, ?_, hpD⟩
            have hlp : L / ((n : ℝ) + 3) < Real.log p := by
              rw [div_lt_iff₀ hn3pos]; linarith [hplog]
            have h := Real.exp_le_exp.mpr hlp.le
            rwa [Real.exp_log hppos] at h)
        have hratio : L / Real.log w = (n : ℝ) + 3 := by
          rw [hlogw, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self (ne_of_gt hlogD),
            mul_one]
        have hlogratio : Real.log (L / Real.log w) = Real.log ((n : ℝ) + 3) := by rw [hratio]
        have h19 : 19 / Real.log w ≤ 19 / Real.log 2 :=
          div_le_div_of_nonneg_left (by norm_num) hlog2 hwlog2
        calc ∑ p ∈ T, (1 : ℝ) / p ≤ Real.log (L / Real.log w) + 19 / Real.log w := hpm
          _ ≤ Real.log ((n : ℝ) + 3) + 19 / Real.log 2 := by rw [hlogratio]; linarith [h19]
      · -- small-D' regime: base w = 2
        replace hcase : L < ((n : ℝ) + 3) * Real.log 2 := not_le.mp hcase
        have hpm := Salt.BrunLower.sum_inv_le_of_prime_window (w := 2) (z := (D' : ℝ)) le_rfl
          (by linarith) (S := T) (fun p hp => by
            obtain ⟨hpp, hpD, _⟩ := hT p hp
            exact ⟨hpp, by exact_mod_cast hpp.two_le, hpD⟩)
        have hlt : L / Real.log 2 < (n : ℝ) + 3 := by rw [div_lt_iff₀ hlog2]; linarith [hcase]
        have hlogle : Real.log (L / Real.log 2) ≤ Real.log ((n : ℝ) + 3) :=
          Real.log_le_log (by positivity) hlt.le
        calc ∑ p ∈ T, (1 : ℝ) / p
            ≤ Real.log (Real.log D' / Real.log 2) + 19 / Real.log 2 := hpm
          _ ≤ Real.log ((n : ℝ) + 3) + 19 / Real.log 2 := by rw [← hLdef]; linarith [hlogle]
  -- (2) the 1/(p−1) bridge and the Σ 1/p² telescope
  have hbridge : ∀ p ∈ T, 1 / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) + 2 / (p : ℝ) ^ 2 := by
    intro p hp
    obtain ⟨hpp, _, _⟩ := hT p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_add_div _ _ (ne_of_gt hp0) (by positivity : ((p : ℝ) ^ 2) ≠ 0),
      div_le_div_iff₀ hp1 (by positivity)]
    nlinarith [mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]
  have hsub : T ⊆ Finset.Icc 2 D' := by
    intro p hp
    obtain ⟨hpp, hpD, _⟩ := hT p hp
    rw [Finset.mem_Icc]
    have : p < D' := by exact_mod_cast hpD
    exact ⟨hpp.two_le, by omega⟩
  have htail : ∑ p ∈ T, 2 / ((p : ℝ) ^ 2) ≤ 2 := by
    have h1 : ∑ p ∈ T, 2 / ((p : ℝ) ^ 2) = 2 * ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    have h2 : ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ ∑ p ∈ Finset.Icc 2 D', 1 / ((p : ℝ) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    have h3 := Salt.BrunLower.sum_one_div_sq_le (M := 2) (K := D') (by norm_num)
    have hle1 : ∑ p ∈ T, 1 / ((p : ℝ) ^ 2) ≤ 1 :=
      le_trans h2 (le_trans h3 (by norm_num))
    rw [h1]; linarith [hle1]
  calc ∑ p ∈ T, 1 / ((p : ℝ) - 1)
      ≤ ∑ p ∈ T, (1 / (p : ℝ) + 2 / (p : ℝ) ^ 2) := Finset.sum_le_sum hbridge
    _ = (∑ p ∈ T, 1 / (p : ℝ)) + ∑ p ∈ T, 2 / ((p : ℝ) ^ 2) := Finset.sum_add_distrib
    _ ≤ (Real.log ((n : ℝ) + 3) + 19 / Real.log 2) + 2 := by linarith [hLn, htail]
    _ = Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2 := by ring

/-! ## Part D — the support window bounds (`fseq n(σ_p) ≠ 0 ⟹ D'^{1/(n+3)} < p < D'`) -/

/-- **The `fseq`-support window in `p`.**  If `fₙ(σ_p) ≠ 0` at `σ_p = log ⌈D'/p⌉/log p` (`n ≥ 1`,
`D' ≥ 1`, `p` prime), then `p` lies in the change-of-variables window: `p < D'` (from the lower
support `σ_p ≥ 1`, i.e. `⌈D'/p⌉ ≥ p`) and `log D' < (n+3)·log p` (from the upper support
`σ_p < n+2` via `⌈D'/p⌉ ≥ D'/p`).  These are exactly the two facts `prime_support_mass_le`
consumes and the head of the `log z/log p ≤ (n+3)/S` change of variables. -/
theorem support_prime_bounds {D' n p : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D') (hp : p.Prime)
    (hne : fseq n (logRatio p (cdiv D' p)) ≠ 0) :
    (p : ℝ) < D' ∧ Real.log D' < ((n : ℝ) + 3) * Real.log p := by
  have hp1 : 1 ≤ p := hp.one_le
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hcdiv1 : (1 : ℝ) ≤ (cdiv D' p : ℝ) := by exact_mod_cast one_le_cdiv D' p
  have hcdivpos : (0 : ℝ) < (cdiv D' p : ℝ) := by linarith
  -- σ_p ≥ 1 (else fseq = 0) and σ_p < n+2 (else fseq = 0)
  have hσ1 : (1 : ℝ) ≤ logRatio p (cdiv D' p) := by
    by_contra h; exact hne (fseq_eq_zero_of_lt_one hn (not_le.mp h))
  have hσn : logRatio p (cdiv D' p) < (n : ℝ) + 2 := by
    by_contra h; exact hne (fseq_eq_zero_of_ge n _ (not_lt.mp h))
  rw [logRatio] at hσ1 hσn
  -- lower: cdiv ≥ p ⟹ p < D'
  have hlogcdiv_ge : Real.log p ≤ Real.log (cdiv D' p) := by
    rw [le_div_iff₀ hlogp, one_mul] at hσ1; exact hσ1
  have hpcdiv : (p : ℝ) ≤ (cdiv D' p : ℝ) := by
    have h := Real.exp_le_exp.mpr hlogcdiv_ge
    rwa [Real.exp_log (by linarith), Real.exp_log hcdivpos] at h
  have hpcdivN : p ≤ cdiv D' p := by exact_mod_cast hpcdiv
  have hpD : (p : ℝ) < (D' : ℝ) := by
    have hp0 : 0 < p := hp1
    have : 1 ≤ (D' - 1) / p := by
      have : 2 ≤ cdiv D' p := le_trans hp.two_le hpcdivN
      rw [cdiv] at this; omega
    have hple : p ≤ D' - 1 := (Nat.one_le_div_iff hp0).mp this
    have : p < D' := by omega
    exact_mod_cast this
  refine ⟨hpD, ?_⟩
  -- upper: cdiv ≥ D'/p ⟹ log D' < (n+3) log p
  have hDlemul : (D' : ℝ) ≤ (p : ℝ) * (cdiv D' p : ℝ) := by
    have h := (mul_lt_iff_lt_cdiv hp1 hD (cdiv D' p)).not.mpr (lt_irrefl (cdiv D' p))
    have : D' ≤ p * cdiv D' p := Nat.not_lt.mp h
    exact_mod_cast this
  have hDp_pos : (0 : ℝ) < (D' : ℝ) := by linarith
  have hlogcdiv_lt : Real.log (cdiv D' p) < ((n : ℝ) + 2) * Real.log p := by
    rw [div_lt_iff₀ hlogp] at hσn; linarith [hσn]
  have hlogDp : Real.log D' - Real.log p ≤ Real.log (cdiv D' p) := by
    have hle : (D' : ℝ) / p ≤ (cdiv D' p : ℝ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ))]; linarith [hDlemul]
    have hdivpos : (0 : ℝ) < (D' : ℝ) / p := by positivity
    have := Real.log_le_log hdivpos hle
    rwa [Real.log_div (by positivity) (by positivity)] at this
  linarith [hlogDp, hlogcdiv_lt]

/-! ## Part E — the operating-window slack `1/S ≤ (n+3)·e^{n+3}·h(S)` on `[1, n+3]` -/

/-- **The operating-window slack.**  On the operating window `1 ≤ S ≤ n+3` (`n ≥ 1`),
`1/S ≤ (n+3)·e^{n+3}·h(S)`.  This is the `s`-uniform conversion that lets the explicit `c_f`
absorb the `1/S` from `(n+3)/S`.  Region-split against `h`'s three branches: `h(S) ≥ h(n+3) =
3(n+3)⁻¹e^{−(n+3)}`, so `(n+3)e^{n+3}·h(S) ≥ 3 ≥ 1 ≥ 1/S`. -/
theorem inv_S_le {n : ℕ} {S : ℝ} (hn : 1 ≤ n) (hS1 : 1 ≤ S) (hSn : S ≤ (n : ℝ) + 3) :
    1 / S ≤ ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S := by
  have hS0 : 0 < S := by linarith
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn3 : (3 : ℝ) ≤ (n : ℝ) + 3 := by linarith
  have hexp_ge_one : ∀ x : ℝ, 0 ≤ x → (1 : ℝ) ≤ Real.exp x := fun x hx => by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hx
  have hge1 : 1 ≤ ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S := by
    rcases le_total S 2 with h2 | h2
    · rw [hBJS_le2 h2]
      have heq : ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * Real.exp (-2)
          = ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 1) := by
        rw [mul_assoc, ← Real.exp_add, show (n : ℝ) + 3 + -2 = (n : ℝ) + 1 by ring]
      rw [heq]
      nlinarith [hexp_ge_one ((n : ℝ) + 1) (by positivity), hn3]
    · rcases le_total S 3 with h3 | h3
      · rw [hBJS_mid h2 h3]
        have heq : ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * Real.exp (-S)
            = ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3 - S) := by
          rw [mul_assoc, ← Real.exp_add, show (n : ℝ) + 3 + -S = (n : ℝ) + 3 - S by ring]
        rw [heq]
        nlinarith [hexp_ge_one ((n : ℝ) + 3 - S) (by linarith), hn3]
      · rw [hBJS_ge3 h3]
        have hexp : Real.exp ((n : ℝ) + 3) * Real.exp (-S) = Real.exp ((n : ℝ) + 3 - S) := by
          rw [← Real.exp_add, show (n : ℝ) + 3 + -S = (n : ℝ) + 3 - S by ring]
        have hrw : ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * (3 * S⁻¹ * Real.exp (-S))
            = 3 * (((n : ℝ) + 3) * S⁻¹) * Real.exp ((n : ℝ) + 3 - S) := by
          rw [← hexp]; ring
        rw [hrw]
        have hninv : (1 : ℝ) ≤ ((n : ℝ) + 3) * S⁻¹ := by
          have h := mul_le_mul_of_nonneg_right hSn (inv_nonneg.mpr hS0.le)
          rwa [mul_inv_cancel₀ (ne_of_gt hS0)] at h
        nlinarith [hexp_ge_one ((n : ℝ) + 3 - S) (by linarith), hninv]
  calc 1 / S ≤ 1 := by rw [div_le_one hS0]; exact hS1
    _ ≤ ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S := hge1

/-! ## Part F — the assembled `f`-comparison `hf` (conditional; the explicit `c_f`) -/

/-- The explicit `f`-coefficient `c_f(n, ε)` (any per-`n` value closes the τ-recursion, per
AbelStep's `ledger_collect`).  Collects the `2` (`fₙ ≤ 2`), the `(1+ε)` (hyp (4)), the `(n+3)`
(the support-window `sup`), the loglog mass `Cbound(n) = log(n+3) + 19/log 2 + 2`, and the
operating-window slack `(n+3)·e^{n+3}` (`inv_S_le`). -/
noncomputable def cf_const (n : ℕ) (ε : ℝ) : ℝ :=
  2 * (1 + ε) * ((n : ℝ) + 3) * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2)
    * (((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3))

/-- **The sharp `f`-comparison `hf`** (BJS (32)–(34), assembled), conditional on the sieve-class
inputs BJS Theorem 6 already carries: the density bound `ν q ≤ 1/(q−1)`, the catch-#22 threshold
guard at each sifting prime (`3 ≤ q`, `19/log q + 4/(q−1) ≤ log(1+ε)`), and the operating window
`1 ≤ σ z D' ≤ n+3`.  With the explicit `c_f = cf_const n ε`,

  `Σ_{p ∈ window} ν(p)·V(p)·fₙ(σ_p) ≤ W·(fₙ₊₁(σ_z) + c_f·h(σ_z))`,   `σ = logRatio`.

Route: `Vbelow_le_ratio` factors `W` out (hyp (4)); the `fₙ`-support restricts the sum to the
window `D'^{1/(n+3)} < p < D'` (`support_prime_bounds`); `prime_support_mass_le` bounds that
window's loglog mass; and `inv_S_le` supplies the `s`-uniform `1/S` slack. -/
theorem hf_of_window (s' : BoundingSieve) (ε : ℝ) (z side' D' n : ℕ)
    (hε : 0 ≤ ε) (hn : 1 ≤ n) (hD : 1 ≤ D')
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hSn : logRatio z D' ≤ (n : ℝ) + 3) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
      ≤ Salt.BrunLower.W s' *
          (fseq (n + 1) (logRatio z D') + cf_const n ε * hBJS (logRatio z D')) := by
  classical
  have hW := Salt.BrunLower.W_pos s'
  set S := logRatio z D' with hSdef
  set win := s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D') with hwin
  -- positivity of log z, log D', S from the operating window
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [hSdef, logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [hSdef, logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  have hS0 : 0 < S := by linarith [hS1]
  have hzS : Real.log z * S = Real.log D' := by
    rw [hSdef, logRatio, mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hlogz)
  have hzR : ∀ q ∈ s'.prodPrimes.primeFactors, (q : ℝ) < (z : ℝ) :=
    fun q hq => by exact_mod_cast hz q hq
  have hlogn3 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 3) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- restrict the window sum to the fseq-support T
  set T := win.filter (fun p => fseq n (logRatio p (cdiv D' p)) ≠ 0) with hTdef
  have hTsub : T ⊆ win := Finset.filter_subset _ _
  have hsum_restrict :
      ∑ p ∈ win, s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p))
        = ∑ p ∈ T, s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)) := by
    refine (Finset.sum_subset hTsub ?_).symm
    intro p hpw hpnT
    have h0 : fseq n (logRatio p (cdiv D' p)) = 0 := by
      by_contra h; exact hpnT (Finset.mem_filter.mpr ⟨hpw, h⟩)
    rw [h0, mul_zero]
  set K0 := 2 * (1 + ε) * (((n : ℝ) + 3) / S) * Salt.BrunLower.W s' with hK0
  -- per-term bound on the support
  have hterm : ∀ p ∈ T, s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p))
      ≤ K0 * (1 / ((p : ℝ) - 1)) := by
    intro p hp
    rw [hTdef, Finset.mem_filter] at hp
    obtain ⟨hpwin, hpne⟩ := hp
    have hp_pf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hpwin).1
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
    have hp_dvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hp_pf
    have hnu0 : 0 ≤ s'.nu p := (s'.nu_pos_of_prime p hp_prime hp_dvd).le
    have hnu_le : s'.nu p ≤ 1 / ((p : ℝ) - 1) := hnu p hp_pf
    obtain ⟨hp3, hpthr⟩ := hguard p hp_pf
    have hpz : (p : ℝ) ≤ (z : ℝ) := le_of_lt (by exact_mod_cast hz p hp_pf)
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hP1 : Vbelow s' p ≤ (1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s' :=
      Vbelow_le_ratio s' hε hp3 hpz hpthr hzR hnu
    obtain ⟨_, hlogDlt⟩ := support_prime_bounds hn hD hp_prime hpne
    have hLzp : Real.log z / Real.log p ≤ ((n : ℝ) + 3) / S := by
      rw [div_le_div_iff₀ hlogp hS0, hzS]; exact hlogDlt.le
    have hLzp0 : (0 : ℝ) ≤ Real.log z / Real.log p := le_of_lt (div_pos hlogz hlogp)
    have hf0 : (0 : ℝ) ≤ fseq n (logRatio p (cdiv D' p)) := fseq_nonneg n _
    have hf2 : fseq n (logRatio p (cdiv D' p)) ≤ 2 := fseq_le_two hn _
    have hns0 : (0 : ℝ) ≤ ((n : ℝ) + 3) / S := div_nonneg (by positivity) hS0.le
    have hM : Real.log z / Real.log p * fseq n (logRatio p (cdiv D' p)) ≤ ((n : ℝ) + 3) / S * 2 :=
      mul_le_mul hLzp hf2 hf0 hns0
    have hconst0 : (0 : ℝ) ≤ (1 + ε) * Salt.BrunLower.W s' := mul_nonneg (by linarith) hW.le
    calc s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p))
        ≤ s'.nu p * ((1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s')
            * fseq n (logRatio p (cdiv D' p)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP1 hnu0) hf0
      _ = (1 + ε) * Salt.BrunLower.W s'
            * (s'.nu p * (Real.log z / Real.log p * fseq n (logRatio p (cdiv D' p)))) := by ring
      _ ≤ (1 + ε) * Salt.BrunLower.W s' * ((1 / ((p : ℝ) - 1)) * (((n : ℝ) + 3) / S * 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hnu_le hM (mul_nonneg hLzp0 hf0)
              (le_of_lt (one_div_pos.mpr (by linarith : (0 : ℝ) < (p : ℝ) - 1)))) hconst0
      _ = K0 * (1 / ((p : ℝ) - 1)) := by rw [hK0]; ring
  -- collect the mass and close against the operating-window slack
  have hTcond : ∀ p ∈ T, p.Prime ∧ (p : ℝ) < D' ∧ Real.log D' < ((n : ℝ) + 3) * Real.log p := by
    intro p hp
    rw [hTdef, Finset.mem_filter] at hp
    obtain ⟨hpwin, hpne⟩ := hp
    have hp_pf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hpwin).1
    exact ⟨Nat.prime_of_mem_primeFactors hp_pf,
      support_prime_bounds hn hD (Nat.prime_of_mem_primeFactors hp_pf) hpne⟩
  have hK0nn : (0 : ℝ) ≤ K0 := by
    rw [hK0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (div_nonneg (by positivity) hS0.le)) hW.le
  have hCbound_nn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2 := by
    have : (0 : ℝ) < 19 / Real.log 2 := by positivity
    linarith [hlogn3, this]
  have hkey : 1 / S ≤ ((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S := inv_S_le hn hS1 hSn
  have hAnn : (0 : ℝ) ≤ 2 * (1 + ε) * ((n : ℝ) + 3)
      * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)) hCbound_nn
  have hcore : 2 * (1 + ε) * (((n : ℝ) + 3) / S) * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2)
      ≤ cf_const n ε * hBJS S := by
    have hmul := mul_le_mul_of_nonneg_left hkey hAnn
    rw [cf_const]
    calc 2 * (1 + ε) * (((n : ℝ) + 3) / S) * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2)
        = 2 * (1 + ε) * ((n : ℝ) + 3) * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2)
            * (1 / S) := by ring
      _ ≤ 2 * (1 + ε) * ((n : ℝ) + 3) * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2)
            * (((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3) * hBJS S) := hmul
      _ = 2 * (1 + ε) * ((n : ℝ) + 3) * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2)
            * (((n : ℝ) + 3) * Real.exp ((n : ℝ) + 3)) * hBJS S := by ring
  have hfseq_nn : (0 : ℝ) ≤ fseq (n + 1) S := fseq_nonneg (n + 1) S
  rw [hsum_restrict]
  calc ∑ p ∈ T, s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p))
      ≤ ∑ p ∈ T, K0 * (1 / ((p : ℝ) - 1)) := Finset.sum_le_sum hterm
    _ = K0 * ∑ p ∈ T, 1 / ((p : ℝ) - 1) := by rw [Finset.mul_sum]
    _ ≤ K0 * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2) :=
        mul_le_mul_of_nonneg_left (prime_support_mass_le D' n T hTcond) hK0nn
    _ = Salt.BrunLower.W s'
          * (2 * (1 + ε) * (((n : ℝ) + 3) / S)
              * (Real.log ((n : ℝ) + 3) + 19 / Real.log 2 + 2)) := by rw [hK0]; ring
    _ ≤ Salt.BrunLower.W s' * (cf_const n ε * hBJS S) :=
        mul_le_mul_of_nonneg_left hcore hW.le
    _ ≤ Salt.BrunLower.W s' * (fseq (n + 1) S + cf_const n ε * hBJS S) := by
        apply mul_le_mul_of_nonneg_left _ hW.le; linarith [hfseq_nn]

/-! ## Part G — the `h`-part pushforward reduction `hh_reduced` (the isolated remainder)

The `h`-part `hh` runs on the *same* mandatory pushforward `Vbelow_le_ratio`, factoring `W`
out.  What it does **not** share with `hf` is the closing: `h > 0` has no compact support, so
the remaining prime sum `Σ (1/(p−1))·(log z/log p)·h(σ_p)` is not a finite loglog window — it is
a *decaying* mass that converges only through `h`'s exponential tail (`h(σ_p) ≤ e·e^{−u_p}`,
`u_p = log D'/log p`).  Bounding it needs the antitone dyadic-piece comparison against the
integral `∫ h(u−1) du/u` (the loglog change of variables piece-by-piece, `h(σ_p) ≤ h(⌊u_p⌋)`
on each `u`-unit `p ∈ (D'^{1/(k+1)}, D'^{1/k}]`, PM1 per piece, then the geometric sum
`Σ_k k·e^{−k}`), closing against `hBJS_funcbound` (`∫_{S−1} h ≤ S·h(S)`, `κ₃ = 1`).  That is a
substantial separate development; `hh_reduced` lands the shared pushforward and states exactly
the decay-mass sum that remains.  See the flag in `docs/blueprints/flags.md`. -/

/-- **The `h`-part pushforward reduction.**  Hypothesis (4) (`Vbelow_le_ratio`) factors `W` out
of the `h`-part Stieltjes sum, reducing `hh` to the pure *decay-mass* prime sum
`Σ_p (1/(p−1))·(log z/log p)·h(σ_p)`.  This is the exact isolated remainder of `hh` (the
antitone dyadic-integral comparison of that sum to `hBJS_funcbound`'s `S·h(S)` is the deferred
piece). -/
theorem hh_reduced (s' : BoundingSieve) (ε : ℝ) (z side' D' : ℕ)
    (hε : 0 ≤ ε)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)))
      ≤ (1 + ε) * Salt.BrunLower.W s'
          * ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
              1 / ((p : ℝ) - 1) * (Real.log z / Real.log p)
                * hBJS (logRatio p (cdiv D' p)) := by
  have hW := Salt.BrunLower.W_pos s'
  have hzR : ∀ q ∈ s'.prodPrimes.primeFactors, (q : ℝ) < (z : ℝ) :=
    fun q hq => by exact_mod_cast hz q hq
  have hterm : ∀ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
      s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
        ≤ (1 + ε) * Salt.BrunLower.W s'
            * (1 / ((p : ℝ) - 1) * (Real.log z / Real.log p)
                * hBJS (logRatio p (cdiv D' p))) := by
    intro p hp
    have hp_pf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
    have hp_dvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hp_pf
    have hnu0 : 0 ≤ s'.nu p := (s'.nu_pos_of_prime p hp_prime hp_dvd).le
    have hnu_le : s'.nu p ≤ 1 / ((p : ℝ) - 1) := hnu p hp_pf
    obtain ⟨hp3, hpthr⟩ := hguard p hp_pf
    have hpz : (p : ℝ) ≤ (z : ℝ) := le_of_lt (by exact_mod_cast hz p hp_pf)
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    have hP1 : Vbelow s' p ≤ (1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s' :=
      Vbelow_le_ratio s' hε hp3 hpz hpthr hzR hnu
    have hh0 : 0 ≤ hBJS (logRatio p (cdiv D' p)) := (hBJS_pos _).le
    have hRne : (0 : ℝ) ≤ (1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s' :=
      mul_nonneg (div_nonneg (mul_nonneg (by linarith) hlogz.le) hlogp.le) hW.le
    calc s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
        = s'.nu p * hBJS (logRatio p (cdiv D' p)) * Vbelow s' p := by ring
      _ ≤ s'.nu p * hBJS (logRatio p (cdiv D' p))
            * ((1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s') :=
          mul_le_mul_of_nonneg_left hP1 (mul_nonneg hnu0 hh0)
      _ ≤ 1 / ((p : ℝ) - 1) * hBJS (logRatio p (cdiv D' p))
            * ((1 + ε) * Real.log z / Real.log p * Salt.BrunLower.W s') :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnu_le hh0) hRne
      _ = (1 + ε) * Salt.BrunLower.W s'
            * (1 / ((p : ℝ) - 1) * (Real.log z / Real.log p)
                * hBJS (logRatio p (cdiv D' p))) := by ring
  calc (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p)))
      ≤ ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
          (1 + ε) * Salt.BrunLower.W s'
            * (1 / ((p : ℝ) - 1) * (Real.log z / Real.log p)
                * hBJS (logRatio p (cdiv D' p))) := Finset.sum_le_sum hterm
    _ = (1 + ε) * Salt.BrunLower.W s'
          * ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
              1 / ((p : ℝ) - 1) * (Real.log z / Real.log p)
                * hBJS (logRatio p (cdiv D' p)) := by rw [Finset.mul_sum]

end Salt.Chen
