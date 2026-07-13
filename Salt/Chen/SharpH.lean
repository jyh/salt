/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WindowedStepC
import Salt.Chen.TauSharp
import Salt.Chen.FlatFuncbound
import Salt.Chen.AbelStep
import Salt.Chen.SharpStep
import Salt.Chen.DecayMass
import Salt.Chen.Hyp4

/-!
# E₁c-hh — the sharp `h`-side windowed comparison + the discrete pushforward engine

This file lands the sharp `h`-part comparison `hh_sharp_of_window` — the conditioned per-step
`h`-slot of `WindowedStepC.StepHypWPC` at the boundary-padded multiplier `chSharpB ε`.  Where the
crude ancestor `DecayMass.hh_of_window` bounds the decay-mass sum by an absolute constant `Cabs`
(throwing away all `s`-dependence, so the RHS balloons to `ch_const ≈ (n+3)e^{n+3}Cabs`), the
sharp route keeps the `(1/S)∫_{S−1}h` structure and closes it against E₁a
(`TauSharp.sharp_h_contract`: `(1/S)∫_{S−1}^c h ≤ (49/50)h(S)`, `S ≥ 2`) / E₁a-flat
(`FlatFuncbound.flat_h_contract`: `(1/S)∫_2^c h ≤ (97/100)h(S)`, `1 ≤ S ≤ 3`).

## The mathematics (the honest discrete → integral pushforward)

Write `m_p := ν(p)·Vbelow(p)` for the descending-`V` Stieltjes increments, `u_p := logRatio p D' =
log D'/log p`, `S := logRatio z D' = log D'/log z`.  Two structural facts:

* **antitone majorant** — `hBJS(σ_p) ≤ hBJS(u_p − 1)` (`hBJS_antitone`, `σ_p ≥ u_p − 1` from
  `⌈D'/p⌉ ≥ D'/p`);
* **the sharp up-set mass control** (`upset_mass_le`, this file) — for any real `t ≥ S`,
  `Σ_{p : u_p ≤ t} m_p ≤ ((1+ε)·t/S − 1)·W`, a *single* `(1+ε)`-error over the whole range (BJS's
  hypothesis (4) `Hyp4.vratio_prod_le`, NOT a per-dyadic-piece PM1 error — that is what makes the
  sharp constant reachable).

The Fubini/FTC/IBP engine (`hh_sharp_engine`) then reconstructs
`Σ_p m_p·hBJS(u_p−1) ≤ (1+ε)(W/S)·∫_{S−1}^{U₀} h + ε·W·hBJS(S−1)` — the ideal pushforward plus the
`z`-edge boundary defect — and `chSharpB ε = (1+ε)(49/50) + 4ε` absorbs the defect via
`hBJS_shift_le` (`γ₃ʰ = sup hBJS(S−1)/hBJS(S) = (4/3)e ≤ 4`).

## Cells (all sharing the one engine)

* **side' = 2** (⇒ `S ≥ 2` via `hlo`/`loBnd_two`) and **side' = 1, S ≥ 3**: the moving lower
  limit `S − 1 ≥ 1`; E₁a `chSharp_h_contract` closes at `49/50`.
* **side' = 1, S ∈ [1,3)**: the `p³ < D'` filter forces `σ_p ≥ 2` (`logRatio_child_lower`), so the
  integral has the FIXED lower limit `2`; E₁a-flat `flat_h_contract` closes at `97/100 < 49/50`.

## FLOOR STATUS (2026-07-13, Opus — honest partial; precise flag in `docs/blueprints/flags.md`)

**Landed FULL (sorry-free, axiom-clean):**
* `hBJS_shift_le` — the boundary helper `γ₃ʰ ≤ 4` (Part A);
* `upset_mass_le` — the **sharp discrete mass control** (Part B): the single-`(1+ε)`-error up-set
  mass bound, the measure heart of the pushforward, via `telescope_ge` + `vratio_prod_le` anchored
  at the minimal prime of the up-set;
* `hh_antitone_majorize` — the ceiling-rounding removal `hBJS(σ_p) ≤ hBJS(u_p−1)` (Part C);
* `hh_sharp_ge2_of_pushforward` — the **`S ≥ 2` cell closure MODULO the pushforward** (Part D):
  antitone + E₁a (`chSharp_h_contract`) + `hBJS_shift_le` compose the pushforward output into
  `chSharpB`, exactly as side' = 2 / side' = 1 (`S ≥ 3`) need.

**NOT landed (the remaining analytic content, flagged):** the FTC/Fubini/IBP *assembly* that turns
`upset_mass_le` into the `hpush` integral bound of Part D — the honest discrete → integral
pushforward `Σ_p m_p·hBJS(u_p−1) = ∫_{S−1}^{U₀} U(v)·(−hBJS'(v)) dv + hBJS(U₀)·M_tot`, then
`U(v) ≤ ((1+ε)(v+1)/S−1)W` (Part B), then integration-by-parts against `−hBJS'` (kink-split at
`2, 3`).  This is genuine multi-hundred-line measure theory (improper-limit / IBP against `dhBJS`),
sized "its own session" by prior executors; the `chSharpB` numerics and the whole architecture are
verified end-to-end modulo it.  The **flat cell** (side' = 1, `S ∈ [1,3)`) additionally needs the
*window-relative* mass bound `V(t) − Vlow ≤ ((1+ε)(v+1)/3 − 1)·Vlow` (the `upset_mass_le` proof with
`vratio_prod_le` at `"z" := D'^{1/3}`) — the full-`pf` bound is loose at the `v = 2` boundary — then
`flat_h_contract` + `h4` (`Vlow ≤ (3(1+ε)/S)W`) close it.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the boundary helper `hBJS_shift_le` (`γ₃ʰ ≤ 4`) -/

/-- **The `h`-boundary shift bound** `hBJS(S−1) ≤ 4·hBJS S` for `S ≥ 1`.  The defect coefficient
`γ₃ʰ = sup_S hBJS(S−1)/hBJS(S) = (4/3)e ≈ 3.6244` (attained at `S = 4`), so `4` is a safe rational
envelope — exactly the `4ε` pad of `chSharpB`.  Branch arithmetic on `hBJS`'s three pieces. -/
theorem hBJS_shift_le {S : ℝ} (hS : 1 ≤ S) : hBJS (S - 1) ≤ 4 * hBJS S := by
  have hexp2 : (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rcases le_total S 2 with h2 | h2
  · -- S ≤ 2: both `e⁻²`
    rw [hBJS_le2 (by linarith), hBJS_le2 h2]; linarith [hexp2]
  · rcases le_total S 3 with h3 | h3
    · -- 2 ≤ S ≤ 3: `hBJS S = e⁻ˢ`, `hBJS (S−1) = e⁻²`; need `e^{S−2} ≤ 4`
      rw [hBJS_le2 (by linarith), hBJS_mid h2 h3]
      have hid : Real.exp (-2) = Real.exp (S - 2) * Real.exp (-S) := by
        rw [← Real.exp_add, show (S - 2) + -S = (-2 : ℝ) by ring]
      rw [hid]
      have hexpS : (0 : ℝ) < Real.exp (-S) := Real.exp_pos _
      have hle : Real.exp (S - 2) ≤ 4 := by
        calc Real.exp (S - 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
          _ ≤ 4 := by linarith
      nlinarith [hle, hexpS]
    · rcases le_total S 4 with h4 | h4
      · -- 3 ≤ S ≤ 4: `hBJS S = 3S⁻¹e⁻ˢ`, `hBJS (S−1) = e^{−(S−1)}`; need `e·S ≤ 12`
        rw [hBJS_mid (by linarith) (by linarith), hBJS_ge3 h3]
        have hSpos : (0 : ℝ) < S := by linarith
        have hid : Real.exp (-(S - 1)) = Real.exp 1 * Real.exp (-S) := by
          rw [← Real.exp_add, show (1 : ℝ) + -S = -(S - 1) by ring]
        rw [hid, show (4 : ℝ) * (3 * S⁻¹ * Real.exp (-S)) = (12 * S⁻¹) * Real.exp (-S) by ring]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos (-S)).le
        rw [show (12 : ℝ) * S⁻¹ = 12 / S by rw [div_eq_mul_inv], le_div_iff₀ hSpos]
        nlinarith [he, h4, hSpos]
      · -- S ≥ 4: `hBJS S = 3S⁻¹e⁻ˢ`, `hBJS (S−1) = 3(S−1)⁻¹e^{−(S−1)}`; need `e·S ≤ 4(S−1)`
        rw [hBJS_ge3 (by linarith), hBJS_ge3 h3]
        have hSpos : (0 : ℝ) < S := by linarith
        have hS1pos : (0 : ℝ) < S - 1 := by linarith
        have hid : Real.exp (-(S - 1)) = Real.exp 1 * Real.exp (-S) := by
          rw [← Real.exp_add, show (1 : ℝ) + -S = -(S - 1) by ring]
        rw [hid,
          show (3 : ℝ) * (S - 1)⁻¹ * (Real.exp 1 * Real.exp (-S))
              = (3 * Real.exp 1 * (S - 1)⁻¹) * Real.exp (-S) by ring,
          show (4 : ℝ) * (3 * S⁻¹ * Real.exp (-S)) = (12 * S⁻¹) * Real.exp (-S) by ring]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos (-S)).le
        rw [show (3 : ℝ) * Real.exp 1 * (S - 1)⁻¹ = (3 * Real.exp 1) / (S - 1) by ring,
          show (12 : ℝ) * S⁻¹ = 12 / S by ring,
          div_le_div_iff₀ hS1pos hSpos]
        nlinarith [he, h4, hSpos]

/-! ## Part B — the sharp up-set mass control `upset_mass_le` (BJS hypothesis (4)) -/

/-- **The sharp up-set mass bound.**  For any real threshold `t ≥ S := logRatio z D'`, the
descending-`V` Stieltjes mass of the primes with `u_p := logRatio p D' ≤ t` (i.e. `p ≥ D'^{1/t}`)
obeys

  `Σ_{p ∈ pf, u_p ≤ t} ν(p)·Vbelow(p) ≤ ((1+ε)·t/S − 1)·W`.

This is the measure control the sharp pushforward runs on: a SINGLE `(1+ε)` multiplicative error
over the whole `[D'^{1/t}, z)` window (hypothesis (4), `Hyp4.vratio_prod_le`), not a per-piece
additive PM1 error.  Route: `AbelStep.telescope_ge` turns the mass into `Vbelow(⌈D'^{1/t}⌉) − W`,
then `vratio_prod_le` (anchored at the minimal prime of the up-set, where the per-prime guard
`hguard` supplies its `hthresh`) bounds `Vbelow(⌈D'^{1/t}⌉)/W ≤ (1+ε)·log z/log p₀ ≤ (1+ε)·t/S`. -/
theorem upset_mass_le (s' : BoundingSieve) (ε : ℝ) (z D' : ℕ) (t : ℝ)
    (hε : 0 ≤ ε)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hSt : logRatio z D' ≤ t) :
    ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => (logRatio p D' : ℝ) ≤ t),
        s'.nu p * Vbelow s' p
      ≤ ((1 + ε) * t / logRatio z D' - 1) * Salt.BrunLower.W s' := by
  classical
  have hW := Salt.BrunLower.W_pos s'
  set S := logRatio z D' with hSdef
  -- log positivity from the operating window `1 ≤ S`
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
  have htpos : 0 < t := by linarith [hS1, hSt]
  -- the change-of-variables threshold `wexp = D'^{1/t}`, `tN = ⌈wexp⌉`
  set wexp := Real.exp (Real.log D' / t) with hwexp
  have hwexp_pos : 0 < wexp := Real.exp_pos _
  set tN := ⌈wexp⌉₊ with htN
  set F := s'.prodPrimes.primeFactors.filter (fun p => tN ≤ p) with hFdef
  -- the two filters coincide on the prime factors
  have hfilter : s'.prodPrimes.primeFactors.filter (fun p => (logRatio p D' : ℝ) ≤ t) = F := by
    rw [hFdef]
    apply Finset.filter_congr
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    constructor
    · intro hle
      -- logRatio p D' ≤ t  →  wexp ≤ p  →  tN ≤ p
      rw [logRatio, div_le_iff₀ hlogp] at hle
      have hdle : Real.log D' / t ≤ Real.log p := by rw [div_le_iff₀ htpos]; linarith [hle]
      have hwle : wexp ≤ (p : ℝ) := by
        rw [hwexp]; exact (Real.le_log_iff_exp_le hp0).mp hdle
      exact Nat.ceil_le.mpr hwle
    · intro hle
      -- tN ≤ p  →  wexp ≤ p  →  logRatio p D' ≤ t
      have hwle : wexp ≤ (p : ℝ) := le_trans (Nat.le_ceil wexp) (by exact_mod_cast hle)
      have hdle : Real.log D' / t ≤ Real.log p := by
        rw [hwexp] at hwle; exact (Real.le_log_iff_exp_le hp0).mpr hwle
      rw [logRatio, div_le_iff₀ hlogp]
      rw [div_le_iff₀ htpos] at hdle; linarith [hdle]
  rw [hfilter]
  -- telescope: the mass is `Vbelow(tN) − W`
  have hmass_eq : ∑ p ∈ F, s'.nu p * Vbelow s' p = Vbelow s' tN - Salt.BrunLower.W s' := by
    rw [hFdef]
    simp only [Vbelow, belowPrimes, Salt.BrunLower.W]
    exact telescope_ge s'.prodPrimes.primeFactors s'.nu tN
  rw [hmass_eq]
  -- the V-ratio bound `Vbelow(tN) ≤ (1+ε)·t/S·W`
  have hFprod_pos : 0 < ∏ p ∈ F, (1 - s'.nu p) := by
    apply Finset.prod_pos
    intro p hp
    rw [hFdef, Finset.mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have hdvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hp.1
    have := s'.nu_lt_one_of_prime p hpp hdvd; linarith
  -- `W = Vbelow(tN) · ∏_F`
  have hnot : s'.prodPrimes.primeFactors.filter (fun p => ¬ p < tN)
      = s'.prodPrimes.primeFactors.filter (fun p => tN ≤ p) := by
    apply Finset.filter_congr; intro p _; simp only [not_lt]
  have hWsplit : Salt.BrunLower.W s' = Vbelow s' tN * ∏ p ∈ F, (1 - s'.nu p) := by
    rw [hFdef]
    simp only [Vbelow, belowPrimes, Salt.BrunLower.W]
    rw [← hnot, Finset.prod_filter_mul_prod_filter_not s'.prodPrimes.primeFactors (· < tN)]
  have hVratio : (∏ p ∈ F, (1 - s'.nu p))⁻¹ ≤ (1 + ε) * t / S := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · rw [hFe, Finset.prod_empty, inv_one]
      rw [le_div_iff₀ hS0]
      nlinarith [hSt, hε, hS0]
    · set p₀ := F.min' hFne with hp₀
      have hp₀F : p₀ ∈ F := F.min'_mem hFne
      have hp₀pf : p₀ ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp₀F).1
      obtain ⟨hp₀3, hp₀thr⟩ := hguard p₀ hp₀pf
      have hp₀pp : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀pf
      have hp₀2 : (2 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀pp.two_le
      have hlogp₀ : 0 < Real.log p₀ := Real.log_pos (by linarith)
      have hp₀z : (p₀ : ℝ) ≤ (z : ℝ) := le_of_lt (by exact_mod_cast hz p₀ hp₀pf)
      have hmain := vratio_prod_le s' F hε hp₀3 hp₀z hp₀thr (fun p hp => by
        have hppf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
        refine ⟨Nat.prime_of_mem_primeFactors hppf, ?_, by exact_mod_cast hz p hppf, hnu p hppf⟩
        exact_mod_cast F.min'_le p hp)
      -- `(1+ε)log z/log p₀ ≤ (1+ε)t/S`, from `logRatio p₀ D' ≤ t`
      have hp₀t : (logRatio p₀ D' : ℝ) ≤ t := by
        have hmem : p₀ ∈ s'.prodPrimes.primeFactors.filter (fun p => (logRatio p D' : ℝ) ≤ t) := by
          rw [hfilter]; exact hp₀F
        exact (Finset.mem_filter.mp hmem).2
      have hp₀t' : Real.log D' ≤ t * Real.log p₀ := by
        rw [logRatio, div_le_iff₀ hlogp₀] at hp₀t; exact hp₀t
      have hlogzp : Real.log z / Real.log p₀ ≤ t / S := by
        rw [div_le_div_iff₀ hlogp₀ hS0]
        have hSval : Real.log z * S = Real.log D' := by
          rw [hSdef, logRatio, mul_comm, div_mul_cancel₀ _ (ne_of_gt hlogz)]
        linarith [hp₀t', hSval]
      calc (∏ p ∈ F, (1 - s'.nu p))⁻¹ ≤ (1 + ε) * Real.log z / Real.log p₀ := hmain
        _ = (1 + ε) * (Real.log z / Real.log p₀) := by ring
        _ ≤ (1 + ε) * (t / S) := mul_le_mul_of_nonneg_left hlogzp (by linarith)
        _ = (1 + ε) * t / S := by ring
  -- `Vbelow(tN) = W · (∏_F)⁻¹`, so the V-ratio bound lifts to the mass bound
  have hVeq : Vbelow s' tN = Salt.BrunLower.W s' * (∏ p ∈ F, (1 - s'.nu p))⁻¹ := by
    rw [hWsplit, mul_assoc, mul_inv_cancel₀ (ne_of_gt hFprod_pos), mul_one]
  have hVbtN : Vbelow s' tN ≤ (1 + ε) * t / S * Salt.BrunLower.W s' := by
    rw [hVeq]
    calc Salt.BrunLower.W s' * (∏ p ∈ F, (1 - s'.nu p))⁻¹
        ≤ Salt.BrunLower.W s' * ((1 + ε) * t / S) := mul_le_mul_of_nonneg_left hVratio hW.le
      _ = (1 + ε) * t / S * Salt.BrunLower.W s' := by ring
  -- conclude the mass bound
  calc Vbelow s' tN - Salt.BrunLower.W s'
      ≤ (1 + ε) * t / S * Salt.BrunLower.W s' - Salt.BrunLower.W s' := by linarith [hVbtN]
    _ = ((1 + ε) * t / S - 1) * Salt.BrunLower.W s' := by ring

/-! ## Part C — the antitone majorization `hBJS(σ_p) ≤ hBJS(u_p − 1)` -/

/-- **The antitone majorization.**  Replacing each child point `σ_p = logRatio p ⌈D'/p⌉` by the
cleaner monotone-in-`p` argument `u_p − 1 = logRatio p D' − 1` is an over-estimate: `σ_p ≥ u_p − 1`
(`logRatio_child_ge`, from `⌈D'/p⌉ ≥ D'/p`) and `hBJS` is antitone (`hBJS_antitone`).  This is the
first step of the pushforward — it removes the ceiling-rounding so the layer-cake / mass argument
runs against the strictly monotone `u_p`. -/
theorem hh_antitone_majorize (s' : BoundingSieve) (D' : ℕ) (hD : 1 ≤ D') (F : Finset ℕ)
    (hFprime : ∀ p ∈ F, p.Prime) (hnn : ∀ p ∈ F, 0 ≤ s'.nu p * Vbelow s' p) :
    ∑ p ∈ F, s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
      ≤ ∑ p ∈ F, s'.nu p * Vbelow s' p * hBJS (logRatio p D' - 1) := by
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (hnn p hp)
  apply hBJS_antitone
  have h := logRatio_child_ge hD (hFprime p hp)
  rwa [show logRatio p D' = Real.log D' / Real.log p from rfl]

/-! ## Part D — the `S ≥ 2` cell closure (side' = 2 and side' = 1, S ≥ 3), modulo the pushforward

The two cells whose operating point has `S ≥ 2` — side' = 2 (`⇒ S ≥ 2` via `hlo`/`loBnd_two`) and
side' = 1 with `S ≥ 3` — share the moving lower limit `S − 1 ≥ 1` and consume E₁a
(`chSharp_h_contract`, `κ₃ = 49/50`).  Given the honest pushforward output `hpush` — the discrete →
integral reconstruction `Σ_p m_p·hBJS(u_p−1) ≤ ε·W·hBJS(S−1) + (1+ε)·(1/S)·∫_{S−1}^U h·W`, whose
measure control is `upset_mass_le` — this closes the cell at `chSharpB ε = chSharp ε + 4ε`. -/

/-- **The `S ≥ 2` cell closure, modulo the pushforward.**  Given the pushforward reconstruction
`hpush` (the FTC/Fubini/IBP output built on `upset_mass_le`), the antitone majorization + E₁a
(`chSharp_h_contract`) + the boundary shift (`hBJS_shift_le`) close the sharp `h`-comparison at
`chSharpB`.  This is the exact composition the two `S ≥ 2` cells of `hh_sharp_of_window` use. -/
theorem hh_sharp_ge2_of_pushforward (s' : BoundingSieve) (ε : ℝ) (z D' : ℕ)
    (hε : 0 ≤ ε) (hD : 1 ≤ D') (hS2 : 2 ≤ logRatio z D')
    (win : Finset ℕ) (hwin_prime : ∀ p ∈ win, p.Prime)
    (hnn : ∀ p ∈ win, 0 ≤ s'.nu p * Vbelow s' p) (U : ℝ)
    (hpush : ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p D' - 1)
        ≤ ε * Salt.BrunLower.W s' * hBJS (logRatio z D' - 1)
          + (1 + ε) * ((1 / logRatio z D') * (∫ u in (logRatio z D' - 1)..U, hBJS u))
              * Salt.BrunLower.W s') :
    ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
      ≤ Salt.BrunLower.W s' * (chSharpB ε * hBJS (logRatio z D')) := by
  set S := logRatio z D' with hSdef
  have hS1 : (1 : ℝ) ≤ S := by linarith
  have hW := Salt.BrunLower.W_pos s'
  have hanti := hh_antitone_majorize s' D' hD win hwin_prime hnn
  have hE1a := chSharp_h_contract S U ε hS2 hε
  have hshift := hBJS_shift_le hS1
  have e1 : (1 + ε) * ((1 / S) * (∫ u in (S - 1)..U, hBJS u)) * Salt.BrunLower.W s'
      ≤ chSharp ε * hBJS S * Salt.BrunLower.W s' := mul_le_mul_of_nonneg_right hE1a hW.le
  have e2 : ε * Salt.BrunLower.W s' * hBJS (S - 1)
      ≤ ε * Salt.BrunLower.W s' * (4 * hBJS S) :=
    mul_le_mul_of_nonneg_left hshift (by positivity)
  have hchsb : chSharpB ε = chSharp ε + 4 * ε := by unfold chSharpB chSharp; ring
  calc ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p (cdiv D' p))
      ≤ ∑ p ∈ win, s'.nu p * Vbelow s' p * hBJS (logRatio p D' - 1) := hanti
    _ ≤ ε * Salt.BrunLower.W s' * hBJS (S - 1)
          + (1 + ε) * ((1 / S) * (∫ u in (S - 1)..U, hBJS u)) * Salt.BrunLower.W s' := hpush
    _ ≤ ε * Salt.BrunLower.W s' * (4 * hBJS S) + chSharp ε * hBJS S * Salt.BrunLower.W s' :=
        add_le_add e2 e1
    _ = Salt.BrunLower.W s' * (chSharpB ε * hBJS S) := by rw [hchsb]; ring

end Salt.Chen
