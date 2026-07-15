/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.FinLed2
import Salt.Chen.StepBound
import Salt.Chen.WindowedStepC
import Salt.BrunLower.MertensWindow
import Salt.BrunLower.MertensDischarge

/-!
# FIN-LED-3 — the `hEbundle ≤ 1/200` numeric assembly → `hL_bundle`

Design: `docs/blueprints/flags.md`, the `2026-07-15 FIN-LED-2 … DEFERRED (= FIN-LED-3)` entry
(the four ingredients + the share table: `e1 ≈ 0.00027`, `e2/2 ≈ 0.002–0.003`, `e3` small,
`e4` tiny; total `≈ 0.0033 < 0.005 = 1/200`).  This module discharges the `hEbundle` threshold
`GlueNormalized.normalized_package` consumes, then supplies the F2 ledger hypothesis `hL` of
`Headline4.chen_headline_of_A3_ledger` at the concrete carriers `M1`/`M2`/`M3`.

The four error shares (`GlueNormalized.lean` pins their forms):

* **e1** `= slack1 + R1/X_W` — the A₁ per-point slack (`opEps·CsharpB·e²·hBJS(s₁)`, `s₁ ≥ 3.9992`,
  so `hBJS(s₁) ≤ e^{−s₁}` — the SHARP `DecayMass` route; the crude `e^{−2}` does NOT close) plus
  the BV strip crumb.  `≈ 0.00027`.
* **e2** `= (3+43/75)·wtail + aggSlack + R2/X_W` — the A₂ tail (`razor_topwindow_cost`, ≈ 0.00215
  halved) + the Mertens `Σ 1/(p−1)` agg-slack (`sum_inv_le_of_prime_window` on `[opZ, opY]`, the
  ratio `log opY/log opZ ≈ 8/3` so the sum `≤ log(8/3)+o(1) ≤ 1`) + the BV crumb.
* **e3** `= (cbar+ecount)·rho·(243/100+slack3) − cbar·(3/8)·(243/100) + log x·R3/X_W` — the
  catch-#49 collapse: `rho → 3/8` (`hWy_at_op`), `ecount → 0` (`hcount_seam`), `slack3` fixed
  small.  `≈ 0.00027`.
* **e4** `= (log x·x/(z−1))/X_W` — the prime-power strip; `x^{−1/8}·polylog`, tiny.

The tower crumbs `Rᵢ/X_W`, `e4` vanish via `XW_lower_at_op` (`X_W ≥ e^{−35}x/(4φ(opQ)log opZ)`)
against the poly-beats-log helpers (`a12_logpow_le_rpow`).

No `sorry`, no `native_decide`, no new axioms.  Lean notes (FinLed): `maxRecDepth 8000`,
`linarith` over `nlinarith` in the heavy op context, explicit-`≠0` `field_simp`.
-/

namespace Salt.Chen

open Real

/-! ## Part A — the frozen slack constants (`opEps·CsharpB`) -/

/-- `0 < CsharpB opEps` — the achieved B-constant is positive (`chSharpB opEps < 1`). -/
theorem opf_CsharpB_pos : 0 < CsharpB opEps := by
  rw [CsharpB]
  apply div_pos (by norm_num)
  have h1 : chSharpB opEps < 1 := chSharpB_lt_one opf_eps49
  linarith

/-- `opEps · CsharpB opEps ≤ 200002/10⁸` — the frozen slack scale (`opEps = 2·10⁻⁸`,
`CsharpB opEps ≤ 100001`, `CsharpB_frozen`). -/
theorem opf_epsC_le : opEps * CsharpB opEps ≤ 200002 / 10 ^ 8 := by
  have hC : CsharpB opEps ≤ 100001 := by
    have h := CsharpB_frozen
    rwa [show (2 : ℝ) / 100000000 = opEps by norm_num [opEps]] at h
  have hεnn : (0 : ℝ) ≤ opEps := opf_eps_pos.le
  calc opEps * CsharpB opEps ≤ opEps * 100001 :=
        mul_le_mul_of_nonneg_left hC hεnn
    _ = 200002 / 10 ^ 8 := by norm_num [opEps]

/-- `0 ≤ opEps · CsharpB opEps` (nonneg of the slack scale). -/
theorem opf_epsC_nn : 0 ≤ opEps * CsharpB opEps :=
  mul_nonneg opf_eps_pos.le opf_CsharpB_pos.le

/-- `0 ≤ opEps·CsharpB opEps·e²·hBJS s` — the per-point slack is nonneg for any argument. -/
theorem slack_nn (s : ℝ) : 0 ≤ opEps * CsharpB opEps * Real.exp 2 * hBJS s :=
  mul_nonneg (mul_nonneg opf_epsC_nn (Real.exp_pos 2).le) (hBJS_pos s).le

/-- `opEps·CsharpB opEps·e²·hBJS s ≤ opEps·CsharpB opEps` — the crude `e²·hBJS ≤ 1` bound
(`hBJS_le_exp2 : hBJS s ≤ e^{−2}`), used for `slack3` and the aggregate `A₂` slack. -/
theorem slack_le_epsC (s : ℝ) :
    opEps * CsharpB opEps * Real.exp 2 * hBJS s ≤ opEps * CsharpB opEps := by
  have hcrude : Real.exp 2 * hBJS s ≤ 1 := by
    have h1 : hBJS s ≤ Real.exp (-2) := hBJS_le_exp2 s
    calc Real.exp 2 * hBJS s ≤ Real.exp 2 * Real.exp (-2) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos 2).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  calc opEps * CsharpB opEps * Real.exp 2 * hBJS s
      = (opEps * CsharpB opEps) * (Real.exp 2 * hBJS s) := by ring
    _ ≤ (opEps * CsharpB opEps) * 1 :=
        mul_le_mul_of_nonneg_left hcrude opf_epsC_nn
    _ = opEps * CsharpB opEps := by ring

/-! ## Part B — the SHARP A₁ slack (`e^{−s₁}` via `DecayMass`)

`slack1 = opEps·CsharpB·e²·hBJS(s₁)` with `s₁ = logRatio (opZ x)(opD x) ≥ 3.9992`
(`logRatio_A1_mem`).  The sharp `hBJS(s₁) ≤ e^{−s₁} ≤ e^{−3.9992}` (`hBJS_le_exp_of_ge`) gives
`e²·hBJS(s₁) ≤ e^{2−3.9992} = e^{−1.9992} ≤ 271/2000`, so `slack1 ≤ (200002/10⁸)·(271/2000) ≤
28/100000` — a tenth of the crude `e^{−2}` value, which is what closes the bundle. -/

/-- `e^{−1.9992} ≤ 271/2000` (the sharp `e²·hBJS(s₁)` scale). -/
theorem exp_neg_19992_le : Real.exp (-(19992 / 10000)) ≤ 271 / 2000 := by
  have hexp2 : (7389 : ℝ) / 1000 < Real.exp 2 := by
    have h9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [h9, Real.exp_pos 1]
  -- exp(19992/10000) = exp 2 · exp(-(8/10000)) ≥ 7.389 · 0.9992 ≥ 2000/271
  have hexp_a : (2000 : ℝ) / 271 ≤ Real.exp (19992 / 10000) := by
    have h1 : Real.exp (19992 / 10000 : ℝ) = Real.exp 2 * Real.exp (-(8 / 10000)) := by
      rw [← Real.exp_add]; norm_num
    have h2 : (9992 : ℝ) / 10000 ≤ Real.exp (-(8 / 10000)) := by
      have := Real.add_one_le_exp (-(8 / 10000) : ℝ); linarith
    rw [h1]
    nlinarith [hexp2, h2, Real.exp_pos 2, Real.exp_pos (-(8 / 10000 : ℝ))]
  have hpos := Real.exp_pos (19992 / 10000 : ℝ)
  rw [show -(19992 / 10000 : ℝ) = -(19992 / 10000) by ring, Real.exp_neg]
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith [hexp_a]

/-- **`slack1_le` — the sharp A₁ slack row.**  Past `logRatio_A1_mem`'s threshold,
`opEps·CsharpB·e²·hBJS(logRatio (opZ x)(opD x)) ≤ 28/100000`. -/
theorem slack1_le : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opZ x) (opD x)) ≤ 28 / 100000 := by
  obtain ⟨xm, hmem⟩ := logRatio_A1_mem
  refine ⟨xm, fun x hx => ?_⟩
  have hmemx : logRatio (opZ x) (opD x) ∈ Set.Icc (39992 / 10000 : ℝ) 4 := by
    rw [opZ, opD]; exact hmem x hx
  set s := logRatio (opZ x) (opD x) with hs
  have hs_ge : (39992 : ℝ) / 10000 ≤ s := hmemx.1
  have hs2 : (2 : ℝ) ≤ s := by linarith [hs_ge]
  -- e²·hBJS s ≤ e²·e^{−s} = e^{2−s} ≤ e^{−1.9992} ≤ 271/2000
  have hbjs : hBJS s ≤ Real.exp (-s) := hBJS_le_exp_of_ge hs2
  have hstep : Real.exp 2 * hBJS s ≤ 271 / 2000 := by
    have h1 : Real.exp 2 * hBJS s ≤ Real.exp 2 * Real.exp (-s) :=
      mul_le_mul_of_nonneg_left hbjs (Real.exp_pos 2).le
    have h2 : Real.exp 2 * Real.exp (-s) = Real.exp (2 - s) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (2 - s) ≤ Real.exp (-(19992 / 10000)) :=
      Real.exp_le_exp.mpr (by linarith [hs_ge])
    calc Real.exp 2 * hBJS s ≤ Real.exp 2 * Real.exp (-s) := h1
      _ = Real.exp (2 - s) := h2
      _ ≤ Real.exp (-(19992 / 10000)) := h3
      _ ≤ 271 / 2000 := exp_neg_19992_le
  have hstep_nn : 0 ≤ Real.exp 2 * hBJS s := mul_nonneg (Real.exp_pos 2).le (hBJS_pos s).le
  calc opEps * CsharpB opEps * Real.exp 2 * hBJS s
      = (opEps * CsharpB opEps) * (Real.exp 2 * hBJS s) := by ring
    _ ≤ (200002 / 10 ^ 8) * (271 / 2000) :=
        mul_le_mul opf_epsC_le hstep hstep_nn (by norm_num)
    _ ≤ 28 / 100000 := by norm_num

/-! ## Part C — the A₂ aggregate slack (`Σ 1/(p−1)` windowed Mertens)

`aggSlack = Σ_{p∈[opZ,opY]} (1/(p−1))·(opEps·CsharpB·e²·hBJS(s_p))`.  Each per-point factor is
`≤ opEps·CsharpB` (crude `e²·hBJS ≤ 1`), so `aggSlack ≤ opEps·CsharpB·Σ 1/(p−1)`.  The windowed
Mertens bound `Σ 1/p ≤ log(log(opY+1)/log opZ) + 19/log opZ` (`sum_inv_le_of_prime_window`) with the
tail `Σ (1/(p−1) − 1/p) ≤ 2·Σ 1/p² ≤ 2/(opZ−1)` (`sum_one_div_sq_le`) and the ratio bound
`log(opY+1)/log opZ ≤ 8/3 + 1/1000 < e` (`logRatio_A2_topwindow_mem`, so `log(·) ≤ 1`) give
`Σ 1/(p−1) ≤ 11/10` past a threshold. -/

/-- **`aggSlack_le`** — the A₂ aggregate slack is `≤ opEps·CsharpB·(11/10)`. -/
theorem aggSlack_le : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
        (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
            * hBJS (logRatio (opZ x) (cdiv (opD x) p)))
      ≤ opEps * CsharpB opEps * (11 / 10) := by
  obtain ⟨xT, hT⟩ := logRatio_A2_topwindow_mem
  obtain ⟨xL, hLg⟩ := a12_log_ge 3050
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max xT xL) (max xt (10 ^ 48)), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxT, hxL⟩, hxt, hx48⟩ := hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  set S := (Finset.Icc (opZ x) (opY x)).filter Nat.Prime with hSdef
  -- floor / window facts
  obtain ⟨-, hz6, hzlog_le, hzlog_ge⟩ :=
    opf_window_floor_bounds x hx48R (γ := (1 : ℝ) / 8) (by norm_num)
  have hzy : opZ x ≤ opY x := (htower x hxt).2.2.2.2.2.2.1
  have hlogx : (3050 : ℝ) ≤ Real.log x := (hLg x hxL).2
  -- opZ ≥ 10^6, opZ ≥ 2
  have hz6' : (10 : ℝ) ^ 6 ≤ (opZ x : ℝ) := by rw [opZ]; exact hz6
  have hzR2 : (2 : ℝ) ≤ (opZ x : ℝ) := le_trans (by norm_num) hz6'
  have hzR1 : (1 : ℝ) < (opZ x : ℝ) := by linarith
  have hlogzpos : 0 < Real.log (opZ x : ℝ) := Real.log_pos hzR1
  have hlogz_ge : (380 : ℝ) ≤ Real.log (opZ x : ℝ) := by
    rw [opZ]; linarith [hzlog_ge, hlogx]
  -- per-term crude bound → factor out opEps·CsharpB
  have hterm : ∀ p ∈ S, (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
        * hBJS (logRatio (opZ x) (cdiv (opD x) p)))
      ≤ (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps) := by
    intro p hp
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hp
    have hp0 : (2 : ℝ) ≤ (p : ℝ) := le_trans hzR2 (by exact_mod_cast hp.1.1)
    have hp1nn : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
      apply div_nonneg (by norm_num); linarith
    exact mul_le_mul_of_nonneg_left (slack_le_epsC _) hp1nn
  have hfactor : ∑ p ∈ S, (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
        * hBJS (logRatio (opZ x) (cdiv (opD x) p)))
      ≤ (opEps * CsharpB opEps) * ∑ p ∈ S, (1 / ((p : ℝ) - 1)) := by
    calc ∑ p ∈ S, (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
            * hBJS (logRatio (opZ x) (cdiv (opD x) p)))
        ≤ ∑ p ∈ S, (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps) := Finset.sum_le_sum hterm
      _ = (opEps * CsharpB opEps) * ∑ p ∈ S, (1 / ((p : ℝ) - 1)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  -- the windowed Mertens sum: Σ 1/(p−1) ≤ Σ 1/p + 2·Σ 1/p²
  have hsplit : ∑ p ∈ S, (1 / ((p : ℝ) - 1))
      ≤ (∑ p ∈ S, (1 : ℝ) / p) + 2 * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 := by
    have hpt : ∀ p ∈ S, 1 / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) + 2 * (1 / (p : ℝ) ^ 2) := by
      intro p hp
      rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := le_trans hzR2 (by exact_mod_cast hp.1.1)
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
      have hp1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1
      have hid : 1 / (p : ℝ) + 2 * (1 / (p : ℝ) ^ 2) - 1 / ((p : ℝ) - 1)
          = ((p : ℝ) - 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by field_simp; ring
      have hnn : 0 ≤ ((p : ℝ) - 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) :=
        div_nonneg (by linarith) (by positivity)
      linarith [hid, hnn]
    calc ∑ p ∈ S, (1 / ((p : ℝ) - 1))
        ≤ ∑ p ∈ S, (1 / (p : ℝ) + 2 * (1 / (p : ℝ) ^ 2)) := Finset.sum_le_sum hpt
      _ = (∑ p ∈ S, (1 : ℝ) / p) + 2 * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Σ 1/p ≤ log(log(opY+1)/log opZ) + 19/log opZ
  have hzyR : (opZ x : ℝ) ≤ (opY x : ℝ) + 1 := by
    have : (opZ x : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hzy
    linarith
  have hmert : ∑ p ∈ S, (1 : ℝ) / p
      ≤ Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ))
        + 19 / Real.log (opZ x : ℝ) := by
    apply Salt.BrunLower.sum_inv_le_of_prime_window hzR2 hzyR
    intro p hp
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hp
    refine ⟨hp.2, by exact_mod_cast hp.1.1, ?_⟩
    have : (p : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hp.1.2
    linarith
  -- Σ 1/p² ≤ 1/(opZ−1)
  have hsq : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / ((opZ x : ℝ) - 1) := by
    have hsub : S ⊆ Finset.Icc (opZ x) (opY x) := Finset.filter_subset _ _
    calc ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑ p ∈ Finset.Icc (opZ x) (opY x), (1 : ℝ) / (p : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
      _ ≤ 1 / ((opZ x : ℝ) - 1) := Salt.BrunLower.sum_one_div_sq_le (by exact_mod_cast hzR2)
  -- log(log(opY+1)/log opZ) ≤ 1
  have hratio_le : Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ) ≤ 8 / 3 + 1 / 1000 := by
    rw [div_le_iff₀ hlogzpos]
    exact (hT x hxT).2
  have hratio_pos : 0 < Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ) := by
    apply div_pos _ hlogzpos
    apply Real.log_pos
    have : (opZ x : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hzy
    linarith
  have hlogratio_le1 : Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ)) ≤ 1 := by
    calc Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ))
        ≤ Real.log (8 / 3 + 1 / 1000) := Real.log_le_log hratio_pos hratio_le
      _ ≤ Real.log (Real.exp 1) := by
          apply Real.log_le_log (by norm_num)
          have := Real.exp_one_gt_d9; linarith
      _ = 1 := Real.log_exp 1
  -- assemble the Σ 1/(p−1) bound
  have hz1 : (2 : ℝ) / ((opZ x : ℝ) - 1) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith [hz6']
  have h19 : (19 : ℝ) / Real.log (opZ x : ℝ) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ hlogzpos (by norm_num)]; linarith [hlogz_ge]
  have hsum_le : ∑ p ∈ S, (1 / ((p : ℝ) - 1)) ≤ 11 / 10 := by
    have h2sq : 2 * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 / ((opZ x : ℝ) - 1) := by
      rw [show (2 : ℝ) / ((opZ x : ℝ) - 1) = 2 * (1 / ((opZ x : ℝ) - 1)) by ring]
      linarith [hsq]
    linarith [hsplit, hmert, hlogratio_le1, h2sq, hz1, h19]
  -- final
  calc ∑ p ∈ S, (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
          * hBJS (logRatio (opZ x) (cdiv (opD x) p)))
      ≤ (opEps * CsharpB opEps) * ∑ p ∈ S, (1 / ((p : ℝ) - 1)) := hfactor
    _ ≤ (opEps * CsharpB opEps) * (11 / 10) :=
        mul_le_mul_of_nonneg_left hsum_le opf_epsC_nn

/-! ## Part D — the ledger crumbs (`Rᵢ/X_W`, `e4`): `X_W`-normalisation reduction

`XW_lower_at_op` gives `X_W ≥ e^{−35}·x/(4φ(opQ)·log opZ)`; over `φ(opQ) ≤ opQ ≤ log x`
(`opf_tower`) and `log opZ ≤ (1/8)log x` (`opf_window_floor_bounds`), `φ·log opZ ≤ (log x)²`, so
`1/X_W ≤ K := 4·e^{35}·(log x)²/x`.  Every crumb `N/X_W ≤ N·K` then vanishes against the concrete
`N` (`x/(log x)^{10}`, `√x·log₂x·log x`, `log x·x/(z−1)`) by poly-beats-power. -/

/-- **`crumb_reduce`** — the `X_W`-normalisation reduction.  Past a threshold, `X_W > 0` and every
nonneg numerator `N` obeys `N/X_W ≤ N·(4·e^{35}·(log x)²/x)`. -/
theorem crumb_reduce : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    0 < (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
          * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x))
      ∧ ∀ N : ℝ, 0 ≤ N →
        N / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
              * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
          ≤ N * (4 * Real.exp 35 * (Real.log x) ^ 2 / (x : ℝ)) := by
  obtain ⟨xlo, hlo⟩ := XW_lower_at_op
  obtain ⟨xpos, hpos⟩ := XW_pos_at_op
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max xlo xpos) (max xt (10 ^ 48)), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxlo, hxpos⟩, hxt, hx48⟩ := hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxR : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx48R
  set XW := (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
      * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)) with hXWdef
  have hXWpos : 0 < XW := hpos x hxpos (opf_P_sq x) (opf_Podd x)
  -- the crude lower bound
  set XWlo := Real.exp (-35) * (x : ℝ) / (4 * (opQ.totient : ℝ) * Real.log (opZ x)) with hXWlodef
  have hXWlo_le : XWlo ≤ XW := hlo x hxlo
  -- positivity of the pieces
  have hφpos : (0 : ℝ) < (opQ.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  have hz3 : 3 ≤ opZ x := (htower x hxt).2.2.2.1
  have hzR1 : (1 : ℝ) < (opZ x : ℝ) := by exact_mod_cast (by omega : 1 < opZ x)
  have hlogzpos : 0 < Real.log (opZ x : ℝ) := Real.log_pos hzR1
  have hlogxpos : 0 < Real.log (x : ℝ) := Real.log_pos (lt_of_lt_of_le (by norm_num) hx48R)
  have hexp35 : (0 : ℝ) < Real.exp 35 := Real.exp_pos 35
  have hXWlopos : 0 < XWlo := by
    rw [hXWlodef]; positivity
  -- φ·logopZ ≤ (logx)²
  have hφlogx : (opQ.totient : ℝ) ≤ Real.log x := by
    have h1 : (opQ.totient : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast Nat.totient_le opQ
    have h2 : (opQ : ℝ) ≤ Real.log x := (htower x hxt).1
    linarith
  have hlogzlogx : Real.log (opZ x : ℝ) ≤ Real.log x := by
    obtain ⟨-, -, hzlog_le, -⟩ := opf_window_floor_bounds x hx48R (γ := (1 : ℝ) / 8) (by norm_num)
    rw [opZ]; linarith [hzlog_le]
  have hφlogz : (opQ.totient : ℝ) * Real.log (opZ x) ≤ (Real.log x) ^ 2 := by
    have := mul_le_mul hφlogx hlogzlogx hlogzpos.le hlogxpos.le
    nlinarith [this]
  set K := 4 * Real.exp 35 * (Real.log x) ^ 2 / (x : ℝ) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  -- 1 ≤ K·XWlo
  have hee : Real.exp 35 * Real.exp (-35) = 1 := by rw [← Real.exp_add]; norm_num
  have hKXWlo_eq : K * XWlo
      = (Real.exp 35 * Real.exp (-35))
          * ((Real.log x) ^ 2 / ((opQ.totient : ℝ) * Real.log (opZ x))) := by
    rw [hKdef, hXWlodef]; field_simp
  rw [hee, one_mul] at hKXWlo_eq
  have hKXWlo_ge : 1 ≤ K * XWlo := by
    rw [hKXWlo_eq, le_div_iff₀ (by positivity)]
    linarith [hφlogz]
  refine ⟨hXWpos, fun N hN => ?_⟩
  have h1XW : (1 : ℝ) / XW ≤ K := by
    rw [div_le_iff₀ hXWpos]
    calc (1 : ℝ) ≤ K * XWlo := hKXWlo_ge
      _ ≤ K * XW := mul_le_mul_of_nonneg_left hXWlo_le hKpos.le
  calc N / XW = N * (1 / XW) := by rw [mul_one_div]
    _ ≤ N * K := mul_le_mul_of_nonneg_left h1XW hN

/-- **`master_le`** — the master crumb bound.  Past a threshold, `1 ≤ log x` and
`8·e^{35}/(log x)^7 ≤ 1/100000`; since `(log x)^k ≥ (log x)^7` for `k ≥ 7`, this dominates
every reduced crumb. -/
theorem master_le : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    2 ≤ Real.log x ∧ 8 * Real.exp 35 / (Real.log x) ^ 7 ≤ 1 / 100000 := by
  obtain ⟨xL, hL⟩ := a12_log_ge (8 * Real.exp 35 * 10 ^ 5)
  refine ⟨xL, fun x hx => ?_⟩
  have hlogx : 8 * Real.exp 35 * 10 ^ 5 ≤ Real.log x := (hL x hx).2
  have hexp35 : (1 : ℝ) ≤ Real.exp 35 := Real.one_le_exp (by norm_num)
  have hlogx2 : 2 ≤ Real.log x := by nlinarith [hlogx, hexp35]
  refine ⟨hlogx2, ?_⟩
  have hpow : Real.log x ≤ (Real.log x) ^ 7 := le_self_pow₀ (by linarith) (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hpow, hlogx, hexp35]

/-- **`logpow_reduction`** — the power-vs-log reductions.  Past a threshold,
`(log x)^{11} ≤ √x` and `(log x)^{11} ≤ x^{1/8}` (both via `a12_logpow_le_rpow`); these convert
the `√x` / `opZ` crumbs into `(log x)^{−k}` crumbs. -/
theorem logpow_reduction : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (Real.log x) ^ (11 : ℕ) ≤ Real.sqrt x
    ∧ (Real.log x) ^ (11 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
  obtain ⟨xa, ha⟩ := a12_logpow_le_rpow 11 (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨xb, hb⟩ := a12_logpow_le_rpow 11 (1 / 8) (by norm_num) (by norm_num)
  refine ⟨max xa xb, fun x hx => ?_⟩
  have hxa : xa ≤ x := le_trans (le_max_left _ _) hx
  have hxb : xb ≤ x := le_trans (le_max_right _ _) hx
  have hcast : ((11 : ℝ)) = ((11 : ℕ) : ℝ) := by norm_num
  constructor
  · have h := ha x hxa
    rw [hcast, Real.rpow_natCast] at h
    rwa [Real.sqrt_eq_rpow]
  · have h := hb x hxb
    rwa [hcast, Real.rpow_natCast] at h

/-- **`crumbs_le`** — the four ledger crumbs at op.  Past a threshold, `X_W > 0` and each of
`R1/X_W`, `R2/X_W`, `log x·R3/X_W`, `e4` is below its (tiny) share. -/
theorem crumbs_le : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    0 < (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
          * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x))
    ∧ ((x : ℝ) / (Real.log x) ^ 10 + Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x)
          / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
            * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
        ≤ 2 / 100000
    ∧ (x : ℝ) / (Real.log x) ^ 10
          / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
            * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
        ≤ 1 / 100000
    ∧ Real.log x * ((x : ℝ) / (Real.log x) ^ 10)
          / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
            * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
        ≤ 1 / 100000
    ∧ Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1)
          / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
            * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
        ≤ 1 / 100000 := by
  obtain ⟨xr, hr⟩ := crumb_reduce
  obtain ⟨xm, hm⟩ := master_le
  obtain ⟨xp, hp⟩ := logpow_reduction
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max xr xm) (max xp (max xt (10 ^ 48))), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxr, hxm⟩, hxp, hxt, hx48⟩ := hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx48R
  obtain ⟨hXWpos, hK⟩ := hr x hxr
  obtain ⟨hlogx2, hmaster⟩ := hm x hxm
  obtain ⟨hsqrt, hx18⟩ := hp x hxp
  have hlogxpos : 0 < Real.log x := by linarith
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hxpos
  have hlogxne : Real.log x ≠ 0 := ne_of_gt hlogxpos
  have hexp35 : (0 : ℝ) < Real.exp 35 := Real.exp_pos 35
  -- Nat.log 2 x ≤ 2·log x
  have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ), hsq]
  have hlog2x : (Nat.log 2 x : ℝ) ≤ 2 * Real.log x := by
    have hpow : (2 : ℕ) ^ (Nat.log 2 x) ≤ x := Nat.pow_log_le_self 2 (by omega : x ≠ 0)
    have hlogpow : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
      have hle : ((2 : ℕ) ^ (Nat.log 2 x) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hpow
      have := Real.log_le_log (by positivity) hle
      rwa [show ((2 : ℕ) ^ (Nat.log 2 x) : ℝ) = (2 : ℝ) ^ (Nat.log 2 x) by push_cast; ring,
        Real.log_pow] at this
    nlinarith [hlogpow, hlog2half, (show (0 : ℝ) ≤ (Nat.log 2 x : ℝ) by positivity)]
  -- opZ − 1 ≥ (log x)^10
  have hopZlo : (x : ℝ) ^ ((1 : ℝ) / 8) - 1 ≤ (opZ x : ℝ) := by
    rw [opZ]; linarith [Nat.lt_floor_add_one ((x : ℝ) ^ ((1 : ℝ) / 8))]
  have hopZm1 : (Real.log x) ^ 10 ≤ (opZ x : ℝ) - 1 := by
    have hchain : (Real.log x) ^ 11 - 1 ≤ (opZ x : ℝ) := by linarith [hx18, hopZlo]
    have h1110 : (Real.log x) ^ 11 = (Real.log x) ^ 10 * Real.log x := by ring
    have hp10 : (2 : ℝ) ≤ (Real.log x) ^ 10 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hlogx2 10)
    have hprod : (2 : ℝ) * 1 ≤ (Real.log x) ^ 10 * (Real.log x - 1) :=
      mul_le_mul hp10 (by linarith) (by norm_num) (by positivity)
    nlinarith [hchain, h1110, hprod]
  set K := 4 * Real.exp 35 * (Real.log x) ^ 2 / (x : ℝ) with hKdef
  have hpow87 : (Real.log x) ^ 8 = (Real.log x) ^ 7 * Real.log x := by ring
  have hp7pos : (0 : ℝ) < (Real.log x) ^ 7 := by positivity
  -- the master bound `4exp35/(logx)^8 ≤ 8exp35/(logx)^7` and its `logx··/(logx)^7` sibling
  have hle86 : 4 * Real.exp 35 / (Real.log x) ^ 8 ≤ 8 * Real.exp 35 / (Real.log x) ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) hp7pos]
    nlinarith [hpow87, hlogx2, hexp35, hp7pos,
      mul_nonneg (mul_nonneg hexp35.le hp7pos.le) (show (0 : ℝ) ≤ 2 * Real.log x - 1 by linarith)]
  have hle77 : 4 * Real.exp 35 / (Real.log x) ^ 7 ≤ 8 * Real.exp 35 / (Real.log x) ^ 7 := by
    rw [div_le_div_iff₀ hp7pos hp7pos]; nlinarith [hexp35, hp7pos]
  -- crumb R2
  have hc_R2 : (x : ℝ) / (Real.log x) ^ 10
        / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
          * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
      ≤ 1 / 100000 := by
    have hNK : ((x : ℝ) / (Real.log x) ^ 10) * K = 4 * Real.exp 35 / (Real.log x) ^ 8 := by
      rw [hKdef]; field_simp
    refine le_trans (hK _ (by positivity)) ?_
    rw [hNK]; exact le_trans hle86 hmaster
  -- crumb log x·R3
  have hc_R3 : Real.log x * ((x : ℝ) / (Real.log x) ^ 10)
        / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
          * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
      ≤ 1 / 100000 := by
    have hNK : (Real.log x * ((x : ℝ) / (Real.log x) ^ 10)) * K
        = 4 * Real.exp 35 / (Real.log x) ^ 7 := by
      rw [hKdef]; field_simp
    refine le_trans (hK _ (by positivity)) ?_
    rw [hNK]; exact le_trans hle77 hmaster
  -- crumb e4
  have hc_e4 : Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1)
        / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
          * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
      ≤ 1 / 100000 := by
    have hopZ1pos : (0 : ℝ) < (opZ x : ℝ) - 1 := by
      have := pow_pos hlogxpos 10; linarith [hopZm1]
    have hN_nn : 0 ≤ Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1) := by positivity
    have hopZ1ne : (opZ x : ℝ) - 1 ≠ 0 := ne_of_gt hopZ1pos
    have hNK : (Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1)) * K
        = 4 * Real.exp 35 * (Real.log x) ^ 3 / ((opZ x : ℝ) - 1) := by
      rw [hKdef]; field_simp
    refine le_trans (hK _ hN_nn) ?_
    rw [hNK]
    calc 4 * Real.exp 35 * (Real.log x) ^ 3 / ((opZ x : ℝ) - 1)
        ≤ 4 * Real.exp 35 * (Real.log x) ^ 3 / (Real.log x) ^ 10 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hopZm1
      _ = 4 * Real.exp 35 / (Real.log x) ^ 7 := by
          rw [div_eq_div_iff (by positivity) (by positivity)]; ring
      _ ≤ 8 * Real.exp 35 / (Real.log x) ^ 7 := hle77
      _ ≤ 1 / 100000 := hmaster
  -- crumb √x·log₂x·log x
  have hc_sqrt : Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x
        / ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
          * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
      ≤ 1 / 100000 := by
    have hsqrtpos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hN_nn : 0 ≤ Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x := by positivity
    refine le_trans (hK _ hN_nn) ?_
    -- N·K = 4exp35·log₂x·(logx)³/√x  ≤ 8exp35·(logx)^4/√x ≤ 8exp35/(logx)^7
    have hNK : (Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x) * K
        = 4 * Real.exp 35 * (Nat.log 2 x : ℝ) * (Real.log x) ^ 3 * (Real.sqrt x / (x : ℝ)) := by
      rw [hKdef]; ring
    rw [hNK]
    have hsx : Real.sqrt x / (x : ℝ) = 1 / Real.sqrt x := by
      rw [div_eq_div_iff (ne_of_gt hxpos) (ne_of_gt hsqrtpos), Real.mul_self_sqrt hxpos.le, one_mul]
    rw [hsx]
    -- ≤ 8exp35·(logx)^4/√x
    have hstep1 : 4 * Real.exp 35 * (Nat.log 2 x : ℝ) * (Real.log x) ^ 3 * (1 / Real.sqrt x)
        ≤ 8 * Real.exp 35 * (Real.log x) ^ 4 * (1 / Real.sqrt x) := by
      have hL2 : 4 * Real.exp 35 * (Nat.log 2 x : ℝ) * (Real.log x) ^ 3
          ≤ 8 * Real.exp 35 * (Real.log x) ^ 4 := by
        have hpow34 : (Real.log x) ^ 4 = (Real.log x) ^ 3 * Real.log x := by ring
        have hkey := mul_le_mul_of_nonneg_left hlog2x
          (show (0 : ℝ) ≤ 4 * Real.exp 35 * (Real.log x) ^ 3 by positivity)
        nlinarith [hkey, hpow34, hexp35, pow_pos hlogxpos 3]
      apply mul_le_mul_of_nonneg_right hL2 (by positivity)
    -- 8exp35(logx)^4/√x ≤ 8exp35(logx)^4/(logx)^11 = 8exp35/(logx)^7
    have hstep2 : 8 * Real.exp 35 * (Real.log x) ^ 4 * (1 / Real.sqrt x)
        ≤ 8 * Real.exp 35 / (Real.log x) ^ 7 := by
      have hp11pos : (0 : ℝ) < (Real.log x) ^ 11 := by positivity
      have hrecip : (1 : ℝ) / Real.sqrt x ≤ 1 / (Real.log x) ^ 11 :=
        one_div_le_one_div_of_le hp11pos hsqrt
      calc 8 * Real.exp 35 * (Real.log x) ^ 4 * (1 / Real.sqrt x)
          ≤ 8 * Real.exp 35 * (Real.log x) ^ 4 * (1 / (Real.log x) ^ 11) :=
            mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ = 8 * Real.exp 35 / (Real.log x) ^ 7 := by
            rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]; ring
    exact le_trans (le_trans hstep1 hstep2) hmaster
  -- assemble
  refine ⟨hXWpos, ?_, hc_R2, hc_R3, hc_e4⟩
  rw [add_div]
  linarith [hc_R2, hc_sqrt]

/-! ## Part E — the A₂ tail weight bound (`e2`'s vanishing `wtail` factor) -/

/-- **`A2weight_le`** — `A2weight(opZ, opZ⁴, opY+1) ≤ 3000/3997`.  The denominator `4·log opZ −
log(opY+1) ≥ (3997/3000)·log opZ` via `logRatio_A2_topwindow_mem`. -/
theorem A2weight_le : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    0 ≤ A2weight (opZ x) ((opZ x) ^ 4) ((opY x : ℝ) + 1)
    ∧ A2weight (opZ x) ((opZ x) ^ 4) ((opY x : ℝ) + 1) ≤ 3000 / 3997 := by
  obtain ⟨xT, hT⟩ := logRatio_A2_topwindow_mem
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max xT xt) (10 ^ 48), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxT, hxt⟩, -⟩ := hx
  have hz3 : 3 ≤ opZ x := (htower x hxt).2.2.2.1
  have hzR1 : (1 : ℝ) < (opZ x : ℝ) := by exact_mod_cast (by omega : 1 < opZ x)
  have hlogzpos : 0 < Real.log (opZ x : ℝ) := Real.log_pos hzR1
  have hlogz4 : Real.log (((opZ x) ^ 4 : ℕ) : ℝ) = 4 * Real.log (opZ x) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  obtain ⟨-, hLy_hi⟩ := hT x hxT
  have hden : (3997 / 3000) * Real.log (opZ x)
      ≤ 4 * Real.log (opZ x) - Real.log ((opY x : ℝ) + 1) := by
    linarith [hLy_hi]
  have hdenpos : 0 < 4 * Real.log (opZ x) - Real.log ((opY x : ℝ) + 1) := by
    have : 0 < (3997 / 3000 : ℝ) * Real.log (opZ x) := by positivity
    linarith [hden]
  refine ⟨?_, ?_⟩
  · unfold A2weight; rw [hlogz4]; exact div_nonneg hlogzpos.le hdenpos.le
  · unfold A2weight; rw [hlogz4, div_le_iff₀ hdenpos]; nlinarith [hden, hlogzpos]

/-! ## Part F — the `W`-ratio collapse (`rho = (log opZ + 38)/log opY ≤ 3/8 + 1/100000`) -/

/-- **`rho_le`** — the operating `W`-ratio `(log opZ/log opY)·(1 + 38/log opZ) = (log opZ + 38)/
log opY` is nonneg and `≤ 3/8 + 1/100000` past a threshold (`log opZ ≤ (1/8)log x`, `log opY ≥
(1/3)log x − o(1)`, `log x ≥ 1.2·10⁷`). -/
theorem rho_le : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    0 ≤ (Real.log (opZ x) / Real.log (opY x)) * (1 + 38 / Real.log (opZ x))
    ∧ (Real.log (opZ x) / Real.log (opY x)) * (1 + 38 / Real.log (opZ x)) ≤ 3 / 8 + 1 / 100000 := by
  obtain ⟨xL, hLg⟩ := a12_log_ge 12000000
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max xL xt) (10 ^ 48), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxL, hxt⟩, hx48⟩ := hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hlogx : (12000000 : ℝ) ≤ Real.log x := (hLg x hxL).2
  have hz3 : 3 ≤ opZ x := (htower x hxt).2.2.2.1
  have hzy : opZ x ≤ opY x := (htower x hxt).2.2.2.2.2.2.1
  have hzR1 : (1 : ℝ) < (opZ x : ℝ) := by exact_mod_cast (by omega : 1 < opZ x)
  have hyR1 : (1 : ℝ) < (opY x : ℝ) := by exact_mod_cast (by omega : 1 < opY x)
  have hlogzpos : 0 < Real.log (opZ x) := Real.log_pos hzR1
  have hlogypos : 0 < Real.log (opY x) := Real.log_pos hyR1
  have hza_le : Real.log (opZ x) ≤ (1 / 8) * Real.log x := by
    obtain ⟨-, -, h, -⟩ := opf_window_floor_bounds x hx48R (γ := (1 : ℝ) / 8) (by norm_num)
    rw [opZ]; linarith [h]
  have hya_ge : (1 / 3) * Real.log x - 1 / 999999 ≤ Real.log (opY x) := by
    obtain ⟨-, -, -, h⟩ := opf_window_floor_bounds x hx48R (γ := (1 : ℝ) / 3) (by norm_num)
    rw [opY]; linarith [h]
  refine ⟨?_, ?_⟩
  · have h38 : 0 ≤ 38 / Real.log (opZ x) := div_nonneg (by norm_num) hlogzpos.le
    exact mul_nonneg (div_nonneg hlogzpos.le hlogypos.le) (by linarith)
  · have hrho_eq : (Real.log (opZ x) / Real.log (opY x)) * (1 + 38 / Real.log (opZ x))
        = (Real.log (opZ x) + 38) / Real.log (opY x) := by
      field_simp
    rw [hrho_eq, div_le_iff₀ hlogypos]
    nlinarith [hza_le, hya_ge, hlogx]

/-! ## Part G — the `e3` catch-#49 collapse (abstract arithmetic) -/

/-- **`e3_collapse`** — the A₃ multiplicative-slack collapse.  With `cbar ≤ 363084/10⁶`, the
count slack `ec`, `W`-ratio `rho ≤ 3/8 + 1/10⁵`, switch slack `s3 ≤ opEps·CsharpB`, and strip
crumb `crumb`, all small, `e3 = (cbar+ec)·rho·(243/100+s3) − cbar·(3/8)·(243/100) + crumb ≤
31/100000`.  Keeps `cbar` symbolic so the leading term cancels (catch #49). -/
theorem e3_collapse {cbar ec rho s3 crumb : ℝ}
    (hcbar_nn : 0 ≤ cbar) (hcbar_hi : cbar ≤ 363084 / 1000000)
    (hec_nn : 0 ≤ ec) (hec_hi : ec ≤ 1 / 100000)
    (hrho_hi : rho ≤ 3 / 8 + 1 / 100000)
    (hs3_nn : 0 ≤ s3) (hs3_hi : s3 ≤ 200002 / 100000000)
    (hcrumb : crumb ≤ 1 / 100000) :
    (cbar + ec) * rho * (243 / 100 + s3) - cbar * (3 / 8) * (243 / 100) + crumb
      ≤ 31 / 100000 := by
  have hA_nn : (0 : ℝ) ≤ 243 / 100 + s3 := by linarith
  have hA_hi : (243 : ℝ) / 100 + s3 ≤ 243 / 100 + 200002 / 100000000 := by linarith
  set Δhi : ℝ := (3 / 8 + 1 / 100000) * (243 / 100 + 200002 / 100000000)
      - (3 / 8) * (243 / 100) with hΔhidef
  have hΔhi_nn : 0 ≤ Δhi := by rw [hΔhidef]; norm_num
  have hrhoA_hi : rho * (243 / 100 + s3)
      ≤ (3 / 8 + 1 / 100000) * (243 / 100 + 200002 / 100000000) :=
    mul_le_mul hrho_hi hA_hi hA_nn (by norm_num)
  have hΔ : rho * (243 / 100 + s3) - (3 / 8) * (243 / 100) ≤ Δhi := by
    rw [hΔhidef]; linarith [hrhoA_hi]
  have hid : (cbar + ec) * rho * (243 / 100 + s3) - cbar * (3 / 8) * (243 / 100)
      = cbar * (rho * (243 / 100 + s3) - (3 / 8) * (243 / 100))
        + ec * (rho * (243 / 100 + s3)) := by
    ring
  have hcbarΔ : cbar * (rho * (243 / 100 + s3) - (3 / 8) * (243 / 100))
      ≤ (363084 / 1000000) * Δhi := by
    calc cbar * (rho * (243 / 100 + s3) - (3 / 8) * (243 / 100))
        ≤ cbar * Δhi := mul_le_mul_of_nonneg_left hΔ hcbar_nn
      _ ≤ (363084 / 1000000) * Δhi := mul_le_mul_of_nonneg_right hcbar_hi hΔhi_nn
  have hecrhoA : ec * (rho * (243 / 100 + s3))
      ≤ (1 / 100000) * ((3 / 8 + 1 / 100000) * (243 / 100 + 200002 / 100000000)) := by
    calc ec * (rho * (243 / 100 + s3))
        ≤ ec * ((3 / 8 + 1 / 100000) * (243 / 100 + 200002 / 100000000)) :=
          mul_le_mul_of_nonneg_left hrhoA_hi hec_nn
      _ ≤ (1 / 100000) * ((3 / 8 + 1 / 100000) * (243 / 100 + 200002 / 100000000)) :=
          mul_le_mul_of_nonneg_right hec_hi (by norm_num)
  have hsum : (363084 / 1000000) * Δhi
      + (1 / 100000) * ((3 / 8 + 1 / 100000) * (243 / 100 + 200002 / 100000000))
      + 1 / 100000 ≤ 31 / 100000 := by rw [hΔhidef]; norm_num
  rw [hid]
  linarith [hcbarΔ, hecrhoA, hcrumb, hsum]

/-! ## Part H — the `hL` ledger bundle: `normalized_package` at the op carriers -/

set_option maxHeartbeats 1000000 in -- deep op composition: normalized_package unifies 4 carriers
/-- **`hL_bundle`** — the F2 ledger hypothesis of `chen_headline_of_A3_ledger` at the concrete
carriers `M1`/`M2`/`M3`.  `normalized_package` at the frozen operating point, with the four error
shares discharged (`e1 ≈ 0.0003`, `e2/2 ≈ 0.0033`, `e3/2 ≈ 0.0016`, `e4/2 ≈ 0.000005`;
total `≈ 0.00374 < 1/200`). -/
theorem hL_bundle : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    0 < M1 x - M2 x / 2 - M3 x / 2 - Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1) / 2 := by
  obtain ⟨Ccount, xcount, hCcount_nn, hcount_s⟩ := hcount_seam
  obtain ⟨xs1, hslack1⟩ := slack1_le
  obtain ⟨xag, hag⟩ := aggSlack_le
  obtain ⟨xcr, hcr⟩ := crumbs_le
  obtain ⟨xa2, ha2⟩ := A2weight_le
  obtain ⟨xrh, hrh⟩ := rho_le
  obtain ⟨xc1, hc1⟩ := hcertA1_at_op
  obtain ⟨xc2, hc2⟩ := hcertA2_at_op
  obtain ⟨xc3, hc3⟩ := hcertA3_at_op
  obtain ⟨xwy, hwy⟩ := hWy_at_op
  obtain ⟨xlg, hlg⟩ := a12_log_ge (1600000 * Ccount + 34000000)
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨xcount + xs1 + xag + xcr + xa2 + xrh + xc1 + xc2 + xc3 + xwy + xlg + xt + 10 ^ 48 + 1,
    fun x hx => ?_⟩
  have hx48 : (10 : ℕ) ^ 48 ≤ x := by omega
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx48R
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48R
  have hlogx : (1600000 * Ccount + 34000000 : ℝ) ≤ Real.log x := (hlg x (by omega)).2
  have hlogxpos : 0 < Real.log x := lt_of_lt_of_le (by positivity) hlogx
  obtain ⟨hQlog, -, hw'z, hz3, hzD, -, hzy, -, -, -, -, -, -, -, -, -, -⟩ := htower x (by omega)
  have hzR1 : (1 : ℝ) < (opZ x : ℝ) := by exact_mod_cast (by omega : 1 < opZ x)
  have hlogzpos : 0 < Real.log (opZ x) := Real.log_pos hzR1
  have hφpos : (0 : ℝ) < (opQ.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  -- floor: log opZ ≥ (1/8)log x − 1/999999
  obtain ⟨-, -, -, hzlog_ge⟩ := opf_window_floor_bounds x hx48R (γ := (1 : ℝ) / 8) (by norm_num)
  have hlogopZ_ge18 : (1 / 8) * Real.log x - 1 / 999999 ≤ Real.log (opZ x) := by
    rw [opZ]; linarith [hzlog_ge]
  -- ══ atom values from crumbs ══
  obtain ⟨hXWpos, hR1XW, hR2XW, hR3XW, he4XW⟩ := hcr x (by omega)
  -- ══ the count slot with its crumb `e` ══
  obtain ⟨e, he_nn, he_le, hcount_bd⟩ := hcount_s x (by omega)
  -- ══ ecount ≤ 1/100000 ══
  have hlogopZ_big : (200000 : ℝ) * Ccount ≤ Real.log (opZ x) := by
    have : (1 / 8) * Real.log x - 1 / 999999 ≥ 200000 * Ccount := by nlinarith [hlogx, hCcount_nn]
    linarith [hlogopZ_ge18, this]
  have hec_ecountOp : ecountOp Ccount x ≤ 1 / 200000 := by
    rw [ecountOp, div_le_iff₀ hlogzpos]
    rcases eq_or_lt_of_le hCcount_nn with h | h
    · rw [← h]; positivity
    · nlinarith [hlogopZ_big, h]
  have he_small : e ≤ 1 / 200000 := by
    have h8 : (8 : ℝ) / Real.log x ≤ 1 / 200000 := by
      rw [div_le_div_iff₀ hlogxpos (by norm_num)]; nlinarith [hlogx, hCcount_nn]
    linarith [he_le, h8]
  have hec_le : ecountOp Ccount x + e ≤ 1 / 100000 := by linarith [hec_ecountOp, he_small]
  have hec_nn : 0 ≤ ecountOp Ccount x + e := by
    have : 0 ≤ ecountOp Ccount x := by rw [ecountOp]; positivity
    linarith [he_nn]
  -- ══ rho, slack3, cbar ══
  obtain ⟨hrho_nn, hrho_hi⟩ := hrh x (by omega)
  have hs3_nn : 0 ≤ opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY x) (opDlev x)) :=
    slack_nn _
  have hs3_hi : opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY x) (opDlev x))
      ≤ 200002 / 100000000 :=
    le_trans (slack_le_epsC _) (le_trans opf_epsC_le (by norm_num))
  -- ══ aggSlack ≤ 2200022/10⁹ ══
  have hagg_bd : (∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
        (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
          * hBJS (logRatio (opZ x) (cdiv (opD x) p))))
      ≤ 2200022 / 1000000000 := by
    refine le_trans (hag x (by omega)) ?_
    have := mul_le_mul_of_nonneg_right opf_epsC_le (by norm_num : (0 : ℝ) ≤ 11 / 10)
    linarith [this]
  -- ══ the A₂ tail: wtail and its bound ══
  set A2w := A2weight (opZ x) ((opZ x) ^ 4) ((opY x : ℝ) + 1) with hA2wdef
  obtain ⟨hA2w_nn, hA2w_hi⟩ := ha2 x (by omega)
  set WTAIL : ℝ := (1250 / 1249) * (Real.log 6 / 4 + 1125 / 3997000
      + A2w * (21 / Real.log (opZ x) + 2 / ((opZ x : ℝ) - 1))) - Real.log 6 / 4 with hWTdef
  -- the vanishing `21/log opZ + 2/(opZ−1) ≤ 1/100000`
  have hlp_nn : 0 ≤ 21 / Real.log (opZ x) + 2 / ((opZ x : ℝ) - 1) := by positivity
  have hlp_le : 21 / Real.log (opZ x) + 2 / ((opZ x : ℝ) - 1) ≤ 1 / 100000 := by
    have hz6 : (10 : ℝ) ^ 6 ≤ (opZ x : ℝ) := by
      obtain ⟨-, h, -, -⟩ := opf_window_floor_bounds x hx48R (γ := (1 : ℝ) / 8) (by norm_num)
      rw [opZ]; exact h
    have h21 : 21 / Real.log (opZ x) ≤ 1 / 200000 := by
      rw [div_le_iff₀ hlogzpos]; nlinarith [hlogopZ_ge18, hlogx, hCcount_nn]
    have h2z : 2 / ((opZ x : ℝ) - 1) ≤ 1 / 200000 := by
      rw [div_le_div_iff₀ (by linarith [hz6]) (by norm_num)]; nlinarith [hz6]
    linarith [h21, h2z]
  have hwtail_bd : (3 + 43 / 75) * WTAIL ≤ 4342 / 1000000 := by
    have hexpand : (3 + 43 / 75) * WTAIL
        = (3 + 43 / 75) * ((1 / 1249) * (Real.log 6 / 4) + (1250 / 1249) * (1125 / 3997000))
          + (3 + 43 / 75) * (1250 / 1249) * A2w
              * (21 / Real.log (opZ x) + 2 / ((opZ x : ℝ) - 1)) := by
      rw [hWTdef]; ring
    have hrazor : (3 + 43 / 75)
        * ((1 / 1249) * (Real.log 6 / 4) + (1250 / 1249) * (1125 / 3997000)) ≤ 4302 / 1000000 := by
      have := razor_topwindow_cost; linarith [this]
    have hvanish : (3 + 43 / 75) * (1250 / 1249) * A2w
        * (21 / Real.log (opZ x) + 2 / ((opZ x : ℝ) - 1)) ≤ 40 / 1000000 := by
      have hA2w1 : A2w ≤ 1 := le_trans hA2w_hi (by norm_num)
      have hprod : A2w * (21 / Real.log (opZ x) + 2 / ((opZ x : ℝ) - 1)) ≤ 1 / 100000 :=
        le_trans (mul_le_mul hA2w1 hlp_le hlp_nn (by norm_num)) (by norm_num)
      nlinarith [hprod, mul_nonneg hA2w_nn hlp_nn]
    rw [hexpand]; linarith [hrazor, hvanish]
  -- ══ the raw carrier bounds (definitional regroupings) ══
  have hrawA1 := (M1_raw_shape x).le
  have hrawA2 := (M2_raw_shape x).ge
  have hrawA3 : M3 x ≤ Real.log x * (tripleSum x (opZ x) (opY x) / (opQ.totient : ℝ)
      * Salt.BrunLower.W (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x))
      * (Fchain (maxDepth (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x)))
            (logRatio (opY x) (opDlev x))
          + opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY x) (opDlev x)))
      + (x : ℝ) / (Real.log x) ^ 10) := le_of_eq rfl
  -- ══ hcertA2 in the `(3+43/75)·(log6/4 + wtail)` shape ══
  have hcertA2 : A2grid ((Finset.Icc (opZ x) (opY x)).filter Nat.Prime) (opZ x) (opD x)
        (fun p => maxDepth (twinA2SieveW opQ opA x (opP x) p (opf_P_sq x) (opf_Podd x)))
      ≤ (3 + 43 / 75) * (Real.log 6 / 4 + WTAIL) := by
    refine le_trans (hc2 x (by omega)) (le_of_eq ?_)
    rw [hWTdef, hA2wdef]; ring
  -- ══ the W-ratio in the `Wz·rho` shape (twinA1SieveW_W_eq bridge) ══
  have hWy : Salt.BrunLower.W (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x))
      ≤ Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x))
        * ((Real.log (opZ x) / Real.log (opY x)) * (1 + 38 / Real.log (opZ x))) := by
    rw [twinA1SieveW_W_eq]; exact hwy x (by omega)
  -- ══ the count slot at totalMass = (twinA1SieveW …).totalMass ══
  have hcount : Real.log x * (tripleSum x (opZ x) (opY x) / (opQ.totient : ℝ))
      ≤ (cbar + (ecountOp Ccount x + e))
          * (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass := by
    rw [twinA1SieveW_totalMass]; exact hcount_bd
  -- ══ nonnegativity side conditions ══
  have hFslack_nn : 0 ≤ Fchain (maxDepth (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x)
        (opf_Psodd x))) (logRatio (opY x) (opDlev x))
      + opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY x) (opDlev x)) := by
    have hFv : 0 ≤ Fchain (maxDepth (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x)
        (opf_Psodd x))) (logRatio (opY x) (opDlev x)) := by
      have hsum : (0 : ℝ) ≤ ∑ n ∈ (Finset.range (maxDepth (switchSieve x (opZ x) (opY x)
          (opPs x) (opf_Ps_sq x) (opf_Psodd x)) + 1)).filter (fun n => Odd n),
          fseq n (logRatio (opY x) (opDlev x)) :=
        Finset.sum_nonneg fun n _ => fseq_nonneg n _
      unfold Fchain; linarith
    linarith [hFv, slack_nn (logRatio (opY x) (opDlev x))]
  have hWz_nn : 0 ≤ Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)) :=
    (Salt.BrunLower.W_pos _).le
  have hLTnn : 0 ≤ Real.log x * (tripleSum x (opZ x) (opY x) / (opQ.totient : ℝ)) := by
    have hTS : 0 ≤ tripleSum x (opZ x) (opY x) := by rw [tripleSum_eq_card]; positivity
    exact mul_nonneg hlogxpos.le (div_nonneg hTS hφpos.le)
  -- ══ compose normalized_package ══
  refine normalized_package (x := x) (z := opZ x)
    (totalMass := (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass)
    (Wz := Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
    hXWpos rfl hrawA1 (hc1 x (by omega)) hrawA2 hcertA2 hrawA3 (hc3 x (by omega))
    hFslack_nn hWy hrho_nn hWz_nn hLTnn hcount ?_
  -- ══ the error bundle `hEbundle ≤ 1/200` ══
  have he3 := e3_collapse (cbar_pos.le) (le_of_lt cbar_lt) hec_nn hec_le hrho_hi hs3_nn hs3_hi hR3XW
  linarith [hslack1 x (by omega), hR1XW, hwtail_bd, hagg_bd, hR2XW, he3, he4XW]

/-- **The compiled endpoint.**  Given the F1 A₃ bundle `hA3` (`triplePrimeSumW ≤ M3`, supplied by
`FinA3c`'s `hBVblocksW_discharge'` composition), the F2 ledger `hL_bundle` closes the entire Chen
headline: infinitely many primes `p` with `p + 2` a P₂.  This is the exact `hL` slot of
`Headline4.chen_headline_of_A3_ledger`; only `hA3` remains. -/
example (hA3 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    triplePrimeSumW opQ opA x (opP x) (opY x) ≤ M3 x) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite :=
  chen_headline_of_A3_ledger hA3 hL_bundle

end Salt.Chen
