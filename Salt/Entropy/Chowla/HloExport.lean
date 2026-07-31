/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE `Hlo` CAP⟧ — the builder's base EQUATION, re-threaded (node HLO-EXPORT)

`chowlaRegime_exists_param_gen` (`RegimeParam.lean:403`) sets the regime base by
an EQUALITY,

```
Hlo = max 4000000 (max Hlo₀ (4·⌈1/ε⌉₊⁴))
```

and then exports only its `≥` half (`Hlo₀ ≤ R.Hlo`).  Every downstream statement
inherits that discard, so no surface in the chain carries an UPPER bound on
`R.Hlo` — and a consumer whose band is TWO-SIDED in `loglog R.Hlo` (the M-band of
the compose) cannot close.  This file re-threads the missing half as ADDITIVE
TWINS: each declaration here is a landed statement plus ONE conjunct, proved by
consuming the previous twin.  No landed declaration is touched.

## The cap shape, step by step

* §1 `chowlaRegime_exists_param_gen_hloCap` carries the builder's own bytes — the
  EQUATION itself, `R.Hlo = max 4000000 (max Hlo₀ (4·⌈1/ε⌉₊⁴))`.  This is the one
  place where the proof must be replayed (the equation is discarded inside the
  landed proof, so no consequence of the landed statement can recover it); the
  replay is `RegimeParam.lean:391–459` verbatim with the equation kept.
* §2 the two tower twins pass the conjunct through untouched
  (`regimeEnlargeX'` carries `Hlo` VERBATIM, `RegimeParam.lean:506`).
* §3 the head twin `log_chowla_two_budget_head_g_sq_count_hloCap` re-shapes it
  for the road.  The head calls the builder at
  `Hlo₀ := max A (max extraFloor U1floor)` with `A` the head's own four-arm
  ε-determined floor, so the equation becomes

  ```
  R.Hlo ≤ max Hcap (max extraFloor U1floor),
  Hcap := max 4000000 (max A (4·⌈1/ε⌉₊⁴))
  ```

  — and `Hcap` is CONSUMER-FREE, hence hoisted into the `∃`-prefix beside
  `ε`, `K`, `δ₀`.  That is the whole content: a consumer who fires the head at
  `U1floor ≥ Hcap` gets `R.Hlo ≤ U1floor` on top of the landed `U1floor ≤ R.Hlo`,
  i.e. the base is PINNED, and a two-sided `loglog R.Hlo` band closes.

⟦WHY THE HEAD IS REPLAYED⟧  `spine_False_core_xi_sq` (`SpineFinal.lean:1164`) is
`private`, so the head's door implication cannot be re-derived from outside its
file by citing it.  The core's own body, however, is a public assembly
(`log_chowla_two_shell_xi_sq` + `sqrt_le_window_at`/`omega_big_at`/`x_big_at`/
`pH_headroom_at`/`singleCorr_of_fails`/`primeWindow_card_le_of_regime`), so §3
carries `spine_False_core_xi_sq_cap`, a VERBATIM in-file transcription of it
(`SpineFinal.lean:1164–1303`, statement and proof, name changed) — the S0-TOWER
in-file-core precedent, one file over.  It is a separate declaration, not an
inline block, because heartbeats are counted per declaration.  The head twin's
own proof is then `SpineFinal.lean:1370–1445` with exactly two edits: the builder
call (§2) and the core name.
-/
import Salt.Entropy.Chowla.SpineFinal

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### §1 — the builder twin: the base equation, KEPT -/

/-- **The parametric regime builder, with the base equation exported**
(`chowlaRegime_exists_param_gen_hloCap`) — `chowlaRegime_exists_param_gen`
(`RegimeParam.lean:386`) plus the fourth conjunct

```
R.Hlo = max 4000000 (max Hlo₀ (4·⌈1/ε⌉₊⁴))
```

which is `hHlodef`, the line the landed proof creates at `:403` and discards at
`:389`.  The three landed conjuncts are byte-identical and the proof is the
landed one verbatim; only the final anonymous constructor gains a component. -/
theorem chowlaRegime_exists_param_gen_hloCap (eps : ℚ) (heps : 0 < eps)
    (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) (Jof : ℕ → ℕ)
    (hJof : ∀ B : ℕ, 4000000 ≤ B → Real.log 2 < towerDropSum 2 1 B (Jof B)) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧
      R.Hhi = chowlaTower 2 1 R.Hlo (Jof R.Hlo) ∧
      R.Hlo = max 4000000 (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
  classical
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- the scale `m ≥ 1/ε`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈(1 / eps : ℚ)⌉₊ := ⟨_, rfl⟩
  have hm_ge : (1 / eps : ℚ) ≤ (m : ℚ) := by rw [hmdef]; exact Nat.le_ceil _
  have hem : (1 : ℚ) ≤ eps * (m : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hm_ge (le_of_lt heps)
    rwa [mul_one_div, div_self (ne_of_gt heps)] at h
  have hm1N : 1 ≤ m := by rw [hmdef]; exact Nat.ceil_pos.mpr (div_pos one_pos heps)
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1N
  have hemR : (1 : ℝ) ≤ (eps : ℝ) * (m : ℝ) := by exact_mod_cast hem
  -- the enlarged base floor
  obtain ⟨Hlo, hHlodef⟩ : ∃ Hlo : ℕ, Hlo = max 4000000 (max Hlo₀ (4 * m ^ 4)) := ⟨_, rfl⟩
  have hHlo_floor : 4000000 ≤ Hlo := by rw [hHlodef]; exact le_max_left _ _
  have hHlo0 : Hlo₀ ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHlo4 : 4 * m ^ 4 ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hHlo4Q : (4 : ℚ) * (m : ℚ) ^ 4 ≤ (Hlo : ℚ) := by exact_mod_cast hHlo4
  have hHlo4R : (4 : ℝ) * (m : ℝ) ^ 4 ≤ (Hlo : ℝ) := by exact_mod_cast hHlo4
  -- ⟦THE EXPORTED EQUATION⟧ the landed `hHlodef`, spelled at `⌈1/ε⌉₊`
  have hHlocap : Hlo = max 4000000 (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
    rw [hHlodef, hmdef]
  -- `hcoprime : 1 ≤ ε²·Hlo/2`
  have hcop : ((1 : ℕ) : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2 := by
    have hprod : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 := by
      have h1 : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 := by nlinarith [hem, sq_nonneg (eps * (m : ℚ) - 1)]
      have h2 : (1 : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith [hm1, sq_nonneg ((m : ℚ) - 1)]
      exact le_trans h1 (le_mul_of_one_le_right (sq_nonneg _) h2)
    have heq : (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 = eps ^ 2 * (m : ℚ) ^ 4 := by ring
    have h4le : (4 : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) := by
      have hmul : eps ^ 2 * (4 * (m : ℚ) ^ 4) ≤ eps ^ 2 * (Hlo : ℚ) :=
        mul_le_mul_of_nonneg_left hHlo4Q (sq_nonneg eps)
      nlinarith [hmul, hprod, heq]
    rw [Nat.cast_one]; linarith
  -- `hPNTwindow : √Hlo ≤ ε²·Hlo/2`
  have hPNT : Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) / 2 := by
    have hsqrtHlo : (2 : ℝ) * (m : ℝ) ^ 2 ≤ Real.sqrt (Hlo : ℝ) := by
      have heq : Real.sqrt (4 * (m : ℝ) ^ 4) = 2 * (m : ℝ) ^ 2 := by
        rw [show (4 : ℝ) * (m : ℝ) ^ 4 = (2 * (m : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      calc (2 : ℝ) * (m : ℝ) ^ 2 = Real.sqrt (4 * (m : ℝ) ^ 4) := heq.symm
        _ ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_le_sqrt hHlo4R
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_nonneg _
    have hHloeq : Real.sqrt (Hlo : ℝ) * Real.sqrt (Hlo : ℝ) = (Hlo : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h2 : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) := by
      have hstep : (eps : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtHlo (sq_nonneg _)
      nlinarith [hstep, hemR, sq_nonneg ((eps : ℝ) * (m : ℝ) - 1)]
    have h3 : 2 * Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h2 hsqrtnn
      rw [mul_assoc, hHloeq] at hh
      linarith [hh]
    linarith [h3]
  -- the tower endpoint and its divergence
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = Jof Hlo := ⟨_, rfl⟩
  have hJ : Real.log 2 < towerDropSum 2 1 Hlo J := by
    rw [hJdef]; exact hJof Hlo hHlo_floor
  obtain ⟨Hhi, hHhidef⟩ : ∃ Hhi : ℕ, Hhi = chowlaTower 2 1 Hlo J := ⟨_, rfl⟩
  have hHhi_floor : 4000000 ≤ Hhi := by rw [hHhidef]; exact chowlaTower_base_floor hHlo_floor J
  have hHlohi : Hlo ≤ Hhi := by rw [hHhidef]; exact chowlaTower_base_ge hHlo_floor J
  have hHhieq : Hhi = chowlaTower 2 1 Hlo (Jof Hlo) := by rw [hHhidef, hJdef]
  -- the outer scale at this `ε` and endpoint
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH, homega, hxb⟩ :=
    regime_outer_param eps heps heps1 Hhi (4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊) hHhi_floor
  exact ⟨{ x := x, ω := ω, a := 1, eps := eps, Hlo := Hlo, Hhi := Hhi, C0 := 2, J := J,
           hx := hx2, hω := hω2, hωx := hωx, ha := le_refl 1, heps := heps, heps1 := heps1,
           hHlo := le_trans (by norm_num) hHlo_floor, hHlohi := hHlohi, hC0 := le_refl 2,
           hHlo_floor := hHlo_floor, hheadroom := hhead, hcoprime := hcop, hfit := hHhidef.ge,
           hJcon := hJ, hheadroom' := hhead', hPHheadroom := hPH, hPNTwindow := hPNT,
           hωbig := homega, hxbig := hxb }, rfl, hHlo0, hHhieq, hHlocap⟩

/-! ### §2 — the two tower twins: the conjunct, PASSED THROUGH -/

/-- **The regime builder at `K = 9/2`, cap-carrying**
(`chowlaRegime_exists_param_tower_45_hloCap`) — `TowerExport.lean:876`'s statement
plus the base equation.  The proof is that one verbatim on the §1 builder. -/
theorem chowlaRegime_exists_param_tower_45_hloCap (eps : ℚ) (heps : 0 < eps)
    (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧
      (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        Real.log (Real.log (R.Hhi : ℝ))
          ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
      R.Hlo = max 4000000 (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
  obtain ⟨R, hReps, hRHlo, hRHhi, hRcap⟩ :=
    chowlaRegime_exists_param_gen_hloCap eps heps heps1 Hlo₀ (towerJmin 2 1)
      (fun _ hB => towerJmin_spec hB)
  refine ⟨R, hReps, hRHlo, fun hu => ?_, hRcap⟩
  rw [hRHhi]
  exact tower_loglog_le_45 R.hHlo_floor hu

/-- **The head-shaped builder at `K = 9/2`, cap-carrying**
(`chowlaRegime_exists_param_head_tower45'_hloCap`) — `TowerExport.lean:892`'s
statement plus the base equation.  `regimeEnlargeX'` carries `Hlo` VERBATIM
(`RegimeParam.lean:506`), so the equation survives the outer-scale push
untouched, exactly as `Hlo₀ ≤ R.Hlo` does there. -/
theorem chowlaRegime_exists_param_head_tower45'_hloCap (eps : ℚ) (heps : 0 < eps)
    (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
      (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        Real.log (Real.log (R.Hhi : ℝ))
          ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
      R.Hlo = max 4000000 (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
  obtain ⟨R, hReps, hRHlo, hRtow, hRcap⟩ :=
    chowlaRegime_exists_param_tower_45_hloCap eps heps heps1 Hlo₀
  exact ⟨regimeEnlargeX' R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRHlo,
    le_max_right _ _, hRtow, hRcap⟩

/-! ### §3 — the head twin: the cap RE-SHAPED for the road -/

/-- Mutual information is symmetric at the window pair (the in-file re-statement
of `SpineFinal`'s own `private` twin, which cannot be cited across files):
`entropy_decrement` produces the `liouville : residue` order, the shell consumes
`residue : liouville`. -/
private lemma mutualInfo_window_comm_cap (R : ChowlaRegime) (H : ℕ) :
    I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      = I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
  simp only [mutualInfo_def]
  rw [entropy_comm (measurable_residueWindow R.eps H) (measurable_liouvilleWindow H)
    (logMeasure R.x R.ω)]
  ring

/-- The `max`-lattice shuffle that turns the builder's base equation into the
head's consumer-facing cap: with `a = 4000000`, `b` the head's ε-determined
floor, `c = 4·⌈1/ε⌉₊⁴` and `(d, e)` the consumer's two floors, the base
`max a (max (max b (max d e)) c)` sits under `max Hcap (max d e)` at the
consumer-FREE `Hcap = max a (max b c)`. -/
private lemma hloCap_shuffle (a b c d e : ℕ) :
    max a (max (max b (max d e)) c) ≤ max (max a (max b c)) (max d e) := by
  omega

/-- **The `L²` spine contradiction core, in-file twin** (`spine_False_core_xi_sq_cap`)
— `SpineFinal.lean:1164`'s `private` core, VERBATIM (statement and proof), under a
fresh name because `private` blocks the citation across files.  The body is a
public assembly (`log_chowla_two_shell_xi_sq` + the regime reads
`sqrt_le_window_at`/`omega_big_at`/`x_big_at`/`pH_headroom_at`, plus
`singleCorr_of_fails` and `primeWindow_card_le_of_regime`), so the twin is a
transcription, not a re-proof; it exists only so §3's head can be replayed at the
cap-carrying regime.  The S0-TOWER in-file-core precedent, one file over. -/
private theorem spine_False_core_xi_sq_cap (R : ChowlaRegime) {ρ : ℝ}
    (hdoor : MRTUniformityXiL2 R ρ)
    (cE : ℝ) (_hcE : 0 < cE) (H₀red : ℕ)
    (hred : ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀red ≤ H →
      (eps : ℝ) ≤ cE / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1
          ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
          ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|)
    (cD3 : ℝ) (hcD3 : 0 < cD3) (H₀D3 : ℕ)
    (hD3 : ∀ (eps : ℚ) (H : ℕ), H₀D3 ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      cD3 / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (C : ℝ) (hC : 0 < C)
    -- the SQUARED, DIAGONAL circle-method estimate (`circle_method_estimate_sq`):
    (hcm : ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H =>
                    (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (H : ℕ) [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hH₀ : max H₀red H₀D3 ≤ H)
    (hepsc : (R.eps : ℝ) ≤ cE / (32 * Real.log 4))
    (t g κ c₀ : ℝ) (ht : 0 < t) (hg : 0 < g)
    (hgle : g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
        / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    (hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ)
    (hbudget1 : C * ((H : ℝ) / Real.log (H : ℝ)) * (c₀ * (R.eps : ℝ))
        + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
        + shellError R H t g κ
      ≤ cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)))
    (hbudget2 : ρ < c₀ * (R.eps : ℝ))
    (hfail : logChowla2Fails R.eps R.x R.ω) : False := by
  classical
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepshalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by
      exact_mod_cast (by linarith [R.heps1] : (2 : ℚ) * R.eps ≤ 1)
    linarith
  have hepssq : (R.eps : ℝ) ^ 2 ≤ 1 := by nlinarith [hepshalf, hepsRpos]
  -- floor bookkeeping
  have hHnatM : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH3 : 3 ≤ H := by omega
  have hH₀red : H₀red ≤ H := le_trans (le_max_left _ _) hH₀
  have hH₀D3 : H₀D3 ≤ H := le_trans (le_max_right _ _) hH₀
  -- real-side H facts
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHnatM
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH : 1 ≤ Real.log (H : ℝ) := by
    rw [Real.le_log_iff_exp_le hHpos]
    exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith
  -- the regime discharges (sqrt / ω / x / head)
  have hreg : Real.sqrt (H : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) / 2 :=
    sqrt_le_window_at R hlo hhi
  have hsqrt2000 : (2000 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    rw [show (2000 : ℝ) = Real.sqrt 4000000 by
      rw [show (4000000 : ℝ) = 2000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hHR
  have h4 : (4 : ℝ) ≤ (R.eps : ℝ) ^ 2 * (H : ℝ) := by nlinarith [hreg, hsqrt2000]
  have hωbig : (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ))
      + 64 / (R.eps : ℝ) + 1 ≤ Real.log (R.ω : ℝ) := omega_big_at R hhi h4
  have hxbig : (R.ω : ℝ) * (H : ℝ)
      + 48 * (R.ω : ℝ) * (1 + 2 / (R.eps : ℝ) ^ 2) / (R.eps : ℝ) ≤ (R.x : ℝ) :=
    x_big_at R hhi
  have hhead : 8 * (PH R.eps H : ℝ) ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := pH_headroom_at R hhi
  -- 2 ≤ log ω
  have hlogε2H_nn : (0 : ℝ) ≤ Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ)) :=
    Real.log_nonneg (by linarith [h4])
  have hterm1 : (0 : ℝ) ≤ (16 / (R.eps : ℝ)) * Real.log ((R.eps : ℝ) ^ 2 * (H : ℝ)) :=
    mul_nonneg (by positivity) hlogε2H_nn
  have h64 : (128 : ℝ) ≤ 64 / (R.eps : ℝ) := by
    rw [le_div_iff₀ hepsRpos]; nlinarith [hepshalf]
  have hlog2 : 2 ≤ Real.log (R.ω : ℝ) := by nlinarith [hωbig, hterm1, h64]
  -- the D3 Mertens lower bound + nonemptiness
  set SP : ℝ := ∑ p ∈ primeWindow R.eps H, (1 / (p : ℝ)) with hSP
  have hmert : cD3 / Real.log (H : ℝ) ≤ SP := hD3 R.eps H hH₀D3 hreg hepssq
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hSPpos : (0 : ℝ) < SP := lt_of_lt_of_le (div_pos hcD3 hlogHpos) hmert
  have hne : (primeWindow R.eps H).Nonempty := by
    rcases (primeWindow R.eps H).eq_empty_or_nonempty with he | hn
    · exact absurd (hSP.trans (by rw [he, Finset.sum_empty])) (ne_of_gt hSPpos)
    · exact hn
  -- the single-correlation seed and the reduce (h211 producer)
  set X : ℝ := |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure R.x R.ω)| with hXdef
  have hseed : (R.eps : ℝ) / 2 ≤ X :=
    singleCorr_of_fails R.eps R.hx R.hω R.hωx hlog2 hfail
  have hredH : (1 / 2) * SP * (H : ℝ) * X
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| :=
    hred R.eps H R.x R.ω R.hx R.hω R.hωx R.heps hepssq hH3 hlogH h4 hreg hH₀red hepsc
      hωbig hxbig hseed
  -- the concrete h211 (coefficient c₁ = cD3/4)
  have hAX : (cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2) ≤ SP * X :=
    mul_le_mul hmert hseed (by positivity) hSPnn
  have h211 : cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ n, fBridgeF R.eps H (liouvilleWindow H n) (residueWindow R.eps H n)
          ∂(logMeasure R.x R.ω)| := by
    calc cD3 / 4 * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        = (1 / 2) * (H : ℝ) * ((cD3 / Real.log (H : ℝ)) * ((R.eps : ℝ) / 2)) := by
          field_simp; ring
      _ ≤ (1 / 2) * (H : ℝ) * (SP * X) :=
          mul_le_mul_of_nonneg_left hAX (by positivity)
      _ = (1 / 2) * SP * (H : ℝ) * X := by ring
      _ ≤ _ := hredH
  -- the SQUARED circle-method bound (hcirc) via the card discharge, at the diagonal
  have hcard : ((primeWindow R.eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((R.eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime R.eps H hreg hH3
  have hcirc : ∀ n : ℕ,
      |∑ p : primeWindow R.eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((R.eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2)
                * ‖ZMod.dft (fun j : ZMod H =>
                    (windowVal H (liouvilleWindow H n) (ZMod.val j) : ℂ)) ξ‖ ^ 2) :=
    fun n => hcm R.eps H (liouvilleWindow H n)
      (fun i => abs_liouvilleWindow_le_one H n i) hcard
  -- fire the Ξ-SUMMED L² shell (no `hXi`, no `0 ≤ δ`: the seam needs neither)
  exact log_chowla_two_shell_xi_sq R hlo hhi hH3 hlogH hne hreg hhead ht hg hgle hI
    (by positivity) h211 hC hcirc hdoor hbudget1 hbudget2

/-- **THE `L²` SPINE-BUDGET HEAD, count-exporting, WITH THE BASE CAP**
(`log_chowla_two_budget_head_g_sq_count_hloCap`) — `SpineFinal.lean:1359` plus
ONE conjunct and ONE `∃`-prefix item:

```
∃ (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), … ∀ extraFloor U1floor g, ∃ R, …
  ∧ R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧ …
```

`Hcap` is `max 4000000 (max A (4·⌈1/ε⌉₊⁴))` at the head's own four-arm floor
`A = max (max (max H₀red H₀D3) H₀xi) (budgetFloor ε (cD3·ε/(144·log 4)))`, so it
depends on `ε` alone and is fixed BEFORE the consumer's floors — which is what
makes the conjunct usable: firing at `U1floor ≥ Hcap` PINS `R.Hlo` between
`U1floor` and `max Hcap U1floor = U1floor`.

Every other conjunct, the `ε` choice, the `δ₀`, the five-arm floor and the
`hbudget1`/`hbudget2` block are the landed head's, verbatim.  Two edits: the
regime comes from `chowlaRegime_exists_param_head_tower45'_hloCap` (§2), and the
final `spine_False_core_xi_sq` discharge — `private`, hence uncitable here — is
INLINED as its own body (`SpineFinal.lean:1214–1303`), which is a public
assembly ending at `log_chowla_two_shell_xi_sq`.

⚠ THE SEAM WARNING rides this statement unchanged (`MRTDoor.lean:174–182`):
`MRTUniformityXiL2 R ρ` is a FINITE SUM OF INTEGRALS, `∑` outside `∫`, no `sup`
inside; the `L²` door is SUPPLIED by the road, never claimed from Prop 2.4. -/
theorem log_chowla_two_budget_head_g_sq_count_hloCap :
    ∃ (ε : ℚ) (K δ₀ : ℝ) (Hcap : ℕ), 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (extraFloor U1floor : ℕ) (g : ℕ → ℕ → ℕ), ∃ R : ChowlaRegime,
        R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXi R.eps H).card : ℝ) ≤ K) ∧
        (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
          Real.log (Real.log (R.Hhi : ℝ))
            ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
        R.Hlo ≤ max Hcap (max extraFloor U1floor) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀ → MRTUniformityXiL2 R ρ →
          ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨cE, hcE, H₀red, hred⟩ := hreduce_holds_final
  obtain ⟨cD3, hcD3, H₀D3, hD3⟩ := primeWindow_sum_inv_ge
  obtain ⟨C, hC, hcm⟩ := circle_method_estimate_sq (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hbound_pos : (0 : ℝ) < min (min (min (cE / (32 * Real.log 4)) (1 / 2))
      (cD3 / 16)) (cD3 / (16 * C)) := by
    refine lt_min (lt_min (lt_min ?_ ?_) ?_) ?_
    · exact div_pos hcE (mul_pos (by norm_num) hlog4)
    · norm_num
    · exact div_pos hcD3 (by norm_num)
    · exact div_pos hcD3 (mul_pos (by norm_num) hC)
  obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn hbound_pos
  have hεR0 : (0 : ℝ) < (ε : ℝ) := hε0
  have hεQpos : 0 < ε := by exact_mod_cast hεR0
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)))
  have hε_half_lt : (ε : ℝ) < 1 / 2 := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := le_of_lt (lt_of_lt_of_le hεlt
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (2 : ℝ) * (ε : ℝ) < 1 := by linarith [hε_half_lt]
    have h2Q : (2 : ℚ) * ε < 1 := by exact_mod_cast h2
    linarith
  have hε2 : (ε : ℝ) ^ 2 < 1 / 2 := by nlinarith [hεR0, hε_half_lt]
  obtain ⟨K, hK, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded ε hεQpos hε2
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ and the consumer-free cap it induces
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = max (max (max H₀red H₀D3) H₀xi)
      (budgetFloor (ε : ℝ) (cD3 * (ε : ℝ) / (144 * Real.log 4))) := ⟨_, rfl⟩
  refine ⟨ε, K, cD3 / (16 * C) * (ε : ℝ) / 4,
    max 4000000 (max A (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), hεQpos, hK,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num), ?_⟩
  intro extraFloor U1floor g₅
  obtain ⟨R, hReps, hRHlo, hRg, hRtow, hRcap⟩ :=
    chowlaRegime_exists_param_head_tower45'_hloCap ε hεQpos hεQ1
      (max A (max extraFloor U1floor)) g₅
  rw [hAdef] at hRHlo
  have hxiHlo : H₀xi ≤ R.Hlo :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hRHlo
  refine ⟨R, hReps, le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, ?_, hRtow, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the builder's base equation, shuffled onto the consumer's floors
    rw [hRcap]
    exact hloCap_shuffle _ _ _ _ _
  intro ρ _hρpos hρ hdoor hfail
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm_cap]; exact hMI
  have hepsc : (R.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) hRHlo) hlo
  have hfloorH : budgetFloor (R.eps : ℝ)
      (cD3 * (R.eps : ℝ) / (144 * Real.log 4)) ≤ H := by
    rw [hReps]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo) hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witness R H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε`
  have hbudget2 : ρ < cD3 / (16 * C) * (R.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ, hpos]
  -- ⟦THE CORE⟧ the in-file twin of the `private` `spine_False_core_xi_sq`
  exact spine_False_core_xi_sq_cap R hdoor cE hcE H₀red hred cD3 hcD3 H₀D3 hD3
    C hC hcm H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail

end Salt.Entropy.Chowla
