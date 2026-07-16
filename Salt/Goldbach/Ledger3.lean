/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Ledger2

/-!
# The Goldbach F2 ledger, part 3 — `gold_hL_bundle`

The ONE analytic bundle `chen_goldbach_of_ledger` consumes: `normalized_package` at the
Goldbach carriers `M1G`/`M2G`/`M3G`, the exact mirror of the twin `hL_bundle`
(`Salt/Chen/FinLed3.lean`) with the punctured suppliers from Ledger parts 1–2:

* the crumbs at the gold `X_W` (`gold_crumbs_le` — the `W`-comparison transfer);
* the count seam with NO equidistribution crumb (`gold_hcount_seam`);
* the value certs at the punctured depth (`gold_hcertA1/A2/A3_at_op`);
* the punctured `W`-ratio and its `3/8 + 1/100000` collapse
  (`gold_hWy_at_op` / `gold_rho_le` — the residual `1 + 16/(z−2)` absorbed);
* the twin rows reused verbatim where the carrier is op-value-only
  (`slack1_le`, `A2weight_le`, `razor_topwindow_cost`, `e3_collapse`).

Error shares as landed: `e1 ≤ 30/100000`, `e2/2 ≤ (4342/10⁶ + 2200022/10⁹ + 1/10⁵)/2`,
`e3/2 ≤ (31/100000 + 1/100000)/2`, `e4/2 ≤ (1/100000)/2` — total `< 1/200`.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen Salt.BrunLower

namespace Salt.Goldbach

set_option maxHeartbeats 1000000 in -- deep op composition: normalized_package unifies 4 carriers
/-- **`gold_hL_bundle`** — the F2 ledger positivity at the Goldbach carriers, uniformly
in the admissible residue `a`.  The exact `hL` slot of `chen_goldbach_of_ledger`. -/
theorem gold_hL_bundle : ∃ (R : ℝ) (x₁ : ℕ), 0 ≤ R ∧ ∀ N : ℕ, x₁ ≤ N →
    R ≤ Real.log N → Even N →
    ∀ a : ℕ, a ≤ N → Nat.Coprime opQ a → Nat.Coprime opQ (N - a) →
    0 < M1G N a - M2G N a / 2 - M3G N / 2
      - Real.log N * (N : ℝ) / ((opZ N : ℝ) - 1) / 2 := by
  obtain ⟨Ccount, xcount, hCcount_nn, hcount_s⟩ := gold_hcount_seam
  obtain ⟨xs1, hslack1⟩ := slack1_le
  obtain ⟨xag, hag⟩ := gold_aggSlack_le
  obtain ⟨xcr, hcr⟩ := gold_crumbs_le
  obtain ⟨xa2, ha2⟩ := A2weight_le
  obtain ⟨xrh, hrh⟩ := gold_rho_le
  obtain ⟨xc1, hc1⟩ := gold_hcertA1_at_op
  obtain ⟨xc2, hc2⟩ := gold_hcertA2_at_op
  obtain ⟨xc3, hc3⟩ := gold_hcertA3_at_op
  obtain ⟨xwy, hwy⟩ := gold_hWy_at_op
  obtain ⟨xlg, hlg⟩ := a12_log_ge (1600000 * Ccount + 34000000)
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨0, xcount + xs1 + xag + xcr + xa2 + xrh + xc1 + xc2 + xc3 + xwy + xlg + xt
    + 10 ^ 48 + 1, le_refl 0, fun N hx _ _ a _ _ _ => ?_⟩
  have hx48 : (10 : ℕ) ^ 48 ≤ N := by omega
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hx48R
  have hlogx : (1600000 * Ccount + 34000000 : ℝ) ≤ Real.log N := (hlg N (by omega)).2
  have hlogxpos : 0 < Real.log N := lt_of_lt_of_le (by positivity) hlogx
  obtain ⟨-, -, -, hz3, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := htower N (by omega)
  have hzR1 : (1 : ℝ) < (opZ N : ℝ) := by exact_mod_cast (by omega : 1 < opZ N)
  have hlogzpos : 0 < Real.log (opZ N) := Real.log_pos hzR1
  have hφpos : (0 : ℝ) < (opQ.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  -- floor: log opZ ≥ (1/8)log N − 1/999999
  obtain ⟨-, -, -, hzlog_ge⟩ := opf_window_floor_bounds N hx48R (γ := (1 : ℝ) / 8)
    (by norm_num)
  have hlogopZ_ge18 : (1 / 8) * Real.log N - 1 / 999999 ≤ Real.log (opZ N) := by
    rw [opZ]
    linarith [hzlog_ge]
  -- ══ atom values from the gold crumbs ══
  obtain ⟨hXWpos, hR1XW, hR2XW, hR3XW, he4XW⟩ := hcr N (by omega) a
  -- ══ the count slot (no equidistribution crumb) ══
  have hcount_bd := hcount_s N (by omega)
  -- ══ ecount = ecountOp Ccount N ≤ 1/100000 ══
  have hlogopZ_big : (200000 : ℝ) * Ccount ≤ Real.log (opZ N) := by
    have : (1 / 8) * Real.log N - 1 / 999999 ≥ 200000 * Ccount := by
      nlinarith [hlogx, hCcount_nn]
    linarith [hlogopZ_ge18, this]
  have hec_le : ecountOp Ccount N ≤ 1 / 100000 := by
    have h2 : ecountOp Ccount N ≤ 1 / 200000 := by
      rw [ecountOp, div_le_iff₀ hlogzpos]
      rcases eq_or_lt_of_le hCcount_nn with h | h
      · rw [← h]; positivity
      · nlinarith [hlogopZ_big, h]
    linarith
  have hec_nn : 0 ≤ ecountOp Ccount N := by
    rw [ecountOp]
    exact div_nonneg hCcount_nn hlogzpos.le
  -- ══ rho, slack3 ══
  obtain ⟨hrho_nn, hrho_hi⟩ := hrh N (by omega)
  have hs3_nn : 0 ≤ opEps * CsharpB opEps * Real.exp 2
      * hBJS (logRatio (opY N) (opDlev N)) := slack_nn _
  have hs3_hi : opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY N) (opDlev N))
      ≤ 200002 / 100000000 :=
    le_trans (slack_le_epsC _) (le_trans opf_epsC_le (by norm_num))
  -- ══ the punctured aggSlack ≤ 2200022/10⁹ ══
  have hagg_bd : (∑ p ∈ (Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
          * hBJS (logRatio (opZ N) (cdiv (opD N) p))))
      ≤ 2200022 / 1000000000 := by
    refine le_trans (hag N (by omega)) ?_
    have := mul_le_mul_of_nonneg_right opf_epsC_le (by norm_num : (0 : ℝ) ≤ 11 / 10)
    linarith [this]
  -- ══ the A₂ tail: wtail and its bound (x-only, twin rows verbatim) ══
  set A2w := A2weight (opZ N) ((opZ N) ^ 4) ((opY N : ℝ) + 1) with hA2wdef
  obtain ⟨hA2w_nn, hA2w_hi⟩ := ha2 N (by omega)
  set WTAIL : ℝ := (1250 / 1249) * (Real.log 6 / 4 + 1125 / 3997000
      + A2w * (21 / Real.log (opZ N) + 2 / ((opZ N : ℝ) - 1))) - Real.log 6 / 4 with hWTdef
  have hlp_nn : 0 ≤ 21 / Real.log (opZ N) + 2 / ((opZ N : ℝ) - 1) := by positivity
  have hlp_le : 21 / Real.log (opZ N) + 2 / ((opZ N : ℝ) - 1) ≤ 1 / 100000 := by
    have hz6 : (10 : ℝ) ^ 6 ≤ (opZ N : ℝ) := by
      obtain ⟨-, h, -, -⟩ := opf_window_floor_bounds N hx48R (γ := (1 : ℝ) / 8)
        (by norm_num)
      rw [opZ]
      exact h
    have h21 : 21 / Real.log (opZ N) ≤ 1 / 200000 := by
      rw [div_le_iff₀ hlogzpos]
      nlinarith [hlogopZ_ge18, hlogx, hCcount_nn]
    have h2z : 2 / ((opZ N : ℝ) - 1) ≤ 1 / 200000 := by
      rw [div_le_div_iff₀ (by linarith [hz6]) (by norm_num)]
      nlinarith [hz6]
    linarith [h21, h2z]
  have hwtail_bd : (3 + 43 / 75) * WTAIL ≤ 4342 / 1000000 := by
    have hexpand : (3 + 43 / 75) * WTAIL
        = (3 + 43 / 75) * ((1 / 1249) * (Real.log 6 / 4) + (1250 / 1249) * (1125 / 3997000))
          + (3 + 43 / 75) * (1250 / 1249) * A2w
              * (21 / Real.log (opZ N) + 2 / ((opZ N : ℝ) - 1)) := by
      rw [hWTdef]; ring
    have hrazor : (3 + 43 / 75)
        * ((1 / 1249) * (Real.log 6 / 4) + (1250 / 1249) * (1125 / 3997000))
        ≤ 4302 / 1000000 := by
      have := razor_topwindow_cost
      linarith [this]
    have hvanish : (3 + 43 / 75) * (1250 / 1249) * A2w
        * (21 / Real.log (opZ N) + 2 / ((opZ N : ℝ) - 1)) ≤ 40 / 1000000 := by
      have hA2w1 : A2w ≤ 1 := le_trans hA2w_hi (by norm_num)
      have hprod : A2w * (21 / Real.log (opZ N) + 2 / ((opZ N : ℝ) - 1)) ≤ 1 / 100000 :=
        le_trans (mul_le_mul hA2w1 hlp_le hlp_nn (by norm_num)) (by norm_num)
      nlinarith [hprod, mul_nonneg hA2w_nn hlp_nn]
    rw [hexpand]
    linarith [hrazor, hvanish]
  -- ══ the raw carrier bounds (definitional regroupings) ══
  have hrawA1 : (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
          (goldOpP_odd N)).totalMass
        * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
            (goldOpP_squarefree N) (goldOpP_odd N))
        * (fchain (maxDepth (goldA1SieveW opQ a N (goldOpP N)
              (goldOpP_squarefree N) (goldOpP_odd N))) (logRatio (opZ N) (opD N))
          - opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opZ N) (opD N)))
      - ((N : ℝ) / (Real.log N) ^ 10 + Real.sqrt N * (Nat.log 2 N : ℝ) * Real.log N)
      ≤ M1G N a := le_of_eq (by rw [M1G]; ring)
  have hrawA2 : M2G N a
      ≤ (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
            (goldOpP_odd N)).totalMass
          * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
              (goldOpP_squarefree N) (goldOpP_odd N))
          * (A2grid ((Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N))
                (opZ N) (opD N)
                (fun p => maxDepth (goldA2SieveW opQ a N (goldOpP N) p
                    (goldOpP_squarefree N) (goldOpP_odd N)))
              + ∑ p ∈ (Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
                  (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
                      * hBJS (logRatio (opZ N) (cdiv (opD N) p))))
        + (N : ℝ) / (Real.log N) ^ 10 := le_of_eq (by rw [M2G])
  have hrawA3 : M3G N ≤ Real.log N
      * (goldTripleSum N (opZ N) (opY N) / (opQ.totient : ℝ)
          * Salt.BrunLower.W (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
              (goldOpPs_squarefree N) (goldOpPs_odd N))
          * (Fchain (maxDepth (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
                (goldOpPs_squarefree N) (goldOpPs_odd N))) (logRatio (opY N) (opDlev N))
            + opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY N) (opDlev N)))
        + (N : ℝ) / (Real.log N) ^ 10) := le_of_eq rfl
  -- ══ hcertA2 in the `(3+43/75)·(log6/4 + wtail)` shape ══
  have hcertA2 : A2grid ((Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N))
        (opZ N) (opD N)
        (fun p => maxDepth (goldA2SieveW opQ a N (goldOpP N) p
            (goldOpP_squarefree N) (goldOpP_odd N)))
      ≤ (3 + 43 / 75) * (Real.log 6 / 4 + WTAIL) := by
    refine le_trans (hc2 N (by omega) a) (le_of_eq ?_)
    rw [hWTdef, hA2wdef]
    ring
  -- ══ the count slot at the gold totalMass ══
  have hcount : Real.log N * (goldTripleSum N (opZ N) (opY N) / (opQ.totient : ℝ))
      ≤ (cbar + ecountOp Ccount N)
          * (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
              (goldOpP_odd N)).totalMass := by
    rw [goldA1SieveW_totalMass]
    exact hcount_bd
  -- ══ nonnegativity side conditions ══
  have hFslack_nn : 0 ≤ Fchain (maxDepth (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
        (goldOpPs_squarefree N) (goldOpPs_odd N))) (logRatio (opY N) (opDlev N))
      + opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY N) (opDlev N)) := by
    have hFv : 0 ≤ Fchain (maxDepth (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
        (goldOpPs_squarefree N) (goldOpPs_odd N))) (logRatio (opY N) (opDlev N)) := by
      have hsum : (0 : ℝ) ≤ ∑ n ∈ (Finset.range (maxDepth (goldSwitchSieve N (opZ N)
          (opY N) (goldOpPs N) (goldOpPs_squarefree N) (goldOpPs_odd N)) + 1)).filter
            (fun n => Odd n),
          fseq n (logRatio (opY N) (opDlev N)) :=
        Finset.sum_nonneg fun n _ => fseq_nonneg n _
      unfold Fchain
      linarith
    linarith [hFv, slack_nn (logRatio (opY N) (opDlev N))]
  have hWz_nn : 0 ≤ Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
      (goldOpP_squarefree N) (goldOpP_odd N)) := (Salt.BrunLower.W_pos _).le
  have hLTnn : 0 ≤ Real.log N * (goldTripleSum N (opZ N) (opY N) / (opQ.totient : ℝ)) := by
    have hTS : 0 ≤ goldTripleSum N (opZ N) (opY N) := by
      rw [goldTripleSum_eq_card]
      positivity
    exact mul_nonneg hlogxpos.le (div_nonneg hTS hφpos.le)
  -- ══ compose normalized_package ══
  refine normalized_package (x := N) (z := opZ N)
    (totalMass := (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
        (goldOpP_odd N)).totalMass)
    (Wz := Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
        (goldOpP_squarefree N) (goldOpP_odd N)))
    hXWpos rfl hrawA1 (hc1 N (by omega) a) hrawA2 hcertA2 hrawA3 (hc3 N (by omega))
    hFslack_nn (hwy N (by omega) a) hrho_nn hWz_nn hLTnn hcount ?_
  -- ══ the error bundle ≤ 1/200 ══
  have he3 := e3_collapse cbar_pos.le (le_of_lt cbar_lt) hec_nn hec_le hrho_hi
    hs3_nn hs3_hi hR3XW
  linarith [hslack1 N (by omega), hR1XW, hwtail_bd, hagg_bd, hR2XW, he3, he4XW]

end Salt.Goldbach
