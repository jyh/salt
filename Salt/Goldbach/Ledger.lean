/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Asm6
import Salt.Chen.FinLed3

/-!
# The Goldbach F2 ledger, part 1 — depth facts, the `W`-comparison, the punctured `W`-ratio

`chen_goldbach_of_ledger` (Asm6) reduced the frozen theorem to ONE analytic bundle; this
file supplies the carrier-side ingredients of its discharge:

* **§0 — the punctured depth facts.**  `maxDepth` of the Goldbach sieves is the CARD of
  the punctured prime window `(Ico opW' z).filter (Prime ∧ ¬·∣N)`.  A Bertrand chain of
  ten primes in `(M₀, 2^10·M₀] ⊆ [opW', opZ N)` (`M₀ = opZ N/2^11`) minus the at-most-
  eight chain primes dividing `N` (nine primes `> M₀ ≳ N^{1/8}/2^12` dividing `N` force
  `N·N^{1/8}/2^{108} ≤ N`, false once `log N ≥ 700`) leaves `≥ 2` punctured primes —
  the `fchain_A1_final` (`N ≥ 2`) and `Fchain_switch_le` (`N ≥ 1`) depth slots.
* **§1 — the `W`-comparison.**  `W(goldA1SieveW …) ≥ W(twinA1SieveW …)`: the punctured
  prime-factor set is a SUBSET of the twin's and every factor `1 − ν(p) ∈ (0,1]`, so the
  punctured product is LARGER.  This transfers `FinLed3.crumbs_le` (the four crumb
  shares at the twin `X_W`) to the Goldbach `X_W` — `totalMass` is IDENTICAL on both
  sides (`= (ΣΛ)/φ(opQ)`, the singular-series cancellation made quantitative).
* **§2 — the punctured `W`-ratio.**  `W(goldSwitchSieve at goldOpPs) ≤ W(goldA1SieveW at
  goldOpP)·ρ`, `ρ = (log z/log y)(1 + 38/log z)(1 + 16/(z−2))` — the `W_ratio_upper`
  mirror whose `hwin` slot is the PUNCTURED window (the G-DENS gate correction), priced
  by `window_prod_upper_punctured_folded` with the `≤ 8` card row from `gold_op_Zpow9`;
  and `gold_rho_le` : `ρ ≤ 3/8 + 1/100000` at the tower.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen Salt.BrunLower

namespace Salt.Goldbach

/-! ## §0 — the Bertrand chain and the punctured depth facts -/

/-- A Bertrand chain: `k` distinct primes in `(b, 2^k·b]`, as a `Finset` of card `k`. -/
theorem bertrand_chain (b : ℕ) (hb : b ≠ 0) (k : ℕ) :
    ∃ S : Finset ℕ, S.card = k ∧ ∀ p ∈ S, p.Prime ∧ b < p ∧ p ≤ 2 ^ k * b := by
  induction k with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨S, hcard, hS⟩ := ih
    have h2k : 2 ^ k * b ≠ 0 := by positivity
    obtain ⟨p, hp, hlt, hle⟩ := Nat.bertrand (2 ^ k * b) h2k
    have hpS : p ∉ S := fun hmem => absurd (hS p hmem).2.2 (by omega)
    refine ⟨insert p S, by rw [Finset.card_insert_of_notMem hpS, hcard], ?_⟩
    intro q hq
    have hble : b ≤ 2 ^ k * b := Nat.le_mul_of_pos_left b (by positivity)
    have hstep : 2 ^ (k + 1) * b = 2 * (2 ^ k * b) := by ring
    rcases Finset.mem_insert.mp hq with rfl | hqS
    · exact ⟨hp, by omega, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := hS q hqS
      exact ⟨h1, h2, by omega⟩

/-- **The punctured window count** — past a threshold, the punctured prime window
`[opW', opZ N)` contains at least two primes not dividing `N`. -/
theorem gold_punctured_card_ge_two : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    2 ≤ ((Finset.Ico opW' (opZ N)).filter (fun q => q.Prime ∧ ¬ q ∣ N)).card := by
  obtain ⟨xL, hLg⟩ := a12_log_ge 700
  refine ⟨max (max xL (10 ^ 48)) ((2 ^ 11 * opW' + 1) ^ 8), fun N hN => ?_⟩
  have hxL : xL ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hx48 : (10 : ℕ) ^ 48 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hxW : (2 ^ 11 * opW' + 1) ^ 8 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : 0 < N := by positivity
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hx48
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  have hlog700 : (700 : ℝ) ≤ Real.log N := (hLg N hxL).2
  have hw'3 := opf_w'3
  -- `2^11·opW' + 1 ≤ opZ N` (the `opZ_gt_of_ge` pattern at the 8th power)
  have hzW : 2 ^ 11 * opW' + 1 ≤ opZ N := by
    rw [opZ]
    have hxR : ((2 ^ 11 * opW' + 1 : ℕ) : ℝ) ^ (8 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hxW
    have key : (((2 ^ 11 * opW' + 1 : ℕ) : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8)
        = ((2 ^ 11 * opW' + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast ((2 ^ 11 * opW' + 1 : ℕ) : ℝ) 8,
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hmono : (((2 ^ 11 * opW' + 1 : ℕ) : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by positivity) hxR (by norm_num)
    rw [key] at hmono
    exact Nat.le_floor (by exact_mod_cast hmono)
  -- `omega` must never see the eighth power or the `opW'` def-tower (it recurses
  -- unfolding them): drop the raw threshold rows and generalize the window floor
  clear hN hxW hxL hx48
  generalize opW' = w at hw'3 hzW ⊢
  -- the chain base `M₀ := opZ N / 2^11`, with `opW' ≤ M₀` and `2^11·M₀ ≤ opZ N`
  set M₀ : ℕ := opZ N / 2 ^ 11 with hM₀def
  have hM₀w : w ≤ M₀ := by
    rw [hM₀def, Nat.le_div_iff_mul_le (by norm_num : 0 < 2 ^ 11)]
    omega
  have hM₀0 : M₀ ≠ 0 := by omega
  have h211 : M₀ * 2 ^ 11 ≤ opZ N := by rw [hM₀def]; exact Nat.div_mul_le_self _ _
  -- the ten-prime Bertrand chain in `(M₀, 2^10·M₀]`
  obtain ⟨S, hScard, hSmem⟩ := bertrand_chain M₀ hM₀0 10
  -- `T` = the chain primes dividing `N`; `(M₀+1)^|T| ≤ N`
  set T : Finset ℕ := S.filter (fun q => q ∣ N) with hTdef
  have hTsub : T ⊆ N.primeFactors := by
    intro q hq
    rw [hTdef, Finset.mem_filter] at hq
    exact Nat.mem_primeFactors.mpr ⟨(hSmem q hq.1).1, hq.2, by omega⟩
  have hTprod : (M₀ + 1) ^ T.card ≤ N := by
    have hpow : (M₀ + 1) ^ T.card ≤ ∏ q ∈ T, q := by
      refine Finset.pow_card_le_prod T _ _ fun q hq => ?_
      have := (hSmem q (Finset.mem_of_mem_filter q hq)).2.1
      omega
    have hdvd : (∏ q ∈ T, q) ∣ N :=
      dvd_trans (Finset.prod_dvd_prod_of_subset T N.primeFactors _ hTsub)
        (Nat.prod_primeFactors_dvd N)
    exact le_trans hpow (Nat.le_of_dvd hN0 hdvd)
  -- the product contradiction: `|T| ≤ 8`
  have hT8 : T.card ≤ 8 := by
    by_contra hcon
    have h9 : (M₀ + 1) ^ 9 ≤ N :=
      le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hTprod
    have h9R : ((M₀ : ℝ) + 1) ^ (9 : ℕ) ≤ (N : ℝ) := by exact_mod_cast h9
    -- real side: `(M₀+1)^9 > N·N^{1/8}/2^{108} > N`
    have hr2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
      have h256 : ((2 : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) = 2 := by
        rw [← Real.rpow_natCast (2 : ℝ) 8, ← Real.rpow_mul (by norm_num)]
        norm_num
      calc (2 : ℝ) = ((2 : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) := h256.symm
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) :=
            Real.rpow_le_rpow (by positivity) (by linarith [hx48R]) (by norm_num)
    have hzfl : (N : ℝ) ^ ((1 : ℝ) / 8) - 1 ≤ ((opZ N : ℕ) : ℝ) := by
      rw [opZ]
      exact le_of_lt (Nat.sub_one_lt_floor _)
    have hzge : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ ((opZ N : ℕ) : ℝ) := by linarith
    have hM₀R : ((opZ N : ℕ) : ℝ) < 2 ^ 11 * ((M₀ : ℝ) + 1) := by
      have hmod : opZ N < 2 ^ 11 * (M₀ + 1) := by
        have := Nat.div_add_mod (opZ N) (2 ^ 11)
        have := Nat.mod_lt (opZ N) (show 0 < 2 ^ 11 by norm_num)
        omega
      exact_mod_cast hmod
    have hM₀big : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ^ 12 < (M₀ : ℝ) + 1 := by
      have h1 : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤ 2 ^ 11 * ((M₀ : ℝ) + 1) := by linarith
      linarith
    have h2108 : (2 : ℝ) ^ (108 : ℕ) < (N : ℝ) ^ ((1 : ℝ) / 8) := by
      have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hexp : Real.log ((2 : ℝ) ^ (108 : ℕ)) = 108 * Real.log 2 := by
        rw [Real.log_pow]; norm_num
      rw [Real.rpow_def_of_pos hNpos,
        ← Real.exp_log (show (0 : ℝ) < (2 : ℝ) ^ (108 : ℕ) by positivity), hexp]
      exact Real.exp_lt_exp.mpr (by linarith [hlog700])
    have hchain : (N : ℝ) < ((M₀ : ℝ) + 1) ^ (9 : ℕ) := by
      have hstep : ((N : ℝ) ^ ((1 : ℝ) / 8) / 2 ^ 12) ^ (9 : ℕ)
          < ((M₀ : ℝ) + 1) ^ (9 : ℕ) :=
        pow_lt_pow_left₀ hM₀big (by positivity) (by norm_num)
      have h98 : (1 : ℝ) / 8 * ((9 : ℕ) : ℝ) = 1 + 1 / 8 := by push_cast; norm_num
      have hpow9 : ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ (9 : ℕ)
          = (N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 8)) 9,
          ← Real.rpow_mul hNpos.le, h98, Real.rpow_add hNpos, Real.rpow_one]
      have hdivpow : ((N : ℝ) ^ ((1 : ℝ) / 8) / 2 ^ 12) ^ (9 : ℕ)
          = ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ (9 : ℕ) / (2 : ℝ) ^ (108 : ℕ) := by
        rw [div_pow]
        norm_num
      have h2108pos : (0 : ℝ) < (2 : ℝ) ^ (108 : ℕ) := by positivity
      have hNfrac : (N : ℝ) < (N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 8) / (2 : ℝ) ^ (108 : ℕ) := by
        rw [lt_div_iff₀ h2108pos]
        have := mul_lt_mul_of_pos_left h2108 hNpos
        linarith
      rw [hdivpow, hpow9] at hstep
      linarith
    linarith
  -- the clean chain primes land in the punctured window
  have hsplit : (S.filter (fun q => q ∣ N)).card
      + (S.filter (fun q => ¬ q ∣ N)).card = S.card :=
    Finset.card_filter_add_card_filter_not (fun q => q ∣ N)
  have hclean2 : 2 ≤ (S.filter (fun q => ¬ q ∣ N)).card := by
    rw [hScard] at hsplit
    rw [← hTdef] at hsplit
    omega
  refine le_trans hclean2 (Finset.card_le_card ?_)
  intro q hq
  rw [Finset.mem_filter] at hq
  obtain ⟨hqS, hqnd⟩ := hq
  obtain ⟨hqp, hqgt, hqle⟩ := hSmem q hqS
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, ?_⟩, hqp, hqnd⟩
  have : 2 ^ 10 * M₀ < M₀ * 2 ^ 11 := by
    have hM₀1 : 1 ≤ M₀ := by omega
    nlinarith
  omega

/-- **Depth ≥ 2 for the punctured A₁ carrier** (uniformly in the residue `a`). -/
theorem two_le_maxDepth_goldA1 : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ a : ℕ,
    2 ≤ maxDepth (goldA1SieveW opQ a N (goldOpP N)
      (goldOpP_squarefree N) (goldOpP_odd N)) := by
  obtain ⟨x₁, h⟩ := gold_punctured_card_ge_two
  refine ⟨x₁, fun N hN a => ?_⟩
  unfold maxDepth
  rw [goldA1SieveW_prodPrimes, goldOpP, goldPs_primeFactors]
  exact h N hN

/-- **Depth ≥ 2 for the punctured A₂ carriers** (same `prodPrimes` as A₁, any inner
prime `p`). -/
theorem two_le_maxDepth_goldA2 : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ a p : ℕ,
    2 ≤ maxDepth (goldA2SieveW opQ a N (goldOpP N) p
      (goldOpP_squarefree N) (goldOpP_odd N)) := by
  obtain ⟨x₁, h⟩ := gold_punctured_card_ge_two
  refine ⟨x₁, fun N hN a p => ?_⟩
  unfold maxDepth
  rw [goldA2SieveW_prodPrimes, goldOpP, goldPs_primeFactors]
  exact h N hN

/-- **Depth ≥ 1 for the punctured switch carrier** — the `opZ`-window count pushed into
the wider `opY` window through the tower row `opZ N ≤ opY N`. -/
theorem one_le_maxDepth_goldSwitch : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    1 ≤ maxDepth (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
      (goldOpPs_squarefree N) (goldOpPs_odd N)) := by
  obtain ⟨x₁, h⟩ := gold_punctured_card_ge_two
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max x₁ xt, fun N hN => ?_⟩
  obtain ⟨-, -, -, -, -, -, hzy, -, -, -, -, -, -, -, -, -, -⟩ := htower N (by omega)
  unfold maxDepth
  rw [goldSwitchSieve_prodPrimes, goldOpPs, goldPs_primeFactors]
  have hsub : ((Finset.Ico opW' (opZ N)).filter (fun q => q.Prime ∧ ¬ q ∣ N))
      ⊆ (Finset.Ico opW' (opY N)).filter (fun q => q.Prime ∧ ¬ q ∣ N) :=
    Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl hzy)
  have h2 := le_trans (h N (by omega)) (Finset.card_le_card hsub)
  omega

/-! ## §1 — the `W`-comparison and the crumbs transfer -/

/-- **The `W`-comparison.**  The Goldbach density product dominates the twin's: the
punctured prime-factor set is a subset of the full window, and every discarded factor
`1 − ν(p)` lies in `[0, 1]`. -/
theorem gold_W_ge_twin (N a : ℕ) :
    Salt.BrunLower.W (twinA1SieveW opQ opA N (opP N) (opf_P_sq N) (opf_Podd N))
      ≤ Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
          (goldOpP_squarefree N) (goldOpP_odd N)) := by
  unfold Salt.BrunLower.W
  rw [twinA1SieveW_prodPrimes, twinA1SieveW_nu, goldA1SieveW_prodPrimes, goldA1SieveW_nu]
  have hsub : (goldOpP N).primeFactors ⊆ (opP N).primeFactors := by
    rw [goldOpP, goldPs_primeFactors, opf_P_primeFactors]
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.1⟩
  rw [← Finset.prod_sdiff hsub]
  have hnn : ∀ q : ℕ, 0 ≤ 1 - nuChen q := fun q => by
    have := nuChen_le_one q; linarith
  have hle1 : ∀ q ∈ (opP N).primeFactors \ (goldOpP N).primeFactors,
      1 - nuChen q ≤ 1 := fun q _ => by
    have h0 : 0 ≤ nuChen q := by rw [nuChen_eq_inv_totient]; positivity
    linarith
  calc (∏ q ∈ (opP N).primeFactors \ (goldOpP N).primeFactors, (1 - nuChen q))
        * ∏ q ∈ (goldOpP N).primeFactors, (1 - nuChen q)
      ≤ 1 * ∏ q ∈ (goldOpP N).primeFactors, (1 - nuChen q) :=
        mul_le_mul_of_nonneg_right
          (Finset.prod_le_one (fun q _ => hnn q) hle1)
          (Finset.prod_nonneg fun q _ => hnn q)
    _ = ∏ q ∈ (goldOpP N).primeFactors, (1 - nuChen q) := one_mul _

/-- **The crumbs transfer.**  The four twin ledger crumbs (`crumbs_le`) re-priced at the
Goldbach `X_W`: `totalMass` is IDENTICAL on both sides (`= (ΣΛ)/φ(opQ)` — the
singular-series cancellation), and `W` only grows under puncturing, so every crumb
share can only shrink. -/
theorem gold_crumbs_le : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ a : ℕ,
    0 < (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
            (goldOpP_odd N)).totalMass
          * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
              (goldOpP_squarefree N) (goldOpP_odd N))
    ∧ ((N : ℝ) / (Real.log N) ^ 10 + Real.sqrt N * (Nat.log 2 N : ℝ) * Real.log N)
          / ((goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
                (goldOpP_odd N)).totalMass
            * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
                (goldOpP_squarefree N) (goldOpP_odd N)))
        ≤ 2 / 100000
    ∧ (N : ℝ) / (Real.log N) ^ 10
          / ((goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
                (goldOpP_odd N)).totalMass
            * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
                (goldOpP_squarefree N) (goldOpP_odd N)))
        ≤ 1 / 100000
    ∧ Real.log N * ((N : ℝ) / (Real.log N) ^ 10)
          / ((goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
                (goldOpP_odd N)).totalMass
            * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
                (goldOpP_squarefree N) (goldOpP_odd N)))
        ≤ 1 / 100000
    ∧ Real.log N * (N : ℝ) / ((opZ N : ℝ) - 1)
          / ((goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
                (goldOpP_odd N)).totalMass
            * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
                (goldOpP_squarefree N) (goldOpP_odd N)))
        ≤ 1 / 100000 := by
  obtain ⟨xr, hr⟩ := crumbs_le
  refine ⟨max xr (10 ^ 48), fun N hN a => ?_⟩
  have hxr : xr ≤ N := le_trans (le_max_left _ _) hN
  have hx48 : (10 : ℕ) ^ 48 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hXWt, hc1, hc2, hc3, hc4⟩ := hr N hxr
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hx48
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith [hx48R]
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  -- `opZ N ≥ 10^6`, so the razor crumb's denominator is positive
  have hz6 : (10 : ℕ) ^ 6 ≤ opZ N := by
    rw [opZ]
    refine Nat.le_floor ?_
    have hxR : ((10 : ℝ) ^ 6) ^ (8 : ℕ) ≤ (N : ℝ) := by norm_num; linarith [hx48R]
    have key : (((10 : ℝ) ^ 6) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) = (10 : ℝ) ^ 6 := by
      rw [← Real.rpow_natCast ((10 : ℝ) ^ 6) 8, ← Real.rpow_mul (by positivity)]
      norm_num
    have hmono := Real.rpow_le_rpow (by positivity) hxR (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [key] at hmono
    exact_mod_cast hmono
  have hz6R : (10 : ℝ) ^ 6 ≤ ((opZ N : ℕ) : ℝ) := by exact_mod_cast hz6
  -- `X_W` only grows from twin to gold: same `totalMass`, larger `W`
  have htm : (twinA1SieveW opQ opA N (opP N) (opf_P_sq N) (opf_Podd N)).totalMass
      = (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
          (goldOpP_odd N)).totalMass := by
    rw [twinA1SieveW_totalMass, goldA1SieveW_totalMass]
  have hWt_pos : 0 < Salt.BrunLower.W (twinA1SieveW opQ opA N (opP N)
      (opf_P_sq N) (opf_Podd N)) := Salt.BrunLower.W_pos _
  have htm_pos : 0 < (twinA1SieveW opQ opA N (opP N) (opf_P_sq N)
      (opf_Podd N)).totalMass := by
    rcases mul_pos_iff.mp hXWt with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · linarith
  have hXW_le : (twinA1SieveW opQ opA N (opP N) (opf_P_sq N) (opf_Podd N)).totalMass
        * Salt.BrunLower.W (twinA1SieveW opQ opA N (opP N) (opf_P_sq N) (opf_Podd N))
      ≤ (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
            (goldOpP_odd N)).totalMass
        * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
            (goldOpP_squarefree N) (goldOpP_odd N)) := by
    rw [← htm]
    exact mul_le_mul_of_nonneg_left (gold_W_ge_twin N a) htm_pos.le
  have hXWg : 0 < (goldA1SieveW opQ a N (goldOpP N) (goldOpP_squarefree N)
        (goldOpP_odd N)).totalMass
      * Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
          (goldOpP_squarefree N) (goldOpP_odd N)) := lt_of_lt_of_le hXWt hXW_le
  -- the four crumb numerators are nonnegative
  have hcrumb1 : (0 : ℝ) ≤ (N : ℝ) / (Real.log N) ^ 10
      + Real.sqrt N * (Nat.log 2 N : ℝ) * Real.log N :=
    add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) hlogN0)
  have hcrumb2 : (0 : ℝ) ≤ (N : ℝ) / (Real.log N) ^ 10 := by positivity
  have hcrumb3 : (0 : ℝ) ≤ Real.log N * ((N : ℝ) / (Real.log N) ^ 10) :=
    mul_nonneg hlogN0 hcrumb2
  have hcrumb4 : (0 : ℝ) ≤ Real.log N * (N : ℝ) / ((opZ N : ℝ) - 1) :=
    div_nonneg (mul_nonneg hlogN0 (Nat.cast_nonneg _)) (by linarith [hz6R])
  exact ⟨hXWg,
    le_trans (div_le_div_of_nonneg_left hcrumb1 hXWt hXW_le) hc1,
    le_trans (div_le_div_of_nonneg_left hcrumb2 hXWt hXW_le) hc2,
    le_trans (div_le_div_of_nonneg_left hcrumb3 hXWt hXW_le) hc3,
    le_trans (div_le_div_of_nonneg_left hcrumb4 hXWt hXW_le) hc4⟩

/-! ## §2 — the punctured `W`-ratio -/

/-- **The switch-factor identity** (`W_switch_factor` mirror at the punctured windows).
The switch density product factors through the A₁ product times the top-window
(punctured) product. -/
theorem gold_W_switch_factor (N a : ℕ) (hzy : opZ N ≤ opY N) :
    Salt.BrunLower.W (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
        (goldOpPs_squarefree N) (goldOpPs_odd N))
      = Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
          (goldOpP_squarefree N) (goldOpP_odd N))
        * ∏ q ∈ (goldOpPs N).primeFactors \ (goldOpP N).primeFactors,
            (1 - nuChen q) := by
  unfold Salt.BrunLower.W
  rw [goldSwitchSieve_prodPrimes, goldSwitchSieve_nu, goldA1SieveW_prodPrimes,
    goldA1SieveW_nu]
  have hsub : (goldOpP N).primeFactors ⊆ (goldOpPs N).primeFactors := by
    rw [goldOpP, goldOpPs, goldPs_primeFactors, goldPs_primeFactors]
    exact Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl hzy)
  rw [← Finset.prod_sdiff hsub]
  ring

/-- **The top-window diff identity.**  The switch/A₁ prime-factor difference is exactly
the PUNCTURED top window — `window_prod_upper_punctured_folded`'s carrier (the G-DENS
gate correction made structural). -/
theorem gold_diff_eq (N : ℕ) (hw'z : opW' ≤ opZ N) :
    (goldOpPs N).primeFactors \ (goldOpP N).primeFactors
      = (primesInWindow ((opZ N : ℕ) : ℝ) ((opY N : ℕ) : ℝ)).filter
          (fun q => ¬ q ∣ N) := by
  rw [goldOpP, goldOpPs, goldPs_primeFactors, goldPs_primeFactors]
  ext q
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ico, primesInWindow,
    Finset.mem_range, Nat.ceil_natCast]
  constructor
  · rintro ⟨⟨⟨hwq, hqy⟩, hqp, hqnd⟩, hnot⟩
    have hzq : opZ N ≤ q := by
      by_contra hlt
      exact hnot ⟨⟨hwq, by omega⟩, hqp, hqnd⟩
    exact ⟨⟨hqy, hqp, by exact_mod_cast hzq⟩, hqnd⟩
  · rintro ⟨⟨hqy, hqp, hzq⟩, hqnd⟩
    have hzq' : opZ N ≤ q := by exact_mod_cast hzq
    refine ⟨⟨⟨le_trans hw'z hzq', hqy⟩, hqp, hqnd⟩, ?_⟩
    rintro ⟨⟨-, hqz⟩, -, -⟩
    omega

/-- **`hWy` at the punctured op** — the switch `W` is at most the A₁ `W` times the
gold `W`-ratio `ρ = (log z/log y)(1 + 38/log z)(1 + 16/(z−2))`, the third factor being
the puncturing residual. -/
theorem gold_hWy_at_op : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ a : ℕ,
    Salt.BrunLower.W (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
        (goldOpPs_squarefree N) (goldOpPs_odd N))
      ≤ Salt.BrunLower.W (goldA1SieveW opQ a N (goldOpP N)
          (goldOpP_squarefree N) (goldOpP_odd N))
        * (Real.log (opZ N) / Real.log (opY N) * (1 + 38 / Real.log (opZ N))
            * (1 + 16 / ((opZ N : ℝ) - 2))) := by
  obtain ⟨x9, h9⟩ := gold_op_Zpow9
  obtain ⟨xt, -, htower⟩ := opf_tower
  obtain ⟨xL, hLg⟩ := a12_log_ge 400
  refine ⟨max (max x9 xt) (max xL (10 ^ 48)), fun N hN a => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hx9, hxt⟩, hxL, hx48⟩ := hN
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hx48
  have hN0 : N ≠ 0 := by omega
  obtain ⟨-, -, hw'z, hz3, -, -, hzy, -, -, -, -, -, -, -, -, -, -⟩ := htower N hxt
  have hlogN : (400 : ℝ) ≤ Real.log N := (hLg N hxL).2
  -- the folded-keystone side conditions
  have hz3R : (3 : ℝ) ≤ ((opZ N : ℕ) : ℝ) := by exact_mod_cast hz3
  have hzyR : ((opZ N : ℕ) : ℝ) ≤ ((opY N : ℕ) : ℝ) := by exact_mod_cast hzy
  have hz38 : (38 : ℝ) ≤ Real.log ((opZ N : ℕ) : ℝ) := by
    obtain ⟨-, -, -, h⟩ := opf_window_floor_bounds N hx48R (γ := (1 : ℝ) / 8)
      (by norm_num)
    rw [opZ]
    linarith
  have hz18 : (18 : ℝ) ≤ ((opZ N : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) < ((opZ N : ℕ) : ℝ) := by linarith
    have h2 : Real.exp 38 ≤ ((opZ N : ℕ) : ℝ) := by
      have := Real.exp_le_exp.mpr hz38
      rwa [Real.exp_log (by linarith : (0 : ℝ) < ((opZ N : ℕ) : ℝ))] at this
    have h3 : (18 : ℝ) ≤ Real.exp 38 := by
      have := Real.add_one_le_exp (38 : ℝ)
      linarith
    linarith
  have hcard : ((primesInWindow ((opZ N : ℕ) : ℝ) ((opY N : ℕ) : ℝ)).filter
      (fun q => q ∣ N)).card ≤ 8 :=
    card_primesInWindow_dvd_le hz3R hN0 (h9 N hx9)
  rw [gold_W_switch_factor N a hzy, gold_diff_eq N hw'z]
  exact mul_le_mul_of_nonneg_left
    (window_prod_upper_punctured_folded hz18 hzyR hz38 hcard)
    (Salt.BrunLower.W_pos _).le

/-- **`gold_rho_le`** — the gold `W`-ratio is nonneg and `≤ 3/8 + 1/100000`: the twin
budget survives the puncturing residual `1 + 16/(z−2)` because at `log N ≥ 10⁹` the
base ratio is within `10⁻⁶` of `3/8` and `z ≥ e⁴⁹ > 2·10⁶` makes the residual `< 10⁻⁵`
multiplicatively. -/
theorem gold_rho_le : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    0 ≤ Real.log (opZ N) / Real.log (opY N) * (1 + 38 / Real.log (opZ N))
        * (1 + 16 / ((opZ N : ℝ) - 2))
    ∧ Real.log (opZ N) / Real.log (opY N) * (1 + 38 / Real.log (opZ N))
        * (1 + 16 / ((opZ N : ℝ) - 2)) ≤ 3 / 8 + 1 / 100000 := by
  obtain ⟨xL, hLg⟩ := a12_log_ge 1000000000
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max (max xL xt) (10 ^ 48), fun N hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨hxL, hxt⟩, hx48⟩ := hN
  have hx48R : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hx48
  have hlogx : (1000000000 : ℝ) ≤ Real.log N := (hLg N hxL).2
  obtain ⟨-, -, -, hz3, -, -, hzy, -, -, -, -, -, -, -, -, -, -⟩ := htower N hxt
  have hzR1 : (1 : ℝ) < (opZ N : ℝ) := by exact_mod_cast (by omega : 1 < opZ N)
  have hyR1 : (1 : ℝ) < (opY N : ℝ) := by exact_mod_cast (by omega : 1 < opY N)
  have hlogzpos : 0 < Real.log (opZ N) := Real.log_pos hzR1
  have hlogypos : 0 < Real.log (opY N) := Real.log_pos hyR1
  have hza_le : Real.log (opZ N) ≤ (1 / 8) * Real.log N := by
    obtain ⟨-, -, h, -⟩ := opf_window_floor_bounds N hx48R (γ := (1 : ℝ) / 8)
      (by norm_num)
    rw [opZ]
    linarith
  have hza_ge : (1 / 8) * Real.log N - 1 / 999999 ≤ Real.log (opZ N) := by
    obtain ⟨-, -, -, h⟩ := opf_window_floor_bounds N hx48R (γ := (1 : ℝ) / 8)
      (by norm_num)
    rw [opZ]
    linarith
  have hya_ge : (1 / 3) * Real.log N - 1 / 999999 ≤ Real.log (opY N) := by
    obtain ⟨-, -, -, h⟩ := opf_window_floor_bounds N hx48R (γ := (1 : ℝ) / 3)
      (by norm_num)
    rw [opY]
    linarith
  -- `z ≥ e⁴⁹ ≥ 8⁷ = 2097152`, so the puncturing residual is `≤ 16/2097150`
  have hlogz49 : (49 : ℝ) ≤ Real.log (opZ N) := by linarith
  have hexp7 : (8 : ℝ) ≤ Real.exp 7 := by
    have := Real.add_one_le_exp (7 : ℝ)
    linarith
  have hexp49 : (2097152 : ℝ) ≤ Real.exp 49 := by
    have h : Real.exp (((7 : ℕ) : ℝ) * (7 : ℝ)) = Real.exp 7 ^ (7 : ℕ) :=
      Real.exp_nat_mul 7 7
    have h49 : ((7 : ℕ) : ℝ) * (7 : ℝ) = 49 := by norm_num
    rw [h49] at h
    rw [h]
    calc (2097152 : ℝ) = 8 ^ (7 : ℕ) := by norm_num
      _ ≤ Real.exp 7 ^ (7 : ℕ) := pow_le_pow_left₀ (by norm_num) hexp7 7
  have hzbig : (2097152 : ℝ) ≤ (opZ N : ℝ) := by
    have h1 : Real.exp 49 ≤ Real.exp (Real.log (opZ N)) := Real.exp_le_exp.mpr hlogz49
    rw [Real.exp_log (by linarith : (0 : ℝ) < (opZ N : ℝ))] at h1
    exact le_trans hexp49 h1
  have hterm : 16 / ((opZ N : ℝ) - 2) ≤ 16 / 2097150 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have htermnn : (0 : ℝ) ≤ 16 / ((opZ N : ℝ) - 2) :=
    div_nonneg (by norm_num) (by linarith)
  have h38nn : (0 : ℝ) ≤ 38 / Real.log (opZ N) := div_nonneg (by norm_num) hlogzpos.le
  have hbase_nn : 0 ≤ Real.log (opZ N) / Real.log (opY N)
      * (1 + 38 / Real.log (opZ N)) :=
    mul_nonneg (div_nonneg hlogzpos.le hlogypos.le) (by linarith)
  refine ⟨mul_nonneg hbase_nn (by linarith), ?_⟩
  have hrho_eq : Real.log (opZ N) / Real.log (opY N) * (1 + 38 / Real.log (opZ N))
      = (Real.log (opZ N) + 38) / Real.log (opY N) := by
    field_simp
  have hbase : Real.log (opZ N) / Real.log (opY N) * (1 + 38 / Real.log (opZ N))
      ≤ 3 / 8 + 1 / 1000000 := by
    rw [hrho_eq, div_le_iff₀ hlogypos]
    nlinarith [hza_le, hya_ge, hlogx]
  calc Real.log (opZ N) / Real.log (opY N) * (1 + 38 / Real.log (opZ N))
        * (1 + 16 / ((opZ N : ℝ) - 2))
      ≤ (3 / 8 + 1 / 1000000) * (1 + 16 / 2097150) :=
        mul_le_mul hbase (by linarith) (by linarith) (by norm_num)
    _ ≤ 3 / 8 + 1 / 100000 := by norm_num

end Salt.Goldbach
