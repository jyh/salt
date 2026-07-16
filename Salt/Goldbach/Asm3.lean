/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Asm2
import Salt.Goldbach.Op2
import Salt.Chen.AggDiag

/-!
# G-ASM §3 — the op-arithmetic rows, discharged (`gold_hBVblocksW_at_op_closed`)

The named per-`N` hypotheses of `gold_hBVblocksW_final` (§2), each proved at the
operating point:

* the ν-side `Σ_{d ∣ goldOpPs N} ν(d) ≤ log N` (the `nu_sum_le_log_at_op` mirror at the
  punctured modulus — `nuChen_sum_divisors_le` with the `goldOpPs` window facts);
* the diagonal price row (r9) via the carrier-free `crumb_le_rpow_at_op` +
  `opPdiag_compat`;
* the conversion-error price row (r10) via `gold_hcount_seam` (the count seam), the
  crude `Λ ≤ log` window mass, and the `N^{7/8}·polylog ≪ N/L^{11}` fold;
* the D-floor/scale rows (r1–r6), the log count (r7), and the boundary cap `hiX` (r8).

Thresholds built from obtained constants are exposed as a single real (the x₀(K)
pattern); `gold_hBVblocksW_at_op_closed` composes everything, leaving only the residue
witness and the threshold row.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset Salt.Chen ArithmeticFunction

namespace Salt.Goldbach

/-! ## §A — the ν-side at the punctured modulus -/

/-- `Σ_{d ∣ goldOpPs N} ν(d) ≤ log N` — the `nu_sum_le_log_at_op` mirror. -/
theorem gold_nu_sum_le_log : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∑ d ∈ Nat.divisors (goldOpPs N), nuChen d ≤ Real.log N := by
  obtain ⟨xt, _hxt8, htower⟩ := opf_tower
  refine ⟨max xt (10 ^ 48), fun N hN => ?_⟩
  have hxt : xt ≤ N := le_trans (le_max_left _ _) hN
  have h10n : (10 ^ 48 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hxR : (10 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast h10n
  have h1x : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hxR
  have hLnn : (0 : ℝ) ≤ Real.log N := Real.log_nonneg h1x.le
  obtain ⟨-, hrow2, -, -, -, -, hrow7, -, -, -, -, -, -, -, -, -, -⟩ := htower N hxt
  have huy : w0R opEps ≤ (opY N : ℝ) := le_trans hrow2 (by exact_mod_cast hrow7)
  have hraw := nuChen_sum_divisors_le N (opZ N) (opY N) (goldOpPs N)
    (goldOpPs_squarefree N) (goldOpPs_odd N) opf_eps_pos.le opf_w0R3 huy
    (w0R_threshold opf_eps_pos) (goldOpPs_plow N)
    (fun p hp => by exact_mod_cast goldOpPs_py N p hp)
  -- the carrier-free log reduction (the `nu_sum_le_log_at_op` tail, transcribed)
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    have h := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have hexp2 : Real.exp 2 ≤ 10 := by nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have := Real.log_le_log (Real.exp_pos 2) hexp2
    rwa [Real.log_exp] at this
  have hlogw2 : (2 : ℝ) ≤ Real.log (w0R opEps) := by
    have h1 : Real.log ((10 : ℝ) ^ 6) ≤ Real.log (w0R opEps) :=
      Real.log_le_log (by norm_num) opf_w0R_big
    have h2 : Real.log ((10 : ℝ) ^ 6) = 6 * Real.log 10 := by
      rw [Real.log_pow]; push_cast; ring
    rw [h2] at h1; linarith [hlog10]
  have hbpos : (0 : ℝ) < Real.log (w0R opEps) := by linarith [hlogw2]
  have hy_le : Real.log (opY N : ℝ) ≤ (1 : ℝ) / 3 * Real.log N := by
    rw [opY]
    exact (opf_window_floor_bounds N hxR (γ := (1 : ℝ) / 3) (by norm_num)).2.2.1
  have hlogoy_nn : (0 : ℝ) ≤ Real.log (opY N : ℝ) := by
    rw [opY]
    exact Real.log_nonneg
      (le_trans (by norm_num)
        (opf_window_floor_bounds N hxR (γ := (1 : ℝ) / 3) (by norm_num)).2.1)
  have h1e2 : (1 : ℝ) + opEps ≤ 2 := by norm_num [opEps]
  refine le_trans hraw ?_
  rw [div_le_iff₀ hbpos]
  have hstep1 : (1 + opEps) * Real.log (opY N : ℝ) ≤ 2 * Real.log (opY N : ℝ) :=
    mul_le_mul_of_nonneg_right h1e2 hlogoy_nn
  have hnum : (1 + opEps) * Real.log (opY N : ℝ) ≤ (2 : ℝ) / 3 * Real.log N := by
    linarith [hstep1, hy_le]
  have hprod : (0 : ℝ) ≤ Real.log N * (Real.log (w0R opEps) - 2 / 3) :=
    mul_nonneg hLnn (by linarith [hlogw2])
  nlinarith [hnum, hprod]

/-! ## §B — the diagonal price row (r9) -/

/-- r9: the honest diagonal row fits `N/(log N)^{11}` at op. -/
theorem gold_hPdiag_row : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    (opY N : ℝ) * (Nat.sqrt N : ℝ)
        * ((2 : ℝ) ^ Nat.log opW' N + ∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
      ≤ (N : ℝ) / (Real.log N) ^ 11 := by
  obtain ⟨xν, hν⟩ := gold_nu_sum_le_log
  obtain ⟨xc, hc⟩ := opPdiag_compat
  refine ⟨max (max xν xc) 1, fun N hN => ?_⟩
  have hxν : xν ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hxc : xc ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hcrumb := crumb_le_rpow_at_op N h1
  have hsum : (2 : ℝ) ^ Nat.log opW' N + ∑ d ∈ Nat.divisors (goldOpPs N), nuChen d
      ≤ (N : ℝ) ^ ((1 : ℝ) / 7) + Real.log N := add_le_add hcrumb (hν N hxν)
  have hnn : (0 : ℝ) ≤ (opY N : ℝ) * (Nat.sqrt N : ℝ) := by positivity
  have hrow : (opY N : ℝ) * (Nat.sqrt N : ℝ)
      * ((2 : ℝ) ^ Nat.log opW' N + ∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
      ≤ opPdiag N := by
    unfold opPdiag
    exact mul_le_mul_of_nonneg_left hsum hnn
  exact le_trans hrow (hc N hxc)

/-! ## §C — the conversion-error price row (r10) -/

/-- r10: the `hCE` budget row at op, with the exposed threshold real. -/
theorem gold_hRCE_row : ∃ (R : ℝ) (x₁ : ℕ), 0 ≤ R ∧ ∀ N : ℕ, x₁ ≤ N →
    R ≤ Real.log N →
    nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
        * goldTripleSum N (opZ N) (opY N) / ((opZ N : ℝ) - 1)
      ≤ (N : ℝ) / (Real.log N) ^ 11 := by
  obtain ⟨Cs, xs, hCs0, hseam⟩ := gold_hcount_seam
  obtain ⟨xν, hν⟩ := gold_nu_sum_le_log
  obtain ⟨xsc, hsc⟩ := gold_op_scales
  obtain ⟨xk, hk⟩ := a12_logpow_le_rpow ((13 : ℕ) : ℝ) (1 / 16) (by positivity) (by norm_num)
  refine ⟨8 * (Cs + Real.log 2) + 4, max (max xs xν) (max xsc xk), ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  intro N hN hR
  have hxs : xs ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hxν : xν ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hxsc : xsc ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hxk : xk ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hN2, hz1, _, hlogz_le, hlogz_ge, _, hlog2e9, hzle, hzge, _, _, _, _⟩ := hsc N hxsc
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLpos : (0 : ℝ) < Real.log N := by linarith
  -- the crude window mass: Σ Λ ≤ N·log N
  have hmass : (∑ n ∈ twinWindow N, vonMangoldt n) ≤ (N : ℝ) * Real.log N := by
    have hcard : (twinWindow N).card ≤ N := by
      unfold twinWindow
      rw [Nat.card_Icc]
      omega
    have hterm : ∀ n ∈ twinWindow N, vonMangoldt n ≤ Real.log N := by
      intro n hn
      have hnN : n ≤ N := by
        have := (Finset.mem_Icc.mp hn).2
        omega
      refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
      · have h1n : 1 ≤ n := by
          have := (Finset.mem_Icc.mp hn).1
          rcases Nat.eq_zero_or_pos n with h0 | h1
          · subst h0
            simp only [Nat.le_zero] at this
            omega
          · exact h1
        exact_mod_cast h1n
      · exact_mod_cast hnN
    calc (∑ n ∈ twinWindow N, vonMangoldt n)
        ≤ ∑ _n ∈ twinWindow N, Real.log N := Finset.sum_le_sum hterm
      _ = (twinWindow N).card * Real.log N := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * Real.log N := by
          refine mul_le_mul_of_nonneg_right ?_ hLpos.le
          exact_mod_cast hcard
  -- the seam → TS ≤ (cbar + ec)·N ≤ 2N  (ec ≤ 1 at the exposed threshold; cbar < 1/2)
  have hphi : (0 : ℝ) < (opQ.totient : ℝ) := by
    have h2 : 2 ≤ opQ := opf_Q2
    have := Nat.totient_pos.mpr (by omega : 0 < opQ)
    exact_mod_cast this
  have hseamN := hseam N hxs
  have hTS0 : (0 : ℝ) ≤ goldTripleSum N (opZ N) (opY N) := by
    rw [goldTripleSum_eq_card]; positivity
  have hec : ecountOp Cs N ≤ 1 := by
    unfold ecountOp
    rw [div_le_one (by linarith : (0 : ℝ) < Real.log (opZ N))]
    linarith [hlogz_ge]
  have hcb : cbar ≤ 1 / 2 := le_of_lt (lt_of_lt_of_le cbar_lt (by norm_num))
  have hTSN : goldTripleSum N (opZ N) (opY N) * Real.log N
      ≤ (3 / 2 : ℝ) * ((N : ℝ) * Real.log N) := by
    have h1 : Real.log N * (goldTripleSum N (opZ N) (opY N) / (opQ.totient : ℝ))
        ≤ (cbar + ecountOp Cs N)
            * ((∑ n ∈ twinWindow N, vonMangoldt n) / (opQ.totient : ℝ)) := hseamN
    have h2 : Real.log N * goldTripleSum N (opZ N) (opY N)
        ≤ (cbar + ecountOp Cs N) * (∑ n ∈ twinWindow N, vonMangoldt n) := by
      have hφne : (opQ.totient : ℝ) ≠ 0 := ne_of_gt hphi
      have hmul := mul_le_mul_of_nonneg_right h1 hphi.le
      rw [mul_assoc, div_mul_cancel₀ _ hφne, mul_assoc, div_mul_cancel₀ _ hφne] at hmul
      exact hmul
    have hmass0 : (0 : ℝ) ≤ (∑ n ∈ twinWindow N, vonMangoldt n) :=
      Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
    have h3 : (cbar + ecountOp Cs N) * (∑ n ∈ twinWindow N, vonMangoldt n)
        ≤ (3 / 2 : ℝ) * ((N : ℝ) * Real.log N) := by
      have hcoef : cbar + ecountOp Cs N ≤ 3 / 2 := by linarith [hec, hcb]
      have := mul_le_mul hcoef hmass (by positivity) (by norm_num)
      linarith [this]
    linarith [h2, h3, mul_comm (Real.log N) (goldTripleSum N (opZ N) (opY N))]
  have hTS : goldTripleSum N (opZ N) (opY N) ≤ (3 / 2 : ℝ) * (N : ℝ) := by
    calc goldTripleSum N (opZ N) (opY N)
        = goldTripleSum N (opZ N) (opY N) * Real.log N / Real.log N := by
          field_simp
      _ ≤ (3 / 2 : ℝ) * ((N : ℝ) * Real.log N) / Real.log N := by
          exact div_le_div_of_nonneg_right hTSN hLpos.le
      _ = (3 / 2 : ℝ) * (N : ℝ) := by field_simp
  -- the fold: LHS ≤ log N · (3/2·N) / (z−1) ≤ 6·N^{7/8}·log N ≤ N/L^{11}
  have hν' := hν N hxν
  have hν0 : (0 : ℝ) ≤ ∑ d ∈ Nat.divisors (goldOpPs N), nuChen d :=
    Finset.sum_nonneg (fun d _ => by rw [nuChen_apply]; positivity)
  have hnuQ : nuChen opQ ≤ 1 := nuChen_le_one opQ
  have hnuQ0 : (0 : ℝ) ≤ nuChen opQ := by rw [nuChen_apply]; positivity
  have h4 : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    have hexp : Real.exp 2 ≤ Real.exp (Real.log N * (1 / 8)) := by
      refine Real.exp_le_exp.mpr ?_
      linarith [hlog2e9]
    have hrw : (N : ℝ) ^ ((1 : ℝ) / 8) = Real.exp (Real.log N * (1 / 8)) := by
      rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (N : ℝ))]
    have he2 : (4 : ℝ) ≤ Real.exp 2 := by
      have hmul : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_gt_d9]
    rw [hrw]; linarith
  have hz2 : (N : ℝ) ^ ((1 : ℝ) / 8) / 4 ≤ (opZ N : ℝ) - 1 := by linarith [hzge, h4]
  have hz1p : (0 : ℝ) < (opZ N : ℝ) - 1 := by linarith [hz2, h4]
  have hnum : nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
      * goldTripleSum N (opZ N) (opY N)
      ≤ Real.log N * ((3 / 2 : ℝ) * (N : ℝ)) := by
    have h1 : nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d) ≤ Real.log N := by
      calc nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
          ≤ 1 * Real.log N := mul_le_mul hnuQ hν' hν0 (by norm_num)
        _ = Real.log N := one_mul _
    exact mul_le_mul h1 hTS hTS0 hLpos.le
  have hLHS : nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
      * goldTripleSum N (opZ N) (opY N) / ((opZ N : ℝ) - 1)
      ≤ Real.log N * ((3 / 2 : ℝ) * (N : ℝ)) / ((N : ℝ) ^ ((1 : ℝ) / 8) / 4) := by
    calc nuChen opQ * (∑ d ∈ Nat.divisors (goldOpPs N), nuChen d)
        * goldTripleSum N (opZ N) (opY N) / ((opZ N : ℝ) - 1)
        ≤ Real.log N * ((3 / 2 : ℝ) * (N : ℝ)) / ((opZ N : ℝ) - 1) :=
          div_le_div_of_nonneg_right hnum hz1p.le
      _ ≤ Real.log N * ((3 / 2 : ℝ) * (N : ℝ)) / ((N : ℝ) ^ ((1 : ℝ) / 8) / 4) := by
          refine div_le_div_of_nonneg_left ?_ (by positivity) hz2
          exact mul_nonneg hLpos.le (by positivity)
  -- 6·N·logN/N^{1/8} ≤ N/L^{11} needs 6·L^{12} ≤ N^{1/8}: square L^{13} ≤ N^{1/16}
  have hkey := hk N hxk
  have hL13 : (Real.log N) ^ (13 : ℕ) ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := by
    have := hkey
    rwa [Real.rpow_natCast] at this
  have hfold : Real.log N * ((3 / 2 : ℝ) * (N : ℝ)) / ((N : ℝ) ^ ((1 : ℝ) / 8) / 4)
      ≤ (N : ℝ) / (Real.log N) ^ 11 := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := by omega
      exact_mod_cast this
    have h18pos : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- goal: logN·(3/2·N)·L^{11} ≤ N·(N^{1/8}/4)
    have hsq : (Real.log N) ^ (13 : ℕ) * (Real.log N) ^ (13 : ℕ)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 16) :=
      mul_le_mul hL13 hL13 (by positivity) (by positivity)
    have hcomb : (Real.log N) ^ (26 : ℕ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
      have h1 : (Real.log N) ^ (13 : ℕ) * (Real.log N) ^ (13 : ℕ)
          = (Real.log N) ^ (26 : ℕ) := by ring
      have h2 : (N : ℝ) ^ ((1 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 16)
          = (N : ℝ) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_add hNpos]; norm_num
      rw [h1, h2] at hsq
      exact hsq
    have h6L : 6 * (Real.log N) ^ (12 : ℕ) ≤ (Real.log N) ^ (26 : ℕ) := by
      have hpow : (Real.log N) ^ (12 : ℕ) * (Real.log N) ^ (14 : ℕ)
          = (Real.log N) ^ (26 : ℕ) := by ring
      have h6 : (6 : ℝ) ≤ (Real.log N) ^ (14 : ℕ) := by
        calc (6 : ℝ) ≤ 2 ^ 14 := by norm_num
          _ ≤ (Real.log N) ^ (14 : ℕ) := by
              refine pow_le_pow_left₀ (by norm_num) ?_ _
              linarith [hlog2e9]
      calc 6 * (Real.log N) ^ (12 : ℕ)
          ≤ (Real.log N) ^ (14 : ℕ) * (Real.log N) ^ (12 : ℕ) := by
            refine mul_le_mul_of_nonneg_right h6 (by positivity)
        _ = (Real.log N) ^ (26 : ℕ) := by ring
    have e4 : 6 * (Real.log N) ^ (12 : ℕ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := le_trans h6L hcomb
    have e5 : (N : ℝ) * (6 * (Real.log N) ^ (12 : ℕ))
        ≤ (N : ℝ) * ((N : ℝ) ^ ((1 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left e4 hNpos.le
    linarith [e5]
  exact le_trans hLHS hfold

/-! ## §D — the D-floor/scale rows (r1–r8) -/

/-- The r1–r8 bundle at op: the `opDlev` floor, the three `opD` price floors, the two
scale caps, the log count, and the boundary cap.  The exposed `R` absorbs the sole
`opQ`-dependent margin (`log(2·opQ) ≤ (291/100000)·log N`). -/
theorem gold_op_rows : ∃ (R : ℝ) (x₁ : ℕ), 0 ≤ R ∧ ∀ N : ℕ, x₁ ≤ N →
    R ≤ Real.log N →
    ((1 : ℝ) ≤ 1 * (opDlev N : ℝ)) ∧
    ((opQ : ℝ) * (1 * (opDlev N : ℝ)) ≤ ((opD N : ℕ) : ℝ)) ∧
    (∀ k, (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((opD N : ℕ) : ℝ)) ∧
    (∀ k, ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2)
      ≤ ((opD N : ℕ) : ℝ)) ∧
    (((opD N : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) ∧
    ((1 : ℝ) * (opDlev N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) ∧
    ((Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N) ∧
    (∀ k' k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
        (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) (Nat.log 2 N),
        2 ^ (i + 1) ≤ N + 1) ∧
    2 ≤ N ∧ 1 ≤ opZ N := by
  obtain ⟨xsc, hsc⟩ := gold_op_scales
  have hQ1 : 1 ≤ opQ := by have := opf_Q2; omega
  refine ⟨(100000 / 291 : ℝ) * Real.log (2 * (opQ : ℝ)), xsc, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ 2 * (opQ : ℝ) := by
      have h2 : (1 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast hQ1
      linarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg h1)
  intro N hN hR
  obtain ⟨hN2, hz1, -, -, -, -, hlog2e9, -, hzge, -, -, -, -⟩ := hsc N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h0 : 0 < N := by omega
    exact_mod_cast h0
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : 1 ≤ N := by omega
    exact_mod_cast h1
  have hl2lt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  -- the opD floor and its half-margin
  have hDfloor : (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) - 1 ≤ ((opD N : ℕ) : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000))
    unfold opD
    linarith
  have hNα : (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)
      = Real.exp (Real.log N * ((1 : ℝ) / 2 - 9 / 100000)) :=
    Real.rpow_def_of_pos hNpos _
  have h2α : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
    have he : Real.exp (Real.log 2)
        ≤ Real.exp (Real.log N * ((1 : ℝ) / 2 - 9 / 100000)) := by
      refine Real.exp_le_exp.mpr ?_
      linarith [hlog2e9, hl2lt]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
    rw [hNα]
    exact he
  have hDhalf : (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) / 2 ≤ ((opD N : ℕ) : ℝ) := by
    linarith [hDfloor, h2α]
  -- the opDlev floor bounds
  have hlev_le : (opDlev N : ℝ) ≤ (N : ℝ) ^ ((497 : ℝ) / 1000) := by
    unfold opDlev
    exact Nat.floor_le (by positivity)
  -- r1
  have hb1 : (1 : ℝ) ≤ 1 * (opDlev N : ℝ) := by
    rw [one_mul]
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ ((497 : ℝ) / 1000) := by
      calc (1 : ℝ) = (1 : ℝ) ^ ((497 : ℝ) / 1000) := (Real.one_rpow _).symm
        _ ≤ (N : ℝ) ^ ((497 : ℝ) / 1000) :=
            Real.rpow_le_rpow (by norm_num) hN1R (by norm_num)
    have h2 : 1 ≤ opDlev N := by
      unfold opDlev
      exact Nat.le_floor (by exact_mod_cast h1)
    exact_mod_cast h2
  -- r2 (the exposed margin row)
  have hDbnd : (opQ : ℝ) * (1 * (opDlev N : ℝ)) ≤ ((opD N : ℕ) : ℝ) := by
    have hstep : (opQ : ℝ) * (opDlev N : ℝ) ≤ (opQ : ℝ) * (N : ℝ) ^ ((497 : ℝ) / 1000) :=
      mul_le_mul_of_nonneg_left hlev_le (by positivity)
    have hmargin : 2 * ((opQ : ℝ) * (N : ℝ) ^ ((497 : ℝ) / 1000))
        ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
      have hlhs : 2 * ((opQ : ℝ) * (N : ℝ) ^ ((497 : ℝ) / 1000))
          = Real.exp (Real.log (2 * (opQ : ℝ)) + Real.log N * ((497 : ℝ) / 1000)) := by
        rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < 2 * (opQ : ℝ)),
          ← Real.rpow_def_of_pos hNpos]
        ring
      rw [hlhs, hNα]
      refine Real.exp_le_exp.mpr ?_
      linarith [hR]
    rw [one_mul]
    linarith [hstep, hmargin, hDhalf]
  -- the goldCut cap
  have hcutle : ∀ j, (goldCut N j : ℝ) ≤ (N : ℝ) := by
    intro j
    have h1 : goldCut N j ≤ N := by
      have h2 : goldCut N j ≤ N / 2 := by
        unfold goldCut
        exact min_le_right _ _
      exact le_trans h2 (Nat.div_le_self N 2)
    exact_mod_cast h1
  -- r3
  have hDband : ∀ k, (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) / 8
      ≤ ((opD N : ℕ) : ℝ) := by
    intro k
    have h1 : (goldCut N (k + 1) : ℝ) ^ ((11 : ℝ) / 24) ≤ (N : ℝ) ^ ((11 : ℝ) / 24) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (hcutle _) (by norm_num)
    have h2 : (N : ℝ) ^ ((11 : ℝ) / 24) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
      Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
    have hα0 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by positivity
    linarith [hDhalf, h1, h2, hα0]
  -- r4
  have hDgeB : ∀ k, ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2)
      ≤ ((opD N : ℕ) : ℝ) := by
    intro k
    have hzpos : (0 : ℝ) < (opZ N : ℝ) := by
      have h0 : 0 < opZ N := hz1
      exact_mod_cast h0
    have h8z : (0 : ℝ) < 8 * (opZ N : ℝ) := by positivity
    have hsplit : (N : ℝ) ^ ((7 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 8) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num
    have hkey : (goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))
        ≤ (N : ℝ) ^ ((7 : ℝ) / 8) / 4 := by
      rw [div_le_div_iff₀ h8z (by norm_num)]
      have h1 : (4 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 8) ≤ 8 * (opZ N : ℝ) := by
        linarith [hzge]
      have h2 : (N : ℝ) ^ ((7 : ℝ) / 8) * ((4 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 8))
          = 4 * (N : ℝ) := by
        calc (N : ℝ) ^ ((7 : ℝ) / 8) * ((4 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 8))
            = 4 * ((N : ℝ) ^ ((7 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 8)) := by ring
          _ = 4 * (N : ℝ) := by rw [hsplit]
      have h3 : (N : ℝ) ^ ((7 : ℝ) / 8) * ((4 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 8))
          ≤ (N : ℝ) ^ ((7 : ℝ) / 8) * (8 * (opZ N : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : (goldCut N (k + 1) : ℝ) ≤ (N : ℝ) := hcutle _
      linarith [h2, h3, h4]
    have hrow : ((goldCut N (k + 1) : ℝ) / (8 * (opZ N : ℝ))) ^ ((1 : ℝ) / 2)
        ≤ ((N : ℝ) ^ ((7 : ℝ) / 8) / 4) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hkey (by norm_num)
    have h4half : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [← Real.sqrt_eq_rpow]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have hsimp : ((N : ℝ) ^ ((7 : ℝ) / 8) / 4) ^ ((1 : ℝ) / 2)
        = (N : ℝ) ^ ((7 : ℝ) / 16) / 2 := by
      rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 4), h4half,
        ← Real.rpow_mul (le_of_lt hNpos)]
      norm_num
    have hend : (N : ℝ) ^ ((7 : ℝ) / 16) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
      Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
    rw [hsimp] at hrow
    linarith [hrow, hend, hDhalf]
  -- r5
  have hDsc : ((opD N : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
    unfold opD
    exact Nat.floor_le (by positivity)
  -- r6
  have hbndsc : (1 : ℝ) * (opDlev N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [one_mul]
    exact le_trans hlev_le (Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num))
  -- r7
  have hcount : (Nat.log 2 N : ℝ) + 1 ≤ 2 * Real.log N := by
    have hp : (2 : ℝ) ^ (Nat.log 2 N : ℕ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hlp : Real.log ((2 : ℝ) ^ (Nat.log 2 N : ℕ)) ≤ Real.log N :=
      Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at hlp
    have hstep : (Nat.log 2 N : ℝ) * 0.6931471803 ≤ (Nat.log 2 N : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_gt_d9) (Nat.cast_nonneg _)
    linarith [hlp, hstep, hlog2e9]
  -- r8
  have hiX : ∀ k' k, ∀ i ∈ dyadicBoundary (pieceN k') (pieceM k')
      (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) (Nat.log 2 N),
      2 ^ (i + 1) ≤ N + 1 := by
    intro k' k i hi
    have hmem := Finset.mem_filter.mp hi
    obtain ⟨h2i, -, -⟩ := hmem.2
    have hle : 2 ^ i ≤ goldCut N (k + 1) := by
      calc 2 ^ i = 2 ^ i * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ i * (pieceN k' + 1) := Nat.mul_le_mul (le_refl _) (by omega)
        _ ≤ goldCut N (k + 1) := h2i
    have hcut : goldCut N (k + 1) ≤ N / 2 := by
      unfold goldCut
      exact min_le_right _ _
    have hhalf : 2 ^ i ≤ N / 2 := le_trans hle hcut
    rw [pow_succ]
    omega
  exact ⟨hb1, hDbnd, hDband, hDgeB, hDsc, hbndsc, hcount, hiX, hN2, hz1⟩

/-! ## §E — the terminal, closed -/

/-- **`gold_hBVblocksW_at_op_closed`** — the A₃ block-BV terminal with every
op-arithmetic row discharged: only the exposed threshold row and the residue-class
witness `a` remain. -/
theorem gold_hBVblocksW_at_op_closed : ∃ (CT : ℝ) (x₁ : ℕ), 0 ≤ CT ∧
    ∀ (N : ℕ), x₁ ≤ N → CT ≤ Real.log N →
      ∀ a : ℕ, a ≤ N → Nat.Coprime opQ a → Nat.Coprime opQ (N - a) →
      (∑ j ∈ Finset.range (maxBlock N (opZ N) (N : ℝ) + 1),
          rosserRemainder
            (goldBlockSwitchSieveW N (opZ N) (opY N) (N : ℝ) j opQ a (goldOpPs N)
              (goldOpPs_squarefree N) (goldOpPs_odd N))
            (1 * (opDlev N : ℝ)))
        ≤ (N : ℝ) / (Real.log N) ^ 10 := by
  obtain ⟨CT, xF, hCT0, hfinal⟩ := gold_hBVblocksW_final
  obtain ⟨RD, xD, hRD0, hrows⟩ := gold_op_rows
  obtain ⟨xP, hPdiag⟩ := gold_hPdiag_row
  obtain ⟨RC, xC, hRC0, hRCE⟩ := gold_hRCE_row
  refine ⟨max CT (max RD RC), max (max xF xD) (max xP xC), ?_, ?_⟩
  · exact le_trans hCT0 (le_max_left _ _)
  intro N hN hthr a haN hQa hQNa
  have hxF : xF ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hxD : xD ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hxP : xP ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hxC : xC ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hCTle : CT ≤ Real.log N := le_trans (le_max_left _ _) hthr
  have hRDle : RD ≤ Real.log N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hthr
  have hRCle : RC ≤ Real.log N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hthr
  obtain ⟨hb1, hDbnd, hDband, hDgeB, hDsc, hbndsc, hcount, hiX, hN2, hz1⟩ :=
    hrows N hxD hRDle
  exact hfinal N hxF hCTle a haN hQa hQNa hb1 hDbnd hDband hDgeB hDsc hbndsc hcount hiX
    (hPdiag N hxP) (hRCE N hxC hRCle) hN2 hz1

end Salt.Goldbach
