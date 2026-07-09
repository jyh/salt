/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Final

/-!
# M7 discharge — the analytic frontier and the unconditional capstone

This file discharges the `AnalyticFrontier` hypothesis of `bounded_gaps_from_eh`,
producing the unconditional `bounded_gaps_from_eh_final : BoundedGapsFromEH`.

The work is entirely quantifier-reordering plumbing plus regime-threshold real
analysis (no new mathematics).  The heart is making the three error constants
(`Cs` of `S1_upper_A1`, `C₀` of `S2m_ge_compatMain_eh`, and the compat constant
of `s2CompatFormM_ge_sixteenth`) *uniform in `R`*: their values factor through
`rankin_bound`/`phi_ratio_le`/`eh_error_pow`, all of which are `R`-free, so we
restate each producer with its constant quantified *before* `R`.
-/

open Finset

namespace Salt.Maynard

/-! ## R-uniform sharp `λ`-bound

`lam_abs_le_sharp` produces the constant `C₃·C₁^k`, which is entirely
`R`-independent (`C₁` from `rankin_bound 1` is `∀Q`-uniform, `C₃` from
`phi_ratio_le` is `R`-free).  We reorder the quantifiers so the single constant
serves every `R ≥ 2`. -/

/-- **R-uniform `lam_abs_le_sharp`.**  A single constant `C = C₃·C₁^k` (from
`rankin_bound`/`phi_ratio_le`, both `R`-free) bounds `|λ(d)|` by
`C·(1+log R)^{k+1}` for *every* `R ≥ 2`, weight `|y| ≤ 1`, and `d`. -/
theorem lam_abs_le_sharp_uniform (k W : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (R : ℕ), 2 ≤ R → ∀ (y : (Fin k → ℕ) → ℝ),
      (∀ r, |y r| ≤ 1) → ∀ d ∈ kSieveIndex k R W,
        |lam k R W y d| ≤ C * (1 + Real.log R) ^ (k + 1) := by
  obtain ⟨C₁, hC₁1, hC₁⟩ := rankin_bound 1
  obtain ⟨C₃, hC₃1, hC₃⟩ := phi_ratio_le
  refine ⟨C₃ * C₁ ^ k, ?_, ?_⟩
  · calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ C₃ * C₁ ^ k := by
          exact mul_le_mul hC₃1 (one_le_pow₀ hC₁1) zero_le_one (le_trans zero_le_one hC₃1)
  intro R hR y hy1 d hd
  -- Real bookkeeping.
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hR
  have hlogR : 0 ≤ Real.log R := (Real.log_pos hR1).le
  have hlogR1 : (0 : ℝ) ≤ 1 + Real.log R := by linarith
  -- Rankin at `L = 1`: `Σ_{q<R sqfree} 1/φ(q) ≤ C₁ log R`.
  have hRankin : ∑ q ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ C₁ * Real.log R := by
    have h := hC₁ R hR
    simpa using h
  rw [mem_kSieveIndex_iff] at hd
  obtain ⟨hsf, hpair, _hcopW, hprodR⟩ := hd
  set D := ∏ i, d i with hDdef
  have hd𝒟 : d ∈ kSieveIndex k R W := (mem_kSieveIndex_iff d).mpr ⟨hsf, hpair, _hcopW, hprodR⟩
  have hDsf : Squarefree D :=
    squarefree_prod_coprime Finset.univ d (fun i _ => hsf i)
      (fun i _ j _ hij => hpair i j hij)
  have hDR : D < R := hprodR
  have hphiD : (Nat.totient D : ℝ) = ∏ i, (Nat.totient (d i) : ℝ) := by
    rw [hDdef, prod_totient_coprime Finset.univ d (fun i _ j _ hij => hpair i j hij),
      Nat.cast_prod]
  have hφpos : ∀ i, (0 : ℝ) < (Nat.totient (d i) : ℝ) := by
    intro i
    have : 0 < Nat.totient (d i) := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hsf i).ne_zero)
    exact_mod_cast this
  have hlam : |lam k R W y d| ≤ (∏ i, (d i : ℝ)) * |wSum k R W y d| := by
    rw [lam, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_prod_moebius_mul_le d) (abs_nonneg _)
  have hwsum : |wSum k R W y d|
      ≤ (∏ i, 1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) ^ k := by
    refine (abs_wSum_le_guarded y hy1 d).trans ((guarded_sum_le_prod d).trans ?_)
    calc ∏ i, ∑ s ∈ (Finset.range R).filter (fun s => Squarefree s ∧ d i ∣ s),
            1 / (Nat.totient s : ℝ)
        ≤ ∏ i, (1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) := by
          apply Finset.prod_le_prod
          · intro i _
            exact Finset.sum_nonneg (fun s _ => by positivity)
          · intro i _
            refine (coord_sum_le (hsf i)).trans ?_
            exact mul_le_mul_of_nonneg_left hRankin (by positivity)
      _ = (∏ i, 1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) ^ k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
  have hDphi : (∏ i, (d i : ℝ)) * (∏ i, 1 / (Nat.totient (d i) : ℝ))
      = (D : ℝ) / (Nat.totient D : ℝ) := by
    rw [hphiD, hDdef, Nat.cast_prod]
    rw [show (∏ i, 1 / (Nat.totient (d i) : ℝ))
          = (∏ i, (Nat.totient (d i) : ℝ))⁻¹ by
        simp_rw [one_div]; rw [Finset.prod_inv_distrib]]
    rw [div_eq_mul_inv]
  have hprodd_nn : (0 : ℝ) ≤ ∏ i, (d i : ℝ) := Finset.prod_nonneg (fun i _ => by positivity)
  have hClogR_nn : (0 : ℝ) ≤ (C₁ * Real.log R) ^ k := by
    apply pow_nonneg; positivity
  calc |lam k R W y d|
      ≤ (∏ i, (d i : ℝ)) * |wSum k R W y d| := hlam
    _ ≤ (∏ i, (d i : ℝ)) *
          ((∏ i, 1 / (Nat.totient (d i) : ℝ)) * (C₁ * Real.log R) ^ k) :=
        mul_le_mul_of_nonneg_left hwsum hprodd_nn
    _ = ((D : ℝ) / (Nat.totient D : ℝ)) * (C₁ * Real.log R) ^ k := by
        rw [← mul_assoc, hDphi]
    _ ≤ (C₃ * (1 + Real.log R)) * (C₁ * Real.log R) ^ k :=
        mul_le_mul_of_nonneg_right (hC₃ hDsf hDR hR) hClogR_nn
    _ ≤ (C₃ * (1 + Real.log R)) * (C₁ ^ k * (1 + Real.log R) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ hlogR (by linarith) k
    _ = (C₃ * C₁ ^ k) * (1 + Real.log R) ^ (k + 1) := by ring

/-! ## R-uniform trivial `S₁` error and the assembled `S₁` upper bound -/

/-- **R-uniform `S1_trivial_error_le'`.**  The trivial error's constant `Cl²`
(from the uniform `λ`-bound) is `R`-free. -/
theorem S1_trivial_error_le'_uniform (k W' : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℕ), 2 ≤ R → ∀ (y : (Fin k → ℕ) → ℝ), (∀ r, |y r| ≤ 1) →
      (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2
        ≤ C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  obtain ⟨Cl, hCl1, hCl⟩ := lam_abs_le_sharp_uniform k W'
  have hCl0 : (0 : ℝ) ≤ Cl := le_trans zero_le_one hCl1
  refine ⟨Cl ^ 2, by positivity, ?_⟩
  intro R hR y hy1
  have hlog0 : (0 : ℝ) ≤ 1 + Real.log R := by
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hR
    have := Real.log_pos hR1; linarith
  have hsum : ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
      ≤ (kSieveIndex k R W').card • (Cl * (1 + Real.log R) ^ (k + 1)) :=
    Finset.sum_le_card_nsmul _ _ _ (fun d hd => hCl R hR y hy1 d hd)
  rw [nsmul_eq_mul] at hsum
  have hcard := kSieveIndex_card_le k R W' hR
  have hsum0 : (0 : ℝ) ≤ ∑ d ∈ kSieveIndex k R W', |lam k R W' y d| :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hchain : ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
      ≤ Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1) := by
    have hexp : k + (k + 1) = 2 * k + 1 := by ring
    calc ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
        ≤ ((kSieveIndex k R W').card : ℝ) * (Cl * (1 + Real.log R) ^ (k + 1)) := hsum
      _ ≤ ((R : ℝ) * (1 + Real.log R) ^ k) * (Cl * (1 + Real.log R) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hCl0 (pow_nonneg hlog0 _))
      _ = Cl * (R : ℝ) * ((1 + Real.log R) ^ k * (1 + Real.log R) ^ (k + 1)) := by ring
      _ = Cl * (R : ℝ) * (1 + Real.log R) ^ (k + (k + 1)) := by rw [← pow_add]
      _ = Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1) := by rw [hexp]
  have hee : (2 * k + 1) * 2 = 4 * k + 2 := by ring
  calc (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2
      ≤ (Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1)) ^ 2 :=
        pow_le_pow_left₀ hsum0 hchain 2
    _ = Cl ^ 2 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
        rw [mul_pow, mul_pow, ← pow_mul, hee]

/-- **R-uniform `S1_upper_A1`.**  A single constant `Cs = 2^{k+1}·Cl²` serves
every `R ≥ 2`: `S₁ ≤ 2((K₀−1)N/W)·A₁^k + Cs·R²·(1+log R)^{4k+2}`. -/
theorem S1_upper_A1_uniform (k K₀ N ν₀ : ℕ) (T : ℝ)
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) (hK₀ : 1 ≤ K₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℕ), 2 ≤ R →
      S1 k K₀ N R (W k) ν₀ (yTensor k R T)
        ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
          + C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  obtain ⟨C0, hC0, hC0le⟩ := S1_trivial_error_le'_uniform k (W k)
  refine ⟨2 ^ (k + 1) * C0, by positivity, ?_⟩
  intro R hR
  have hWpos : 0 < W k := Nat.pos_of_ne_zero (W_squarefree k).ne_zero
  -- solvability of compat pairs (as in `S1_upper_tensor`)
  have hsol : ∀ d ∈ kSieveIndex k R (W k), ∀ e ∈ kSieveIndex k R (W k),
      ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i) := by
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvable k d e ν₀ hWpos
      (fun i => Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero))
      (fun i => ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i)))
      (fun i j hij => compat_lcm_coprime k R hd he hcompat hij)
  -- `fTilde` divisor-antitone (as in `S1_upper_tensor`)
  have hfmono : ∀ d n : ℕ, d ∣ n → 0 < d → fTilde k R T n ≤ fTilde k R T d := by
    intro d n hdn hd0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : (0 : ℕ) ∉ sqfCop (R0 k R T) (W k) := by
        rw [sqfCop, Finset.mem_filter]
        rintro ⟨-, hsq, -⟩
        exact hsq.ne_zero rfl
      rw [show fTilde k R T 0 = 0 by simp only [fTilde, if_neg h0]]
      exact fTilde_nonneg k R T d hR
    · exact fTilde_anti k R T hR d n hn hdn
  have hL3 := S1_le k K₀ N R (W k) ν₀ (yTensor k R T) (fTilde k R T)
    (fun n => ⟨fTilde_nonneg k R T n hR, fTilde_le_one k R T hR n⟩) hfmono (fun r => rfl) rfl
    hk hD hK₀ hsol
  have htriv := hC0le R hR (yTensor k R T) (yTensor_abs_le_one k R T hR)
  have hyside := yside_le_A1pow k R T
  have hcoef : (0 : ℝ) ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) := by
    have h1 : (0 : ℝ) ≤ (K₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      linarith
    have h2 : (0 : ℝ) ≤ ((K₀ - 1) * N / (W k) : ℝ) :=
      div_nonneg (mul_nonneg h1 (Nat.cast_nonneg N)) (Nat.cast_nonneg _)
    linarith
  calc S1 k K₀ N R (W k) ν₀ (yTensor k R T)
      ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ)
          * (∑ r ∈ kSieveIndex k R (W k), (yTensor k R T r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R (W k), |lam k R (W k) (yTensor k R T) d|) ^ 2 :=
        hL3
    _ ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
        + 2 ^ (k + 1) * (C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hyside hcoef)
          (mul_le_mul_of_nonneg_left htriv (by positivity))
    _ = 2 * ((K₀ - 1) * N / (W k) : ℝ) * (A1 k R (W k) T) ^ k
        + (2 ^ (k + 1) * C0) * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by ring

/-! ## R-uniform disc bound and EH consumption

`abs_S2m_sub_compatMain_le_disc_uniform` and `S2m_ge_compatMain_eh` expose `Clam`
resp. `C₀` as `∃`-quantities that depend on the lemma's `R` parameter, yet their
*values* (`C₃·C₁^k` and `2·Clam²·C·(K₀+1)`, `C` from the `R`-free `eh_error_pow`)
are `R`-free.  We reorder so the constants sit before `R`. -/

/-- **R-uniform disc bound.**  The sharp `λ`-constant `Clam` is pulled out before
`R`, using `lam_abs_le_sharp_uniform`.  The body is the landed disc-bound proof. -/
theorem abs_S2m_sub_compatMain_le_disc_R_uniform (k K₀ : ℕ) (hK₀ : 1 ≤ K₀) :
    ∃ Clam : ℝ, 0 ≤ Clam ∧ ∀ (R ν₀ : ℕ) (T : ℝ), 2 ≤ R →
      (∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k)) →
      ∀ (m : Fin k) (N : ℕ), R ≤ N →
        |S2m k K₀ N R ν₀ m (yTensor k R T)
            - deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
                * s2CompatFormM k R (W k) m (yTensor k R T)|
          ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
              * ∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
                  ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
                    (if IsCollisionPair d e then 0
                     else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                          + maxDiscrepancy (N + hSeq k m) (qMod k d e)) := by
  classical
  obtain ⟨Clam, hClam1, hClam⟩ := lam_abs_le_sharp_uniform k (W k)
  refine ⟨Clam, le_trans zero_le_one hClam1, fun R ν₀ T hR hν₀ m N hRN => ?_⟩
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  set B := Clam * (1 + Real.log R) ^ (k + 1) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hcoef : Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2) = B ^ 2 := by
    have he : (2 * k + 2) = (k + 1) * 2 := by omega
    rw [hBdef, mul_pow, ← pow_mul, he]
  rw [hcoef]
  refine le_trans (abs_S2m_sub_compatMain_le k K₀ N R ν₀ m T hRN) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun d hd => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun e he => ?_)
  by_cases hcol : IsCollisionPair d e
  · rw [if_pos hcol, if_pos hcol, mul_zero]
  · rw [if_neg hcol, if_neg hcol]
    rw [Finset.mem_filter] at hd he
    obtain ⟨hdmem, hdm⟩ := hd
    obtain ⟨hemem, hem⟩ := he
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hdmem
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp hemem
    have hlcmpos : ∀ i, 0 < Nat.lcm (d i) (e i) := fun i =>
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero)
    have hcopW : ∀ i, Nat.Coprime (W k) (Nat.lcm (d i) (e i)) := fun i =>
      ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i))
    have hcoplcm : ∀ i j, i ≠ j →
        Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) :=
      fun i j hij => compat_lcm_coprime k R hdmem hemem hcol hij
    have happrox := s2PrimeCount_approx' k K₀ N ν₀ m d e hdm hem hlcmpos hcopW hcoplcm hν₀ hK₀
    simp only [phiLcmProd] at happrox
    set M := maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
      + maxDiscrepancy (N + hSeq k m) (qMod k d e) with hMdef
    calc |lam k R (W k) (yTensor k R T) d| * |lam k R (W k) (yTensor k R T) e|
            * |(s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ)
                    * ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))|
          ≤ B * B * M := by
            refine mul_le_mul ?_ happrox (abs_nonneg _) (mul_nonneg hBnn hBnn)
            exact mul_le_mul
              (hClam R hR (yTensor k R T) (yTensor_abs_le_one k R T hR) d hdmem)
              (hClam R hR (yTensor k R T) (yTensor_abs_le_one k R T hR) e hemem)
              (abs_nonneg _) hBnn
      _ = B ^ 2 * M := by ring

/-- **R-uniform C4 EH consumption.**  The error constant
`C₀ = 2·Clam²·C·(K₀+1)` and threshold `N₀ = max (max 2 N₁) (D₀ k)` are both
`R`-free (`Clam` via the uniform disc bound, `C`/`N₁` via the `R`-free
`eh_error_pow`).  The body is the landed `S2m_ge_compatMain_eh` proof. -/
theorem S2m_ge_compatMain_eh_uniform (k K₀ : ℕ) (hk : 1 ≤ k) (hK₀ : 1 ≤ K₀)
    (hEH : EH (1 / 2)) :
    ∃ (C₀ : ℝ) (N₀ : ℕ), 0 ≤ C₀ ∧ ∀ (R ν₀ : ℕ) (T : ℝ), 2 ≤ R →
      (∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k)) →
      ∀ N : ℕ, N₀ ≤ N → R ≤ N → (W k * R ^ 2 ≤ ⌊(N : ℝ) ^ (1 / 2 : ℝ)⌋₊) →
      ∀ m : Fin k,
        S2m k K₀ N R ν₀ m (yTensor k R T)
          ≥ deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
              * s2CompatFormM k R (W k) m (yTensor k R T)
            - C₀ * (1 + Real.log R) ^ (2 * k + 2) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
  classical
  obtain ⟨Clam, hClam0, hdisc⟩ := abs_S2m_sub_compatMain_le_disc_R_uniform k K₀ hK₀
  obtain ⟨C, N₁, hEHb⟩ := eh_error_pow k (2 * k + 4) (by omega) hEH
  have hCnn : 0 ≤ C := by
    set x₀ := max N₁ 2 with hx₀
    have hmax2 : 2 ≤ x₀ := le_max_right N₁ 2
    have hb := hEHb x₀ (le_max_left N₁ 2)
    have hx0pos : 0 < x₀ := by omega
    have hlogx0 : 0 < Real.log x₀ :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x₀ by omega))
    have hLHS0 : (0 : ℝ) ≤ ∑ q ∈ (Finset.range (⌊(x₀ : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1)).filter Squarefree,
        (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x₀ q :=
      Finset.sum_nonneg (fun q _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x₀ q))
    have hpos : 0 < (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) :=
      div_pos (by exact_mod_cast hx0pos) (pow_pos hlogx0 _)
    by_contra hCneg
    have hbad : C * (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) < 0 := by
      rw [mul_div_assoc]; exact mul_neg_of_neg_of_pos (not_le.mp hCneg) hpos
    linarith [hLHS0, hb, hbad]
  refine ⟨2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1), max (max 2 N₁) (D₀ k), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * Clam ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h1 hCnn) (by positivity)
  intro R ν₀ T hR hν₀ N hN0 hRN hrange m
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  -- regime facts from `N₀ = max (max 2 N₁) (D₀ k) ≤ N`
  have hle2N1 : max 2 N₁ ≤ N := le_trans (le_max_left (max 2 N₁) (D₀ k)) hN0
  have hD0N : D₀ k ≤ N := le_trans (le_max_right (max 2 N₁) (D₀ k)) hN0
  have h2N : 2 ≤ N := le_trans (le_max_left 2 N₁) hle2N1
  have hN1N : N₁ ≤ N := le_trans (le_max_right 2 N₁) hle2N1
  have hNpos : 0 < N := by omega
  have hhm : hSeq k m ≤ N := le_trans (hSeq_le_D₀ k m) hD0N
  have hNleK0N : N ≤ K₀ * N := Nat.le_mul_of_pos_left N (by omega)
  have hlogN0 : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  have endpoint : ∀ x : ℕ, N ≤ x → x ≤ (K₀ + 1) * N →
      ∑ q ∈ (Finset.range (W k * R ^ 2 + 1)).filter Squarefree,
          (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    intro x hNx hxub
    have hNxr : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNx
    have hfloorle : ⌊(N : ℝ) ^ (1 / 2 : ℝ)⌋₊ ≤ ⌊(x : ℝ) ^ (1 / 2 : ℝ)⌋₊ :=
      Nat.floor_mono (Real.rpow_le_rpow (by positivity) hNxr (by norm_num))
    have hWRx : W k * R ^ 2 ≤ ⌊(x : ℝ) ^ (1 / 2 : ℝ)⌋₊ := le_trans hrange hfloorle
    have hsub : (Finset.range (W k * R ^ 2 + 1)).filter Squarefree
        ⊆ (Finset.range (⌊(x : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1)).filter Squarefree :=
      Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega))
    have hlogx0 : 0 < Real.log x :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x by omega))
    have hlogxN : Real.log N ≤ Real.log x := Real.log_le_log (by exact_mod_cast hNpos) hNxr
    have hd1pos : 0 < (Real.log x) ^ (2 * k + 4) := pow_pos hlogx0 _
    have hd2pos : 0 < (Real.log N) ^ (2 * k + 4) := pow_pos hlogN0 _
    have hd21 : (Real.log N) ^ (2 * k + 4) ≤ (Real.log x) ^ (2 * k + 4) :=
      pow_le_pow_left₀ hlogN0.le hlogxN _
    calc ∑ q ∈ (Finset.range (W k * R ^ 2 + 1)).filter Squarefree,
            (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ ∑ q ∈ (Finset.range (⌊(x : ℝ) ^ (1 / 2 : ℝ)⌋₊ + 1)).filter Squarefree,
            (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun q _ _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x q))
      _ ≤ C * (x : ℝ) / (Real.log x) ^ (2 * k + 4) := hEHb x (le_trans hN1N hNx)
      _ ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
          rw [div_le_div_iff₀ hd1pos hd2pos]
          have hxubr : (x : ℝ) ≤ ((K₀ : ℝ) + 1) * (N : ℝ) := by exact_mod_cast hxub
          have step_num : C * (x : ℝ) ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) := by
            calc C * (x : ℝ) ≤ C * (((K₀ : ℝ) + 1) * (N : ℝ)) :=
                  mul_le_mul_of_nonneg_left hxubr hCnn
              _ = C * ((K₀ : ℝ) + 1) * (N : ℝ) := by ring
          have hcnum : 0 ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) :=
            mul_nonneg (mul_nonneg hCnn (by positivity)) (by positivity)
          exact mul_le_mul step_num hd21 (pow_nonneg hlogN0.le _) hcnum
  have hexp : (K₀ + 1) * N = K₀ * N + N := by ring
  have hx1lb : N ≤ K₀ * N + hSeq k m := le_trans hNleK0N (Nat.le_add_right _ _)
  have hx1ub : K₀ * N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hx2ub : N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hEP1 := endpoint (K₀ * N + hSeq k m) hx1lb hx1ub
  have hEP2 := endpoint (N + hSeq k m) (Nat.le_add_right _ _) hx2ub
  have hfib1 := compat_pair_fiber_le k R m (fun q => maxDiscrepancy (K₀ * N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (K₀ * N + hSeq k m) q)
  have hfib2 := compat_pair_fiber_le k R m (fun q => maxDiscrepancy (N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (N + hSeq k m) q)
  have hsplit : (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                + maxDiscrepancy (N + hSeq k m) (qMod k d e)))
      = (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)))
        + (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
            ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
              (if IsCollisionPair d e then 0
               else maxDiscrepancy (N + hSeq k m) (qMod k d e))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hcol : IsCollisionPair d e
    · simp only [if_pos hcol, add_zero]
    · simp only [if_neg hcol]
  have hDiscSum : (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                + maxDiscrepancy (N + hSeq k m) (qMod k d e)))
      ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
        + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    rw [hsplit]
    exact add_le_add (le_trans hfib1 hEP1) (le_trans hfib2 hEP2)
  have hLnn : 0 ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _)
  have hfinal : |S2m k K₀ N R ν₀ m (yTensor k R T)
        - deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
            * s2CompatFormM k R (W k) m (yTensor k R T)|
      ≤ 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
          * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    refine le_trans (hdisc R ν₀ T hR hν₀ m N hRN) ?_
    calc Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
          * (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
              ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
                (if IsCollisionPair d e then 0
                 else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                      + maxDiscrepancy (N + hSeq k m) (qMod k d e)))
        ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
            * (C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
              + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)) :=
          mul_le_mul_of_nonneg_left hDiscSum hLnn
      _ = 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
            * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by ring
  have := (abs_le.mp hfinal).1
  linarith

/-! ## Regime threshold real-analysis: polynomial beats polylog

The `herr1`/`herr2`/`hδlb` thresholds all reduce to "a fixed power of `1+log x`
is eventually dominated by a positive power of `x`". -/

open Filter Asymptotics in
/-- **Polynomial beats polylog.**  For any degree `n`, exponent `a > 0`, and
coefficient `K`, eventually `K·(1+log x)^n ≤ x^a`.  This is the analytic core of
the `herr` thresholds (`R²·(1+log R)^{4k+2} = o(N')` at `R = ⌊N'^{1/5}⌋`). -/
theorem eventually_poly_beats_polylog (n : ℕ) (a K : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ n ≤ x ^ a := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero, mul_one]
    filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop K] with x hx using hx
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set r := a / (2 * n) with hr
    have hrpos : 0 < r := by rw [hr]; positivity
    have hlog := isLittleO_log_rpow_atTop hrpos
    have hev1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ r := by
      filter_upwards [hlog.eventuallyLE, (eventually_gt_atTop (0 : ℝ))] with x hx hx0
      calc Real.log x ≤ |Real.log x| := le_abs_self _
        _ ≤ |x ^ r| := hx
        _ = x ^ r := abs_of_nonneg (Real.rpow_nonneg hx0.le r)
    have hev2 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x ^ r :=
      (tendsto_rpow_atTop hrpos).eventually_ge_atTop 1
    have hev3 : ∀ᶠ x : ℝ in atTop, K * 2 ^ n ≤ x ^ (a / 2) :=
      (tendsto_rpow_atTop (by positivity : (0 : ℝ) < a / 2)).eventually_ge_atTop (K * 2 ^ n)
    filter_upwards [hev1, hev2, hev3, (eventually_ge_atTop (1 : ℝ))]
      with x hlx h1x h3x hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hbase_nn : 0 ≤ 1 + Real.log x := by linarith
    have hstep : 1 + Real.log x ≤ 2 * x ^ r := by linarith [hlx, h1x]
    -- `(x^r)^n = x^(a/2)` since `r·n = a/2`.
    have hpow : (x ^ r) ^ n = x ^ (a / 2) := by
      rw [← Real.rpow_natCast (x ^ r) n, ← Real.rpow_mul hx0.le]
      congr 1
      rw [hr]; field_simp
    have hxa2nn : (0 : ℝ) ≤ x ^ (a / 2) := Real.rpow_nonneg hx0.le _
    have hxann : (0 : ℝ) ≤ x ^ a := Real.rpow_nonneg hx0.le _
    by_cases hK : 0 ≤ K
    · calc K * (1 + Real.log x) ^ n
          ≤ K * (2 * x ^ r) ^ n :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hstep n) hK
        _ = K * 2 ^ n * x ^ (a / 2) := by rw [mul_pow, hpow]; ring
        _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul_of_nonneg_right h3x hxa2nn
        _ = x ^ a := by rw [← Real.rpow_add hx0]; congr 1; ring
    · have hle0 : K * (1 + Real.log x) ^ n ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hK)) (pow_nonneg hbase_nn n)
      linarith [hxann]

end Salt.Maynard
