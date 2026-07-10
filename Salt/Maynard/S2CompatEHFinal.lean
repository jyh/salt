/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2CompatEH
import Salt.Maynard.S2FiberCount
import Salt.Maynard.EHConsume
import Salt.Maynard.Endgame

/-!
# C4 EH consumption — the assembled per-`m` lower bound on `S₂^(m)`

This file assembles the landed C4 pieces into the headline consequence of the
Elliott–Halberstam hypothesis `EH (1/2)`: for each coordinate `m`, the prime-
restricted Selberg object `S₂^(m)` exceeds its compat main term
`(Δπ/φW)·s2CompatFormM` up to an error of size
`O((1+log R)^{2k+2}·N/(log N)^{2k+4})`.

The route is pure real-analysis bookkeeping over already-proved lemmas:

1. **Disc bound** (`abs_S2m_sub_compatMain_le_disc_uniform`, a uniform-`L`
   repackaging of `abs_S2m_sub_compatMain_le_disc`): the S₂ error is
   `Clam²·(1+log R)^{2k+2}` times a compat sum of endpoint discrepancies at the
   combined modulus `qMod`, with `Clam ≥ 1` the sharp `λ`-constant, *uniform in
   `N` and `m`*.
2. **Split** the two endpoints `maxDisc(K₀N+hₘ) + maxDisc(N+hₘ)`.
3. **Fiber regroup** (`compat_pair_fiber_le`): each endpoint's compat pair sum is
   `≤ ∑_{q<W·R²+1, sqf} (3k)^{ω(q)}·maxDisc(x,q)`.
4. **Range-extend + EH** (`eh_error_pow`): extend `range(W·R²+1) ⊆
   range(⌊x^{1/2}⌋₊+1)` (nonneg terms) and apply the EH bound at the two
   endpoints `x ∈ {K₀N+hₘ, N+hₘ}`.
5. **Uniformize in `m`** (`hSeq_le_D₀`): for `N ≥ D₀ k`, both endpoints are
   `≤ (K₀+1)N` and have `log ≥ log N`, so each is
   `≤ C·(K₀+1)·N/(log N)^{2k+4}`.

Combining gives `|S₂^(m) − main| ≤ C₀·(1+log R)^{2k+2}·N/(log N)^{2k+4}` with
`C₀ = 2·Clam²·C·(K₀+1)`, whence the per-`m` lower bound.
-/

open Finset

namespace Salt.Maynard

/-- **Uniform disc bound.** A repackaging of `abs_S2m_sub_compatMain_le_disc`
that pulls the (`N`- and `m`-independent) sharp `λ`-constant `Clam` out in front
of the `∀ m, ∀ N` quantifiers, so the coefficient
`Clam²·(1+log R)^{2k+2}` is a single fixed real usable for every `N` and `m`.
The body is the landed disc-bound proof with the existential restructured. -/
theorem abs_S2m_sub_compatMain_le_disc_uniform (k K₀ R ν₀ : ℕ) (T : ℝ)
    (hR : 2 ≤ R) (hK₀ : 1 ≤ K₀)
    (hν₀ : ∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k)) :
    ∃ Clam : ℝ, 0 ≤ Clam ∧ ∀ (m : Fin k) (N : ℕ), R ≤ N →
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
  have hW0 : W k ≠ 0 := (Nat.pos_of_ne_zero (W_squarefree k).ne_zero).ne'
  obtain ⟨Clam, hClam1, hClam⟩ := lam_abs_le_sharp k R (W k) (yTensor k R T)
    (yTensor_abs_le_one k R T hR) hR hW0
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  refine ⟨Clam, le_trans zero_le_one hClam1, fun m N hRN => ?_⟩
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
            exact mul_le_mul (hClam d hdmem) (hClam e hemem) (abs_nonneg _) hBnn
      _ = B ^ 2 * M := by ring

/-- **C4 EH consumption — the per-`m` lower bound on `S₂^(m)`.** Under `EH (1/2)`,
`S₂^(m)` exceeds its compat main term `(Δπ/φW)·s2CompatFormM` up to an error
`O((1+log R)^{2k+2}·N/(log N)^{2k+4})`, once `N` is past the regime threshold
`N₀ = max (max 2 N₁) (D₀ k)` and satisfies the range condition
`W·R² ≤ ⌊√N⌋`.  The constant is `C₀ = 2·Clam²·C·(K₀+1)`. -/
theorem S2m_ge_compatMain_eh (k K₀ R ν₀ : ℕ) (T : ℝ)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hK₀ : 1 ≤ K₀)
    (hν₀ : ∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k))
    (hEH : EH (1 / 2)) :
    ∃ (C₀ : ℝ) (N₀ : ℕ), 0 ≤ C₀ ∧ ∀ N : ℕ, N₀ ≤ N → R ≤ N →
      (W k * R ^ 2 ≤ ⌊(N : ℝ) ^ (1 / 2 : ℝ)⌋₊) →
      ∀ m : Fin k,
        S2m k K₀ N R ν₀ m (yTensor k R T)
          ≥ deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
              * s2CompatFormM k R (W k) m (yTensor k R T)
            - C₀ * (1 + Real.log R) ^ (2 * k + 2) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
  classical
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  obtain ⟨Clam, hClam0, hdisc⟩ :=
    abs_S2m_sub_compatMain_le_disc_uniform k K₀ R ν₀ T hR hK₀ hν₀
  obtain ⟨C, N₁, hEHb⟩ := eh_error_pow k (2 * k + 4) (by omega) hEH
  -- `C ≥ 0`: the EH bound dominates a nonnegative sum at a large point.
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
  intro N hN0 hRN hrange m
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
  -- **Endpoint bound**: for `x` in `[N, (K₀+1)N]`, the fiber sum over the
  -- `W·R²`-range is `≤ C·(K₀+1)·N/(log N)^{2k+4}` (range-extend + EH + uniformize).
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
  -- endpoints `x₁ = K₀N+hₘ`, `x₂ = N+hₘ`
  have hexp : (K₀ + 1) * N = K₀ * N + N := by ring
  have hx1lb : N ≤ K₀ * N + hSeq k m := le_trans hNleK0N (Nat.le_add_right _ _)
  have hx1ub : K₀ * N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hx2ub : N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hEP1 := endpoint (K₀ * N + hSeq k m) hx1lb hx1ub
  have hEP2 := endpoint (N + hSeq k m) (Nat.le_add_right _ _) hx2ub
  -- fiber regroup at each endpoint
  have hfib1 := compat_pair_fiber_le k R m (fun q => maxDiscrepancy (K₀ * N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (K₀ * N + hSeq k m) q)
  have hfib2 := compat_pair_fiber_le k R m (fun q => maxDiscrepancy (N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (N + hSeq k m) q)
  -- split the two endpoints of the disc sum
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
  -- assemble: the disc sum `≤ 2·EP`
  have hDiscSum : (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qMod k d e)
                + maxDiscrepancy (N + hSeq k m) (qMod k d e)))
      ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
        + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    rw [hsplit]
    exact add_le_add (le_trans hfib1 hEP1) (le_trans hfib2 hEP2)
  -- multiply by the disc coefficient and simplify to the target error
  have hLnn : 0 ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _)
  have hfinal : |S2m k K₀ N R ν₀ m (yTensor k R T)
        - deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
            * s2CompatFormM k R (W k) m (yTensor k R T)|
      ≤ 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
          * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    refine le_trans (hdisc m N hRN) ?_
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
  -- `|a - b| ≤ e ⟹ a ≥ b - e`
  have := (abs_le.mp hfinal).1
  linarith

end Salt.Maynard
