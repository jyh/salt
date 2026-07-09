/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Eh
import Salt.Maynard.LamBoundSharp
import Salt.Maynard.TensorA1
import Salt.Maynard.Lemma53Rel

/-!
# C4 assembly — `S₂^(m)` over compatible pairs (`docs/blueprints/endgame-design.md`, C4)

The landed `S2m_lower` used the FULL diagonal `Qdiag_m` as its main term, which
made its `herr` (a discrepancy sum over ALL `dₘ=eₘ=1` pairs) vacuous: collision
pairs have `count = 0` but nonzero density, so their `|count − density|` is main-
sized.  The fix: restrict the main to `s2CompatFormM` (compat pairs only) and route
the collision pairs through Wave 2's SIGNED bound `s2Compat_ge_N`.

This file builds the compat-restricted error side:

* `abs_S2m_sub_compatMain_le` — the algebraic core (LANDED lemmas only): `S2m`
  rewrites to a compat sum (collision ⟹ `s2PrimeCount = 0`), and the main term
  `(Δπ/φW)·s2CompatFormM` expands as `Σ_compat λλ·density`, so their difference
  is `Σ_compat λλ·(count − density)` and, by the triangle inequality,
  `|S2m − main| ≤ Σ_compat |λ_d||λ_e|·|count − density|`.

The EH consumption (`s2PrimeCount_approx'` per pair, the `(3k)^ω` fiber
regrouping, and `eh_error_pow` at both endpoints) is layered on top.
-/

namespace Salt.Maynard

open Finset

/-- For a prime `p`, `p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b` (via `lcm ∣ a*b` and `a,b ∣ lcm`). -/
theorem prime_dvd_lcm_iff {p a b : ℕ} (hp : p.Prime) :
    p ∣ Nat.lcm a b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · intro h
    exact (Nat.Prime.dvd_mul hp).mp (h.trans (Nat.lcm_dvd_mul a b))
  · rintro (h | h)
    · exact h.trans (Nat.dvd_lcm_left a b)
    · exact h.trans (Nat.dvd_lcm_right a b)

/-- **The `¬collision ⟹ pairwise-coprime lcm` bridge.** For sieve tuples `d, e`
that are not a collision pair, the combined moduli `lcm(dᵢ,eᵢ)` are pairwise
coprime: a shared prime forces either a same-side coprimality failure (against
`kSieveIndex`) or a cross-side one (a collision). -/
theorem compat_lcm_coprime (k R : ℕ) {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
  obtain ⟨hdsq, hdcop, -, -⟩ := (mem_kSieveIndex_iff d).mp hd
  obtain ⟨hesq, hecop, -, -⟩ := (mem_kSieveIndex_iff e).mp he
  by_contra hnc
  obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  rcases (prime_dvd_lcm_iff hp).mp hpi with hpdi | hpei <;>
    rcases (prime_dvd_lcm_iff hp).mp hpj with hpdj | hpej
  · exact absurd (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpdi, hpdj⟩)
      (not_not.mpr (hdcop i j hij))
  · exact hcompat ⟨i, j, hij, Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpdi, hpej⟩⟩
  · exact hcompat ⟨j, i, hij.symm, Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpdj, hpei⟩⟩
  · exact absurd (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpei, hpej⟩)
      (not_not.mpr (hecop i j hij))

/-- `|yTensor| ≤ 1` (product of `fTilde ∈ [0,1]`). -/
theorem yTensor_abs_le_one (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) (r : Fin k → ℕ) :
    |yTensor k R T r| ≤ 1 := by
  simp only [yTensor]
  split_ifs
  · rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR))]
    calc ∏ i, fTilde k R T (r i) ≤ ∏ _i : Fin k, (1 : ℝ) :=
          Finset.prod_le_prod (fun i _ => fTilde_nonneg k R T _ hR)
            (fun i _ => fTilde_le_one k R T hR _)
      _ = 1 := by simp
  · simp

/-- **C4 core (algebraic).** The S₂ object minus its compat main term is
controlled, pair by pair, by `|λ_d||λ_e|·|count − density|` over compat pairs.
Collision pairs drop out on both sides (`s2PrimeCount_collision` on the left,
the `IsCollisionPair` guard on the right).  Uses only landed lemmas. -/
theorem abs_S2m_sub_compatMain_le (k K₀ N R ν₀ : ℕ) (m : Fin k) (T : ℝ) (hRN : R ≤ N) :
    |S2m k K₀ N R ν₀ m (yTensor k R T)
        - deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
            * s2CompatFormM k R (W k) m (yTensor k R T)|
      ≤ ∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else |lam k R (W k) (yTensor k R T) d| * |lam k R (W k) (yTensor k R T) e|
                    * |(s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                        - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ)
                            * ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))|) := by
  classical
  -- `S2m` as a compat-guarded sum: on collision pairs the count is `0`.
  have hS2m : S2m k K₀ N R ν₀ m (yTensor k R T)
      = ∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else lam k R (W k) (yTensor k R T) d * lam k R (W k) (yTensor k R T) e
                    * (s2PrimeCount k K₀ N ν₀ m d e : ℝ)) := by
    rw [S2m_eq_guarded k K₀ N R ν₀ m (yTensor k R T) hRN, guarded_double_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mem_filter] at hd
    by_cases hcol : IsCollisionPair d e
    · rw [if_pos hcol]
      obtain ⟨i, j, hij, hcolij⟩ := hcol
      have hdcop : ∀ i, Nat.Coprime (d i) (W k) := ((mem_kSieveIndex_iff d).mp hd.1).2.2.1
      rw [s2PrimeCount_collision k K₀ N ν₀ m d e hdcop hij hcolij]
      simp
    · rw [if_neg hcol]
  -- the difference is a single compat-guarded sum of `λλ·(count − density)`.
  have hcombine : S2m k K₀ N R ν₀ m (yTensor k R T)
        - deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
            * s2CompatFormM k R (W k) m (yTensor k R T)
      = ∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else lam k R (W k) (yTensor k R T) d * lam k R (W k) (yTensor k R T) e
                    * ((s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                        - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ)
                            * ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)))) := by
    rw [hS2m, s2CompatMain_eq k K₀ N R m (yTensor k R T), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hcol : IsCollisionPair d e
    · simp only [if_pos hcol, sub_zero]
    · rw [if_neg hcol, if_neg hcol, if_neg hcol]; ring
  rw [hcombine]
  -- triangle inequality, twice, then per-pair `|λλΔ| = |λ||λ||Δ|`.
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => ?_))
  by_cases hcol : IsCollisionPair d e
  · rw [if_pos hcol, if_pos hcol, abs_zero]
  · rw [if_neg hcol, if_neg hcol, abs_mul, abs_mul]

/-- **C4 discrepancy bound.** Bounding `|λ_d|,|λ_e| ≤ λmax` (`lam_abs_le_sharp`)
and `|count − density| ≤ maxDisc(K₀N+hₘ) + maxDisc(N+hₘ)` per compat pair
(`s2PrimeCount_approx'`, whose pairwise-coprime-lcm hypothesis is discharged by
`compat_lcm_coprime`), the S₂ error is `λmax²` times a compat sum of endpoint
discrepancies at the combined modulus `qMod`. -/
theorem abs_S2m_sub_compatMain_le_disc (k K₀ N R ν₀ : ℕ) (m : Fin k) (T : ℝ)
    (hRN : R ≤ N) (hR : 2 ≤ R) (hK₀ : 1 ≤ K₀)
    (hν₀ : ∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k)) :
    ∃ L : ℝ, 0 ≤ L ∧
      |S2m k K₀ N R ν₀ m (yTensor k R T)
          - deltaPi k K₀ N m / (Nat.totient (W k) : ℝ)
              * s2CompatFormM k R (W k) m (yTensor k R T)|
        ≤ L * ∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
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
  set B := Clam * (1 + Real.log R) ^ (k + 1) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  refine ⟨B ^ 2, by positivity, ?_⟩
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
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) happrox
    calc |lam k R (W k) (yTensor k R T) d| * |lam k R (W k) (yTensor k R T) e|
            * |(s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                - deltaPi k K₀ N m / ((Nat.totient (W k) : ℝ)
                    * ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))|
          ≤ B * B * M := by
            refine mul_le_mul ?_ happrox (abs_nonneg _) (mul_nonneg hBnn hBnn)
            exact mul_le_mul (hClam d hdmem) (hClam e hemem) (abs_nonneg _) hBnn
      _ = B ^ 2 * M := by ring

end Salt.Maynard
