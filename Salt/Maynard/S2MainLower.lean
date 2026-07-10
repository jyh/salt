/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.DiagonalS2
import Salt.Maynard.S2DiagRestricted
import Salt.Maynard.Lemma53
import Salt.Maynard.GFunction
import Salt.Maynard.KSieve

/-!
# The S₂ main lower bound (Maynard)

This file assembles the `S₂^{(m)}` diagonal lower bound.  Starting from the
`dₘ = eₘ = 1`-restricted S₂ diagonalisation `s2_diag_lam_restricted`
(`Q_m = ∑_{u:uₘ=1} (∏ᵢ g(uᵢ))·Vₘ(u)²`), we

1. repackage each summand as `(yM u)² / ∏ᵢ g(uᵢ)` (Step 1), using
   `(∏ᵢ μ(uᵢ)g(uᵢ))² = (∏ᵢ g(uᵢ))²` on the squarefree support (`μ² = 1`);
2. apply `gMult_le_totient` **pointwise** — `g(uᵢ) ≤ φ(uᵢ)`, all positive, so
   `∏g ≤ ∏φ` and `(yM u)²/∏g ≥ (yM u)²/∏φ` (Step 2, the ratio-critical step;
   there is NO `∑f²/g`-vs-`A₁` ratio, so no compounding);
3. replace `yM u` by its 1-dimensional `m`-coordinate contraction via
   `lemma53`, with an `O(log R / D₀)` per-`u` error (Step 3).

The result `s2main_lower` states, with an `R`-free constant `C`,

  `Q_m ≥ ∑_{u:uₘ=1} (∑_{aₘ<R} y_{u;m→aₘ}/φ(aₘ))² / ∏ᵢ φ(uᵢ)
          − (2·C·log R / D₀) · ∑_{u:uₘ=1} |∑_{aₘ<R} y_{u;m→aₘ}/φ(aₘ)| / ∏ᵢ φ(uᵢ)`.

The main term `∑_{u:uₘ=1} (contraction u)² / ∏ᵢ φ(uᵢ)` is load-bearing (the next
node factorises it into `B₁²·A₁^{k-1}`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- **S₂ main lower bound.** The `dₘ = eₘ = 1`-restricted S₂ quadratic form is
lower-bounded by the `φ`-denominator contraction main term minus an
`R`-free-constant · `log R` / `D₀` error.  Step 2 (`gMult_le_totient`) is applied
**pointwise**, so no `∑f²/g`-vs-`A₁` ratio ever appears (no compounding). -/
theorem s2main_lower (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
          lam k R (W k) y d * lam k R (W k) y e
            / ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))
        ≥ (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
             (∑ am ∈ Finset.range R,
                 y (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
               / ∏ i, (Nat.totient (u i) : ℝ))
          - (2 * C * Real.log R / (D₀ k : ℝ))
            * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
                |∑ am ∈ Finset.range R,
                    y (Function.update u m am) / (Nat.totient am : ℝ)|
                  / ∏ i, (Nat.totient (u i) : ℝ) := by
  classical
  -- basic positivity facts
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D₀ k := by omega
  have hD0pos : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0pos
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ R)
  have hlognn : 0 ≤ Real.log R := Real.log_nonneg hR1
  -- monotonicity of `c ↦ c · log R / D₀`
  have mono : ∀ {c c' : ℝ}, c ≤ c' →
      c * Real.log R / (D₀ k : ℝ) ≤ c' * Real.log R / (D₀ k : ℝ) := by
    intro c c' h; gcongr
  -- a uniform `lemma53` constant over any finite set of tuples
  have gen : ∀ (s : Finset (Fin k → ℕ)),
      (∀ u ∈ s, ∃ C, 0 ≤ C ∧
        |yM k R (W k) m y u
            - ∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
          ≤ C * Real.log R / (D₀ k : ℝ)) →
      ∃ C, 0 ≤ C ∧ ∀ u ∈ s,
        |yM k R (W k) m y u
            - ∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
          ≤ C * Real.log R / (D₀ k : ℝ) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _; exact ⟨0, le_refl 0, fun u hu => absurd hu (by simp)⟩
    · intro a₀ t ha₀ ih hall
      obtain ⟨Ca, hCa0, hCa⟩ := hall a₀ (Finset.mem_insert_self a₀ t)
      obtain ⟨Ct, hCt0, hCtb⟩ := ih (fun u hu => hall u (Finset.mem_insert_of_mem hu))
      refine ⟨max Ca Ct, le_trans hCa0 (le_max_left _ _), fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hus
      · exact le_trans hCa (mono (le_max_left _ _))
      · exact le_trans (hCtb u hus) (mono (le_max_right _ _))
  -- instantiate the uniform constant on the pinned sieve set
  obtain ⟨C, hC0, hspec⟩ := gen ((kSieveIndex k R (W k)).filter (fun u => u m = 1)) (by
    intro u hu
    rw [Finset.mem_filter] at hu
    exact lemma53 k R m y hy1 hysupp u hu.2 hR hu.1 hk hD)
  refine ⟨C, hC0, ?_⟩
  set K := 2 * C * Real.log R / (D₀ k : ℝ) with hKdef
  -- per-`u` lower bound: this is Steps 1–3 combined
  have hmain :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              y (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * (|∑ am ∈ Finset.range R,
                      y (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))))
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m y u) ^ 2 := by
    apply Finset.sum_le_sum
    intro u hu
    have hmem := hu
    rw [Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff u).mp husupp
    -- every prime factor of a coordinate is `≥ 3`
    have hodd : ∀ i, ∀ p ∈ (u i).primeFactors, 3 ≤ p := by
      intro i p hp
      have := D₀_lt_of_prime_dvd_coord husupp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    -- coordinatewise positivity of `g`
    have hgcoord_pos : ∀ i, 0 < (gMult (u i) : ℝ) := by
      intro i
      have hpos : 0 < gMult (u i) := by
        rw [gMult]; apply Finset.prod_pos
        intro p hp; have := hodd i p hp; omega
      exact_mod_cast hpos
    have hφcoord_pos : ∀ i, 0 < (Nat.totient (u i) : ℝ) := by
      intro i; exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos husupp i)
    -- abbreviations
    set V := lamPhiContractM k R (W k) m y u with hVdef
    set G := ∏ i, (gMult (u i) : ℝ) with hGdef
    set Φ := ∏ i, (Nat.totient (u i) : ℝ) with hΦdef
    set a := yM k R (W k) m y u with hadef
    set b := ∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ) with hbdef
    have hGpos : 0 < G := Finset.prod_pos (fun i _ => hgcoord_pos i)
    have hΦpos : 0 < Φ := Finset.prod_pos (fun i _ => hφcoord_pos i)
    have hGleΦ : G ≤ Φ := by
      apply Finset.prod_le_prod
      · intro i _; exact (hgcoord_pos i).le
      · intro i _; exact gMult_le_totient (hsq i) (hodd i)
    -- Step 1: `(yM u)² = (∏g)² · V²` via `μ² = 1`
    have hμsq : (∏ i, ((μ (u i) : ℤ) : ℝ)) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro i _
      have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsq i)
      have hc : ((μ (u i) : ℤ) : ℝ) ^ 2 = (((μ (u i)) ^ 2 : ℤ) : ℝ) := by push_cast; ring
      rw [hc, h]; norm_num
    have hyMsq : a ^ 2 = G ^ 2 * V ^ 2 := by
      have hdef : a = (∏ i, ((μ (u i) : ℤ) : ℝ) * (gMult (u i) : ℝ)) * V := rfl
      rw [hdef, mul_pow, Finset.prod_mul_distrib, mul_pow, hμsq, one_mul]
    -- the uniform `lemma53` bound for this `u`
    have herr : |a - b| ≤ C * Real.log R / (D₀ k : ℝ) := hspec u hmem
    -- Step 3: `b² − 2|b|·(C log R/D₀) ≤ a²`
    have hsqb : b ^ 2 - 2 * |b| * (C * Real.log R / (D₀ k : ℝ)) ≤ a ^ 2 := by
      have h1b : -(|b| * |a - b|) ≤ b * (a - b) := by
        have := neg_abs_le (b * (a - b)); rwa [abs_mul] at this
      have hstep : b ^ 2 - 2 * |b| * |a - b| ≤ a ^ 2 := by
        nlinarith [sq_nonneg (a - b), h1b]
      have h2b0 : (0 : ℝ) ≤ 2 * |b| := by positivity
      have hmul := mul_le_mul_of_nonneg_left herr h2b0
      linarith [hstep, hmul]
    -- Step 2 + assembly, divided through by `Φ > 0`
    have heq : b ^ 2 / Φ - K * (|b| / Φ)
        = (b ^ 2 - 2 * |b| * (C * Real.log R / (D₀ k : ℝ))) / Φ := by
      rw [sub_div, hKdef]; ring
    have hle1 : (b ^ 2 - 2 * |b| * (C * Real.log R / (D₀ k : ℝ))) / Φ ≤ a ^ 2 / Φ :=
      (div_le_div_iff_of_pos_right hΦpos).mpr hsqb
    have hle2 : a ^ 2 / Φ ≤ G * V ^ 2 := by
      rw [hyMsq, div_le_iff₀ hΦpos]
      nlinarith [mul_nonneg (mul_nonneg hGpos.le (sq_nonneg V)) (sub_nonneg.mpr hGleΦ)]
    rw [heq]; exact le_trans hle1 hle2
  -- rewrite `M − K·S` as the per-`u` sum, then close with `hmain`
  have hrw' :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∑ am ∈ Finset.range R,
              y (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        - K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            |∑ am ∈ Finset.range R,
                y (Function.update u m am) / (Nat.totient am : ℝ)|
              / ∏ i, (Nat.totient (u i) : ℝ)
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              y (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * (|∑ am ∈ Finset.range R,
                      y (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [ge_iff_le, s2_diag_lam_restricted k R (W k) m y, hrw']
  exact hmain

end Salt.Maynard
