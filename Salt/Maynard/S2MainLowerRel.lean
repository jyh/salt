/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2MainLower
import Salt.Maynard.Lemma53Rel
import Salt.Maynard.EulerTailL
import Salt.Maynard.S2Eh

/-!
# The S₂ main lower bound with the *relative* contraction error (fifth-fragility fix)

`s2main_lower` (Salt/Maynard/S2MainLower.lean) proves, for the concrete tensor
`y = yTensor`, the diagonal lower bound

  `Qdiag_m ≥ MAIN − (2C·logR/D₀) · ∑_u |contraction u| / ∏φ(uᵢ)`

but with the *absolute* per-`u` error of `lemma53`.  For `yTensor` the error is
in fact *relative* (`lemma53_rel`): it carries the tensor weight
`P_u := ∏_{i≠m} fTilde(uᵢ)`.  Threading that factor through and bounding the
resulting error box A-type (steps 1–3 of the design) yields

  `Qdiag_m ≥ MAIN − (2C·logR/D₀) · B₁ · (2·A₁^{k−1})`,

where `MAIN = ∑_{u:uₘ=1} (contraction u)² / ∏ᵢ φ(uᵢ)`.  The error term now
carries the `∏fTilde` (`P_u`) factor everywhere, making the box A-type
(`B₁·A₁^{k−1}`) rather than the B-type `B₁^k` that would swamp the main term.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-- `∑_{a<R} fTilde(a)/φ(a) ≤ B₁`: `fTilde = fWt` on `sqfCop(R₀,W)` and `0` off
it, and the box `sqfCop(R₀,W)` may only contribute a subset of `range R` (all
terms nonnegative). -/
private lemma sumFTilde_le_B1 (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) :
    (∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ)) ≤ B1 k R (W k) T := by
  classical
  have hfe : ∀ am : ℕ, fTilde k R T am / (Nat.totient am : ℝ)
      = if am ∈ sqfCop (R0 k R T) (W k) then fWt k R am / (Nat.totient am : ℝ) else 0 := by
    intro am
    simp only [fTilde]
    split_ifs <;> simp
  have hrewrite : (∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ))
      = ∑ am ∈ Finset.range R,
          if am ∈ sqfCop (R0 k R T) (W k) then fWt k R am / (Nat.totient am : ℝ) else 0 :=
    Finset.sum_congr rfl (fun am _ => hfe am)
  rw [hrewrite, ← Finset.sum_filter]
  unfold B1
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro am ham
    rw [Finset.mem_filter] at ham
    exact ham.2
  · intro am ham _
    have hr : 1 ≤ am := by
      rw [sqfCop, Finset.mem_filter] at ham
      exact Nat.one_le_iff_ne_zero.mpr ham.2.1.ne_zero
    exact div_nonneg (fWt_nonneg hr hR) (Nat.cast_nonneg _)

/-- Pointwise: `yTensor(update u m a) ≤ fTilde(a) · ∏_{i≠m} fTilde(uᵢ)` — the
`m`-coordinate contributes `fTilde(a)`, the `i≠m` coordinates `fTilde(uᵢ)`, and
dropping the `𝒟` indicator only loses (nonnegative) mass. -/
private lemma yTensor_update_le (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) (am : ℕ) :
    yTensor k R T (Function.update u m am)
      ≤ fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
  have hprodeq : (∏ i, fTilde k R T ((Function.update u m am) i))
      = fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => fTilde k R T ((Function.update u m am) i)) (Finset.mem_univ m)]
    rw [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [yTensor]
  split_ifs with hmem
  · exact le_of_eq hprodeq
  · exact mul_nonneg (fTilde_nonneg k R T am hR)
      (Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR))

/-- The contraction `∑_{a<R} yTensor(update u m a)/φ(a)` is nonnegative. -/
private lemma contraction_nonneg (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) :
    0 ≤ ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) := by
  apply Finset.sum_nonneg
  intro am _
  exact div_nonneg (yTensor_nonneg k R T hR _) (Nat.cast_nonneg _)

/-- The contraction is `≤ P_u · B₁` for the tensor, where
`P_u = ∏_{i≠m} fTilde(uᵢ)`. -/
private lemma contraction_le (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) :
    (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i)) * B1 k R (W k) T := by
  set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hP
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
  calc (∑ am ∈ Finset.range R,
          yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      ≤ ∑ am ∈ Finset.range R, (fTilde k R T am * P) / (Nat.totient am : ℝ) := by
        apply Finset.sum_le_sum
        intro am _
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (yTensor_update_le k R T m hR u am)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = P * ∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro am _
        rw [mul_comm (fTilde k R T am) P, mul_div_assoc]
    _ ≤ P * B1 k R (W k) T :=
        mul_le_mul_of_nonneg_left (sumFTilde_le_B1 k R T hR) hPnn

/-- **The error box is A-type.** The relative error box
`∑_{u:uₘ=1} P_u·|contraction u| / ∏ᵢ φ(uᵢ)` is bounded by `B₁·(2·A₁^{k−1})`.
Steps: `|contraction u| = contraction u ≤ P_u·B₁`; `∏ᵢφ = ∏_{i≠m}φ` (`uₘ=1`) and
`P_u² = ∏_{i≠m}fTilde²`; `1/φ ≤ 1/g` per coordinate (`gMult_le_totient`) collapses
the fibre to `Gdiag ≤ 2·A₁^{k−1}` (`Gdiag_le`). -/
private lemma errbox_le (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (hD : 12 * k ^ 2 ≤ D₀ k) :
    (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
          * |∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≤ B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1)) := by
  classical
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k m.pos
  have hD12 : 12 ≤ D₀ k := by omega
  have hB1nn : 0 ≤ B1 k R (W k) T := B1_nonneg k R (W k) T hR
  have hclaimA : ∀ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
      (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
        * |∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
        / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ B1 k R (W k) T
          * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    have hsq : ∀ i, Squarefree (u i) := fun i => ((mem_kSieveIndex_iff u).mp husupp).1 i
    have hodd : ∀ i, ∀ p ∈ (u i).primeFactors, 3 ≤ p := by
      intro i p hp
      have := D₀_lt_of_prime_dvd_coord husupp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    have hgpos : ∀ i, 0 < (gMult (u i) : ℝ) := by
      intro i
      have hpos : 0 < gMult (u i) := by
        rw [gMult]; apply Finset.prod_pos; intro p hp; have := hodd i p hp; omega
      exact_mod_cast hpos
    have hφpos : ∀ i, 0 < (Nat.totient (u i) : ℝ) := by
      intro i; exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos husupp i)
    set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
    have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
    set Φ := ∏ i, (Nat.totient (u i) : ℝ) with hΦdef
    have hΦpos : 0 < Φ := Finset.prod_pos (fun i _ => hφpos i)
    have hbnn := contraction_nonneg k R T m hR u
    have hble := contraction_le k R T m hR u
    set b := ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) with hbdef
    rw [abs_of_nonneg hbnn]
    have hΦerase : Φ = ∏ i ∈ Finset.univ.erase m, (Nat.totient (u i) : ℝ) := by
      rw [hΦdef, ← Finset.mul_prod_erase Finset.univ
        (fun i => (Nat.totient (u i) : ℝ)) (Finset.mem_univ m), hum]
      simp
    have hP2Φ : P ^ 2 / Φ
        = ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
      rw [hPdef, hΦerase, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    calc P * b / Φ
        = (P / Φ) * b := by ring
      _ ≤ (P / Φ) * (P * B1 k R (W k) T) :=
          mul_le_mul_of_nonneg_left hble (div_nonneg hPnn hΦpos.le)
      _ = B1 k R (W k) T * (P ^ 2 / Φ) := by ring
      _ = B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
          rw [hP2Φ]
      _ ≤ B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hB1nn
          apply Finset.prod_le_prod
          · intro i _; exact div_nonneg (sq_nonneg _) (hφpos i).le
          · intro i _
            exact div_le_div_of_nonneg_left (sq_nonneg _) (hgpos i)
              (gMult_le_totient (hsq i) (hodd i))
  calc (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * |∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
            / ∏ i, (Nat.totient (u i) : ℝ))
      ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) :=
        Finset.sum_le_sum hclaimA
    _ = B1 k R (W k) T
          * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
              ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
        rw [← Finset.mul_sum]
    _ = B1 k R (W k) T * Gdiag k R T m := by simp only [Gdiag]
    _ ≤ B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left (Gdiag_le k R T m hR hD) hB1nn

/-- **S₂ main lower bound, relative form.** For the concrete tensor `yTensor`, the
`dₘ=eₘ=1`-restricted S₂ diagonal `Qdiag_m` is lower-bounded by the `φ`-denominator
contraction main term minus an error whose box factor is the *A-type*
`B₁·(2·A₁^{k−1})` (carrying the `∏fTilde` weight from `lemma53_rel`), not the
`B-type` `B₁^k` of the absolute `s2main_lower`. -/
theorem s2main_lower_rel (k R : ℕ) (m : Fin k) (T : ℝ)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      Qdiag_m k R m (yTensor k R T)
        ≥ (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
             (∑ am ∈ Finset.range R,
                 yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
               / ∏ i, (Nat.totient (u i) : ℝ))
          - (2 * C * Real.log R / (D₀ k : ℝ)) * (B1 k R (W k) T)
              * (2 * (A1 k R (W k) T) ^ (k - 1)) := by
  classical
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D₀ k := by omega
  have hD0pos : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0pos
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ R)
  have hlognn : 0 ≤ Real.log R := Real.log_nonneg hR1
  have mono : ∀ {c c' : ℝ}, c ≤ c' →
      c * Real.log R / (D₀ k : ℝ) ≤ c' * Real.log R / (D₀ k : ℝ) := by
    intro c c' h; gcongr
  -- a uniform *relative* `lemma53_rel` constant over any finite set of tuples
  have gen_rel : ∀ (s : Finset (Fin k → ℕ)),
      (∀ u ∈ s, ∃ C, 0 ≤ C ∧
        |yM k R (W k) m (yTensor k R T) u
            - ∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
          ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * (C * Real.log R / (D₀ k : ℝ))) →
      ∃ C, 0 ≤ C ∧ ∀ u ∈ s,
        |yM k R (W k) m (yTensor k R T) u
            - ∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
          ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * (C * Real.log R / (D₀ k : ℝ)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _; exact ⟨0, le_refl 0, fun u hu => absurd hu (by simp)⟩
    · intro a₀ t ha₀ ih hall
      obtain ⟨Ca, hCa0, hCa⟩ := hall a₀ (Finset.mem_insert_self a₀ t)
      obtain ⟨Ct, hCt0, hCtb⟩ := ih (fun u hu => hall u (Finset.mem_insert_of_mem hu))
      refine ⟨max Ca Ct, le_trans hCa0 (le_max_left _ _), fun u hu => ?_⟩
      have hPnn : 0 ≤ ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) :=
        Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
      rcases Finset.mem_insert.mp hu with rfl | hus
      · exact le_trans hCa (mul_le_mul_of_nonneg_left (mono (le_max_left _ _)) hPnn)
      · exact le_trans (hCtb u hus) (mul_le_mul_of_nonneg_left (mono (le_max_right _ _)) hPnn)
  obtain ⟨C, hC0, hspec⟩ := gen_rel ((kSieveIndex k R (W k)).filter (fun u => u m = 1)) (by
    intro u hu
    rw [Finset.mem_filter] at hu
    exact lemma53_rel k R T m u hu.2 hR hu.1 hk hD)
  refine ⟨C, hC0, ?_⟩
  set K := 2 * C * Real.log R / (D₀ k : ℝ) with hKdef
  -- per-`u` lower bound with the *relative* error (`P_u` factor threaded in)
  have hmain_rel :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * ((∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
                    * |∑ am ∈ Finset.range R,
                        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))))
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    apply Finset.sum_le_sum
    intro u hu
    have hmem := hu
    rw [Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff u).mp husupp
    have hodd : ∀ i, ∀ p ∈ (u i).primeFactors, 3 ≤ p := by
      intro i p hp
      have := D₀_lt_of_prime_dvd_coord husupp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    have hgcoord_pos : ∀ i, 0 < (gMult (u i) : ℝ) := by
      intro i
      have hpos : 0 < gMult (u i) := by
        rw [gMult]; apply Finset.prod_pos; intro p hp; have := hodd i p hp; omega
      exact_mod_cast hpos
    have hφcoord_pos : ∀ i, 0 < (Nat.totient (u i) : ℝ) := by
      intro i; exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos husupp i)
    set V := lamPhiContractM k R (W k) m (yTensor k R T) u with hVdef
    set G := ∏ i, (gMult (u i) : ℝ) with hGdef
    set Φ := ∏ i, (Nat.totient (u i) : ℝ) with hΦdef
    set a := yM k R (W k) m (yTensor k R T) u with hadef
    set b := ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) with hbdef
    set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
    have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
    have hGpos : 0 < G := Finset.prod_pos (fun i _ => hgcoord_pos i)
    have hΦpos : 0 < Φ := Finset.prod_pos (fun i _ => hφcoord_pos i)
    have hGleΦ : G ≤ Φ := by
      apply Finset.prod_le_prod
      · intro i _; exact (hgcoord_pos i).le
      · intro i _; exact gMult_le_totient (hsq i) (hodd i)
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
    have herr : |a - b| ≤ P * (C * Real.log R / (D₀ k : ℝ)) := hspec u hmem
    have hsqb : b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ))) ≤ a ^ 2 := by
      have h1b : -(|b| * |a - b|) ≤ b * (a - b) := by
        have := neg_abs_le (b * (a - b)); rwa [abs_mul] at this
      have hstep : b ^ 2 - 2 * |b| * |a - b| ≤ a ^ 2 := by
        nlinarith [sq_nonneg (a - b), h1b]
      have h2b0 : (0 : ℝ) ≤ 2 * |b| := by positivity
      have hmul := mul_le_mul_of_nonneg_left herr h2b0
      linarith [hstep, hmul]
    have heq : b ^ 2 / Φ - K * ((P * |b|) / Φ)
        = (b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ)))) / Φ := by
      rw [sub_div, hKdef]; ring
    have hle1 : (b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ)))) / Φ ≤ a ^ 2 / Φ :=
      (div_le_div_iff_of_pos_right hΦpos).mpr hsqb
    have hle2 : a ^ 2 / Φ ≤ G * V ^ 2 := by
      rw [hyMsq, div_le_iff₀ hΦpos]
      nlinarith [mul_nonneg (mul_nonneg hGpos.le (sq_nonneg V)) (sub_nonneg.mpr hGleΦ)]
    rw [heq]; exact le_trans hle1 hle2
  -- rewrite `MAIN − K·E` as the per-`u` sum
  have hrw' :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        - K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * |∑ am ∈ Finset.range R,
                  yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
              / ∏ i, (Nat.totient (u i) : ℝ)
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * ((∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
                    * |∑ am ∈ Finset.range R,
                        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- `Qdiag_m` = the diagonalised `∑_u (∏g)·V²`
  have hQ : Qdiag_m k R m (yTensor k R T)
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    unfold Qdiag_m
    exact s2_diag_lam_restricted k R (W k) m (yTensor k R T)
  have hE := errbox_le k R T m hR hD
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hlognn) hD0R.le
  have hcombine :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        - K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * |∑ am ∈ Finset.range R,
                  yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
              / ∏ i, (Nat.totient (u i) : ℝ)
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    rw [hrw']; exact hmain_rel
  rw [ge_iff_le, hQ]
  have hKE :
      K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * |∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
            / ∏ i, (Nat.totient (u i) : ℝ)
        ≤ K * (B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))) :=
    mul_le_mul_of_nonneg_left hE hK0
  have hassoc : K * B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))
      = K * (B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))) := by ring
  rw [hassoc]
  linarith [hcombine, hKE]

end Salt.Maynard
