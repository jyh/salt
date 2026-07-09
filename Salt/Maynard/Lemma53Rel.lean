/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.VAbs
import Salt.Maynard.S2Tensor
import Salt.Maynard.Transfer

/-!
# Lemma 5.3, relative form (`lemma53_rel`) — the fifth-fragility fix

Design: `docs/blueprints/endgame-design.md`, Fix P1.  The landed `lemma53`
gives the *absolute* contraction error `|yM(v) − contraction(v)| ≤ C·logR/D₀`
for any unit-bounded `y`.  For the concrete tensor `y = yTensor`, the error is
in fact *relative*: it carries the tensor weight `∏_{i≠m} fTilde(vᵢ)`.  Without
this, the downstream `s2main_lower` error term is B-type (`~B₁^k`) and swamps
the main `(1/4)B₁²A₁^{k−1}`; the `∏fTilde` factor makes it A-type.

The proof is a rescaling: apply `lemma53` to
`z(a) := if (∀i, vᵢ ∣ aᵢ) then yTensor(a)/P else 0` where `P := ∏_{i≠m} fTilde(vᵢ)`.
On the divisibility fibre — exactly where `lamPhiContractM`'s collapse reads
`y(a)` and where the contraction lives — `z = y/P`, so both `yM` and the
contraction scale by `1/P`; multiplying `lemma53`'s bound by `P` gives the
relative bound.  When `P = 0` (some `fTilde(vᵢ) = 0`), both `yM(v)` and the
contraction vanish outright.
-/

namespace Salt.Maynard

open Finset ArithmeticFunction

/-- `fTilde ≤ 1`: on `sqfCop` it is `fWt ≤ 1` (`fWt_le_one`, using squarefree ⟹
`≥ 1`); off it, `0 ≤ 1`. -/
lemma fTilde_le_one (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) (n : ℕ) : fTilde k R T n ≤ 1 := by
  simp only [fTilde]
  split_ifs with hn
  · have hsq : Squarefree n := by
      rw [sqfCop, Finset.mem_filter] at hn; exact hn.2.1
    exact fWt_le_one (Nat.one_le_iff_ne_zero.mpr hsq.ne_zero) hR
  · exact zero_le_one

/-- `0 ≤ yTensor` everywhere. -/
lemma yTensor_nonneg (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) (s : Fin k → ℕ) :
    0 ≤ yTensor k R T s := by
  simp only [yTensor]
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
  · exact le_rfl

/-- **Fix P1 — Lemma 5.3, relative form.** For the tensor `y = yTensor` and any
`v` with `vₘ = 1` in `𝒟`, the contraction error carries the tensor weight
`∏_{i≠m} fTilde(vᵢ)`. -/
theorem lemma53_rel (k R : ℕ) (T : ℝ) (m : Fin k)
    (v : Fin k → ℕ) (hvm : v m = 1) (hR : 2 ≤ R)
    (hvsupp : v ∈ kSieveIndex k R (W k)) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      |yM k R (W k) m (yTensor k R T) v
          - ∑ am ∈ Finset.range R,
              yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)|
        ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (v i))
            * (C * Real.log R / (D₀ k : ℝ)) := by
  classical
  set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (v i) with hPdef
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
  by_cases hP0 : P = 0
  · -- degenerate: some `fTilde(v i₀) = 0`, so both `yM(v)` and the contraction vanish.
    obtain ⟨i₀, hi₀mem, hi₀0⟩ := Finset.prod_eq_zero_iff.mp hP0
    have hi₀ne : i₀ ≠ m := Finset.ne_of_mem_erase hi₀mem
    have hyM0 : yM k R (W k) m (yTensor k R T) v = 0 := by
      have hV0 : lamPhiContractM k R (W k) m (yTensor k R T) v = 0 := by
        rw [lamPhiContractM_collapse k R (W k) m (yTensor k R T) v hvm]
        apply Finset.sum_eq_zero
        intro a ha
        by_cases hcond : ∀ i, v i ∣ a i
        · rw [if_pos hcond]
          have hya : yTensor k R T a = 0 := by
            simp only [yTensor, if_pos ha]
            refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
            have hpos : 0 < a i₀ :=
              Nat.pos_of_ne_zero (((mem_kSieveIndex_iff a).mp ha).1 i₀).ne_zero
            have hle : fTilde k R T (a i₀) ≤ fTilde k R T (v i₀) :=
              fTilde_anti k R T hR (v i₀) (a i₀) hpos (hcond i₀)
            rw [hi₀0] at hle
            exact le_antisymm hle (fTilde_nonneg k R T _ hR)
          rw [hya]; ring
        · rw [if_neg hcond]
      simp only [yM, hV0, mul_zero]
    have hC0sum : (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro am _
      have hya : yTensor k R T (Function.update v m am) = 0 := by
        simp only [yTensor]
        split_ifs with hmem
        · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
          rw [Function.update_of_ne hi₀ne]; exact hi₀0
        · rfl
      rw [hya, zero_div]
    exact ⟨0, le_rfl, by rw [hyM0, hC0sum]; simp⟩
  · -- `P > 0`: rescale.  `z = y/P` on the fibre `{a : ∀i, vᵢ ∣ aᵢ}`, `0` off it.
    have hP : 0 < P := lt_of_le_of_ne hPnn (Ne.symm hP0)
    set z : (Fin k → ℕ) → ℝ :=
      fun a => if (∀ i, v i ∣ a i) then yTensor k R T a / P else 0 with hzdef
    have hza : ∀ a, z a = if (∀ i, v i ∣ a i) then yTensor k R T a / P else 0 :=
      fun a => rfl
    -- (1) `|z| ≤ 1`.
    have hy1 : ∀ s, |z s| ≤ 1 := by
      intro s
      rw [hza s]
      split_ifs with hcond
      · rw [abs_div, abs_of_pos hP, div_le_one hP,
          abs_of_nonneg (yTensor_nonneg k R T hR s)]
        -- `yTensor s ≤ P` under the divisibility hypothesis `hcond`.
        simp only [yTensor]
        split_ifs with hmem
        · have hsq : ∀ i, Squarefree (s i) := fun i => ((mem_kSieveIndex_iff s).mp hmem).1 i
          calc ∏ i, fTilde k R T (s i)
              = fTilde k R T (s m) * ∏ i ∈ Finset.univ.erase m, fTilde k R T (s i) :=
                (Finset.mul_prod_erase Finset.univ (fun i => fTilde k R T (s i))
                  (Finset.mem_univ m)).symm
            _ ≤ 1 * ∏ i ∈ Finset.univ.erase m, fTilde k R T (v i) := by
                refine mul_le_mul (fTilde_le_one k R T hR (s m)) ?_
                  (Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)) zero_le_one
                refine Finset.prod_le_prod (fun i _ => fTilde_nonneg k R T _ hR) ?_
                intro i _
                exact fTilde_anti k R T hR (v i) (s i)
                  (Nat.pos_of_ne_zero (hsq i).ne_zero) (hcond i)
            _ = P := by rw [one_mul, hPdef]
        · exact hPnn
      · simp
    -- (2) support.
    have hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → z s = 0 := by
      intro s hs
      rw [hza s]
      split_ifs with hcond
      · rw [show yTensor k R T s = 0 by simp only [yTensor]; rw [if_neg hs], zero_div]
      · rfl
    -- (3) `lamPhiContractM` scales by `1/P` on the fibre.
    have hV : lamPhiContractM k R (W k) m z v
        = lamPhiContractM k R (W k) m (yTensor k R T) v / P := by
      rw [lamPhiContractM_collapse k R (W k) m z v hvm,
          lamPhiContractM_collapse k R (W k) m (yTensor k R T) v hvm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hcond : ∀ i, v i ∣ a i
      · rw [if_pos hcond, if_pos hcond, hza a, if_pos hcond]; ring
      · rw [if_neg hcond, if_neg hcond, zero_div]
    have hyM : yM k R (W k) m z v = yM k R (W k) m (yTensor k R T) v / P := by
      simp only [yM]; rw [hV]; ring
    -- (4) the contraction scales by `1/P`.
    have hContr : (∑ am ∈ Finset.range R, z (Function.update v m am) / (Nat.totient am : ℝ))
        = (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)) / P := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro am _
      have hcond : ∀ i, v i ∣ (Function.update v m am) i := by
        intro i
        by_cases hi : i = m
        · subst hi; rw [Function.update_self, hvm]; exact one_dvd _
        · rw [Function.update_of_ne hi]
      rw [hza (Function.update v m am), if_pos hcond]; ring
    -- assemble.
    obtain ⟨C, hC0, hbound⟩ := lemma53 k R m z hy1 hysupp v hvm hR hvsupp hk hD
    refine ⟨C, hC0, ?_⟩
    rw [hyM, hContr, ← sub_div, abs_div, abs_of_pos hP, div_le_iff₀ hP] at hbound
    calc |yM k R (W k) m (yTensor k R T) v
            - ∑ am ∈ Finset.range R,
                yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)|
        ≤ C * Real.log R / (D₀ k : ℝ) * P := hbound
      _ = P * (C * Real.log R / (D₀ k : ℝ)) := by ring

end Salt.Maynard
