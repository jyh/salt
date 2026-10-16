/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.Ratio54
import Salt.MaynardK.BridgeM

/-!
# C1 · A2d (f) — the normalised weight `F54 = F / Qsum54`

`Qsum54 = Σ |c|` over the 1236-term coefficient list `cs54`, `F54 := scale (1/Qsum54) (FpolyM 13
54 cs54)` (the `k = 105` pattern `F1`). On the simplex `|F54| ≤ 1`; its two Dirichlet integrals
are the forms over `Qsum54²` (through `IformM_eq` and `JformM_eq`, with the basis facts
`basisEvalM_holds`, `basisIntM_holds`). `Qsum54 > 0` because a zero coefficient list has
`Iform54 = 0`, against `Iform54_pos`: no coefficient is read. Nothing here bears on twin primes.
-/

open Finset Salt.Twelve

open scoped Nat

namespace SaltC1.MaynardK

open Salt.MaynardK SaltC1.Cert54

/-- The `ℓ¹` norm of the `k = 54` coefficient list. -/
noncomputable def Qsum54 : ℚ := (cs54.map fun x => |(x.2 : ℚ)|).sum

lemma eq_zero_of_sum_eq_zero (l : List ℚ) (h : ∀ y ∈ l, 0 ≤ y) (hs : l.sum = 0) :
    ∀ y ∈ l, y = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons] at hs
    have hx := h x List.mem_cons_self
    have hl := List.sum_nonneg fun y hy => h y (List.mem_cons_of_mem _ hy)
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · linarith
    · exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by linarith) y hy

theorem Qsum54_pos : 0 < Qsum54 := by
  have hnn : ∀ y ∈ cs54.map (fun x => |(x.2 : ℚ)|), 0 ≤ y := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact abs_nonneg _
  rcases (List.sum_nonneg hnn).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := eq_zero_of_sum_eq_zero _ hnn h.symm
    have hc : ∀ x ∈ cs54, (x.2 : ℚ) = 0 := fun x hx =>
      abs_eq_zero.mp (hz _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
    have hI : Iform54 = 0 := by
      unfold Iform54 IformM
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      refine List.sum_eq_zero fun z hz' => ?_
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz'
      push_cast
      rw [hc x hx]
      ring
    have := Iform54_pos
    rw [hI] at this
    exact lt_irrefl _ this

/-- The normalised `k = 54` Maynard weight. -/
noncomputable def F54 : BPoly 54 := scale (1 / Qsum54) (FpolyM 13 54 cs54)

/-- **`|F54| ≤ 1` on the simplex.** -/
theorem eval_F54_abs_le_one (t : Fin 54 → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ≤ 1) :
    |eval F54 t| ≤ 1 := by
  unfold F54
  rw [eval_scale, abs_mul]
  have hQpos : (0 : ℝ) < (Qsum54 : ℝ) := by exact_mod_cast Qsum54_pos
  have hb := eval_FpolyM_abs_le (basisEvalM_holds 13 54) cs54 t ht0 ht1
  have hQ : ((QsumM cs54 : ℚ) : ℝ) = (Qsum54 : ℝ) := rfl
  rw [hQ] at hb
  push_cast
  rw [abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ hQpos, mul_one]
  exact hb

theorem simplexInt_sq_F54 : simplexInt (sq F54) = Iform54 / Qsum54 ^ 2 := by
  have hQ : Qsum54 ≠ 0 := Qsum54_pos.ne'
  unfold F54 Iform54
  rw [simplexInt_sq_scale, simplexInt_sq_FpolyM, ← IformM_eq (basisIntM_holds 13 54)]
  field_simp

theorem simplexInt_sq_contractB_F54 (m : Fin 54) :
    simplexInt (sq (contractB m F54)) = Jform54 / Qsum54 ^ 2 := by
  have hQ : Qsum54 ≠ 0 := Qsum54_pos.ne'
  unfold F54 Jform54
  rw [contractB_scale (n := 53), simplexInt_sq_scale,
    ← JformM_eq (M := 13) (n := 53) (basisIntM_holds 13 53) m cs54]
  field_simp

end SaltC1.MaynardK
