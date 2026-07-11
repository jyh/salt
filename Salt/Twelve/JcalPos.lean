/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.FstarNorm

/-!
# Rung 4a — R1a: positivity of `Jcal m Fstar1` (`Salt/Twelve/JcalPos.lean`)

The ℓ¹-normalized certificate `Fstar1` (`Salt.Twelve.FstarNorm`) transports the
per-`m` sieve moment `Jcal m Fstar` by the positive scale factor
`(Qabs Fstar)⁻²`: since `Qabs Fstar = 1227` (`Qabs_Fstar_eq`) and
`Jcal m Fstar = 191881/119750400` for each concrete `m` (`J_Fstar_0` ..
`J_Fstar_4`, `Salt.Twelve.Certificate`), the closed form is
`Jcal m Fstar1 = 191881/119750400 · (1/1227)²`, manifestly positive.

The scaling lemmas `Jcal_scale`/`Fstar1_eq_scale` (`Salt.Twelve.FstarNorm`) are
`private` there, so this file replicates the short `biQuad`-homogeneity chain
locally (suffix `P`) rather than editing that module.
-/

namespace Salt.Twelve

/-! ## Local replica of the `biQuad` homogeneity chain (private in `FstarNorm`) -/

private def biQuadP (ker : (Fin 5 → ℕ) → (Fin 5 → ℕ) → ℚ) (F : Poly) : ℚ :=
  (F.map (fun p => (F.map (fun q => p.2 * q.2 * ker p.1 q.1)).sum)).sum

private lemma Jcal_eq_biQuadP (m : Fin 5) (F : Poly) :
    Jcal m F = biQuadP (fun a b => JD a b m) F := rfl

private lemma biQuadP_scale (ker : (Fin 5 → ℕ) → (Fin 5 → ℕ) → ℚ) (F : Poly) (c : ℚ) :
    biQuadP ker (F.map (fun m => (m.1, m.2 * c))) = c ^ 2 * biQuadP ker F := by
  unfold biQuadP
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  dsimp only [Function.comp]
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  dsimp only [Function.comp]
  ring

private lemma Jcal_scaleP (m : Fin 5) (F : Poly) (c : ℚ) :
    Jcal m (F.map (fun n => (n.1, n.2 * c))) = c ^ 2 * Jcal m F := by
  rw [Jcal_eq_biQuadP, Jcal_eq_biQuadP]
  exact biQuadP_scale _ F c

private lemma Fstar1_eq_scaleP :
    Fstar1 = Fstar.map (fun m => (m.1, m.2 * (Qabs Fstar)⁻¹)) := by
  unfold Fstar1
  simp only [div_eq_mul_inv]

/-! ## `Jcal m Fstar1` -/

private lemma Jcal_Fstar1_scale (m : Fin 5) :
    Jcal m Fstar1 = ((Qabs Fstar)⁻¹) ^ 2 * Jcal m Fstar := by
  rw [Fstar1_eq_scaleP]; exact Jcal_scaleP m Fstar _

/-- The closed-form value of the per-`m` sieve moment at the ℓ¹-normalized
certificate `Fstar1`: transported from `Jcal m Fstar = 191881/119750400`
(`J_Fstar_0` .. `J_Fstar_4`) by the scale factor `(Qabs Fstar)⁻² = (1/1227)²`
(`Qabs_Fstar_eq`). -/
theorem Jcal_Fstar1_eq (m : Fin 5) :
    Jcal m Fstar1 = 191881 / 119750400 * (1 / 1227) ^ 2 := by
  rw [Jcal_Fstar1_scale, Qabs_Fstar_eq]
  match m with
  | 0 => rw [J_Fstar_0]; norm_num
  | 1 => rw [J_Fstar_1]; norm_num
  | 2 => rw [J_Fstar_2]; norm_num
  | 3 => rw [J_Fstar_3]; norm_num
  | 4 => rw [J_Fstar_4]; norm_num

/-- `Jcal m Fstar1` is strictly positive for every `m`. -/
theorem Jcal_Fstar1_pos (m : Fin 5) : 0 < Jcal m Fstar1 := by
  rw [Jcal_Fstar1_eq]; norm_num

end Salt.Twelve
