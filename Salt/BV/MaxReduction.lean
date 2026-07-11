/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.BDHPrep

/-!
# V1a — the max-reduction (`Salt/BV/MaxReduction.lean`)

Design: `docs/blueprints/bv.md`, node `V1a`. Bridges the L8.3
(`psiChi_eq_sum_psiAP`) character expansion "the other way": instead of
expressing `ψ(x,χ)` as a sum over reduced residues, we invert it to express
`ψ(x;q,a)` (for a single reduced `a`) as a character average, isolate the
principal-character mean term, and bound the remainder by the triangle
inequality. The resulting bound is *a-free* on the right, which is exactly
what lets the maximum over reduced residues `a` obey the same bound.

Route:
1. `key`: for reduced `a`, `∑_χ χ(a⁻¹) · ψ(x,χ) = ψ(x;q,a) · φ(q)`. Proof:
   expand each `ψ(x,χ)` via `psiChi_eq_sum_psiAP`, swap the double sum,
   collapse the inner `∑_χ χ(a⁻¹)·χ(b)` via mathlib's
   `DirichletCharacter.sum_char_inv_mul_char_eq` (an off-the-shelf inversion
   form of the orthogonality relation `BDHPrep`'s `double_sum_key` derives
   by hand — no need to re-derive the `conj`/`χ⁻¹` bridge here), then collapse
   the resulting `b`-sum to the single `b = a` term.
2. Split the `χ = 1` (principal) term off the sum via `Finset.sum_erase_eq_sub`
   (`(1 : DirichletCharacter ℂ q) (a⁻¹) = 1` since `a⁻¹` is a unit,
   `MulChar.one_apply`), giving
   `∑_{χ≠1} χ(a⁻¹)·ψ(x,χ) = ψ(x;q,a)·φ(q) − ψ(x,χ₀)`.
3. Divide by `φ(q)` and take norms: `‖χ(a⁻¹)‖ ≤ 1`
   (`DirichletCharacter.norm_le_one`) turns the triangle inequality into the
   a-free bound `‖ψ(x;q,a) − ψ(x,χ₀)/φ(q)‖ ≤ (1/φ(q))·∑_{χ≠χ₀} ‖ψ(x,χ)‖`.

Packaging: stated over `ℂ` (matching `variance_eq`'s style in `BDHPrep`,
since the χ₀-mean term is genuinely ℂ-valued while `psiAP` is ℝ-valued) —
this is the RECOMMENDED packaging from the node brief. The a-freeness of the
RHS is the point of the node: the corollary `psiAP_discrepancy_sup'_le`
records that the `Finset.sup'` over reduced `a` obeys the identical bound.
-/

namespace Salt.BV

open Finset Salt.LS

/-- **V1a (max-reduction), single-residue form.** For `q ≥ 1` and reduced `a
< q`, the discrepancy of `ψ(x;q,a)` from the principal-character mean
`ψ(x,χ₀)/φ(q)` is bounded by `(1/φ(q))` times the non-principal character
energy — an *a-free* right-hand side. Route: invert `psiChi_eq_sum_psiAP` by
multiplying by `χ(a⁻¹)` and summing over `χ`, apply
`DirichletCharacter.sum_char_inv_mul_char_eq` to collapse the orthogonality
sum, isolate the `χ = 1` term, then the triangle inequality with
`‖χ(a⁻¹)‖ ≤ 1`. -/
theorem psiAP_discrepancy_le {q : ℕ} [NeZero q] (x : ℕ) {a : ℕ}
    (ha : a < q) (hcop : Nat.Coprime q a) :
    ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖ ≤
      (1 / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ := by
  set S := (Finset.range q).filter (Nat.Coprime q) with hS
  have haS : a ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨ha, hcop⟩
  have hau : IsUnit (a : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]; exact hcop.symm
  have hauinv : IsUnit ((a : ZMod q)⁻¹) := by
    rw [isUnit_iff_exists]
    exact ⟨a, ZMod.inv_mul_of_unit _ hau, ZMod.mul_inv_of_unit _ hau⟩
  have htot_pos : (0 : ℝ) < (q.totient : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast this
  have htot_ne : (q.totient : ℂ) ≠ 0 := by
    have h : (q.totient : ℝ) ≠ 0 := ne_of_gt htot_pos
    exact_mod_cast h
  -- Step 1: invert the `psiChi_eq_sum_psiAP` expansion via orthogonality.
  have key : ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * psiChi x χ
      = (psiAP x q a : ℂ) * (q.totient : ℂ) := by
    calc ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * psiChi x χ
        = ∑ χ : DirichletCharacter ℂ q,
            χ (a : ZMod q)⁻¹ * ∑ b ∈ S, χ (b : ZMod q) * (psiAP x q b : ℂ) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [psiChi_eq_sum_psiAP x χ]
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ b ∈ S,
            (psiAP x q b : ℂ) * (χ (a : ZMod q)⁻¹ * χ (b : ZMod q)) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
      _ = ∑ b ∈ S, (psiAP x q b : ℂ) * ∑ χ : DirichletCharacter ℂ q,
            χ (a : ZMod q)⁻¹ * χ (b : ZMod q) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ b ∈ S, (psiAP x q b : ℂ) *
            (if (a : ZMod q) = (b : ZMod q) then (q.totient : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hau (b : ZMod q)]
      _ = ∑ b ∈ S, (psiAP x q b : ℂ) * (if a = b then (q.totient : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun b hb => ?_)
          have hbb : b < q := Finset.mem_range.mp (Finset.mem_filter.mp (hS ▸ hb)).1
          have hcongr : ((a : ZMod q) = (b : ZMod q)) = (a = b) := by
            rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hbb]
          simp only [hcongr]
      _ = (psiAP x q a : ℂ) * (q.totient : ℂ) := by
          rw [Finset.sum_eq_single a
            (fun b _ hne => by rw [if_neg (Ne.symm hne), mul_zero])
            (fun h => absurd haS h)]
          simp
  -- Step 2: split off the principal character, isolating the mean.
  have hone : (1 : DirichletCharacter ℂ q) (a : ZMod q)⁻¹ = 1 := MulChar.one_apply hauinv
  have split : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ (a : ZMod q)⁻¹ * psiChi x χ
      = (psiAP x q a : ℂ) * (q.totient : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : DirichletCharacter ℂ q)), key, hone, one_mul]
  -- Step 3: divide by `φ(q)` and bound by the triangle inequality.
  have hdiv : (psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)
      = (1 / (q.totient : ℂ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            χ (a : ZMod q)⁻¹ * psiChi x χ := by
    rw [split]
    field_simp
  rw [hdiv, norm_mul]
  have hnormfac : ‖(1 / (q.totient : ℂ))‖ = 1 / (q.totient : ℝ) := by
    rw [norm_div, norm_one]
    congr 1
    exact Complex.norm_natCast q.totient
  rw [hnormfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun χ _ => ?_)
  calc ‖χ (a : ZMod q)⁻¹ * psiChi x χ‖
      = ‖χ (a : ZMod q)⁻¹‖ * ‖psiChi x χ‖ := norm_mul _ _
    _ ≤ 1 * ‖psiChi x χ‖ :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
    _ = ‖psiChi x χ‖ := one_mul _

/-- **V1a corollary (a-freeness).** The maximum discrepancy over all reduced
residues `a < q` obeys the same bound as the single-residue form
`psiAP_discrepancy_le`, since its right-hand side does not depend on `a`. -/
theorem psiAP_discrepancy_sup'_le {q : ℕ} [NeZero q] (x : ℕ)
    (hne : ((Finset.range q).filter (Nat.Coprime q)).Nonempty) :
    ((Finset.range q).filter (Nat.Coprime q)).sup' hne
        (fun a => ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖)
      ≤ (1 / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ := by
  refine Finset.sup'_le hne _ (fun a ha => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at ha
  exact psiAP_discrepancy_le x ha.1 ha.2

end Salt.BV
