/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.PsiDefs

/-!
# The SW rung, wave S0 — the Riesz carriers

Design: `docs/blueprints/sw.md`, wave S0 (the Fable Riesz amendment + error-#14
correction). This module lands the *carriers* the whole gate-discharging arc is
built on, together with the two structural facts S6 consumes.

* **The carriers.** `psi1Chi x χ = ∑_{n ≤ ⌊x⌋} Λ(n)·χ(n)·(x − n)` (the ℂ-valued
  character Riesz mean) and the real AP carrier
  `psi1AP x q a = ∑_{n ≤ ⌊x⌋, n ≡ a (q)} Λ(n)·(x − n)`. The `(x − n)₊` positive
  part of the Riesz kernel is enforced by the *range* `n ≤ ⌊x⌋₊`: for `x ≥ 0`,
  `n ≤ ⌊x⌋₊` gives `n ≤ x`, hence `x − n ≥ 0`, so the truncation is automatic and
  the summand is the plain `x − n`. Conventions (`Finset.Icc 1 ⌊x⌋₊`, residues via
  `n % q = a % q`) match `Salt.LS.psiAP` exactly — `psi1AP` is the Riesz-weighted
  refinement of the landed `psiAP`.

* **The orthogonality fold** (`psi1_fold`, the ψ₁-analog of the landed
  `MaxReduction` identity): for reduced `a`,
  `∑_χ χ̄(a)·psi1Chi x χ = φ(q)·psi1AP x q a`. This is the REAL carrier `psi1AP`
  extracted from the per-character `psi1Chi` bounds S5 produces — the algebraic
  half of S6's "orthogonality FIRST" order (error #14). Mechanism mirrors
  `Salt/BV/MaxReduction.lean`: invert the character expansion
  (`psi1Chi_eq_sum_psi1AP`), bridge `conj (χ a) = χ a⁻¹` for the unit `a`, and
  collapse via mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`.

* **The monotonicity / first-difference sandwich** (`psi1AP_sandwich`, the
  hypothesis S6's de-smoothing consumes): with the bridging def
  `psiAPr x q a := psiAP ⌊x⌋₊ q a` (the landed `psiAP` at the floor), for
  `0 ≤ x ≤ y`,
  `(y − x)·psiAPr x q a ≤ psi1AP y q a − psi1AP x q a ≤ (y − x)·psiAPr y q a`.
  The honest discrete identity behind it:
  `psi1AP y − psi1AP x = (y − x)·Σ_{n ≤ ⌊x⌋} Λ + Σ_{⌊x⌋ < n ≤ ⌊y⌋} Λ(n)(y − n)`;
  the remainder is `≥ 0` (nonneg `Λ`, `n ≤ y`) for the lower jaw and
  `≤ (y − x)·Σ_{⌊x⌋ < n ≤ ⌊y⌋} Λ` (since `n > x`) for the upper jaw. These two
  inequalities ARE the sandwich the A-tuned `h = x/(log x)^{A+2}` step plugs into.

* **The −L'/L identity** (`neg_logDeriv_LSeries_eq_LSeries_twist`): re-export of
  mathlib's `DirichletCharacter.LSeries_twist_vonMangoldt_eq` — on `Re s > 1`,
  `−L'/L(s, χ) = LSeries (χ·Λ) s`. S1 bridges `LSeries ↗χ` to the analytic
  continuation `LFunction χ` on `Re s > 1` for the contour work.

Contour conventions (for S1/S5): all vertical integrals are taken along the line
`Re s = c` with `c > 1`, oriented upward (`t : ℝ`, `s = c + i t`), the standard
Perron/Mellin orientation; the Riesz kernel `x^{s+1}/(s(s+1))` has `1/|s|²` decay
so these converge absolutely (no truncation bookkeeping).
-/

namespace Salt.SW

open Salt.LS ArithmeticFunction Finset ComplexConjugate

/-! ## 1. The carriers -/

/-- **The ℂ-valued character Riesz mean** `ψ₁(x, χ) = ∑_{n ≤ ⌊x⌋} Λ(n)·χ(n)·(x − n)`.
The `(x − n)₊` positive part is enforced by the range `n ≤ ⌊x⌋₊`. -/
noncomputable def psi1Chi {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n : ℂ) * χ (n : ZMod q) * ((x : ℂ) - n)

/-- **The real AP Riesz carrier** `ψ₁(x; q, a) = ∑_{n ≤ ⌊x⌋, n ≡ a (q)} Λ(n)·(x − n)`.
Residue convention (`n % q = a % q`) matches `Salt.LS.psiAP`. -/
noncomputable def psi1AP (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), vonMangoldt n * (x - n)

/-- **The floor bridge** `psiAPr x q a := psiAP ⌊x⌋₊ q a` — the landed
`Salt.LS.psiAP` evaluated at the integer floor `⌊x⌋₊`. This is the discrete
`ψ(x; q, a)`-level quantity the first-difference sandwich brackets. -/
noncomputable def psiAPr (x : ℝ) (q a : ℕ) : ℝ := psiAP ⌊x⌋₊ q a

/-! ## 2. The character expansion of the Riesz carrier -/

/-- **Riesz-carrier character expansion.** For any `χ : DirichletCharacter ℂ q`,
`ψ₁(x, χ) = ∑_{a reduced} χ(a)·ψ₁(x; q, a)`. Non-coprime residues drop out because
`χ` vanishes at non-units (`MulChar.map_nonunit`); the `Icc 1 ⌊x⌋₊` range is
fibered by `n % q`. This is the Riesz-weighted analog of `psiChi_eq_sum_psiAP`
(the `(x − n)` factor rides along the fibering unchanged). -/
theorem psi1Chi_eq_sum_psi1AP {q : ℕ} [NeZero q] (x : ℝ) (χ : DirichletCharacter ℂ q) :
    psi1Chi x χ
      = ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), χ (a : ZMod q) * (psi1AP x q a : ℂ) := by
  set S := (Finset.range q).filter (Nat.Coprime q) with hS
  have hmaps : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, n % q ∈ Finset.range q := fun n _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)))
  have step1 : psi1Chi x χ = ∑ a ∈ Finset.range q, χ (a : ZMod q) * (psi1AP x q a : ℂ) := by
    rw [psi1Chi, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun n => (vonMangoldt n : ℂ) * χ (n : ZMod q) * ((x : ℂ) - n))]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' : a % q = a := Nat.mod_eq_of_lt (Finset.mem_range.mp ha)
    have hcast : (psi1AP x q a : ℂ) = ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a),
        (vonMangoldt n : ℂ) * ((x : ℂ) - n) := by
      unfold psi1AP
      rw [ha', Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun n _ => by push_cast; ring)
    rw [hcast, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_filter] at hn
    have hnq : (n : ZMod q) = (a : ZMod q) := by rw [← ZMod.natCast_mod n q, hn.2]
    rw [hnq]; ring
  have step2 : ∑ a ∈ S, χ (a : ZMod q) * (psi1AP x q a : ℂ)
      = ∑ a ∈ Finset.range q, χ (a : ZMod q) * (psi1AP x q a : ℂ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hc : Nat.Coprime q a
    · simp [hc]
    · have hnu : ¬ IsUnit (a : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]; exact fun h => hc h.symm
      simp [hc, MulChar.map_nonunit χ hnu]
  rw [step1, ← step2]

/-! ## 3. The orthogonality fold -/

/-- **The ψ₁ orthogonality fold** (ψ₁-analog of `Salt.BV.MaxReduction`'s identity).
For reduced `a` (`a < q`, `Nat.Coprime q a`),
`∑_χ χ̄(a)·ψ₁(x, χ) = φ(q)·ψ₁(x; q, a)` — the real AP carrier extracted from the
character carriers. Route: invert `psi1Chi_eq_sum_psi1AP`, bridge
`conj (χ a) = χ a⁻¹` for the unit `a`, then collapse the orthogonality sum via
`DirichletCharacter.sum_char_inv_mul_char_eq`. -/
theorem psi1_fold {q : ℕ} [NeZero q] (x : ℝ) {a : ℕ} (ha : a < q) (hcop : Nat.Coprime q a) :
    (∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ)
      = (q.totient : ℂ) * (psi1AP x q a : ℂ) := by
  set S := (Finset.range q).filter (Nat.Coprime q) with hS
  have haS : a ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨ha, hcop⟩
  have hau : IsUnit (a : ZMod q) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.symm
  -- `conj (χ a) = χ a⁻¹` for the unit `a` (values are roots of unity).
  have conj_a : ∀ χ : DirichletCharacter ℂ q,
      (starRingEnd ℂ) (χ (a : ZMod q)) = χ ((a : ZMod q)⁻¹) := by
    intro χ
    have hmul : χ ((a : ZMod q)⁻¹) * χ (a : ZMod q) = 1 := by
      rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit hau (a : ZMod q)).mpr rfl, map_one]
    have hne : χ (a : ZMod q) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hmul; exact one_ne_zero hmul.symm
    have hinv : (χ (a : ZMod q))⁻¹ * χ (a : ZMod q) = 1 := inv_mul_cancel₀ hne
    have final : χ ((a : ZMod q)⁻¹) = (χ (a : ZMod q))⁻¹ :=
      mul_right_cancel₀ hne (hmul.trans hinv.symm)
    rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact final.symm
  calc ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * psi1Chi x χ
      = ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * ∑ b ∈ S, χ (b : ZMod q) * (psi1AP x q b : ℂ) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [conj_a χ, psi1Chi_eq_sum_psi1AP x χ]
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ b ∈ S,
          (psi1AP x q b : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (b : ZMod q)) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => by ring)
    _ = ∑ b ∈ S, (psi1AP x q b : ℂ) * ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * χ (b : ZMod q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => by rw [Finset.mul_sum])
    _ = ∑ b ∈ S, (psi1AP x q b : ℂ) *
          (if (a : ZMod q) = (b : ZMod q) then (q.totient : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) hau (b : ZMod q)]
    _ = ∑ b ∈ S, (psi1AP x q b : ℂ) * (if a = b then (q.totient : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun b hb => ?_)
        have hbb : b < q := Finset.mem_range.mp (Finset.mem_filter.mp (hS ▸ hb)).1
        have hcongr : ((a : ZMod q) = (b : ZMod q)) = (a = b) := by
          rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hbb]
        simp only [hcongr]
    _ = (q.totient : ℂ) * (psi1AP x q a : ℂ) := by
        rw [Finset.sum_eq_single a
          (fun b _ hne => by rw [if_neg (Ne.symm hne), mul_zero])
          (fun h => absurd haS h)]
        rw [if_pos rfl]; ring

/-! ## 4. Nonnegativity and the first-difference sandwich -/

/-- **Nonnegativity of the Riesz carrier.** For `0 ≤ x`, every summand
`Λ(n)·(x − n)` is `≥ 0` (`Λ ≥ 0`, and `n ≤ ⌊x⌋₊ ≤ x`). -/
theorem psi1AP_nonneg {x : ℝ} (hx : 0 ≤ x) (q a : ℕ) : 0 ≤ psi1AP x q a := by
  unfold psi1AP
  refine Finset.sum_nonneg (fun n hn => ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn.1.2) (Nat.floor_le hx)
  exact mul_nonneg vonMangoldt_nonneg (by linarith)

/-- **The first-difference sandwich** (the monotonicity package S6's de-smoothing
consumes). For `0 ≤ x ≤ y`,
`(y − x)·psiAPr x q a ≤ ψ₁(y; q, a) − ψ₁(x; q, a) ≤ (y − x)·psiAPr y q a`. Both
jaws come from the honest discrete identity
`ψ₁(y) − ψ₁(x) = (y − x)·Σ_{n ≤ ⌊x⌋} Λ + Σ_{⌊x⌋ < n ≤ ⌊y⌋} Λ(n)(y − n)`: the
remainder is `≥ 0` (lower jaw) and `≤ (y − x)·Σ_{⌊x⌋ < n ≤ ⌊y⌋} Λ` since `n > x`
(upper jaw). -/
theorem psi1AP_sandwich {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (q a : ℕ) :
    (y - x) * psiAPr x q a ≤ psi1AP y q a - psi1AP x q a
      ∧ psi1AP y q a - psi1AP x q a ≤ (y - x) * psiAPr y q a := by
  have hy : 0 ≤ y := le_trans hx hxy
  set Fx := (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q) with hFx
  set Fy := (Finset.Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q) with hFy
  have hfloor : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hsub : Fx ⊆ Fy := by
    intro n hn
    rw [hFx, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [hFy, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn.1.1, le_trans hn.1.2 hfloor⟩, hn.2⟩
  have hpsiAPr_x : psiAPr x q a = ∑ n ∈ Fx, vonMangoldt n := by rw [psiAPr, psiAP, ← hFx]
  have hpsiAPr_y : psiAPr y q a = ∑ n ∈ Fy, vonMangoldt n := by rw [psiAPr, psiAP, ← hFy]
  -- The Riesz-weighted sum splits across `Fx ⊆ Fy`.
  have hsplit : ∑ n ∈ Fy, vonMangoldt n * (y - n)
      = ∑ n ∈ Fx, vonMangoldt n * (y - n) + ∑ n ∈ Fy \ Fx, vonMangoldt n * (y - n) := by
    rw [← Finset.sum_sdiff hsub]; ring
  -- The unweighted `Λ` sum splits the same way.
  have hLamsplit : ∑ n ∈ Fy, vonMangoldt n
      = ∑ n ∈ Fx, vonMangoldt n + ∑ n ∈ Fy \ Fx, vonMangoldt n := by
    rw [← Finset.sum_sdiff hsub]; ring
  -- The honest first-difference identity.
  have hdiff : psi1AP y q a - psi1AP x q a
      = (y - x) * psiAPr x q a + ∑ n ∈ Fy \ Fx, vonMangoldt n * (y - n) := by
    have e1 : psi1AP y q a = ∑ n ∈ Fx, vonMangoldt n * (y - n)
        + ∑ n ∈ Fy \ Fx, vonMangoldt n * (y - n) := by rw [psi1AP, ← hFy]; exact hsplit
    have e2 : psi1AP x q a = ∑ n ∈ Fx, vonMangoldt n * (x - n) := by rw [psi1AP, ← hFx]
    have e3 : ∑ n ∈ Fx, vonMangoldt n * (y - n) - ∑ n ∈ Fx, vonMangoldt n * (x - n)
        = (y - x) * psiAPr x q a := by
      rw [hpsiAPr_x, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [e1, e2]; linarith [e3]
  -- The `psiAPr` first difference is the `Λ`-mass of the new residues.
  have hpsiAPr_diff : psiAPr y q a - psiAPr x q a = ∑ n ∈ Fy \ Fx, vonMangoldt n := by
    rw [hpsiAPr_x, hpsiAPr_y, hLamsplit]; ring
  refine ⟨?_, ?_⟩
  · -- Lower jaw: the remainder is `≥ 0`.
    have hrem_nonneg : 0 ≤ ∑ n ∈ Fy \ Fx, vonMangoldt n * (y - n) := by
      refine Finset.sum_nonneg (fun n hn => ?_)
      rw [Finset.mem_sdiff, hFy, Finset.mem_filter, Finset.mem_Icc] at hn
      have hnx : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn.1.1.2) (Nat.floor_le hy)
      exact mul_nonneg vonMangoldt_nonneg (by linarith)
    linarith [hdiff]
  · -- Upper jaw: the remainder is `≤ (y − x)·(new-residue Λ-mass)` since `n > x`.
    have hR_le : ∑ n ∈ Fy \ Fx, vonMangoldt n * (y - n)
        ≤ (y - x) * ∑ n ∈ Fy \ Fx, vonMangoldt n := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_sdiff] at hn
      obtain ⟨hnFy, hnFx⟩ := hn
      rw [hFy, Finset.mem_filter, Finset.mem_Icc] at hnFy
      have hnx_up : ⌊x⌋₊ < n := by
        by_contra h
        exact hnFx (by
          rw [hFx, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hnFy.1.1, not_lt.mp h⟩, hnFy.2⟩)
      have hxn : (x : ℝ) ≤ n := by
        have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnx_up)
        linarith
      have hle : y - (n : ℝ) ≤ y - x := by linarith
      calc vonMangoldt n * (y - n) ≤ vonMangoldt n * (y - x) :=
            mul_le_mul_of_nonneg_left hle vonMangoldt_nonneg
        _ = (y - x) * vonMangoldt n := by ring
    rw [hdiff]
    have : (y - x) * ∑ n ∈ Fy \ Fx, vonMangoldt n = (y - x) * (psiAPr y q a - psiAPr x q a) := by
      rw [hpsiAPr_diff]
    nlinarith [hR_le, this]

/-- **Lower jaw** of `psi1AP_sandwich`. -/
theorem psi1AP_sub_lower {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (q a : ℕ) :
    (y - x) * psiAPr x q a ≤ psi1AP y q a - psi1AP x q a :=
  (psi1AP_sandwich hx hxy q a).1

/-- **Upper jaw** of `psi1AP_sandwich`. -/
theorem psi1AP_sub_upper {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (q a : ℕ) :
    psi1AP y q a - psi1AP x q a ≤ (y - x) * psiAPr y q a :=
  (psi1AP_sandwich hx hxy q a).2

/-! ## 5. The −L'/L Dirichlet-series identity -/

open scoped LSeries.notation in
/-- **The −L'/L identity (S0 interface).** On `Re s > 1`,
`−L'/L(s, χ) = LSeries (χ·Λ) s`. Re-export of mathlib's
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`; S1 bridges `LSeries ↗χ` to the
analytic continuation `LFunction χ` (they agree on `Re s > 1`) for the contour
integral. -/
theorem neg_logDeriv_LSeries_eq_LSeries_twist {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    -deriv (LSeries ↗χ) s / LSeries ↗χ s = LSeries (↗χ * ↗vonMangoldt) s :=
  (DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs).symm

end Salt.SW
