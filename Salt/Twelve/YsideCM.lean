/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MvI
import Salt.Twelve.MvJ

/-!
# Node B, card NB-2 — the weighted-moment lower bound `yside_ge_cM`

Card NB-2 of the `explicit12` Node-B finish
(`docs/blueprints/explicit12-design.md`).  Converts the crude collision moment
`M = ∑_r 1/∏φ(rᵢ)` into a `yside`-relative bound: for a fixed polynomial `F`
with `0 < Ical F`, there is `c > 0` with `c·M ≤ yside := ∑_r yF(r)²/∏φ(rᵢ)`
for all large `R`.

Route (both moments through the landed keystone `mv_I`):
* `yside = X⁵·Ical F ± cI·(1+X)⁵·(1/log R + 1/D)` (`mv_I` at `F`);
* `M = X⁵·(1/120) ± cM·(1+X)⁵·(1/log R + 1/D)` (`mv_I` at the constant `1`,
  since `simplexInt (sq (ofPoly 1)) = DInt' 0 0 = 1/120`);
* choose `c = 60·Ical F`, so `c·X⁵/120 = X⁵·Ical F/2` leaves `X⁵·Ical F/2` of
  head-room for the two errors.

The errors are `O((1+X)⁵·(1/log R + 1/D))`.  For `X ≥ 1` we have
`(1+X)⁵ ≤ 32·X⁵`, so the `1/log R` piece is killed by a threshold `R ≥ R₀`
(the `X` power cancels), and the `1/D` piece — a *fixed* fraction of the main
term at fixed `D` — needs `D` above a threshold.  The `D`-threshold is exposed
via the (opaque) `mv_I` error witnesses as `hD0`; at the endgame (`F = Fstar1`,
`D = Dstar = 3·10⁷`) it holds with room to spare.
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-! ## The constant polynomial and its Dirichlet moments -/

/-- The constant-`1` polynomial on the 5-simplex. -/
def onePoly : Poly := [(![0, 0, 0, 0, 0], 1)]

/-- `eval (ofPoly onePoly) t = 1` for every point `t`. -/
lemma eval_ofPoly_onePoly (t : Fin 5 → ℝ) : eval (ofPoly onePoly) t = 1 := by
  simp [eval, ofPoly, onePoly, Fin.prod_univ_five]

/-- `simplexInt (sq (ofPoly onePoly)) = 1/120` (= `DInt' 0 0`). -/
lemma simplexInt_sq_ofPoly_onePoly :
    simplexInt (sq (ofPoly onePoly)) = (1 / 120 : ℚ) := by
  rw [simplexInt_sq_ofPoly_eq_Ical]
  simp only [Ical, onePoly, DInt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Fin.prod_univ_five, Fin.sum_univ_five, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num [Nat.factorial]

/-! ## The `mv_I` error witness, exposed for the `D`-threshold hypothesis -/

/-- The error constant produced by the keystone `mv_I` at `(W', F)`. Opaque, but
its defining bound (`mvIErr_bound`) and nonnegativity (`mvIErr_nonneg`) are
available.  Exposed so the `D`-threshold hypothesis `hD0` of `yside_ge_cM` can be
stated against it. -/
noncomputable def mvIErr (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) : ℝ :=
  (mv_I W' hW' hpos hUpper F).choose

lemma mvIErr_nonneg (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) : 0 ≤ mvIErr W' hW' hpos hUpper F :=
  (mv_I W' hW' hpos hUpper F).choose_spec.1

lemma mvIErr_bound (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) (D R : ℕ) (hD : 3 ≤ D)
    (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hlogR : 1 ≤ Real.log R) :
    |(∑ r ∈ kSieveIndex 5 R W',
          eval (ofPoly F) (fun i => Real.log (r i) / Real.log R) ^ 2
            / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 5 * ((simplexInt (sq (ofPoly F)) : ℚ) : ℝ)|
      ≤ mvIErr W' hW' hpos hUpper F * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 5
          * (1 / Real.log R + 1 / D) :=
  (mv_I W' hW' hpos hUpper F).choose_spec.2 D R hD hDW hlogR

/-! ## The keystone `yside_ge_cM` -/

/-- **NB-2.** The `yside`-relative lower bound on the crude collision moment `M`.
For a polynomial `F` with `0 < Ical F` there is a positive constant
`c = 60·Ical F` with `c·M ≤ yside` for all large `R`, where
`M = ∑_r 1/∏φ(rᵢ)` and `yside = ∑_r yF(r)²/∏φ(rᵢ)`.

Two added hypotheses beyond the frozen card:
* `hIcal : 0 < Ical F` — makes `c = 60·Ical F > 0`;
* `hD0` — `D` beats the `mv_I` error witnesses (a fixed `1/D` fraction of the
  main term must be dominated by the `Ical F/4` head-room). -/
theorem yside_ge_cM (F : Poly) (hIcal : 0 < Ical F) :
    ∃ c : ℝ, 0 < c ∧ ∀ W' D : ℕ, (hW' : Squarefree W') → (hpos : 0 < W') →
      (hUpper : PhiUpperAtom W') → 3 ≤ D → (∀ p, p.Prime → ¬p ∣ W' → D < p) →
      128 * (mvIErr W' hW' hpos hUpper F
              + 60 * ((Ical F : ℚ) : ℝ) * mvIErr W' hW' hpos hUpper onePoly)
          ≤ ((Ical F : ℚ) : ℝ) * (D : ℝ) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        c * (∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ))
          ≤ ∑ r ∈ kSieveIndex 5 R W', (yF R W' F r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  set A : ℝ := ((Ical F : ℚ) : ℝ) with hAdef
  have hA : 0 < A := by rw [hAdef]; exact_mod_cast hIcal
  refine ⟨60 * A, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD3 hDW hD0
  -- the two error witnesses
  set cI : ℝ := mvIErr W' hW' hpos hUpper F with hcIdef
  set cM : ℝ := mvIErr W' hW' hpos hUpper onePoly with hcMdef
  have hcI0 : 0 ≤ cI := mvIErr_nonneg W' hW' hpos hUpper F
  have hcM0 : 0 ≤ cM := mvIErr_nonneg W' hW' hpos hUpper onePoly
  set E : ℝ := cI + 60 * A * cM with hEdef
  have hE0 : 0 ≤ E := by
    rw [hEdef]; have : 0 ≤ 60 * A * cM := by positivity
    linarith
  -- hD0 in `E`-form
  have hD0' : 128 * E ≤ A * (D : ℝ) := by rw [hEdef]; exact hD0
  -- density constant
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκ : 0 < κ := by
    rw [hκdef]
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  have hκne : κ ≠ 0 := ne_of_gt hκ
  -- the R-threshold
  set T : ℝ := max (1 / κ) (128 * E / A) with hTdef
  refine ⟨⌈Real.exp T⌉₊ + 1, ?_⟩
  intro R hRR₀ hlogR
  set L : ℝ := Real.log R with hLdef
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- basic facts about R
  have hRpos : 0 < R := by omega
  have hRR : (Real.exp T : ℝ) ≤ (R : ℝ) := by
    have h1 : (⌈Real.exp T⌉₊ : ℝ) ≤ (R : ℝ) := by
      have : (⌈Real.exp T⌉₊ : ℕ) ≤ R := by omega
      exact_mod_cast this
    have h2 : Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hTL : T ≤ L := by
    rw [hLdef]
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hRpos)]
    exact hRR
  -- consequences of the threshold
  have hκinvL : 1 / κ ≤ L := le_trans (le_max_left _ _) hTL
  have hEL : 128 * E / A ≤ L := le_trans (le_max_right _ _) hTL
  -- `X ≥ 1`
  set X : ℝ := κ * L with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]
    have : κ * (1 / κ) ≤ κ * L := mul_le_mul_of_nonneg_left hκinvL hκ.le
    rwa [mul_one_div, div_self hκne] at this
  have hX0 : 0 < X := by linarith
  have hX50 : 0 < X ^ 5 := by positivity
  -- `X` matches `mv_I`'s main-term factor
  have hXeq : X = (W'.totient : ℝ) / W' * L := by rw [hXdef, hκdef]
  -- (1+X)^5 ≤ 32 X^5
  have h1X : 1 + X ≤ 2 * X := by linarith
  have h32 : (1 + X) ^ 5 ≤ 32 * X ^ 5 := by
    calc (1 + X) ^ 5 ≤ (2 * X) ^ 5 := by
          apply pow_le_pow_left₀ (by linarith) h1X
      _ = 32 * X ^ 5 := by ring
  -- the two moment sums
  set yside : ℝ := ∑ r ∈ kSieveIndex 5 R W', (yF R W' F r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
    with hysidedef
  set Msum : ℝ := ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) with hMsumdef
  -- rewrite `yside` in the `eval`-form of `mv_I`
  have hyside_eval : yside
      = ∑ r ∈ kSieveIndex 5 R W',
          eval (ofPoly F) (fun i => Real.log (r i) / L) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
    rw [hysidedef]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    simp only [yF, if_pos hr, hLdef]
  -- rewrite `Msum` in the `eval`-form of `mv_I` at `onePoly`
  have hMsum_eval : (∑ r ∈ kSieveIndex 5 R W',
          eval (ofPoly onePoly) (fun i => Real.log (r i) / L) ^ 2
            / ∏ i, (Nat.totient (r i) : ℝ)) = Msum := by
    rw [hMsumdef]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [eval_ofPoly_onePoly]; norm_num
  -- `mv_I` at `F`
  have hboundF := mvIErr_bound W' hW' hpos hUpper F D R hD3 hDW hlogR
  rw [← hcIdef, ← hLdef, simplexInt_sq_ofPoly_eq_Ical, ← hAdef, ← hXeq] at hboundF
  rw [← hyside_eval] at hboundF
  -- `mv_I` at `onePoly`
  have hboundM := mvIErr_bound W' hW' hpos hUpper onePoly D R hD3 hDW hlogR
  rw [← hcMdef, ← hLdef, simplexInt_sq_ofPoly_onePoly, ← hXeq, hMsum_eval] at hboundM
  push_cast at hboundM
  -- lower bound on `yside`, upper bound on `Msum`
  have hyside_lb : X ^ 5 * A - cI * (1 + X) ^ 5 * (1 / L + 1 / D) ≤ yside := by
    have := (abs_le.mp hboundF).1
    linarith
  have hMsum_ub : Msum ≤ X ^ 5 * (1 / 120) + cM * (1 + X) ^ 5 * (1 / L + 1 / D) := by
    have := (abs_le.mp hboundM).2
    linarith
  -- error control
  have hDpos : 0 < (D : ℝ) := by
    have : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD3
    linarith
  -- the key inequality: `E · (1+X)^5 · (1/L + 1/D) ≤ A · X^5 / 2`, split into halves.
  have hstep : E * (1 + X) ^ 5 ≤ 32 * E * X ^ 5 := by
    calc E * (1 + X) ^ 5 ≤ E * (32 * X ^ 5) := mul_le_mul_of_nonneg_left h32 hE0
      _ = 32 * E * X ^ 5 := by ring
  have hkeyL : cM * 60 * A * ((1 + X) ^ 5 * (1 / L)) + cI * ((1 + X) ^ 5 * (1 / L))
      ≤ A * X ^ 5 / 4 := by
    have hEXL : 128 * E ≤ A * L := by rw [div_le_iff₀ hA] at hEL; linarith
    have h1 : 32 * E ≤ A * L / 4 := by linarith
    have hmul : E * (1 + X) ^ 5 ≤ A * X ^ 5 * L / 4 :=
      calc E * (1 + X) ^ 5 ≤ 32 * E * X ^ 5 := hstep
        _ ≤ A * L / 4 * X ^ 5 := mul_le_mul_of_nonneg_right h1 hX50.le
        _ = A * X ^ 5 * L / 4 := by ring
    have hmain : E * ((1 + X) ^ 5 * (1 / L)) ≤ A * X ^ 5 / 4 := by
      have heq : E * ((1 + X) ^ 5 * (1 / L)) = (E * (1 + X) ^ 5) * (1 / L) := by ring
      rw [heq]
      calc (E * (1 + X) ^ 5) * (1 / L) ≤ (A * X ^ 5 * L / 4) * (1 / L) :=
            mul_le_mul_of_nonneg_right hmul (one_div_nonneg.mpr hLpos.le)
        _ = A * X ^ 5 / 4 := by field_simp
    calc cM * 60 * A * ((1 + X) ^ 5 * (1 / L)) + cI * ((1 + X) ^ 5 * (1 / L))
        = E * ((1 + X) ^ 5 * (1 / L)) := by rw [hEdef]; ring
      _ ≤ A * X ^ 5 / 4 := hmain
  have hkeyD : cM * 60 * A * ((1 + X) ^ 5 * (1 / D)) + cI * ((1 + X) ^ 5 * (1 / D))
      ≤ A * X ^ 5 / 4 := by
    have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
    have h1 : 32 * E ≤ A * (D : ℝ) / 4 := by linarith
    have hmul : E * (1 + X) ^ 5 ≤ A * X ^ 5 * (D : ℝ) / 4 :=
      calc E * (1 + X) ^ 5 ≤ 32 * E * X ^ 5 := hstep
        _ ≤ A * (D : ℝ) / 4 * X ^ 5 := mul_le_mul_of_nonneg_right h1 hX50.le
        _ = A * X ^ 5 * (D : ℝ) / 4 := by ring
    have hmain : E * ((1 + X) ^ 5 * (1 / D)) ≤ A * X ^ 5 / 4 := by
      have heq : E * ((1 + X) ^ 5 * (1 / D)) = (E * (1 + X) ^ 5) * (1 / D) := by ring
      rw [heq]
      calc (E * (1 + X) ^ 5) * (1 / D) ≤ (A * X ^ 5 * (D : ℝ) / 4) * (1 / D) :=
            mul_le_mul_of_nonneg_right hmul (one_div_nonneg.mpr hDpos.le)
        _ = A * X ^ 5 / 4 := by field_simp
    calc cM * 60 * A * ((1 + X) ^ 5 * (1 / D)) + cI * ((1 + X) ^ 5 * (1 / D))
        = E * ((1 + X) ^ 5 * (1 / D)) := by rw [hEdef]; ring
      _ ≤ A * X ^ 5 / 4 := hmain
  -- assemble: `60·A·Msum ≤ yside`
  have hcombine : 60 * A * Msum ≤ yside := by
    have hexp : 60 * A * (X ^ 5 * (1 / 120) + cM * (1 + X) ^ 5 * (1 / L + 1 / D))
        = A * X ^ 5 / 2
          + (cM * 60 * A * ((1 + X) ^ 5 * (1 / L)) + cM * 60 * A * ((1 + X) ^ 5 * (1 / D))) := by
      ring
    have hupper : 60 * A * Msum
        ≤ A * X ^ 5 / 2
          + (cM * 60 * A * ((1 + X) ^ 5 * (1 / L)) + cM * 60 * A * ((1 + X) ^ 5 * (1 / D))) := by
      calc 60 * A * Msum
          ≤ 60 * A * (X ^ 5 * (1 / 120) + cM * (1 + X) ^ 5 * (1 / L + 1 / D)) :=
            mul_le_mul_of_nonneg_left hMsum_ub (by positivity)
        _ = _ := hexp
    have hlower : X ^ 5 * A
          - (cI * ((1 + X) ^ 5 * (1 / L)) + cI * ((1 + X) ^ 5 * (1 / D))) ≤ yside := by
      have hrw : cI * (1 + X) ^ 5 * (1 / L + 1 / D)
          = cI * ((1 + X) ^ 5 * (1 / L)) + cI * ((1 + X) ^ 5 * (1 / D)) := by ring
      rw [hrw] at hyside_lb
      exact hyside_lb
    linarith [hkeyL, hkeyD, hupper, hlower]
  exact hcombine

end Salt.Twelve
