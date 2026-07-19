/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cELT1
import Salt.HB.L2cELT2
import Salt.HB.L2cELT3F
import Salt.HB.L2cELTsw
import Salt.HB.L2cELJunk
import Salt.HB.L2cEven
import Salt.HB.L2cERT1
import Salt.HB.L2cERT2
import Salt.HB.L2cERT3
import Salt.HB.L2cERTsw

/-!
# HB-L2c master assembly — Wave 3 (node HB-L2c, Horn A keystone)

This file completes the exact-overshoot surgery: the theorem whose shape is `hb_lemma2`'s
conclusion (`TransferFull.hb_lemma2`), proven *directly* from the exact identity
`S⁽²⁾ − S⁽¹⁾ = Σ_{n∈W} overshootExact χ n` (`L2cCore.S2_sub_S1_eq`) and the eleven landed
`E_L`/`E_R` family rows.  No `τ`-crude majorant (`hres`) is consumed.

## The assembly ladder

* **R7a** the split `Σ_W overshootExact = E_L + E_R` (`overshoot_eq_EL_add_ER`) and the
  parity reduction `E_L ≤ E_L^{odd} + evenCornerSum` (`EL_le_ELodd_add_even`; the even
  class of *both* overshoot summands is the sixth `E_L` row, owned by `L2cEven`).
* **R7b** the cover lemmas.  The `E_R` side is a *complete* cover
  (`E_R_split` + `ER_prime_cover` + `singleBlock_cover`): every nonzero `E_R` term lies in
  the squarefull-junk, `T1'`, `T2'`, `T3'`, `Tsw'`, or `w`-junk row (`Tsw'` conditional on
  the count residual `hcount`, engine-blocked per `L2cERTsw`'s NOTES).  The `E_L`-odd side
  is covered by the six landed slices *up to a precise residual* `L2cELuncov` — the two
  freeze-acknowledged gaps (the never-landed `T2`-mirror family and the mid-range
  squarefull corner; see the module NOTES).
* **R7c** the ledger: all row bounds + the `x/L' ≤ x/log x` and `√(2x)·L'² ≤ x^{9/10}·L'³`
  conversions collected into the three `hb_lemma2` lines.

The export is `hb_l2c_master_of_count`, conditional on the two named residuals `hcount`
(the `ER_Tsw'` count) and `hEL_uncov` (the `E_L` mop-up).  Both are characterized exactly
in the NOTES; neither is vacuous.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 (R7a) — the overshoot split and the parity reduction -/

/-- Each `E_R` summand `Λ(n)·(Λ̃−Λ)(n+2)` is nonnegative. -/
lemma er_summand_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) :=
  mul_nonneg vonMangoldt_nonneg (lamTilde_sub_nonneg χ hsq (n + 2))

/-- **The exact overshoot split.**  `Σ_{n∈W} overshootExact χ n = E_L + E_R`, the two
    summands of `overshootExact` summed separately over the honest window. -/
lemma overshoot_eq_EL_add_ER (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    ∑ n ∈ l2cWindow χ z x, overshootExact χ n = EL χ z x + E_R χ z x := by
  rw [EL, E_R, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => rfl

/-- **The odd left-family sum** `E_L^{odd} := Σ_{n∈W, Odd n} (Λ̃−Λ)(n)·Λ̃(n+2)` — the
    part of `E_L` the odd-guarded family slices cover. -/
noncomputable def L2cELodd (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ (l2cWindow χ z x).filter (fun n => Odd n),
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

/-- **The parity reduction.**  `E_L ≤ E_L^{odd} + evenCornerSum`: the even part of `E_L`
    (the left summand on even `n`) is dominated by the full even overshoot
    (`evenCornerSum`, which adds back the nonnegative right summand). -/
lemma EL_le_ELodd_add_even (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    EL χ z x ≤ L2cELodd χ z x + evenCornerSum χ z x := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (l2cWindow χ z x) (fun n => Odd n)
    (fun n => (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
  rw [EL, ← hsplit, L2cELodd]
  have hle : ∑ n ∈ (l2cWindow χ z x).filter (fun n => ¬ Odd n),
        (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ evenCornerSum χ z x := ?_
  · linarith [hle]
  -- the `¬ Odd` part: left summand ≤ full overshoot on the even-corner set
  rw [evenCornerSum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_filter] at hn
  have hmem : n ∈ evenCornerSet χ z x := (evenCorner_mem χ).mpr ⟨hn.1, hn.2⟩
  rw [overshootExact]
  have := er_summand_nonneg χ hsq n
  linarith

/-! ## §2 (R7b, E_R side) — the complete `E_R` cover

The `E_R` decomposition is *complete* (no residual): `E_R_split` peels the squarefull junk,
`ER_prime_cover` splits the prime part into the all-plus (`T1'`) and single-block classes,
and `singleBlock_cover` (below) covers the single-block class by `T2' ∪ T3' ∪ Tsw' ∪ w-junk`.
-/

/-- On a window element, `(n+2)₋ ∣ (n+2)`. -/
lemma master_nMinus_np2_dvd (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : nMinus χ (n + 2) ∣ (n + 2) :=
  ⟨nPlus χ (n + 2), by
    rw [mul_comm]; exact eq_nPlus_mul_nMinus χ hsq (by omega) (l2cWindow_np2_coprime_q χ hn)⟩

/-- A junk block on `(n+2)₋` puts `n` into `wJunkSet`. -/
lemma master_mem_wJunkSet (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) {p e : ℕ} (hp : p.Prime) (hpZ : p ≤ Zz z) (he : 2 ≤ e)
    (hgt : (z : ℝ) ^ ((1 : ℝ) / 4) < ((p ^ e : ℕ) : ℝ)) (hdvd : p ^ e ∣ (n + 2)) :
    n ∈ wJunkSet χ z x := by
  simp only [wJunkSet, Finset.mem_filter]
  exact ⟨hn, p, e, hp, hpZ, he, hgt, hdvd⟩

/-- If `n ∉ wJunkSet` then `(n+2)₋` is not a junk block (in the shared `ERT2'/T3'/Tsw'`
    shape). -/
lemma master_not_junkBlock (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (hnw : n ∉ wJunkSet χ z x) :
    ¬ (∃ p e : ℕ, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ nMinus χ (n + 2) = p ^ e ∧
        (z : ℝ) ^ ((1 : ℝ) / 4) < ((nMinus χ (n + 2) : ℕ) : ℝ)) := by
  rintro ⟨p, e, hp, hpZ, he, heq, hgt⟩
  refine hnw (master_mem_wJunkSet χ hn hp hpZ he ?_ ?_)
  · rw [← heq]; exact hgt
  · rw [← heq]; exact master_nMinus_np2_dvd χ hsq hn

open Classical in
/-- **The single-block cover** (`ER_prime_cover`'s second summand).  Every single-block
    `E_R` term (`n` prime, `(n+2)₋` a prime power, `1 < (n+2)₊`) lies in the `T2'`, `T3'`,
    `Tsw'`, or `w`-junk row — a *complete* cover (no residual). -/
lemma singleBlock_cover (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hx2 : 2 ≤ x) :
    ∑ n ∈ (l2cWindow χ z x).filter
        (fun n => n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2)),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ (∑ n ∈ (l2cWindow χ z x).filter (fun n =>
            n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
              ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2))),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
        + ER_T3' χ z x + ER_Tsw' χ z x + wJunkSum χ z x := by
  classical
  set SB := (l2cWindow χ z x).filter
      (fun n => n.Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2)) with hSB
  -- peel w-junk, then ¬U.Prime (T2'), then z ≤ w (T3'), remainder (Tsw')
  have step1 := Finset.sum_filter_add_sum_filter_not SB (fun n => n ∈ wJunkSet χ z x)
    (fun n => Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
  set SB1 := SB.filter (fun n => ¬ n ∈ wJunkSet χ z x) with hSB1
  have step2 := Finset.sum_filter_add_sum_filter_not SB1 (fun n => ¬ (nPlus χ (n + 2)).Prime)
    (fun n => Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
  set SB2 := SB1.filter (fun n => ¬ ¬ (nPlus χ (n + 2)).Prime) with hSB2
  have step3 := Finset.sum_filter_add_sum_filter_not SB2 (fun n => z ≤ nMinus χ (n + 2))
    (fun n => Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
  -- bound the four pieces
  have hj : ∑ n ∈ SB.filter (fun n => n ∈ wJunkSet χ z x),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≤ wJunkSum χ z x := by
    rw [wJunkSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => er_summand_nonneg χ hsq n)
  have hT2 : ∑ n ∈ SB1.filter (fun n => ¬ (nPlus χ (n + 2)).Prime),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ ∑ n ∈ (l2cWindow χ z x).filter (fun n =>
            n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
              ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2))),
          Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
      (fun n _ _ => er_summand_nonneg χ hsq n)
    simp only [hSB1, hSB, Finset.mem_filter] at hn
    obtain ⟨⟨⟨hnW, hp, hpp, hU⟩, hnw⟩, hUcomp⟩ := hn
    exact Finset.mem_filter.mpr ⟨hnW, hp, erT1_mem_odd χ hx2 hnW hp, hpp, hU, hUcomp,
      master_not_junkBlock χ hsq hnW hnw⟩
  have hT3 : ∑ n ∈ SB2.filter (fun n => z ≤ nMinus χ (n + 2)),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≤ ER_T3' χ z x := by
    rw [ER_T3']
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
      (fun n _ _ => er_summand_nonneg χ hsq n)
    simp only [hSB2, hSB1, hSB, Finset.mem_filter] at hn
    obtain ⟨⟨⟨⟨hnW, hp, hpp, hU⟩, hnw⟩, hUp⟩, hwz⟩ := hn
    exact Finset.mem_filter.mpr ⟨hnW, hp, not_not.mp hUp, hpp, hwz,
      master_not_junkBlock χ hsq hnW hnw⟩
  have hTsw : ∑ n ∈ SB2.filter (fun n => ¬ z ≤ nMinus χ (n + 2)),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≤ ER_Tsw' χ z x := by
    rw [ER_Tsw']
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
      (fun n _ _ => er_summand_nonneg χ hsq n)
    simp only [hSB2, hSB1, hSB, Finset.mem_filter] at hn
    obtain ⟨⟨⟨⟨hnW, hp, hpp, hU⟩, hnw⟩, hUp⟩, hwz⟩ := hn
    exact Finset.mem_filter.mpr ⟨hnW, hp, hpp, by omega, not_not.mp hUp,
      master_not_junkBlock χ hsq hnW hnw⟩
  linarith [step1, step2, step3, hj, hT2, hT3, hTsw]

open Classical in
/-- **The complete `E_R` cover.**  `E_R ≤ squarefull + allPlus(T1') + T2' + T3' + Tsw' + w-junk`
    — a decomposition with no residual (`E_R_split` + `ER_prime_cover` + `singleBlock_cover`),
    each piece the exact LHS of a landed row (or `ER_T3'`/`ER_Tsw'`). -/
lemma E_R_cover (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ} (hx2 : 2 ≤ x) :
    E_R χ z x
      ≤ (∑ n ∈ (l2cWindow χ z x).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
        + (∑ n ∈ (l2cWindow χ z x).filter (fun n => n.Prime ∧ nMinus χ (n + 2) = 1),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
        + (∑ n ∈ (l2cWindow χ z x).filter (fun n =>
              n.Prime ∧ Odd n ∧ IsPrimePow (nMinus χ (n + 2)) ∧ 1 < nPlus χ (n + 2) ∧
                ¬ (nPlus χ (n + 2)).Prime ∧ ¬ ERT2'JunkBlock z (nMinus χ (n + 2))),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
        + ER_T3' χ z x + ER_Tsw' χ z x + wJunkSum χ z x := by
  rw [E_R_split χ z x, ER_prime_cover χ hsq z x]
  linarith [singleBlock_cover χ hsq (z := z) (x := x) hx2]

/-! ## §3 (R7b, E_L odd side) — the six-slice cover and the isolated residual

The odd left family `E_L^{odd}` is covered by the six landed slices (`T1`, `T2`, `T3F`,
`Tsw`, `(c)`-junk, corners) *up to a precise residual* `L2cELuncov` — the odd window
elements whose left summand is nonzero yet which sit in none of the six slices.  By the
support classification (`lamTilde_sub_support_classification`) this residual is exactly the
two freeze-acknowledged gaps: the never-landed `T2`-mirror family (`n₊` prime, `1 < n₋ < z`,
`(n+2)₊` not prime) and the mid-range squarefull corner (`n₊` prime, `n₋ = p^a` a proper
prime power with `Zz < p` and `z ≤ p^a ≤ x^{1/4}`).  See the module NOTES for the exact
priceability arithmetic; the master carries a bound on it as the named residual
`hEL_uncov`. -/

open Classical in
/-- **The `E_L` odd-cover residual** — the odd window elements in *none* of the six landed
    `E_L` slices.  Its nonzero terms are exactly the two freeze gaps (`T2`-mirror +
    mid-squarefull); see the module NOTES. -/
noncomputable def L2cELuncov (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ (l2cWindow χ z x).filter (fun n => Odd n ∧ n ∉ T1slice χ z x ∧ n ∉ T2Set χ z x ∧
      n ∉ T3FSet χ z x ∧ n ∉ (l2cWindow χ z x).filter (fun m => IsTsw χ z m) ∧
      n ∉ cJunkSet χ z x ∧ n ∉ cornerSet χ z x),
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

open Classical in
/-- **The `E_L` odd cover.**  `E_L^{odd} ≤ T1 + T2 + T3F + Tsw + (c)-junk + corners +
    residual` — the six landed slices plus the isolated residual `L2cELuncov`. -/
lemma ELodd_cover (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    L2cELodd χ z x
      ≤ ELT1 χ z x + EL_T2 χ z x + EL_T3F χ z x + EL_Tsw χ z x
        + cJunkSum χ z x + cornersSum χ z x + L2cELuncov χ z x := by
  classical
  -- the six slices and the residual set, raw
  set Tsw4 := (l2cWindow χ z x).filter (fun m => IsTsw χ z m) with hTsw4
  set Wc := (l2cWindow χ z x).filter (fun n => Odd n ∧ n ∉ T1slice χ z x ∧ n ∉ T2Set χ z x ∧
      n ∉ T3FSet χ z x ∧ n ∉ Tsw4 ∧ n ∉ cJunkSet χ z x ∧ n ∉ cornerSet χ z x) with hWc
  have hnn : ∀ n, 0 ≤ (LamTilde χ n - Λ n) * LamTilde χ (n + 2) :=
    fun n => EL_summand_nonneg χ hsq n
  have hite : ∀ (n : ℕ) (T : Finset ℕ),
      0 ≤ (if n ∈ T then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0) := by
    intro n T; split_ifs with h
    · exact hnn n
    · exact le_refl 0
  -- the pointwise seven-indicator cover
  have key : ∀ n ∈ (l2cWindow χ z x).filter (fun n => Odd n),
      (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
        ≤ (if n ∈ T1slice χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
          + (if n ∈ T2Set χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
          + (if n ∈ T3FSet χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
          + (if n ∈ Tsw4 then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
          + (if n ∈ cJunkSet χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
          + (if n ∈ cornerSet χ z x then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0)
          + (if n ∈ Wc then (LamTilde χ n - Λ n) * LamTilde χ (n + 2) else 0) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hcover : n ∈ T1slice χ z x ∨ n ∈ T2Set χ z x ∨ n ∈ T3FSet χ z x ∨ n ∈ Tsw4 ∨
        n ∈ cJunkSet χ z x ∨ n ∈ cornerSet χ z x ∨ n ∈ Wc := by
      by_cases hc : n ∈ T1slice χ z x ∨ n ∈ T2Set χ z x ∨ n ∈ T3FSet χ z x ∨ n ∈ Tsw4 ∨
          n ∈ cJunkSet χ z x ∨ n ∈ cornerSet χ z x
      · tauto
      · simp only [not_or] at hc
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
        rw [hWc, Finset.mem_filter]
        exact ⟨hn.1, hn.2, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
    rcases hcover with h | h | h | h | h | h | h <;>
      simp only [if_pos h] <;>
      linarith [hite n (T1slice χ z x), hite n (T2Set χ z x), hite n (T3FSet χ z x),
        hite n Tsw4, hite n (cJunkSet χ z x), hite n (cornerSet χ z x), hite n Wc]
  -- the seven sub-bounds: each filter-sum ≤ its row
  have b1 : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
        (fun n => n ∈ T1slice χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ ELT1 χ z x := by
    rw [ELT1]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have b2 : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
        (fun n => n ∈ T2Set χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ EL_T2 χ z x := by
    rw [EL_T2]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have b3 : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
        (fun n => n ∈ T3FSet χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ EL_T3F χ z x := by
    rw [EL_T3F]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have b4 : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
        (fun n => n ∈ Tsw4), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ EL_Tsw χ z x := by
    rw [EL_Tsw, ← hTsw4]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have b5 : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
        (fun n => n ∈ cJunkSet χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ cJunkSum χ z x := by
    rw [cJunkSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have b6 : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
        (fun n => n ∈ cornerSet χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ cornersSum χ z x := by
    rw [cornersSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  have b7 : ∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
        (fun n => n ∈ Wc), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ L2cELuncov χ z x := by
    rw [L2cELuncov, ← hWc]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => hnn n)
  -- sum the pointwise bound, split into filter-sums, collect
  have hsum : L2cELodd χ z x
      ≤ (∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
            (fun n => n ∈ T1slice χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
            (fun n => n ∈ T2Set χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
            (fun n => n ∈ T3FSet χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
            (fun n => n ∈ Tsw4), (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
            (fun n => n ∈ cJunkSet χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
            (fun n => n ∈ cornerSet χ z x), (LamTilde χ n - Λ n) * LamTilde χ (n + 2))
        + (∑ n ∈ ((l2cWindow χ z x).filter (fun n => Odd n)).filter
            (fun n => n ∈ Wc), (LamTilde χ n - Λ n) * LamTilde χ (n + 2)) := by
    rw [L2cELodd]
    refine le_trans (Finset.sum_le_sum key) (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, Finset.sum_filter]
  linarith [hsum, b1, b2, b3, b4, b5, b6, b7]

/-! ## §4 (R7c) — the ledger and the master -/

/-- `√(2x) ≤ 2·x^{9/10}` for `x ≥ 1` (`√2 ≤ 2` and `x^{1/2} ≤ x^{9/10}`). -/
lemma master_sqrt_le {x : ℕ} (hx1 : (1 : ℝ) ≤ (x : ℝ)) :
    Real.sqrt (2 * (x : ℝ)) ≤ 2 * (x : ℝ) ^ ((9 : ℝ) / 10) := by
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hsx : Real.sqrt (x : ℝ) ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  calc Real.sqrt (2 * (x : ℝ)) = Real.sqrt 2 * Real.sqrt (x : ℝ) :=
        Real.sqrt_mul (by norm_num) _
    _ ≤ 2 * (x : ℝ) ^ ((9 : ℝ) / 10) :=
        mul_le_mul hs2 hsx (Real.sqrt_nonneg _) (by norm_num)

/-- The absolute master constant `Cmain = 2^31` (dominates every summed row constant:
    `J1 = 2^30 + 4`, `J2 = 40345603 + 524288`, junk `≤ 24580`). -/
noncomputable def L2cCmain : ℝ := 2 ^ 31

open Classical in
/-- **THE MASTER ASSEMBLY** (`hb_lemma2`'s conclusion shape, proven on the exact identity).
    Over the honest window `W = l2cWindow χ z x`, under the frozen hypothesis packet, the
    twin-sum gap obeys the `J1 + J2 + junk` bound with the absolute constant `L2cCmain`.

    Conditional on two named residuals:
    * `hcount` — the `ER_Tsw'` count residual (engine-blocked at `(log z)²`; see
      `L2cERTsw`'s NOTES), fixed at the ledger constant `524288`;
    * `hEL_uncov` — the `E_L` odd-cover residual `L2cELuncov` (the two freeze gaps, the
      never-landed `T2`-mirror family and the mid-range squarefull corner; both priceable
      at the `J2` and junk shapes — see the module NOTES). -/
theorem hb_l2c_master_of_count (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x)
    (hcount : ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERTsw χ z n),
        Λ (nMinus χ (n + 2))
        ≤ 524288 * x * PretenseSum χ (2 * x + 2) / (Real.log z) ^ 2)
    (hEL_uncov : L2cELuncov χ z x
        ≤ (x : ℝ) / Lwin x * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2)
          + Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ)) * Lwin x ^ 3) :
    S2 χ (l2cWindow χ z x) - S1 (l2cWindow χ z x)
      ≤ L2cCmain * ((x : ℝ) / z0 z x)
        + L2cCmain * ((x : ℝ) / Real.log x) * Real.exp (5 * z0 z x)
            * PretenseSum χ (2 * x + 2)
        + L2cCmain * Real.exp (2 * z0 z x)
            * ((x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3 := by
  classical
  rw [L2cCmain]
  -- scale facts
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz100R : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have hx48 : (100 : ℝ) ^ 48 ≤ (x : ℝ) := by
    calc (100 : ℝ) ^ 48 = ((100 : ℝ) ^ 16) ^ 3 := by norm_num
      _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hz100R 3
      _ ≤ (x : ℝ) := hzx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48
  have hxgt1 : (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx48
  have hx2N : 2 ≤ x := by
    have : (2 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48; exact_mod_cast this
  have hLwin1 : (1 : ℝ) ≤ Lwin x := one_le_Lwin (by omega)
  have hlogxpos : 0 < Real.log x := Real.log_pos hxgt1
  have hlogx_le : Real.log x ≤ Lwin x := by
    rw [Lwin]; exact Real.log_le_log (by linarith) (by linarith)
  have hz0nn : 0 ≤ z0 z x := z0_nonneg hz2
  have hPS0 : 0 ≤ PretenseSum χ (2 * x + 2) := pretenseSum_nonneg χ _
  have hexp5 : 0 ≤ Real.exp (5 * z0 z x) := (Real.exp_pos _).le
  have hexp2 : 0 ≤ Real.exp (2 * z0 z x) := (Real.exp_pos _).le
  have hL3 : 0 ≤ Lwin x ^ 3 := by positivity
  have hXZ : 0 ≤ (x : ℝ) / (z : ℝ) ^ (1 / 8 : ℝ) :=
    div_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hX9 : 0 ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  -- the J2 conversion `x/L' ≤ x/log x`
  have hA2 : (x : ℝ) / Lwin x * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2)
      ≤ (x : ℝ) / Real.log x * Real.exp (5 * z0 z x) * PretenseSum χ (2 * x + 2) := by
    have hxL : (x : ℝ) / Lwin x ≤ (x : ℝ) / Real.log x :=
      div_le_div_of_nonneg_left (by linarith) hlogxpos hlogx_le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxL hexp5) hPS0
  -- the squarefull → `x^{9/10}` junk conversion
  have hsqf : 2 * Real.sqrt (2 * (x : ℝ)) * Lwin x ^ 2 * Real.exp (0.7 * z0 z x)
      ≤ 4 * Real.exp (2 * z0 z x) * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by
    have ha : 2 * Real.sqrt (2 * (x : ℝ)) ≤ 4 * (x : ℝ) ^ ((9 : ℝ) / 10) := by
      linarith [master_sqrt_le (x := x) hx1]
    have hb : Lwin x ^ 2 ≤ Lwin x ^ 3 := by nlinarith [hLwin1]
    have hc : Real.exp (0.7 * z0 z x) ≤ Real.exp (2 * z0 z x) :=
      Real.exp_le_exp.mpr (by nlinarith [hz0nn])
    have hL0 : 0 ≤ Lwin x := Lwin_nonneg x
    calc 2 * Real.sqrt (2 * (x : ℝ)) * Lwin x ^ 2 * Real.exp (0.7 * z0 z x)
        ≤ 4 * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 * Real.exp (2 * z0 z x) :=
          mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity)) hc
            (Real.exp_pos _).le (mul_nonneg (by positivity) (pow_nonneg hL0 3))
      _ = 4 * Real.exp (2 * z0 z x) * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by ring
  -- the structural chain
  have hexact := S2_sub_S1_exact χ (l2cWindow χ z x)
  rw [overshoot_eq_EL_add_ER χ z x] at hexact
  have hELeven := EL_le_ELodd_add_even χ hsq z x
  have hELcov := ELodd_cover χ hsq z x
  have hERcov := E_R_cover χ hsq (z := z) (x := x) hx2N
  -- the row bounds
  have r1 := EL_T1_bound χ hsq hz100 hz8 hzx
  rw [T1Cmain] at r1
  have r2 := EL_T2_bound χ hsq hz100 hz8 hzx
  have r3 := EL_T3F_bound χ hsq hz100 hz8 hzx
  have r4 := EL_Tsw_bound χ hsq hz100 hz8 hzx
  have r5 := EL_cJunk_bound χ hsq hz100 hz8 hzx
  have r6 := EL_corners_bound χ hsq hz100 hz8 hzx
  have r7 := EL_evenCorner_bound χ hsq hz100 hz8 hzx
  have r8 := ER_squarefull_junk χ hsq hz2 (z := z) (x := x)
  have r9 := ER_T1'_bound_mixed χ hsq hz100 hz8 hzx
  have r10 := ER_T2'_bound χ hsq hz100 hz8 hzx
  have r11 := ER_T3'_bound χ hsq hz100 hz8 hzx
  have r12 := ER_Tsw'_bound_of_count χ hsq hz100 hz8 hzx (by norm_num : (0 : ℝ) ≤ 524288) hcount
  have r13 := ER_wJunk_bound χ hsq hz100 hz8 hzx
  linarith [hexact, hELeven, hELcov, hERcov, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
    r12, r13, hEL_uncov, hA2, hsqf, hPS0, hexp5, hexp2, hL3, hXZ, hX9,
    mul_nonneg (mul_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ)) (Lwin_nonneg x)) hexp5) hPS0,
    mul_nonneg (mul_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ)) hlogxpos.le) hexp5) hPS0,
    mul_nonneg (mul_nonneg hexp2 hXZ) hL3, mul_nonneg (mul_nonneg hexp2 hX9) hL3,
    div_nonneg (by linarith : (0:ℝ) ≤ (x:ℝ)) hz0nn]

end Salt.HB
