/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.JMainM

/-!
# Controls: the general-`M` square and contracted square recover the landed `M = 1` statements

Each control below is a NEW theorem whose statement is a landed `M = 1` result of `Square`, `F1`
or `JMain`, restated by `type_of%` (so it cannot drift from the original by a binder), and proved
from its general-`M` generalisation in `SquareM`/`JMainM` at `M = 1` on the landed 42-term `F`
re-keyed as `List ((ℕ × (Fin 1 → ℕ)) × ℤ)` (`rekey1`) — never from the original. They are checks
on the generalisations, not inputs to `gaps_le_636`: none of them is in its dependency closure.

* `simplexInt_sq_Fpoly'` restates `simplexInt_sq_Fpoly` and is proved from `simplexInt_sq_FpolyM 1`,
  with no hypothesis;
* `Iform_eq_ofM` and `Jform_eq_ofM` restate `Iform_eq` and `Jform_eq` and are proved from
  `IformM_eq` and `JformM_eq` at `M = 1`. Until node A2a merges they carry ONE hypothesis,
  `GMOneEq` (`[x^{(c)}] GM 1^k = [x^c] G^k`), which is A2a's `coeff_GM_one_pow`; at that merge
  the hypothesis-free forms are `Iform_eq_ofM (fun k c => …coeff_GM_one_pow k c)` and likewise.

Pure polynomial algebra: nothing here bears on twin primes.
-/

open Finset Nat Salt.Twelve

namespace Salt.MaynardK

/-- a landed coefficient list `(b, c, a)`, re-keyed at `M = 1` as `(b, (fun _ => c), a)`. -/
def rekey1 (cs : List ((ℕ × ℕ) × ℤ)) : List ((ℕ × (Fin 1 → ℕ)) × ℤ) :=
  cs.map fun x => ((x.1.1, fun _ => x.1.2), x.2)

/-- A2a's `coeff_GM_one_pow`, as a hypothesis until its merge: `GM 1` is `G` in one variable. -/
def GMOneEq : Prop :=
  ∀ k c : ℕ, MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => c)) (GM 1 ^ k)
    = PowerSeries.coeff c (G ^ k)

/-! ## The `M = 1` reindexing -/

private lemma fin_one_const (C : Fin 1 → ℕ) : C = fun _ => C 0 :=
  funext fun m => by rw [Fin.fin_one_eq_zero m]

/-- `basisPolyM 1 k a C` and `basisPoly k a (C 0)` have the same coefficient-linear functionals
(the same monomials, indexed by `Fin 1`-tuples of `piAntidiag` and by `piAntidiag`). -/
lemma lsum_basisPolyM_one {k : ℕ} {R : Type*} [Field R] [CharZero R] (g : (Fin k → ℕ) → ℕ → R)
    (a : ℕ) (C : Fin 1 → ℕ) : lsum g (basisPolyM 1 k a C) = lsum g (basisPoly k a (C 0)) := by
  rw [lsum_basisPolyM]
  unfold lsum basisPoly
  rw [List.map_map, Finset.sum_map_toList]
  refine Finset.sum_nbij' (fun e => e 0) (fun x _ => x) ?_ ?_ ?_ ?_ ?_
  · intro e he
    exact Fintype.mem_piFinset.mp he 0
  · intro x hx
    rw [Fintype.mem_piFinset]
    intro m
    rw [Fin.fin_one_eq_zero m]
    exact hx
  · intro e _
    funext m
    rw [Fin.fin_one_eq_zero m]
  · intro x _
    rfl
  · intro e _
    have hexp : expoM e = fun i => 2 * e 0 i := by
      funext i
      simp [expoM]
    simp [multM, hexp]

lemma lsum_Fpoly_one {k : ℕ} {R : Type*} [Field R] [CharZero R] (g : (Fin k → ℕ) → ℕ → R)
    (cs : List ((ℕ × ℕ) × ℤ)) : lsum g (Fpoly k cs) = lsum g (FpolyM 1 k (rekey1 cs)) := by
  unfold Fpoly FpolyM rekey1
  simp only [List.flatMap_map]
  rw [lsum_flatMap, lsum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [lsum_scale, lsum_scale, lsum_basisPolyM_one]

lemma lsum_Fsq_one {k : ℕ} {R : Type*} [Field R] [CharZero R] (g : (Fin k → ℕ) → ℕ → R)
    (cs : List ((ℕ × ℕ) × ℤ)) : lsum g (Fsq k cs) = lsum g (FsqM 1 k (rekey1 cs)) := by
  unfold Fsq FsqM rekey1
  simp only [List.flatMap_map]
  rw [lsum_flatMap, lsum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [lsum_flatMap, lsum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  rw [lsum_scale, lsum_scale, lsum_basisPolyM_one]
  rfl

lemma closedM_one (hG : GMOneEq) (k a c : ℕ) : closedM 1 k a (fun _ => c) = closed k a c := by
  have hw : weight (fun _ : Fin 1 => c) = 2 * c := by simp [weight]
  unfold closedM closed
  rw [hG k c, hw, Fin.prod_univ_one]

lemma basisIntM_one (hG : GMOneEq) (k : ℕ) : BasisIntM 1 k := by
  intro a C
  have h := simplexInt_basisPoly k a (C 0)
  rw [simplexInt_eq_lsum, ← lsum_basisPolyM_one DInt' a C, ← simplexInt_eq_lsum] at h
  rw [h, fin_one_const C, closedM_one hG]
  rfl

/-! ## The controls -/

/-- CONTROL: `simplexInt_sq_Fpoly`, restated by `type_of%`, from `simplexInt_sq_FpolyM 1`. -/
theorem simplexInt_sq_Fpoly' : type_of% @simplexInt_sq_Fpoly := by
  intro k cs
  rw [simplexInt_sq_congr (Q := FpolyM 1 k (rekey1 cs)) fun g => lsum_Fpoly_one g cs,
    simplexInt_sq_FpolyM, simplexInt_eq_lsum, simplexInt_eq_lsum, lsum_Fsq_one]

/-- CONTROL: `Iform_eq`, restated by `type_of%`, from `IformM_eq` at `M = 1` (A2a's
`coeff_GM_one_pow` entering as `hG` until its merge). -/
theorem Iform_eq_ofM (hG : GMOneEq) : type_of% @Iform_eq := by
  have h1 : simplexInt (Fsq 105 F) = simplexInt (FsqM 1 105 (rekey1 F)) := by
    rw [simplexInt_eq_lsum, simplexInt_eq_lsum, lsum_Fsq_one]
  rw [h1, ← IformM_eq (basisIntM_one hG 105)]
  unfold IformM Iform rekey1
  simp only [List.map_map, Function.comp_def]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
  rw [← T105_eq,
    intg_eq_closed _ _ _ (by have := F_c_le x hx; have := F_c_le y hy; omega)]
  congr 1
  exact (closedM_one hG 105 (x.1.1 + y.1.1) (x.1.2 + y.1.2)).symm

/-- `FJg` (`JMain`) is the `M = 1` marginal list `FJM 1`, read back through the `Fin 1` key. -/
lemma FJg_eq_FJM_one (cs : List ((ℕ × ℕ) × ℤ)) :
    FJg cs = (FJM 1 (rekey1 cs)).map fun u => ((u.1.1, u.1.2 0), u.2) := by
  have ht : ∀ c, tuplesLE 1 (fun _ => c)
      = (List.range (c + 1)).map fun x => (Fin.cons x (fun m => m.elim0) : Fin 1 → ℕ) := by
    intro c
    simp only [tuplesLE, List.map_cons, List.map_nil]
    rw [← List.map_eq_flatMap]
  unfold FJg FJM rekey1
  simp only [List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun p _ => ?_
  rw [ht, List.map_map, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  have hw : weight (Fin.cons j (fun m => m.elim0) : Fin 1 → ℕ) = 2 * j := by simp [weight]
  simp only [Function.comp_apply, wJ, hw, Pi.sub_apply, Fin.cons_zero, Fin.prod_univ_one]
  refine Prod.ext (Prod.ext rfl rfl) ?_
  push_cast
  ring

/-- CONTROL: `Jform_eq`, restated by `type_of%`, from `JformM_eq` at `M = 1` (A2a's
`coeff_GM_one_pow` entering as `hG` until its merge). -/
theorem Jform_eq_ofM (hG : GMOneEq) : type_of% @Jform_eq := by
  intro m
  have h1 : simplexInt (sq (contractB m (Fpoly 105 F)))
      = simplexInt (sq (contractB m (FpolyM 1 105 (rekey1 F)))) := by
    apply simplexInt_sq_congr
    intro g
    rw [lsum_contractB, lsum_contractB, lsum_Fpoly_one]
  have hJ2 : J2 = J2M 1 105 (rekey1 F) := by
    have hFJ : FJ = (FJM 1 (rekey1 F)).map fun u => ((u.1.1, u.1.2 0), u.2) := FJg_eq_FJM_one F
    have hmem : ∀ u ∈ FJM 1 (rekey1 F), u.1.2 0 ≤ 5 := by
      intro u hu
      have h := FJ_c_le ((u.1.1, u.1.2 0), u.2) (by rw [hFJ]; exact List.mem_map_of_mem hu)
      exact h
    unfold J2 J2M
    rw [hFJ]
    simp only [List.map_map, Function.comp_def]
    refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
    refine congrArg List.sum (List.map_congr_left fun v hv => ?_)
    rw [← T104_eq,
      intg_eq_closed _ _ _ (by have := hmem u hu; have := hmem v hv; omega)]
    congr 1
    rw [fin_one_const (u.1.2 + v.1.2), closedM_one hG]
    rfl
  calc Jform = J2 := Jform_eq_J2
    _ = J2M 1 105 (rekey1 F) := hJ2
    _ = JformM 1 105 (rekey1 F) := (JformM_eq_J2M 1 105 _).symm
    _ = simplexInt (sq (contractB m (FpolyM 1 105 (rekey1 F)))) :=
        JformM_eq (n := 104) (basisIntM_one hG 104) m (rekey1 F)
    _ = simplexInt (sq (contractB m (Fpoly 105 F))) := h1.symm

end Salt.MaynardK
