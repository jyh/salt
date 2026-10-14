/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.A2aStandIn
import Salt.MaynardK.F1

/-!
# C1 glue at general `M` — Maynard's `F` and `F²` over the basis `(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}`

The `M`-variable generalisation of `Square` (`Fpoly`, `Fsq`, `eval_Fsq`, `simplexInt_Fsq`), of
`F1.simplexInt_sq_Fpoly` and of `F1.eval_Fpoly_abs_le`. A coefficient list
`cs : List ((ℕ × (Fin M → ℕ)) × ℤ)` carries, per term, the exponent `a` of `1 − P₁`, the exponents
`C m` of the power sums `P_{2(m+1)}`, and an integer coefficient.

* `FpolyM M k cs` is `F` and `FsqM M k cs` is the pairwise expansion of `F²`; `eval_FsqM`:
  `eval (FsqM …) = (eval (FpolyM …))²` pointwise;
* `closedM M k a C = a!·Π_m (C m)!·[x^C] GM^k / (k + a + weight C)!` (the `M`-twin of `closed`);
  `simplexInt_FsqM` and `IformM_eq`: the Dirichlet integral of `F²` is the double sum of closed
  forms at the SUMMED exponents `(a + a′, C + C′)`;
* `simplexInt_sq_FpolyM`: the list square `sq (FpolyM …)` has the integral of `FsqM …`, through
  `multM_conv`, the multinomial convolution of assignment tuples (`mult_conv` once per `m`);
* `eval_FpolyM_abs_le`: `|F| ≤ Σ|c|` on the simplex.

The basis `basisPolyM` and the series `GM` are node A2a's (`SeriesM`/`BasisM`); until its merge
they come from `A2aStandIn`, and its two results enter here as the hypotheses `BasisEvalM` and
`BasisIntM` (discharged at the merge by `eval_basisPolyM` and `simplexInt_basisPolyM`). The
statements that do not need them (`simplexInt_sq_FpolyQ`, `simplexInt_sq_FpolyM`) carry none.
Pure polynomial algebra: nothing here bears on twin primes.
-/

open Finset Nat Salt.Twelve

namespace Salt.MaynardK

/-! ## A2a's two results, as hypotheses until its merge -/

/-- A2a's `eval_basisPolyM`, as a hypothesis: the basis evaluates to
`(1 − Σt)^a · Π_m (Σ_i t_i^{2(m+1)})^{C m}`. -/
def BasisEvalM (M k : ℕ) : Prop :=
  ∀ (a : ℕ) (C : Fin M → ℕ) (t : Fin k → ℝ), eval (basisPolyM M k a C) t
      = (1 - ∑ i, t i) ^ a * ∏ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (C m)

/-- the closed form of `∫_{R_k} (1 − P₁)^a · Π_m P_{2(m+1)}^{C m}`:
`a!·Π_m (C m)!·[x^C] GM^k / (k + a + weight C)!`. At `M = 1` it is `closed`. -/
noncomputable def closedM (M k a : ℕ) (C : Fin M → ℕ) : ℚ :=
  ((a ! : ℕ) : ℚ) * (∏ m, (((C m)! : ℕ) : ℚ)) *
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm C) (GM M ^ k)
    / (((k + a + weight C)! : ℕ) : ℚ)

/-- A2a's `simplexInt_basisPolyM`, as a hypothesis: the basis has the closed-form integral. -/
def BasisIntM (M k : ℕ) : Prop :=
  ∀ (a : ℕ) (C : Fin M → ℕ), simplexInt (basisPolyM M k a C) = closedM M k a C

/-! ## Assignment tuples and the basis written out -/

/-- the assignment tuples of `C`: one antidiagonal of `C m` on `k` coordinates per `m`. -/
abbrev asgM (M k : ℕ) (C : Fin M → ℕ) : Finset (Fin M → Fin k → ℕ) :=
  Fintype.piFinset fun m => piAntidiag (univ : Finset (Fin k)) (C m)

/-- the `t`-exponent of an assignment tuple: `i ↦ Σ_m 2(m+1)·e m i`. -/
def expoM {M k : ℕ} (e : Fin M → Fin k → ℕ) : Fin k → ℕ :=
  fun i => ∑ m : Fin M, 2 * ((m : ℕ) + 1) * e m i

/-- the coefficient of an assignment tuple: `Π_m multinomial (e m)`. -/
def multM {M k : ℕ} (e : Fin M → Fin k → ℕ) : ℕ := ∏ m, Nat.multinomial univ (e m)

lemma basisPolyM_eq (M k a : ℕ) (C : Fin M → ℕ) :
    basisPolyM M k a C = (asgM M k C).toList.map fun e => (expoM e, a, ((multM e : ℕ) : ℚ)) :=
  rfl

lemma expoM_add {M k : ℕ} (e f : Fin M → Fin k → ℕ) : expoM (e + f) = expoM e + expoM f := by
  funext i
  simp only [expoM, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-! ## Coefficient-linear functionals of a budget polynomial -/

/-- `Σ_u c_u · g(e_u, d_u)` over the monomials `(e_u, d_u, c_u)` of `P`: `eval` and `simplexInt`
are both of this form (`eval_eq_lsum`, `simplexInt_eq_lsum`). -/
def lsum {n : ℕ} {R : Type*} [DivisionRing R] (g : (Fin n → ℕ) → ℕ → R) (P : BPoly n) : R :=
  (P.map fun u => (u.2.2 : R) * g u.1 u.2.1).sum

lemma lsum_append {n : ℕ} {R : Type*} [Field R] [CharZero R] (g : (Fin n → ℕ) → ℕ → R)
    (p q : BPoly n) :
    lsum g (p ++ q) = lsum g p + lsum g q := by
  simp only [lsum, List.map_append, List.sum_append]

lemma lsum_flatMap {n : ℕ} {R : Type*} [Field R] [CharZero R] {γ : Type*}
    (g : (Fin n → ℕ) → ℕ → R) (l : List γ) (f : γ → BPoly n) :
    lsum g (l.flatMap f) = (l.map fun x => lsum g (f x)).sum := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => rw [List.flatMap_cons, lsum_append, ih, List.map_cons, List.sum_cons]

lemma lsum_scale {n : ℕ} {R : Type*} [Field R] [CharZero R] (g : (Fin n → ℕ) → ℕ → R)
    (c : ℚ) (P : BPoly n) :
    lsum g (scale c P) = (c : R) * lsum g P := by
  unfold lsum scale
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  simp only [Function.comp_apply, Rat.cast_mul]
  ring

lemma lsum_basisPolyM {n : ℕ} {R : Type*} [Field R] [CharZero R] {M : ℕ}
    (g : (Fin n → ℕ) → ℕ → R) (a : ℕ) (C : Fin M → ℕ) :
    lsum g (basisPolyM M n a C) = ∑ e ∈ asgM M n C, ((multM e : ℕ) : R) * g (expoM e) a := by
  rw [basisPolyM_eq]
  unfold lsum
  rw [List.map_map, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Function.comp_apply, Rat.cast_natCast]

lemma lsum_congr_flatMap {n : ℕ} {R : Type*} [Field R] [CharZero R] {γ : Type*}
    (g : (Fin n → ℕ) → ℕ → R) (l : List γ)
    (f f' : γ → BPoly n) (h : ∀ x ∈ l, lsum g (f x) = lsum g (f' x)) :
    lsum g (l.flatMap f) = lsum g (l.flatMap f') := by
  rw [lsum_flatMap, lsum_flatMap]
  exact congrArg List.sum (List.map_congr_left h)

lemma eval_eq_lsum {n : ℕ} (P : BPoly n) (t : Fin n → ℝ) :
    eval P t = lsum (fun e d => (∏ i, t i ^ e i) * (1 - ∑ i, t i) ^ d) P := by
  unfold eval lsum
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  ring

lemma simplexInt_eq_lsum {n : ℕ} (P : BPoly n) : simplexInt P = lsum (R := ℚ) DInt' P := by
  unfold simplexInt lsum
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  simp only [Rat.cast_id]

lemma simplexInt_basisPolyM_sum (M k a : ℕ) (C : Fin M → ℕ) :
    simplexInt (basisPolyM M k a C)
      = ∑ e ∈ asgM M k C, ((multM e : ℕ) : ℚ) * DInt' (expoM e) a := by
  rw [simplexInt_eq_lsum, lsum_basisPolyM]

/-- two budget polynomials with the same coefficient-linear functionals have the same squared
integral (`simplexInt ∘ sq` is a bilinear form in the monomials). -/
theorem simplexInt_sq_congr {n : ℕ} {P Q : BPoly n}
    (h : ∀ g : (Fin n → ℕ) → ℕ → ℚ, lsum g P = lsum g Q) :
    simplexInt (sq P) = simplexInt (sq Q) := by
  have inner : ∀ (u : (Fin n → ℕ) × ℕ × ℚ) (X : BPoly n),
      (X.map fun v => u.2.2 * v.2.2 * DInt' (u.1 + v.1) (u.2.1 + v.2.1)).sum
        = u.2.2 * lsum (fun e d => DInt' (u.1 + e) (u.2.1 + d)) X := by
    intro u X
    unfold lsum
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
    simp only [Rat.cast_id]
    ring
  have outer : ∀ X : BPoly n,
      (X.map fun u => u.2.2 * lsum (fun e d => DInt' (u.1 + e) (u.2.1 + d)) Q).sum
        = lsum (fun e' d' => lsum (fun e d => DInt' (e' + e) (d' + d)) Q) X := by
    intro X
    unfold lsum
    refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
    simp only [Rat.cast_id]
  rw [Salt.Twelve.sq, Salt.Twelve.sq, simplexInt_mul, simplexInt_mul]
  simp only [inner, h]
  rw [outer P, outer Q, h]

/-! ## The multinomial convolution of assignment tuples -/

/-- splitting a sum over a `Fin (M + 1)`-indexed `piFinset` at the head coordinate. -/
lemma sum_piFinset_cons {M : ℕ} {β γ : Type*} [AddCommMonoid γ]
    (t : Fin (M + 1) → Finset β) (g : (Fin (M + 1) → β) → γ) :
    ∑ e ∈ Fintype.piFinset t, g e
      = ∑ x ∈ t 0, ∑ y ∈ Fintype.piFinset (fun m : Fin M => t m.succ),
          g (Fin.cons x y : Fin (M + 1) → β) := by
  rw [← Finset.sum_product' (f := fun x y => g (Fin.cons x y : Fin (M + 1) → β))]
  refine Finset.sum_nbij' (fun e => (e 0, Fin.tail e))
    (fun p => (Fin.cons p.1 p.2 : Fin (M + 1) → β)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [Fintype.mem_piFinset] at he
    rw [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨he 0, fun m => he m.succ⟩
  · intro p hp
    rw [Finset.mem_product, Fintype.mem_piFinset] at hp
    rw [Fintype.mem_piFinset]
    intro m
    refine Fin.cases ?_ (fun m => ?_) m
    · simpa using hp.1
    · simpa using hp.2 m
  · intro e _
    exact Fin.cons_self_tail e
  · intro p _
    simp
  · intro e _
    simp only [Fin.cons_self_tail]

lemma multM_cons {M k : ℕ} (x : Fin k → ℕ) (y : Fin M → Fin k → ℕ) :
    multM (Fin.cons x y : Fin (M + 1) → Fin k → ℕ) = Nat.multinomial univ x * multM y := by
  unfold multM
  rw [Fin.prod_univ_succ]
  simp

lemma cons_add_cons' {M : ℕ} {β : Type*} [Add β] (x x' : β) (y y' : Fin M → β) :
    (Fin.cons x y : Fin (M + 1) → β) + Fin.cons x' y' = Fin.cons (x + x') (y + y') := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma asgM_zero (k : ℕ) (C : Fin 0 → ℕ) : asgM 0 k C = {fun m => Fin.elim0 m} := by
  ext e
  rw [Finset.mem_singleton]
  constructor
  · intro _
    funext m
    exact m.elim0
  · intro _
    rw [Fintype.mem_piFinset]
    intro m
    exact m.elim0

/-- **The multinomial convolution of assignment tuples:**
`Σ_{e ⊨ C} Σ_{f ⊨ C′} mult e · mult f · phi(e + f) = Σ_{h ⊨ C + C′} mult h · phi h`
(`mult_conv` once per `m`). -/
theorem multM_conv {k : ℕ} : ∀ {M : ℕ} (C C' : Fin M → ℕ) (phi : (Fin M → Fin k → ℕ) → ℚ),
    ∑ e ∈ asgM M k C, ∑ f ∈ asgM M k C', ((multM e : ℕ) : ℚ) * (multM f : ℕ) * phi (e + f)
      = ∑ h ∈ asgM M k (C + C'), ((multM h : ℕ) : ℚ) * phi h := by
  intro M
  induction M with
  | zero =>
    intro C C' phi
    simp only [asgM_zero, Finset.sum_singleton]
    have h0 : ∀ e : Fin 0 → Fin k → ℕ, multM e = 1 := fun e => by simp [multM]
    have h1 : ((fun m => Fin.elim0 m) + (fun m => Fin.elim0 m) : Fin 0 → Fin k → ℕ)
        = fun m => Fin.elim0 m := funext fun m => m.elim0
    rw [h1]
    simp [h0]
  | succ M ih =>
    intro C C' phi
    have hL : ∀ (D : Fin (M + 1) → ℕ) (G : (Fin (M + 1) → Fin k → ℕ) → ℚ),
        ∑ e ∈ asgM (M + 1) k D, G e
          = ∑ x ∈ piAntidiag (univ : Finset (Fin k)) (D 0),
              ∑ y ∈ asgM M k (fun m => D m.succ), G (Fin.cons x y) :=
      fun D G => sum_piFinset_cons _ G
    set Ψ : (Fin k → ℕ) → ℚ := fun z =>
      ∑ w ∈ asgM M k (fun m => (C + C') m.succ), ((multM w : ℕ) : ℚ) * phi (Fin.cons z w) with hΨ
    have step : ∀ x ∈ piAntidiag (univ : Finset (Fin k)) (C 0),
        ∑ y ∈ asgM M k (fun m => C m.succ), ∑ f ∈ asgM (M + 1) k C',
            ((multM (Fin.cons x y : Fin (M + 1) → Fin k → ℕ) : ℕ) : ℚ) * (multM f : ℕ)
              * phi ((Fin.cons x y : Fin (M + 1) → Fin k → ℕ) + f)
          = ∑ x' ∈ piAntidiag (univ : Finset (Fin k)) (C' 0),
              ((Nat.multinomial univ x : ℕ) : ℚ) * (Nat.multinomial univ x' : ℕ) * Ψ (x + x') := by
      intro x _
      calc _ = ∑ y ∈ asgM M k (fun m => C m.succ), ∑ x' ∈ piAntidiag (univ : Finset (Fin k)) (C' 0),
              ∑ y' ∈ asgM M k (fun m => C' m.succ),
                ((Nat.multinomial univ x : ℕ) : ℚ) * (Nat.multinomial univ x' : ℕ) *
                  (((multM y : ℕ) : ℚ) * (multM y' : ℕ) * phi (Fin.cons (x + x') (y + y'))) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hL C']
            refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
            rw [multM_cons, multM_cons, cons_add_cons']
            push_cast
            ring
        _ = ∑ x' ∈ piAntidiag (univ : Finset (Fin k)) (C' 0),
              ((Nat.multinomial univ x : ℕ) : ℚ) * (Nat.multinomial univ x' : ℕ) *
                ∑ y ∈ asgM M k (fun m => C m.succ), ∑ y' ∈ asgM M k (fun m => C' m.succ),
                  ((multM y : ℕ) : ℚ) * (multM y' : ℕ) * phi (Fin.cons (x + x') (y + y')) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.mul_sum]
        _ = _ := by
            refine Finset.sum_congr rfl fun x' _ => ?_
            have hih := ih (fun m => C m.succ) (fun m => C' m.succ)
              (fun w => phi (Fin.cons (x + x') w))
            beta_reduce at hih
            rw [hih]
            rfl
    rw [hL C, Finset.sum_congr rfl fun x hx => step x hx]
    have hconv := mult_conv (k := k) (C 0) (C' 0) Ψ
    rw [hconv, hL (C + C')]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [hΨ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [multM_cons]
    push_cast
    ring

/-! ## `F` and `F²` -/

/-- `F = Σ c · (1 − P₁)^a · Π_m P_{2(m+1)}^{C m}` over a RATIONAL coefficient list (the form the
`J` side produces, `JMainM.FJM`). -/
noncomputable def FpolyQ (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℚ)) : BPoly k :=
  cs.flatMap fun x => scale x.2 (basisPolyM M k x.1.1 x.1.2)

/-- `F = Σ c · (1 − P₁)^a · Π_m P_{2(m+1)}^{C m}` (`a`, `C`, integer `c` per term). -/
noncomputable def FpolyM (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : BPoly k :=
  cs.flatMap fun x => scale (x.2 : ℚ) (basisPolyM M k x.1.1 x.1.2)

/-- `F²`, expanded pairwise. -/
noncomputable def FsqM (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : BPoly k :=
  cs.flatMap fun x => cs.flatMap fun y =>
    scale ((x.2 * y.2 : ℤ) : ℚ) (basisPolyM M k (x.1.1 + y.1.1) (x.1.2 + y.1.2))

lemma FpolyM_eq_FpolyQ (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    FpolyM M k cs = FpolyQ M k (cs.map fun x => (x.1, (x.2 : ℚ))) := by
  unfold FpolyM FpolyQ
  induction cs with
  | nil => rfl
  | cons x cs ih => simp only [List.flatMap_cons, List.map_cons, ih]

theorem eval_FsqM {M k : ℕ} (hE : BasisEvalM M k) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ))
    (t : Fin k → ℝ) : eval (FsqM M k cs) t = eval (FpolyM M k cs) t ^ 2 := by
  unfold BasisEvalM at hE
  unfold FsqM FpolyM
  rw [eval_flatMap, eval_flatMap, pow_two, list_sum_mul_sum]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [eval_flatMap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  simp only [eval_scale, hE, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  push_cast
  ring

/-- `I` at general `M`: the double sum of closed forms at the summed exponents. -/
noncomputable def IformM (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : ℚ :=
  (cs.map fun x => (cs.map fun y =>
    ((x.2 * y.2 : ℤ) : ℚ) * closedM M k (x.1.1 + y.1.1) (x.1.2 + y.1.2)).sum).sum

theorem simplexInt_FsqM {M k : ℕ} (hS : BasisIntM M k) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    simplexInt (FsqM M k cs) = (cs.map fun x => (cs.map fun y =>
      ((x.2 * y.2 : ℤ) : ℚ) * closedM M k (x.1.1 + y.1.1) (x.1.2 + y.1.2)).sum).sum := by
  unfold BasisIntM at hS
  unfold FsqM
  rw [simplexInt_flatMap]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [simplexInt_flatMap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  rw [simplexInt_scale, hS]

/-- **`I` at general `M` is the Dirichlet integral of `F²`.** -/
theorem IformM_eq {M k : ℕ} (hS : BasisIntM M k) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    IformM M k cs = simplexInt (FsqM M k cs) :=
  (simplexInt_FsqM hS cs).symm

lemma FpolyQ_eq (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℚ)) :
    FpolyQ M k cs = cs.flatMap fun x => (asgM M k x.1.2).toList.map fun e =>
      (expoM e, x.1.1, x.2 * ((multM e : ℕ) : ℚ)) := by
  unfold FpolyQ scale
  refine List.flatMap_congr fun x _ => ?_
  rw [basisPolyM_eq, List.map_map]
  rfl

/-- the list square of `FpolyQ` integrates as the pairwise double sum of basis integrals at the
summed exponents (no hypothesis: this is the convolution, not the closed form). -/
theorem simplexInt_sq_FpolyQ (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℚ)) :
    simplexInt (sq (FpolyQ M k cs)) = (cs.map fun x => (cs.map fun y =>
      x.2 * y.2 * simplexInt (basisPolyM M k (x.1.1 + y.1.1) (x.1.2 + y.1.2))).sum).sum := by
  rw [FpolyQ_eq, Salt.Twelve.sq, simplexInt_mul]
  simp only [list_sum_flatMap, List.map_map, Function.comp_def, Finset.sum_map_toList]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [finset_list_swap]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  rw [simplexInt_basisPolyM_sum, ← multM_conv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [expoM_add]
  ring

/-- **the list square of `FpolyM` has the same Dirichlet integral as its pairwise expansion `FsqM`**
(the `M`-twin of `simplexInt_sq_Fpoly`). -/
theorem simplexInt_sq_FpolyM (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    simplexInt (sq (FpolyM M k cs)) = simplexInt (FsqM M k cs) := by
  rw [FpolyM_eq_FpolyQ, simplexInt_sq_FpolyQ]
  unfold FsqM
  rw [simplexInt_flatMap]
  simp only [List.map_map, Function.comp_def, simplexInt_flatMap, simplexInt_scale]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  push_cast
  ring

/-! ## The pointwise bound -/

/-- the `ℓ¹` norm of a coefficient list. -/
def QsumM {M : ℕ} (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : ℚ := (cs.map fun x => |(x.2 : ℚ)|).sum

lemma basisM_val_bounds {M k : ℕ} (t : Fin k → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ≤ 1)
    (a : ℕ) (C : Fin M → ℕ) :
    0 ≤ (1 - ∑ i, t i) ^ a * ∏ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (C m) ∧
      (1 - ∑ i, t i) ^ a * ∏ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (C m) ≤ 1 := by
  have hti : ∀ i, t i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => ht0 j) (Finset.mem_univ i)).trans ht1
  have hP : ∀ m : Fin M, 0 ≤ ∑ i, t i ^ (2 * ((m : ℕ) + 1)) ∧
      ∑ i, t i ^ (2 * ((m : ℕ) + 1)) ≤ 1 := by
    intro m
    refine ⟨Finset.sum_nonneg fun i _ => pow_nonneg (ht0 i) _, ?_⟩
    calc ∑ i, t i ^ (2 * ((m : ℕ) + 1)) ≤ ∑ i, t i :=
          Finset.sum_le_sum fun i _ => pow_le_of_le_one (ht0 i) (hti i) (by omega)
      _ ≤ 1 := ht1
  have hb0 : 0 ≤ 1 - ∑ i, t i := by linarith
  have hs0 : 0 ≤ ∑ i, t i := Finset.sum_nonneg fun i _ => ht0 i
  have hb1 : 1 - ∑ i, t i ≤ 1 := by linarith
  have hprod0 : 0 ≤ ∏ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (C m) :=
    Finset.prod_nonneg fun m _ => pow_nonneg (hP m).1 _
  have hprod1 : ∏ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (C m) ≤ 1 :=
    Finset.prod_le_one (fun m _ => pow_nonneg (hP m).1 _)
      fun m _ => pow_le_one₀ (hP m).1 (hP m).2
  exact ⟨mul_nonneg (pow_nonneg hb0 _) hprod0,
    mul_le_one₀ (pow_le_one₀ hb0 hb1) hprod0 hprod1⟩

lemma eval_FpolyM {M k : ℕ} (hE : BasisEvalM M k) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ))
    (t : Fin k → ℝ) :
    eval (FpolyM M k cs) t = (cs.map fun x => (x.2 : ℝ) * ((1 - ∑ i, t i) ^ x.1.1 *
      ∏ m : Fin M, (∑ i, t i ^ (2 * ((m : ℕ) + 1))) ^ (x.1.2 m))).sum := by
  unfold BasisEvalM at hE
  unfold FpolyM
  rw [eval_flatMap]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [eval_scale, hE]
  push_cast
  ring

/-- **`|F| ≤ Σ|c|` on the simplex** (the `M`-twin of `eval_Fpoly_abs_le`). -/
theorem eval_FpolyM_abs_le {M k : ℕ} (hE : BasisEvalM M k) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ))
    (t : Fin k → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ≤ 1) :
    |eval (FpolyM M k cs) t| ≤ ((QsumM cs : ℚ) : ℝ) := by
  have hQ : ((QsumM cs : ℚ) : ℝ) = (cs.map fun x => |(x.2 : ℝ)|).sum := by
    unfold QsumM
    rw [Rat.cast_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    simp
  rw [hQ, eval_FpolyM hE]
  clear hQ
  induction cs with
  | nil => simp
  | cons x cs ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨h0, h1⟩ := basisM_val_bounds t ht0 ht1 x.1.1 x.1.2
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right (abs_nonneg _) h1

end Salt.MaynardK
