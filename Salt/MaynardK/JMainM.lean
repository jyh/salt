/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.SquareM

/-!
# C1 glue at general `M` — the contracted square of `F`, and `J` as its Dirichlet integral

The `M`-variable generalisation of `JMain` (`contractB_Fpoly`, `simplexInt_sq_contractB`,
`Jform_eq`) and of `JSide` (`FJ`, `J2`, `Jform_eq_J2`).

* `contractB_basisPolyM_lsum` (with its `eval` and `simplexInt` forms): contracting coordinate `p`
  of one basis element `(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}` on `n + 1` coordinates gives the
  marginal `contractListM`: the concatenation over `j ≤ C` (componentwise) of
  `wJ a C j · basisPolyM M n (a + weight j + 1) (C − j)`, with
  `wJ a C j = Π_m C(C m, j m) · a!·(weight j)!/(a + weight j + 1)!`;
* `FJM`: the uncollected marginal list of a coefficient list (the `M`-twin of `FJ`), enumerated
  computably (`tuplesLE`); `J2M`: the uncollected double sum of closed forms over it, at the
  SUMMED exponents; `JformM`: the same double sum collected over the marginal keys;
  `JformM_eq_J2M`: the two groupings agree;
* `JformM_eq`: `JformM M (n+1) cs = simplexInt (sq (contractB p (FpolyM M (n+1) cs)))` at every
  coordinate `p`.

As in `SquareM`, A2a's `simplexInt_basisPolyM` enters as the hypothesis `BasisIntM` until its
merge; `simplexInt_sq_contractB_FpolyM` needs no hypothesis.
Pure polynomial algebra: nothing here bears on twin primes.
-/

open Finset Nat Salt.Twelve

namespace Salt.MaynardK

/-! ## The marginal exponents `j ≤ C`, enumerated computably -/

/-- the tuples `j` with `j m ≤ C m` for every `m`, in lexicographic order (head coordinate
outermost). At `M = 1` this is `List.range (C 0 + 1)`. -/
def tuplesLE : (M : ℕ) → (Fin M → ℕ) → List (Fin M → ℕ)
  | 0, _ => [fun m => m.elim0]
  | M + 1, C => (List.range (C 0 + 1)).flatMap fun x =>
      (tuplesLE M fun m => C m.succ).map fun y => (Fin.cons x y : Fin (M + 1) → ℕ)

lemma mem_tuplesLE : ∀ {M : ℕ} (C j : Fin M → ℕ), j ∈ tuplesLE M C ↔ ∀ m, j m ≤ C m := by
  intro M
  induction M with
  | zero =>
    intro C j
    simp only [tuplesLE, List.mem_singleton]
    constructor
    · intro _ m
      exact m.elim0
    · intro _
      funext m
      exact m.elim0
  | succ M ih =>
    intro C j
    simp only [tuplesLE, List.mem_flatMap, List.mem_range, List.mem_map, ih]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩ m
      refine Fin.cases ?_ (fun m => ?_) m
      · simp only [Fin.cons_zero]
        omega
      · simpa using hy m
    · intro h
      exact ⟨j 0, by have := h 0; omega, Fin.tail j, fun m => h m.succ, Fin.cons_self_tail j⟩

lemma nodup_tuplesLE : ∀ {M : ℕ} (C : Fin M → ℕ), (tuplesLE M C).Nodup := by
  intro M
  induction M with
  | zero =>
    intro C
    simp [tuplesLE]
  | succ M ih =>
    intro C
    rw [tuplesLE, List.nodup_flatMap]
    refine ⟨fun x _ => (ih _).map fun y y' h => by simpa using congrArg Fin.tail h, ?_⟩
    refine (List.nodup_range (n := C 0 + 1)).imp fun {x x'} hne => ?_
    intro v hv hv'
    rw [List.mem_map] at hv hv'
    obtain ⟨y, _, rfl⟩ := hv
    obtain ⟨y', _, hyy⟩ := hv'
    have h0 := congrFun hyy 0
    simp only [Fin.cons_zero] at h0
    exact hne h0.symm

lemma sum_tuplesLE {M : ℕ} {γ : Type*} [AddCommMonoid γ] (C : Fin M → ℕ) (f : (Fin M → ℕ) → γ) :
    ((tuplesLE M C).map f).sum = ∑ j ∈ Fintype.piFinset (fun m => range (C m + 1)), f j := by
  rw [← List.sum_toFinset f (nodup_tuplesLE C)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  rw [List.mem_toFinset, mem_tuplesLE, Fintype.mem_piFinset]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-! ## The contraction of one basis element -/

/-- the marginal weight of `j ≤ C`: `Π_m C(C m, j m) · a!·(weight j)!/(a + weight j + 1)!`. -/
def wJ {M : ℕ} (a : ℕ) (C j : Fin M → ℕ) : ℚ :=
  ((∏ m, (C m).choose (j m) : ℕ) : ℚ) * (a ! : ℕ) * ((weight j)! : ℕ) / ((a + weight j + 1)! : ℕ)

/-- the collected marginal of one basis element: `Σ_{j ≤ C} wJ a C j ·
(1 − P₁)^{a + weight j + 1} · Π_m P_{2(m+1)}^{C m − j m}` on `n` coordinates. -/
noncomputable def contractListM (M n a : ℕ) (C : Fin M → ℕ) : BPoly n :=
  (Fintype.piFinset fun m => range (C m + 1)).toList.flatMap fun j =>
    scale (wJ a C j) (basisPolyM M n (a + weight j + 1) (C - j))

lemma multM_split {M n : ℕ} (p : Fin (n + 1)) (C : Fin M → ℕ) (e : Fin M → Fin (n + 1) → ℕ)
    (he : e ∈ asgM M (n + 1) C) :
    multM e = (∏ m, (C m).choose (e m p)) * multM (fun m => Fin.removeNth p (e m)) := by
  unfold multM
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  have hs : ∑ i, e m i = C m := (mem_piAntidiag.mp (Fintype.mem_piFinset.mp he m)).1
  have h := multinomial_split p (e m)
  rw [hs] at h
  exact_mod_cast h

/-- **splitting the assignment tuples at coordinate `p`:** `e ↦ (j, e′)` with `j m = e m p` and
`e′ m = removeNth p (e m)`, `mult e = Π_m C(C m, j m) · mult e′` (`sum_piAntidiag_split` once
per `m`). -/
theorem sum_asgM_split {R : Type*} [CommSemiring R] {M n : ℕ} (p : Fin (n + 1)) (C : Fin M → ℕ)
    (Ψ : (Fin M → ℕ) → (Fin M → Fin n → ℕ) → R) :
    ∑ e ∈ asgM M (n + 1) C,
        ((multM e : ℕ) : R) * Ψ (fun m => e m p) (fun m => Fin.removeNth p (e m))
      = ∑ j ∈ Fintype.piFinset (fun m => range (C m + 1)), ((∏ m, (C m).choose (j m) : ℕ) : R) *
          ∑ e' ∈ asgM M n (C - j), ((multM e' : ℕ) : R) * Ψ j e' := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun e => ⟨fun m => e m p, fun m => Fin.removeNth p (e m)⟩)
    (fun x => fun m => Fin.insertNth p (x.1 m) (x.2 m)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have he' := Fintype.mem_piFinset.mp he
    have hs : ∀ m, ∑ i, e m i = C m := fun m => (mem_piAntidiag.mp (he' m)).1
    have hsplit : ∀ m, ∑ i, e m i = e m p + ∑ i, Fin.removeNth p (e m) i := fun m => by
      rw [Fin.sum_univ_succAbove (e m) p]; rfl
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Fintype.mem_piFinset]
    refine ⟨fun m => ?_, fun m => ?_⟩
    · rw [Finset.mem_range]
      change e m p < C m + 1
      have := hs m
      have := hsplit m
      omega
    · rw [mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      change ∑ i, Fin.removeNth p (e m) i = C m - e m p
      have := hs m
      have := hsplit m
      omega
  · intro x hx
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    intro m
    rw [mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    change ∑ i, Fin.insertNth p (x.1 m) (x.2 m) i = C m
    have h1 := Finset.mem_range.mp (hx.1 m)
    have h2 : ∑ i, x.2 m i = C m - x.1 m := (mem_piAntidiag.mp (hx.2 m)).1
    have hs := Fin.sum_univ_succAbove (Fin.insertNth p (x.1 m) (x.2 m)) p
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hs
    rw [hs, h2]
    omega
  · intro e _
    funext m
    exact Fin.insertNth_self_removeNth p (e m)
  · intro x _
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
  · intro e he
    dsimp only
    rw [multM_split p C e he]
    push_cast
    ring

lemma contractB_basisPolyM_eq {M n : ℕ} (p : Fin (n + 1)) (a : ℕ) (C : Fin M → ℕ) :
    contractB p (basisPolyM M (n + 1) a C) = (asgM M (n + 1) C).toList.map fun e =>
      (Fin.removeNth p (expoM e), expoM e p + a + 1,
        ((multM e : ℕ) : ℚ) * (((expoM e p)! * a ! : ℕ) : ℚ) / ((expoM e p + a + 1)! : ℕ)) := by
  unfold contractB
  rw [basisPolyM_eq, List.map_map]
  rfl

/-- **the contraction of one basis element is its collected marginal**, for every
coefficient-linear functional (in particular `eval` and `simplexInt`, below). -/
theorem contractB_basisPolyM_lsum {R : Type*} [Field R] [CharZero R] {M n : ℕ} (p : Fin (n + 1))
    (a : ℕ) (C : Fin M → ℕ) (g : (Fin n → ℕ) → ℕ → R) :
    lsum g (contractB p (basisPolyM M (n + 1) a C)) = lsum g (contractListM M n a C) := by
  set Ψ : (Fin M → ℕ) → (Fin M → Fin n → ℕ) → R := fun j e' =>
    (((weight j)! * a ! : ℕ) : R) / ((a + weight j + 1)! : ℕ) * g (expoM e') (a + weight j + 1)
    with hΨ
  have hL : lsum g (contractB p (basisPolyM M (n + 1) a C))
      = ∑ e ∈ asgM M (n + 1) C,
          ((multM e : ℕ) : R) * Ψ (fun m => e m p) (fun m => Fin.removeNth p (e m)) := by
    rw [contractB_basisPolyM_eq]
    unfold lsum
    rw [List.map_map, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hw : expoM e p = weight (fun m => e m p) := rfl
    have hr : Fin.removeNth p (expoM e) = expoM (fun m => Fin.removeNth p (e m)) := rfl
    have hb : expoM e p + a + 1 = a + weight (fun m => e m p) + 1 := by rw [hw]; ring
    simp only [Function.comp_apply, hΨ, hr, hb]
    rw [hw]
    push_cast
    ring
  rw [hL, sum_asgM_split]
  unfold contractListM
  rw [lsum_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lsum_scale, lsum_basisPolyM, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' _ => ?_
  simp only [hΨ, wJ]
  push_cast
  ring

theorem contractB_basisPolyM_eval {M n : ℕ} (p : Fin (n + 1)) (a : ℕ) (C : Fin M → ℕ)
    (t : Fin n → ℝ) :
    eval (contractB p (basisPolyM M (n + 1) a C)) t = eval (contractListM M n a C) t := by
  rw [eval_eq_lsum, eval_eq_lsum, contractB_basisPolyM_lsum]

theorem contractB_basisPolyM_simplexInt {M n : ℕ} (p : Fin (n + 1)) (a : ℕ) (C : Fin M → ℕ) :
    simplexInt (contractB p (basisPolyM M (n + 1) a C)) = simplexInt (contractListM M n a C) := by
  rw [simplexInt_eq_lsum, simplexInt_eq_lsum, contractB_basisPolyM_lsum]

lemma contractB_append' {n : ℕ} (p : Fin (n + 1)) (P Q : BPoly (n + 1)) :
    contractB p (P ++ Q) = contractB p P ++ contractB p Q := by
  unfold contractB
  exact List.map_append

/-- the contraction of `FpolyM`, term by term (the `M`-twin of `contractB_Fpoly`). -/
lemma contractB_FpolyM {M n : ℕ} (p : Fin (n + 1)) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    contractB p (FpolyM M (n + 1) cs)
      = cs.flatMap fun x => scale (x.2 : ℚ) (contractB p (basisPolyM M (n + 1) x.1.1 x.1.2)) := by
  unfold FpolyM
  induction cs with
  | nil => rfl
  | cons x cs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, contractB_append', ih, contractB_scale]

/-- a coefficient-linear functional of a contraction is a coefficient-linear functional of the
uncontracted polynomial. -/
lemma lsum_contractB {R : Type*} [Field R] [CharZero R] {n : ℕ} (p : Fin (n + 1))
    (g : (Fin n → ℕ) → ℕ → R) (P : BPoly (n + 1)) :
    lsum g (contractB p P) = lsum (fun e d => (((e p)! * d ! : ℕ) : R) / ((e p + d + 1)! : ℕ) *
      g (Fin.removeNth p e) (e p + d + 1)) P := by
  unfold lsum contractB
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
  simp only [Function.comp_apply]
  push_cast
  ring

/-! ## `J` at general `M` -/

/-- the uncollected marginal list of `F` (the `M`-twin of `FJ`): one entry per term
`(a, C, c)` of `cs` and per `j ≤ C`, at `(a + weight j + 1, C − j)` with weight `c · wJ a C j`. -/
def FJM (M : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : List ((ℕ × (Fin M → ℕ)) × ℚ) :=
  cs.flatMap fun x => (tuplesLE M x.1.2).map fun j =>
    ((x.1.1 + weight j + 1, x.1.2 - j), (x.2 : ℚ) * wJ x.1.1 x.1.2 j)

/-- `J` as an uncollected double sum over `FJM` (the `M`-twin of `J2`), closed forms at the
SUMMED exponents. -/
noncomputable def J2M (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : ℚ :=
  ((FJM M cs).map fun u => ((FJM M cs).map fun v =>
    u.2 * v.2 * closedM M (k - 1) (u.1.1 + v.1.1) (u.1.2 + v.1.2)).sum).sum

/-- the marginal keys `(E, G)` of `FJM`. -/
def keysJM (M : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : Finset (ℕ × (Fin M → ℕ)) :=
  ((FJM M cs).map Prod.fst).toFinset

/-- the collected weight of a marginal key. -/
def wtJM (M : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) (K : ℕ × (Fin M → ℕ)) : ℚ :=
  (((FJM M cs).filter fun u => u.1 = K).map Prod.snd).sum

/-- `J` at general `M`, collected over the marginal keys `(E, G)`, `(E′, G′)`:
`Σ w·w′·(E + E′)!·Π_m (G m + G′ m)!·[x^{G+G′}] GM^{k−1} / (k − 1 + E + E′ + weight (G + G′))!`. -/
noncomputable def JformM (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) : ℚ :=
  ∑ K ∈ keysJM M cs, ∑ K' ∈ keysJM M cs,
    wtJM M cs K * wtJM M cs K' * closedM M (k - 1) (K.1 + K'.1) (K.2 + K'.2)

/-- a list sum, split over the fibres of a key. -/
lemma list_sum_fiber {α β : Type*} [DecidableEq α] (L : List (α × β)) (h : α × β → ℚ)
    (S : Finset α) (hS : ∀ u ∈ L, u.1 ∈ S) :
    (L.map h).sum = ∑ K ∈ S, ((L.filter fun u => u.1 = K).map h).sum := by
  induction L with
  | nil => simp
  | cons u L ih =>
    have hu := hS u List.mem_cons_self
    rw [List.map_cons, List.sum_cons, ih fun v hv => hS v (List.mem_cons_of_mem _ hv)]
    have hK : ∀ K, ((List.filter (fun v => decide (v.1 = K)) (u :: L)).map h).sum
        = (if u.1 = K then h u else 0) + ((L.filter fun v => decide (v.1 = K)).map h).sum := by
      intro K
      by_cases hk : u.1 = K <;> simp [hk]
    rw [Finset.sum_congr rfl fun K _ => hK K, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hu]

/-- **collected = uncollected** (the `M`-twin of `Jform_eq_J2`, here for EVERY coefficient list,
by bilinearity, not by kernel reduction). -/
theorem JformM_eq_J2M (M k : ℕ) (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    JformM M k cs = J2M M k cs := by
  set L := FJM M cs with hLdef
  set cl : ℕ × (Fin M → ℕ) → ℕ × (Fin M → ℕ) → ℚ := fun K K' =>
    closedM M (k - 1) (K.1 + K'.1) (K.2 + K'.2) with hcl
  have hS : ∀ u ∈ L, u.1 ∈ keysJM M cs := fun u hu =>
    List.mem_toFinset.mpr (List.mem_map_of_mem hu)
  have hfil : ∀ K (X : ℚ), ((L.filter fun u => u.1 = K).map fun u => u.2 * X).sum
      = wtJM M cs K * X := by
    intro K X
    unfold wtJM
    rw [← hLdef, List.sum_map_mul_right]
  have hinner : ∀ (K : ℕ × (Fin M → ℕ)) (x : ℚ),
      (L.map fun v => x * v.2 * cl K v.1).sum
        = x * ∑ K' ∈ keysJM M cs, wtJM M cs K' * cl K K' := by
    intro K x
    rw [list_sum_fiber L _ _ hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K' _ => ?_
    rw [← hfil K' (cl K K')]
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun v hv => ?_)
    have hv1 : v.1 = K' := by simpa using (List.mem_filter.mp hv).2
    rw [hv1]
    ring
  unfold JformM J2M
  rw [← hLdef]
  change ∑ K ∈ keysJM M cs, ∑ K' ∈ keysJM M cs, wtJM M cs K * wtJM M cs K' * cl K K'
    = (L.map fun u => (L.map fun v => u.2 * v.2 * cl u.1 v.1).sum).sum
  rw [list_sum_fiber L _ _ hS]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hu : ∀ u ∈ L.filter (fun u => u.1 = K),
      (L.map fun v => u.2 * v.2 * cl u.1 v.1).sum
        = u.2 * ∑ K' ∈ keysJM M cs, wtJM M cs K' * cl K K' := by
    intro u hu
    have hu1 : u.1 = K := by simpa using (List.mem_filter.mp hu).2
    rw [hu1, hinner]
  rw [List.map_congr_left hu, hfil, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K' _ => ?_
  ring

/-- the contracted square of `FpolyM` has the integral of the list square of `FpolyQ` over its
marginal list `FJM` (no hypothesis). -/
theorem simplexInt_sq_contractB_FpolyM {M n : ℕ} (p : Fin (n + 1))
    (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    simplexInt (sq (contractB p (FpolyM M (n + 1) cs)))
      = simplexInt (sq (FpolyQ M n (FJM M cs))) := by
  apply simplexInt_sq_congr
  intro g
  rw [contractB_FpolyM, lsum_flatMap]
  unfold FpolyQ
  rw [lsum_flatMap, FJM, list_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  rw [lsum_scale, contractB_basisPolyM_lsum, contractListM, lsum_flatMap, Finset.sum_map_toList,
    List.map_map, sum_tuplesLE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, lsum_scale, Rat.cast_id]
  ring

/-- **`J2M` is the Dirichlet integral of the contracted square of `F`, at every coordinate.** -/
theorem J2M_eq {M n : ℕ} (hS : BasisIntM M n) (p : Fin (n + 1))
    (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    J2M M (n + 1) cs = simplexInt (sq (contractB p (FpolyM M (n + 1) cs))) := by
  rw [simplexInt_sq_contractB_FpolyM, simplexInt_sq_FpolyQ]
  unfold BasisIntM at hS
  unfold J2M
  simp only [Nat.add_sub_cancel, hS]

/-- **`J` at general `M` is the Dirichlet integral of the contracted square of `F`, at every
coordinate** (the `M`-twin of `Jform_eq`). -/
theorem JformM_eq {M n : ℕ} (hS : BasisIntM M n) (p : Fin (n + 1))
    (cs : List ((ℕ × (Fin M → ℕ)) × ℤ)) :
    JformM M (n + 1) cs = simplexInt (sq (contractB p (FpolyM M (n + 1) cs))) :=
  (JformM_eq_J2M M (n + 1) cs).trans (J2M_eq hS p cs)

end Salt.MaynardK
