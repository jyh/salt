/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Transversal2
import Salt.Vmvt.HolderTwo

/-!
# VMVT node R3-c — the Hölder-over-residues transversal count (Vaughan PSU 24.5)

This file closes the last design gap before the VMVT induction assembles: the
transversal count `I(p) = Ncount(transBox)` obeys

  `I(p) ≤ p^{2(kr-k)} · x^k · k! · p^{k(k-1)/2} · J_k(k(r-1), (0, x/p+1])`.

Following catch #78 (the pure combinatorial frame provably *cannot* reach this),
the Hölder step is carried on the **integral side** via the landed Fourier
machinery (`integral_setGen_mul_conj` is fully general in the two boxes).

## The six rungs (see the freeze in `docs/exploration/s3-a3-design.md`)

* **c-1** `powerSumEq_sub_const` — translating the whole system by a constant `a`.
* **c-2** the block factorization `setGen(box) = Gdesig · (rest genFun)^{kr-k}`,
  via the transversal reindex `Fin (kr) ≃ Fin k ⊕ Fin (kr-k)` compatible with `e`.
* **c-3** the residue power-mean + `∫/∑` swap.
* **c-4** the mixed Parseval `∫‖Gdesig‖²‖g_a‖^{2b} = Ncount(mixBox a)`.
* **c-5** the fibration bounding `Ncount(mixBox a)`.
* **c-6** the assembly `transBox_Ncount_le`.
-/

namespace Salt.Vmvt

open Finset MeasureTheory
open scoped ComplexConjugate
open Salt.ExpSum

/-! ## c-1 — the system translation (binomial triangular, from `powerSums_translate`) -/

/-- **c-1.**  Power-sum equality is invariant under translating both tuples by a
constant `a`.  Immediate from the landed binomial `powerSums_translate` (the
`i = 0` term `b·(−a)^j` cancels on both sides). -/
theorem powerSumEq_sub_const (k b : ℕ) (a : ℤ) (m n : Fin b → ℤ) :
    PowerSumEq k b m n ↔
      PowerSumEq k b (fun q => m q - a) (fun q => n q - a) := by
  constructor
  · intro h
    have h2 := powerSums_translate (-a) h
    simpa only [← sub_eq_add_neg] using h2
  · intro h
    have h2 := powerSums_translate a h
    simpa only [sub_add_cancel] using h2

/-! ## The designated and mixed boxes -/

/-- The **designated box** `Ddesig`: `k`-tuples in `(0,x]^k` pairwise distinct
modulo `p`.  Its generating function `setGen k k Ddesig` is Vaughan's `Gdesig`. -/
noncomputable def desigBox (k x p : ℕ) : Finset (Fin k → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin k => Finset.Ioc (0 : ℤ) (x : ℤ)).filter
    (fun md => ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (md i - md j))

theorem mem_desigBox {k x p : ℕ} {md : Fin k → ℤ} :
    md ∈ desigBox k x p ↔
      (∀ i, md i ∈ Finset.Ioc (0 : ℤ) (x : ℤ)) ∧
      (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (md i - md j)) := by
  classical
  unfold desigBox
  rw [Finset.mem_filter, Fintype.mem_piFinset]

/-- The **mixed box** `mixBox a`: tuples in `(0,x]^{kr}` whose designated block is
distinct modulo `p` and whose every *rest* coordinate is `≡ a (mod p)`. -/
noncomputable def mixBox {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r)) (p : ℕ) (a : ℤ) :
    Finset (Fin (k * r) → ℤ) := by
  classical
  exact (solBox (k * r) x).filter
    (fun m => blockDistinctMod e p m ∧ ∀ q, q ∉ Set.range e → (p : ℤ) ∣ (m q - a))

theorem mem_mixBox {k r : ℕ} {x : ℕ} {e : Fin k → Fin (k * r)} {p : ℕ} {a : ℤ}
    {m : Fin (k * r) → ℤ} :
    m ∈ mixBox x e p a ↔
      (∀ q, m q ∈ Finset.Ioc (0 : ℤ) (x : ℤ)) ∧
      blockDistinctMod e p m ∧ (∀ q, q ∉ Set.range e → (p : ℤ) ∣ (m q - a)) := by
  classical
  unfold mixBox solBox
  rw [Finset.mem_filter, Fintype.mem_piFinset]

/-! ## The `setGen`-as-coordinate-product rewrite -/

/-- Any `setGen` is the sum over its tuples of the coordinate-block product
`∏_q gcoord(m q)` (immediate from `setGen_summand_eq_prod`). -/
theorem setGen_eq_sum_prod_gcoord (k b : ℕ) (D : Finset (Fin b → ℤ)) (α : Deg k → ℝ) :
    setGen k b D α = ∑ m ∈ D, ∏ q : Fin b, gcoord k α (m q) := by
  rw [setGen]
  exact Finset.sum_congr rfl (fun m _ => setGen_summand_eq_prod k b m α)

/-! ## c-2 — the transversal reindex `Fin (kr) ≃ Fin k ⊕ {q ∉ range e}` -/

/-- The generic **transversal box** with an arbitrary rest-predicate `P`: tuples in
`(0,x]^{kr}`, designated block distinct modulo `p`, and every rest coordinate
satisfying `P`.  `transBox = transRestBox (P = ⊤)`, `mixBox a = transRestBox
(P = (p ∣ ·−a))`. -/
noncomputable def transRestBox {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r)) (p : ℕ)
    (P : ℤ → Prop) : Finset (Fin (k * r) → ℤ) := by
  classical
  exact (solBox (k * r) x).filter
    (fun m => blockDistinctMod e p m ∧ ∀ q, q ∉ Set.range e → P (m q))

theorem mem_transRestBox {k r : ℕ} {x : ℕ} {e : Fin k → Fin (k * r)} {p : ℕ}
    {P : ℤ → Prop} {m : Fin (k * r) → ℤ} :
    m ∈ transRestBox x e p P ↔
      (∀ q, m q ∈ Finset.Ioc (0 : ℤ) (x : ℤ)) ∧
      blockDistinctMod e p m ∧ (∀ q, q ∉ Set.range e → P (m q)) := by
  classical
  unfold transRestBox solBox
  rw [Finset.mem_filter, Fintype.mem_piFinset]

/-- **c-2 (the combinatorial core).**  Reindexing the coordinate-product sum over
`transRestBox` along the transversal split `Fin (kr) ≃ Fin k ⊕ {q ∉ range e}`
factors it as (designated sum) · (rest sum)^{kr−k}. -/
theorem sum_prod_transRestBox {R : Type*} [CommSemiring R] {k r : ℕ}
    (x : ℕ) (g : ℤ → R) (e : Fin k → Fin (k * r)) (he : Function.Injective e)
    (p : ℕ) (P : ℤ → Prop) [DecidablePred P] :
    (∑ m ∈ transRestBox x e p P, ∏ q : Fin (k * r), g (m q))
      = (∑ md ∈ desigBox k x p, ∏ i : Fin k, g (md i))
        * (∑ v ∈ (Finset.Ioc (0 : ℤ) (x : ℤ)).filter P, g v) ^ (k * r - k) := by
  classical
  set B : Finset ℤ := (Finset.Ioc (0 : ℤ) (x : ℤ)).filter P with hBdef
  -- the reindex equiv σ : Fin (kr) ≃ Fin k ⊕ {q ∉ range e}
  set σ : Fin (k * r) ≃ Fin k ⊕ {q : Fin (k * r) // q ∉ Set.range e} :=
    (Equiv.sumCompl (· ∈ Set.range e)).symm.trans
      (Equiv.sumCongr (Equiv.ofInjective e he).symm (Equiv.refl _)) with hσdef
  have hσinl : ∀ a : Fin k, σ.symm (Sum.inl a) = e a := by
    intro a; simp [hσdef]
  have hσinr : ∀ b : {q : Fin (k * r) // q ∉ Set.range e},
      σ.symm (Sum.inr b) = (b : Fin (k * r)) := by
    intro b; simp [hσdef]
  have hσinr_notmem : ∀ b : {q : Fin (k * r) // q ∉ Set.range e},
      σ.symm (Sum.inr b) ∉ Set.range e := by
    intro b; rw [hσinr b]; exact b.2
  have hσe : ∀ a : Fin k, σ (e a) = Sum.inl a := by
    intro a; rw [← hσinl a, Equiv.apply_symm_apply]
  have hσcases : ∀ q, q ∉ Set.range e → ∃ b, σ q = Sum.inr b := by
    intro q hq
    rcases hqe : σ q with a | b
    · exact absurd ⟨a, by rw [← hσinl a, ← hqe, Equiv.symm_apply_apply]⟩ hq
    · exact ⟨b, rfl⟩
  -- cardinality of the rest index
  have hcardRange : Fintype.card {q : Fin (k * r) // q ∈ Set.range e} = k := by
    have h := Fintype.card_congr (Equiv.ofInjective e he)
    rw [Fintype.card_fin] at h
    exact h.symm
  have hcardRest : Fintype.card {q : Fin (k * r) // q ∉ Set.range e} = k * r - k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardRange]
  -- the rest power as a piFinset sum
  have hpow : ∑ rest ∈ (Fintype.piFinset fun _ : {q : Fin (k * r) // q ∉ Set.range e} => B),
        ∏ b, g (rest b) = (∑ v ∈ B, g v) ^ (k * r - k) := by
    have h := Finset.sum_prod_piFinset
      (ι := {q : Fin (k * r) // q ∉ Set.range e}) B (fun _ b => g b)
    rw [h, Finset.prod_const, Finset.card_univ, hcardRest]
  -- rewrite the RHS as a single sum over the product finset
  have hRHS : (∑ md ∈ desigBox k x p, ∏ i : Fin k, g (md i)) * (∑ v ∈ B, g v) ^ (k * r - k)
      = ∑ mn ∈ (desigBox k x p ×ˢ
          Fintype.piFinset fun _ : {q : Fin (k * r) // q ∉ Set.range e} => B),
          (∏ a, g (mn.1 a)) * (∏ b, g (mn.2 b)) := by
    rw [← hpow, Finset.sum_mul_sum, Finset.sum_product]
  rw [hRHS]
  refine Finset.sum_nbij'
    (fun m => (fun a => m (e a), fun b => m (σ.symm (Sum.inr b))))
    (fun mn => fun q => Sum.elim mn.1 mn.2 (σ q))
    ?_ ?_ ?_ ?_ ?_
  · -- hi : maps into the product box
    intro m hm
    rw [mem_transRestBox] at hm
    obtain ⟨hbox, hdist, hrest⟩ := hm
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [mem_desigBox]
      exact ⟨fun a => hbox (e a), fun i' j' hij => hdist i' j' hij⟩
    · rw [Fintype.mem_piFinset]
      intro b
      rw [hBdef, Finset.mem_filter]
      exact ⟨hbox (σ.symm (Sum.inr b)), hrest (σ.symm (Sum.inr b)) (hσinr_notmem b)⟩
  · -- hj : maps back into transRestBox
    intro mn hmn
    rw [Finset.mem_product, mem_desigBox, Fintype.mem_piFinset] at hmn
    obtain ⟨⟨hmdbox, hmddist⟩, hrest⟩ := hmn
    rw [mem_transRestBox]
    refine ⟨?_, ?_, ?_⟩
    · intro q
      rcases hq : σ q with a | b
      · simpa only [hq, Sum.elim_inl] using hmdbox a
      · have hb := hrest b
        rw [hBdef, Finset.mem_filter] at hb
        simpa only [hq, Sum.elim_inr] using hb.1
    · intro i' j' hij
      change ¬ (p : ℤ) ∣ (Sum.elim mn.1 mn.2 (σ (e i')) - Sum.elim mn.1 mn.2 (σ (e j')))
      rw [hσe i', hσe j', Sum.elim_inl, Sum.elim_inl]
      exact hmddist i' j' hij
    · intro q hq
      obtain ⟨b, hb⟩ := hσcases q hq
      rw [hb, Sum.elim_inr]
      have hbmem := hrest b
      rw [hBdef, Finset.mem_filter] at hbmem
      exact hbmem.2
  · -- left_inv
    intro m _
    funext q
    change Sum.elim (fun a => m (e a)) (fun b => m (σ.symm (Sum.inr b))) (σ q) = m q
    rcases hq : σ q with a | b
    · rw [Sum.elim_inl]
      exact congrArg m (by rw [← hσinl a, ← hq, Equiv.symm_apply_apply])
    · rw [Sum.elim_inr]
      exact congrArg m (by rw [← hq, Equiv.symm_apply_apply])
  · -- right_inv
    intro mn _
    refine Prod.ext (funext fun a => ?_) (funext fun b => ?_)
    · change Sum.elim mn.1 mn.2 (σ (e a)) = mn.1 a
      rw [hσe a, Sum.elim_inl]
    · change Sum.elim mn.1 mn.2 (σ (σ.symm (Sum.inr b))) = mn.2 b
      rw [Equiv.apply_symm_apply, Sum.elim_inr]
  · -- integrand match
    intro m _
    change (∏ q, g (m q)) = (∏ a, g (m (e a))) * ∏ b, g (m (σ.symm (Sum.inr b)))
    have e1 : (∏ a, g (m (e a))) = ∏ a, g (m (σ.symm (Sum.inl a))) :=
      Finset.prod_congr rfl (fun a _ => by rw [hσinl a])
    rw [e1, ← Fintype.prod_sum_type (fun s => g (m (σ.symm s)))]
    exact Fintype.prod_equiv σ _ _ (fun q => by rw [Equiv.symm_apply_apply])

/-- **c-2 (the `setGen` factorization).**  The transversal generating function
factors as `Gdesig · (rest genFun)^{kr−k}`. -/
theorem setGen_transRestBox_factor {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (he : Function.Injective e) (p : ℕ) (P : ℤ → Prop) [DecidablePred P] (α : Deg k → ℝ) :
    setGen k (k * r) (transRestBox x e p P) α
      = setGen k k (desigBox k x p) α
        * (genFun k ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter P) α) ^ (k * r - k) := by
  rw [setGen_eq_sum_prod_gcoord, sum_prod_transRestBox x (gcoord k α) e he p P,
    ← setGen_eq_sum_prod_gcoord, ← genFun_eq_sum_gcoord]

/-- `transBox` is the `P = ⊤` transversal box. -/
theorem transBox_eq_transRestBox {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r)) (p : ℕ) :
    transBox x e p = transRestBox x e p (fun _ => True) := by
  classical
  ext m
  rw [mem_transRestBox]
  unfold transBox solBox
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => ⟨h.1, h.2, fun _ _ => trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-- `mixBox a` is the `P = (p ∣ ·−a)` transversal box. -/
theorem mixBox_eq_transRestBox {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r)) (p : ℕ) (a : ℤ) :
    mixBox x e p a = transRestBox x e p (fun v => (p : ℤ) ∣ (v - a)) := by
  classical
  ext m
  simp only [mem_mixBox, mem_transRestBox]

/-- **The transBox factorization.**  `setGen(transBox) = Gdesig · f^{kr−k}`, with
`f = genFun k (0,x]`. -/
theorem setGen_transBox_factor {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (he : Function.Injective e) (p : ℕ) (α : Deg k → ℝ) :
    setGen k (k * r) (transBox x e p) α
      = setGen k k (desigBox k x p) α
        * (genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α) ^ (k * r - k) := by
  classical
  rw [transBox_eq_transRestBox, setGen_transRestBox_factor x e he p _ α,
    Finset.filter_true_of_mem (fun v _ => trivial)]

/-- **The mixBox factorization.**  `setGen(mixBox a) = Gdesig · g_a^{kr−k}`, with
`g_a = genFun` over the residue class `a mod p`. -/
theorem setGen_mixBox_factor {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (he : Function.Injective e) (p : ℕ) (a : ℤ) (α : Deg k → ℝ) :
    setGen k (k * r) (mixBox x e p a) α
      = setGen k k (desigBox k x p) α
        * (genFun k ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter (fun v => (p : ℤ) ∣ (v - a))) α)
            ^ (k * r - k) := by
  classical
  rw [mixBox_eq_transRestBox, setGen_transRestBox_factor x e he p _ α]

/-! ## c-3/c-4 support — continuity, integrability, and the residue partition -/

@[fun_prop]
theorem continuous_setGen (k b : ℕ) (D : Finset (Fin b → ℤ)) :
    Continuous (setGen k b D) := by unfold setGen; fun_prop

/-- `‖F_D‖²` is torus-integrable (continuous, bounded by `|D|²`). -/
theorem integrable_norm_setGen_sq (k b : ℕ) (D : Finset (Fin b → ℤ)) :
    Integrable (fun α => ‖setGen k b D α‖ ^ 2) (torusMeasure k) := by
  refine integrable_cont_bdd ((continuous_setGen k b D).norm.pow 2)
    (C := (D.card : ℝ) ^ 2) (fun α => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_setGen_le k b D α) 2

/-- The residue equivalence: `(v : ZMod p) = a ↔ p ∣ (v − a.val)`. -/
theorem cast_eq_iff_dvd_sub {p : ℕ} [NeZero p] (v : ℤ) (a : ZMod p) :
    (v : ZMod p) = a ↔ (p : ℤ) ∣ (v - ((a.val : ℕ) : ℤ)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sub_eq_zero, eq_comm]

/-- **c-3 (the residue partition).**  `f = ∑_{a : ZMod p} g_a`, where `g_a` is the
generating function over the residue class `a mod p` in `(0, x]`. -/
theorem genFun_eq_sum_residue {k : ℕ} (x p : ℕ) [NeZero p] (α : Deg k → ℝ) :
    genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α
      = ∑ a : ZMod p, genFun k ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter
          (fun v => (p : ℤ) ∣ (v - ((a.val : ℕ) : ℤ)))) α := by
  classical
  rw [genFun_eq_sum_gcoord,
    ← Finset.sum_fiberwise (Finset.Ioc (0 : ℤ) (x : ℤ)) (fun v => (v : ZMod p)) (gcoord k α)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [genFun_eq_sum_gcoord]
  refine Finset.sum_congr (Finset.filter_congr (fun v _ => ?_)) (fun v _ => rfl)
  exact cast_eq_iff_dvd_sub v a

/-- **c-3 + c-4 (the residue Hölder step).**  `I(p) = Ncount(transBox) ≤
p^{2b−1}·∑_{a} Ncount(mixBox a)`, `b = kr−k`, `a` over residues mod `p`.
The pointwise residue power-mean `‖f‖^{2b} ≤ p^{2b−1}∑‖g_a‖^{2b}` is integrated
against `‖Gdesig‖²` and each mixed term collapsed by Parseval. -/
theorem transBox_Ncount_le_sum_mixBox {k r : ℕ} (x p : ℕ) (e : Fin k → Fin (k * r))
    (he : Function.Injective e) [NeZero p] (hb : 1 ≤ k * r - k) :
    (Ncount k (k * r) 0 (transBox x e p) (transBox x e p) : ℝ)
      ≤ (p : ℝ) ^ (2 * (k * r - k) - 1)
        * ∑ a : ZMod p, (Ncount k (k * r) 0 (mixBox x e p ((a.val : ℕ) : ℤ))
              (mixBox x e p ((a.val : ℕ) : ℤ)) : ℝ) := by
  classical
  set b := k * r - k with hbdef
  set μ := torusMeasure k with hμ
  -- the pointwise power-mean after factorization
  have hpt : ∀ α : Deg k → ℝ,
      ‖setGen k (k * r) (transBox x e p) α‖ ^ 2
        ≤ (p : ℝ) ^ (2 * b - 1)
          * ∑ a : ZMod p, ‖setGen k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)) α‖ ^ 2 := by
    intro α
    have hT : ‖setGen k (k * r) (transBox x e p) α‖ ^ 2
        = ‖setGen k k (desigBox k x p) α‖ ^ 2
          * ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖ ^ (2 * b) := by
      rw [setGen_transBox_factor x e he p α, norm_mul, mul_pow, norm_pow, ← pow_mul,
        mul_comm b 2]
    have hM : ∀ a : ZMod p, ‖setGen k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)) α‖ ^ 2
        = ‖setGen k k (desigBox k x p) α‖ ^ 2
          * ‖genFun k ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter
              (fun v => (p : ℤ) ∣ (v - ((a.val : ℕ) : ℤ)))) α‖ ^ (2 * b) := by
      intro a
      rw [setGen_mixBox_factor x e he p _ α, norm_mul, mul_pow, norm_pow, ← pow_mul,
        mul_comm b 2]
    rw [hT, Finset.sum_congr rfl (fun a _ => hM a), ← Finset.mul_sum, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    -- the honest power-mean `‖f‖^{2b} ≤ p^{2b−1} ∑ ‖g_a‖^{2b}`
    have hf : ‖genFun k (Finset.Ioc (0 : ℤ) (x : ℤ)) α‖
        ≤ ∑ a : ZMod p, ‖genFun k ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter
            (fun v => (p : ℤ) ∣ (v - ((a.val : ℕ) : ℤ)))) α‖ := by
      rw [genFun_eq_sum_residue x p α]
      exact norm_sum_le _ _
    have h1 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (ZMod p)))
      (f := fun a => ‖genFun k ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter
          (fun v => (p : ℤ) ∣ (v - ((a.val : ℕ) : ℤ)))) α‖)
      (fun a _ => norm_nonneg _) (2 * b - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * b), Finset.card_univ, ZMod.card] at h1
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hf (2 * b)) h1
  -- integrate the pointwise bound
  have hφint : Integrable (fun α => ‖setGen k (k * r) (transBox x e p) α‖ ^ 2) μ :=
    integrable_norm_setGen_sq k (k * r) (transBox x e p)
  have hψint : Integrable (fun α => (p : ℝ) ^ (2 * b - 1) *
      ∑ a : ZMod p, ‖setGen k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)) α‖ ^ 2) μ :=
    (MeasureTheory.integrable_finsetSum Finset.univ
      (fun a _ => integrable_norm_setGen_sq k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)))).const_mul _
  calc (Ncount k (k * r) 0 (transBox x e p) (transBox x e p) : ℝ)
      = ∫ α, ‖setGen k (k * r) (transBox x e p) α‖ ^ 2 ∂μ :=
        (integral_setGen_normSq k (k * r) (transBox x e p)).symm
    _ ≤ ∫ α, (p : ℝ) ^ (2 * b - 1) *
          ∑ a : ZMod p, ‖setGen k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)) α‖ ^ 2 ∂μ :=
        integral_mono hφint hψint hpt
    _ = (p : ℝ) ^ (2 * b - 1) * ∑ a : ZMod p,
          ∫ α, ‖setGen k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)) α‖ ^ 2 ∂μ := by
        rw [integral_const_mul, integral_finsetSum Finset.univ
          (fun a _ => integrable_norm_setGen_sq k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)))]
    _ = (p : ℝ) ^ (2 * b - 1) * ∑ a : ZMod p,
          (Ncount k (k * r) 0 (mixBox x e p ((a.val : ℕ) : ℤ))
            (mixBox x e p ((a.val : ℕ) : ℤ)) : ℝ) := by
        congr 1
        exact Finset.sum_congr rfl
          (fun a _ => integral_setGen_normSq k (k * r) (mixBox x e p ((a.val : ℕ) : ℤ)))

/-! ## c-5 (v) — the designated pair count `B(p,a)` via Linnik -/

/-- The graded designated-pair predicate: `p^{j+1} ∣ (∑(md−a)^{j+1} − ∑(nd−a)^{j+1})`
for every degree `1 ≤ j+1 ≤ k`.  This is the source's `B(p,a)` membership condition. -/
def gradedCond {k : ℕ} (p : ℕ) (a : ℤ) (md nd : Fin k → ℤ) : Prop :=
  ∀ j : Fin k, (p : ℤ) ^ ((j : ℕ) + 1) ∣
    ((∑ q, (md q - a) ^ ((j : ℕ) + 1)) - (∑ q, (nd q - a) ^ ((j : ℕ) + 1)))

instance {k : ℕ} (p : ℕ) (a : ℤ) (md nd : Fin k → ℤ) : Decidable (gradedCond p a md nd) := by
  unfold gradedCond; infer_instance

/-- **c-5(v), the `nd`-fibre.**  For fixed `md`, the designated `nd`-tuples in
`(0,x]^k` distinct mod `p` satisfying the graded system number `≤ k!·p^{k(k−1)/2}`.
Under `x < p^k` the residue map `nd ↦ (nd−a mod p^k)` is injective, landing in
`LinnikSol`. -/
theorem ndFibre_card_le {k p : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpk : k < p)
    (hk : 0 < k) (x : ℕ) (a : ℤ) (hpx : x < p ^ k) (md : Fin k → ℤ) :
    ((desigBox k x p).filter (fun nd => gradedCond p a md nd)).card
      ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
  classical
  set h : Fin k → ZMod (p ^ k) := fun j => ∑ q, (((md q - a : ℤ)) : ZMod (p ^ k)) ^ ((j : ℕ) + 1)
    with hh
  have hcast : ∀ (t : Fin k → ℤ) (j : Fin k),
      ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1)))
          (∑ q, (((t q - a : ℤ)) : ZMod (p ^ k)) ^ ((j : ℕ) + 1))
        = ((∑ q, (t q - a) ^ ((j : ℕ) + 1) : ℤ) : ZMod (p ^ ((j : ℕ) + 1))) := by
    intro t j
    rw [map_sum, Int.cast_sum]
    exact Finset.sum_congr rfl (fun q _ => by rw [map_pow, map_intCast, Int.cast_pow])
  refine le_trans (Finset.card_le_card_of_injOn
    (fun nd => fun q => (((nd q - a : ℤ)) : ZMod (p ^ k))) ?_ ?_) (linnik_lemma p k hp hpk h)
  · -- MapsTo into `LinnikSol p k h`
    intro nd hnd
    rw [Finset.mem_coe, Finset.mem_filter, mem_desigBox] at hnd
    obtain ⟨⟨_, hdist⟩, hgrad⟩ := hnd
    have hdist' : ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ ((nd i - a) - (nd j - a)) := by
      intro i j hij hc
      exact hdist i j hij (by have he : (nd i - a) - (nd j - a) = nd i - nd j := by ring
                              rwa [he] at hc)
    refine Finset.mem_coe.mpr (mem_LinnikSol.mpr ⟨residue_distinctModP hk _ hdist', fun j => ?_⟩)
    have hL := hcast nd j
    have hR : ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j)
        = ((∑ q, (md q - a) ^ ((j : ℕ) + 1) : ℤ) : ZMod (p ^ ((j : ℕ) + 1))) := by
      rw [hh]; exact hcast md j
    rw [hL, hR, eq_comm, ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hgrad j
  · -- InjOn: `x < p^k` makes the residue map injective
    intro nd hnd nd' hnd' heq
    rw [Finset.mem_coe, Finset.mem_filter, mem_desigBox] at hnd hnd'
    obtain ⟨⟨hbox, _⟩, _⟩ := hnd
    obtain ⟨⟨hbox', _⟩, _⟩ := hnd'
    funext q
    have hq : (((nd q - a : ℤ)) : ZMod (p ^ k)) = (((nd' q - a : ℤ)) : ZMod (p ^ k)) :=
      congrFun heq q
    have hdvd : ((p : ℤ) ^ k) ∣ (nd q - nd' q) := by
      have h0 : (((nd q - nd' q : ℤ)) : ZMod (p ^ k)) = 0 := by
        rw [show (nd q - nd' q : ℤ) = (nd q - a) - (nd' q - a) by ring]
        push_cast; push_cast at hq; rw [hq]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (nd q - nd' q) (p ^ k)).mp h0
      exact_mod_cast this
    obtain ⟨hb1a, hb1b⟩ := Finset.mem_Ioc.mp (hbox q)
    obtain ⟨hb2a, hb2b⟩ := Finset.mem_Ioc.mp (hbox' q)
    have hlt : (nd q - nd' q).natAbs < ((p : ℤ) ^ k).natAbs := by
      rw [Int.natAbs_pow, Int.natAbs_natCast]
      omega
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
    omega

/-- The designated-pair set `B(p,a)`: pairs `(md, nd)` both in `(0,x]^k` distinct
mod `p` satisfying the graded system. -/
noncomputable def gradedPairs (k x p : ℕ) (a : ℤ) : Finset ((Fin k → ℤ) × (Fin k → ℤ)) := by
  classical
  exact (desigBox k x p ×ˢ desigBox k x p).filter (fun w => gradedCond p a w.1 w.2)

/-- **c-5(v), the `B(p,a)` count.**  `card B(p,a) ≤ x^k · k! · p^{k(k−1)/2}`
(`md` free `≤ x^k`, each `nd`-fibre `≤ k!·p^{k(k−1)/2}` by `ndFibre_card_le`). -/
theorem gradedPairs_card_le {k p : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpk : k < p)
    (hk : 0 < k) (x : ℕ) (a : ℤ) (hpx : x < p ^ k) :
    (gradedPairs k x p a).card ≤ x ^ k * k.factorial * p ^ (k * (k - 1) / 2) := by
  classical
  have hdcard : (desigBox k x p).card ≤ x ^ k := by
    have hsub : desigBox k x p ⊆ Fintype.piFinset fun _ : Fin k => Finset.Ioc (0 : ℤ) (x : ℤ) := by
      intro md hmd; rw [mem_desigBox] at hmd; rw [Fintype.mem_piFinset]; exact hmd.1
    calc (desigBox k x p).card
        ≤ (Fintype.piFinset fun _ : Fin k => Finset.Ioc (0 : ℤ) (x : ℤ)).card :=
          Finset.card_le_card hsub
      _ = x ^ k := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            card_Ioc_zero]
  rw [gradedPairs, Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (t := desigBox k x p)
      (fun w hw => (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).1)]
  calc ∑ md ∈ desigBox k x p,
        (((desigBox k x p ×ˢ desigBox k x p).filter (fun w => gradedCond p a w.1 w.2)).filter
          (fun w => w.1 = md)).card
      ≤ ∑ _md ∈ desigBox k x p, k.factorial * p ^ (k * (k - 1) / 2) := by
        refine Finset.sum_le_sum (fun md _ => ?_)
        refine le_trans (Finset.card_le_card_of_injOn (fun w => w.2) ?_ ?_)
          (ndFibre_card_le hp hpk hk x a hpx md)
        · intro w hw
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hw
          obtain ⟨⟨⟨_, h2⟩, hg⟩, hfst⟩ := hw
          rw [Finset.mem_coe, Finset.mem_filter]
          exact ⟨h2, hfst ▸ hg⟩
        · intro w hw w' hw' he
          rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
          exact Prod.ext (hw.2.trans hw'.2.symm) he
    _ = (desigBox k x p).card * (k.factorial * p ^ (k * (k - 1) / 2)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ x ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) :=
        Nat.mul_le_mul_right _ hdcard
    _ = x ^ k * k.factorial * p ^ (k * (k - 1) / 2) := by ring

/-! ## c-5 (i)–(iv) — the transversal split equiv and the power-sum decomposition -/

/-- The transversal reindex `Fin (kr) ≃ Fin k ⊕ Fin (kr−k)` sending `e i ↦ inl i`. -/
noncomputable def transEquiv {k r : ℕ} (e : Fin k → Fin (k * r)) (he : Function.Injective e) :
    Fin (k * r) ≃ Fin k ⊕ Fin (k * r - k) := by
  classical
  refine (Equiv.sumCompl (· ∈ Set.range e)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective e he).symm (Fintype.equivFinOfCardEq ?_))
  have hcardRange : Fintype.card {q : Fin (k * r) // q ∈ Set.range e} = k := by
    have h := Fintype.card_congr (Equiv.ofInjective e he)
    rw [Fintype.card_fin] at h; exact h.symm
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardRange]

theorem transEquiv_symm_inl {k r : ℕ} (e : Fin k → Fin (k * r)) (he : Function.Injective e)
    (a : Fin k) : (transEquiv e he).symm (Sum.inl a) = e a := by
  simp [transEquiv]

theorem transEquiv_symm_inr_notmem {k r : ℕ} (e : Fin k → Fin (k * r)) (he : Function.Injective e)
    (b : Fin (k * r - k)) : (transEquiv e he).symm (Sum.inr b) ∉ Set.range e := by
  rintro ⟨i, hi⟩
  have h1 : transEquiv e he (e i) = Sum.inl i :=
    ((transEquiv e he).symm_apply_eq.mp (transEquiv_symm_inl e he i)).symm
  have h2 : transEquiv e he (e i) = Sum.inr b := by rw [hi, Equiv.apply_symm_apply]
  rw [h1] at h2
  exact Sum.inl_ne_inr h2

/-- **The power-sum split.**  `∑_q (m q)^j` splits over the designated block and the
rest along `transEquiv`. -/
theorem powerSum_split {k r : ℕ} (e : Fin k → Fin (k * r)) (he : Function.Injective e)
    (m : Fin (k * r) → ℤ) (j : ℕ) :
    ∑ q, (m q) ^ j
      = (∑ i, (m (e i)) ^ j) + ∑ i, (m ((transEquiv e he).symm (Sum.inr i))) ^ j := by
  rw [Fintype.sum_equiv (transEquiv e he) (fun q => (m q) ^ j)
        (fun s => (m ((transEquiv e he).symm s)) ^ j) (fun q => by rw [Equiv.symm_apply_apply]),
      Fintype.sum_sum_type]
  congr 1

/-! ## c-5 — the arithmetic-progression `Jk` bound (the `x → x/p` scale drop) -/

/-- **The residue-class `Jk` bound.**  The residue class `{v ∈ (0,x] : v ≡ a (mod p)}`
is an arithmetic progression `{p·w + a%p}`, so by affine invariance and monotonicity
its `J_k` is dominated by that of the base interval `[1, x/p+1]`. -/
theorem Jk_restSet_le {k b : ℕ} (x p : ℕ) (hp : 0 < p) (a : ℤ) :
    Jk k b ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter (fun v => (p : ℤ) ∣ (v - a)))
      ≤ Jk k b (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := by
  classical
  set r : ℤ := a % (p : ℤ) with hr
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hrnn : 0 ≤ r := Int.emod_nonneg a (by exact_mod_cast hp.ne')
  have hrlt : r < p := Int.emod_lt_of_pos a hpz
  have hsub : (Finset.Ioc (0 : ℤ) (x : ℤ)).filter (fun v => (p : ℤ) ∣ (v - a))
      ⊆ (Finset.Icc (0 : ℤ) ((x / p : ℕ) : ℤ)).image (fun w => (p : ℤ) * w + r) := by
    intro v hv
    rw [Finset.mem_filter, Finset.mem_Ioc] at hv
    obtain ⟨⟨hv0, hvx⟩, hdvd⟩ := hv
    have hdva : (p : ℤ) ∣ (a - r) :=
      ⟨a / p, by have := Int.mul_ediv_add_emod a (p : ℤ); rw [hr]; linarith⟩
    have hdvr : (p : ℤ) ∣ (v - r) := by
      have := dvd_add hdvd hdva; rwa [show (v - a) + (a - r) = v - r by ring] at this
    obtain ⟨w, hw⟩ := hdvr
    have hpw_le : (p : ℤ) * w ≤ x := by omega
    have hpw_gt : -(p : ℤ) < (p : ℤ) * w := by omega
    have hwnn : 0 ≤ w := by
      rcases le_or_gt 0 w with h | h
      · exact h
      · have hw1 : w ≤ -1 := by omega
        have hle : (p : ℤ) * w ≤ -(p : ℤ) := by nlinarith [hpz, hw1]
        omega
    have hwle : w ≤ ((x / p : ℕ) : ℤ) := by
      rw [Int.natCast_div, Int.le_ediv_iff_mul_le hpz, mul_comm]; exact hpw_le
    rw [Finset.mem_image]
    exact ⟨w, Finset.mem_Icc.mpr ⟨hwnn, hwle⟩, by omega⟩
  calc Jk k b ((Finset.Ioc (0 : ℤ) (x : ℤ)).filter (fun v => (p : ℤ) ∣ (v - a)))
      ≤ Jk k b ((Finset.Icc (0 : ℤ) ((x / p : ℕ) : ℤ)).image (fun w => (p : ℤ) * w + r)) :=
        Jk_mono hsub
    _ = Jk k b (Finset.Icc (0 : ℤ) ((x / p : ℕ) : ℤ)) :=
        Jk_image_affine k b _ p r (by exact_mod_cast hp.ne')
    _ = Jk k b (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := by
        rw [← Jk_image_add k b (Finset.Icc (0 : ℤ) ((x / p : ℕ) : ℤ)) 1]
        congr 1
        ext y
        simp only [Finset.mem_image, Finset.mem_Icc]
        constructor
        · rintro ⟨w, ⟨hw0, hwN⟩, rfl⟩; omega
        · rintro ⟨hy1, hyN⟩; exact ⟨y - 1, ⟨by omega, by omega⟩, by omega⟩

/-- **c-5 (i)–(iv), the designated-pair fibre.**  For fixed designated pair `(md, nd)`,
the pairs `(m,n) ∈ mixBox²` with `m∘e = md`, `n∘e = nd` and equal power sums inject
(via the rest block) into the shifted rest-count, hence number `≤ J_k(k(r−1), [1,x/p+1])`. -/
theorem mixBox_fibre_le {k r p : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (he : Function.Injective e) (a : ℤ) (hp : 0 < p) (md nd : Fin k → ℤ) :
    ((solSetN k (k * r) 0 (mixBox x e p a) (mixBox x e p a)).filter
        (fun mn => (fun i => mn.1 (e i)) = md ∧ (fun i => mn.2 (e i)) = nd)).card
      ≤ Jk k (k * r - k) (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := by
  classical
  set S : Finset ℤ := (Finset.Ioc (0 : ℤ) (x : ℤ)).filter (fun v => (p : ℤ) ∣ (v - a)) with hS
  set C : ℕ → ℤ := fun j => (∑ i, (nd i) ^ j) - (∑ i, (md i) ^ j) with hC
  have hrec : ∀ (f f' : Fin (k * r) → ℤ), (∀ i, f (e i) = f' (e i)) →
      (∀ i, f ((transEquiv e he).symm (Sum.inr i)) = f' ((transEquiv e he).symm (Sum.inr i))) →
      f = f' := by
    intro f f' hE hR
    funext q
    rcases hq : transEquiv e he q with i | i
    · have hqi : q = e i :=
        ((transEquiv e he).eq_symm_apply.mpr hq).trans (transEquiv_symm_inl e he i)
      rw [hqi]; exact hE i
    · have hqi : q = (transEquiv e he).symm (Sum.inr i) := (transEquiv e he).eq_symm_apply.mpr hq
      rw [hqi]; exact hR i
  refine le_trans (Finset.card_le_card_of_injOn
    (t := solSetN k (k * r - k) C (Fintype.piFinset fun _ : Fin (k * r - k) => S)
            (Fintype.piFinset fun _ : Fin (k * r - k) => S))
    (fun mn => (fun i => mn.1 ((transEquiv e he).symm (Sum.inr i)),
                fun i => mn.2 ((transEquiv e he).symm (Sum.inr i)))) ?_ ?_) ?_
  · -- MapsTo into `solSetN k (k*r-k) C (S^…) (S^…)`
    intro mn hmn
    rw [Finset.mem_coe, Finset.mem_filter, mem_solSetN] at hmn
    obtain ⟨⟨hm1, hm2, hpse⟩, hproj1, hproj2⟩ := hmn
    rw [mem_mixBox] at hm1 hm2
    have he1 : ∀ i, mn.1 (e i) = md i := fun i => congrFun hproj1 i
    have he2 : ∀ i, mn.2 (e i) = nd i := fun i => congrFun hproj2 i
    rw [Finset.mem_coe, mem_solSetN]
    refine ⟨?_, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]; intro i; rw [hS, Finset.mem_filter]
      exact ⟨hm1.1 _, hm1.2.2 _ (transEquiv_symm_inr_notmem e he i)⟩
    · rw [Fintype.mem_piFinset]; intro i; rw [hS, Finset.mem_filter]
      exact ⟨hm2.1 _, hm2.2.2 _ (transEquiv_symm_inr_notmem e he i)⟩
    · intro deg hdeg
      have hsplit1 := powerSum_split e he mn.1 deg
      have hsplit2 := powerSum_split e he mn.2 deg
      have hpd := hpse deg hdeg
      simp only [Pi.zero_apply, add_zero] at hpd
      simp only [he1] at hsplit1
      simp only [he2] at hsplit2
      have key : (∑ i, (mn.1 ((transEquiv e he).symm (Sum.inr i))) ^ deg)
          = (∑ i, (mn.2 ((transEquiv e he).symm (Sum.inr i))) ^ deg)
            + ((∑ i, (nd i) ^ deg) - (∑ i, (md i) ^ deg)) := by
        linarith [hsplit1, hsplit2, hpd]
      simpa only [hC] using key
  · -- InjOn
    intro mn hmn mn' hmn' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hmn hmn'
    obtain ⟨_, hp1, hp2⟩ := hmn
    obtain ⟨_, hp1', hp2'⟩ := hmn'
    have hr1 : ∀ i, mn.1 ((transEquiv e he).symm (Sum.inr i))
        = mn'.1 ((transEquiv e he).symm (Sum.inr i)) := fun i => congrFun (congrArg Prod.fst heq) i
    have hr2 : ∀ i, mn.2 ((transEquiv e he).symm (Sum.inr i))
        = mn'.2 ((transEquiv e he).symm (Sum.inr i)) := fun i => congrFun (congrArg Prod.snd heq) i
    refine Prod.ext (hrec mn.1 mn'.1 (fun i => ?_) hr1) (hrec mn.2 mn'.2 (fun i => ?_) hr2)
    · rw [congrFun hp1 i, congrFun hp1' i]
    · rw [congrFun hp2 i, congrFun hp2' i]
  · -- the count bound
    calc (solSetN k (k * r - k) C (Fintype.piFinset fun _ : Fin (k * r - k) => S)
              (Fintype.piFinset fun _ : Fin (k * r - k) => S)).card
        = Ncount k (k * r - k) C (Fintype.piFinset fun _ : Fin (k * r - k) => S)
            (Fintype.piFinset fun _ : Fin (k * r - k) => S) := rfl
      _ ≤ Ncount k (k * r - k) 0 (Fintype.piFinset fun _ : Fin (k * r - k) => S)
            (Fintype.piFinset fun _ : Fin (k * r - k) => S) := Ncount_shift_le k (k * r - k) C _
      _ = Jk k (k * r - k) S := Ncount_zero_eq_Jk k (k * r - k) S
      _ ≤ Jk k (k * r - k) (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := Jk_restSet_le x p hp a

/-- The `−a` translated power-sum split (beta-reduced form of `powerSum_split`). -/
theorem powerSum_split_sub {k r : ℕ} (e : Fin k → Fin (k * r)) (he : Function.Injective e)
    (m : Fin (k * r) → ℤ) (a : ℤ) (j : ℕ) :
    ∑ q, (m q - a) ^ j
      = (∑ i, (m (e i) - a) ^ j)
        + ∑ i, (m ((transEquiv e he).symm (Sum.inr i)) - a) ^ j :=
  powerSum_split e he (fun q => m q - a) j

/-- **c-5 (i)/(iii), the graded divisibility.**  Every solution pair projects to a
`B(p,a)` designated pair: the rest coordinates `≡ a (mod p)` force the graded
congruence `p^{j+1} ∣ D_{j+1}`. -/
theorem proj_mem_gradedPairs {k r p : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    (he : Function.Injective e) (a : ℤ)
    (mn : (Fin (k * r) → ℤ) × (Fin (k * r) → ℤ))
    (hmn : mn ∈ solSetN k (k * r) 0 (mixBox x e p a) (mixBox x e p a)) :
    ((fun i => mn.1 (e i)), (fun i => mn.2 (e i))) ∈ gradedPairs k x p a := by
  classical
  rw [mem_solSetN] at hmn
  obtain ⟨hm1, hm2, hpse⟩ := hmn
  rw [mem_mixBox] at hm1 hm2
  rw [gradedPairs, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_desigBox]; exact ⟨fun i => hm1.1 _, fun i j hij => hm1.2.1 i j hij⟩
  · rw [mem_desigBox]; exact ⟨fun i => hm2.1 _, fun i j hij => hm2.2.1 i j hij⟩
  · intro j
    set deg := (j : ℕ) + 1 with hdeg_def
    have hdeg : deg ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hpe0 : PowerSumEq k (k * r) mn.1 mn.2 := fun d hd => by
      have := hpse d hd; simpa using this
    have hteq : ∑ q, (mn.1 q - a) ^ deg = ∑ q, (mn.2 q - a) ^ deg := by
      have := (powerSumEq_sub_const k (k * r) a mn.1 mn.2).mp hpe0 deg hdeg; simpa using this
    have hs1 := powerSum_split_sub e he mn.1 a deg
    have hs2 := powerSum_split_sub e he mn.2 a deg
    have hDeq : (∑ i, (mn.1 (e i) - a) ^ deg) - (∑ i, (mn.2 (e i) - a) ^ deg)
        = (∑ i, (mn.2 ((transEquiv e he).symm (Sum.inr i)) - a) ^ deg)
          - (∑ i, (mn.1 ((transEquiv e he).symm (Sum.inr i)) - a) ^ deg) := by
      rw [hs1, hs2] at hteq; linarith [hteq]
    have hdvd1 : (p : ℤ) ^ deg ∣ ∑ i, (mn.1 ((transEquiv e he).symm (Sum.inr i)) - a) ^ deg :=
      Finset.dvd_sum fun i _ =>
        pow_dvd_pow_of_dvd (hm1.2.2 _ (transEquiv_symm_inr_notmem e he i)) deg
    have hdvd2 : (p : ℤ) ^ deg ∣ ∑ i, (mn.2 ((transEquiv e he).symm (Sum.inr i)) - a) ^ deg :=
      Finset.dvd_sum fun i _ =>
        pow_dvd_pow_of_dvd (hm2.2.2 _ (transEquiv_symm_inr_notmem e he i)) deg
    change (p : ℤ) ^ deg ∣
      ((∑ q, (mn.1 (e q) - a) ^ deg) - (∑ q, (mn.2 (e q) - a) ^ deg))
    rw [hDeq]
    exact dvd_sub hdvd2 hdvd1

/-- **c-5 (the fibration assembly).**  `Ncount(mixBox a) ≤ card B(p,a) · J_k`, and
`card B(p,a) ≤ x^k·k!·p^{k(k−1)/2}`, giving the `x → x/p` scale-drop bound. -/
theorem mixBox_Ncount_le {k r p : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpk : k < p) (hk : 0 < k)
    (x : ℕ) (e : Fin k → Fin (k * r)) (he : Function.Injective e) (a : ℤ) (hpx : x < p ^ k) :
    Ncount k (k * r) 0 (mixBox x e p a) (mixBox x e p a)
      ≤ x ^ k * k.factorial * p ^ (k * (k - 1) / 2)
        * Jk k (k * r - k) (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := by
  classical
  have hproj : ∀ mn ∈ solSetN k (k * r) 0 (mixBox x e p a) (mixBox x e p a),
      ((fun i => mn.1 (e i)), (fun i => mn.2 (e i))) ∈ gradedPairs k x p a :=
    fun mn hmn => proj_mem_gradedPairs x e he a mn hmn
  rw [Ncount, Finset.card_eq_sum_card_fiberwise hproj]
  calc ∑ w ∈ gradedPairs k x p a,
        ((solSetN k (k * r) 0 (mixBox x e p a) (mixBox x e p a)).filter
          (fun mn => ((fun i => mn.1 (e i)), (fun i => mn.2 (e i))) = w)).card
      ≤ ∑ _w ∈ gradedPairs k x p a,
          Jk k (k * r - k) (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        have heqf : ((solSetN k (k * r) 0 (mixBox x e p a) (mixBox x e p a)).filter
              (fun mn => ((fun i => mn.1 (e i)), (fun i => mn.2 (e i))) = w))
            = ((solSetN k (k * r) 0 (mixBox x e p a) (mixBox x e p a)).filter
              (fun mn => (fun i => mn.1 (e i)) = w.1 ∧ (fun i => mn.2 (e i)) = w.2)) := by
          ext mn; simp only [Finset.mem_filter, Prod.ext_iff]
        rw [heqf]
        exact mixBox_fibre_le x e he a hp.pos w.1 w.2
    _ = (gradedPairs k x p a).card
          * Jk k (k * r - k) (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ x ^ k * k.factorial * p ^ (k * (k - 1) / 2)
          * Jk k (k * r - k) (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) :=
        Nat.mul_le_mul_right _ (gradedPairs_card_le hp hpk hk x a hpx)

/-! ## c-6 — the frozen assembly (THE INDUCTION UNLOCKS) -/

/-- **c-6 (THE FROZEN TARGET).**  The transversal count `I(p) = Ncount(transBox)`
obeys the VMVT-inductive bound
`I(p) ≤ p^{2(kr)−2k}·x^k·k!·p^{k(k−1)/2}·J_k(k(r−1), [1, x/p+1])`.
Chains c-3/c-4 (`transBox_Ncount_le_sum_mixBox`) with c-5 (`mixBox_Ncount_le`),
the `a`-sum bounded by `p ×` the uniform c-5 bound. -/
theorem transBox_Ncount_le {k r : ℕ} (x p : ℕ) (e : Fin k → Fin (k * r))
    (he : Function.Injective e) (hp : p.Prime) (hkp : k < p) (hk : 0 < k) (hr : 1 ≤ r)
    (hpx : x < p ^ k) :
    Ncount k (k * r) 0 (transBox x e p) (transBox x e p)
      ≤ p ^ (2 * (k * r) - 2 * k) * (x ^ k * k.factorial * p ^ (k * (k - 1) / 2))
        * Jk k (k * (r - 1)) (Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1)) := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  set I : Finset ℤ := Finset.Icc (1 : ℤ) (((x / p : ℕ) : ℤ) + 1) with hI
  have hkrk : k * r - k = k * (r - 1) := by
    cases r with
    | zero => omega
    | succ s => rw [Nat.succ_sub_one, Nat.mul_succ]; omega
  rcases lt_or_ge r 2 with hr2 | hr2
  · -- r = 1: the rest block is empty, `mixBox = transBox`
    have hr1 : r = 1 := by omega
    have hsurj : ∀ q : Fin (k * r), q ∈ Set.range e := by
      intro q
      have hcard : Fintype.card (Fin k) = Fintype.card (Fin (k * r)) := by
        rw [Fintype.card_fin, Fintype.card_fin, hr1, Nat.mul_one]
      exact ((Fintype.bijective_iff_injective_and_card e).mpr ⟨he, hcard⟩).surjective q
    have hmt : mixBox x e p 0 = transBox x e p := by
      ext m; rw [mem_mixBox]; unfold transBox solBox
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun q hq => absurd (hsurj q) hq⟩⟩
    have hmb := mixBox_Ncount_le hp hkp hk x e he 0 hpx
    rw [hmt, ← hI, hkrk] at hmb
    have hE1 : 2 * (k * r) - 2 * k = 0 := by rw [hr1, Nat.mul_one]; omega
    have hE2 : k * (r - 1) = 0 := by simp [hr1]
    rw [hE2] at hmb
    rw [hE1, hE2, pow_zero, one_mul]
    exact hmb
  · -- r ≥ 2: the honest residue-Hölder chain
    have hb : 1 ≤ k * r - k := by rw [hkrk]; exact Nat.mul_pos hk (by omega)
    have hb2 : 1 ≤ 2 * (k * r - k) := by omega
    set B0 : ℕ := x ^ k * k.factorial * p ^ (k * (k - 1) / 2) * Jk k (k * r - k) I with hB0
    have huni : ∀ a : ZMod p,
        (Ncount k (k * r) 0 (mixBox x e p (a.val : ℤ)) (mixBox x e p (a.val : ℤ)) : ℝ)
          ≤ (B0 : ℝ) := by
      intro a; rw [hB0]; exact_mod_cast mixBox_Ncount_le hp hkp hk x e he (a.val : ℤ) hpx
    have hsum : (∑ a : ZMod p,
          (Ncount k (k * r) 0 (mixBox x e p (a.val : ℤ)) (mixBox x e p (a.val : ℤ)) : ℝ))
        ≤ (p : ℝ) * (B0 : ℝ) := by
      calc (∑ a : ZMod p,
              (Ncount k (k * r) 0 (mixBox x e p (a.val : ℤ)) (mixBox x e p (a.val : ℤ)) : ℝ))
          ≤ ∑ _a : ZMod p, (B0 : ℝ) := Finset.sum_le_sum (fun a _ => huni a)
        _ = (p : ℝ) * (B0 : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hfin : (Ncount k (k * r) 0 (transBox x e p) (transBox x e p) : ℝ)
        ≤ (p : ℝ) ^ (2 * (k * r - k)) * (B0 : ℝ) := by
      have hR := transBox_Ncount_le_sum_mixBox x p e he hb
      calc (Ncount k (k * r) 0 (transBox x e p) (transBox x e p) : ℝ)
          ≤ (p : ℝ) ^ (2 * (k * r - k) - 1)
              * (∑ a : ZMod p,
                  (Ncount k (k * r) 0 (mixBox x e p (a.val : ℤ))
                    (mixBox x e p (a.val : ℤ)) : ℝ)) := hR
        _ ≤ (p : ℝ) ^ (2 * (k * r - k) - 1) * ((p : ℝ) * (B0 : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (p : ℝ) ^ (2 * (k * r - k)) * (B0 : ℝ) := by
            rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hb2]
    have hnat : Ncount k (k * r) 0 (transBox x e p) (transBox x e p)
        ≤ p ^ (2 * (k * r - k)) * B0 := by exact_mod_cast hfin
    calc Ncount k (k * r) 0 (transBox x e p) (transBox x e p)
        ≤ p ^ (2 * (k * r - k)) * B0 := hnat
      _ = p ^ (2 * (k * r) - 2 * k) * (x ^ k * k.factorial * p ^ (k * (k - 1) / 2))
            * Jk k (k * (r - 1)) I := by
          rw [hB0, show 2 * (k * r - k) = 2 * (k * r) - 2 * k by omega, hkrk, ← mul_assoc]

end Salt.Vmvt
