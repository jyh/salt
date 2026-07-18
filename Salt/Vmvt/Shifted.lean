/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Defs

/-!
# The `ℓ`-shifted counting object `N(B, C, ℓ)` and the remaining Lemma 24.1 items

This file ports the still-open parts of **Lemma 24.1** of Vaughan's PSU
Chapter 24 notes: the general shifted solution count `N(B, C, ℓ)` and the
inequalities (b), (c), (e).  With `s_j(m) = ∑_q (m q)^j` the degree-`j` power
sum, `N(B, C, ℓ)` counts the pairs `(m, n) ∈ B × C` of `b`-tuples solving the
**shifted Vinogradov system**
`s_j(m) = s_j(n) + ℓ_j`  for `1 ≤ j ≤ k`,
and the notes abbreviate `N(B, ℓ) = N(B, B, ℓ)`, `N(B) = N(B, 0)`,
`J_k(A, b, ℓ) = N(A^b, ℓ)`, so `J_k(A, b) = N(A^b) = N(A^b, 0)`.

## The porting frame: combinatorial, not generating-function

The notes state Lemma 24.1 with proof "homework"; the later analytic proof of
Lemma 24.3(d) writes `J_k(x, b, ℓ) = ∫ |f(α)|^{2b} e(ℓ·α) dα` and deduces
`J_k(x, b, ℓ) ≤ J_k(x, b)` from `|e(ℓ·α)| = 1`.  We port the **combinatorial
mirror**: grouping the pairs by the power-sum *signature* `σ(m) = (s_1(m), …,
s_k(m))` turns `N` into a convolution of the fibre-counting function
`r_D(h) = #{m ∈ D : σ(m) = h}`:
`N(B, C, ℓ) = ∑_h r_B(h + ℓ) · r_C(h)`.
Then (b)/(e) is `∑_h r_B(h+ℓ) r_B(h) ≤ ∑_h r_B(h)²`, exactly the discrete
Cauchy–Schwarz — provable by the elementary `2ab ≤ a² + b²` (AM–GM) plus the
translation invariance `∑_h r_B(h+ℓ)² = ∑_h r_B(h)²` of the square-sum, with no
Parseval/generating-function machinery.  So the analytic `|e(ℓ·α)| = 1` step is
*not* needed: the combinatorial frame carries (b),(c),(e) in full.

## Signatures as `Deg k → ℤ`

`Deg k = {j // j ∈ Icc 1 k}` is the (finite, decidable-eq) index of active
degrees, so `σ = sig k b : (Fin b → ℤ) → (Deg k → ℤ)` lands in a `Fintype`-Pi
where `Finset.image`/`card_eq_sum_card_fiberwise` apply.  `sigOf k ℓ` is the
shift `ℓ` read as an element of `Deg k → ℤ`.
-/

namespace Salt.Vmvt

open Finset

/-- The shifted power-sum predicate: `s_j(m) = s_j(n) + ℓ_j` for `1 ≤ j ≤ k`,
i.e. the defining relation of the shifted Vinogradov system.  With `ℓ = 0` this
is `PowerSumEq`. -/
def PowerSumShiftEq (k b : ℕ) (ℓ : ℕ → ℤ) (m n : Fin b → ℤ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, ∑ q, (m q) ^ j = (∑ q, (n q) ^ j) + ℓ j

instance (k b : ℕ) (ℓ : ℕ → ℤ) (m n : Fin b → ℤ) :
    Decidable (PowerSumShiftEq k b ℓ m n) := by
  unfold PowerSumShiftEq; infer_instance

/-- `N(B, C, ℓ)` as a `Finset`: the pairs `(m, n) ∈ B × C` solving the shifted
system.  `B, C` are finite sets of `b`-tuples (subsets of `ℤ^b`), matching the
notes' `B, C ⊆ ℝ^b`. -/
def solSetN (k b : ℕ) (ℓ : ℕ → ℤ) (B C : Finset (Fin b → ℤ)) :
    Finset ((Fin b → ℤ) × (Fin b → ℤ)) :=
  (B ×ˢ C).filter fun mn => PowerSumShiftEq k b ℓ mn.1 mn.2

/-- **The shifted count `N(B, C, ℓ)`** of Lemma 24.1. -/
def Ncount (k b : ℕ) (ℓ : ℕ → ℤ) (B C : Finset (Fin b → ℤ)) : ℕ :=
  (solSetN k b ℓ B C).card

/-- `J_k(A, b, ℓ) = N(A^b, ℓ)`, the shifted mean value. -/
noncomputable def JkShift (k b : ℕ) (A : Finset ℤ) (ℓ : ℕ → ℤ) : ℕ :=
  Ncount k b ℓ (Fintype.piFinset fun _ : Fin b => A) (Fintype.piFinset fun _ : Fin b => A)

/-- Membership in the shifted solution set. -/
theorem mem_solSetN {k b : ℕ} {ℓ : ℕ → ℤ} {B C : Finset (Fin b → ℤ)}
    {mn : (Fin b → ℤ) × (Fin b → ℤ)} :
    mn ∈ solSetN k b ℓ B C ↔
      mn.1 ∈ B ∧ mn.2 ∈ C ∧ PowerSumShiftEq k b ℓ mn.1 mn.2 := by
  unfold solSetN
  rw [Finset.mem_filter, Finset.mem_product]
  tauto

/-- **Lemma 24.1(a).**  `N(B, C, ℓ)` is monotone in each of the two boxes; in
particular `B ⊆ C ⟹ N(B, ℓ) ≤ N(C, ℓ)` (take the diagonal). -/
theorem Ncount_mono (k b : ℕ) (ℓ : ℕ → ℤ) {B B' C C' : Finset (Fin b → ℤ)}
    (hB : B ⊆ B') (hC : C ⊆ C') : Ncount k b ℓ B C ≤ Ncount k b ℓ B' C' := by
  apply Finset.card_le_card
  intro mn hmn
  rw [mem_solSetN] at hmn ⊢
  exact ⟨hB hmn.1, hC hmn.2.1, hmn.2.2⟩

/-! ## Signatures -/

/-- The active-degree index `{1, …, k}` as a finite decidable-eq type. -/
abbrev Deg (k : ℕ) : Type := {j : ℕ // j ∈ Finset.Icc 1 k}

/-- The power-sum signature `σ(m) = (s_1(m), …, s_k(m))`. -/
def sig (k b : ℕ) (m : Fin b → ℤ) : Deg k → ℤ := fun j => ∑ q, (m q) ^ (j : ℕ)

/-- The shift vector `ℓ` read as a signature offset. -/
def sigOf (k : ℕ) (ℓ : ℕ → ℤ) : Deg k → ℤ := fun j => ℓ (j : ℕ)

@[simp] theorem sigOf_zero (k : ℕ) : sigOf k (0 : ℕ → ℤ) = 0 := by
  funext j; simp [sigOf]

/-- `PowerSumEq` is signature equality. -/
theorem powerSumEq_iff_sig (k b : ℕ) (m n : Fin b → ℤ) :
    PowerSumEq k b m n ↔ sig k b m = sig k b n := by
  constructor
  · intro h; funext j; exact h j.1 j.2
  · intro h j hj; exact congrFun h ⟨j, hj⟩

/-- `PowerSumShiftEq` is signature equality up to the shift `sigOf k ℓ`. -/
theorem powerSumShiftEq_iff_sig (k b : ℕ) (ℓ : ℕ → ℤ) (m n : Fin b → ℤ) :
    PowerSumShiftEq k b ℓ m n ↔ sig k b m = sig k b n + sigOf k ℓ := by
  constructor
  · intro h; funext j
    simp only [Pi.add_apply, sig, sigOf]
    exact h j.1 j.2
  · intro h j hj
    have := congrFun h ⟨j, hj⟩
    simpa only [Pi.add_apply, sig, sigOf] using this

/-! ## The fibre-counting function and the convolution identity -/

/-- `r_D(h) = #{m ∈ D : σ(m) = h}`, the number of `b`-tuples in `D` of
signature `h`. -/
def rcount (k b : ℕ) (D : Finset (Fin b → ℤ)) (h : Deg k → ℤ) : ℕ :=
  (D.filter fun m => sig k b m = h).card

/-- Signatures outside the image are unrepresented. -/
theorem rcount_eq_zero (k b : ℕ) (B : Finset (Fin b → ℤ)) (h : Deg k → ℤ)
    (hh : h ∉ B.image (sig k b)) : rcount k b B h = 0 := by
  unfold rcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hcon
  exact hh (Finset.mem_image.mpr ⟨m, hm, hcon⟩)

/-- Elementary AM–GM over `ℕ`: `2ab ≤ a² + b²`. -/
theorem two_mul_mul_le_sq_add_sq (a c : ℕ) : 2 * (a * c) ≤ a ^ 2 + c ^ 2 := by
  have h : (2 * (a * c) : ℤ) ≤ (a : ℤ) ^ 2 + (c : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℤ) - c)]
  exact_mod_cast h

/-- Cauchy–Schwarz `(∑ f)² ≤ #s · ∑ f²` over `ℕ` (via `ℤ`). -/
theorem sq_sum_le_card_mul_sum_sq_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => (f i : ℤ))
  exact_mod_cast h

/-- **The convolution identity.**  Grouping the shifted pairs by the signature
of the second tuple, `N(B, C, ℓ) = ∑_h r_B(h + ℓ) · r_C(h)` over any index set
`W` containing the signatures occurring in `C`. -/
theorem Ncount_eq_sum_rcount (k b : ℕ) (ℓ : ℕ → ℤ) (B C : Finset (Fin b → ℤ))
    (W : Finset (Deg k → ℤ)) (hW : C.image (sig k b) ⊆ W) :
    Ncount k b ℓ B C = ∑ h ∈ W, rcount k b B (h + sigOf k ℓ) * rcount k b C h := by
  have H : ∀ mn ∈ solSetN k b ℓ B C, sig k b mn.2 ∈ W := by
    intro mn hmn
    rw [mem_solSetN] at hmn
    exact hW (Finset.mem_image.mpr ⟨mn.2, hmn.2.1, rfl⟩)
  rw [Ncount, Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  unfold rcount
  rw [← Finset.card_product]
  refine congrArg Finset.card ?_
  ext mn
  constructor
  · intro hmn
    rw [Finset.mem_filter, mem_solSetN] at hmn
    obtain ⟨⟨hm, hn, hpred⟩, hsig⟩ := hmn
    rw [powerSumShiftEq_iff_sig] at hpred
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨hm, ?_⟩, ⟨hn, hsig⟩⟩
    rw [hpred, hsig]
  · intro hmn
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hmn
    obtain ⟨⟨hm, hm2⟩, ⟨hn, hn2⟩⟩ := hmn
    rw [Finset.mem_filter, mem_solSetN]
    refine ⟨⟨hm, hn, ?_⟩, hn2⟩
    rw [powerSumShiftEq_iff_sig, hm2, hn2]

/-- The unshifted count as a sum of squares: `N(D) = ∑_h r_D(h)²`. -/
theorem Ncount_zero_eq_sum_sq (k b : ℕ) (D : Finset (Fin b → ℤ))
    (W : Finset (Deg k → ℤ)) (hW : D.image (sig k b) ⊆ W) :
    Ncount k b 0 D D = ∑ h ∈ W, rcount k b D h ^ 2 := by
  rw [Ncount_eq_sum_rcount k b 0 D D W hW, sigOf_zero]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [add_zero, pow_two]

/-- **Translation invariance of the square-sum.**  Shifting every signature by a
fixed `L` cannot increase `∑_h r_B(h)²`: the reindexed sum only misses (never
gains) support, because `r_B` vanishes off the signature image. -/
theorem translation_sq_bound (k b : ℕ) (B : Finset (Fin b → ℤ)) (L : Deg k → ℤ) :
    ∑ h ∈ B.image (sig k b), rcount k b B (h + L) ^ 2
      ≤ ∑ h ∈ B.image (sig k b), rcount k b B h ^ 2 := by
  have hinj : Set.InjOn (· + L) (↑(B.image (sig k b))) :=
    fun x _ y _ hxy => add_right_cancel hxy
  have reindex : ∑ h ∈ B.image (sig k b), rcount k b B (h + L) ^ 2
      = ∑ h' ∈ (B.image (sig k b)).image (· + L), rcount k b B h' ^ 2 := by
    rw [Finset.sum_image hinj]
  rw [reindex]
  calc ∑ h' ∈ (B.image (sig k b)).image (· + L), rcount k b B h' ^ 2
      ≤ ∑ h' ∈ B.image (sig k b) ∪ (B.image (sig k b)).image (· + L),
          rcount k b B h' ^ 2 :=
        Finset.sum_le_sum_of_subset Finset.subset_union_right
    _ = ∑ h' ∈ B.image (sig k b), rcount k b B h' ^ 2 := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro x _ hxI
        rw [rcount_eq_zero k b B x hxI]; simp

/-- Aggregate AM–GM over an abstract finite index: `2 ∑ f·g ≤ ∑ f² + ∑ g²`.
Kept generic (no `Deg`/`rcount`) so the heavy termwise step never touches the
symbolic decidable-eq instances on `Deg k → ℤ`. -/
theorem two_mul_sum_mul_le {α : Type*} (s : Finset α) (f g : α → ℕ) :
    2 * ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ 2) + ∑ i ∈ s, g i ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => two_mul_mul_le_sq_add_sq (f i) (g i)

/-- **Lemma 24.1(b).**  `N(B, ℓ) ≤ N(B)` for every shift `ℓ`.  This is the
discrete Cauchy–Schwarz `∑_h r_B(h+ℓ) r_B(h) ≤ ∑_h r_B(h)²`, obtained from AM–GM
`2ab ≤ a² + b²` and the translation invariance of the square-sum. -/
theorem Ncount_shift_le (k b : ℕ) (ℓ : ℕ → ℤ) (B : Finset (Fin b → ℤ)) :
    Ncount k b ℓ B B ≤ Ncount k b 0 B B := by
  have hWsub : B.image (sig k b) ⊆ B.image (sig k b) := subset_rfl
  have hL : Ncount k b ℓ B B
      = ∑ h ∈ B.image (sig k b), rcount k b B (h + sigOf k ℓ) * rcount k b B h :=
    Ncount_eq_sum_rcount k b ℓ B B _ hWsub
  have h0 : Ncount k b 0 B B = ∑ h ∈ B.image (sig k b), rcount k b B h ^ 2 :=
    Ncount_zero_eq_sum_sq k b B _ hWsub
  have key : 2 * ∑ h ∈ B.image (sig k b), rcount k b B (h + sigOf k ℓ) * rcount k b B h
      ≤ (∑ h ∈ B.image (sig k b), rcount k b B (h + sigOf k ℓ) ^ 2)
          + ∑ h ∈ B.image (sig k b), rcount k b B h ^ 2 :=
    two_mul_sum_mul_le _ _ _
  have tsb : (∑ h ∈ B.image (sig k b), rcount k b B (h + sigOf k ℓ) ^ 2)
      ≤ ∑ h ∈ B.image (sig k b), rcount k b B h ^ 2 :=
    translation_sq_bound k b B (sigOf k ℓ)
  have amgm : 2 * Ncount k b ℓ B B ≤ 2 * Ncount k b 0 B B := by
    rw [hL, h0, two_mul (∑ h ∈ B.image (sig k b), rcount k b B h ^ 2)]
    exact key.trans (Nat.add_le_add_right tsb _)
  exact Nat.le_of_mul_le_mul_left amgm (by norm_num)

/-- The `ℓ = 0` shifted count on the product box `A^b` is the landed `J_k(A, b)`:
the general object subsumes `Jk` as its unshifted special case. -/
theorem Ncount_zero_eq_Jk (k b : ℕ) (A : Finset ℤ) :
    Ncount k b 0 (Fintype.piFinset fun _ : Fin b => A)
        (Fintype.piFinset fun _ : Fin b => A) = Jk k b A := by
  unfold Ncount Jk
  congr 1
  ext mn
  simp only [mem_solSetN, mem_solSet, Fintype.mem_piFinset]
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · intro h j hj; simpa [Pi.zero_apply] using h j hj
  · intro h j hj; simpa [Pi.zero_apply] using h j hj

/-- **Lemma 24.1(e).**  `J_k(A, b, ℓ) ≤ J_k(A, b)`: the shifted mean value is
dominated by the diagonal one.  Immediate from (b) on the box `A^b`. -/
theorem Jk_shift_le (k b : ℕ) (ℓ : ℕ → ℤ) (A : Finset ℤ) :
    JkShift k b A ℓ ≤ Jk k b A := by
  unfold JkShift
  rw [← Ncount_zero_eq_Jk]
  exact Ncount_shift_le k b ℓ _

/-- Each fibre count over a union is at most the sum of the piece fibre counts. -/
theorem rcount_biUnion_le (k b : ℕ) {ι : Type*} (s : Finset ι)
    (Bf : ι → Finset (Fin b → ℤ)) (h : Deg k → ℤ) :
    rcount k b (s.biUnion Bf) h ≤ ∑ i ∈ s, rcount k b (Bf i) h := by
  unfold rcount
  calc ((s.biUnion Bf).filter fun m => sig k b m = h).card
      ≤ (s.biUnion fun i => (Bf i).filter fun m => sig k b m = h).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter, Finset.mem_biUnion] at hm
        obtain ⟨⟨i, hi, hmi⟩, hsig⟩ := hm
        rw [Finset.mem_biUnion]
        exact ⟨i, hi, Finset.mem_filter.mpr ⟨hmi, hsig⟩⟩
    _ ≤ ∑ i ∈ s, ((Bf i).filter fun m => sig k b m = h).card := Finset.card_biUnion_le

/-- **Lemma 24.1(c).**  If `C = ⋃_{i} B_i` then `N(C) ≤ j · ∑_i N(B_i)` with
`j = #s` the number of pieces.  Combinatorial proof: `N(D) = ∑_h r_D(h)²`,
`r_C(h) ≤ ∑_i r_{B_i}(h)`, and `(∑_i a_i)² ≤ j ∑_i a_i²` (Cauchy–Schwarz),
summed over signatures `h`. -/
theorem Ncount_union_le (k b : ℕ) {ι : Type*} (s : Finset ι)
    (Bf : ι → Finset (Fin b → ℤ)) :
    Ncount k b 0 (s.biUnion Bf) (s.biUnion Bf)
      ≤ s.card * ∑ i ∈ s, Ncount k b 0 (Bf i) (Bf i) := by
  have hBi : ∀ i ∈ s, Ncount k b 0 (Bf i) (Bf i)
      = ∑ h ∈ (s.biUnion Bf).image (sig k b), rcount k b (Bf i) h ^ 2 := by
    intro i hi
    apply Ncount_zero_eq_sum_sq
    exact Finset.image_subset_image (Finset.subset_biUnion_of_mem Bf hi)
  rw [Ncount_zero_eq_sum_sq k b (s.biUnion Bf) _ subset_rfl]
  calc ∑ h ∈ (s.biUnion Bf).image (sig k b), rcount k b (s.biUnion Bf) h ^ 2
      ≤ ∑ h ∈ (s.biUnion Bf).image (sig k b),
          s.card * ∑ i ∈ s, rcount k b (Bf i) h ^ 2 := by
        refine Finset.sum_le_sum (fun h _ => ?_)
        calc rcount k b (s.biUnion Bf) h ^ 2
            ≤ (∑ i ∈ s, rcount k b (Bf i) h) ^ 2 :=
              Nat.pow_le_pow_left (rcount_biUnion_le k b s Bf h) 2
          _ ≤ s.card * ∑ i ∈ s, rcount k b (Bf i) h ^ 2 :=
              sq_sum_le_card_mul_sum_sq_nat s _
    _ = s.card * ∑ i ∈ s, ∑ h ∈ (s.biUnion Bf).image (sig k b),
          rcount k b (Bf i) h ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = s.card * ∑ i ∈ s, Ncount k b 0 (Bf i) (Bf i) := by
        congr 1
        exact Finset.sum_congr rfl (fun i hi => (hBi i hi).symm)

end Salt.Vmvt
