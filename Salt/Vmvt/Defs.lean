/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# The Vinogradov mean-value counting object `J_k`

This file opens the VMVT campaign by porting the counting object `J_k(A, b)`
and the elementary parts of **Lemma 24.1** of Vaughan's PSU Chapter 24 notes.

## The object

For `k b : ℕ` and a finite set `A ⊆ ℤ`, `J_k(A, b)` counts the pairs of
`b`-tuples `(m, n) ∈ A^b × A^b` whose power sums agree up to degree `k`:
`∑_q (m q)^j = ∑_q (n q)^j` for every `j` with `1 ≤ j ≤ k`.  This is the number
of solutions of the Vinogradov system (24.1) and, by Parseval, equals the mean
value `∫_{T^k} |S(α, A)|^{2b} dα`.

## Representation choices (documented deliberately)

* **Value type `ℤ`, not `ℕ`.**  The notes work with intervals of *integers* and
  the load-bearing symmetry of `J_k` is the *dilation–translation invariance*
  `J_k(qA + r, b) = J_k(A, b)`.  Translation needs subtraction and dilation
  needs `q^j ≠ 0`; both are cleanest over the integral domain `ℤ`.

* **Tuples as `Fin b → ℤ` via `Fintype.piFinset`, not `Finset.pi`.**  The tuple
  space is `Fintype.piFinset (fun _ : Fin b => A)`, a `Finset (Fin b → ℤ)` of
  *total* functions.  This makes the invariance bijections literal function
  composition `g ∘ m` (no dependent-`Finset.pi` friction), and
  `Fintype.mem_piFinset : m ∈ piFinset t ↔ ∀ q, m q ∈ t q` gives a clean
  membership characterisation.

* **The power-sum equalities as `∀ j ∈ Finset.Icc 1 k`.**  Bounded `∀` over a
  `Finset` is decidable (`Finset.decidableBAll`), so `solSet` is a genuine
  `Finset.filter` with a computable cardinality.

## Scope

Landed here: the object `Jk`/`JkI`, the API (`mem_solSet`, `Jk_nonneg`,
`Jk_mono`), the diagonal lower bound `A.card ^ b ≤ Jk`, the **translation
invariance** (`Jk_image_add`), the **dilation invariance** (`Jk_image_mul`), and
their combined **affine invariance** `J_k(qA + r, b) = J_k(A, b)`
(`Jk_image_affine`).  The `ℓ`-shifted general count `N(B, C, ℓ)`
[Lemma 24.1(b),(e)] and the union/splitting bound [24.1(c)] are deferred as
named residuals for the next VMVT node.
-/

namespace Salt.Vmvt

open Finset

/-- The power-sum agreement predicate: the tuples `m, n : Fin b → ℤ` have equal
power sums `∑_q (m q)^j = ∑_q (n q)^j` for every degree `j` with `1 ≤ j ≤ k`.
This is the defining relation of the Vinogradov system (24.1). -/
def PowerSumEq (k b : ℕ) (m n : Fin b → ℤ) : Prop :=
  ∀ j ∈ Finset.Icc 1 k, ∑ q, (m q) ^ j = ∑ q, (n q) ^ j

instance (k b : ℕ) (m n : Fin b → ℤ) : Decidable (PowerSumEq k b m n) := by
  unfold PowerSumEq; infer_instance

/-- The set of solution pairs `(m, n) ∈ A^b × A^b` of the Vinogradov system:
`b`-tuples over `A` whose power sums agree for every degree `1 ≤ j ≤ k`. -/
def solSet (k b : ℕ) (A : Finset ℤ) : Finset ((Fin b → ℤ) × (Fin b → ℤ)) :=
  ((Fintype.piFinset fun _ : Fin b => A) ×ˢ (Fintype.piFinset fun _ : Fin b => A)).filter
    fun mn => PowerSumEq k b mn.1 mn.2

/-- `J_k(A, b)`: the number of solutions of the Vinogradov system (24.1). -/
def Jk (k b : ℕ) (A : Finset ℤ) : ℕ := (solSet k b A).card

/-- The interval specialisation `J_k(x, b) = J_k((0, x], b)` of the notes, with
`(0, x]` the integer interval `{1, …, x}`. -/
noncomputable def JkI (k b x : ℕ) : ℕ := Jk k b (Finset.Ioc (0 : ℤ) (x : ℤ))

/-- Membership in the solution set: both tuples lie in `A`, and their power sums
agree up to degree `k`. -/
theorem mem_solSet {k b : ℕ} {A : Finset ℤ} {mn : (Fin b → ℤ) × (Fin b → ℤ)} :
    mn ∈ solSet k b A ↔
      (∀ q, mn.1 q ∈ A) ∧ (∀ q, mn.2 q ∈ A) ∧ PowerSumEq k b mn.1 mn.2 := by
  unfold solSet
  rw [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
  tauto

/-- Trivial nonnegativity (`Jk` is a `ℕ`-valued count). -/
theorem Jk_nonneg (k b : ℕ) (A : Finset ℤ) : 0 ≤ Jk k b A := Nat.zero_le _

/-- **Lemma 24.1(a).**  `J_k` is monotone in the underlying set. -/
theorem Jk_mono {k b : ℕ} {A B : Finset ℤ} (h : A ⊆ B) : Jk k b A ≤ Jk k b B := by
  apply Finset.card_le_card
  intro mn hmn
  rw [mem_solSet] at hmn ⊢
  exact ⟨fun q => h (hmn.1 q), fun q => h (hmn.2.1 q), hmn.2.2⟩

/-- **Lemma 24.1(c), diagonal case.**  The diagonal solutions `(m, m)` give the
lower bound `|A|^b ≤ J_k(A, b)`. -/
theorem Jk_ge_card_pow (k b : ℕ) (A : Finset ℤ) : A.card ^ b ≤ Jk k b A := by
  rw [← Fintype.card_piFinset_const A b]
  apply Finset.card_le_card_of_injOn (fun m => (m, m))
  · intro m hm
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hm
    rw [Finset.mem_coe, mem_solSet]
    exact ⟨hm, hm, fun j _ => rfl⟩
  · intro m _ m' _ h
    exact congrArg Prod.fst h

/-!
## Translation invariance (Lemma 24.1(d), `r`-part)

The load-bearing symmetry: shifting every entry of the tuples by a constant `c`
preserves the power-sum agreement.  Mechanism (binomial theorem): for a fixed
degree `j`,
`∑_q (f q + c)^j = ∑_{i ≤ j} c^{j-i} C(j,i) ∑_q (f q)^i`,
and the inner sums agree for `m` and `n` at every `i ≤ j ≤ k` (the `i = 0`
term is `b` on both sides, the `i ≥ 1` terms by hypothesis).
-/

/-- **Translation-stability of equal power sums.**  If `m, n` have equal power
sums up to degree `k`, so do the translates `m + c`, `n + c`. -/
theorem powerSums_translate {k b : ℕ} {m n : Fin b → ℤ} (c : ℤ)
    (h : PowerSumEq k b m n) :
    PowerSumEq k b (fun q => m q + c) (fun q => n q + c) := by
  intro j hj
  have key : ∀ f : Fin b → ℤ,
      ∑ q, (f q + c) ^ j
        = ∑ i ∈ Finset.range (j + 1), c ^ (j - i) * (j.choose i : ℤ) * ∑ q, (f q) ^ i := by
    intro f
    calc ∑ q, (f q + c) ^ j
        = ∑ q, ∑ i ∈ Finset.range (j + 1), (f q) ^ i * c ^ (j - i) * (j.choose i : ℤ) := by
          refine Finset.sum_congr rfl (fun q _ => ?_); rw [add_pow]
      _ = ∑ i ∈ Finset.range (j + 1), ∑ q, (f q) ^ i * c ^ (j - i) * (j.choose i : ℤ) :=
          Finset.sum_comm
      _ = ∑ i ∈ Finset.range (j + 1), c ^ (j - i) * (j.choose i : ℤ) * ∑ q, (f q) ^ i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun q _ => by ring)
  simp only [key m, key n]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0; simp
  · rw [h i (Finset.mem_Icc.mpr ⟨hipos, le_trans hi (Finset.mem_Icc.mp hj).2⟩)]

/-- **Lemma 24.1(d), translation part.**  `J_k` is invariant under translating
the underlying set by a constant `c`: `J_k(A + c, b) = J_k(A, b)`. -/
theorem Jk_image_add (k b : ℕ) (A : Finset ℤ) (c : ℤ) :
    Jk k b (A.image (· + c)) = Jk k b A := by
  have himg : ∀ y : ℤ, y ∈ A.image (· + c) ↔ y - c ∈ A := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa using ha
    · intro hy; exact ⟨y - c, hy, by ring⟩
  refine Finset.card_nbij' (fun mn => (fun q => mn.1 q - c, fun q => mn.2 q - c))
    (fun mn => (fun q => mn.1 q + c, fun q => mn.2 q + c)) ?_ ?_ ?_ ?_
  · -- MapsTo the `-c` shift : solSet (A + c) → solSet A
    intro mn hmn
    rw [Finset.mem_coe, mem_solSet] at hmn
    obtain ⟨hm, hn, hpred⟩ := hmn
    rw [Finset.mem_coe, mem_solSet]
    refine ⟨fun q => (himg _).mp (hm q), fun q => (himg _).mp (hn q), ?_⟩
    intro j hj
    have h2 := powerSums_translate (-c) hpred j hj
    simpa only [← sub_eq_add_neg] using h2
  · -- MapsTo the `+c` shift : solSet A → solSet (A + c)
    intro mn hmn
    rw [Finset.mem_coe, mem_solSet] at hmn
    obtain ⟨hm, hn, hpred⟩ := hmn
    rw [Finset.mem_coe, mem_solSet]
    exact ⟨fun q => Finset.mem_image.mpr ⟨mn.1 q, hm q, rfl⟩,
      fun q => Finset.mem_image.mpr ⟨mn.2 q, hn q, rfl⟩, powerSums_translate c hpred⟩
  · intro mn _; ext q <;> simp
  · intro mn _; ext q <;> simp

/-!
## Dilation invariance (Lemma 24.1(d), `q`-part)

Scaling every tuple entry by a nonzero `q` scales the degree-`j` power sum by
`q^j`.  Since `ℤ` is an integral domain, `q^j ≠ 0`, so power-sum equality is
preserved and reflected.  Together with translation this gives the full
`J_k(qA + r, b) = J_k(A, b)` of the notes.
-/

/-- **Dilation-stability of equal power sums.**  Scaling both tuples by a common
`q` preserves power-sum agreement (the degree-`j` sums both scale by `q^j`). -/
theorem powerSums_mul {k b : ℕ} {m n : Fin b → ℤ} (q : ℤ)
    (h : PowerSumEq k b m n) :
    PowerSumEq k b (fun i => q * m i) (fun i => q * n i) := by
  intro j hj
  have e : ∀ f : Fin b → ℤ, ∑ i, (q * f i) ^ j = q ^ j * ∑ i, (f i) ^ j := fun f => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [mul_pow])
  simp only [e, h j hj]

/-- **Lemma 24.1(d), dilation part.**  For `q ≠ 0`, `J_k` is invariant under
scaling the underlying set: `J_k(qA, b) = J_k(A, b)`. -/
theorem Jk_image_mul (k b : ℕ) (A : Finset ℤ) (q : ℤ) (hq : q ≠ 0) :
    Jk k b (A.image (q * ·)) = Jk k b A := by
  refine Finset.card_nbij' (fun mn => (fun i => mn.1 i / q, fun i => mn.2 i / q))
    (fun mn => (fun i => q * mn.1 i, fun i => q * mn.2 i)) ?_ ?_ ?_ ?_
  · -- MapsTo the `/q` shrink : solSet (qA) → solSet A
    intro mn hmn
    rw [Finset.mem_coe, mem_solSet] at hmn
    obtain ⟨hm, hn, hpred⟩ := hmn
    have dvd1 : ∀ i, q ∣ mn.1 i := fun i => by
      obtain ⟨a, _, hqa⟩ := Finset.mem_image.mp (hm i); exact ⟨a, hqa.symm⟩
    have dvd2 : ∀ i, q ∣ mn.2 i := fun i => by
      obtain ⟨a, _, hqa⟩ := Finset.mem_image.mp (hn i); exact ⟨a, hqa.symm⟩
    rw [Finset.mem_coe, mem_solSet]
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp (hm i)
      have hdiv : mn.1 i / q = a := by rw [← hqa]; exact Int.mul_ediv_cancel_left a hq
      simpa only [hdiv] using ha
    · obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp (hn i)
      have hdiv : mn.2 i / q = a := by rw [← hqa]; exact Int.mul_ediv_cancel_left a hq
      simpa only [hdiv] using ha
    · intro j hj
      have hp := hpred j hj
      have r1 : ∑ i, (mn.1 i) ^ j = q ^ j * ∑ i, (mn.1 i / q) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [← mul_pow, Int.mul_ediv_cancel' (dvd1 i)])
      have r2 : ∑ i, (mn.2 i) ^ j = q ^ j * ∑ i, (mn.2 i / q) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [← mul_pow, Int.mul_ediv_cancel' (dvd2 i)])
      rw [r1, r2] at hp
      exact mul_left_cancel₀ (pow_ne_zero j hq) hp
  · -- MapsTo the `*q` stretch : solSet A → solSet (qA)
    intro mn hmn
    rw [Finset.mem_coe, mem_solSet] at hmn
    obtain ⟨hm, hn, hpred⟩ := hmn
    rw [Finset.mem_coe, mem_solSet]
    exact ⟨fun i => Finset.mem_image.mpr ⟨mn.1 i, hm i, rfl⟩,
      fun i => Finset.mem_image.mpr ⟨mn.2 i, hn i, rfl⟩, powerSums_mul q hpred⟩
  · -- left inverse: `*q` after `/q` on solSet (qA)
    intro mn hmn
    rw [Finset.mem_coe, mem_solSet] at hmn
    obtain ⟨hm, hn, _⟩ := hmn
    have dvd1 : ∀ i, q ∣ mn.1 i := fun i => by
      obtain ⟨a, _, hqa⟩ := Finset.mem_image.mp (hm i); exact ⟨a, hqa.symm⟩
    have dvd2 : ∀ i, q ∣ mn.2 i := fun i => by
      obtain ⟨a, _, hqa⟩ := Finset.mem_image.mp (hn i); exact ⟨a, hqa.symm⟩
    ext i
    · exact Int.mul_ediv_cancel' (dvd1 i)
    · exact Int.mul_ediv_cancel' (dvd2 i)
  · -- right inverse: `/q` after `*q` on solSet A
    intro mn _
    ext i
    · exact Int.mul_ediv_cancel_left (mn.1 i) hq
    · exact Int.mul_ediv_cancel_left (mn.2 i) hq

/-- **Lemma 24.1(d), full form.**  The dilation–translation invariance
`J_k(qA + r, b) = J_k(A, b)` for `q ≠ 0`, obtained by composing the dilation and
translation invariances (`qA + r = (qA) + r` as an image). -/
theorem Jk_image_affine (k b : ℕ) (A : Finset ℤ) (q r : ℤ) (hq : q ≠ 0) :
    Jk k b (A.image (fun a => q * a + r)) = Jk k b A := by
  have himg : A.image (fun a => q * a + r) = (A.image (q * ·)).image (· + r) := by
    simp only [Finset.image_image, Function.comp_def]
  rw [himg, Jk_image_add, Jk_image_mul k b A q hq]

end Salt.Vmvt
