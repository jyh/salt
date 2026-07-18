/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Defs

/-!
# Linnik's Lemma (Vaughan PSU Chapter 24, Lemma 24.4)

For a prime `p > k` and any target vector `h`, the number of tuples
`m : Fin k → ZMod (p^k)` whose reductions modulo `p` are pairwise distinct and
which satisfy the graded congruence system
`∑_q (m q)^j ≡ h_j (mod p^j)` for `1 ≤ j ≤ k`
is at most `k! · p^{k(k-1)/2}`.

## Route

* **The Newton–Vieta transfer over `ZMod (p^k)`.**  Because `p > k`, every
  `r` with `1 ≤ r ≤ k` is a *unit* in `ZMod (p^k)` (`p ∤ r`), so the
  integral Newton–Girard cancellation of `BaseCase.lean` goes through verbatim
  with `mul_left_cancel₀` replaced by unit cancellation.  Equal power sums
  `∑ (m i)^j = ∑ (n i)^j` for `1 ≤ j ≤ k` therefore force the monic polynomials
  `∏ (X - C (m i))` and `∏ (X - C (n i))` to be *equal* (not merely to share
  roots — `ZMod (p^k)` is not a domain, so we never pass to roots).

* **Root rigidity via distinctness.**  Evaluating that polynomial identity at
  `n s` gives `∏_q (n s - m q) = 0`.  Reducing modulo `p` (a field) pins a `q`
  with `n s ≡ m q (mod p)`; distinctness makes it unique, the remaining factors
  are units in `ZMod (p^k)`, and cancelling them yields `n s = m q` outright.
  Hence `n` is a permutation of `m`.

* **The count.**  Fibring the solution set over the exact power-sum vector
  `g = (∑ (m q)^j)_{j}` gives `card ≤ (number of admissible g) · k!`; each fibre
  injects into `Equiv.Perm (Fin k)` (`≤ k!`), and the admissible `g` form a
  product of `castHom` fibres of sizes `p^{k-j}`, total `p^{k(k-1)/2}`.
-/

namespace Salt.Vmvt

open Finset Polynomial

/-! ### Unit cancellation and the Newton–Vieta transfer over a commutative ring -/

/-- Cancellation of a unit factor in a commutative ring (works with zero
divisors, unlike `mul_left_cancel₀`). -/
lemma unit_mul_cancel {R : Type*} [CommRing R] {a A B : R} (hu : IsUnit a)
    (h : a * A = a * B) : A = B := by
  obtain ⟨u, rfl⟩ := hu
  calc A = ↑u⁻¹ * (↑u * A) := by rw [← mul_assoc, u.inv_mul, one_mul]
    _ = ↑u⁻¹ * (↑u * B) := by rw [h]
    _ = B := by rw [← mul_assoc, u.inv_mul, one_mul]

/-- Evaluating the multivariate power sum `psum` at a tuple `x` gives the ordinary
power sum `∑ i, (x i)^n`. -/
lemma aeval_psum' {R : Type*} [CommRing R] {b : ℕ} (x : Fin b → R) (n : ℕ) :
    MvPolynomial.aeval x (MvPolynomial.psum (Fin b) R n) = ∑ i, (x i) ^ n := by
  simp [MvPolynomial.psum, map_sum]

/-- The zeroth elementary symmetric function of any multiset is `1`. -/
lemma esymm_zero'' {R : Type*} [CommRing R] (s : Multiset R) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

/-- **Newton's identities, evaluated, over any commutative ring with the low
degrees invertible.**  If `1, …, b` are units in `R` and two `b`-tuples have equal
power sums up to degree `b`, then their value multisets have equal
`Multiset.esymm` up to degree `b`.  (Generalises `BaseCase.esymm_eq_of_powerSum_eq`
from `ℤ` to any such `R`; the cancellation of `d` uses `unit_mul_cancel`.) -/
lemma esymm_eq_of_powerSum_eq_units {R : Type*} [CommRing R] {b : ℕ} {m n : Fin b → R}
    (hu : ∀ r ∈ Finset.Icc 1 b, IsUnit (r : R))
    (h : ∀ j ∈ Finset.Icc 1 b, ∑ i, (m i) ^ j = ∑ i, (n i) ^ j) :
    ∀ d, d ≤ b → (Finset.univ.val.map m).esymm d = (Finset.univ.val.map n).esymm d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro hd
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · rw [esymm_zero'', esymm_zero'']
    · have Hm := congrArg (MvPolynomial.aeval m) (MvPolynomial.mul_esymm_eq_sum (Fin b) R d)
      have Hn := congrArg (MvPolynomial.aeval n) (MvPolynomial.mul_esymm_eq_sum (Fin b) R d)
      simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one,
        MvPolynomial.aeval_esymm_eq_multiset_esymm, aeval_psum'] at Hm Hn
      have key : (d : R) * (univ.val.map m).esymm d = (d : R) * (univ.val.map n).esymm d := by
        rw [Hm, Hn]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
        obtain ⟨hsum, hlt⟩ := ha
        rw [IH a.1 hlt (by omega), h a.2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
      exact unit_mul_cancel (hu d (Finset.mem_Icc.mpr ⟨hdpos, hd⟩)) key

/-- **The Newton–Vieta transfer.**  If `1, …, b` are units in `R` and two
`b`-tuples have equal power sums for every degree `1 ≤ j ≤ b`, then the monic
polynomials `∏ (X - C (m i))` and `∏ (X - C (n i))` are equal.  (Vieta packages
the equal elementary symmetric functions; no passage to roots is used, so this
holds even when `R` has zero divisors.) -/
lemma prod_X_sub_C_eq_of_powerSum_eq {R : Type*} [CommRing R] {b : ℕ} {m n : Fin b → R}
    (hu : ∀ r ∈ Finset.Icc 1 b, IsUnit (r : R))
    (h : ∀ j ∈ Finset.Icc 1 b, ∑ i, (m i) ^ j = ∑ i, (n i) ^ j) :
    ∏ i, (X - C (m i)) = ∏ i, (X - C (n i)) := by
  have hE := esymm_eq_of_powerSum_eq_units hu h
  set S := Finset.univ.val.map m with hS
  set T := Finset.univ.val.map n with hT
  have hcardS : Multiset.card S = b := by rw [hS]; simp
  have hcardT : Multiset.card T = b := by rw [hT]; simp
  have hpoly : (S.map fun a => X - C a).prod = (T.map fun a => X - C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hcardS, hcardT]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    rw [hE j hj]
  -- rewrite both Finset products into the multiset form of `hpoly`
  have lhs : ∏ i, (X - C (m i)) = (S.map fun a => X - C a).prod := by
    rw [hS, Multiset.map_map]; rfl
  have rhs : ∏ i, (X - C (n i)) = (T.map fun a => X - C a).prod := by
    rw [hT, Multiset.map_map]; rfl
  rw [lhs, rhs, hpoly]

/-! ### The mod-`p` reduction of `ZMod (p^k)` and unit detection -/

/-- The `castHom` reduction `ZMod (p^k) → ZMod p` (for `k ≥ 1`) computed via `val`. -/
lemma castHom_eq_val_cast {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k) (x : ZMod (p ^ k)) :
    ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x = ((x.val : ℕ) : ZMod p) := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

/-- **Unit detection via the residue field.**  An element of `ZMod (p^k)` whose
mod-`p` reduction is nonzero is a unit (`ZMod (p^k)` is local with residue field
`ZMod p`; concretely `p ∤ x.val` gives `Coprime x.val (p^k)`). -/
lemma isUnit_of_red_ne_zero {p k : ℕ} (hp : p.Prime) (hk : 0 < k) {x : ZMod (p ^ k)}
    (h : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x ≠ 0) : IsUnit x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hval : ((x.val : ℕ) : ZMod p) ≠ 0 := by rwa [castHom_eq_val_cast hk x] at h
  have hnd : ¬ p ∣ x.val := fun hd => hval ((ZMod.natCast_eq_zero_iff x.val p).mpr hd)
  have hcop : Nat.Coprime x.val (p ^ k) :=
    (((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm).pow_right k
  have : IsUnit ((x.val : ℕ) : ZMod (p ^ k)) := (ZMod.isUnit_iff_coprime x.val (p ^ k)).mpr hcop
  rwa [ZMod.natCast_rightInverse x] at this

/-! ### The permutation rigidity (`B(p, g) ≤ k!` at its core) -/

/-- Pairwise-distinct-mod-`p` predicate for a tuple over `ZMod (p^k)`, phrased via
`val` (total, so it makes sense for every `k`). -/
def DistinctModP {p k : ℕ} (m : Fin k → ZMod (p ^ k)) : Prop :=
  Function.Injective (fun q => ((m q).val : ZMod p))

instance {p k : ℕ} (m : Fin k → ZMod (p ^ k)) : Decidable (DistinctModP m) := by
  unfold DistinctModP; infer_instance

/-- **Linnik's rigidity (the heart of `B(p, g) ≤ k!`).**  Two tuples over
`ZMod (p^k)`, each with pairwise-distinct mod-`p` reductions, that have equal power
sums for every degree `1 ≤ j ≤ k`, differ by a permutation of the index set.

Mechanism: the Newton–Vieta transfer forces `∏ (X - C (m q)) = ∏ (X - C (n q))`;
evaluating at `n s` gives `∏_q (n s - m q) = 0`; reducing mod `p` (a field) pins a
unique `q` with `n s ≡ m q (mod p)` (uniqueness from distinctness), the other
factors are units, and cancelling them yields `n s = m q` exactly. -/
theorem perm_of_powerSum_eq_distinct {p k : ℕ} (hp : p.Prime) (hpk : k < p) (hk : 0 < k)
    {m n : Fin k → ZMod (p ^ k)} (hm : DistinctModP m) (hn : DistinctModP n)
    (h : ∀ j ∈ Finset.Icc 1 k, ∑ q, (m q) ^ j = ∑ q, (n q) ^ j) :
    ∃ σ : Equiv.Perm (Fin k), n = m ∘ σ := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set red := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) with hred_def
  -- the low degrees are units in `ZMod (p^k)`
  have hu : ∀ r ∈ Finset.Icc 1 k, IsUnit ((r : ℕ) : ZMod (p ^ k)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hrp : r < p := lt_of_le_of_lt hr.2 hpk
    have hnd : ¬ p ∣ r := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    exact (ZMod.isUnit_iff_coprime r (p ^ k)).mpr
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm.pow_right k)
  -- the Newton–Vieta polynomial identity
  have hpoly : ∏ q, (X - C (m q)) = ∏ q, (X - C (n q)) :=
    prod_X_sub_C_eq_of_powerSum_eq hu h
  -- `red` computed pointwise, and distinctness in `red`-form
  have hred_val : ∀ x, red x = ((x.val : ℕ) : ZMod p) := fun x => castHom_eq_val_cast hk x
  have hm_red : Function.Injective (fun q => red (m q)) := by
    have : (fun q => red (m q)) = (fun q => ((m q).val : ZMod p)) := funext fun q => hred_val (m q)
    rw [this]; exact hm
  have hn_red : Function.Injective (fun q => red (n q)) := by
    have : (fun q => red (n q)) = (fun q => ((n q).val : ZMod p)) := funext fun q => hred_val (n q)
    rw [this]; exact hn
  -- evaluate the identity at `n s`
  have evalP : ∀ (f : Fin k → ZMod (p ^ k)) (y : ZMod (p ^ k)),
      eval y (∏ q, (X - C (f q))) = ∏ q, (y - f q) := by
    intro f y; rw [eval_prod]
    exact Finset.prod_congr rfl fun q _ => by rw [eval_sub, eval_X, eval_C]
  have hzero : ∀ s, ∏ q, (n s - m q) = 0 := by
    intro s
    have he := congrArg (eval (n s)) hpoly
    rw [evalP m (n s), evalP n (n s)] at he
    rw [he]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (sub_self (n s))
  -- reduce mod `p` and locate a matching index
  have hexists : ∀ s, ∃ q, red (n s) = red (m q) := by
    intro s
    have := congrArg red (hzero s)
    rw [map_prod] at this
    simp only [map_sub, map_zero] at this
    obtain ⟨q, _, hq⟩ := Finset.prod_eq_zero_iff.mp this
    exact ⟨q, sub_eq_zero.mp hq⟩
  classical
  set σ0 : Fin k → Fin k := fun s => (hexists s).choose with hσ0_def
  have hσ0 : ∀ s, red (n s) = red (m (σ0 s)) := fun s => (hexists s).choose_spec
  -- upgrade the mod-`p` match to an exact equality
  have hnm : ∀ s, n s = m (σ0 s) := by
    intro s
    have hzs := hzero s
    rw [← Finset.mul_prod_erase univ (fun q => n s - m q) (Finset.mem_univ (σ0 s))] at hzs
    have hU : IsUnit (∏ q ∈ univ.erase (σ0 s), (n s - m q)) := by
      apply Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one
      intro q hq
      rw [Finset.mem_erase] at hq
      apply isUnit_of_red_ne_zero hp hk
      rw [map_sub, hσ0 s]
      intro hcontra
      exact hq.1 (hm_red (sub_eq_zero.mp hcontra)).symm
    exact sub_eq_zero.mp ((hU.mul_left_eq_zero).mp hzs)
  -- `σ0` is injective, hence a permutation
  have hσ0inj : Function.Injective σ0 := by
    intro s t hst
    exact hn_red (by rw [hσ0 s, hσ0 t, hst] : red (n s) = red (n t))
  refine ⟨Equiv.ofBijective σ0 (Finite.injective_iff_bijective.mp hσ0inj), funext fun s => ?_⟩
  simp only [Function.comp_apply, Equiv.ofBijective_apply]
  exact hnm s

/-! ### The fibre count of the reduction `ZMod (p^k) → ZMod (p^j)` -/

/-- **Each fibre of the reduction `ZMod (p^k) → ZMod (p^j)` has size `p^{k-j}`.**
The reduction is a surjective additive hom, so all fibres are equinumerous
(translation by a lift of the difference); there are `p^j` of them partitioning
`p^k` elements, giving `p^{k-j}` each.  This is the source's count of admissible
`g_j` (residues mod `p^k` reducing to a fixed value mod `p^j`). -/
lemma card_castHom_fiber {p : ℕ} (hp : p.Prime) {j k : ℕ} [NeZero (p ^ k)] [NeZero (p ^ j)]
    (hjk : j ≤ k) (c : ZMod (p ^ j)) :
    (Finset.univ.filter fun x : ZMod (p ^ k) =>
      ZMod.castHom (pow_dvd_pow p hjk) (ZMod (p ^ j)) x = c).card = p ^ (k - j) := by
  set f := ZMod.castHom (pow_dvd_pow p hjk) (ZMod (p ^ j)) with hf_def
  have hsurj : Function.Surjective f := by
    intro y0
    exact ⟨((y0.val : ℕ) : ZMod (p ^ k)), by rw [map_natCast]; exact ZMod.natCast_rightInverse y0⟩
  -- all fibres are equinumerous (translate by a lift of `b - a`)
  have equi : ∀ a b : ZMod (p ^ j),
      (univ.filter fun x => f x = a).card = (univ.filter fun x => f x = b).card := by
    intro a b
    obtain ⟨d, hd⟩ := hsurj (b - a)
    apply Finset.card_bij (fun x _ => x + d)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, by rw [map_add, hx.2, hd]; ring⟩
    · intro x _ y _ hxy; exact add_right_cancel hxy
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨y - d, ?_, by ring⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [map_sub, hy.2, hd]; ring⟩
  -- the fibres partition `ZMod (p^k)`
  have hsum : ∑ a : ZMod (p ^ j), (univ.filter fun x => f x = a).card = p ^ k := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x)),
      Finset.card_univ, ZMod.card]
  -- rewriting each summand to the `c`-fibre: `p^j · |c-fibre| = p^k`
  have hconst : ∑ a : ZMod (p ^ j), (univ.filter fun x => f x = a).card
      = Fintype.card (ZMod (p ^ j)) * (univ.filter fun x => f x = c).card := by
    rw [Finset.sum_congr rfl (fun a _ => equi a c), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  rw [hsum, ZMod.card] at hconst
  have hpk : p ^ j * p ^ (k - j) = p ^ k := by rw [← pow_add, Nat.add_sub_cancel' hjk]
  have hcancel : p ^ j * p ^ (k - j) = p ^ j * (univ.filter fun x => f x = c).card := by
    rw [hpk]; exact hconst
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) hcancel).symm

/-! ### The solution set and Linnik's Lemma -/

/-- **`A(p, h)`: the solution set of Linnik's congruence system.**  Tuples
`m : Fin k → ZMod (p^k)` with pairwise-distinct mod-`p` reductions satisfying the
graded system `∑_q (m q)^{j+1} ≡ h_j (mod p^{j+1})` for `j : Fin k` (i.e. the
`i`-th equation, `1 ≤ i ≤ k`, taken modulo `p^i`).  The graded congruence is
encoded as equality of the mod-`p^{j+1}` reductions (`ZMod.castHom`) of the power
sum and of the target `h j`. -/
def LinnikSol (p k : ℕ) [NeZero (p ^ k)] (h : Fin k → ZMod (p ^ k)) :
    Finset (Fin k → ZMod (p ^ k)) :=
  Finset.univ.filter fun m => DistinctModP m ∧ ∀ j : Fin k,
    ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (∑ q, (m q) ^ ((j : ℕ) + 1))
      = ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j)

/-- Membership in the Linnik solution set. -/
theorem mem_LinnikSol {p k : ℕ} [NeZero (p ^ k)] {h m : Fin k → ZMod (p ^ k)} :
    m ∈ LinnikSol p k h ↔ DistinctModP m ∧ ∀ j : Fin k,
      ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (∑ q, (m q) ^ ((j : ℕ) + 1))
        = ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j) := by
  unfold LinnikSol
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- **Linnik's Lemma (Vaughan PSU 24.4).**  For a prime `p > k` and any target
vector `h`, the Linnik congruence system has at most `k! · p^{k(k-1)/2}`
solutions.

The proof fibres `LinnikSol` over the *exact* power-sum vector
`g_j = ∑_q (m q)^{j+1} ∈ ZMod (p^k)`.  Each fibre injects into `Equiv.Perm (Fin k)`
(`perm_of_powerSum_eq_distinct`, the rigidity core), so has `≤ k!` elements; the
admissible `g` form a product of `castHom` fibres (`card_castHom_fiber`) of sizes
`p^{k-(j+1)}`, whose total is `p^{k(k-1)/2}`. -/
theorem linnik_lemma (p k : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hpk : k < p)
    (h : Fin k → ZMod (p ^ k)) :
    (LinnikSol p k h).card ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: a single (empty) tuple, bound `= 1`
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  -- the power-sum vector map and the admissible-target product `Gh`
  set Φ : (Fin k → ZMod (p ^ k)) → (Fin k → ZMod (p ^ k)) :=
    fun m j => ∑ q, (m q) ^ ((j : ℕ) + 1) with hΦ
  set Gh : Finset (Fin k → ZMod (p ^ k)) :=
    Fintype.piFinset fun j : Fin k => Finset.univ.filter fun x : ZMod (p ^ k) =>
      ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) x
        = ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j) with hGh
  -- every solution's power-sum vector is admissible
  have hmaps : ∀ m ∈ LinnikSol p k h, Φ m ∈ Gh := by
    intro m hm
    rw [mem_LinnikSol] at hm
    rw [hGh, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hm.2 j⟩
  -- each fibre has at most `k!` elements (the rigidity core)
  have hfibre : ∀ g : Fin k → ZMod (p ^ k),
      ((LinnikSol p k h).filter fun m => Φ m = g).card ≤ k.factorial := by
    intro g
    rcases Finset.eq_empty_or_nonempty ((LinnikSol p k h).filter fun m => Φ m = g) with
      he | ⟨m0, hm0⟩
    · rw [he]; simp
    · rw [Finset.mem_filter, mem_LinnikSol] at hm0
      obtain ⟨⟨hd0, _⟩, hΦ0⟩ := hm0
      calc ((LinnikSol p k h).filter fun m => Φ m = g).card
          ≤ (Finset.image (fun σ : Equiv.Perm (Fin k) => m0 ∘ σ) Finset.univ).card := by
            apply Finset.card_le_card
            intro m' hm'
            rw [Finset.mem_filter, mem_LinnikSol] at hm'
            obtain ⟨⟨hd', _⟩, hΦ'⟩ := hm'
            have hps : ∀ i ∈ Finset.Icc 1 k, ∑ q, (m0 q) ^ i = ∑ q, (m' q) ^ i := by
              intro i hi
              rw [Finset.mem_Icc] at hi
              have hlt : i - 1 < k := by omega
              have key : Φ m0 ⟨i - 1, hlt⟩ = Φ m' ⟨i - 1, hlt⟩ := by rw [hΦ0, hΦ']
              have hval : (i - 1) + 1 = i := by omega
              simpa only [hΦ, Fin.val_mk, hval] using key
            obtain ⟨σ, hσ⟩ := perm_of_powerSum_eq_distinct hp hpk hk hd0 hd' hps
            rw [Finset.mem_image]
            exact ⟨σ, Finset.mem_univ _, hσ.symm⟩
        _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin k))).card := Finset.card_image_le
        _ = k.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- the admissible targets number exactly `p^{k(k-1)/2}`
  have hGhcard : Gh.card = p ^ (k * (k - 1) / 2) := by
    rw [hGh, Fintype.card_piFinset]
    have hcard_j : ∀ j : Fin k, (Finset.univ.filter fun x : ZMod (p ^ k) =>
        ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) x
          = ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j)).card
        = p ^ (k - ((j : ℕ) + 1)) := by
      intro j
      haveI : NeZero (p ^ ((j : ℕ) + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
      exact card_castHom_fiber hp j.2 _
    rw [Finset.prod_congr rfl (fun j _ => hcard_j j), Finset.prod_pow_eq_pow_sum]
    congr 1
    have e1 : ∑ j : Fin k, (k - ((j : ℕ) + 1)) = ∑ i ∈ Finset.range k, i := by
      rw [Fin.sum_univ_eq_sum_range (fun i => k - (i + 1)) k,
        ← Finset.sum_range_reflect (fun i => k - (i + 1)) k]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi; omega
    rw [e1]
    have h2 := Finset.sum_range_id_mul_two k
    omega
  -- assemble: fibre-sum ≤ (#admissible targets) · k!
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ g ∈ Gh, ((LinnikSol p k h).filter fun m => Φ m = g).card
      ≤ ∑ _g ∈ Gh, k.factorial := Finset.sum_le_sum fun g _ => hfibre g
    _ = Gh.card * k.factorial := by rw [Finset.sum_const, smul_eq_mul]
    _ = k.factorial * p ^ (k * (k - 1) / 2) := by rw [hGhcard, Nat.mul_comm]

end Salt.Vmvt
