/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Shifted
import Salt.Vmvt.PrimeCount

/-!
# Theorem 24.5 — the transversality split (VMVT node R2)

This file ports the **transversality argument** of Vaughan PSU Chapter 24,
Theorem 24.5 (the large-`x` p-adic step), following the source's `S₁`/`S₂` split
and the prime-pigeonhole that makes the transversal case work.

## The Zeno ladder (three rungs)

* **R2-1 — the pigeonhole (`transversal_prime_exists`).**  Given `k` integer
  values `m : Fin k → ℤ` in `(0, x]`, pairwise distinct as integers, and a set of
  primes `P` each `> y` with `y^k ≥ x` and `#P > ½k²(k−1)`, *some* `p ∈ P` has the
  `mᵢ` pairwise distinct modulo `p`.  Mechanism: the product `P(m) = ∏_{i<j}(mᵢ−mⱼ)`
  is a nonzero integer of size `≤ x^{k(k−1)/2} ≤ y^{k²(k−1)/2}`, so at most
  `½k²(k−1)` primes `> y` divide it (each contributes a factor `≥ y`); the surplus
  prime is transversal.  **Catch #66**: the source's printed prime count
  `½k(k−1)` is an OCR error — the correct supply is `½k(k²−1) = Θ(k³)`, and the
  margin `½k(k²−1) − ½k²(k−1) = ½k(k−1) > 0` is exactly what closes the box.

* **R2-2 — the split** (below): `J_k ≤ 2(S₁ + S₂)` with `Sᵢ = ∑_h Rᵢ(h)²`, and the
  transversal union bound `R₁(h) ≤ ∑_{p∈P} R₄(h,p)`.

* **R2-3 — the degenerate count** (below): the `S₂` term.

## The prime-count engineering (R2-1)

The clean chain over `ℕ`, division-free (all `/2`'s are dodged by working with the
*full* off-diagonal exponent `k(k−1)` on the squared count).  Let
`bad = {p ∈ P : p ∣ P(m)}`.  Distinct primes multiply into a divisor of `P(m)`, so
`∏_{p∈bad} p ≤ |P(m)|`, and each `p ≥ y` gives `y^{#bad} ≤ ∏_{p∈bad} p`.  Then
`y^{#bad} ≤ |P(m)| ≤ x^{C(k,2)} ≤ (y^k)^{C(k,2)} = y^{k·C(k,2)}`, so
`#bad ≤ k·C(k,2) = ½k²(k−1)`.  With `#P > ½k²(k−1)`, `bad ⊊ P`.
-/

namespace Salt.Vmvt

open Finset

/-! ## R2-1: the strict-upper-triangle index and its cardinality -/

/-- The strict-upper-triangle set of ordered index pairs `(i, j)` with `i < j`,
the domain of the difference product `P(m) = ∏_{i<j}(mᵢ − mⱼ)`. -/
def offPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

/-- `#{(i,j) : i < j} = C(k,2)`, in the division-free form `2·#offPairs = k(k−1)`.
Proof: `offPairs` and its mirror `{j < i}` are equinumerous (`Prod.swap`), disjoint,
and union to the off-diagonal `univ.offDiag` of cardinality `k·k − k`. -/
lemma two_mul_offPairs_card (k : ℕ) : 2 * (offPairs k).card = k * (k - 1) := by
  classical
  let G : Finset (Fin k × Fin k) := Finset.univ.filter (fun ij => ij.2 < ij.1)
  have hcardEq : (offPairs k).card = G.card := by
    apply Finset.card_bij (fun ij _ => Prod.swap ij)
    · intro ij hij
      simp only [offPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact hij
    · intro a _ b _ hab
      exact Prod.swap_injective hab
    · intro ij hij
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      refine ⟨Prod.swap ij, ?_, ?_⟩
      · simp only [offPairs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
          Prod.snd_swap]
        exact hij
      · simp [Prod.swap_swap]
  have hunion : offPairs k ∪ G = (Finset.univ : Finset (Fin k)).offDiag := by
    ext ij
    simp only [Finset.mem_union, offPairs, G, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact (ne_of_lt h).symm
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hdisj : Disjoint (offPairs k) G := by
    simp only [Finset.disjoint_left, offPairs, G, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ij h1 h2
    exact absurd h1 (not_lt.mpr (le_of_lt h2))
  have hcardUnion : (offPairs k ∪ G).card = (offPairs k).card + G.card :=
    Finset.card_union_of_disjoint hdisj
  have hoff : (Finset.univ : Finset (Fin k)).offDiag.card = k * k - k := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  rw [hunion, hoff, ← hcardEq] at hcardUnion
  have hks : k * k - k = k * (k - 1) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rfl
    · have h1 : 1 ≤ k := h
      have hle : k ≤ k * k := by nlinarith [h]
      zify [hle, h1]
      ring
  omega

/-! ## R2-1: the pigeonhole -/

/-- **R2-1 — the transversal prime exists.**  Let `m : Fin k → ℤ` be `k` integer
values in `(0, x]`, pairwise distinct as integers, and `P` a set of primes each
`> y`, with `y^k ≥ x` and `#P > ½k²(k−1)` (division-free: `k·k·(k−1) < 2·#P`).
Then *some* `p ∈ P` has the `mᵢ` pairwise distinct modulo `p`.

This is the heart of the transversality argument: the difference product
`P(m) = ∏_{i<j}(mᵢ − mⱼ)` has at most `½k²(k−1)` prime divisors `> y`, fewer than
the `> ½k²(k−1)` available primes, so a surplus prime avoids `P(m)` entirely. -/
theorem transversal_prime_exists
    {k : ℕ} (x y : ℕ) (hy : 2 ≤ y) (hyx : x ≤ y ^ k)
    (m : Fin k → ℤ) (hm_pos : ∀ i, 1 ≤ m i) (hm_le : ∀ i, m i ≤ (x : ℤ))
    (hm_inj : Function.Injective m)
    (P : Finset ℕ) (hP_prime : ∀ p ∈ P, p.Prime) (hP_gt : ∀ p ∈ P, y < p)
    (hP_card : k * k * (k - 1) < 2 * P.card) :
    ∃ p ∈ P, ∀ i j : Fin k, i ≠ j → ¬ ((p : ℤ) ∣ (m i - m j)) := by
  classical
  -- The difference product and its nonvanishing.
  set Pm : ℤ := ∏ ij ∈ offPairs k, (m ij.1 - m ij.2) with hPmdef
  have hPm_ne : Pm ≠ 0 := by
    rw [hPmdef, Finset.prod_ne_zero_iff]
    intro ij hij
    rw [offPairs, Finset.mem_filter] at hij
    exact sub_ne_zero.mpr (fun h => (ne_of_lt hij.2) (hm_inj h))
  -- Each difference has natAbs at most x.
  have hdiff_le : ∀ i j : Fin k, (m i - m j).natAbs ≤ x := by
    intro i j
    have hi : ((m i).toNat : ℤ) = m i := Int.toNat_of_nonneg (by linarith [hm_pos i])
    have hj : ((m j).toNat : ℤ) = m j := Int.toNat_of_nonneg (by linarith [hm_pos j])
    have hix : (m i).toNat ≤ x := by
      have : ((m i).toNat : ℤ) ≤ (x : ℤ) := by rw [hi]; exact hm_le i
      exact_mod_cast this
    have hjx : (m j).toNat ≤ x := by
      have : ((m j).toNat : ℤ) ≤ (x : ℤ) := by rw [hj]; exact hm_le j
      exact_mod_cast this
    calc (m i - m j).natAbs
        = (((m i).toNat : ℤ) - ((m j).toNat : ℤ)).natAbs := by rw [hi, hj]
      _ ≤ x := Int.natAbs_coe_sub_coe_le_of_le hix hjx
  -- |P(m)| ≤ x ^ #offPairs.
  have hPm_natAbs_le : Pm.natAbs ≤ x ^ (offPairs k).card := by
    have hmap : Pm.natAbs = ∏ ij ∈ offPairs k, (m ij.1 - m ij.2).natAbs := by
      rw [hPmdef]; exact map_prod Int.natAbsHom _ _
    rw [hmap]
    calc ∏ ij ∈ offPairs k, (m ij.1 - m ij.2).natAbs
        ≤ ∏ _ij ∈ offPairs k, x := Finset.prod_le_prod' (fun ij _ => hdiff_le ij.1 ij.2)
      _ = x ^ (offPairs k).card := by rw [Finset.prod_const]
  -- The bad primes (those dividing P(m)).
  set bad : Finset ℕ := P.filter (fun p => (p : ℤ) ∣ Pm) with hbaddef
  have hbadsub : bad ⊆ P := Finset.filter_subset _ _
  -- ∏_{p ∈ bad} p divides |P(m)|.
  have hprod_dvd : (∏ p ∈ bad, p) ∣ Pm.natAbs := by
    apply Finset.prod_primes_dvd
    · intro p hp; exact (hP_prime p (hbadsub hp)).prime
    · intro p hp
      rw [hbaddef, Finset.mem_filter] at hp
      have : ((p : ℤ)).natAbs ∣ Pm.natAbs := Int.natAbs_dvd_natAbs.mpr hp.2
      simpa using this
  -- Count bound: #bad ≤ k · #offPairs.
  have hcount : bad.card ≤ k * (offPairs k).card := by
    have hchain : y ^ bad.card ≤ y ^ (k * (offPairs k).card) := by
      calc y ^ bad.card
          = ∏ _p ∈ bad, y := by rw [Finset.prod_const]
        _ ≤ ∏ p ∈ bad, p := Finset.prod_le_prod' (fun p hp => le_of_lt (hP_gt p (hbadsub hp)))
        _ ≤ Pm.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hPm_ne) hprod_dvd
        _ ≤ x ^ (offPairs k).card := hPm_natAbs_le
        _ ≤ (y ^ k) ^ (offPairs k).card := Nat.pow_le_pow_left hyx _
        _ = y ^ (k * (offPairs k).card) := by rw [← pow_mul]
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < y)).1 hchain
  -- Pigeonhole: #bad < #P, so a prime avoids P(m).
  have hval : 2 * (k * (offPairs k).card) = k * k * (k - 1) := by
    have h := two_mul_offPairs_card k
    calc 2 * (k * (offPairs k).card)
        = k * (2 * (offPairs k).card) := by ring
      _ = k * (k * (k - 1)) := by rw [h]
      _ = k * k * (k - 1) := by ring
  have hlt : bad.card < P.card := by omega
  have hexists : (P \ bad).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hbadsub]
    omega
  obtain ⟨p, hp⟩ := hexists
  rw [Finset.mem_sdiff] at hp
  obtain ⟨hpP, hpbad⟩ := hp
  refine ⟨p, hpP, ?_⟩
  intro i j hij hdvd
  apply hpbad
  rw [hbaddef, Finset.mem_filter]
  refine ⟨hpP, ?_⟩
  rw [hPmdef]
  rcases lt_or_gt_of_ne hij with hlt' | hgt'
  · have hmem : (i, j) ∈ offPairs k := by
      rw [offPairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt'⟩
    exact hdvd.trans (Finset.dvd_prod_of_mem (fun ij => m ij.1 - m ij.2) hmem)
  · have hmem : (j, i) ∈ offPairs k := by
      rw [offPairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt'⟩
    have hdvd2 : (p : ℤ) ∣ (m j - m i) := by
      have : (p : ℤ) ∣ -(m i - m j) := dvd_neg.mpr hdvd
      simpa using this
    exact hdvd2.trans (Finset.dvd_prod_of_mem (fun ij => m ij.1 - m ij.2) hmem)

/-! ## R2-2: the transversality split

The full solution box `solBox b x = (0, x]^b`, split by whether the `k` designated
coordinates `e : Fin k → Fin b` are pairwise distinct (as integers).  The
combinatorial split `J_k ≤ 2(S₁ + S₂)` is `Jk_le_two_mul_filter_split`; the
transversal bound `S₁ ≤ #P · ∑_p I(p)` is `distinctBox_le_card_mul_sum`, feeding
R2-1's pigeonhole through `Ncount_mono` + the landed `Ncount_union_le`. -/

/-- The full solution box `(0, x]^b` of `b`-tuples of integers in `(0, x]`. -/
noncomputable def solBox (b x : ℕ) : Finset (Fin b → ℤ) :=
  Fintype.piFinset fun _ : Fin b => Finset.Ioc (0 : ℤ) (x : ℤ)

/-- The designated block (`k` coordinates `e`) is pairwise distinct as integers. -/
def blockDistinct {k b : ℕ} (e : Fin k → Fin b) (m : Fin b → ℤ) : Prop :=
  ∀ i j : Fin k, i ≠ j → m (e i) ≠ m (e j)

instance {k b : ℕ} (e : Fin k → Fin b) : DecidablePred (blockDistinct e) :=
  fun m => by unfold blockDistinct; infer_instance

/-- The designated block is pairwise distinct modulo `p`. -/
def blockDistinctMod {k b : ℕ} (e : Fin k → Fin b) (p : ℕ) (m : Fin b → ℤ) : Prop :=
  ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (m (e i) - m (e j))

instance {k b : ℕ} (e : Fin k → Fin b) (p : ℕ) : DecidablePred (blockDistinctMod e p) :=
  fun m => by unfold blockDistinctMod; infer_instance

/-- The transversal (block-distinct) sub-box `D₁`. -/
noncomputable def distinctBox {k b : ℕ} (x : ℕ) (e : Fin k → Fin b) :
    Finset (Fin b → ℤ) :=
  (solBox b x).filter (blockDistinct e)

/-- The degenerate (block-not-distinct) sub-box `D₂`. -/
noncomputable def degenBox {k b : ℕ} (x : ℕ) (e : Fin k → Fin b) : Finset (Fin b → ℤ) :=
  (solBox b x).filter (fun m => ¬ blockDistinct e m)

/-- The `p`-transversal sub-box `D₄(p)`: block distinct modulo `p`. -/
noncomputable def transBox {k b : ℕ} (x : ℕ) (e : Fin k → Fin b) (p : ℕ) :
    Finset (Fin b → ℤ) :=
  (solBox b x).filter (blockDistinctMod e p)

/-- **The `Q`/¬`Q` fibre split of `J_k` (general form).**  For any decidable
predicate `Q` on tuples, `J_k(A,b) ≤ 2(S₁ + S₂)` where `Sᵢ` are the diagonal counts
of the `Q`- and `¬Q`-filtered boxes.  This is the source's `J_k ≤ 2(S₁ + S₂)` from
`R = R₁ + R₂` and `(a+b)² ≤ 2(a²+b²)`, summed over signatures with the common index
`W = D.image σ`. -/
theorem Jk_le_two_mul_filter_split (k b : ℕ) (A : Finset ℤ) (Q : (Fin b → ℤ) → Prop)
    [DecidablePred Q] :
    Jk k b A ≤ 2 * (Ncount k b 0 ((Fintype.piFinset fun _ : Fin b => A).filter Q)
                      ((Fintype.piFinset fun _ : Fin b => A).filter Q)
                    + Ncount k b 0 ((Fintype.piFinset fun _ : Fin b => A).filter (fun m => ¬ Q m))
                      ((Fintype.piFinset fun _ : Fin b => A).filter (fun m => ¬ Q m))) := by
  classical
  set D := Fintype.piFinset fun _ : Fin b => A with hD
  set DQ := D.filter Q with hDQ
  set DnQ := D.filter (fun m => ¬ Q m) with hDnQ
  -- fibre split: r_D = r_DQ + r_DnQ
  have hfib : ∀ h, rcount k b D h = rcount k b DQ h + rcount k b DnQ h := by
    intro h
    have hdisj : Disjoint (DQ.filter fun m => sig k b m = h)
        (DnQ.filter fun m => sig k b m = h) := by
      rw [Finset.disjoint_left]
      intro m hmQ hmnQ
      simp only [hDQ, hDnQ, Finset.mem_filter] at hmQ hmnQ
      exact hmnQ.1.2 hmQ.1.2
    unfold rcount
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext m
    simp only [hDQ, hDnQ, Finset.mem_union, Finset.mem_filter]
    tauto
  -- Jk = Ncount 0 D D = ∑_{h ∈ W} r_D(h)^2, with W = D.image σ
  set W := D.image (sig k b) with hW
  have hJ : Jk k b A = ∑ h ∈ W, rcount k b D h ^ 2 := by
    rw [← Ncount_zero_eq_Jk, Ncount_zero_eq_sum_sq k b D W subset_rfl]
  have hSQ : Ncount k b 0 DQ DQ = ∑ h ∈ W, rcount k b DQ h ^ 2 :=
    Ncount_zero_eq_sum_sq k b DQ W (Finset.image_subset_image (Finset.filter_subset _ _))
  have hSnQ : Ncount k b 0 DnQ DnQ = ∑ h ∈ W, rcount k b DnQ h ^ 2 :=
    Ncount_zero_eq_sum_sq k b DnQ W (Finset.image_subset_image (Finset.filter_subset _ _))
  rw [hJ, hSQ, hSnQ, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [hfib h]
  nlinarith [two_mul_mul_le_sq_add_sq (rcount k b DQ h) (rcount k b DnQ h)]

/-- **`J_k(x, b) ≤ 2(S₁ + S₂)`** on the interval box, split by block distinctness:
`S₁ = Ncount(D₁)`, `S₂ = Ncount(D₂)`.  The interval specialisation of
`Jk_le_two_mul_filter_split` with `Q = blockDistinct e`. -/
theorem JkI_le_two_mul_split {k b : ℕ} (x : ℕ) (e : Fin k → Fin b) :
    JkI k b x ≤ 2 * (Ncount k b 0 (distinctBox x e) (distinctBox x e)
                     + Ncount k b 0 (degenBox x e) (degenBox x e)) := by
  unfold JkI distinctBox degenBox solBox
  exact Jk_le_two_mul_filter_split k b (Finset.Ioc (0 : ℤ) (x : ℤ)) (blockDistinct e)

/-- **R2-2 — the transversal bound `S₁ ≤ #P · ∑_p I(p)`.**  Given the pigeonhole
prime set `P` (each prime `> y`, `y^k ≥ x`, `#P > ½k²(k−1)`), the transversal box
`D₁` is covered by `⋃_{p∈P} D₄(p)` (R2-1 supplies the covering prime per tuple), so
`Ncount(D₁) ≤ #P · ∑_{p∈P} Ncount(D₄(p))` via `Ncount_mono` + the landed
`Ncount_union_le`.  `Ncount(D₄(p)) = I(p)` is R3's transversal count. -/
theorem distinctBox_le_card_mul_sum {k r : ℕ} (x y : ℕ) (e : Fin k → Fin (k * r))
    (hy : 2 ≤ y) (hyx : x ≤ y ^ k)
    (P : Finset ℕ) (hP_prime : ∀ p ∈ P, p.Prime) (hP_gt : ∀ p ∈ P, y < p)
    (hP_card : k * k * (k - 1) < 2 * P.card) :
    Ncount k (k * r) 0 (distinctBox x e) (distinctBox x e)
      ≤ P.card * ∑ p ∈ P, Ncount k (k * r) 0 (transBox x e p) (transBox x e p) := by
  classical
  -- The covering: every block-distinct tuple lands in some D₄(p).
  have hsub : distinctBox x e ⊆ P.biUnion (fun p => transBox x e p) := by
    intro m hm
    rw [distinctBox, Finset.mem_filter] at hm
    obtain ⟨hmD, hmdist⟩ := hm
    have hmem : ∀ i, m (e i) ∈ Finset.Ioc (0 : ℤ) (x : ℤ) := by
      intro i; rw [solBox, Fintype.mem_piFinset] at hmD; exact hmD (e i)
    have hpos : ∀ i, 1 ≤ m (e i) := by
      intro i; have := hmem i; rw [Finset.mem_Ioc] at this; omega
    have hle : ∀ i, m (e i) ≤ (x : ℤ) := by
      intro i; have := hmem i; rw [Finset.mem_Ioc] at this; exact this.2
    have hinj : Function.Injective (fun i => m (e i)) := by
      intro i j hij; by_contra hne; exact hmdist i j hne hij
    obtain ⟨p, hpP, hpdist⟩ :=
      transversal_prime_exists x y hy hyx (fun i => m (e i)) hpos hle hinj P hP_prime hP_gt hP_card
    rw [Finset.mem_biUnion]
    exact ⟨p, hpP, Finset.mem_filter.mpr ⟨hmD, hpdist⟩⟩
  calc Ncount k (k * r) 0 (distinctBox x e) (distinctBox x e)
      ≤ Ncount k (k * r) 0 (P.biUnion (fun p => transBox x e p))
          (P.biUnion (fun p => transBox x e p)) := Ncount_mono k (k * r) 0 hsub hsub
    _ ≤ P.card * ∑ p ∈ P, Ncount k (k * r) 0 (transBox x e p) (transBox x e p) :=
        Ncount_union_le k (k * r) P (fun p => transBox x e p)

/-! ## R2-3: the degenerate decomposition (partial — Hölder closure flagged)

The degenerate box `D₂` (block not distinct) is the union over pairs `a < b` of the
**pair-collapse boxes** `D_{a=b}` (tuples with `m(e a) = m(e b)`).  This lands the
source's "the degenerate S₂-case collapses two variables" as a clean union bound
`S₂ ≤ #offPairs · ∑_{a<b} Ncount(D_{a=b})` via the landed `Ncount_union_le`.

⚠ **FLAGGED (node R2-3, `docs/blueprints/flags.md`).**  Closing each
`Ncount(D_{a=b})` term to beat the target exponent `E(k,r)` needs the source's
**self-improving fractional Hölder** `S₂ ≤ k⁴·J_k^{1−2/(kr)}` (via
`Finset.inner_le_Lp_mul_Lq`) — the "second named gap".  Crude routes provably fail:
`S₂ ≤ |D₂|²` lands at `x^{2kr−2}`, and `2kr−2 > E(k,r)` for `k ≥ 2` (wrong side);
`Ncount(D_{a=b}) ≤ x²·J_k(x,kr−2) ≤ J_k(x,kr)` is linear-in-`J_k`, hence circular
(`J_k ≤ 4S₂ ≤ 4k⁴J_k` is vacuous). Only the strictly-sublinear fractional power
self-improves. -/

/-- The pair-collapse box: tuples in `(0,x]^b` whose designated coordinates
`e a`, `e b` coincide. -/
noncomputable def pairEqBox {k b : ℕ} (x : ℕ) (e : Fin k → Fin b) (ab : Fin k × Fin k) :
    Finset (Fin b → ℤ) :=
  (solBox b x).filter (fun m => m (e ab.1) = m (e ab.2))

/-- **R2-3 (partial) — the degenerate decomposition.**  `S₂ = Ncount(D₂) ≤
#offPairs · ∑_{a<b} Ncount(D_{a=b})`: the degenerate box splits as the union over
pairs of the pair-collapse boxes, and the landed `Ncount_union_le` closes it. -/
theorem degenBox_Ncount_le {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r)) :
    Ncount k (k * r) 0 (degenBox x e) (degenBox x e)
      ≤ (offPairs k).card * ∑ ab ∈ offPairs k,
          Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) := by
  classical
  have hbeq : degenBox x e = (offPairs k).biUnion (fun ab => pairEqBox x e ab) := by
    ext m
    constructor
    · intro hm
      rw [degenBox, Finset.mem_filter] at hm
      obtain ⟨hmD, hnd⟩ := hm
      have hnd' : ∃ i j : Fin k, i ≠ j ∧ m (e i) = m (e j) := by
        by_contra hc
        exact hnd (fun i j hij heq => hc ⟨i, j, hij, heq⟩)
      obtain ⟨i, j, hij, heq⟩ := hnd'
      rw [Finset.mem_biUnion]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact ⟨(i, j), by rw [offPairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩,
          by rw [pairEqBox, Finset.mem_filter]; exact ⟨hmD, heq⟩⟩
      · exact ⟨(j, i), by rw [offPairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩,
          by rw [pairEqBox, Finset.mem_filter]; exact ⟨hmD, heq.symm⟩⟩
    · intro hm
      rw [Finset.mem_biUnion] at hm
      obtain ⟨ab, hab, hmab⟩ := hm
      rw [offPairs, Finset.mem_filter] at hab
      rw [pairEqBox, Finset.mem_filter] at hmab
      rw [degenBox, Finset.mem_filter]
      refine ⟨hmab.1, ?_⟩
      intro hcon
      exact (hcon ab.1 ab.2 (ne_of_lt hab.2)) hmab.2
  rw [hbeq]
  exact Ncount_union_le k (k * r) (offPairs k) (fun ab => pairEqBox x e ab)

end Salt.Vmvt
