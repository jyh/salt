/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Transversal
import Salt.Vmvt.Linnik

/-!
# VMVT node R3 — the transversal count factorization (residue/quotient split)

This file ports the **p-adic reduction** of Vaughan PSU Chapter 24, Theorem 24.5
(the transversal case), following the fresh house design
(`docs/exploration/s3-a3-design.md`, "VMVT-R3 DESIGN").  The whole-tuple
`Ncount`/`sig` frame (`Shifted.lean`) has no block decomposition, so we do not
decompose the *frame* — we decompose the **counting map** on the designated
block.

## The three rungs

* **R3-a — the graded-congruence bridge (`residue_distinctModP`,
  `residue_mem_LinnikSol`).**  For a designated `k`-tuple `m : Fin k → ℤ` with
  entries pairwise distinct modulo `p`, the residue tuple `ρ_q = m_q mod p^k`
  (`ZMod (p^k)`) is `DistinctModP`, and — whenever `m`'s graded power sums match
  a target `h` modulo `p^j` — lies in `LinnikSol p k h`.  This is the
  design's "the graded power-sum system at precision `p^j` depends only on `ρ`"
  (the `μ`-contributions carry `p^k ≥ p^j`, but here we bridge the *integer*
  power sums to the `ZMod (p^k)` power sums directly, and the graded congruence
  is exactly `LinnikSol`'s defining condition).

* **R3-b — the fibre bound (`desigFibre_card_le`).**  For a fixed target `h`,
  the number of designated `k`-tuples in `(0,x]^k`, pairwise distinct modulo
  `p`, whose graded power sums match `h`, is at most
  `k!·p^{k(k−1)/2}·(x/p^k + 1)^k`: the residue tuple `ρ` lands in `LinnikSol`
  (`≤ k!·p^{k(k−1)/2}` by the landed `linnik_lemma`), and each residue class
  lifts to at most `x/p^k + 1` values in `(0,x]` (the `μ`-quotient box).  The
  map `m ↦ (ρ, μ)` (residue, quotient) is injective with `m_q` recovered as
  `ρ_q.val + p^k·μ_q`.

## The R3-c residual (flagged, `docs/blueprints/flags.md`)

The full assembly `Ncount(transBox p) ≤ ...·Jk(·, k(r−1))` is **not** landed
here: the source's transversal count `I(p) = Σ_h R₄(h,p)²` reaches the
`p^{k(k−1)/2}`-savings-and-`x/p`-scale-drop form only through a
**Hölder-over-residues** step (PSU 24.5, `I(p) ≤ p^{2rk−2k}·max_a I₁(p,a)`),
which restricts the rest-block coordinates to a single residue class `a mod p`;
*only then* does the designated congruence `(m_i−a)^j ≡ (n_i−a)^j (mod p^j)`
emerge (from the rest becoming `p·u` after the `−a` translation, so its
`j`-th powers carry `p^j`).  The combinatorial `Ncount` frame has no such
residue-class power-mean on counts (it would need `Finset.inner_le_Lp_mul_Lq`
on a residue-class partition, plus the block projection
`Fin (kr) ≃ Fin k ⊕ Fin (k(r−1))`), so R3-c is a design/Fable-tier residual.
The stones R3-a/R3-b — the graded bridge and the fibre count — are the reusable
heart and are landed here in full.
-/

namespace Salt.Vmvt

open Finset

/-! ## R3-a — the graded-congruence bridge (residue map into `LinnikSol`) -/

/-- **R3-a (distinctness descent).**  If the integer entries `m_q` are pairwise
distinct modulo `p`, then their residue tuple `ρ_q = m_q mod p^k` (as elements
of `ZMod (p^k)`) is `DistinctModP` (pairwise distinct modulo `p` in the `val`
encoding). -/
theorem residue_distinctModP {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k)
    (m : Fin k → ℤ) (hdist : ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (m i - m j)) :
    DistinctModP (fun q => ((m q : ℤ) : ZMod (p ^ k))) := by
  intro i j hval
  by_contra hne
  apply hdist i j hne
  -- rewrite `((ρ q).val : ZMod p)` back to `((m q : ℤ) : ZMod p)` via `castHom`
  have key : ∀ q : Fin k,
      (((((m q : ℤ) : ZMod (p ^ k))).val : ℕ) : ZMod p) = ((m q : ℤ) : ZMod p) := by
    intro q
    rw [← castHom_eq_val_cast hk ((m q : ℤ) : ZMod (p ^ k)), map_intCast]
  simp only [key] at hval
  -- `((m i : ℤ) : ZMod p) = ((m j : ℤ) : ZMod p)` ⟹ `p ∣ (m i − m j)`
  have hz : (((m i - m j : ℤ)) : ZMod p) = 0 := by push_cast; rw [hval]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (m i - m j) p).mp hz

/-- **R3-a (the bridge).**  If moreover the graded power sums of `m` match a
target `h` modulo `p^{j+1}` for every `j : Fin k`, then the residue tuple lies
in the Linnik solution set `LinnikSol p k h`.  (The graded congruence is exactly
`LinnikSol`'s defining condition; `residue_distinctModP` supplies distinctness.) -/
theorem residue_mem_LinnikSol {p k : ℕ} [NeZero (p ^ k)] (hk : 0 < k)
    (m : Fin k → ℤ) (hdist : ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (m i - m j))
    (h : Fin k → ZMod (p ^ k))
    (hcong : ∀ j : Fin k,
      ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1)))
          (∑ q, ((m q : ℤ) : ZMod (p ^ k)) ^ ((j : ℕ) + 1))
        = ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j)) :
    (fun q => ((m q : ℤ) : ZMod (p ^ k))) ∈ LinnikSol p k h := by
  rw [mem_LinnikSol]
  exact ⟨residue_distinctModP hk m hdist, hcong⟩

/-! ## R3-b — the fibre bound (Linnik × lifts) -/

/-- The **designated fibre** at target `h`: designated `k`-tuples in `(0,x]^k`,
pairwise distinct modulo `p`, whose graded power sums match `h` modulo
`p^{j+1}`.  This is the object of R3-b's count (the `ρ`-constrained,
`μ`-free block of a single transversal tuple). -/
noncomputable def desigFibre (p k x : ℕ) [NeZero (p ^ k)] (h : Fin k → ZMod (p ^ k)) :
    Finset (Fin k → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin k => Finset.Ioc (0 : ℤ) (x : ℤ)).filter
    (fun m => (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (m i - m j)) ∧
      ∀ j : Fin k, ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1)))
          (∑ q, ((m q : ℤ) : ZMod (p ^ k)) ^ ((j : ℕ) + 1))
        = ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j))

theorem mem_desigFibre {p k x : ℕ} [NeZero (p ^ k)] {h : Fin k → ZMod (p ^ k)}
    {m : Fin k → ℤ} :
    m ∈ desigFibre p k x h ↔
      (∀ q, m q ∈ Finset.Ioc (0 : ℤ) (x : ℤ)) ∧
      (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (m i - m j)) ∧
      ∀ j : Fin k, ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1)))
          (∑ q, ((m q : ℤ) : ZMod (p ^ k)) ^ ((j : ℕ) + 1))
        = ZMod.castHom (pow_dvd_pow p j.2) (ZMod (p ^ ((j : ℕ) + 1))) (h j) := by
  classical
  unfold desigFibre
  rw [Finset.mem_filter, Fintype.mem_piFinset]

/-- **R3-b — the fibre bound.**  For a prime `p > k`, `k ≥ 1`, and any target
`h`, the designated fibre has at most `k!·p^{k(k−1)/2}·(x/p^k + 1)^k` elements:
`linnik_lemma` bounds the residue tuples `ρ`, and each residue class lifts to at
most `x/p^k + 1` values of the quotient `μ` in `(0,x]`. -/
theorem desigFibre_card_le {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hpk : k < p)
    (hk : 0 < k) (x : ℕ) (h : Fin k → ZMod (p ^ k)) :
    (desigFibre p k x h).card
      ≤ k.factorial * p ^ (k * (k - 1) / 2) * (x / p ^ k + 1) ^ k := by
  classical
  set μbox : Finset (Fin k → ℕ) :=
    Fintype.piFinset fun _ : Fin k => Finset.Icc 0 (x / p ^ k) with hμboxdef
  -- the injection into `LinnikSol ×ˢ μbox`
  have hcard : (desigFibre p k x h).card ≤ (LinnikSol p k h ×ˢ μbox).card := by
    apply Finset.card_le_card_of_injOn
      (f := fun m => (fun q => ((m q : ℤ) : ZMod (p ^ k)), fun q => (m q).toNat / p ^ k))
    · -- MapsTo
      intro m hm
      rw [Finset.mem_coe, mem_desigFibre] at hm
      obtain ⟨hbox, hdist, hcong⟩ := hm
      rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨residue_mem_LinnikSol hk m hdist h hcong, ?_⟩
      rw [hμboxdef, Fintype.mem_piFinset]
      intro q
      rw [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      apply Nat.div_le_div_right
      have hq := hbox q
      rw [Finset.mem_Ioc] at hq
      exact (Int.toNat_le).mpr hq.2
    · -- InjOn
      intro m hm m' hm' hφe
      rw [Finset.mem_coe, mem_desigFibre] at hm hm'
      obtain ⟨hbox, _, _⟩ := hm
      obtain ⟨hbox', _, _⟩ := hm'
      funext q
      have hpos : 0 < m q := (Finset.mem_Ioc.mp (hbox q)).1
      have hpos' : 0 < m' q := (Finset.mem_Ioc.mp (hbox' q)).1
      have h1 : ((m q : ℤ) : ZMod (p ^ k)) = ((m' q : ℤ) : ZMod (p ^ k)) :=
        congrFun (congrArg Prod.fst hφe) q
      have h2 : (m q).toNat / p ^ k = (m' q).toNat / p ^ k :=
        congrFun (congrArg Prod.snd hφe) q
      -- residues equal ⟹ `.toNat % p^k` equal
      have hcast : ∀ (a : ℤ), 0 ≤ a → ((a : ZMod (p ^ k))) = ((a.toNat : ℕ) : ZMod (p ^ k)) := by
        intro a ha
        conv_lhs => rw [← Int.toNat_of_nonneg ha]
        rw [Int.cast_natCast]
      rw [hcast _ hpos.le, hcast _ hpos'.le] at h1
      have hmod : (m q).toNat % p ^ k = (m' q).toNat % p ^ k := by
        have := congrArg ZMod.val h1
        rwa [ZMod.val_natCast, ZMod.val_natCast] at this
      -- reconstruct `.toNat` via `mod + p^k * div`
      have hrec : (m q).toNat = (m' q).toNat := by
        have e1 := Nat.mod_add_div (m q).toNat (p ^ k)
        have e2 := Nat.mod_add_div (m' q).toNat (p ^ k)
        rw [hmod, h2] at e1
        omega
      -- both nonneg ⟹ equal as integers
      have : ((m q).toNat : ℤ) = ((m' q).toNat : ℤ) := by rw [hrec]
      rwa [Int.toNat_of_nonneg hpos.le, Int.toNat_of_nonneg hpos'.le] at this
  -- card of the product target
  have hμcard : μbox.card = (x / p ^ k + 1) ^ k := by
    rw [hμboxdef, Fintype.card_piFinset]
    simp [Nat.card_Icc, Finset.prod_const, Finset.card_univ]
  calc (desigFibre p k x h).card
      ≤ (LinnikSol p k h ×ˢ μbox).card := hcard
    _ = (LinnikSol p k h).card * μbox.card := Finset.card_product _ _
    _ ≤ k.factorial * p ^ (k * (k - 1) / 2) * (x / p ^ k + 1) ^ k := by
        rw [hμcard]
        gcongr
        exact linnik_lemma p k hp hpk h

end Salt.Vmvt
