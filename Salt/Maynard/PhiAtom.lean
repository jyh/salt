/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.M3Expansion
import Salt.Brun.CongruenceCounting

/-!
# N3.1 probe — the `μ²/φ` atom (Maynard track)

For `B ≠ 0` let `phiAtomSum x B = ∑_{r < x, r squarefree, (r,B)=1} 1/φ(r)`.
This file proves:

* `phiAtom_lower` — the exact-leading-constant lower bound
  `(φ(B)/B)·log x − C_B ≤ phiAtomSum x B`;
* `phiAtom_upper_lossy` — an upper bound with a `4×`-lossy leading constant
  `phiAtomSum x B ≤ 4·(φ(B)/B)·log x + C_B`;
* `phiAtom_upper_fallback` — the crude form `phiAtomSum x B ≤ C_B·(1 + log x)`.

Route (lower): group `n < x` coprime to `B` by radical `r = rad n`; each fiber's
harmonic mass is at most `1/φ(r)` (geometric expansion per prime, mirroring
`Salt.Brun.M3Expansion.radical_fiber_bound`), so `phiAtomSum` dominates the
coprime harmonic sum, which is bounded below by block counting (`φ(B)` coprime
residues per length-`B` block, via `Salt.Brun.CongruenceCounting.block_count`)
plus `harmonic q ≥ log (q+1)`.

Route (upper): the finite identity `r/φ(r) = ∑_{d ∣ r} μ²(d)/φ(d)` (squarefree
`r`; proved via the powerset expansion `∏(1 + 1/(p−1))`) turns `1/φ(r)` into
`∑_{de = r} 1/(d·e·φ(d))`; summing over `r` and relaxing the pair set to a
product gives `phiAtomSum x B ≤ (∑_{d<x sqfree} 1/(dφ(d)))·(coprime harmonic)`.
The first factor is `≤ 1 + 2√2 ≤ 4` since `d ≤ 2φ(d)²` for squarefree `d`
(telescoping `∑ 1/(d√d) ≤ 2`), the second is `≤ (φ(B)/B)log x + C_B` by block
counting. The exact-constant upper bound would need the tail cancellation
`∑_d h(d)/d = 1` for `h = (μ²·id/φ) * μ`; see the PORT-BLOCKER note at the end.
-/

open Finset
open Salt.M3Expansion (rad rad_squarefree rad_eq_primeFactors)

namespace Salt.Maynard

/-- Squarefree integers below `x` that are coprime to `B`. -/
def sqfCop (x B : ℕ) : Finset ℕ :=
  (Finset.range x).filter (fun r => Squarefree r ∧ Nat.Coprime r B)

/-- The `μ²/φ` atom: `∑_{r < x, squarefree, coprime to B} 1/φ(r)`. -/
noncomputable def phiAtomSum (x B : ℕ) : ℝ :=
  ∑ r ∈ sqfCop x B, (1 : ℝ) / (Nat.totient r)

/-- The coprime harmonic sum `∑_{n < x, (n,B)=1} 1/n` (the `n = 0` term is `0`). -/
noncomputable def copHarmonic (x B : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range x).filter (fun n => Nat.Coprime n B), (1 : ℝ) / n

/-! ## Totient on squarefree numbers -/

/-- For squarefree `r`, `φ(r) = ∏_{p ∣ r} (p - 1)`. -/
lemma totient_squarefree {r : ℕ} (hr : Squarefree r) :
    Nat.totient r = ∏ p ∈ r.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors r
  rw [Nat.prod_primeFactors_of_squarefree hr, mul_comm r] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr.ne_zero) h

/-- Real-cast version of `totient_squarefree`. -/
lemma totient_squarefree_cast {r : ℕ} (hr : Squarefree r) :
    (Nat.totient r : ℝ) = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
  rw [totient_squarefree hr, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have h1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  push_cast [Nat.cast_sub h1]
  ring

/-! ## The per-prime geometric bound and the radical-fiber bound (lower route)

These mirror `Salt.Brun.M3Expansion.geom_bound` / `radical_fiber_bound` with
`ν*(m) = 2^Ω(m)/m` replaced by `1/m` and the Selberg term `g` by `1/φ`. -/

/-- `∑_{j=1}^{K} p^{-j} ≤ 1/(p-1)` for a prime `p`. -/
lemma geom_inv_bound {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, ((p : ℝ))⁻¹ ^ j ≤ ((p : ℝ) - 1)⁻¹ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set r : ℝ := ((p : ℝ))⁻¹ with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, inv_lt_one_iff₀]; right; linarith
  have hshift : ∀ N : ℕ, ∑ j ∈ Finset.Icc 1 N, r ^ j = r * ∑ j ∈ Finset.range N, r ^ j := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]; ring
  rw [hshift K]
  have hgeo : ∑ j ∈ Finset.range K, r ^ j ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => by positivity)
  calc r * ∑ j ∈ Finset.range K, r ^ j
      ≤ r * (1 - r)⁻¹ := by exact mul_le_mul_of_nonneg_left hgeo hr0
    _ = ((p : ℝ) - 1)⁻¹ := by
        rw [hr]
        have hpne : (p : ℝ) ≠ 0 := by linarith
        have h1 : (0 : ℝ) < 1 - ((p : ℝ))⁻¹ := by
          rw [sub_pos, inv_lt_one_iff₀]; right; linarith
        rw [← mul_inv]
        congr 1
        rw [mul_sub, mul_inv_cancel₀ hpne, mul_one]

/-- `1/m` as a product over the prime factorization. -/
lemma inv_eq_prod_primeFactors {m : ℕ} (hm : m ≠ 0) :
    ((m : ℝ))⁻¹ = ∏ p ∈ m.primeFactors, ((p : ℝ))⁻¹ ^ (m.factorization p) := by
  have hprodnat : ∏ p ∈ m.primeFactors, p ^ (m.factorization p) = m := by
    have h := Nat.prod_factorization_pow_eq_self hm
    rwa [Finsupp.prod, Nat.support_factorization] at h
  have hden : ∏ p ∈ m.primeFactors, ((p : ℝ)) ^ (m.factorization p) = (m : ℝ) := by
    have hcast : ((∏ p ∈ m.primeFactors, p ^ (m.factorization p) : ℕ) : ℝ) = (m : ℝ) := by
      rw [hprodnat]
    rw [Nat.cast_prod] at hcast
    simp only [Nat.cast_pow] at hcast
    exact hcast
  rw [← hden, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [inv_pow]

/-- The radical fiber bound for the harmonic weight: any set of nonzero `n < x`
with `rad n = r` (squarefree `r`) has harmonic mass at most `1/φ(r)`. -/
lemma fiber_sum_le_inv_totient {x r : ℕ} (hr : Squarefree r) (F : Finset ℕ)
    (hF : ∀ n ∈ F, n ≠ 0 ∧ n < x ∧ rad n = r) :
    ∑ n ∈ F, ((n : ℝ))⁻¹ ≤ ((Nat.totient r : ℝ))⁻¹ := by
  classical
  -- the exponent function attached to each fiber element
  let φe : ℕ → (∀ p ∈ r.primeFactors, ℕ) := fun m p _ => m.factorization p
  have hval : ∀ n ∈ F, ((n : ℝ))⁻¹
      = ∏ q ∈ r.primeFactors.attach, (((q : ℕ) : ℝ))⁻¹ ^ (n.factorization (q : ℕ)) := by
    intro n hn
    obtain ⟨hn0, _, hnrad⟩ := hF n hn
    have hpf : n.primeFactors = r.primeFactors := rad_eq_primeFactors hnrad
    rw [inv_eq_prod_primeFactors hn0, hpf, ← Finset.prod_attach]
  have hinj : Set.InjOn φe ↑F := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    obtain ⟨ha0, _, harad⟩ := hF a ha
    obtain ⟨hb0, _, hbrad⟩ := hF b hb
    apply Nat.eq_of_factorization_eq ha0 hb0
    intro q
    by_cases hq : q ∈ r.primeFactors
    · exact congrFun (congrFun hab q) hq
    · have hqa : a.factorization q = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization, rad_eq_primeFactors harad]
        exact hq
      have hqb : b.factorization q = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization, rad_eq_primeFactors hbrad]
        exact hq
      rw [hqa, hqb]
  have hsub : F.image φe ⊆ r.primeFactors.pi (fun _ => Finset.Icc 1 x) := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨n, hnF, rfl⟩ := he
    obtain ⟨hn0, hnx, hnrad⟩ := hF n hnF
    have hpf : n.primeFactors = r.primeFactors := rad_eq_primeFactors hnrad
    rw [Finset.mem_pi]
    intro p hp
    change n.factorization p ∈ Finset.Icc 1 x
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have hpn : p ∈ n.primeFactors := by rw [hpf]; exact hp
      exact (Nat.prime_of_mem_primeFactors hpn).factorization_pos_of_dvd hn0
        (Nat.dvd_of_mem_primeFactors hpn)
    · have hlt : n.factorization p < n := Nat.factorization_lt p hn0
      omega
  calc ∑ n ∈ F, ((n : ℝ))⁻¹
      = ∑ e ∈ F.image φe,
          ∏ q ∈ r.primeFactors.attach, (((q : ℕ) : ℝ))⁻¹ ^ (e (q : ℕ) q.2) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl (fun n hn => hval n hn)
    _ ≤ ∑ e ∈ r.primeFactors.pi (fun _ => Finset.Icc 1 x),
          ∏ q ∈ r.primeFactors.attach, (((q : ℕ) : ℝ))⁻¹ ^ (e (q : ℕ) q.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro e _ _
        exact Finset.prod_nonneg (fun q _ => by positivity)
    _ = ∏ p ∈ r.primeFactors, ∑ j ∈ Finset.Icc 1 x, ((p : ℝ))⁻¹ ^ j :=
        (Finset.prod_sum r.primeFactors (fun _ => Finset.Icc 1 x)
          (fun p j => ((p : ℝ))⁻¹ ^ j)).symm
    _ ≤ ∏ p ∈ r.primeFactors, ((p : ℝ) - 1)⁻¹ := by
        apply Finset.prod_le_prod
        · intro p _
          exact Finset.sum_nonneg (fun j _ => by positivity)
        · intro p hp
          exact geom_inv_bound (Nat.prime_of_mem_primeFactors hp) x
    _ = ((Nat.totient r : ℝ))⁻¹ := by
        rw [totient_squarefree_cast hr, ← Finset.prod_inv_distrib]

/-! ## The lower bound, step 1: `copHarmonic ≤ phiAtomSum` -/

/-- Dropping the `n = 0` term (which is `0`) from the coprime harmonic sum. -/
lemma copHarmonic_eq (x B : ℕ) :
    copHarmonic x B
      = ∑ n ∈ (Finset.range x).filter (fun n => n ≠ 0 ∧ Nat.Coprime n B), ((n : ℝ))⁻¹ := by
  unfold copHarmonic
  simp_rw [one_div]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.2⟩
  · intro n hn hn'
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_filter, not_and] at hn'
    have : n = 0 := by
      by_contra h0
      exact absurd ⟨h0, hn.2⟩ (hn' hn.1)
    simp [this]

/-- Grouping by radicals: the coprime harmonic sum is dominated by the atom. -/
lemma copHarmonic_le_phiAtomSum (x B : ℕ) : copHarmonic x B ≤ phiAtomSum x B := by
  classical
  rw [copHarmonic_eq]
  set dom := (Finset.range x).filter (fun n => n ≠ 0 ∧ Nat.Coprime n B) with hdom
  have hmaps : ∀ n ∈ dom, rad n ∈ sqfCop x B := by
    intro n hn
    rw [hdom, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hn0, hncop⟩ := hn
    have hdvd : rad n ∣ n := Nat.prod_primeFactors_dvd n
    rw [sqfCop, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, rad_squarefree n, Nat.Coprime.coprime_dvd_left hdvd hncop⟩
    calc rad n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
      _ < x := hnx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => ((n : ℝ))⁻¹)]
  unfold phiAtomSum
  simp_rw [one_div]
  apply Finset.sum_le_sum
  intro r hr
  rw [sqfCop, Finset.mem_filter] at hr
  refine fiber_sum_le_inv_totient (x := x) hr.2.1 _ (fun n hn => ?_)
  rw [Finset.mem_filter, hdom, Finset.mem_filter, Finset.mem_range] at hn
  exact ⟨hn.1.2.1, hn.1.1, hn.2⟩

/-! ## Block counting for the coprime harmonic sum -/

/-- The coprime residues mod `B`. -/
def copRes (B : ℕ) : Finset ℕ := (Finset.range B).filter (fun a => Nat.Coprime a B)

lemma coprime_mod_iff {n B : ℕ} : Nat.Coprime (n % B) B ↔ Nat.Coprime n B := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

lemma copRes_card (B : ℕ) : (copRes B).card = Nat.totient B := by
  rw [Nat.totient_eq_card_coprime]
  unfold copRes
  congr 1
  apply Finset.filter_congr
  intro a _
  rw [Nat.coprime_comm]

/-- Each length-`B` block `[jB+1, (j+1)B]` contains exactly `φ(B)` integers
coprime to `B`. -/
lemma block_coprime_card (B : ℕ) (hB : 0 < B) (j : ℕ) :
    ((Finset.Ico (j * B + 1) (j * B + 1 + B)).filter (fun n => Nat.Coprime n B)).card
      = Nat.totient B := by
  have h := block_count B (copRes B) hB (j * B)
  have hfilter : (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter (fun n => n % B ∈ copRes B)
      = (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter (fun n => Nat.Coprime n B) := by
    apply Finset.filter_congr
    intro n _
    simp only [copRes, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hc⟩; exact coprime_mod_iff.mp hc
    · intro hc; exact ⟨Nat.mod_lt _ hB, coprime_mod_iff.mpr hc⟩
  have hinter : copRes B ∩ Finset.range B = copRes B :=
    Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
  rw [hfilter, hinter, copRes_card] at h
  exact h

/-- Lower bound for one block's harmonic mass: `≥ φ(B)/((j+1)B)`. -/
lemma block_sum_lower (B : ℕ) (hB : 0 < B) (j : ℕ) :
    (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B) ≤
      ∑ n ∈ (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter (fun n => Nat.Coprime n B),
        (1 : ℝ) / n := by
  have hpos : (0 : ℝ) < ((j : ℝ) + 1) * B := by positivity
  have hle : ∀ n ∈ (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter
      (fun n => Nat.Coprime n B), (1 : ℝ) / (((j : ℝ) + 1) * B) ≤ (1 : ℝ) / n := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    have h1 : 0 < n := by omega
    have h2 : n ≤ (j + 1) * B := by
      have : (j + 1) * B = j * B + B := by ring
      omega
    apply one_div_le_one_div_of_le
    · exact_mod_cast h1
    · exact_mod_cast h2
  have := Finset.card_nsmul_le_sum _ _ _ hle
  rw [block_coprime_card B hB j, nsmul_eq_mul] at this
  calc (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B)
      = (Nat.totient B : ℝ) * ((1 : ℝ) / (((j : ℝ) + 1) * B)) := by ring
    _ ≤ _ := this

/-- Upper bound for one block's harmonic mass, `j ≥ 1` version: `≤ φ(B)/(jB)`. -/
lemma block_sum_upper (B : ℕ) (hB : 0 < B) (j : ℕ) (hj : 1 ≤ j) :
    ∑ n ∈ (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter (fun n => Nat.Coprime n B),
        (1 : ℝ) / n ≤ (Nat.totient B : ℝ) / ((j : ℝ) * B) := by
  have hpos : (0 : ℝ) < (j : ℝ) * B := by
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    positivity
  have hle : ∀ n ∈ (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter
      (fun n => Nat.Coprime n B), (1 : ℝ) / n ≤ (1 : ℝ) / ((j : ℝ) * B) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    have h1 : j * B < n := by omega
    apply one_div_le_one_div_of_le hpos
    exact_mod_cast h1.le
  have := Finset.sum_le_card_nsmul _ _ _ hle
  rw [block_coprime_card B hB j, nsmul_eq_mul] at this
  calc ∑ n ∈ (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter (fun n => Nat.Coprime n B),
        (1 : ℝ) / n ≤ (Nat.totient B : ℝ) * ((1 : ℝ) / ((j : ℝ) * B)) := this
    _ = (Nat.totient B : ℝ) / ((j : ℝ) * B) := by ring

/-- Upper bound for block `0`: `≤ φ(B)`. -/
lemma block_sum_upper_zero (B : ℕ) (hB : 0 < B) :
    ∑ n ∈ (Finset.Ico (0 * B + 1) (0 * B + 1 + B)).filter (fun n => Nat.Coprime n B),
        (1 : ℝ) / n ≤ (Nat.totient B : ℝ) := by
  have hle : ∀ n ∈ (Finset.Ico (0 * B + 1) (0 * B + 1 + B)).filter
      (fun n => Nat.Coprime n B), (1 : ℝ) / n ≤ 1 := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    have h1 : 1 ≤ n := by omega
    have h1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    rw [div_le_one (by linarith)]
    exact h1R
  have := Finset.sum_le_card_nsmul _ _ _ hle
  rw [block_coprime_card B hB 0, nsmul_eq_mul, mul_one] at this
  exact this

/-- Decomposition of `[1, qB]` into `q` length-`B` blocks. -/
lemma sum_Icc_mul_eq_sum_blocks (B : ℕ) (f : ℕ → ℝ) (q : ℕ) :
    ∑ n ∈ (Finset.Icc 1 (q * B)).filter (fun n => Nat.Coprime n B), f n
      = ∑ j ∈ Finset.range q,
          ∑ n ∈ (Finset.Ico (j * B + 1) (j * B + 1 + B)).filter (fun n => Nat.Coprime n B),
            f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hmul : (q + 1) * B = q * B + B := by ring
    have hsplit : Finset.Icc 1 ((q + 1) * B)
        = Finset.Icc 1 (q * B) ∪ Finset.Ico (q * B + 1) (q * B + 1 + B) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico, hmul]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (q * B)) (Finset.Ico (q * B + 1) (q * B + 1 + B)) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_Ico] at hn'
      omega
    rw [hsplit, Finset.filter_union,
      Finset.sum_union (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ih, Finset.sum_range_succ]

/-- The real-cast harmonic number as a `range` sum. -/
lemma harmonic_real (q : ℕ) :
    ((harmonic q : ℚ) : ℝ) = ∑ j ∈ Finset.range q, ((j : ℝ) + 1)⁻¹ := by
  unfold harmonic
  push_cast
  rfl

/-- The sum of the per-block main terms is `(φ(B)/B) · harmonic q`. -/
lemma sum_block_main (B : ℕ) (q : ℕ) :
    ∑ j ∈ Finset.range q, (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B)
      = (Nat.totient B / B : ℝ) * ((harmonic q : ℚ) : ℝ) := by
  rw [harmonic_real, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## The lower bound, step 2: block counting -/

/-- `∑_{n < x, (n,B)=1} 1/n ≥ (φ(B)/B)(log x − log B)`. -/
lemma copHarmonic_lower (B : ℕ) (hB : B ≠ 0) (x : ℕ) (hx : 2 ≤ x) :
    (Nat.totient B / B : ℝ) * Real.log x - (Nat.totient B / B : ℝ) * Real.log B
      ≤ copHarmonic x B := by
  have hB0 : 0 < B := Nat.pos_of_ne_zero hB
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB0
  set q := (x - 1) / B with hq
  -- `x ≤ (q+1) B`
  have hxq : x ≤ (q + 1) * B := by
    have h1 : B * q + (x - 1) % B = x - 1 := Nat.div_add_mod (x - 1) B
    have h2 : (x - 1) % B < B := Nat.mod_lt _ hB0
    have h3 : (q + 1) * B = B * q + B := by ring
    omega
  -- step A: the block sum is inside `copHarmonic`
  have hA : ∑ n ∈ (Finset.Icc 1 (q * B)).filter (fun n => Nat.Coprime n B), (1 : ℝ) / n
      ≤ copHarmonic x B := by
    unfold copHarmonic
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_filter, Finset.mem_range]
      have hqx : q * B ≤ x - 1 := Nat.div_mul_le_self (x - 1) B
      exact ⟨by omega, hn.2⟩
    · intro n _ _
      positivity
  -- step B: blocks + per-block lower bound
  have hB1 : ∑ j ∈ Finset.range q, (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B)
      ≤ ∑ n ∈ (Finset.Icc 1 (q * B)).filter (fun n => Nat.Coprime n B), (1 : ℝ) / n := by
    rw [sum_Icc_mul_eq_sum_blocks]
    exact Finset.sum_le_sum (fun j _ => block_sum_lower B hB0 j)
  -- step C: the block lower sum is `(φB/B) · harmonic q`
  have hC : ∑ j ∈ Finset.range q, (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B)
      = (Nat.totient B / B : ℝ) * ((harmonic q : ℚ) : ℝ) := sum_block_main B q
  -- step D: `harmonic q ≥ log (q+1) ≥ log x − log B`
  have hD : Real.log x - Real.log B ≤ ((harmonic q : ℚ) : ℝ) := by
    have h1 : Real.log ((q : ℝ) + 1) ≤ ((harmonic q : ℚ) : ℝ) := by
      have h := log_add_one_le_harmonic q
      push_cast at h
      exact h
    have h2 : Real.log x - Real.log B ≤ Real.log ((q : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) (ne_of_gt hBR)]
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hBR]
      have : (x : ℝ) ≤ ((q + 1) * B : ℕ) := by exact_mod_cast hxq
      push_cast at this
      linarith
    linarith
  -- assemble
  have hnn : (0 : ℝ) ≤ (Nat.totient B / B : ℝ) := by positivity
  calc (Nat.totient B / B : ℝ) * Real.log x - (Nat.totient B / B : ℝ) * Real.log B
      = (Nat.totient B / B : ℝ) * (Real.log x - Real.log B) := by ring
    _ ≤ (Nat.totient B / B : ℝ) * ((harmonic q : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hD hnn
    _ = ∑ j ∈ Finset.range q, (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B) := hC.symm
    _ ≤ ∑ n ∈ (Finset.Icc 1 (q * B)).filter (fun n => Nat.Coprime n B), (1 : ℝ) / n := hB1
    _ ≤ copHarmonic x B := hA

/-- **N3.1 lower bound** (exact leading constant): for `B ≠ 0` there is `C` with
`(φ(B)/B)·log x − C ≤ ∑_{r < x, squarefree, (r,B)=1} 1/φ(r)` for all `x ≥ 2`. -/
theorem phiAtom_lower (B : ℕ) (hB : B ≠ 0) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      (Nat.totient B / B : ℝ) * Real.log x - C ≤ phiAtomSum x B := by
  refine ⟨(Nat.totient B / B : ℝ) * Real.log B, fun x hx => ?_⟩
  calc (Nat.totient B / B : ℝ) * Real.log x - (Nat.totient B / B : ℝ) * Real.log B
      ≤ copHarmonic x B := copHarmonic_lower B hB x hx
    _ ≤ phiAtomSum x B := copHarmonic_le_phiAtomSum x B

/-! ## The upper bound

Finite identity: for squarefree `r`, `r/φ(r) = ∑_{d ∣ r} 1/φ(d)` (the divisors
of a squarefree number are the subset products of its prime factors, and
`∏_{p∣r} (1 + 1/(p-1)) = ∏_{p∣r} p/(p-1)`).  Only the `≥` direction is needed. -/

/-- For squarefree `r`: `r/φ(r) ≤ ∑_{d ∣ r} 1/φ(d)` (in fact equality). -/
lemma sum_divisors_inv_totient_ge {r : ℕ} (hr : Squarefree r) :
    (r : ℝ) / (Nat.totient r) ≤ ∑ d ∈ r.divisors, (1 : ℝ) / (Nat.totient d) := by
  classical
  have hr0 : r ≠ 0 := hr.ne_zero
  have hprime : ∀ p ∈ r.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- the left side as a product over prime factors
  have hcast : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hr]
    rw [Nat.cast_prod]
  have hL : (r : ℝ) / (Nat.totient r) = ∏ p ∈ r.primeFactors, (((p : ℝ) - 1)⁻¹ + 1) := by
    rw [totient_squarefree_cast hr, hcast, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  -- expand the product over subsets of the prime factors
  rw [hL, Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  -- each subset contributes `1/φ` of the corresponding divisor
  have hval : ∀ t ∈ r.primeFactors.powerset,
      ∏ p ∈ t, ((p : ℝ) - 1)⁻¹ = (1 : ℝ) / (Nat.totient (∏ p ∈ t, p)) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have hdvd : (∏ p ∈ t, p) ∣ r := by
      have h := Finset.prod_dvd_prod_of_subset t r.primeFactors (fun p => p) ht
      rwa [Nat.prod_primeFactors_of_squarefree hr] at h
    have hsq : Squarefree (∏ p ∈ t, p) := hr.squarefree_of_dvd hdvd
    have hpf : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod (fun p hp => hprime p (ht hp))
    rw [totient_squarefree_cast hsq, hpf, one_div, ← Finset.prod_inv_distrib]
  rw [Finset.sum_congr rfl hval]
  -- reindex by the (injective) subset-product map and enlarge to all divisors
  have hinj : Set.InjOn (fun t => ∏ p ∈ t, p)
      (r.primeFactors.powerset : Set (Finset ℕ)) := by
    intro t1 h1 t2 h2 h12
    simp only [Finset.mem_coe, Finset.mem_powerset] at h1 h2
    simp only at h12
    have k1 : (∏ p ∈ t1, p).primeFactors = t1 :=
      Nat.primeFactors_prod (fun p hp => hprime p (h1 hp))
    have k2 : (∏ p ∈ t2, p).primeFactors = t2 :=
      Nat.primeFactors_prod (fun p hp => hprime p (h2 hp))
    rw [← k1, ← k2, h12]
  calc ∑ t ∈ r.primeFactors.powerset, (1 : ℝ) / (Nat.totient (∏ p ∈ t, p))
      = ∑ d ∈ r.primeFactors.powerset.image (fun t => ∏ p ∈ t, p),
          (1 : ℝ) / (Nat.totient d) :=
        (Finset.sum_image (f := fun d => (1 : ℝ) / (Nat.totient d)) hinj).symm
    _ ≤ ∑ d ∈ r.divisors, (1 : ℝ) / (Nat.totient d) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_image] at hd
          obtain ⟨t, ht, rfl⟩ := hd
          rw [Finset.mem_powerset] at ht
          rw [Nat.mem_divisors]
          refine ⟨?_, hr0⟩
          have h := Finset.prod_dvd_prod_of_subset t r.primeFactors (fun p => p) ht
          rwa [Nat.prod_primeFactors_of_squarefree hr] at h
        · intro d _ _
          positivity

/-- For squarefree `r`: `1/φ(r) ≤ ∑_{de = r} 1/(d·e·φ(d))`. -/
lemma inv_totient_le_sum_antidiag {r : ℕ} (hr : Squarefree r) :
    (1 : ℝ) / (Nat.totient r) ≤
      ∑ de ∈ r.divisorsAntidiagonal, (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
  -- each pair's term is `(1/r)·(1/φ(d))`
  have hcongr : ∀ de ∈ r.divisorsAntidiagonal,
      (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1) = 1 / r * (1 / Nat.totient de.1) := by
    intro de hde
    rw [Nat.mem_divisorsAntidiagonal] at hde
    have hprod : (de.1 : ℝ) * de.2 = (r : ℝ) := by exact_mod_cast congrArg Nat.cast hde.1
    rw [hprod, div_mul_div_comm, one_mul]
  -- the first-coordinate map is a bijection from the antidiagonal to the divisors
  have hinj : Set.InjOn Prod.fst (r.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    intro p1 h1 p2 h2 h12
    simp only [Finset.mem_coe, Nat.mem_divisorsAntidiagonal] at h1 h2
    have h10 : p1.1 ≠ 0 := by
      rintro h
      rw [h, zero_mul] at h1
      exact h1.2 h1.1.symm
    refine Prod.ext h12 ?_
    have hmul : p1.1 * p1.2 = p1.1 * p2.2 := by
      rw [h1.1, h12, h2.1]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h10) hmul
  have hsum_eq : ∑ d ∈ r.divisors, (1 : ℝ) / (Nat.totient d)
      = ∑ de ∈ r.divisorsAntidiagonal, (1 : ℝ) / (Nat.totient de.1) := by
    rw [← Nat.image_fst_divisorsAntidiagonal,
      Finset.sum_image (f := fun d => (1 : ℝ) / (Nat.totient d)) hinj]
  have hφ : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr0)
  calc (1 : ℝ) / (Nat.totient r) = 1 / r * ((r : ℝ) / (Nat.totient r)) := by
        field_simp
    _ ≤ 1 / r * ∑ d ∈ r.divisors, (1 : ℝ) / (Nat.totient d) :=
        mul_le_mul_of_nonneg_left (sum_divisors_inv_totient_ge hr) (by positivity)
    _ = 1 / r * ∑ de ∈ r.divisorsAntidiagonal, (1 : ℝ) / (Nat.totient de.1) := by
        rw [hsum_eq]
    _ = ∑ de ∈ r.divisorsAntidiagonal, 1 / (r : ℝ) * (1 / Nat.totient de.1) :=
        Finset.mul_sum _ _ _
    _ = ∑ de ∈ r.divisorsAntidiagonal, (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1) :=
        (Finset.sum_congr rfl hcongr).symm

/-- Relaxing the atom to a product of two one-dimensional sums. -/
lemma phiAtomSum_le_mul (x B : ℕ) :
    phiAtomSum x B ≤
      (∑ d ∈ sqfCop x B, (1 : ℝ) / (d * Nat.totient d)) * copHarmonic x B := by
  classical
  have hmem : ∀ r ∈ sqfCop x B, Squarefree r ∧ Nat.Coprime r B ∧ r < x := by
    intro r hr
    rw [sqfCop, Finset.mem_filter, Finset.mem_range] at hr
    exact ⟨hr.2.1, hr.2.2, hr.1⟩
  -- expand each `1/φ(r)` over the divisor antidiagonal
  have h1 : phiAtomSum x B ≤ ∑ r ∈ sqfCop x B, ∑ de ∈ r.divisorsAntidiagonal,
      (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1) :=
    Finset.sum_le_sum (fun r hr => inv_totient_le_sum_antidiag (hmem r hr).1)
  -- the antidiagonals are pairwise disjoint (the pair determines `r`)
  have hdisj : (↑(sqfCop x B) : Set ℕ).PairwiseDisjoint
      (fun r => r.divisorsAntidiagonal) := by
    intro r1 _ r2 _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    rw [Nat.mem_divisorsAntidiagonal] at hp1 hp2
    exact hne (hp1.1.symm.trans hp2.1)
  have h2 : ∑ r ∈ sqfCop x B, ∑ de ∈ r.divisorsAntidiagonal,
        (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1)
      = ∑ de ∈ (sqfCop x B).biUnion (fun r => r.divisorsAntidiagonal),
          (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1) := (Finset.sum_biUnion hdisj).symm
  -- the collected pairs sit inside a product set
  have h3 : (sqfCop x B).biUnion (fun r => r.divisorsAntidiagonal)
      ⊆ (sqfCop x B) ×ˢ ((Finset.range x).filter (fun n => Nat.Coprime n B)) := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    rw [Nat.mem_divisorsAntidiagonal] at hpr
    obtain ⟨hsqr, hcop, hrx⟩ := hmem r hr
    obtain ⟨hprod, hr0⟩ := hpr
    have hd1 : p.1 ∣ r := ⟨p.2, hprod.symm⟩
    have hd2 : p.2 ∣ r := ⟨p.1, by rw [← hprod, mul_comm]⟩
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    rw [Finset.mem_product]
    constructor
    · rw [sqfCop, Finset.mem_filter, Finset.mem_range]
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd hrpos hd1) hrx, hsqr.squarefree_of_dvd hd1,
        Nat.Coprime.coprime_dvd_left hd1 hcop⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd hrpos hd2) hrx,
        Nat.Coprime.coprime_dvd_left hd2 hcop⟩
  have h4 : ∑ de ∈ (sqfCop x B).biUnion (fun r => r.divisorsAntidiagonal),
        (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1)
      ≤ ∑ de ∈ (sqfCop x B) ×ˢ ((Finset.range x).filter (fun n => Nat.Coprime n B)),
          (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h3
    intro de _ _
    positivity
  -- the product sum factorizes
  have h5 : ∑ de ∈ (sqfCop x B) ×ˢ ((Finset.range x).filter (fun n => Nat.Coprime n B)),
        (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1)
      = (∑ d ∈ sqfCop x B, (1 : ℝ) / (d * Nat.totient d)) * copHarmonic x B := by
    rw [Finset.sum_product]
    unfold copHarmonic
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
    rw [div_mul_div_comm, one_mul]
    congr 1
    ring
  calc phiAtomSum x B
      ≤ ∑ r ∈ sqfCop x B, ∑ de ∈ r.divisorsAntidiagonal,
          (1 : ℝ) / (de.1 * de.2 * Nat.totient de.1) := h1
    _ = _ := h2
    _ ≤ _ := h4
    _ = _ := h5

/-! ## Bounding `∑ 1/(d·φ(d))` over squarefree `d` -/

/-- Telescoping: `∑_{d=2}^{N} 1/(d√d) ≤ 2 − 2/√N`. -/
lemma sum_inv_mul_sqrt_aux (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d * Real.sqrt d) ≤ 2 - 2 / Real.sqrt N := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · interval_cases n
      simp [Real.sqrt_one]
    · have ihn := ih h1
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      set a := Real.sqrt n with ha
      set b := Real.sqrt ((n : ℝ) + 1) with hb
      have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
      have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
      have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
      have ha2 : a ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
      have hb2 : b ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
      have key : (1 : ℝ) / (((n : ℝ) + 1) * b) ≤ 2 / a - 2 / b := by
        have hba : (b - a) * (b + a) = 1 := by linear_combination hb2 - ha2
        have hd2 : 2 / a - 2 / b = 2 / (a * b * (b + a)) := by
          rw [div_sub_div _ _ (ne_of_gt ha0) (ne_of_gt hb0)]
          rw [div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (2 * a * b) * hba
        rw [hd2, ← hb2]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) hb0.le) hb0.le,
          mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) ha0.le) hb0.le]
      have htop : (1 : ℝ) / ((((n + 1) : ℕ) : ℝ) * Real.sqrt (((n + 1) : ℕ) : ℝ))
          = (1 : ℝ) / (((n : ℝ) + 1) * b) := by
        rw [hb]
        push_cast
        rfl
      have hsqN : Real.sqrt (((n + 1) : ℕ) : ℝ) = b := by
        rw [hb]
        push_cast
        rfl
      rw [htop, hsqN]
      have hlast : 2 - 2 / a + (1 : ℝ) / (((n : ℝ) + 1) * b) ≤ 2 - 2 / b := by
        linarith [key]
      calc ∑ d ∈ Finset.Icc 2 n, (1 : ℝ) / (d * Real.sqrt d) + 1 / (((n : ℝ) + 1) * b)
          ≤ (2 - 2 / a) + 1 / (((n : ℝ) + 1) * b) := by linarith [ihn]
        _ ≤ 2 - 2 / b := hlast

/-- `∑_{d=2}^{N} 1/(d√d) ≤ 2`. -/
lemma sum_inv_mul_sqrt_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d * Real.sqrt d) ≤ 2 := by
  rcases Nat.lt_or_ge N 1 with h | h
  · interval_cases N
    simp
  · have h1 := sum_inv_mul_sqrt_aux N h
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    have h3 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
    have h4 : 0 < 2 / Real.sqrt N := by positivity
    linarith

/-- For squarefree `d`: `d ≤ 2·φ(d)²` (each odd prime satisfies `p ≤ (p−1)²`;
the prime `2` costs the factor `2`). -/
lemma le_two_mul_totient_sq {d : ℕ} (hd : Squarefree d) :
    d ≤ 2 * Nat.totient d ^ 2 := by
  classical
  have hstep : ∀ p ∈ d.primeFactors, p ≠ 2 → p ≤ (p - 1) ^ 2 := by
    intro p hp hp2
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h3 : 3 ≤ p := by have := hpp.two_le; omega
    have hk : 2 ≤ p - 1 := by omega
    calc p ≤ 2 * (p - 1) := by omega
      _ ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right _ hk
      _ = (p - 1) ^ 2 := (sq (p - 1)).symm
  rw [totient_squarefree hd]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  rw [← Finset.prod_pow]
  by_cases h2 : 2 ∈ d.primeFactors
  · rw [← Finset.mul_prod_erase _ _ h2, ← Finset.mul_prod_erase _ (fun p => (p - 1) ^ 2) h2]
    have h11 : (2 - 1 : ℕ) ^ 2 = 1 := rfl
    rw [h11, one_mul]
    have hprod : ∏ p ∈ d.primeFactors.erase 2, p
        ≤ ∏ p ∈ d.primeFactors.erase 2, (p - 1) ^ 2 :=
      Finset.prod_le_prod' (fun p hp =>
        hstep p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp))
    exact Nat.mul_le_mul_left _ hprod
  · calc ∏ p ∈ d.primeFactors, p
        ≤ ∏ p ∈ d.primeFactors, (p - 1) ^ 2 :=
          Finset.prod_le_prod' (fun p hp => hstep p hp (fun h => h2 (h ▸ hp)))
      _ ≤ 2 * ∏ p ∈ d.primeFactors, (p - 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)

/-- For squarefree `d ≥ 2`: `1/(d·φ(d)) ≤ √2 · 1/(d√d)`. -/
lemma inv_mul_totient_le {d : ℕ} (hd : Squarefree d) (hd2 : 2 ≤ d) :
    (1 : ℝ) / (d * Nat.totient d) ≤ Real.sqrt 2 * ((1 : ℝ) / (d * Real.sqrt d)) := by
  have hφ : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
  have hφR : (0 : ℝ) < Nat.totient d := by exact_mod_cast hφ
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsq : Real.sqrt d ≤ Real.sqrt 2 * Nat.totient d := by
    have h1 : (d : ℝ) ≤ 2 * (Nat.totient d : ℝ) ^ 2 := by
      exact_mod_cast le_two_mul_totient_sq hd
    calc Real.sqrt d ≤ Real.sqrt (2 * (Nat.totient d : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 2 * Nat.totient d := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hφR.le]
  have hsqd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (1 : ℝ) * ((d : ℝ) * Real.sqrt d) = (d : ℝ) * Real.sqrt d := one_mul _
    _ ≤ (d : ℝ) * (Real.sqrt 2 * Nat.totient d) := mul_le_mul_of_nonneg_left hsq hdR.le
    _ = Real.sqrt 2 * ((d : ℝ) * Nat.totient d) := by ring

/-- `∑_{d < x, squarefree, (d,B)=1} 1/(d·φ(d)) ≤ 4`. -/
lemma sum_inv_mul_totient_le (x B : ℕ) :
    ∑ d ∈ sqfCop x B, (1 : ℝ) / (d * Nat.totient d) ≤ 4 := by
  classical
  set f : ℕ → ℝ := fun d => (1 : ℝ) / (d * Nat.totient d) with hf
  have hf1 : f 1 = 1 := by simp [hf]
  have hnn : ∀ d, 0 ≤ f d := fun d => by rw [hf]; positivity
  have hsplit : ∑ d ∈ sqfCop x B, f d ≤ f 1 + ∑ d ∈ (sqfCop x B).erase 1, f d := by
    by_cases h : 1 ∈ sqfCop x B
    · exact le_of_eq (Finset.add_sum_erase _ f h).symm
    · rw [Finset.erase_eq_of_notMem h]
      linarith [hnn 1]
  have herase : ∑ d ∈ (sqfCop x B).erase 1, f d ≤ Real.sqrt 2 * 2 := by
    have hsub : (sqfCop x B).erase 1 ⊆ Finset.Icc 2 x := by
      intro d hd
      have hne := Finset.ne_of_mem_erase hd
      have hmem := Finset.mem_of_mem_erase hd
      rw [sqfCop, Finset.mem_filter, Finset.mem_range] at hmem
      have h0 : d ≠ 0 := hmem.2.1.ne_zero
      rw [Finset.mem_Icc]
      omega
    calc ∑ d ∈ (sqfCop x B).erase 1, f d
        ≤ ∑ d ∈ (sqfCop x B).erase 1, Real.sqrt 2 * ((1 : ℝ) / (d * Real.sqrt d)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hne := Finset.ne_of_mem_erase hd
          have hmem := Finset.mem_of_mem_erase hd
          rw [sqfCop, Finset.mem_filter] at hmem
          have h0 : d ≠ 0 := hmem.2.1.ne_zero
          exact inv_mul_totient_le hmem.2.1 (by omega)
      _ = Real.sqrt 2 * ∑ d ∈ (sqfCop x B).erase 1, (1 : ℝ) / (d * Real.sqrt d) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Real.sqrt 2 * ∑ d ∈ Finset.Icc 2 x, (1 : ℝ) / (d * Real.sqrt d) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro d _ _
          positivity
      _ ≤ Real.sqrt 2 * 2 :=
          mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_le x) (Real.sqrt_nonneg 2)
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 / 2) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  calc ∑ d ∈ sqfCop x B, f d ≤ f 1 + ∑ d ∈ (sqfCop x B).erase 1, f d := hsplit
    _ ≤ 1 + Real.sqrt 2 * 2 := by rw [hf1]; linarith [herase]
    _ ≤ 4 := by linarith

/-! ## Upper bound for the coprime harmonic sum -/

/-- `∑_{n < x, (n,B)=1} 1/n ≤ (φ(B)/B)·log x + (φ(B) + 1)`. -/
lemma copHarmonic_upper (B : ℕ) (hB : B ≠ 0) (x : ℕ) (hx : 2 ≤ x) :
    copHarmonic x B ≤ (Nat.totient B / B : ℝ) * Real.log x + ((Nat.totient B : ℝ) + 1) := by
  have hB0 : 0 < B := Nat.pos_of_ne_zero hB
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB0
  set q := (x - 1) / B with hq
  have hxq : x ≤ (q + 1) * B := by
    have h1 : B * q + (x - 1) % B = x - 1 := Nat.div_add_mod (x - 1) B
    have h2 : (x - 1) % B < B := Nat.mod_lt _ hB0
    have h3 : (q + 1) * B = B * q + B := by ring
    omega
  -- cover the domain by the blocks `0, …, q`
  have hA : copHarmonic x B ≤
      ∑ n ∈ (Finset.Icc 1 ((q + 1) * B)).filter (fun n => Nat.Coprime n B), (1 : ℝ) / n := by
    rw [copHarmonic_eq]
    simp_rw [one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hn.2.2⟩
    · intro n _ _
      positivity
  rw [sum_Icc_mul_eq_sum_blocks B _ (q + 1)] at hA
  -- split off block `0` and bound the rest by the harmonic sum
  rw [Finset.sum_range_succ'] at hA
  have hb0 : ∑ n ∈ (Finset.Ico (0 * B + 1) (0 * B + 1 + B)).filter
      (fun n => Nat.Coprime n B), (1 : ℝ) / n ≤ (Nat.totient B : ℝ) :=
    block_sum_upper_zero B hB0
  have hbj : ∑ j ∈ Finset.range q,
        ∑ n ∈ (Finset.Ico ((j + 1) * B + 1) ((j + 1) * B + 1 + B)).filter
          (fun n => Nat.Coprime n B), (1 : ℝ) / n
      ≤ ∑ j ∈ Finset.range q, (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B) := by
    apply Finset.sum_le_sum
    intro j _
    have h := block_sum_upper B hB0 (j + 1) (by omega)
    push_cast at h
    exact h
  have hharm : ∑ j ∈ Finset.range q, (Nat.totient B : ℝ) / (((j : ℝ) + 1) * B)
      = (Nat.totient B / B : ℝ) * ((harmonic q : ℚ) : ℝ) := sum_block_main B q
  have hlog : ((harmonic q : ℚ) : ℝ) ≤ 1 + Real.log x := by
    have h1 := harmonic_le_one_add_log q
    have h2 : Real.log q ≤ Real.log x := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h]
        norm_num
        exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
      · apply Real.log_le_log (by exact_mod_cast h)
        have hqx : q ≤ x := by
          have := Nat.div_le_self (x - 1) B
          omega
        exact_mod_cast hqx
    linarith
  have hratio : (Nat.totient B / B : ℝ) ≤ 1 := by
    rw [div_le_one hBR]
    exact_mod_cast Nat.totient_le B
  have hratio0 : (0 : ℝ) ≤ (Nat.totient B / B : ℝ) := by positivity
  have hmain : (Nat.totient B / B : ℝ) * ((harmonic q : ℚ) : ℝ)
      ≤ (Nat.totient B / B : ℝ) * (1 + Real.log x) :=
    mul_le_mul_of_nonneg_left hlog hratio0
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  calc copHarmonic x B
      ≤ (∑ j ∈ Finset.range q,
          ∑ n ∈ (Finset.Ico ((j + 1) * B + 1) ((j + 1) * B + 1 + B)).filter
            (fun n => Nat.Coprime n B), (1 : ℝ) / n)
        + ∑ n ∈ (Finset.Ico (0 * B + 1) (0 * B + 1 + B)).filter
            (fun n => Nat.Coprime n B), (1 : ℝ) / n := hA
    _ ≤ (Nat.totient B / B : ℝ) * ((harmonic q : ℚ) : ℝ) + (Nat.totient B : ℝ) := by
        rw [← hharm]
        linarith [hbj, hb0]
    _ ≤ (Nat.totient B / B : ℝ) * (1 + Real.log x) + (Nat.totient B : ℝ) := by
        linarith [hmain]
    _ ≤ (Nat.totient B / B : ℝ) * Real.log x + ((Nat.totient B : ℝ) + 1) := by
        have : (Nat.totient B / B : ℝ) * (1 + Real.log x)
            = (Nat.totient B / B : ℝ) + (Nat.totient B / B : ℝ) * Real.log x := by ring
        linarith [hratio]

/-! ## The packaged upper bounds -/

/-- **N3.1 upper bound, 4×-lossy leading constant**: for `B ≠ 0` there is `C`
with `phiAtomSum x B ≤ 4·(φ(B)/B)·log x + C` for all `x ≥ 2`.

The exact-constant version (leading coefficient `φ(B)/B`) did NOT land; see the
PORT-BLOCKER note at the end of the file. -/
theorem phiAtom_upper_lossy (B : ℕ) (hB : B ≠ 0) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      phiAtomSum x B ≤ 4 * ((Nat.totient B / B : ℝ) * Real.log x) + C := by
  refine ⟨4 * ((Nat.totient B : ℝ) + 1), fun x hx => ?_⟩
  have h1 := phiAtomSum_le_mul x B
  have h2 := sum_inv_mul_totient_le x B
  have h3 := copHarmonic_upper B hB x hx
  have hch : 0 ≤ copHarmonic x B := by
    unfold copHarmonic
    apply Finset.sum_nonneg
    intro n _
    positivity
  calc phiAtomSum x B
      ≤ (∑ d ∈ sqfCop x B, (1 : ℝ) / (d * Nat.totient d)) * copHarmonic x B := h1
    _ ≤ 4 * copHarmonic x B := mul_le_mul_of_nonneg_right h2 hch
    _ ≤ 4 * ((Nat.totient B / B : ℝ) * Real.log x + ((Nat.totient B : ℝ) + 1)) := by
        linarith [h3]
    _ = 4 * ((Nat.totient B / B : ℝ) * Real.log x) + 4 * ((Nat.totient B : ℝ) + 1) := by
        ring

/-- **N3.1 upper bound, fallback form**: `phiAtomSum x B ≤ C_B·(1 + log x)`. -/
theorem phiAtom_upper_fallback (B : ℕ) (hB : B ≠ 0) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → phiAtomSum x B ≤ C * (1 + Real.log x) := by
  refine ⟨4 * ((Nat.totient B : ℝ) + 1) + 4, fun x hx => ?_⟩
  have h1 := phiAtomSum_le_mul x B
  have h2 := sum_inv_mul_totient_le x B
  have h3 := copHarmonic_upper B hB x hx
  have hch : 0 ≤ copHarmonic x B := by
    unfold copHarmonic
    apply Finset.sum_nonneg
    intro n _
    positivity
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hBR : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hratio : (Nat.totient B / B : ℝ) ≤ 1 := by
    rw [div_le_one hBR]
    exact_mod_cast Nat.totient_le B
  have hφ0 : (0 : ℝ) ≤ (Nat.totient B : ℝ) := Nat.cast_nonneg _
  have hratio0 : (0 : ℝ) ≤ (Nat.totient B / B : ℝ) := by positivity
  have hbase : phiAtomSum x B
      ≤ 4 * ((Nat.totient B / B : ℝ) * Real.log x) + 4 * ((Nat.totient B : ℝ) + 1) := by
    calc phiAtomSum x B
        ≤ (∑ d ∈ sqfCop x B, (1 : ℝ) / (d * Nat.totient d)) * copHarmonic x B := h1
      _ ≤ 4 * copHarmonic x B := mul_le_mul_of_nonneg_right h2 hch
      _ ≤ 4 * ((Nat.totient B / B : ℝ) * Real.log x + ((Nat.totient B : ℝ) + 1)) := by
          linarith [h3]
      _ = 4 * ((Nat.totient B / B : ℝ) * Real.log x) + 4 * ((Nat.totient B : ℝ) + 1) := by
          ring
  have hstep : 4 * ((Nat.totient B / B : ℝ) * Real.log x) ≤ 4 * Real.log x := by
    have := mul_le_mul_of_nonneg_right hratio hlogx
    linarith
  calc phiAtomSum x B
      ≤ 4 * ((Nat.totient B / B : ℝ) * Real.log x) + 4 * ((Nat.totient B : ℝ) + 1) := hbase
    _ ≤ 4 * Real.log x + 4 * ((Nat.totient B : ℝ) + 1) := by linarith [hstep]
    _ ≤ (4 * ((Nat.totient B : ℝ) + 1) + 4) * (1 + Real.log x) := by
        nlinarith [mul_nonneg hφ0 hlogx, hlogx, hφ0]

/-! ## What did NOT land: the exact-constant upper bound

-- PORT-BLOCKER: the exact-constant upper bound
--
--   theorem phiAtom_upper (B : ℕ) (hB : B ≠ 0) :
--       ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
--         phiAtomSum x B ≤ (Nat.totient B / B : ℝ) * Real.log x + C
--
-- is NOT proved here.  The obstruction, precisely: expanding
-- `1/φ(r) = (1/r)·∑_{m : rad m ∣ r} 1/m` requires the *full* (infinite)
-- geometric sum, and the truncation error
--
--   ∑_{r < x squarefree} (1/r) · ∑_{m ≥ M(r), rad m ∣ r} 1/m
--
-- must be `O_B(1)`.  Every elementary bound tried turns the inner tail into
-- `≤ M^{-θ}·∏_{p ∣ r}(1 - p^{-(1-θ)})⁻¹ ≤ M^{-θ}·C_θ^{ω(r)}` and then needs
-- `∑_{r<x} C^{ω(r)}/r ≪ (log x)^C`, i.e. a Mertens-strength bound on
-- `∏_{p<x}(1 + C/p)` — not available elementarily (the crude
-- `∑_{p<x} 1/p ≤ 1 + log x` gives `x^C`, which is fatal).  The clean route is
-- the Dirichlet-series decomposition `μ²(r)·r/φ(r) = (1 * h)(r)` with
-- `h(p) = 1/(p-1)`, `h(p²) = -p/(p-1)`, `h(p^k) = 0 (k ≥ 3)`, whose key
-- miracle is `h(p)/p + h(p²)/p² = 0`, so `∑_d h(d)/d = 1` (leading constant
-- exactly recovered) and `∑_d |h(d)|/d < ∞`.  Formalizing that needs signed
-- multiplicative-function convolution plus a convergent-Euler-product argument
-- (mathlib's `EulerProduct` machinery); estimated a full C-difficulty node of
-- its own, out of scope for this probe.
--
-- What IS proved instead (this file): the same pair expansion kept *finite*
-- via the divisor identity `r/φ(r) = ∑_{d ∣ r} 1/φ(d)` (squarefree `r`),
-- giving the factorized bound
-- `phiAtomSum x B ≤ (∑_{d<x sqfree} 1/(dφ(d))) · (∑_{e<x, (e,B)=1} 1/e)`
-- with `∑ 1/(dφ(d)) ≤ 1 + 2√2 ≤ 4`.  The true value of that factor is
-- `ζ(2)ζ(3)/ζ(6) ≈ 1.9436`, so even a `2×`-lossy constant is out of reach of
-- the `d ≤ 2φ(d)²` bound used here (it would need ≈ 2500 explicitly summed
-- terms); `4×` is what honest elementary effort yields.
-/

end Salt.Maynard
