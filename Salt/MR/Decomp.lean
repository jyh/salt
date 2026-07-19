/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Decomp — the Ramaré/Buchstab decomposition (S8 / MR-CORE, node A1)

The Matomäki–Radziwiłł Dirichlet-polynomial decomposition (MR §2/§5, eq (9),
Lemma 12; source `docs/sources/1501.04585v4.pdf` pp.8-10, 19-20;
`docs/sources/mr_extract.md` §2.2).  The integration range
`(log X)^{1/15} ≤ t ≤ X/h` is split into `J+1` disjoint sets `𝒯₁,…,𝒯_J, 𝒰` by the
size of the prime Dirichlet polynomials `Σ_{P_j≤p≤Q_j} f(p)/p^{1+it}`, and on each
`𝒯_j` a **Buchstab/Ramaré identity** extracts a short prime block times a mean
value over the co-factor.

## The Sedunova–Wang v4 correction (the NAMED checklist item)

MR footnote 1, p.9 (verbatim): *"In the published version of this paper the term
`1_{(p,m)=1}` was incorrectly expressed as 1 leading to a slight gap in the
argument that affected only the proof of Lemma 12. This is corrected here."*

Concretely, eq (16) (p.19) writes, for the coefficient sequence `a`,

  `Σ_{X≤n≤2X} a_n/n^s
     = Σ_{P≤p≤Q} Σ_{X/p≤m≤2X/p} a_{pm}/(pm)^s · 1/(#{P≤q≤Q : q|m} + 1_{(p,m)=1})
       + Σ_{X≤n≤2X, (n,∏p)=1} a_n/n^s`.

The load-bearing algebraic fact — the one the `+1_{(p,m)=1}` correction repairs —
is that for every `n` with at least one block prime factor, the Ramaré weights of
its block-prime factorisations sum to **exactly 1** (`ramare_weight_sum`).  The
mechanism: for a block prime `p ∣ n` with `m = n/p`, the denominator
`#{block q ∣ m} + 1_{(p,m)=1}` equals `ω(n;P,Q)` (the number of distinct block
primes dividing `n`) *regardless of whether `p² ∣ n`*
(`blockPrimeDivs_div_card`).  Each weight is thus `1/ω(n)`, and there are `ω(n)`
of them.  With the published (uncorrected) `+1` this fails precisely when some
`p² ∣ n` — see `ramare_weight_bad` (at `P=Q=2, n=4` the sum is `1/2 ≠ 1`).

Source pins (D5): MR arXiv v4 (`1501.04585v4`), §2/§5, eq (9)/(16), Lemma 12,
footnote 1 p.9.
-/

namespace Salt.MR

open Finset

/-! ## §1  Block primes and the Ramaré weight -/

/-- **The block primes dividing `n`.**  The distinct primes `p ∣ n` with
`P ≤ p ≤ Q`; i.e. `n.primeFactors` restricted to the block `[P,Q]`. -/
def BlockPrimeDivs (P Q n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => P ≤ p ∧ p ≤ Q)

/-- `ω(n; P, Q)` — the number of distinct block primes dividing `n` (MR p.19). -/
def blockOmega (P Q n : ℕ) : ℕ := (BlockPrimeDivs P Q n).card

lemma mem_blockPrimeDivs {P Q n p : ℕ} :
    p ∈ BlockPrimeDivs P Q n ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 ∧ P ≤ p ∧ p ≤ Q := by
  rw [BlockPrimeDivs, Finset.mem_filter, Nat.mem_primeFactors]
  tauto

/-- **The Ramaré weight** (the corrected, v4 form).  For a block prime `p` and a
co-factor `m`, the weight `1/(#{block q ∣ m} + 1_{(p,m)=1})` attached to the
factorisation `n = p·m` in eq (16). -/
noncomputable def ramareWeight (P Q p m : ℕ) : ℝ :=
  1 / (((BlockPrimeDivs P Q m).card : ℝ) + (if Nat.Coprime p m then 1 else 0))

/-- **The uncorrected (published) weight**, denominator `#{block q ∣ m} + 1` for
*all* `m`.  This is the shape the v4 footnote flags as wrong. -/
noncomputable def ramareWeightBad (P Q _p m : ℕ) : ℝ :=
  1 / (((BlockPrimeDivs P Q m).card : ℝ) + 1)

/-! ## §2  The correction identity: the denominator equals `ω(n;P,Q)` -/

/-- **The correction step (v4).**  For a block prime `p ∣ n` with `m = n/p`, the
corrected denominator `#{block q ∣ m} + 1_{(p,m)=1}` equals `ω(n; P, Q)` —
*whether or not `p² ∣ n`*.  This is the exact off-by-one the Sedunova–Wang
correction repairs (footnote 1, p.9): the `p² ∣ n` branch keeps `p` among the
block divisors of `m` but has `1_{(p,m)=1}=0`; the `p² ∤ n` branch drops `p` but
has `1_{(p,m)=1}=1`. -/
lemma blockPrimeDivs_div_card {P Q n p : ℕ} (hp : p ∈ BlockPrimeDivs P Q n) :
    (BlockPrimeDivs P Q (n / p)).card + (if Nat.Coprime p (n / p) then 1 else 0)
      = blockOmega P Q n := by
  rw [mem_blockPrimeDivs] at hp
  obtain ⟨hpp, hpdvd, hn0, _hPp, _hpQ⟩ := hp
  have hnpm : n = p * (n / p) := (Nat.mul_div_cancel' hpdvd).symm
  set m := n / p with hm
  have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hnpm; exact hn0 hnpm
  have hp0 : p ≠ 0 := hpp.pos.ne'
  unfold blockOmega
  by_cases hpm : p ∣ m
  · have hcop : ¬ Nat.Coprime p m := fun h => (hpp.coprime_iff_not_dvd.mp h) hpm
    rw [if_neg hcop, add_zero]
    have hpf : n.primeFactors = m.primeFactors := by
      conv_lhs => rw [hnpm]
      rw [Nat.primeFactors_mul hp0 hm0, hpp.primeFactors, Finset.singleton_union,
        Finset.insert_eq_self.mpr (Nat.mem_primeFactors.mpr ⟨hpp, hpm, hm0⟩)]
    simp only [BlockPrimeDivs, hpf]
  · have hcop : Nat.Coprime p m := hpp.coprime_iff_not_dvd.mpr hpm
    rw [if_pos hcop]
    have hpnotf : p ∉ m.primeFactors := fun h => hpm (Nat.dvd_of_mem_primeFactors h)
    have hpf : n.primeFactors = insert p m.primeFactors := by
      conv_lhs => rw [hnpm]
      rw [Nat.primeFactors_mul hp0 hm0, hpp.primeFactors, Finset.singleton_union]
    have hins : BlockPrimeDivs P Q n = insert p (BlockPrimeDivs P Q m) := by
      rw [BlockPrimeDivs, BlockPrimeDivs, hpf, Finset.filter_insert, if_pos ⟨_hPp, _hpQ⟩]
    have hpnotB : p ∉ BlockPrimeDivs P Q m := fun h => hpnotf (Finset.mem_of_mem_filter p h)
    rw [hins, Finset.card_insert_of_notMem hpnotB]

/-! ## §3  The Ramaré identity: the weights sum to 1 -/

/-- **The Ramaré identity (eq (16)'s combinatorial core, with the v4
correction).**  For any `n` with at least one block prime factor, the corrected
Ramaré weights over its block-prime factorisations sum to exactly `1`.  This is
the algebraic identity underlying the Buchstab/Ramaré decomposition; the
`1_{(p,m)=1}` correction is what makes every weight equal to `1/ω(n;P,Q)`. -/
theorem ramare_weight_sum {P Q n : ℕ} (hn : 1 ≤ blockOmega P Q n) :
    ∑ p ∈ BlockPrimeDivs P Q n, ramareWeight P Q p (n / p) = 1 := by
  have key : ∀ p ∈ BlockPrimeDivs P Q n,
      ramareWeight P Q p (n / p) = 1 / (blockOmega P Q n : ℝ) := by
    intro p hp
    have hR := congrArg (fun k : ℕ => (k : ℝ)) (blockPrimeDivs_div_card hp)
    simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hR
    rw [ramareWeight, hR]
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul]
  have hne : (blockOmega P Q n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  change ((BlockPrimeDivs P Q n).card : ℝ) * (1 / (blockOmega P Q n : ℝ)) = 1
  rw [show ((BlockPrimeDivs P Q n).card : ℝ) = (blockOmega P Q n : ℝ) from rfl]
  exact mul_one_div_cancel hne

/-! ## §4  The correction is load-bearing: the uncorrected weight fails -/

/-- **The v4 correction is necessary (the false-witness).**  With the published
uncorrected weight (`+1` instead of `+1_{(p,m)=1}`), the Ramaré sum is *not* `1`:
at `P=Q=2`, `n=4` the single block-prime factorisation `4 = 2·2` has `p²∣n`, the
uncorrected denominator is `#{block q∣2}+1 = 1+1 = 2`, and the sum is `1/2 ≠ 1`.
This is exactly the gap footnote 1 (p.9) describes. -/
theorem ramare_weight_bad :
    ∑ p ∈ BlockPrimeDivs 2 2 4, ramareWeightBad 2 2 p (4 / p) = 1 / 2
      ∧ (1 : ℝ) / 2 ≠ 1 := by
  refine ⟨?_, by norm_num⟩
  have h4 : BlockPrimeDivs 2 2 4 = {2} := by
    ext p
    rw [mem_blockPrimeDivs, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, _, hle, hge⟩; omega
    · rintro rfl; exact ⟨Nat.prime_two, by norm_num, by norm_num, le_refl 2, le_refl 2⟩
  have h2 : BlockPrimeDivs 2 2 2 = {2} := by
    ext p
    rw [mem_blockPrimeDivs, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, _, hle, hge⟩; omega
    · rintro rfl; exact ⟨Nat.prime_two, dvd_refl 2, by norm_num, le_refl 2, le_refl 2⟩
  rw [h4, Finset.sum_singleton]
  change ramareWeightBad 2 2 2 (4 / 2) = 1 / 2
  rw [show (4 : ℕ) / 2 = 2 from rfl, ramareWeightBad, h2]
  norm_num

/-! ## §5  The Ramaré/Buchstab decomposition (eq (16)) as an identity of sums

The algebraic content of eq (16): summing any coefficient `c : ℕ → M` (`M` an
`ℝ`-module — instantiated at `ℝ` or `ℂ` for the Dirichlet-polynomial `a_n/n^s`)
over a finite index set `S` splits into a **Ramaré-weighted double sum** over the
`n` with a block prime factor, plus a **coprime tail** over the `n` with none.
The double sum carries the corrected weights `ramareWeight` (v4); on the
block-prime part the weights sum to `1` (`ramare_weight_sum`), so the double sum
reproduces exactly `∑_{ω≥1} c n`.  This is the `n`-indexed form of eq (16); the
`n = p·m` factorisation into `Q_{v,H}·R_{v,H}` (Lemma 12) is a downstream
re-presentation. -/

/-- **The Ramaré regrouping on the block-prime part.**  On the `n` that have at
least one block prime factor, `c n` equals its Ramaré-weighted expansion over the
block-prime factorisations `n = p·(n/p)` (with the v4-corrected weights). -/
theorem ramare_decomp_filter {P Q : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (S : Finset ℕ) (c : ℕ → M) :
    ∑ n ∈ S.filter (fun n => 1 ≤ blockOmega P Q n), c n
      = ∑ n ∈ S.filter (fun n => 1 ≤ blockOmega P Q n),
          ∑ p ∈ BlockPrimeDivs P Q n, ramareWeight P Q p (n / p) • c n := by
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  rw [← Finset.sum_smul, ramare_weight_sum hn.2, one_smul]

/-- **The Ramaré/Buchstab decomposition (eq (16)).**  For any coefficient
`c : ℕ → M` and index set `S`,
`∑_{n∈S} c n = (Ramaré double sum over the block-prime n) + (coprime tail)`,
where the tail runs over the `n∈S` with `ω(n;P,Q)=0` (no block prime factor —
`(n, ∏_{P≤p≤Q} p) = 1`). -/
theorem ramare_decomp {P Q : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (S : Finset ℕ) (c : ℕ → M) :
    ∑ n ∈ S, c n
      = (∑ n ∈ S.filter (fun n => 1 ≤ blockOmega P Q n),
            ∑ p ∈ BlockPrimeDivs P Q n, ramareWeight P Q p (n / p) • c n)
        + ∑ n ∈ S.filter (fun n => blockOmega P Q n = 0), c n := by
  rw [← ramare_decomp_filter]
  have hcompl : S.filter (fun n => blockOmega P Q n = 0)
      = S.filter (fun n => ¬ 1 ≤ blockOmega P Q n) :=
    Finset.filter_congr (fun n _ => by omega)
  rw [hcompl, Finset.sum_filter_add_sum_filter_not]

/-! ## §6  The `𝒯_j / 𝒰` split of the integration range (p.8)

The range `(log X)^{1/15} ≤ t ≤ X/h` is split into `J+1` disjoint sets
`𝒯₁,…,𝒯_J, 𝒰` by the sizes of the prime Dirichlet polynomials
`Σ_{P_j≤p≤Q_j} f(p)/p^{1+it}` (eq (6)).  We formalise the definitions and their
structural properties (disjointness, exhaustiveness); the analytic content (`𝒰`
is thin, `O(T^{1/2-ε})`) is a separate rung. -/

/-- **The prime block Dirichlet polynomial** (eq (6)):
`Σ_{P≤p≤Q, p prime} f(p)/p^{1+it}`. -/
noncomputable def primeBlockPoly (f : ℕ → ℂ) (P Q : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
    f p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- **Block smallness at index `j`.**  All subdivisions `[P,Q] ⊂ [P_j,Q_j]` of the
prime block polynomial are small (norm `≤ δ`) at `t` — the "appropriate
subdivisions of (6) are small (power-saving)" condition (p.8). -/
def BlockSmallAt (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (j : ℕ)
    (t : ℝ) : Prop :=
  ∀ P Q, Pseq j ≤ P → Q ≤ Qseq j → ‖primeBlockPoly f P Q t‖ ≤ δ

/-- **`𝒯_j`** (p.8): `t ∈ 𝒯_j` iff `j` is the *smallest* index in `[1,J]` for which
all subdivisions of (6) over `[P_j,Q_j]` are small. -/
def Tset (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J j : ℕ) : Set ℝ :=
  {t | 1 ≤ j ∧ j ≤ J ∧ BlockSmallAt f Pseq Qseq δ j t ∧
       ∀ i, 1 ≤ i → i < j → ¬ BlockSmallAt f Pseq Qseq δ i t}

/-- **`𝒰`** (p.8, the exceptional/extreme-`t` set): `t ∈ 𝒰` iff there is *no*
index `j ∈ [1,J]` for which all subdivisions of (6) are small. -/
def Uset (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J : ℕ) : Set ℝ :=
  {t | ∀ j, 1 ≤ j → j ≤ J → ¬ BlockSmallAt f Pseq Qseq δ j t}

variable {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {δ : ℝ} {J : ℕ}

/-- The `𝒯_j` are determined by the *smallest* small index, so `t` lies in at
most one of them. -/
lemma Tset_unique {j j' : ℕ} {t : ℝ}
    (hj : t ∈ Tset f Pseq Qseq δ J j) (hj' : t ∈ Tset f Pseq Qseq δ J j') : j = j' := by
  obtain ⟨hj1, _, hjs, hjm⟩ := hj
  obtain ⟨hj'1, _, hj's, hj'm⟩ := hj'
  by_contra hne
  rcases Nat.lt_or_ge j j' with h | h
  · exact hj'm j hj1 h hjs
  · rcases Nat.lt_or_ge j' j with h' | h'
    · exact hjm j' hj'1 h' hj's
    · omega

/-- The `𝒯_j` are pairwise disjoint. -/
lemma Tset_disjoint {j j' : ℕ} (h : j ≠ j') :
    Disjoint (Tset f Pseq Qseq δ J j) (Tset f Pseq Qseq δ J j') := by
  rw [Set.disjoint_left]
  exact fun t ht ht' => h (Tset_unique ht ht')

/-- Each `𝒯_j` is disjoint from `𝒰`. -/
lemma Tset_Uset_disjoint {j : ℕ} :
    Disjoint (Tset f Pseq Qseq δ J j) (Uset f Pseq Qseq δ J) := by
  rw [Set.disjoint_left]
  rintro t ⟨hj1, hjJ, hjs, _⟩ hU
  exact hU j hj1 hjJ hjs

/-- **Exhaustiveness of the split.**  Every real is in some `𝒯_j` or in `𝒰`:
`[1,J]`'s `𝒯_j` together with `𝒰` cover the line (the range restriction
`(log X)^{1/15} ≤ t ≤ X/h` is imposed separately). -/
lemma exists_Tset_or_mem_Uset (t : ℝ) :
    (∃ j, t ∈ Tset f Pseq Qseq δ J j) ∨ t ∈ Uset f Pseq Qseq δ J := by
  classical
  by_cases h : ∃ j, 1 ≤ j ∧ j ≤ J ∧ BlockSmallAt f Pseq Qseq δ j t
  · left
    have hspec := Nat.find_spec h
    refine ⟨Nat.find h, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
    intro i hi1 hij hsmall
    have hiJ : i ≤ J := by have := hspec.2.1; omega
    exact (Nat.find_min h hij) ⟨hi1, hiJ, hsmall⟩
  · right
    exact fun j hj1 hjJ hsmall => h ⟨j, hj1, hjJ, hsmall⟩

end Salt.MR
