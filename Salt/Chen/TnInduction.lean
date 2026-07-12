/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Buchstab
import Salt.Chen.Tail
import Salt.BrunLower.WRatio

/-!
# C1c″ — The `Tₙ` Buchstab-chain decomposition of the Rosser sieve (BJS Prop 13 / (28))

This file discharges the combinatorial heart of the main-term comparison `hmain` of the
two-sided explicit linear sieve (BJS Theorem 6, `Salt/Chen/LinearSieve.lean`): the
**Buchstab decomposition** of the Rosser-truncated Möbius sum,

  `G(z, λ±) = V(z) ± Σₙ Tₙ`   (BJS Proposition 13),

where `G(z, λ) = mainSum λ`, `V(z) = W s = ∏_{p|P(z)}(1−ν(p))`, and

  `Tₙ = Σ_{p₁ > ⋯ > pₙ, Rosser-violating first at n} ν(p₁⋯pₙ)·V(pₙ)`   (BJS (28)).

## The identity (floor B — the primary artifact)

Starting from C1c′'s `mainSum_lam_defect`
(`W s − mainSum S.lam = Σ_{d|P(z)} μ(d)[¬P d]ν(d)`), we organise the Rosser-violating
Möbius defect by the **position of first violation**.  Every squarefree `d | P(z)` that
fails the Rosser check factors uniquely as `d = c·e` where:

* `c = p₁⋯pₙ` is the **violating prefix** — the top `n` primes, with `n ≡ ν (mod 2)` the
  first checked position that fails: `c·(minFac c)² ≥ D`, while all earlier same-parity
  positions pass;
* `e | P(pₙ)` is the **free tail** below `pₙ = minFac c`, ranging over *all* divisors of
  the sifting primes below `pₙ`.

Multiplicativity collapses the inner tail sum to `V(pₙ)` (the untruncated Möbius sum over
`e | P(pₙ)`, `Vbelow_eq`), giving the master identity

  `W s − mainSum S.lam = Σ_{c : violating prefix} μ(c)·ν(c)·V(minFac c)`   (`buchstab_defect`)

and, grouping by `μ(c) = (−1)^{ω(c)}`, the signed Prop-13 form
`mainSum λ⁺ = W + Σ_{n odd} Tₙ`, `mainSum λ⁻ = W − Σ_{n even} Tₙ`.

## The `hbar` vs `hBJS` design choice

`LinearSieve.hmain` is phrased against `hBJS` (BJS's piecewise `e⁻²/e⁻ˢ/3s⁻¹e⁻ˢ`);
Tail.lean's per-level bounds (`fseq_le`) are against the exponential majorant `hbar`.
Since `hbar` decays *faster* (`hbar s ≤ hBJS s`, `hbar_le_hBJS`), a `hbar`-slack upper
bound is *a fortiori* an `hBJS`-slack bound — the correct direction for the upper `hmain`.
The bridge is landed here.
-/

open Finset Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

namespace Salt.Chen

open List

/-- The Rosser condition is (classically) decidable, so it may key `Finset.filter`. -/
noncomputable instance (side D : ℕ) : DecidablePred (rosserCond side D) :=
  fun _ => Classical.propDecidable _

/-! ## Part A — the base density `V(u) = Vbelow` below a cutoff and its Möbius sum -/

/-- The sifting primes below the cutoff `q` (BJS `p < u`). -/
noncomputable def belowPrimes (s : BoundingSieve) (q : ℕ) : Finset ℕ :=
  s.prodPrimes.primeFactors.filter (fun p => p < q)

/-- `P(u) = ∏_{p < u} p` over the sifting primes — the modulus of the free Buchstab tail. -/
noncomputable def Pbelow (s : BoundingSieve) (q : ℕ) : ℕ := ∏ p ∈ belowPrimes s q, p

/-- `V(u) = ∏_{p < u}(1 − ν(p))` over the sifting primes (BJS `V(u)`); the Buchstab base
density at cutoff `u`.  Equals `W s` at `q > z`. -/
noncomputable def Vbelow (s : BoundingSieve) (q : ℕ) : ℝ := ∏ p ∈ belowPrimes s q, (1 - s.nu p)

lemma belowPrimes_prime {s : BoundingSieve} {q p : ℕ} (hp : p ∈ belowPrimes s q) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-- `Pbelow` is squarefree (a product of distinct primes dividing the squarefree `P(z)`). -/
lemma Pbelow_squarefree (s : BoundingSieve) (q : ℕ) : Squarefree (Pbelow s q) := by
  have hdvd : Pbelow s q ∣ s.prodPrimes := by
    unfold Pbelow
    calc ∏ p ∈ belowPrimes s q, p
        ∣ ∏ p ∈ s.prodPrimes.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      _ = s.prodPrimes := Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree
  exact s.prodPrimes_squarefree.squarefree_of_dvd hdvd

lemma Pbelow_ne_zero (s : BoundingSieve) (q : ℕ) : Pbelow s q ≠ 0 :=
  (Pbelow_squarefree s q).ne_zero

/-- The prime factors of `Pbelow` are exactly the sifting primes below `q`. -/
lemma primeFactors_Pbelow (s : BoundingSieve) (q : ℕ) :
    (Pbelow s q).primeFactors = belowPrimes s q :=
  Nat.primeFactors_prod (fun _p hp => belowPrimes_prime hp)

/-- **The inner Buchstab factorisation** (BJS Prop 13, the `V(pₙ)` tail collapse): the
untruncated Möbius sum over the free tail `e | P(u)` equals the base density `V(u)`.  This
is the multiplicative heart that turns each chain's inner sum into a single `V`-factor. -/
lemma Vbelow_eq (s : BoundingSieve) (q : ℕ) :
    ∑ e ∈ (Pbelow s q).divisors, (μ e : ℝ) * s.nu e = Vbelow s q := by
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    s.nu s.nu_mult (Pbelow_squarefree s q)
  rw [primeFactors_Pbelow] at h
  rw [← h, Vbelow]

lemma Vbelow_pos (s : BoundingSieve) (q : ℕ) : 0 < Vbelow s q := by
  unfold Vbelow
  apply Finset.prod_pos
  intro p hp
  have hpp : p.Prime := belowPrimes_prime hp
  have hdvd : p ∣ s.prodPrimes :=
    Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have := s.nu_lt_one_of_prime p hpp hdvd
  linarith

/-! ## Part B — the descending-list block concatenation

`rlist_mul_prime` (LinearSieve.lean) shows `rlist (p·t) = rlist t ++ [p]` when prepending a
single prime `p` below every factor of `t`.  For the Buchstab reindexing `d = c·e` we need
the *block* form: when every prime of `e` lies below every prime of `c`, the descending
prime list of `c·e` is `rlist c ++ rlist e`. -/

/-- **Descending-list block concatenation.**  If `c, e` are nonzero, coprime, and every
prime factor of `e` is smaller than every prime factor of `c`, then
`rlist (c·e) = rlist c ++ rlist e`. -/
lemma rlist_mul_block {c e : ℕ} (hc : c ≠ 0) (he : e ≠ 0)
    (hlt : ∀ p ∈ e.primeFactors, ∀ q ∈ c.primeFactors, p < q) :
    rlist (c * e) = rlist c ++ rlist e := by
  have hdisj : Disjoint c.primeFactors e.primeFactors := by
    rw [Finset.disjoint_left]
    intro a hac hae
    exact absurd (hlt a hae a hac) (lt_irrefl a)
  have hpf : (c * e).primeFactors = c.primeFactors ∪ e.primeFactors :=
    Nat.primeFactors_mul hc he
  have hsortedR : (rlist c ++ rlist e).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨(rlist_sortedGE c).pairwise, (rlist_sortedGE e).pairwise, ?_⟩
    intro a ha b hb
    exact le_of_lt (hlt b (rlist_mem.mp hb) a (rlist_mem.mp ha))
  have hcoe : (↑(rlist (c * e)) : Multiset ℕ) = ↑(rlist c ++ rlist e) := by
    rw [← Multiset.coe_add, rlist, rlist, rlist, Finset.sort_eq, Finset.sort_eq,
      Finset.sort_eq, hpf, ← Finset.disjUnion_eq_union c.primeFactors e.primeFactors hdisj]
    rfl
  exact List.Perm.eq_of_sortedGE (rlist_sortedGE (c * e)) hsortedR (Multiset.coe_eq_coe.mp hcoe)

/-! ## Part C — the prefix / suffix split of a squarefree divisor

For `d = p₁ > ⋯ > pᵣ` and a depth `n`, the top-`n` prefix product `rprefix d n = p₁⋯pₙ`
and the free suffix `rsuffix d n = pₙ₊₁⋯pᵣ` satisfy `d = (rprefix d n)·(rsuffix d n)`, and
their positional data (`relem`, `rprefix`) coincides with `d`'s on the overlapping range.
This is the surgery that lets the Buchstab reindexing translate a violating divisor `d`
into `(violating prefix, free tail)`. -/

/-- General list fact: `(l.take n).prod = ∏_{j<n} l.getD j 1`. -/
theorem take_prod_eq (l : List ℕ) (n : ℕ) :
    (l.take n).prod = ∏ j ∈ Finset.range n, l.getD j 1 := by
  induction n generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons a t =>
      rw [List.take_succ_cons, List.prod_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih t]; ring

/-- `rlist` inverts `List.prod` on a descending nodup list of primes: `rlist l.prod = l`. -/
theorem rlist_prod_of_sortedGE_primes (l : List ℕ) (hnd : l.Nodup)
    (hp : ∀ p ∈ l, p.Prime) (hs : l.SortedGE) : rlist l.prod = l := by
  have hpf : l.prod.primeFactors = l.toFinset := by
    have hpr : l.prod = ∏ p ∈ l.toFinset, p := by
      rw [List.prod_toFinset (fun p => p) hnd]; simp
    rw [hpr]
    exact Nat.primeFactors_prod (fun p hp' => hp p (List.mem_toFinset.mp hp'))
  have hcoe : (↑(rlist l.prod) : Multiset ℕ) = ↑l := by
    rw [rlist, Finset.sort_eq, hpf]
    simp [List.toFinset_val, List.dedup_eq_self.mpr hnd]
  exact List.Perm.eq_of_sortedGE (rlist_sortedGE l.prod) hs (Multiset.coe_eq_coe.mp hcoe)

/-- The full descending list multiplies back to `d` (squarefree). -/
theorem rlist_prod {d : ℕ} (hd : Squarefree d) : (rlist d).prod = d := by
  rw [← Multiset.prod_coe, rlist, Finset.sort_eq]
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hd, Finset.prod_eq_multiset_prod]
  simp

/-- `rprefix d n` is the product of the top `n` primes, i.e. `((rlist d).take n).prod`. -/
theorem rprefix_eq_take (d n : ℕ) : rprefix d n = ((rlist d).take n).prod := by
  rw [rprefix, take_prod_eq]

/-- The free suffix `pₙ₊₁⋯pᵣ` = product of the bottom `length − n` primes. -/
noncomputable def rsuffix (d n : ℕ) : ℕ := ((rlist d).drop n).prod

/-- `d = (rprefix d n)·(rsuffix d n)` (squarefree `d`): the top-`n`/bottom split. -/
theorem rprefix_mul_rsuffix {d : ℕ} (hd : Squarefree d) (n : ℕ) :
    rprefix d n * rsuffix d n = d := by
  rw [rprefix_eq_take, rsuffix, ← List.prod_append, List.take_append_drop, rlist_prod hd]

lemma take_nodup (d n : ℕ) : ((rlist d).take n).Nodup :=
  (rlist_nodup d).sublist (List.take_sublist n _)
lemma take_sortedGE (d n : ℕ) : ((rlist d).take n).SortedGE :=
  List.sortedGE_iff_pairwise.mpr
    (List.Pairwise.sublist (List.take_sublist n _) (rlist_sortedGE d).pairwise)
lemma take_prime {d n p : ℕ} (hp : p ∈ (rlist d).take n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (rlist_mem.mp (List.mem_of_mem_take hp))
lemma drop_sortedGE (d n : ℕ) : ((rlist d).drop n).SortedGE :=
  List.sortedGE_iff_pairwise.mpr
    (List.Pairwise.sublist (List.drop_sublist n _) (rlist_sortedGE d).pairwise)

/-- `rlist (rprefix d n) = (rlist d).take n`: the prefix's own list is the top-`n` segment. -/
theorem rlist_rprefix (d n : ℕ) : rlist (rprefix d n) = (rlist d).take n := by
  rw [rprefix_eq_take]
  exact rlist_prod_of_sortedGE_primes _ (take_nodup d n) (fun _ => take_prime) (take_sortedGE d n)

/-- `rlist (rsuffix d n) = (rlist d).drop n`. -/
theorem rlist_rsuffix (d n : ℕ) : rlist (rsuffix d n) = (rlist d).drop n := by
  rw [rsuffix]
  refine rlist_prod_of_sortedGE_primes _
    ((rlist_nodup d).sublist (List.drop_sublist n _)) (fun p hp => ?_) (drop_sortedGE d n)
  exact Nat.prime_of_mem_primeFactors (rlist_mem.mp (List.mem_of_mem_drop hp))

/-- The prefix has exactly `min n (length)` primes; for `n ≤ length`, exactly `n`. -/
theorem length_rlist_rprefix (d n : ℕ) :
    (rlist (rprefix d n)).length = min n (rlist d).length := by
  rw [rlist_rprefix, List.length_take]

/-- `getD` domination: within the top `n`, the prefix's list agrees with `d`'s. -/
theorem getD_rlist_rprefix {d n i : ℕ} (hi : i < n) :
    (rlist (rprefix d n)).getD i 1 = (rlist d).getD i 1 := by
  rw [rlist_rprefix]
  rcases lt_or_ge i (rlist d).length with h | h
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_take]; omega),
      List.getD_eq_getElem _ _ h, List.getElem_take]
  · rw [List.getD_eq_default _ _ (by rw [List.length_take]; omega),
      List.getD_eq_default _ _ h]

/-- `getD` of the suffix: `(drop n)` re-indexes by `+n`. -/
theorem getD_rlist_rsuffix (d n i : ℕ) :
    (rlist (rsuffix d n)).getD i 1 = (rlist d).getD (n + i) 1 := by
  rw [rlist_rsuffix]
  rcases lt_or_ge (n + i) (rlist d).length with h | h
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_drop]; omega),
      List.getD_eq_getElem _ _ h, List.getElem_drop]
  · rw [List.getD_eq_default _ _ (by rw [List.length_drop]; omega),
      List.getD_eq_default _ _ h]

/-- `relem` translation: the `i`-th prime of the prefix (for `i < n`) is `d`'s `i`-th. -/
theorem relem_rprefix {d n i : ℕ} (hi : i < n) : relem (rprefix d n) i = relem d i := by
  rw [relem, relem, getD_rlist_rprefix hi]

/-- `rprefix` translation: `rprefix (rprefix d n) m = rprefix d m` for `m ≤ n`. -/
theorem rprefix_rprefix {d n m : ℕ} (hm : m ≤ n) : rprefix (rprefix d n) m = rprefix d m := by
  unfold rprefix
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  exact getD_rlist_rprefix (by omega)

/-- Strict descent across a gap: `relem d j < relem d i` for `i < j < length`. -/
theorem relem_lt_relem {d i j : ℕ} (hij : i < j) (hj : j < (rlist d).length) :
    relem d j < relem d i := by
  have hgt : (rlist d)[j] < (rlist d)[i]'(by omega) :=
    (sortedGT_iff_getElem_gt_getElem_of_lt.mp (Finset.sortedGT_sort d.primeFactors))
      (i := j) (j := i) (by omega)
  rw [relem, relem, List.getD_eq_getElem _ _ hj,
    List.getD_eq_getElem _ _ (by omega : i < (rlist d).length)]
  exact hgt

/-- The smallest prime factor of `c` (`pₙ`, the last of the descending list). -/
noncomputable def rmin (c : ℕ) : ℕ := relem c ((rlist c).length - 1)

/-! ## Part D — the Buchstab decomposition identity (BJS Prop 13 / (28))

The Rosser-violating Möbius defect (C1c′'s `mainSum_lam_defect`) is reorganised by the
**position of first violation**.  `failIdx` collects the failing checked positions,
`fvLen` is the first (least) one, and `prefixMap d = p₁⋯p_{fvLen}` is the violating prefix.
Every violating `d` factors uniquely as `d = (prefixMap d)·(free tail below pₙ)`, giving
the master identity. -/

/-- The failing checked positions of `d` (0-indexed): position `i+1` is checked
(`(i+1) ≡ side`) and violates (`D ≤ (p₁⋯p_{i+1})·p_{i+1}²`). -/
noncomputable def failIdx (side D d : ℕ) : Finset ℕ :=
  (Finset.range (rlist d).length).filter
    (fun i => (i + 1) % 2 = side % 2 ∧ D ≤ rprefix d (i + 1) * (relem d i) ^ 2)

theorem mem_failIdx {side D d i : ℕ} :
    i ∈ failIdx side D d ↔
      i < (rlist d).length ∧ (i + 1) % 2 = side % 2 ∧ D ≤ rprefix d (i + 1) * (relem d i) ^ 2 := by
  simp only [failIdx, Finset.mem_filter, Finset.mem_range]

/-- `d` violates the Rosser condition iff it has a failing checked position. -/
theorem not_rosserCond_iff_failIdx (side D d : ℕ) :
    ¬ rosserCond side D d ↔ (failIdx side D d).Nonempty := by
  constructor
  · intro hncond
    by_contra hemp
    apply hncond
    intro i hiL hpar
    by_contra hge
    exact hemp ⟨i, mem_failIdx.mpr ⟨hiL, hpar, not_lt.mp hge⟩⟩
  · rintro ⟨i, hi⟩ hcond
    obtain ⟨hiL, hpar, hge⟩ := mem_failIdx.mp hi
    exact absurd (hcond i hiL hpar) (not_lt.mpr hge)

/-- The first-violation length `n` (least failing position `+1`); junk `0` if none. -/
noncomputable def fvLen (side D d : ℕ) : ℕ :=
  if h : (failIdx side D d).Nonempty then (failIdx side D d).min' h + 1 else 0

/-- The violating prefix `p₁⋯pₙ` (junk `1` if `d` passes). -/
noncomputable def prefixMap (side D d : ℕ) : ℕ := rprefix d (fvLen side D d)

/-- **First-violation specification (K1).**  If `d` has a failing checked position then
`n = fvLen` is a checked position (`1 ≤ n ≤ length`, `n ≡ side`) where `d` first violates,
with all earlier same-parity positions passing. -/
theorem fvLen_spec {side D d : ℕ} (hne : (failIdx side D d).Nonempty) :
    let n := fvLen side D d
    1 ≤ n ∧ n ≤ (rlist d).length ∧ n % 2 = side % 2 ∧
      D ≤ rprefix d n * (relem d (n - 1)) ^ 2 ∧
      (∀ m, 1 ≤ m → m < n → m % 2 = side % 2 →
        rprefix d m * (relem d (m - 1)) ^ 2 < D) := by
  have hval : fvLen side D d = (failIdx side D d).min' hne + 1 := dif_pos hne
  set i₀ := (failIdx side D d).min' hne with hi₀
  have hmem := Finset.min'_mem (failIdx side D d) hne
  obtain ⟨hi₀L, hi₀par, hi₀ge⟩ := mem_failIdx.mp hmem
  refine ⟨by rw [hval]; omega, by rw [hval]; omega, ?_, ?_, ?_⟩
  · rw [hval]; simpa using hi₀par
  · rw [hval, Nat.add_sub_cancel]; simpa using hi₀ge
  · intro m hm1 hmn hmpar
    rw [hval] at hmn
    -- m - 1 < i₀, so m - 1 ∉ failIdx; but its parity/range hold, hence it passes
    have hnotmem : m - 1 ∉ failIdx side D d := fun hmem =>
      absurd (Finset.min'_le _ _ hmem) (by omega)
    have hmL : m - 1 < (rlist d).length := by omega
    by_contra hge
    refine hnotmem (mem_failIdx.mpr ⟨hmL, ?_, ?_⟩)
    · rw [Nat.sub_add_cancel hm1]; exact hmpar
    · rw [Nat.sub_add_cancel hm1]; exact not_lt.mp hge

/-- **The violating-prefix predicate** (BJS (28)'s chain conditions on `c = p₁⋯pₙ`): the
last position (`n = ω(c)`, a checked position `≡ side`) fails `c·pₙ² ≥ D`, while all earlier
same-parity positions pass. -/
def isViolPrefix (side D c : ℕ) : Prop :=
  1 ≤ (rlist c).length ∧
  (rlist c).length % 2 = side % 2 ∧
  D ≤ rprefix c (rlist c).length * (relem c ((rlist c).length - 1)) ^ 2 ∧
  (∀ m, 1 ≤ m → m < (rlist c).length → m % 2 = side % 2 →
    rprefix c m * (relem c (m - 1)) ^ 2 < D)

/-- `isViolPrefix` is (classically) decidable, so it may key `Finset.filter`. -/
noncomputable instance (side D : ℕ) : DecidablePred (isViolPrefix side D) :=
  fun _ => Classical.propDecidable _

/-- **K2 — `prefixMap` lands in the violating prefixes.**  If `d` violates the Rosser
condition, its first-violation prefix `p₁⋯pₙ` is itself a violating prefix. -/
theorem isViolPrefix_prefixMap {side D d : ℕ} (hne : (failIdx side D d).Nonempty) :
    isViolPrefix side D (prefixMap side D d) := by
  obtain ⟨hn1, hnL, hnpar, hfail, hpass⟩ := fvLen_spec hne
  set n := fvLen side D d with hn
  have hpm : prefixMap side D d = rprefix d n := rfl
  have hLc : (rlist (prefixMap side D d)).length = n := by
    rw [hpm, length_rlist_rprefix, min_eq_left hnL]
  refine ⟨by rw [hLc]; exact hn1, by rw [hLc]; exact hnpar, ?_, ?_⟩
  · rw [hLc, hpm, rprefix_rprefix (le_refl n), relem_rprefix (by omega : n - 1 < n)]
    exact hfail
  · intro m hm1 hmlt hmpar
    rw [hLc] at hmlt
    rw [hpm, rprefix_rprefix (by omega : m ≤ n), relem_rprefix (by omega : m - 1 < n)]
    exact hpass m hm1 hmlt hmpar

/-! ## Part D (b) — the geometric split facts (`rmin` bounds, coprimality) -/

/-- `pₙ = rmin c` is `≤` every listed prime of `c` (it is the last, smallest one). -/
theorem rmin_le_relem {c j : ℕ} (hj : j < (rlist c).length) : rmin c ≤ relem c j := by
  rw [rmin]
  rcases Nat.lt_or_ge j ((rlist c).length - 1) with h | h
  · exact le_of_lt (relem_lt_relem h (by omega))
  · rw [show j = (rlist c).length - 1 by omega]

/-- `pₙ = rmin c ≤ q` for every prime factor `q` of `c`. -/
theorem rmin_le_of_mem {c q : ℕ} (hq : q ∈ c.primeFactors) : rmin c ≤ q := by
  obtain ⟨j, hj, hjq⟩ := List.mem_iff_getElem.mp (rlist_mem.mpr hq)
  have : relem c j = q := by rw [relem, List.getD_eq_getElem _ _ hj, hjq]
  rw [← this]; exact rmin_le_relem hj

/-- Separated prime factors give coprimality (the block factors `c ⊥ e`). -/
theorem coprime_of_primeFactors_lt {c e : ℕ} (hc : c ≠ 0) (he : e ≠ 0)
    (hlt : ∀ p ∈ e.primeFactors, ∀ q ∈ c.primeFactors, p < q) : Nat.Coprime c e := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  exact absurd (hlt p (Nat.mem_primeFactors.mpr ⟨hp, hpd.trans (Nat.gcd_dvd_right c e), he⟩)
      p (Nat.mem_primeFactors.mpr ⟨hp, hpd.trans (Nat.gcd_dvd_left c e), hc⟩)) (lt_irrefl p)

/-- The free tail `e | P(pₙ)` has all its primes below `pₙ = rmin c`, hence lies below every
prime of `c`; this is the `rlist_mul_block` hypothesis for `d = c·e`. -/
theorem tail_primeFactors_lt {s : BoundingSieve} {c e : ℕ}
    (he : e ∣ Pbelow s (rmin c)) :
    ∀ p ∈ e.primeFactors, ∀ q ∈ c.primeFactors, p < q := by
  intro p hp q hq
  have hpsub : e.primeFactors ⊆ (Pbelow s (rmin c)).primeFactors :=
    Nat.primeFactors_mono he (Pbelow_ne_zero s (rmin c))
  have hpbelow : p ∈ belowPrimes s (rmin c) := by
    rw [← primeFactors_Pbelow]; exact hpsub hp
  have hplt : p < rmin c := (Finset.mem_filter.mp hpbelow).2
  exact lt_of_lt_of_le hplt (rmin_le_of_mem hq)

/-! ## Part D (c) — the two fiber directions -/

/-- **Direction 1 (tail reconstruction).**  For a violating prefix `c | P(z)` and any free
tail `e | P(pₙ)`, the product `d = c·e` is a Rosser-violating divisor whose first-violation
prefix is `c` (`prefixMap d = c`). -/
theorem mul_tail_mem_fiber {s : BoundingSieve} {side D c e : ℕ}
    (hc : c ∣ s.prodPrimes) (hviol : isViolPrefix side D c) (he : e ∣ Pbelow s (rmin c)) :
    c * e ∣ s.prodPrimes ∧ ¬ rosserCond side D (c * e) ∧ prefixMap side D (c * e) = c := by
  obtain ⟨hL1, hLpar, hLfail, hLpass⟩ := hviol
  set Lc := (rlist c).length with hLcdef
  have hcsf : Squarefree c := s.prodPrimes_squarefree.squarefree_of_dvd hc
  have hc0 : c ≠ 0 := hcsf.ne_zero
  have he_pp : e ∣ s.prodPrimes := he.trans (by
    unfold Pbelow
    calc ∏ p ∈ belowPrimes s (rmin c), p
        ∣ ∏ p ∈ s.prodPrimes.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      _ = s.prodPrimes := Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree)
  have hesf : Squarefree e := s.prodPrimes_squarefree.squarefree_of_dvd he_pp
  have he0 : e ≠ 0 := hesf.ne_zero
  have hlt := tail_primeFactors_lt (s := s) (c := c) (e := e) he
  have hcop : Nat.Coprime c e := coprime_of_primeFactors_lt hc0 he0 hlt
  have hce_dvd : c * e ∣ s.prodPrimes := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hc he_pp
  have hblock : rlist (c * e) = rlist c ++ rlist e := rlist_mul_block hc0 he0 hlt
  have hlence : (rlist (c * e)).length = Lc + (rlist e).length := by
    rw [hblock, List.length_append]
  -- translation of positional data on the top `Lc` positions
  have htrp : ∀ m, m ≤ Lc → rprefix (c * e) m = rprefix c m := by
    intro m hm
    unfold rprefix
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [hblock, List.getD_append _ _ _ _ (by omega : j < (rlist c).length)]
  have htre : ∀ i, i < Lc → relem (c * e) i = relem c i := by
    intro i hi
    rw [relem, relem, hblock, List.getD_append _ _ _ _ (by omega : i < (rlist c).length)]
  have hcL : rprefix c Lc = c := rprefix_full hcsf
  have hrmin : relem c (Lc - 1) = rmin c := rfl
  -- position `Lc` fails on `c·e`
  have hmemL : Lc - 1 ∈ failIdx side D (c * e) := by
    refine mem_failIdx.mpr ⟨by omega, ?_, ?_⟩
    · rw [Nat.sub_add_cancel hL1]; exact hLpar
    · rw [Nat.sub_add_cancel hL1, htrp Lc (le_refl _), htre (Lc - 1) (by omega)]
      rw [hcL] at hLfail ⊢
      exact hLfail
  have hne' : (failIdx side D (c * e)).Nonempty := ⟨_, hmemL⟩
  -- no earlier failing position (the `c`-part all passes)
  have hnosmall : ∀ i ∈ failIdx side D (c * e), Lc - 1 ≤ i := by
    intro i hi
    obtain ⟨hiL, hipar, hige⟩ := mem_failIdx.mp hi
    by_contra hlt'
    rw [not_le] at hlt'
    have him1 : i + 1 ≤ Lc := by omega
    rw [htrp (i + 1) him1, htre i (by omega)] at hige
    exact absurd hige (not_le.mpr (hLpass (i + 1) (by omega) (by omega) hipar))
  have hminval : (failIdx side D (c * e)).min' hne' = Lc - 1 :=
    le_antisymm (Finset.min'_le _ _ hmemL) (hnosmall _ (Finset.min'_mem _ hne'))
  refine ⟨hce_dvd, (not_rosserCond_iff_failIdx _ _ _).mpr hne', ?_⟩
  rw [prefixMap, fvLen, dif_pos hne', hminval, Nat.sub_add_cancel hL1, htrp Lc (le_refl _), hcL]

/-- Squarefree `e` divides `P(q)` once all its primes are sifting primes below `q`. -/
theorem dvd_Pbelow_of_subset {s : BoundingSieve} {e q : ℕ} (hesf : Squarefree e)
    (hsub : e.primeFactors ⊆ belowPrimes s q) : e ∣ Pbelow s q := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hesf]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- **Direction 2 (prefix/tail split).**  A Rosser-violating divisor `d` splits as
`d = c·e` with `c = prefixMap d` the violating prefix and `e = rsuffix d n` a free tail
`e | P(pₙ)`. -/
theorem tail_of_fiber {s : BoundingSieve} {side D d : ℕ}
    (hd : d ∣ s.prodPrimes) (hne : (failIdx side D d).Nonempty) :
    rsuffix d (fvLen side D d) ∣ Pbelow s (rmin (prefixMap side D d)) ∧
      prefixMap side D d * rsuffix d (fvLen side D d) = d := by
  obtain ⟨hn1, hnL, hnpar, hfail, hpass⟩ := fvLen_spec hne
  set n := fvLen side D d with hn
  have hdsf : Squarefree d := s.prodPrimes_squarefree.squarefree_of_dvd hd
  have hsplit : prefixMap side D d * rsuffix d n = d := rprefix_mul_rsuffix hdsf n
  -- `rmin (prefixMap d) = relem d (n-1)`
  have hLc : (rlist (prefixMap side D d)).length = n := by
    rw [prefixMap, ← hn, length_rlist_rprefix, min_eq_left hnL]
  have hrmin : rmin (prefixMap side D d) = relem d (n - 1) := by
    rw [rmin, hLc, prefixMap, ← hn, relem_rprefix (by omega : n - 1 < n)]
  refine ⟨?_, hsplit⟩
  rw [hrmin]
  -- `e = rsuffix d n` divides `prodPrimes`, is squarefree, and its primes are `< relem d (n-1)`
  have he_dvd_d : rsuffix d n ∣ d := ⟨prefixMap side D d, by rw [mul_comm]; exact hsplit.symm⟩
  have he_pp : rsuffix d n ∣ s.prodPrimes := he_dvd_d.trans hd
  have hesf : Squarefree (rsuffix d n) := s.prodPrimes_squarefree.squarefree_of_dvd he_pp
  refine dvd_Pbelow_of_subset hesf (fun p hp => ?_)
  have hp_pp : p ∈ s.prodPrimes.primeFactors :=
    Nat.primeFactors_mono he_pp s.prodPrimes_squarefree.ne_zero hp
  -- locate `p` in the dropped suffix `(rlist d).drop n`
  have hpin : p ∈ (rlist d).drop n := by
    rw [← rlist_rsuffix]; exact rlist_mem.mpr hp
  obtain ⟨i, hi, hip⟩ := List.mem_iff_getElem.mp hpin
  rw [List.length_drop] at hi
  rw [List.getElem_drop] at hip
  have hplt : p < relem d (n - 1) := by
    have hlt2 : relem d (n + i) < relem d (n - 1) := relem_lt_relem (by omega) (by omega)
    rwa [relem, List.getD_eq_getElem _ _ (by omega : n + i < (rlist d).length), hip] at hlt2
  exact Finset.mem_filter.mpr ⟨hp_pp, hplt⟩

/-! ## Part D (d) — the fiber sum and the master identity -/

/-- **The fiber sum** (BJS Prop 13, one violating prefix's contribution).  Summing the
Möbius weight over all Rosser-violating divisors with first-violation prefix `c` collapses
(via the free-tail bijection `e ↔ c·e` and the inner factorisation `Vbelow_eq`) to
`μ(c)·ν(c)·V(pₙ)`. -/
theorem fiber_sum {s : BoundingSieve} {side D c : ℕ}
    (hc : c ∣ s.prodPrimes) (hviol : isViolPrefix side D c) :
    ∑ d ∈ ((divisors s.prodPrimes).filter (fun d => ¬ rosserCond side D d)).filter
        (fun d => prefixMap side D d = c), (μ d : ℝ) * s.nu d
      = (μ c : ℝ) * s.nu c * Vbelow s (rmin c) := by
  have hc0 : c ≠ 0 := (s.prodPrimes_squarefree.squarefree_of_dvd hc).ne_zero
  have hPb0 : Pbelow s (rmin c) ≠ 0 := Pbelow_ne_zero s (rmin c)
  have key : ∑ d ∈ ((divisors s.prodPrimes).filter (fun d => ¬ rosserCond side D d)).filter
        (fun d => prefixMap side D d = c), (μ d : ℝ) * s.nu d
      = ∑ e ∈ (Pbelow s (rmin c)).divisors, (μ (c * e) : ℝ) * s.nu (c * e) := by
    refine Finset.sum_nbij' (i := fun d => rsuffix d (fvLen side D d)) (j := fun e => c * e)
      ?hi ?hj ?left ?right ?h
    case hi =>
      intro d hd
      obtain ⟨hdX, hpm⟩ := Finset.mem_filter.mp hd
      obtain ⟨hddvd, hncond⟩ := Finset.mem_filter.mp hdX
      have hne := (not_rosserCond_iff_failIdx side D d).mp hncond
      obtain ⟨htail, _⟩ := tail_of_fiber (Nat.mem_divisors.mp hddvd).1 hne
      rw [hpm] at htail
      exact Nat.mem_divisors.mpr ⟨htail, hPb0⟩
    case hj =>
      intro e he
      have he' : e ∣ Pbelow s (rmin c) := (Nat.mem_divisors.mp he).1
      obtain ⟨hdvd, hncond, hpm⟩ := mul_tail_mem_fiber hc hviol he'
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdvd, s.prodPrimes_squarefree.ne_zero⟩, hncond⟩, hpm⟩
    case left =>
      intro d hd
      obtain ⟨hdX, hpm⟩ := Finset.mem_filter.mp hd
      obtain ⟨hddvd, hncond⟩ := Finset.mem_filter.mp hdX
      have hne := (not_rosserCond_iff_failIdx side D d).mp hncond
      obtain ⟨_, hsplit⟩ := tail_of_fiber (Nat.mem_divisors.mp hddvd).1 hne
      rw [← hpm]; exact hsplit
    case right =>
      intro e he
      have he' : e ∣ Pbelow s (rmin c) := (Nat.mem_divisors.mp he).1
      obtain ⟨hdvd, hncond, hpm⟩ := mul_tail_mem_fiber hc hviol he'
      have hne := (not_rosserCond_iff_failIdx side D (c * e)).mp hncond
      obtain ⟨_, hsplit⟩ := tail_of_fiber hdvd hne
      rw [hpm] at hsplit
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) hsplit
    case h =>
      intro d hd
      obtain ⟨hdX, hpm⟩ := Finset.mem_filter.mp hd
      obtain ⟨hddvd, hncond⟩ := Finset.mem_filter.mp hdX
      have hne := (not_rosserCond_iff_failIdx side D d).mp hncond
      obtain ⟨_, hsplit⟩ := tail_of_fiber (Nat.mem_divisors.mp hddvd).1 hne
      have hcd : c * rsuffix d (fvLen side D d) = d := by rw [← hpm]; exact hsplit
      rw [hcd]
  rw [key]
  have hfactor : ∀ e ∈ (Pbelow s (rmin c)).divisors,
      (μ (c * e) : ℝ) * s.nu (c * e) = ((μ c : ℝ) * s.nu c) * ((μ e : ℝ) * s.nu e) := by
    intro e he
    have he' : e ∣ Pbelow s (rmin c) := (Nat.mem_divisors.mp he).1
    have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
    have hcop : Nat.Coprime c e :=
      coprime_of_primeFactors_lt hc0 he0 (tail_primeFactors_lt he')
    have hmu : (μ (c * e) : ℝ) = (μ c : ℝ) * (μ e : ℝ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]; push_cast; ring
    have hnu : s.nu (c * e) = s.nu c * s.nu e := s.nu_mult.map_mul_of_coprime hcop
    rw [hmu, hnu]; ring
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum, Vbelow_eq]

/-- **The Buchstab decomposition identity** (BJS Proposition 13, prefix form).  The
Rosser-violating Möbius defect reorganises exactly as a signed sum over violating prefixes,
each carrying `μ(c)·ν(c)·V(pₙ)`.  This is the combinatorial heart of the main-term
comparison — floor B of C1c″. -/
theorem buchstab_defect (s : BoundingSieve) (side D : ℕ) (h : side = 1 ∨ side = 2) :
    Salt.BrunLower.W s - s.mainSum (rosserSquarefreeSieve side D h).lam
      = ∑ c ∈ (divisors s.prodPrimes).filter (isViolPrefix side D),
          (μ c : ℝ) * s.nu c * Vbelow s (rmin c) := by
  rw [mainSum_lam_defect]
  -- reduce the defect to the Möbius sum over Rosser-violating divisors
  have hstep1 : ∑ d ∈ divisors s.prodPrimes,
        (μ d : ℝ) * (if (rosserSquarefreeSieve side D h).P d then 0 else 1) * s.nu d
      = ∑ d ∈ (divisors s.prodPrimes).filter (fun d => ¬ rosserCond side D d),
          (μ d : ℝ) * s.nu d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdsf : Squarefree d := s.prodPrimes_squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    by_cases hcond : rosserCond side D d
    · simp [rosserSquarefreeSieve_P, hcond, hdsf]
    · simp [rosserSquarefreeSieve_P, hcond]
  rw [hstep1]
  -- fiber over the first-violation prefix
  have hmaps : ∀ d ∈ (divisors s.prodPrimes).filter (fun d => ¬ rosserCond side D d),
      prefixMap side D d ∈ (divisors s.prodPrimes).filter (isViolPrefix side D) := by
    intro d hd
    obtain ⟨hddvd, hncond⟩ := Finset.mem_filter.mp hd
    have hddvd' : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hddvd).1
    have hdsf : Squarefree d := s.prodPrimes_squarefree.squarefree_of_dvd hddvd'
    have hne := (not_rosserCond_iff_failIdx side D d).mp hncond
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, s.prodPrimes_squarefree.ne_zero⟩,
      isViolPrefix_prefixMap hne⟩
    have hdvd : prefixMap side D d ∣ d :=
      ⟨rsuffix d (fvLen side D d), (rprefix_mul_rsuffix hdsf (fvLen side D d)).symm⟩
    exact hdvd.trans hddvd'
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun d => (μ d : ℝ) * s.nu d)]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  obtain ⟨hcdvd, hcviol⟩ := Finset.mem_filter.mp hc
  exact fiber_sum (Nat.mem_divisors.mp hcdvd).1 hcviol

/-! ## Part E — the signed `Tₙ` form (BJS Proposition 13)

Grouping the violating prefixes by chain depth `n = ω(c)` folds `μ(c) = (−1)ⁿ` into the
alternating sign, giving `mainSum λ⁺ = V(z) + Σ_{n odd} Tₙ` and
`mainSum λ⁻ = V(z) − Σ_{n even} Tₙ` (the exact Prop-13 shape). -/

/-- The maximal chain depth (`ω(P(z))`), an a-priori bound on any prefix's length. -/
noncomputable def maxDepth (s : BoundingSieve) : ℕ := s.prodPrimes.primeFactors.card

/-- **The `n`-th Buchstab term** `Tₙ = Σ_{chains of depth n, first-violating at n} ν·V(pₙ)`
(BJS (28), divisor form): the sum of `ν(c)·V(pₙ)` over violating prefixes `c` of length `n`. -/
noncomputable def T (s : BoundingSieve) (side D n : ℕ) : ℝ :=
  ∑ c ∈ (divisors s.prodPrimes).filter
      (fun c => isViolPrefix side D c ∧ (rlist c).length = n),
    s.nu c * Vbelow s (rmin c)

/-- Each `Tₙ ≥ 0` (a sum of `ν(c)·V(pₙ) > 0`). -/
theorem T_nonneg (s : BoundingSieve) (side D n : ℕ) : 0 ≤ T s side D n := by
  refine Finset.sum_nonneg (fun c hc => ?_)
  obtain ⟨hcdvd, _⟩ := Finset.mem_filter.mp hc
  exact mul_nonneg (nu_pos_of_dvd_prodPrimes (Nat.mem_divisors.mp hcdvd).1).le
    (Vbelow_pos s (rmin c)).le

/-- The depth-`n` slice of the prefix sum equals `(−1)ⁿ·Tₙ` (folding `μ(c) = (−1)ⁿ`). -/
theorem inner_eq (s : BoundingSieve) (side D n : ℕ) :
    ∑ c ∈ (divisors s.prodPrimes).filter
        (fun c => isViolPrefix side D c ∧ (rlist c).length = n),
        (μ c : ℝ) * s.nu c * Vbelow s (rmin c)
      = (-1 : ℝ) ^ n * T s side D n := by
  rw [T, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  obtain ⟨hcdvd, _, hlen⟩ := Finset.mem_filter.mp hc
  have hcsf : Squarefree c :=
    s.prodPrimes_squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hcdvd).1
  have hmu : (μ c : ℝ) = (-1 : ℝ) ^ n := by
    rw [Salt.BrunLower.moebius_real_of_squarefree hcsf, ← rlist_length, hlen]
  rw [hmu]; ring

/-- **BJS Proposition 13, upper.**  `mainSum λ⁺ = V(z) + Σ_{n odd} Tₙ`. -/
theorem buchstab_upper (s : BoundingSieve) (D : ℕ) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      = Salt.BrunLower.W s +
        ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), T s 1 D n := by
  have hdef := buchstab_defect s 1 D (Or.inl rfl)
  have hmaps : ∀ c ∈ (divisors s.prodPrimes).filter (isViolPrefix 1 D),
      (rlist c).length ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n) := by
    intro c hc
    obtain ⟨hcdvd, hcviol⟩ := Finset.mem_filter.mp hc
    have hle : (rlist c).length ≤ maxDepth s := by
      rw [rlist_length, maxDepth]
      exact Finset.card_le_card (Nat.primeFactors_mono (Nat.mem_divisors.mp hcdvd).1
        s.prodPrimes_squarefree.ne_zero)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.odd_iff.mpr hcviol.2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun c => (μ c : ℝ) * s.nu c * Vbelow s (rmin c))] at hdef
  have hstep : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
      (∑ c ∈ (divisors s.prodPrimes).filter (isViolPrefix 1 D) with (rlist c).length = n,
        (μ c : ℝ) * s.nu c * Vbelow s (rmin c)) = - T s 1 D n := by
    intro n hn
    have hodd : Odd n := (Finset.mem_filter.mp hn).2
    rw [Finset.filter_filter, inner_eq, hodd.neg_one_pow]; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib] at hdef
  linarith [hdef]

/-- **BJS Proposition 13, lower.**  `mainSum λ⁻ = V(z) − Σ_{n even} Tₙ`. -/
theorem buchstab_lower (s : BoundingSieve) (D : ℕ) :
    s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam
      = Salt.BrunLower.W s -
        ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), T s 2 D n := by
  have hdef := buchstab_defect s 2 D (Or.inr rfl)
  have hmaps : ∀ c ∈ (divisors s.prodPrimes).filter (isViolPrefix 2 D),
      (rlist c).length ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n) := by
    intro c hc
    obtain ⟨hcdvd, hcviol⟩ := Finset.mem_filter.mp hc
    have hle : (rlist c).length ≤ maxDepth s := by
      rw [rlist_length, maxDepth]
      exact Finset.card_le_card (Nat.primeFactors_mono (Nat.mem_divisors.mp hcdvd).1
        s.prodPrimes_squarefree.ne_zero)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.even_iff.mpr hcviol.2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun c => (μ c : ℝ) * s.nu c * Vbelow s (rmin c))] at hdef
  have hstep : ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n),
      (∑ c ∈ (divisors s.prodPrimes).filter (isViolPrefix 2 D) with (rlist c).length = n,
        (μ c : ℝ) * s.nu c * Vbelow s (rmin c)) = T s 2 D n := by
    intro n hn
    have heven : Even n := (Finset.mem_filter.mp hn).2
    rw [Finset.filter_filter, inner_eq, heven.neg_one_pow]; ring
  rw [Finset.sum_congr rfl hstep] at hdef
  linarith [hdef]

/-! ## Part F — the `hmain` compiler-plugs (BJS Theorem 6 (5)/(6))

The upper/lower `hmain` inequalities of C1c′'s `linear_sieve_{upper,lower}_rosser` are
assembled from the Prop-13 identity and the **analytic `Tₙ`-sum bound** (BJS Lemma 11 +
Lemma 12 — the chain-to-integral induction through hypothesis (4) and the `τₙ` geometric
close), which enters here as the single named hypothesis `hTbound` (the analytic heart,
deferred; see the flag).  The `fseq`-tail (BJS `F(s) = Fchain N + tail`, C1b) and the
`hbar → hBJS` reconciliation are absorbed into `hTbound`'s `ε·Cᵢ·e²·hBJS` slack, matching
the C0 ledger's S1/S2 budget.  These plug directly (compiler-verified) into
`linear_sieve_upper_rosser` / `linear_sieve_lower_rosser`. -/

/-- **`hmain` (upper), assembled.**  From the analytic bound on the odd Buchstab tail
`Σ_{n odd} Tₙ ≤ V(z)·(Fchain N − 1 + εC₁e²h)` (BJS Lemma 11/12) and Prop 13, the upper
main-term comparison of BJS Theorem 6 (5) follows. -/
theorem hmain_upper (s : BoundingSieve) (D N : ℕ) (sparam ε C₁ : ℝ)
    (hTbound : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), T s 1 D n
      ≤ Salt.BrunLower.W s * (Fchain N sparam - 1 + ε * C₁ * Real.exp 2 * hBJS sparam)) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s * (Fchain N sparam + ε * C₁ * Real.exp 2 * hBJS sparam) := by
  rw [buchstab_upper]
  have hW := Salt.BrunLower.W_pos s
  calc Salt.BrunLower.W s
        + ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), T s 1 D n
      ≤ Salt.BrunLower.W s
        + Salt.BrunLower.W s * (Fchain N sparam - 1 + ε * C₁ * Real.exp 2 * hBJS sparam) := by
        linarith [hTbound]
    _ = Salt.BrunLower.W s * (Fchain N sparam + ε * C₁ * Real.exp 2 * hBJS sparam) := by ring

/-- **`hmain` (lower), assembled.**  From the analytic bound on the even Buchstab tail
`Σ_{n even} Tₙ ≤ V(z)·(1 − fchain N + εC₂e²h)` (BJS Lemma 11/12) and Prop 13, the lower
main-term comparison of BJS Theorem 6 (6) follows. -/
theorem hmain_lower (s : BoundingSieve) (D N : ℕ) (sparam ε C₂ : ℝ)
    (hTbound : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), T s 2 D n
      ≤ Salt.BrunLower.W s * (1 - fchain N sparam + ε * C₂ * Real.exp 2 * hBJS sparam)) :
    Salt.BrunLower.W s * (fchain N sparam - ε * C₂ * Real.exp 2 * hBJS sparam)
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam := by
  rw [buchstab_lower]
  calc Salt.BrunLower.W s * (fchain N sparam - ε * C₂ * Real.exp 2 * hBJS sparam)
      = Salt.BrunLower.W s
        - Salt.BrunLower.W s * (1 - fchain N sparam + ε * C₂ * Real.exp 2 * hBJS sparam) := by ring
    _ ≤ Salt.BrunLower.W s
        - ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), T s 2 D n := by
        linarith [hTbound]

/-- **Compiler-plug demonstrator (upper).**  Feeding `hmain_upper` into
`linear_sieve_upper_rosser` yields BJS Theorem 6 (5) modulo the analytic `hTbound`, the
level `2 ≤ D`, `0 ≤ totalMass`, and `1 ≤ Q`. -/
theorem linear_sieve_upper_rosser_assembled (s : BoundingSieve) (D : ℕ) (hD : 2 ≤ D)
    (htm : 0 ≤ s.totalMass) (N : ℕ) (sparam ε C₁ Q : ℝ) (hQ : 1 ≤ Q)
    (hTbound : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), T s 1 D n
      ≤ Salt.BrunLower.W s * (Fchain N sparam - 1 + ε * C₁ * Real.exp 2 * hBJS sparam)) :
    s.siftedSum
      ≤ s.totalMass * (Salt.BrunLower.W s *
          (Fchain N sparam + ε * C₁ * Real.exp 2 * hBJS sparam))
        + rosserRemainder s (Q * D) :=
  linear_sieve_upper_rosser s D hD htm N sparam ε C₁ Q hQ
    (hmain_upper s D N sparam ε C₁ hTbound)

/-- **Compiler-plug demonstrator (lower).**  Feeding `hmain_lower` into
`linear_sieve_lower_rosser` yields BJS Theorem 6 (6) modulo the analytic `hTbound`, the
smoothness `hz`, `z ≤ D` (from `D ≥ z²`), `0 ≤ totalMass`, and `1 ≤ Q`. -/
theorem linear_sieve_lower_rosser_assembled (s : BoundingSieve) (D z : ℕ) (hz2 : 2 ≤ z)
    (hzD : z ≤ D) (hz : ∀ p ∈ s.prodPrimes.primeFactors, p < z) (htm : 0 ≤ s.totalMass)
    (N : ℕ) (sparam ε C₂ Q : ℝ) (hQ : 1 ≤ Q)
    (hTbound : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), T s 2 D n
      ≤ Salt.BrunLower.W s * (1 - fchain N sparam + ε * C₂ * Real.exp 2 * hBJS sparam)) :
    s.totalMass * (Salt.BrunLower.W s *
        (fchain N sparam - ε * C₂ * Real.exp 2 * hBJS sparam))
      - rosserRemainder s (Q * D) ≤ s.siftedSum :=
  linear_sieve_lower_rosser s D z hz2 hzD hz htm N sparam ε C₂ Q hQ
    (hmain_lower s D N sparam ε C₂ hTbound)

/-! ## Part G — the `hbar → hBJS` majorant bridge (the flagged design check)

`LinearSieve.hmain` is phrased against BJS's piecewise `hBJS`; C1b's per-level bounds
(`fseq_le`) are against the exponential majorant `hbar` (decay rate `6/5`).  Since `hbar`
decays *strictly faster*, `hbar s ≤ hBJS s` everywhere, so an `hbar`-slack upper bound is a
fortiori an `hBJS`-slack bound — the correct direction for both endpoints.  This lets the
(deferred) analytic Lemma 11, which produces `hbar`-form bounds, discharge the `hBJS`-form
`hTbound` of `hmain_upper`/`hmain_lower`.  The `s > 3` (lower-endpoint) case is the one
needing the degree-2 exponential bound `mathlib.quadratic_le_exp_of_nonneg`. -/

/-- **The majorant bridge** `hbar s ≤ hBJS s` for all `s` (equal on `s ≤ 2`; strictly
tighter beyond, since `hbar`'s rate `6/5 > 1`).  On `s > 3` the tail form `3s⁻¹e⁻ˢ`
dominates via `(s−2)·e^{−(s−2)/5} ≤ 3` (a degree-2 `exp` bound). -/
theorem hbar_le_hBJS (s : ℝ) : hbar s ≤ hBJS s := by
  unfold hBJS
  split_ifs with h2 h3
  · exact le_of_eq (hbar_lo h2)
  · rw [hbar_hi (not_le.mp h2).le]
    exact Real.exp_le_exp.mpr (by linarith [not_le.mp h2])
  · -- s > 3 : hbar ≤ 3 s⁻¹ e⁻ˢ
    have hs3 : (3 : ℝ) < s := not_le.mp h3
    have hs0 : (0 : ℝ) < s := by linarith
    rw [hbar_hi (by linarith)]
    have hexpid : Real.exp (-2 - (6 / 5) * (s - 2))
        = Real.exp (-s) * Real.exp (-(1 / 5) * (s - 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexpid]
    have hq := Real.quadratic_le_exp_of_nonneg (x := (1 / 5) * (s - 2)) (by linarith)
    -- `s · e^{−(s−2)/5} ≤ 3` via the degree-2 lower bound on `exp`
    have hkey2 : s * Real.exp (-(1 / 5) * (s - 2)) ≤ 3 := by
      have hexpinv : Real.exp (-(1 / 5) * (s - 2)) = (Real.exp ((1 / 5) * (s - 2)))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [hexpinv, mul_inv_le_iff₀ (Real.exp_pos _)]
      calc s ≤ 3 * (1 + (1 / 5) * (s - 2) + ((1 / 5) * (s - 2)) ^ 2 / 2) := by
            nlinarith [sq_nonneg (3 * (s - 2) - 10)]
        _ ≤ 3 * Real.exp ((1 / 5) * (s - 2)) := by
            exact mul_le_mul_of_nonneg_left hq (by norm_num)
    have hkey : Real.exp (-(1 / 5) * (s - 2)) ≤ 3 * s⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hkey2 (inv_pos.mpr hs0).le
      rw [← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul, mul_comm s⁻¹ (3 : ℝ)] at h
      exact h
    calc Real.exp (-s) * Real.exp (-(1 / 5) * (s - 2))
        ≤ Real.exp (-s) * (3 * s⁻¹) :=
          mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
      _ = 3 * s⁻¹ * Real.exp (-s) := by ring

end Salt.Chen
