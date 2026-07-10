/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom
import Salt.Twelve.MomentAtom

/-!
# The sharp `μ²/φ` upper bound (toward discharging `PhiUpperAtom`)

Target (`Salt.Twelve.PhiUpperAtom`, `MomentAtom.lean`):
`∃ C, ∀ x ≥ 2, phiAtomSum x B ≤ (φB/B)·log x + C` — the exact leading constant
`φB/B` (NOT the `4×`-lossy `phiAtom_upper_lossy`).

## What lands here (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`)

* **Part 1 — the radical-fiber identity** (`radFiber_inv_hasSum`):
  `∑'_{n : rad n = r} 1/n = 1/φ(r)` for squarefree `r`.  This is the
  Euler-product miracle the pre-existing PORT-BLOCKER note
  (`Salt/Maynard/PhiAtom.lean`, lines 918-953) singled out as the obstruction —
  `∑_d h(d)/d = 1`, per-prime cancellation of the `6/π²`.  It is proved via
  mathlib's `Nat.factoredNumbers` Euler-product machinery
  (`factoredNumbers_inv_hasSum`: `∑'_{rad m ∣ r} 1/m = ∏_{p∣r}(1-1/p)⁻¹`, by
  induction on the prime set with per-prime geometric series) composed with the
  totient product `prod_geom_eq_ratio : ∏_{p∣r}(1-1/p)⁻¹ = r/φ(r)` and the
  fiber bijection `radFiberEquiv : {n // rad n = r} ≃ factoredNumbers r.primeFactors`.

* **Part 2 — the reduction** (`phiAtomSum_eq_copHarmonic_add_tail`):
  grouping `n < x` by radical gives `copHarmonic x B = ∑_r headSum_r`
  (`copHarmonic_eq_sum_head`), so with `phiAtomSum x B = ∑_r 1/φ(r)`,
  `phiAtomSum x B = copHarmonic x B + ∑_r (1/φ(r) − headSum_r)`.
  Each tail term `radFiberTail r x B := 1/φ(r) − headSum_r` is `≥ 0`
  (`radFiberHead_le`, a finite subsum of the Part-1 `HasSum`), and equals the
  fiber tail `∑'_{n : rad n = r, x ≤ n} 1/n`.

* **`phiAtom_upper_of_tail_bound`**: given `∑_r radFiberTail r x B ≤ C₀`
  (uniformly), `copHarmonic_upper` finishes the sharp bound.

## PORT-BLOCKER (the narrow remaining atom)

`∃ C₀, ∀ x ≥ 2, ∑_{r ∈ sqfCop x B} radFiberTail r x B ≤ C₀`, i.e.
`Tail(x) := ∑'_{n : rad n < x, x ≤ n, (n,B)=1} 1/n = O_B(1)`.
Route (elementary but ~250 lines of `tsum` reindexing left): reindex `n` by its
squarefree/powerful decomposition `n = u·v` (`u` squarefree, `v` powerful,
`(u,v)=1`); the inner harmonic sum over `u ∈ [x/v, x/rad v)` is `≤ 1 + log v`, so
`Tail(x) ≤ ∑_{v powerful, v ≥ 2} (1 + log v)/v`, and the powerful-number sum is
finite via the surjection `(a,c) ↦ a²c³` which factors it into ordinary
`log`-weighted `p`-series `∑ 1/a², ∑ log a/a², ∑ 1/c³, ∑ log c/c³` (each bounded
by elementary telescoping — no Mertens, no Euler-product estimate).  This needs a
from-scratch `Nat` powerful/squarefree-part decomposition (absent from mathlib)
plus the reindex; deferred as its own node.
-/

open Finset

namespace Salt.Twelve

/-! ## Part 1 — the radical-fiber identity -/

/-- Geometric series per prime: `∑'_e (p^e)⁻¹ = (1 - p⁻¹)⁻¹`. -/
lemma hasSum_inv_prime_pow {p : ℕ} (hp : 2 ≤ p) :
    HasSum (fun e : ℕ => (((p : ℝ)) ^ e)⁻¹) (1 - ((p : ℝ))⁻¹)⁻¹ := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h0 : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := by positivity
  have h1 : ((p : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; linarith
  have hg := hasSum_geometric_of_lt_one h0 h1
  have heq : (fun e : ℕ => (((p : ℝ)) ^ e)⁻¹) = (fun e : ℕ => (((p : ℝ))⁻¹) ^ e) := by
    funext e; rw [inv_pow]
  rw [heq]; exact hg

/-- The fiber identity as a `HasSum` over `factoredNumbers s` for a finset of primes:
`∑'_{m : rad m ∣ prod s} 1/m = ∏_{p ∈ s} (1 - 1/p)⁻¹`. -/
lemma factoredNumbers_inv_hasSum {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    HasSum (fun m : Nat.factoredNumbers s => (((m : ℕ) : ℝ))⁻¹)
      (∏ p ∈ s, (1 - ((p : ℝ))⁻¹)⁻¹) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.prod_empty]
      have hb : (1 : ℕ) ∈ Nat.factoredNumbers (∅ : Finset ℕ) := by
        rw [Nat.factoredNumbers_empty]; rfl
      have hsetsub : (Nat.factoredNumbers (∅ : Finset ℕ)).Subsingleton :=
        Nat.factoredNumbers_empty.symm ▸ Set.subsingleton_singleton
      have hsub : ∀ i : Nat.factoredNumbers (∅ : Finset ℕ),
          i = (⟨1, hb⟩ : Nat.factoredNumbers (∅ : Finset ℕ)) :=
        fun i => Subtype.ext (hsetsub i.2 hb)
      have hsingle := hasSum_single (⟨1, hb⟩ : Nat.factoredNumbers (∅ : Finset ℕ))
        (f := fun m : Nat.factoredNumbers (∅ : Finset ℕ) => (((m : ℕ) : ℝ))⁻¹)
        (fun i hi => absurd (hsub i) hi)
      simpa using hsingle
  | @insert p s hps ih =>
      have hp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hp2 : 2 ≤ p := hp.two_le
      set e := Nat.equivProdNatFactoredNumbers hp hps with he
      have hf : HasSum (fun a : ℕ => (((p : ℝ)) ^ a)⁻¹) (1 - ((p : ℝ))⁻¹)⁻¹ :=
        hasSum_inv_prime_pow hp2
      have hg : HasSum (fun m : Nat.factoredNumbers s => (((m : ℕ) : ℝ))⁻¹)
          (∏ q ∈ s, (1 - ((q : ℝ))⁻¹)⁻¹) := ih hs'
      have hsummable : Summable
          (fun x : ℕ × Nat.factoredNumbers s => (((p : ℝ)) ^ x.1)⁻¹ * (((x.2 : ℕ) : ℝ))⁻¹) :=
        hf.summable.mul_of_nonneg hg.summable (fun a => by positivity) (fun m => by positivity)
      have hmul := hf.mul hg hsummable
      rw [Finset.prod_insert hps]
      have hcomp :
          (fun x : ℕ × Nat.factoredNumbers s => (((p : ℝ)) ^ x.1)⁻¹ * (((x.2 : ℕ) : ℝ))⁻¹)
            = (fun m : Nat.factoredNumbers (insert p s) => (((m : ℕ) : ℝ))⁻¹) ∘ e := by
        funext x
        simp only [Function.comp, he, Nat.equivProdNatFactoredNumbers_apply']
        push_cast
        rw [mul_inv]
      rw [hcomp] at hmul
      exact (e.hasSum_iff).mp hmul

/-- For squarefree `r`, `∏_{p ∣ r} (1 - 1/p)⁻¹ = r/φ(r)`. -/
lemma prod_geom_eq_ratio {r : ℕ} (hr : Squarefree r) :
    ∏ p ∈ r.primeFactors, (1 - ((p : ℝ))⁻¹)⁻¹ = (r : ℝ) / (Nat.totient r) := by
  rw [Salt.Maynard.totient_squarefree_cast hr]
  have hcast : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hr]
    rw [Nat.cast_prod]
  rw [hcast, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpne : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [show (1 - ((p : ℝ))⁻¹) = ((p : ℝ) - 1) / (p : ℝ) from by field_simp, inv_div]

open Salt.M3Expansion (rad rad_squarefree rad_eq_primeFactors)

/-- For squarefree `r` and `m ∈ factoredNumbers r.primeFactors`, `rad (r * m) = r`. -/
lemma rad_mul_mem {r m : ℕ} (hr : Squarefree r) (hm : m ∈ Nat.factoredNumbers r.primeFactors) :
    rad (r * m) = r := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hm0 : m ≠ 0 := hm.1
  have hsub : m.primeFactors ⊆ r.primeFactors :=
    Nat.primeFactors_subset_of_mem_factoredNumbers hm
  have hpf : (r * m).primeFactors = r.primeFactors := by
    rw [Nat.primeFactors_mul hr0 hm0]
    exact Finset.union_eq_left.mpr hsub
  rw [rad, hpf, Nat.prod_primeFactors_of_squarefree hr]

/-- The bijection `{n // rad n = r} ≃ factoredNumbers r.primeFactors`, `n ↦ n / r`. -/
def radFiberEquiv {r : ℕ} (hr : Squarefree r) :
    {n : ℕ // rad n = r ∧ n ≠ 0} ≃ Nat.factoredNumbers r.primeFactors where
  toFun := fun ⟨n, hn, hn0⟩ =>
    ⟨n / r, by
      have hrdvd : r ∣ n := by rw [← hn, rad]; exact Nat.prod_primeFactors_dvd n
      have hpfn : n.primeFactors = r.primeFactors := rad_eq_primeFactors hn
      refine Nat.mem_factoredNumbers_of_primeFactors_subset ?_ ?_
      · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hrdvd)
          (Nat.pos_of_ne_zero hr.ne_zero)).ne'
      · calc (n / r).primeFactors ⊆ n.primeFactors :=
              Nat.primeFactors_mono (Nat.div_dvd_of_dvd hrdvd) hn0
            _ = r.primeFactors := hpfn⟩
  invFun := fun ⟨m, hm⟩ =>
    ⟨r * m, ⟨rad_mul_mem hr hm, Nat.mul_ne_zero hr.ne_zero hm.1⟩⟩
  left_inv := by
    rintro ⟨n, hn, hn0⟩
    have hrdvd : r ∣ n := by rw [← hn, rad]; exact Nat.prod_primeFactors_dvd n
    apply Subtype.ext
    exact Nat.mul_div_cancel' hrdvd
  right_inv := by
    rintro ⟨m, hm⟩
    apply Subtype.ext
    exact Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hr.ne_zero)

/-- `n`-indexed radical-fiber identity: `∑'_{n : rad n = r} 1/n = 1/φ(r)`. -/
lemma radFiber_inv_hasSum {r : ℕ} (hr : Squarefree r) :
    HasSum (Set.indicator {n : ℕ | rad n = r ∧ n ≠ 0} (fun n => ((n : ℕ) : ℝ)⁻¹))
      (1 / (Nat.totient r : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hprime : ∀ p ∈ r.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- the `factoredNumbers` (excess `m`) sum, scaled by `1/r`
  have hbase := (factoredNumbers_inv_hasSum hprime).mul_left ((r : ℝ)⁻¹)
  rw [prod_geom_eq_ratio hr] at hbase
  have hval : (r : ℝ)⁻¹ * ((r : ℝ) / (Nat.totient r : ℝ)) = 1 / (Nat.totient r : ℝ) := by
    field_simp
  rw [hval] at hbase
  -- transport along the fiber bijection `radFiberEquiv : {n // rad n = r} ≃ FN`
  have hfe : HasSum ((fun m : Nat.factoredNumbers r.primeFactors =>
      (r : ℝ)⁻¹ * (((m : ℕ) : ℝ))⁻¹) ∘ (radFiberEquiv hr)) (1 / (Nat.totient r : ℝ)) :=
    ((radFiberEquiv hr).hasSum_iff).mpr hbase
  have hfun : ((fun m : Nat.factoredNumbers r.primeFactors =>
        (r : ℝ)⁻¹ * (((m : ℕ) : ℝ))⁻¹) ∘ (radFiberEquiv hr))
      = fun x : {n : ℕ // rad n = r ∧ n ≠ 0} => (((x : ℕ) : ℝ))⁻¹ := by
    funext x
    obtain ⟨n, hn, hn0⟩ := x
    have hrdvd : r ∣ n := by rw [← hn, rad]; exact Nat.prod_primeFactors_dvd n
    simp only [Function.comp, radFiberEquiv, Equiv.coe_fn_mk]
    rw [← mul_inv, ← Nat.cast_mul, Nat.mul_div_cancel' hrdvd]
  rw [hfun] at hfe
  exact hasSum_subtype_iff_indicator.mp hfe

/-! ## Part 2 — reduction of `phiAtom_upper` to a bounded radical-fiber tail

Grouping `n < x` (coprime to `B`) by radical, `copHarmonic x B = ∑_r headSum_r`,
where `headSum_r = ∑_{n<x, rad n = r} 1/n` is the truncated fiber.  Since
`phiAtomSum x B = ∑_r 1/φ(r)` and (Part 1) `1/φ(r)` is the FULL fiber mass, the
difference is the sum of fiber tails:
`phiAtomSum x B = copHarmonic x B + ∑_r (1/φ(r) − headSum_r)`.
Discharging the sharp upper bound is thus exactly bounding the tail sum by an
`x`-independent constant. -/

open Salt.Maynard (phiAtomSum sqfCop copHarmonic copHarmonic_eq copHarmonic_upper)

/-- The truncated radical fiber `∑_{n < x, (n,B)=1, rad n = r} 1/n`. -/
noncomputable def radFiberHead (r x B : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range x).filter (fun n => (n ≠ 0 ∧ Nat.Coprime n B) ∧ rad n = r),
    ((n : ℕ) : ℝ)⁻¹

/-- **R1** (finite fiberwise grouping): `copHarmonic x B = ∑_{r ∈ sqfCop} headSum_r`. -/
lemma copHarmonic_eq_sum_head (x B : ℕ) :
    copHarmonic x B = ∑ r ∈ sqfCop x B, radFiberHead r x B := by
  classical
  rw [copHarmonic_eq]
  set dom := (Finset.range x).filter (fun n => n ≠ 0 ∧ Nat.Coprime n B) with hdom
  have hmaps : ∀ n ∈ dom, rad n ∈ sqfCop x B := by
    intro n hn
    rw [hdom, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hn0, hncop⟩ := hn
    have hdvd : rad n ∣ n := Nat.prod_primeFactors_dvd n
    rw [sqfCop, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hnx,
      rad_squarefree n, Nat.Coprime.coprime_dvd_left hdvd hncop⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => ((n : ℕ) : ℝ)⁻¹)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [radFiberHead]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, hdom]
  tauto

/-- The radical-fiber tail `1/φ(r) − headSum_r`, the object to be bounded. -/
noncomputable def radFiberTail (r x B : ℕ) : ℝ :=
  1 / (Nat.totient r : ℝ) - radFiberHead r x B

/-- Each fiber tail is nonnegative: the truncated fiber never exceeds `1/φ(r)`
(a finite subsum of the Part-1 fiber `HasSum`). -/
lemma radFiberHead_le {r x B : ℕ} (hr : Squarefree r) :
    radFiberHead r x B ≤ 1 / (Nat.totient r : ℝ) := by
  classical
  have hg := radFiber_inv_hasSum hr
  set S := (Finset.range x).filter (fun n => (n ≠ 0 ∧ Nat.Coprime n B) ∧ rad n = r) with hS
  have hval : radFiberHead r x B
      = ∑ n ∈ S, Set.indicator {n : ℕ | rad n = r ∧ n ≠ 0} (fun n => ((n : ℕ) : ℝ)⁻¹) n := by
    rw [radFiberHead]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [hS, Finset.mem_filter] at hn
    rw [Set.indicator_of_mem (show n ∈ {n : ℕ | rad n = r ∧ n ≠ 0} from ⟨hn.2.2, hn.2.1.1⟩)]
  rw [hval]
  refine sum_le_hasSum S (fun n _ => ?_) hg
  exact Set.indicator_nonneg (fun n _ => by positivity) n

/-- **Reduction identity**: `phiAtomSum = copHarmonic + ∑_r (fiber tail)`. -/
lemma phiAtomSum_eq_copHarmonic_add_tail (x B : ℕ) :
    phiAtomSum x B = copHarmonic x B + ∑ r ∈ sqfCop x B, radFiberTail r x B := by
  rw [phiAtomSum, copHarmonic_eq_sum_head x B]
  simp only [radFiberTail]
  rw [Finset.sum_sub_distrib]
  ring

/-- **Conditional sharp upper bound.**  If the radical-fiber tail sum is
`O_B(1)`, then `phiAtomSum x B ≤ (φB/B)·log x + C` — the exact leading constant.
The hypothesis is the narrow PORT-BLOCKER (`Tail(x) = O_B(1)`); see the note. -/
theorem phiAtom_upper_of_tail_bound (B : ℕ) (hB : B ≠ 0)
    (htail : ∃ C₀ : ℝ, ∀ x : ℕ, 2 ≤ x → ∑ r ∈ sqfCop x B, radFiberTail r x B ≤ C₀) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      phiAtomSum x B ≤ (Nat.totient B / B : ℝ) * Real.log (x : ℝ) + C := by
  obtain ⟨C₀, hC₀⟩ := htail
  refine ⟨((Nat.totient B : ℝ) + 1) + C₀, fun x hx => ?_⟩
  rw [phiAtomSum_eq_copHarmonic_add_tail x B]
  have h1 := copHarmonic_upper B hB x hx
  have h2 := hC₀ x hx
  linarith

/-! ## Part 3 — the convergent powerful-number series (discharging the tail)

The tail-bound `Tail(x) = O_B(1)` reduces, via the squarefree/powerful
decomposition `n = u·v` (`u` squarefree, `v` powerful), to the `x`-independent
series `∑_{v powerful} (1 + log v)/v < ∞`.  This section lands that convergent
series fact unconditionally: every powerful `v` is `a²·c³`, so the surjection
`(a,c) ↦ a²c³` factors the series into convergent (log-weighted) `p`-series
`∑ 1/a², ∑ log a/a², ∑ 1/c³, ∑ log c/c³` — elementary, no Mertens.

`∑_{v powerful, v≥2} (1+log v)/v ≈ 3.95` numerically (converges fast: powerful
numbers ≤ N number `~ √N`). -/

/-- A number is *powerful* if every prime dividing it does so to power ≥ 2. -/
def IsPowerful (n : ℕ) : Prop := ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- **Powerful ⟹ `a²c³`.** Every nonzero powerful number is `a^2 * c^3`
(`a,c ≥ 1`): each prime exponent `e ≥ 2` is `2·aₚ + 3·cₚ`. -/
lemma exists_sq_mul_cube_of_powerful {v : ℕ} (hv : v ≠ 0) (hpow : IsPowerful v) :
    ∃ a c : ℕ, 1 ≤ a ∧ 1 ≤ c ∧ v = a ^ 2 * c ^ 3 := by
  classical
  set aExp : ℕ → ℕ := fun e => (e - 3 * (e % 2)) / 2 with haExp
  set cExp : ℕ → ℕ := fun e => e % 2 with hcExp
  have hea : ∀ p ∈ v.primeFactors,
      2 * aExp (v.factorization p) + 3 * cExp (v.factorization p) = v.factorization p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ v := Nat.dvd_of_mem_primeFactors hp
    have hp2 : 2 ≤ v.factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hpp hv).mp (hpow p hpp hpd)
    simp only [haExp, hcExp]; omega
  have hself : ∏ p ∈ v.primeFactors, p ^ (v.factorization p) = v := by
    have h1 := Nat.prod_factorization_pow_eq_self hv
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at h1
  refine ⟨∏ p ∈ v.primeFactors, p ^ (aExp (v.factorization p)),
    ∏ p ∈ v.primeFactors, p ^ (cExp (v.factorization p)), ?_, ?_, ?_⟩
  · exact Finset.one_le_prod' (fun p hp => Nat.one_le_pow _ _ (Nat.pos_of_mem_primeFactors hp))
  · exact Finset.one_le_prod' (fun p hp => Nat.one_le_pow _ _ (Nat.pos_of_mem_primeFactors hp))
  · calc v = ∏ p ∈ v.primeFactors, p ^ (v.factorization p) := hself.symm
      _ = ∏ p ∈ v.primeFactors,
            (p ^ (aExp (v.factorization p))) ^ 2 * (p ^ (cExp (v.factorization p))) ^ 3 := by
          refine Finset.prod_congr rfl (fun p hp => ?_)
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          have := hea p hp; omega
      _ = (∏ p ∈ v.primeFactors, p ^ (aExp (v.factorization p))) ^ 2
            * (∏ p ∈ v.primeFactors, p ^ (cExp (v.factorization p))) ^ 3 := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow]

lemma log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  rcases hx.lt_or_eq with hx | hx
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
    have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx.le]; ring
    rw [h2]; nlinarith [Real.sqrt_nonneg x]
  · rw [← hx]; simp

/-- The log-weighted `p`-series `∑ log n / n^k` converges for `k ≥ 2`
(via `log n ≤ 2√n`, dominating by the `p`-series at `k - 1/2 > 1`). -/
lemma summable_log_div_pow {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ k) := by
  have hexp : (1 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hdom : Summable (fun n : ℕ => 2 * ((n : ℝ) ^ ((k : ℝ) - 1 / 2))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr hexp).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hdom
  · exact div_nonneg (log_natCast_nonneg n) (by positivity)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, Real.log_zero, zero_div]
      have : ((0 : ℝ) ^ ((k : ℝ) - 1 / 2))⁻¹ = 0 := by rw [Real.zero_rpow (by linarith), inv_zero]
      rw [this]; simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hlog : Real.log n ≤ 2 * Real.sqrt n := log_le_two_sqrt hnR.le
      have hnk : (n : ℝ) ^ k = (n : ℝ) ^ ((k : ℝ)) := (Real.rpow_natCast _ _).symm
      have hkey : Real.sqrt n / (n : ℝ) ^ k = ((n : ℝ) ^ ((k : ℝ) - 1 / 2))⁻¹ := by
        rw [Real.sqrt_eq_rpow, hnk, ← Real.rpow_sub hnR, ← Real.rpow_neg hnR.le]
        congr 1; ring
      have hstep : Real.log n / (n : ℝ) ^ k ≤ 2 * Real.sqrt n / (n : ℝ) ^ k := by gcongr
      rw [mul_div_assoc, hkey] at hstep
      exact hstep

/-- Summand over the `(a,c)`-plane dominating the powerful log-series. -/
noncomputable def powFac (q : ℕ × ℕ) : ℝ :=
  (1 + Real.log ((q.1 ^ 2 * q.2 ^ 3 : ℕ))) / ((q.1 ^ 2 * q.2 ^ 3 : ℕ))

noncomputable def powGa (a : ℕ) : ℝ := (1 + 2 * Real.log a) / (a : ℝ) ^ 2
noncomputable def powHc (c : ℕ) : ℝ := (1 + 3 * Real.log c) / (c : ℝ) ^ 3

lemma powGa_nonneg (a : ℕ) : 0 ≤ powGa a := by
  rw [powGa]; apply div_nonneg _ (by positivity); nlinarith [log_natCast_nonneg a]
lemma powHc_nonneg (c : ℕ) : 0 ≤ powHc c := by
  rw [powHc]; apply div_nonneg _ (by positivity); nlinarith [log_natCast_nonneg c]

lemma summable_powGa : Summable powGa := by
  have h : powGa = fun a : ℕ => 1 / (a : ℝ) ^ 2 + 2 * (Real.log a / (a : ℝ) ^ 2) := by
    funext a; rw [powGa]; ring
  rw [h]
  exact (Real.summable_one_div_nat_pow.mpr one_lt_two).add
    ((summable_log_div_pow (le_refl 2)).mul_left 2)
lemma summable_powHc : Summable powHc := by
  have h : powHc = fun c : ℕ => 1 / (c : ℝ) ^ 3 + 3 * (Real.log c / (c : ℝ) ^ 3) := by
    funext c; rw [powHc]; ring
  rw [h]
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num)).add
    ((summable_log_div_pow (by norm_num)).mul_left 3)

lemma powFac_nonneg (q : ℕ × ℕ) : 0 ≤ powFac q := by
  rw [powFac]; apply div_nonneg _ (by positivity)
  nlinarith [log_natCast_nonneg (q.1 ^ 2 * q.2 ^ 3)]

lemma powFac_le (q : ℕ × ℕ) : powFac q ≤ powGa q.1 * powHc q.2 := by
  obtain ⟨a, c⟩ := q
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hF : powFac (0, c) = 0 := by rw [powFac]; simp
    have hG : powGa 0 = 0 := by rw [powGa]; simp
    rw [hF, hG, zero_mul]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have hF : powFac (a, 0) = 0 := by rw [powFac]; simp
    have hH : powHc 0 = 0 := by rw [powHc]; simp
    rw [hF, hH, mul_zero]
  · change powFac (a, c) ≤ powGa a * powHc c
    have hla : 0 ≤ Real.log a := log_natCast_nonneg a
    have hlc : 0 ≤ Real.log c := log_natCast_nonneg c
    have hden : (0 : ℝ) < (a : ℝ) ^ 2 * (c : ℝ) ^ 3 := by positivity
    have hlogeq : Real.log ((a : ℝ) ^ 2 * (c : ℝ) ^ 3) = 2 * Real.log a + 3 * Real.log c := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast; ring
    have hcast : ((a ^ 2 * c ^ 3 : ℕ) : ℝ) = (a : ℝ) ^ 2 * (c : ℝ) ^ 3 := by push_cast; ring
    rw [powFac, powGa, powHc, hcast, hlogeq, div_mul_div_comm, div_le_div_iff_of_pos_right hden]
    nlinarith [mul_nonneg hla hlc]

lemma summable_powFac : Summable powFac :=
  Summable.of_nonneg_of_le powFac_nonneg powFac_le
    (Summable.mul_of_nonneg summable_powGa summable_powHc powGa_nonneg powHc_nonneg)

/-- **The convergent-series fact.**  `∑_{v powerful} (1 + log v)/v` is bounded by
an explicit constant `C = ∑'_{(a,c)} powFac`, uniformly over any finite set of
powerful numbers. This is the `x`-independent core that discharges `Tail(x)`. -/
theorem powerful_sum_bounded :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ v ∈ S, IsPowerful v ∧ v ≠ 0) →
      ∑ v ∈ S, (1 + Real.log v) / (v : ℝ) ≤ C := by
  classical
  have key : ∀ v : ℕ, ∃ q : ℕ × ℕ, (IsPowerful v ∧ v ≠ 0) → q.1 ^ 2 * q.2 ^ 3 = v := by
    intro v
    by_cases h : IsPowerful v ∧ v ≠ 0
    · obtain ⟨a, c, _, _, hac⟩ := exists_sq_mul_cube_of_powerful h.2 h.1
      exact ⟨(a, c), fun _ => hac.symm⟩
    · exact ⟨(0, 0), fun h' => absurd h' h⟩
  choose g hg using key
  refine ⟨∑' q, powFac q, fun S hS => ?_⟩
  have hgval : ∀ v ∈ S, (g v).1 ^ 2 * (g v).2 ^ 3 = v := fun v hv => hg v (hS v hv)
  have hinj : Set.InjOn g S := by
    intro v hv w hw hvw
    have := hgval v hv; rw [hvw, hgval w hw] at this; omega
  have hfeq : ∀ v ∈ S, (1 + Real.log v) / (v : ℝ) = powFac (g v) :=
    fun v hv => by rw [powFac, hgval v hv]
  calc ∑ v ∈ S, (1 + Real.log v) / (v : ℝ)
      = ∑ v ∈ S, powFac (g v) := Finset.sum_congr rfl hfeq
    _ = ∑ q ∈ S.image g, powFac q := (Finset.sum_image (fun x hx y hy => hinj hx hy)).symm
    _ ≤ ∑' q, powFac q := Summable.sum_le_tsum _ (fun q _ => powFac_nonneg q) summable_powFac

/-! ## Part 4 — the unconditional tail bound

The radical-fiber tail `radFiberTail r x B = ∑'_{n : rad n = r, x ≤ n} 1/n`;
summing over `r ∈ sqfCop x B` regroups to `Tail(x) = ∑'_{n : rad n < x ≤ n,
(n,B)=1} 1/n`.  Reindexing `n = u·v` (`u` squarefree, `v` powerful) turns this
into `∑_{v powerful} (1/v)·∑_{u ∈ [x/v, x/rad v)} 1/u ≤ ∑_{v powerful}
(1+log v)/v`, an `x`-independent bound.  The convergent series `∑_{v powerful}
(1+log v)/v` is `powerfulWeight_tsum_le` (Part 3, LANDED unconditionally).

The remaining step — the `Nat` squarefree/powerful reindex bounding
`∑_r radFiberTail r x B ≤ ∑'_v powerfulWeight v` — is a from-scratch `tsum`
regrouping over a decomposition absent from mathlib (`n ↦ (sqfreePart n,
powerfulPart n)`, the inner harmonic estimate over the `u`-window).  It is
carried as the hypothesis `hReindex` (a true, `x`-independent inequality: the
reindex introduces no new analytic content beyond Part 3's convergence). -/

open Classical in
/-- The `x`-independent envelope: `(1 + log v)/v` on powerful `v`, else `0`. -/
noncomputable def powerfulWeight (v : ℕ) : ℝ :=
  if IsPowerful v ∧ v ≠ 0 then (1 + Real.log v) / (v : ℝ) else 0

lemma powerfulWeight_nonneg (v : ℕ) : 0 ≤ powerfulWeight v := by
  rw [powerfulWeight]
  split_ifs with h
  · exact div_nonneg (by nlinarith [log_natCast_nonneg v]) (by positivity)
  · exact le_rfl

/-- The powerful envelope has finite total mass, bounded by the Part-3 constant. -/
lemma powerfulWeight_tsum_le : ∃ C : ℝ, ∑' v : ℕ, powerfulWeight v ≤ C := by
  classical
  obtain ⟨C, hC⟩ := powerful_sum_bounded
  refine ⟨C, Real.tsum_le_of_sum_le (fun v => powerfulWeight_nonneg v) (fun s => ?_)⟩
  calc ∑ v ∈ s, powerfulWeight v
      = ∑ v ∈ s, if (IsPowerful v ∧ v ≠ 0) then (1 + Real.log v) / (v : ℝ) else 0 := by
        exact Finset.sum_congr rfl (fun v _ => by rw [powerfulWeight])
    _ = ∑ v ∈ s.filter (fun v => IsPowerful v ∧ v ≠ 0), (1 + Real.log v) / (v : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ ≤ C := hC _ (fun v hv => (Finset.mem_filter.mp hv).2)

/-- **The uniform radical-fiber tail bound (from the reindex).**  Given the
squarefree/powerful reindex `hReindex`, the fiber-tail sum is bounded by the
`x`-independent Part-3 constant.  This is the antecedent of
`phiAtom_upper_of_tail_bound`. -/
theorem tail_bound (B : ℕ) (_hB : B ≠ 0)
    (hReindex : ∀ x : ℕ, 2 ≤ x →
      (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B) ≤ ∑' v : ℕ, powerfulWeight v) :
    ∃ C₀ : ℝ, ∀ x : ℕ, 2 ≤ x →
      (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B) ≤ C₀ := by
  obtain ⟨C, hC⟩ := powerfulWeight_tsum_le
  exact ⟨C, fun x hx => (hReindex x hx).trans hC⟩

/-- **The sharp `μ²/φ` upper bound**, modulo the squarefree/powerful reindex
`hReindex`.  The hard analytic core (`radFiber_inv_hasSum`, the reduction, and
the convergent powerful-number series) is unconditional; only the elementary
`Nat` reindex remains as a hypothesis. -/
theorem phiAtom_upper (B : ℕ) (hB : B ≠ 0)
    (hReindex : ∀ x : ℕ, 2 ≤ x →
      (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B) ≤ ∑' v : ℕ, powerfulWeight v) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      Salt.Maynard.phiAtomSum x B ≤ (Nat.totient B / B : ℝ) * Real.log (x : ℝ) + C :=
  phiAtom_upper_of_tail_bound B hB (tail_bound B hB hReindex)

/-- Discharge of `Salt.Twelve.PhiUpperAtom` (modulo `hReindex`). -/
theorem phiUpperAtom_holds (B : ℕ) (hB : B ≠ 0)
    (hReindex : ∀ x : ℕ, 2 ≤ x →
      (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B) ≤ ∑' v : ℕ, powerfulWeight v) :
    Salt.Twelve.PhiUpperAtom B :=
  phiAtom_upper B hB hReindex

end Salt.Twelve


