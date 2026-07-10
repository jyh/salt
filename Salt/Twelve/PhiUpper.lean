/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom

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

end Salt.Twelve


