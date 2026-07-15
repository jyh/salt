/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Lemma11

/-!
# C1c⁗ — The `Tₙ` peeling identity and the Buchstab induction skeleton (BJS §2.4, (34))

This file supplies the infrastructure the C1c‴ executor named as the last analytic gap:
the **peeling recursion** `Tₙ₊₁(D,z) = Σ_p ν(p)·Tₙ(⌈D/p⌉, p)` of BJS (28)/(34), which
reduces the depth-`(n+1)` Buchstab term to depth-`n` terms of a *restricted sieve below `p`*.
`TnInduction.T` bakes `z` into the fixed `s.prodPrimes`, so the recursion needs a genuine
"sieve below `p`" object; we build it (`sieveBelow`) and prove the exact chain identity.

## What is proved (sorry-free, axiom-clean)

* **The restricted sieve `sieveBelow s p`** (Part B): the `BoundingSieve` whose sifting
  primes are exactly those of `s` below `p` (`prodPrimes = Pbelow s p`), with the density
  `ν`, mass, and support inherited.  The density carriers transport cleanly:
  `Vbelow (sieveBelow s p) q = Vbelow s q` for `q ≤ p` (`Vbelow_sieveBelow`) and
  `W (sieveBelow s p) = Vbelow s p` (`W_sieveBelow`) — i.e. `W(sieveBelow) = V(p)`, the
  Buchstab base density at the new cutoff, which is what hypothesis (4) `V(p)/V(z)` bounds.

* **The level ceiling `cdiv D p = ⌈D/p⌉`** (Part A): the exact ℕ-level transform, via the
  biconditional `p·X < D ↔ X < cdiv D p` (`mul_lt_iff_lt_cdiv`).  This is what turns the
  scaled Rosser check `p·(p₂⋯pₘ)·pₘ² < D` on the head-peeled chain into the intrinsic check
  `(p₂⋯pₘ)·pₘ² < ⌈D/p⌉` of the sub-sieve.

* **The peeling identity** (Part C): `T_peel`, for `n ≥ 1` and `1 ≤ D`,
  `T s side D (n+1) = Σ_{p ∈ window} ν(p)·T (sieveBelow s p) (3−side) (cdiv D p) n`,
  where the head window is the sifting primes with `p³ < D` on the upper side (position 1
  is the odd/upper check) and all sifting primes on the lower side (position 1 unchecked).
  An exact identity, proved by the head-peel bijection `c ↔ (p, c/p)` (`Finset.sum_nbij'`
  over the first-violation fibers), the sign/parity flip, and the `cdiv` check translation.

* **The Buchstab induction skeleton** (Part D): `T_le_of_peel_step`, the strong-induction
  engine.  From an abstract target family `B : BoundingSieve → ℕ → ℕ → ℕ → ℝ`, a base bound
  `hbase` (BJS (39), discharged by `Lemma11.hlevel_one_upper` / `T_two_one_zero`), and the
  **per-step comparison** `hstep : Σ_p ν(p)·B(sieveBelow s p)… ≤ B s …` as a single named
  hypothesis (the discrete-to-integral core of BJS (34)–(38)), it yields `T s side D n ≤
  B s side D n` for every `n`.

* **The `hlevel` / `hTbound` plugs** (Part E): `hlevel_upper_of_step` /
  `hlevel_lower_of_step` produce Lemma11's exact `hlevel` shape (hence, through
  `hTbound_*_of_levels`, the assembled BJS Theorem 6 (5)/(6)) modulo the two named
  hypotheses `hbase` and `hstep`.

## The deferred piece (precise flag in `docs/blueprints/flags.md`)

The per-step comparison `hstep` — BJS's (35)–(38) partial-summation bound turning the
head-sum `Σ_p ν(p)·V(p)·fₙ(log(D/p)/log p)` into the integral `V(z)·fₙ₊₁(s)` via
hypothesis (4) — remains a named hypothesis.  It is the genuine real-analysis heart
(discrete-to-integral, varying `sparam' = log⌈D/p⌉/log p`), and it is the *only* analytic
content not discharged here: everything combinatorial (the peel, the induction) is proved.
-/

open Finset Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

namespace Salt.Chen

open List

/-! ## Part A — the level ceiling `cdiv D p = ⌈D/p⌉`

The Rosser check on the head-peeled chain carries an extra factor `p`
(`p·(p₂⋯pₘ)·pₘ² < D`); to express the sub-check intrinsically we need the natural-number
level `D'` with `p·X < D ↔ X < D'`.  That `D'` is the ceiling `⌈D/p⌉ = (D−1)/p + 1`. -/

/-- The level ceiling `⌈D/p⌉` realised as `(D − 1)/p + 1` (`1 ≤ D`, `1 ≤ p`). -/
def cdiv (D p : ℕ) : ℕ := (D - 1) / p + 1

/-- `1 ≤ cdiv D p` always (so the recursion never drops below the `1 ≤ D` threshold). -/
lemma one_le_cdiv (D p : ℕ) : 1 ≤ cdiv D p := Nat.le_add_left 1 _

/-- **The defining biconditional** `p·X < D ↔ X < ⌈D/p⌉` (`1 ≤ p`, `1 ≤ D`).  Both the
Rosser *pass* checks (`< D`) and the *fail* check (`D ≤ ·`, its negation) translate through
this. -/
lemma mul_lt_iff_lt_cdiv {D p : ℕ} (hp : 1 ≤ p) (hD : 1 ≤ D) (X : ℕ) :
    p * X < D ↔ X < cdiv D p := by
  have hp0 : 0 < p := hp
  rw [cdiv, Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hp0, mul_comm X p]
  omega

/-! ## Part B — the restricted sieve `sieveBelow s p` -/

/-- `Pbelow s q ∣ s.prodPrimes`: the below-`q` sub-product divides the full sifting product. -/
lemma Pbelow_dvd_prodPrimes (s : BoundingSieve) (q : ℕ) : Pbelow s q ∣ s.prodPrimes := by
  unfold Pbelow
  calc ∏ p ∈ belowPrimes s q, p
      ∣ ∏ p ∈ s.prodPrimes.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    _ = s.prodPrimes := Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree

/-- **The restricted sieve `sieveBelow s p`** (BJS's sieve at the reduced cutoff `p`): the
same weights/mass/density as `s`, but sifting only the primes `< p`.  Its sifting product is
`Pbelow s p = ∏_{q < p} q`, so `W (sieveBelow s p) = V(p)`. -/
noncomputable def sieveBelow (s : BoundingSieve) (p : ℕ) : BoundingSieve where
  support := s.support
  prodPrimes := Pbelow s p
  prodPrimes_squarefree := Pbelow_squarefree s p
  weights := s.weights
  weights_nonneg := s.weights_nonneg
  totalMass := s.totalMass
  nu := s.nu
  nu_mult := s.nu_mult
  nu_pos_of_prime := fun q hq hqd => s.nu_pos_of_prime q hq (hqd.trans (Pbelow_dvd_prodPrimes s p))
  nu_lt_one_of_prime := fun q hq hqd =>
    s.nu_lt_one_of_prime q hq (hqd.trans (Pbelow_dvd_prodPrimes s p))

@[simp] lemma sieveBelow_nu (s : BoundingSieve) (p : ℕ) : (sieveBelow s p).nu = s.nu := rfl

@[simp] lemma sieveBelow_prodPrimes (s : BoundingSieve) (p : ℕ) :
    (sieveBelow s p).prodPrimes = Pbelow s p := rfl

/-- The sifting primes of `sieveBelow s p` are exactly `belowPrimes s p`. -/
lemma sieveBelow_primeFactors (s : BoundingSieve) (p : ℕ) :
    (sieveBelow s p).prodPrimes.primeFactors = belowPrimes s p := by
  rw [sieveBelow_prodPrimes, primeFactors_Pbelow]

/-- `belowPrimes` of the restricted sieve agrees with `s`'s below any cutoff `q ≤ p`. -/
lemma belowPrimes_sieveBelow (s : BoundingSieve) {p q : ℕ} (hqp : q ≤ p) :
    belowPrimes (sieveBelow s p) q = belowPrimes s q := by
  unfold belowPrimes
  rw [sieveBelow_primeFactors, belowPrimes, Finset.filter_filter]
  apply Finset.filter_congr
  intro r _
  simp only [and_iff_right_iff_imp]
  intro hrq; omega

/-- `Vbelow (sieveBelow s p) q = Vbelow s q` for `q ≤ p` (density carrier transport). -/
lemma Vbelow_sieveBelow (s : BoundingSieve) {p q : ℕ} (hqp : q ≤ p) :
    Vbelow (sieveBelow s p) q = Vbelow s q := by
  unfold Vbelow
  rw [belowPrimes_sieveBelow s hqp, sieveBelow_nu]

/-- `W (sieveBelow s p) = V(p) = Vbelow s p`: the restricted sieve's total density is the
Buchstab base density at the reduced cutoff — exactly the `V(p)` that hypothesis (4) bounds
against `V(z) = W s`. -/
lemma W_sieveBelow (s : BoundingSieve) (p : ℕ) :
    Salt.BrunLower.W (sieveBelow s p) = Vbelow s p := by
  rw [Salt.BrunLower.W, sieveBelow_primeFactors, sieveBelow_nu, Vbelow]

/-! ## Part C — the peeling identity `Tₙ₊₁(D) = Σ_p ν(p)·Tₙ(⌈D/p⌉) over sieveBelow`

The head-peel: a violating prefix `c = p₁ > ⋯ > pₙ₊₁` factors as `c = p·c'` where `p = p₁`
is the head and `c' = p₂⋯pₙ₊₁` a length-`n` chain of primes `< p`.  Under this bijection the
depth-`(n+1)` term of `s` becomes the sum over heads `p` of `ν(p)` times the depth-`n` term
of `sieveBelow s p` at the reduced level `⌈D/p⌉` and flipped side (each check shifts one
position).  We first record the positional translations of `rlist`/`rprefix`/`relem`/`rmin`
across `c = p·c'`, then the `isViolPrefix` biconditional, then the fibered sum. -/

/-- `rlist p = [p]` for a prime `p`. -/
lemma rlist_prime {p : ℕ} (hp : p.Prime) : rlist p = [p] := by
  rw [rlist, hp.primeFactors, Finset.sort_singleton]

/-- All prime factors of a divisor of `Pbelow s p` lie below `p`. -/
lemma dvd_Pbelow_primeFactors_lt {s : BoundingSieve} {p c' : ℕ} (hc' : c' ∣ Pbelow s p) :
    ∀ q ∈ c'.primeFactors, q < p := by
  intro q hq
  have hsub : c'.primeFactors ⊆ (Pbelow s p).primeFactors :=
    Nat.primeFactors_mono hc' (Pbelow_ne_zero s p)
  rw [primeFactors_Pbelow] at hsub
  exact (Finset.mem_filter.mp (hsub hq)).2

/-- **Head-cons**: `rlist (p·c') = p :: rlist c'` when `p` is a prime above every prime of
`c' ∣ Pbelow s p`. -/
lemma rlist_head_cons {s : BoundingSieve} {p c' : ℕ} (hp : p.Prime) (hc'0 : c' ≠ 0)
    (hc' : c' ∣ Pbelow s p) : rlist (p * c') = p :: rlist c' := by
  have hlt : ∀ q ∈ c'.primeFactors, ∀ r ∈ p.primeFactors, q < r := by
    intro q hq r hr
    rw [hp.primeFactors, Finset.mem_singleton] at hr; subst hr
    exact dvd_Pbelow_primeFactors_lt hc' q hq
  rw [rlist_mul_block hp.ne_zero hc'0 hlt, rlist_prime hp]; rfl

/-- Positional: the head is `relem (p·c') 0 = p`. -/
lemma relem_cons_zero {p c' : ℕ} (hcons : rlist (p * c') = p :: rlist c') :
    relem (p * c') 0 = p := by
  rw [relem, hcons]; rfl

/-- Positional: `relem (p·c') (i+1) = relem c' i` (shift by the head). -/
lemma relem_cons_succ {p c' : ℕ} (hcons : rlist (p * c') = p :: rlist c') (i : ℕ) :
    relem (p * c') (i + 1) = relem c' i := by
  rw [relem, relem, hcons, List.getD_cons_succ]

/-- Positional: `rprefix (p·c') (m+1) = p · rprefix c' m`. -/
lemma rprefix_cons_succ {p c' : ℕ} (hcons : rlist (p * c') = p :: rlist c') (m : ℕ) :
    rprefix (p * c') (m + 1) = p * rprefix c' m := by
  unfold rprefix
  rw [hcons, Finset.prod_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  ring

/-- Positional: `rmin (p·c') = rmin c'` (the smallest prime is unchanged by prepending a
larger head), for `c'` of positive length. -/
lemma rmin_cons {p c' n : ℕ} (hcons : rlist (p * c') = p :: rlist c')
    (hlen : (rlist c').length = n) (hn : 1 ≤ n) : rmin (p * c') = rmin c' := by
  have hlen1 : (rlist (p * c')).length = n + 1 := by rw [hcons, List.length_cons, hlen]
  simp only [rmin]
  rw [hlen1, hlen]
  have hn' : n + 1 - 1 = (n - 1) + 1 := by omega
  rw [hn', relem_cons_succ hcons]

/-- `rprefix d 0 = 1` (empty prefix). -/
lemma rprefix_zero (d : ℕ) : rprefix d 0 = 1 := by
  unfold rprefix; rw [Finset.range_zero, Finset.prod_empty]

/-- Positional: `rprefix (p·c') 1 = p` (the top-1 prefix is the head). -/
lemma rprefix_cons_one {p c' : ℕ} (hcons : rlist (p * c') = p :: rlist c') :
    rprefix (p * c') 1 = p := by
  have h := rprefix_cons_succ hcons 0
  rw [rprefix_zero, mul_one] at h
  simpa using h

/-- **The `isViolPrefix` peel biconditional** (BJS (28)'s chain condition under head-peel).
A violating prefix `p·c'` of length `n+1` for `(side, D)` corresponds to a violating prefix
`c'` of length `n` for `(3−side, ⌈D/p⌉)`, together with the head check `p³ < D` on the upper
side (position 1 is the odd check).  Each interior check `p·(p₂⋯pₘ)·pₘ² < D` becomes the
intrinsic sub-check `(p₂⋯pₘ)·pₘ² < ⌈D/p⌉` and shifts one position (parity flip). -/
lemma isViolPrefix_peel_iff {s : BoundingSieve} {side D p c' n : ℕ}
    (hside : side = 1 ∨ side = 2) (hp : p.Prime) (hc'0 : c' ≠ 0) (hc' : c' ∣ Pbelow s p)
    (hlen : (rlist c').length = n) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    isViolPrefix side D (p * c')
      ↔ (side % 2 = 1 → p ^ 3 < D) ∧ isViolPrefix (3 - side) (cdiv D p) c' := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcons : rlist (p * c') = p :: rlist c' := rlist_head_cons hp hc'0 hc'
  have hlen1 : (rlist (p * c')).length = n + 1 := by rw [hcons, List.length_cons, hlen]
  have hflip : ∀ k, ((k + 1) % 2 = side % 2) ↔ (k % 2 = (3 - side) % 2) := by
    intro k; rcases hside with rfl | rfl <;> omega
  have hrp1 : rprefix (p * c') 1 = p := rprefix_cons_one hcons
  have hr0 : relem (p * c') 0 = p := relem_cons_zero hcons
  -- FAIL translation: `D ≤ p·Y  ↔  ⌈D/p⌉ ≤ Y`
  have hfail : (D ≤ rprefix (p * c') (n + 1) * (relem (p * c') n) ^ 2)
      ↔ (cdiv D p ≤ rprefix c' n * (relem c' (n - 1)) ^ 2) := by
    have hrn : relem (p * c') n = relem c' (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [relem_cons_succ hcons]
    rw [rprefix_cons_succ hcons n, hrn, mul_assoc, ← not_lt, ← not_lt, not_iff_not]
    exact mul_lt_iff_lt_cdiv hp1 hD _
  -- PASS translation: head check + shifted interior checks
  have hpass : (∀ m, 1 ≤ m → m < n + 1 → m % 2 = side % 2 →
        rprefix (p * c') m * (relem (p * c') (m - 1)) ^ 2 < D)
      ↔ (side % 2 = 1 → p ^ 3 < D) ∧
        (∀ m, 1 ≤ m → m < n → m % 2 = (3 - side) % 2 →
          rprefix c' m * (relem c' (m - 1)) ^ 2 < cdiv D p) := by
    constructor
    · intro hall
      refine ⟨fun hs1 => ?_, fun m hm1 hmn hmpar => ?_⟩
      · have h := hall 1 (le_refl 1) (by omega) (by omega)
        rw [hrp1, hr0] at h
        rw [show p ^ 3 = p * p ^ 2 from by ring]; exact h
      · have hmpar' : (m + 1) % 2 = side % 2 := (hflip m).mpr hmpar
        have h := hall (m + 1) (by omega) (by omega) hmpar'
        rw [rprefix_cons_succ hcons m, show (m + 1) - 1 = (m - 1) + 1 by omega,
          relem_cons_succ hcons, mul_assoc] at h
        exact (mul_lt_iff_lt_cdiv hp1 hD _).mp h
    · rintro ⟨hhead, hsub⟩ m hm1 hmn hmpar
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · -- m = 1
        have hm1' : m = 1 := by omega
        subst hm1'
        have hs1 : side % 2 = 1 := by omega
        rw [hrp1, hr0, show p * p ^ 2 = p ^ 3 from by ring]
        exact hhead hs1
      · -- m = k + 1, k ≥ 1
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hk1 : 1 ≤ k := by omega
        have hkn : k < n := by omega
        have hkpar : k % 2 = (3 - side) % 2 := (hflip k).mp hmpar
        have h := hsub k hk1 hkn hkpar
        rw [rprefix_cons_succ hcons k, show (k + 1) - 1 = (k - 1) + 1 by omega,
          relem_cons_succ hcons, mul_assoc]
        exact (mul_lt_iff_lt_cdiv hp1 hD _).mpr h
  -- assemble
  unfold isViolPrefix
  rw [hlen1, hlen, Nat.add_sub_cancel]
  constructor
  · rintro ⟨_, h2, h3, h4⟩
    obtain ⟨hhead, hsub⟩ := hpass.mp h4
    exact ⟨hhead, hn, (hflip n).mp h2, hfail.mp h3, hsub⟩
  · rintro ⟨hhead, _, h2', h3', h4'⟩
    exact ⟨by omega, (hflip n).mpr h2', hfail.mpr h3', hpass.mpr ⟨hhead, h4'⟩⟩

/-- The drop-1 tail `rsuffix c 1 = p₂⋯pᵣ` divides `Pbelow s (p₁)`: all its primes lie below
the head `p₁ = relem c 0`. -/
lemma rsuffix_one_dvd_Pbelow {s : BoundingSieve} {c : ℕ} (hc : c ∣ s.prodPrimes)
    (hlen : 1 ≤ (rlist c).length) : rsuffix c 1 ∣ Pbelow s (relem c 0) := by
  have hcsf : Squarefree c := s.prodPrimes_squarefree.squarefree_of_dvd hc
  have hsuf_dvd_c : rsuffix c 1 ∣ c :=
    ⟨rprefix c 1, by rw [mul_comm]; exact (rprefix_mul_rsuffix hcsf 1).symm⟩
  have hsuf_pp : rsuffix c 1 ∣ s.prodPrimes := hsuf_dvd_c.trans hc
  have hsuf_sf : Squarefree (rsuffix c 1) := s.prodPrimes_squarefree.squarefree_of_dvd hsuf_pp
  refine dvd_Pbelow_of_subset hsuf_sf (fun q hq => ?_)
  have hq_pp : q ∈ s.prodPrimes.primeFactors :=
    Nat.primeFactors_mono hsuf_pp s.prodPrimes_squarefree.ne_zero hq
  have hqin : q ∈ (rlist c).drop 1 := by rw [← rlist_rsuffix]; exact rlist_mem.mpr hq
  obtain ⟨i, hi, hiq⟩ := List.mem_iff_getElem.mp hqin
  rw [List.length_drop] at hi
  rw [List.getElem_drop] at hiq
  have hlt : q < relem c 0 := by
    have h2 : relem c (1 + i) < relem c 0 := relem_lt_relem (by omega) (by omega)
    rwa [relem, List.getD_eq_getElem _ _ (by omega : 1 + i < (rlist c).length), hiq] at h2
  exact Finset.mem_filter.mpr ⟨hq_pp, hlt⟩

/-- `rprefix c 1 = relem c 0` (the top-1 prefix is the head). -/
lemma rprefix_one (c : ℕ) : rprefix c 1 = relem c 0 := by
  rw [rprefix, Finset.prod_range_one, relem]

/-! ### The peeling identity -/

/-- **The peeling identity** (BJS (28)/(34), head-peel form).  For `n ≥ 1` and `1 ≤ D`, the
depth-`(n+1)` Buchstab term of `s` at level `D` reorganises, by peeling the head prime `p`
of each violating chain, as `Σ_p ν(p)` times the depth-`n` term of the restricted sieve
`sieveBelow s p` at the reduced level `⌈D/p⌉` and flipped side `3−side`.  The head window is
the sifting primes passing the position-1 check (`p³ < D` on the odd/upper side; all sifting
primes on the even/lower side, where position 1 is unchecked). -/
theorem T_peel (s : BoundingSieve) (side D n : ℕ) (hside : side = 1 ∨ side = 2)
    (hn : 1 ≤ n) (hD : 1 ≤ D) :
    T s side D (n + 1)
      = ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p => side % 2 = 1 → p ^ 3 < D),
          s.nu p * T (sieveBelow s p) (3 - side) (cdiv D p) n := by
  -- `T s side D (n+1)` is the sum over length-`(n+1)` violating prefixes.
  rw [T]
  -- Map each chain to its head; the head lands in the window.
  have hmaps : ∀ c ∈ (divisors s.prodPrimes).filter
        (fun c => isViolPrefix side D c ∧ (rlist c).length = n + 1),
      relem c 0 ∈ s.prodPrimes.primeFactors.filter (fun p => side % 2 = 1 → p ^ 3 < D) := by
    intro c hc
    obtain ⟨hcdvd, hviol, hclen⟩ := Finset.mem_filter.mp hc
    have hcdvd' : c ∣ s.prodPrimes := (Nat.mem_divisors.mp hcdvd).1
    have hlen1 : 1 ≤ (rlist c).length := by rw [hclen]; omega
    have hhead_mem : relem c 0 ∈ c.primeFactors := by
      rw [relem, List.getD_eq_getElem _ _ hlen1]
      exact rlist_mem.mp (List.getElem_mem _)
    have hhead_pp : relem c 0 ∈ s.prodPrimes.primeFactors :=
      Nat.primeFactors_mono hcdvd' s.prodPrimes_squarefree.ne_zero hhead_mem
    refine Finset.mem_filter.mpr ⟨hhead_pp, fun hs1 => ?_⟩
    obtain ⟨_, _, _, hpass⟩ := hviol
    have h := hpass 1 (le_refl 1) (by rw [hclen]; omega) (by omega)
    rw [rprefix_one] at h
    calc (relem c 0) ^ 3 = relem c 0 * (relem c 0) ^ 2 := by ring
      _ < D := h
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun c => s.nu c * Vbelow s (rmin c))]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨hp_pf, hp_window⟩ := Finset.mem_filter.mp hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
  have hp_dvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp_pf
  have hPb0 : Pbelow s p ≠ 0 := Pbelow_ne_zero s p
  rw [T, Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun c => rsuffix c 1) (j := fun c' => p * c')
    ?hi ?hj ?left ?right ?h
  case hi =>
    intro c hc
    rw [Finset.mem_filter, Finset.mem_filter] at hc
    obtain ⟨⟨hcdvd, hviol, hclen⟩, hchead⟩ := hc
    have hcdvd' : c ∣ s.prodPrimes := (Nat.mem_divisors.mp hcdvd).1
    have hcsf : Squarefree c := s.prodPrimes_squarefree.squarefree_of_dvd hcdvd'
    have hlen1 : 1 ≤ (rlist c).length := by rw [hclen]; omega
    have hc'dvd : rsuffix c 1 ∣ Pbelow s p := by
      have := rsuffix_one_dvd_Pbelow hcdvd' hlen1; rwa [hchead] at this
    have hc'0 : rsuffix c 1 ≠ 0 :=
      ((Pbelow_squarefree s p).squarefree_of_dvd hc'dvd).ne_zero
    have hc'len : (rlist (rsuffix c 1)).length = n := by
      rw [rlist_rsuffix, List.length_drop, hclen, Nat.add_sub_cancel]
    have hsplit : p * rsuffix c 1 = c := by
      rw [← hchead, ← rprefix_one]; exact rprefix_mul_rsuffix hcsf 1
    have hviol' : isViolPrefix (3 - side) (cdiv D p) (rsuffix c 1) := by
      have := (isViolPrefix_peel_iff hside hp_prime hc'0 hc'dvd hc'len hn hD).mp
        (by rw [hsplit]; exact hviol)
      exact this.2
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hc'dvd, hPb0⟩, hviol', hc'len⟩
  case hj =>
    intro c' hc'
    obtain ⟨hc'dvd, hviol', hc'len⟩ := Finset.mem_filter.mp hc'
    have hc'dvdPb : c' ∣ Pbelow s p := (Nat.mem_divisors.mp hc'dvd).1
    have hc'0 : c' ≠ 0 := ((Pbelow_squarefree s p).squarefree_of_dvd hc'dvdPb).ne_zero
    have hlt : ∀ q ∈ c'.primeFactors, q < p := dvd_Pbelow_primeFactors_lt hc'dvdPb
    have hcop : Nat.Coprime p c' := by
      apply coprime_of_primeFactors_lt hp_prime.ne_zero hc'0
      intro r hr q hq
      rw [hp_prime.primeFactors, Finset.mem_singleton] at hq; subst hq
      exact hlt r hr
    have hpc'dvd : p * c' ∣ s.prodPrimes :=
      hcop.mul_dvd_of_dvd_of_dvd hp_dvd (hc'dvdPb.trans (Pbelow_dvd_prodPrimes s p))
    have hcons : rlist (p * c') = p :: rlist c' := rlist_head_cons hp_prime hc'0 hc'dvdPb
    have hviol : isViolPrefix side D (p * c') :=
      (isViolPrefix_peel_iff hside hp_prime hc'0 hc'dvdPb hc'len hn hD).mpr ⟨hp_window, hviol'⟩
    have hpc'len : (rlist (p * c')).length = n + 1 := by rw [hcons, List.length_cons, hc'len]
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hpc'dvd, s.prodPrimes_squarefree.ne_zero⟩, hviol, hpc'len⟩, ?_⟩
    exact relem_cons_zero hcons
  case left =>
    intro c hc
    rw [Finset.mem_filter, Finset.mem_filter] at hc
    obtain ⟨⟨hcdvd, _, _⟩, hchead⟩ := hc
    have hcdvd' : c ∣ s.prodPrimes := (Nat.mem_divisors.mp hcdvd).1
    have hcsf : Squarefree c := s.prodPrimes_squarefree.squarefree_of_dvd hcdvd'
    rw [← hchead, ← rprefix_one]; exact rprefix_mul_rsuffix hcsf 1
  case right =>
    intro c' hc'
    obtain ⟨hc'dvd, _, _⟩ := Finset.mem_filter.mp hc'
    have hc'dvdPb : c' ∣ Pbelow s p := (Nat.mem_divisors.mp hc'dvd).1
    have hc'0 : c' ≠ 0 := ((Pbelow_squarefree s p).squarefree_of_dvd hc'dvdPb).ne_zero
    have hc'sf : Squarefree c' := (Pbelow_squarefree s p).squarefree_of_dvd hc'dvdPb
    rw [rsuffix, rlist_head_cons hp_prime hc'0 hc'dvdPb, List.drop_one, List.tail_cons,
      rlist_prod hc'sf]
  case h =>
    intro c hc
    rw [Finset.mem_filter, Finset.mem_filter] at hc
    obtain ⟨⟨hcdvd, hviol, hclen⟩, hchead⟩ := hc
    have hcdvd' : c ∣ s.prodPrimes := (Nat.mem_divisors.mp hcdvd).1
    have hcsf : Squarefree c := s.prodPrimes_squarefree.squarefree_of_dvd hcdvd'
    have hlen1 : 1 ≤ (rlist c).length := by rw [hclen]; omega
    have hc'dvd : rsuffix c 1 ∣ Pbelow s p := by
      have := rsuffix_one_dvd_Pbelow hcdvd' hlen1; rwa [hchead] at this
    have hc'0 : rsuffix c 1 ≠ 0 :=
      ((Pbelow_squarefree s p).squarefree_of_dvd hc'dvd).ne_zero
    have hc'len : (rlist (rsuffix c 1)).length = n := by
      rw [rlist_rsuffix, List.length_drop, hclen, Nat.add_sub_cancel]
    have hsplit : p * rsuffix c 1 = c := by
      rw [← hchead, ← rprefix_one]; exact rprefix_mul_rsuffix hcsf 1
    have hcons : rlist (p * rsuffix c 1) = p :: rlist (rsuffix c 1) :=
      rlist_head_cons hp_prime hc'0 hc'dvd
    -- ν(c) = ν(p)·ν(c'), rmin c = rmin c', Vbelow transports to sieveBelow
    have hlt : ∀ q ∈ (rsuffix c 1).primeFactors, q < p := dvd_Pbelow_primeFactors_lt hc'dvd
    have hcop : Nat.Coprime p (rsuffix c 1) := by
      apply coprime_of_primeFactors_lt hp_prime.ne_zero hc'0
      intro r hr q hq
      rw [hp_prime.primeFactors, Finset.mem_singleton] at hq; subst hq
      exact hlt r hr
    have hnu : s.nu c = s.nu p * s.nu (rsuffix c 1) := by
      have h := s.nu_mult.map_mul_of_coprime hcop
      rw [hsplit] at h; exact h
    have hrmin : rmin c = rmin (rsuffix c 1) := by
      have h := rmin_cons hcons hc'len hn
      rw [hsplit] at h; exact h
    have hrmin_lt : rmin (rsuffix c 1) ≤ p := by
      have hmem : rmin (rsuffix c 1) ∈ (rsuffix c 1).primeFactors := by
        rw [rmin, relem, List.getD_eq_getElem _ _ (by rw [hc'len]; omega)]
        exact rlist_mem.mp (List.getElem_mem _)
      exact (hlt _ hmem).le
    rw [hnu, hrmin, sieveBelow_nu, Vbelow_sieveBelow s hrmin_lt]
    ring

/-! ## Part D — the Buchstab induction skeleton

The strong-induction engine: from an abstract target family `B` (to be instantiated by the
`fₙ`/`h`/`τ` bound of BJS Lemma 11), a base bound `hbase` (BJS (39)), and the **per-step
comparison** `hstep` — the single named hypothesis carrying BJS's (35)–(38)
partial-summation content — every `Tₙ` is bounded by `B`.  The recursion drives `n → n−1`
through `T_peel`, applying the induction hypothesis to each restricted sub-sieve. -/

/-- **The Buchstab induction skeleton** (BJS Lemma 11, the induction on chain depth).  With
`B : BoundingSieve → ℕ → ℕ → ℕ → ℝ` (sieve, side, level, depth) the abstract target family,
`hbase` the depth-1 bound, and `hstep` the per-step comparison `Σ_p ν(p)·B(sieveBelow…) ≤
B s …` (BJS (34)–(38), the discrete-to-integral heart, taken as a hypothesis), we get
`Tₙ ≤ B s side D n` for every depth `n ≥ 1`, every sieve, level, and side. -/
theorem T_le_of_peel_step (B : BoundingSieve → ℕ → ℕ → ℕ → ℝ)
    (hbase : ∀ (s' : BoundingSieve) (side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ B s' side' D' 1)
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * B (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ B s' side' D' (n + 1)) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (s' : BoundingSieve) (side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
      T s' side' D' n ≤ B s' side' D' n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro _ s' side' D' hside' hD'
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; exact hbase s' side' D' hside' hD'
    · have hm1 : 1 ≤ m := hm
      rw [T_peel s' side' D' m hside' hm1 hD']
      refine le_trans (Finset.sum_le_sum (fun p hp => ?_)) (hstep s' side' D' m hside' hD' hm1)
      obtain ⟨hp_pf, _⟩ := Finset.mem_filter.mp hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
      have hp_dvd : p ∣ s'.prodPrimes := Nat.dvd_of_mem_primeFactors hp_pf
      have hnu_pos : 0 ≤ s'.nu p := (s'.nu_pos_of_prime p hp_prime hp_dvd).le
      have hflip : 3 - side' = 1 ∨ 3 - side' = 2 := by rcases hside' with rfl | rfl <;> omega
      exact mul_le_mul_of_nonneg_left
        (ih hm1 (sieveBelow s' p) (3 - side') (cdiv D' p) hflip (one_le_cdiv D' p)) hnu_pos

/-! ## Part E — the `hlevel` / `hTbound` plugs (Lemma11 shape, BJS Theorem 6)

Instantiating the skeleton at the `fₙ`/`h`/`τ` target family `fseqBound` produces Lemma11's
exact `hlevel` shape, which flows through `hTbound_*_of_levels` (C1c‴) to the assembled BJS
Theorem 6 (5)/(6).  The operating point `sparam = σ s D = log D/log z` is threaded by the
`σ` parameter; the base (`hbase`, BJS (39) = `hlevel_one_upper`/`T_two_one_zero`) and the
per-step analytic comparison (`hstep`) remain the two named hypotheses. -/

/-- The `fₙ`/`h`/`τ` target family of BJS Lemma 11: `B s' D' n = W s'·(fₙ(σ s' D') +
ε·τₙ·e²·h(σ s' D'))`, with `σ` the operating-point map `(sieve, level) ↦ log D/log z`. -/
noncomputable def fseqBound (σ : BoundingSieve → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ)
    (s' : BoundingSieve) (_side' D' n : ℕ) : ℝ :=
  Salt.BrunLower.W s' * (fseq n (σ s' D') + ε * tau n * Real.exp 2 * hBJS (σ s' D'))

/-- **`hlevel`, upper (BJS Theorem 6 (5)).**  From the fseq-shaped base and per-step
hypotheses, the skeleton yields Lemma11's exact upper `hlevel` shape at `sparam = σ s D`. -/
theorem hlevel_upper_of_step (s : BoundingSieve) (D : ℕ) (hD : 1 ≤ D)
    (σ : BoundingSieve → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ)
    (hbase : ∀ (s' : BoundingSieve) (side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ fseqBound σ ε tau s' side' D' 1)
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1)) :
    ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n),
      T s 1 D n
        ≤ Salt.BrunLower.W s * (fseq n (σ s D) + ε * tau n * Real.exp 2 * hBJS (σ s D)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  have hn1 : 1 ≤ n := by rcases hn.2 with ⟨k, rfl⟩; omega
  have h := T_le_of_peel_step (fseqBound σ ε tau) hbase hstep n hn1 s 1 D (Or.inl rfl) hD
  simpa [fseqBound] using h

/-- `T s side D 0 = 0` (there are no length-0 violating prefixes). -/
theorem T_zero (s : BoundingSieve) (side D : ℕ) : T s side D 0 = 0 := by
  apply Finset.sum_eq_zero
  intro c hc
  obtain ⟨_, hviol, hlen⟩ := Finset.mem_filter.mp hc
  exact absurd hviol.1 (by rw [hlen]; omega)

/-- **`hlevel`, lower (BJS Theorem 6 (6)).**  The even/lower mirror.  The even filter carries
the `n = 0` term (`T s 2 D 0 = 0`, `fseq 0 = 0`), handled directly; `n ≥ 2` runs through the
skeleton. -/
theorem hlevel_lower_of_step (s : BoundingSieve) (D : ℕ) (hD : 1 ≤ D)
    (σ : BoundingSieve → ℕ → ℝ) (ε : ℝ) (tau : ℕ → ℝ) (hε : 0 ≤ ε) (htau0 : 0 ≤ tau 0)
    (hbase : ∀ (s' : BoundingSieve) (side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ fseqBound σ ε tau s' side' D' 1)
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1)) :
    ∀ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n),
      T s 2 D n
        ≤ Salt.BrunLower.W s * (fseq n (σ s D) + ε * tau n * Real.exp 2 * hBJS (σ s D)) := by
  intro n hn
  rw [Finset.mem_filter] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [T_zero, fseq_zero]
    have hW := Salt.BrunLower.W_pos s
    have hh := (hBJS_pos (σ s D)).le
    have : 0 ≤ ε * tau 0 * Real.exp 2 * hBJS (σ s D) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg hε htau0) (Real.exp_pos 2).le) hh
    nlinarith [this, hW]
  · have h := T_le_of_peel_step (fseqBound σ ε tau) hbase hstep n hn1 s 2 D (Or.inr rfl) hD
    simpa [fseqBound] using h

/-- **BJS Theorem 6 (5), assembled to the base + per-step hypotheses (upper).**  Composes
`hlevel_upper_of_step` through C1c‴'s `hmain_upper_of_levels` to the full main-term
comparison at `sparam = σ s D`. -/
theorem hmain_upper_of_step (s : BoundingSieve) (D : ℕ) (hD : 1 ≤ D)
    (σ : BoundingSieve → ℕ → ℝ) (ε C₁ : ℝ) (tau : ℕ → ℝ) (hε : 0 ≤ ε)
    (hbase : ∀ (s' : BoundingSieve) (side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ fseqBound σ ε tau s' side' D' 1)
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    s.mainSum (rosserSquarefreeSieve 1 D (Or.inl rfl)).lam
      ≤ Salt.BrunLower.W s *
        (Fchain (maxDepth s) (σ s D) + ε * C₁ * Real.exp 2 * hBJS (σ s D)) :=
  hmain_upper_of_levels s D (σ s D) ε C₁ tau hε
    (hlevel_upper_of_step s D hD σ ε tau hbase hstep) htau

/-- **BJS Theorem 6 (6), assembled to the base + per-step hypotheses (lower).** -/
theorem hmain_lower_of_step (s : BoundingSieve) (D : ℕ) (hD : 1 ≤ D)
    (σ : BoundingSieve → ℕ → ℝ) (ε C₂ : ℝ) (tau : ℕ → ℝ) (hε : 0 ≤ ε) (htau0 : 0 ≤ tau 0)
    (hbase : ∀ (s' : BoundingSieve) (side' D' : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' →
        T s' side' D' 1 ≤ fseqBound σ ε tau s' side' D' 1)
    (hstep : ∀ (s' : BoundingSieve) (side' D' n : ℕ), side' = 1 ∨ side' = 2 → 1 ≤ D' → 1 ≤ n →
        (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
            s'.nu p * fseqBound σ ε tau (sieveBelow s' p) (3 - side') (cdiv D' p) n)
          ≤ fseqBound σ ε tau s' side' D' (n + 1))
    (htau : ∑ n ∈ (Finset.range (maxDepth s + 1)).filter (fun n => Even n), tau n ≤ C₂) :
    Salt.BrunLower.W s * (fchain (maxDepth s) (σ s D) - ε * C₂ * Real.exp 2 * hBJS (σ s D))
      ≤ s.mainSum (rosserSquarefreeSieve 2 D (Or.inr rfl)).lam :=
  hmain_lower_of_levels s D (σ s D) ε C₂ tau hε
    (hlevel_lower_of_step s D hD σ ε tau hε htau0 hbase hstep) htau

end Salt.Chen
