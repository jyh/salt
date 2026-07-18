/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.GrahamWeights

/-!
# The Selberg Λ² lcm-collection regroup and Graham's L² mean bound

Design: `docs/exploration/s3-hb3-design.md`, HB-ENGINE WP2 (the DH-2b product detector).
This module lands the analytic heart of the repulsion tail cancellation: the
lcm-collection regroup of the squared mollifier `w(n) = (Σ_{d ∣ n} θ_d)²` and the
coefficient bounds on the collected `gc(m)`.

## Objects

* `grahamW z n = (Σ_{d ∣ n} θ_d)²` — the squared divisor-collected Graham/Barban–Vehov
  mollifier (the product detector's local factor).
* `grahamGc z m = lambdaSquared (grahamTheta z) m
    = Σ_{d,e ∣ m, lcm(d,e)=m} θ_d θ_e` — the lcm-collected pair coefficient, reusing
  mathlib's Selberg Λ² coefficient of the weight sequence `θ`.

## Rungs landed

* **L1** `grahamW_eq_sum_grahamGc` — the lcm-collection regroup
  `w(n) = Σ_{m ∣ n} gc(m)` (the classical Selberg λ²-regroup; closes GrahamWeights'
  named residual (1), the crux stone of DHFinal's obstruction 2). Reindexes the raw
  double sum via mathlib's `lambdaSquared`.

* **L2** `grahamGc_eq_zero_of_not_squarefree` (gc vanishes off squarefree `m`, since
  `lcm` of squarefree is squarefree) and `abs_grahamGc_le` (`|gc(m)| ≤ 3^ω(m)`, the
  divisor-pair count via `Nat.card_pair_lcm_eq`, template `selberg_bound_muPlus`).

* **L3 (structural stone)** `graham_diagonalisation` — the Selberg gcd/totient
  diagonalization `Σ_{d,e ≤ z} θ_d θ_e/lcm(d,e) = Σ_{g ≤ z} φ(g)·(innerG z g)²`, via
  `1/lcm = gcd/(d·e)` and `gcd = Σ_{g ∣ ·} φ` (`sum_totient_indicator_eq_gcd`);
  `graham_diagonalisation_nonneg` records its L² positivity. `innerG_one_eq` exposes
  the `g = 1` diagonal factor as the LANDED sharp Barban–Vehov sum `Σ_{d ≤ z} θ_d/d`.

* **L3a** `grahamW_mean_eq` — the harmonic reduction
  `Σ_{n ≤ N} w(n)/n = Σ_{m ≤ N} gc(m)·(Σ_{n ≤ N, m ∣ n} 1/n)` (divisor-sum swap via L1).

## Named residual (the sharp L² mean bound `≍ log N/log z`)

The remaining gap to Graham's sharp mean is the `g ≥ 2` coprime-restricted Barban–Vehov
decay `|innerG z g| ≤ C·h(g)/(g·log z)` (the `g = 1` term is already sharp via the landed
`abs_sum_grahamTheta_div_le_inv_log`). That parametric-in-`g` estimate — a coprimality-Euler
variant of the MoebiusLog Abel machinery — is the genuine analytic residual; see
`docs/blueprints/flags.md` (DH-LCM).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Finset BoundingSieve
open scoped ArithmeticFunction.omega

namespace Salt.SW

open ArithmeticFunction

/-- The squared divisor-collected Graham/Barban–Vehov mollifier `w(n) = (Σ_{d ∣ n} θ_d)²`. -/
noncomputable def grahamW (z n : ℕ) : ℝ := (∑ d ∈ n.divisors, grahamTheta z d) ^ 2

/-- The lcm-collected pair coefficient `gc(m) = Σ_{lcm(d,e)=m} θ_d θ_e`, i.e. mathlib's
Selberg Λ² coefficient of the weight sequence `θ = grahamTheta z`. -/
noncomputable def grahamGc (z m : ℕ) : ℝ := lambdaSquared (grahamTheta z) m

/-- Unfolded form of `grahamGc` as the guarded lcm pair-sum over `m.divisors`. -/
lemma grahamGc_eq (z m : ℕ) :
    grahamGc z m = ∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
      if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0 := by
  simp only [grahamGc, lambdaSquared]

/-! ## L1 — the lcm-collection regroup `w(n) = Σ_{m ∣ n} gc(m)` -/

/-- **L1 (the lcm-collection regroup).** For every `n`, the squared divisor sum equals the
divisor-collected pair coefficients:
`(Σ_{d ∣ n} θ_d)² = Σ_{m ∣ n} gc(m)`. The classical Selberg λ²-regroup, reindexing the
raw double sum by `m = lcm(d,e)`. Closes GrahamWeights' named residual (1). -/
theorem grahamW_eq_sum_grahamGc (z n : ℕ) :
    grahamW z n = ∑ m ∈ n.divisors, grahamGc z m := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [grahamW, grahamGc, lambdaSquared]
  -- Expand each `gc(m)` (m ∣ n) from `m.divisors` to `n.divisors` ranges.
  have hexpand_m : ∀ m ∈ n.divisors, grahamGc z m
      = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
          if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0 := by
    intro m hm
    have hmn : m ∣ n := Nat.dvd_of_mem_divisors hm
    have hm0 : m ≠ 0 := (Nat.pos_of_mem_divisors hm).ne'
    have hsub : m.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn hmn
    have hinner : ∀ d1 : ℕ,
        (∑ d2 ∈ m.divisors,
            if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0)
          = ∑ d2 ∈ n.divisors,
            if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0 := by
      intro d1
      refine Finset.sum_subset hsub (fun d2 _ hd2m => ?_)
      rw [if_neg]
      intro heq
      exact hd2m (Nat.mem_divisors.mpr ⟨by rw [heq]; exact Nat.dvd_lcm_right d1 d2, hm0⟩)
    rw [grahamGc_eq]
    trans (∑ d1 ∈ m.divisors, ∑ d2 ∈ n.divisors,
        if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0)
    · exact Finset.sum_congr rfl (fun d1 _ => hinner d1)
    · refine Finset.sum_subset hsub (fun d1 _ hd1m => ?_)
      refine Finset.sum_eq_zero (fun d2 _ => ?_)
      rw [if_neg]
      intro heq
      exact hd1m (Nat.mem_divisors.mpr ⟨by rw [heq]; exact Nat.dvd_lcm_left d1 d2, hm0⟩)
  -- Reindex: collect the raw double sum by `m = lcm(d1,d2)`.
  have key : ∑ m ∈ n.divisors, grahamGc z m
      = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, grahamTheta z d1 * grahamTheta z d2 := by
    calc ∑ m ∈ n.divisors, grahamGc z m
        = ∑ m ∈ n.divisors, ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
            if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0 :=
          Finset.sum_congr rfl hexpand_m
      _ = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, ∑ m ∈ n.divisors,
            if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun d1 _ => Finset.sum_comm)
      _ = ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, grahamTheta z d1 * grahamTheta z d2 := by
          refine Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => ?_))
          rw [Finset.sum_ite_eq', if_pos]
          exact Nat.mem_divisors.mpr
            ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd1) (Nat.dvd_of_mem_divisors hd2), hn⟩
  rw [grahamW, sq, Finset.sum_mul_sum, key]

/-! ## L2 — the coefficient bounds `gc(m) = 0` off squarefree and `|gc(m)| ≤ 3^ω(m)` -/

/-- If the weight `θ_d ≠ 0` then `d` is squarefree (`μ(d) ≠ 0`). -/
lemma sqfree_of_grahamTheta_ne_zero {z d : ℕ} (h : grahamTheta z d ≠ 0) : Squarefree d := by
  by_contra hsf
  apply h
  rw [grahamTheta]
  split_ifs with hdz
  · rw [moebius_eq_zero_of_not_squarefree hsf]; simp
  · rfl

/-- The `lcm` of two squarefree numbers is squarefree (max-exponent factorization). -/
lemma squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  have hlcm0 : Nat.lcm a b ≠ 0 := by
    simp only [ne_eq, Nat.lcm_eq_zero_iff, not_or]; exact ⟨ha0, hb0⟩
  rw [Nat.squarefree_iff_factorization_le_one hlcm0]
  intro p
  have hpa := (Nat.squarefree_iff_factorization_le_one ha0).mp ha p
  have hpb := (Nat.squarefree_iff_factorization_le_one hb0).mp hb p
  rw [Nat.factorization_lcm ha0 hb0, Finsupp.sup_apply]
  exact sup_le hpa hpb

/-- **L2a.** `gc(m) = 0` unless `m` is squarefree: every nonzero pair `θ_d θ_e` forces
`d, e` squarefree, whence `lcm(d,e) = m` is squarefree. -/
theorem grahamGc_eq_zero_of_not_squarefree {z m : ℕ} (hm : ¬ Squarefree m) :
    grahamGc z m = 0 := by
  rw [grahamGc_eq]
  refine Finset.sum_eq_zero (fun d1 _ => Finset.sum_eq_zero (fun d2 _ => ?_))
  split_ifs with heq
  · by_contra hne
    have h1 : grahamTheta z d1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : grahamTheta z d2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    exact hm (by rw [heq]; exact
      squarefree_lcm (sqfree_of_grahamTheta_ne_zero h1) (sqfree_of_grahamTheta_ne_zero h2))
  · rfl

/-- **L2b.** `|gc(m)| ≤ 3^ω(m)`: bound each `|θ_d θ_e| ≤ 1` and count the lcm-pairs via
`Nat.card_pair_lcm_eq` (the divisor-pair count for squarefree `m`); off squarefree `gc = 0`.
Template: `Salt.SelbergPort.selberg_bound_muPlus`. -/
theorem abs_grahamGc_le {z : ℕ} (hz : 2 ≤ z) (m : ℕ) :
    |grahamGc z m| ≤ (3 : ℝ) ^ ω m := by
  by_cases hsf : Squarefree m
  · rw [grahamGc_eq]
    calc |∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
            if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0|
        ≤ ∑ d1 ∈ m.divisors, |∑ d2 ∈ m.divisors,
            if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors,
            |if m = Nat.lcm d1 d2 then grahamTheta z d1 * grahamTheta z d2 else 0| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors, if m = Nat.lcm d1 d2 then (1 : ℝ) else 0 := by
          gcongr with d1 _ d2 _
          rw [apply_ite abs, abs_zero]
          split_ifs with h
          · rw [abs_mul]
            exact mul_le_one₀ (abs_grahamTheta_le_one hz d1) (abs_nonneg _)
              (abs_grahamTheta_le_one hz d2)
          · exact le_rfl
      _ = ∑ p ∈ m.divisors ×ˢ m.divisors, if m = Nat.lcm p.1 p.2 then (1 : ℝ) else 0 := by
          rw [← Finset.sum_product']
      _ = (((m.divisors ×ˢ m.divisors).filter fun p : ℕ × ℕ => m = Nat.lcm p.1 p.2).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, Nat.smul_one_eq_cast]
      _ = (((m.divisors ×ˢ m.divisors).filter fun p : ℕ × ℕ => p.1.lcm p.2 = m).card : ℝ) := by
          norm_cast; congr 1; ext p; simp only [Finset.mem_filter, eq_comm]
      _ = (3 : ℝ) ^ ω m := by rw [Nat.card_pair_lcm_eq hsf]; push_cast; ring
  · rw [grahamGc_eq_zero_of_not_squarefree hsf, abs_zero]; positivity

/-! ## L3 (structural stone) — the Selberg gcd/totient diagonalization -/

/-- The `g`-restricted Barban–Vehov sum `Σ_{d ≤ z, g ∣ d} θ_d/d` (the diagonal factor). -/
noncomputable def innerG (z g : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 z, if g ∣ d then grahamTheta z d / (d : ℝ) else 0

/-- The totient identity `gcd(d,e) = Σ_{g ≤ z, g ∣ d ∧ g ∣ e} φ(g)` for `1 ≤ d ≤ z`, `1 ≤ e`
(the divisors of `gcd(d,e)` are exactly the common divisors, all `≤ d ≤ z`). -/
lemma sum_totient_indicator_eq_gcd {z d e : ℕ} (hd1 : 1 ≤ d) (hdz : d ≤ z) :
    (∑ g ∈ Finset.Icc 1 z, if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) else 0)
      = (Nat.gcd d e : ℝ) := by
  have hd0 : 0 < d := hd1
  have hgcd0 : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd0
  have hset : (Finset.Icc 1 z).filter (fun g => g ∣ d ∧ g ∣ e) = (Nat.gcd d e).divisors := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨_, hgd, hge⟩; exact ⟨⟨hgd, hge⟩, hgcd0.ne'⟩
    · rintro ⟨⟨hgd, hge⟩, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hgd hd0, le_trans (Nat.le_of_dvd hd0 hgd) hdz⟩, hgd, hge⟩
  rw [← Finset.sum_filter, hset]
  exact_mod_cast Nat.sum_totient (Nat.gcd d e)

/-- **L3 (the Selberg diagonalization).** The lcm-weighted double sum diagonalizes over the
common divisor `g` via `1/lcm(d,e) = gcd(d,e)/(d·e)` and `gcd = Σ_{g ∣ ·} φ`:
`Σ_{d,e ≤ z} θ_d θ_e/lcm(d,e) = Σ_{g ≤ z} φ(g)·(Σ_{g ∣ d, d ≤ z} θ_d/d)²`.
The classical Barban–Vehov / Selberg diagonal quadratic form; reduces the L² mean to the
`g`-restricted BV sums `innerG`. -/
theorem graham_diagonalisation (z : ℕ) :
    ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        grahamTheta z d * grahamTheta z e / (Nat.lcm d e : ℝ)
      = ∑ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * (innerG z g) ^ 2 := by
  have hterm : ∀ d ∈ Finset.Icc 1 z, ∀ e ∈ Finset.Icc 1 z,
      grahamTheta z d * grahamTheta z e / (Nat.lcm d e : ℝ)
        = ∑ g ∈ Finset.Icc 1 z,
            (if g ∣ d then grahamTheta z d / (d : ℝ) else 0)
              * (if g ∣ e then grahamTheta z e / (e : ℝ) else 0) * (Nat.totient g : ℝ) := by
    intro d hd e he
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he1, hez⟩ := Finset.mem_Icc.mp he
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have he0 : (e : ℝ) ≠ 0 := by positivity
    have hlcm0 : (Nat.lcm d e : ℝ) ≠ 0 := by
      have : Nat.lcm d e ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
      exact_mod_cast this
    have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * (e : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    have hBsum := sum_totient_indicator_eq_gcd (z := z) (e := e) hd1 hdz
    have hstep : ∀ g : ℕ,
        (if g ∣ d then grahamTheta z d / (d : ℝ) else 0)
            * (if g ∣ e then grahamTheta z e / (e : ℝ) else 0) * (Nat.totient g : ℝ)
          = (grahamTheta z d / (d : ℝ) * (grahamTheta z e / (e : ℝ)))
              * (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) else 0) := by
      intro g
      rw [ite_zero_mul_ite_zero]
      split_ifs with h <;> ring
    rw [Finset.sum_congr rfl (fun g _ => hstep g), ← Finset.mul_sum, hBsum]
    field_simp
    linear_combination (-(grahamTheta z d * grahamTheta z e)) * hgl
  calc ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        grahamTheta z d * grahamTheta z e / (Nat.lcm d e : ℝ)
      = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z, ∑ g ∈ Finset.Icc 1 z,
          (if g ∣ d then grahamTheta z d / (d : ℝ) else 0)
            * (if g ∣ e then grahamTheta z e / (e : ℝ) else 0) * (Nat.totient g : ℝ) :=
        Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))
    _ = ∑ d ∈ Finset.Icc 1 z, ∑ g ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (if g ∣ d then grahamTheta z d / (d : ℝ) else 0)
            * (if g ∣ e then grahamTheta z e / (e : ℝ) else 0) * (Nat.totient g : ℝ) :=
        Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
    _ = ∑ g ∈ Finset.Icc 1 z, ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (if g ∣ d then grahamTheta z d / (d : ℝ) else 0)
            * (if g ∣ e then grahamTheta z e / (e : ℝ) else 0) * (Nat.totient g : ℝ) :=
        Finset.sum_comm
    _ = ∑ g ∈ Finset.Icc 1 z, (Nat.totient g : ℝ) * (innerG z g) ^ 2 := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        have hfac : ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
              (if g ∣ d then grahamTheta z d / (d : ℝ) else 0)
                * (if g ∣ e then grahamTheta z e / (e : ℝ) else 0) * (Nat.totient g : ℝ)
            = (Nat.totient g : ℝ) * (innerG z g * innerG z g) := by
          unfold innerG
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          ring
        rw [hfac, sq]

/-- The `g = 1` diagonal factor is the full Barban–Vehov value sum `Σ_{d ≤ z} θ_d/d`,
which the LANDED `MoebiusLog.abs_sum_grahamTheta_div_le_inv_log` bounds sharply by `C/log z`.
Thus the dominant `g = 1` term of the diagonal form `Σ_g φ(g)(innerG z g)²` is already
`≤ (C/log z)²`; only the `g ≥ 2` coprime-restricted factors remain (the named residual). -/
lemma innerG_one_eq (z : ℕ) :
    innerG z 1 = ∑ d ∈ Finset.Icc 1 z, grahamTheta z d / (d : ℝ) := by
  unfold innerG
  exact Finset.sum_congr rfl (fun d _ => by rw [if_pos (one_dvd d)])

/-- The diagonal quadratic form is nonnegative: `Σ_{d,e ≤ z} θ_d θ_e/lcm(d,e) ≥ 0` (it equals
`Σ_g φ(g)·(innerG z g)²`, a sum of `φ(g)·squares`). The genuine L² positivity of the object. -/
lemma graham_diagonalisation_nonneg (z : ℕ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        grahamTheta z d * grahamTheta z e / (Nat.lcm d e : ℝ) := by
  rw [graham_diagonalisation]
  exact Finset.sum_nonneg (fun g _ => by positivity)

/-! ## L3a — the harmonic mean reduction `Σ_{n≤N} w(n)/n = Σ_m gc(m)·Σ_{n≤N, m∣n} 1/n` -/

/-- **L3a (the harmonic reduction).** Swapping the divisor sum via L1:
`Σ_{n ≤ N} w(n)/n = Σ_{m ≤ N} gc(m)·(Σ_{n ≤ N, m ∣ n} 1/n)`. The inner harmonic sum is the
classical `(1/m)·(log(N/m) + O(1))`; carrying the SIGN of `gc(m)` through it (against the
Barban–Vehov cancellation) is the sharp route to the L² mean bound. -/
theorem grahamW_mean_eq (z N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, grahamW z n / (n : ℝ)
      = ∑ m ∈ Finset.Icc 1 N, grahamGc z m
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m ∣ n), (n : ℝ)⁻¹ := by
  have hstep : ∀ n ∈ Finset.Icc 1 N, grahamW z n / (n : ℝ)
      = ∑ m ∈ Finset.Icc 1 N, if m ∣ n then grahamGc z m * (n : ℝ)⁻¹ else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hdiv : n.divisors = (Finset.Icc 1 N).filter (fun m => m ∣ n) := by
      ext m
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hmn, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hmn (by omega), le_trans (Nat.le_of_dvd (by omega) hmn) hnN⟩,
          hmn⟩
      · rintro ⟨_, hmn⟩; exact ⟨hmn, by omega⟩
    rw [grahamW_eq_sum_grahamGc, div_eq_mul_inv, Finset.sum_mul, hdiv, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_filter, Finset.mul_sum]

end Salt.SW
