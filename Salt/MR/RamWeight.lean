/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareWindows
import Salt.MR.HalaszLambda
import Salt.MR.PrimeSigmaShift

/-!
# RamWeight — the Ramaré-weight multiplicativization (U-7, stone U7-B)

The Ramaré weight `1/(ω(m;P,Q)+1)` sitting inside `ramR` (`RamareWindows.lean:74`) is
**not multiplicative** in `m`, so the co-factor polynomial `R_{j,H}` is not a Dirichlet
polynomial with a multiplicative datum and the Halász machinery cannot see it.  The repair
(the ⟦V5⟧ plan's `W2`) is the integral representation

  `1/(ω+1) = ∫₀¹ x^ω dx`,

whose integrand `x^{ω(m;P,Q)}` **is** multiplicative in `m`; on the squarefree support of
`ellLin` it is absorbed into the *prime datum*:

  `ellLin (gxDatum g P Q x) m = ellLin g m · x^{ω(m;P,Q)}`,   `‖gxDatum g P Q x p‖ ≤ 1`
  for `x ∈ [0,1]`.

So the weighted co-factor sum becomes a one-parameter family of *honest* `ellLin`-datum
Dirichlet polynomials, and the weight is paid once, at the end, by a `[0,1]` integral.

## The stones

* §1 `integral_pow_unit` / `integral_cpow_unit` / `inv_blockOmega_succ_eq_integral` — B-1,
  the integral representation of the weight (`∫₀¹ xⁿ dx = 1/(n+1)`, real and complex).
* §2 `blockOmega_mul_coprime` / `blockOmega_pow_mul_coprime` — B-2, `ω(·;P,Q)` is additive
  on coprimes (disjoint prime-factor windows), hence `x^ω` is multiplicative.
* §3 `gxDatum` / `gxDatum_norm_le_one` / `ellLin_gxDatum` — B-3, the damped prime datum,
  its `1`-boundedness on `[0,1]`, and the **absorption identity** (unconditional: the
  non-squarefree and `0` slots are `0 = 0 · x^ω`).
* §4 `ramRdamp` / `ramR_eq_integral_damp` / `ramR_norm_le_of_damp_le` — B-4, the
  finite-sum ↔ interval-integral interchange and **the exit shape**: a bound on the damped
  polynomial *uniform over `x ∈ [0,1]`* is a bound on `ramR` itself.  Bridges to `spoly`
  (`ramRdamp_eq_spoly`) and to the `gxDatum` datum (`ramRdamp_ellLin`) ship with it.
* §5 `gxDatum_pretDistSq_ge` / `gxDatum_pretDistSq_ge_one` — B-5, the one-sided distance
  loss: damping the block primes by `x ∈ [0,1]` costs at most `(1−x)·Σ_{P≤p≤Q, p≤X} 1/p`
  (**factor 1, not 2**).  The Mertens evaluation of that window sum is U7-C's, not this
  file's: the exit is the abstract `Σ 1/p` over `blockWindowPrimes`.

Nothing here is `P`/`Q`/`H`-specific: every statement is in the abstract window.
-/

namespace Salt.MR

open Finset Complex MeasureTheory
open scoped BigOperators

/-! ## §1 (B-1) — the weight as a `[0,1]` integral -/

/-- **B-1 (real).**  `∫₀¹ xⁿ dx = 1/(n+1)`. -/
lemma integral_pow_unit (n : ℕ) : (∫ x in (0:ℝ)..1, x ^ n) = ((n : ℝ) + 1)⁻¹ := by
  rw [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, one_div]

/-- **B-1 (complex).**  `∫₀¹ xⁿ dx = 1/(n+1)` with the monomial read in `ℂ` (the
`Nat`-power form; no `rpow` anywhere). -/
lemma integral_cpow_unit (n : ℕ) : (∫ x in (0:ℝ)..1, ((x : ℝ) : ℂ) ^ n) = ((n : ℂ) + 1)⁻¹ := by
  have hfun : (fun x : ℝ => ((x : ℝ) : ℂ) ^ n) = fun x : ℝ => ((x ^ n : ℝ) : ℂ) := by
    funext x; push_cast; ring
  rw [hfun, intervalIntegral.integral_ofReal, integral_pow_unit]
  push_cast
  ring

/-- **B-1, at the Ramaré weight.**  The weight `(ω(m;P,Q)+1)⁻¹` carried by `ramR` is the
`[0,1]` integral of the *multiplicative* monomial `x^{ω(m;P,Q)}`. -/
theorem inv_blockOmega_succ_eq_integral (P Q m : ℕ) :
    (((blockOmega P Q m : ℂ)) + 1)⁻¹ = ∫ x in (0:ℝ)..1, ((x : ℝ) : ℂ) ^ blockOmega P Q m :=
  (integral_cpow_unit _).symm

/-! ## §2 (B-2) — `ω(·;P,Q)` is additive on coprimes, so `x^ω` is multiplicative -/

/-- The block prime divisors of a coprime product split as a disjoint union. -/
lemma blockPrimeDivs_mul_coprime {P Q m n : ℕ} (hco : m.Coprime n) :
    BlockPrimeDivs P Q (m * n) = BlockPrimeDivs P Q m ∪ BlockPrimeDivs P Q n := by
  unfold BlockPrimeDivs
  rw [Nat.Coprime.primeFactors_mul hco, Finset.filter_union]

/-- **B-2 (additivity).**  `ω(mn;P,Q) = ω(m;P,Q) + ω(n;P,Q)` for coprime `m n`: the block
prime divisors of `m` and of `n` are disjoint, so their windows just add. -/
theorem blockOmega_mul_coprime {P Q m n : ℕ} (hco : m.Coprime n) :
    blockOmega P Q (m * n) = blockOmega P Q m + blockOmega P Q n := by
  unfold blockOmega
  rw [blockPrimeDivs_mul_coprime hco]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hco.disjoint_primeFactors)

/-- **B-2 (the multiplicative monomial).**  `x^{ω(mn;P,Q)} = x^{ω(m;P,Q)}·x^{ω(n;P,Q)}` on
coprimes — the property the Ramaré weight itself lacks. -/
theorem blockOmega_pow_mul_coprime (x : ℂ) {P Q m n : ℕ} (hco : m.Coprime n) :
    x ^ blockOmega P Q (m * n) = x ^ blockOmega P Q m * x ^ blockOmega P Q n := by
  rw [blockOmega_mul_coprime hco, pow_add]

/-! ## §3 (B-3) — the damped prime datum `g_x` and the absorption identity -/

/-- **B-3 datum.**  The `x`-damped prime datum: `g_x(p) = g(p)·x` for `P ≤ p ≤ Q`, and
`g_x(p) = g(p)` off the window.  For `x ∈ [0,1]` it inherits `g`'s `1`-boundedness
(`gxDatum_norm_le_one`), so every `hg`-style hypothesis downstream survives. -/
noncomputable def gxDatum (g : ℕ → ℂ) (P Q : ℕ) (x : ℝ) : ℕ → ℂ :=
  fun p => g p * (if P ≤ p ∧ p ≤ Q then (x : ℂ) else 1)

/-- **B-3.**  `‖g_x(p)‖ ≤ 1` for `x ∈ [0,1]` whenever `‖g(p)‖ ≤ 1`. -/
theorem gxDatum_norm_le_one {g : ℕ → ℂ} {P Q : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (p : ℕ) (hp : p.Prime) :
    ‖gxDatum g P Q x p‖ ≤ 1 := by
  have h2 : ‖(if P ≤ p ∧ p ≤ Q then (x : ℂ) else 1)‖ ≤ 1 := by
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
    · simp
  calc ‖gxDatum g P Q x p‖
      = ‖g p‖ * ‖(if P ≤ p ∧ p ≤ Q then (x : ℂ) else 1)‖ := by rw [gxDatum, norm_mul]
    _ ≤ 1 * 1 := mul_le_mul (hg p hp) h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The window indicator product over any finite prime set is the monomial `x^{#window}`. -/
lemma prod_window_ite (P Q : ℕ) (x : ℂ) (s : Finset ℕ) :
    (∏ p ∈ s, (if P ≤ p ∧ p ≤ Q then x else 1))
      = x ^ (s.filter (fun p => P ≤ p ∧ p ≤ Q)).card := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.filter_insert]
      split_ifs with h
      · have hna : a ∉ s.filter (fun p => P ≤ p ∧ p ≤ Q) := fun hmem =>
          ha (Finset.mem_of_mem_filter a hmem)
        rw [Finset.card_insert_of_notMem hna, pow_succ]
        ring
      · rw [one_mul]

/-- **B-3, THE ABSORPTION IDENTITY.**  The `x`-damped datum's squarefree lift is the
original lift times the multiplicative monomial:

  `ellLin (g_x) m = ellLin g m · x^{ω(m;P,Q)}`.

Unconditional in `m`: on non-squarefree `m` (and at `m = 0`) both sides are `0`; on
squarefree `m` the product over `m.primeFactors` splits and the window factor collects
exactly `ω(m;P,Q)` copies of `x`. -/
theorem ellLin_gxDatum (g : ℕ → ℂ) (P Q : ℕ) (x : ℝ) (m : ℕ) :
    ellLin (gxDatum g P Q x) m = ellLin g m * ((x : ℝ) : ℂ) ^ blockOmega P Q m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [ellLin]
  unfold ellLin
  rw [if_neg hm, if_neg hm]
  by_cases hsq : Squarefree m
  · rw [if_pos hsq, if_pos hsq]
    have hsplit : (∏ p ∈ m.primeFactors, gxDatum g P Q x p)
        = (∏ p ∈ m.primeFactors, g p)
          * ∏ p ∈ m.primeFactors, (if P ≤ p ∧ p ≤ Q then ((x : ℝ) : ℂ) else 1) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun p _ => rfl)
    rw [hsplit, prod_window_ite]
    rfl
  · rw [if_neg hsq, if_neg hsq, zero_mul]

/-! ## §4 (B-4) — the damped co-factor polynomial and the weight interchange -/

/-- **B-4 datum.**  The `x`-damped co-factor polynomial: `ramR` with the Ramaré weight
`(ω+1)⁻¹` replaced by the multiplicative monomial `x^{ω}`. -/
noncomputable def ramRdamp (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (x t : ℝ) : ℂ :=
  ∑ m ∈ ramRrange H N X j,
    (b m * ((x : ℝ) : ℂ) ^ blockOmega P Q m) / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)

/-- `x ↦ ramRdamp … x t` is continuous (a finite sum of polynomials in `x`). -/
lemma continuous_ramRdamp (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    Continuous (fun x : ℝ => ramRdamp H N X P Q j b x t) := by
  unfold ramRdamp
  refine continuous_finsetSum _ (fun m _ => ?_)
  fun_prop

/-- **B-4, THE INTERCHANGE.**  The Ramaré-weighted co-factor polynomial is the `[0,1]`
average of the damped ones:  `R_{j,H}(1+it) = ∫₀¹ R_{j,H}^{(x)}(1+it) dx`.  Finite sum
against interval integral (`intervalIntegral.integral_finsetSum`; every summand is a
continuous — indeed polynomial — function of `x`). -/
theorem ramR_eq_integral_damp (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    ramR H N X P Q j b t = ∫ x in (0:ℝ)..1, ramRdamp H N X P Q j b x t := by
  unfold ramRdamp
  rw [intervalIntegral.integral_finsetSum (fun m _ => (by fun_prop : Continuous
    (fun x : ℝ => (b m * ((x : ℝ) : ℂ) ^ blockOmega P Q m)
      / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))).intervalIntegrable _ _)]
  rw [ramR]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hfun : (fun x : ℝ => (b m * ((x : ℝ) : ℂ) ^ blockOmega P Q m)
        / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
      = fun x : ℝ => (b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
        * ((x : ℝ) : ℂ) ^ blockOmega P Q m := by
    funext x; ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_cpow_unit]

/-- **B-4, THE EXIT SHAPE** (the one U7-E/F consume).  A bound on the damped polynomial
that is *uniform over `x ∈ [0,1]`* is a bound on `ramR` itself — no integrability side
condition survives to the consumer (`norm_integral_le_of_norm_le_const` over the unit
interval, whose length is `1`).

This is the cheaper of the two candidate exits: the alternative
`‖ramR t‖ ≤ ∫₀¹ ‖ramRdamp x t‖ dx` would hand U7-E/F an integral they must then bound
uniformly anyway, *plus* an integrability obligation for `x ↦ ‖ramRdamp x t‖`. -/
theorem ramR_norm_le_of_damp_le {H : ℝ} {N X P Q j : ℕ} {b : ℕ → ℂ} {t B : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖ramRdamp H N X P Q j b x t‖ ≤ B) :
    ‖ramR H N X P Q j b t‖ ≤ B := by
  rw [ramR_eq_integral_damp]
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖ramRdamp H N X P Q j b x t‖ ≤ B := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact h x ⟨hx.1.le, hx.2⟩
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- **B-4, the `spoly` bridge** (for U7-A's Abel/adapter page): the damped co-factor
polynomial is a `spoly` with the coefficients cut down to the co-factor range. -/
lemma ramRdamp_eq_spoly (H : ℝ) (N X P Q j : ℕ) (b : ℕ → ℂ) (x t : ℝ) :
    ramRdamp H N X P Q j b x t
      = spoly N (fun m => if m ∈ ramRrange H N X j
          then b m * ((x : ℝ) : ℂ) ^ blockOmega P Q m else 0) t := by
  have hsub : ramRrange H N X j ⊆ Finset.Icc 1 N := by
    intro m hm
    rw [ramRrange, Finset.mem_filter] at hm
    exact hm.1
  rw [spoly, ← Finset.sum_subset hsub (fun m _ hnm => by simp [hnm]), ramRdamp]
  exact Finset.sum_congr rfl (fun m hm => by simp [hm])

/-- **B-4, the datum bridge.**  With an `ellLin`-datum coefficient the damped polynomial is
literally the `ellLin` polynomial of the damped prime datum `g_x` — the multiplicative
object the Halász machinery wants (`ellLin_gxDatum`). -/
lemma ramRdamp_ellLin (H : ℝ) (N X P Q j : ℕ) (g : ℕ → ℂ) (x t : ℝ) :
    ramRdamp H N X P Q j (ellLin g) x t
      = ∑ m ∈ ramRrange H N X j,
          ellLin (gxDatum g P Q x) m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
  rw [ramRdamp]
  exact Finset.sum_congr rfl (fun m _ => by rw [ellLin_gxDatum])

/-! ## §5 (B-5) — the one-sided distance loss of the damping -/

/-- The primes of the block window `[P,Q]` that the distance at scale `X` can see.  The
window sum `Σ 1/p` over this set is the *entire* price of the damping (`gxDatum_pretDistSq_ge`);
its Mertens evaluation `≤ θ·loglog X + C` is U7-C's page, not this file's. -/
noncomputable def blockWindowPrimes (P Q : ℕ) (X : ℝ) : Finset ℕ :=
  ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p => P ≤ p ∧ p ≤ Q)

/-- The scale-truncated window sits inside the full block window `[P,Q]` — the handoff to
U7-C, whose Mertens page evaluates the *untruncated* `Σ_{P≤p≤Q} 1/p`. -/
lemma blockWindowPrimes_subset (P Q : ℕ) (X : ℝ) :
    blockWindowPrimes P Q X ⊆ (Finset.Icc P Q).filter Nat.Prime := by
  intro p hp
  rw [blockWindowPrimes, Finset.mem_filter, Finset.mem_filter] at hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp.2, hp.1.2⟩

/-- The price of the damping, released from the scale truncation: `Σ_{P≤p≤Q, p≤X} 1/p ≤
Σ_{P≤p≤Q} 1/p`.  Composing with `gxDatum_pretDistSq_ge_one` puts U7-C's Mertens window
evaluation directly on the exit. -/
lemma sum_blockWindowPrimes_le (P Q : ℕ) (X : ℝ) :
    ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
  Finset.sum_le_sum_of_subset_of_nonneg (blockWindowPrimes_subset P Q X)
    (fun p _ _ => by positivity)

/-- **B-5, THE SHARP FORM.**  Damping the block primes by `x ∈ [0,1]` lowers the
pretentious distance by at most `(1−x)·Σ_{P≤p≤Q, p≤X} 1/p`.

The per-prime page (`w` any `1`-bounded twist, `u = g(p)·conj w(p)`, `|Re u| ≤ ‖u‖ ≤ 1`):
off the window the two terms are *equal*; on the window

  `(1 − Re u) − (1 − x·Re u) = (1−x)·Re u ≥ −(1−x)`,

so the loss is `(1−x)·(−Re u) ≤ (1−x)` per prime — **factor 1, not 2** — summed against
`1/p` over the window.  (Both `(1−x) ≥ 0` and `−Re u ≤ 1` are used; nothing is discarded.) -/
theorem gxDatum_pretDistSq_ge {g w : ℕ → ℂ} {P Q : ℕ} {x X : ℝ}
    (hx1 : x ≤ 1) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (hw : ∀ p : ℕ, p.Prime → ‖w p‖ ≤ 1) :
    pretDistSq (ellLin g) w X - (1 - x) * ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ pretDistSq (ellLin (gxDatum g P Q x)) w X := by
  have hx1' : (0 : ℝ) ≤ 1 - x := by linarith
  set Pr := (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime with hPrdef
  -- the per-prime page
  have key : ∀ p ∈ Pr,
      (1 - (ellLin g p * (starRingEnd ℂ) (w p)).re) / (p : ℝ)
          - (if P ≤ p ∧ p ≤ Q then (1 - x) * (1 / (p : ℝ)) else 0)
        ≤ (1 - (ellLin (gxDatum g P Q x) p * (starRingEnd ℂ) (w p)).re) / (p : ℝ) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hgp : ellLin g p = g p := ellLin_apply_prime g hpp
    have hgxp : ellLin (gxDatum g P Q x) p = gxDatum g P Q x p :=
      ellLin_apply_prime (gxDatum g P Q x) hpp
    -- the atom and its real part
    set u : ℂ := g p * (starRingEnd ℂ) (w p) with hu
    have hunorm : ‖u‖ ≤ 1 := by
      rw [hu, norm_mul, RCLike.norm_conj]
      calc ‖g p‖ * ‖w p‖ ≤ 1 * 1 := mul_le_mul (hg p hpp) (hw p hpp) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hure : |u.re| ≤ 1 := le_trans (Complex.abs_re_le_norm u) hunorm
    have hure' : -1 ≤ u.re := (abs_le.mp hure).1
    rw [hgp, hgxp, gxDatum]
    by_cases hwin : P ≤ p ∧ p ≤ Q
    · rw [if_pos hwin, if_pos hwin]
      have hre : ((g p * ((x : ℝ) : ℂ)) * (starRingEnd ℂ) (w p)).re = x * u.re := by
        rw [show (g p * ((x : ℝ) : ℂ)) * (starRingEnd ℂ) (w p)
            = ((x : ℝ) : ℂ) * u by rw [hu]; ring, Complex.re_ofReal_mul]
      rw [hre]
      have hnum : (1 - u.re) - (1 - x) * 1 ≤ 1 - x * u.re := by nlinarith
      calc (1 - u.re) / (p : ℝ) - (1 - x) * (1 / (p : ℝ))
          = ((1 - u.re) - (1 - x) * 1) * ((p : ℝ)⁻¹) := by field_simp
        _ ≤ (1 - x * u.re) * ((p : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hppos.le)
        _ = (1 - x * u.re) / (p : ℝ) := by rw [div_eq_mul_inv]
    · rw [if_neg hwin, if_neg hwin, mul_one, sub_zero]
  -- sum the page, then read the two sides
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib] at hsum
  have hwin : ∑ p ∈ Pr, (if P ≤ p ∧ p ≤ Q then (1 - x) * (1 / (p : ℝ)) else 0)
      = (1 - x) * ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ) := by
    rw [blockWindowPrimes, ← hPrdef, Finset.mul_sum, ← Finset.sum_filter]
  rw [hwin] at hsum
  simpa [pretDistSq, ← hPrdef] using hsum

/-- **B-5, the factor-`1` corollary** (the shape U7-C's Mertens page consumes): for
`x ∈ [0,1]` the damping loses at most the *undamped* window sum `Σ_{P≤p≤Q, p≤X} 1/p`. -/
theorem gxDatum_pretDistSq_ge_one {g w : ℕ → ℂ} {P Q : ℕ} {x X : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    (hw : ∀ p : ℕ, p.Prime → ‖w p‖ ≤ 1) :
    pretDistSq (ellLin g) w X - ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ pretDistSq (ellLin (gxDatum g P Q x)) w X := by
  have hbase := gxDatum_pretDistSq_ge (g := g) (w := w) (P := P) (Q := Q) (X := X) hx1 hg hw
  have hnn : 0 ≤ ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => by positivity)
  nlinarith [hbase, hnn]

/-- **B-5 at the `costwist` twist** (the live consumer's shape): the damped datum's
distance to `p^{it}` drops by at most the block-window sum. -/
theorem gxDatum_pretDistSq_costwist {g : ℕ → ℂ} {P Q : ℕ} {x X t : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) :
    pretDistSq (ellLin g) (costwist t) X
        - ∑ p ∈ blockWindowPrimes P Q X, (1 : ℝ) / (p : ℝ)
      ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist t) X :=
  gxDatum_pretDistSq_ge_one hx0 hx1 hg (fun p _ => le_of_eq (costwist_norm t p))

end Salt.MR
