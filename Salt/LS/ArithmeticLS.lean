/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.AnalyticLS
import Salt.LS.Farey

/-!
# Large sieve track, nodes L6.1b + L6.2: the arithmetic large sieve

Blueprint: `docs/blueprints/largesieve.md`.

* **L6.1b** — Farey system assembly. We enumerate the reduced Farey system
  `{(q, a) : 1 ≤ q ≤ Q, a < q, gcd q a = 1}` as a `Finset` of dependent pairs
  (`fareyPairs`), map each pair to its fraction `a/q` (`fareyFrac`), and package
  the pairwise Farey spacing (L6.1) into the `Spaced (1/Q²)` hypothesis that
  `analytic_LS` (L3.1) consumes.  The generic engine is
  `sum_expSum_sq_le_of_spaced`: given any finite index set carrying pairwise
  `dist₁`-separation, the analytic large-sieve bound holds for the corresponding
  `expSum` sum.  The `Fin R` reindexing that `analytic_LS` needs is done once,
  here, via `Fintype.equivFin` on the coe-sort of the finset.

  **Why reducedness matters (but did not in L6.1).**  L6.1 (`farey_spacing`)
  is coprimality-free, but it needs the two fractions to be *distinct* reals.
  Distinctness of the *pairs* only forces distinctness of the *fractions* when
  the fractions are in lowest terms: `a/q = a'/q'` with `gcd q a = gcd q' a' = 1`
  and `a < q, a' < q'` forces `(q,a) = (q',a')`.  This is exactly
  `fareyFrac`-injectivity, proved by cross-multiplication + `Nat.Coprime`
  divisibility (`Nat.Coprime.dvd_of_dvd_mul_left`).

* **L6.2** — the arithmetic large sieve (FROZEN), for `2 ≤ Q`.  Route:
  `sum_expSum_sq_le_of_spaced` at `δ = 1/Q²`, whose gate `δ ≤ 1/2` uses
  `Q² ≥ 4`, and whose `δ⁻¹` reads off as `Q²`.  The `Q = 1` degenerate case
  (`δ = 1` violates the `δ ≤ 1/2` gate) is the separate one-line Cauchy–Schwarz
  corollary `arithmetic_LS_one`.

**Filter-direction convention.**  The blueprint freezes the reduced-residue
filter as `(Finset.range q).filter (Nat.Coprime q)`, i.e. `fun a => Nat.Coprime q a`
(modulus first).  `Salt/Maynard` uses `fun n => Nat.Coprime n B` (residue first);
`Nat.Coprime` is symmetric so the two filters are equal as sets, but we match the
*frozen* statement here (modulus-first).  Downstream L7.3/L8 consumers follow this.
-/

namespace Salt.LS

open scoped BigOperators

/-- **L6.1b.** The reduced Farey system of order `Q`: dependent pairs `(q, a)`
with `1 ≤ q ≤ Q`, `a < q`, and `gcd q a = 1`. -/
def fareyPairs (Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (Nat.Coprime q))

/-- **L6.1b.** The fraction attached to a Farey pair: `(q, a) ↦ a / q`. -/
noncomputable def fareyFrac (x : Σ _ : ℕ, ℕ) : ℝ := (x.2 : ℝ) / (x.1 : ℝ)

@[simp] lemma fareyFrac_mk (q a : ℕ) : fareyFrac ⟨q, a⟩ = (a : ℝ) / q := rfl

/-- **L6.1b (assembly engine).** The analytic large sieve, packaged for an
arbitrary finite index set `S` whose points, mapped by `φ` into `ℝ`, are
pairwise `δ`-separated (mod 1). The `Fin R` reindexing `analytic_LS` requires is
performed here once via `Fintype.equivFin`. -/
theorem sum_expSum_sq_le_of_spaced {ι : Type*} {N : ℕ} {δ : ℝ}
    (S : Finset ι) (φ : ι → ℝ) (c : ℕ → ℂ)
    (hSp : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist₁ (φ x) (φ y))
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ x ∈ S, ‖expSum N c (φ x)‖ ^ 2 ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  classical
  set R := Fintype.card {x // x ∈ S} with hRdef
  set σ : {x // x ∈ S} ≃ Fin R := Fintype.equivFin _ with hσdef
  set α : Fin R → ℝ := fun r => φ ((σ.symm r : {x // x ∈ S}) : ι) with hαdef
  -- The reduced system is `δ`-spaced: distinct `Fin R` indices point to distinct
  -- members of `S`, whose `φ`-images are `δ`-separated by hypothesis.
  have hspaced : Spaced δ α := by
    intro r s hrs
    have hne : σ.symm r ≠ σ.symm s := fun h => hrs (σ.symm.injective h)
    have hval : ((σ.symm r : {x // x ∈ S}) : ι) ≠ ((σ.symm s : {x // x ∈ S}) : ι) :=
      fun h => hne (Subtype.ext h)
    simpa only [hαdef] using hSp _ (σ.symm r).2 _ (σ.symm s).2 hval
  -- Reindex `∑ x ∈ S` through the enumeration `σ`.
  have hreindex : ∑ x ∈ S, ‖expSum N c (φ x)‖ ^ 2 = ∑ r : Fin R, ‖expSum N c (α r)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort S (fun x => ‖expSum N c (φ x)‖ ^ 2)]
    refine Fintype.sum_equiv σ _ _ (fun i => ?_)
    simp only [hαdef, Equiv.symm_apply_apply]
  rw [hreindex]
  exact analytic_LS c hspaced hδ hδ2

/-- **L6.2 — arithmetic large sieve (FROZEN).** For `2 ≤ Q`, the exponential-sum
energy over the reduced Farey fractions of order `Q` is bounded by
`(Q² + 13N)·∑‖cₙ‖²`. -/
theorem arithmetic_LS {N Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖expSum N c ((a : ℝ) / q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  -- `δ = 1/Q²` clears the analytic gate `0 < δ ≤ 1/2` because `Q² ≥ 4`.
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have hQsq : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := one_div_pos.mpr hQsq
  have hδ2 : 1 / (Q : ℝ) ^ 2 ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [hQR]
  -- Pairwise spacing of the Farey system: distinct reduced pairs ⇒ distinct
  -- fractions (reducedness ⇒ injectivity) ⇒ `1/Q²`-separated by `farey_spacing`.
  have hSp : ∀ x ∈ fareyPairs Q, ∀ y ∈ fareyPairs Q, x ≠ y →
      1 / (Q : ℝ) ^ 2 ≤ dist₁ (fareyFrac x) (fareyFrac y) := by
    rintro ⟨q, a⟩ hx ⟨q', a'⟩ hy hxy
    simp only [fareyPairs, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_range] at hx hy
    obtain ⟨⟨hq1, hqQ⟩, ha_lt, hcop⟩ := hx
    obtain ⟨⟨hq'1, hq'Q⟩, ha'_lt, hcop'⟩ := hy
    have hqpos : 0 < q := hq1
    have hq'pos : 0 < q' := hq'1
    have hfrac_ne : (a : ℝ) / q ≠ (a' : ℝ) / q' := by
      intro heq
      apply hxy
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
      have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'pos
      rw [div_eq_div_iff hqR.ne' hq'R.ne'] at heq
      have heqN : a * q' = a' * q := by exact_mod_cast heq
      -- coprimality turns the cross-relation into `q = q'` and `a = a'`
      have hdvd1 : q ∣ q' := hcop.dvd_of_dvd_mul_left ⟨a', by rw [heqN]; ring⟩
      have hdvd2 : q' ∣ q := hcop'.dvd_of_dvd_mul_left ⟨a, by rw [← heqN]; ring⟩
      have hq_eq : q = q' := Nat.dvd_antisymm hdvd1 hdvd2
      have ha_eq : a = a' := by
        have hh := heqN
        rw [hq_eq] at hh
        exact Nat.eq_of_mul_eq_mul_right hq'pos hh
      rw [hq_eq, ha_eq]
    simp only [fareyFrac_mk]
    exact farey_spacing hqpos hq'pos hqQ hq'Q ha_lt ha'_lt hfrac_ne
  -- Assemble: the engine at `δ = 1/Q²`, then read off `δ⁻¹ = Q²`.
  have hkey := sum_expSum_sq_le_of_spaced (N := N) (fareyPairs Q) fareyFrac c hSp hδ hδ2
  have hcoef : (1 / (Q : ℝ) ^ 2)⁻¹ = (Q : ℝ) ^ 2 := by rw [one_div, inv_inv]
  rw [hcoef] at hkey
  have hrewrite : ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖expSum N c ((a : ℝ) / q)‖ ^ 2 = ∑ x ∈ fareyPairs Q, ‖expSum N c (fareyFrac x)‖ ^ 2 := by
    rw [fareyPairs, Finset.sum_sigma']
    simp only [fareyFrac]
  rw [hrewrite]
  exact hkey

/-- **L6.2 corollary — the `Q = 1` case.** Here `δ = 1/Q² = 1` violates the
`δ ≤ 1/2` gate of `analytic_LS`, so this degenerate case is proved directly by
Cauchy–Schwarz: the single Farey point is `0/1 = 0`, and
`‖∑ cₙ‖² ≤ N·∑‖cₙ‖² ≤ (1 + 13N)·∑‖cₙ‖²`. -/
theorem arithmetic_LS_one {N : ℕ} (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 1, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖expSum N c ((a : ℝ) / q)‖ ^ 2 ≤ (1 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  -- The `q = 1` system is the single point `0/1 = 0`.
  have hfilter : (Finset.range 1).filter (Nat.Coprime 1) = {0} := by
    ext a
    simp
  have hexp0 : expSum N c 0 = ∑ n ∈ Finset.range N, c n := by
    unfold expSum
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_zero, e_zero, mul_one]
  rw [Finset.Icc_self, Finset.sum_singleton, hfilter, Finset.sum_singleton]
  simp only [Nat.cast_zero, Nat.cast_one, zero_div]
  rw [hexp0]
  -- Cauchy–Schwarz: `‖∑ cₙ‖² ≤ (∑‖cₙ‖)² ≤ N·∑‖cₙ‖² ≤ (1 + 13N)·∑‖cₙ‖²`.
  have hnorm_sum : ‖∑ n ∈ Finset.range N, c n‖ ≤ ∑ n ∈ Finset.range N, ‖c n‖ :=
    norm_sum_le _ _
  have hcs : (∑ n ∈ Finset.range N, ‖c n‖) ^ 2 ≤ (N : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun n => ‖c n‖)
    simpa [Finset.card_range] using h
  have hsq : ‖∑ n ∈ Finset.range N, c n‖ ^ 2 ≤ (∑ n ∈ Finset.range N, ‖c n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_sum 2
  have hS2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hNle : (N : ℝ) ≤ 1 + 13 * (N : ℝ) := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  calc ‖∑ n ∈ Finset.range N, c n‖ ^ 2
      ≤ (∑ n ∈ Finset.range N, ‖c n‖) ^ 2 := hsq
    _ ≤ (N : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := hcs
    _ ≤ (1 + 13 * (N : ℝ)) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hNle hS2

end Salt.LS
