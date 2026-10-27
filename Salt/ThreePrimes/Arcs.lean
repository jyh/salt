/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ThreePrimes.MinorArc

/-!
# Three primes: the major and minor arcs

These are lemma L4 and the minor-arc half of Step 6 of the three-primes plan
(`docs/plans/three-primes-PLAN.md`, Steps 2 and 6a).

Fix `P ≥ 1` and the half-width `δ = P/N`. **The major arc** at a fraction `a/q`, with `q ≤ P`,
`1 ≤ a ≤ q` and `gcd(a, q) = 1`, is the interval `[a/q − δ, a/q + δ]`. We work on the period window
`(δ, 1 + δ]` instead of `[0, 1)`. The arc at `1/1` then sits inside the window, at `1`, rather than
wrapping around `0`, and every other arc sits inside it too once `N > 2P²`.

* **The arcs are disjoint** once `N > 2P³`. Two distinct fractions with denominators at most `P`
  differ by at least `1/(qq′) ≥ 1/P²`, which exceeds `2δ = 2P/N`. This is what lets the major-arc
  integral be computed one arc at a time, each with its own approximation.
* **Off the arcs, `S` is small.** For `α` in the window and on no arc, Dirichlet's theorem with
  `Q = ⌊N/P⌋` gives a fraction `a/q` in lowest terms, `q ≤ Q`, with `|α − a/q| ≤ 1/(q(Q + 1))`. That
  is within `δ` of `a/q`. Suppose `q ≤ P`. Then `1 ≤ a ≤ q`: `a/q` is within `δ` of `α > δ`, so
  `a ≥ 1`; and `a > q` would give `a/q ≥ 1 + 1/q ≥ 1 + 1/P > 1 + 2δ` (as `N > 2P²`), too far above
  `α ≤ 1 + δ`. So `α` is on the arc at `a/q`, which it is not. Hence `P < q ≤ N/P`, and also
  `|α − a/q| ≤ 1/q²`.
  Vinogradov's estimate (`norm_primeExpSum_le_minor`) then gives `N/√q ≤ N/√P` and `√(Nq) ≤ N/√P`:

    `|S(α)| ≤ K (2N/√P + N^{7/8}) (log N)³`.
-/

namespace Salt.ThreePrimes

/-- **The major arc** at `a/q`: the interval `[a/q − P/N, a/q + P/N]`. -/
def majorArc (N P q a : ℕ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - (P : ℝ) / N) ((a : ℝ) / q + (P : ℝ) / N)

/-- **The arcs' labels** `(q, a)`: `1 ≤ q ≤ P`, `1 ≤ a ≤ q`, `gcd(a, q) = 1`. -/
def arcIndex (P : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 P) ×ˢ (Finset.Icc 1 P)).filter (fun x => x.2 ≤ x.1 ∧ Nat.Coprime x.2 x.1)

/-- Two fractions `a/q` and `a'/q'` with `aq' ≠ a'q` are at least `1/(qq')` apart. -/
theorem one_div_mul_le_abs_sub_div {a q a' q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hne : a * q' ≠ a' * q) : 1 / ((q : ℝ) * q') ≤ |(a : ℝ) / q - (a' : ℝ) / q'| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  set d : ℤ := ((a * q' : ℕ) : ℤ) - ((a' * q : ℕ) : ℤ) with hd
  have hd0 : d ≠ 0 := by
    intro h
    apply hne
    exact_mod_cast sub_eq_zero.mp h
  have hdiff : (a : ℝ) / q - (a' : ℝ) / q' = (d : ℝ) / ((q : ℝ) * q') := by
    rw [hd]; push_cast; field_simp
  have h1 : (1 : ℝ) ≤ |(d : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hd0
  rw [hdiff, abs_div, abs_of_pos (mul_pos hqR hq'R)]
  exact div_le_div_of_nonneg_right h1 (mul_pos hqR hq'R).le

/-- **The major arcs are disjoint** once `N > 2P³`: distinct fractions with denominators at most
`P` are at least `1/P²` apart, more than `2P/N`, the two arcs' half-widths added. -/
theorem majorArc_disjoint {N P : ℕ} (hN : 2 * P ^ 3 < N) {x y : ℕ × ℕ} (hx : x ∈ arcIndex P)
    (hy : y ∈ arcIndex P) (hxy : x ≠ y) :
    Disjoint (majorArc N P x.1 x.2) (majorArc N P y.1 y.2) := by
  obtain ⟨q, a⟩ := x
  obtain ⟨q', a'⟩ := y
  simp only [arcIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx hy
  obtain ⟨⟨⟨hq1, hqP⟩, ha1, -⟩, haq, hcop⟩ := hx
  obtain ⟨⟨⟨hq1', hqP'⟩, ha1', -⟩, haq', hcop'⟩ := hy
  have hne : a * q' ≠ a' * q := by
    intro h
    have h1 : q ∣ q' := by
      have : q ∣ q' * a := ⟨a', by rw [mul_comm q' a, h, mul_comm]⟩
      exact hcop.symm.dvd_of_dvd_mul_right this
    have h2 : q' ∣ q := by
      have : q' ∣ q * a' := ⟨a, by rw [mul_comm q a', ← h, mul_comm]⟩
      exact hcop'.symm.dvd_of_dvd_mul_right this
    have hqq : q = q' := Nat.dvd_antisymm h1 h2
    subst hqq
    have : a = a' := Nat.eq_of_mul_eq_mul_right (by omega) h
    exact hxy (by rw [this])
  have hsep := one_div_mul_le_abs_sub_div (by omega : 0 < q) (by omega : 0 < q') hne
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast (le_trans hq1 hqP)
  have hNR : (2 : ℝ) * (P : ℝ) ^ 3 < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) < (P : ℝ) ^ 3 := by positivity
    linarith
  have hqq : (q : ℝ) * q' ≤ (P : ℝ) ^ 2 := by
    have : (q : ℝ) ≤ P := by exact_mod_cast hqP
    have : (q' : ℝ) ≤ P := by exact_mod_cast hqP'
    have : (0 : ℝ) ≤ q := by positivity
    have : (0 : ℝ) ≤ q' := by positivity
    nlinarith
  have hqqpos : (0 : ℝ) < (q : ℝ) * q' := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have : (1 : ℝ) ≤ q' := by exact_mod_cast hq1'
    nlinarith
  -- `2P/N < 1/P² ≤ 1/(qq')`
  have hwidth : 2 * ((P : ℝ) / N) < 1 / ((q : ℝ) * q') := by
    rw [lt_div_iff₀ hqqpos]
    calc 2 * ((P : ℝ) / N) * ((q : ℝ) * q') ≤ 2 * ((P : ℝ) / N) * (P : ℝ) ^ 2 := by
          gcongr
      _ = 2 * (P : ℝ) ^ 3 / N := by ring
      _ < 1 := by rw [div_lt_one hNpos]; exact hNR
  rw [Set.disjoint_left]
  intro t ht ht'
  simp only [majorArc, Set.mem_Icc] at ht ht'
  have : |(a : ℝ) / q - (a' : ℝ) / q'| ≤ 2 * ((P : ℝ) / N) := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  linarith

/-- **Every major arc lies in the window** `(P/N, 1 + P/N]` once `N > 2P²`. -/
theorem majorArc_subset_window {N P : ℕ} (hP : 1 ≤ P) (hN : 2 * P ^ 2 < N) {x : ℕ × ℕ}
    (hx : x ∈ arcIndex P) :
    majorArc N P x.1 x.2 ⊆ Set.Ioc ((P : ℝ) / N) (1 + (P : ℝ) / N) := by
  obtain ⟨q, a⟩ := x
  simp only [arcIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  obtain ⟨⟨⟨hq1, hqP⟩, ha1, -⟩, haq, -⟩ := hx
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hNR : (2 : ℝ) * (P : ℝ) ^ 2 < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqPR : (q : ℝ) ≤ P := by exact_mod_cast hqP
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have haqR : (a : ℝ) ≤ q := by exact_mod_cast haq
  -- `a/q ≥ 1/P > 2P/N`
  have hlow : 2 * ((P : ℝ) / N) < (a : ℝ) / q := by
    have h1 : 1 / (P : ℝ) ≤ (a : ℝ) / q := by
      rw [div_le_div_iff₀ (by linarith) hqR]; nlinarith
    have h2 : 2 * ((P : ℝ) / N) < 1 / (P : ℝ) := by
      rw [lt_div_iff₀ (by linarith)]
      calc 2 * ((P : ℝ) / N) * P = 2 * (P : ℝ) ^ 2 / N := by ring
        _ < 1 := by rw [div_lt_one hNpos]; exact hNR
    linarith
  have hup : (a : ℝ) / q ≤ 1 := by rw [div_le_one hqR]; exact haqR
  intro t ht
  simp only [majorArc, Set.mem_Icc] at ht
  constructor <;> linarith [ht.1, ht.2]

/-- **The off-arc approximation.** For `α` in the window and on no major arc, there is a fraction
`a/q` in lowest terms with `P < q ≤ N/P` and `|α − a/q| ≤ 1/q²` (Dirichlet at order `⌊N/P⌋`). -/
theorem exists_minor_approx {N P : ℕ} {α : ℝ} (hP : 1 ≤ P) (hN : 2 * P ^ 2 < N)
    (hα : α ∈ Set.Ioc ((P : ℝ) / N) (1 + (P : ℝ) / N))
    (hoff : ∀ x ∈ arcIndex P, α ∉ majorArc N P x.1 x.2) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ Int.gcd a (q : ℤ) = 1 ∧ P < q ∧ (q : ℝ) ≤ (N : ℝ) / P ∧
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
  have hPN : P ≤ N := by nlinarith
  have hQ : 0 < N / P := Nat.div_pos hPN (by omega)
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  set q := r.den with hqdef
  set a := r.num with hadef
  have hq0 : 0 < q := r.den_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hNR : (2 : ℝ) * (P : ℝ) ^ 2 < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hrcast : ((r : ℝ)) = (a : ℝ) / (q : ℝ) := by
    rw [hadef, hqdef]; exact Rat.cast_def r
  rw [hrcast] at hr
  have hQR : ((N / P : ℕ) : ℝ) ≤ (N : ℝ) / P := Nat.cast_div_le
  have hQ1 : (N : ℝ) / P ≤ ((N / P : ℕ) : ℝ) + 1 := by
    have h := Nat.lt_div_mul_add (a := N) (b := P) (by omega)
    have h' : (N : ℝ) ≤ ((N / P : ℕ) : ℝ) * P + P := by
      have : N ≤ N / P * P + P := by omega
      exact_mod_cast this
    rw [div_le_iff₀ (by linarith)]; linarith
  have hqQ : (q : ℝ) ≤ ((N / P : ℕ) : ℝ) := by exact_mod_cast hden
  -- the Dirichlet radius is at most `P/(qN)`
  have hrad : 1 / ((((N / P : ℕ) : ℝ) + 1) * q) ≤ (P : ℝ) / N / q := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (N : ℝ) ≤ P * (((N / P : ℕ) : ℝ) + 1) := by
      have := (div_le_iff₀ (by linarith : (0 : ℝ) < P)).mp hQ1; linarith
    nlinarith
  have hcopN : a.natAbs.Coprime q := r.reduced
  have hgcd : Int.gcd a (q : ℤ) = 1 := by
    rw [Int.gcd, Int.natAbs_natCast]; exact hcopN
  refine ⟨a, q, hq0, hgcd, ?_, hqQ.trans hQR, ?_⟩
  · by_contra hqP
    push Not at hqP
    have hqPR : (q : ℝ) ≤ P := by exact_mod_cast hqP
    have hrad' : |α - (a : ℝ) / q| ≤ (P : ℝ) / N / q := hr.trans hrad
    have hPNq : (P : ℝ) / N / q ≤ (P : ℝ) / N :=
      div_le_self (by positivity) (by exact_mod_cast hq0)
    obtain ⟨hαl, hαr⟩ := abs_le.mp hrad'
    -- `a ≥ 1`
    have ha0 : 0 < a := by
      have : (0 : ℝ) < (a : ℝ) / q := by linarith [hα.1]
      have : (0 : ℝ) < (a : ℝ) := by
        have := mul_pos this hqR; rwa [div_mul_cancel₀ _ hqR.ne'] at this
      exact_mod_cast this
    -- `a ≤ q`
    have haq : a ≤ (q : ℤ) := by
      by_contra hgt
      push Not at hgt
      have hge : ((q : ℤ) + 1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hgt
      have h1 : 1 + 1 / (q : ℝ) ≤ (a : ℝ) / q := by
        rw [le_div_iff₀ hqR, add_mul, one_div_mul_cancel hqR.ne']; push_cast at hge; linarith
      have h2 : 1 / (P : ℝ) ≤ 1 / (q : ℝ) := one_div_le_one_div_of_le hqR hqPR
      have h3 : 2 * ((P : ℝ) / N) < 1 / (P : ℝ) := by
        rw [lt_div_iff₀ (by linarith)]
        calc 2 * ((P : ℝ) / N) * P = 2 * (P : ℝ) ^ 2 / N := by ring
          _ < 1 := by rw [div_lt_one hNpos]; exact hNR
      linarith [hα.2]
    apply hoff (q, a.toNat)
    · simp only [arcIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      have hcop' : a.toNat.Coprime q := by
        have e : a.natAbs = a.toNat := by omega
        rw [← e]; exact hcopN
      refine ⟨⟨⟨by omega, hqP⟩, by omega, by omega⟩, by omega, hcop'⟩
    · simp only [majorArc, Set.mem_Icc]
      have : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha0.le
      rw [this]
      constructor <;> linarith
  · refine hr.trans ?_
    rw [sq]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

/-- **Off the major arcs, `S` is small:** there is a `K` such that, for `N > 2P²` and every `α` in
the window that lies on no major arc, `|S(α)| ≤ K (2N/√P + N^{7/8}) (log N)³`. -/
theorem norm_primeExpSum_le_off_arcs :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N P : ℕ) (α : ℝ), 2 ≤ N → 1 ≤ P → 2 * P ^ 2 < N →
      α ∈ Set.Ioc ((P : ℝ) / N) (1 + (P : ℝ) / N) →
      (∀ x ∈ arcIndex P, α ∉ majorArc N P x.1 x.2) →
        ‖primeExpSum N α‖
          ≤ K * (2 * (N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((7 : ℝ) / 8)) * Real.log N ^ 3 := by
  obtain ⟨K, hK, hmin⟩ := norm_primeExpSum_le_minor
  refine ⟨K, hK, ?_⟩
  intro N P α hN hP hNP hα hoff
  obtain ⟨a, q, hq1, hgcd, hPq, hqN, happ⟩ := exists_minor_approx hP hNP hα hoff
  refine (hmin N q a α hN hq1 hgcd happ).trans ?_
  have hPR : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hPq' : (P : ℝ) ≤ q := by exact_mod_cast hPq.le
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hPR
  have h1 : (N : ℝ) / Real.sqrt q ≤ (N : ℝ) / Real.sqrt P :=
    div_le_div_of_nonneg_left hNR hsP (Real.sqrt_le_sqrt hPq')
  have h2 : Real.sqrt ((N : ℝ) * q) ≤ (N : ℝ) / Real.sqrt P := by
    rw [le_div_iff₀ hsP, ← Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_le_left (by positivity)]
    · rw [le_div_iff₀ hPR] at hqN
      nlinarith
  have hlog : 0 ≤ Real.log N ^ 3 :=
    pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) 3
  apply mul_le_mul_of_nonneg_right _ hlog
  apply mul_le_mul_of_nonneg_left _ hK
  have : 2 * (N : ℝ) / Real.sqrt P = (N : ℝ) / Real.sqrt P + (N : ℝ) / Real.sqrt P := by ring
  rw [this]; linarith

end Salt.ThreePrimes
