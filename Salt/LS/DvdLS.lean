/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.CharLS

/-!
# Large sieve track, node PE3c-1: the δ-restricted analytic root

Design: `docs/blueprints/flags.md`, entry `2026-07-13 PE3c RECON`.

The `Q²` diagonal of the arithmetic/character large sieve is born at a single
place: the Farey spacing `farey_spacing_core`. Restricting the modulus sum to
the multiples of a fixed `δ`, the separation between two Farey fractions
`a/q ≠ a'/q'` with `δ ∣ q`, `δ ∣ q'` improves from `1/(q q')` to `δ/(q q')`,
because the separation numerator `k = a q' − a' q − n q q'` is divisible by `δ`
(each term is), so `k ≠ 0 ⇒ δ ≤ |k|` (`Int.le_of_dvd`) rather than merely
`1 ≤ |k|`. Everything downstream is a `δ`-copy that feeds the improved
separation `δ/Q²` into the *same* generic engines (`sum_expSum_sq_le_of_spaced`,
`analytic_LS`, `char_LS_perQ`), whose point-set separation is already a
parameter — so the diagonal reads off as `Q²/δ`.

* `farey_spacing_core_dvd` / `farey_spacing_dvd` — the spacing refinement.
* `arithmetic_LS_dvd` — arithmetic large sieve, modulus sum over
  `(Icc 1 Q).filter (δ ∣ ·)`, diagonal `Q²/δ + 13N`.
* `char_LS_dvd` — the character form with the same modulus filter.

The `δ = 1` specializations recover the landed (un-restricted) lemmas; see the
`example` blocks at the end of the file.

**Wiring.** This module lives under `Salt/LS`; it should be added to whatever
aggregate imports the `Salt.LS.*` character-sieve modules (the same aggregate
that pulls in `Salt.LS.CharLS`). It is *not* wired here — the designer wires it.
-/

namespace Salt.LS

open scoped BigOperators

/-- **PE3c-1 core.** δ-restricted Farey spacing: two distinct fractions
`a/q ≠ a'/q'` with `a < q`, `a' < q'` and a common divisor `δ ∣ q`, `δ ∣ q'`
are `dist₁`-separated by at least `δ/(q q')` (vs. `1/(q q')` without the divisor).
Proof = `farey_spacing_core` with `1 ≤ |k|` upgraded to `δ ≤ |k|` via
`δ ∣ k` (the separation numerator). -/
theorem farey_spacing_core_dvd {q q' a a' δ : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (ha : a < q) (ha' : a' < q') (hδq : δ ∣ q) (hδq' : δ ∣ q')
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    (δ : ℝ) / ((q : ℝ) * q') ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hδqZ : (δ : ℤ) ∣ (q : ℤ) := Int.natCast_dvd_natCast.mpr hδq
  have hδq'Z : (δ : ℤ) ∣ (q' : ℤ) := Int.natCast_dvd_natCast.mpr hδq'
  set x : ℝ := (a : ℝ) / q with hxdef
  set y : ℝ := (a' : ℝ) / q' with hydef
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg a) hqR.le
  have hx1 : x < 1 := by rw [hxdef, div_lt_one hqR]; exact_mod_cast ha
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg a') hq'R.le
  have hy1 : y < 1 := by rw [hydef, div_lt_one hq'R]; exact_mod_cast ha'
  -- For every integer `n`, `|x - y - n| ≥ δ/(q q')`.
  have key : ∀ n : ℤ, (δ : ℝ) / ((q : ℝ) * q') ≤ |x - y - (n : ℝ)| := by
    intro n
    set k : ℤ := (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - n * (q : ℤ) * (q' : ℤ)
      with hkdef
    have hxy : x - y - (n : ℝ) = (k : ℝ) / ((q : ℝ) * q') := by
      rw [hxdef, hydef, hkdef]
      push_cast
      field_simp
    have hk0 : k ≠ 0 := by
      intro h0
      apply hne
      have hz : (k : ℝ) = 0 := by exact_mod_cast h0
      have hxyn : x - y - (n : ℝ) = 0 := by rw [hxy, hz, zero_div]
      have hnlt : (n : ℝ) < 1 := by linarith
      have hngt : (-1 : ℝ) < (n : ℝ) := by linarith
      have hn0 : n = 0 := by
        have h1 : n < 1 := by exact_mod_cast hnlt
        have h2 : -1 < n := by exact_mod_cast hngt
        omega
      have hn0R : (n : ℝ) = 0 := by exact_mod_cast hn0
      linarith
    -- The divisibility upgrade: `δ ∣ k` because each term of `k` is.
    have hδk : (δ : ℤ) ∣ k := by
      obtain ⟨s, hs⟩ := hδqZ
      obtain ⟨t, ht⟩ := hδq'Z
      refine ⟨(a : ℤ) * t - (a' : ℤ) * s - n * (δ : ℤ) * s * t, ?_⟩
      rw [hkdef, hs, ht]; ring
    have hkδ : (δ : ℤ) ≤ |k| := Int.le_of_dvd (abs_pos.mpr hk0) ((dvd_abs _ _).mpr hδk)
    have hk1 : (δ : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hkδ
    rw [hxy, abs_div, abs_of_pos (mul_pos hqR hq'R)]
    gcongr
  have := key (round (x - y))
  unfold dist₁
  exact this

/-- **PE3c-1.** δ-restricted Farey spacing, `Q`-uniform form: distinct fractions
`a/q ≠ a'/q'` with `q, q' ≤ Q` and `δ ∣ q`, `δ ∣ q'` are `dist₁`-separated by at
least `δ/Q²`. -/
theorem farey_spacing_dvd {q q' Q a a' δ : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hqQ : q ≤ Q) (hq'Q : q' ≤ Q) (ha : a < q) (ha' : a' < q')
    (hδq : δ ∣ q) (hδq' : δ ∣ q')
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    (δ : ℝ) / (Q : ℝ) ^ 2 ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hq'QR : (q' : ℝ) ≤ Q := by exact_mod_cast hq'Q
  have hcore := farey_spacing_core_dvd hq hq' ha ha' hδq hδq' hne
  have hQR : (0 : ℝ) ≤ (Q : ℝ) := hqR.le.trans hqQR
  have hQQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have hmul : (q : ℝ) * q' ≤ (Q : ℝ) * Q := mul_le_mul hqQR hq'QR hq'R.le hQR
    nlinarith [hmul]
  have hstep0 : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') :=
    one_div_le_one_div_of_le (mul_pos hqR hq'R) hQQ
  have hδnn : (0 : ℝ) ≤ (δ : ℝ) := Nat.cast_nonneg δ
  have hstep : (δ : ℝ) / (Q : ℝ) ^ 2 ≤ (δ : ℝ) / ((q : ℝ) * q') := by
    rw [div_eq_mul_one_div (δ : ℝ) ((Q : ℝ) ^ 2),
      div_eq_mul_one_div (δ : ℝ) ((q : ℝ) * q')]
    exact mul_le_mul_of_nonneg_left hstep0 hδnn
  exact hstep.trans hcore

/-- **PE3c-1.** The δ-restricted reduced Farey system of order `Q`: the pairs of
`fareyPairs Q` whose denominator is divisible by `δ`. -/
def fareyPairsDvd (Q δ : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((Finset.Icc 1 Q).filter (fun q => δ ∣ q)).sigma
    (fun q => (Finset.range q).filter (Nat.Coprime q))

/-- **PE3c-1 — δ-restricted arithmetic large sieve.** For `δ ≥ 1`, restricting
the modulus sum to multiples of `δ` improves the diagonal to `Q²/δ`:
```
∑ q ∈ Icc 1 Q, δ ∣ q, ∑ a coprime, ‖expSum N c (a/q)‖²
  ≤ (Q²/δ + 13N) · ∑ ‖cₙ‖².
```
Route: the spaced-points engine at separation `δ/Q²` (gate `δ/Q² ≤ 1/Q ≤ 1/2`
from `δ ≤ Q`, `Q ≥ 2`), read off `(δ/Q²)⁻¹ = Q²/δ`. The `Q = 1` degenerate case
(`δ = 1`, separation `1 > 1/2`) reuses `arithmetic_LS_one`; the `δ > Q` case has
an empty modulus filter. -/
theorem arithmetic_LS_dvd {N Q δ : ℕ} (hδ1 : 1 ≤ δ) (c : ℕ → ℂ) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q),
        ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
          ‖expSum N c ((a : ℝ) / q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 / δ + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  by_cases hδQ : δ ≤ Q
  · -- `δ ≤ Q`, hence `Q ≥ 1`.
    rcases le_or_gt Q 1 with hQ1 | hQ2
    · -- `Q ≤ 1`, so `Q = 1` and `δ = 1`: the degenerate Cauchy–Schwarz case.
      have hQeq : Q = 1 := le_antisymm hQ1 (le_trans hδ1 hδQ)
      have hδeq : δ = 1 := le_antisymm (le_trans hδQ (le_of_eq hQeq)) hδ1
      subst hQeq; subst hδeq
      have hfilter1 : (Finset.Icc 1 1).filter (fun q => (1 : ℕ) ∣ q) = Finset.Icc 1 1 :=
        Finset.filter_true_of_mem (fun q _ => one_dvd q)
      rw [hfilter1]
      have hcast : ((1 : ℕ) : ℝ) ^ 2 / ((1 : ℕ) : ℝ) + 13 * (N : ℝ) = 1 + 13 * (N : ℝ) := by
        norm_num
      rw [hcast]
      exact arithmetic_LS_one c
    · -- `Q ≥ 2`: the main engine at separation `δ/Q²`.
      have hQ2' : 2 ≤ Q := hQ2
      have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2'
      have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
      have hQsq : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
      have hδR1 : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ1
      have hδRpos : (0 : ℝ) < (δ : ℝ) := by linarith
      have hδRQ : (δ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hδQ
      set δsp : ℝ := (δ : ℝ) / (Q : ℝ) ^ 2 with hδspdef
      have hδsp_pos : 0 < δsp := by rw [hδspdef]; exact div_pos hδRpos hQsq
      have hδsp2 : δsp ≤ 1 / 2 := by
        rw [hδspdef, div_le_iff₀ hQsq]
        nlinarith [hδRQ, hQR, mul_nonneg (sub_nonneg.mpr hQR) hQpos.le]
      -- Pairwise spacing over the δ-restricted Farey system.
      have hSp : ∀ x ∈ fareyPairsDvd Q δ, ∀ y ∈ fareyPairsDvd Q δ, x ≠ y →
          δsp ≤ dist₁ (fareyFrac x) (fareyFrac y) := by
        rintro ⟨q, a⟩ hx ⟨q', a'⟩ hy hxy
        simp only [fareyPairsDvd, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_range] at hx hy
        obtain ⟨⟨⟨hq1, hqQ⟩, hδq⟩, ha_lt, hcop⟩ := hx
        obtain ⟨⟨⟨hq'1, hq'Q⟩, hδq'⟩, ha'_lt, hcop'⟩ := hy
        have hqpos : 0 < q := hq1
        have hq'pos : 0 < q' := hq'1
        have hfrac_ne : (a : ℝ) / q ≠ (a' : ℝ) / q' := by
          intro heq
          apply hxy
          have hqR2 : (0 : ℝ) < q := by exact_mod_cast hqpos
          have hq'R2 : (0 : ℝ) < q' := by exact_mod_cast hq'pos
          rw [div_eq_div_iff hqR2.ne' hq'R2.ne'] at heq
          have heqN : a * q' = a' * q := by exact_mod_cast heq
          have hdvd1 : q ∣ q' := hcop.dvd_of_dvd_mul_left ⟨a', by rw [heqN]; ring⟩
          have hdvd2 : q' ∣ q := hcop'.dvd_of_dvd_mul_left ⟨a, by rw [← heqN]; ring⟩
          have hq_eq : q = q' := Nat.dvd_antisymm hdvd1 hdvd2
          have ha_eq : a = a' := by
            have hh := heqN
            rw [hq_eq] at hh
            exact Nat.eq_of_mul_eq_mul_right hq'pos hh
          rw [hq_eq, ha_eq]
        simp only [fareyFrac_mk]
        rw [hδspdef]
        exact farey_spacing_dvd hqpos hq'pos hqQ hq'Q ha_lt ha'_lt hδq hδq' hfrac_ne
      have hkey := sum_expSum_sq_le_of_spaced (N := N) (fareyPairsDvd Q δ) fareyFrac c hSp
        hδsp_pos hδsp2
      have hcoef : δsp⁻¹ = (Q : ℝ) ^ 2 / (δ : ℝ) := by rw [hδspdef, inv_div]
      rw [hcoef] at hkey
      have hrewrite : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q),
          ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
            ‖expSum N c ((a : ℝ) / q)‖ ^ 2
          = ∑ x ∈ fareyPairsDvd Q δ, ‖expSum N c (fareyFrac x)‖ ^ 2 := by
        rw [fareyPairsDvd, Finset.sum_sigma']
        simp only [fareyFrac]
      rw [hrewrite]
      exact hkey
  · -- `δ > Q`: no `q ∈ Icc 1 Q` is divisible by `δ`, so the modulus filter is empty.
    have hδQ' : Q < δ := not_le.mp hδQ
    have hempty : (Finset.Icc 1 Q).filter (fun q => δ ∣ q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq
      rw [Finset.mem_Icc] at hq
      intro hdvd
      have hle : δ ≤ q := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [hempty, Finset.sum_empty]
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun n _ => sq_nonneg _)

open Classical in
/-- **PE3c-1 — δ-restricted character large sieve.** For `δ ≥ 1`,
```
∑ q ∈ Icc 1 Q, δ ∣ q, (q/φ q) · ∑ χ primitive mod q, ‖∑ n < N, c n · χ n‖²
  ≤ (Q²/δ + 13N) · ∑ n < N, ‖c n‖².
```
Proof: `char_LS_perQ` (reused verbatim) for each modulus in the filtered set,
then `arithmetic_LS_dvd`. The modulus filter is the only change from `char_LS`. -/
theorem char_LS_dvd {N Q δ : ℕ} (hδ1 : 1 ≤ δ) (c : ℕ → ℂ) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q),
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 / δ + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  classical
  calc ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q),
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => δ ∣ q),
          ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), ‖expSum N c ((a : ℝ) / q)‖ ^ 2 := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_filter, Finset.mem_Icc] at hq
        have hq1 : 1 ≤ q := hq.1.1
        haveI : NeZero q := ⟨Nat.one_le_iff_ne_zero.mp hq1⟩
        exact char_LS_perQ q c
    _ ≤ ((Q : ℝ) ^ 2 / δ + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
        arithmetic_LS_dvd hδ1 c

/-! ## Sanity: `δ = 1` recovers the landed (un-restricted) shapes. -/

/-- At `δ = 1`, `farey_spacing_core_dvd` recovers `farey_spacing_core`. -/
example {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (ha : a < q) (ha' : a' < q') (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / ((q : ℝ) * q') ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have h := farey_spacing_core_dvd hq hq' ha ha' (one_dvd q) (one_dvd q') hne
  simpa only [Nat.cast_one] using h

/-- At `δ = 1`, `farey_spacing_dvd` recovers `farey_spacing`. -/
example {q q' Q a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hqQ : q ≤ Q) (hq'Q : q' ≤ Q) (ha : a < q) (ha' : a' < q')
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / (Q : ℝ) ^ 2 ≤ dist₁ ((a : ℝ) / q) ((a' : ℝ) / q') := by
  have h := farey_spacing_dvd hq hq' hqQ hq'Q ha ha' (one_dvd q) (one_dvd q') hne
  simpa only [Nat.cast_one] using h

/-- At `δ = 1`, `arithmetic_LS_dvd` recovers `arithmetic_LS`'s shape (in fact for
every `Q`, dropping the `2 ≤ Q` hypothesis). -/
example {N Q : ℕ} (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖expSum N c ((a : ℝ) / q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  have h := arithmetic_LS_dvd (N := N) (Q := Q) (δ := 1) (le_refl 1) c
  have hf : (Finset.Icc 1 Q).filter (fun q => (1 : ℕ) ∣ q) = Finset.Icc 1 Q :=
    Finset.filter_true_of_mem (fun q _ => one_dvd q)
  rw [hf] at h
  simpa only [Nat.cast_one, div_one] using h

open Classical in
/-- At `δ = 1`, `char_LS_dvd` recovers `char_LS`'s shape (for every `Q`). -/
example {N Q : ℕ} (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range N, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  classical
  have h := char_LS_dvd (N := N) (Q := Q) (δ := 1) (le_refl 1) c
  have hf : (Finset.Icc 1 Q).filter (fun q => (1 : ℕ) ∣ q) = Finset.Icc 1 Q :=
    Finset.filter_true_of_mem (fun q _ => one_dvd q)
  rw [hf] at h
  simpa only [Nat.cast_one, div_one] using h

end Salt.LS
