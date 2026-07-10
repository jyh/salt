/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MvMoment
import Salt.Twelve.BudgetMomentG

/-!
# W3-3 (g-workhorse) — the multi-dimensional budget moment with `g`-weights (`mv_monomial_g`)

Card W3-3 of the `explicit12` wave-3 dispatch
(`docs/blueprints/explicit12-design.md`).  The g-weighted analogue of the W3-1
workhorse `mv_monomial`, with the SAME `φ`-main term; the g/φ singular-series
deviation lives entirely in an extra `(1 + log R / D)` error factor.

Route (the design's PREFERRED top-level comparison — `mv_monomial` is reused as a
black box, no re-induction):
`|g-sum − Main| ≤ |g-sum − φ-sum| + |φ-sum − Main|`.  The second term is
`mv_monomial`.  For the first term, `g-sum − φ-sum ≥ 0` is bounded by telescoping
the product `∏ 1/g − ∏ 1/φ` coordinate-by-coordinate (`product_gap_bound`),
relaxing the coupled `decBox` to the uncoupled product box, factoring via
`Finset.sum_prod_piFinset`, and bounding each coordinate: the marked coordinate is
a `budget_moment_g` GAP `≤ Cg·log R/D`, the others are crude g-moments
`≤ c·(1+X)` (via `marked_sqf_g` at `s = 1`).
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-! ## The product-telescope inequality -/

/-- Telescoping bound for a product difference: if `0 ≤ b i ≤ a i` on `s`, then
`∏ a − ∏ b ≤ ∑_j (a_j − b_j)·∏_{i≠j} a_i`.  (Standard telescope, proved by
`Finset.induction`.) -/
private lemma product_gap_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℝ) (h : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ a i) :
    (∏ i ∈ s, a i) - (∏ i ∈ s, b i)
      ≤ ∑ j ∈ s, (a j - b j) * ∏ i ∈ s.erase j, a i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    have hs : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ a i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hx' := h x (Finset.mem_insert_self x s)
    have hax : 0 ≤ a x := le_trans hx'.1 hx'.2
    have habx : 0 ≤ a x - b x := by linarith [hx'.2]
    have hprod_b_le_a : (∏ i ∈ s, b i) ≤ ∏ i ∈ s, a i :=
      Finset.prod_le_prod (fun i hi => (hs i hi).1) (fun i hi => (hs i hi).2)
    have ihs := ih hs
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx,
      Finset.erase_insert hx]
    have hsum_eq : ∑ j ∈ s, (a j - b j) * ∏ i ∈ (insert x s).erase j, a i
        = ∑ j ∈ s, (a j - b j) * (a x * ∏ i ∈ s.erase j, a i) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjx : j ≠ x := fun hjx => hx (hjx ▸ hj)
      rw [Finset.erase_insert_of_ne (Ne.symm hjx),
        Finset.prod_insert (fun hmem => hx (Finset.mem_of_mem_erase hmem))]
    rw [hsum_eq]
    have hfactor : ∑ j ∈ s, (a j - b j) * (a x * ∏ i ∈ s.erase j, a i)
        = a x * ∑ j ∈ s, (a j - b j) * ∏ i ∈ s.erase j, a i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hfactor]
    have k1 : a x * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)
        ≤ a x * ∑ j ∈ s, (a j - b j) * ∏ i ∈ s.erase j, a i :=
      mul_le_mul_of_nonneg_left ihs hax
    nlinarith [k1, mul_nonneg habx (sub_nonneg.mpr hprod_b_le_a)]

/-- Algebraic identity peeling the `w`-weight out of a product-of-inverse difference. -/
private lemma sub_div_eq {n : ℕ} (w : ℝ) (f h : Fin n → ℝ) :
    w / (∏ i, f i) - w / (∏ i, h i) = w * ((∏ i, (f i)⁻¹) - (∏ i, (h i)⁻¹)) := by
  rw [mul_sub, Finset.prod_inv_distrib, Finset.prod_inv_distrib,
    ← div_eq_mul_inv, ← div_eq_mul_inv]

/-! ## The two one-dimensional g-moment corollaries -/

/-- Crude g-moment: `∑ (log x/log R)^a / g(x) ≤ c·(1+X)`, `X = (φW'/W')·log R`.
Obtained from `marked_sqf_g` at `s = 1` (`g(1) = 1`, `1 ∣ x` trivial). -/
private lemma crude_g_moment (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (a : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D z R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      (∑ x ∈ (Finset.range z).filter (fun x => Squarefree x ∧ x.Coprime W'),
          (Real.log x / Real.log R) ^ a * (gMult x : ℝ)⁻¹)
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) := by
  obtain ⟨cm, hcm0, hcm⟩ := marked_sqf_g W' hW' hpos a
  refine ⟨cm * ((W' : ℝ) / (Nat.totient W' : ℝ)), by positivity, ?_⟩
  intro D z R hD3 hD hz hzR hR
  have hLpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le zero_lt_one hR
  have hLnn : (0 : ℝ) ≤ Real.log R := hLpos.le
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hZnn : (0 : ℝ) ≤ Real.log z := Real.log_nonneg hz1
  have hZL : Real.log z ≤ Real.log R := Real.log_le_log (by linarith) (by exact_mod_cast hzR)
  have hg1 := hcm D 1 z hD3 hD one_pos hz
  have hgMult1 : (gMult 1 : ℝ) = 1 := by
    rw [gMult, Nat.primeFactors_one, Finset.prod_empty]; norm_num
  rw [hgMult1] at hg1
  have hFeq : ((Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ (1 : ℕ) ∣ r))
      = (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W') := by
    apply Finset.filter_congr; intro r _
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, one_dvd r⟩
  rw [hFeq] at hg1
  simp only [div_one, one_mul] at hg1
  -- hg1 : ∑ (log x)^a / g x ≤ cm * (log z)^(a+1)
  have hsum_eq : (∑ x ∈ (Finset.range z).filter (fun x => Squarefree x ∧ x.Coprime W'),
          (Real.log x / Real.log R) ^ a * (gMult x : ℝ)⁻¹)
      = ((Real.log R) ^ a)⁻¹ * ∑ x ∈ (Finset.range z).filter (fun x => Squarefree x ∧ x.Coprime W'),
          (Real.log x) ^ a / (gMult x : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [hsum_eq]
  have hInvNn : (0 : ℝ) ≤ ((Real.log R) ^ a)⁻¹ := by positivity
  have hLa : (0 : ℝ) < (Real.log R) ^ a := by positivity
  have hbound2 : ((Real.log R) ^ a)⁻¹ * (cm * (Real.log z) ^ (a + 1)) ≤ cm * Real.log R := by
    rw [show ((Real.log R) ^ a)⁻¹ * (cm * (Real.log z) ^ (a + 1))
        = cm * ((Real.log z) ^ (a + 1) / (Real.log R) ^ a) by rw [div_eq_mul_inv]; ring]
    apply mul_le_mul_of_nonneg_left _ hcm0
    rw [div_le_iff₀ hLa]
    calc (Real.log z) ^ (a + 1) ≤ (Real.log R) ^ (a + 1) := pow_le_pow_left₀ hZnn hZL _
      _ = Real.log R * (Real.log R) ^ a := by rw [pow_succ]; ring
  have hlogR_le : Real.log R
      ≤ ((W' : ℝ) / (Nat.totient W' : ℝ)) * (1 + (W'.totient : ℝ) / W' * Real.log R) := by
    have hW0 : (W' : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hphi0 : (Nat.totient W' : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hpos).ne'
    have hκX : ((W' : ℝ) / (Nat.totient W' : ℝ)) * (1 + (W'.totient : ℝ) / W' * Real.log R)
        = (W' : ℝ) / (Nat.totient W' : ℝ) + Real.log R := by field_simp
    have hκnn : (0 : ℝ) ≤ (W' : ℝ) / (Nat.totient W' : ℝ) := by positivity
    rw [hκX]; linarith
  calc ((Real.log R) ^ a)⁻¹ * ∑ x ∈ (Finset.range z).filter (fun x => Squarefree x ∧ x.Coprime W'),
          (Real.log x) ^ a / (gMult x : ℝ)
      ≤ ((Real.log R) ^ a)⁻¹ * (cm * (Real.log z) ^ (a + 1)) := mul_le_mul_of_nonneg_left hg1 hInvNn
    _ ≤ cm * Real.log R := hbound2
    _ ≤ cm * (((W' : ℝ) / (Nat.totient W' : ℝ)) * (1 + (W'.totient : ℝ) / W' * Real.log R)) :=
        mul_le_mul_of_nonneg_left hlogR_le hcm0
    _ = cm * ((W' : ℝ) / (Nat.totient W' : ℝ)) * (1 + (W'.totient : ℝ) / W' * Real.log R) := by ring

/-- Gap g-moment: `∑ (log x/log R)^a·(1/g(x) − 1/φ(x)) ≤ c·(log R/D)`.  Directly
the `budget_moment_g` sandwich's slack at budget exponent `b = 0`. -/
private lemma gap_g_moment (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (a : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D z R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      (∑ x ∈ (Finset.range z).filter (fun x => Squarefree x ∧ x.Coprime W'),
          (Real.log x / Real.log R) ^ a * ((gMult x : ℝ)⁻¹ - (Nat.totient x : ℝ)⁻¹))
        ≤ c * (Real.log R / D) := by
  obtain ⟨Cg, hCg0, hCg⟩ := budget_moment_g W' hW' hpos hUpper a 0
  refine ⟨Cg, hCg0, ?_⟩
  intro D z R hD3 hD hz hzR hR
  obtain ⟨_, hup⟩ := hCg D z R hD3 hD hz hzR hR
  have key : (∑ x ∈ (Finset.range z).filter (fun x => Squarefree x ∧ x.Coprime W'),
          (Real.log x / Real.log R) ^ a * ((gMult x : ℝ)⁻¹ - (Nat.totient x : ℝ)⁻¹))
      = (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ a * ((Real.log z - Real.log r) / Real.log R) ^ 0
            / (gMult r : ℝ))
        - (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ a * ((Real.log z - Real.log r) / Real.log R) ^ 0
            / (Nat.totient r : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    simp only [pow_zero, mul_one]; ring
  rw [key]
  have hring : Cg / (D : ℝ) * Real.log R = Cg * (Real.log R / (D : ℝ)) := by ring
  linarith [hup, hring]

/-! ## The keystone -/

set_option maxHeartbeats 1600000 in
-- The final assembly bundles the two 1-D corollaries, the per-r telescope, and the
-- per-j product factoring in a single elaboration; the nested `calc`s over `decBox`
-- and the product box exceed the default heartbeat budget.
theorem mv_monomial_g (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (n : ℕ) (e : Fin n → ℕ) (d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D z R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ r ∈ decBox n z W',
            (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
              / ∏ i, (gMult (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ n
            * ((DInt' e d : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (n + d + ∑ i, e i)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n - 1)
          * (1 + Real.log R / D) := by
  classical
  obtain ⟨c1, hc1_0, hc1⟩ := mv_monomial W' hW' hpos hUpper n e d
  choose cg hcg0 hcg using (fun a => crude_g_moment W' hW' hpos a)
  choose cgap hcgap0 hcgap using (fun a => gap_g_moment W' hW' hpos hUpper a)
  refine ⟨c1 + ∑ j : Fin n, cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i), ?_, ?_⟩
  · have hSK0 : (0 : ℝ) ≤ ∑ j : Fin n, cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i) := by
      apply Finset.sum_nonneg; intro j _
      exact mul_nonneg (hcgap0 _) (Finset.prod_nonneg (fun i _ => hcg0 _))
    linarith
  · intro D z R hD3 hD hz hzR hR
    have hLpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le zero_lt_one hR
    have hLnn : (0 : ℝ) ≤ Real.log R := hLpos.le
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    have hLD0 : (0 : ℝ) ≤ Real.log R / D := div_nonneg hLnn hDpos.le
    -- primes on the box are ≥ 3
    have hp3 : ∀ x : ℕ, x.Coprime W' → ∀ p ∈ x.primeFactors, 3 ≤ p := by
      intro x hxcop p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpx := Nat.dvd_of_mem_primeFactors hp
      have hnpW : ¬ p ∣ W' := by
        intro hpW
        have h1 : p ∣ 1 := hxcop ▸ Nat.dvd_gcd hpx hpW
        exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
      have := hD p hpp hnpW; omega
    have hmain0 := hc1 z R hz hzR hR
    set X : ℝ := (W'.totient : ℝ) / W' * Real.log R with hXdef
    have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
    set Main : ℝ := X ^ n * ((DInt' e d : ℚ) : ℝ) * (Real.log z / Real.log R) ^ (n + d + ∑ i, e i)
      with hMaindef
    set Sg : ℝ := ∑ r ∈ decBox n z W',
        (∏ i, (Real.log (r i) / Real.log R) ^ e i)
          * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
          / ∏ i, (gMult (r i) : ℝ) with hSgdef
    set Sphi : ℝ := ∑ r ∈ decBox n z W',
        (∏ i, (Real.log (r i) / Real.log R) ^ e i)
          * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
          / ∏ i, (Nat.totient (r i) : ℝ) with hSphidef
    -- hmain0 : |Sphi - Main| ≤ c1 * (1 + X)^(n-1)
    -- box-membership facts
    have hbox_facts : ∀ r ∈ decBox n z W',
        (∀ i, 1 ≤ r i) ∧ (∀ i, Squarefree (r i)) ∧ (∀ i, (r i).Coprime W') ∧ ∏ i, r i < z := by
      intro r hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
      exact ⟨fun i => Nat.pos_of_ne_zero (hr.2.1 i).ne_zero, hr.2.1, hr.2.2.1, hr.2.2.2⟩
    -- per r: weight nonneg, budget ∈ [0,1]
    have hWTfacts : ∀ r ∈ decBox n z W',
        0 ≤ ∏ i, (Real.log (r i) / Real.log R) ^ e i
        ∧ 0 ≤ (Real.log z - ∑ i, Real.log (r i)) / Real.log R
        ∧ ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ≤ 1 := by
      intro r hr
      obtain ⟨hr1, _hsqf, _hcop, hprodlt⟩ := hbox_facts r hr
      have hlog0 : ∀ i, 0 ≤ Real.log (r i) := fun i => Real.log_nonneg (by exact_mod_cast hr1 i)
      have hprodE0 : 0 ≤ ∏ i, (Real.log (r i) / Real.log R) ^ e i :=
        Finset.prod_nonneg (fun i _ => pow_nonneg (div_nonneg (hlog0 i) hLnn) _)
      have hne : ∀ i ∈ (Finset.univ : Finset (Fin n)), ((r i : ℝ)) ≠ 0 :=
        fun i _ => by exact_mod_cast Nat.one_le_iff_ne_zero.mp (hr1 i)
      have hSeq : (∑ i, Real.log (r i)) = Real.log ((∏ i, r i : ℕ) : ℝ) := by
        rw [Nat.cast_prod, ← Real.log_prod hne]
      have hprodpos : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => hr1 i)
      have hSle : (∑ i, Real.log (r i)) ≤ Real.log z := by
        rw [hSeq]; exact Real.log_le_log (by exact_mod_cast hprodpos)
          (by exact_mod_cast (by omega : (∏ i, r i) ≤ z))
      have hSnn : 0 ≤ ∑ i, Real.log (r i) := Finset.sum_nonneg (fun i _ => hlog0 i)
      have hlogzR : Real.log z ≤ Real.log R :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) (by exact_mod_cast hzR)
      exact ⟨hprodE0, div_nonneg (by linarith) hLnn, (div_le_one hLpos).mpr (by linarith)⟩
    -- termwise g > 0 and g ≤ φ on the box
    have hgpos : ∀ r ∈ decBox n z W', ∀ i, (0 : ℝ) < (gMult (r i) : ℝ) := by
      intro r hr i
      obtain ⟨_, hsqf, hcop, _⟩ := hbox_facts r hr
      exact_mod_cast box_g_pos (hsqf i) (hcop i) hD3 hD
    have hgφ : ∀ r ∈ decBox n z W', ∀ i, (gMult (r i) : ℝ) ≤ (Nat.totient (r i) : ℝ) := by
      intro r hr i
      obtain ⟨_, hsqf, hcop, _⟩ := hbox_facts r hr
      exact gMult_le_totient (hsqf i) (hp3 (r i) (hcop i))
    have hinv_le : ∀ r ∈ decBox n z W', ∀ i,
        (Nat.totient (r i) : ℝ)⁻¹ ≤ (gMult (r i) : ℝ)⁻¹ := by
      intro r hr i
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (hgpos r hr i) (hgφ r hr i)
    -- The abbreviation for the uncoupled box.
    set F_z : Finset ℕ := (Finset.range z).filter (fun x => Squarefree x ∧ x.Coprime W')
      with hFzdef
    have hFz_facts : ∀ x ∈ F_z, 1 ≤ x ∧ Squarefree x ∧ x.Coprime W' := by
      intro x hx; rw [hFzdef, Finset.mem_filter, Finset.mem_range] at hx
      exact ⟨Nat.pos_of_ne_zero hx.2.1.ne_zero, hx.2.1, hx.2.2⟩
    have hgapx_nn : ∀ x ∈ F_z, 0 ≤ (gMult x : ℝ)⁻¹ - (Nat.totient x : ℝ)⁻¹ := by
      intro x hx
      obtain ⟨_hx1, hxsf, hxcop⟩ := hFz_facts x hx
      have hgp : (0 : ℝ) < (gMult x : ℝ) := by exact_mod_cast box_g_pos hxsf hxcop hD3 hD
      have hle : (gMult x : ℝ) ≤ (Nat.totient x : ℝ) := gMult_le_totient hxsf (hp3 x hxcop)
      have : (Nat.totient x : ℝ)⁻¹ ≤ (gMult x : ℝ)⁻¹ := by
        rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hgp hle
      linarith
    have hwx_nn : ∀ x ∈ F_z, ∀ a : ℕ, (0 : ℝ) ≤ (Real.log x / Real.log R) ^ a := by
      intro x hx a
      exact pow_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (hFz_facts x hx).1)) hLnn) a
    set PB : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ : Fin n => F_z) with hPBdef
    have hsubset : decBox n z W' ⊆ PB := by
      intro r hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
      rw [hPBdef]; simp only [Fintype.mem_piFinset, hFzdef, Finset.mem_filter, Finset.mem_range]
      intro i; exact ⟨hr.1 i, hr.2.1 i, hr.2.2.1 i⟩
    have hPB_facts : ∀ r ∈ PB, ∀ i, 1 ≤ r i ∧ Squarefree (r i) ∧ (r i).Coprime W' := by
      intro r hr i
      rw [hPBdef, Fintype.mem_piFinset] at hr
      exact hFz_facts (r i) (hr i)
    -- ================= the g↔φ comparison =================
    have hcompare : |Sg - Sphi|
        ≤ (∑ j : Fin n, cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i))
            * (1 + X) ^ (n - 1) * (Real.log R / D) := by
      rw [hSgdef, hSphidef, ← Finset.sum_sub_distrib]
      -- nonnegativity of the summed difference
      have hnn : 0 ≤ ∑ r ∈ decBox n z W',
          ((∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d / ∏ i, (gMult (r i) : ℝ)
            - (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                / ∏ i, (Nat.totient (r i) : ℝ)) := by
        apply Finset.sum_nonneg; intro r hr
        obtain ⟨hWT0, _, _⟩ := hWTfacts r hr
        have hbud0 : 0 ≤ ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d :=
          pow_nonneg (hWTfacts r hr).2.1 d
        have hWTnn : 0 ≤ (∏ i, (Real.log (r i) / Real.log R) ^ e i)
            * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d := mul_nonneg hWT0 hbud0
        rw [sub_div_eq]
        apply mul_nonneg hWTnn
        have hprodle : (∏ i, (Nat.totient (r i) : ℝ)⁻¹) ≤ ∏ i, (gMult (r i) : ℝ)⁻¹ :=
          Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
            (fun i _ => hinv_le r hr i)
        linarith
      rw [abs_of_nonneg hnn]
      -- per-r telescope
      have hstep_r : ∀ r ∈ decBox n z W',
          (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d / ∏ i, (gMult (r i) : ℝ)
            - (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d / ∏ i, (Nat.totient (r i) : ℝ)
          ≤ ∑ j : Fin n,
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := by
        intro r hr
        obtain ⟨hWT0, _, _⟩ := hWTfacts r hr
        have hbud0 : 0 ≤ ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d :=
          pow_nonneg (hWTfacts r hr).2.1 d
        have hWTnn : 0 ≤ (∏ i, (Real.log (r i) / Real.log R) ^ e i)
            * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d := mul_nonneg hWT0 hbud0
        rw [sub_div_eq]
        have hpgb := product_gap_bound Finset.univ (fun i => (gMult (r i) : ℝ)⁻¹)
          (fun i => (Nat.totient (r i) : ℝ)⁻¹)
          (fun i _ => ⟨inv_nonneg.mpr (Nat.cast_nonneg _), hinv_le r hr i⟩)
        calc (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                * ((∏ i, (gMult (r i) : ℝ)⁻¹) - ∏ i, (Nat.totient (r i) : ℝ)⁻¹)
            ≤ (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                * ∑ j : Fin n, ((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left hpgb hWTnn
          _ = ∑ j : Fin n,
                (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                  * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                      * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := by
              rw [Finset.mul_sum]
      -- per-j bound
      have hPjbound : ∀ j : Fin n,
          (∑ r ∈ decBox n z W',
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹))
            ≤ (cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i)) * (1 + X) ^ (n - 1)
                * (Real.log R / D) := by
        intro j
        set f_j : Fin n → ℕ → ℝ := fun i x =>
          if i = j then (Real.log x / Real.log R) ^ (e j)
              * ((gMult x : ℝ)⁻¹ - (Nat.totient x : ℝ)⁻¹)
            else (Real.log x / Real.log R) ^ (e i) * (gMult x : ℝ)⁻¹ with hf_jdef
        -- (a) budget drop, (b) subset, (c) regroup + factor
        have hregroup : ∀ r : Fin n → ℕ,
            (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                  * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹)
              = ∏ i, f_j i (r i) := by
          intro r
          have hjj : f_j j (r j) = (Real.log (r j) / Real.log R) ^ (e j)
              * ((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹) := by
            simp only [hf_jdef]; split_ifs with h
            · rfl
            · simp at h
          have herase : ∏ i ∈ Finset.univ.erase j, f_j i (r i)
              = ∏ i ∈ Finset.univ.erase j,
                  (Real.log (r i) / Real.log R) ^ (e i) * (gMult (r i) : ℝ)⁻¹ := by
            apply Finset.prod_congr rfl; intro i hi
            simp only [hf_jdef]; rw [if_neg (Finset.ne_of_mem_erase hi)]
          rw [← Finset.mul_prod_erase Finset.univ (fun i => f_j i (r i)) (Finset.mem_univ j),
            hjj, herase, Finset.prod_mul_distrib,
            ← Finset.mul_prod_erase Finset.univ
              (fun i => (Real.log (r i) / Real.log R) ^ (e i)) (Finset.mem_univ j)]
          ring
        have hfac : (∑ r ∈ PB,
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹))
            = ∏ i, ∑ x ∈ F_z, f_j i x := by
          rw [Finset.sum_congr rfl (fun r _ => hregroup r), hPBdef]
          exact Finset.sum_prod_piFinset F_z f_j
        -- coordinate sums
        have hSj_eq : (∑ x ∈ F_z, f_j j x)
            = ∑ x ∈ F_z, (Real.log x / Real.log R) ^ (e j)
                * ((gMult x : ℝ)⁻¹ - (Nat.totient x : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl; intro x _
          simp only [hf_jdef]; split_ifs with h
          · rfl
          · simp at h
        have hSi_eq : ∀ i ∈ Finset.univ.erase j, (∑ x ∈ F_z, f_j i x)
            = ∑ x ∈ F_z, (Real.log x / Real.log R) ^ (e i) * (gMult x : ℝ)⁻¹ := by
          intro i hi
          apply Finset.sum_congr rfl; intro x _
          simp only [hf_jdef]; rw [if_neg (Finset.ne_of_mem_erase hi)]
        have hSj_nn : 0 ≤ ∑ x ∈ F_z, f_j j x := by
          rw [hSj_eq]; apply Finset.sum_nonneg; intro x hx
          exact mul_nonneg (hwx_nn x hx (e j)) (hgapx_nn x hx)
        have hSi_nn : ∀ i ∈ Finset.univ.erase j, 0 ≤ ∑ x ∈ F_z, f_j i x := by
          intro i hi; rw [hSi_eq i hi]; apply Finset.sum_nonneg; intro x hx
          exact mul_nonneg (hwx_nn x hx (e i)) (inv_nonneg.mpr (Nat.cast_nonneg _))
        have hSj_bd : (∑ x ∈ F_z, f_j j x) ≤ cgap (e j) * (Real.log R / D) := by
          rw [hSj_eq, hFzdef]; exact hcgap (e j) D z R hD3 hD hz hzR hR
        have hSi_bd : ∀ i ∈ Finset.univ.erase j, (∑ x ∈ F_z, f_j i x) ≤ cg (e i) * (1 + X) := by
          intro i hi; rw [hSi_eq i hi, hFzdef]; exact hcg (e i) D z R hD3 hD hz hzR hR
        have hprodsimp : ∏ i ∈ Finset.univ.erase j, (cg (e i) * (1 + X))
            = (∏ i ∈ Finset.univ.erase j, cg (e i)) * (1 + X) ^ (n - 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
        -- (a) drop budget
        have ha : (∑ r ∈ decBox n z W',
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹))
            ≤ ∑ r ∈ decBox n z W',
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := by
          apply Finset.sum_le_sum; intro r hr
          obtain ⟨hprodE0, hbud0', hbud1'⟩ := hWTfacts r hr
          have hgapnn : 0 ≤ (gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹ := by
            have := hinv_le r hr j; linarith
          have hPjnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹ :=
            Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
          have hA0 : 0 ≤ (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                  * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) :=
            mul_nonneg hprodE0 (mul_nonneg hgapnn hPjnn)
          have hbudd1 : ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d ≤ 1 :=
            pow_le_one₀ hbud0' hbud1'
          calc (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                  * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                      * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹)
              = ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                  * ((∏ i, (Real.log (r i) / Real.log R) ^ e i)
                    * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                        * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹)) := by ring
            _ ≤ (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                      * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) :=
                mul_le_of_le_one_left hA0 hbudd1
        -- (b) enlarge to product box
        have hb : (∑ r ∈ decBox n z W',
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹))
            ≤ ∑ r ∈ PB,
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro r hrPB _
          have hf := hPB_facts r hrPB
          have hprodE0 : 0 ≤ ∏ i, (Real.log (r i) / Real.log R) ^ e i :=
            Finset.prod_nonneg (fun i _ =>
              pow_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (hf i).1)) hLnn) _)
          have hgapnn : 0 ≤ (gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹ := by
            have hgp : (0 : ℝ) < (gMult (r j) : ℝ) := by
              exact_mod_cast box_g_pos (hf j).2.1 (hf j).2.2 hD3 hD
            have hle : (gMult (r j) : ℝ) ≤ (Nat.totient (r j) : ℝ) :=
              gMult_le_totient (hf j).2.1 (hp3 (r j) (hf j).2.2)
            have : (Nat.totient (r j) : ℝ)⁻¹ ≤ (gMult (r j) : ℝ)⁻¹ := by
              rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hgp hle
            linarith
          have hPjnn : 0 ≤ ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹ :=
            Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
          exact mul_nonneg hprodE0 (mul_nonneg hgapnn hPjnn)
        -- assemble
        calc (∑ r ∈ decBox n z W',
                (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                  * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                      * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹))
            ≤ ∑ r ∈ decBox n z W',
                (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                      * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := ha
          _ ≤ ∑ r ∈ PB,
                (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                      * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := hb
          _ = ∏ i, ∑ x ∈ F_z, f_j i x := hfac
          _ = (∑ x ∈ F_z, f_j j x) * ∏ i ∈ Finset.univ.erase j, ∑ x ∈ F_z, f_j i x :=
              (Finset.mul_prod_erase Finset.univ (fun i => ∑ x ∈ F_z, f_j i x)
                (Finset.mem_univ j)).symm
          _ ≤ (cgap (e j) * (Real.log R / D)) * ∏ i ∈ Finset.univ.erase j, (cg (e i) * (1 + X)) :=
              mul_le_mul hSj_bd (Finset.prod_le_prod hSi_nn hSi_bd)
                (Finset.prod_nonneg hSi_nn) (mul_nonneg (hcgap0 _) hLD0)
          _ = (cgap (e j) * (Real.log R / D))
                * ((∏ i ∈ Finset.univ.erase j, cg (e i)) * (1 + X) ^ (n - 1)) := by rw [hprodsimp]
          _ = (cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i)) * (1 + X) ^ (n - 1)
                * (Real.log R / D) := by ring
      -- combine the per-r and per-j bounds
      calc ∑ r ∈ decBox n z W',
              ((∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d / ∏ i, (gMult (r i) : ℝ)
                - (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                  * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                    / ∏ i, (Nat.totient (r i) : ℝ))
          ≤ ∑ r ∈ decBox n z W', ∑ j : Fin n,
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := Finset.sum_le_sum hstep_r
        _ = ∑ j : Fin n, ∑ r ∈ decBox n z W',
              (∏ i, (Real.log (r i) / Real.log R) ^ e i)
                * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
                * (((gMult (r j) : ℝ)⁻¹ - (Nat.totient (r j) : ℝ)⁻¹)
                    * ∏ i ∈ Finset.univ.erase j, (gMult (r i) : ℝ)⁻¹) := Finset.sum_comm
        _ ≤ ∑ j : Fin n, (cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i))
              * (1 + X) ^ (n - 1) * (Real.log R / D) := Finset.sum_le_sum (fun j _ => hPjbound j)
        _ = (∑ j : Fin n, cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i))
              * (1 + X) ^ (n - 1) * (Real.log R / D) := by rw [← Finset.sum_mul, ← Finset.sum_mul]
    -- ================= final assembly =================
    have hP : (0 : ℝ) ≤ (1 + X) ^ (n - 1) := by positivity
    have hSK0 : (0 : ℝ) ≤ ∑ j : Fin n, cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hcgap0 _) (Finset.prod_nonneg (fun i _ => hcg0 _)))
    calc |Sg - Main| ≤ |Sg - Sphi| + |Sphi - Main| := abs_sub_le _ _ _
      _ ≤ (∑ j : Fin n, cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i))
            * (1 + X) ^ (n - 1) * (Real.log R / D) + c1 * (1 + X) ^ (n - 1) :=
          add_le_add hcompare hmain0
      _ ≤ (c1 + ∑ j : Fin n, cgap (e j) * ∏ i ∈ Finset.univ.erase j, cg (e i))
            * (1 + X) ^ (n - 1) * (1 + Real.log R / D) := by
          nlinarith [mul_nonneg (mul_nonneg hc1_0 hP) hLD0, mul_nonneg hSK0 hP,
            mul_nonneg (mul_nonneg hSK0 hP) hLD0]

end Salt.Twelve
