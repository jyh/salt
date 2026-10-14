/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.MvSplit
import Salt.MaynardK.ICRel
import Salt.MaynardK.JMainSplit

/-!
# C1 · B4.2b — `mv_J_split` at general `n` (`mv_J_split_gen`)

`mv_J_split_gen_of` derives the J-side split engine from the two `Prop`s `MvJMainSplitGen` and
`InnerContractRelGen` (ported, as a falsifier, by an Opus executor from a frozen brief, 2026-10-11);
`mv_J_split_gen` discharges both with `mv_J_main_split_gen` (`JMainSplit`) and
`inner_contract_rel_gen` (`ICRel`). `mv_J_split_of_gen` (in `Controls`) re-derives the landed k = 5
statement (its private `mv_J_main_split` entering as a hypothesis).
-/

open Finset

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Twelve Salt.Maynard Salt.MaynardK

/-- `phiAtomSum` is a sum of nonnegative terms. -/
private lemma pas_nonneg (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg fun r _ => by positivity

/-- `phiAtomSum` is monotone in the cap (more terms, all nonnegative). -/
private lemma pas_mono {z z' W' : ℕ} (h : z ≤ z') :
    Salt.Maynard.phiAtomSum z W' ≤ Salt.Maynard.phiAtomSum z' W' := by
  unfold Salt.Maynard.phiAtomSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    simp only [Salt.Maynard.sqfCop, Finset.mem_filter, Finset.mem_range] at hr ⊢
    exact ⟨lt_of_lt_of_le hr.1 h, hr.2⟩
  · intro r _ _; positivity

private lemma int_tail (D R : ℕ) (hD : 3 ≤ D) :
    ∑ k ∈ (Finset.range R).filter (fun k => D < k), 1 / ((k:ℝ) - 1)^2
      ≤ 1 / ((D:ℝ) - 1) := by
  have hset : (Finset.range R).filter (fun k => D < k) = Finset.Ico (D+1) R := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  set N := R - (D+1) with hN
  set φ : ℕ → ℝ := fun t => 1 / ((D:ℝ) - 1 + t) with hφ
  have hterm : ∀ t ∈ Finset.range N,
      1 / (((D+1+t:ℕ):ℝ) - 1)^2 ≤ φ t - φ (t+1) := by
    intro t _
    set a : ℝ := (D:ℝ) - 1 + t with ha_def
    have ha : (0:ℝ) < a := by
      have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
      have ht : (0:ℝ) ≤ (t:ℝ) := by positivity
      simp only [ha_def]; linarith
    have ha1 : (0:ℝ) < a + 1 := by linarith
    have hcast : (((D+1+t:ℕ):ℝ) - 1) = a + 1 := by simp only [ha_def]; push_cast; ring
    have hφt : φ t = 1 / a := by simp only [hφ, ha_def]
    have hφt1 : φ (t+1) = 1 / (a+1) := by
      simp only [hφ, ha_def]
      rw [show (D:ℝ) - 1 + (t+1:ℕ) = (D:ℝ) - 1 + t + 1 by push_cast; ring]
    rw [hcast, hφt, hφt1]
    have hstep1 : 1 / (a*(a+1)) = 1/a - 1/(a+1) := by field_simp; ring
    have hle : a * (a+1) ≤ (a+1)^2 := by linarith only [ha]
    have hstep2 : 1 / (a+1)^2 ≤ 1 / (a*(a+1)) :=
      one_div_le_one_div_of_le (mul_pos ha ha1) hle
    rw [← hstep1]; exact hstep2
  calc ∑ t ∈ Finset.range N, 1 / (((D+1+t:ℕ):ℝ) - 1)^2
      ≤ ∑ t ∈ Finset.range N, (φ t - φ (t+1)) := Finset.sum_le_sum hterm
    _ = φ 0 - φ N := Finset.sum_range_sub' φ N
    _ ≤ φ 0 := by
        have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
        have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
        have hpos : (0:ℝ) < (D:ℝ) - 1 + (N:ℝ) := by linarith
        have : 0 ≤ φ N := by simp only [hφ]; exact div_nonneg zero_le_one hpos.le
        linarith
    _ = 1 / ((D:ℝ) - 1) := by simp [hφ]

private lemma prime_tail (D R : ℕ) (hD : 3 ≤ D) :
    ∑ p ∈ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p), 1 / ((p:ℝ) - 1)^2
      ≤ 2 / (D:ℝ) := by
  have hsub : (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p)
      ⊆ (Finset.range R).filter (fun k => D < k) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have h1 : ∑ p ∈ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p), 1 / ((p:ℝ) - 1)^2
      ≤ ∑ k ∈ (Finset.range R).filter (fun k => D < k), 1 / ((k:ℝ) - 1)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _; positivity
  have h2 : (1:ℝ) / ((D:ℝ) - 1) ≤ 2 / (D:ℝ) := by
    have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith only [h3]
  linarith [int_tail D R hD, h1, h2]

private lemma ic_list_abs_sum_le {γ : Type*} (L : List γ) (f : γ → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
        _ ≤ |f a| + (L.map (fun a => |f a|)).sum := by linarith [ih]

private lemma ic_list_sum_le {γ : Type*} (L : List γ) (f g : γ → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

private lemma mjs_gMult_prime_cast {p : ℕ} (hp : Nat.Prime p) : (gMult p : ℝ) = (p : ℝ) - 2 := by
  have : gMult p = p - 2 := by rw [gMult, Nat.Prime.primeFactors hp, Finset.prod_singleton]
  rw [this, Nat.cast_sub hp.two_le]; norm_num

private lemma mjs_gMult_one_cast : (gMult 1 : ℝ) = 1 := by
  rw [gMult, Nat.primeFactors_one, Finset.prod_empty]; norm_num

private lemma mjs_gMult_pq_cast {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (gMult (p * q) : ℝ) = ((p:ℝ) - 2) * ((q:ℝ) - 2) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hmul : gMult (p * q) = gMult p * gMult q := by
    rw [gMult, gMult, gMult, Nat.Coprime.primeFactors_mul hcop,
      Finset.prod_union hcop.disjoint_primeFactors]
  rw [hmul, Nat.cast_mul, mjs_gMult_prime_cast hp, mjs_gMult_prime_cast hq]

private lemma mjs_box_PF_subset {W' D R : ℕ} (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    {x : ℕ} (hxR : x < R) (hxcop : x.Coprime W') :
    x.primeFactors ⊆ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpx := Nat.dvd_of_mem_primeFactors hp
  have hx0 : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
  have hpltR : p < R := lt_of_le_of_lt (Nat.le_of_dvd hx0 hpx) hxR
  have hnpW : ¬ p ∣ W' := by
    intro hpW; have h1 : p ∣ 1 := hxcop ▸ Nat.dvd_gcd hpx hpW
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
  rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hpltR, hpp, hD p hpp hnpW⟩

private lemma mjs_PFsum_nn (m : ℕ) : 0 ≤ ∑ p ∈ m.primeFactors, (1 / ((p:ℝ) - 1)) := by
  apply Finset.sum_nonneg; intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
  have : (0:ℝ) < (p:ℝ) - 1 := by linarith
  positivity

private lemma mjs_sum_biUnion_le {ι : Type*} (s : Finset ι) (t : ι → Finset ℕ)
    (g : ℕ → ℝ) (hg : ∀ i ∈ s, ∀ p ∈ t i, 0 ≤ g p) :
    ∑ p ∈ s.biUnion t, g p ≤ ∑ i ∈ s, ∑ p ∈ t i, g p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hga : ∀ p ∈ t a, 0 ≤ g p := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ i ∈ s, ∀ p ∈ t i, 0 ≤ g p :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hunion : ∑ p ∈ t a ∪ s.biUnion t, g p ≤ ∑ p ∈ t a, g p + ∑ p ∈ s.biUnion t, g p := by
      rw [← Finset.sum_union_inter]
      have : 0 ≤ ∑ p ∈ t a ∩ s.biUnion t, g p :=
        Finset.sum_nonneg (fun p hp => hga p (Finset.mem_of_mem_inter_left hp))
      linarith
    linarith [ih hgs]

private lemma mjs_eval_bpoly_bound {n : ℕ} (P : BPoly n) (t : Fin n → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (hs : ∑ i, t i ≤ 1) :
    |eval P t| ≤ (P.map (fun mo => |(mo.2.2 : ℝ)|)).sum := by
  unfold eval
  refine le_trans (ic_list_abs_sum_le P _) (ic_list_sum_le _ _ _ (fun mo _ => ?_))
  have hprod0 : 0 ≤ ∏ i, t i ^ mo.1 i := Finset.prod_nonneg (fun i _ => pow_nonneg (ht0 i) _)
  have hprod1 : ∏ i, t i ^ mo.1 i ≤ 1 :=
    Finset.prod_le_one (fun i _ => pow_nonneg (ht0 i) _) (fun i _ => pow_le_one₀ (ht0 i) (ht1 i))
  have hb0 : 0 ≤ 1 - ∑ i, t i := by linarith
  have hb1 : 1 - ∑ i, t i ≤ 1 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => ht0 i); linarith
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hprod0, abs_of_nonneg hb0]
  calc |(mo.2.2:ℝ)| * (∏ i, t i ^ mo.1 i) * (1 - ∑ i, t i) ^ mo.2.1
      ≤ |(mo.2.2:ℝ)| * 1 * 1 := by
        apply mul_le_mul _ (pow_le_one₀ hb0 hb1) (pow_nonneg hb0 _) (by positivity)
        exact mul_le_mul_of_nonneg_left hprod1 (abs_nonneg _)
    _ = |(mo.2.2:ℝ)| := by ring

/-! ### Relative one-coordinate g-moments (`M0`, `MQ`, `MQ2`) over `sqfCop R W'` -/

private lemma mjs_M0_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)))
      ≤ 2 * Salt.Maynard.phiAtomSum R W' := by
  have hg1 := marked_sqf_g_rel W' hW' hpos 0 D 1 R hD hDW one_pos hR2
  have hFeq : ((Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ (1:ℕ) ∣ r))
      = (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') := by
    apply Finset.filter_congr; intro r _
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, one_dvd r⟩
  rw [mjs_gMult_one_cast, hFeq] at hg1
  have hL : ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (Real.log x) ^ 0 / (gMult x : ℝ)
      = ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)) :=
    Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
  rw [hL] at hg1
  simpa using hg1

private lemma mjs_M0_op (W' : ℕ) (_hW' : Squarefree W') (_hpos : 0 < W') (cg : ℝ)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)))
      ≤ cg * Real.log R := by
  have hg1 := hcg D 1 R hD hDW one_pos hR2
  have hFeq : ((Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ (1:ℕ) ∣ r))
      = (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') := by
    apply Finset.filter_congr; intro r _
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, one_dvd r⟩
  rw [mjs_gMult_one_cast, hFeq] at hg1
  have hL : ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (Real.log x) ^ 0 / (gMult x : ℝ)
      = ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)) :=
    Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
  rw [hL] at hg1
  have hRw : (1:ℝ) / 1 * cg * (Real.log R) ^ (0 + 1) = cg * Real.log R := by norm_num
  rw [hRw] at hg1
  exact hg1

private lemma mjs_MQ_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
      ≤ 8 * Salt.Maynard.phiAtomSum R W' / (D : ℝ) := by
  classical
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set Primes := (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimes
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hswap : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
      ≤ ∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
          ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)) := by
    have hstep : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
        ≤ ∑ x ∈ F_R, ∑ p ∈ Primes,
            (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [hF_R, Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hxR, hxsf, hxcop⟩ := hx
      rw [Finset.sum_div]
      have hcongr : ∑ p ∈ x.primeFactors, 1 / ((p:ℝ) - 1) / (gMult x : ℝ)
          = ∑ p ∈ x.primeFactors, 1 / ((p:ℝ) - 1) * (1 / (gMult x : ℝ)) :=
        Finset.sum_congr rfl (fun p _ => by ring)
      rw [hcongr, ← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter]
        exact ⟨mjs_box_PF_subset hDW hxR hxcop hp, Nat.dvd_of_mem_primeFactors hp⟩
      · intro p hp _
        rw [Finset.mem_filter, hPrimes, Finset.mem_filter, Finset.mem_range] at hp
        have hpD : D < p := hp.1.2.2
        have hp1 : (0:ℝ) < (p:ℝ) - 1 := by
          have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
          linarith
        positivity
    calc (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
        ≤ ∑ x ∈ F_R, ∑ p ∈ Primes,
            (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := hstep
      _ = ∑ p ∈ Primes, ∑ x ∈ F_R,
            (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := Finset.sum_comm
      _ = ∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
            ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)) := by
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.mul_sum, ← Finset.sum_filter]
  refine le_trans hswap ?_
  have hper : ∀ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
        ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ))
      ≤ 2 * PAS * (2 / ((p:ℝ) - 1) ^ 2) := by
    intro p hp
    rw [hPrimes, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpR, hpp, hpD⟩ := hp
    have hp3 : 3 ≤ p := by omega
    have hp3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    have hmk := marked_sqf_g_rel W' hW' hpos 0 D p R hD hDW hpp.pos hR2
    rw [mjs_gMult_prime_cast hpp] at hmk
    have hfilt : F_R.filter (fun x => p ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1,h2,h3⟩
      · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h2⟩,h3⟩
    rw [hfilt]
    have hsum_le : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
          (1 / (gMult x : ℝ)) ≤ (1 / ((p:ℝ) - 2)) * 2 * PAS := by
      have hcv : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
          (Real.log x) ^ 0 / (gMult x : ℝ)
          = ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
            (1 / (gMult x : ℝ)) := Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
      rw [hcv] at hmk
      rw [hPAS]; simpa using hmk
    have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
    have hp2 : (0:ℝ) < (p:ℝ) - 2 := by linarith
    have hfrac : (1 / ((p:ℝ) - 1)) * (1 / ((p:ℝ) - 2)) ≤ 2 / ((p:ℝ) - 1) ^ 2 := by
      rw [one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hp3R, (Nat.cast_nonneg _ : 0 ≤ ↑p)]
    calc (1 / ((p:ℝ) - 1)) * ∑ x ∈ (Finset.range R).filter
            (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r), (1 / (gMult x : ℝ))
        ≤ (1 / ((p:ℝ) - 1)) * ((1 / ((p:ℝ) - 2)) * 2 * PAS) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = 2 * PAS * ((1 / ((p:ℝ) - 1)) * (1 / ((p:ℝ) - 2))) := by ring
      _ ≤ 2 * PAS * (2 / ((p:ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
  calc (∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
          ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)))
      ≤ ∑ p ∈ Primes, 2 * PAS * (2 / ((p:ℝ) - 1) ^ 2) := Finset.sum_le_sum hper
    _ = 2 * PAS * (2 * ∑ p ∈ Primes, 1 / ((p:ℝ) - 1) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ 2 * PAS * (2 * (2 / (D:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left (prime_tail D R hD) (by norm_num)
    _ = 8 * PAS / (D : ℝ) := by ring

private lemma mjs_MQ2_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / (gMult x : ℝ))
      ≤ 40 * Salt.Maynard.phiAtomSum R W' / (D : ℝ) := by
  classical
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set Primes := (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimes
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hprime_facts : ∀ p ∈ Primes,
      Nat.Prime p ∧ D < p ∧ (0:ℝ) < (p:ℝ) - 1 ∧ (0:ℝ) < (p:ℝ) - 2 := by
    intro p hp
    rw [hPrimes, Finset.mem_filter, Finset.mem_range] at hp
    have hpge : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 4 ≤ p)
    exact ⟨hp.2.1, hp.2.2, by linarith, by linarith⟩
  set c1 : ℕ → ℝ := fun p => 1 / ((p:ℝ) - 1) with hc1def
  set S : ℕ → ℕ → ℝ := fun p q =>
    ∑ x ∈ F_R.filter (fun x => p ∣ x ∧ q ∣ x), (1 / (gMult x : ℝ)) with hSdef
  have hSnn : ∀ p q, 0 ≤ S p q := fun p q => Finset.sum_nonneg (fun x _ => by positivity)
  have hexp : ∀ x, (∑ p ∈ x.primeFactors, c1 p) ^ 2 / (gMult x : ℝ)
      = ∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors, c1 p * c1 q * (1 / (gMult x : ℝ)) := by
    intro x
    rw [pow_two, sum_mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro q _; ring
  have hbound_x : ∀ x ∈ F_R,
      (∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors, c1 p * c1 q * (1 / (gMult x : ℝ)))
      ≤ ∑ p ∈ Primes, ∑ q ∈ Primes,
          (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
    intro x hx
    rw [hF_R, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxR, hxsf, hxcop⟩ := hx
    have hsub : x.primeFactors ⊆ Primes := mjs_box_PF_subset hDW hxR hxcop
    have hnnW : ∀ p q, p ∈ Primes → q ∈ Primes → 0 ≤ c1 p * c1 q * (1 / (gMult x : ℝ)) := by
      intro p q hpP hqP
      obtain ⟨_, _, hp1, _⟩ := hprime_facts p hpP
      obtain ⟨_, _, hq1, _⟩ := hprime_facts q hqP
      rw [hc1def]; positivity
    calc (∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors, c1 p * c1 q * (1 / (gMult x : ℝ)))
        ≤ ∑ p ∈ x.primeFactors, ∑ q ∈ Primes,
            (if q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
          apply Finset.sum_le_sum; intro p hp
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq; rw [Finset.mem_filter]
            exact ⟨hsub hq, Nat.dvd_of_mem_primeFactors hq⟩
          · intro q hq _; exact hnnW p q (hsub hp) (Finset.mem_of_mem_filter q hq)
      _ ≤ ∑ p ∈ Primes,
            (if p ∣ x then ∑ q ∈ Primes,
              (if q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) else 0) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; rw [Finset.mem_filter]
            exact ⟨hsub hp, Nat.dvd_of_mem_primeFactors hp⟩
          · intro p hp _
            apply Finset.sum_nonneg; intro q hq; split_ifs with hqx
            · exact hnnW p q (Finset.mem_of_mem_filter p hp) hq
            · exact le_refl 0
      _ = ∑ p ∈ Primes, ∑ q ∈ Primes,
            (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
          apply Finset.sum_congr rfl; intro p _
          by_cases hpx : p ∣ x
          · rw [if_pos hpx]; apply Finset.sum_congr rfl; intro q _
            by_cases hqx : q ∣ x
            · rw [if_pos hqx, if_pos ⟨hpx, hqx⟩]
            · rw [if_neg hqx, if_neg (fun h => hqx h.2)]
          · rw [if_neg hpx]; symm; apply Finset.sum_eq_zero; intro q _
            rw [if_neg (fun h => hpx h.1)]
  have hMQ2_le : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, c1 p) ^ 2 / (gMult x : ℝ))
      ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, c1 p * c1 q * S p q := by
    calc ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, c1 p) ^ 2 / (gMult x : ℝ)
        = ∑ x ∈ F_R, ∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors,
            c1 p * c1 q * (1 / (gMult x : ℝ)) := by
          apply Finset.sum_congr rfl; intro x _; exact hexp x
      _ ≤ ∑ x ∈ F_R, ∑ p ∈ Primes, ∑ q ∈ Primes,
            (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) :=
          Finset.sum_le_sum hbound_x
      _ = ∑ p ∈ Primes, ∑ q ∈ Primes, ∑ x ∈ F_R,
            (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
      _ = ∑ p ∈ Primes, ∑ q ∈ Primes, c1 p * c1 q * S p q := by
          apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _
          rw [← Finset.sum_filter, hSdef, Finset.mul_sum]
  refine le_trans hMQ2_le ?_
  have htail_a : ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) ≤ 4 / (D:ℝ) := by
    have hpt : ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)))
        ≤ ∑ p ∈ Primes, (2 / ((p:ℝ) - 1) ^ 2) := by
      apply Finset.sum_le_sum; intro p hp
      obtain ⟨_, hpD, hp1, hp2⟩ := hprime_facts p hp
      have hp4 : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 4 ≤ p)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hp1, hp2, hp4]
    calc ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)))
        ≤ ∑ p ∈ Primes, (2 / ((p:ℝ) - 1) ^ 2) := hpt
      _ = 2 * ∑ p ∈ Primes, (1 / ((p:ℝ) - 1) ^ 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ 2 * (2 / (D:ℝ)) := by apply mul_le_mul_of_nonneg_left (prime_tail D R hD) (by norm_num)
      _ = 4 / (D:ℝ) := by ring
  have hmarked : ∀ s : ℕ, 0 < s →
      (∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (1 / (gMult x : ℝ)))
        ≤ (1 / (gMult s : ℝ)) * 2 * PAS := by
    intro s hs
    have hmk := marked_sqf_g_rel W' hW' hpos 0 D s R hD hDW hs hR2
    have hcv : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log x)^0/(gMult x:ℝ)
        = ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (1/(gMult x:ℝ)) := Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
    rw [hcv] at hmk; rw [hPAS]; simpa using hmk
  have hS_diag : ∀ p ∈ Primes, S p p ≤ (1 / ((p:ℝ) - 2)) * 2 * PAS := by
    intro p hp
    obtain ⟨hpp, _, _, _⟩ := hprime_facts p hp
    have hfe : F_R.filter (fun x => p ∣ x ∧ p ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,_⟩; exact ⟨h1,h2,h3⟩
      · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h2⟩,h3,h3⟩
    simp only [hSdef]; rw [hfe]
    have := hmarked p hpp.pos; rw [mjs_gMult_prime_cast hpp] at this; exact this
  have hS_off : ∀ p ∈ Primes, ∀ q ∈ Primes, p ≠ q →
      S p q ≤ (1 / (((p:ℝ) - 2) * ((q:ℝ) - 2))) * 2 * PAS := by
    intro p hp q hq hpq
    obtain ⟨hpp, _, _, _⟩ := hprime_facts p hp
    obtain ⟨hqp, _, _, _⟩ := hprime_facts q hq
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
    have hfe : F_R.filter (fun x => p ∣ x ∧ q ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p * q ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,h4⟩; exact ⟨h1,h2, hcop.mul_dvd_of_dvd_of_dvd h3 h4⟩
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨h1,h2⟩, (dvd_mul_right p q).trans h3, (dvd_mul_left q p).trans h3⟩
    simp only [hSdef]; rw [hfe]
    have := hmarked (p*q) (Nat.mul_pos hpp.pos hqp.pos)
    rw [mjs_gMult_pq_cast hpp hqp hpq] at this; exact this
  have hsplit : ∑ p ∈ Primes, ∑ q ∈ Primes, c1 p * c1 q * S p q
      = ∑ p ∈ Primes, c1 p * c1 p * S p p
        + ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p hp
    exact (Finset.add_sum_erase Primes (fun q => c1 p * c1 q * S p q) hp).symm
  rw [hsplit]
  have h2PAS0 : 0 ≤ 2 * PAS := by positivity
  have hdiag : ∑ p ∈ Primes, c1 p * c1 p * S p p ≤ 2 * PAS * (4 / (D:ℝ)) := by
    have hstep : ∑ p ∈ Primes, c1 p * c1 p * S p p
        ≤ ∑ p ∈ Primes, (2 * PAS) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by
      apply Finset.sum_le_sum; intro p hp
      obtain ⟨_, _, hp1, hp2⟩ := hprime_facts p hp
      have hc1nn : 0 ≤ c1 p := by rw [hc1def]; positivity
      have hc1le1 : c1 p ≤ 1 := by rw [hc1def, div_le_one hp1]; linarith
      have hcSnn : 0 ≤ c1 p * S p p := mul_nonneg hc1nn (hSnn p p)
      have hap : c1 p * (1 / ((p:ℝ) - 2)) = 1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)) := by
        rw [hc1def, div_mul_div_comm, one_mul]
      calc c1 p * c1 p * S p p
          = c1 p * (c1 p * S p p) := by ring
        _ ≤ 1 * (c1 p * S p p) := mul_le_mul_of_nonneg_right hc1le1 hcSnn
        _ = c1 p * S p p := one_mul _
        _ ≤ c1 p * ((1 / ((p:ℝ) - 2)) * 2 * PAS) :=
            mul_le_mul_of_nonneg_left (hS_diag p hp) hc1nn
        _ = (2 * PAS) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by rw [← hap]; ring
    calc ∑ p ∈ Primes, c1 p * c1 p * S p p
        ≤ ∑ p ∈ Primes, (2 * PAS) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := hstep
      _ = (2 * PAS) * ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by rw [Finset.mul_sum]
      _ ≤ (2 * PAS) * (4 / (D:ℝ)) := mul_le_mul_of_nonneg_left htail_a h2PAS0
  have hoff : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
      ≤ 2 * PAS * ((4 / (D:ℝ)) * (4 / (D:ℝ))) := by
    set a : ℕ → ℝ := fun p => 1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)) with hadef
    have hann : ∀ p ∈ Primes, 0 ≤ a p := by
      intro p hp; obtain ⟨_,_,hp1,hp2⟩ := hprime_facts p hp; rw [hadef]; positivity
    have hstep1 : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (2 * PAS) * (a p * a q) := by
      apply Finset.sum_le_sum; intro p hp
      apply Finset.sum_le_sum; intro q hq
      have hqP : q ∈ Primes := Finset.mem_of_mem_erase hq
      have hne : p ≠ q := (Finset.ne_of_mem_erase hq).symm
      obtain ⟨_,_,hp1,hp2⟩ := hprime_facts p hp
      obtain ⟨_,_,hq1,hq2⟩ := hprime_facts q hqP
      have hc1nn : 0 ≤ c1 p * c1 q := by rw [hc1def]; positivity
      have h1 : (p:ℝ)-1 ≠ 0 := ne_of_gt hp1
      have h2 : (p:ℝ)-2 ≠ 0 := ne_of_gt hp2
      have h3 : (q:ℝ)-1 ≠ 0 := ne_of_gt hq1
      have h4 : (q:ℝ)-2 ≠ 0 := ne_of_gt hq2
      calc c1 p * c1 q * S p q
          ≤ c1 p * c1 q * ((1 / (((p:ℝ) - 2) * ((q:ℝ) - 2))) * 2 * PAS) :=
            mul_le_mul_of_nonneg_left (hS_off p hp q hqP hne) hc1nn
        _ = (2 * PAS) * (a p * a q) := by rw [hc1def, hadef]; field_simp
    have hstep2 : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (2 * PAS) * (a p * a q)
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, (2 * PAS) * (a p * a q) := by
      apply Finset.sum_le_sum; intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p Primes)
      intro q hq _
      exact mul_nonneg h2PAS0 (mul_nonneg (hann p hp) (hann q hq))
    calc ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (2 * PAS) * (a p * a q) := hstep1
      _ ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, (2 * PAS) * (a p * a q) := hstep2
      _ = (2 * PAS) * ((∑ p ∈ Primes, a p) * (∑ q ∈ Primes, a q)) := by
          rw [sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.mul_sum]
      _ ≤ (2 * PAS) * ((4 / (D:ℝ)) * (4 / (D:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ h2PAS0
          apply mul_le_mul htail_a htail_a (Finset.sum_nonneg (fun q hq => hann q hq))
            (by positivity)
  have hfinal : 2 * PAS * (4 / (D:ℝ)) + 2 * PAS * ((4 / (D:ℝ)) * (4 / (D:ℝ)))
      ≤ 40 * PAS / (D:ℝ) := by
    have hD1 : (1:ℝ) ≤ (D:ℝ) := by linarith
    have hDsq : (4 / (D:ℝ)) * (4 / (D:ℝ)) ≤ 16 / (D:ℝ) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hDpos]; nlinarith
    have h2 : 2 * PAS * ((4 / (D:ℝ)) * (4 / (D:ℝ))) ≤ 2 * PAS * (16 / (D:ℝ)) :=
      mul_le_mul_of_nonneg_left hDsq h2PAS0
    have h3 : 2 * PAS * (4 / (D:ℝ)) + 2 * PAS * (16 / (D:ℝ)) = 40 * PAS / (D:ℝ) := by ring
    linarith
  linarith [hdiag, hoff, hfinal]

/-! ### The 4-dim aggregate g-moments `T0` (opaque), `T1`, `T2` (relative) -/

private lemma erase_prod_removeNth_g {n : ℕ} {M : Type*} [CommMonoid M] (m : Fin (n + 1)) (F : Fin
        (n + 1) → M) :
    ∏ i ∈ Finset.univ.erase m, F i = ∏ i : Fin n, F (m.succAbove i) := by
  have he : Finset.univ.erase m = ({m}ᶜ : Finset (Fin (n + 1))) := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]
  rw [he, ← Fin.image_succAbove_univ m, Finset.prod_image
    (fun i _ j _ h => Fin.succAbove_right_injective h)]

-- factor a single "marked" coordinate over the product box (n = 4)
private lemma factor_one {n : ℕ} (F_R : Finset ℕ) (i : Fin n) (w : ℕ → ℝ) :
    ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R), w (ρ i) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) * (∑ x ∈ F_R, (1 / (gMult x : ℝ))) ^ (n - 1) := by
  classical
  have hrw : ∀ ρ : Fin n → ℕ, w (ρ i) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∏ k, (if k = i then w (ρ k) * (1 / (gMult (ρ k) : ℝ)) else (1 / (gMult (ρ k) : ℝ))) := by
    intro ρ
    rw [← Finset.mul_prod_erase Finset.univ (fun k => (1 / (gMult (ρ k) : ℝ))) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ
        (fun k => if k = i then w (ρ k) * (1 / (gMult (ρ k) : ℝ)) else (1 / (gMult (ρ k) : ℝ)))
        (Finset.mem_univ i)]
    rw [if_pos rfl]
    have hp : (∏ k ∈ Finset.univ.erase i,
        (if k = i then w (ρ k) * (1 / (gMult (ρ k) : ℝ)) else (1 / (gMult (ρ k) : ℝ))))
        = ∏ k ∈ Finset.univ.erase i, (1 / (gMult (ρ k) : ℝ)) :=
      Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))
    rw [hp]; ring
  rw [Finset.sum_congr rfl (fun ρ _ => hrw ρ),
    ← Finset.prod_univ_sum (fun _ : Fin n => F_R)
      (fun k x => if k = i then w x * (1 / (gMult x : ℝ)) else (1 / (gMult x : ℝ)))]
  have heval : ∀ k : Fin n, (∑ x ∈ F_R, (if k = i then w x * (1 / (gMult x : ℝ)) else (1 /
          (gMult x : ℝ))))
      = if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) else (∑ x ∈ F_R, (1 /
              (gMult x : ℝ))) := by
    intro k; by_cases hk : k = i
    · simp only [hk, if_true]
    · simp only [hk, if_false]
  rw [Finset.prod_congr rfl (fun k _ => heval k)]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun k => if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) else (∑ x ∈ F_R, (1 /
              (gMult x : ℝ))))
      (Finset.mem_univ i)]
  rw [if_pos rfl]
  have hp2 : (∏ k ∈ Finset.univ.erase i,
      (if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) else (∑ x ∈ F_R, (1 / (gMult x : ℝ)))))
      = ∏ k ∈ Finset.univ.erase i, (∑ x ∈ F_R, (1 / (gMult x : ℝ))) :=
    Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))
  rw [hp2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

private lemma P_subadd {n : ℕ} (ρ : Fin n → ℕ) (hρ : ∀ i, ρ i ≠ 0) :
    (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
      ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
  classical
  have hsub : (∏ i, ρ i).primeFactors ⊆ Finset.univ.biUnion (fun i => (ρ i).primeFactors) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨i, _, hpi⟩ := (Prime.exists_mem_finset_dvd hpp.prime hpdvd)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, Nat.mem_primeFactors.mpr ⟨hpp, hpi, hρ i⟩⟩
  calc (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
      ≤ ∑ p ∈ Finset.univ.biUnion (fun i => (ρ i).primeFactors), (1 / ((p:ℝ) - 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        rw [Finset.mem_biUnion] at hp
        obtain ⟨i, _, hpi⟩ := hp
        have hpp := Nat.prime_of_mem_primeFactors hpi
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        positivity
    _ ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
        apply mjs_sum_biUnion_le
        intro i _ p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        positivity

-- common: enlarge a nonneg per-coordinate weighted sum from kSieveIndex4 (via decBox4)
-- to the product box
private lemma enlarge_to_PB {n : ℕ} (W' D R : ℕ) (_hD : 3 ≤ D) (_hDW : ∀ p : ℕ,
        p.Prime → ¬ p ∣ W' → D < p)
    (num : (Fin n → ℕ) → ℝ) (hnum0 : ∀ ρ, 0 ≤ num ρ) :
    (∑ ρ ∈ kSieveIndex n R W', num ρ / ∏ i, (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => (Finset.range R).filter
              (fun x => Squarefree x ∧ x.Coprime W')),
          num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
  classical
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  have hsub1 : kSieveIndex n R W' ⊆ decBox n R W' := by
    intro r hr
    have hmem := (mem_kSieveIndex_iff r).mp hr
    obtain ⟨hsqf, _, hcop, hprod⟩ := hmem
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
  have hsub2 : decBox n R W' ⊆ Fintype.piFinset (fun _ : Fin n => F_R) := by
    intro r hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
    rw [Fintype.mem_piFinset]; intro i
    rw [hF_R, Finset.mem_filter, Finset.mem_range]; exact ⟨hr.1 i, hr.2.1 i, hr.2.2.1 i⟩
  have hrw : ∀ ρ, num ρ / ∏ i, (gMult (ρ i) : ℝ) = num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
    intro ρ; rw [Finset.prod_div_distrib, Finset.prod_const_one, div_eq_mul_inv, one_div,
      ← Finset.prod_inv_distrib]
  have hnn : ∀ ρ, 0 ≤ num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
    fun ρ => mul_nonneg (hnum0 ρ) (Finset.prod_nonneg (fun i _ => by positivity))
  calc (∑ ρ ∈ kSieveIndex n R W', num ρ / ∏ i, (gMult (ρ i) : ℝ))
      = ∑ ρ ∈ kSieveIndex n R W', num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
        Finset.sum_congr rfl (fun ρ _ => hrw ρ)
    _ ≤ ∑ ρ ∈ decBox n R W', num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun ρ _ _ => hnn ρ)
    _ ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R), num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun ρ _ _ => hnn ρ)

/-! ## NEW: the general-`n` relative aggregate moments `T0`, `T1`, `T2` -/

private lemma pow_split_g (n : ℕ) (hn : 1 ≤ n) (a : ℝ) : a ^ n = a * a ^ (n - 1) := by
  rw [← pow_succ']; congr 1; omega

private lemma T0_op_g (n : ℕ) (hn : 1 ≤ n) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
        (cg : ℝ) (_hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex n R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ)) ≤ (cg * Real.log R) ^ n := by
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ cg * Real.log R := mjs_M0_op W' hW' hpos cg hcg D R hD hDW hR2
  have h1 := enlarge_to_PB (n := n) W' D R hD hDW (fun _ => (1:ℝ)) (fun _ => zero_le_one)
  refine le_trans h1 ?_
  have hfac := factor_one F_R ⟨0, hn⟩ (fun _ => (1:ℝ))
  simp only [one_mul] at hfac ⊢
  rw [hfac]
  calc (∑ x ∈ F_R, (1 / (gMult x : ℝ))) * (∑ x ∈ F_R, (1 / (gMult x : ℝ))) ^ (n - 1)
      = M0 ^ n := by rw [pow_split_g n hn M0]
    _ ≤ (cg * Real.log R) ^ n := pow_le_pow_left₀ hM0nn hM0le n

private lemma T1_rel_g (n : ℕ) (hn : 1 ≤ n) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex n R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ))
      ≤ (8 * (n:ℝ) * 2 ^ (n - 1)) * (Salt.Maynard.phiAtomSum R W') ^ n / (D:ℝ) := by
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ) with hMQdef
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * PAS := mjs_M0_rel W' hW' hpos D R hD hDW hR2
  have hMQnn : 0 ≤ MQ := Finset.sum_nonneg (fun x _ => div_nonneg (mjs_PFsum_nn _) (by positivity))
  have hMQle : MQ ≤ 8 * PAS / (D:ℝ) := mjs_MQ_rel W' hW' hpos D R hD hDW hR2
  have h1 := enlarge_to_PB (n := n) W' D R hD hDW
    (fun ρ => ∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) (fun ρ => mjs_PFsum_nn _)
  refine le_trans h1 ?_
  have hstep2 : ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
          (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    exact mul_le_mul_of_nonneg_right (P_subadd ρ hρne)
      (Finset.prod_nonneg (fun i _ => by positivity))
  refine le_trans hstep2 ?_
  have hdist : ∀ ρ : Fin n → ℕ,
      (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
    fun ρ => by rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => hdist ρ), Finset.sum_comm]
  have hi : ∀ i : Fin n,
      (∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
        (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ * M0 ^ (n - 1) := by
    intro i
    rw [factor_one F_R i (fun x => ∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1)))]
    congr 1
    rw [hMQdef]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hM0cube : M0 ^ (n - 1) ≤ (2 * PAS) ^ (n - 1) := pow_le_pow_left₀ hM0nn hM0le (n - 1)
  have hMQM0 : MQ * M0 ^ (n - 1) ≤ (8 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1) :=
    mul_le_mul hMQle hM0cube (by positivity) (by positivity)
  calc (n:ℝ) * (MQ * M0 ^ (n - 1)) ≤ (n:ℝ) * ((8 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hMQM0 (Nat.cast_nonneg _)
    _ = (8 * (n:ℝ) * 2 ^ (n - 1)) * (PAS * PAS ^ (n - 1)) / (D:ℝ) := by rw [mul_pow]; ring
    _ = (8 * (n:ℝ) * 2 ^ (n - 1)) * PAS ^ n / (D:ℝ) := by rw [← pow_split_g n hn PAS]

private lemma T2_rel_g (n : ℕ) (hn : 1 ≤ n) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex n R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ))
      ≤ (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * (Salt.Maynard.phiAtomSum R W') ^ n / (D:ℝ) := by
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set PB := Fintype.piFinset (fun _ : Fin n => F_R) with hPBdef
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ2 := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / (gMult x : ℝ) with hMQ2def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * PAS := mjs_M0_rel W' hW' hpos D R hD hDW hR2
  have hMQ2le : MQ2 ≤ 40 * PAS / (D:ℝ) := mjs_MQ2_rel W' hW' hpos D R hD hDW hR2
  have hQsqmom : ∀ i : Fin n,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ2 * M0 ^ (n - 1) := by
    intro i
    rw [hPBdef, factor_one F_R i (fun x => (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)]
    congr 1
    rw [hMQ2def]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  have h1 := enlarge_to_PB (n := n) W' D R hD hDW
    (fun ρ => (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2) (fun ρ => sq_nonneg _)
  refine le_trans h1 ?_
  rw [← hPBdef]
  have hstep2 : ∑ ρ ∈ PB,
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ PB, (∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [hPBdef, Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    have hsub := P_subadd ρ hρne
    have hsq : (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
        ≤ (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2 :=
      pow_le_pow_left₀ (mjs_PFsum_nn _) hsub 2
    have hexp : (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2
        = ∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) := by rw [pow_two, sum_mul_sum]
    rw [hexp] at hsq
    exact mul_le_mul_of_nonneg_right hsq (Finset.prod_nonneg (fun k _ => by positivity))
  refine le_trans hstep2 ?_
  have hdist : ∀ ρ : Fin n → ℕ,
      (∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) := by
    intro ρ; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => hdist ρ), Finset.sum_comm]
  have hswapj : ∀ i : Fin n,
      (∑ ρ ∈ PB, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = ∑ j, ∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
    fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i _ => hswapj i)]
  have hij : ∀ i j : Fin n,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      ≤ MQ2 * M0 ^ (n - 1) := by
    intro i j
    have hamgm : ∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
        ≤ ∑ ρ ∈ PB, (1/2) * ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
            * ∏ k, (1 / (gMult (ρ k) : ℝ))
            + (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
              * ∏ k, (1 / (gMult (ρ k) : ℝ))) := by
      apply Finset.sum_le_sum; intro ρ _
      have hprodnn : 0 ≤ ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
        Finset.prod_nonneg (fun k _ => by positivity)
      have hamg : (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
            * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))
          ≤ (1/2) * ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
              + (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2) := by
        nlinarith [sq_nonneg ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          - (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))))]
      linarith only [mul_le_mul_of_nonneg_right hamg hprodnn]
    refine le_trans hamgm (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hQsqmom i, hQsqmom j]; ring
  calc ∑ i, ∑ j, (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      ≤ ∑ i : Fin n, ∑ j : Fin n, MQ2 * M0 ^ (n - 1) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hij i j))
    _ = (n:ℝ) ^ 2 * (MQ2 * M0 ^ (n - 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * PAS ^ n / (D:ℝ) := by
        have hM0cube : M0 ^ (n - 1) ≤ (2 * PAS) ^ (n - 1) := pow_le_pow_left₀ hM0nn hM0le (n - 1)
        have hMM : MQ2 * M0 ^ (n - 1) ≤ (40 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1) :=
          mul_le_mul hMQ2le hM0cube (by positivity) (by positivity)
        calc (n:ℝ) ^ 2 * (MQ2 * M0 ^ (n - 1))
            ≤ (n:ℝ) ^ 2 * ((40 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1)) :=
              mul_le_mul_of_nonneg_left hMM (by positivity)
          _ = (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * (PAS * PAS ^ (n - 1)) / (D:ℝ) := by
              rw [mul_pow]; ring
          _ = (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * PAS ^ n / (D:ℝ) := by
              rw [← pow_split_g n hn PAS]

/-- general-`n` `mjs_absorb`: the mixed-base absorptions of the opaque `1/L` pieces. -/
private lemma absorb_g (n : ℕ) (κ L : ℝ) (hκ : 0 < κ) (hL : 1 ≤ L) :
    κ * L * L ^ n ≤ 1 / κ ^ (n + 1) * (1 + κ * L) ^ (n + 2) * (1 / L)
    ∧ L ^ n ≤ 1 / κ ^ (n + 2) * (1 + κ * L) ^ (n + 2) * (1 / L) := by
  have hLpos : 0 < L := by linarith
  have hbase : (κ * L) ^ (n + 2) ≤ (1 + κ * L) ^ (n + 2) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (n + 2)
  constructor
  · rw [show 1 / κ ^ (n + 1) * (1 + κ * L) ^ (n + 2) * (1 / L)
        = (1 + κ * L) ^ (n + 2) / (κ ^ (n + 1) * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc κ * L * L ^ n * (κ ^ (n + 1) * L) = (κ * L) ^ (n + 2) := by ring
      _ ≤ (1 + κ * L) ^ (n + 2) := hbase
  · rw [show 1 / κ ^ (n + 2) * (1 + κ * L) ^ (n + 2) * (1 / L)
        = (1 + κ * L) ^ (n + 2) / (κ ^ (n + 2) * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc L ^ n * (κ ^ (n + 2) * L) = κ ^ (n + 2) * L ^ (n + 1) := by ring
      _ ≤ κ ^ (n + 2) * L ^ (n + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc L ^ (n + 1) = L ^ (n + 1) * 1 := by ring
            _ ≤ L ^ (n + 1) * L := by apply mul_le_mul_of_nonneg_left hL (by positivity)
            _ = L ^ (n + 2) := by ring
      _ = (κ * L) ^ (n + 2) := by ring
      _ ≤ (1 + κ * L) ^ (n + 2) := hbase

set_option maxHeartbeats 2000000 in
-- the general-`n` square-expansion and absorption calc chains are long; the k = 5 template is too
omit [Salt.Maynard.TupleChoice] in
theorem mv_J_split_gen_of (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hMain : MvJMainSplitGen n P m) (hIC : InnerContractRelGen n P m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
              (∑ u ∈ Finset.range R,
                  yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
          + A * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D := by
  classical
  obtain ⟨Amain, hAmain0, hAmain⟩ := hMain
  obtain ⟨Aic, hAic0, hAic⟩ := hIC
  set cF : ℝ := ((contractB m P).map (fun mo => |(mo.2.2 : ℝ)|)).sum with hcFdef
  have hcF0 : 0 ≤ cF := by
    rw [hcFdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨mo, _, rfl⟩ := hx; exact abs_nonneg _
  set C1 : ℝ := 8 * (n:ℝ) * 2 ^ (n - 1) with hC1def
  set C2 : ℝ := 40 * (n:ℝ) ^ 2 * 2 ^ (n - 1) with hC2def
  have hC1 : 0 ≤ C1 := by rw [hC1def]; positivity
  have hC2 : 0 ≤ C2 := by rw [hC2def]; positivity
  refine ⟨Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2, by
    have h1 : 0 ≤ (2 * C1) * cF * Aic := by
      apply mul_nonneg (mul_nonneg (by linarith) hcF0) hAic0
    have h2 : 0 ≤ (2 * C2) * Aic ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  obtain ⟨cg, hcg0, hcg⟩ := marked_sqf_g W' hW' hpos 0
  obtain ⟨cmain, hcmain0, hcmain⟩ := hAmain W' D hW' hpos hUpper hD hDW
  obtain ⟨cic, hcic0, hcic⟩ := hAic W' D hW' hpos hUpper hD hDW
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  have hκle1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by exact_mod_cast hpos)]; exact_mod_cast Nat.totient_le W'
  refine ⟨cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2),
          by positivity, ?_⟩
  intro R hlogR
  have hRpos : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · rw [h] at hlogR; simp at hlogR; linarith
    · exact h
  have hR2 : 2 ≤ R := by
    have hRr : (0:ℝ) < (R:ℝ) := by exact_mod_cast hRpos
    have h2e : (2:ℝ) ≤ Real.exp (Real.log R) := by
      calc (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
        _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hlogR
    rw [Real.exp_log hRr] at h2e; exact_mod_cast h2e
  set L : ℝ := Real.log R with hLdef
  set X : ℝ := κ * L with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hDpos : (0:ℝ) < (D:ℝ) := by
    have : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    linarith
  have hclogR : 0 ≤ cg * L := mul_nonneg hcg0 hLpos.le
  set Y : ℝ := 1 + X + PAS with hYdef
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith
  have hXY : X ≤ Y := by rw [hYdef]; linarith
  have hPASY : PAS ≤ Y := by rw [hYdef]; linarith
  have h1PASY : 1 + PAS ≤ Y := by rw [hYdef]; linarith
  have hY0 : 0 ≤ Y := by linarith
  -- abbreviations
  set filt := (kSieveIndex (n + 1) R W').filter (fun r => r m = 1) with hfiltdef
  set Denom : (Fin (n + 1) → ℕ) → ℝ := fun r => ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)
    with hDenomdef
  set Inn : (Fin (n + 1) → ℕ) → ℝ := fun r => ∑ u ∈ Finset.range R,
      yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ) with hInndef
  set Ev : (Fin (n + 1) → ℕ) → ℝ := fun r =>
      eval (contractB m P) (fun i => Real.log (r (m.succAbove i)) / L) with hEvdef
  set Pr : (Fin (n + 1) → ℕ) → ℝ := fun r =>
      ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p:ℝ) - 1)) with hPrdef
  have hX_eq : (W'.totient : ℝ) / W' * Real.log R = X := by rw [hXdef, hκdef, hLdef]
  -- Denom positive on filt
  have hDenompos : ∀ r ∈ filt, 0 < Denom r := by
    intro r hr; rw [hfiltdef, Finset.mem_filter, mem_kSieveIndex_iff] at hr
    obtain ⟨⟨hsqf, _, hcop, _⟩, _⟩ := hr
    rw [hDenomdef]; apply Finset.prod_pos; intro i _
    have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this
  have hprodeq : ∀ r ∈ filt, (∏ i, r i) = ∏ i : Fin n, r (m.succAbove i) := by
    intro r hr; rw [hfiltdef, Finset.mem_filter] at hr
    rw [Fin.prod_univ_succAbove (fun j => r j) m, hr.2, one_mul]
  -- |Ev| ≤ cF on filt
  have hEvbd : ∀ r ∈ filt, |Ev r| ≤ cF := by
    intro r hr
    have hrmem := hr
    rw [hfiltdef, Finset.mem_filter] at hr
    have hrk := hr.1
    rw [hEvdef, hcFdef]
    apply mjs_eval_bpoly_bound
    · intro i; apply div_nonneg (Real.log_nonneg _) hLpos.le
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (kSieveIndex_coord_pos hrk (m.succAbove i)).ne'
    · intro i; rw [div_le_one hLpos, hLdef]
      exact Real.log_le_log (by exact_mod_cast kSieveIndex_coord_pos hrk (m.succAbove i))
        (by exact_mod_cast (kSieveIndex_coord_lt hrk (m.succAbove i)).le)
    · have hpe := hprodeq r hrmem
      have hprodlt : (∏ i, r i) < R := ((mem_kSieveIndex_iff r).mp hrk).2.2.2
      have hlogsum : (∑ i : Fin n, Real.log (r (m.succAbove i))) = Real.log ((∏ i, r i : ℕ):ℝ) := by
        have h1 : ((∏ i, r i : ℕ):ℝ) = ∏ i : Fin n, ((r (m.succAbove i) : ℕ):ℝ) := by
          rw [hpe, Nat.cast_prod]
        rw [h1, Real.log_prod
          (fun i _ => by exact_mod_cast (kSieveIndex_coord_pos hrk (m.succAbove i)).ne')]
      rw [← Finset.sum_div, div_le_one hLpos, hlogsum, hLdef]
      exact Real.log_le_log
        (by exact_mod_cast Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hrk i))
        (by exact_mod_cast hprodlt.le)
  -- inner_contract_rel per r
  have hInnbd : ∀ r ∈ filt, |Inn r - X * Ev r| ≤ cic + Aic * PAS * Pr r := by
    intro r hr
    rw [hfiltdef, Finset.mem_filter] at hr
    have := hcic R hlogR r hr.1 hr.2
    rw [hX_eq] at this
    exact this
  -- the reindex helper
  have hreindex_gen : ∀ (gn : ℕ → ℝ),
      (∑ r ∈ filt, gn (∏ i, r i) / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W', gn (∏ i, ρ i) / ∏ i, (gMult (ρ i) : ℝ) := by
    intro gn
    rw [← sum_filt_removeNth_g R W' m (fun ρ => gn (∏ i, ρ i) / ∏ i, (gMult (ρ i) : ℝ))]
    rw [hfiltdef]
    apply Finset.sum_congr rfl
    intro r hr
    have hrf : r ∈ filt := by rw [hfiltdef]; exact hr
    simp only [hDenomdef, Fin.removeNth_apply]
    rw [erase_prod_removeNth_g m (fun i => (gMult (r i):ℝ)), hprodeq r hrf]
  -- S0, S1, S2 bounds
  have hS0le : (∑ r ∈ filt, (1:ℝ) / Denom r) ≤ (cg * L) ^ n := by
    have key : (∑ r ∈ filt, (1:ℝ) / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun _ => 1)
    rw [key]; exact T0_op_g n hn W' hW' hpos cg hcg0 hcg D R hD hDW hR2
  have hS1le : (∑ r ∈ filt, Pr r / Denom r) ≤ C1 * PAS ^ n / (D:ℝ) := by
    have key : (∑ r ∈ filt, Pr r / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => ∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1)))
    rw [key, hPASdef]; exact T1_rel_g n hn W' hW' hpos D R hD hDW hR2
  have hS2le : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) ≤ C2 * PAS ^ n / (D:ℝ) := by
    have key : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => (∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)
    rw [key, hPASdef]; exact T2_rel_g n hn W' hW' hpos D R hD hDW hR2
  -- === main part via mv_J_main_split ===
  have hEvSum : |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ n * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ n / L + Amain * (1 + PAS) ^ n / (D:ℝ) := by
    have h := hcmain R hlogR
    rw [hX_eq, ← hLdef, ← hPASdef] at h
    exact h
  have hmainpart : |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ (n + 2) / L + Amain * Y ^ (n + 2) / (D:ℝ) := by
    have hfac : X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)
        = X ^ 2 * ((∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ n * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ X ^ 2)]
    -- X² · (1/L-bound + 1/D-bound)
    have hLpart : X ^ 2 * (cmain * (1 + X) ^ n / L) ≤ cmain * (1 + X) ^ (n + 2) / L := by
      have hXsq : X ^ 2 ≤ (1 + X) ^ 2 := pow_le_pow_left₀ hX0 (by linarith) 2
      have e : X ^ 2 * (cmain * (1 + X) ^ n / L) = cmain * (X ^ 2 * (1 + X) ^ n) / L := by ring
      have e2 : cmain * (1 + X) ^ (n + 2) / L = cmain * ((1 + X) ^ 2 * (1 + X) ^ n) / L := by ring
      rw [e, e2]
      refine div_le_div_of_nonneg_right ?_ hLpos.le
      refine mul_le_mul_of_nonneg_left ?_ hcmain0
      exact mul_le_mul_of_nonneg_right hXsq (by positivity)
    have hDpart : X ^ 2 * (Amain * (1 + PAS) ^ n / (D:ℝ)) ≤ Amain * Y ^ (n + 2) / (D:ℝ) := by
      have hkey : X ^ 2 * (1 + PAS) ^ n ≤ Y ^ (n + 2) := by
        calc X ^ 2 * (1 + PAS) ^ n ≤ Y ^ 2 * Y ^ n :=
              mul_le_mul (pow_le_pow_left₀ hX0 hXY 2) (pow_le_pow_left₀ (by linarith) h1PASY n)
                (by positivity) (by positivity)
          _ = Y ^ (n + 2) := by ring
      have e : X ^ 2 * (Amain * (1 + PAS) ^ n / (D:ℝ))
          = Amain * (X ^ 2 * (1 + PAS) ^ n) / (D:ℝ) := by
        ring
      rw [e]
      refine div_le_div_of_nonneg_right ?_ hDpos.le
      exact mul_le_mul_of_nonneg_left hkey hAmain0
    calc X ^ 2 * |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ n * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ X ^ 2 * (cmain * (1 + X) ^ n / L + Amain * (1 + PAS) ^ n / (D:ℝ)) :=
          mul_le_mul_of_nonneg_left hEvSum (by positivity)
      _ = X ^ 2 * (cmain * (1 + X) ^ n / L) + X ^ 2 * (Amain * (1 + PAS) ^ n / (D:ℝ)) := by ring
      _ ≤ cmain * (1 + X) ^ (n + 2) / L + Amain * Y ^ (n + 2) / (D:ℝ) := add_le_add hLpart hDpart
  -- === error part (Approach A: Inn² − X²Ev² = 2X·Ev·δ + δ²) ===
  have hPrnn : ∀ r, 0 ≤ Pr r := fun r => by rw [hPrdef]; exact mjs_PFsum_nn _
  have hterm : ∀ r ∈ filt,
      |(Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)|
      ≤ ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r := by
    intro r hr
    have hdpos := hDenompos r hr
    have hE := hEvbd r hr
    have hI := hInnbd r hr
    have hPr := hPrnn r
    set δ : ℝ := Inn r - X * Ev r with hδdef
    set Q : ℝ := Aic * PAS * Pr r with hQdef
    have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
    have hδbd : |δ| ≤ cic + Q := by rw [hδdef, hQdef]; exact hI
    have hnum : (Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2 = 2 * X * (Ev r) * δ + δ ^ 2 := by
      rw [hδdef]; ring
    have habs : |(Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2|
        ≤ (2 * X * cF * cic + 2 * cic ^ 2) + 2 * X * cF * Aic * PAS * Pr r
          + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2 := by
      rw [hnum]
      have h1 : |2 * X * (Ev r) * δ| = 2 * X * |Ev r| * |δ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * X)]
      have h2 : |2 * X * (Ev r) * δ| ≤ 2 * X * cF * (cic + Q) := by
        rw [h1]
        have hb : |Ev r| * |δ| ≤ cF * (cic + Q) :=
          mul_le_mul hE hδbd (abs_nonneg _) hcF0
        calc 2 * X * |Ev r| * |δ| = 2 * X * (|Ev r| * |δ|) := by ring
          _ ≤ 2 * X * (cF * (cic + Q)) := mul_le_mul_of_nonneg_left hb (by positivity)
          _ = 2 * X * cF * (cic + Q) := by ring
      have h3 : |δ ^ 2| ≤ 2 * cic ^ 2 + 2 * Q ^ 2 := by
        rw [abs_pow]
        have hsq : |δ| ^ 2 ≤ (cic + Q) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδbd 2
        linarith only [hsq, sq_nonneg (cic - Q)]
      have hcomb : 2 * X * cF * (cic + Q) + (2 * cic ^ 2 + 2 * Q ^ 2)
          = (2 * X * cF * cic + 2 * cic ^ 2) + 2 * X * cF * Aic * PAS * Pr r
            + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2 := by rw [hQdef]; ring
      calc |2 * X * (Ev r) * δ + δ ^ 2|
          ≤ |2 * X * (Ev r) * δ| + |δ ^ 2| := abs_add_le _ _
        _ ≤ 2 * X * cF * (cic + Q) + (2 * cic ^ 2 + 2 * Q ^ 2) := add_le_add h2 h3
        _ = _ := hcomb
    have heq : (Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)
        = ((Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2) / Denom r := by ring
    rw [heq, abs_div, abs_of_pos hdpos]
    exact div_le_div_of_nonneg_right habs hdpos.le
  have herr : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
      ≤ ∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hbound_eq : (∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r)
      = (2 * X * cF * cic + 2 * cic ^ 2) * (∑ r ∈ filt, 1 / Denom r)
        + (2 * X * cF * Aic * PAS) * (∑ r ∈ filt, Pr r / Denom r)
        + (2 * Aic ^ 2 * PAS ^ 2) * (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  have herr2 : (∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r)
      ≤ (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
        + (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
        + (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ)) := by
    rw [hbound_eq]
    have c0 : 0 ≤ 2 * X * cF * cic + 2 * cic ^ 2 := by positivity
    have c1 : 0 ≤ 2 * X * cF * Aic * PAS := by positivity
    have c2 : 0 ≤ 2 * Aic ^ 2 * PAS ^ 2 := by positivity
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hS0le c0
    · exact mul_le_mul_of_nonneg_left hS1le c1
    · exact mul_le_mul_of_nonneg_left hS2le c2
  -- === absorptions ===
  obtain ⟨habsXL0, habsL0⟩ := absorb_g n κ L hκpos hL1
  have habsXL : X * L ^ n ≤ (1 / κ ^ (n + 1)) * (1 + X) ^ (n + 2) * (1 / L) := by
    rw [hXdef]; exact habsXL0
  have habsL : L ^ n ≤ (1 / κ ^ (n + 2)) * (1 + X) ^ (n + 2) * (1 / L) := by
    rw [hXdef]; exact habsL0
  -- assemble error side
  have hLLnn : (0:ℝ) ≤ 1 / L := by positivity
  have hXPAS5 : X * PAS ^ (n + 1) ≤ Y ^ (n + 2) := by
    calc X * PAS ^ (n + 1) ≤ Y * Y ^ (n + 1) :=
          mul_le_mul hXY (pow_le_pow_left₀ hPAS0 hPASY (n + 1)) (by positivity) hY0
      _ = Y ^ (n + 2) := by ring
  have hPAS6 : PAS ^ (n + 2) ≤ Y ^ (n + 2) := pow_le_pow_left₀ hPAS0 hPASY (n + 2)
  -- the 1/L opaque pieces
  have hm1 : (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
      ≤ (2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1 + X) ^
              (n + 2) / L := by
    have e : (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
        = (2 * cF * cic * cg ^ n) * (X * L ^ n) + (2 * cic ^ 2 * cg ^ n) * (L ^ n) := by ring
    rw [e]
    have hb1 : (2 * cF * cic * cg ^ n) * (X * L ^ n)
        ≤ (2 * cF * cic * cg ^ n) * ((1 / κ ^ (n + 1)) * (1 + X) ^ (n + 2) * (1 / L)) :=
      mul_le_mul_of_nonneg_left habsXL (by positivity)
    have hb2 : (2 * cic ^ 2 * cg ^ n) * (L ^ n)
        ≤ (2 * cic ^ 2 * cg ^ n) * ((1 / κ ^ (n + 2)) * (1 + X) ^ (n + 2) * (1 / L)) :=
      mul_le_mul_of_nonneg_left habsL (by positivity)
    calc (2 * cF * cic * cg ^ n) * (X * L ^ n) + (2 * cic ^ 2 * cg ^ n) * (L ^ n)
        ≤ (2 * cF * cic * cg ^ n) * ((1 / κ ^ (n + 1)) * (1 + X) ^ (n + 2) * (1 / L))
          + (2 * cic ^ 2 * cg ^ n) * ((1 / κ ^ (n + 2)) * (1 + X) ^ (n + 2) * (1 / L))
                  := add_le_add hb1 hb2
      _ = (2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1 + X) ^
              (n + 2) / L := by
        ring
  -- the 1/D relative pieces
  have hm2 : (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
      ≤ ((2 * C1) * cF * Aic) * Y ^ (n + 2) / (D:ℝ) := by
    have e : (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
        = ((2 * C1) * cF * Aic) * (X * PAS ^ (n + 1)) / (D:ℝ) := by ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    exact mul_le_mul_of_nonneg_left hXPAS5 (mul_nonneg (mul_nonneg (by linarith) hcF0) hAic0)
  have hm3 : (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ))
      ≤ ((2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ) := by
    have e : (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ))
        = ((2 * C2) * Aic ^ 2) * (PAS ^ (n + 2)) / (D:ℝ) := by ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    exact mul_le_mul_of_nonneg_left hPAS6 (mul_nonneg (by linarith) (sq_nonneg _))
  -- === final assembly ===
  have hgoal : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
      ≤ (cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1
              + X) ^ (n + 2) / L
        + (Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ) := by
    calc |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
            - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r) - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
          + |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)| := abs_sub_le _ _ _
      _ ≤ ((2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
            + (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
            + (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ)))
          + (cmain * (1 + X) ^ (n + 2) / L + Amain * Y ^ (n + 2) / (D:ℝ)) :=
          add_le_add (le_trans herr herr2) hmainpart
      _ ≤ (cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) *
              (1 + X) ^ (n + 2) / L
          + (Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ) := by
          have hexpand :
              (cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2))
                  * (1 + X) ^ (n + 2) / L
              = (2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1
                      + X) ^ (n + 2) / L
                + cmain * (1 + X) ^ (n + 2) / L := by ring
          have hexpand2 :
              (Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ)
              = ((2 * C1) * cF * Aic) * Y ^ (n + 2) / (D:ℝ) + ((2 * C2) * Aic ^ 2) * Y ^ (n + 2)
                      / (D:ℝ)
                + Amain * Y ^ (n + 2) / (D:ℝ) := by ring
          rw [hexpand, hexpand2]
          linarith [hm1, hm2, hm3]
  -- the frozen goal is definitionally the `Inn/Denom/X/Y` form
  exact hgoal

omit [Salt.Maynard.TupleChoice] in
/-- **B4.2b: the J-side split engine at general `n`, unconditional.** -/
theorem mv_J_split_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
              (∑ u ∈ Finset.range R,
                  yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
          + A * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D :=
  mv_J_split_gen_of n hn P m (mv_J_main_split_gen n hn P m) (inner_contract_rel_gen n hn P m)

end Salt.MaynardK

