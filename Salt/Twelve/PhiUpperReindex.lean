/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.PhiUpper

/-!
# Discharging `hReindex` (W4-0): the squarefree/powerful tsum regroup

This file lands the critical-path leaf `reindex_tail_le`, the elementary `Nat`
reindex left open in `PhiUpper.lean`, and thereby `phiUpperAtom_final`, an
unconditional `PhiUpperAtom B` for every `B ≠ 0`.

## Route (all in `ℝ`, nonneg/summable — no `ENNReal`)

* `∑_{r ∈ sqfCop x B} radFiberTail r x B` is a finite sum of fiber-tails; each
  `radFiberTail r x B` is the tsum of `n⁻¹` over `{n | rad n = r, n ≠ 0, x ≤ n}`
  (from `radFiber_inv_hasSum` minus the finite head; coprimality to `B` is
  automatic on the fiber since `rad n = r ⊥ B`).  Summing over `r` regroups to
  the tsum of `n⁻¹` over `unionDom x B = {n | rad n ∈ sqfCop x B, n ≠ 0, x ≤ n}`.
* The `Nat` decomposition `n = sqfPart n * powPart n` (squarefree × powerful,
  coprime) injects `unionDom x B` into `ℕ × ℕ` via `n ↦ (powPart n, sqfPart n)`,
  under which `n⁻¹ = windowWeight x (powPart n, sqfPart n)`.
* `windowWeight` is dominated column-by-column (fixed powerful `v`) by the
  harmonic-window estimate `∑_{a ≤ u ≤ b} 1/u ≤ 1 + log b − log a`
  (`sum_Icc_inv_le`, via mathlib's `harmonic` bounds): the `u`-window
  `[x/v, x/rad v)` gives `(1/v)(1 + log(v/rad v)) ≤ powerfulWeight v`.
* Hence `∑' windowWeight ≤ ∑' powerfulWeight`, closing the bound.
-/

open Salt.M3Expansion (rad rad_eq_primeFactors)

namespace Salt.Twelve

/-! ## The radical is multiplicative on coprime arguments -/

lemma rad_mul_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    rad (a * b) = rad a * rad b := by
  simp only [rad]
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

/-! ## The squarefree/powerful decomposition -/

/-- The squarefree part of `n`: product of primes dividing `n` to exponent `1`. -/
def sqfPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p

/-- The powerful part of `n`: product of prime powers `p ^ e_p` with `e_p ≠ 1`. -/
def powPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬ (n.factorization p = 1)), p ^ (n.factorization p)

lemma sqfPart_pos (n : ℕ) : 0 < sqfPart n := by
  rw [sqfPart]
  exact Finset.prod_pos (fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos)

lemma powPart_pos (n : ℕ) : 0 < powPart n := by
  rw [powPart]
  exact Finset.prod_pos (fun p hp =>
    pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).pos _)

/-- The fundamental factorization: `n = sqfPart n * powPart n` (for `n ≠ 0`). -/
lemma sqfPart_mul_powPart {n : ℕ} (hn : n ≠ 0) : sqfPart n * powPart n = n := by
  have hself : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    have h1 := Nat.prod_factorization_pow_eq_self hn
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at h1
  have hsqf : sqfPart n
      = ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p ^ (n.factorization p) := by
    rw [sqfPart]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [hp.2, pow_one]
  rw [hsqf, powPart,
    Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => n.factorization p = 1)
      (fun p => p ^ (n.factorization p))]
  exact hself

lemma sqfPart_squarefree (n : ℕ) : Squarefree (sqfPart n) := by
  rw [sqfPart]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    have ha' := Finset.mem_of_mem_filter a (Finset.mem_coe.mp ha)
    have hb' := Finset.mem_of_mem_filter b (Finset.mem_coe.mp hb)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha')
        (Nat.prime_of_mem_primeFactors hb')).mpr hab)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)).prime.squarefree

lemma sqfPart_coprime_powPart (n : ℕ) : Nat.Coprime (sqfPart n) (powPart n) := by
  rw [sqfPart]
  apply Nat.Coprime.prod_left
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)
  have hp1 : n.factorization p = 1 := (Finset.mem_filter.mp hp).2
  rw [hpp.coprime_iff_not_dvd]
  intro hdvd
  rw [powPart] at hdvd
  obtain ⟨q, hq, hpq⟩ := hpp.prime.exists_mem_finset_dvd hdvd
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)
  have hq1 : ¬ (n.factorization q = 1) := (Finset.mem_filter.mp hq).2
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.dvd_of_dvd_pow hpq)
  rw [heq] at hp1
  exact hq1 hp1

lemma powPart_isPowerful (n : ℕ) : IsPowerful (powPart n) := by
  intro q hq hqdvd
  rw [powPart] at hqdvd ⊢
  obtain ⟨p, hp, hqp⟩ := hq.prime.exists_mem_finset_dvd hqdvd
  have hpmem : p ∈ n.primeFactors := Finset.mem_of_mem_filter p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hp2ne : ¬ (n.factorization p = 1) := (Finset.mem_filter.mp hp).2
  obtain ⟨_, hpdvd, hn0⟩ := Nat.mem_primeFactors.mp hpmem
  have hge1 : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd hpp hn0 hpdvd
  have hfp2 : 2 ≤ n.factorization p := by omega
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hpp).mp (hq.dvd_of_dvd_pow hqp)
  subst heq
  calc q ^ 2 ∣ q ^ (n.factorization q) := pow_dvd_pow q hfp2
    _ ∣ ∏ p' ∈ n.primeFactors.filter (fun p => ¬ (n.factorization p = 1)),
          p' ^ (n.factorization p') := Finset.dvd_prod_of_mem _ hp

/-- The radical splits along the decomposition: `rad n = sqfPart n * rad (powPart n)`. -/
lemma rad_eq_sqfPart_mul_rad_powPart {n : ℕ} (hn : n ≠ 0) :
    rad n = sqfPart n * rad (powPart n) := by
  have h1 := sqfPart_mul_powPart hn
  calc rad n = rad (sqfPart n * powPart n) := by rw [h1]
    _ = rad (sqfPart n) * rad (powPart n) :=
        rad_mul_coprime (sqfPart_pos n).ne' (powPart_pos n).ne' (sqfPart_coprime_powPart n)
    _ = sqfPart n * rad (powPart n) := by
        congr 1
        rw [rad]
        exact Nat.prod_primeFactors_of_squarefree (sqfPart_squarefree n)

/-! ## Coprimality to `B` is automatic on a radical fiber -/

lemma coprime_of_rad_eq {n r B : ℕ} (hn : n ≠ 0) (hB : B ≠ 0) (h : rad n = r)
    (hrc : Nat.Coprime r B) : Nat.Coprime n B := by
  have hr0 : r ≠ 0 := by
    rw [← h, rad]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos.ne')
  rw [← Nat.disjoint_primeFactors hn hB, rad_eq_primeFactors h, Nat.disjoint_primeFactors hr0 hB]
  exact hrc

/-! ## The harmonic-window estimate -/

/-- `∑_{a ≤ u ≤ b} 1/u ≤ 1 + log b − log a` for `1 ≤ a ≤ b`, via mathlib's
`harmonic` bounds `log(n+1) ≤ H_n ≤ 1 + log n`. -/
lemma sum_Icc_inv_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ u ∈ Finset.Icc a b, (u : ℝ)⁻¹ ≤ 1 + Real.log b - Real.log a := by
  have hsub : Finset.Icc 1 (a - 1) ⊆ Finset.Icc 1 b :=
    Finset.Icc_subset_Icc le_rfl (by omega)
  have hsplit : Finset.Icc 1 b \ Finset.Icc 1 (a - 1) = Finset.Icc a b := by
    ext u; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
  have hcast : ∀ m : ℕ, (harmonic m : ℝ) = ∑ u ∈ Finset.Icc 1 m, (u : ℝ)⁻¹ := by
    intro m
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Rat.cast_inv, Rat.cast_natCast])
  have heq : ∑ u ∈ Finset.Icc a b, (u : ℝ)⁻¹ = (harmonic b : ℝ) - (harmonic (a - 1) : ℝ) := by
    rw [hcast, hcast, ← hsplit, eq_sub_iff_add_eq]
    exact Finset.sum_sdiff hsub
  rw [heq]
  have h1 : (harmonic b : ℝ) ≤ 1 + Real.log b := harmonic_le_one_add_log b
  have h2 : Real.log a ≤ (harmonic (a - 1) : ℝ) := by
    have := log_add_one_le_harmonic (a - 1)
    rwa [Nat.sub_add_cancel ha] at this
  linarith

/-! ## The window weight on `ℕ × ℕ` -/

/-- The `u`-window for a fixed `v`: `u < x`, `u ≥ 1`, `u·rad v < x ≤ u·v`. -/
def windowSet (x v : ℕ) : Finset ℕ :=
  (Finset.range x).filter (fun u => 0 < u ∧ u * rad v < x ∧ x ≤ u * v)

open Classical in
/-- `windowWeight x (v, u) = 1/(u·v)` on the window (with powerful `v`), else `0`. -/
noncomputable def windowWeight (x : ℕ) (p : ℕ × ℕ) : ℝ :=
  if IsPowerful p.1 ∧ p.1 ≠ 0 ∧ 0 < p.2 ∧ p.2 * rad p.1 < x ∧ x ≤ p.2 * p.1
  then ((p.2 * p.1 : ℕ) : ℝ)⁻¹ else 0

lemma windowWeight_nonneg (x : ℕ) (p : ℕ × ℕ) : 0 ≤ windowWeight x p := by
  rw [windowWeight]; split_ifs
  · positivity
  · exact le_rfl

lemma windowWeight_of (x v u : ℕ)
    (h : IsPowerful v ∧ v ≠ 0 ∧ 0 < u ∧ u * rad v < x ∧ x ≤ u * v) :
    windowWeight x (v, u) = ((u * v : ℕ) : ℝ)⁻¹ := by
  rw [windowWeight]; exact if_pos h

lemma windowWeight_supp (x v u : ℕ) (hu : u ∉ windowSet x v) :
    windowWeight x (v, u) = 0 := by
  rw [windowWeight]
  apply if_neg
  rintro ⟨_, _, hu0, hurad, hux⟩
  apply hu
  simp only [windowSet, Finset.mem_filter, Finset.mem_range]
  have hradv1 : 1 ≤ rad v := by
    rw [rad]
    exact Finset.one_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  exact ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_right u hradv1) hurad, hu0, hurad, hux⟩

/-! ## Summability of `powerfulWeight` -/

lemma summable_powerfulWeight : Summable powerfulWeight := by
  classical
  obtain ⟨C, hC⟩ := powerful_sum_bounded
  refine summable_of_sum_le (c := C) (fun v => powerfulWeight_nonneg v) (fun u => ?_)
  have heq : ∑ v ∈ u, powerfulWeight v
      = ∑ v ∈ u.filter (fun v => IsPowerful v ∧ v ≠ 0), (1 + Real.log v) / (v : ℝ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun v _ => by rw [powerfulWeight])
  rw [heq]
  exact hC _ (fun v hv => (Finset.mem_filter.mp hv).2)

/-! ## The column bound: `∑'_u windowWeight x (v, u) ≤ powerfulWeight v` -/

lemma windowWeight_col_le (x : ℕ) (hx : 2 ≤ x) (v : ℕ) :
    ∑' u : ℕ, windowWeight x (v, u) ≤ powerfulWeight v := by
  by_cases hv : IsPowerful v ∧ v ≠ 0
  · rw [tsum_eq_sum (s := windowSet x v) (fun u hu => windowWeight_supp x v u hu),
      powerfulWeight, if_pos hv]
    have hv0 : 0 < v := Nat.pos_of_ne_zero hv.2
    have hradv1 : 1 ≤ rad v := by
      rw [rad]
      exact Finset.one_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    have hradv0 : 0 < rad v := hradv1
    have hsumval : (∑ u ∈ windowSet x v, windowWeight x (v, u))
        = (∑ u ∈ windowSet x v, (u : ℝ)⁻¹) * (v : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun u hu => ?_)
      simp only [windowSet, Finset.mem_filter, Finset.mem_range] at hu
      rw [windowWeight_of x v u ⟨hv.1, hv.2, hu.2.1, hu.2.2.1, hu.2.2.2⟩]
      push_cast; rw [mul_inv]
    rw [hsumval, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hv1R : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv0
    have hlogv : 0 ≤ Real.log v := Real.log_nonneg hv1R
    rcases Finset.eq_empty_or_nonempty (windowSet x v) with hemp | hne
    · rw [hemp, Finset.sum_empty]; linarith
    · obtain ⟨u₀, hu₀⟩ := hne
      set aL := (x + v - 1) / v with haL_def
      set aU := (x - 1) / rad v with haU_def
      have haL1 : 1 ≤ aL := by
        rw [haL_def, Nat.le_div_iff_mul_le hv0]; omega
      have hsubset : windowSet x v ⊆ Finset.Icc aL aU := by
        intro u hu
        simp only [windowSet, Finset.mem_filter, Finset.mem_range] at hu
        obtain ⟨_, _, hurad, hux⟩ := hu
        rw [Finset.mem_Icc, haL_def, haU_def]
        refine ⟨?_, ?_⟩
        · have h : (x + v - 1) / v < u + 1 := by
            rw [Nat.div_lt_iff_lt_mul hv0]
            have he : (u + 1) * v = u * v + v := by ring
            omega
          exact Nat.le_of_lt_succ h
        · rw [Nat.le_div_iff_mul_le hradv0]; omega
      have haLaU : aL ≤ aU := by
        have := hsubset hu₀; rw [Finset.mem_Icc] at this; exact this.1.trans this.2
      have haLmul : x ≤ aL * v := by
        rw [haL_def]
        have hdm := Nat.div_add_mod (x + v - 1) v
        have hmod : (x + v - 1) % v < v := Nat.mod_lt _ hv0
        have hcomm : (x + v - 1) / v * v = v * ((x + v - 1) / v) := Nat.mul_comm _ _
        omega
      have haUmul : aU * rad v ≤ x - 1 := by rw [haU_def]; exact Nat.div_mul_le_self _ _
      have hx0R : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
      have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
      have hradv0R : (0 : ℝ) < rad v := by exact_mod_cast hradv0
      have haU0R : (0 : ℝ) < aU := by exact_mod_cast (le_trans haL1 haLaU)
      have haLge : (x : ℝ) / (v : ℝ) ≤ (aL : ℝ) := by
        rw [div_le_iff₀ hv0R]; exact_mod_cast haLmul
      have haUle : (aU : ℝ) ≤ (x : ℝ) / (rad v : ℝ) := by
        rw [le_div_iff₀ hradv0R]
        have hle : (aU * rad v : ℕ) ≤ x := le_trans haUmul (Nat.sub_le _ _)
        exact_mod_cast hle
      have hlogaL : Real.log x - Real.log v ≤ Real.log aL := by
        rw [← Real.log_div (ne_of_gt hx0R) (ne_of_gt hv0R)]
        exact Real.log_le_log (by positivity) haLge
      have hlogaU : Real.log aU ≤ Real.log x - Real.log (rad v) := by
        rw [← Real.log_div (ne_of_gt hx0R) (ne_of_gt hradv0R)]
        exact Real.log_le_log haU0R haUle
      have hlogradv : 0 ≤ Real.log (rad v) := Real.log_nonneg (by exact_mod_cast hradv1)
      calc (∑ u ∈ windowSet x v, (u : ℝ)⁻¹)
          ≤ ∑ u ∈ Finset.Icc aL aU, (u : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => by positivity)
        _ ≤ 1 + Real.log aU - Real.log aL := sum_Icc_inv_le haL1 haLaU
        _ ≤ 1 + Real.log v := by linarith
  · have h0 : ∀ u, windowWeight x (v, u) = 0 := by
      intro u
      rw [windowWeight]
      apply if_neg
      rintro ⟨hp, hne, _⟩
      exact hv ⟨hp, hne⟩
    simp only [h0, tsum_zero]
    exact powerfulWeight_nonneg v

/-! ## Summability and the total bound for `windowWeight` -/

lemma summable_windowWeight (x : ℕ) (hx : 2 ≤ x) : Summable (windowWeight x) := by
  rw [summable_prod_of_nonneg (fun p => windowWeight_nonneg x p)]
  refine ⟨fun v => ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := windowSet x v)
    intro u hu
    exact windowWeight_supp x v u hu
  · exact Summable.of_nonneg_of_le (fun v => tsum_nonneg (fun u => windowWeight_nonneg x _))
      (fun v => windowWeight_col_le x hx v) summable_powerfulWeight

lemma windowWeight_tsum_le (x : ℕ) (hx : 2 ≤ x) :
    ∑' p : ℕ × ℕ, windowWeight x p ≤ ∑' v : ℕ, powerfulWeight v := by
  have hcolsum : ∀ v, Summable (fun u => windowWeight x (v, u)) := by
    intro v
    apply summable_of_ne_finset_zero (s := windowSet x v)
    intro u hu
    exact windowWeight_supp x v u hu
  rw [(summable_windowWeight x hx).tsum_prod' hcolsum]
  refine Summable.tsum_le_tsum (fun v => windowWeight_col_le x hx v) ?_ summable_powerfulWeight
  exact Summable.of_nonneg_of_le (fun v => tsum_nonneg (fun u => windowWeight_nonneg x _))
    (fun v => windowWeight_col_le x hx v) summable_powerfulWeight

/-! ## The fiber tail as an indicator tsum, and the regroup -/

/-- The reindex map `n ↦ (powPart n, sqfPart n)`. -/
def decMap (n : ℕ) : ℕ × ℕ := (powPart n, sqfPart n)

/-- The disjoint-union domain of the regroup. -/
def unionDom (x B : ℕ) : Set ℕ := {n : ℕ | rad n ∈ Salt.Maynard.sqfCop x B ∧ n ≠ 0 ∧ x ≤ n}

/-- Each fiber tail is the tsum of `n⁻¹` over `{n | rad n = r, n ≠ 0, x ≤ n}`. -/
lemma hasSum_indicator_tail {r x B : ℕ} (hB : B ≠ 0) (hr : Squarefree r) (hrcop : Nat.Coprime r B) :
    HasSum (Set.indicator {n : ℕ | rad n = r ∧ n ≠ 0 ∧ x ≤ n} (fun n => ((n : ℕ) : ℝ)⁻¹))
      (radFiberTail r x B) := by
  classical
  set f : ℕ → ℝ := fun n => ((n : ℕ) : ℝ)⁻¹ with hf
  have hfull := radFiber_inv_hasSum hr
  set Hd : Finset ℕ :=
    (Finset.range x).filter (fun n => (n ≠ 0 ∧ Nat.Coprime n B) ∧ rad n = r) with hHd
  have hheadsum : HasSum (Set.indicator (↑Hd) f) (radFiberHead r x B) := by
    have hval : radFiberHead r x B = ∑ n ∈ Hd, Set.indicator (↑Hd) f n := by
      rw [radFiberHead]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Set.indicator_of_mem (Finset.mem_coe.mpr hn)]
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero
      (fun n hn => Set.indicator_of_notMem (fun hc => hn (Finset.mem_coe.mp hc)) f)
  have hHdsub : (↑Hd : Set ℕ) ⊆ {n : ℕ | rad n = r ∧ n ≠ 0} := by
    intro n hn
    rw [Finset.mem_coe, hHd, Finset.mem_filter] at hn
    exact ⟨hn.2.2, hn.2.1.1⟩
  have hdiff : ({n : ℕ | rad n = r ∧ n ≠ 0} : Set ℕ) \ ↑Hd
      = {n : ℕ | rad n = r ∧ n ≠ 0 ∧ x ≤ n} := by
    ext n
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, Finset.mem_coe, hHd, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hrad, hn0⟩, hnHd⟩
      refine ⟨hrad, hn0, ?_⟩
      by_contra hlt
      exact hnHd ⟨Nat.not_le.mp hlt, ⟨hn0, coprime_of_rad_eq hn0 hB hrad hrcop⟩, hrad⟩
    · rintro ⟨hrad, hn0, hxn⟩
      refine ⟨⟨hrad, hn0⟩, ?_⟩
      rintro ⟨hlt, _, _⟩
      omega
  have hres : HasSum (Set.indicator (({n : ℕ | rad n = r ∧ n ≠ 0} : Set ℕ) \ ↑Hd) f)
      (1 / (Nat.totient r : ℝ) - radFiberHead r x B) := by
    rw [Set.indicator_sdiff hHdsub]
    exact hfull.sub hheadsum
  rw [hdiff] at hres
  rw [radFiberTail]
  exact hres

/-- Fiberwise, summing the tail-indicators over `r ∈ sqfCop x B` collapses to the
indicator of `unionDom x B`. -/
lemma sum_indicator_tail_eq (x B n : ℕ) :
    (∑ r ∈ Salt.Maynard.sqfCop x B,
        Set.indicator {m : ℕ | rad m = r ∧ m ≠ 0 ∧ x ≤ m} (fun m => ((m : ℕ) : ℝ)⁻¹) n)
      = Set.indicator (unionDom x B) (fun m => ((m : ℕ) : ℝ)⁻¹) n := by
  classical
  by_cases hmem : rad n ∈ Salt.Maynard.sqfCop x B
  · have h0 : ∀ r ∈ Salt.Maynard.sqfCop x B, r ≠ rad n →
        Set.indicator {m : ℕ | rad m = r ∧ m ≠ 0 ∧ x ≤ m} (fun m => ((m : ℕ) : ℝ)⁻¹) n = 0 := by
      intro r _ hrne
      apply Set.indicator_of_notMem
      rintro ⟨hrad, _, _⟩
      exact hrne hrad.symm
    rw [Finset.sum_eq_single_of_mem (rad n) hmem h0]
    by_cases hc : n ≠ 0 ∧ x ≤ n
    · rw [Set.indicator_of_mem
          (show n ∈ {m : ℕ | rad m = rad n ∧ m ≠ 0 ∧ x ≤ m} from ⟨rfl, hc.1, hc.2⟩),
        Set.indicator_of_mem (show n ∈ unionDom x B from ⟨hmem, hc.1, hc.2⟩)]
    · rw [Set.indicator_of_notMem
          (show n ∉ {m : ℕ | rad m = rad n ∧ m ≠ 0 ∧ x ≤ m} from fun h => hc ⟨h.2.1, h.2.2⟩),
        Set.indicator_of_notMem (show n ∉ unionDom x B from fun h => hc ⟨h.2.1, h.2.2⟩)]
  · rw [Set.indicator_of_notMem (show n ∉ unionDom x B from fun h => hmem h.1)]
    apply Finset.sum_eq_zero
    intro r hr
    apply Set.indicator_of_notMem
    rintro ⟨hrad, _, _⟩
    exact hmem (by rw [hrad]; exact hr)

/-- The regroup: `∑_{r ∈ sqfCop x B} radFiberTail r x B` is the tsum of `n⁻¹`
over `unionDom x B`. -/
lemma hasSum_indicator_U (x B : ℕ) (hB : B ≠ 0) :
    HasSum (Set.indicator (unionDom x B) (fun n => ((n : ℕ) : ℝ)⁻¹))
      (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B) := by
  have hpr : ∀ r ∈ Salt.Maynard.sqfCop x B,
      HasSum (Set.indicator {n : ℕ | rad n = r ∧ n ≠ 0 ∧ x ≤ n} (fun n => ((n : ℕ) : ℝ)⁻¹))
        (radFiberTail r x B) := by
    intro r hr
    rw [Salt.Maynard.sqfCop, Finset.mem_filter] at hr
    exact hasSum_indicator_tail hB hr.2.1 hr.2.2
  have hsum := hasSum_sum hpr
  have hfun : (fun p => ∑ r ∈ Salt.Maynard.sqfCop x B,
        Set.indicator {n : ℕ | rad n = r ∧ n ≠ 0 ∧ x ≤ n} (fun n => ((n : ℕ) : ℝ)⁻¹) p)
      = Set.indicator (unionDom x B) (fun n => ((n : ℕ) : ℝ)⁻¹) := by
    funext p
    exact sum_indicator_tail_eq x B p
  rwa [hfun] at hsum

/-! ## The frozen deliverables -/

theorem reindex_tail_le (B : ℕ) (hB : B ≠ 0) : ∀ x : ℕ, 2 ≤ x →
    (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B)
      ≤ ∑' v : ℕ, powerfulWeight v := by
  intro x hx
  have hHS := hasSum_indicator_U x B hB
  have hsub : HasSum (fun nn : ↥(unionDom x B) => ((nn : ℕ) : ℝ)⁻¹)
      (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B) :=
    hasSum_subtype_iff_indicator.mpr hHS
  have hinj : Function.Injective (fun nn : ↥(unionDom x B) => decMap (nn : ℕ)) := by
    rintro ⟨n, hn⟩ ⟨m, hm⟩ hnm
    simp only [decMap, Prod.mk.injEq] at hnm
    apply Subtype.ext
    change n = m
    calc n = sqfPart n * powPart n := (sqfPart_mul_powPart hn.2.1).symm
      _ = sqfPart m * powPart m := by rw [hnm.2, hnm.1]
      _ = m := sqfPart_mul_powPart hm.2.1
  have hval : ∀ nn : ↥(unionDom x B), ((nn : ℕ) : ℝ)⁻¹ = windowWeight x (decMap (nn : ℕ)) := by
    rintro ⟨n, hrad, hn0, hxn⟩
    have hrad_lt : rad n < x := by
      rw [Salt.Maynard.sqfCop, Finset.mem_filter, Finset.mem_range] at hrad
      exact hrad.1
    have hcond : IsPowerful (powPart n) ∧ powPart n ≠ 0 ∧ 0 < sqfPart n ∧
        sqfPart n * rad (powPart n) < x ∧ x ≤ sqfPart n * powPart n := by
      refine ⟨powPart_isPowerful n, (powPart_pos n).ne', sqfPart_pos n, ?_, ?_⟩
      · rw [← rad_eq_sqfPart_mul_rad_powPart hn0]; exact hrad_lt
      · rw [sqfPart_mul_powPart hn0]; exact hxn
    change ((n : ℝ))⁻¹ = windowWeight x (decMap n)
    rw [decMap, windowWeight_of x (powPart n) (sqfPart n) hcond, sqfPart_mul_powPart hn0]
  calc (∑ r ∈ Salt.Maynard.sqfCop x B, radFiberTail r x B)
      = ∑' nn : ↥(unionDom x B), ((nn : ℕ) : ℝ)⁻¹ := hsub.tsum_eq.symm
    _ = ∑' nn : ↥(unionDom x B), windowWeight x (decMap (nn : ℕ)) := tsum_congr hval
    _ ≤ ∑' p : ℕ × ℕ, windowWeight x p :=
        tsum_comp_le_tsum_of_inj (summable_windowWeight x hx)
          (fun p => windowWeight_nonneg x p) hinj
    _ ≤ ∑' v : ℕ, powerfulWeight v := windowWeight_tsum_le x hx

theorem phiUpperAtom_final (B : ℕ) (hB : B ≠ 0) : Salt.Twelve.PhiUpperAtom B :=
  phiUpperAtom_holds B hB (reindex_tail_le B hB)

end Salt.Twelve
