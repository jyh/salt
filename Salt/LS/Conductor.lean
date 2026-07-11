/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.LS.PsiDefs

/-!
# L8.1 — conductor descent (BDH toolkit)

Design: `docs/blueprints/largesieve.md`, node L8.1. The toolkit that node L8.4
(Barban–Davenport–Halberstam) consumes to pass from sums over **all** Dirichlet
characters `χ mod q` to sums over **primitive** characters `χ⋆ mod f` where
`f = conductor χ ∣ q`, tracking the `q/φ(q)` bookkeeping. Three pieces:

1. **Descent structure** (`conductor_dvd`, `primitiveCharacter_apply_of_isUnit`):
   for `χ : DirichletCharacter ℂ q`, the associated primitive character
   `χ⋆ = χ.primitiveCharacter` at level `f = conductor χ` divides the level and
   agrees with `χ` on residues coprime to `q`. Pure mathlib API.

2. **The ψ-difference crude bound** (`norm_psiChi_sub_primitiveCharacter_le`):
   `‖ψ(x, χ) − ψ(x, χ⋆)‖ ≤ ω(q) · log x` for `1 ≤ x`, where `ω(q) =
   q.primeFactors.card`. The two ψ's differ only on `n` not coprime to `q`; on
   those the von Mangoldt weight lives on prime powers `p^k` with `p ∣ q`, and
   each prime contributes `⌊log_p x⌋·log p ≤ log x` (a fiber count). The
   character values have norm `≤ 1` (`DirichletCharacter.norm_le_one`), so the
   difference is bounded by the von Mangoldt mass of those prime powers. The
   crude corollary `ω(q) ≤ logb 2 q` (`primeFactors_card_le_logb`, via
   `2^ω(q) ≤ ∏_{p∣q} p ∣ q`) turns this into a `(log q)(log x)` bound.

3. **The φ double-counting sum** (`sum_inv_totient_dvd_le`): reindexing
   `q = f·m` with totient super-multiplicativity `φ(f)·φ(m) ≤ φ(f·m)`, the
   level sum `∑_{q ∈ Icc 1 Q, f ∣ q} 1/φ(q)` is controlled by
   `(1/φ(f)) · ∑_{m ∈ Icc 1 Q} 1/φ(m)`. See the node card for the status of the
   standalone `∑ 1/φ ≤ C(1+log Q)` factor.

Integrability / measurability: none — everything is a finite `Finset` sum.

Constants are loose and explicit throughout (track doctrine).
-/

open ArithmeticFunction Finset

namespace Salt.LS

/-! ## 1. Conductor descent structure -/

/-- The conductor of a Dirichlet character divides its level. -/
lemma conductor_dvd {q : ℕ} (χ : DirichletCharacter ℂ q) : χ.conductor ∣ q :=
  χ.conductor_dvd_level

/-- **Agreement on the coprime part.** For a residue `n` coprime to the level
`q` (i.e. `IsUnit (n : ZMod q)`), the primitive character `χ⋆ = χ.primitiveCharacter`
at level `conductor χ` agrees with `χ`. -/
lemma primitiveCharacter_apply_of_isUnit {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hn : IsUnit (n : ZMod q)) :
    χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod q) := by
  have hco : IsCoprime (n : ℤ) (q : ℤ) := by
    have hu : IsUnit ((n : ℤ) : ZMod q) := by rwa [Int.cast_natCast]
    rw [ZMod.coe_int_isUnit_iff_isCoprime] at hu
    exact hu.symm
  have h := χ.primitiveCharacter_apply_of_isCoprime hco
  rwa [Int.cast_natCast, Int.cast_natCast] at h

/-! ## 2. The ψ-difference crude bound -/

/-- **Prime-power fiber bound.** For a fixed prime `p` and `1 ≤ x`, any finite
set of prime powers `p^k ≤ x` carries von Mangoldt mass at most `log x`
(each term is `log p`, and there are at most `⌊log_p x⌋` of them). -/
lemma vonMangoldt_primePow_fiber_le {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ≤ x ∧ IsPrimePow n ∧ n.minFac = p) :
    ∑ n ∈ S, vonMangoldt n ≤ Real.log x := by
  classical
  set K := Nat.log p x with hKdef
  have hp1 : 1 < p := hp.one_lt
  have hx0 : x ≠ 0 := by omega
  -- every element of `S` is `p ^ k` with `1 ≤ k ≤ K`
  have hsub : S ⊆ (Finset.Icc 1 K).image (fun k => p ^ k) := by
    intro n hn
    obtain ⟨hnx, hpp, hmf⟩ := hS n hn
    have hdecomp : p ^ n.factorization p = n := by
      have h := hpp.minFac_pow_factorization_eq
      rwa [hmf] at h
    have hn0 : n ≠ 0 := hpp.pos.ne'
    have hpdvd : p ∣ n := hmf ▸ Nat.minFac_dvd n
    have hkpos : 1 ≤ n.factorization p := hp.factorization_pos_of_dvd hn0 hpdvd
    have hkle : n.factorization p ≤ K := by
      rw [hKdef, Nat.le_log_iff_pow_le hp1 hx0, hdecomp]
      exact hnx
    rw [Finset.mem_image]
    exact ⟨n.factorization p, Finset.mem_Icc.mpr ⟨hkpos, hkle⟩, hdecomp⟩
  calc ∑ n ∈ S, vonMangoldt n
      ≤ ∑ n ∈ (Finset.Icc 1 K).image (fun k => p ^ k), vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => vonMangoldt_nonneg)
    _ = ∑ k ∈ Finset.Icc 1 K, vonMangoldt (p ^ k) := by
        rw [Finset.sum_image (fun a _ b _ hab => Nat.pow_right_injective hp.two_le hab)]
    _ = ∑ _k ∈ Finset.Icc 1 K, Real.log p := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk0 : k ≠ 0 := by rw [Finset.mem_Icc] at hk; omega
        rw [vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hp]
    _ = (K : ℝ) * Real.log p := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ Real.log x := by
        rw [← Real.log_pow]
        apply Real.log_le_log (by positivity)
        calc ((p : ℝ) ^ K) = ((p ^ K : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (x : ℝ) := by exact_mod_cast Nat.pow_log_le_self p hx0

/-- **The ψ-difference crude bound.** The character-twisted Chebyshev function
of `χ mod q` and of its primitive character `χ⋆ mod conductor χ` differ by at
most `ω(q)·log x`, where `ω(q) = q.primeFactors.card`. -/
lemma norm_psiChi_sub_primitiveCharacter_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℕ} (hx : 1 ≤ x) :
    ‖psiChi x χ - psiChi x χ.primitiveCharacter‖
      ≤ (q.primeFactors.card : ℝ) * Real.log x := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  -- Step 1: the difference as one sum over `Icc 1 x`
  have hdiff : psiChi x χ - psiChi x χ.primitiveCharacter
      = ∑ n ∈ Finset.Icc 1 x,
          (vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)) := by
    unfold psiChi
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [hdiff]
  -- Step 2: triangle inequality, then a pointwise bound to `¬IsUnit` von Mangoldt mass
  refine (norm_sum_le _ _).trans ?_
  have step1 : ∑ n ∈ Finset.Icc 1 x,
        ‖(vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor))‖
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)), vonMangoldt n := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun n _ => ?_)
    by_cases hu : IsUnit (n : ZMod q)
    · rw [if_neg (not_not.mpr hu), primitiveCharacter_apply_of_isUnit χ hu, sub_self, mul_zero,
        norm_zero]
    · rw [if_pos hu, norm_mul]
      have hLnorm : ‖(vonMangoldt n : ℂ)‖ = vonMangoldt n := by
        rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      rw [hLnorm]
      have hcn : ‖χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ 1 := by
        rw [χ.map_nonunit hu, zero_sub, norm_neg]
        exact χ.primitiveCharacter.norm_le_one _
      calc vonMangoldt n * ‖χ (n : ZMod q) - χ.primitiveCharacter (n : ZMod χ.conductor)‖
          ≤ vonMangoldt n * 1 := mul_le_mul_of_nonneg_left hcn vonMangoldt_nonneg
        _ = vonMangoldt n := mul_one _
  refine step1.trans ?_
  -- Step 3: drop the non-prime-powers, then fiber over the prime factors of `q`
  set S' := (Finset.Icc 1 x).filter (fun n : ℕ => ¬ IsUnit (n : ZMod q) ∧ IsPrimePow n) with hS'def
  have hdrop : ∑ n ∈ (Finset.Icc 1 x).filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)), vonMangoldt n
      = ∑ n ∈ S', vonMangoldt n := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      rw [hS'def, Finset.mem_filter] at hn
      rw [Finset.mem_filter]
      exact ⟨hn.1, hn.2.1⟩
    · intro n hn hn'
      rw [Finset.mem_filter] at hn
      rw [hS'def, Finset.mem_filter] at hn'
      rw [vonMangoldt_eq_zero_iff]
      exact fun hpp => hn' ⟨hn.1, hn.2, hpp⟩
  rw [hdrop]
  -- the minimal-prime map sends `S'` into `q.primeFactors`
  have hmaps : ∀ n ∈ S', n.minFac ∈ q.primeFactors := by
    intro n hn
    rw [hS'def, Finset.mem_filter] at hn
    obtain ⟨_, hnu, hpp⟩ := hn
    have hp : (n.minFac).Prime := Nat.minFac_prime hpp.ne_one
    have hpdvdq : n.minFac ∣ q := by
      by_contra hnd
      have hcop_p : Nat.Coprime (n.minFac) q := (hp.coprime_iff_not_dvd).mpr hnd
      have hdecomp : (n.minFac) ^ n.factorization (n.minFac) = n := hpp.minFac_pow_factorization_eq
      have hcop_n : Nat.Coprime n q := by rw [← hdecomp]; exact hcop_p.pow_left _
      exact hnu ((ZMod.isUnit_iff_coprime n q).mpr hcop_n)
    exact (Nat.mem_primeFactors_of_ne_zero hq0).mpr ⟨hp, hpdvdq⟩
  calc ∑ n ∈ S', vonMangoldt n
      = ∑ p ∈ q.primeFactors, ∑ n ∈ S'.filter (fun n => n.minFac = p), vonMangoldt n :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log x := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        refine vonMangoldt_primePow_fiber_le (Nat.prime_of_mem_primeFactors hp) hx _ ?_
        intro n hn
        rw [Finset.mem_filter, hS'def, Finset.mem_filter, Finset.mem_Icc] at hn
        exact ⟨hn.1.1.2, hn.1.2.2, hn.2⟩
    _ = (q.primeFactors.card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Crude `ω(q) ≤ logb 2 q`.** Since `2^ω(q) = ∏_{p∣q} 2 ≤ ∏_{p∣q} p ∣ q`,
the number of prime factors is at most `log q / log 2`. -/
lemma primeFactors_card_le_logb {q : ℕ} (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.logb 2 q := by
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card
        = ∏ _p ∈ q.primeFactors, 2 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.prod_le_prod (fun _ _ => by norm_num)
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have h2q : ((2 : ℝ)) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hpow
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, le_div_iff₀ hlog2]
  calc (q.primeFactors.card : ℝ) * Real.log 2
      = Real.log ((2 : ℝ) ^ q.primeFactors.card) := by rw [Real.log_pow]
    _ ≤ Real.log q := Real.log_le_log (by positivity) h2q

/-- **ψ-difference bound, `log q` form.** Combining the two bounds above. -/
lemma norm_psiChi_sub_primitiveCharacter_le_logb {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℕ} (hx : 1 ≤ x) :
    ‖psiChi x χ - psiChi x χ.primitiveCharacter‖
      ≤ Real.logb 2 q * Real.log x := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine (norm_psiChi_sub_primitiveCharacter_le χ hx).trans ?_
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  exact mul_le_mul_of_nonneg_right (primeFactors_card_le_logb hq) hlogx

/-! ## 3. The φ double-counting sum -/

/-- **Reduction of the level sum by super-multiplicativity.** Reindexing
`q = f·m` over the divisors `f ∣ q` in `Icc 1 Q` and using
`φ(f)·φ(m) ≤ φ(f·m)` (`Nat.totient_super_multiplicative`) reduces the level
sum to `(1/φ(f))` times the plain reciprocal-totient sum over `Icc 1 Q`. -/
lemma sum_inv_totient_dvd_le_mul {f Q : ℕ} (hf : 1 ≤ f) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => f ∣ q), (1 / (Nat.totient q : ℝ))
      ≤ (1 / (Nat.totient f : ℝ)) * ∑ m ∈ Finset.Icc 1 Q, (1 / (Nat.totient m : ℝ)) := by
  have hf0 : 0 < f := hf
  -- reindex the divisibility-filtered sum as the image of `Icc 1 (Q/f)` under `f · ·`
  have hset : (Finset.Icc 1 Q).filter (fun q => f ∣ q)
      = (Finset.Icc 1 (Q / f)).image (fun m => f * m) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hq1, hqQ⟩, m, rfl⟩
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hq1
        · exact h
      refine ⟨m, ⟨hm1, ?_⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le hf0, Nat.mul_comm]
      exact hqQ
    · rintro ⟨m, ⟨hm1, hmQ⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le hf0] at hmQ
      refine ⟨⟨Nat.mul_pos hf0 hm1, ?_⟩, ⟨m, rfl⟩⟩
      rw [Nat.mul_comm]
      exact hmQ
  rw [hset, Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hf0 hab)]
  calc ∑ m ∈ Finset.Icc 1 (Q / f), (1 / (Nat.totient (f * m) : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 (Q / f),
          (1 / (Nat.totient f : ℝ)) * (1 / (Nat.totient m : ℝ)) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        rw [Finset.mem_Icc] at hm
        rw [div_mul_div_comm, one_mul]
        refine one_div_le_one_div_of_le ?_ ?_
        · have h1 : 0 < Nat.totient f := Nat.totient_pos.mpr hf0
          have h2 : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
          positivity
        · exact_mod_cast Nat.totient_super_multiplicative f m
    _ = (1 / (Nat.totient f : ℝ)) * ∑ m ∈ Finset.Icc 1 (Q / f), (1 / (Nat.totient m : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (Nat.totient f : ℝ)) * ∑ m ∈ Finset.Icc 1 Q, (1 / (Nat.totient m : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (Nat.div_le_self Q f)) (fun i _ _ => by positivity)

/-- **The φ double-counting bound.** With the classical harmonic-type bound
`∑_{m ∈ Icc 1 Q} 1/φ(m) ≤ C·(1 + log Q)` supplied as `hphi`, the divisibility
level sum obeys `∑_{q ∈ Icc 1 Q, f ∣ q} 1/φ(q) ≤ (C/φ(f))·(1 + log Q)`.

The `hphi` factor is the one genuinely analytic ingredient (see the node card
and `docs/blueprints/flags.md` for the intended standalone proof route via the
divisor swap `1/φ(m) = ∑_{de = m} μ²(d)/(d·e·φ(d))` and reuse of
`Salt.Maynard.PhiAtom.sum_inv_mul_totient_le`). -/
theorem sum_inv_totient_dvd_le {f Q : ℕ} (hf : 1 ≤ f) {C : ℝ}
    (hphi : ∑ m ∈ Finset.Icc 1 Q, (1 / (Nat.totient m : ℝ)) ≤ C * (1 + Real.log Q)) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => f ∣ q), (1 / (Nat.totient q : ℝ))
      ≤ (C / (Nat.totient f : ℝ)) * (1 + Real.log Q) := by
  refine (sum_inv_totient_dvd_le_mul hf).trans ?_
  have hφf : (0 : ℝ) < (Nat.totient f : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hf
  calc (1 / (Nat.totient f : ℝ)) * ∑ m ∈ Finset.Icc 1 Q, (1 / (Nat.totient m : ℝ))
      ≤ (1 / (Nat.totient f : ℝ)) * (C * (1 + Real.log Q)) :=
        mul_le_mul_of_nonneg_left hphi (by positivity)
    _ = (C / (Nat.totient f : ℝ)) * (1 + Real.log Q) := by ring

end Salt.LS
