/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Crush

/-!
# T-BAL R5c — the crush's first inequality (`selHSum_ge_dhA_div_sum`)

The radical-fiber / box-domination step of the crush: `Σ_{n≤z} dhA(n)·n^{−1} ≤ H(z)`.

The map `n ↦ rad(n) = ∏_{p∣n} p` sends `[1,z]` into the squarefree `r ≤ z`, so the sum
partitions into fibers (`Finset.sum_fiberwise_of_maps_to`). On the fiber `rad(n)=r`, the
multiplicative summand `g̃(n) = dhA(n)·n^{−1}` factors as `∏_{p∣r} dhA(p^{e_p})·p^{−e_p}`,
and the exponent vector `(e_p) = (n.factorization p)` injects into the box
`r.primeFactors.pi (fun _ => Icc 1 z)` (each `e_p ∈ [1,z]`). Nonnegativity + `Finset.prod_sum`
turn the box sum into `∏_{p∣r} Σ_{e≤z} dhA(p^e)·p^{−e}`, and the per-prime floor R5b
(`selG_ge_partial_geom`) bounds each factor by `selG χ p`, giving `∏_{p∣r} selG χ p = selGmul χ r`.

NUMERIC TRUTH (verified): at `z=20`, `q=3` (Legendre χ mod 3),
`selHSum χ 20 ≈ 2.857 ≥ Σ_{n≤20} dhA(n)/n ≈ 2.385`. True and not tight.
-/

namespace Salt.SW

open Finset

/-- **The fiber bound (crux of R5c).** For any `r`, summing the multiplicative term
`dhA(n)·n^{−1}` over the radical fiber `{n ≤ z : rad(n) = r}` is dominated by `selGmul χ r`.
The fiber's exponent vectors inject into the box `Icc 1 z` per prime of `r`; `Finset.prod_sum`
and the per-prime floor `selG_ge_partial_geom` (R5b) close it. -/
private lemma crush_fiber_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (z r : ℕ) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => (∏ p ∈ n.primeFactors, p) = r),
        dhA χ n * (n : ℝ) ^ (-(1 : ℝ))
      ≤ selGmul χ r := by
  classical
  set P := r.primeFactors with hPdef
  set Sr := (Finset.Icc 1 z).filter (fun n => (∏ p ∈ n.primeFactors, p) = r) with hSr
  -- membership unpacking
  have hmemP : ∀ n ∈ Sr, n.primeFactors = P := by
    intro n hn
    simp only [hSr, Finset.mem_filter, Finset.mem_Icc] at hn
    have hprimes : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    calc n.primeFactors = (∏ p ∈ n.primeFactors, p).primeFactors :=
          (Nat.primeFactors_prod hprimes).symm
      _ = r.primeFactors := by rw [hn.2]
      _ = P := hPdef.symm
  have hne : ∀ n ∈ Sr, n ≠ 0 := by
    intro n hn; simp only [hSr, Finset.mem_filter, Finset.mem_Icc] at hn; omega
  have hle : ∀ n ∈ Sr, n ≤ z := by
    intro n hn; simp only [hSr, Finset.mem_filter, Finset.mem_Icc] at hn; exact hn.1.2
  -- the two-factor per-prime term is nonnegative
  have hnn : ∀ p ∈ P, ∀ e : ℕ, 0 ≤ dhA χ (p ^ e) * (p : ℝ) ^ (-(e : ℝ)) := by
    intro p hp e
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hPdef ▸ hp)
    exact mul_nonneg (dhA_nonneg χ hsq (pow_ne_zero e hpp.pos.ne'))
      (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  -- (a) the multiplicative summand identity on the fiber
  have ha : ∀ n ∈ Sr, dhA χ n * (n : ℝ) ^ (-(1 : ℝ))
      = ∏ p ∈ P, dhA χ (p ^ n.factorization p) * (p : ℝ) ^ (-(n.factorization p : ℝ)) := by
    intro n hn
    have hn0 : n ≠ 0 := hne n hn
    have hP : n.primeFactors = P := hmemP n hn
    have ha1 : dhA χ n = ∏ p ∈ P, dhA χ (p ^ n.factorization p) := by
      rw [← dhAArith_apply χ n,
        (dhAArith_mult χ hsq).multiplicative_factorization (dhAArith χ) hn0, Finsupp.prod,
        Nat.support_factorization, hP]
      exact Finset.prod_congr rfl (fun p _ => dhAArith_apply χ _)
    have hnat : n = ∏ p ∈ P, p ^ n.factorization p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization, hP]
    have haR : (n : ℝ) = ∏ p ∈ P, (p : ℝ) ^ n.factorization p := by
      conv_lhs => rw [hnat]
      rw [Nat.cast_prod]; exact Finset.prod_congr rfl (fun p _ => Nat.cast_pow p _)
    have ha2 : (n : ℝ) ^ (-(1 : ℝ)) = ∏ p ∈ P, (p : ℝ) ^ (-(n.factorization p : ℝ)) := by
      rw [Real.rpow_neg_one, haR, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_natCast]
    rw [ha1, ha2, ← Finset.prod_mul_distrib]
  -- the exponent-vector map into the box
  let φ : ℕ → ((p : ℕ) → p ∈ P → ℕ) := fun n p _ => n.factorization p
  -- (b) φ maps the fiber into the box
  have hbox : ∀ n ∈ Sr, φ n ∈ P.pi (fun _ => Finset.Icc 1 z) := by
    intro n hn
    rw [Finset.mem_pi]
    intro p hp
    have hpn : p ∈ n.primeFactors := (hmemP n hn) ▸ hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpn
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpn
    have hn0 : n ≠ 0 := hne n hn
    have hlt : n.factorization p < n := Nat.factorization_lt p hn0
    have hnz : n ≤ z := hle n hn
    rw [Finset.mem_Icc]
    refine ⟨hpp.factorization_pos_of_dvd hn0 hdvd, ?_⟩
    change n.factorization p ≤ z
    omega
  -- (c) φ is injective on the fiber
  have hinj : Set.InjOn φ ↑Sr := by
    intro a ha' b hb' hab
    have hPa : a.primeFactors = P := hmemP a (Finset.mem_coe.mp ha')
    have hPb : b.primeFactors = P := hmemP b (Finset.mem_coe.mp hb')
    refine Nat.eq_of_factorization_eq (hne a (Finset.mem_coe.mp ha'))
      (hne b (Finset.mem_coe.mp hb')) (fun p => ?_)
    by_cases hp : p ∈ P
    · exact congrFun (congrFun hab p) hp
    · have h0a : a.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rw [Nat.support_factorization, hPa]; exact hp)
      have h0b : b.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rw [Nat.support_factorization, hPb]; exact hp)
      rw [h0a, h0b]
  -- assemble
  have E1 : ∑ n ∈ Sr, dhA χ n * (n : ℝ) ^ (-(1 : ℝ))
      = ∑ n ∈ Sr, ∏ x ∈ P.attach,
          dhA χ (x.1 ^ φ n x.1 x.2) * (x.1 : ℝ) ^ (-(φ n x.1 x.2 : ℝ)) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [ha n hn]
    exact (Finset.prod_attach P
      (fun p => dhA χ (p ^ n.factorization p) * (p : ℝ) ^ (-(n.factorization p : ℝ)))).symm
  have E2 : ∑ n ∈ Sr, ∏ x ∈ P.attach,
          dhA χ (x.1 ^ φ n x.1 x.2) * (x.1 : ℝ) ^ (-(φ n x.1 x.2 : ℝ))
      = ∑ f ∈ Sr.image φ, ∏ x ∈ P.attach,
          dhA χ (x.1 ^ f x.1 x.2) * (x.1 : ℝ) ^ (-(f x.1 x.2 : ℝ)) := by
    rw [Finset.sum_image hinj]
  have E3 : ∑ f ∈ Sr.image φ, ∏ x ∈ P.attach,
          dhA χ (x.1 ^ f x.1 x.2) * (x.1 : ℝ) ^ (-(f x.1 x.2 : ℝ))
      ≤ ∑ f ∈ P.pi (fun _ => Finset.Icc 1 z), ∏ x ∈ P.attach,
          dhA χ (x.1 ^ f x.1 x.2) * (x.1 : ℝ) ^ (-(f x.1 x.2 : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun f _ _ => ?_)
    · rw [Finset.image_subset_iff]; exact hbox
    · exact Finset.prod_nonneg (fun x _ => hnn x.1 x.2 _)
  have E4 : ∑ f ∈ P.pi (fun _ => Finset.Icc 1 z), ∏ x ∈ P.attach,
          dhA χ (x.1 ^ f x.1 x.2) * (x.1 : ℝ) ^ (-(f x.1 x.2 : ℝ))
      = ∏ p ∈ P, ∑ e ∈ Finset.Icc 1 z, dhA χ (p ^ e) * (p : ℝ) ^ (-(e : ℝ)) :=
    (Finset.prod_sum P (fun _ => Finset.Icc 1 z)
      (fun p e => dhA χ (p ^ e) * (p : ℝ) ^ (-(e : ℝ)))).symm
  have E5 : ∏ p ∈ P, ∑ e ∈ Finset.Icc 1 z, dhA χ (p ^ e) * (p : ℝ) ^ (-(e : ℝ))
      ≤ ∏ p ∈ P, selG χ p := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · exact Finset.sum_nonneg (fun e _ => hnn p hp e)
    · exact selG_ge_partial_geom χ hsq (Nat.prime_of_mem_primeFactors (hPdef ▸ hp)) z
  have E6 : ∏ p ∈ P, selG χ p = selGmul χ r := by rw [selGmul, ← hPdef]
  rw [E1, E2]
  exact le_trans E3 (le_trans (le_of_eq E4) (le_trans E5 (le_of_eq E6)))

/-- **R5c (`selHSum_ge_dhA_div_sum`).** The crush's first inequality:
`Σ_{n≤z} dhA(n)·n^{−1} ≤ H(z) = selHSum χ z`. The radical map `n ↦ ∏_{p∣n} p` sends `[1,z]`
into the squarefree `r ≤ z`, so `Finset.sum_fiberwise_of_maps_to` partitions the sum into
fibers, each bounded by `selGmul χ r` via `crush_fiber_le`. -/
theorem selHSum_ge_dhA_div_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (z : ℕ) :
    ∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-(1 : ℝ)) ≤ selHSum χ z := by
  classical
  have hmaps : ∀ n ∈ Finset.Icc 1 z, (∏ p ∈ n.primeFactors, p)
      ∈ (Finset.Icc 1 z).filter Squarefree := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hdvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
    have h1 : 1 ≤ ∏ p ∈ n.primeFactors, p :=
      Finset.one_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    refine ⟨⟨h1, le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, ?_⟩
    rw [← Nat.radical_eq_prod_primeFactors]
    exact UniqueFactorizationMonoid.squarefree_radical
  rw [selHSum, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => dhA χ n * (n : ℝ) ^ (-(1 : ℝ)))]
  exact Finset.sum_le_sum (fun r _ => crush_fiber_le χ hsq z r)

end Salt.SW
