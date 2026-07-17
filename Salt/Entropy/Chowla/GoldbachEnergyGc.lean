/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# GB-6c — the coprime-restriction denominator bound (the house re-freeze)

The GB-6 comparison route costs `sCorr n = 2^{ω_odd(n)}·∏(p−1)/(p−2)`, whose
square-sum `Σ 4^{ω(n)}` is polylog-too-large for `hsq`.  The house re-freeze
(`docs/exploration/s3-a3-design.md`, "Night-shift adjudications", the GB-6
resolution) replaces the per-`ℓ` majorant by a *coprime restriction*: on `ℓ`
coprime to `n`, the gold Selberg term equals `gTwin ℓ` EXACTLY (every `p ∣ ℓ`
has `p ∤ n`), and the unique `d·m` factorization (`d = gcd(ℓ,n)` supported on
`n`'s primes, `m` coprime to `n`) gives

  `Σ_{ℓ≤z} gTwin ℓ ≤ sTrunc2 n · Σ_{m≤z,(m,n)=1} gTwin m`

with `hFac2 d = ∏_{p∣d} 2/(p−2)` and `sTrunc2 n = Σ_{d∣n,sqfree,odd} hFac2 d`.
The twin engine's `mainTermSum ≥ c₀·log²z` then transfers to
`c₀·log²z / sTrunc2 n ≤ Σ_{ℓ≤z} gold(ℓ)` (the coprime carrier sum equals the
`gTwin` sum; the full carrier sum dominates it, terms `≥ 0`).

Key observation: `gTwin` (defined in `Salt/Brun/M3Expansion.lean` as
`∏_{p∣ℓ} 2/(p−2)`) is DEFINITIONALLY the frozen `hFac2` — so `hFac2 = gTwin`
collapses the coprime-exactness identity.

* `sTrunc2_pos` / `hFac2_nonneg` — the majorant API.
* `mainTermSum_le_sTrunc2_mul_coprimeSum` — the `d·m` factorization
  (`Finset.image`/`×ˢ`-product reindex; the injection `ℓ ↦ (gcd ℓ n, ℓ/gcd)`).
* `goldCarrierSum_ge_log_sq_div_sTrunc2` — the denominator bound.
* `goldSelbergBoundingSum_ge_log_sq_div_sTrunc2` — the GB-7 seam (composed with
  GB-6's `carrierSum_le_selbergBoundingSum` verbatim).

No `sorry`, no `native_decide`, no new axioms.
-/
import Mathlib
import Salt.Entropy.Chowla.GoldbachEnergyG
import Salt.Entropy.Chowla.GoldbachEnergyHsq
import Salt.Brun.M3Expansion

open ArithmeticFunction Finset

namespace Salt.Entropy.Chowla

variable {n P : ℕ} {hn : 2 ∣ n} {hP : Squarefree P}

/-! ## The doubled singular-series majorant `hFac2` / `sTrunc2` -/

/-- The per-prime weight `hFac2 d = ∏_{p ∣ d} 2/(p−2)`.  For odd squarefree `d`
every prime factor `p ≥ 3`.  Definitionally equal to `gTwin d`. -/
noncomputable def hFac2 (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, (2 : ℝ) / ((p : ℝ) - 2)

/-- The doubled truncated singular-series majorant: the sum of `hFac2 d` over the
odd squarefree divisors of `n`.  `= ∏_{p ∣ n, odd} (1 + 2/(p−2))`. -/
noncomputable def sTrunc2 (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => Squarefree d ∧ Odd d), hFac2 d

/-- `hFac2` is definitionally `gTwin`. -/
lemma hFac2_eq_gTwin (d : ℕ) : hFac2 d = Salt.M3Expansion.gTwin d := rfl

/-- `hFac2 d ≥ 0` for odd `d` (each factor `2/(p−2) ≥ 0` for `p ≥ 3`). -/
theorem hFac2_nonneg {d : ℕ} (hd : Odd d) : 0 ≤ hFac2 d := by
  rw [hFac2]
  apply Finset.prod_nonneg
  intro p hp
  have h3 := three_le_of_odd_primeFactor hd hp
  have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  apply div_nonneg (by norm_num)
  linarith

/-- `gTwin d ≥ 0` for odd `d`. -/
lemma gTwin_nonneg_of_odd {d : ℕ} (hd : Odd d) : 0 ≤ Salt.M3Expansion.gTwin d := by
  rw [← hFac2_eq_gTwin]; exact hFac2_nonneg hd

/-- `sTrunc2 n ≥ 0`. -/
theorem sTrunc2_nonneg (n : ℕ) : 0 ≤ sTrunc2 n := by
  apply Finset.sum_nonneg
  intro d hd
  exact hFac2_nonneg (Finset.mem_filter.mp hd).2.2

/-- `sTrunc2 n > 0` for `n ≠ 0` (the `d = 1` term is `hFac2 1 = 1`). -/
theorem sTrunc2_pos (hn0 : n ≠ 0) : 0 < sTrunc2 n := by
  have h1mem : (1 : ℕ) ∈ n.divisors.filter (fun d => Squarefree d ∧ Odd d) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd n, hn0⟩, squarefree_one, odd_one⟩
  have hle : hFac2 1 ≤ sTrunc2 n :=
    Finset.single_le_sum (fun d hd => hFac2_nonneg (Finset.mem_filter.mp hd).2.2) h1mem
  have h1 : hFac2 1 = 1 := by rw [hFac2, Nat.primeFactors_one, Finset.prod_empty]
  rw [h1] at hle; linarith

/-! ## `gTwin` multiplicativity and divisor-parity helpers -/

/-- Multiplicativity of `gTwin` over coprime factors. -/
lemma gTwin_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.Coprime a b) :
    Salt.M3Expansion.gTwin (a * b)
      = Salt.M3Expansion.gTwin a * Salt.M3Expansion.gTwin b := by
  rw [Salt.M3Expansion.gTwin, Salt.M3Expansion.gTwin, Salt.M3Expansion.gTwin,
    Nat.primeFactors_mul ha hb, Finset.prod_union h.disjoint_primeFactors]

/-- A divisor of an odd number is odd. -/
lemma odd_of_dvd_odd {a b : ℕ} (hb : Odd b) (hab : a ∣ b) : Odd a := by
  rw [Nat.odd_iff] at hb ⊢
  by_contra h
  have h2a : 2 ∣ a := by omega
  have h2b : 2 ∣ b := h2a.trans hab
  omega

/-! ## Step 1 — coprime exactness and odd-squarefree nonnegativity -/

/-- The gold Selberg term of an odd squarefree `ℓ` is `≥ 0` (each prime factor
`p ≥ 3` contributes a nonnegative per-prime term). -/
lemma goldSelbergTerms_nonneg_of_odd {ℓ : ℕ} (hℓodd : Odd ℓ) (hℓsq : Squarefree ℓ) :
    0 ≤ (goldEnergySieve n P hn hP).selbergTerms ℓ := by
  rw [← (goldEnergySieve n P hn hP).selbergTerms_isMultiplicative.prod_primeFactors hℓsq]
  apply Finset.prod_nonneg
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h3 := three_le_of_odd_primeFactor hℓodd hp
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  by_cases hpn : p ∣ n
  · rw [goldSelbergTerms_prime_dvd p hpp hpn]; apply div_nonneg (by norm_num); linarith
  · rw [goldSelbergTerms_prime_not_dvd p hpp hpn]; apply div_nonneg (by norm_num); linarith

/-- **Coprime exactness.**  For `m` odd, squarefree, and coprime to `n`, every
prime `p ∣ m` has `p ∤ n`, so `selbergTerms p = 2/(p−2)` matches `gTwin`'s
per-prime factor; by multiplicativity `selbergTerms m = gTwin m`. -/
lemma selbergTerms_eq_gTwin_of_coprime (m : ℕ) (_hmodd : Odd m) (hmsq : Squarefree m)
    (hmn : Nat.Coprime m n) :
    (goldEnergySieve n P hn hP).selbergTerms m = Salt.M3Expansion.gTwin m := by
  rw [← (goldEnergySieve n P hn hP).selbergTerms_isMultiplicative.prod_primeFactors hmsq,
    Salt.M3Expansion.gTwin]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpm := Nat.dvd_of_mem_primeFactors hp
  have hpn : ¬ p ∣ n := (hpp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_left hpm hmn)
  rw [goldSelbergTerms_prime_not_dvd p hpp hpn]

/-! ## Step 2 — the `d·m` factorization -/

/-- **The `d·m` factorization.**  Every odd squarefree `ℓ ≤ z` factors uniquely
as `ℓ = d·m` with `d = gcd(ℓ,n)` (supported on `n`'s primes, hence `d ∣ n` odd
squarefree) and `m = ℓ/d` (coprime to `n`, odd squarefree, `< z`).  Since `gTwin`
is multiplicative and `d,m` coprime, `gTwin ℓ = gTwin d · gTwin m`; the injection
`ℓ ↦ (d,m)` lands in `Dn ×ˢ Fcop` (terms `≥ 0`), so the twin main-term sum is at
most `(Σ_d gTwin d)·(Σ_m gTwin m) = sTrunc2 n · Σ_{(m,n)=1} gTwin m`. -/
lemma mainTermSum_le_sTrunc2_mul_coprimeSum (z : ℕ) (hn0 : n ≠ 0) :
    Salt.M3Assembly.mainTermSum z
      ≤ sTrunc2 n * ∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
          (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m := by
  classical
  set F := (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) with hF
  set Dn := n.divisors.filter (fun d => Squarefree d ∧ Odd d) with hDn
  set Fcop := F.filter (fun m => Nat.Coprime m n) with hFcop
  set φ : ℕ → ℕ × ℕ := fun ℓ => (Nat.gcd ℓ n, ℓ / Nat.gcd ℓ n) with hφ
  set g : ℕ × ℕ → ℝ :=
    fun q => Salt.M3Expansion.gTwin q.1 * Salt.M3Expansion.gTwin q.2 with hg
  -- (A) per-`ℓ` multiplicative split `gTwin ℓ = g (φ ℓ)`
  have hcongr : ∀ ℓ ∈ F, Salt.M3Expansion.gTwin ℓ = g (φ ℓ) := by
    intro ℓ hℓ
    rw [hF, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨_, hℓodd, hℓsq⟩ := hℓ
    have hℓpos : 0 < ℓ := by have := Nat.odd_iff.mp hℓodd; omega
    have hdvd : Nat.gcd ℓ n ∣ ℓ := Nat.gcd_dvd_left ℓ n
    have heq : Nat.gcd ℓ n * (ℓ / Nat.gcd ℓ n) = ℓ := Nat.mul_div_cancel' hdvd
    have hmdvd : (ℓ / Nat.gcd ℓ n) ∣ ℓ := ⟨Nat.gcd ℓ n, (Nat.div_mul_cancel hdvd).symm⟩
    have hcop_dm : Nat.Coprime (Nat.gcd ℓ n) (ℓ / Nat.gcd ℓ n) :=
      Nat.coprime_of_squarefree_mul (by rw [heq]; exact hℓsq)
    have hdpos : 0 < Nat.gcd ℓ n := Nat.pos_of_dvd_of_pos hdvd hℓpos
    have hmpos : 0 < ℓ / Nat.gcd ℓ n := Nat.pos_of_dvd_of_pos hmdvd hℓpos
    change Salt.M3Expansion.gTwin ℓ
        = Salt.M3Expansion.gTwin (Nat.gcd ℓ n) * Salt.M3Expansion.gTwin (ℓ / Nat.gcd ℓ n)
    rw [← gTwin_mul_of_coprime hdpos.ne' hmpos.ne' hcop_dm, heq]
  -- (B) injectivity of `φ` on `F`
  have hInj : Set.InjOn φ ↑F := by
    intro x _ y _ hxy
    simp only [hφ, Prod.mk.injEq] at hxy
    obtain ⟨e1, e2⟩ := hxy
    calc x = Nat.gcd x n * (x / Nat.gcd x n) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left x n)).symm
      _ = Nat.gcd y n * (y / Nat.gcd y n) := by rw [e2, e1]
      _ = y := Nat.mul_div_cancel' (Nat.gcd_dvd_left y n)
  -- (C) `F.image φ ⊆ Dn ×ˢ Fcop`
  have himgsub : F.image φ ⊆ Dn ×ˢ Fcop := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨ℓ, hℓF, rfl⟩ := hq
    have hℓF' := hℓF
    rw [hF, Finset.mem_filter, Finset.mem_range] at hℓF'
    obtain ⟨hℓz, hℓodd, hℓsq⟩ := hℓF'
    have hℓpos : 0 < ℓ := by have := Nat.odd_iff.mp hℓodd; omega
    have hdvd : Nat.gcd ℓ n ∣ ℓ := Nat.gcd_dvd_left ℓ n
    have hmdvd : (ℓ / Nat.gcd ℓ n) ∣ ℓ := ⟨Nat.gcd ℓ n, (Nat.div_mul_cancel hdvd).symm⟩
    have hcop_dm : Nat.Coprime (Nat.gcd ℓ n) (ℓ / Nat.gcd ℓ n) :=
      Nat.coprime_of_squarefree_mul (by rw [Nat.mul_div_cancel' hdvd]; exact hℓsq)
    have hgcd_dvd : Nat.gcd (ℓ / Nat.gcd ℓ n) n ∣ Nat.gcd ℓ n :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left _ n).trans hmdvd) (Nat.gcd_dvd_right _ n)
    have hcop_mn : Nat.Coprime (ℓ / Nat.gcd ℓ n) n := by
      have h1 : Nat.gcd (ℓ / Nat.gcd ℓ n) n ∣ Nat.gcd (Nat.gcd ℓ n) (ℓ / Nat.gcd ℓ n) :=
        Nat.dvd_gcd hgcd_dvd (Nat.gcd_dvd_left _ n)
      have h2 : Nat.gcd (Nat.gcd ℓ n) (ℓ / Nat.gcd ℓ n) = 1 := hcop_dm
      rw [h2] at h1
      exact Nat.dvd_one.mp h1
    have hmle : ℓ / Nat.gcd ℓ n ≤ ℓ := Nat.le_of_dvd hℓpos hmdvd
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · change Nat.gcd ℓ n ∈ Dn
      rw [hDn, Finset.mem_filter]
      exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ℓ n, hn0⟩,
        Squarefree.squarefree_of_dvd hdvd hℓsq, odd_of_dvd_odd hℓodd hdvd⟩
    · change ℓ / Nat.gcd ℓ n ∈ Fcop
      rw [hFcop, Finset.mem_filter]
      refine ⟨?_, hcop_mn⟩
      rw [hF, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, odd_of_dvd_odd hℓodd hmdvd, Squarefree.squarefree_of_dvd hmdvd hℓsq⟩
  -- (D) nonnegativity of the pair-product on the majorant carrier
  have hnn : ∀ q ∈ Dn ×ˢ Fcop, 0 ≤ g q := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    have o1 : Odd q.1 := (Finset.mem_filter.mp (hDn ▸ hq1)).2.2
    have o2 : Odd q.2 :=
      (Finset.mem_filter.mp (hF ▸ (Finset.mem_filter.mp (hFcop ▸ hq2)).1)).2.1
    exact mul_nonneg (gTwin_nonneg_of_odd o1) (gTwin_nonneg_of_odd o2)
  -- (E) `sTrunc2 n = Σ_{d∈Dn} gTwin d`, and the product majorant
  have hsT : sTrunc2 n = ∑ d ∈ Dn, Salt.M3Expansion.gTwin d := by
    rw [sTrunc2, ← hDn]
    exact Finset.sum_congr rfl (fun d _ => hFac2_eq_gTwin d)
  have hmaj : (∑ q ∈ Dn ×ˢ Fcop, g q)
      = sTrunc2 n * ∑ m ∈ Fcop, Salt.M3Expansion.gTwin m := by
    rw [hsT, Finset.sum_product, Finset.sum_mul_sum]
  -- assemble
  calc Salt.M3Assembly.mainTermSum z
      = ∑ ℓ ∈ F, Salt.M3Expansion.gTwin ℓ := by rw [Salt.M3Assembly.mainTermSum, ← hF]
    _ = ∑ ℓ ∈ F, g (φ ℓ) := Finset.sum_congr rfl hcongr
    _ = ∑ q ∈ F.image φ, g q := (Finset.sum_image hInj).symm
    _ ≤ ∑ q ∈ Dn ×ˢ Fcop, g q :=
        Finset.sum_le_sum_of_subset_of_nonneg himgsub (fun q hq _ => hnn q hq)
    _ = sTrunc2 n * ∑ m ∈ Fcop, Salt.M3Expansion.gTwin m := hmaj

/-! ## Step 3 — the denominator bound and the GB-7 seam -/

/-- **GB-6c, the coprime-restricted main-term denominator bound.**  The gold
Selberg carrier sum is `≥ c₀ (log z)² / sTrunc2 n` for all large `z`, with `c₀`
the twin main-term constant (`1/64`).  Chain: the twin `mainTermSum ≥ c₀·log²z`
transfers via the `d·m` factorization to `sTrunc2 n · Σ_{(m,n)=1} gTwin m`, the
coprime `gTwin` sum equals the coprime gold Selberg sum (coprime exactness), and
the full carrier sum dominates the coprime-restricted one (terms `≥ 0`). -/
theorem goldCarrierSum_ge_log_sq_div_sTrunc2 (hn0 : n ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z →
      c₀ * (Real.log z) ^ 2 / sTrunc2 n
        ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
  obtain ⟨c₀, hc₀, z₀, hz₀⟩ := Salt.M3Assembly.exists_const_mainTermSum_ge
  refine ⟨c₀, hc₀, z₀, fun z hz => ?_⟩
  rw [div_le_iff₀ (sTrunc2_pos hn0)]
  have hcop_le :
      (∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
          (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m)
        ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
    calc (∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m)
        = ∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
            (fun m => Nat.Coprime m n), (goldEnergySieve n P hn hP).selbergTerms m := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hm
          exact (selbergTerms_eq_gTwin_of_coprime m hm.1.2.1 hm.1.2.2 hm.2).symm
      _ ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
            (goldEnergySieve n P hn hP).selbergTerms ℓ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ℓ hℓ _ => ?_)
          rw [Finset.mem_filter, Finset.mem_range] at hℓ
          exact goldSelbergTerms_nonneg_of_odd hℓ.2.1 hℓ.2.2
  calc c₀ * (Real.log z) ^ 2
      ≤ Salt.M3Assembly.mainTermSum z := hz₀ z hz
    _ ≤ sTrunc2 n * ∑ m ∈ ((Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)).filter
          (fun m => Nat.Coprime m n), Salt.M3Expansion.gTwin m :=
        mainTermSum_le_sTrunc2_mul_coprimeSum z hn0
    _ ≤ sTrunc2 n * ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          (goldEnergySieve n P hn hP).selbergTerms ℓ :=
        mul_le_mul_of_nonneg_left hcop_le (sTrunc2_nonneg n)
    _ = (∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ),
          (goldEnergySieve n P hn hP).selbergTerms ℓ) * sTrunc2 n := mul_comm _ _

/-- **GB-6c, the composed denominator bound at the literal `selbergBoundingSum`.**
The coprime-restricted analogue of GB-6's `goldSelbergBoundingSum_ge_log_sq`,
with `sTrunc2 n` (square-sum-fundable) in place of `sCorr n`.  Composed with
GB-6's `carrierSum_le_selbergBoundingSum` verbatim.  This is the surface GB-7
feeds to `selberg_bound_simple`. -/
theorem goldSelbergBoundingSum_ge_log_sq_div_sTrunc2 (hn0 : n ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ z₀ : ℕ, ∀ (z : ℕ), z₀ ≤ z → ∀ (level : ℝ) (hlvl : 1 ≤ level),
      (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ)
          ⊆ P.divisors.filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ level) →
      c₀ * (Real.log z) ^ 2 / sTrunc2 n
        ≤ Salt.SelbergPort.selbergBoundingSum (goldSelbergSieve n P hn hP level hlvl) := by
  obtain ⟨c₀, hc₀, z₀, hz₀⟩ := goldCarrierSum_ge_log_sq_div_sTrunc2 (hn := hn) (hP := hP) hn0
  refine ⟨c₀, hc₀, z₀, fun z hz level hlvl hsub => ?_⟩
  exact le_trans (hz₀ z hz) (carrierSum_le_selbergBoundingSum level hlvl z hsub)

end Salt.Entropy.Chowla
