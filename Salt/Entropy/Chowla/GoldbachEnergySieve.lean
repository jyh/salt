/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# GB-5 — the binary-Goldbach `BoundingSieve` instance (rebuild node GB-5)

The mathlib `BoundingSieve` for sifting the values `m * (n - m)`, `m ∈ [1, n]`,
by the primes dividing a squarefree modulus `P`.  The Goldbach-sieve analogue of
the twin track's `Salt/Brun/Sieve.lean`, consuming the local density facts of
`Salt/Entropy/Chowla/GoldbachEnergyM2.lean` (`rhoG`/`rhoG_mul_of_coprime`/the
prime values/the count bound) and mirroring the twin plumbing idiom.

* **The density** `nuG n d = rhoG n d / d` as an `ArithmeticFunction ℝ`,
  multiplicative on coprime moduli (from `rhoG_mul_of_coprime`), with
  `0 < ν(p) < 1` on every prime — the `ν(p) < 1` proof is exactly where the
  `n`-even guard `hn : 2 ∣ n` fires (at `p = 2, p ∤ n` we would need `p ≥ 3`,
  but `p = 2 ∧ 2 ∤ n` contradicts `hn`).

* **The support**: mathlib sifts a support element `x` by `d ∣ x`, so to sift
  `m * (n - m)` the support must hold those VALUES.  Since `m ↦ m(n-m)` is
  symmetric (hence non-injective) on `[1, n]`, the twin's injective `image`
  trick fails; instead the support is `(Icc 1 n).image (m ↦ m(n-m))` with
  MULTIPLICITY weights `x ↦ #{m ∈ [1,n] : m(n-m) = x}`.  This realizes
  `multSum d = #{m ∈ [1,n] : d ∣ m(n-m)}` (the `goldProgression_count_bound`
  carrier) EXACTLY, and — crucially — keeps `siftedSum` an over-count of the
  ordered representations, so the downstream `repCount ≤ siftedSum` survives.

* **The remainder** `rem d` equals `#{m ∈ [1,n] : d ∣ m(n-m)} - ν(d)·n`, bounded
  in absolute value by `rhoG n d` via `goldProgression_count_bound n d n` (the
  counting interval is instantiated at `N = n` EXACTLY, per that node's caveat).

No `sorry`, no `native_decide`, no new axioms.
-/
import Mathlib
import Salt.Entropy.Chowla.GoldbachEnergyM2
import Salt.Entropy.Chowla.QuadrupleCount

open ArithmeticFunction Finset

namespace Salt.Entropy.Chowla

/-! ## The local density `nuG` -/

/-- GB-5: the local density `ν_n d = ρ_n(d)/d` as an arithmetic function
(`ν_n 0 = 0`).  Mirrors the twin `Salt.TwinSieve.nu`. -/
noncomputable def nuG (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => (rhoG n d : ℝ) / d, by simp [rhoG]⟩

@[simp] lemma nuG_apply (n d : ℕ) : nuG n d = (rhoG n d : ℝ) / d := rfl

/-- `ν_n` is multiplicative on coprime moduli (from `rhoG_mul_of_coprime`). -/
lemma nuG_mult (n : ℕ) : (nuG n).IsMultiplicative := by
  constructor
  · simp only [nuG_apply]; rw [rhoG_one]; norm_num
  · intro a b hab
    simp only [nuG_apply]
    rcases eq_or_ne a 0 with rfl | ha
    · simp only [Nat.coprime_zero_left] at hab; subst hab; simp
    rcases eq_or_ne b 0 with rfl | hb
    · simp only [Nat.coprime_zero_right] at hab; subst hab; simp
    rw [rhoG_mul_of_coprime ha hb hab]; push_cast; field_simp

/-- `0 < ν_n(p)` for prime `p` (`ρ_n(p) ∈ {1, 2}`, both positive). -/
lemma nuG_pos_of_prime (n p : ℕ) (hp : p.Prime) : 0 < nuG n p := by
  rw [nuG_apply]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hrho : (0 : ℝ) < (rhoG n p : ℝ) := by
    by_cases hpn : p ∣ n
    · rw [rhoG_prime_dvd hp hpn]; norm_num
    · rw [rhoG_prime_not_dvd hp hpn]; norm_num
  exact div_pos hrho hp0

/-- `ν_n(p) < 1` for prime `p`, given `n` even.  At `p ∣ n` we have
`ρ_n(p) = 1`, so `ν = 1/p < 1` (`p ≥ 2`).  At `p ∤ n` we have `ρ_n(p) = 2`, so
`ν = 2/p < 1` needs `p ≥ 3`; but `p = 2 ∧ 2 ∤ n` contradicts `hn : 2 ∣ n`, so
`p ≥ 3` — this is where the `n`-even guard fires. -/
lemma nuG_lt_one_of_prime (n : ℕ) (hn : 2 ∣ n) (p : ℕ) (hp : p.Prime) : nuG n p < 1 := by
  rw [nuG_apply, div_lt_one (by exact_mod_cast hp.pos)]
  by_cases hpn : p ∣ n
  · rw [rhoG_prime_dvd hp hpn]
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    push_cast; linarith
  · rw [rhoG_prime_not_dvd hp hpn]
    have hp3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · exact absurd hn (h2 ▸ hpn)
      · obtain ⟨k, hk⟩ := hodd; have := hp.two_le; omega
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    push_cast; linarith

/-! ## The instance -/

/-- **GB-5**: the binary-Goldbach `BoundingSieve` for the values `m * (n - m)`,
`m ∈ [1, n]`, sifted by the primes dividing the squarefree modulus `P`.  Support
= the image `{m(n-m) : m ∈ [1,n]}` with MULTIPLICITY weights (the fibre card),
so the abstract `d ∣ (support element)` test realizes the honest count
`#{m : d ∣ m(n-m)}`.  Needs `n` even (`hn`) for `ν(2) < 1`. -/
noncomputable def goldEnergySieve (n P : ℕ) (hn : 2 ∣ n) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.Icc 1 n).image (fun m => m * (n - m))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun v => (((Finset.Icc 1 n).filter (fun m => m * (n - m) = v)).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := (n : ℝ)
  nu := nuG n
  nu_mult := nuG_mult n
  nu_pos_of_prime := fun p hp _ => nuG_pos_of_prime n p hp
  nu_lt_one_of_prime := fun p hp _ => nuG_lt_one_of_prime n hn p hp

variable {n P : ℕ} {hn : 2 ∣ n} {hP : Squarefree P}

@[simp] lemma goldEnergySieve_prodPrimes : (goldEnergySieve n P hn hP).prodPrimes = P := rfl
@[simp] lemma goldEnergySieve_nu : (goldEnergySieve n P hn hP).nu = nuG n := rfl
@[simp] lemma goldEnergySieve_totalMass : (goldEnergySieve n P hn hP).totalMass = (n : ℝ) := rfl

/-! ## The multiplicity-weight fibre identity -/

/-- The core fibre decomposition: summing a `Q`-gated multiplicity weight over the
image equals the honest count `#{m ∈ [1,n] : Q (m(n-m))}`.  Shared by `multSum`
(`Q v := d ∣ v`) and `siftedSum` (`Q v := Coprime P v`). -/
private lemma image_weight_sum_eq (n : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ v ∈ (Finset.Icc 1 n).image (fun m => m * (n - m)),
        (if Q v then (((Finset.Icc 1 n).filter (fun m => m * (n - m) = v)).card : ℝ) else 0))
      = (((Finset.Icc 1 n).filter (fun m => Q (m * (n - m)))).card : ℝ) := by
  have hnat : ((Finset.Icc 1 n).filter (fun m => Q (m * (n - m)))).card
      = ∑ v ∈ (Finset.Icc 1 n).image (fun m => m * (n - m)),
          (if Q v then ((Finset.Icc 1 n).filter (fun m => m * (n - m) = v)).card else 0) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun m => m * (n - m))
        (t := (Finset.Icc 1 n).image (fun m => m * (n - m)))
        (by intro m hm
            rw [Finset.mem_coe] at hm ⊢
            exact Finset.mem_image_of_mem _ (Finset.mem_of_mem_filter _ hm))]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hQ : Q v
    · rw [if_pos hQ]
      congr 1
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨ha, _⟩, hav⟩; exact ⟨ha, hav⟩
      · rintro ⟨ha, hav⟩; exact ⟨⟨ha, by rw [hav]; exact hQ⟩, hav⟩
    · rw [if_neg hQ, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha hav
      exact hQ (hav ▸ (Finset.mem_filter.mp ha).2)
  exact_mod_cast hnat.symm

/-- **`multSum d` = the honest Goldbach count** `#{m ∈ [1,n] : d ∣ m(n-m)}`. -/
lemma goldEnergySieve_multSum (d : ℕ) :
    (goldEnergySieve n P hn hP).multSum d
      = (((Finset.Icc 1 n).filter (fun m => d ∣ m * (n - m))).card : ℝ) := by
  change (∑ v ∈ (Finset.Icc 1 n).image (fun m => m * (n - m)),
      if d ∣ v then (((Finset.Icc 1 n).filter (fun m => m * (n - m) = v)).card : ℝ) else 0) = _
  exact image_weight_sum_eq n (fun v => d ∣ v)

/-- **`siftedSum` = the coprime Goldbach count** `#{m ∈ [1,n] : Coprime P (m(n-m))}`. -/
lemma goldEnergySieve_siftedSum :
    (goldEnergySieve n P hn hP).siftedSum
      = (((Finset.Icc 1 n).filter (fun m => Nat.Coprime P (m * (n - m)))).card : ℝ) := by
  rw [BoundingSieve.siftedSum]
  change (∑ v ∈ (Finset.Icc 1 n).image (fun m => m * (n - m)),
      if Nat.Coprime P v then
        (((Finset.Icc 1 n).filter (fun m => m * (n - m) = v)).card : ℝ) else 0) = _
  exact image_weight_sum_eq n (fun v => Nat.Coprime P v)

/-- **`rem d`** — the AP-remainder, `rem d = #{m : d ∣ m(n-m)} - ν_n(d)·n`. -/
lemma goldEnergySieve_rem (d : ℕ) :
    (goldEnergySieve n P hn hP).rem d
      = (((Finset.Icc 1 n).filter (fun m => d ∣ m * (n - m))).card : ℝ)
        - nuG n d * (n : ℝ) := by
  rw [BoundingSieve.rem, goldEnergySieve_multSum, goldEnergySieve_nu, goldEnergySieve_totalMass]

/-- **The remainder bound** `|rem d| ≤ ρ_n(d)`, from `goldProgression_count_bound`
instantiated at the counting interval `N = n` (per the GB-M2 caveat). -/
lemma goldEnergySieve_abs_rem_le (d : ℕ) (hd : d ≠ 0) :
    |(goldEnergySieve n P hn hP).rem d| ≤ (rhoG n d : ℝ) := by
  rw [goldEnergySieve_rem, nuG_apply,
    show (rhoG n d : ℝ) / d * n = n * rhoG n d / d from by ring]
  exact goldProgression_count_bound n d n hd le_rfl

/-! ## The GB-9 consumer seam: `repCount ≤ siftedSum`

Each ordered representation `n = p + q` with `p, q ∈ 𝒫_H` survives the sift: at
`m = p` the sifted value `m(n-m) = p·q` is coprime to `P` (both `p, q > z ≥`
every prime factor of `P`), so `(p, q) ↦ p` injects the representations into the
`siftedSum` carrier `{m ∈ [1,n] : Coprime P (m(n-m))}`.  Injectivity is where the
MULTIPLICITY-weight support pays off — the two orders `(p,q)`, `(q,p)` map to the
distinct survivors `p ≠ q`, so the ordered count is not collapsed. -/

/-- **GB-9 seam**: the ordered representation count is at most the `siftedSum`,
whenever every prime factor of `P` is `≤ z` and every window prime exceeds `z`. -/
lemma repCount_le_siftedSum (n P : ℕ) (hn : 2 ∣ n) (hP : Squarefree P)
    (eps : ℚ) (H : ℕ) {z : ℕ}
    (hPz : ∀ q, q.Prime → q ∣ P → q ≤ z)
    (hwin : ∀ p ∈ primeWindow eps H, z < p) :
    (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
      ≤ (goldEnergySieve n P hn hP).siftedSum := by
  rw [goldEnergySieve_siftedSum]
  have hcopP : ∀ r ∈ primeWindow eps H, Nat.Coprime P r := by
    intro r hr
    have hrp := prime_of_mem_primeWindow hr
    refine (hrp.coprime_iff_not_dvd.mpr ?_).symm
    intro hdvd
    exact absurd (hPz r hrp hdvd) (by have := hwin r hr; omega)
  have hcard : repCount (primeWindow eps H) (primeWindow eps H) n
      ≤ ((Finset.Icc 1 n).filter (fun m => Nat.Coprime P (m * (n - m)))).card := by
    unfold repCount
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · rintro ⟨p, q⟩ hpq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq
      obtain ⟨⟨hp, hq⟩, hsum'⟩ := hpq
      have hsum : p + q = n := hsum'
      have hpp := prime_of_mem_primeWindow hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hpp.pos, by omega⟩, ?_⟩
      have hnp : n - p = q := by omega
      rw [hnp]
      exact Nat.Coprime.mul_right (hcopP p hp) (hcopP q hq)
    · rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' heq
      rw [Finset.mem_coe, Finset.mem_filter] at hpq hpq'
      have h1 : p + q = n := hpq.2
      have h2 : p' + q' = n := hpq'.2
      have hpp' : p = p' := heq
      simp only [Prod.mk.injEq]
      exact ⟨hpp', by omega⟩
  exact_mod_cast hcard

end Salt.Entropy.Chowla
