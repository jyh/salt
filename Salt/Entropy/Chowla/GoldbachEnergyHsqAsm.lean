/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The Goldbach-sieve `hsq` residual (rebuild nodes GB-12 + GB-13)

The squared-main-term second moment of the binary-Goldbach upper sieve, closing
the `hsq` hypothesis of `W3_AE_d_of_sieve` at the GB-0 frozen `rbound`
(`docs/exploration/s3-a3-design.md`, sections "GB-0 — THE REBUILD DESIGN FREEZE"
and the hsq track).

The content is **parametric in the multiplicative weight** `h : ℕ → ℝ`: the GB-6
re-freeze changed the frozen `rbound` from an `hFac`-truncated singular series to
an `hFac2`-truncated one, so the Fubini/count machinery is stated once for a
general `h` (nonnegative on odd squarefree, with the lcm-double-sum majorant `K`
supplied as a hypothesis) and instantiated at `h = hFac` here.  The `hFac2`
instantiation waits on GB-14b and is left to the caller.

* **GB-12 — expand.**  Pull the constant `A = C₁·(ε²H/log²H)` out of
  `rbound n = if Even n then A·(∑_{d∣n, sf, odd} h d) else 0`; the odd terms
  vanish, so the sum is `≤ A²·∑_{n ∈ 𝒫+𝒫} (∑ h)²`.  Then `(∑ h)²` expands
  (`Finset.sum_mul_sum`) into a double sum over odd squarefree divisor pairs,
  re-indexed over the enlarged cap `E = range(2⌊ε²H⌋+1)` with `d ∣ n` indicators,
  the pair `[d₁∣n]·[d₂∣n]` collapsing to `[lcm(d₁,d₂)∣n]` (`Nat.lcm_dvd_iff`).

* **GB-13 — count.**  Every `n ∈ 𝒫+𝒫` lies in `Ioc 0 (2⌊ε²H⌋)`, so the multiples
  of `L = lcm(d₁,d₂)` there number `≤ M/L` EXACTLY (`Nat.Ioc_filter_dvd_card_eq_div`,
  then `Nat.cast_div_le` — no `+1` slack, so no Mertens second-order term).  The
  lcm-double-sum majorant `K` then bounds `∑_{d₁,d₂} h·h/L ≤ K`, giving
  `∑ (∑h)² ≤ 2⌊ε²H⌋·K` and the residual `≤ C·H³/log⁴H` with `C = 2K·C₁²·ε⁶`,
  uniformly for `H ≥ 2`.
-/
import Salt.Entropy.Chowla.GoldbachEnergyHsq
import Salt.Entropy.Chowla.QuadrupleCount
import Mathlib

open Finset
open scoped BigOperators Pointwise

namespace Salt.Entropy.Chowla

/-- The truncated singular-series majorant for a general weight `h`: the sum of
`h d` over the odd squarefree divisors of `n`.  `sTruncW hFac = sTrunc`. -/
noncomputable def sTruncW (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => Squarefree d ∧ Odd d), h d

/-- The landed `sTrunc` is the `h = hFac` instance of `sTruncW`. -/
lemma sTrunc_eq_sTruncW (n : ℕ) : sTrunc n = sTruncW hFac n := rfl

/-- Every element of the prime-window sumset `𝒫+𝒫` lies in `Ioc 0 (2⌊ε²H⌋)`:
each `n = p₁+p₂` with primes `p₁,p₂ ≤ ⌊ε²H⌋` and `≥ 2`, so `0 < n ≤ 2⌊ε²H⌋`. -/
lemma sumset_subset_Ioc (eps : ℚ) (H : ℕ) :
    primeWindow eps H + primeWindow eps H
      ⊆ Finset.Ioc 0 (2 * ⌊eps ^ 2 * (H : ℚ)⌋₊) := by
  intro n hn
  rw [Finset.mem_add] at hn
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := hn
  rw [mem_primeWindow] at hp₁ hp₂
  have h1le := hp₁.1
  have h2le := hp₂.1
  have h1pos := hp₁.2.1.pos
  have h2pos := hp₂.2.1.pos
  rw [Finset.mem_Ioc]
  omega

/-- The truncated series, re-indexed over the enlarged squarefree-odd cap
`E = range(M+1)` with a `d ∣ n` indicator: for `0 < n ≤ M` the odd squarefree
divisors of `n` are exactly the elements of `E` dividing `n`. -/
lemma sTruncW_eq_sum_ite (h : ℕ → ℝ) {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    sTruncW h n = ∑ d ∈ (Finset.range (M + 1)).filter (fun d => Squarefree d ∧ Odd d),
      (if d ∣ n then h d else 0) := by
  have hset : ((Finset.range (M + 1)).filter (fun d => Squarefree d ∧ Odd d)).filter
      (fun d => d ∣ n) = n.divisors.filter (fun d => Squarefree d ∧ Odd d) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, hsf, hodd⟩, hdvd⟩
      exact ⟨⟨hdvd, hn.ne'⟩, hsf, hodd⟩
    · rintro ⟨⟨hdvd, _⟩, hsf, hodd⟩
      have hdle : d ≤ n := Nat.le_of_dvd hn hdvd
      exact ⟨⟨by omega, hsf, hodd⟩, hdvd⟩
  rw [sTruncW, ← hset, Finset.sum_filter]

/-- **The core second-moment bound (GB-12 + GB-13).**  Given the lcm-double-sum
majorant `K` (at `X = 2⌊ε²H⌋`), the sum of `(∑_{d∣n, sf, odd} h d)²` over the
prime-window sumset is `≤ 2⌊ε²H⌋·K`.  Expand the square (`Finset.sum_mul_sum`),
swap to sum over divisor pairs, collapse the two dvd indicators to `lcm ∣ n` and
count EXACTLY (`Nat.Ioc_filter_dvd_card_eq_div`, so `≤ M/L` with no `+1`), then
apply `K`. -/
lemma sum_sTruncW_sq_le (eps : ℚ) (H : ℕ) (h : ℕ → ℝ)
    (hh : ∀ d, Squarefree d → Odd d → 0 ≤ h d) (K : ℝ)
    (hK : ∑ d₁ ∈ (Finset.range (2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ + 1)).filter
            (fun d => Squarefree d ∧ Odd d),
          ∑ d₂ ∈ (Finset.range (2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ + 1)).filter
            (fun d => Squarefree d ∧ Odd d),
            h d₁ * h d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K) :
    ∑ n ∈ primeWindow eps H + primeWindow eps H, sTruncW h n ^ 2
      ≤ ((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) * K := by
  classical
  set M := 2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ with hMdef
  set W := primeWindow eps H + primeWindow eps H with hWdef
  set E := (Finset.range (M + 1)).filter (fun d => Squarefree d ∧ Odd d) with hEdef
  calc ∑ n ∈ W, sTruncW h n ^ 2
      = ∑ d₁ ∈ E, ∑ d₂ ∈ E, ∑ n ∈ W,
          (if d₁ ∣ n ∧ d₂ ∣ n then h d₁ * h d₂ else 0) := by
        rw [show (∑ n ∈ W, sTruncW h n ^ 2)
            = ∑ n ∈ W, ∑ d₁ ∈ E, ∑ d₂ ∈ E,
                (if d₁ ∣ n ∧ d₂ ∣ n then h d₁ * h d₂ else 0) from
          Finset.sum_congr rfl fun n hn => by
            have hmem := (sumset_subset_Ioc eps H) hn
            rw [Finset.mem_Ioc] at hmem
            rw [pow_two, sTruncW_eq_sum_ite h hmem.1 hmem.2, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
            by_cases h1 : d₁ ∣ n <;> by_cases h2 : d₂ ∣ n <;> simp [h1, h2]]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
    _ ≤ ∑ d₁ ∈ E, ∑ d₂ ∈ E, (M : ℝ) * (h d₁ * h d₂ / (Nat.lcm d₁ d₂ : ℝ)) := by
        refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
        have hsf₁ : Squarefree d₁ := (Finset.mem_filter.mp hd₁).2.1
        have hodd₁ : Odd d₁ := (Finset.mem_filter.mp hd₁).2.2
        have hsf₂ : Squarefree d₂ := (Finset.mem_filter.mp hd₂).2.1
        have hodd₂ : Odd d₂ := (Finset.mem_filter.mp hd₂).2.2
        have hc : (0 : ℝ) ≤ h d₁ * h d₂ :=
          mul_nonneg (hh d₁ hsf₁ hodd₁) (hh d₂ hsf₂ hodd₂)
        have hcond : ∑ n ∈ W, (if d₁ ∣ n ∧ d₂ ∣ n then h d₁ * h d₂ else 0)
            = ∑ n ∈ W, (if Nat.lcm d₁ d₂ ∣ n then h d₁ * h d₂ else 0) :=
          Finset.sum_congr rfl fun n _ => if_congr Nat.lcm_dvd_iff.symm rfl rfl
        rw [hcond, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hcard : (W.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card ≤ M / Nat.lcm d₁ d₂ :=
          calc (W.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card
              ≤ ((Finset.Ioc 0 M).filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card :=
                Finset.card_le_card (Finset.filter_subset_filter _ (sumset_subset_Ioc eps H))
            _ = M / Nat.lcm d₁ d₂ := Nat.Ioc_filter_dvd_card_eq_div M (Nat.lcm d₁ d₂)
        have hcast : (↑(W.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ)
            ≤ (M : ℝ) / (Nat.lcm d₁ d₂ : ℝ) :=
          le_trans (by exact_mod_cast hcard) Nat.cast_div_le
        calc (↑(W.filter (fun n => Nat.lcm d₁ d₂ ∣ n)).card : ℝ) * (h d₁ * h d₂)
            ≤ ((M : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) * (h d₁ * h d₂) :=
              mul_le_mul_of_nonneg_right hcast hc
          _ = (M : ℝ) * (h d₁ * h d₂ / (Nat.lcm d₁ d₂ : ℝ)) := by ring
    _ = (M : ℝ) * ∑ d₁ ∈ E, ∑ d₂ ∈ E, h d₁ * h d₂ / (Nat.lcm d₁ d₂ : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d₁ _ => by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * K := mul_le_mul_of_nonneg_left hK (by positivity)

/-- **The parametric `hsq` keystone (GB-12 + GB-13).**  For any weight `h`
nonnegative on odd squarefree moduli, with an lcm-double-sum majorant `K`
(uniform in the range cap), the squared-main-term second moment of the frozen
`rbound n = if Even n then C₁·(ε²H/log²H)·(∑_{d∣n, sf, odd} h d) else 0` over the
prime-window sumset is `≤ C·H³/log⁴H` with `C = 2K·C₁²·ε⁶`, for all `H ≥ 2`.
This is the `hsq` hypothesis of `W3_AE_d_of_sieve` at the GB-0 rbound. -/
theorem hsq_holds_gen (eps : ℚ) (heps : 0 < eps) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (h : ℕ → ℝ) (hh : ∀ d, Squarefree d → Odd d → 0 ≤ h d) (K : ℝ) (hKpos : 0 < K)
    (hK : ∀ X : ℕ, ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
            ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
              h d₁ * h d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∑ n ∈ primeWindow eps H + primeWindow eps H,
        ((if Even n then C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTruncW h n
          else 0)) ^ 2
        ≤ C * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
  have hε : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  refine ⟨2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6, by positivity, 2, le_refl 2, fun H hH => ?_⟩
  set A := C₁ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) with hAdef
  have hL : (0 : ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hfloor : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
    calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
      _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
      _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
  have hMle : ((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ 2 * (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h2 : ((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
        = 2 * ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) := by push_cast; ring
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left hfloor (by norm_num)
  calc ∑ n ∈ primeWindow eps H + primeWindow eps H,
        (if Even n then A * sTruncW h n else 0) ^ 2
      ≤ A ^ 2 * ∑ n ∈ primeWindow eps H + primeWindow eps H, sTruncW h n ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n _ => ?_
        by_cases he : Even n
        · rw [if_pos he]; exact le_of_eq (mul_pow _ _ _)
        · rw [if_neg he, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]; positivity
    _ ≤ A ^ 2 * (((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) * K) :=
        mul_le_mul_of_nonneg_left (sum_sTruncW_sq_le eps H h hh K (hK _)) (sq_nonneg A)
    _ ≤ (2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6) * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
        have hAK : (0 : ℝ) ≤ A ^ 2 * K := mul_nonneg (sq_nonneg A) hKpos.le
        calc A ^ 2 * (((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) * K)
            = (A ^ 2 * K) * ((2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) := by ring
          _ ≤ (A ^ 2 * K) * (2 * (eps : ℝ) ^ 2 * (H : ℝ)) :=
              mul_le_mul_of_nonneg_left hMle hAK
          _ = (2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6) * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
              rw [hAdef]; field_simp

/-- **The `hsq` keystone at `h = hFac`** (the landed GB-11/14 weight).  Discharges
the `hsq` hypothesis of `W3_AE_d_of_sieve` at the original GB-0 frozen `rbound`
(`if Even n then C₁·(ε²H/log²H)·sTrunc n else 0`), via `hFac_lcm_sum_le`
(`K = exp(9·ζ(2))`).  `C = 2·exp(9·ζ(2))·C₁²·ε⁶`, `H₀ = 2`. -/
theorem hsq_holds (eps : ℚ) (heps : 0 < eps) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∑ n ∈ primeWindow eps H + primeWindow eps H,
        ((if Even n then C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc n
          else 0)) ^ 2
        ≤ C * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
  obtain ⟨K, hKpos, hKall⟩ := hFac_lcm_sum_le
  simp only [sTrunc_eq_sTruncW]
  exact hsq_holds_gen eps heps C₁ hC₁ hFac (fun d _ hodd => hFac_nonneg hodd) K hKpos hKall

end Salt.Entropy.Chowla
