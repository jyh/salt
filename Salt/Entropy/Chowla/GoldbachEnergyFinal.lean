/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# GB-15 — the Goldbach rebuild's terminal assembly

Make both sieve residuals of `W3_AE_d_of_sieve` / `bigXi_bounded_of_sieve` REAL
at the re-frozen (GB-7 catch, RE-FREEZE #2) `rbound`

  `rbound H n := C₁·((eps:ℝ)²·H/(log H)²)·sTrunc2 n`   (for ALL `n`, no parity split)

and land the unconditional `|Ξ_H|` bound (Tao 1509.05422 Lemma 3.5).  See
`docs/exploration/s3-a3-design.md`, the "Night-shift adjudications" +
"GB-7 CATCH + RE-FREEZE #2" sections.

Deliverables:

* **`hsq_holds_gen'` / `hsq_holds3`** — the no-`if` `hsq` residual.  The
  parity split is dropped, so the frozen summand loses its `if Even n`; the
  proof is strictly easier than `hsq_holds_gen` (the leading `by_cases`
  becomes a plain `mul_pow`).
* **`hpt_holds`** — the ungated `hpt` at the re-frozen `rbound`.  Case
  analysis: the degenerate cells (`n = 0`; `H ∈ {0,1}` where `rbound = 0` in
  Lean's junk-division sense) close by `repCount = 0`; below the threshold
  `H₁(ε)` a crude `card²` bound absorbs into `C₁`; above it the odd targets
  vanish (`repCount_eq_zero_of_window_odd`) and the even targets land the
  sieve core (`repCount_even_le_primorial`) through the `z = ⌊H^(1/10)⌋₊`
  rpow seam.
* **`bigXi_bounded`** — THE unconditional `|Ξ_H| ≤ C` bound, composing
  `bigXi_bounded_of_sieve` with `hpt_holds` + `hsq_holds3`, no sieve
  hypotheses left.

No `sorry`, no `native_decide`, no new axioms.
-/
import Salt.Entropy.Chowla.GoldbachEnergyHpt
import Salt.Entropy.Chowla.GoldbachEnergyHsqAsm
import Salt.Entropy.Chowla.GoldbachEnergyHsq2
import Salt.Entropy.Chowla.LargeSpectrumBound
import Salt.Brun.M5BigO

open ArithmeticFunction Finset
open scoped BigOperators Pointwise

namespace Salt.Entropy.Chowla

/-! ## Small helpers — degenerate representation counts, crude bounds, thresholds -/

/-- `1 ≤ sTrunc2 n` for `n ≠ 0`: the `d = 1` term of the truncated series is
`hFac2 1 = 1` (empty product), and every term is nonnegative. -/
lemma one_le_sTrunc2 {n : ℕ} (hn : n ≠ 0) : (1 : ℝ) ≤ sTrunc2 n := by
  have h1mem : (1 : ℕ) ∈ n.divisors.filter (fun d => Squarefree d ∧ Odd d) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd n, hn⟩, squarefree_one, odd_one⟩
  have hle : hFac2 1 ≤ sTrunc2 n :=
    Finset.single_le_sum (fun d hd => hFac2_nonneg (Finset.mem_filter.mp hd).2.2) h1mem
  have h1 : hFac2 1 = 1 := by rw [hFac2, Nat.primeFactors_one, Finset.prod_empty]
  rwa [h1] at hle

/-- Crude representation-count bound: `repCount s t n ≤ |s| · |t|` (the filtered
subset of `s ×ˢ t` is no larger than the whole product). -/
lemma repCount_le_card_mul (s t : Finset ℕ) (n : ℕ) :
    repCount s t n ≤ s.card * t.card := by
  unfold repCount
  calc {xy ∈ s ×ˢ t | xy.1 + xy.2 = n}.card
      ≤ (s ×ˢ t).card := Finset.card_filter_le _ _
    _ = s.card * t.card := Finset.card_product s t

/-- If the first window is empty, the representation count is `0`. -/
lemma repCount_eq_zero_of_empty {s t : Finset ℕ} {n : ℕ} (hs : s = ∅) :
    repCount s t n = 0 := by
  rw [repCount, hs, Finset.empty_product, Finset.filter_empty, Finset.card_empty]

/-- No two window primes sum to `0` (each is `≥ 1`), so `repCount … 0 = 0`. -/
lemma repCount_zero_target {eps : ℚ} {H : ℕ} :
    repCount (primeWindow eps H) (primeWindow eps H) 0 = 0 := by
  rw [repCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨p, q⟩ hpq heq
  rw [Finset.mem_product] at hpq
  have hpp : 0 < p := (prime_of_mem_primeWindow hpq.1).pos
  simp only [] at heq
  omega

/-- A target beyond `2⌊ε²H⌋` has no representation (any `p + q` with window primes
`p, q ≤ ⌊ε²H⌋` lies in `Ioc 0 (2⌊ε²H⌋)`), so `repCount = 0`. -/
lemma repCount_eq_zero_of_large {eps : ℚ} {H n : ℕ}
    (hn : 2 * ⌊eps ^ 2 * (H : ℚ)⌋₊ < n) :
    repCount (primeWindow eps H) (primeWindow eps H) n = 0 := by
  by_contra hne
  have hpos : 0 < repCount (primeWindow eps H) (primeWindow eps H) n := Nat.pos_of_ne_zero hne
  rw [repCount, Finset.card_pos] at hpos
  obtain ⟨⟨p, q⟩, hpq⟩ := hpos
  rw [Finset.mem_filter, Finset.mem_product] at hpq
  have hmem : n ∈ primeWindow eps H + primeWindow eps H := by
    rw [Finset.mem_add]
    exact ⟨p, hpq.1.1, q, hpq.1.2, hpq.2⟩
  have hIoc := sumset_subset_Ioc eps H hmem
  rw [Finset.mem_Ioc] at hIoc
  omega

/-- A threshold builder: for any `c` and exponent `r > 0`, there is `H₁` with
`c ≤ H^r` for all `H ≥ H₁`. -/
lemma rpow_ge_threshold (c : ℝ) (r : ℝ) (hr : 0 < r) :
    ∃ H₁ : ℕ, ∀ H : ℕ, H₁ ≤ H → c ≤ (H : ℝ) ^ r := by
  by_cases hc : c ≤ 0
  · exact ⟨1, fun H _ => le_trans hc (Real.rpow_nonneg (Nat.cast_nonneg H) r)⟩
  · have hc : 0 < c := not_le.mp hc
    refine ⟨⌈c ^ (1 / r)⌉₊ + 1, fun H hH => ?_⟩
    have hcr : (0 : ℝ) ≤ c ^ (1 / r) := Real.rpow_nonneg hc.le _
    have h1 : c ^ (1 / r) ≤ (⌈c ^ (1 / r)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈c ^ (1 / r)⌉₊ : ℕ) : ℝ) ≤ (H : ℝ) := by
      have hnat : (⌈c ^ (1 / r)⌉₊ : ℕ) ≤ H := le_trans (Nat.le_succ _) hH
      exact_mod_cast hnat
    have h3 : c ^ (1 / r) ≤ (H : ℝ) := le_trans h1 h2
    have h4 : (c ^ (1 / r)) ^ r ≤ (H : ℝ) ^ r := Real.rpow_le_rpow hcr h3 hr.le
    rwa [← Real.rpow_mul hc.le, one_div, inv_mul_cancel₀ hr.ne', Real.rpow_one] at h4

/-- A rational threshold for the "window all odd" hypothesis `4 ≤ ε²H`. -/
lemma four_le_threshold (eps : ℚ) (heps : 0 < eps) :
    ∃ tA : ℕ, ∀ H : ℕ, tA ≤ H → 4 ≤ eps ^ 2 * (H : ℚ) := by
  have heps2 : 0 < eps ^ 2 := by positivity
  refine ⟨⌈4 / eps ^ 2⌉₊, fun H hH => ?_⟩
  have h1 : (4 / eps ^ 2 : ℚ) ≤ (⌈4 / eps ^ 2⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : ((⌈4 / eps ^ 2⌉₊ : ℕ) : ℚ) ≤ (H : ℚ) := by exact_mod_cast hH
  have h3 : (4 / eps ^ 2 : ℚ) ≤ (H : ℚ) := le_trans h1 h2
  rw [div_le_iff₀ heps2] at h3
  linarith [h3, mul_comm (H : ℚ) (eps ^ 2)]

/-! ## Deliverable 1 — the no-`if` `hsq` residual -/

/-- **The no-`if` parametric `hsq` keystone.**  The GB-7 re-freeze dropped the
parity split, so the frozen summand is `(C₁·(ε²H/log²H)·sTruncW h n)²` with no
`if Even n`.  Identical to `hsq_holds_gen` except the leading `by_cases` collapses
to a plain `mul_pow` (the odd terms are no longer discarded — `sum_sTruncW_sq_le`
already bounds the FULL sumset). -/
theorem hsq_holds_gen' (eps : ℚ) (heps : 0 < eps) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (h : ℕ → ℝ) (hh : ∀ d, Squarefree d → Odd d → 0 ≤ h d) (K : ℝ) (hKpos : 0 < K)
    (hK : ∀ X : ℕ, ∑ d₁ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
            ∑ d₂ ∈ (Finset.range (X + 1)).filter (fun d => Squarefree d ∧ Odd d),
              h d₁ * h d₂ / (Nat.lcm d₁ d₂ : ℝ) ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∑ n ∈ primeWindow eps H + primeWindow eps H,
        (C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTruncW h n) ^ 2
        ≤ C * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
  have hε : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  refine ⟨2 * K * C₁ ^ 2 * (eps : ℝ) ^ 6, by positivity, 2, le_refl 2, fun H hH => ?_⟩
  set A := C₁ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) with hAdef
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
  calc ∑ n ∈ primeWindow eps H + primeWindow eps H, (A * sTruncW h n) ^ 2
      = A ^ 2 * ∑ n ∈ primeWindow eps H + primeWindow eps H, sTruncW h n ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => mul_pow _ _ _
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

/-- **The no-`if` `hsq` keystone at `h = hFac2`** (the GB-6 re-frozen weight,
GB-7 no-parity re-freeze).  Discharges `hsq` at the re-frozen `rbound`
`C₁·(ε²H/log²H)·sTrunc2 n` (no `if Even n`), via `hFac2_lcm_sum_le`
(`K = exp(24·ζ(2))`).  `C = 2·exp(24·ζ(2))·C₁²·ε⁶`, `H₀ = 2`. -/
theorem hsq_holds3 (eps : ℚ) (heps : 0 < eps) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∑ n ∈ primeWindow eps H + primeWindow eps H,
        (C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) ^ 2
        ≤ C * (H : ℝ) ^ 3 / (Real.log H) ^ 4 := by
  obtain ⟨K, hKpos, hKall⟩ := hFac2_lcm_sum_le
  simp only [sTrunc2_eq_sTruncW]
  exact hsq_holds_gen' eps heps C₁ hC₁ hFac2 (fun d _ hodd => hFac2_nonneg hodd) K hKpos hKall

/-! ## Deliverable 2 — the ungated `hpt`

The large-`H` core (sieve + rpow seam), then the crude small-`H` absorption. -/

/-- `(H^(1/10))^8 = H^(4/5)` — the rpow bookkeeping of the error term. -/
private lemma rpow_tenth_pow8' (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 10 : ℝ)) ^ 8 = x ^ (4 / 5 : ℝ) := by
  rw [← Real.rpow_natCast (x ^ (1 / 10 : ℝ)) 8, ← Real.rpow_mul hx]; norm_num

/-- `(H^(1/20))^2 = H^(1/10)`. -/
private lemma rpow_twentieth_sq' (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 20 : ℝ)) ^ 2 = x ^ (1 / 10 : ℝ) := by
  rw [← Real.rpow_natCast (x ^ (1 / 20 : ℝ)) 2, ← Real.rpow_mul hx]; norm_num

/-- **The large-`H` core of `hpt`.**  For `H` above an `ε`-threshold `H₁`, the
representation count is bounded by `C₁·(ε²H/log²H)·sTrunc2 n` for ALL `n`: odd
targets vanish (window all odd once `4 ≤ ε²H`), out-of-range targets vanish, and
even in-range targets land the Selberg sieve core (`repCount_even_le_primorial`)
at `z = ⌊H^(1/10)⌋₊`, with `log z ≥ (1/20)log H` (`M5BigO.logZ_ge`) taming the
main term and `(z²+1)⁴ ≤ 256 H^(4/5)` the error. -/
theorem hpt_large (eps : ℚ) (heps : 0 < eps) (heps2 : (eps : ℝ) ^ 2 < 1 / 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H : ℕ, H₁ ≤ H → ∀ n : ℕ,
      (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
        ≤ C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hepsq : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  obtain ⟨c₀, hc₀, z₀, hsieve⟩ := repCount_even_le_primorial
  obtain ⟨tB, htB⟩ := rpow_ge_threshold (z₀ : ℝ) (1 / 10) (by norm_num)
  obtain ⟨tD, htD⟩ := rpow_ge_threshold (2 / (eps : ℝ) ^ 2) (9 / 10) (by norm_num)
  obtain ⟨tA, htA⟩ := four_le_threshold eps heps
  refine ⟨800 / c₀ + 102400 / (eps : ℝ) ^ 2, by positivity,
    max Salt.M5BigO.N0 (max tA (max tB tD)), ?_, ?_⟩
  · -- 2 ≤ H₁
    have : (2 : ℕ) ≤ Salt.M5BigO.N0 := by unfold Salt.M5BigO.N0; norm_num
    exact le_trans this (le_max_left _ _)
  intro H hH n
  simp only [max_le_iff] at hH
  obtain ⟨hHN0, hHtA, hHtB, hHtD⟩ := hH
  -- Basic facts about H.
  have hH2 : 2 ≤ H := by unfold Salt.M5BigO.N0 at hHN0; omega
  have hHpos : 0 < H := by omega
  have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : 1 ≤ H)
  have hHposR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hHpos
  have hlogH : (0 : ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hLnn : (0 : ℝ) ≤ Real.log H := hlogH.le
  -- The frozen main-term coefficient is nonnegative.
  have hfrac_nonneg : (0 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  have hCLnn : (0 : ℝ) ≤ 800 / c₀ + 102400 / (eps : ℝ) ^ 2 := by positivity
  -- The window is all odd, and `4 ≤ ε²H`.
  have hAcond : 4 ≤ eps ^ 2 * (H : ℚ) := htA H hHtA
  -- The truncation `z := ⌊H^(1/10)⌋₊` and its threshold facts.
  set z := Salt.M5Assembly.z H with hzdef
  have hzB : z₀ ≤ z := by rw [hzdef]; exact Nat.le_floor (htB H hHtB)
  have hz100 : Salt.M3Assembly.z0 ≤ z := Salt.M5BigO.zN_ge_z0 hHN0
  have hz2 : 2 ≤ z := by unfold Salt.M3Assembly.z0 at hz100; omega
  have hzR_le : (z : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := by
    rw [hzdef]; exact Nat.floor_le (by positivity)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  -- Window primes exceed `z` (from `z ≤ H^(1/10) ≤ ε²H/2 < p`).
  have hz_le_half : (z : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 := by
    have hD : 2 / (eps : ℝ) ^ 2 ≤ (H : ℝ) ^ (9 / 10 : ℝ) := htD H hHtD
    have hmul : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ (9 / 10 : ℝ) := by
      rw [div_le_iff₀ hepsq] at hD; linarith [hD, mul_comm ((H : ℝ) ^ (9 / 10 : ℝ)) ((eps : ℝ) ^ 2)]
    have hsplit : (H : ℝ) ^ (9 / 10 : ℝ) * (H : ℝ) ^ (1 / 10 : ℝ) = (H : ℝ) := by
      rw [← Real.rpow_add hHposR]; norm_num
    have h10nn : (0 : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := by positivity
    -- 2·H^(1/10) ≤ ε²·H^(9/10)·H^(1/10) = ε²·H
    have hstep : 2 * (H : ℝ) ^ (1 / 10 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
      calc 2 * (H : ℝ) ^ (1 / 10 : ℝ)
          ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ (9 / 10 : ℝ) * (H : ℝ) ^ (1 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_right hmul h10nn
        _ = (eps : ℝ) ^ 2 * (H : ℝ) := by rw [mul_assoc, hsplit]
    have : (z : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := hzR_le
    linarith
  have hzwin : ∀ p ∈ primeWindow eps H, z < p := by
    intro p hp
    have hpmem := mem_primeWindow.mp hp
    have hplt : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (p : ℝ) := by
      have := hpmem.2.2
      have hcast : ((eps ^ 2 * (H : ℚ) / 2 : ℚ) : ℝ) < ((p : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at hcast; linarith [hcast]
    have : (z : ℝ) < (p : ℝ) := lt_of_le_of_lt hz_le_half hplt
    exact_mod_cast this
  -- The key rpow comparisons (reused across the branches).
  have hLzsq : (Real.log H) ^ 2 / 400 ≤ (Real.log z) ^ 2 := by
    have hE : (1 / 20 : ℝ) * Real.log H ≤ Real.log z := by
      rw [hzdef]; exact Salt.M5BigO.logZ_ge hHN0
    have h0 : (0 : ℝ) ≤ (1 / 20 : ℝ) * Real.log H := mul_nonneg (by norm_num) hLnn
    have := pow_le_pow_left₀ h0 hE 2
    calc (Real.log H) ^ 2 / 400 = ((1 / 20 : ℝ) * Real.log H) ^ 2 := by ring
      _ ≤ (Real.log z) ^ 2 := this
  -- The `n`-case analysis.
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [repCount_zero_target, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hCLnn hfrac_nonneg) (sTrunc2_nonneg 0)
  · by_cases hpar : Odd n
    · -- odd `n`: the window is all odd, so no representation exists
      have hodd_win : ∀ p ∈ primeWindow eps H, Odd p := fun p hp =>
        primeWindow_odd_of_four_le hAcond hp
      rw [repCount_eq_zero_of_window_odd hodd_win hpar, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg hCLnn hfrac_nonneg) (sTrunc2_nonneg n)
    · -- even `n`
      have hne2 : 2 ∣ n := (Nat.not_odd_iff_even.mp hpar).two_dvd
      by_cases hrange : n ≤ 2 * ⌊eps ^ 2 * (H : ℚ)⌋₊
      · -- in range: the Selberg sieve core
        have hsb := hsieve eps H n hne2 hn0 z hzB hz2 hzwin
        -- `n ≤ 2 ε²H`
        have hn2 : (n : ℝ) ≤ 2 * (eps : ℝ) ^ 2 * (H : ℝ) := by
          have hfloor : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
            have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
            calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
                = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
              _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
              _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
          have hcast : (n : ℝ) ≤ 2 * ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hrange
          linarith
        -- T1: the main term
        have hnum : (n : ℝ) * sTrunc2 n ≤ 2 * (eps : ℝ) ^ 2 * (H : ℝ) * sTrunc2 n :=
          mul_le_mul_of_nonneg_right hn2 (sTrunc2_nonneg n)
        have hden : c₀ * ((Real.log H) ^ 2 / 400) ≤ c₀ * (Real.log z) ^ 2 :=
          mul_le_mul_of_nonneg_left hLzsq hc₀.le
        have hdpos : (0 : ℝ) < c₀ * ((Real.log H) ^ 2 / 400) :=
          mul_pos hc₀ (div_pos (pow_pos hlogH 2) (by norm_num))
        have hinv : 1 / (c₀ * (Real.log z) ^ 2) ≤ 1 / (c₀ * ((Real.log H) ^ 2 / 400)) :=
          one_div_le_one_div_of_le hdpos hden
        have hnn_nsT : (0 : ℝ) ≤ (n : ℝ) * sTrunc2 n :=
          mul_nonneg (Nat.cast_nonneg n) (sTrunc2_nonneg n)
        have hc₀ne : c₀ ≠ 0 := hc₀.ne'
        have hLsq_ne : (Real.log H) ^ 2 ≠ 0 := (pow_pos hlogH 2).ne'
        have hT1 : (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2)
            ≤ 800 / c₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n := by
          calc (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2)
              = ((n : ℝ) * sTrunc2 n) * (1 / (c₀ * (Real.log z) ^ 2)) := by ring
            _ ≤ ((n : ℝ) * sTrunc2 n) * (1 / (c₀ * ((Real.log H) ^ 2 / 400))) :=
                mul_le_mul_of_nonneg_left hinv hnn_nsT
            _ ≤ (2 * (eps : ℝ) ^ 2 * (H : ℝ) * sTrunc2 n)
                  * (1 / (c₀ * ((Real.log H) ^ 2 / 400))) :=
                mul_le_mul_of_nonneg_right hnum (by positivity)
            _ = 800 / c₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n := by
                field_simp; ring
        -- T2: the error term
        have hzp1 : (z : ℝ) + 1 ≤ 2 * (H : ℝ) ^ (1 / 10 : ℝ) := by
          have h1 : (1 : ℝ) ≤ (H : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hH1R (by norm_num)
          linarith [hzR_le, h1]
        have hcast_z : ((z ^ 2 + 1 : ℕ) : ℝ) ≤ ((z : ℝ) + 1) ^ 2 := by
          push_cast; nlinarith [(Nat.cast_nonneg z : (0 : ℝ) ≤ (z : ℝ))]
        have hT2a : ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 ≤ 256 * (H : ℝ) ^ (4 / 5 : ℝ) := by
          calc ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4
              ≤ (((z : ℝ) + 1) ^ 2) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcast_z 4
            _ = ((z : ℝ) + 1) ^ 8 := by ring
            _ ≤ (2 * (H : ℝ) ^ (1 / 10 : ℝ)) ^ 8 := pow_le_pow_left₀ (by positivity) hzp1 8
            _ = 256 * ((H : ℝ) ^ (1 / 10 : ℝ)) ^ 8 := by rw [mul_pow]; norm_num
            _ = 256 * (H : ℝ) ^ (4 / 5 : ℝ) := by
                rw [rpow_tenth_pow8' (H : ℝ) (Nat.cast_nonneg H)]
        have hlog_le : Real.log H ≤ 20 * (H : ℝ) ^ (1 / 20 : ℝ) := by
          have h1 : Real.log ((H : ℝ) ^ (1 / 20 : ℝ)) ≤ (H : ℝ) ^ (1 / 20 : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          rw [Real.log_rpow hHposR] at h1
          linarith [h1]
        have hlogsq : (Real.log H) ^ 2 ≤ 400 * (H : ℝ) ^ (1 / 10 : ℝ) := by
          have hmul := mul_le_mul hlog_le hlog_le hLnn (by positivity)
          calc (Real.log H) ^ 2 = Real.log H * Real.log H := by ring
            _ ≤ (20 * (H : ℝ) ^ (1 / 20 : ℝ)) * (20 * (H : ℝ) ^ (1 / 20 : ℝ)) := hmul
            _ = 400 * ((H : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by ring
            _ = 400 * (H : ℝ) ^ (1 / 10 : ℝ) := by
                rw [rpow_twentieth_sq' (H : ℝ) (Nat.cast_nonneg H)]
        have hlogsq2 : (Real.log H) ^ 2 ≤ 400 * (H : ℝ) ^ (1 / 5 : ℝ) := by
          refine le_trans hlogsq ?_
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 400)
          exact Real.rpow_le_rpow_of_exponent_le hH1R (by norm_num)
        have hT2b : 256 * (H : ℝ) ^ (4 / 5 : ℝ) ≤ 102400 * (H : ℝ) / (Real.log H) ^ 2 := by
          rw [le_div_iff₀ (pow_pos hlogH 2)]
          calc 256 * (H : ℝ) ^ (4 / 5 : ℝ) * (Real.log H) ^ 2
              ≤ 256 * (H : ℝ) ^ (4 / 5 : ℝ) * (400 * (H : ℝ) ^ (1 / 5 : ℝ)) :=
                mul_le_mul_of_nonneg_left hlogsq2 (by positivity)
            _ = 102400 * ((H : ℝ) ^ (4 / 5 : ℝ) * (H : ℝ) ^ (1 / 5 : ℝ)) := by ring
            _ = 102400 * (H : ℝ) := by
                rw [← Real.rpow_add hHposR, show (4 / 5 : ℝ) + 1 / 5 = 1 by norm_num,
                  Real.rpow_one]
        have hT2c : 102400 * (H : ℝ) / (Real.log H) ^ 2
            = 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) := by
          field_simp
        have hT2 : ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4
            ≤ 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2)
                * sTrunc2 n := by
          calc ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4
              ≤ 256 * (H : ℝ) ^ (4 / 5 : ℝ) := hT2a
            _ ≤ 102400 * (H : ℝ) / (Real.log H) ^ 2 := hT2b
            _ = 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) := hT2c
            _ ≤ 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2)
                  * sTrunc2 n :=
                le_mul_of_one_le_right (by positivity) (one_le_sTrunc2 hn0)
        -- combine
        calc (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
            ≤ (n : ℝ) * sTrunc2 n / (c₀ * (Real.log z) ^ 2) + ((z ^ 2 + 1 : ℕ) : ℝ) ^ 4 := hsb
          _ ≤ 800 / c₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n
              + 102400 / (eps : ℝ) ^ 2 * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2)
                  * sTrunc2 n := add_le_add hT1 hT2
          _ = (800 / c₀ + 102400 / (eps : ℝ) ^ 2)
              * ((eps : ℝ) ^ 2 * (H : ℝ) / (Real.log H) ^ 2) * sTrunc2 n := by ring
      · -- out of range: no representation exists
        rw [repCount_eq_zero_of_large (by omega), Nat.cast_zero]
        exact mul_nonneg (mul_nonneg hCLnn hfrac_nonneg) (sTrunc2_nonneg n)

/-- **Deliverable 2 — the ungated `hpt`** at the re-frozen `rbound`
`C₁·(ε²H/log²H)·sTrunc2 n` (no parity split, no `H`-gate, no `n`-gate).  Combines
the large-`H` core `hpt_large` with a crude `card²` absorption below the threshold
`H₁(ε)`: the degenerate cells (`n = 0`, `H ∈ {0,1}` — the empty window) close by
`repCount = 0`, and `2 ≤ H < H₁` absorbs into `C₁` via `repCount ≤ |𝒫_H|²` and
`1 ≤ sTrunc2 n`. -/
theorem hpt_holds (eps : ℚ) (heps : 0 < eps) (heps2 : (eps : ℝ) ^ 2 < 1 / 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ H n : ℕ,
      (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
        ≤ C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
  obtain ⟨CL, hCL, H₁, hH₁2, hlarge⟩ := hpt_large eps heps heps2
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hepsq : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  have heps2Q : eps ^ 2 < 1 / 2 := by
    have h : ((eps ^ 2 : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith [heps2]
    exact_mod_cast h
  have hlogH₁ : (0 : ℝ) < Real.log H₁ := Real.log_pos (by exact_mod_cast (by omega : 1 < H₁))
  set CS := ((eps : ℝ) ^ 2 * H₁ + 1) ^ 2 * (Real.log H₁) ^ 2 / (2 * (eps : ℝ) ^ 2) with hCSdef
  have hCSnn : (0 : ℝ) ≤ CS := by rw [hCSdef]; positivity
  refine ⟨CL + CS, add_pos_of_pos_of_nonneg hCL hCSnn, fun H n => ?_⟩
  have hfrac_nonneg : (0 : ℝ) ≤ (eps : ℝ) ^ 2 * H / (Real.log H) ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  have hF_nonneg : (0 : ℝ) ≤ ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n :=
    mul_nonneg hfrac_nonneg (sTrunc2_nonneg n)
  by_cases hHge : H₁ ≤ H
  · -- large-`H` branch: scale `CL` up to `CL + CS`
    refine le_trans (hlarge H hHge n) ?_
    calc CL * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n
        = CL * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) := by ring
      _ ≤ (CL + CS) * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :=
          mul_le_mul_of_nonneg_right (by linarith) hF_nonneg
      _ = (CL + CS) * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by ring
  · -- small-`H` branch: `H < H₁`
    have hsmall : (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
        ≤ CS * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by
      rcases eq_or_ne n 0 with rfl | hn0
      · rw [repCount_zero_target, Nat.cast_zero]
        exact mul_nonneg (mul_nonneg hCSnn hfrac_nonneg) (sTrunc2_nonneg 0)
      · rcases Nat.lt_or_ge H 2 with hH1 | hH2
        · -- `H ∈ {0,1}`: the window is empty
          have hHle1 : (H : ℚ) ≤ 1 := by exact_mod_cast (by omega : H ≤ 1)
          have hlt2 : eps ^ 2 * (H : ℚ) < 2 := by
            have hle := mul_le_of_le_one_right (sq_nonneg eps) hHle1
            linarith [hle, heps2Q]
          have hempty : primeWindow eps H = ∅ := primeWindow_eq_empty_of_lt_two hlt2
          rw [repCount_eq_zero_of_empty hempty, Nat.cast_zero]
          exact mul_nonneg (mul_nonneg hCSnn hfrac_nonneg) (sTrunc2_nonneg n)
        · -- `2 ≤ H < H₁`: crude `card²`
          have hlogH : (0 : ℝ) < Real.log H := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
          have hHge2R : (2 : ℝ) ≤ H := by exact_mod_cast hH2
          have hcard_le : ((primeWindow eps H).card : ℝ) ≤ (eps : ℝ) ^ 2 * H₁ + 1 := by
            have h1 : (primeWindow eps H).card ≤ ⌊eps ^ 2 * (H : ℚ)⌋₊ + 1 :=
              primeWindow_card_le eps H
            have hfloor : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
              have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
              calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
                  = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
                _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
                _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
            have hHH₁ : (H : ℝ) ≤ (H₁ : ℝ) := by exact_mod_cast (by omega : H ≤ H₁)
            have h2 : (eps : ℝ) ^ 2 * (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H₁ : ℝ) :=
              mul_le_mul_of_nonneg_left hHH₁ (sq_nonneg _)
            have h3 : ((primeWindow eps H).card : ℝ) ≤ ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by
              exact_mod_cast h1
            linarith
          have hrep_le : (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
              ≤ ((eps : ℝ) ^ 2 * H₁ + 1) ^ 2 := by
            have hcs : (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
                ≤ ((primeWindow eps H).card : ℝ) ^ 2 := by
              have hle := repCount_le_card_mul (primeWindow eps H) (primeWindow eps H) n
              calc (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
                  ≤ (((primeWindow eps H).card * (primeWindow eps H).card : ℕ) : ℝ) := by
                    exact_mod_cast hle
                _ = ((primeWindow eps H).card : ℝ) ^ 2 := by push_cast; ring
            exact le_trans hcs (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard_le 2)
          have hlogmono : (Real.log H) ^ 2 ≤ (Real.log H₁) ^ 2 := by
            apply pow_le_pow_left₀ hlogH.le
            exact Real.log_le_log (by exact_mod_cast (show 0 < H by omega))
              (by exact_mod_cast (show H ≤ H₁ by omega))
          have hbracket : (0 : ℝ) ≤ (H : ℝ) * (Real.log H₁) ^ 2 - 2 * (Real.log H) ^ 2 := by
            nlinarith [hlogmono, sq_nonneg (Real.log H₁), hHge2R]
          have hfrac_ge : 2 * (eps : ℝ) ^ 2 / (Real.log H₁) ^ 2
              ≤ (eps : ℝ) ^ 2 * H / (Real.log H) ^ 2 := by
            rw [div_le_div_iff₀ (pow_pos hlogH₁ 2) (pow_pos hlogH 2)]
            nlinarith [mul_nonneg (sq_nonneg (eps : ℝ)) hbracket]
          have h2eps_pos : (0 : ℝ) < 2 * (eps : ℝ) ^ 2 := by linarith [hepsq]
          have hstep_eq : ((eps : ℝ) ^ 2 * H₁ + 1) ^ 2
              = CS * (2 * (eps : ℝ) ^ 2 / (Real.log H₁) ^ 2) := by
            rw [hCSdef]; field_simp [h2eps_pos.ne', (pow_pos hlogH₁ 2).ne']
          calc (repCount (primeWindow eps H) (primeWindow eps H) n : ℝ)
              ≤ ((eps : ℝ) ^ 2 * H₁ + 1) ^ 2 := hrep_le
            _ = CS * (2 * (eps : ℝ) ^ 2 / (Real.log H₁) ^ 2) := hstep_eq
            _ ≤ CS * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) :=
                mul_le_mul_of_nonneg_left hfrac_ge hCSnn
            _ ≤ CS * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n :=
                le_mul_of_one_le_right (mul_nonneg hCSnn hfrac_nonneg) (one_le_sTrunc2 hn0)
    refine le_trans hsmall ?_
    calc CS * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n
        = CS * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) := by ring
      _ ≤ (CL + CS) * (((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n) :=
          mul_le_mul_of_nonneg_right (by linarith) hF_nonneg
      _ = (CL + CS) * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n := by ring

/-! ## Deliverable 3 — the unconditional large-spectrum bound (Tao Lemma 3.5) -/

/-- **`bigXi_bounded` — THE unconditional `|Ξ_H|` bound.**  Compose the
sieve-parametric `bigXi_bounded_of_sieve` (L35-ASM) with the two now-real sieve
residuals: `hpt_holds` (the Goldbach upper sieve at the re-frozen `rbound`) and
`hsq_holds3` (the squared-main-term second moment at the same `rbound`).  No sieve
hypotheses remain: the number of large-spectrum frequencies `|Ξ_H|` is bounded by
an `H`-independent constant `C(ε)`.  This is Lemma 3.5 of the log-Chowla spine,
made REAL. -/
theorem bigXi_bounded (eps : ℚ) (heps : 0 < eps) (heps2 : (eps : ℝ) ^ 2 < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXi eps H).card : ℝ) ≤ C := by
  obtain ⟨C₁, hC₁, hpt⟩ := hpt_holds eps heps heps2
  exact bigXi_bounded_of_sieve eps heps heps2
    (fun H n => C₁ * ((eps : ℝ) ^ 2 * H / (Real.log H) ^ 2) * sTrunc2 n)
    hpt (hsq_holds3 eps heps C₁ hC₁)

end Salt.Entropy.Chowla
