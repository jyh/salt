/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The two-scale main-term carriers (Tao arXiv:1509.05422v2 §2, Prop 2.6), nodes W3-F-G1/G2

The h211 main-term identification (`docs/exploration/s3-a3-design.md`, the
`W3-F-G-R0 ADJUDICATED` route) collapses the residue-gated Liouville
correlation onto the base window in two moves:

1. **`perPair_collapse` (G1, class B) — collapse BEFORE dilate.**  On the
   residue class `{n : n % p = r}` with `r ≡ −(j+1) [MOD p]` (so `p ∣ r+j+1`),
   the gated summand `λ(n+j+1)·λ(n+j+p+1)` factors exactly through the
   dilation: writing `n = p·m + r` sends it to `λ(m+k)·λ(m+k+1)` at the
   collapsed offset `k = (r+j+1)/p`, using only `λ(p)² = 1` (no primality).
   Composing with the landed `dilation_error_div` (`q := p`, `r := r`) yields
   the `1/p·(image correlation) ± 2r/p²/Z` reduction.

2. **`dilated_window_stability` (G2, class C) — the two-scale edge lemma.**
   The dilated image window `((x/ω,x] ∩ {≡r}).image (·/p)` and the base window
   `(x/ω, x]` differ by two harmonic strips of mass `≤ log p + 3` each (an
   overlap that cancels exactly plus a low strip `≈ (x/pω, x/ω]` and a high
   strip `≈ (x/p, x]`).  For any bounded `g`, the two window averages of
   `g(m)/m` therefore agree up to `(2·log p + 6)/Z`.

Assembly node `W3-F-A` chains G1 then G2 at `g m := λ(m+k)·λ(m+k+1)`, so the
per-pair defect is `[2r/p² + (2·log p + 6)/p]/Z`; the residual `k → 0` offset
reduction is `corr_shift_le`'s job, downstream.
-/
import Salt.Entropy.Chowla.Dilation
import Salt.Entropy.Chowla.LogMeasure
import Mathlib

namespace Salt.Entropy.Chowla

open scoped BigOperators

/-- `|λ(k)| ≤ 1` for the real-cast Liouville value (mirrors ShiftCorr's private form). -/
private lemma abs_liou_le (k : ℕ) : |(ArithmeticFunction.liouville k : ℝ)| ≤ 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [ArithmeticFunction.liouville_apply hk]; push_cast; simp [abs_pow]

/-- `λ(p)² = 1` for `p ≠ 0`: the alphabet of `λ` on positives is `{±1}`. -/
private lemma liouville_sq {p : ℕ} (hp : p ≠ 0) :
    (ArithmeticFunction.liouville p : ℝ) ^ 2 = 1 := by
  rw [ArithmeticFunction.liouville_apply hp]; push_cast
  rw [← pow_mul]
  exact Even.neg_one_pow ⟨ArithmeticFunction.cardFactors p, by ring⟩

/-- **The collapse identity.**  For `p ≠ 0`, `λ(p·N)·λ(p·N+p) = λ(N)·λ(N+1)`.
Both arguments carry the factor `p`; `λ(p)² = 1` erases it. -/
private lemma collapse_identity {p : ℕ} (hp : p ≠ 0) (N : ℕ) :
    (ArithmeticFunction.liouville (p * N) : ℝ)
        * (ArithmeticFunction.liouville (p * N + p) : ℝ)
      = (ArithmeticFunction.liouville N : ℝ)
          * (ArithmeticFunction.liouville (N + 1) : ℝ) := by
  have hpN : p * N + p = p * (N + 1) := by ring
  rw [hpN, ArithmeticFunction.liouville_apply_mul, ArithmeticFunction.liouville_apply_mul]
  have hsq := liouville_sq hp
  push_cast
  linear_combination (ArithmeticFunction.liouville N : ℝ)
    * (ArithmeticFunction.liouville (N + 1) : ℝ) * hsq

/-- **W3-F-G1 (`perPair_collapse`, class B).**  Collapse before dilate.  On the residue
class `{n : n % p = r}` with `p ∣ r+j+1` (i.e. `r ≡ −(j+1) [MOD p]`), the gated Liouville
correlation `λ(n+j+1)·λ(n+j+p+1)` reduces, via the landed `dilation_error_div`, to
`1/p` times the *clean* correlation `λ(m+k)·λ(m+k+1)` at the collapsed offset
`k = (r+j+1)/p` summed over the dilated image window, up to the `2r/p²/Z` dilation defect. -/
theorem perPair_collapse {x ω p r j : ℕ} (hp : 1 ≤ p) (hr : r ≤ x / ω)
    (hdvd : p ∣ (r + j + 1)) {Z : ℝ} (hZ : 0 < Z) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (n + j + p + 1) : ℝ) / (n : ℝ)) / Z
       - 1 / (p : ℝ) *
         ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
            (ArithmeticFunction.liouville (m + (r + j + 1) / p) : ℝ)
              * (ArithmeticFunction.liouville (m + (r + j + 1) / p + 1) : ℝ) / (m : ℝ)) / Z)|
      ≤ 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z := by
  set k := (r + j + 1) / p with hk
  have hpk : r + j + 1 = p * k := (Nat.mul_div_cancel' hdvd).symm
  have hM : ∀ n : ℕ, |(ArithmeticFunction.liouville (n + j + 1) : ℝ)
      * (ArithmeticFunction.liouville (n + j + p + 1) : ℝ)| ≤ 1 := fun n => by
    rw [abs_mul]
    exact mul_le_one₀ (abs_liou_le _) (abs_nonneg _) (abs_liou_le _)
  have hkey := dilation_error_div (x := x) (ω := ω) (q := p) (r := r)
    (f := fun n => (ArithmeticFunction.liouville (n + j + 1) : ℝ)
      * (ArithmeticFunction.liouville (n + j + p + 1) : ℝ)) (M := 1) hp hr hM hZ
  have hcongr : ∀ m ∈
      ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
      (ArithmeticFunction.liouville (p * m + r + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (p * m + r + j + p + 1) : ℝ) / (m : ℝ)
      = (ArithmeticFunction.liouville (m + k) : ℝ)
        * (ArithmeticFunction.liouville (m + k + 1) : ℝ) / (m : ℝ) := by
    intro m _
    have e1 : p * m + r + j + 1 = p * (m + k) := by rw [Nat.mul_add]; omega
    have e2 : p * m + r + j + p + 1 = p * (m + k) + p := by rw [Nat.mul_add]; omega
    rw [e1, e2, collapse_identity (by omega) (m + k)]
  rw [show (∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
        (ArithmeticFunction.liouville (m + k) : ℝ)
          * (ArithmeticFunction.liouville (m + k + 1) : ℝ) / (m : ℝ))
      = ∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
          (ArithmeticFunction.liouville (p * m + r + j + 1) : ℝ)
            * (ArithmeticFunction.liouville (p * m + r + j + p + 1) : ℝ) / (m : ℝ)
      from Finset.sum_congr rfl (fun m hm => (hcongr m hm).symm)]
  calc |_| ≤ 2 * 1 * (r : ℝ) / (p : ℝ) ^ 2 / Z := hkey
    _ = 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z := by ring

/-- Harmonic mass of a tail `Icc a B`: `Σ 1/m = harmonic B − harmonic (a−1) ≤ 1 + log B − log a`
for `1 ≤ a ≤ B`, via the mathlib harmonic bounds. -/
private lemma sum_Icc_inv_le {a B : ℕ} (ha : 1 ≤ a) (haB : a ≤ B) :
    ∑ m ∈ Finset.Icc a B, (m : ℝ)⁻¹ ≤ 1 + Real.log B - Real.log a := by
  have hcast : ∀ M : ℕ, (harmonic M : ℝ) = ∑ i ∈ Finset.Icc 1 M, (i : ℝ)⁻¹ :=
    fun M => by rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have key : ∑ m ∈ Finset.Icc a B, (m : ℝ)⁻¹
      = (harmonic B : ℝ) - (harmonic (a - 1) : ℝ) := by
    rw [hcast, hcast]
    have hun : Finset.Icc 1 B = Finset.Icc 1 (a - 1) ∪ Finset.Icc a B := by
      ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    rw [hun, Finset.sum_union (Finset.disjoint_left.mpr (fun n hn hn' => by
      rw [Finset.mem_Icc] at hn hn'; omega))]
    ring
  rw [key]
  have hB : (harmonic B : ℝ) ≤ 1 + Real.log B := harmonic_le_one_add_log B
  have haa : Real.log a ≤ (harmonic (a - 1) : ℝ) := by
    have h := log_add_one_le_harmonic (a - 1)
    rw [show a - 1 + 1 = a from by omega] at h
    exact_mod_cast h
  linarith

/-- A harmonic strip of ratio `≤ p` has mass `≤ log p + 3`: for `1 ≤ p`, `1 ≤ B`, and
`B ≤ p·(A+1)`, `Σ_{m ∈ Icc A B} 1/m ≤ log p + 3`.  The `+3` absorbs `1 + log 2` from the
ratio slack `(A+1)/A ≤ 2`.  This is the per-strip edge bound for the two-scale swap. -/
private lemma harmonic_Icc_le {A B p : ℕ} (hp : 1 ≤ p) (hAB : B ≤ p * (A + 1))
    (hB1 : 1 ≤ B) : ∑ m ∈ Finset.Icc A B, (m : ℝ)⁻¹ ≤ Real.log p + 3 := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB1
  rcases le_or_gt A B with hAle | hBA
  swap
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; linarith
  rcases Nat.eq_zero_or_pos A with hA0 | hApos
  · subst hA0
    have hdrop : ∑ m ∈ Finset.Icc 0 B, (m : ℝ)⁻¹
        = ∑ m ∈ Finset.Icc 1 B, (m : ℝ)⁻¹ :=
      (Finset.sum_subset (fun n hn => by rw [Finset.mem_Icc] at hn ⊢; omega)
        (fun n hn hn' => by
          rw [Finset.mem_Icc] at hn hn'
          rw [show n = 0 from by omega]; simp)).symm
    rw [hdrop]
    have hle := sum_Icc_inv_le (le_refl 1) hB1
    have hBp : (B : ℝ) ≤ p := by
      have h : B ≤ p * (0 + 1) := hAB
      exact_mod_cast (by simpa using h : B ≤ p)
    have hlogB : Real.log B ≤ Real.log p := Real.log_le_log hBR hBp
    simp only [Nat.cast_one, Real.log_one, sub_zero] at hle
    linarith
  · have hle := sum_Icc_inv_le hApos hAle
    have hA1R : (1 : ℝ) ≤ A := by exact_mod_cast hApos
    have hBp : (B : ℝ) ≤ (p : ℝ) * ((A : ℝ) + 1) := by exact_mod_cast hAB
    have hlogB : Real.log B ≤ Real.log p + Real.log ((A : ℝ) + 1) := by
      have h := Real.log_le_log hBR hBp
      rwa [Real.log_mul (by positivity) (by positivity)] at h
    have hlogA1 : Real.log ((A : ℝ) + 1) ≤ Real.log A + 1 := by
      have h2A : (A : ℝ) + 1 ≤ 2 * A := by nlinarith [hA1R]
      have hmono := Real.log_le_log (by positivity) h2A
      rw [Real.log_mul (by norm_num) (by positivity)] at hmono
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      linarith
    linarith

/-- **W3-F-G2 (`dilated_window_stability`, class C).**  The two-scale edge lemma.  The
dilated image window `((x/ω,x] ∩ {≡r}).image (·/p)` and the base window `(x/ω, x]` share
their overlap exactly; their symmetric difference is a low strip `⊆ Icc (x/ω/p) (x/ω)` and a
high strip `⊆ Icc (x/p) x`, each of harmonic mass `≤ log p + 3`.  So for any `|g| ≤ 1` the two
window sums of `g(m)/m ÷ Z` agree up to `(2·log p + 6)/Z`.  Assembly `W3-F-A` feeds
`g m := λ(m+k)·λ(m+k+1)` (the collapsed correlation from `perPair_collapse`). -/
theorem dilated_window_stability {x ω p r : ℕ} (hp : 2 ≤ p) (hrp : r < p) (hB : 1 ≤ x / ω)
    {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ 1) {Z : ℝ} (hZ : 0 < Z) :
    |(∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
         g m / (m : ℝ)) / Z
       - (∑ n ∈ Finset.Ioc (x / ω) x, g n / (n : ℝ)) / Z|
      ≤ (2 * Real.log p + 6) / Z := by
  set base := Finset.Ioc (x / ω) x with hbase
  set s := base.filter (fun n => n % p = r) with hs
  set img := s.image (fun n => n / p) with himg
  have hp0 : 0 < p := by omega
  have hp1 : 1 ≤ p := by omega
  have hx1 : 1 ≤ x := le_trans hB (Nat.div_le_self x ω)
  -- membership: m ∈ img ↔ x/ω < p·m+r ≤ x
  have hmem : ∀ m, m ∈ img ↔ x / ω < p * m + r ∧ p * m + r ≤ x := by
    intro m
    rw [himg, hs, hbase, Finset.mem_image]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h1, h2⟩, hmod⟩ := hn
      have hnp : p * (n / p) + r = n := by have := Nat.div_add_mod n p; omega
      rw [hnp]; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨p * m + r, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨h1, h2⟩, by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrp]⟩
      · rw [Nat.mul_add_div hp0, Nat.div_eq_of_lt hrp, Nat.add_zero]
  -- pointwise: |g m / m| ≤ 1/m
  have hbnd : ∀ T : Finset ℕ,
      |∑ m ∈ T, g m / (m : ℝ)| ≤ ∑ m ∈ T, (m : ℝ)⁻¹ := by
    intro T
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun m _ => ?_))
    rw [abs_div, Nat.abs_cast, div_eq_mul_inv]
    calc |g m| * (m : ℝ)⁻¹ ≤ 1 * (m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (hg m) (by positivity)
      _ = (m : ℝ)⁻¹ := one_mul _
  -- low strip ⊆ Icc (x/ω/p) (x/ω)
  have hlosub : img \ base ⊆ Finset.Icc (x / ω / p) (x / ω) := by
    intro m hm
    rw [Finset.mem_sdiff, hbase, hmem, Finset.mem_Ioc] at hm
    obtain ⟨⟨hg1, hg2⟩, hnb⟩ := hm
    have hmpm : m ≤ p * m := Nat.le_mul_of_pos_left m hp0
    have hup : m ≤ x / ω := by omega
    have hlt : x / ω < (m + 1) * p := by
      have hmul : (m + 1) * p = p * m + p := by ring
      omega
    have hlo : x / ω / p ≤ m := by
      have := (Nat.div_lt_iff_lt_mul hp0).mpr hlt; omega
    rw [Finset.mem_Icc]; exact ⟨hlo, hup⟩
  -- high strip ⊆ Icc (x/p) x
  have hhisub : base \ img ⊆ Finset.Icc (x / p) x := by
    intro m hm
    rw [Finset.mem_sdiff, hbase, Finset.mem_Ioc, hmem] at hm
    obtain ⟨⟨hg1, hg2⟩, hni⟩ := hm
    have hmpm : m ≤ p * m := Nat.le_mul_of_pos_left m hp0
    have hxlt : x < p * m + r := by omega
    have hlt : x < (m + 1) * p := by
      have hmul : (m + 1) * p = p * m + p := by ring
      omega
    have hlo : x / p ≤ m := by have := (Nat.div_lt_iff_lt_mul hp0).mpr hlt; omega
    rw [Finset.mem_Icc]; exact ⟨hlo, hg2⟩
  -- each strip's mass ≤ log p + 3
  have hloB : x / ω ≤ p * (x / ω / p + 1) := by
    have h1 := Nat.div_add_mod (x / ω) p
    have h2 := Nat.mod_lt (x / ω) hp0
    have hmul : p * (x / ω / p + 1) = p * (x / ω / p) + p := by ring
    omega
  have hhiB : x ≤ p * (x / p + 1) := by
    have h1 := Nat.div_add_mod x p
    have h2 := Nat.mod_lt x hp0
    have hmul : p * (x / p + 1) = p * (x / p) + p := by ring
    omega
  have hlomass : ∑ m ∈ img \ base, (m : ℝ)⁻¹ ≤ Real.log p + 3 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hlosub (fun i _ _ => by positivity))
      (harmonic_Icc_le hp1 hloB hB)
  have hhimass : ∑ m ∈ base \ img, (m : ℝ)⁻¹ ≤ Real.log p + 3 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hhisub (fun i _ _ => by positivity))
      (harmonic_Icc_le hp1 hhiB hx1)
  -- raw difference bound via symmetric difference
  have htri : ∀ X Y : ℝ, |X - Y| ≤ |X| + |Y| := fun X Y => by simpa using abs_sub_le X 0 Y
  have hraw : |(∑ m ∈ img, g m / (m : ℝ)) - (∑ n ∈ base, g n / (n : ℝ))|
      ≤ 2 * Real.log p + 6 := by
    have hsplit : (∑ m ∈ img, g m / (m : ℝ)) - (∑ n ∈ base, g n / (n : ℝ))
        = (∑ m ∈ img \ base, g m / (m : ℝ)) - (∑ n ∈ base \ img, g n / (n : ℝ)) :=
      (Finset.sum_sdiff_sub_sum_sdiff).symm
    rw [hsplit]
    calc |(∑ m ∈ img \ base, g m / (m : ℝ)) - (∑ n ∈ base \ img, g n / (n : ℝ))|
        ≤ |∑ m ∈ img \ base, g m / (m : ℝ)| + |∑ n ∈ base \ img, g n / (n : ℝ)| :=
          htri _ _
      _ ≤ (Real.log p + 3) + (Real.log p + 3) :=
          add_le_add (le_trans (hbnd _) hlomass) (le_trans (hbnd _) hhimass)
      _ = 2 * Real.log p + 6 := by ring
  -- divide by Z
  have halg : (∑ m ∈ img, g m / (m : ℝ)) / Z - (∑ n ∈ base, g n / (n : ℝ)) / Z
      = ((∑ m ∈ img, g m / (m : ℝ)) - (∑ n ∈ base, g n / (n : ℝ))) / Z := by ring
  rw [halg, abs_div, abs_of_pos hZ, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hraw (le_of_lt (inv_pos.mpr hZ))

end Salt.Entropy.Chowla
