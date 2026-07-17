/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# Affine/dilation invariance of the log-window sums (Tao Lemma 2.5, dilation half)

The translation half of Lemma 2.5 (the `n ↦ n + t` pushforward comparisons) is
already frozen in `Step`/`Invariance`/`ResidueUniform`. This file supplies the
new **dilation** half: reading the residue progression `{n ≡ r (mod q)}` inside
the window `(x/ω, x]` through the substitution `n = q·m + r`.

The exact reindex is `dilation_reindex` (a `Finset.sum_image` bijection along
`n ↦ n / q`, inverse `m ↦ q·m + r`). The per-term reciprocal comparison
`1/(qm+r) − 1/(qm) = −r/((qm+r)(qm))`, summed against the harmonic-square tail
`Σ 1/m² ≤ 2`, yields the explicit dilation error `≤ 2·M·r/q²`
(`dilation_error`, and its normalized division form `dilation_error_div`).

Everything here is explicit-hypothesis and regime-free (per the W1-a precedent);
the only Chowla import is `LogMeasure` (for the window normalizer downstream).
-/
import Mathlib
import Salt.Entropy.Chowla.LogMeasure

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- Telescoping harmonic-square partial-sum bound `Σ_{1≤m≤K} 1/m² ≤ 2 − 1/K`. -/
private lemma sum_Icc_inv_sq_le' :
    ∀ K : ℕ, 1 ≤ K → ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 - 1 / (K : ℝ) := by
  intro K
  induction K with
  | zero => intro h; exact absurd h (by norm_num)
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one]
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ n + 1)]
      have hih := ih hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
      have hn1ne : (n : ℝ) + 1 ≠ 0 := by positivity
      have hid : (1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [div_sub_div _ _ hnne hn1ne]; ring
      have hkey : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [hid]
        exact one_div_le_one_div_of_le (mul_pos hnR (by positivity)) (by nlinarith [hnR])
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [hih, hkey]

/-- Harmonic-square partial-sum bound `Σ_{1≤m≤K} 1/m² ≤ 2`. -/
private lemma sum_Icc_inv_sq_le (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]; norm_num
  · have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    linarith [sum_Icc_inv_sq_le' K hK, one_div_pos.mpr hKR]

/-- Per-term dilation comparison: for `m ≥ 1`, `q ≥ 1`, `|c| ≤ M`,
    `|c/(qm+r) − (1/q)·(c/m)| ≤ M·r/(q²m²)` (from `1/(qm+r) − 1/(qm) = −r/((qm+r)(qm))`). -/
private lemma dilation_term_bound {q r m : ℕ} (hq : 1 ≤ q) (hm : 1 ≤ m)
    {c M : ℝ} (hc : |c| ≤ M) :
    |c / ((q * m + r : ℕ) : ℝ) - 1 / (q : ℝ) * (c / (m : ℝ))|
      ≤ M * (r : ℝ) / ((q : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hMnn : (0 : ℝ) ≤ M := le_trans (abs_nonneg c) hc
  set A : ℝ := (q : ℝ) * m with hAdef
  have hA : 0 < A := mul_pos hqR hmR
  have hAne : A ≠ 0 := ne_of_gt hA
  have hABpos : (0 : ℝ) < A + r := by linarith
  have hBcast : ((q * m + r : ℕ) : ℝ) = A + r := by rw [hAdef]; push_cast; ring
  have hCA : 1 / (q : ℝ) * (c / (m : ℝ)) = c / A := by rw [hAdef, div_mul_div_comm, one_mul]
  have hA2 : (q : ℝ) ^ 2 * (m : ℝ) ^ 2 = A ^ 2 := by rw [hAdef]; ring
  rw [hBcast, hCA, hA2]
  have hdiff : c / (A + r) - c / A = -(c * r) / ((A + r) * A) := by
    rw [div_sub_div _ _ (ne_of_gt hABpos) hAne]; ring
  rw [hdiff, abs_div, abs_neg, abs_mul, abs_of_nonneg hrR, abs_of_pos (mul_pos hABpos hA),
    div_le_div_iff₀ (mul_pos hABpos hA) (pow_pos hA 2)]
  nlinarith [mul_nonneg (mul_nonneg hrR hA.le) (mul_nonneg (sub_nonneg.mpr hc) hA.le),
    mul_nonneg (mul_nonneg hrR hA.le) (mul_nonneg hMnn hrR)]

/-- The dilation reindex bijection: on any residue set `s ⊆ {n : n % q = r}`, the map
    `n ↦ n / q` (inverse `m ↦ q·m + r`) reindexes `Σ_{n∈s} F n = Σ_{m∈s.image(·/q)} F (qm+r)`. -/
theorem dilation_reindex (q r : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n % q = r) (F : ℕ → ℝ) :
    ∑ m ∈ s.image (fun n => n / q), F (q * m + r) = ∑ n ∈ s, F n := by
  rw [Finset.sum_image (fun a ha b hb hab => by
    have hqab : q * (a / q) = q * (b / q) := by rw [hab]
    have hda := Nat.div_add_mod a q
    have hdb := Nat.div_add_mod b q
    have hma := hs a ha
    have hmb := hs b hb
    omega)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hd := Nat.div_add_mod n q
  have hr := hs n hn
  have heq : q * (n / q) + r = n := by omega
  rw [heq]

/-- The dilation identity with explicit error. For `q ≥ 1`, `r ≤ x/ω` (so the residue class
    sits strictly inside the window and every dilated index is `≥ 1`), and `f` bounded by `M`:
    `|Σ_{n≡r(q)} f n/n − (1/q)·Σ_m f(qm+r)/m| ≤ 2·M·r/q²`. The dilated sum ranges over the
    image window `((x/ω,x] ∩ {≡r}).image (·/q)`; the error is the harmonic-square tail
    `Σ 1/m² ≤ 2` weighted by the per-term defect `r/(q²m²)`. -/
theorem dilation_error {x ω q r : ℕ} (hq : 1 ≤ q) (hr : r ≤ x / ω)
    {f : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |f n| ≤ M) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % q = r), f n / (n : ℝ))
        - 1 / (q : ℝ) *
          (∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % q = r)).image (fun n => n / q),
            f (q * m + r) / (m : ℝ))|
      ≤ 2 * M * (r : ℝ) / (q : ℝ) ^ 2 := by
  set s := (Finset.Ioc (x / ω) x).filter (fun n => n % q = r) with hsdef
  set T := s.image (fun n => n / q) with hTdef
  have hMnn : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hTmem : ∀ m ∈ T, 1 ≤ m := by
    intro m hm
    rw [hTdef, Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    rw [hsdef, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hlt, _hle⟩, hmod⟩ := hn
    have hnr : r < n := lt_of_le_of_lt hr hlt
    have hdm := Nat.div_add_mod n q
    have hpos : 0 < q * (n / q) := by omega
    exact Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hTsub : T ⊆ Finset.Icc 1 (x / q) := by
    intro m hm
    rw [Finset.mem_Icc]
    refine ⟨hTmem m hm, ?_⟩
    rw [hTdef, Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    rw [hsdef, Finset.mem_filter, Finset.mem_Ioc] at hn
    exact Nat.div_le_div_right hn.1.2
  have hreindex : ∑ m ∈ T, f (q * m + r) / ((q * m + r : ℕ) : ℝ) = ∑ n ∈ s, f n / (n : ℝ) := by
    have := dilation_reindex q r s
      (fun n hn => by rw [hsdef, Finset.mem_filter] at hn; exact hn.2) (fun n => f n / (n : ℝ))
    rw [hTdef]; exact this
  rw [← hreindex, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hcoef : (0 : ℝ) ≤ M * (r : ℝ) / (q : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg hMnn (Nat.cast_nonneg r)) (by positivity)
  refine le_trans (Finset.sum_le_sum
    (fun m hm => dilation_term_bound hq (hTmem m hm) (hM (q * m + r)))) ?_
  have hfact : ∑ m ∈ T, M * (r : ℝ) / ((q : ℝ) ^ 2 * (m : ℝ) ^ 2)
      = M * (r : ℝ) / (q : ℝ) ^ 2 * ∑ m ∈ T, (1 : ℝ) / (m : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
  have hsum2 : ∑ m ∈ T, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun i _ _ => by positivity))
      (sum_Icc_inv_sq_le (x / q))
  rw [hfact]
  calc M * (r : ℝ) / (q : ℝ) ^ 2 * ∑ m ∈ T, (1 : ℝ) / (m : ℝ) ^ 2
      ≤ M * (r : ℝ) / (q : ℝ) ^ 2 * 2 := mul_le_mul_of_nonneg_left hsum2 hcoef
    _ = 2 * M * (r : ℝ) / (q : ℝ) ^ 2 := by ring

/-- Normalized (probability) form. Dividing both window sums by any positive normalizer `Z`
    — e.g. `Z = Σ_{(x/ω,x]} 1/n`, bounded below via `harmonic_window_bounds`
    (`≥ log ω − 1`) or `logMeasure_norm_ge_half` (`≥ 1 − 1/ω`) — the dilation error scales as
    `2·M·r/q² / Z`. This is the expectation shape the F-function bridge (W2-b) consumes. -/
theorem dilation_error_div {x ω q r : ℕ} (hq : 1 ≤ q) (hr : r ≤ x / ω)
    {f : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |f n| ≤ M) {Z : ℝ} (hZ : 0 < Z) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % q = r), f n / (n : ℝ)) / Z
        - 1 / (q : ℝ) *
          ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % q = r)).image (fun n => n / q),
            f (q * m + r) / (m : ℝ)) / Z)|
      ≤ 2 * M * (r : ℝ) / (q : ℝ) ^ 2 / Z := by
  have hkey := dilation_error hq hr hM
  set A := ∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % q = r), f n / (n : ℝ) with hAdef
  set B := ∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % q = r)).image (fun n => n / q),
    f (q * m + r) / (m : ℝ) with hBdef
  have halg : A / Z - 1 / (q : ℝ) * (B / Z) = (A - 1 / (q : ℝ) * B) / Z := by ring
  rw [halg, abs_div, abs_of_pos hZ, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hkey (le_of_lt (inv_pos.mpr hZ))

end Salt.Entropy.Chowla
