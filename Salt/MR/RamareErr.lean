/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareWindows

/-!
# RamareErr — the HONEST Lemma-12 window row (hU ladder, U-2a/b/c)

`Salt.MR.RamareWindows` closes Lemma 12 unconditionally, but prices its window row by the
`t`-uniform ℓ¹ sup bound `ramWindowErr_moment_triv` (`2T·windowMass²`).  That row is
kernel-valid and analytically vacuous: `windowMass` carries no cancellation, so the row is off
MR's grade by `≈ X·H·(log X)²`.

This file lands MR p.20's ACTUAL mechanism.  Verbatim (rendered p.20, top):

> `Xe^{−(j+1)/H} ≤ m ≤ Xe^{−j/H}` we undercount at most by integers `mp` in the range
> `[Xe^{−1/H}, Xe^{1/H}]`.  Therefore we can, for some bounded `d_m`, rewrite (16) as
> `Σ_{j∈I} Q_{j,H}(s)R_{j,H}(s) + Σ_{Xe^{−1/H}≤m≤Xe^{1/H}} d_m/m^s
>   + Σ_{2X≤m≤2Xe^{1/H}} d_m/m^s + (p²-row) + (coprime tail)`.

i.e. the seam defect is collected **at the frequency level** as a Dirichlet polynomial over a
NARROW window, its coefficients are BOUNDED (`‖d_n‖ ≤ 1`, by the landed `ramare_weight_sum`),
and it is then priced by the mean-value theorem (`moment_core_bound`) — giving the
`(2T+20N)·1/(HX)` grade, i.e. the paper's `(T/X + 1)·(1/H)` row.

## The chain

* `ramSeam H N X j` — the seam window `{m ∈ [1,N] : Xe^{−(j+1)/H} ≤ m < Xe^{−j/H}}`.
* `seam_sum_identity` — **R1a**, the combinatorial core: for `p` in the block `j` and any
  coefficient function vanishing off `X ≤ pm ≤ 2X`, the honest-minus-`R_{j,H}` cofactor
  difference is EXACTLY the sum over `ramSeam H N X j`.
* `ramWindowErr_eq_seamPoly` — **R1b**, `ramWindowErr = ramSeamPoly` under `hwin`.
* `ramSeamPoly_eq_spoly` — **R1c**, the `(j,p,m) ↦ pm` frequency collapse: the seam polynomial
  is `spoly N ramSeamCoeff` — no frequency inflation, every frequency in `[Xe^{−1/H}, Xe^{1/H}]`.
* `norm_ramSeamCoeff_le_one` — **R1d**, `‖d_n‖ ≤ 1` via `ramare_weight_sum` (Decomp:119).
* `ramSeamPoly_moment` / `ramWindowErr_moment_sharp` — **R2**, the honest row
  `(2T+20N)·(2e·X/H + 1)·(e/X²)`; `ramWindowErr_moment_grade` is its `720·(T/X + 1)/H`
  normal form.
* `lemma12_meansq_sharp` — **R3**, Lemma 12 with the honest window row in place of the
  trivial-sup row (`ramWindowErr_moment_triv` is superseded, not deleted).
* `ramCopTail_eq_zero_of_blockSupport` / `lemma12_meansq_sharp_blockSupport` — **R4**, the
  coprime tail row is identically `0` under the §8.3 support pin.

## The hypothesis `hwin`, and what it costs (READ THIS)

`hwin : c p * b m ≠ 0 → X ≤ pm ≤ 2X` is MR's "`a` is supported on `[X,2X]`" transported
through the factorisation `a_{pm} = b_m c_p`.  For **coprime** `(p,m)` it is *derivable* from
`RamareWindows`' own `hcoef` plus that support — see `seam_support_of_hcoef`.  For `p ∣ m`
pairs it is a genuine extra assumption: `RamareWindows`' clean term extends the factorised
summand to ALL cofactors `m` (the `p ∣ m` overreach being repaired by the separate
`ramP2corr` row), so the seam identity needs the vanishing there too.  Without it the `p ∣ m`
part of the window error would have to be priced as a fourth row at the `p²` frequencies
(MR's `1/P` row).  This is the one recorded deviation of this file.

NOTE (a structural finding).  MR's display carries TWO seam windows,
`[Xe^{−1/H}, Xe^{1/H}]` (undercount) and `[2X, 2Xe^{1/H}]` (overcount).  Here only the first
survives: the corpus's `ramRrange` upper endpoint is exactly `2Xe^{−j/H} ≥ 2X/p`, so every
`m` that `R_{j,H}` overcounts has `pm > 2X` and its coefficient vanishes by `hwin`.  The
second window is therefore identically zero in this formalisation.

Source pins (D5): MR arXiv v4 (`1501.04585v4`), p.20 (Lemma 12's proof), rendered page.
-/

namespace Salt.MR

open Finset Complex MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## R1a — the seam window and the exact index-set identity -/

open Classical in
/-- **The seam window** at block `j` (MR p.20): `W_{j,H} = {m ∈ [1,N] : Xe^{−(j+1)/H} ≤ m <
Xe^{−j/H}}` — the cofactors that the `p`-independent range `R_{j,H}` UNDERCOUNTS, for `p` in
the dyadic block `e^{j/H} ≤ p < e^{(j+1)/H}`. -/
noncomputable def ramSeam (H : ℝ) (N X j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun m => (X : ℝ) * Real.exp (-((j : ℝ) + 1) / H) ≤ (m : ℝ) ∧
      (m : ℝ) < (X : ℝ) * Real.exp (-(j : ℝ) / H))

/-- The honest eq (16) cofactor range `{m : pm ∈ [1,N]}` is exactly the corpus's
image-filter shape (the image is redundant once `pm ∈ [1,N]`). -/
lemma mem_honest_cofactor {N p m : ℕ} (hp : 0 < p) :
    m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter (fun m => p * m ∈ Finset.Icc 1 N)
      ↔ (1 ≤ p * m ∧ p * m ≤ N) := by
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨⟨p * m, h, Nat.mul_div_cancel_left m hp⟩, h⟩

/-- Rewriting a sum over `s ⊆ [1,N]` as an indicator sum over `[1,N]` — the common frame in
which the three index sets of the seam identity are compared. -/
lemma sum_eq_icc_ite {N : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.Icc 1 N) (f : ℕ → ℂ) :
    ∑ m ∈ s, f m = ∑ m ∈ Finset.Icc 1 N, (if m ∈ s then f m else 0) := by
  classical
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hs]

/-- **R1a — the seam identity (the combinatorial core, MR p.20).**  Fix a block index `j` and a
prime `p` in the block (`e^{j/H} ≤ p < e^{(j+1)/H}`).  For ANY coefficient function `f`
vanishing off the dyadic window `X ≤ pm ≤ 2X`, the honest eq (16) cofactor sum minus the
`p`-independent `R_{j,H}` cofactor sum is EXACTLY the sum over the seam window `ramSeam`.

Two facts drive it: (i) `p ≥ e^{j/H}` forces `m ≤ 2X/p ≤ 2Xe^{−j/H}`, so `R_{j,H}`'s upper
endpoint never cuts and its overcount is empty; (ii) `p < e^{(j+1)/H}` forces
`m ≥ X/p > Xe^{−(j+1)/H}`, so the undercount is confined to the seam window. -/
theorem seam_sum_identity (H : ℝ) (N X P Q j p : ℕ)
    (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hp : p ∈ ramQblock H P Q j) (f : ℕ → ℂ)
    (hf : ∀ m : ℕ, f m ≠ 0 → (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ)) :
    (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
        (fun m => p * m ∈ Finset.Icc 1 N), f m)
      - (∑ m ∈ ramRrange H N X j, f m) = ∑ m ∈ ramSeam H N X j, f m := by
  classical
  have hp' := hp
  rw [ramQblock, Finset.mem_filter, Finset.mem_Icc] at hp'
  obtain ⟨⟨hPp, hpQ⟩, hpp, hplo, hphi⟩ := hp'
  have hp0 : 0 < p := hpp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- the three index sets all sit inside `[1,N]`
  have hAsub : ((Finset.Icc 1 N).image (fun n => n / p)).filter
      (fun m => p * m ∈ Finset.Icc 1 N) ⊆ Finset.Icc 1 N := by
    intro m hm
    rw [mem_honest_cofactor hp0] at hm
    rw [Finset.mem_Icc]
    refine ⟨?_, le_trans (Nat.le_mul_of_pos_left m hp0) hm.2⟩
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm
    · exact h
  have hBsub : ramRrange H N X j ⊆ Finset.Icc 1 N := by
    rw [ramRrange]; exact Finset.filter_subset _ _
  have hWsub : ramSeam H N X j ⊆ Finset.Icc 1 N := by
    rw [ramSeam]; exact Finset.filter_subset _ _
  rw [sum_eq_icc_ite hAsub f, sum_eq_icc_ite hBsub f, sum_eq_icc_ite hWsub f,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rcases eq_or_ne (f m) 0 with h0 | h0
  · rw [h0]; simp
  obtain ⟨hlo, hhi⟩ := hf m h0
  rw [Finset.mem_Icc] at hm
  have hm1 : 1 ≤ m := hm.1
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  -- the honest range always contains `m`
  have hA : m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
      (fun m => p * m ∈ Finset.Icc 1 N) := by
    rw [mem_honest_cofactor hp0]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp0.ne' (by omega)), ?_⟩
    have hc : ((p * m : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
    exact_mod_cast hc
  -- `R_{j,H}`'s upper endpoint never cuts: `m ≤ 2X/p ≤ 2Xe^{−j/H}`
  have hEj : (0 : ℝ) < Real.exp ((j : ℝ) / H) := Real.exp_pos _
  have hEj' : Real.exp (-(j : ℝ) / H) = (Real.exp ((j : ℝ) / H))⁻¹ := by
    rw [show (-(j : ℝ) / H) = -((j : ℝ) / H) by ring, Real.exp_neg]
  have hupper : (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H) := by
    have key : (m : ℝ) * Real.exp ((j : ℝ) / H) ≤ 2 * (X : ℝ) := by nlinarith
    rw [hEj']
    calc (m : ℝ) = ((m : ℝ) * Real.exp ((j : ℝ) / H)) * (Real.exp ((j : ℝ) / H))⁻¹ := by
          field_simp
      _ ≤ (2 * (X : ℝ)) * (Real.exp ((j : ℝ) / H))⁻¹ :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 2 * (X : ℝ) * (Real.exp ((j : ℝ) / H))⁻¹ := by ring
  -- the undercount never reaches below the seam window: `m ≥ X/p > Xe^{−(j+1)/H}`
  have hFj : (0 : ℝ) < Real.exp (((j : ℝ) + 1) / H) := Real.exp_pos _
  have hFj' : Real.exp (-((j : ℝ) + 1) / H) = (Real.exp (((j : ℝ) + 1) / H))⁻¹ := by
    rw [show (-((j : ℝ) + 1) / H) = -(((j : ℝ) + 1) / H) by ring, Real.exp_neg]
  have hlower : (X : ℝ) * Real.exp (-((j : ℝ) + 1) / H) ≤ (m : ℝ) := by
    have key : (X : ℝ) ≤ Real.exp (((j : ℝ) + 1) / H) * (m : ℝ) := by nlinarith
    rw [hFj']
    calc (X : ℝ) * (Real.exp (((j : ℝ) + 1) / H))⁻¹
        ≤ (Real.exp (((j : ℝ) + 1) / H) * (m : ℝ)) * (Real.exp (((j : ℝ) + 1) / H))⁻¹ :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = (m : ℝ) := by field_simp
  -- membership in `R_{j,H}`'s range and in the seam window are complementary
  have hBiff : m ∈ ramRrange H N X j ↔ (X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ) := by
    rw [ramRrange, Finset.mem_filter]
    exact ⟨fun h => h.2.1, fun h => ⟨Finset.mem_Icc.mpr hm, h, hupper⟩⟩
  have hWiff : m ∈ ramSeam H N X j ↔ (m : ℝ) < (X : ℝ) * Real.exp (-(j : ℝ) / H) := by
    rw [ramSeam, Finset.mem_filter]
    exact ⟨fun h => h.2.2, fun h => ⟨Finset.mem_Icc.mpr hm, hlower, h⟩⟩
  rw [if_pos hA]
  by_cases hcase : (X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ)
  · rw [if_pos (hBiff.mpr hcase), if_neg (fun h => absurd (hWiff.mp h) (not_lt.mpr hcase)),
      sub_self]
  · rw [not_le] at hcase
    rw [if_neg (fun h => absurd (hBiff.mp h) (not_le.mpr hcase)), if_pos (hWiff.mpr hcase),
      sub_zero]

/-! ## R1b — the window error as the seam polynomial -/

/-- **The seam polynomial** (MR p.20's `Σ d_m/m^s` rows, before the frequency collapse): the
block sum of `c_p/p^s` against the seam-window cofactors. -/
noncomputable def ramSeamPoly (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j, ∑ m ∈ ramSeam H N X j,
    (c p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
      ((b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) * ((blockOmega P Q m : ℂ) + 1)⁻¹)

/-- **R1b — the window error IS the seam polynomial.**  Under the dyadic-window support
`hwin` (MR's `a` supported on `[X,2X]`, transported through `a_{pm} = b_m c_p`), the corpus's
`ramWindowErr` collapses onto the narrow seam windows. -/
theorem ramWindowErr_eq_seamPoly (H : ℝ) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (b c : ℕ → ℂ)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))
    (t : ℝ) :
    ramWindowErr H N X P Q b c t = ramSeamPoly H N X P Q b c t := by
  rw [ramWindowErr, ramSeamPoly]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun p hp => ?_))
  have hp' := hp
  rw [ramQblock, Finset.mem_filter, Finset.mem_Icc] at hp'
  obtain ⟨⟨hPp, hpQ⟩, hpp, -⟩ := hp'
  rw [mul_sub, ramR, Finset.mul_sum, Finset.mul_sum]
  refine seam_sum_identity H N X P Q j p hX hN hp _ (fun m hm => ?_)
  refine hwin p m hpp hPp hpQ (fun hzero => hm ?_)
  rcases mul_eq_zero.mp hzero with h | h
  · simp [h]
  · simp [h]

/-- **The coprime half of `hwin` is free.**  MR's support (`a` vanishes off `[X,2X]`) together
with `RamareWindows`' own coefficient factorisation `hcoef` gives the `hwin` instances at
coprime pairs.  The `p ∣ m` instances are the recorded extra assumption (see the header). -/
theorem seam_support_of_hcoef (X P Q : ℕ) (a b c : ℕ → ℂ)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p) :
    ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ) := by
  intro p m hpp hPp hpQ hpm hne
  have hane : a (p * m) ≠ 0 := by
    rw [hcoef p m hpp hPp hpQ hpm, mul_comm]
    exact hne
  have h := hasupp _ hane
  push_cast at h
  exact h

/-! ## R1c — the frequency collapse `(j,p,m) ↦ pm` -/

/-- **The seam domain**: block-index/prime/cofactor triples `(j, p, m)` with `p` in the dyadic
block `j` and `m` in that block's seam window. -/
noncomputable def ramSeamDom (H : ℝ) (N X P Q : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (ramI H P Q).sigma (fun j => (ramQblock H P Q j) ×ˢ (ramSeam H N X j))

/-- **The seam coefficient `d_n`** (MR p.20's "for some bounded `d_m`"): the fiber sum of
`c_p b_m/(ω(m;P,Q)+1)` over the seam factorisations `pm = n`. -/
noncomputable def ramSeamCoeff (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ σ ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
    c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹

/-- `e^{1/2} ≤ 2` — keeps every seam frequency inside `[1,N]` for `N ≥ 2X`, `H ≥ 2`. -/
lemma exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h1 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]

/-- **The narrow window** (MR p.20): every seam frequency `n = pm` lies in
`[Xe^{−1/H}, Xe^{1/H}]` — the block bounds on `p` and the seam bounds on `m` telescope. -/
lemma ramSeamDom_frequency_window (H : ℝ) (N X P Q : ℕ)
    {σ : Σ _ : ℕ, ℕ × ℕ} (hσ : σ ∈ ramSeamDom H N X P Q) :
    (X : ℝ) * Real.exp (-(1 / H)) ≤ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ∧
      ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ (X : ℝ) * Real.exp (1 / H) := by
  rw [ramSeamDom, Finset.mem_sigma, Finset.mem_product] at hσ
  obtain ⟨-, hp, hm⟩ := hσ
  rw [ramQblock, Finset.mem_filter] at hp
  obtain ⟨-, hpp, hplo, hphi⟩ := hp
  rw [ramSeam, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hm1, -⟩, hmlo, hmhi⟩ := hm
  have hp0 : (0 : ℝ) < (σ.2.1 : ℝ) := by exact_mod_cast hpp.pos
  have hm0 : (0 : ℝ) < (σ.2.2 : ℝ) := by exact_mod_cast hm1
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hE1 : Real.exp ((σ.1 : ℝ) / H) * Real.exp (-((σ.1 : ℝ) + 1) / H)
      = Real.exp (-(1 / H)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE2 : Real.exp (((σ.1 : ℝ) + 1) / H) * Real.exp (-(σ.1 : ℝ) / H) = Real.exp (1 / H) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlo : Real.exp ((σ.1 : ℝ) / H) * ((X : ℝ) * Real.exp (-((σ.1 : ℝ) + 1) / H))
      = (X : ℝ) * Real.exp (-(1 / H)) := by
    rw [← hE1]; ring
  have hhi : Real.exp (((σ.1 : ℝ) + 1) / H) * ((X : ℝ) * Real.exp (-(σ.1 : ℝ) / H))
      = (X : ℝ) * Real.exp (1 / H) := by
    rw [← hE2]; ring
  constructor
  · have hstep : Real.exp ((σ.1 : ℝ) / H) * ((X : ℝ) * Real.exp (-((σ.1 : ℝ) + 1) / H))
        ≤ (σ.2.1 : ℝ) * (σ.2.2 : ℝ) :=
      mul_le_mul hplo hmlo (by positivity) (by positivity)
    rw [hlo] at hstep
    push_cast
    linarith
  · have hstep : (σ.2.1 : ℝ) * (σ.2.2 : ℝ)
        ≤ Real.exp (((σ.1 : ℝ) + 1) / H) * ((X : ℝ) * Real.exp (-(σ.1 : ℝ) / H)) :=
      mul_le_mul hphi.le hmhi.le (by positivity) (by positivity)
    rw [hhi] at hstep
    push_cast
    linarith

/-- **R1c — the seam polynomial is a `spoly`.**  The reindex `(j,p,m) ↦ pm` collapses the
triple seam sum to a `σ=1` Dirichlet polynomial on `[1,N]` with coefficients `ramSeamCoeff` —
no frequency inflation (every `pm < Xe^{1/H} ≤ 2X ≤ N`). -/
theorem ramSeamPoly_eq_spoly (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N)
    (b c : ℕ → ℂ) (t : ℝ) :
    ramSeamPoly H N X P Q b c t = spoly N (ramSeamCoeff H N X P Q b c) t := by
  classical
  have hH0 : (0 : ℝ) < H := by linarith
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- every seam frequency lands in `[1,N]`
  have hmaps : ∀ σ ∈ ramSeamDom H N X P Q, σ.2.1 * σ.2.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    have hw := ramSeamDom_frequency_window H N X P Q hσ
    rw [ramSeamDom, Finset.mem_sigma, Finset.mem_product] at hσ
    obtain ⟨-, hp, hm⟩ := hσ
    rw [ramQblock, Finset.mem_filter] at hp
    rw [ramSeam, Finset.mem_filter, Finset.mem_Icc] at hm
    have hp1 : 0 < σ.2.1 := hp.2.1.pos
    have hm1 : 1 ≤ σ.2.2 := hm.1.1
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp1.ne' (by omega)), ?_⟩
    have hexp : Real.exp (1 / H) ≤ 2 := by
      refine le_trans (Real.exp_le_exp.mpr ?_) exp_half_le_two
      rw [div_le_div_iff₀ hH0 (by norm_num)]; linarith
    have hle : ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ (N : ℝ) := by
      refine le_trans hw.2 ?_
      nlinarith
    exact_mod_cast hle
  calc ramSeamPoly H N X P Q b c t
      = ∑ j ∈ ramI H P Q, ∑ x ∈ (ramQblock H P Q j) ×ˢ (ramSeam H N X j),
          (c x.1 / (x.1 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
            ((b x.2 / (x.2 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
              ((blockOmega P Q x.2 : ℂ) + 1)⁻¹) := by
        rw [ramSeamPoly]
        exact Finset.sum_congr rfl (fun j _ => (Finset.sum_product' _ _ _).symm)
    _ = ∑ σ ∈ ramSeamDom H N X P Q,
          (c σ.2.1 / (σ.2.1 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
            ((b σ.2.2 / (σ.2.2 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
              ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹) := by
        rw [ramSeamDom, Finset.sum_sigma']
    _ = ∑ σ ∈ ramSeamDom H N X P Q,
          (c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹)
            / ((σ.2.1 * σ.2.2 : ℕ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        have hmem := hmaps σ hσ
        rw [Finset.mem_Icc] at hmem
        rw [ramSeamDom, Finset.mem_sigma, Finset.mem_product] at hσ
        obtain ⟨-, hp, hm⟩ := hσ
        rw [ramQblock, Finset.mem_filter] at hp
        rw [ramSeam, Finset.mem_filter, Finset.mem_Icc] at hm
        have hp0 : (σ.2.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.2.1.pos.ne'
        have hm0 : (σ.2.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hm.1.1; omega)
        have hps : ((σ.2.1 : ℂ)) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
          rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, -⟩; exact hp0 h0
        have hms : ((σ.2.2 : ℂ)) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
          rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, -⟩; exact hm0 h0
        rw [natCast_mul_cpow]
        field_simp
    _ = spoly N (ramSeamCoeff H N X P Q b c) t := by
        rw [spoly, ← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [ramSeamCoeff, Finset.sum_div]
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [Finset.mem_filter] at hσ
        rw [hσ.2]

/-! ## R1d — the coefficients are bounded (`ramare_weight_sum`) -/

/-- **R1d — `‖d_n‖ ≤ 1`** (MR p.20's "for some bounded `d_m`").  The seam fiber at a frequency
`n` injects (via `σ ↦ p`) into the block primes dividing `n`, and each term is dominated by the
Ramaré weight `1/(ω(n/p;P,Q) + 1_{(p,n/p)=1})`; the landed `ramare_weight_sum` (Decomp:119)
sums those to exactly `1`.  This is the step that a naive per-frequency Cauchy–Schwarz would
lose a `(log X)^θ` on. -/
theorem norm_ramSeamCoeff_le_one (H : ℝ) (hH : 0 < H) (N X P Q : ℕ) (hP : 1 ≤ P)
    (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    ‖ramSeamCoeff H N X P Q b c n‖ ≤ 1 := by
  classical
  rw [ramSeamCoeff]
  rcases Finset.eq_empty_or_nonempty
      ((ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n)) with he | hne
  · rw [he]; simp
  obtain ⟨σ₀, hσ₀⟩ := hne
  -- the data carried by a fiber member
  have hmem : ∀ σ ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
      σ.2.1.Prime ∧ P ≤ σ.2.1 ∧ σ.2.1 ≤ Q ∧ 1 ≤ σ.2.2 ∧ σ.2.1 * σ.2.2 = n ∧
        ⌊H * Real.log (σ.2.1 : ℝ)⌋₊ = σ.1 := by
    intro σ hσ
    rw [Finset.mem_filter, ramSeamDom, Finset.mem_sigma, Finset.mem_product] at hσ
    obtain ⟨⟨-, hp, hm⟩, hn⟩ := hσ
    rw [ramQblock_eq_filter H hH P Q hP, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_Icc] at hp
    rw [ramSeam, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2, hm.1.1, hn, hp.2⟩
  obtain ⟨hp₀p, hp₀P, hp₀Q, hm₀1, hn₀, -⟩ := hmem σ₀ hσ₀
  have hn0 : n ≠ 0 := by
    rw [← hn₀]; exact Nat.mul_ne_zero hp₀p.pos.ne' (by omega)
  have hω : 1 ≤ blockOmega P Q n := by
    rw [blockOmega]
    exact Finset.card_pos.mpr
      ⟨σ₀.2.1, mem_blockPrimeDivs.mpr ⟨hp₀p, ⟨σ₀.2.2, hn₀.symm⟩, hn0, hp₀P, hp₀Q⟩⟩
  -- the fiber's terms, bounded by the Ramaré weights
  have hbound : ∀ σ ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
      ‖c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹‖
        ≤ 1 / ((blockOmega P Q (n / σ.2.1) : ℝ) + 1) := by
    intro σ hσ
    obtain ⟨hpp, -, -, -, hn, -⟩ := hmem σ hσ
    have hdiv : n / σ.2.1 = σ.2.2 := by rw [← hn, Nat.mul_div_cancel_left _ hpp.pos]
    rw [hdiv]
    have hw : ‖((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹‖ = 1 / ((blockOmega P Q σ.2.2 : ℝ) + 1) := by
      rw [norm_inv, show ((blockOmega P Q σ.2.2 : ℂ) + 1)
          = ((blockOmega P Q σ.2.2 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast
      rw [one_div]
    rw [norm_mul, norm_mul, hw]
    have h1 : ‖c σ.2.1‖ * ‖b σ.2.2‖ ≤ 1 :=
      mul_le_one₀ (hc _) (norm_nonneg _) (hb _)
    have h2 : (0 : ℝ) ≤ 1 / ((blockOmega P Q σ.2.2 : ℝ) + 1) := by positivity
    nlinarith [norm_nonneg (c σ.2.1), norm_nonneg (b σ.2.2)]
  -- the injection `σ ↦ p` into the block primes of `n`
  have hinj : ∀ x ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
      ∀ y ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
      x.2.1 = y.2.1 → x = y := by
    rintro ⟨xj, xp, xm⟩ hx ⟨yj, yp, ym⟩ hy hxy
    obtain ⟨hxpp, -, -, -, hxn, hxj⟩ := hmem _ hx
    obtain ⟨-, -, -, -, hyn, hyj⟩ := hmem _ hy
    simp only at hxy hxn hyn hxj hyj hxpp
    have h1 : xj = yj := by rw [← hxj, ← hyj, hxy]
    have h2 : xm = ym := by
      refine Nat.eq_of_mul_eq_mul_left hxpp.pos ?_
      rw [hxn, hxy, hyn]
    subst h1; subst hxy; subst h2; rfl
  have himg : ((ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n)).image
      (fun σ => σ.2.1) ⊆ BlockPrimeDivs P Q n := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨σ, hσ, rfl⟩ := hp
    obtain ⟨hpp, hpP, hpQ, -, hn, -⟩ := hmem σ hσ
    exact mem_blockPrimeDivs.mpr ⟨hpp, ⟨σ.2.2, hn.symm⟩, hn0, hpP, hpQ⟩
  have hweight : ∀ p ∈ BlockPrimeDivs P Q n,
      1 / ((blockOmega P Q (n / p) : ℝ) + 1) ≤ ramareWeight P Q p (n / p) := by
    intro p hp
    rw [mem_blockPrimeDivs] at hp
    obtain ⟨hpp, hpdvd, -, hpP, hpQ⟩ := hp
    rw [ramareWeight]
    have hcard : (((BlockPrimeDivs P Q (n / p)).card : ℕ) : ℝ)
        = ((blockOmega P Q (n / p) : ℕ) : ℝ) := rfl
    by_cases hcop : Nat.Coprime p (n / p)
    · rw [if_pos hcop, hcard]
    · rw [if_neg hcop, add_zero, hcard]
      have hpm : p ∣ n / p := by
        by_contra h; exact hcop (hpp.coprime_iff_not_dvd.mpr h)
      have hm0 : n / p ≠ 0 := by
        intro h
        rw [Nat.div_eq_zero_iff] at h
        rcases h with h | h
        · exact hpp.pos.ne' h
        · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd) (not_le.mpr h)
      have h1 : 1 ≤ blockOmega P Q (n / p) := by
        rw [blockOmega]
        exact Finset.card_pos.mpr
          ⟨p, mem_blockPrimeDivs.mpr ⟨hpp, hpm, hm0, hpP, hpQ⟩⟩
      have hR : (1 : ℝ) ≤ (blockOmega P Q (n / p) : ℝ) := by exact_mod_cast h1
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
  calc ‖∑ σ ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
          c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹‖
      ≤ ∑ σ ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
          ‖c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ σ ∈ (ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n),
          1 / ((blockOmega P Q (n / σ.2.1) : ℝ) + 1) := Finset.sum_le_sum hbound
    _ = ∑ p ∈ ((ramSeamDom H N X P Q).filter (fun σ => σ.2.1 * σ.2.2 = n)).image
            (fun σ => σ.2.1), 1 / ((blockOmega P Q (n / p) : ℝ) + 1) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ BlockPrimeDivs P Q n, 1 / ((blockOmega P Q (n / p) : ℝ) + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ ≤ ∑ p ∈ BlockPrimeDivs P Q n, ramareWeight P Q p (n / p) := Finset.sum_le_sum hweight
    _ = 1 := ramare_weight_sum hω

/-- The seam coefficient vanishes off the narrow window `[Xe^{−1/H}, Xe^{1/H}]`. -/
theorem ramSeamCoeff_eq_zero_of_notMem (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ)
    (n : ℕ) (hn : ¬ ((X : ℝ) * Real.exp (-(1 / H)) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (X : ℝ) * Real.exp (1 / H))) :
    ramSeamCoeff H N X P Q b c n = 0 := by
  classical
  rw [ramSeamCoeff]
  refine Finset.sum_eq_zero (fun σ hσ => absurd ?_ hn)
  rw [Finset.mem_filter] at hσ
  have hw := ramSeamDom_frequency_window H N X P Q hσ.1
  rw [hσ.2] at hw
  exact hw

/-! ## R2 — the honest window row: the mean-value pricing -/

/-- **R2 — the seam second moment at the true grade.**  `moment_core_bound` on the bounded
seam coefficients, over the narrow frequency window `[Xe^{−1/H}, Xe^{1/H}]` whose count is the
landed `window_card_le` (`2eX/H + 1`):

  `∫_{−T}^{T} ‖seam‖² ≤ (2T + 20N)·(2e·X/H + 1)·(e/X²)`,

i.e. the `(T/X + 1)·(1/H)` row of MR p.20 — see `ramWindowErr_moment_grade`. -/
theorem ramSeamPoly_moment (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N)
    (hP : 1 ≤ P) (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramSeamPoly H N X P Q b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * ((2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2)) := by
  classical
  have hH0 : (0 : ℝ) < H := by linarith
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hcongr : (∫ t in (-T)..T, ‖ramSeamPoly H N X P Q b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖spoly N (ramSeamCoeff H N X P Q b c) t‖ ^ 2 :=
    intervalIntegral.integral_congr
      (fun t _ => by rw [ramSeamPoly_eq_spoly H hH N X P Q hX hN b c t])
  rw [hcongr]
  refine (moment_core_bound N (ramSeamCoeff H N X P Q b c) T).trans ?_
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  refine mul_le_mul_of_nonneg_left ?_ hpre
  -- restrict to the narrow window
  set S := (Finset.Icc 1 N).filter (fun n : ℕ => (X : ℝ) * Real.exp (-(1 / H)) ≤ (n : ℝ) ∧
    (n : ℝ) ≤ (X : ℝ) * Real.exp (1 / H)) with hS
  have hsub : S ⊆ Finset.Icc 1 N := by rw [hS]; exact Finset.filter_subset _ _
  have hrestrict : ∑ n ∈ Finset.Icc 1 N, ‖ramSeamCoeff H N X P Q b c n‖ ^ 2 / (n : ℝ) ^ 2
      = ∑ n ∈ S, ‖ramSeamCoeff H N X P Q b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
    refine (Finset.sum_subset hsub (fun x hx hxs => ?_)).symm
    have hnot : ¬ ((X : ℝ) * Real.exp (-(1 / H)) ≤ (x : ℝ) ∧
        (x : ℝ) ≤ (X : ℝ) * Real.exp (1 / H)) := by
      intro h; exact hxs (by rw [hS, Finset.mem_filter]; exact ⟨hx, h⟩)
    rw [ramSeamCoeff_eq_zero_of_notMem H N X P Q b c x hnot, norm_zero]
    simp
  rw [hrestrict]
  -- each term ≤ e/X²
  have hterm : ∀ n ∈ S, ‖ramSeamCoeff H N X P Q b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ Real.exp 1 / (X : ℝ) ^ 2 := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, -⟩, hnlo, -⟩ := hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hd : ‖ramSeamCoeff H N X P Q b c n‖ ≤ 1 :=
      norm_ramSeamCoeff_le_one H hH0 N X P Q hP b c hb hc n
    have hd0 : (0 : ℝ) ≤ ‖ramSeamCoeff H N X P Q b c n‖ := norm_nonneg _
    -- `n ≥ X e^{−1/H} ≥ X e^{−1/2}`, and `e·(e^{−1/2})² = 1`
    have hexp : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(1 / H)) := by
      refine Real.exp_le_exp.mpr ?_
      have h : 1 / H ≤ 1 / (2 : ℝ) := by
        rw [div_le_div_iff₀ hH0 (by norm_num)]; linarith
      linarith
    have hnlo' : (X : ℝ) * Real.exp (-(1 / 2 : ℝ)) ≤ (n : ℝ) := by
      refine le_trans ?_ hnlo
      exact mul_le_mul_of_nonneg_left hexp hXR.le
    have hsq : Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) = Real.exp (-1 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have hee : Real.exp 1 * Real.exp (-1 : ℝ) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hepos : (0 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
    have hkey : (X : ℝ) ^ 2 ≤ Real.exp 1 * (n : ℝ) ^ 2 := by
      have h1 : ((X : ℝ) * Real.exp (-(1 / 2 : ℝ))) ^ 2 ≤ (n : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hXR.le hepos.le]
      have h2 : ((X : ℝ) * Real.exp (-(1 / 2 : ℝ))) ^ 2 = (X : ℝ) ^ 2 * Real.exp (-1 : ℝ) := by
        rw [mul_pow]; rw [show Real.exp (-(1 / 2 : ℝ)) ^ 2
          = Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) by ring, hsq]
      rw [h2] at h1
      nlinarith [Real.exp_pos (1 : ℝ), sq_nonneg (X : ℝ)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hd2 : ‖ramSeamCoeff H N X P Q b c n‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (X : ℝ), hkey, hd2]
  have hcard : (S.card : ℝ) ≤ 2 * Real.exp 1 * (X : ℝ) / H + 1 := by
    refine window_card_le H (by linarith) X S (fun n hn => ?_)
    rw [hS, Finset.mem_filter] at hn
    exact hn.2
  calc ∑ n ∈ S, ‖ramSeamCoeff H N X P Q b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ S.card • (Real.exp 1 / (X : ℝ) ^ 2) := Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * (Real.exp 1 / (X : ℝ) ^ 2) := by rw [nsmul_eq_mul]
    _ ≤ (2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_right hcard ?_
        positivity

/-- **R2 (exit) — the window error at MR's grade.**  The honest replacement for
`ramWindowErr_moment_triv`. -/
theorem ramWindowErr_moment_sharp (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * ((2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2)) := by
  have hcongr : (∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖ramSeamPoly H N X P Q b c t‖ ^ 2 :=
    intervalIntegral.integral_congr
      (fun t _ => by rw [ramWindowErr_eq_seamPoly H N X P Q hX hN b c hwin t])
  rw [hcongr]
  exact ramSeamPoly_moment H hH N X P Q hX hN hP b c hb hc T hT

/-- **R2 (normal form) — the paper's `(T/X + 1)/H` row.**  With `N ≤ 2X` and `H ≤ X` (both
harmless: MR takes `N = 2X` and `H = (log X)^A`), the honest window row collapses to

  `∫_{−T}^{T} ‖window‖² ≤ 720·(T/X + 1)/H`,

MR p.20's grade with an explicit absolute constant. -/
theorem ramWindowErr_moment_grade (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hN2 : (N : ℝ) ≤ 2 * (X : ℝ)) (hHX : H ≤ (X : ℝ)) (hP : 1 ≤ P)
    (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramWindowErr H N X P Q b c t‖ ^ 2)
      ≤ 720 * (T / (X : ℝ) + 1) / H := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  refine (ramWindowErr_moment_sharp H hH N X P Q hX hN hP b c hb hc hwin T hT).trans ?_
  have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- the row mass, collapsed onto `1/(HX)`
  have hmass : (2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2)
      ≤ 18 / (H * (X : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hexpand : (2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2)
          * (H * (X : ℝ))
        = 2 * Real.exp 1 ^ 2 + Real.exp 1 * H / (X : ℝ) := by
      field_simp
    rw [hexpand]
    have h6 : Real.exp 1 * H / (X : ℝ) ≤ Real.exp 1 := by
      rw [div_le_iff₀ hXR]
      nlinarith
    nlinarith
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  calc (2 * T + 20 * (N : ℝ))
        * ((2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2))
      ≤ (2 * T + 20 * (N : ℝ)) * (18 / (H * (X : ℝ))) :=
        mul_le_mul_of_nonneg_left hmass hpre
    _ ≤ (2 * T + 40 * (X : ℝ)) * (18 / (H * (X : ℝ))) := by
        refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 720 * (T / (X : ℝ) + 1) / H := by
        have e1 : (2 * T + 40 * (X : ℝ)) * (18 / (H * (X : ℝ)))
            = (36 * T + 720 * (X : ℝ)) / (H * (X : ℝ)) := by
          field_simp
          ring
        have e2 : 720 * (T / (X : ℝ) + 1) / H = (720 * T + 720 * (X : ℝ)) / (H * (X : ℝ)) := by
          field_simp
        rw [e1, e2, div_le_div_iff_of_pos_right (by positivity)]
        linarith

/-! ## R3 — Lemma 12 with the honest window row -/

/-- **R3 — Lemma 12's mean square, with MR's honest window row.**  This is
`RamareWindows.lemma12_meansq` with the vacuous trivial-sup row `2T·windowMass²` replaced by
the seam row `(2T+20N)·(2eX/H+1)·(e/X²)` of `ramWindowErr_moment_sharp`.

Path taken (R3): the `herr` binder of `lemma12_meansq_of_windowErr` is generic in `E`, so no
statement surgery was needed — the honest row is fed through the SAME
`ramErr_moment_split` assembly, discharging `herr` at the true grade.
`ramWindowErr_moment_triv` is thereby superseded (not deleted). -/
theorem lemma12_meansq_sharp (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N)
    (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                    ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  have hH0 : (0 : ℝ) < H := by linarith
  refine lemma12_meansq_of_windowErr H N X P Q a b c T _ hT ?_
  refine (ramErr_moment_split H hH0 N X P Q hP a b c hcoef T hT).trans ?_
  gcongr
  · exact ramWindowErr_moment_sharp H hH N X P Q hX hN hP b c hb hc hwin T hT
  · exact ramP2corr_moment N P Q a b c T
  · exact ramCopTail_moment N P Q a T

/-! ## R4 — the coprime tail vanishes under the §8.3 support pin -/

/-- **R4 — the coprime tail is identically zero** when every frequency in the support of `a`
carries a block prime (the §8.3 instantiation pin: each `n ∈ supp a` has a prime factor in
`[P,Q]`).  MR's `Σ_{(n,𝒫)=1} a_n/n^s` row then costs nothing. -/
theorem ramCopTail_eq_zero_of_blockSupport (N P Q : ℕ) (a : ℕ → ℂ)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n) (t : ℝ) :
    ramCopTail N P Q a t = 0 := by
  classical
  rw [ramCopTail]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  have ha : a n = 0 := by
    by_contra h
    have := hsupp n h
    omega
  rw [ha, zero_div]

/-- The coprime-tail second moment is exactly `0` under the support pin. -/
theorem ramCopTail_moment_zero (N P Q : ℕ) (a : ℕ → ℂ)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n) (T : ℝ) :
    (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2) = 0 := by
  have hcongr : (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2) = ∫ _t in (-T)..T, (0 : ℝ) :=
    intervalIntegral.integral_congr (fun t _ => by
      rw [ramCopTail_eq_zero_of_blockSupport N P Q a hsupp t, norm_zero]
      norm_num)
  rw [hcongr, intervalIntegral.integral_zero]

/-- **R4 (exit) — Lemma 12 with the honest window row AND no tail row.**  Under the §8.3
support pin the three-row error collapses to two rows: the seam row (MR's `1/H`) and the
`p²`-correction row (MR's `1/P`). -/
theorem lemma12_meansq_sharp_blockSupport (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (X : ℝ) / H + 1) * (Real.exp 1 / (X : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  have hH0 : (0 : ℝ) < H := by linarith
  refine lemma12_meansq_of_windowErr H N X P Q a b c T _ hT ?_
  refine (ramErr_moment_split H hH0 N X P Q hP a b c hcoef T hT).trans ?_
  have h1 := ramWindowErr_moment_sharp H hH N X P Q hX hN hP b c hb hc hwin T hT
  have h2 := ramP2corr_moment N P Q a b c T
  have h3 := ramCopTail_moment_zero N P Q a hsupp T
  rw [h3]
  linarith

/-! ## R5 — the MR-faithful template: BOTH seam windows, no coefficient hypothesis

The `hwin` hypothesis above is forced by ONE deviation of `RamareWindows`: its clean term sums
the cofactor `m` over the full range `{m : pm ∈ [1,N]}` (the dyadic window `[X,2X]` having been
folded into the coefficient `a`), rather than MR's own range `{m : X ≤ pm ≤ 2X}`.

This section certifies the fix.  With MR's range the seam identity is **unconditional in the
coefficients** — and it produces exactly the paper's TWO windows: the undercount
`Σ_{Xe^{−1/H}≤·≤Xe^{1/H}}` (lower seam) and the overcount `Σ_{2X≤·≤2Xe^{1/H}}` (upper seam).
Wiring it in needs a windowed re-derivation of `spoly_ramare_split` upstream — the exact
residual this file leaves. -/

open Classical in
/-- **MR's honest eq (16) cofactor range** `{m ∈ [1,N] : X ≤ pm ≤ 2X}` — the range the paper
actually sums over. -/
noncomputable def ramHonMR (N X p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun m => (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ))

open Classical in
/-- **The upper seam window** (MR's `[2X, 2Xe^{1/H}]` row): the cofactors `R_{j,H}`
OVERCOUNTS, `{m ∈ [1,N] : 2Xe^{−(j+1)/H} < m ≤ 2Xe^{−j/H}}`. -/
noncomputable def ramSeamUpper (H : ℝ) (N X j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun m => 2 * (X : ℝ) * Real.exp (-((j : ℝ) + 1) / H) < (m : ℝ) ∧
      (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H))

/-- **R5 — the seam identity at MR's range, UNCONDITIONALLY in the coefficients.**  For `p` in
the dyadic block `j` and ANY `f`, the honest `X ≤ pm ≤ 2X` cofactor sum minus the
`p`-independent `R_{j,H}` sum is (lower seam) − (upper seam): MR p.20's two `d_m` rows, with
the `p`-dependence confined to the frequency cuts `X ≤ pm` / `2X < pm` (both are cut inside a
`p`-independent narrow window).  No support hypothesis on `f` is used — this is what makes the
honest row available for MR's own long block `[P,Q]`. -/
theorem seam_sum_identity_mr (H : ℝ) (hH : 2 ≤ H) (N X P Q j p : ℕ) (hX : 1 ≤ X)
    (hp : p ∈ ramQblock H P Q j) (f : ℕ → ℂ) :
    (∑ m ∈ ramHonMR N X p, f m) - (∑ m ∈ ramRrange H N X j, f m)
      = (∑ m ∈ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ)), f m)
        - ∑ m ∈ (ramSeamUpper H N X j).filter (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ)),
            f m := by
  classical
  have hH0 : (0 : ℝ) < H := by linarith
  have hp' := hp
  rw [ramQblock, Finset.mem_filter, Finset.mem_Icc] at hp'
  obtain ⟨-, hpp, hplo, hphi⟩ := hp'
  have hp0 : 0 < p := hpp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hEpos : (0 : ℝ) < Real.exp (-(j : ℝ) / H) := Real.exp_pos _
  have hFpos : (0 : ℝ) < Real.exp (((j : ℝ) + 1) / H) := Real.exp_pos _
  have hGpos : (0 : ℝ) < Real.exp (-((j : ℝ) + 1) / H) := Real.exp_pos _
  -- the three exponential collapses
  have hE1 : Real.exp ((j : ℝ) / H) * Real.exp (-(j : ℝ) / H) = 1 := by
    rw [← Real.exp_add, show (j : ℝ) / H + -(j : ℝ) / H = 0 by ring, Real.exp_zero]
  have hE2 : Real.exp (((j : ℝ) + 1) / H) * Real.exp (-(j : ℝ) / H) = Real.exp (1 / H) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE3 : Real.exp (((j : ℝ) + 1) / H) * Real.exp (-((j : ℝ) + 1) / H) = 1 := by
    rw [← Real.exp_add, show ((j : ℝ) + 1) / H + -((j : ℝ) + 1) / H = 0 by ring, Real.exp_zero]
  have hexpH : Real.exp (1 / H) ≤ 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_half_le_two
    rw [div_le_div_iff₀ hH0 (by norm_num)]; linarith
  -- `p·(Xe^{−j/H})` straddles `[X, 2X)`
  have hpL1 : (X : ℝ) ≤ (p : ℝ) * ((X : ℝ) * Real.exp (-(j : ℝ) / H)) := by
    have h := mul_le_mul_of_nonneg_right hplo
      (le_of_lt (by positivity : (0:ℝ) < (X : ℝ) * Real.exp (-(j : ℝ) / H)))
    nlinarith [hE1]
  have hpL2 : (p : ℝ) * ((X : ℝ) * Real.exp (-(j : ℝ) / H)) < 2 * (X : ℝ) := by
    have h := mul_lt_mul_of_pos_right hphi
      (by positivity : (0:ℝ) < (X : ℝ) * Real.exp (-(j : ℝ) / H))
    nlinarith [hE2, hexpH]
  have hFG : Real.exp (((j : ℝ) + 1) / H) * ((X : ℝ) * Real.exp (-((j : ℝ) + 1) / H))
      = (X : ℝ) := by nlinarith [hE3]
  -- the four index sets sit inside `[1,N]`
  have hAsub : ramHonMR N X p ⊆ Finset.Icc 1 N := by rw [ramHonMR]; exact Finset.filter_subset _ _
  have hBsub : ramRrange H N X j ⊆ Finset.Icc 1 N := by
    rw [ramRrange]; exact Finset.filter_subset _ _
  have hW1sub : (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ))
      ⊆ Finset.Icc 1 N := by
    refine subset_trans (Finset.filter_subset _ _) ?_
    rw [ramSeam]; exact Finset.filter_subset _ _
  have hW2sub : (ramSeamUpper H N X j).filter (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ))
      ⊆ Finset.Icc 1 N := by
    refine subset_trans (Finset.filter_subset _ _) ?_
    rw [ramSeamUpper]; exact Finset.filter_subset _ _
  rw [sum_eq_icc_ite hAsub f, sum_eq_icc_ite hBsub f, sum_eq_icc_ite hW1sub f,
    sum_eq_icc_ite hW2sub f, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  have hm1 : 1 ≤ m := hm.1
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  -- the four membership characterisations
  have hAiff : m ∈ ramHonMR N X p
      ↔ ((X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ)) := by
    rw [ramHonMR, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_Icc.mpr hm, h⟩⟩
  have hBiff : m ∈ ramRrange H N X j
      ↔ ((X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H)) := by
    rw [ramRrange, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_Icc.mpr hm, h⟩⟩
  have hW1iff : m ∈ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ))
      ↔ (((X : ℝ) * Real.exp (-((j : ℝ) + 1) / H) ≤ (m : ℝ) ∧
            (m : ℝ) < (X : ℝ) * Real.exp (-(j : ℝ) / H)) ∧ (X : ℝ) ≤ (p : ℝ) * (m : ℝ)) := by
    rw [Finset.mem_filter, ramSeam, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Finset.mem_Icc.mpr hm, h.1⟩, h.2⟩⟩
  have hW2iff : m ∈ (ramSeamUpper H N X j).filter (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ))
      ↔ ((2 * (X : ℝ) * Real.exp (-((j : ℝ) + 1) / H) < (m : ℝ) ∧
            (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H)) ∧
          2 * (X : ℝ) < (p : ℝ) * (m : ℝ)) := by
    rw [Finset.mem_filter, ramSeamUpper, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Finset.mem_Icc.mpr hm, h.1⟩, h.2⟩⟩
  -- the monotone transfers between the `m`-cuts and the `pm`-cuts
  have hmono1 : (X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ) → (X : ℝ) ≤ (p : ℝ) * (m : ℝ) := by
    intro h; nlinarith
  have hmono2 : (m : ℝ) < (X : ℝ) * Real.exp (-(j : ℝ) / H) → (p : ℝ) * (m : ℝ) < 2 * (X : ℝ) := by
    intro h; nlinarith
  have hmono3 : 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H) < (m : ℝ) →
      2 * (X : ℝ) < (p : ℝ) * (m : ℝ) := by intro h; nlinarith
  have hmono4 : (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ) →
      (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H) := by
    intro h; by_contra hcon; exact absurd h (not_le.mpr (hmono3 (not_le.mp hcon)))
  have hmono5 : (X : ℝ) ≤ (p : ℝ) * (m : ℝ) →
      (X : ℝ) * Real.exp (-((j : ℝ) + 1) / H) ≤ (m : ℝ) := by
    intro h
    nlinarith [mul_lt_mul_of_pos_right hphi hmR, hFG]
  have hmono6 : 2 * (X : ℝ) < (p : ℝ) * (m : ℝ) →
      2 * (X : ℝ) * Real.exp (-((j : ℝ) + 1) / H) < (m : ℝ) := by
    intro h
    nlinarith [mul_lt_mul_of_pos_right hphi hmR, hFG]
  -- the trichotomy of `pm` against the dyadic window `[X, 2X]`
  rcases lt_trichotomy ((p : ℝ) * (m : ℝ)) (X : ℝ) with hlt | heq | hgt
  · -- `pm < X`: nothing is counted anywhere
    have hnA : m ∉ ramHonMR N X p := fun h => absurd (hAiff.mp h).1 (not_le.mpr hlt)
    have hnB : m ∉ ramRrange H N X j := fun h => absurd (hmono1 (hBiff.mp h).1) (not_le.mpr hlt)
    have hnW1 : m ∉ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ)) :=
      fun h => absurd (hW1iff.mp h).2 (not_le.mpr hlt)
    have hnW2 : m ∉ (ramSeamUpper H N X j).filter (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ)) :=
      fun h => absurd (hW2iff.mp h).2 (by linarith)
    rw [if_neg hnA, if_neg hnB, if_neg hnW1, if_neg hnW2]
  · -- `pm = X`: inside the window, at its lower edge
    have hin : (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ) := by
      constructor <;> linarith
    have hA : m ∈ ramHonMR N X p := hAiff.mpr hin
    have hnW2 : m ∉ (ramSeamUpper H N X j).filter (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ)) :=
      fun h => absurd (hW2iff.mp h).2 (by linarith)
    by_cases hcase : (X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ)
    · have hB : m ∈ ramRrange H N X j := hBiff.mpr ⟨hcase, hmono4 hin.2⟩
      have hnW1 : m ∉ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ)) :=
        fun h => absurd (hW1iff.mp h).1.2 (not_lt.mpr hcase)
      rw [if_pos hA, if_pos hB, if_neg hnW1, if_neg hnW2]; ring
    · rw [not_le] at hcase
      have hnB : m ∉ ramRrange H N X j := fun h => absurd (hBiff.mp h).1 (not_le.mpr hcase)
      have hW1 : m ∈ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ)) :=
        hW1iff.mpr ⟨⟨hmono5 hin.1, hcase⟩, hin.1⟩
      rw [if_pos hA, if_neg hnB, if_pos hW1, if_neg hnW2]
  · -- `X < pm`: split on the upper edge
    by_cases hup : (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ)
    · -- inside the window
      have hin : (X : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (X : ℝ) :=
        ⟨le_of_lt hgt, hup⟩
      have hA : m ∈ ramHonMR N X p := hAiff.mpr hin
      have hnW2 : m ∉ (ramSeamUpper H N X j).filter
          (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ)) :=
        fun h => absurd (hW2iff.mp h).2 (not_lt.mpr hup)
      by_cases hcase : (X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ)
      · have hB : m ∈ ramRrange H N X j := hBiff.mpr ⟨hcase, hmono4 hup⟩
        have hnW1 : m ∉ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ)) :=
          fun h => absurd (hW1iff.mp h).1.2 (not_lt.mpr hcase)
        rw [if_pos hA, if_pos hB, if_neg hnW1, if_neg hnW2]; ring
      · rw [not_le] at hcase
        have hnB : m ∉ ramRrange H N X j := fun h => absurd (hBiff.mp h).1 (not_le.mpr hcase)
        have hW1 : m ∈ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ)) :=
          hW1iff.mpr ⟨⟨hmono5 hin.1, hcase⟩, hin.1⟩
        rw [if_pos hA, if_neg hnB, if_pos hW1, if_neg hnW2]
    · -- above the window: `R_{j,H}` overcounts exactly on the upper seam
      rw [not_le] at hup
      have hnA : m ∉ ramHonMR N X p := fun h => absurd (hAiff.mp h).2 (not_le.mpr hup)
      have hnW1 : m ∉ (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ)) := by
        intro h
        exact absurd (hmono2 (hW1iff.mp h).1.2) (not_lt.mpr (le_of_lt hup))
      by_cases hcase : (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(j : ℝ) / H)
      · have hlow : (X : ℝ) * Real.exp (-(j : ℝ) / H) ≤ (m : ℝ) := by
          by_contra hcon
          exact absurd (hmono2 (not_le.mp hcon)) (not_lt.mpr (le_of_lt hup))
        have hB : m ∈ ramRrange H N X j := hBiff.mpr ⟨hlow, hcase⟩
        have hW2 : m ∈ (ramSeamUpper H N X j).filter
            (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ)) :=
          hW2iff.mpr ⟨⟨hmono6 hup, hcase⟩, hup⟩
        rw [if_neg hnA, if_pos hB, if_neg hnW1, if_pos hW2]
      · rw [not_le] at hcase
        have hnB : m ∉ ramRrange H N X j := fun h => absurd (hBiff.mp h).2 (not_le.mpr hcase)
        have hnW2 : m ∉ (ramSeamUpper H N X j).filter
            (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ)) :=
          fun h => absurd (hW2iff.mp h).1.2 (not_le.mpr hcase)
        rw [if_neg hnA, if_neg hnB, if_neg hnW1, if_neg hnW2]

end Salt.MR
