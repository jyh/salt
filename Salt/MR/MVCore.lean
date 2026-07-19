/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MVHilbert

/-!
# MR-CORE, node K2 (MV-CORE): the generalized Hilbert inequality core

This file works on `MVHilbertUniform` (`Salt/MR/MVHilbert.lean`), the frozen hypothesis
of `dirichlet_poly_l2_mvt`.  It reduces that bilinear (sesquilinear) Hilbert bound DOWN to
the **`L²`-kernel bound** for the discrete Hilbert transform on well-spaced points — the
"well-spaced `L²` kernel bound" flagged in E3 — via a single Cauchy–Schwarz step, and lands
the diagonal part of that `L²` bound.

## Source-hunt verdict (2026-07-19)

Montgomery–Vaughan, *Multiplicative Number Theory III* (draft, `montgomery3.pdf` = the 351pp
`docs/sources/montgomery3.txt`):

* **STAGED (with anchors):** the *application* — **Theorem 26.1** (mean-value estimate,
  txt:9453) and its **Second Proof** (txt:9560–9600) is *verbatim the E3 twist structure*
  (`ym = am e(λm T)`, two applications of the Hilbert inequality, `1/(2δ)` per copy);
  **Theorem 26.3** (txt:9683) is the local-spacing weighted variant (constant `3/2`).
* **NOT STAGED:** the *proof* of the generalized Hilbert inequality itself.  It is cited as
  "Hilbert's inequality, **Theorem G.14**" (txt:26827) and "Theorem ??" (txt:9579), living in
  **Appendix G**.  The staged document's table of contents (txt:193–221) lists only
  appendices I/J/K/L; appendices A–H (hence G) are absent, and *every* cross-reference to the
  Hilbert inequality and to the Beurling–Selberg majorant (txt:9499) renders as the broken
  "Theorem ??".  The sharp `π/δ` proof method is therefore entirely unstaged.

Per doctrine (no from-memory port of the sharp `π/δ` version), this file lands the reduction
stone and the diagonal kernel stone, and carries the off-diagonal `L²` cancellation as the
named residual.  The `(constant)·Σ‖x‖²/δ` shape is preserved throughout — no `log` factor.

## What is landed here (sorry-free)

* `norm_sum_conj_mul_le` — the abstract Cauchy–Schwarz reduction:
  `‖∑ conj(xᵢ)·wᵢ‖ ≤ C·∑‖xᵢ‖²` from the linear `L²` bound `∑‖wᵢ‖² ≤ C²·∑‖xᵢ‖²`.
* `mvHilbert_form_le_of_l2` — the same, specialized to the Hilbert form (`wᵢ` = the discrete
  Hilbert transform `∑_{j≠i} xⱼ/(λⱼ−λᵢ)`).  No spacing hypothesis is used here.
* `L2KernelUniform` — the residual, packaged as a `Prop`: the discrete Hilbert transform on
  `δ`-separated points is `L²`-bounded with constant `C/δ`.
* `mvHilbertUniform_of_l2` — **the reduction**: `L2KernelUniform π ⟹ MVHilbertUniform`.

## The residual (the K2 wall)

`L2KernelUniform π` — equivalently, `‖K‖_op ≤ π/δ` for the real skew kernel
`Kᵢⱼ = 1/(λⱼ−λᵢ)` — is the genuine Montgomery–Vaughan content.  Its diagonal part is
bounded here (`sep_inv_sq_sum_le`, `π²/(3δ²)`); the off-diagonal cross-terms need sign
cancellation (the Schur / diagonal bound alone is `≍ log N`, a refuted route).
-/

namespace Salt.MR

open scoped BigOperators

/-- **The Cauchy–Schwarz reduction (abstract form).**  If the "output" vector `w` satisfies
the linear `L²` bound `∑‖wᵢ‖² ≤ C²·∑‖xᵢ‖²`, then the sesquilinear pairing
`∑ conj(xᵢ)·wᵢ` has `‖·‖ ≤ C·∑‖xᵢ‖²`.  This is the step that turns the *bilinear* Hilbert
bound into a *linear* `L²` bound on the Hilbert-transform operator. -/
theorem norm_sum_conj_mul_le {ι : Type*} (s : Finset ι) (x w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hL2 : ∑ i ∈ s, ‖w i‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ s, ‖x i‖ ^ 2) :
    ‖∑ i ∈ s, (starRingEnd ℂ) (x i) * w i‖ ≤ C * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  classical
  have hP : 0 ≤ ∑ i ∈ s, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  -- ‖∑ conj(xᵢ)·wᵢ‖ ≤ ∑ ‖xᵢ‖·‖wᵢ‖
  have hnorm : ‖∑ i ∈ s, (starRingEnd ℂ) (x i) * w i‖
      ≤ ∑ i ∈ s, ‖x i‖ * ‖w i‖ := by
    calc ‖∑ i ∈ s, (starRingEnd ℂ) (x i) * w i‖
        ≤ ∑ i ∈ s, ‖(starRingEnd ℂ) (x i) * w i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖x i‖ * ‖w i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, Complex.norm_conj]
  have hWnn : 0 ≤ ∑ i ∈ s, ‖x i‖ * ‖w i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCPnn : 0 ≤ C * ∑ i ∈ s, ‖x i‖ ^ 2 := mul_nonneg hC hP
  -- Cauchy–Schwarz, then feed in the linear L² bound
  have hCS : (∑ i ∈ s, ‖x i‖ * ‖w i‖) ^ 2
      ≤ (∑ i ∈ s, ‖x i‖ ^ 2) * (∑ i ∈ s, ‖w i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖x i‖) (fun i => ‖w i‖)
  have hsq : (∑ i ∈ s, ‖x i‖ * ‖w i‖) ^ 2 ≤ (C * ∑ i ∈ s, ‖x i‖ ^ 2) ^ 2 := by
    calc (∑ i ∈ s, ‖x i‖ * ‖w i‖) ^ 2
        ≤ (∑ i ∈ s, ‖x i‖ ^ 2) * (∑ i ∈ s, ‖w i‖ ^ 2) := hCS
      _ ≤ (∑ i ∈ s, ‖x i‖ ^ 2) * (C ^ 2 * ∑ i ∈ s, ‖x i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hL2 hP
      _ = (C * ∑ i ∈ s, ‖x i‖ ^ 2) ^ 2 := by ring
  have hW_le : (∑ i ∈ s, ‖x i‖ * ‖w i‖) ≤ C * ∑ i ∈ s, ‖x i‖ ^ 2 := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hWnn, Real.sqrt_sq hCPnn] at h
  exact le_trans hnorm hW_le

/-- **The Cauchy–Schwarz reduction (Hilbert form).**  For a finite index set `s`, real
frequencies `lam` and complex weights `x`, the bilinear Hilbert form
`∑ᵢ ∑_{j≠i} xⱼ·conj(xᵢ)/(λⱼ−λᵢ)` is bounded by `C·∑‖xᵢ‖²` as soon as the *linear*
discrete Hilbert transform `wᵢ = ∑_{j≠i} xⱼ/(λⱼ−λᵢ)` satisfies `∑‖wᵢ‖² ≤ C²·∑‖xᵢ‖²`.
No spacing hypothesis is used here — the well-spacing enters only through the `L²` bound. -/
theorem mvHilbert_form_le_of_l2 (s : Finset ℕ) (lam : ℕ → ℝ) (x : ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C)
    (hL2 : ∑ i ∈ s, ‖∑ j ∈ s.erase i, x j / ((lam j : ℂ) - (lam i : ℂ))‖ ^ 2
        ≤ C ^ 2 * ∑ i ∈ s, ‖x i‖ ^ 2) :
    ‖∑ i ∈ s, ∑ j ∈ s.erase i,
        x j * (starRingEnd ℂ) (x i) / ((lam j : ℂ) - (lam i : ℂ))‖
      ≤ C * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  have hform : (∑ i ∈ s, ∑ j ∈ s.erase i,
        x j * (starRingEnd ℂ) (x i) / ((lam j : ℂ) - (lam i : ℂ)))
      = ∑ i ∈ s, (starRingEnd ℂ) (x i)
          * (∑ j ∈ s.erase i, x j / ((lam j : ℂ) - (lam i : ℂ))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hform]
  exact norm_sum_conj_mul_le s x
    (fun i => ∑ j ∈ s.erase i, x j / ((lam j : ℂ) - (lam i : ℂ))) hC hL2

/-- **The residual, packaged.**  The discrete Hilbert transform on `δ`-separated frequencies
is `L²`-bounded with constant `C/δ`:
`∑ᵢ ‖∑_{j≠i} xⱼ/(λⱼ−λᵢ)‖² ≤ (C/δ)²·∑ᵢ‖xᵢ‖²`.
Equivalently `‖K‖_op ≤ C/δ` for the real skew kernel `Kᵢⱼ = 1/(λⱼ−λᵢ)`.  This is the
genuine Montgomery–Vaughan content that mathlib lacks; `mvHilbertUniform_of_l2` discharges
the frozen `MVHilbertUniform` from `L2KernelUniform Real.pi`. -/
def L2KernelUniform (C : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (lam : ℕ → ℝ) (x : ℕ → ℂ) (δ : ℝ), 0 < δ →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |lam i - lam j|) →
    ∑ i ∈ s, ‖∑ j ∈ s.erase i, x j / ((lam j : ℂ) - (lam i : ℂ))‖ ^ 2
      ≤ (C / δ) ^ 2 * ∑ i ∈ s, ‖x i‖ ^ 2

/-- **The reduction.**  The sharp `L²`-kernel bound `L2KernelUniform Real.pi` implies the
frozen `MVHilbertUniform` verbatim (constant `π/δ`).  Cauchy–Schwarz is loss-free in the
constant: `‖K‖_op ≤ π/δ ⟹ |⟨x, Kx⟩| ≤ (π/δ)‖x‖²`.  So the entire remaining obligation of
the K2 wall is the *linear* `L²` bound `L2KernelUniform Real.pi`. -/
theorem mvHilbertUniform_of_l2 (h : L2KernelUniform Real.pi) : MVHilbertUniform := by
  intro s lam x δ hδ hsep
  have hCnn : 0 ≤ Real.pi / δ := div_nonneg Real.pi_nonneg hδ.le
  exact mvHilbert_form_le_of_l2 s lam x hCnn (h s lam x δ hδ hsep)

/-! ## The diagonal kernel stone

The diagonal part of the `L²`-kernel bound: for `δ`-separated positive values `u j ≥ δ`,
`∑ⱼ 1/(u j)² ≤ π²/(6δ²)`.  The rank map `g j = ⌊u j/δ⌋` injects the well-spaced values
into `ℕ⁺` with `u j ≥ (g j)·δ`, reducing the sum to a sub-sum of `ζ(2) = π²/6` (Basel). -/

/-- **Rank bound for a δ-separated set of positive values.**  If `u j ≥ δ` for all `j ∈ T`
and the `u j` are pairwise `δ`-separated, then `∑_{j∈T} 1/(u j)² ≤ π²/(6δ²)`.  Proof:
`g j = ⌊u j/δ⌋` maps `T` injectively into `ℕ⁺` with `(g j)·δ ≤ u j`; the sum is then a
sub-sum of `∑_{n≥1} 1/n²`. -/
lemma inv_sq_sum_of_sep {T : Finset ℕ} {δ : ℝ} (hδ : 0 < δ) (u : ℕ → ℝ)
    (hpos : ∀ j ∈ T, δ ≤ u j)
    (hsep : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → δ ≤ |u j - u k|) :
    ∑ j ∈ T, 1 / (u j) ^ 2 ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  classical
  set g : ℕ → ℕ := fun j => (⌊u j / δ⌋).toNat with hg
  have hupos : ∀ j ∈ T, 0 < u j := fun j hj => lt_of_lt_of_le hδ (hpos j hj)
  have hge1 : ∀ j ∈ T, (1 : ℝ) ≤ u j / δ := fun j hj =>
    (one_le_div hδ).mpr (hpos j hj)
  have hfloor_nonneg : ∀ j ∈ T, 0 ≤ ⌊u j / δ⌋ := fun j hj =>
    Int.le_floor.mpr (by simpa using le_trans zero_le_one (hge1 j hj))
  have hcast : ∀ j ∈ T, ((g j : ℤ)) = ⌊u j / δ⌋ := fun j hj =>
    Int.toNat_of_nonneg (hfloor_nonneg j hj)
  have hg1 : ∀ j ∈ T, 1 ≤ g j := by
    intro j hj
    have h1 : (1 : ℤ) ≤ ⌊u j / δ⌋ := Int.le_floor.mpr (by exact_mod_cast hge1 j hj)
    have := hcast j hj; omega
  have hglb : ∀ j ∈ T, (g j : ℝ) * δ ≤ u j := by
    intro j hj
    have hcr : (g j : ℝ) = (⌊u j / δ⌋ : ℝ) := by exact_mod_cast hcast j hj
    have hfl : (⌊u j / δ⌋ : ℝ) ≤ u j / δ := Int.floor_le _
    have : (g j : ℝ) ≤ u j / δ := by rw [hcr]; exact hfl
    calc (g j : ℝ) * δ ≤ (u j / δ) * δ := by nlinarith [this, hδ]
      _ = u j := by field_simp
  have hgpos : ∀ j ∈ T, (0 : ℝ) < (g j : ℝ) := fun j hj => by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hg1 j hj)
  -- injectivity of the rank map
  have hginj : ∀ j ∈ T, ∀ k ∈ T, g j = g k → j = k := by
    intro j hj k hk hgjk
    by_contra hjk
    have hfjk : ⌊u j / δ⌋ = ⌊u k / δ⌋ := by
      have cj := hcast j hj; have ck := hcast k hk; omega
    have hfjkr : (⌊u j / δ⌋ : ℝ) = (⌊u k / δ⌋ : ℝ) := by exact_mod_cast hfjk
    have haj := Int.lt_floor_add_one (u j / δ)
    have hbj := Int.floor_le (u j / δ)
    have hak := Int.lt_floor_add_one (u k / δ)
    have hbk := Int.floor_le (u k / δ)
    have habs : |u j / δ - u k / δ| < 1 := by
      rw [abs_lt]
      refine ⟨?_, ?_⟩
      · linarith [hak, hbj, hfjkr]
      · linarith [haj, hbk, hfjkr]
    have hid : u j - u k = δ * (u j / δ - u k / δ) := by field_simp
    have : |u j - u k| < δ := by
      rw [hid, abs_mul, abs_of_pos hδ]
      calc δ * |u j / δ - u k / δ| < δ * 1 := mul_lt_mul_of_pos_left habs hδ
        _ = δ := mul_one δ
    linarith [hsep j hj k hk hjk, this]
  -- termwise domination by the rank series
  have hterm : ∀ j ∈ T, 1 / (u j) ^ 2 ≤ 1 / ((g j : ℝ) ^ 2 * δ ^ 2) := by
    intro j hj
    have hden : (0 : ℝ) < (g j : ℝ) ^ 2 * δ ^ 2 :=
      mul_pos (pow_pos (hgpos j hj) 2) (pow_pos hδ 2)
    have hgδnn : (0 : ℝ) ≤ (g j : ℝ) * δ := le_of_lt (mul_pos (hgpos j hj) hδ)
    have hsqle : (g j : ℝ) ^ 2 * δ ^ 2 ≤ (u j) ^ 2 := by
      have h1 : ((g j : ℝ) * δ) ^ 2 ≤ (u j) ^ 2 := by nlinarith [hglb j hj, hgδnn]
      nlinarith [h1]
    exact one_div_le_one_div_of_le hden hsqle
  -- assemble: dominate, factor 1/δ², reindex through the injection, bound by ζ(2)
  calc ∑ j ∈ T, 1 / (u j) ^ 2
      ≤ ∑ j ∈ T, 1 / ((g j : ℝ) ^ 2 * δ ^ 2) := Finset.sum_le_sum hterm
    _ = (1 / δ ^ 2) * ∑ j ∈ T, 1 / (g j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = (1 / δ ^ 2) * ∑ m ∈ T.image g, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.sum_image hginj]
    _ ≤ (1 / δ ^ 2) * (Real.pi ^ 2 / 6) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_hasSum (T.image g) (fun m _ => by positivity) hasSum_zeta_two
    _ = Real.pi ^ 2 / (6 * δ ^ 2) := by ring

/-- **The diagonal kernel stone.**  For `δ`-separated real frequencies `lam` and any
`i ∈ s`, `∑_{j≠i} 1/(λᵢ−λⱼ)² ≤ π²/(3δ²)`.  This is the diagonal (`j = k`) part of the
`L²`-kernel bound `L2KernelUniform`; it splits `s.erase i` at `λᵢ` and applies
`inv_sq_sum_of_sep` to each side. -/
theorem sep_inv_sq_sum_le (s : Finset ℕ) (lam : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ |lam a - lam b|)
    {i : ℕ} (hi : i ∈ s) :
    ∑ j ∈ s.erase i, 1 / (lam i - lam j) ^ 2 ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  have hsplit := (Finset.sum_filter_add_sum_filter_not (s.erase i)
      (fun j => lam i < lam j) (fun j => 1 / (lam i - lam j) ^ 2)).symm
  rw [hsplit]
  have hPos : ∑ j ∈ (s.erase i).filter (fun j => lam i < lam j), 1 / (lam i - lam j) ^ 2
      ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    have hconv : (∑ j ∈ (s.erase i).filter (fun j => lam i < lam j), 1 / (lam i - lam j) ^ 2)
        = ∑ j ∈ (s.erase i).filter (fun j => lam i < lam j), 1 / (lam j - lam i) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (lam i - lam j) ^ 2 = (lam j - lam i) ^ 2 from by ring]
    rw [hconv]
    refine inv_sq_sum_of_sep hδ (fun j => lam j - lam i) ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj.1
      have hji : j ≠ i := Finset.ne_of_mem_erase hj.1
      have hd := hsep i hi j hjs (Ne.symm hji)
      rw [abs_of_neg (show lam i - lam j < 0 by linarith [hj.2])] at hd
      linarith
    · intro j hj k hk hjk
      rw [Finset.mem_filter] at hj hk
      have hd := hsep j (Finset.mem_of_mem_erase hj.1) k (Finset.mem_of_mem_erase hk.1) hjk
      rw [show (lam j - lam i) - (lam k - lam i) = lam j - lam k from by ring]
      exact hd
  have hNeg : ∑ j ∈ (s.erase i).filter (fun j => ¬ lam i < lam j), 1 / (lam i - lam j) ^ 2
      ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    refine inv_sq_sum_of_sep hδ (fun j => lam i - lam j) ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj.1
      have hji : j ≠ i := Finset.ne_of_mem_erase hj.1
      have hd := hsep i hi j hjs (Ne.symm hji)
      rwa [abs_of_nonneg (show (0 : ℝ) ≤ lam i - lam j by linarith [not_lt.mp hj.2])] at hd
    · intro j hj k hk hjk
      rw [Finset.mem_filter] at hj hk
      have hd := hsep j (Finset.mem_of_mem_erase hj.1) k (Finset.mem_of_mem_erase hk.1) hjk
      rw [show (lam i - lam j) - (lam i - lam k) = -(lam j - lam k) from by ring, abs_neg]
      exact hd
  calc (∑ j ∈ (s.erase i).filter (fun j => lam i < lam j), 1 / (lam i - lam j) ^ 2)
        + ∑ j ∈ (s.erase i).filter (fun j => ¬ lam i < lam j), 1 / (lam i - lam j) ^ 2
      ≤ Real.pi ^ 2 / (6 * δ ^ 2) + Real.pi ^ 2 / (6 * δ ^ 2) := add_le_add hPos hNeg
    _ = Real.pi ^ 2 / (3 * δ ^ 2) := by ring

end Salt.MR
