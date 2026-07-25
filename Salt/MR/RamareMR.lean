/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RamareErr

/-!
# RamareMR — Lemma 12 re-derived at MR's OWN cofactor range (the `hwin` retirement)

`Salt.MR.RamareErr` lands MR p.20's honest seam mechanism, but pays for it with the
hypothesis

  `hwin : c p * b m ≠ 0 → X ≤ pm ≤ 2X`,

a support statement about the *product* `c_p b_m` at EVERY pair `(p,m)` — including the
`p ∣ m` pairs, where `RamareWindows`' clean term has no coefficient identity to lean on.
That is a genuine extra assumption (RamareErr's header records it as its one deviation).

This file retires it.  The cause of `hwin` is that `RamareWindows.spoly_ramare_split`
extends the clean summand over the FULL eq (16) cofactor range `{m : pm ∈ [1,N]}`, while MR
sums over `{m : X ≤ pm ≤ 2X}`.  Re-running the split at MR's own range

  `ramHonMR N X p = {m ∈ [1,N] : X ≤ pm ≤ 2X}`   (`RamareErr`:743)

makes the seam identity `seam_sum_identity_mr` (`RamareErr`:761) — which is UNCONDITIONAL in
the coefficients — available, and the only hypothesis that survives is MR's own dyadic
support of `a`:

  `hasupp : a n ≠ 0 → X ≤ n ≤ 2X`.

That is strictly weaker than `hwin`: `seam_support_of_hcoef` derives `hwin`'s coprime half
from `hasupp`, and it is exactly `hwin`'s `p ∣ m` half — the unprovable one — that
disappears here, absorbed into the `p²` row where MR itself puts it.

## The chain

* `ramGenPoly` / `ramGenDom` / `ramGenCoeff` — **G**, the generic block-window Dirichlet
  polynomial `Σ_{j∈I} Σ_{p∈block j} Σ_{m∈W j p} (c_p/p^s)(b_m/m^s)/(ω(m)+1)`, its
  `(j,p,m) ↦ pm` frequency domain and fiber coefficients, with the three landed facts:
  `ramGenPoly_eq_spoly` (collapse), `norm_ramGenCoeff_le_one` (`ramare_weight_sum`), and
  `ramGenPoly_moment` (the `moment_core_bound` row at an arbitrary frequency window).
  Both seam rows are instances — no clone.
* `ramSeamLoW` / `ramSeamUpW` — the two `p`-cut seam windows of `seam_sum_identity_mr`.
* `ramSeamLoPoly_moment` / `ramSeamUpPoly_moment` — **M1**, the two rows.  The upper row
  carries the `4×` saving: its frequencies live in `(2X, 2Xe^{1/H}]`, so `1/n² ≤ 1/(2X)²`.
* `spoly_ramare_split_mr` — **M2a**, `spoly = cleanMR + p²MR + tail`, where the `p²` row is
  now supported on `{m ∈ ramHonMR : p ∣ m}` and the clean term is at MR's range.
* `cleanMR_dyadic_sub_main` / `ramErr_decomp_mr` — **M2b**, the four-row exact identity
  `ramErr = lower seam − upper seam + p²MR + tail`.
* `lemma12_meansq_mr` — **M3**, Lemma 12's mean square with NO `hwin`.
* `lemma12_meansq_mr_blockSupport`, `lemma12_meansq_mr_consume` — **M4**, the tail-free and
  `(T/X+1)/H`-graded consumption forms.

Source pins (D5): MR arXiv v4 (`1501.04585v4`), p.20 (Lemma 12's proof), rendered page.
-/

namespace Salt.MR

open Finset Complex MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## G — the generic block-window Dirichlet polynomial

Both seam rows of `seam_sum_identity_mr` have the same shape: a block sum of `c_p/p^s`
against a `(j,p)`-indexed cofactor window `W j p`.  This section prices that shape once. -/

/-- **The generic block-window polynomial**: `Σ_{j∈I} Σ_{p∈block j} Σ_{m∈W j p}
(c_p/p^s)·(b_m/m^s)/(ω(m;P,Q)+1)`. -/
noncomputable def ramGenPoly (H : ℝ) (P Q : ℕ) (W : ℕ → ℕ → Finset ℕ) (b c : ℕ → ℂ) (t : ℝ) :
    ℂ :=
  ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j, ∑ m ∈ W j p,
    (c p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
      ((b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) * ((blockOmega P Q m : ℂ) + 1)⁻¹)

/-- **The generic seam domain**: triples `(j, p, m)` with `p` in the block `j` and `m` in the
window `W j p` (realised inside `[1,N]`). -/
noncomputable def ramGenDom (H : ℝ) (N P Q : ℕ) (W : ℕ → ℕ → Finset ℕ) :
    Finset (Σ _ : ℕ, ℕ × ℕ) :=
  ((ramI H P Q).sigma (fun j => (ramQblock H P Q j) ×ˢ (Finset.Icc 1 N))).filter
    (fun σ => σ.2.2 ∈ W σ.1 σ.2.1)

/-- **The generic seam coefficient `d_n`**: the fiber sum of `c_p b_m/(ω(m;P,Q)+1)` over the
window factorisations `pm = n`. -/
noncomputable def ramGenCoeff (H : ℝ) (N P Q : ℕ) (W : ℕ → ℕ → Finset ℕ) (b c : ℕ → ℂ)
    (n : ℕ) : ℂ :=
  ∑ σ ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
    c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹

lemma mem_ramGenDom {H : ℝ} {N P Q : ℕ} {W : ℕ → ℕ → Finset ℕ} {σ : Σ _ : ℕ, ℕ × ℕ} :
    σ ∈ ramGenDom H N P Q W ↔ (σ.1 ∈ ramI H P Q ∧ σ.2.1 ∈ ramQblock H P Q σ.1 ∧
      σ.2.2 ∈ Finset.Icc 1 N ∧ σ.2.2 ∈ W σ.1 σ.2.1) := by
  rw [ramGenDom, Finset.mem_filter, Finset.mem_sigma, Finset.mem_product]
  tauto

/-- **G1 — the frequency collapse.**  The reindex `(j,p,m) ↦ pm` turns the generic block-window
polynomial into a `σ=1` Dirichlet polynomial on `[1,M]` with coefficients `ramGenCoeff`. -/
theorem ramGenPoly_eq_spoly (H : ℝ) (N M P Q : ℕ) (W : ℕ → ℕ → Finset ℕ)
    (hWsub : ∀ j p, W j p ⊆ Finset.Icc 1 N)
    (hmaps : ∀ σ ∈ ramGenDom H N P Q W, σ.2.1 * σ.2.2 ∈ Finset.Icc 1 M)
    (b c : ℕ → ℂ) (t : ℝ) :
    ramGenPoly H P Q W b c t = spoly M (ramGenCoeff H N P Q W b c) t := by
  classical
  calc ramGenPoly H P Q W b c t
      = ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j, ∑ m ∈ Finset.Icc 1 N,
          (if m ∈ W j p then
            (c p / (p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
              ((b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
                ((blockOmega P Q m : ℂ) + 1)⁻¹) else 0) := by
        rw [ramGenPoly]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl
          (fun p _ => sum_eq_icc_ite (hWsub j p) _))
    _ = ∑ j ∈ ramI H P Q, ∑ x ∈ (ramQblock H P Q j) ×ˢ (Finset.Icc 1 N),
          (if x.2 ∈ W j x.1 then
            (c x.1 / (x.1 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
              ((b x.2 / (x.2 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
                ((blockOmega P Q x.2 : ℂ) + 1)⁻¹) else 0) :=
        Finset.sum_congr rfl (fun j _ => (Finset.sum_product' _ _ _).symm)
    _ = ∑ σ ∈ (ramI H P Q).sigma (fun j => (ramQblock H P Q j) ×ˢ (Finset.Icc 1 N)),
          (if σ.2.2 ∈ W σ.1 σ.2.1 then
            (c σ.2.1 / (σ.2.1 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
              ((b σ.2.2 / (σ.2.2 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
                ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹) else 0) := by
        rw [Finset.sum_sigma']
    _ = ∑ σ ∈ ramGenDom H N P Q W,
          (c σ.2.1 / (σ.2.1 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
            ((b σ.2.2 / (σ.2.2 : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) *
              ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹) := by
        rw [ramGenDom, Finset.sum_filter]
    _ = ∑ σ ∈ ramGenDom H N P Q W,
          (c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹)
            / ((σ.2.1 * σ.2.2 : ℕ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [mem_ramGenDom] at hσ
        obtain ⟨-, hp, hm, -⟩ := hσ
        rw [ramQblock, Finset.mem_filter] at hp
        rw [Finset.mem_Icc] at hm
        have hp0 : (σ.2.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.2.1.pos.ne'
        have hm0 : (σ.2.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hps : ((σ.2.1 : ℂ)) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
          rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, -⟩; exact hp0 h0
        have hms : ((σ.2.2 : ℂ)) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
          rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, -⟩; exact hm0 h0
        rw [natCast_mul_cpow]
        field_simp
    _ = spoly M (ramGenCoeff H N P Q W b c) t := by
        rw [spoly, ← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [ramGenCoeff, Finset.sum_div]
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [Finset.mem_filter] at hσ
        rw [hσ.2]

/-- **G2 — `‖d_n‖ ≤ 1`.**  The window fiber at `n` injects (via `σ ↦ p`) into the block primes
of `n`, each term dominated by the Ramaré weight; `ramare_weight_sum` sums those to `1`. -/
theorem norm_ramGenCoeff_le_one (H : ℝ) (hH : 0 < H) (N P Q : ℕ) (hP : 1 ≤ P)
    (W : ℕ → ℕ → Finset ℕ) (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    ‖ramGenCoeff H N P Q W b c n‖ ≤ 1 := by
  classical
  rw [ramGenCoeff]
  rcases Finset.eq_empty_or_nonempty
      ((ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n)) with he | hne
  · rw [he]; simp
  obtain ⟨σ₀, hσ₀⟩ := hne
  have hmem : ∀ σ ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
      σ.2.1.Prime ∧ P ≤ σ.2.1 ∧ σ.2.1 ≤ Q ∧ 1 ≤ σ.2.2 ∧ σ.2.1 * σ.2.2 = n ∧
        ⌊H * Real.log (σ.2.1 : ℝ)⌋₊ = σ.1 := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    obtain ⟨hd, hn⟩ := hσ
    rw [mem_ramGenDom] at hd
    obtain ⟨-, hp, hm, -⟩ := hd
    rw [ramQblock_eq_filter H hH P Q hP, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_Icc] at hp
    rw [Finset.mem_Icc] at hm
    exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2, hm.1, hn, hp.2⟩
  obtain ⟨hp₀p, hp₀P, hp₀Q, hm₀1, hn₀, -⟩ := hmem σ₀ hσ₀
  have hn0 : n ≠ 0 := by
    rw [← hn₀]; exact Nat.mul_ne_zero hp₀p.pos.ne' (by omega)
  have hω : 1 ≤ blockOmega P Q n := by
    rw [blockOmega]
    exact Finset.card_pos.mpr
      ⟨σ₀.2.1, mem_blockPrimeDivs.mpr ⟨hp₀p, ⟨σ₀.2.2, hn₀.symm⟩, hn0, hp₀P, hp₀Q⟩⟩
  have hbound : ∀ σ ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
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
    have h1 : ‖c σ.2.1‖ * ‖b σ.2.2‖ ≤ 1 := mul_le_one₀ (hc _) (norm_nonneg _) (hb _)
    have h2 : (0 : ℝ) ≤ 1 / ((blockOmega P Q σ.2.2 : ℝ) + 1) := by positivity
    nlinarith [norm_nonneg (c σ.2.1), norm_nonneg (b σ.2.2)]
  have hinj : ∀ x ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
      ∀ y ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
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
  have himg : ((ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n)).image
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
        exact Finset.card_pos.mpr ⟨p, mem_blockPrimeDivs.mpr ⟨hpp, hpm, hm0, hpP, hpQ⟩⟩
      have hR : (1 : ℝ) ≤ (blockOmega P Q (n / p) : ℝ) := by exact_mod_cast h1
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
  calc ‖∑ σ ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
          c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹‖
      ≤ ∑ σ ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
          ‖c σ.2.1 * b σ.2.2 * ((blockOmega P Q σ.2.2 : ℂ) + 1)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ σ ∈ (ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n),
          1 / ((blockOmega P Q (n / σ.2.1) : ℝ) + 1) := Finset.sum_le_sum hbound
    _ = ∑ p ∈ ((ramGenDom H N P Q W).filter (fun σ => σ.2.1 * σ.2.2 = n)).image
            (fun σ => σ.2.1), 1 / ((blockOmega P Q (n / p) : ℝ) + 1) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ BlockPrimeDivs P Q n, 1 / ((blockOmega P Q (n / p) : ℝ) + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ ≤ ∑ p ∈ BlockPrimeDivs P Q n, ramareWeight P Q p (n / p) := Finset.sum_le_sum hweight
    _ = 1 := ramare_weight_sum hω

/-- **G3 — the coefficient vanishes off the frequency window.** -/
theorem ramGenCoeff_eq_zero_of_notMem (H : ℝ) (N P Q : ℕ) (W : ℕ → ℕ → Finset ℕ) (b c : ℕ → ℂ)
    (lo hi : ℝ)
    (hwin : ∀ σ ∈ ramGenDom H N P Q W,
      lo ≤ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ∧ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ hi)
    (n : ℕ) (hn : ¬ (lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi)) :
    ramGenCoeff H N P Q W b c n = 0 := by
  classical
  rw [ramGenCoeff]
  refine Finset.sum_eq_zero (fun σ hσ => absurd ?_ hn)
  rw [Finset.mem_filter] at hσ
  have hw := hwin σ hσ.1
  rw [hσ.2] at hw
  exact hw

/-- The frequency domain lands in `[1,M]` once the window's top is `≤ M`. -/
lemma ramGenDom_maps (H : ℝ) (N M P Q : ℕ) (W : ℕ → ℕ → Finset ℕ) (lo hi : ℝ)
    (hhiM : hi ≤ (M : ℝ))
    (hwin : ∀ σ ∈ ramGenDom H N P Q W,
      lo ≤ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ∧ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ hi) :
    ∀ σ ∈ ramGenDom H N P Q W, σ.2.1 * σ.2.2 ∈ Finset.Icc 1 M := by
  intro σ hσ
  have hw := hwin σ hσ
  rw [mem_ramGenDom] at hσ
  obtain ⟨-, hp, hm, -⟩ := hσ
  rw [ramQblock, Finset.mem_filter] at hp
  rw [Finset.mem_Icc] at hm
  rw [Finset.mem_Icc]
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.2.1.pos.ne' (by omega)), ?_⟩
  have hle : ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ (M : ℝ) := le_trans hw.2 hhiM
  exact_mod_cast hle

/-- **G4 — the generic window row.**  `moment_core_bound` on bounded coefficients supported in
a frequency window `[lo,hi]` of cardinality `≤ C`:
`∫_{−T}^{T} ‖·‖² ≤ (2T + 20M)·C/lo²`. -/
theorem ramGenPoly_moment (H : ℝ) (hH : 0 < H) (N M P Q : ℕ) (hP : 1 ≤ P)
    (W : ℕ → ℕ → Finset ℕ) (hWsub : ∀ j p, W j p ⊆ Finset.Icc 1 N)
    (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (lo hi C : ℝ) (hlo : 0 < lo) (hhiM : hi ≤ (M : ℝ))
    (hwin : ∀ σ ∈ ramGenDom H N P Q W,
      lo ≤ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ∧ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ hi)
    (hcard : ∀ s : Finset ℕ, (∀ n ∈ s, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) → (s.card : ℝ) ≤ C)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramGenPoly H P Q W b c t‖ ^ 2)
      ≤ (2 * T + 20 * (M : ℝ)) * (C / lo ^ 2) := by
  classical
  have hmaps := ramGenDom_maps H N M P Q W lo hi hhiM hwin
  have hcongr : (∫ t in (-T)..T, ‖ramGenPoly H P Q W b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖spoly M (ramGenCoeff H N P Q W b c) t‖ ^ 2 :=
    intervalIntegral.integral_congr
      (fun t _ => by rw [ramGenPoly_eq_spoly H N M P Q W hWsub hmaps b c t])
  rw [hcongr]
  refine (moment_core_bound M (ramGenCoeff H N P Q W b c) T).trans ?_
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (M : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) M; linarith
  refine mul_le_mul_of_nonneg_left ?_ hpre
  set S := (Finset.Icc 1 M).filter (fun n : ℕ => lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi) with hS
  have hsub : S ⊆ Finset.Icc 1 M := by rw [hS]; exact Finset.filter_subset _ _
  have hrestrict : ∑ n ∈ Finset.Icc 1 M, ‖ramGenCoeff H N P Q W b c n‖ ^ 2 / (n : ℝ) ^ 2
      = ∑ n ∈ S, ‖ramGenCoeff H N P Q W b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
    refine (Finset.sum_subset hsub (fun x hx hxs => ?_)).symm
    have hnot : ¬ (lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) := by
      intro h; exact hxs (by rw [hS, Finset.mem_filter]; exact ⟨hx, h⟩)
    rw [ramGenCoeff_eq_zero_of_notMem H N P Q W b c lo hi hwin x hnot, norm_zero]
    simp
  rw [hrestrict]
  have hterm : ∀ n ∈ S, ‖ramGenCoeff H N P Q W b c n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / lo ^ 2 := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨-, hnlo, -⟩ := hn
    have hd : ‖ramGenCoeff H N P Q W b c n‖ ≤ 1 :=
      norm_ramGenCoeff_le_one H hH N P Q hP W b c hb hc n
    have hd0 : (0 : ℝ) ≤ ‖ramGenCoeff H N P Q W b c n‖ := norm_nonneg _
    have hd2 : ‖ramGenCoeff H N P Q W b c n‖ ^ 2 ≤ 1 := by nlinarith
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have hcardS : (S.card : ℝ) ≤ C := by
    refine hcard S (fun n hn => ?_)
    rw [hS, Finset.mem_filter] at hn
    exact hn.2
  calc ∑ n ∈ S, ‖ramGenCoeff H N P Q W b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ S.card • ((1 : ℝ) / lo ^ 2) := Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * (1 / lo ^ 2) := by rw [nsmul_eq_mul]
    _ ≤ C * (1 / lo ^ 2) := mul_le_mul_of_nonneg_right hcardS (by positivity)
    _ = C / lo ^ 2 := by ring

/-- `ramGenPoly` is continuous. -/
lemma continuous_ramGenPoly (H : ℝ) (N P Q : ℕ) (W : ℕ → ℕ → Finset ℕ)
    (hWsub : ∀ j p, W j p ⊆ Finset.Icc 1 N) (b c : ℕ → ℂ) :
    Continuous (ramGenPoly H P Q W b c) := by
  unfold ramGenPoly
  refine continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun p hp => ?_))
  rw [ramQblock, Finset.mem_filter] at hp
  refine continuous_finsetSum _ (fun m hm => ?_)
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hWsub j p hm)).1
  exact (continuous_cterm hp.2.1.pos.ne' (c p)).mul
    ((continuous_cterm (by omega) (b m)).mul continuous_const)

/-! ## M1 — the two seam rows of `seam_sum_identity_mr`

`seam_sum_identity_mr` produces two `p`-cut windows: the lower seam filtered at `X ≤ pm`
(frequencies in `[X, Xe^{1/H}]`) and the upper seam filtered at `2X < pm` (frequencies in
`(2X, 2Xe^{1/H}]`).  Both are `ramGenPoly` instances. -/

/-- **The lower seam window** at `(j,p)`: `ramSeam` cut at `X ≤ pm`. -/
noncomputable def ramSeamLoW (H : ℝ) (N X : ℕ) (j p : ℕ) : Finset ℕ :=
  (ramSeam H N X j).filter (fun m : ℕ => (X : ℝ) ≤ (p : ℝ) * (m : ℝ))

/-- **The upper seam window** at `(j,p)`: `ramSeamUpper` cut at `2X < pm`. -/
noncomputable def ramSeamUpW (H : ℝ) (N X : ℕ) (j p : ℕ) : Finset ℕ :=
  (ramSeamUpper H N X j).filter (fun m : ℕ => 2 * (X : ℝ) < (p : ℝ) * (m : ℝ))

/-- **The lower seam polynomial** (MR's `Σ_{Xe^{−1/H}≤m≤Xe^{1/H}} d_m/m^s` row). -/
noncomputable def ramSeamLoPoly (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ramGenPoly H P Q (ramSeamLoW H N X) b c t

/-- **The upper seam polynomial** (MR's `Σ_{2X≤m≤2Xe^{1/H}} d_m/m^s` row). -/
noncomputable def ramSeamUpPoly (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ramGenPoly H P Q (ramSeamUpW H N X) b c t

lemma ramSeamLoW_sub (H : ℝ) (N X : ℕ) (j p : ℕ) : ramSeamLoW H N X j p ⊆ Finset.Icc 1 N := by
  refine subset_trans (Finset.filter_subset _ _) ?_
  rw [ramSeam]; exact Finset.filter_subset _ _

lemma ramSeamUpW_sub (H : ℝ) (N X : ℕ) (j p : ℕ) : ramSeamUpW H N X j p ⊆ Finset.Icc 1 N := by
  refine subset_trans (Finset.filter_subset _ _) ?_
  rw [ramSeamUpper]; exact Finset.filter_subset _ _

/-- `e^{1/H} ≤ 2` for `H ≥ 2` — the workhorse of both window computations. -/
lemma exp_inv_H_le_two (H : ℝ) (hH : 2 ≤ H) : Real.exp (1 / H) ≤ 2 := by
  have hH0 : (0 : ℝ) < H := by linarith
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_half_le_two
  rw [div_le_div_iff₀ hH0 (by norm_num)]; linarith

/-- **The lower seam frequency window**: `X ≤ pm ≤ Xe^{1/H}`.  The lower cut is the filter
itself; the upper is the block/seam telescope `p < e^{(j+1)/H}`, `m < Xe^{−j/H}`. -/
lemma ramSeamLoW_window (H : ℝ) (N X P Q : ℕ) :
    ∀ σ ∈ ramGenDom H N P Q (ramSeamLoW H N X),
      (X : ℝ) ≤ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ∧
        ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ (X : ℝ) * Real.exp (1 / H) := by
  intro σ hσ
  rw [mem_ramGenDom] at hσ
  obtain ⟨-, hp, hm, hW⟩ := hσ
  rw [ramSeamLoW, Finset.mem_filter, ramSeam, Finset.mem_filter] at hW
  obtain ⟨⟨-, -, hmhi⟩, hcut⟩ := hW
  rw [ramQblock, Finset.mem_filter] at hp
  obtain ⟨-, hpp, -, hphi⟩ := hp
  rw [Finset.mem_Icc] at hm
  have hp0 : (0 : ℝ) < (σ.2.1 : ℝ) := by exact_mod_cast hpp.pos
  have hm0 : (0 : ℝ) < (σ.2.2 : ℝ) := by exact_mod_cast hm.1
  have hE2 : Real.exp (((σ.1 : ℝ) + 1) / H) * Real.exp (-(σ.1 : ℝ) / H) = Real.exp (1 / H) := by
    rw [← Real.exp_add]; congr 1; ring
  constructor
  · push_cast; linarith
  · have hstep : (σ.2.1 : ℝ) * (σ.2.2 : ℝ)
        ≤ Real.exp (((σ.1 : ℝ) + 1) / H) * ((X : ℝ) * Real.exp (-(σ.1 : ℝ) / H)) :=
      mul_le_mul hphi.le hmhi.le (by positivity) (by positivity)
    push_cast
    nlinarith [hE2]

/-- **The upper seam frequency window**: `2X ≤ pm ≤ 2Xe^{1/H}` — the `X ↦ 2X` rescale of the
lower one, and the source of the row's `4×` saving (`1/n² ≤ 1/(2X)²`). -/
lemma ramSeamUpW_window (H : ℝ) (N X P Q : ℕ) :
    ∀ σ ∈ ramGenDom H N P Q (ramSeamUpW H N X),
      2 * (X : ℝ) ≤ ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ∧
        ((σ.2.1 * σ.2.2 : ℕ) : ℝ) ≤ 2 * (X : ℝ) * Real.exp (1 / H) := by
  intro σ hσ
  rw [mem_ramGenDom] at hσ
  obtain ⟨-, hp, hm, hW⟩ := hσ
  rw [ramSeamUpW, Finset.mem_filter, ramSeamUpper, Finset.mem_filter] at hW
  obtain ⟨⟨-, -, hmhi⟩, hcut⟩ := hW
  rw [ramQblock, Finset.mem_filter] at hp
  obtain ⟨-, hpp, -, hphi⟩ := hp
  rw [Finset.mem_Icc] at hm
  have hp0 : (0 : ℝ) < (σ.2.1 : ℝ) := by exact_mod_cast hpp.pos
  have hm0 : (0 : ℝ) < (σ.2.2 : ℝ) := by exact_mod_cast hm.1
  have hE2 : Real.exp (((σ.1 : ℝ) + 1) / H) * Real.exp (-(σ.1 : ℝ) / H) = Real.exp (1 / H) := by
    rw [← Real.exp_add]; congr 1; ring
  constructor
  · push_cast; linarith
  · have hstep : (σ.2.1 : ℝ) * (σ.2.2 : ℝ)
        ≤ Real.exp (((σ.1 : ℝ) + 1) / H) * (2 * (X : ℝ) * Real.exp (-(σ.1 : ℝ) / H)) :=
      mul_le_mul hphi.le hmhi (by positivity) (by positivity)
    push_cast
    nlinarith [hE2]

/-- **M1a — the lower seam row.**  Frequencies in `[X, Xe^{1/H}]` (count `≤ 2eX/H + 1` by
`window_card_le`), bounded coefficients, so `moment_core_bound` gives
`(2T + 20N)·(2eX/H + 1)/X²` — sharper than `RamareErr`'s unfiltered row by the factor `e`. -/
theorem ramSeamLoPoly_moment (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N)
    (hP : 1 ≤ P) (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramSeamLoPoly H N X P Q b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp := exp_inv_H_le_two H hH
  unfold ramSeamLoPoly
  refine ramGenPoly_moment H hH0 N N P Q hP (ramSeamLoW H N X) (ramSeamLoW_sub H N X) b c hb hc
    (X : ℝ) ((X : ℝ) * Real.exp (1 / H)) (2 * Real.exp 1 * (X : ℝ) / H + 1) hXR ?_
    (ramSeamLoW_window H N X P Q) ?_ T hT
  · nlinarith
  · intro s hs
    refine window_card_le H (by linarith) X s (fun n hn => ?_)
    obtain ⟨h1, h2⟩ := hs n hn
    refine ⟨?_, h2⟩
    have : Real.exp (-(1 / H)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : (0 : ℝ) < 1 / H := by positivity
      linarith
    nlinarith

/-- **M1b — the upper seam row** (HERR-WAVE's `Z1`).  Frequencies in `(2X, 2Xe^{1/H}]`: the
count is `window_card_le` at `2X` (`4eX/H + 1`) and `1/n² ≤ 1/(2X)²` — the `4×` saving. -/
theorem ramSeamUpPoly_moment (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hP : 1 ≤ P) (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramSeamUpPoly H N X P Q b c t‖ ^ 2)
      ≤ (2 * T + 80 * (X : ℝ))
          * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hexp := exp_inv_H_le_two H hH
  unfold ramSeamUpPoly
  have hcast : ((4 * X : ℕ) : ℝ) = 4 * (X : ℝ) := by push_cast; ring
  have hcast2 : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by push_cast; ring
  refine le_trans (ramGenPoly_moment H hH0 N (4 * X) P Q hP (ramSeamUpW H N X)
    (ramSeamUpW_sub H N X) b c hb hc
    (2 * (X : ℝ)) (2 * (X : ℝ) * Real.exp (1 / H)) (4 * Real.exp 1 * (X : ℝ) / H + 1)
    (by linarith) ?_ (ramSeamUpW_window H N X P Q) ?_ T hT) ?_
  · rw [hcast]; nlinarith
  · intro s hs
    have h := window_card_le H (by linarith) (2 * X) s (fun n hn => ?_)
    · rw [hcast2] at h
      refine h.trans (le_of_eq ?_)
      ring
    · obtain ⟨h1, h2⟩ := hs n hn
      rw [hcast2]
      refine ⟨?_, h2⟩
      have hle : Real.exp (-(1 / H)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have : (0 : ℝ) < 1 / H := by positivity
        linarith
      nlinarith
  · rw [hcast]
    refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)


/-! ## M2 — the MR-range clean term, and the four-row identity

`RamareWindows.spoly_ramare_split` extends the clean summand over the FULL eq (16) cofactor
range; MR sums over `{m : X ≤ pm ≤ 2X}`.  Re-running the split at MR's range costs nothing
(the terms dropped carry `a_{pm} = 0` by `hasupp`) and buys everything: the `p ∣ m` repair
row is now confined to MR's range, and `seam_sum_identity_mr` — unconditional in the
coefficients — replaces the `hwin`-gated `seam_sum_identity`. -/

/-- **The MR-range clean term**: the Ramaré-weighted factorised summand over MR's own
cofactor range `ramHonMR`. -/
noncomputable def ramCleanMR (N X P Q : ℕ) (b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, ∑ m ∈ ramHonMR N X p,
    (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
      * ((blockOmega P Q m : ℂ) + 1)⁻¹

/-- **The MR-range `p²`-correction**: the `p ∣ m` overreach of `ramCleanMR`, repaired inside
MR's range (MR p.20's `1/P` row). -/
noncomputable def ramP2corrMR (N X P Q : ℕ) (a b c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m),
    (ramareWeight P Q p m • (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
      - (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
          * ((blockOmega P Q m : ℂ) + 1)⁻¹)

/-- MR's range sits inside the honest eq (16) range once `1 ≤ X` and `2X ≤ N`. -/
lemma ramHonMR_subset (N X p : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hp : 0 < p) :
    ramHonMR N X p ⊆ ((Finset.Icc 1 N).image (fun n => n / p)).filter
      (fun m => p * m ∈ Finset.Icc 1 N) := by
  intro m hm
  rw [ramHonMR, Finset.mem_filter] at hm
  obtain ⟨-, hlo, hhi⟩ := hm
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [mem_honest_cofactor hp]
  constructor
  · have h : (1 : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  · have h : ((p * m : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
    exact_mod_cast h

/-- **M2a — the Ramaré split at MR's OWN range.**  `spoly = cleanMR + p²MR + coprime tail`.
No `hwin`: the only support input is MR's own `hasupp` (`a` vanishes off `[X,2X]`), and it is
used exactly once — to drop the eq (16) cofactors outside `[X,2X]`, where `a_{pm} = 0`. -/
theorem spoly_ramare_split_mr (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (t : ℝ) :
    spoly N a t
      = ramCleanMR N X P Q b c t + ramP2corrMR N X P Q a b c t + ramCopTail N P Q a t := by
  classical
  have hper : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N),
        ramareWeight P Q p m •
          (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)))
        = (∑ m ∈ ramHonMR N X p,
            (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
              * ((blockOmega P Q m : ℂ) + 1)⁻¹)
          + ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m),
              (ramareWeight P Q p m •
                  (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
                - (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
                    * ((blockOmega P Q m : ℂ) + 1)⁻¹) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hPp, hpQ⟩, hpp⟩ := hp
    have hrestrict : (∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N),
        ramareWeight P Q p m *
          (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)))
        = ∑ m ∈ ramHonMR N X p,
          ramareWeight P Q p m *
            (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
      refine (Finset.sum_subset (ramHonMR_subset N X p hX hN hpp.pos) (fun m hm hmn => ?_)).symm
      have ha : a (p * m) = 0 := by
        by_contra h
        obtain ⟨h1, h2⟩ := hasupp _ h
        rw [mem_honest_cofactor hpp.pos] at hm
        refine hmn ?_
        rw [ramHonMR, Finset.mem_filter, Finset.mem_Icc]
        push_cast at h1 h2
        refine ⟨⟨?_, ?_⟩, h1, h2⟩
        · rcases Nat.eq_zero_or_pos m with rfl | hm0
          · simp at hm
          · exact hm0
        · exact le_trans (Nat.le_mul_of_pos_left m hpp.pos) hm.2
      rw [ha]
      simp
    simp only [Complex.real_smul] at hrestrict ⊢
    rw [hrestrict, Finset.sum_filter (fun m => p ∣ m), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hpm : p ∣ m
    · rw [if_pos hpm]; ring
    · rw [if_neg hpm, add_zero, hcoef p m hpp hPp hpQ hpm,
        ramareWeight_coprime P Q p m (hpp.coprime_iff_not_dvd.mpr hpm)]
      push_cast
      ring
  have hmain : (∑ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ∑ m ∈ ((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N),
        ramareWeight P Q p m •
          (a (p * m) / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)))
      = ramCleanMR N X P Q b c t + ramP2corrMR N X P Q a b c t := by
    rw [ramCleanMR, ramP2corrMR, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hper
  rw [spoly_ramare_eq16 N a P Q t, hmain, ramCopTail]

/-- **M2b — the dyadic regroup of the MR clean term** (MR p.19 bottom, at MR's range). -/
theorem cleanMR_dyadic (H : ℝ) (hH : 0 < H) (N X P Q : ℕ) (hP : 1 ≤ P) (b c : ℕ → ℂ) (t : ℝ) :
    ramCleanMR N X P Q b c t
      = ∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j,
          (c p / (↑p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
            * ∑ m ∈ ramHonMR N X p,
              (b m / (↑m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
                * ((blockOmega P Q m : ℂ) + 1)⁻¹ := by
  rw [ramCleanMR, prime_sum_dyadic_partition H hH P Q hP
    (fun p => ∑ m ∈ ramHonMR N X p,
      (b m * c p / (↑(p * m) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
        * ((blockOmega P Q m : ℂ) + 1)⁻¹)]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [natCast_mul_cpow p m]; ring

/-- **M2c — the two seam rows, unconditionally.**  Factoring `R_{j,H}` out of the dyadic MR
clean term leaves exactly `seam_sum_identity_mr`'s two windows: the lower seam minus the
upper seam.  No hypothesis on the coefficients is used. -/
theorem cleanMR_dyadic_sub_main (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (b c : ℕ → ℂ) (t : ℝ) :
    (∑ j ∈ ramI H P Q, ∑ p ∈ ramQblock H P Q j,
        (c p / (↑p : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
          * ∑ m ∈ ramHonMR N X p,
            (b m / (↑m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
              * ((blockOmega P Q m : ℂ) + 1)⁻¹)
      - (∑ j ∈ ramI H P Q, ramMain H N X P Q b c j t)
      = ramSeamLoPoly H N X P Q b c t - ramSeamUpPoly H N X P Q b c t := by
  rw [ramSeamLoPoly, ramSeamUpPoly, ramGenPoly, ramGenPoly,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ramMain, ramQ, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [ramR, ramSeamLoW, ramSeamUpW, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, ← mul_sub,
    seam_sum_identity_mr H hH N X P Q j p hX hp]

/-- **M2d — the exact four-row `ramErr` identity, with NO `hwin`.**
`ramErr = lower seam − upper seam + p²MR + coprime tail`. -/
theorem ramErr_decomp_mr (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N)
    (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (t : ℝ) :
    ramErr H N X P Q a b c t
      = ramSeamLoPoly H N X P Q b c t - ramSeamUpPoly H N X P Q b c t
        + ramP2corrMR N X P Q a b c t + ramCopTail N P Q a t := by
  have hH0 : (0 : ℝ) < H := by linarith
  rw [ramErr, spoly_ramare_split_mr N X P Q hX hN a b c hcoef hasupp t,
    cleanMR_dyadic H hH0 N X P Q hP b c t, ← cleanMR_dyadic_sub_main H hH N X P Q hX b c t]
  abel

/-! ## M2e — the `p²` row of the MR range as a `spoly` -/

/-- **The MR-range `p²` domain**: block-prime/cofactor pairs `(p,m)` with `p ∣ m` and
`X ≤ pm ≤ 2X`. -/
noncomputable def ramP2domMR (N X P Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((Finset.Icc P Q).filter Nat.Prime).sigma
    (fun p => (ramHonMR N X p).filter (fun m => p ∣ m))

/-- **The MR-range `p²` coefficient** at frequency `n` (supported on `p² ∣ n`, `X ≤ n ≤ 2X`). -/
noncomputable def ramP2coeffMR (N X P Q : ℕ) (a b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
    ((ramareWeight P Q σ.1 σ.2 : ℂ) * a (σ.1 * σ.2)
      - b σ.2 * c σ.1 * ((blockOmega P Q σ.2 : ℂ) + 1)⁻¹)

theorem ramP2corrMR_eq_spoly (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (a b c : ℕ → ℂ)
    (t : ℝ) :
    ramP2corrMR N X P Q a b c t = spoly N (ramP2coeffMR N X P Q a b c) t := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmaps : ∀ σ ∈ ((Finset.Icc P Q).filter Nat.Prime).sigma
      (fun p => (ramHonMR N X p).filter (fun m => p ∣ m)),
      σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨-, h2⟩ := hσ
    rw [Finset.mem_filter, ramHonMR, Finset.mem_filter] at h2
    obtain ⟨⟨-, hlo, hhi⟩, -⟩ := h2
    rw [Finset.mem_Icc]
    constructor
    · have h : (1 : ℝ) ≤ ((σ.1 * σ.2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((σ.1 * σ.2 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
      exact_mod_cast h
  rw [ramP2corrMR, Finset.sum_sigma', ← Finset.sum_fiberwise_of_maps_to hmaps, spoly]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [ramP2coeffMR, Finset.sum_div]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  rw [Complex.real_smul, ← mul_div_assoc, div_mul_eq_mul_div, div_sub_div_same, hσ.2]

/-- **M2e — the MR-range `p²` row.**  `moment_core_bound` at the `(2T+20N)·Σ‖·‖²/n²` grade. -/
theorem ramP2corrMR_moment (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (a b c : ℕ → ℂ)
    (T : ℝ) :
    (∫ t in (-T)..T, ‖ramP2corrMR N X P Q a b c t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ))
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
  have hcongr : (∫ t in (-T)..T, ‖ramP2corrMR N X P Q a b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖spoly N (ramP2coeffMR N X P Q a b c) t‖ ^ 2 :=
    intervalIntegral.integral_congr
      (fun t _ => by rw [ramP2corrMR_eq_spoly N X P Q hX hN a b c t])
  rw [hcongr]
  exact moment_core_bound N (ramP2coeffMR N X P Q a b c) T

lemma continuous_ramP2corrMR (N X P Q : ℕ) (a b c : ℕ → ℂ) :
    Continuous (ramP2corrMR N X P Q a b c) := by
  unfold ramP2corrMR
  refine continuous_finsetSum _ (fun p hp => continuous_finsetSum _ (fun m hm => ?_))
  rw [Finset.mem_filter] at hp
  rw [Finset.mem_filter, ramHonMR, Finset.mem_filter, Finset.mem_Icc] at hm
  have hpm : p * m ≠ 0 := Nat.mul_ne_zero hp.2.pos.ne' (by omega)
  exact ((continuous_cterm hpm (a (p * m))).const_smul _).sub
    ((continuous_cterm hpm (b m * c p)).mul continuous_const)

lemma continuous_ramSeamLoPoly (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) :
    Continuous (ramSeamLoPoly H N X P Q b c) :=
  continuous_ramGenPoly H N P Q (ramSeamLoW H N X) (ramSeamLoW_sub H N X) b c

lemma continuous_ramSeamUpPoly (H : ℝ) (N X P Q : ℕ) (b c : ℕ → ℂ) :
    Continuous (ramSeamUpPoly H N X P Q b c) :=
  continuous_ramGenPoly H N P Q (ramSeamUpW H N X) (ramSeamUpW_sub H N X) b c

/-! ## M3 — Lemma 12's mean square at the MR range, with NO `hwin` -/

lemma norm_add_sq_le_two (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith [norm_add_le u v, norm_nonneg u, norm_nonneg v, norm_nonneg (u + v),
    sq_nonneg (‖u‖ - ‖v‖)]

/-- **The four-row Cauchy–Schwarz split**: `‖g₁+g₂+g₃+g₄‖² ≤ 4Σ‖gᵢ‖²`, integrated. -/
theorem moment_split4 {f g₁ g₂ g₃ g₄ : ℝ → ℂ} (hf : Continuous f) (h1 : Continuous g₁)
    (h2 : Continuous g₂) (h3 : Continuous g₃) (h4 : Continuous g₄)
    (heq : ∀ t, f t = g₁ t + g₂ t + g₃ t + g₄ t) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖f t‖ ^ 2)
      ≤ 4 * ((∫ t in (-T)..T, ‖g₁ t‖ ^ 2) + (∫ t in (-T)..T, ‖g₂ t‖ ^ 2)
          + (∫ t in (-T)..T, ‖g₃ t‖ ^ 2) + (∫ t in (-T)..T, ‖g₄ t‖ ^ 2)) := by
  have hI : ∀ g : ℝ → ℂ, Continuous g →
      IntervalIntegrable (fun t => ‖g t‖ ^ 2) MeasureTheory.volume (-T) T :=
    fun g hg => (hg.norm.pow 2).intervalIntegrable (-T) T
  have i1 := (hI g₁ h1).const_mul 4
  have i2 := (hI g₂ h2).const_mul 4
  have i3 := (hI g₃ h3).const_mul 4
  have i4 := (hI g₄ h4).const_mul 4
  calc (∫ t in (-T)..T, ‖f t‖ ^ 2)
      ≤ ∫ t in (-T)..T, (4 * ‖g₁ t‖ ^ 2 + 4 * ‖g₂ t‖ ^ 2 + 4 * ‖g₃ t‖ ^ 2
          + 4 * ‖g₄ t‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on (by linarith) (hI f hf)
          (((i1.add i2).add i3).add i4) (fun t _ => ?_)
        rw [heq t, show g₁ t + g₂ t + g₃ t + g₄ t = (g₁ t + g₂ t) + (g₃ t + g₄ t) by ring]
        have k1 := norm_add_sq_le_two (g₁ t + g₂ t) (g₃ t + g₄ t)
        have k2 := norm_add_sq_le_two (g₁ t) (g₂ t)
        have k3 := norm_add_sq_le_two (g₃ t) (g₄ t)
        linarith
    _ = 4 * ((∫ t in (-T)..T, ‖g₁ t‖ ^ 2) + (∫ t in (-T)..T, ‖g₂ t‖ ^ 2)
          + (∫ t in (-T)..T, ‖g₃ t‖ ^ 2) + (∫ t in (-T)..T, ‖g₄ t‖ ^ 2)) := by
        rw [intervalIntegral.integral_add ((i1.add i2).add i3) i4,
          intervalIntegral.integral_add (i1.add i2) i3,
          intervalIntegral.integral_add i1 i2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        ring

/-- **M3a — the four-row error split at the MR range.** -/
theorem ramErr_moment_split_mr (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖ramErr H N X P Q a b c t‖ ^ 2)
      ≤ 4 * ((∫ t in (-T)..T, ‖ramSeamLoPoly H N X P Q b c t‖ ^ 2)
          + (∫ t in (-T)..T, ‖ramSeamUpPoly H N X P Q b c t‖ ^ 2)
          + (∫ t in (-T)..T, ‖ramP2corrMR N X P Q a b c t‖ ^ 2)
          + (∫ t in (-T)..T, ‖ramCopTail N P Q a t‖ ^ 2)) := by
  have hneg : (∫ t in (-T)..T, ‖-ramSeamUpPoly H N X P Q b c t‖ ^ 2)
      = ∫ t in (-T)..T, ‖ramSeamUpPoly H N X P Q b c t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => by rw [norm_neg])
  have h := moment_split4 (f := ramErr H N X P Q a b c)
    (g₁ := ramSeamLoPoly H N X P Q b c) (g₂ := fun t => -ramSeamUpPoly H N X P Q b c t)
    (g₃ := ramP2corrMR N X P Q a b c) (g₄ := ramCopTail N P Q a)
    (continuous_ramErr H N X P Q a b c) (continuous_ramSeamLoPoly H N X P Q b c)
    (continuous_ramSeamUpPoly H N X P Q b c).neg (continuous_ramP2corrMR N X P Q a b c)
    (continuous_ramCopTail N P Q a)
    (fun t => by rw [ramErr_decomp_mr H hH N X P Q hX hN hP a b c hcoef hasupp t]; ring) T hT
  rw [hneg] at h
  exact h

/-- **M3 — Lemma 12's mean square at MR's range: `hwin` RETIRED.**  The hypotheses are the
coefficient factorisation `hcoef`, the normalisations `‖b‖,‖c‖ ≤ 1`, MR's own dyadic support
`hasupp` of `a`, and the structural `2 ≤ H`, `1 ≤ X`, `2X ≤ N`, `1 ≤ P`, `0 ≤ T`.  The error
is four honest rows: the two seams of `seam_sum_identity_mr` (both at the `(T/X+1)/H` grade —
the upper one with the `4×` saving), the `p²` row confined to `[X,2X]`, and the coprime tail. -/
theorem lemma12_meansq_mr (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N)
    (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (4 * ((2 * T + 20 * (N : ℝ))
                  * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)
              + (2 * T + 80 * (X : ℝ))
                  * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
              + (2 * T + 20 * (N : ℝ))
                  * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
              + (2 * T + 20 * (N : ℝ))
                  * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                      ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  refine lemma12_meansq_of_windowErr H N X P Q a b c T _ hT ?_
  refine (ramErr_moment_split_mr H hH N X P Q hX hN hP a b c hcoef hasupp T hT).trans ?_
  gcongr
  · exact ramSeamLoPoly_moment H hH N X P Q hX hN hP b c hb hc T hT
  · exact ramSeamUpPoly_moment H hH N X P Q hX hP b c hb hc T hT
  · exact ramP2corrMR_moment N X P Q hX hN a b c T
  · exact ramCopTail_moment N P Q a T

/-- **M3 (exit) — the tail-free form.**  Under the §8.3 support pin (every frequency in
`supp a` carries a block prime) the coprime-tail row is identically `0`: three rows remain. -/
theorem lemma12_meansq_mr_blockSupport (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 2 * (4 * ((2 * T + 20 * (N : ℝ))
                  * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)
              + (2 * T + 80 * (X : ℝ))
                  * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
              + (2 * T + 20 * (N : ℝ))
                  * ∑ n ∈ Finset.Icc 1 N,
                      ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  refine lemma12_meansq_of_windowErr H N X P Q a b c T _ hT ?_
  refine (ramErr_moment_split_mr H hH N X P Q hX hN hP a b c hcoef hasupp T hT).trans ?_
  have h1 := ramSeamLoPoly_moment H hH N X P Q hX hN hP b c hb hc T hT
  have h2 := ramSeamUpPoly_moment H hH N X P Q hX hP b c hb hc T hT
  have h3 := ramP2corrMR_moment N X P Q hX hN a b c T
  have h4 := ramCopTail_moment_zero N P Q a hsupp T
  rw [h4]
  linarith

/-! ## M4 — the consumption form -/

/-- **M4a — the two seam rows at MR's normal form.**  With `N ≤ 2X` and `H ≤ X` (MR takes
`N = 2X`, `H = (log X)^A`) the lower row is `≤ (2T+40X)·7/(HX)` and the upper row
`≤ (2T+80X)·3/(HX)`; together they collapse to `520·(T/X + 1)/H`. -/
theorem seam_rows_grade (H : ℝ) (hH : 2 ≤ H) (N X : ℕ) (hX : 1 ≤ X)
    (hN2 : (N : ℝ) ≤ 2 * (X : ℝ)) (hHX : H ≤ (X : ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    (2 * T + 20 * (N : ℝ)) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)
        + (2 * T + 80 * (X : ℝ)) * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
      ≤ 520 * (T / (X : ℝ) + 1) / H := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hHX2 : H * (X : ℝ) ≤ (X : ℝ) ^ 2 := by nlinarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : (2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2 ≤ 7 / (H * (X : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hexpand : (2 * Real.exp 1 * (X : ℝ) / H + 1) * (H * (X : ℝ))
        = 2 * Real.exp 1 * (X : ℝ) ^ 2 + H * (X : ℝ) := by field_simp
    rw [hexpand]
    nlinarith [sq_nonneg (X : ℝ)]
  have h2 : (4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2 ≤ 3 / (H * (X : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hexpand : (4 * Real.exp 1 * (X : ℝ) / H + 1) * (H * (X : ℝ))
        = 4 * Real.exp 1 * (X : ℝ) ^ 2 + H * (X : ℝ) := by field_simp
    rw [hexpand]
    nlinarith [sq_nonneg (X : ℝ)]
  have hd1 : (0 : ℝ) ≤ (2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2 := by positivity
  have hd2 : (0 : ℝ) ≤ (4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2 := by positivity
  have hs1 : (2 * T + 20 * (N : ℝ)) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)
      ≤ (2 * T + 40 * (X : ℝ)) * (7 / (H * (X : ℝ))) :=
    mul_le_mul (by linarith) h1 hd1 (by linarith)
  have hs2 : (2 * T + 80 * (X : ℝ)) * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)
      ≤ (2 * T + 80 * (X : ℝ)) * (3 / (H * (X : ℝ))) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have e1 : (2 * T + 40 * (X : ℝ)) * (7 / (H * (X : ℝ)))
      + (2 * T + 80 * (X : ℝ)) * (3 / (H * (X : ℝ)))
      = (20 * T + 520 * (X : ℝ)) / (H * (X : ℝ)) := by field_simp; ring
  have e2 : 520 * (T / (X : ℝ) + 1) / H = (520 * T + 520 * (X : ℝ)) / (H * (X : ℝ)) := by
    field_simp
  refine le_trans (add_le_add hs1 hs2) ?_
  rw [e1, e2, div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- **M4 — the consumption form.**  Lemma 12 at the MR range, tail-free, with the two seam
rows collapsed onto MR's `(T/X + 1)/H` grade and the `p²` mass left in-statement (its
collapse to MR's `1/P` is the `Σ_{p≥P} p⁻²` zeta-tail — a separate stone).  This is the
`[−T,T]` shape the `U-1` consumer takes. -/
theorem lemma12_meansq_mr_consume (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hN2 : (N : ℝ) ≤ 2 * (X : ℝ)) (hHX : H ≤ (X : ℝ)) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 4160 * (T / (X : ℝ) + 1) / H
        + 8 * (2 * T + 20 * (N : ℝ))
            * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
  refine (lemma12_meansq_mr_blockSupport H hH N X P Q hX hN hP a b c hcoef hb hc hasupp
    hsupp T hT).trans ?_
  have hg := seam_rows_grade H hH N X hX hN2 hHX T hT
  have hbridge : (4160 : ℝ) * (T / (X : ℝ) + 1) / H = 8 * (520 * (T / (X : ℝ) + 1) / H) := by
    ring
  rw [hbridge]
  linarith

end Salt.MR
