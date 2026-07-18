/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.Basic
import Salt.ExpSum.DerivTest
import Salt.ExpSum.DerivTestK
import Salt.ExpSum.Kusmin
import Salt.ExpSum.ZetaBlock
import Salt.ExpSum.ZetaGrowth
import Salt.ExpSum.ZetaApprox
import Salt.ExpSum.Window

/-!
# The k-uniform Weyl strip family (`LITT-STRIP`)

For every `k ≥ 4` there is an ABSOLUTE constant `C` (outside the `k`-quantifier)
with
`‖ζ(σ + it)‖ ≤ C · t^{1/(2^{k+2}(k−1))} · (1 + log t)`
on the strip `σ ≥ 1 − 2^{−(k+2)}`, `σ ≤ 2`, for `t ≥ 4·(k!)^6`.

The power/width ratio `1/(k−1) → 0` is the Littlewood mechanism (convexity has
ratio `1` and saturates at `1/log t`); the absolute constant `C = 4096` is what
makes `LITT-LANDAU`'s loglog balance run.

## Design spine

Approximate formula (`norm_zeta_sub_approx_le`) at `N_t := ⌊t²⌋` (kills
error+pole); the truncated head `[1, M₀]` bounded trivially; the middle
`(M₀, N_t]` cut into `≤ 3(1+log t)` dyadic blocks, each phase-bounded by a
regime dispatch and Abel-weighted by `n^{−σ}`.  Prefix (non-`2N` top endpoint)
phase bounds are legal because `IsVdCBound` has general `ℤ` endpoints.

Rungs R1–R8 per the `LITT-STRIP` freeze (`docs/exploration/s3-a3-design.md`).
-/

namespace Salt.ExpSum

open Finset Real

/-! ## R1 — the Kusmin prefix block (`N ≥ t`, general top endpoint `x ≤ 2N`) -/

/-- **The Kusmin–Landau prefix block.**  A prefix `(N, x]` of the dyadic block
`(N, 2N]` (`N < x ≤ 2N`) in the large-argument regime `t ≤ N`.  The bound is the
same `2π(2N+1)/t` as the full block: the phase differences stay in the single
unit interval `[−1+δ, −δ]` on the whole `(N, 2N]`, so any prefix inherits it. -/
theorem zeta_block_kusmin_prefix (t : ℝ) (ht : 0 < t) (N : ℕ) (hN : t ≤ (N : ℝ))
    (hN1 : 1 ≤ N) (x : ℤ) (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)‖
      ≤ 2 * π * (2 * (N : ℝ) + 1) / t := by
  set b : ℕ := x.toNat with hb
  have hNb : N < b := by omega
  have hb2N : b ≤ 2 * N := by omega
  set f : ℕ → ℝ := fun j => phi t (j : ℤ) with hf
  set δ : ℝ := t / (2 * π * (2 * (N : ℝ) + 1)) with hδ
  -- reindex the ℤ-window to a ℕ-window and switch eR → eK
  have hsum : ∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)
      = ∑ n ∈ Finset.Ioc N b, eK (f n) := by
    apply Finset.sum_nbij' (i := fun n : ℤ => n.toNat) (j := fun k : ℕ => (k : ℤ))
    · intro n hn; rw [Finset.mem_Ioc] at hn ⊢; omega
    · intro k hk; rw [Finset.mem_Ioc] at hk ⊢; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn; omega
    · intro k hk; rw [Finset.mem_Ioc] at hk; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn
      rw [eR_eq_eK]; simp only [hf]
      rw [show ((n.toNat : ℤ)) = n from by omega]
  have hfval : ∀ j : ℕ, f j = -(t / (2 * π)) * Real.log (j : ℝ) := by
    intro j; simp only [hf, phi, Int.cast_natCast]
  have hgval : ∀ m : ℕ, f (m + 1) - f m
      = -(t / (2 * π)) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by
    intro m; rw [hfval (m + 1), hfval m]; push_cast; ring
  have hApos : 0 < t / (2 * π) := div_pos ht (by positivity)
  have hpi1 : (1 : ℝ) ≤ π := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
  have hδ2π : δ ≤ 1 / (2 * π) := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by positivity)]
    have ht2N1 : t ≤ 2 * (N : ℝ) + 1 := by linarith [hN, Nat.cast_nonneg (α := ℝ) N]
    nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr ht2N1)]
  have hδ12 : δ ≤ 1 / 2 := by
    have h : 1 / (2 * π) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hpi1]
    linarith [hδ2π]
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos ht (by positivity)
  have hg_ub : ∀ n : ℕ, N < n → n ≤ b →
      f (n + 1) - f n ≤ ((-1 : ℤ) : ℝ) + 1 - δ := by
    intro n hlt hle
    have hle2N : n ≤ 2 * N := le_trans hle hb2N
    have hn1 : 1 ≤ n := by omega
    have hLlb := log_succ_sub_ge n hn1
    have hn12N : (n : ℝ) + 1 ≤ 2 * (N : ℝ) + 1 := by
      have : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hle2N
      linarith
    have hstep1 : t / (2 * π) * (1 / ((n : ℝ) + 1))
        ≤ t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLlb (le_of_lt hApos)
    have hstep2 : δ ≤ t / (2 * π) * (1 / ((n : ℝ) + 1)) := by
      rw [mul_one_div, hδ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hn12N
        (mul_nonneg (le_of_lt ht) (le_of_lt (show (0 : ℝ) < 2 * π by positivity)))]
    have hcomb : δ ≤ t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      le_trans hstep2 hstep1
    rw [hgval n, neg_mul]; push_cast; linarith [hcomb]
  have hg_lb : ∀ n : ℕ, N < n → n ≤ b →
      ((-1 : ℤ) : ℝ) + δ ≤ f (n + 1) - f n := by
    intro n hlt hle
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hLub := log_succ_sub_le n hn1
    have htn : t ≤ (n : ℝ) := by
      have : (N : ℝ) < (n : ℝ) := by exact_mod_cast hlt
      linarith
    have hstep1 : t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ t / (2 * π) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLub (le_of_lt hApos)
    have hbound : t / (2 * π) * (1 / (n : ℝ)) ≤ 1 - δ := by
      rw [mul_one_div, div_div]
      have h1 : t / (2 * π * (n : ℝ)) ≤ 1 / (2 * π) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr htn)]
      have h3 : 1 / (2 * π) + 1 / (2 * π) ≤ 1 := by
        rw [← add_div, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
      linarith [h1, hδ2π, h3]
    have hcomb : t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 - δ :=
      le_trans hstep1 hbound
    rw [hgval n, neg_mul]; push_cast; linarith [hcomb]
  have hmono : ∀ n : ℕ, N < n → n < b →
      f (n + 1) - f n ≤ f (n + 1 + 1) - f (n + 1) := by
    intro n hlt hlt2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hratio : ((n : ℝ) + 2) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / (n : ℝ) := by
      rw [div_le_div_iff₀ hn1 hn0]; nlinarith
    have hlogle :=
      Real.log_le_log (show (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1) by positivity) hratio
    rw [Real.log_div (by positivity) (ne_of_gt hn1),
      Real.log_div (ne_of_gt hn1) (ne_of_gt hn0)] at hlogle
    have he2 : f (n + 1 + 1) - f (n + 1)
        = -(t / (2 * π)) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
      rw [hfval (n + 1 + 1), hfval (n + 1)]; push_cast; ring
    rw [hgval n, he2, neg_mul, neg_mul]
    linarith [mul_le_mul_of_nonneg_left hlogle (le_of_lt hApos)]
  have hkl := kusmin_landau (f := f) (a := N) (b := b) (δ := δ) (m := -1)
    hδ0 hδ12 hg_lb hg_ub hmono
  rw [hsum]
  refine le_trans hkl (le_of_eq ?_)
  rw [hδ, one_div_div]

/-! ## R2 — the van der Corput prefix block (explicit engine constant 144) -/

/-- `2k ≤ 2^k` for `k ≥ 2` (the `c`-grade exponent bound `4k/2^k ≤ 2`). -/
lemma two_mul_le_two_pow (k : ℕ) (hk : 2 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    have h2K : 2 ≤ 2 ^ K :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * (K + 1) = 2 * K + 2 := by ring
      _ ≤ 2 ^ K + 2 ^ K := by omega
      _ = 2 ^ (K + 1) := by rw [pow_succ]; ring

/-- Monotonicity of the vdC bound constant: enlarging `C` preserves the bound
(the RHS bracket `c^{4/2^k}·(…)` is nonnegative). -/
lemma isVdCBound_mono {k : ℕ} {C C' : ℝ} (hC : IsVdCBound k C) (hCC' : C ≤ C') :
    IsVdCBound k C' := by
  intro f a b lam c hab hlam hc hlo hhi
  refine le_trans (hC f a b lam c hab hlam hc hlo hhi) ?_
  have hX1 : (0 : ℝ) ≤ c ^ (4 / (2 : ℝ) ^ k) := Real.rpow_nonneg (by linarith) _
  have hbase : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hX2 : (0 : ℝ) ≤ ((b : ℝ) - a) * lam ^ (1 / ((2 : ℝ) ^ k - 2))
      + ((b : ℝ) - a) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(1 / ((2 : ℝ) ^ k - 2))) :=
    add_nonneg
      (mul_nonneg hbase (le_of_lt (Real.rpow_pos_of_pos hlam _)))
      (mul_nonneg (Real.rpow_nonneg hbase _) (le_of_lt (Real.rpow_pos_of_pos hlam _)))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hX1) hX2

/-- **The k-uniform van der Corput engine constant.**  `IsVdCBound k 16` for
every `k ≥ 2`: `16` is the fixed point of `C ↦ 4√C`.  Base `IsVdCBound 2 8 ≤ 16`
by `C`-monotonicity; step `4·√16 = 16` exactly.  A reusable gift beyond this node. -/
lemma isVdCBound_16 (k : ℕ) (hk : 2 ≤ k) : IsVdCBound k 16 := by
  induction k, hk using Nat.le_induction with
  | base => exact isVdCBound_mono isVdCBound_two (by norm_num)
  | succ K hK ih =>
    have hsqrt : (4 : ℝ) * Real.sqrt 16 = 16 := by
      have h : Real.sqrt 16 = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      rw [h]; norm_num
    have := isVdCBound_succ K hK 16 (by norm_num) ih
    rwa [hsqrt] at this

/-- **The van der Corput prefix block, explicit constant 144.**  For `k ≥ 2` and a
prefix `(N, x]` of `(N, 2N]` (`N < x ≤ 2N`), with `λ` the honest lower bound on the
`k`-th-derivative magnitude, the block obeys
`‖∑_{N<n≤x} n^{−it}‖ ≤ 144·(N·λ^α + N^β·λ^{−α})` (`α = 1/(2^k−2)`, `β = 1−4/2^k`).
`144 = 16·9`: the engine constant `16` times the `c`-grade `c^{4/2^k} ≤ 3^{4k/2^k} ≤ 9`. -/
theorem zeta_block_vdC_prefix (k : ℕ) (hk : 2 ≤ k)
    (t : ℝ) (N : ℕ) (lam : ℝ) (x : ℤ) (ht : 0 < t) (hkN : k ≤ N)
    (hlam : lam = t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹)
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)‖
      ≤ 144 * ((N : ℝ) * lam ^ (1 / ((2 : ℝ) ^ k - 2))
          + (N : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(1 / ((2 : ℝ) ^ k - 2)))) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlam
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have htp : (0 : ℝ) < t / (2 * π) := div_pos ht (by positivity)
  have hfacpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  set g : ℤ → ℝ := fun m => (-1 : ℝ) ^ (i + 1) * phi t m with hg
  have hlampos : (0 : ℝ) < lam := by
    rw [hlam]; exact mul_pos (mul_pos htp hfacpos) (inv_pos.mpr (by positivity))
  -- window ratio c = (2N+k)^k/N^k ≤ 3^k, and c^{4/2^k} ≤ 9
  set cc : ℝ := ((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1) / (N : ℝ) ^ (i + 1) with hcc
  have hNk_pos : (0 : ℝ) < (N : ℝ) ^ (i + 1) := by positivity
  have hnum_pos : (0 : ℝ) < ((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1) := by positivity
  have hNle2N : (N : ℝ) ≤ ((2 * N + (i + 1) : ℕ) : ℝ) := by push_cast; linarith
  have hcc1 : 1 ≤ cc := by
    rw [hcc, one_le_div hNk_pos]
    exact pow_le_pow_left₀ (le_of_lt hNR) hNle2N _
  have hcc0 : (0 : ℝ) ≤ cc := le_trans zero_le_one hcc1
  have hratio : ((2 * N + (i + 1) : ℕ) : ℝ) / (N : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hNR]; push_cast
    have : (i : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hkN
    linarith
  have hcc3 : cc ≤ (3 : ℝ) ^ (i + 1) := by
    rw [hcc, ← div_pow]
    exact pow_le_pow_left₀ (by positivity) hratio _
  have hclam : cc * lam = t / (2 * π) * (i.factorial : ℝ) * ((N : ℝ) ^ (i + 1))⁻¹ := by
    rw [hcc, hlam]
    have h1 : ((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1) ≠ 0 := ne_of_gt hnum_pos
    have h2 : ((N : ℝ) ^ (i + 1)) ≠ 0 := ne_of_gt hNk_pos
    field_simp
  -- the c-grade constant: cc^{4/2^{i+1}} ≤ 9
  have hcc9 : cc ^ (4 / (2 : ℝ) ^ (i + 1)) ≤ 9 := by
    have h1 : cc ^ (4 / (2 : ℝ) ^ (i + 1))
        ≤ ((3 : ℝ) ^ (i + 1)) ^ (4 / (2 : ℝ) ^ (i + 1)) :=
      Real.rpow_le_rpow hcc0 hcc3 (by positivity)
    refine le_trans h1 ?_
    rw [← Real.rpow_natCast (3 : ℝ) (i + 1), ← Real.rpow_mul (by norm_num)]
    have hle2 : ((i + 1 : ℕ) : ℝ) * (4 / (2 : ℝ) ^ (i + 1)) ≤ 2 := by
      have hpp : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
      have hnat : 2 * (i + 1) ≤ 2 ^ (i + 1) := two_mul_le_two_pow (i + 1) (by omega)
      have hnatR : (2 : ℝ) * ((i : ℝ) + 1) ≤ (2 : ℝ) ^ (i + 1) := by
        have h := (Nat.cast_le (α := ℝ)).mpr hnat; push_cast at h; linarith
      rw [← mul_div_assoc, div_le_iff₀ hpp]; push_cast; nlinarith [hnatR]
    calc (3 : ℝ) ^ (((i + 1 : ℕ) : ℝ) * (4 / (2 : ℝ) ^ (i + 1)))
        ≤ (3 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle2
      _ = 9 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  -- apply the engine at a = N, b = x
  have hab : (N : ℤ) ≤ x := le_of_lt hx1
  have hbase := isVdCBound_16 (i + 1) hk g (N : ℤ) x lam cc hab hlampos hcc1
    (fun n h1 h2 => by rw [hlam]; exact (zeta_dk_window t ht i N hN1 n h1 (by omega)).1)
    (fun n h1 h2 => by rw [hclam]; exact (zeta_dk_window t ht i N hN1 n h1 (by omega)).2)
  have hnorm : ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (g n)‖
      = ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)‖ := by
    simp only [hg]; exact norm_sum_eR_signed _ (phi t) (i + 1)
  rw [← hnorm]
  refine le_trans hbase ?_
  -- prefix length (x − N) ≤ N; sharpen the bracket
  set α : ℝ := 1 / ((2 : ℝ) ^ (i + 1) - 2) with hα
  set β : ℝ := 1 - 4 / (2 : ℝ) ^ (i + 1) with hβ
  have hβ0 : (0 : ℝ) ≤ β := by
    rw [hβ]; have : (4 : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpp : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
    rw [sub_nonneg, div_le_one hpp]; linarith
  have hxNnn : (0 : ℝ) ≤ (x : ℝ) - (N : ℤ) := by
    have : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast le_of_lt hx1
    push_cast; linarith
  have hxNle : (x : ℝ) - (N : ℤ) ≤ (N : ℝ) := by
    have : (x : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hx2
    push_cast; linarith
  have hlamα : (0 : ℝ) ≤ lam ^ α := le_of_lt (Real.rpow_pos_of_pos hlampos _)
  have hlamnα : (0 : ℝ) ≤ lam ^ (-α) := le_of_lt (Real.rpow_pos_of_pos hlampos _)
  have hbrk : ((x : ℝ) - (N : ℤ)) * lam ^ α
        + ((x : ℝ) - (N : ℤ)) ^ β * lam ^ (-α)
      ≤ (N : ℝ) * lam ^ α + (N : ℝ) ^ β * lam ^ (-α) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hxNle hlamα
    · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hxNnn hxNle hβ0) hlamnα
  have hbx_nonneg : (0 : ℝ) ≤ ((x : ℝ) - (N : ℤ)) * lam ^ α
      + ((x : ℝ) - (N : ℤ)) ^ β * lam ^ (-α) :=
    add_nonneg (mul_nonneg hxNnn hlamα)
      (mul_nonneg (Real.rpow_nonneg hxNnn _) hlamnα)
  have hcoef : 16 * cc ^ (4 / (2 : ℝ) ^ (i + 1)) ≤ 144 := by
    nlinarith [hcc9, hcc0]
  calc 16 * cc ^ (4 / (2 : ℝ) ^ (i + 1))
        * (((x : ℝ) - (N : ℤ)) * lam ^ α + ((x : ℝ) - (N : ℤ)) ^ β * lam ^ (-α))
      ≤ 144 * (((x : ℝ) - (N : ℤ)) * lam ^ α
          + ((x : ℝ) - (N : ℤ)) ^ β * lam ^ (-α)) :=
        mul_le_mul_of_nonneg_right hcoef hbx_nonneg
    _ ≤ 144 * ((N : ℝ) * lam ^ α + (N : ℝ) ^ β * lam ^ (-α)) :=
        mul_le_mul_of_nonneg_left hbrk (by norm_num)

/-! ## R3 — the collapsed prefix block (explicit constant 288) -/

/-- **The collapsed prefix block bound.**  On the honest van der Corput window
`λ ∈ [N^{−3+8/2^k}, N^{−1}]`, the two-term prefix bound collapses to the single
power `‖∑_{N<n≤x} n^{−it}‖ ≤ 288·N^{1−1/(2^k−2)}` (`288 = 144·2`; both terms are
`≤ N^{1−α}`, the `β`-arm identity `α(2^k−2) = 1` being exact). -/
theorem zeta_block_prefix_collapse (k : ℕ) (hk : 2 ≤ k)
    (t : ℝ) (N : ℕ) (lam : ℝ) (x : ℤ) (ht : 0 < t) (hkN : k ≤ N)
    (hlam : lam = t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹)
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N)
    (hrlo : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) ≤ lam) (hrhi : lam ≤ (N : ℝ) ^ (-1 : ℝ)) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)‖
      ≤ 288 * (N : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) := by
  have hb := zeta_block_vdC_prefix k hk t N lam x ht hkN hlam hx1 hx2
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have h2k : (4 : ℝ) ≤ (2 : ℝ) ^ k := four_le_two_pow k hk
  set p : ℝ := (2 : ℝ) ^ k with hp
  set α : ℝ := 1 / (p - 2) with hαdef
  set β : ℝ := 1 - 4 / p with hβdef
  have hppos : (0 : ℝ) < p := by rw [hp]; positivity
  have hp2ne : p - 2 ≠ 0 := ne_of_gt (by linarith [h2k])
  have hα0 : 0 < α := by rw [hαdef]; exact div_pos one_pos (by linarith [h2k])
  have hlampos : (0 : ℝ) < lam := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hrlo
  have hlamnn : (0 : ℝ) ≤ lam := le_of_lt hlampos
  have hterm1 : (N : ℝ) * lam ^ α ≤ (N : ℝ) ^ (1 - α) := by
    have h1 : lam ^ α ≤ (N : ℝ) ^ (-α) := by
      have hstep := Real.rpow_le_rpow hlamnn hrhi (le_of_lt hα0)
      rwa [← Real.rpow_mul (le_of_lt hNpos), show (-1 : ℝ) * α = -α from by ring] at hstep
    calc (N : ℝ) * lam ^ α ≤ (N : ℝ) * (N : ℝ) ^ (-α) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
      _ = (N : ℝ) ^ (1 - α) := by
          nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
          rw [← Real.rpow_add hNpos, show (1 : ℝ) + (-α) = 1 - α from by ring]
  have hterm2 : (N : ℝ) ^ β * lam ^ (-α) ≤ (N : ℝ) ^ (1 - α) := by
    set M : ℝ := (N : ℝ) ^ (-3 + 8 / p) with hM
    have hMpos : (0 : ℝ) < M := Real.rpow_pos_of_pos hNpos _
    have hlaminv : lam ^ (-α) ≤ M ^ (-α) := by
      rw [Real.rpow_neg hlamnn, Real.rpow_neg (le_of_lt hMpos)]
      exact inv_anti₀ (Real.rpow_pos_of_pos hMpos _)
        (Real.rpow_le_rpow (le_of_lt hMpos) hrlo (le_of_lt hα0))
    have hstep : (N : ℝ) ^ β * lam ^ (-α) ≤ (N : ℝ) ^ β * M ^ (-α) :=
      mul_le_mul_of_nonneg_left hlaminv (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hcombine : (N : ℝ) ^ β * M ^ (-α) = (N : ℝ) ^ (1 - α) := by
      rw [hM, ← Real.rpow_mul (le_of_lt hNpos), ← Real.rpow_add hNpos]
      congr 1
      rw [hβdef, hαdef]; field_simp; ring
    rw [← hcombine]; exact hstep
  refine le_trans hb ?_
  have hsum : (N : ℝ) * lam ^ α + (N : ℝ) ^ β * lam ^ (-α) ≤ 2 * (N : ℝ) ^ (1 - α) := by
    linarith [hterm1, hterm2]
  calc 144 * ((N : ℝ) * lam ^ α + (N : ℝ) ^ β * lam ^ (-α))
      ≤ 144 * (2 * (N : ℝ) ^ (1 - α)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 288 * (N : ℝ) ^ (1 - α) := by ring

/-! ## R4 — Stone A: the three window discharges (all with `x`-prefix) -/

/-- **R4a — the `k ≥ 4` window discharge.**  On the honest factorial-shifted
window `t ∈ [N^{k−2}/(k−2)!, N^{k−1}/(k−1)!]` with floor `N ≥ (k!)^6`, the prefix
block collapses to `288·N^{1−1/(2^k−2)}`.  Mirrors `zeta_block_window`'s
λ-sandwich, then applies `zeta_block_prefix_collapse`. -/
theorem zeta_window_prefix (k : ℕ) (hk : 4 ≤ k) (t : ℝ) (N : ℕ) (x : ℤ)
    (hN0 : (k.factorial : ℝ) ^ 6 ≤ (N : ℝ))
    (hlo : (N : ℝ) ^ ((k : ℝ) - 2) / ((k - 2).factorial : ℝ) ≤ t)
    (hhi : t ≤ (N : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ))
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)‖
      ≤ 288 * (N : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) := by
  have hfac1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (one_le_pow₀ hfac1) hN0
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hkN : k ≤ N := by
    have h1 : (k : ℝ) ≤ (N : ℝ) :=
      calc (k : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial k
        _ ≤ (k.factorial : ℝ) ^ 6 := le_self_pow₀ hfac1 (by norm_num)
        _ ≤ (N : ℝ) := hN0
    exact_mod_cast h1
  have hπpos : (0 : ℝ) < π := Real.pi_pos
  have h2πpos : (0 : ℝ) < 2 * π := by positivity
  have hf1 : (1 : ℝ) ≤ ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
  have hf2 : (1 : ℝ) ≤ ((k - 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 2)
  have hf1pos : (0 : ℝ) < ((k - 1).factorial : ℝ) := lt_of_lt_of_le one_pos hf1
  have hf2pos : (0 : ℝ) < ((k - 2).factorial : ℝ) := lt_of_lt_of_le one_pos hf2
  have hbaseN : 0 < 2 * N + k := by omega
  have hbase_pos : (0 : ℝ) < ((2 * N + k : ℕ) : ℝ) := by exact_mod_cast hbaseN
  have hden_pos : (0 : ℝ) < ((2 * N + k : ℕ) : ℝ) ^ k := pow_pos hbase_pos k
  have hDne : (((2 * N + k : ℕ) : ℝ) ^ k) ≠ 0 := ne_of_gt hden_pos
  have htpos : 0 < t := by
    have hp : (0 : ℝ) < (N : ℝ) ^ ((k : ℝ) - 2) / ((k - 2).factorial : ℝ) :=
      div_pos (Real.rpow_pos_of_pos hNpos _) hf2pos
    linarith
  set lam : ℝ := t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹
    with hlam_def
  have hlam_eq :
      lam * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k)) = t * ((k - 1).factorial : ℝ) := by
    rw [hlam_def]; field_simp
  have hbase_up : ((2 * N + k : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
    have h : 2 * N + k ≤ 3 * N := by omega
    calc ((2 * N + k : ℕ) : ℝ) ≤ ((3 * N : ℕ) : ℝ) := by exact_mod_cast h
      _ = 3 * (N : ℝ) := by push_cast; ring
  have hbase_lo : 2 * (N : ℝ) ≤ ((2 * N + k : ℕ) : ℝ) := by
    have h : 2 * N ≤ 2 * N + k := by omega
    calc 2 * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * N + k : ℕ) : ℝ) := by exact_mod_cast h
  have hden_up : ((2 * N + k : ℕ) : ℝ) ^ k ≤ (3 : ℝ) ^ k * (N : ℝ) ^ k := by
    calc ((2 * N + k : ℕ) : ℝ) ^ k ≤ (3 * (N : ℝ)) ^ k :=
          pow_le_pow_left₀ (le_of_lt hbase_pos) hbase_up k
      _ = (3 : ℝ) ^ k * (N : ℝ) ^ k := by rw [mul_pow]
  have hden_lo : (2 : ℝ) ^ k * (N : ℝ) ^ k ≤ ((2 * N + k : ℕ) : ℝ) ^ k := by
    calc (2 : ℝ) ^ k * (N : ℝ) ^ k = (2 * (N : ℝ)) ^ k := by rw [mul_pow]
      _ ≤ ((2 * N + k : ℕ) : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hbase_lo k
  have hmargin : 2 * π * (3 : ℝ) ^ k ≤ (N : ℝ) ^ (1 - 8 / (2 : ℝ) ^ k) := by
    have hs1 : 2 * π * (3 : ℝ) ^ k ≤ 8 * (3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_le_four]) (by positivity)
    have hs2 : (8 : ℝ) * (3 : ℝ) ^ k ≤ (k.factorial : ℝ) ^ 3 := by
      exact_mod_cast eight_mul_three_pow_le_factorial_cube k hk
    have hhalf : ((k.factorial : ℝ) ^ 6) ^ (1 / 2 : ℝ) = (k.factorial : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast (k.factorial : ℝ) 6, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast (k.factorial : ℝ) 3]
      norm_num
    have hs3 : (k.factorial : ℝ) ^ 3 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← hhalf]; exact Real.rpow_le_rpow (by positivity) hN0 (by norm_num)
    have hs4 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 - 8 / (2 : ℝ) ^ k) := by
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ k :=
        calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
          _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
      have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hbnd : 8 / (2 : ℝ) ^ k ≤ 1 / 2 := by
        rw [div_le_div_iff₀ h2kpos (by norm_num)]; linarith
      linarith
    linarith [hs1, hs2, hs3, hs4]
  have hnum : (N : ℝ) ^ ((k : ℝ) - 2) ≤ t * ((k - 1).factorial : ℝ) := by
    have e1 : (N : ℝ) ^ ((k : ℝ) - 2) ≤ t * ((k - 2).factorial : ℝ) :=
      (div_le_iff₀ hf2pos).mp hlo
    have hfle : ((k - 2).factorial : ℝ) ≤ ((k - 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : k - 2 ≤ k - 1)
    exact le_trans e1 (mul_le_mul_of_nonneg_left hfle (le_of_lt htpos))
  have hcore : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k))
      ≤ t * ((k - 1).factorial : ℝ) := by
    have hA : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k))
        ≤ (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * ((3 : ℝ) ^ k * (N : ℝ) ^ k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_up (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hB : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * ((3 : ℝ) ^ k * (N : ℝ) ^ k))
        ≤ (N : ℝ) ^ ((k : ℝ) - 2) := by
      have heq1 : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * ((3 : ℝ) ^ k * (N : ℝ) ^ k))
          = (2 * π * (3 : ℝ) ^ k) * (N : ℝ) ^ ((-3 + 8 / (2 : ℝ) ^ k) + (k : ℝ)) := by
        rw [← Real.rpow_natCast (N : ℝ) k,
            Real.rpow_add hNpos (-3 + 8 / (2 : ℝ) ^ k) (k : ℝ)]
        ring
      rw [heq1]
      have heq2 : (N : ℝ) ^ (1 - 8 / (2 : ℝ) ^ k)
            * (N : ℝ) ^ ((-3 + 8 / (2 : ℝ) ^ k) + (k : ℝ)) = (N : ℝ) ^ ((k : ℝ) - 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      rw [← heq2]
      exact mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg (le_of_lt hNpos) _)
    exact le_trans (le_trans hA hB) hnum
  have hrlo : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) ≤ lam := by
    rw [← hlam_eq] at hcore
    exact le_of_mul_le_mul_right hcore (mul_pos h2πpos hden_pos)
  have hnum_up : t * ((k - 1).factorial : ℝ) ≤ (N : ℝ) ^ ((k : ℝ) - 1) :=
    (le_div_iff₀ hf1pos).mp hhi
  have hconst1 : (1 : ℝ) ≤ 2 * π * (2 : ℝ) ^ k := by
    have h2π1 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have h2k1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc (1 : ℝ) ≤ 2 * π := h2π1
      _ ≤ 2 * π * (2 : ℝ) ^ k := le_mul_of_one_le_right (le_of_lt h2πpos) h2k1
  have hcore_up : t * ((k - 1).factorial : ℝ)
      ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k)) := by
    have hA' : (N : ℝ) ^ ((k : ℝ) - 1)
        ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * ((2 : ℝ) ^ k * (N : ℝ) ^ k)) := by
      have heq : (N : ℝ) ^ (-1 : ℝ) * (2 * π * ((2 : ℝ) ^ k * (N : ℝ) ^ k))
          = (2 * π * (2 : ℝ) ^ k) * (N : ℝ) ^ ((-1 : ℝ) + (k : ℝ)) := by
        rw [← Real.rpow_natCast (N : ℝ) k, Real.rpow_add hNpos (-1) (k : ℝ)]
        ring
      rw [heq]
      have heq2 :
          (N : ℝ) ^ ((k : ℝ) - 1) = (1 : ℝ) * (N : ℝ) ^ ((-1 : ℝ) + (k : ℝ)) := by
        rw [one_mul]
        congr 1
        ring
      rw [heq2]
      exact mul_le_mul_of_nonneg_right hconst1 (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hB' : (N : ℝ) ^ (-1 : ℝ) * (2 * π * ((2 : ℝ) ^ k * (N : ℝ) ^ k))
        ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_lo (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNpos) _)
    exact le_trans hnum_up (le_trans hA' hB')
  have hrhi : lam ≤ (N : ℝ) ^ (-1 : ℝ) := by
    rw [← hlam_eq] at hcore_up
    exact le_of_mul_le_mul_right hcore_up (mul_pos h2πpos hden_pos)
  exact zeta_block_prefix_collapse k (by omega) t N lam x htpos hkN hlam_def hx1 hx2 hrlo hrhi

/-- **R4b — the `k = 3` seam (third-derivative regime).**  On the window
`t ∈ [27π·N, N²/2]` with floor `N ≥ 3`, the prefix block collapses to
`288·N^{5/6}`.  Mirrors `zeta_block_window_three`, then `zeta_block_prefix_collapse 3`. -/
theorem zeta_seam_prefix (t : ℝ) (N : ℕ) (x : ℤ) (hN3 : 3 ≤ N)
    (hlo : 27 * π * (N : ℝ) ≤ t)
    (hhi : t ≤ (N : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ))
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)‖
      ≤ 288 * (N : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ 3 - 2)) := by
  have hNRpos : (0 : ℝ) < (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    linarith
  have hπpos : (0 : ℝ) < π := Real.pi_pos
  have h2πpos : (0 : ℝ) < 2 * π := by positivity
  have htpos : 0 < t := lt_of_lt_of_le (mul_pos (by positivity) hNRpos) hlo
  have hbaseN : 0 < 2 * N + 3 := by omega
  have hbase_pos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) := by exact_mod_cast hbaseN
  have hden_pos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) ^ 3 := pow_pos hbase_pos 3
  have hDne : (((2 * N + 3 : ℕ) : ℝ) ^ 3) ≠ 0 := ne_of_gt hden_pos
  have hfac2 : ((3 - 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  set lam : ℝ := t / (2 * π) * ((3 - 1).factorial : ℝ) * (((2 * N + 3 : ℕ) : ℝ) ^ 3)⁻¹
    with hlam_def
  have hlam_eq0 :
      lam * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) = t * ((3 - 1).factorial : ℝ) := by
    rw [hlam_def]; field_simp
  have hlam_eq : lam * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) = 2 * t := by
    rw [hlam_eq0, hfac2]; ring
  have hue : (N : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ) = (N : ℝ) ^ 2 / 2 := by
    have e2 : ((3 : ℝ) - 1) = ((2 : ℕ) : ℝ) := by norm_num
    rw [hfac2, e2, Real.rpow_natCast]
  rw [hue] at hhi
  have hden_up : ((2 * N + 3 : ℕ) : ℝ) ^ 3 ≤ 27 * (N : ℝ) ^ 3 := by
    have h : ((2 * N + 3 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      have hn : 2 * N + 3 ≤ 3 * N := by omega
      calc ((2 * N + 3 : ℕ) : ℝ) ≤ ((3 * N : ℕ) : ℝ) := by exact_mod_cast hn
        _ = 3 * (N : ℝ) := by push_cast; ring
    calc ((2 * N + 3 : ℕ) : ℝ) ^ 3 ≤ (3 * (N : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h 3
      _ = 27 * (N : ℝ) ^ 3 := by ring
  have hden_lo : 8 * (N : ℝ) ^ 3 ≤ ((2 * N + 3 : ℕ) : ℝ) ^ 3 := by
    have h : 2 * (N : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by
      have hn : 2 * N ≤ 2 * N + 3 := by omega
      calc 2 * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 * N + 3 : ℕ) : ℝ) := by exact_mod_cast hn
    calc 8 * (N : ℝ) ^ 3 = (2 * (N : ℝ)) ^ 3 := by ring
      _ ≤ ((2 * N + 3 : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
  have hprod : (N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ 3 = (N : ℝ) := by
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hNRpos,
        show (-2 : ℝ) + ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hcore_lo :
      (N : ℝ) ^ (-2 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) ≤ 2 * t := by
    have hA : (N : ℝ) ^ (-2 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3))
        ≤ (N : ℝ) ^ (-2 : ℝ) * (2 * π * (27 * (N : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_up (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNRpos) _)
    have hB : (N : ℝ) ^ (-2 : ℝ) * (2 * π * (27 * (N : ℝ) ^ 3)) = 54 * π * (N : ℝ) := by
      rw [show (N : ℝ) ^ (-2 : ℝ) * (2 * π * (27 * (N : ℝ) ^ 3))
            = 2 * π * 27 * ((N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ 3) by ring, hprod]
      ring
    calc (N : ℝ) ^ (-2 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3))
        ≤ 54 * π * (N : ℝ) := by rw [← hB]; exact hA
      _ ≤ 2 * t := by nlinarith [hlo]
  have hrlo : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ 3) ≤ lam := by
    rw [show (-3 + 8 / (2 : ℝ) ^ 3 : ℝ) = -2 by norm_num]
    rw [← hlam_eq] at hcore_lo
    exact le_of_mul_le_mul_right hcore_lo (mul_pos h2πpos hden_pos)
  have hprod1 : (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hNRpos,
        show (-1 : ℝ) + ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcore_up :
      2 * t ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) := by
    have hstep : (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3))
        ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_lo (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNRpos) _)
    have hEq :
        (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3)) = 16 * π * (N : ℝ) ^ 2 := by
      rw [show (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3))
            = 2 * π * 8 * ((N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ 3) by ring, hprod1]
      ring
    calc 2 * t ≤ (N : ℝ) ^ 2 := by linarith [hhi]
      _ ≤ 16 * π * (N : ℝ) ^ 2 := by
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 * π - 1 by linarith [Real.pi_gt_three])
            (sq_nonneg (N : ℝ))]
      _ = (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3)) := hEq.symm
      _ ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) := hstep
  have hrhi : lam ≤ (N : ℝ) ^ (-1 : ℝ) := by
    rw [← hlam_eq] at hcore_up
    exact le_of_mul_le_mul_right hcore_up (mul_pos h2πpos hden_pos)
  exact zeta_block_prefix_collapse 3 (by norm_num) t N lam x htpos hN3 hlam_def hx1 hx2 hrlo hrhi

/-- **R4c — the `k = 2` patch (the COVER residual `[N, 27πN]`, closed).**  On
`N ≤ t ≤ 27π·N` with floor `N ≥ 2`, the prefix block obeys `1348·√N`.  Via the
`k=2` prefix vdC block (`β = 1−4/2² = 0`, so the second term collapses to
`λ^{−1/2}`); razor-thin constants `144·(1.84+7.52) = 1347.84 ≤ 1348`. -/
theorem zeta_patch_prefix (t : ℝ) (N : ℕ) (x : ℤ) (hN2 : 2 ≤ N)
    (hlo : (N : ℝ) ≤ t) (hhi : t ≤ 27 * π * (N : ℝ))
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n)‖ ≤ 1348 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hNRpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have htpos : 0 < t := lt_of_lt_of_le hNRpos hlo
  set lam : ℝ := t / (2 * π) * ((2 - 1).factorial : ℝ) * (((2 * N + 2 : ℕ) : ℝ) ^ 2)⁻¹
    with hlam_def
  have hvdc := zeta_block_vdC_prefix 2 (by norm_num) t N lam x htpos hN2 hlam_def hx1 hx2
  have e1 : (1 : ℝ) / ((2 : ℝ) ^ 2 - 2) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) - 4 / (2 : ℝ) ^ 2 = 0 := by norm_num
  rw [e1, e2, Real.rpow_zero, one_mul] at hvdc
  -- λ in closed form
  have hlam2 : lam = t / (2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2) := by
    have hfac1 : ((2 - 1).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
    have hπ : π ≠ 0 := ne_of_gt Real.pi_pos
    have hD : ((2 * N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hlam_def, hfac1, mul_one]; field_simp
  have hDpos : (0 : ℝ) < ((2 * N + 2 : ℕ) : ℝ) := by positivity
  have hlam_pos : 0 < lam := by rw [hlam2]; positivity
  -- sqrt bridges
  have hsqrt1 : lam ^ (1 / 2 : ℝ) = Real.sqrt lam := (Real.sqrt_eq_rpow lam).symm
  have hsqrtN : (N : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (N : ℝ) := (Real.sqrt_eq_rpow (N : ℝ)).symm
  have hsqrt2 : lam ^ (-(1 / 2) : ℝ) = Real.sqrt lam⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hlam_pos), hsqrt1, ← Real.sqrt_inv]
  -- base-square bounds
  have hD2ge : (4 : ℝ) * (N : ℝ) ^ 2 ≤ ((2 * N + 2 : ℕ) : ℝ) ^ 2 := by
    have h : 2 * (N : ℝ) ≤ ((2 * N + 2 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * (N:ℝ)) h 2]
  have hD2le : ((2 * N + 2 : ℕ) : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by
    have h : ((2 * N + 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      push_cast; linarith
    nlinarith [pow_le_pow_left₀ hDpos.le h 2]
  -- term 1:  N·√λ ≤ 1.84·√N   (via N·λ ≤ 27/8, the π cancels)
  have hNlam : (N : ℝ) * lam ≤ 27 / 8 := by
    rw [hlam2]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have hNt : (N : ℝ) * t ≤ 27 * π * (N : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg (α := ℝ) N)]
    have hRHS : 27 * π * (N : ℝ) ^ 2 ≤ 27 / 8 * (2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2) := by
      nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr hD2ge)]
    linarith
  have hT1 : (N : ℝ) * lam ^ (1 / 2 : ℝ) ≤ 1.84 * (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hsqrt1, hsqrtN]
    have hT1eq : (N : ℝ) * Real.sqrt lam = Real.sqrt ((N : ℝ) ^ 2 * lam) := by
      rw [Real.sqrt_mul (sq_nonneg (N : ℝ)) lam, Real.sqrt_sq (Nat.cast_nonneg N)]
    have hle : (N : ℝ) ^ 2 * lam ≤ 3.3856 * (N : ℝ) := by
      nlinarith [hNlam, Nat.cast_nonneg (α := ℝ) N]
    rw [hT1eq]
    calc Real.sqrt ((N : ℝ) ^ 2 * lam)
        ≤ Real.sqrt (3.3856 * (N : ℝ)) := Real.sqrt_le_sqrt hle
      _ = 1.84 * Real.sqrt (N : ℝ) := by
          rw [Real.sqrt_mul (show (0:ℝ) ≤ 3.3856 by norm_num) (N : ℝ),
            show (3.3856 : ℝ) = 1.84 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  -- term 2:  λ^{−1/2} = √(λ⁻¹) ≤ 7.52·√N   (needs 18π ≤ 56.5504)
  have hinvlam : lam⁻¹ ≤ 56.5504 * (N : ℝ) := by
    have hlaminv_eq : lam⁻¹ = 2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2 / t := by
      rw [hlam2, inv_div]
    rw [hlaminv_eq, div_le_iff₀ htpos]
    have step1 : 2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2 ≤ 18 * π * (N : ℝ) ^ 2 := by
      nlinarith [hD2le, Real.pi_pos]
    have step2 : 18 * π * (N : ℝ) ^ 2 ≤ 56.5504 * (N : ℝ) * t := by
      have hpiN : 18 * π * (N : ℝ) ^ 2 ≤ 56.5504 * (N : ℝ) ^ 2 := by
        nlinarith [Real.pi_lt_d6, sq_nonneg (N : ℝ)]
      have hNt : 56.5504 * (N : ℝ) ^ 2 ≤ 56.5504 * (N : ℝ) * t := by
        nlinarith [hlo, Nat.cast_nonneg (α := ℝ) N]
      linarith
    linarith [step1, step2]
  have hT2 : lam ^ (-(1 / 2) : ℝ) ≤ 7.52 * (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [hsqrt2, hsqrtN]
    calc Real.sqrt lam⁻¹
        ≤ Real.sqrt (56.5504 * (N : ℝ)) := Real.sqrt_le_sqrt hinvlam
      _ = 7.52 * Real.sqrt (N : ℝ) := by
          rw [Real.sqrt_mul (show (0:ℝ) ≤ 56.5504 by norm_num) (N : ℝ),
            show (56.5504 : ℝ) = 7.52 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  -- combine
  refine le_trans hvdc ?_
  have hsqrtNnn : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc 144 * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2) : ℝ))
      ≤ 144 * (1.84 * (N : ℝ) ^ (1 / 2 : ℝ) + 7.52 * (N : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (by norm_num)
    _ ≤ 1348 * (N : ℝ) ^ (1 / 2 : ℝ) := by nlinarith [hsqrtNnn]

/-! ## R5 — Stone B (part 1): the `n^{−s}` split and antitone Abel weighting -/

/-- **The `n^{−s}` weight split.**  For `n ≥ 1`, `s = σ + it`,
`n^{−s} = n^{−σ}·e(φ_t(n))`: the modulus `n^{−σ}` times the ζ-phase. -/
lemma cpow_weight_split (σ t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * eR (phi t (n : ℤ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  rw [Complex.cpow_def_of_ne_zero hnC, hlog, Real.rpow_def_of_pos hn0,
    Complex.ofReal_exp, eR, ← Complex.exp_add]
  congr 1
  push_cast [phi]
  field_simp
  ring

/-- **Antitone Abel weighting with a prefix phase bound.**  If the weights `w`
are antitone and nonnegative on `(M, x]` and every prefix `∑_{M<n≤k} z n`
(`M < k ≤ x`) has norm `≤ B` (`0 ≤ B`), then the weighted sum obeys
`‖∑_{M<n≤x} w n · z n‖ ≤ w(M+1)·B`.  (ℕ Abel by parts + telescoping.) -/
lemma abel_antitone_prefix (M x : ℕ) (hMx : M < x) (w : ℕ → ℝ) (z : ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hwnn : ∀ n, M < n → n ≤ x → 0 ≤ w n)
    (hwanti : ∀ n, M < n → n < x → w (n + 1) ≤ w n)
    (hpref : ∀ k, M < k → k ≤ x → ‖∑ n ∈ Finset.Ioc M k, z n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc M x, ((w n : ℝ) : ℂ) * z n‖ ≤ w (M + 1) * B := by
  set W : ℕ → ℂ := fun i => ((w i : ℝ) : ℂ) with hWdef
  set S : ℕ → ℂ := fun k => ∑ n ∈ Finset.Ioc M k, z n with hSdef
  have hSsucc : ∀ k, M ≤ k → S (k + 1) = S k + z (k + 1) := fun k hk => by
    simp only [hSdef]; exact Finset.sum_Ioc_succ_top hk _
  -- the clean Abel identity
  have hident : ∀ y, M + 1 ≤ y →
      ∑ n ∈ Finset.Ioc M y, W n * z n
        = W y * S y + ∑ i ∈ Finset.Ico (M + 1) y, (W i - W (i + 1)) * S i := by
    intro y hy
    induction y, hy using Nat.le_induction with
    | base =>
        have hS1 : S (M + 1) = z (M + 1) := by
          simp only [hSdef]
          rw [Finset.sum_Ioc_succ_top (le_refl M), Finset.Ioc_self, Finset.sum_empty, zero_add]
        rw [Finset.Ico_self, Finset.sum_empty, add_zero, hS1,
          Finset.sum_Ioc_succ_top (le_refl M), Finset.Ioc_self, Finset.sum_empty, zero_add]
    | succ y hy ih =>
        have hMy : M ≤ y := le_trans (Nat.le_succ M) hy
        rw [Finset.sum_Ioc_succ_top hMy, ih, Finset.sum_Ico_succ_top hy, hSsucc y hMy]
        ring
  -- bound the identity
  rw [hident x hMx]
  refine le_trans (norm_add_le _ _) ?_
  have hb1 : ‖W x * S x‖ ≤ w x * B := by
    rw [norm_mul, hWdef]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hwnn x hMx (le_refl x))]
    exact mul_le_mul_of_nonneg_left (hpref x hMx (le_refl x)) (hwnn x hMx (le_refl x))
  have hb2 : ‖∑ i ∈ Finset.Ico (M + 1) x, (W i - W (i + 1)) * S i‖
      ≤ (w (M + 1) - w x) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.Ico (M + 1) x,
        ‖(W i - W (i + 1)) * S i‖ ≤ (w i - w (i + 1)) * B := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hMi : M < i := by omega
      have hix : i < x := hi.2
      have hnn : 0 ≤ w i - w (i + 1) := by linarith [hwanti i hMi hix]
      rw [norm_mul, hWdef]
      have hnorm : ‖((w i : ℝ) : ℂ) - ((w (i + 1) : ℝ) : ℂ)‖ = w i - w (i + 1) := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left (hpref i hMi (le_of_lt hix)) hnn
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have htel : ∀ y, M + 1 ≤ y →
        ∑ i ∈ Finset.Ico (M + 1) y, (w i - w (i + 1)) = w (M + 1) - w y := by
      intro y hy
      induction y, hy using Nat.le_induction with
      | base => rw [Finset.Ico_self, Finset.sum_empty]; ring
      | succ y hy ih => rw [Finset.sum_Ico_succ_top hy, ih]; ring
    rw [htel x hMx]
  refine le_trans (add_le_add hb1 hb2) (le_of_eq ?_)
  ring

/-- **The weighted block bound.**  Given a uniform phase-prefix bound `B` on the
block `(M, x]` (`M < x`), the `n^{−s}`-weighted sum obeys
`‖∑_{M<n≤x} n^{−s}‖ ≤ M^{−σ}·B`.  Abel weighting by the antitone modulus
`n^{−σ}`, folded into `(M+1)^{−σ} ≤ M^{−σ}`. -/
lemma zeta_weighted_block (σ t : ℝ) (hσ : 0 < σ) (M x : ℕ) (hM1 : 1 ≤ M) (hMx : M < x)
    (B : ℝ) (hB : 0 ≤ B)
    (hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x : ℤ) →
      ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n)‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc M x, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (M : ℝ) ^ (-σ) * B := by
  have hσle : -σ ≤ 0 := by linarith
  -- ℤ → ℕ reindex for the phase prefix sums
  have hreindex : ∀ k : ℕ, ∑ n ∈ Finset.Ioc (M : ℤ) (k : ℤ), eR (phi t n)
      = ∑ n ∈ Finset.Ioc M k, eR (phi t (n : ℤ)) := by
    intro k
    apply Finset.sum_nbij' (i := fun n : ℤ => n.toNat) (j := fun m : ℕ => (m : ℤ))
    · intro n hn; rw [Finset.mem_Ioc] at hn ⊢; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm ⊢; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn; rw [show ((n.toNat : ℤ)) = n from by omega]
  -- rewrite the summand n^{-s} = n^{-σ}·e(φ)
  have hcong : ∑ n ∈ Finset.Ioc M x, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = ∑ n ∈ Finset.Ioc M x, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * eR (phi t (n : ℤ)) := by
    apply Finset.sum_congr rfl
    intro n hn; rw [Finset.mem_Ioc] at hn
    exact cpow_weight_split σ t (by omega)
  rw [hcong]
  -- Abel weighting
  have habel := abel_antitone_prefix M x hMx (fun n => (n : ℝ) ^ (-σ))
    (fun n => eR (phi t (n : ℤ))) B hB
    (fun n hn _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (fun n hn _ => by
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast Nat.le_succ n) hσle)
    (fun k hk hkx => by
      show ‖∑ n ∈ Finset.Ioc M k, eR (phi t (n : ℤ))‖ ≤ B
      rw [← hreindex k]
      exact hpref (k : ℤ) (by exact_mod_cast hk) (by exact_mod_cast hkx))
  refine le_trans habel ?_
  have hstep : ((M + 1 : ℕ) : ℝ) ^ (-σ) ≤ (M : ℝ) ^ (-σ) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    exact Real.rpow_le_rpow_of_nonpos hM0 (by push_cast; linarith) hσle
  exact mul_le_mul_of_nonneg_right hstep hB

/-! ## R6 — Stone B (part 2): window coverage and the block dispatch -/

/-- **Window coverage.**  If `M²/2 < t ≤ M^{k−1}/(k−1)!` (and `k ≤ M`), then `t`
lies in exactly one factorial-shifted window `[M^{k'−2}/(k'−2)!, M^{k'−1}/(k'−1)!]`
with `4 ≤ k' ≤ k`.  The adjacent windows tile the `t`-axis via
`zeta_block_window_meet`. -/
lemma window_coverage (k : ℕ) (hk : 4 ≤ k) (M : ℕ) (t : ℝ) (hkM : (k : ℝ) ≤ (M : ℝ))
    (hlo : (M : ℝ) ^ (2 : ℝ) / 2 < t)
    (hhi : t ≤ (M : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ)) :
    ∃ k', 4 ≤ k' ∧ k' ≤ k ∧
      (M : ℝ) ^ ((k' : ℝ) - 2) / ((k' - 2).factorial : ℝ) ≤ t ∧
      t ≤ (M : ℝ) ^ ((k' : ℝ) - 1) / ((k' - 1).factorial : ℝ) := by
  clear hkM
  revert hhi
  induction k, hk using Nat.le_induction with
  | base =>
      intro hhi
      refine ⟨4, le_refl 4, le_refl 4, ?_, hhi⟩
      rw [show ((4 : ℕ) : ℝ) - 2 = (2 : ℝ) from by norm_num,
        show (((4 : ℕ) - 2).factorial : ℝ) = 2 from by norm_num [Nat.factorial]]
      exact le_of_lt hlo
  | succ k hk ih =>
      intro hhi
      by_cases hcase : t ≤ (M : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ)
      · obtain ⟨k', h4, hk'k, hl, hu⟩ := ih hcase
        exact ⟨k', h4, le_trans hk'k (Nat.le_succ k), hl, hu⟩
      · push_neg at hcase
        refine ⟨k + 1, by omega, le_refl _, ?_, hhi⟩
        rw [zeta_block_window_meet M k]
        exact le_of_lt hcase

/-- **The uniform per-block dispatch.**  For a dyadic block `(M, x']` (`M < x' ≤ 2M`,
floor `M ≥ (k!)^6`, guard `t ≤ M^{k−1}/(k−1)!`, `M ≤ t²`) and `σ` in the strip
`[1−2^{−(k+2)}, 2]`, the weighted block sum is bounded by the absolute constant
`1348`.  A 4-case trichotomy on `t`: Kusmin (`t ≤ M`), patch (`M<t≤27πM`), seam
(`27πM<t≤M²/2`), and the `k'`-window ladder (`M²/2<t`). -/
theorem zeta_block_dispatch (k : ℕ) (hk : 4 ≤ k) (σ t : ℝ)
    (hσlo : 1 - 1 / (2 : ℝ) ^ (k + 2) ≤ σ) (hσhi : σ ≤ 2) (ht1 : 1 ≤ t)
    (M x' : ℕ) (hM : (k.factorial : ℝ) ^ 6 ≤ (M : ℝ)) (hMx' : M < x') (hx'2 : x' ≤ 2 * M)
    (hMt2 : (M : ℝ) ≤ t ^ 2)
    (hguard : t ≤ (M : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ)) :
    ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 := by
  have hfacpos : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := le_trans (one_le_pow₀ hfacpos) hM
    exact_mod_cast this
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMRpos : (0 : ℝ) < (M : ℝ) := by linarith
  have htpos : 0 < t := by linarith
  have hπpos : (0 : ℝ) < π := Real.pi_pos
  have hx'2Z : (x' : ℤ) ≤ 2 * (M : ℤ) := by exact_mod_cast hx'2
  -- strip facts:  1/2 ≤ σ, and the ε-bound
  have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hεbd : (1 : ℝ) / (2 : ℝ) ^ (k + 2) ≤ 1 / 64 :=
    one_div_le_one_div_of_le (by norm_num) h64
  have hσhalf : (1 : ℝ) / 2 ≤ σ := by linarith
  have hσpos : 0 < σ := by linarith
  have hkM : (k : ℝ) ≤ (M : ℝ) := by
    have : (k : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial k
    calc (k : ℝ) ≤ (k.factorial : ℝ) := this
      _ ≤ (k.factorial : ℝ) ^ 6 := le_self_pow₀ hfacpos (by norm_num)
      _ ≤ (M : ℝ) := hM
  have hM4 : 4 ≤ M := by
    have : (4 : ℝ) ≤ (M : ℝ) := le_trans (by exact_mod_cast hk) hkM
    exact_mod_cast this
  -- the folding helper for cases (ii)–(iv):  M^{−σ}·(C·M^e) ≤ 1348 when e ≤ σ, C ≤ 1348
  have hfin : ∀ C e : ℝ, 0 ≤ C → e ≤ σ → C ≤ 1348 →
      (M : ℝ) ^ (-σ) * (C * (M : ℝ) ^ e) ≤ 1348 := by
    intro C e hC he hC1348
    rw [show (M : ℝ) ^ (-σ) * (C * (M : ℝ) ^ e) = C * (M : ℝ) ^ (e + -σ) from by
      rw [Real.rpow_add hMRpos]; ring]
    have hle1 : (M : ℝ) ^ (e + -σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hMR1 (by linarith)
    calc C * (M : ℝ) ^ (e + -σ) ≤ C * 1 := mul_le_mul_of_nonneg_left hle1 hC
      _ = C := mul_one C
      _ ≤ 1348 := hC1348
  rcases le_or_gt t (M : ℝ) with hc1 | hc1
  · -- (i) t ≤ M:  Kusmin
    have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
        ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n)‖ ≤ 2 * π * (2 * (M : ℝ) + 1) / t :=
      fun y hy1 hy2 => zeta_block_kusmin_prefix t htpos M hc1 hM1 y hy1 (le_trans hy2 hx'2Z)
    have hBnn : (0 : ℝ) ≤ 2 * π * (2 * (M : ℝ) + 1) / t := by positivity
    refine le_trans (zeta_weighted_block σ t hσpos M x' hM1 hMx' _ hBnn hpref) ?_
    -- M^{−σ}·(2π(2M+1)/t) ≤ 1348
    have hMM : (M : ℝ) ^ (-σ) * (M : ℝ) = (M : ℝ) ^ (1 - σ) := by
      nth_rewrite 2 [← Real.rpow_one (M : ℝ)]
      rw [← Real.rpow_add hMRpos]; congr 1; ring
    have h1 : (M : ℝ) ^ (-σ) * (2 * (M : ℝ) + 1) ≤ 3 * (M : ℝ) ^ (1 - σ) := by
      have hMsigpos : (0 : ℝ) ≤ (M : ℝ) ^ (-σ) := Real.rpow_nonneg (le_of_lt hMRpos) _
      calc (M : ℝ) ^ (-σ) * (2 * (M : ℝ) + 1)
          ≤ (M : ℝ) ^ (-σ) * (3 * (M : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith [hMR1]) hMsigpos
        _ = 3 * ((M : ℝ) ^ (-σ) * (M : ℝ)) := by ring
        _ = 3 * (M : ℝ) ^ (1 - σ) := by rw [hMM]
    have hM1sig : (M : ℝ) ^ (1 - σ) / t ≤ 1 := by
      rw [div_le_one htpos]
      rcases le_or_gt σ 1 with hs | hs
      · calc (M : ℝ) ^ (1 - σ) ≤ (t ^ 2) ^ (1 - σ) :=
              Real.rpow_le_rpow (le_of_lt hMRpos) hMt2 (by linarith)
          _ = t ^ (2 * (1 - σ)) := by
              rw [← Real.rpow_natCast t 2, ← Real.rpow_mul (le_of_lt htpos)]; norm_num
          _ ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
          _ = t := Real.rpow_one t
      · have : (M : ℝ) ^ (1 - σ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hMR1 (by linarith)
        linarith
    have hred : (M : ℝ) ^ (-σ) * (2 * π * (2 * (M : ℝ) + 1) / t)
        ≤ 6 * π * ((M : ℝ) ^ (1 - σ) / t) := by
      rw [show (M : ℝ) ^ (-σ) * (2 * π * (2 * (M : ℝ) + 1) / t)
            = 2 * π * ((M : ℝ) ^ (-σ) * (2 * (M : ℝ) + 1)) / t from by ring,
        show 6 * π * ((M : ℝ) ^ (1 - σ) / t) = 2 * π * (3 * (M : ℝ) ^ (1 - σ)) / t from by ring]
      gcongr
    refine le_trans hred ?_
    have : 6 * π * ((M : ℝ) ^ (1 - σ) / t) ≤ 6 * π * 1 :=
      mul_le_mul_of_nonneg_left hM1sig (by positivity)
    calc 6 * π * ((M : ℝ) ^ (1 - σ) / t) ≤ 6 * π * 1 := this
      _ ≤ 1348 := by nlinarith [Real.pi_lt_four]
  · rcases le_or_gt t (27 * π * (M : ℝ)) with hc2 | hc2
    · -- (ii) M < t ≤ 27πM:  patch (k=2)
      have hM2 : 2 ≤ M := by omega
      have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
          ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n)‖ ≤ 1348 * (M : ℝ) ^ (1 / 2 : ℝ) :=
        fun y hy1 hy2 => zeta_patch_prefix t M y hM2 (le_of_lt hc1) hc2 hy1
          (le_trans hy2 hx'2Z)
      have hBnn : (0 : ℝ) ≤ 1348 * (M : ℝ) ^ (1 / 2 : ℝ) := by positivity
      refine le_trans (zeta_weighted_block σ t hσpos M x' hM1 hMx' _ hBnn hpref) ?_
      exact hfin 1348 (1 / 2) (by norm_num) (by linarith) (by norm_num)
    · rcases le_or_gt t ((M : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ)) with hc3 | hc3
      · -- (iii) 27πM < t ≤ M²/2:  seam (k=3)
        have hM3 : 3 ≤ M := by omega
        have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
            ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n)‖
              ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ 3 - 2)) :=
          fun y hy1 hy2 => zeta_seam_prefix t M y hM3 (le_of_lt hc2) hc3 hy1
            (le_trans hy2 hx'2Z)
        have hBnn : (0 : ℝ) ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ 3 - 2)) := by positivity
        refine le_trans (zeta_weighted_block σ t hσpos M x' hM1 hMx' _ hBnn hpref) ?_
        refine hfin 288 (1 - 1 / ((2 : ℝ) ^ 3 - 2)) (by norm_num) ?_ (by norm_num)
        have : (1 : ℝ) / ((2 : ℝ) ^ 3 - 2) = 1 / 6 := by norm_num
        rw [this]; linarith
      · -- (iv) M²/2 < t ≤ M^{k−1}/(k−1)!:  window ladder
        have hMsqeq : (M : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ) = (M : ℝ) ^ (2 : ℝ) / 2 := by
          rw [show ((3 : ℝ) - 1) = (2 : ℝ) by norm_num,
            show (((3 : ℕ) - 1).factorial : ℝ) = 2 from by norm_num [Nat.factorial]]
        rw [hMsqeq] at hc3
        obtain ⟨k', h4k', hk'k, hlk', huk'⟩ := window_coverage k hk M t hkM hc3 hguard
        have hMk' : (k'.factorial : ℝ) ^ 6 ≤ (M : ℝ) := by
          refine le_trans ?_ hM
          have : (k'.factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le hk'k
          exact pow_le_pow_left₀ (by positivity) this 6
        have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
            ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n)‖
              ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k' - 2)) :=
          fun y hy1 hy2 => zeta_window_prefix k' h4k' t M y hMk' hlk' huk' hy1
            (le_trans hy2 hx'2Z)
        have hBnn : (0 : ℝ) ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k' - 2)) := by positivity
        refine le_trans (zeta_weighted_block σ t hσpos M x' hM1 hMx' _ hBnn hpref) ?_
        refine hfin 288 (1 - 1 / ((2 : ℝ) ^ k' - 2)) (by norm_num) ?_ (by norm_num)
        -- 1 − 1/(2^{k'}−2) ≤ σ,  i.e.  1 − σ ≤ 1/(2^{k'}−2)
        have h2k' : (4 : ℝ) ≤ (2 : ℝ) ^ k' := by
          calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
            _ ≤ (2 : ℝ) ^ k' := pow_le_pow_right₀ (by norm_num) (by omega)
        have hstep1 : (1 : ℝ) / (2 : ℝ) ^ k' ≤ 1 / ((2 : ℝ) ^ k' - 2) :=
          one_div_le_one_div_of_le (by linarith) (by linarith)
        have hstep2 : (1 : ℝ) / (2 : ℝ) ^ (k + 2) ≤ 1 / (2 : ℝ) ^ k' := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        linarith

/-! ## R7 — Stone C (part 1): the head and ladder sums -/

/-- **Summand-generic dyadic split** (ℕ form).  `Ioc N₀ (2^J·N₀)` telescopes into
`J` dyadic blocks.  The proof never inspects the summand. -/
lemma dyadic_sum_split_gen {A : Type*} [AddCommMonoid A] (g : ℕ → A) (N₀ : ℕ) :
    ∀ J : ℕ, ∑ n ∈ Finset.Ioc N₀ (2 ^ J * N₀), g n
      = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j * N₀) (2 ^ (j + 1) * N₀), g n := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      have hmono1 : N₀ ≤ 2 ^ J * N₀ := Nat.le_mul_of_pos_left N₀ (by positivity)
      have hmono2 : 2 ^ J * N₀ ≤ 2 ^ (J + 1) * N₀ :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)) (le_refl N₀)
      rw [Finset.sum_range_succ, ← ih]
      exact (Finset.sum_Ioc_consecutive g hmono1 hmono2).symm

/-- **The `σ ≥ 1` head variant.**  `∑_{n≤N} n^{−σ} ≤ 1 + log N` (dominated by the
harmonic series). -/
lemma sum_Icc_rpow_neg_le' {σ : ℝ} (hσ : 1 ≤ σ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤ 1 + Real.log N := by
  have hstep : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)
      ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn; rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  refine le_trans hstep ?_
  have h := sum_Icc_rpow_neg_le (le_refl (1 : ℝ)) hN
  simpa using h

/-- `k² ≤ 2^k` for `k ≥ 4`. -/
lemma sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have h1 : 2 * k + 1 ≤ k ^ 2 := by nlinarith [hk]
      have h2 : 2 * k + 1 ≤ 2 ^ k := le_trans h1 ih
      calc (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- **The head coefficient bound.**  `(2·(k!)^6)^e ≤ 8` for `0 ≤ e ≤ 2^{−(k+2)}` and
`k ≥ 4` — the k-free constant that keeps the strip constant absolute.  Crude log
bounds (`k! ≤ k^k`, `log k ≤ k`, `k² ≤ 2^k`) suffice inside the budget slack. -/
lemma head_coeff_le (k : ℕ) (hk : 4 ≤ k) (e : ℝ) (he0 : 0 ≤ e)
    (he : e ≤ 1 / (2 : ℝ) ^ (k + 2)) : (2 * (k.factorial : ℝ) ^ 6) ^ e ≤ 8 := by
  have hfacpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hbase_pos : (0 : ℝ) < 2 * (k.factorial : ℝ) ^ 6 := by positivity
  have hbase1 : (1 : ℝ) ≤ 2 * (k.factorial : ℝ) ^ 6 := by
    have : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast Nat.factorial_pos k)
    linarith
  have hlnfac : Real.log ((k.factorial : ℝ) ^ 6) ≤ 6 * (k : ℝ) ^ 2 := by
    rw [Real.log_pow]
    have hk_fac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    have hlogfac : Real.log (k.factorial : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
      have h1 : Real.log (k.factorial : ℝ) ≤ Real.log ((k : ℝ) ^ k) :=
        Real.log_le_log hfacpos hk_fac
      rwa [Real.log_pow] at h1
    have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) by positivity); linarith
    have hkpos : (0 : ℝ) ≤ (k : ℝ) := by positivity
    push_cast
    nlinarith [hlogfac, mul_le_mul_of_nonneg_left hlogk hkpos]
  have hln : Real.log (2 * (k.factorial : ℝ) ^ 6) ≤ Real.log 2 + 6 * (k : ℝ) ^ 2 := by
    rw [Real.log_mul (by norm_num) (by positivity)]; linarith [hlnfac]
  have hk16 : (16 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hk2R : (k : ℝ) ^ 2 ≤ (2 : ℝ) ^ k := by exact_mod_cast sq_le_two_pow k hk
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h2k2 : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by rw [pow_add]; ring
  have hεln : e * Real.log (2 * (k.factorial : ℝ) ^ 6) ≤ 2 := by
    have hstep : e * Real.log (2 * (k.factorial : ℝ) ^ 6)
        ≤ (1 / (2 : ℝ) ^ (k + 2)) * (Real.log 2 + 6 * (k : ℝ) ^ 2) :=
      mul_le_mul he hln (Real.log_nonneg (by linarith)) (by positivity)
    refine le_trans hstep ?_
    rw [show (1 / (2 : ℝ) ^ (k + 2)) * (Real.log 2 + 6 * (k : ℝ) ^ 2)
        = (Real.log 2 + 6 * (k : ℝ) ^ 2) / (2 : ℝ) ^ (k + 2) from by ring,
      div_le_iff₀ (by positivity), h2k2]
    nlinarith [hk2R, hlog2, hk16]
  calc (2 * (k.factorial : ℝ) ^ 6) ^ e
      = Real.exp (e * Real.log (2 * (k.factorial : ℝ) ^ 6)) := by
        rw [Real.rpow_def_of_pos hbase_pos, mul_comm]
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr hεln
    _ ≤ 8 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [h2]; nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]

/-- **The ladder bound.**  The weighted sum over `(M₀, X]` (with `X ≤ t²` and the
guard `t ≤ M₀^{k−1}/(k−1)!`) splits into `≤ 3(1+log t)` dyadic blocks, each bounded
by `1348` via `zeta_block_dispatch`; total `≤ 4044·(1+log t)`. -/
theorem zeta_ladder_bound (k : ℕ) (hk : 4 ≤ k) (σ t : ℝ)
    (hσlo : 1 - 1 / (2 : ℝ) ^ (k + 2) ≤ σ) (hσhi : σ ≤ 2) (ht1 : 1 ≤ t)
    (M₀ : ℕ) (hM₀1 : 1 ≤ M₀) (hM₀ : (k.factorial : ℝ) ^ 6 ≤ (M₀ : ℝ))
    (hguard : t ≤ (M₀ : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ))
    (X : ℕ) (hX0 : M₀ ≤ X) (hXt2 : (X : ℝ) ≤ t ^ 2) :
    ‖∑ n ∈ Finset.Ioc M₀ X, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ 4044 * (1 + Real.log t) := by
  have hM₀R1 : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀1
  -- per-block dispatch bound
  have hblock : ∀ M x' : ℕ, M₀ ≤ M → M < x' → x' ≤ 2 * M → x' ≤ X →
      ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 := by
    intro M x' hM₀M hMx' hx'2 hx'X
    have hMR : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM₀M
    have hMfloor : (k.factorial : ℝ) ^ 6 ≤ (M : ℝ) := le_trans hM₀ hMR
    have hMt2 : (M : ℝ) ≤ t ^ 2 :=
      le_trans (by exact_mod_cast le_trans (le_of_lt hMx') hx'X) hXt2
    have hMguard : t ≤ (M : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ) := by
      refine le_trans hguard ?_
      have hexp : (0 : ℝ) ≤ (k : ℝ) - 1 := by
        have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      have hbase : (M₀ : ℝ) ^ ((k : ℝ) - 1) ≤ (M : ℝ) ^ ((k : ℝ) - 1) :=
        Real.rpow_le_rpow (le_trans zero_le_one hM₀R1) hMR hexp
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hbase (by positivity)
    exact zeta_block_dispatch k hk σ t hσlo hσhi ht1 M x' hMfloor hMx' hx'2 hMt2 hMguard
  -- budget induction
  have hlad : ∀ (J Y : ℕ), M₀ ≤ Y → Y ≤ 2 ^ J * M₀ → Y ≤ X →
      ‖∑ n ∈ Finset.Ioc M₀ Y, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 * J := by
    intro J
    induction J with
    | zero =>
        intro Y hY0 hY1 hYX
        simp only [pow_zero, one_mul] at hY1
        have hYeq : Y = M₀ := le_antisymm hY1 hY0
        subst hYeq; simp
    | succ J ih =>
        intro Y hY0 hY1 hYX
        by_cases hc : Y ≤ 2 ^ J * M₀
        · refine le_trans (ih Y hY0 hc hYX) ?_
          have : (0 : ℝ) ≤ (J : ℝ) := by positivity
          push_cast; nlinarith
        · push_neg at hc
          have hmid : M₀ ≤ 2 ^ J * M₀ := Nat.le_mul_of_pos_left M₀ (by positivity)
          have hsplit : ∑ n ∈ Finset.Ioc M₀ Y, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
              = ∑ n ∈ Finset.Ioc M₀ (2 ^ J * M₀), (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
                + ∑ n ∈ Finset.Ioc (2 ^ J * M₀) Y, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
            (Finset.sum_Ioc_consecutive _ hmid (le_of_lt hc)).symm
          rw [hsplit]
          refine le_trans (norm_add_le _ _) ?_
          have hb1 := ih (2 ^ J * M₀) hmid (le_refl _) (le_trans (le_of_lt hc) hYX)
          have hY2M : Y ≤ 2 * (2 ^ J * M₀) := by
            rw [show 2 * (2 ^ J * M₀) = 2 ^ (J + 1) * M₀ from by rw [pow_succ]; ring]; exact hY1
          have hb2 := hblock (2 ^ J * M₀) Y hmid hc hY2M hYX
          calc _ ≤ 1348 * (J : ℝ) + 1348 := add_le_add hb1 hb2
            _ = 1348 * ((J : ℝ) + 1) := by ring
            _ = 1348 * ((J + 1 : ℕ) : ℝ) := by push_cast; ring
  -- choose the minimal dyadic budget J
  have hex : ∃ J : ℕ, X ≤ 2 ^ J * M₀ := by
    refine ⟨X, ?_⟩
    calc X ≤ 2 ^ X := le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ X * M₀ := Nat.le_mul_of_pos_right _ hM₀1
  set J := Nat.find hex with hJdef
  have hmain := hlad J X hX0 (Nat.find_spec hex) (le_refl X)
  -- count bound J ≤ 3(1+log t)
  have htpos : (0 : ℝ) < t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hJcount : (J : ℝ) ≤ 3 * (1 + Real.log t) := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · rw [hJ0]; push_cast; nlinarith [hlogt]
    · have hJm1 : ¬ X ≤ 2 ^ (J - 1) * M₀ := Nat.find_min hex (show J - 1 < J by omega)
      push_neg at hJm1
      have h2lt : (2 : ℝ) ^ (J - 1) < t ^ 2 := by
        calc (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ (J - 1) * (M₀ : ℝ) :=
              le_mul_of_one_le_right (by positivity) hM₀R1
          _ < (X : ℝ) := by exact_mod_cast hJm1
          _ ≤ t ^ 2 := hXt2
      have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlogineq : ((J : ℝ) - 1) * Real.log 2 < 2 * Real.log t := by
        have h := Real.log_lt_log (by positivity) h2lt
        rw [Real.log_pow, Real.log_pow] at h
        have hcast : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [hcast] at h; push_cast at h; linarith
      have h23 : (2 : ℝ) ≤ 3 * Real.log 2 := by
        have := Real.log_two_gt_d9; nlinarith
      have hJm1lt : (J : ℝ) - 1 < 3 * Real.log t := by
        have hchain : ((J : ℝ) - 1) * Real.log 2 < (3 * Real.log t) * Real.log 2 := by
          calc ((J : ℝ) - 1) * Real.log 2 < 2 * Real.log t := hlogineq
            _ ≤ (3 * Real.log t) * Real.log 2 := by
                nlinarith [mul_nonneg hlogt (show (0 : ℝ) ≤ 3 * Real.log 2 - 2 by linarith [h23])]
        exact lt_of_mul_lt_mul_right hchain (le_of_lt hlog2pos)
      linarith
  refine le_trans hmain ?_
  calc 1348 * (J : ℝ) ≤ 1348 * (3 * (1 + Real.log t)) :=
        mul_le_mul_of_nonneg_left hJcount (by norm_num)
    _ = 4044 * (1 + Real.log t) := by ring

/-! ## R8 — Stone C (part 2): the M₀-guard, the head sum, and the assembly -/

/-- **The M₀-guard.**  With `M₀ = (k!)^6·c` and `c ≥ t^{1/(k−1)}`, the guard
`t ≤ M₀^{k−1}/(k−1)!` holds: `M₀^{k−1} ≥ (k!)^{6(k−1)}·t ≥ (k−1)!·t` (the ceiling
kills case (v) of the dispatch). -/
lemma m0_guard (k : ℕ) (hk : 4 ≤ k) (t : ℝ) (ht : 1 ≤ t) (c : ℕ) (hc0 : 0 < c)
    (hc : t ^ (1 / ((k : ℝ) - 1)) ≤ (c : ℝ)) :
    t ≤ ((k.factorial ^ 6 * c : ℕ) : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ) := by
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set e : ℝ := (k : ℝ) - 1 with he
  have he1 : (1 : ℝ) ≤ e := by rw [he]; linarith
  have hepos : (0 : ℝ) < e := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hfacpos : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
  have htpow_pos : (0 : ℝ) < t ^ (1 / e) := Real.rpow_pos_of_pos htpos _
  -- c^e ≥ t
  have hidentity : (t ^ (1 / e)) ^ e = t := by
    rw [← Real.rpow_mul (le_of_lt htpos), show 1 / e * e = (1 : ℝ) from by field_simp, Real.rpow_one]
  have hce : t ≤ (c : ℝ) ^ e := by
    rw [← hidentity]
    exact Real.rpow_le_rpow (le_of_lt htpow_pos) hc (le_of_lt hepos)
  -- ((k!)^6)^e ≥ (k−1)!
  have hfacpart : ((k - 1).factorial : ℝ) ≤ ((k.factorial : ℝ) ^ 6) ^ e := by
    have h1 : ((k - 1).factorial : ℝ) ≤ (k.factorial : ℝ) ^ 6 := by
      calc ((k - 1).factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
        _ ≤ (k.factorial : ℝ) ^ 6 :=
            le_self_pow₀ (by exact_mod_cast Nat.factorial_pos k) (by norm_num)
    have h2 : (k.factorial : ℝ) ^ 6 ≤ ((k.factorial : ℝ) ^ 6) ^ e := by
      nth_rewrite 1 [← Real.rpow_one ((k.factorial : ℝ) ^ 6)]
      exact Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (by exact_mod_cast Nat.factorial_pos k)) he1
    linarith
  rw [le_div_iff₀ hfacpos]
  have hM₀_eq : ((k.factorial ^ 6 * c : ℕ) : ℝ) ^ e = ((k.factorial : ℝ) ^ 6) ^ e * (c : ℝ) ^ e := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [hM₀_eq]
  calc t * ((k - 1).factorial : ℝ) = ((k - 1).factorial : ℝ) * t := by ring
    _ ≤ ((k.factorial : ℝ) ^ 6) ^ e * (c : ℝ) ^ e :=
        mul_le_mul hfacpart hce (le_of_lt htpos)
          (Real.rpow_nonneg (by positivity) e)

/-- **The head sum bound.**  `∑_{n≤M₀} n^{−σ} ≤ 16·t^{B_k}·(1+log t)` with
`M₀ = (k!)^6·⌈t^{1/(k−1)}⌉` and `B_k = 1/(2^{k+2}(k−1))`.  The `(k!)^6` factor is
absorbed into the k-free head coefficient `8` (head_coeff_le), the tail power into
`t^{B_k}`, and `1+log M₀ ≤ 2(1+log t)` from `t ≥ 4(k!)^6`. -/
theorem zeta_head_bound (k : ℕ) (hk : 4 ≤ k) (σ t : ℝ)
    (hσlo : 1 - 1 / (2 : ℝ) ^ (k + 2) ≤ σ) (hσhi : σ ≤ 2)
    (ht : 4 * (k.factorial : ℝ) ^ 6 ≤ t) :
    ∑ n ∈ Finset.Icc 1 (k.factorial ^ 6 * ⌈t ^ (1 / ((k : ℝ) - 1))⌉₊), (n : ℝ) ^ (-σ)
      ≤ 16 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) * (1 + Real.log t) := by
  have hfac1 : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast Nat.factorial_pos k)
  have htge4 : (4 : ℝ) ≤ t := le_trans (by nlinarith [hfac1]) ht
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set e : ℝ := (k : ℝ) - 1 with he
  have hepos : (0 : ℝ) < e := by rw [he]; linarith
  have he1 : (1 : ℝ) ≤ e := by rw [he]; linarith
  have hene : e ≠ 0 := ne_of_gt hepos
  set tp : ℝ := t ^ (1 / e) with htp
  have htp1 : (1 : ℝ) ≤ tp := Real.one_le_rpow ht1 (by positivity)
  have htppos : (0 : ℝ) < tp := by linarith
  set c : ℕ := ⌈tp⌉₊ with hc
  have hcR : tp ≤ (c : ℝ) := Nat.le_ceil tp
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := le_trans htp1 hcR
  have hcle : (c : ℝ) ≤ 2 * tp := by
    rw [hc]
    calc ((⌈tp⌉₊ : ℕ) : ℝ) ≤ tp + 1 := le_of_lt (Nat.ceil_lt_add_one (by linarith))
      _ ≤ 2 * tp := by linarith
  set M₀ : ℕ := k.factorial ^ 6 * c with hM₀
  have hM₀R : (M₀ : ℝ) = (k.factorial : ℝ) ^ 6 * (c : ℝ) := by rw [hM₀]; push_cast; ring
  have hM₀1 : (1 : ℝ) ≤ (M₀ : ℝ) := by rw [hM₀R]; nlinarith [hfac1, hc1]
  have hM₀1N : 1 ≤ M₀ := by exact_mod_cast hM₀1
  -- 1 + log M₀ ≤ 2(1 + log t)
  have hlogM0 : 1 + Real.log (M₀ : ℝ) ≤ 2 * (1 + Real.log t) := by
    rw [hM₀R, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hlogc : Real.log (c : ℝ) ≤ Real.log 2 + (1 / e) * Real.log t := by
      calc Real.log (c : ℝ) ≤ Real.log (2 * tp) := Real.log_le_log (by linarith) hcle
        _ = Real.log 2 + Real.log tp := by rw [Real.log_mul (by norm_num) (by linarith)]
        _ = Real.log 2 + (1 / e) * Real.log t := by rw [htp, Real.log_rpow htpos]
    have h6log : 6 * Real.log (k.factorial : ℝ) + Real.log 2 ≤ Real.log t := by
      have hstep := Real.log_le_log (by positivity : (0:ℝ) < 4 * (k.factorial:ℝ)^6) ht
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hstep
      have hlog4 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      push_cast at hstep; linarith
    have he_inv : (1 / e) * Real.log t ≤ Real.log t := by
      have h1e : (1 / e) ≤ 1 := by rw [div_le_one hepos]; linarith
      nlinarith [hlogt, h1e]
    push_cast
    nlinarith [hlogc, h6log, he_inv, hlogt]
  -- M₀^{1-σ} ≤ 8 t^{B_k}  (σ ≤ 1 arm)
  have hM01sig : σ ≤ 1 → (M₀ : ℝ) ^ (1 - σ) ≤ 8 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * e)) := by
    intro hσ1
    have h1σ0 : (0 : ℝ) ≤ 1 - σ := by linarith
    have h1σε : 1 - σ ≤ 1 / (2 : ℝ) ^ (k + 2) := by linarith [hσlo]
    have hM₀le : (M₀ : ℝ) ≤ (2 * (k.factorial : ℝ) ^ 6) * tp := by
      rw [hM₀R]; nlinarith [hcle, hfac1, htppos]
    have hM01 : (M₀ : ℝ) ^ (1 - σ) ≤ ((2 * (k.factorial : ℝ) ^ 6) * tp) ^ (1 - σ) :=
      Real.rpow_le_rpow (by positivity) hM₀le h1σ0
    rw [Real.mul_rpow (by positivity) (le_of_lt htppos)] at hM01
    have hcoef := head_coeff_le k hk (1 - σ) h1σ0 h1σε
    have htpsig : tp ^ (1 - σ) ≤ t ^ (1 / ((2 : ℝ) ^ (k + 2) * e)) := by
      rw [htp, ← Real.rpow_mul (le_of_lt htpos)]
      apply Real.rpow_le_rpow_of_exponent_le ht1
      calc (1 / e) * (1 - σ) ≤ (1 / e) * (1 / (2 : ℝ) ^ (k + 2)) :=
            mul_le_mul_of_nonneg_left h1σε (by positivity)
        _ = 1 / ((2 : ℝ) ^ (k + 2) * e) := by field_simp
    calc (M₀ : ℝ) ^ (1 - σ)
        ≤ (2 * (k.factorial : ℝ) ^ 6) ^ (1 - σ) * tp ^ (1 - σ) := hM01
      _ ≤ 8 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * e)) :=
          mul_le_mul hcoef htpsig (Real.rpow_nonneg (le_of_lt htppos) _) (by norm_num)
  have htBk1 : (1 : ℝ) ≤ t ^ (1 / ((2 : ℝ) ^ (k + 2) * e)) := Real.one_le_rpow ht1 (by positivity)
  rcases le_or_gt σ 1 with hσ1 | hσ1
  · refine le_trans (sum_Icc_rpow_neg_le hσ1 hM₀1N) ?_
    calc (M₀ : ℝ) ^ (1 - σ) * (1 + Real.log (M₀ : ℝ))
        ≤ (8 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * e))) * (2 * (1 + Real.log t)) :=
          mul_le_mul (hM01sig hσ1) hlogM0 (by positivity) (by positivity)
      _ = 16 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * e)) * (1 + Real.log t) := by ring
  · refine le_trans (sum_Icc_rpow_neg_le' (le_of_lt hσ1) hM₀1N) ?_
    calc 1 + Real.log (M₀ : ℝ) ≤ 2 * (1 + Real.log t) := hlogM0
      _ ≤ 16 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * e)) * (1 + Real.log t) := by
          nlinarith [htBk1, hlogt, mul_nonneg (by linarith [htBk1] : (0:ℝ) ≤ t ^ (1 / ((2:ℝ)^(k+2)*e)) - 1) (by linarith [hlogt] : (0:ℝ) ≤ 1 + Real.log t)]

set_option maxHeartbeats 1000000 in
/-- **`LITT-STRIP`: the k-uniform Weyl strip family.**  There is an ABSOLUTE
constant `C = 4096` (outside the `k`-quantifier) with
`‖ζ(σ + it)‖ ≤ C·t^{1/(2^{k+2}(k−1))}·(1 + log t)` on `σ ∈ [1−2^{−(k+2)}, 2]`,
`t ≥ 4(k!)^6`, for every `k ≥ 4`.  The power/width ratio `1/(k−1) → 0` is the
Littlewood mechanism; `C` absolute is what `LITT-LANDAU` needs.  Route: the
approximate formula at `N_t = ⌊t²⌋` (error `≤ 16`, pole `≤ 1`), the trivial head
`[1, M₀]` (`≤ 16·t^{B_k}·(1+log t)`), and the dyadic ladder `(M₀, N_t]`
(`≤ 4044·(1+log t)`); total `≤ 4096·t^{B_k}·(1+log t)`. -/
theorem zeta_strip_family : ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, 4 ≤ k → ∀ σ t : ℝ,
    1 - 1 / (2 : ℝ) ^ (k + 2) ≤ σ → σ ≤ 2 → 4 * (k.factorial : ℝ) ^ 6 ≤ t →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C * t ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) * (1 + Real.log t) := by
  refine ⟨4096, by norm_num, fun k hk σ t hσlo hσhi ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hfac1 : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast Nat.factorial_pos k)
  have htge4 : (4 : ℝ) ≤ t := le_trans (by nlinarith [hfac1]) ht
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (2 : ℝ) ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hεbd : (1 : ℝ) / (2 : ℝ) ^ (k + 2) ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) h64
  have hσhalf : (1 : ℝ) / 2 ≤ σ := by linarith
  have hσ0 : 0 < s.re := by rw [hsre]; linarith
  have him : 0 < s.im := by rw [hsim]; linarith
  set N : ℕ := ⌊t ^ 2⌋₊ with hNdef
  have ht2ge : (16 : ℝ) ≤ t ^ 2 := by nlinarith [htge4]
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith [ht2ge])
  have hNle : (N : ℝ) ≤ t ^ 2 := Nat.floor_le (by positivity)
  have hNhalf : t ^ 2 / 2 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one (t ^ 2)
    rw [← hNdef] at h; nlinarith [ht2ge]
  have hσ2 : (0 : ℝ) < t ^ 2 := by positivity
  -- (A) error ≤ 16
  have hNsig : (N : ℝ) ^ (-σ) ≤ 4 * (t ^ 2) ^ (-σ) := by
    have hstep : (N : ℝ) ^ (-σ) ≤ (t ^ 2 / 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hNhalf (by linarith)
    have hval : (t ^ 2 / 2) ^ (-σ) ≤ 4 * (t ^ 2) ^ (-σ) := by
      rw [Real.div_rpow (le_of_lt hσ2) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv, inv_inv, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hσ2) _)
      calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσhi
        _ = 4 := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    linarith
  have hsnorm : ‖s‖ ≤ 2 + t := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im s) ?_
    rw [hsre, hsim, abs_of_pos (by linarith : (0:ℝ) < σ), abs_of_pos htpos]; linarith
  have hA : ‖riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ 16 := by
    refine le_trans (norm_zeta_sub_approx_le hσ0 him hN1) ?_
    rw [hsre]
    have hσinv : (1 : ℝ) / σ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have ht12σ : (t ^ 2) ^ (-σ) = t ^ (-2 * σ) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul (le_of_lt htpos)]; congr 1; push_cast; ring
    have hstep1 : ‖s‖ * (N : ℝ) ^ (-σ) / σ ≤ (2 + t) * (4 * (t ^ 2) ^ (-σ)) * 2 := by
      rw [div_eq_mul_inv]
      refine mul_le_mul (mul_le_mul hsnorm hNsig (Real.rpow_nonneg (by positivity) _) (by linarith))
        ?_ (by positivity) (by positivity)
      rw [← one_div]; exact hσinv
    refine le_trans hstep1 ?_
    rw [ht12σ]
    have htexp : t * t ^ (-2 * σ) = t ^ (1 - 2 * σ) := by
      rw [show (1 - 2 * σ) = 1 + (-2 * σ) from by ring, Real.rpow_add htpos, Real.rpow_one]
    have htle1 : t ^ (1 - 2 * σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
    have htnn : (0 : ℝ) ≤ t ^ (-2 * σ) := Real.rpow_nonneg (le_of_lt htpos) _
    nlinarith [mul_le_mul_of_nonneg_right (show (2 + t) ≤ 2 * t by linarith) htnn, htexp, htle1]
  -- (C) pole ≤ 1
  have hC : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
    rw [norm_div]
    have hNRpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hpole_norm : ‖(N : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
      rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hNRpos, Complex.sub_re, Complex.one_re, hsre]
    have hden : t ≤ ‖s - 1‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm (s - 1))
      rw [Complex.sub_im, Complex.one_im, hsim, sub_zero, abs_of_pos htpos]
    rw [hpole_norm]
    have hNσ1 : (N : ℝ) ^ (1 - σ) ≤ t := by
      rcases le_or_gt σ 1 with hs1 | hs1
      · calc (N : ℝ) ^ (1 - σ) ≤ (t ^ 2) ^ (1 - σ) := Real.rpow_le_rpow (by positivity) hNle (by linarith)
          _ = t ^ (2 * (1 - σ)) := by
              rw [← Real.rpow_natCast t 2, ← Real.rpow_mul (le_of_lt htpos)]; norm_num
          _ ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
          _ = t := Real.rpow_one t
      · have : (N : ℝ) ^ (1 - σ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
        linarith
    rw [div_le_one (lt_of_lt_of_le htpos hden)]
    exact le_trans hNσ1 hden
  -- M₀ and its facts
  set c : ℕ := ⌈t ^ (1 / ((k : ℝ) - 1))⌉₊ with hc
  set M₀ : ℕ := k.factorial ^ 6 * c with hM₀
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkexp : (0 : ℝ) ≤ 1 / ((k : ℝ) - 1) := le_of_lt (div_pos one_pos hkm1)
  have hBkexp : (0 : ℝ) ≤ 1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1)) :=
    le_of_lt (div_pos one_pos (mul_pos (by positivity) hkm1))
  have htpow_pos : (0 : ℝ) < t ^ (1 / ((k : ℝ) - 1)) := Real.rpow_pos_of_pos htpos _
  have hc0 : 0 < c := Nat.ceil_pos.mpr htpow_pos
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
  have hM₀R : (M₀ : ℝ) = (k.factorial : ℝ) ^ 6 * (c : ℝ) := by rw [hM₀]; push_cast; ring
  have hM₀N1 : 1 ≤ M₀ := by
    have : (1 : ℝ) ≤ (M₀ : ℝ) := by rw [hM₀R]; nlinarith [hfac1, hcR1]
    exact_mod_cast this
  have hM₀floor : (k.factorial : ℝ) ^ 6 ≤ (M₀ : ℝ) := by
    rw [hM₀R]; nlinarith [hfac1, hcR1, mul_nonneg (by linarith [hfac1] : (0:ℝ) ≤ (k.factorial:ℝ)^6) (by linarith [hcR1] : (0:ℝ) ≤ (c:ℝ) - 1)]
  have hM₀leN : M₀ ≤ N := by
    have hc2 : (c : ℝ) ≤ 2 * t ^ (1 / ((k : ℝ) - 1)) := by
      rw [hc]; have hp1 : (1 : ℝ) ≤ t ^ (1 / ((k : ℝ) - 1)) := Real.one_le_rpow ht1 hkexp
      calc ((⌈t ^ (1 / ((k : ℝ) - 1))⌉₊ : ℕ) : ℝ) ≤ t ^ (1 / ((k : ℝ) - 1)) + 1 :=
            le_of_lt (Nat.ceil_lt_add_one (le_of_lt htpow_pos))
        _ ≤ 2 * t ^ (1 / ((k : ℝ) - 1)) := by linarith
    have htp_t : t ^ (1 / ((k : ℝ) - 1)) ≤ t := by
      calc t ^ (1 / ((k : ℝ) - 1)) ≤ t ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht1 (by rw [div_le_one (by linarith)]; linarith)
        _ = t := Real.rpow_one t
    have hM₀le_t2 : (M₀ : ℝ) ≤ t ^ 2 / 2 := by
      rw [hM₀R]
      calc (k.factorial : ℝ) ^ 6 * (c : ℝ) ≤ (t / 4) * (2 * t ^ (1 / ((k : ℝ) - 1))) :=
            mul_le_mul (by linarith [ht]) hc2 (by positivity) (by linarith [htge4])
        _ = (t / 2) * t ^ (1 / ((k : ℝ) - 1)) := by ring
        _ ≤ (t / 2) * t := mul_le_mul_of_nonneg_left htp_t (by linarith)
        _ = t ^ 2 / 2 := by ring
    have : (M₀ : ℝ) ≤ (N : ℝ) := le_trans hM₀le_t2 hNhalf
    exact_mod_cast this
  -- (B) head
  have hB : ‖∑ n ∈ Finset.Icc 1 M₀, (n : ℂ) ^ (-s)‖
      ≤ 16 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) * (1 + Real.log t) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Icc 1 M₀, ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-σ) := by
      intro n hn; rw [Finset.mem_Icc] at hn
      rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn.1 : (0:ℝ) < (n:ℝ)),
        Complex.neg_re, hsre]
    rw [Finset.sum_congr rfl hterm]
    exact zeta_head_bound k hk σ t hσlo hσhi ht
  -- (D) ladder
  have hLad : ‖∑ n ∈ Finset.Ioc M₀ N, (n : ℂ) ^ (-s)‖ ≤ 4044 * (1 + Real.log t) := by
    have hguard := m0_guard k hk t ht1 c hc0 (Nat.le_ceil _)
    exact zeta_ladder_bound k hk σ t hσlo hσhi ht1 M₀ hM₀N1 hM₀floor hguard N hM₀leN hNle
  -- assemble
  have hIcc_Ioc : ∀ x : ℕ, Finset.Icc 1 x = Finset.Ioc 0 x :=
    fun x => by ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)
      = ∑ n ∈ Finset.Icc 1 M₀, (n : ℂ) ^ (-s) + ∑ n ∈ Finset.Ioc M₀ N, (n : ℂ) ^ (-s) := by
    rw [hIcc_Ioc N, hIcc_Ioc M₀]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le M₀) hM₀leN).symm
  have hsum_s : (1 : ℝ) ≤ 1 + Real.log t := by linarith
  have htri : ‖riemannZeta s‖
      ≤ 16 + 16 * t ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) * (1 + Real.log t)
        + 4044 * (1 + Real.log t) + 1 := by
    have hz : riemannZeta s
        = (riemannZeta s - (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (s - 1))
          + (∑ n ∈ Finset.Icc 1 M₀, (n : ℂ) ^ (-s))
          + (∑ n ∈ Finset.Ioc M₀ N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) := by
      rw [hsplit]; ring
    rw [hz]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ hC)
    refine le_trans (norm_add_le _ _) (add_le_add ?_ hLad)
    exact le_trans (norm_add_le _ _) (add_le_add hA hB)
  refine le_trans htri ?_
  have hBk1 : (1 : ℝ) ≤ t ^ (1 / ((2 : ℝ) ^ (k + 2) * ((k : ℝ) - 1))) :=
    Real.one_le_rpow ht1 hBkexp
  nlinarith [hBk1, hsum_s, hlogt,
    mul_nonneg (by linarith [hBk1] : (0:ℝ) ≤ t ^ (1 / ((2:ℝ)^(k+2)*((k:ℝ)-1))) - 1)
      (by linarith [hsum_s] : (0:ℝ) ≤ 1 + Real.log t)]

end Salt.ExpSum
