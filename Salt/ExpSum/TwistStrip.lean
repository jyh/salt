/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.Twist

/-!
# VK-TWIST VT-4(a) — the twisted van der Corput strip (the HIGH branch, phase side)

`Salt/Vk/TwistLadder.lean` (VT-3) threaded the twist `e(βn)` through the *Vinogradov*
half of the per-block routing and stopped at the boundary `10·log M ≥ log t`, where the
landed `ExpSum.zeta_block_dispatch` takes over.  VT-3's reading of that boundary was:
"the dispatch's first sub-case is **Kusmin**, a *first*-derivative test, and VT-1's affine
blindness starts at order 2 — so the high branch does not transcribe."

That reading is **half** right, and this file is the other half.

## What actually transcribes

`zeta_block_dispatch` is a four-case split on `t` against the block base `M`:

| case | range | engine | twists? |
|---|---|---|---|
| (i) | `t ≤ M` | Kusmin–Landau (1st derivative) | **no** |
| (ii) | `M < t ≤ 27πM` | `zeta_block_vdC_prefix` at `k = 2` | **yes** |
| (iii) | `27πM < t ≤ M²/2` | ditto at `k = 3` | **yes** |
| (iv) | `M²/2 < t` | ditto at `k = k' ∈ [4, k]` | **yes** |

Cases (ii)–(iv) read the phase *only* through `dk k` with `k ≥ 2`, which is exactly what
VT-1's `dk_add_linear` annihilates: `zeta_dk_window_twist` hands the engine the identical
window `[λ, cλ]`.  So they transcribe verbatim, and this file transcribes them —
`zeta_block_vdC_prefix_twist`, `zeta_block_prefix_collapse_twist`, and the three window
discharges `zeta_window_prefix_twist` / `zeta_seam_prefix_twist` / `zeta_patch_prefix_twist`
are the landed proofs with the phase `phi t n` replaced by `phi t n + β·n` and the two
sites that read it (`zeta_dk_window` → `zeta_dk_window_twist`, `norm_sum_eR_signed` at the
twisted argument) re-pointed.  Every constant is the landed one.

## What replaces Kusmin

Case (i) is the only genuinely blocked one — and it does not need Kusmin at all.  On
`t ≤ M` the `k = 2` van der Corput bound already suffices, because there the two terms of
`zeta_block_vdC_prefix_twist 2` read

  `M·λ^{1/2} ≤ √M`   (from `M²λ ≤ t/(8π) ≤ M`)  and  `λ^{−1/2} ≤ 7.6·M/√t`,

and the `√t` in the second term is harmless: the consumer knows `M ≤ t²`, so
`M^{1−σ} ≤ t^{1/32} ≤ √t` on the strip.  `zeta_lowt_prefix_twist` is that bound.  It is
*not* a weaker Kusmin: it is a different (and, on this range, entirely sufficient) test,
and it is affine-blind by construction.

So the twisted high branch needs **no Diophantine hypothesis on `β`**, and in particular
no `√q` is spent here.  (The `√q` of the classical treatment is spent at the Gauss
completion, one level up, in `Salt/MR/VkTwistLadder.lean`.)

Conventions unchanged: `eR x = exp(2πi·x)`, `phi t n = −(t/2π)·log n`, twisted summand
`eR (phi t n + β·n)`.
-/

namespace Salt.ExpSum

open Finset Real

/-! ## §1 — the twisted van der Corput prefix block (constant 144) -/

/-- **The twisted van der Corput prefix block, explicit constant 144.**  The twin of
`zeta_block_vdC_prefix`: for `k ≥ 2` and a prefix `(N, x]` of `(N, 2N]`, the *twisted*
phase sum obeys the *same* bound `144·(N·λ^α + N^β·λ^{−α})`.

The engine (`isVdCBound_16`) reads the phase only through `dk k`, and `dk k` is blind to
the affine `β·n` for `k ≥ 2` (`zeta_dk_window_twist`); the sign correction `(−1)^k` maps
the twist to `(−1)^k·β`, which is still affine. -/
theorem zeta_block_vdC_prefix_twist (k : ℕ) (hk : 2 ≤ k)
    (t : ℝ) (N : ℕ) (lam : ℝ) (x : ℤ) (β : ℝ) (ht : 0 < t) (hkN : k ≤ N)
    (hlam : lam = t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹)
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n + β * (n : ℝ))‖
      ≤ 144 * ((N : ℝ) * lam ^ (1 / ((2 : ℝ) ^ k - 2))
          + (N : ℝ) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(1 / ((2 : ℝ) ^ k - 2)))) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlam
  have hi1 : 1 ≤ i := by omega
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have htp : (0 : ℝ) < t / (2 * π) := div_pos ht (by positivity)
  have hfacpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  set g : ℤ → ℝ := fun m => (-1 : ℝ) ^ (i + 1) * (phi t m + β * (m : ℝ)) with hg
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
  -- apply the engine at a = N, b = x, with the TWISTED window
  have hab : (N : ℤ) ≤ x := le_of_lt hx1
  have hbase := isVdCBound_16 (i + 1) hk g (N : ℤ) x lam cc hab hlampos hcc1
    (fun n h1 h2 => by
      rw [hlam]; exact (zeta_dk_window_twist t ht β i hi1 N hN1 n h1 (by omega)).1)
    (fun n h1 h2 => by
      rw [hclam]; exact (zeta_dk_window_twist t ht β i hi1 N hN1 n h1 (by omega)).2)
  have hnorm : ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (g n)‖
      = ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n + β * (n : ℝ))‖ := by
    simp only [hg]
    exact norm_sum_eR_signed _ (fun m : ℤ => phi t m + β * (m : ℝ)) (i + 1)
  rw [← hnorm]
  refine le_trans hbase ?_
  set α : ℝ := 1 / ((2 : ℝ) ^ (i + 1) - 2) with hα
  set βe : ℝ := 1 - 4 / (2 : ℝ) ^ (i + 1) with hβ
  have hβ0 : (0 : ℝ) ≤ βe := by
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
        + ((x : ℝ) - (N : ℤ)) ^ βe * lam ^ (-α)
      ≤ (N : ℝ) * lam ^ α + (N : ℝ) ^ βe * lam ^ (-α) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hxNle hlamα
    · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hxNnn hxNle hβ0) hlamnα
  have hbx_nonneg : (0 : ℝ) ≤ ((x : ℝ) - (N : ℤ)) * lam ^ α
      + ((x : ℝ) - (N : ℤ)) ^ βe * lam ^ (-α) :=
    add_nonneg (mul_nonneg hxNnn hlamα)
      (mul_nonneg (Real.rpow_nonneg hxNnn _) hlamnα)
  have hcoef : 16 * cc ^ (4 / (2 : ℝ) ^ (i + 1)) ≤ 144 := by
    nlinarith [hcc9, hcc0]
  calc 16 * cc ^ (4 / (2 : ℝ) ^ (i + 1))
        * (((x : ℝ) - (N : ℤ)) * lam ^ α + ((x : ℝ) - (N : ℤ)) ^ βe * lam ^ (-α))
      ≤ 144 * (((x : ℝ) - (N : ℤ)) * lam ^ α
          + ((x : ℝ) - (N : ℤ)) ^ βe * lam ^ (-α)) :=
        mul_le_mul_of_nonneg_right hcoef hbx_nonneg
    _ ≤ 144 * ((N : ℝ) * lam ^ α + (N : ℝ) ^ βe * lam ^ (-α)) :=
        mul_le_mul_of_nonneg_left hbrk (by norm_num)

/-! ## §2 — the collapsed twisted prefix block (constant 288) -/

/-- **The collapsed twisted prefix block bound.**  Twin of `zeta_block_prefix_collapse`:
on the honest van der Corput window `λ ∈ [N^{−3+8/2^k}, N^{−1}]` the two-term twisted
bound collapses to `288·N^{1−1/(2^k−2)}`.  Pure real arithmetic on top of
`zeta_block_vdC_prefix_twist`; the phase never reappears. -/
theorem zeta_block_prefix_collapse_twist (k : ℕ) (hk : 2 ≤ k)
    (t : ℝ) (N : ℕ) (lam : ℝ) (x : ℤ) (β : ℝ) (ht : 0 < t) (hkN : k ≤ N)
    (hlam : lam = t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹)
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N)
    (hrlo : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) ≤ lam) (hrhi : lam ≤ (N : ℝ) ^ (-1 : ℝ)) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n + β * (n : ℝ))‖
      ≤ 288 * (N : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) := by
  have hb := zeta_block_vdC_prefix_twist k hk t N lam x β ht hkN hlam hx1 hx2
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have h2k : (4 : ℝ) ≤ (2 : ℝ) ^ k := four_le_two_pow k hk
  set p : ℝ := (2 : ℝ) ^ k with hp
  set α : ℝ := 1 / (p - 2) with hαdef
  set βe : ℝ := 1 - 4 / p with hβdef
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
  have hterm2 : (N : ℝ) ^ βe * lam ^ (-α) ≤ (N : ℝ) ^ (1 - α) := by
    set Mlo : ℝ := (N : ℝ) ^ (-3 + 8 / p) with hM
    have hMpos : (0 : ℝ) < Mlo := Real.rpow_pos_of_pos hNpos _
    have hlaminv : lam ^ (-α) ≤ Mlo ^ (-α) := by
      rw [Real.rpow_neg hlamnn, Real.rpow_neg (le_of_lt hMpos)]
      exact inv_anti₀ (Real.rpow_pos_of_pos hMpos _)
        (Real.rpow_le_rpow (le_of_lt hMpos) hrlo (le_of_lt hα0))
    have hstep : (N : ℝ) ^ βe * lam ^ (-α) ≤ (N : ℝ) ^ βe * Mlo ^ (-α) :=
      mul_le_mul_of_nonneg_left hlaminv (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hcombine : (N : ℝ) ^ βe * Mlo ^ (-α) = (N : ℝ) ^ (1 - α) := by
      rw [hM, ← Real.rpow_mul (le_of_lt hNpos), ← Real.rpow_add hNpos]
      congr 1
      rw [hβdef, hαdef]; field_simp; ring
    rw [← hcombine]; exact hstep
  refine le_trans hb ?_
  have hsum : (N : ℝ) * lam ^ α + (N : ℝ) ^ βe * lam ^ (-α) ≤ 2 * (N : ℝ) ^ (1 - α) := by
    linarith [hterm1, hterm2]
  calc 144 * ((N : ℝ) * lam ^ α + (N : ℝ) ^ βe * lam ^ (-α))
      ≤ 144 * (2 * (N : ℝ) ^ (1 - α)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 288 * (N : ℝ) ^ (1 - α) := by ring

/-! ## §3 — the three twisted window discharges -/

/-- **The twisted `k ≥ 4` window discharge.**  Twin of `zeta_window_prefix`: on the
factorial-shifted window `t ∈ [N^{k−2}/(k−2)!, N^{k−1}/(k−1)!]` with floor `N ≥ (k!)^6`,
the twisted prefix block collapses to `288·N^{1−1/(2^k−2)}`.  The λ-sandwich is
phase-independent; only the closing call changes. -/
theorem zeta_window_prefix_twist (k : ℕ) (hk : 4 ≤ k) (t : ℝ) (N : ℕ) (x : ℤ) (β : ℝ)
    (hN0 : (k.factorial : ℝ) ^ 6 ≤ (N : ℝ))
    (hlo : (N : ℝ) ^ ((k : ℝ) - 2) / ((k - 2).factorial : ℝ) ≤ t)
    (hhi : t ≤ (N : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ))
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n + β * (n : ℝ))‖
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
  exact zeta_block_prefix_collapse_twist k (by omega) t N lam x β htpos hkN hlam_def hx1 hx2
    hrlo hrhi

/-- **The twisted `k = 3` seam.**  Twin of `zeta_seam_prefix`: on `t ∈ [27π·N, N²/2]`
with floor `N ≥ 3`, the twisted prefix block collapses to `288·N^{5/6}`. -/
theorem zeta_seam_prefix_twist (t : ℝ) (N : ℕ) (x : ℤ) (β : ℝ) (hN3 : 3 ≤ N)
    (hlo : 27 * π * (N : ℝ) ≤ t)
    (hhi : t ≤ (N : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ))
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n + β * (n : ℝ))‖
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
  exact zeta_block_prefix_collapse_twist 3 (by norm_num) t N lam x β htpos hN3 hlam_def hx1 hx2
    hrlo hrhi

/-- **The twisted `k = 2` patch.**  Twin of `zeta_patch_prefix`: on `N ≤ t ≤ 27π·N` with
floor `N ≥ 2`, the twisted prefix block obeys `1348·√N`.  Razor-thin constants unchanged. -/
theorem zeta_patch_prefix_twist (t : ℝ) (N : ℕ) (x : ℤ) (β : ℝ) (hN2 : 2 ≤ N)
    (hlo : (N : ℝ) ≤ t) (hhi : t ≤ 27 * π * (N : ℝ))
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n + β * (n : ℝ))‖
      ≤ 1348 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hNRpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have htpos : 0 < t := lt_of_lt_of_le hNRpos hlo
  set lam : ℝ := t / (2 * π) * ((2 - 1).factorial : ℝ) * (((2 * N + 2 : ℕ) : ℝ) ^ 2)⁻¹
    with hlam_def
  have hvdc := zeta_block_vdC_prefix_twist 2 (by norm_num) t N lam x β htpos hN2 hlam_def hx1 hx2
  have e1 : (1 : ℝ) / ((2 : ℝ) ^ 2 - 2) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) - 4 / (2 : ℝ) ^ 2 = 0 := by norm_num
  rw [e1, e2, Real.rpow_zero, one_mul] at hvdc
  have hlam2 : lam = t / (2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2) := by
    have hfac1 : ((2 - 1).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
    have hπ : π ≠ 0 := ne_of_gt Real.pi_pos
    have hD : ((2 * N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hlam_def, hfac1, mul_one]; field_simp
  have hDpos : (0 : ℝ) < ((2 * N + 2 : ℕ) : ℝ) := by positivity
  have hlam_pos : 0 < lam := by rw [hlam2]; positivity
  have hsqrt1 : lam ^ (1 / 2 : ℝ) = Real.sqrt lam := (Real.sqrt_eq_rpow lam).symm
  have hsqrtN : (N : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (N : ℝ) := (Real.sqrt_eq_rpow (N : ℝ)).symm
  have hsqrt2 : lam ^ (-(1 / 2) : ℝ) = Real.sqrt lam⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hlam_pos), hsqrt1, ← Real.sqrt_inv]
  have hD2ge : (4 : ℝ) * (N : ℝ) ^ 2 ≤ ((2 * N + 2 : ℕ) : ℝ) ^ 2 := by
    have h : 2 * (N : ℝ) ≤ ((2 * N + 2 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * (N:ℝ)) h 2]
  have hD2le : ((2 * N + 2 : ℕ) : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by
    have h : ((2 * N + 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      push_cast; linarith
    nlinarith [pow_le_pow_left₀ hDpos.le h 2]
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
  refine le_trans hvdc ?_
  have hsqrtNnn : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc 144 * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2) : ℝ))
      ≤ 144 * (1.84 * (N : ℝ) ^ (1 / 2 : ℝ) + 7.52 * (N : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (by norm_num)
    _ ≤ 1348 * (N : ℝ) ^ (1 / 2 : ℝ) := by nlinarith [hsqrtNnn]

/-! ## §4 — the low-`t` branch: what replaces Kusmin -/

/-- **The twisted low-`t` prefix block — the Kusmin replacement.**  On `t ≤ N` (where the
untwisted dispatch runs Kusmin–Landau, a *first*-derivative test the twist destroys), the
`k = 2` van der Corput bound already suffices:

  `‖∑_{N<n≤x} e(βn)·n^{−it}‖ ≤ 144·√N + 1095·N/√t`.

The two terms are `144·N·λ^{1/2} ≤ 144·√N` (from `N²λ = N²t/(2π(2N+2)²) ≤ t/(8π) ≤ N`)
and `144·λ^{−1/2} ≤ 144·7.6·N/√t`.  The `√t` denominator is exactly what makes this
*better* than Kusmin here — the consumer supplies `N ≤ t²`, and `N^{1−σ} ≤ √t` on the
strip.  Affine-blind by construction: `k = 2 ≥ 2`. -/
theorem zeta_lowt_prefix_twist (t : ℝ) (N : ℕ) (x : ℤ) (β : ℝ) (hN2 : 2 ≤ N)
    (ht0 : 0 < t) (hle : t ≤ (N : ℝ))
    (hx1 : (N : ℤ) < x) (hx2 : x ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) x, eR (phi t n + β * (n : ℝ))‖
      ≤ 144 * Real.sqrt (N : ℝ) + 1095 * (N : ℝ) / Real.sqrt t := by
  have hNRpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  set lam : ℝ := t / (2 * π) * ((2 - 1).factorial : ℝ) * (((2 * N + 2 : ℕ) : ℝ) ^ 2)⁻¹
    with hlam_def
  have hvdc := zeta_block_vdC_prefix_twist 2 (by norm_num) t N lam x β ht0 hN2 hlam_def hx1 hx2
  have e1 : (1 : ℝ) / ((2 : ℝ) ^ 2 - 2) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) - 4 / (2 : ℝ) ^ 2 = 0 := by norm_num
  rw [e1, e2, Real.rpow_zero, one_mul] at hvdc
  have hlam2 : lam = t / (2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2) := by
    have hfac1 : ((2 - 1).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
    have hπ : π ≠ 0 := ne_of_gt Real.pi_pos
    have hD : ((2 * N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hlam_def, hfac1, mul_one]; field_simp
  have hDpos : (0 : ℝ) < ((2 * N + 2 : ℕ) : ℝ) := by positivity
  have hlam_pos : 0 < lam := by rw [hlam2]; positivity
  have hsqrt1 : lam ^ (1 / 2 : ℝ) = Real.sqrt lam := (Real.sqrt_eq_rpow lam).symm
  have hsqrt2 : lam ^ (-(1 / 2) : ℝ) = Real.sqrt lam⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hlam_pos), hsqrt1, ← Real.sqrt_inv]
  have hD2ge : (4 : ℝ) * (N : ℝ) ^ 2 ≤ ((2 * N + 2 : ℕ) : ℝ) ^ 2 := by
    have h : 2 * (N : ℝ) ≤ ((2 * N + 2 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2 * (N:ℝ)) h 2]
  have hD2le : ((2 * N + 2 : ℕ) : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by
    have h : ((2 * N + 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      push_cast; linarith
    nlinarith [pow_le_pow_left₀ hDpos.le h 2]
  -- term 1:  N·√λ = √(N²λ) ≤ √N, since N²λ ≤ t/(8π) ≤ N
  have hT1 : (N : ℝ) * lam ^ (1 / 2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [hsqrt1]
    have hT1eq : (N : ℝ) * Real.sqrt lam = Real.sqrt ((N : ℝ) ^ 2 * lam) := by
      rw [Real.sqrt_mul (sq_nonneg (N : ℝ)) lam, Real.sqrt_sq (Nat.cast_nonneg N)]
    have hkey : (N : ℝ) ^ 2 * lam ≤ (N : ℝ) := by
      rw [hlam2, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      have h1 : (N : ℝ) ^ 2 * t ≤ (N : ℝ) ^ 2 * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hle (sq_nonneg (N : ℝ))
      have hD8 : 8 * π * (N : ℝ) ^ 2 ≤ 2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2 := by
        nlinarith [hD2ge, Real.pi_pos]
      have hcube : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
      have h2 : (N : ℝ) ^ 2 * (N : ℝ) ≤ (N : ℝ) * (8 * π * (N : ℝ) ^ 2) := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 * π - 1 by linarith [Real.pi_gt_three]) hcube]
      have h3 : (N : ℝ) * (8 * π * (N : ℝ) ^ 2)
          ≤ (N : ℝ) * (2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hD8 hNRpos.le
      linarith
    rw [hT1eq]
    exact Real.sqrt_le_sqrt hkey
  -- term 2:  λ^{−1/2} = √(λ⁻¹) ≤ 7.6·N/√t
  have hsqrtt : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hT2 : lam ^ (-(1 / 2) : ℝ) ≤ 7.6 * (N : ℝ) / Real.sqrt t := by
    rw [hsqrt2]
    have hlaminv_eq : lam⁻¹ = 2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2 * t⁻¹ := by
      rw [hlam2, inv_div, div_eq_mul_inv]
    have hnum : 2 * π * ((2 * N + 2 : ℕ) : ℝ) ^ 2 ≤ 57 * (N : ℝ) ^ 2 := by
      nlinarith [hD2le, Real.pi_lt_d6, sq_nonneg (N : ℝ)]
    have hinv : lam⁻¹ ≤ 57 * (N : ℝ) ^ 2 * t⁻¹ := by
      rw [hlaminv_eq]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr ht0.le)
    have hstep : Real.sqrt lam⁻¹ ≤ Real.sqrt (57 * (N : ℝ) ^ 2 * t⁻¹) :=
      Real.sqrt_le_sqrt hinv
    have heq : Real.sqrt (57 * (N : ℝ) ^ 2 * t⁻¹)
        = Real.sqrt (57 * (N : ℝ) ^ 2) * (Real.sqrt t)⁻¹ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]
    have hb : Real.sqrt (57 * (N : ℝ) ^ 2) ≤ 7.6 * (N : ℝ) := by
      rw [Real.sqrt_mul (show (0:ℝ) ≤ 57 by norm_num), Real.sqrt_sq (Nat.cast_nonneg N)]
      have h57 : Real.sqrt 57 ≤ 7.6 := by
        rw [show (7.6 : ℝ) = Real.sqrt (7.6 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) N, Real.sqrt_nonneg (57 : ℝ)]
    calc Real.sqrt lam⁻¹ ≤ Real.sqrt (57 * (N : ℝ) ^ 2) * (Real.sqrt t)⁻¹ := by
          rw [← heq]; exact hstep
      _ ≤ (7.6 * (N : ℝ)) * (Real.sqrt t)⁻¹ :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 7.6 * (N : ℝ) / Real.sqrt t := by rw [div_eq_mul_inv]
  refine le_trans hvdc ?_
  have hd : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt t := by positivity
  calc 144 * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2) : ℝ))
      ≤ 144 * (Real.sqrt (N : ℝ) + 7.6 * (N : ℝ) / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (by norm_num)
    _ ≤ 144 * Real.sqrt (N : ℝ) + 1095 * (N : ℝ) / Real.sqrt t := by
        rw [mul_add]
        have : (144 : ℝ) * (7.6 * (N : ℝ) / Real.sqrt t) = 1094.4 * ((N : ℝ) / Real.sqrt t) := by
          ring
        rw [this]
        have h2 : (1095 : ℝ) * (N : ℝ) / Real.sqrt t = 1095 * ((N : ℝ) / Real.sqrt t) := by
          ring
        rw [h2]
        nlinarith [hd]

end Salt.ExpSum
