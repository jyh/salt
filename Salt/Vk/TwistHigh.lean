/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.TwistLadder
import Salt.ExpSum.TwistStrip

/-!
# VK-TWIST VT-4(b) — the twisted high branch, discharged

VT-3 (`Salt/Vk/TwistLadder.lean`) landed the twisted per-block bound on the *non-high*
range `10·log M < log t` and left `vk_dirichlet_block_twist_le_of_high`'s residual `hhigh`
— the range `log t ≤ 10·log M`, where the untwisted routing runs
`ExpSum.zeta_block_dispatch` — as an explicit socket binder.

This file **discharges that socket**.  `Salt/ExpSum/TwistStrip.lean` supplies the twisted
twins of the dispatch's three van der Corput sub-cases (which transcribe, `k ≥ 2` being
affine-blind) together with `zeta_lowt_prefix_twist`, the `k = 2` bound that replaces the
one sub-case that does not (Kusmin, `t ≤ M`).  Here they are re-assembled into

* `zeta_block_dispatch_twist` — the twisted twin of `ExpSum.zeta_block_dispatch`, same
  hypotheses, same `1348`;
* `vk_dirichlet_block_twist_all` — the **unconditional** twisted per-block bound: every
  dyadic block, every `β`, no socket.

The consequence for the campaign: no Diophantine hypothesis on `β` is needed anywhere in
the ladder, so the `√q` VT-4 spends is spent *only* at the Gauss/Fourier completion one
level up, never per block.
-/

namespace Salt.Vk

open Finset Real Salt.ExpSum

/-- **The twisted per-block dispatch.**  Byte-for-byte the hypotheses of
`ExpSum.zeta_block_dispatch`, with the twist `e(βn)` in the summand and the same absolute
constant `1348`.

Four cases on `t` against the block base `M`, as untwisted.  Cases (ii)–(iv) are the landed
van der Corput windows, twisted (`zeta_patch_prefix_twist`, `zeta_seam_prefix_twist`,
`zeta_window_prefix_twist`); case (i) — untwisted Kusmin, `t ≤ M` — is replaced by
`zeta_lowt_prefix_twist`, whose `√t` denominator is paid off by `M ≤ t²` on the strip.

One binder is *dropped*, not added: the untwisted dispatch carries `σ ≤ 2`, which the
replacement for case (i) does not need — so this statement is strictly more general in `σ`,
exactly as VT-3's `vk_dirichlet_block_twist_le` is. -/
theorem zeta_block_dispatch_twist (k : ℕ) (hk : 4 ≤ k) (σ t β : ℝ)
    (hσlo : 1 - 1 / (2 : ℝ) ^ (k + 2) ≤ σ) (ht1 : 1 ≤ t)
    (M x' : ℕ) (hM : (k.factorial : ℝ) ^ 6 ≤ (M : ℝ)) (hMx' : M < x') (hx'2 : x' ≤ 2 * M)
    (hMt2 : (M : ℝ) ≤ t ^ 2)
    (hguard : t ≤ (M : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ)) :
    ‖∑ n ∈ Finset.Ioc M x',
        eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 := by
  have hfacpos : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := le_trans (one_le_pow₀ hfacpos) hM
    exact_mod_cast this
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hMRpos : (0 : ℝ) < (M : ℝ) := by linarith
  have htpos : 0 < t := by linarith
  have hπpos : (0 : ℝ) < π := Real.pi_pos
  have hx'2Z : (x' : ℤ) ≤ 2 * (M : ℤ) := by exact_mod_cast hx'2
  -- strip facts
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
  -- the folding helper for the single-power cases
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
  · -- (i) t ≤ M:  the `k = 2` replacement for Kusmin
    have hM2 : 2 ≤ M := by omega
    have hsqrt_t_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have hBnn : (0 : ℝ) ≤ 144 * Real.sqrt (M : ℝ) + 1095 * (M : ℝ) / Real.sqrt t := by
      positivity
    have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
        ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n + β * (n : ℝ))‖
          ≤ 144 * Real.sqrt (M : ℝ) + 1095 * (M : ℝ) / Real.sqrt t :=
      fun y hy1 hy2 =>
        zeta_lowt_prefix_twist t M y β hM2 htpos hc1 hy1 (le_trans hy2 hx'2Z)
    refine le_trans (vk_weighted_block_twist σ t β hσpos M x' hM1 hMx' _ hBnn hpref) ?_
    -- `M^{−σ}·(144√M + 1095·M/√t) ≤ 1348`
    have hstepA : (M : ℝ) ^ (-σ) * Real.sqrt (M : ℝ) ≤ 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hMRpos]
      exact Real.rpow_le_one_of_one_le_of_nonpos hMR1 (by linarith)
    have hkey : (M : ℝ) ^ (1 - σ) ≤ Real.sqrt t := by
      have e1 : (M : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ ((1 : ℝ) / 64) :=
        Real.rpow_le_rpow_of_exponent_le hMR1 (by linarith)
      have e2 : (M : ℝ) ^ ((1 : ℝ) / 64) ≤ (t ^ 2) ^ ((1 : ℝ) / 64) :=
        Real.rpow_le_rpow hMRpos.le hMt2 (by norm_num)
      have e3 : (t ^ 2 : ℝ) ^ ((1 : ℝ) / 64) = t ^ ((1 : ℝ) / 32) := by
        rw [← Real.rpow_natCast t 2, ← Real.rpow_mul htpos.le]
        norm_num
      have e4 : t ^ ((1 : ℝ) / 32) ≤ t ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      rw [Real.sqrt_eq_rpow]
      rw [e3] at e2
      linarith
    have hMcol : (M : ℝ) ^ (-σ) * (M : ℝ) = (M : ℝ) ^ (1 - σ) := by
      rw [← Real.rpow_add_one (ne_of_gt hMRpos) (-σ)]
      congr 1; ring
    have hA : (M : ℝ) ^ (-σ) * (144 * Real.sqrt (M : ℝ)) ≤ 144 := by
      rw [show (M : ℝ) ^ (-σ) * (144 * Real.sqrt (M : ℝ))
            = 144 * ((M : ℝ) ^ (-σ) * Real.sqrt (M : ℝ)) from by ring]
      linarith [hstepA]
    have hB2 : (M : ℝ) ^ (-σ) * (1095 * (M : ℝ) / Real.sqrt t) ≤ 1095 := by
      rw [show (M : ℝ) ^ (-σ) * (1095 * (M : ℝ) / Real.sqrt t)
            = 1095 * ((M : ℝ) ^ (-σ) * (M : ℝ) / Real.sqrt t) from by ring, hMcol]
      have hdiv : (M : ℝ) ^ (1 - σ) / Real.sqrt t ≤ 1 := (div_le_one hsqrt_t_pos).mpr hkey
      linarith
    calc (M : ℝ) ^ (-σ) * (144 * Real.sqrt (M : ℝ) + 1095 * (M : ℝ) / Real.sqrt t)
        = (M : ℝ) ^ (-σ) * (144 * Real.sqrt (M : ℝ))
          + (M : ℝ) ^ (-σ) * (1095 * (M : ℝ) / Real.sqrt t) := by ring
      _ ≤ 1348 := by linarith
  · rcases le_or_gt t (27 * π * (M : ℝ)) with hc2 | hc2
    · -- (ii) M < t ≤ 27πM:  the twisted patch (k = 2)
      have hM2 : 2 ≤ M := by omega
      have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
          ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n + β * (n : ℝ))‖
            ≤ 1348 * (M : ℝ) ^ (1 / 2 : ℝ) :=
        fun y hy1 hy2 => zeta_patch_prefix_twist t M y β hM2 (le_of_lt hc1) hc2 hy1
          (le_trans hy2 hx'2Z)
      have hBnn : (0 : ℝ) ≤ 1348 * (M : ℝ) ^ (1 / 2 : ℝ) := by positivity
      refine le_trans (vk_weighted_block_twist σ t β hσpos M x' hM1 hMx' _ hBnn hpref) ?_
      exact hfin 1348 (1 / 2) (by norm_num) (by linarith) (by norm_num)
    · rcases le_or_gt t ((M : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ)) with hc3 | hc3
      · -- (iii) 27πM < t ≤ M²/2:  the twisted seam (k = 3)
        have hM3 : 3 ≤ M := by omega
        have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
            ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n + β * (n : ℝ))‖
              ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ 3 - 2)) :=
          fun y hy1 hy2 => zeta_seam_prefix_twist t M y β hM3 (le_of_lt hc2) hc3 hy1
            (le_trans hy2 hx'2Z)
        have hBnn : (0 : ℝ) ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ 3 - 2)) := by positivity
        refine le_trans (vk_weighted_block_twist σ t β hσpos M x' hM1 hMx' _ hBnn hpref) ?_
        refine hfin 288 (1 - 1 / ((2 : ℝ) ^ 3 - 2)) (by norm_num) ?_ (by norm_num)
        have : (1 : ℝ) / ((2 : ℝ) ^ 3 - 2) = 1 / 6 := by norm_num
        rw [this]; linarith
      · -- (iv) M²/2 < t ≤ M^{k−1}/(k−1)!:  the twisted window ladder
        have hMsqeq :
            (M : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ) = (M : ℝ) ^ (2 : ℝ) / 2 := by
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
            ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n + β * (n : ℝ))‖
              ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k' - 2)) :=
          fun y hy1 hy2 => zeta_window_prefix_twist k' h4k' t M y β hMk' hlk' huk' hy1
            (le_trans hy2 hx'2Z)
        have hBnn : (0 : ℝ) ≤ 288 * (M : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k' - 2)) := by positivity
        refine le_trans (vk_weighted_block_twist σ t β hσpos M x' hM1 hMx' _ hBnn hpref) ?_
        refine hfin 288 (1 - 1 / ((2 : ℝ) ^ k' - 2)) (by norm_num) ?_ (by norm_num)
        have h2k' : (4 : ℝ) ≤ (2 : ℝ) ^ k' := by
          calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
            _ ≤ (2 : ℝ) ^ k' := pow_le_pow_right₀ (by norm_num) (by omega)
        have hstep1 : (1 : ℝ) / (2 : ℝ) ^ k' ≤ 1 / ((2 : ℝ) ^ k' - 2) :=
          one_div_le_one_div_of_le (by linarith) (by linarith)
        have hstep2 : (1 : ℝ) / (2 : ℝ) ^ (k + 2) ≤ 1 / (2 : ℝ) ^ k' := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        linarith

set_option maxHeartbeats 1000000 in
-- Mirrors `GrowthPow.vk_dirichlet_block_le`'s budget: the same staged rpow/exp/log gate
-- derivation at `k = 12`, threaded through `nlinarith`.
/-- **THE TWISTED PER-BLOCK BOUND, UNCONDITIONAL.**  For every twist `β : ℝ`, on the
sub-unit strip `σ ≥ 1 − vkTheta t` (no upper gate), above the schedule floor
`log t ≥ e^100`, every dyadic block `(M, x']` with `M ≤ t²` obeys

  `‖∑_{M<n≤x'} e(βn)·n^{−(σ+it)}‖ ≤ 1348`.

This is `GrowthPow.vk_dirichlet_block_le` with the twist added and **nothing else changed**
— same grades, same `1348`, no Diophantine hypothesis on `β`.  It discharges VT-3's socket
`vk_dirichlet_block_twist_le_of_high`: the residual high branch is
`zeta_block_dispatch_twist` at `k = 12` (`Θ ≤ 2^{−14}` puts `σ` inside the dispatch's
strip), and the gate derivation `M ≥ (12!)^6`, `t ≤ M^{11}/11!` is the landed one, driven
by `log t ≤ 10·log M` and `log t ≥ e^100`. -/
theorem vk_dirichlet_block_twist_all {σ t β : ℝ} {M x' : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσlo : 1 - vkTheta t ≤ σ)
    (hM1 : 1 ≤ M) (hMx' : M < x') (hx'2 : x' ≤ 2 * M) (hMt2 : (M : ℝ) ≤ t ^ 2) :
    ‖∑ n ∈ Finset.Ioc M x',
        eR (β * (n : ℝ)) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 := by
  have hlogtpos : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hlogt1 : 1 < Real.log t := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith [hL100]
  have ht1 : (1 : ℝ) ≤ t := by
    have h := Real.exp_lt_exp.mpr hlogtpos
    rw [Real.exp_zero, Real.exp_log ht0] at h; linarith
  have hΘ14 : vkTheta t ≤ 1 / (2 : ℝ) ^ 14 := by
    rw [vkTheta]
    have h1 : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have h2 : (100 : ℝ) ≤ Real.log (Real.log t) := by
      rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hL100
    have h3 : (10000 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := by nlinarith [h2]
    have hDpos : 0 < (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) := by
      positivity
    rw [div_le_iff₀ hDpos]
    nlinarith [h1, h3, mul_le_mul h1 h3 (by norm_num) (by positivity)]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  refine vk_dirichlet_block_twist_le_of_high ht0 hL100 hσlo hM1 hMx' hx'2 ?_
  intro hhi
  -- the landed high-branch gate derivation, at `k = 12`
  have hexp2601 : (2601 : ℝ) ≤ Real.exp 100 := by
    have h50 : (51 : ℝ) ≤ Real.exp 50 := by linarith [Real.add_one_le_exp (50 : ℝ)]
    have he : Real.exp 100 = Real.exp 50 * Real.exp 50 := by rw [← Real.exp_add]; norm_num
    nlinarith [h50, he, Real.exp_pos 50]
  have hlogM260 : (260 : ℝ) ≤ Real.log M := by linarith [hhi, hL100, hexp2601]
  have hMfac : ((Nat.factorial 12 : ℝ)) ^ 6 ≤ (M : ℝ) := by
    have hfac2 : (Nat.factorial 12 : ℝ) ≤ 2 ^ 29 := by norm_num [Nat.factorial]
    have hlog2le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hlogfac : Real.log (Nat.factorial 12 : ℝ) ≤ 29 := by
      calc Real.log (Nat.factorial 12 : ℝ) ≤ Real.log ((2 : ℝ) ^ 29) :=
            Real.log_le_log (by positivity) hfac2
        _ = 29 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
        _ ≤ 29 := by nlinarith [hlog2le1]
    have hlog6 : Real.log (((Nat.factorial 12 : ℝ)) ^ 6) ≤ 174 := by
      rw [Real.log_pow]; push_cast; nlinarith [hlogfac]
    rw [show ((Nat.factorial 12 : ℝ)) ^ 6
          = Real.exp (Real.log (((Nat.factorial 12 : ℝ)) ^ 6)) from
          (Real.exp_log (by positivity)).symm]
    calc Real.exp (Real.log (((Nat.factorial 12 : ℝ)) ^ 6)) ≤ Real.exp 174 :=
          Real.exp_le_exp.mpr hlog6
      _ ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr (by linarith [hlogM260])
      _ = M := Real.exp_log hMpos
  have hσlo12 : 1 - 1 / (2 : ℝ) ^ (12 + 2) ≤ σ := by
    have he : (1 : ℝ) / (2 : ℝ) ^ (12 + 2) = 1 / (2 : ℝ) ^ 14 := by norm_num
    rw [he]; linarith [hσlo, hΘ14]
  have hguard : t ≤ (M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ)) := by
    have hfac11 : ((12 - 1).factorial : ℝ) ≤ 2 ^ 26 := by norm_num [Nat.factorial]
    have hfac11pos : (0 : ℝ) < ((12 - 1).factorial : ℝ) := by positivity
    have hlog2le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hlog11 : Real.log ((12 - 1).factorial : ℝ) ≤ 26 := by
      calc Real.log ((12 - 1).factorial : ℝ) ≤ Real.log ((2 : ℝ) ^ 26) :=
            Real.log_le_log hfac11pos hfac11
        _ = 26 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
        _ ≤ 26 := by nlinarith [hlog2le1]
    have hRHSpos : (0 : ℝ) < (M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ)) :=
      div_pos (Real.rpow_pos_of_pos hMpos _) hfac11pos
    have hlogRHS : Real.log ((M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ)))
        = (((12 : ℕ) : ℝ) - 1) * Real.log M - Real.log ((12 - 1).factorial : ℝ) := by
      rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hMpos _)) (ne_of_gt hfac11pos),
        Real.log_rpow hMpos]
    have hle : Real.log t
        ≤ Real.log ((M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ))) := by
      rw [hlogRHS]
      have h11 : ((12 : ℕ) : ℝ) - 1 = 11 := by norm_num
      rw [h11]; linarith [hhi, hlog11, hlogM260]
    have hexp := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log ht0, Real.exp_log hRHSpos] at hexp
  exact zeta_block_dispatch_twist 12 (by norm_num) σ t β hσlo12 ht1 M x' hMfac hMx'
    hx'2 hMt2 hguard

end Salt.Vk
