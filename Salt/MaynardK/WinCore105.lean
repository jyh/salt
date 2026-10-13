/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Frontier105
import Salt.MaynardK.QBridge
import Salt.MaynardK.CollisionS1
import Salt.MaynardK.PigeonholeK
import Salt.Twelve.WinCore
import Salt.Twelve.GapsUncond

open Finset Filter Topology

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard Salt.Twelve Salt.MaynardK

/-!
# B4.5b — the sieve inequality at k = 105 and the frontier-conditional capstone (C1)

* `S1_lt_sum_S2mW_k`, `sharp_S1_upperM_k`: `Salt/Twelve/WinCore.lean`'s and
  `Salt/Twelve/GapsFinal.lean`'s k = 5 lemmas at general `k` (its `k = 5` instance is checked in
`Controls`).
* `deltaPi_upper_ev_105`: Chebyshev `Δπ ≤ 1000·N'/log N'` with `h_max ≤ 743` (the hypothesis `hle`).
* `qdiag_err_split_gen` / `qdiag_err_split_105`: `|Qdiag − X^(n+2)·J| ≤ (c/log R + A/√D)·X^(n+2)`,
  `A` before `∀ W'`, from `qdiag_bridge_gen`.
* `sharp_S1_upper_105`, `win_core_105`: the sharp `S₁` bound and `S₁ < Σ_m S₂ᵂ⁽ᵐ⁾` for
  `yFg R W' F1`, the slack hypothesis being conjunct 7 of `WinFrontierMW105`.
* `gaps_le_of_frontier105`: `WinFrontierMW105 D` gives gaps `≤ d` for a tuple of diameter `≤ d`
  (`hdiam`), through `bounded_gaps_reduces_diam 105 … d hdiam`.

Maynard's proof of Theorem 1.3 (arXiv:1311.4600v3, p. 3; Prop. 4.2 and Prop. 4.3(2),
`M₁₀₅ > 4`) run at k = 105. The module is generic in the tuple (`TupleChoice`): the `105`-entries
are assumed `≤ 743` (`hle`) and the diameter `≤ d` (`hdiam`); `Gaps636` instantiates it at the
standard tuple (the first 105 primes greater than 105, diameter 636).
Nothing here bears on twin primes.
-/

theorem S1_lt_sum_S2mW_k (k K₀ N R ν₀ W' : ℕ) (y : (Fin k → ℕ) → ℝ)
    (δ : ℝ) (errEH cval : Fin k → ℝ)
    (hφ : 0 < (Nat.totient W' : ℝ)) (hcval : ∀ m : Fin k, 0 ≤ cval m) (hδ0 : 0 ≤ δ)
    (hDpi : ∀ m : Fin k, δ ≤ deltaPi k K₀ N m)
    (hcompat : ∀ m : Fin k, cval m ≤ Qdiag_mW k R W' m y)
    (hEHres : ∀ m : Fin k,
      deltaPi k K₀ N m / (Nat.totient W' : ℝ) * Qdiag_mW k R W' m y - errEH m
        ≤ S2mW k K₀ N R ν₀ W' m y)
    (hnum : S1 k K₀ N R W' ν₀ y
      < (∑ m : Fin k, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin k, errEH m) :
    S1 k K₀ N R W' ν₀ y < ∑ m : Fin k, S2mW k K₀ N R ν₀ W' m y := by
  have hlow : ∀ m : Fin k,
      δ / (Nat.totient W' : ℝ) * cval m - errEH m ≤ S2mW k K₀ N R ν₀ W' m y := by
    intro m
    refine le_trans ?_ (hEHres m)
    have hDpinn : 0 ≤ deltaPi k K₀ N m := le_trans hδ0 (hDpi m)
    have hdiv : δ / (Nat.totient W' : ℝ) ≤ deltaPi k K₀ N m / (Nat.totient W' : ℝ) := by
      gcongr; exact hDpi m
    have hmain : δ / (Nat.totient W' : ℝ) * cval m
        ≤ deltaPi k K₀ N m / (Nat.totient W' : ℝ) * Qdiag_mW k R W' m y :=
      mul_le_mul hdiv (hcompat m) (hcval m) (div_nonneg hDpinn hφ.le)
    linarith
  calc S1 k K₀ N R W' ν₀ y
      < (∑ m : Fin k, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin k, errEH m := hnum
    _ = ∑ m : Fin k, (δ / (Nat.totient W' : ℝ) * cval m - errEH m) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ m : Fin k, S2mW k K₀ N R ν₀ W' m y := Finset.sum_le_sum (fun m _ => hlow m)

/-! ## (2) `deltaPi_upper_ev_105` — Chebyshev `Δπ ≤ 1000·N'/log N'` at `h_max = 743` -/

theorem deltaPi_upper_ev_105 (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743) :
    ∀ᶠ N' : ℕ in atTop, ∀ m : Fin 105,
      deltaPi 105 64 N' m ≤ 1000 * (N' : ℝ) / Real.log N' := by
  have hsqrt : Tendsto (fun N : ℕ => Real.log N / Real.sqrt N) atTop (𝓝 0) := by
    have h : (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) =
        (fun x : ℝ => Real.log x / Real.sqrt x) := by
      funext x; rw [Real.sqrt_eq_rpow]
    have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).tendsto_div_nhds_zero
    rw [h] at hlo
    exact hlo.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 743,
      hsqrt.eventually_lt_const (show (0:ℝ) < 1 by norm_num)] with N' hN743 hsq m
  have hh : hSeq 105 m ≤ 743 := hle m
  have hN743r : (743 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN743
  have hN1 : (1 : ℝ) < (N' : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N' : ℝ) := by linarith
  set L := Real.log (N' : ℝ) with hLdef
  have hL : 0 < L := Real.log_pos hN1
  set s := Real.sqrt (N' : ℝ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hN0
  have hss : s * s = (N' : ℝ) := Real.mul_self_sqrt hN0.le
  have hLs : L < s := by rw [div_lt_one hs0] at hsq; exact hsq
  have hsL : L * s ≤ (N' : ℝ) := by nlinarith only [hs0, hLs, hss]
  have hdmono : deltaPi 105 64 N' m ≤ (Nat.primeCounting (64 * N' + 743) : ℝ) := by
    rw [deltaPi, primesCount_one_zero_eq, primesCount_one_zero_eq]
    have h1 : (Nat.primeCounting (64 * N' + hSeq 105 m) : ℝ)
        ≤ (Nat.primeCounting (64 * N' + 743) : ℝ) := by
      exact_mod_cast primeCounting_mono (by omega)
    have h2 : (0:ℝ) ≤ (Nat.primeCounting (N' + hSeq 105 m) : ℝ) := Nat.cast_nonneg _
    linarith
  set x : ℝ := ((64 * N' + 743 : ℕ) : ℝ) with hxdef
  have hxN : x = 64 * (N':ℝ) + 743 := by rw [hxdef]; push_cast; ring
  have hx1 : (1 : ℝ) < x := by rw [hxN]; linarith only [hN743r]
  have hx0 : 0 < x := by linarith
  have hcheb := Chebyshev.pi_le_log4_mul_div hx1
  rw [Nat.floor_natCast] at hcheb
  have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  have hlogxL : L ≤ Real.log x := by
    rw [hLdef]; exact Real.log_le_log hN0 (by rw [hxN]; linarith)
  have hlogx0 : 0 < Real.log x := lt_of_lt_of_le hL hlogxL
  have hlogsqrt_pos : 0 < Real.log (Real.sqrt x) := by rw [hlogsqrt]; linarith
  have hlogsqrt_ge : L / 2 ≤ Real.log (Real.sqrt x) := by rw [hlogsqrt]; linarith
  have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4 : Real.log 4 < 1.4 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    rw [he]; linarith
  have hxle : x ≤ 65 * (N':ℝ) := by rw [hxN]; linarith
  have hterm1 : Real.log 4 * x / Real.log (Real.sqrt x) ≤ 182 * (N':ℝ) / L := by
    have h_a : Real.log 4 * x ≤ 91 * (N':ℝ) := by
      linarith only [hxle, hN743r,
          mul_le_mul_of_nonneg_right (le_of_lt hlog4) hx0.le]
    rw [div_le_div_iff₀ hlogsqrt_pos hL]
    linarith only [mul_le_mul_of_nonneg_left hlogsqrt_ge
        (show (0 : ℝ) ≤ 182 * (N' : ℝ) by positivity), mul_le_mul_of_nonneg_right h_a hL.le]
  have hsqrtx : Real.sqrt x ≤ 9 * s := by
    have h81 : x ≤ 81 * (N':ℝ) := by rw [hxN]; linarith
    calc Real.sqrt x ≤ Real.sqrt (81 * (N':ℝ)) := Real.sqrt_le_sqrt h81
      _ = 9 * s := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 81), show (81:ℝ) = 9^2 by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9)]
  have hsN : s ≤ (N':ℝ) / L := by rw [le_div_iff₀ hL]; linarith only [hsL]
  have hterm2 : Real.sqrt x ≤ 9 * (N':ℝ) / L := by
    calc Real.sqrt x ≤ 9 * s := hsqrtx
      _ ≤ 9 * ((N':ℝ)/L) := by linarith [hsN]
      _ = 9 * (N':ℝ) / L := by ring
  calc deltaPi 105 64 N' m ≤ (Nat.primeCounting (64 * N' + 743) : ℝ) := hdmono
    _ ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x := hcheb
    _ ≤ 182 * (N':ℝ) / L + 9 * (N':ℝ) / L := add_le_add hterm1 hterm2
    _ ≤ 1000 * (N':ℝ) / L := by
        rw [← add_div, div_le_div_iff₀ hL hL]; nlinarith only [hL, (Nat.cast_nonneg _ : 0 ≤ ↑N')]

/-! ## (3) `qdiag_err_split_gen` — the tight `Qdiag` bound at general `n` -/

private lemma wc105_log_ge_of_ceil_exp (Lc : ℝ) (R : ℕ) (hR : ⌈Real.exp Lc⌉₊ ≤ R) :
    Lc ≤ Real.log R := by
  have hpos : (0 : ℝ) < Real.exp Lc := Real.exp_pos Lc
  have h1 : Real.exp Lc ≤ (⌈Real.exp Lc⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈Real.exp Lc⌉₊ : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  calc Lc = Real.log (Real.exp Lc) := (Real.log_exp Lc).symm
    _ ≤ Real.log R := Real.log_le_log hpos (le_trans h1 h2)

theorem qdiag_err_split_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hy1 : ∀ R W' : ℕ, ∀ s, |yFg R W' P s| ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → 12 * (n + 1) ^ 2 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ (c : ℝ) (R₀ : ℕ), 0 ≤ c ∧ ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW (n + 1) R W' m (yFg R W' P)
            - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
                * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
          ≤ (c / Real.log R + A / Real.sqrt D)
                * ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) := by
  obtain ⟨A, hA0, hbridge⟩ := qdiag_bridge_gen n hn P m hy1
  set J : ℝ := ((simplexInt (sq (contractB m P)) : ℚ) : ℝ) with hJdef
  refine ⟨30 * 6 ^ (n + 2) * A, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hDk hDlt hκ
  have hn1sq : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hDpos : 0 < D := by omega
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hDne : (D : ℝ) ≠ 0 := hDR.ne'
  have hsqD : Real.sqrt D * Real.sqrt D = (D : ℝ) := Real.mul_self_sqrt hDR.le
  have hsqDnn : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsqDpos : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hDR
  have hsqDne : Real.sqrt D ≠ 0 := hsqDpos.ne'
  have hsqD_ge1 : (1 : ℝ) ≤ Real.sqrt D := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ D))
  have hsqD_le_D : Real.sqrt D ≤ (D : ℝ) := by nlinarith only [hsqDnn, hsqD_ge1, hsqD]
  have hsqrtD_div : Real.sqrt D / (D:ℝ) = 1 / Real.sqrt D := by
    rw [div_eq_div_iff hDne hsqDne]; rw [one_mul, hsqD]
  obtain ⟨c, hc0, hb⟩ := hbridge W' D hW' hpos hUpper hDk hDlt
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  set κinv : ℝ := (W' : ℝ) / W'.totient with hκinvdef
  have htotpos : 0 < W'.totient := Nat.totient_pos.mpr hpos
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast htotpos) (by exact_mod_cast hpos)
  have hκinv_pos : 0 < κinv := by
    rw [hκinvdef]; exact div_pos (by exact_mod_cast hpos) (by exact_mod_cast htotpos)
  obtain ⟨Cpas, hpas⟩ := phiAtom_upper_lossy W' hpos.ne'
  rw [← hκdef] at hpas
  set Lc : ℝ := max ((1 + Cpas) / κ) (1 / κ) with hLcdef
  refine ⟨2 ^ (n + 2) * c, max 2 ⌈Real.exp Lc⌉₊, by positivity, ?_⟩
  intro R hR hlogR
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  set X : ℝ := κ * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le one_pos hlogR
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hlogRpos
  have hLlogR : Lc ≤ Real.log R :=
    wc105_log_ge_of_ceil_exp Lc R (le_trans (le_max_right _ _) hR)
  have h1Cpas : 1 + Cpas ≤ X := by
    have hle : (1 + Cpas) / κ ≤ Real.log R :=
      le_trans (le_trans (le_max_left _ _) (le_of_eq hLcdef.symm)) hLlogR
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  have h1X : (1 : ℝ) ≤ X := by
    have hle : (1 : ℝ) / κ ≤ Real.log R :=
      le_trans (le_trans (le_max_right _ _) (le_of_eq hLcdef.symm)) hLlogR
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  have hpasR : PAS ≤ 4 * X + Cpas := by
    have h := hpas R hR2; rw [← hXdef, ← hPASdef] at h; linarith [h]
  have hPASnn : 0 ≤ PAS := by
    rw [hPASdef]; unfold Salt.Maynard.phiAtomSum
    exact Finset.sum_nonneg fun r _ => by positivity
  have hb2 := hb R hR2 hlogR
  rw [← hPASdef, ← hXdef] at hb2
  -- atomise every power base
  have hYnn : (0 : ℝ) ≤ 1 + X + PAS := by linarith
  have hY6X : 1 + X + PAS ≤ 6 * X := by linarith [hpasR, h1Cpas]
  have h1Xnn : (0 : ℝ) ≤ 1 + X := by linarith
  have h1X2X : 1 + X ≤ 2 * X := by linarith
  generalize hYdef : 1 + X + PAS = Y at hYnn hY6X hb2
  generalize hZdef : 1 + X = Z at h1Xnn h1X2X hb2
  have hXp_nn : 0 ≤ X ^ (n + 2) := (pow_pos hXpos (n + 2)).le
  have hY6 : Y ^ (n + 2) ≤ 6 ^ (n + 2) * X ^ (n + 2) := by
    calc Y ^ (n + 2) ≤ (6 * X) ^ (n + 2) := pow_le_pow_left₀ hYnn hY6X (n + 2)
      _ = 6 ^ (n + 2) * X ^ (n + 2) := by rw [mul_pow]
  have hZ2 : Z ^ (n + 2) ≤ 2 ^ (n + 2) * X ^ (n + 2) := by
    calc Z ^ (n + 2) ≤ (2 * X) ^ (n + 2) := pow_le_pow_left₀ h1Xnn h1X2X (n + 2)
      _ = 2 ^ (n + 2) * X ^ (n + 2) := by rw [mul_pow]
  generalize hXpdef : X ^ (n + 2) = Xp at hXp_nn hY6 hZ2 hb2 ⊢
  generalize hYpdef : Y ^ (n + 2) = Yp at hY6 hb2
  generalize hZpdef : Z ^ (n + 2) = Zp at hZ2 hb2
  generalize hS6 : (6 : ℝ) ^ (n + 2) = S6 at hY6 ⊢
  generalize hT2 : (2 : ℝ) ^ (n + 2) = T2 at hZ2 ⊢
  have hS6nn : 0 ≤ S6 := by rw [← hS6]; positivity
  have hT2nn : 0 ≤ T2 := by rw [← hT2]; positivity
  have hκinv2 : κinv ^ 2 ≤ 25 * (D : ℝ) := by
    have hfac : (0 : ℝ) ≤ (5 * Real.sqrt D - κinv) * (5 * Real.sqrt D + κinv) :=
      mul_nonneg (sub_nonneg.mpr hκ) (by linarith [hsqDnn, hκinv_pos.le])
    linarith only [hfac, hsqD]
  have hterm1 : c * Zp / Real.log R ≤ (T2 * c / Real.log R) * Xp := by
    have hnum : c * Zp ≤ T2 * c * Xp := by
      calc c * Zp ≤ c * (T2 * Xp) := mul_le_mul_of_nonneg_left hZ2 hc0
        _ = T2 * c * Xp := by ring
    have heq : (T2 * c / Real.log R) * Xp = T2 * c * Xp / Real.log R := by ring
    rw [heq]; exact div_le_div_of_nonneg_right hnum hlogRpos.le
  have hterm2 : A * κinv * Yp / (D : ℝ)
      ≤ (5 * S6 * A / Real.sqrt D) * Xp := by
    have hc1 : A * κinv * Yp ≤ A * (5 * Real.sqrt D) * (S6 * Xp) := by
      calc A * κinv * Yp ≤ A * κinv * (S6 * Xp) :=
            mul_le_mul_of_nonneg_left hY6 (mul_nonneg hA0 hκinv_pos.le)
        _ ≤ A * (5 * Real.sqrt D) * (S6 * Xp) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ hA0)
              (mul_nonneg hS6nn hXp_nn)
    have hDeq2 : A * (5 * Real.sqrt D) * (S6 * Xp) / (D:ℝ)
        = (5 * S6 * A / Real.sqrt D) * Xp := by
      rw [show A * (5 * Real.sqrt D) * (S6 * Xp) / (D:ℝ)
          = (5 * S6 * A * Xp) * (Real.sqrt D / (D:ℝ)) by ring, hsqrtD_div]; ring
    calc A * κinv * Yp / (D : ℝ)
        ≤ A * (5 * Real.sqrt D) * (S6 * Xp) / (D:ℝ) :=
          div_le_div_of_nonneg_right hc1 hDR.le
      _ = (5 * S6 * A / Real.sqrt D) * Xp := hDeq2
  have hterm3 : A * κinv ^ 2 * Yp / (D : ℝ) ^ 2
      ≤ (25 * S6 * A / Real.sqrt D) * Xp := by
    have hc1 : A * κinv ^ 2 * Yp ≤ A * (25 * (D:ℝ)) * (S6 * Xp) := by
      calc A * κinv ^ 2 * Yp ≤ A * κinv ^ 2 * (S6 * Xp) :=
            mul_le_mul_of_nonneg_left hY6 (mul_nonneg hA0 (sq_nonneg _))
        _ ≤ A * (25 * (D:ℝ)) * (S6 * Xp) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκinv2 hA0)
              (mul_nonneg hS6nn hXp_nn)
    have hDeq3 : A * (25 * (D:ℝ)) * (S6 * Xp) / (D:ℝ)^2
        = (25 * S6 * A / (D:ℝ)) * Xp := by field_simp
    have hDsqrt : (25 * S6 * A / (D:ℝ)) * Xp
        ≤ (25 * S6 * A / Real.sqrt D) * Xp := by
      apply mul_le_mul_of_nonneg_right _ hXp_nn
      exact div_le_div_of_nonneg_left (by positivity) hsqDpos hsqD_le_D
    calc A * κinv ^ 2 * Yp / (D : ℝ) ^ 2
        ≤ A * (25 * (D:ℝ)) * (S6 * Xp) / (D:ℝ)^2 :=
          div_le_div_of_nonneg_right hc1 (by positivity)
      _ = (25 * S6 * A / (D:ℝ)) * Xp := hDeq3
      _ ≤ (25 * S6 * A / Real.sqrt D) * Xp := hDsqrt
  have hcollect : ((T2 * c) / Real.log R + (30 * S6 * A) / Real.sqrt D) * Xp
      = (T2 * c / Real.log R) * Xp
        + ((5 * S6 * A / Real.sqrt D) * Xp + (25 * S6 * A / Real.sqrt D) * Xp) := by
    ring
  refine le_trans hb2 ?_
  rw [hcollect]
  linarith [hterm1, hterm2, hterm3]

/-- **`qdiag_err_split_105`** — the `n = 104`, `P = F1` instance. -/
theorem qdiag_err_split_105 (m : Fin 105) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → 12 * 105 ^ 2 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ (c : ℝ) (R₀ : ℕ), 0 ≤ c ∧ ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 105 R W' m (yFg R W' F1)
            - ((W'.totient : ℝ) / W' * Real.log R) ^ 106
                * ((simplexInt (sq (contractB m F1)) : ℚ) : ℝ)|
          ≤ (c / Real.log R + A / Real.sqrt D)
                * ((W'.totient : ℝ) / W' * Real.log R) ^ 106 :=
  qdiag_err_split_gen 104 (by norm_num) F1 m (fun R W' s => yFg_F1_abs_le_one R W' s)

/-! ## (4) `sharp_S1_upper_105` — the M-based sharp `S1` upper bound -/

theorem sharp_S1_upperM_k (k N R W' ν₀ D : ℕ) (hk : 1 ≤ k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ r, |y r| ≤ 1) (hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin k, hSeq k i < D)
    (hDk : 12 * k ^ 2 ≤ D)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    S1 k 64 N R W' ν₀ y
      ≤ ((64 - 1) * N / W' : ℝ)
          * ((∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (k : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by
  have hL2 := S1_le_main_add_errorW k 64 N R W' ν₀ D y hW' (by norm_num) hDlt hlt hsol
  have hcompat_eq := s1_compat_eq k R W' y hy0
  have hcoll := collision_y_M k R W' D y hk hy1 hy0 hDlt hDk
  set yside := ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
    with hys
  set M := ∑ r ∈ kSieveIndex k R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) with hM
  have hcoeff : (0 : ℝ) ≤ ((64 - 1) * N / W' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (64 : ℝ) - 1 := by norm_num
    exact div_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  have hcompat_le : s1CompatForm k R W' y ≤ yside + 12 * (k : ℝ) ^ 2 / D * M := by
    rw [hcompat_eq]
    have h1 : - s1CollisionForm k R W' y ≤ |s1CollisionForm k R W' y| := neg_le_abs _
    linarith [hcoll, h1]
  calc S1 k 64 N R W' ν₀ y
      ≤ ((64 - 1) * N / W' : ℝ) * s1CompatForm k R W' y
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL2
    _ ≤ ((64 - 1) * N / W' : ℝ) * (yside + 12 * (k : ℝ) ^ 2 / D * M)
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hcompat_le hcoeff) (le_refl _)

private lemma wc105_yFg_F1_zero (R W' : ℕ) (r : Fin 105 → ℕ)
        (hr : r ∉ kSieveIndex 105 R W') :
    yFg R W' F1 r = 0 := by
  unfold yFg; exact if_neg hr

theorem sharp_S1_upper_105 (N R W' ν₀ D : ℕ)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin 105, hSeq 105 i < D)
    (hDk : 12 * 105 ^ 2 ≤ D)
    (hsol : ∀ d ∈ kSieveIndex 105 R W', ∀ e ∈ kSieveIndex 105 R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 105 i)) :
    S1 105 64 N R W' ν₀ (yFg R W' F1)
      ≤ ((64 - 1) * N / W' : ℝ)
          * ((∑ r ∈ kSieveIndex 105 R W', (yFg R W' F1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (105 : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex 105 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (105 + 1) * (∑ d ∈ kSieveIndex 105 R W', |lam 105 R W' (yFg R W' F1) d|) ^ 2 := by
  have h := sharp_S1_upperM_k 105 N R W' ν₀ D (by norm_num) (yFg R W' F1)
    (fun r => yFg_F1_abs_le_one R W' r) (wc105_yFg_F1_zero R W') hW' hDlt hlt hDk hsol
  simp only [Nat.cast_ofNat] at h
  exact h

/-! ## (5) `win_core_105` — the sieve inequality `S₁ < Σ_m S₂ᵂ⁽ᵐ⁾` at k = 105 -/

theorem win_core_105 (N' R ν₀ W' D : ℕ) (δ : ℝ) (errEH cval : Fin 105 → ℝ)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin 105, hSeq 105 i < D)
    (hDk : 12 * 105 ^ 2 ≤ D)
    (hsol : ∀ d ∈ kSieveIndex 105 R W', ∀ e ∈ kSieveIndex 105 R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 105 i))
    (hφpos : 0 < (Nat.totient W' : ℝ)) (hcval : ∀ m : Fin 105, 0 ≤ cval m) (hδ0 : 0 ≤ δ)
    (hDpi : ∀ m : Fin 105, δ ≤ deltaPi 105 64 N' m)
    (hQlow : ∀ m : Fin 105, cval m ≤ Qdiag_mW 105 R W' m (yFg R W' F1))
    (hS2low : ∀ m : Fin 105,
      deltaPi 105 64 N' m / (Nat.totient W' : ℝ) * Qdiag_mW 105 R W' m (yFg R W' F1) - errEH m
        ≤ S2mW 105 64 N' R ν₀ W' m (yFg R W' F1))
    (hslack :
      ((64 - 1) * N' / W' : ℝ)
          * ((∑ r ∈ kSieveIndex 105 R W',
                  (yFg R W' F1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (105 : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex 105 R W',
                      1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (105 + 1)
            * (∑ d ∈ kSieveIndex 105 R W',
                |lam 105 R W' (yFg R W' F1) d|) ^ 2
        < (∑ m : Fin 105,
              δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 105, errEH m) :
    S1 105 64 N' R W' ν₀ (yFg R W' F1)
      < ∑ m : Fin 105, S2mW 105 64 N' R ν₀ W' m (yFg R W' F1) := by
  have hS1sharp := sharp_S1_upper_105 N' R W' ν₀ D hW' hDlt hlt hDk hsol
  have hnum : S1 105 64 N' R W' ν₀ (yFg R W' F1)
      < (∑ m : Fin 105, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 105, errEH m :=
    lt_of_le_of_lt hS1sharp hslack
  exact S1_lt_sum_S2mW_k 105 64 N' R ν₀ W' (yFg R W' F1) δ errEH cval hφpos hcval hδ0 hDpi
    hQlow hS2low hnum

/-! ## (6) `gaps_le_of_frontier105` — the frontier-conditional capstone, at any tuple of diameter `≤ d` -/

theorem gaps_le_of_frontier105 (D : ℕ) (hD : 744 ≤ D) (hDk : 12 * 105 ^ 2 ≤ D)
    (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743) (d : ℤ)
    (hdiam : ∀ i j : Fin 105, (hSeq 105 j : ℤ) - (hSeq 105 i : ℤ) ∈ Set.Icc (-d) d)
    (hPNT : WindowPNT) (hLoD : HasLevel (1 / 2)) (hF : WinFrontierMW105 D) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-d) d := by
  refine bounded_gaps_reduces_diam 105 (primorial D) d hdiam (fun N => ?_)
  obtain ⟨N', R, ν₀, δ, errEH, cval, hNN', hsol, hφpos, hcvnn, hδ0, hDpi, hQlow,
    hS2low, hslack⟩ := hF hPNT hLoD N
  refine ⟨N', R, ν₀, yFg R (primorial D) F1, hNN', ?_⟩
  exact win_core_105 N' R ν₀ (primorial D) D δ errEH cval
    (primorial_sqf' D) (primorial_hDlt D) (fun i => by have := hle i; omega)
    hDk hsol hφpos hcvnn hδ0 hDpi hQlow hS2low hslack

end Salt.MaynardK

