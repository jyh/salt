/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.FrontierM
import Salt.Twelve.QdiagFloor
import Salt.Twelve.YsideCM
import Salt.Twelve.MvSplit
import Salt.Twelve.QdiagBridge
import Salt.Maynard.ChebyshevInterval
import Salt.Maynard.Endgame
import Salt.Maynard.Final
import Salt.Maynard.EHLevelTheta
import Salt.Maynard.FrontierDischarge

/-!
# R2b + R2c — the unconditional closure of the `explicit12` rung

Design: `docs/blueprints/explicit12-design.md`, cards NC-3 / R2b / R2c; the W5-7
flag in `docs/blueprints/flags.md`.

* **R2b** (`winSlackM_ev`) discharges the conjunct-7 slack `WinSlackM D C₀ N'`
  eventually in `N'`, for all `D` above an explicit (∃, F-only) cutoff `D₀`.
* **R2c** (`gaps_le_twelve` — THE frozen capstone name) feeds `winSlackM_ev` through
  `winFrontierMW_of` (R2a) and mirrors `gaps_le_twelve_of_frontierM` at
  `(D₀, primorial D₀)`, yielding the unconditional explicit bounded-gaps theorem.

The slack anatomy (all at FIXED `(D, W' = primorial D)`, `N' → ∞`,
`R = ⌊N'^{1999/4000}⌋₊`, `X = (φW'/W')·log R`):

* RHS main `∑_m (δ/φW')·Qdiag` bounded below by `(δ/φW')·X⁶·SJ` up to the qdiag
  error `(c/logR + A/√D)·X⁶` per `m` (`qdiag_err_split`, from `qdiag_bridge`);
* LHS main `(63N'/W')·yside` and the `(300/D)·M` term bounded above via
  `mv_I_split` at `Fstar1` and `onePoly`;
* the certified ratio `63·N'·Ic·(1+eps) < δ·log R·SJ` (`win_ratio_core` +
  `theta_ratio_cert_sharp`), with `eps ≤ 1/100000` assembled from the vanishing
  budget;
* the S₂ collision `Δπ/φW'·(Qdiag − s2CompatFormM)` bounded via
  `s2_collision_floor` and the Chebyshev `Δπ ≤ 1000·N'/log N'` (`deltaPi_upper_ev`);
* the `herr` and S₁-truncation `2⁶(∑|λ|)²` pieces vanish against the main.
-/

open Finset Filter Topology

namespace Salt.Twelve

open Salt.Maynard

/-! ## Local numeric helper -/

private lemma hSeq_le_nineteen' (i : Fin 5) : hSeq 5 i ≤ 19 := by
  fin_cases i <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

private lemma log_ge_of_ceil_exp' (Lc : ℝ) (R : ℕ) (hR : ⌈Real.exp Lc⌉₊ ≤ R) :
    Lc ≤ Real.log R := by
  have hpos : (0 : ℝ) < Real.exp Lc := Real.exp_pos Lc
  have h1 : Real.exp Lc ≤ (⌈Real.exp Lc⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈Real.exp Lc⌉₊ : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  calc Lc = Real.log (Real.exp Lc) := (Real.log_exp Lc).symm
    _ ≤ Real.log R := Real.log_le_log hpos (le_trans h1 h2)

/-! ## The Chebyshev `Δπ` upper bound -/

/-- **Chebyshev `Δπ` upper bound.**  Eventually in `N'`, `deltaPi 5 64 N' m ≤
1000·N'/log N'`, uniformly in `m`.  From `Δπ ≤ π(64N'+19)` and mathlib's
`Chebyshev.pi_le_log4_mul_div`. -/
theorem deltaPi_upper_ev :
    ∀ᶠ N' : ℕ in atTop, ∀ m : Fin 5,
      deltaPi 5 64 N' m ≤ 1000 * (N' : ℝ) / Real.log N' := by
  have hsqrt : Tendsto (fun N : ℕ => Real.log N / Real.sqrt N) atTop (𝓝 0) := by
    have h : (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) =
        (fun x : ℝ => Real.log x / Real.sqrt x) := by
      funext x; rw [Real.sqrt_eq_rpow]
    have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).tendsto_div_nhds_zero
    rw [h] at hlo
    exact hlo.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 100,
      hsqrt.eventually_lt_const (show (0:ℝ) < 1 by norm_num)] with N' hN100 hsq m
  have hh19 : hSeq 5 m ≤ 19 := hSeq_le_nineteen' m
  have hN100r : (100 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN100
  have hN1 : (1 : ℝ) < (N' : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N' : ℝ) := by linarith
  set L := Real.log (N' : ℝ) with hLdef
  have hL : 0 < L := Real.log_pos hN1
  set s := Real.sqrt (N' : ℝ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hN0
  have hss : s * s = (N' : ℝ) := Real.mul_self_sqrt hN0.le
  have hLs : L < s := by rw [div_lt_one hs0] at hsq; exact hsq
  have hsL : L * s ≤ (N' : ℝ) := by nlinarith [hLs, hs0, hL]
  have hdmono : deltaPi 5 64 N' m ≤ (Nat.primeCounting (64 * N' + 19) : ℝ) := by
    rw [deltaPi, primesCount_one_zero_eq, primesCount_one_zero_eq]
    have h1 : (Nat.primeCounting (64 * N' + hSeq 5 m) : ℝ)
        ≤ (Nat.primeCounting (64 * N' + 19) : ℝ) := by
      exact_mod_cast primeCounting_mono (by omega)
    have h2 : (0:ℝ) ≤ (Nat.primeCounting (N' + hSeq 5 m) : ℝ) := by positivity
    linarith
  set x : ℝ := ((64 * N' + 19 : ℕ) : ℝ) with hxdef
  have hxN : x = 64 * (N':ℝ) + 19 := by rw [hxdef]; push_cast; ring
  have hx1 : (1 : ℝ) < x := by rw [hxN]; nlinarith
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
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hlog4) hx0.le,
        mul_le_mul_of_nonneg_left hxle (show (0:ℝ) ≤ 1.4 by norm_num)]
    rw [div_le_div_iff₀ hlogsqrt_pos hL]
    nlinarith [mul_le_mul_of_nonneg_right h_a hL.le,
      mul_le_mul_of_nonneg_left hlogsqrt_ge (show (0:ℝ) ≤ 182 * (N':ℝ) by positivity)]
  have hsqrtx : Real.sqrt x ≤ 9 * s := by
    have h81 : x ≤ 81 * (N':ℝ) := by rw [hxN]; linarith
    calc Real.sqrt x ≤ Real.sqrt (81 * (N':ℝ)) := Real.sqrt_le_sqrt h81
      _ = 9 * s := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 81), show (81:ℝ) = 9^2 by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9)]
  have hsN : s ≤ (N':ℝ) / L := by rw [le_div_iff₀ hL]; nlinarith [hsL]
  have hterm2 : Real.sqrt x ≤ 9 * (N':ℝ) / L := by
    calc Real.sqrt x ≤ 9 * s := hsqrtx
      _ ≤ 9 * ((N':ℝ)/L) := by linarith [hsN]
      _ = 9 * (N':ℝ) / L := by ring
  calc deltaPi 5 64 N' m ≤ (Nat.primeCounting (64 * N' + 19) : ℝ) := hdmono
    _ ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x := hcheb
    _ ≤ 182 * (N':ℝ) / L + 9 * (N':ℝ) / L := add_le_add hterm1 hterm2
    _ ≤ 1000 * (N':ℝ) / L := by
        rw [← add_div, div_le_div_iff₀ hL hL]; nlinarith [hN0.le, hL.le]

/-! ## The tight `Qdiag` lower bound (error `(c/log R + A/√D)·X⁶`) -/

/-- **Tight `Qdiag` bound.**  `|Qdiag − X⁶·J_m| ≤ (c/log R + A/√D)·X⁶`, with `A`
`F`-only (obtained before `W'`) and `c` per-`(W',D)`.  Adapts `qdiag_floor`'s
three-term error control from `qdiag_bridge`, exposing the two vanishing scales
`1/log R` (`N'`-threshold) and `1/√D` (`D`-threshold). -/
theorem qdiag_err_split (m : Fin 5) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → 300 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ (c : ℝ) (R₀ : ℕ), 0 ≤ c ∧ ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' Fstar1)
            - ((W'.totient : ℝ) / W' * Real.log R) ^ 6 * ((Jcal m Fstar1 : ℚ) : ℝ)|
          ≤ (c / Real.log R + A / Real.sqrt D)
                * ((W'.totient : ℝ) / W' * Real.log R) ^ 6 := by
  obtain ⟨A, hA0, hbridge⟩ := qdiag_bridge Fstar1 m (le_of_eq Qabs_Fstar1)
  set J : ℝ := ((Jcal m Fstar1 : ℚ) : ℝ) with hJdef
  refine ⟨30 * 6 ^ 6 * A, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD300 hDlt hκ
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
  have hsqD_le_D : Real.sqrt D ≤ (D : ℝ) := by nlinarith [hsqD, hsqD_ge1]
  have hsqrtD_div : Real.sqrt D / (D:ℝ) = 1 / Real.sqrt D := by
    rw [div_eq_div_iff hDne hsqDne]; rw [one_mul, hsqD]
  obtain ⟨c, hc0, hb⟩ := hbridge W' D hW' hpos hUpper hD300 hDlt
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
  refine ⟨64 * c, max 2 ⌈Real.exp Lc⌉₊, by positivity, ?_⟩
  intro R hR hlogR
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  set X : ℝ := κ * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le one_pos hlogR
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hlogRpos
  have hX6nn : 0 ≤ X ^ 6 := (pow_pos hXpos 6).le
  have hLlogR : Lc ≤ Real.log R := log_ge_of_ceil_exp' Lc R (le_trans (le_max_right _ _) hR)
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
  have hYnn : (0 : ℝ) ≤ 1 + X + PAS := by linarith
  have hY6X : 1 + X + PAS ≤ 6 * X := by linarith [hpasR, h1Cpas]
  have hY6 : (1 + X + PAS) ^ 6 ≤ 6 ^ 6 * X ^ 6 := by
    calc (1 + X + PAS) ^ 6 ≤ (6 * X) ^ 6 := pow_le_pow_left₀ hYnn hY6X 6
      _ = 6 ^ 6 * X ^ 6 := by rw [mul_pow]
  have h1X6 : (1 + X) ^ 6 ≤ 2 ^ 6 * X ^ 6 := by
    calc (1 + X) ^ 6 ≤ (2 * X) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = 2 ^ 6 * X ^ 6 := by rw [mul_pow]
  have hκinv2 : κinv ^ 2 ≤ 25 * (D : ℝ) := by
    have hfac : (0 : ℝ) ≤ (5 * Real.sqrt D - κinv) * (5 * Real.sqrt D + κinv) :=
      mul_nonneg (sub_nonneg.mpr hκ) (by linarith [hsqDnn, hκinv_pos.le])
    nlinarith [hfac, hsqD]
  have hterm1 : c * (1 + X) ^ 6 / Real.log R ≤ (64 * c / Real.log R) * X ^ 6 := by
    have hnum : c * (1 + X) ^ 6 ≤ 64 * c * X ^ 6 := by nlinarith [h1X6, hc0, hX6nn]
    have heq : (64 * c / Real.log R) * X ^ 6 = 64 * c * X ^ 6 / Real.log R := by ring
    rw [heq]; exact div_le_div_of_nonneg_right hnum hlogRpos.le
  have hterm2 : A * κinv * (1 + X + PAS) ^ 6 / (D : ℝ)
      ≤ (5 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6 := by
    have hc1 : A * κinv * (1 + X + PAS) ^ 6 ≤ A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6) := by
      calc A * κinv * (1 + X + PAS) ^ 6 ≤ A * κinv * (6 ^ 6 * X ^ 6) :=
            mul_le_mul_of_nonneg_left hY6 (mul_nonneg hA0 hκinv_pos.le)
        _ ≤ A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ hA0)
              (mul_nonneg (by norm_num) hX6nn)
    have hDeq2 : A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6) / (D:ℝ)
        = (5 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6 := by
      rw [show A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6) / (D:ℝ)
          = (5 * 6 ^ 6 * A * X ^ 6) * (Real.sqrt D / (D:ℝ)) by ring, hsqrtD_div]; ring
    calc A * κinv * (1 + X + PAS) ^ 6 / (D : ℝ)
        ≤ A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6) / (D:ℝ) :=
          div_le_div_of_nonneg_right hc1 hDR.le
      _ = (5 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6 := hDeq2
  have hterm3 : A * κinv ^ 2 * (1 + X + PAS) ^ 6 / (D : ℝ) ^ 2
      ≤ (25 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6 := by
    have hc1 : A * κinv ^ 2 * (1 + X + PAS) ^ 6 ≤ A * (25 * (D:ℝ)) * (6 ^ 6 * X ^ 6) := by
      calc A * κinv ^ 2 * (1 + X + PAS) ^ 6 ≤ A * κinv ^ 2 * (6 ^ 6 * X ^ 6) :=
            mul_le_mul_of_nonneg_left hY6 (mul_nonneg hA0 (sq_nonneg _))
        _ ≤ A * (25 * (D:ℝ)) * (6 ^ 6 * X ^ 6) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκinv2 hA0)
              (mul_nonneg (by norm_num) hX6nn)
    have hDeq3 : A * (25 * (D:ℝ)) * (6 ^ 6 * X ^ 6) / (D:ℝ)^2
        = (25 * 6 ^ 6 * A / (D:ℝ)) * X ^ 6 := by field_simp
    have hDsqrt : (25 * 6 ^ 6 * A / (D:ℝ)) * X ^ 6
        ≤ (25 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6 := by
      apply mul_le_mul_of_nonneg_right _ hX6nn
      exact div_le_div_of_nonneg_left (by positivity) hsqDpos hsqD_le_D
    calc A * κinv ^ 2 * (1 + X + PAS) ^ 6 / (D : ℝ) ^ 2
        ≤ A * (25 * (D:ℝ)) * (6 ^ 6 * X ^ 6) / (D:ℝ)^2 :=
          div_le_div_of_nonneg_right hc1 (by positivity)
      _ = (25 * 6 ^ 6 * A / (D:ℝ)) * X ^ 6 := hDeq3
      _ ≤ (25 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6 := hDsqrt
  have hb2 := hb R hR2 hlogR
  have htie : ((simplexInt (sq (contractAt m Fstar1)) : ℚ) : ℝ) = J := by
    rw [hJdef]; exact_mod_cast simplexInt_sq_contractAt_eq_Jcal m Fstar1
  rw [← hPASdef, ← hXdef, htie] at hb2
  have hcollect : ((64 * c) / Real.log R + (30 * 6 ^ 6 * A) / Real.sqrt D) * X ^ 6
      = (64 * c / Real.log R) * X ^ 6
        + ((5 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6 + (25 * 6 ^ 6 * A / Real.sqrt D) * X ^ 6) := by
    ring
  refine le_trans hb2 ?_
  rw [hcollect]
  linarith [hterm1, hterm2, hterm3]

/-! ## Vanishing-rate helpers (all at `R = ⌊N'^{1999/4000}⌋₊`) -/

private lemma eventually_logN_ge (M : ℝ) : ∀ᶠ N' : ℕ in atTop, M ≤ Real.log N' :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M

private lemma eventually_logR_ge (b : ℝ) :
    ∀ᶠ N' : ℕ in atTop, b ≤ Real.log (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) := by
  filter_upwards [eventually_logR_lower_theta (1/4) (by norm_num) (by norm_num),
    eventually_logN_ge (4 * b)] with N' h1 h2
  linarith

private lemma eventually_div_logR_le (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N' : ℕ in atTop,
      C / Real.log (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ≤ ε := by
  filter_upwards [eventually_logR_ge (max C 1 / ε), eventually_logR_ge 1] with N' hge hpos
  set L := Real.log (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  rw [div_le_iff₀ hLpos]
  have hCle : C ≤ max C 1 := le_max_left _ _
  have h2 : max C 1 / ε ≤ L := hge
  calc C ≤ max C 1 := hCle
    _ = (max C 1 / ε) * ε := by field_simp
    _ ≤ L * ε := mul_le_mul_of_nonneg_right h2 hε.le
    _ = ε * L := by ring

private lemma eventually_polylog_ratio_le (p q : ℕ) (A K : ℝ) (hpq : p < q)
    (hK : 0 < K) (hA : 0 ≤ A) :
    ∀ᶠ N' : ℕ in atTop,
      A * (1 + Real.log (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ)) ^ p / (Real.log N') ^ q
        ≤ K := by
  filter_upwards [eventually_logN_ge (max 1 (2 ^ p * A / K)), eventually_ge_atTop 8]
    with N' hlogN hN8
  have hlog1 : (1 : ℝ) ≤ Real.log N' := le_trans (le_max_left _ _) hlogN
  have hlogNpos : 0 < Real.log N' := by linarith
  have hN1 : (1:ℕ) < N' := by omega
  set R := ⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ with hRdef
  have hRleN : R ≤ N' := R_le_N'_theta N' (by omega)
  have hlogRle : Real.log R ≤ Real.log N' := by
    apply Real.log_le_log
    · have : 2 ≤ R := R_ge_two_theta N' (by exact_mod_cast hN8)
      exact_mod_cast (by omega : 0 < R)
    · exact_mod_cast hRleN
  have hlogRnn : 0 ≤ Real.log R := by
    have : 2 ≤ R := R_ge_two_theta N' (by exact_mod_cast hN8)
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  -- (1+logR)^p ≤ (2 logN')^p, and 2^p A/K ≤ logN'^{q-p}
  have hbase : 1 + Real.log R ≤ 2 * Real.log N' := by linarith
  have hbasenn : 0 ≤ 1 + Real.log R := by linarith
  have hpow : (1 + Real.log R) ^ p ≤ 2 ^ p * (Real.log N') ^ p := by
    calc (1 + Real.log R) ^ p ≤ (2 * Real.log N') ^ p :=
          pow_le_pow_left₀ hbasenn hbase p
      _ = 2 ^ p * (Real.log N') ^ p := by rw [mul_pow]
  have hqp : 1 ≤ q - p := by omega
  have hLqp : (Real.log N') ^ (q - p) ≥ Real.log N' := by
    calc Real.log N' = (Real.log N') ^ 1 := (pow_one _).symm
      _ ≤ (Real.log N') ^ (q - p) := pow_le_pow_right₀ hlog1 hqp
  have hThr : 2 ^ p * A / K ≤ Real.log N' := le_trans (le_max_right _ _) hlogN
  -- assemble
  rw [div_le_iff₀ (by positivity)]
  have hsplit : (Real.log N') ^ q = (Real.log N') ^ p * (Real.log N') ^ (q - p) := by
    rw [← pow_add]; congr 1; omega
  have hAle : A * (2 ^ p * (Real.log N') ^ p)
      ≤ K * ((Real.log N') ^ p * (Real.log N') ^ (q - p)) := by
    have h1 : A * 2 ^ p ≤ K * (Real.log N') ^ (q - p) := by
      have : A * 2 ^ p ≤ K * Real.log N' := by
        rw [mul_comm A (2^p)]
        have := (div_le_iff₀ hK).mp hThr
        nlinarith [this, hlog1]
      nlinarith [hLqp, hK.le, this]
    nlinarith [h1, pow_nonneg hlogNpos.le p]
  calc A * (1 + Real.log R) ^ p
      ≤ A * (2 ^ p * (Real.log N') ^ p) := mul_le_mul_of_nonneg_left hpow hA
    _ ≤ K * ((Real.log N') ^ p * (Real.log N') ^ (q - p)) := hAle
    _ = K * (Real.log N') ^ q := by rw [← hsplit]

private lemma eventually_poly_o_linear (n : ℕ) (K C : ℝ) (hK : 0 < K) (hC : 0 ≤ C) :
    ∀ᶠ N' : ℕ in atTop,
      C * (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) ^ 2
          * (1 + Real.log (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ)) ^ n
        ≤ K * (N':ℝ) := by
  have hev := eventually_poly_beats_polylog n (1 / 2000) (C / K) (by norm_num)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN, eventually_ge_atTop 8] with N' hpoly hN8
  set R := ⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ with hRdef
  have hN1 : (1:ℝ) < (N':ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hNpos : (0:ℝ) < (N':ℝ) := by linarith
  have hlogN : 0 < Real.log N' := Real.log_pos hN1
  have hR2n : 2 ≤ R := R_ge_two_theta N' (by exact_mod_cast hN8)
  have hRleN : R ≤ N' := R_le_N'_theta N' (by omega)
  have hRsq : (R:ℝ) ^ 2 ≤ (N':ℝ) ^ (3998 / 4000 : ℝ) := R_sq_le_theta N' (by omega)
  have hlogRle : Real.log R ≤ Real.log N' :=
    Real.log_le_log (by exact_mod_cast (by omega : (0:ℕ) < R)) (by exact_mod_cast hRleN)
  have hlogRnn : 0 ≤ Real.log R := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  have hpolylog : (1 + Real.log R) ^ n ≤ (1 + Real.log N') ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith) n
  have hpolyK : C * (1 + Real.log N') ^ n ≤ K * (N':ℝ) ^ (1 / 2000 : ℝ) := by
    have h := hpoly
    rw [div_mul_eq_mul_div, div_le_iff₀ hK] at h
    linarith [h]
  have hrpow : (N':ℝ) ^ (3998 / 4000 : ℝ) * (N':ℝ) ^ (1 / 2000 : ℝ) = (N':ℝ) := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hRsqnn : 0 ≤ (N':ℝ) ^ (3998 / 4000 : ℝ) := Real.rpow_nonneg hNpos.le _
  have hCpolyR_nn : 0 ≤ C * (1 + Real.log R) ^ n := by positivity
  calc C * (R:ℝ) ^ 2 * (1 + Real.log R) ^ n
      = (C * (1 + Real.log R) ^ n) * (R:ℝ) ^ 2 := by ring
    _ ≤ (C * (1 + Real.log R) ^ n) * (N':ℝ) ^ (3998 / 4000 : ℝ) :=
        mul_le_mul_of_nonneg_left hRsq hCpolyR_nn
    _ ≤ (C * (1 + Real.log N') ^ n) * (N':ℝ) ^ (3998 / 4000 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpolylog hC) hRsqnn
    _ ≤ (K * (N':ℝ) ^ (1 / 2000 : ℝ)) * (N':ℝ) ^ (3998 / 4000 : ℝ) :=
        mul_le_mul_of_nonneg_right hpolyK hRsqnn
    _ = K * ((N':ℝ) ^ (3998 / 4000 : ℝ) * (N':ℝ) ^ (1 / 2000 : ℝ)) := by ring
    _ = K * (N':ℝ) := by rw [hrpow]

private lemma eventually_R_ge (Rb : ℕ) :
    ∀ᶠ N' : ℕ in atTop, Rb ≤ ⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ := by
  have htend : Tendsto (fun N' : ℕ => (N':ℝ) ^ (1999 / 4000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (Rb:ℝ)] with N' h
  exact Nat.le_floor h

/-! ## The `Δπ` lower-bound pinning `31465/1000·N' ≤ δ·log R` -/

private lemma eventually_DL :
    ∀ᶠ N' : ℕ in atTop,
      (31465 : ℝ) / 1000 * N'
        ≤ ((63 - 1 / 100) * (N':ℝ) / Real.log N' - 19)
            * Real.log (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) := by
  have hpin := eventually_logR_lower_theta (4997 / 10000) (by norm_num) (by norm_num)
  have hbeat := eventually_poly_beats_polylog 1 1 1000 (by norm_num)
  have hbeatN := tendsto_natCast_atTop_atTop.eventually hbeat
  filter_upwards [hpin, hbeatN, eventually_ge_atTop 8] with N' hpin hbeat hN8
  set L := Real.log (N':ℝ) with hLdef
  set LR := Real.log (⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ : ℝ) with hLRdef
  have hN1 : (1:ℝ) < (N':ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hL : 0 < L := Real.log_pos hN1
  have hLne : L ≠ 0 := hL.ne'
  simp only [pow_one, Real.rpow_one] at hbeat
  -- hbeat : 1000 * (1 + L) ≤ N'
  have hδ0 : 0 ≤ (63 - 1 / 100) * (N':ℝ) / L - 19 := by
    rw [sub_nonneg, le_div_iff₀ hL]
    nlinarith [hbeat, hL]
  set δ : ℝ := (63 - 1 / 100) * (N':ℝ) / L - 19 with hδdef
  have hδL : δ * L = (63 - 1 / 100) * (N':ℝ) - 19 * L := by
    rw [hδdef]; field_simp
  have hstep : δ * (4997 / 10000 * L) ≤ δ * LR :=
    mul_le_mul_of_nonneg_left hpin hδ0
  have hkey : δ * (4997 / 10000 * L) = 4997 / 10000 * ((63 - 1 / 100) * (N':ℝ) - 19 * L) := by
    rw [show δ * (4997 / 10000 * L) = 4997 / 10000 * (δ * L) by ring, hδL]
  rw [hkey] at hstep
  nlinarith [hstep, hbeat, hL]

/-! ## R2b — the slack discharge -/

set_option maxHeartbeats 10000000 in
-- The endgame assembly threads ~40 named bounds through one linear closure; the
-- large local context makes elaboration heartbeat-heavy.
theorem winSlackM_ev : ∃ D₀ : ℕ, 300 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
    ∀ C₀ : ℝ, 0 ≤ C₀ → ∀ᶠ N' : ℕ in atTop, WinSlackM D C₀ N' := by
  classical
  -- === F-only constants (obtained before the cutoff `D₀`) ===
  set Ic : ℝ := (Ical Fstar1 : ℝ) with hIcdef
  have hIcpos : 0 < Ic := Ical_Fstar1_pos
  set Jc : Fin 5 → ℝ := fun m => ((Jcal m Fstar1 : ℚ) : ℝ) with hJcdef
  have hJcpos : ∀ m, 0 < Jc m := fun m => by
    simp only [hJcdef]; exact_mod_cast Jcal_Fstar1_pos m
  set SJ : ℝ := ∑ m : Fin 5, Jc m with hSJdef
  have hcert : (4003 : ℝ) * Ic < 1999 * SJ := by
    simp only [hSJdef, hJcdef, hIcdef]
    rw [← Rat.cast_sum]
    exact_mod_cast theta_ratio_cert_sharp
  have hSJpos : 0 < SJ := by nlinarith [hcert, hIcpos]
  obtain ⟨AF, hAF0, hyb⟩ := mv_I_split Fstar1
  obtain ⟨A1, hA10, hMb⟩ := mv_I_split onePoly
  have hqd_ex : ∀ m : Fin 5, ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → 300 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ (c : ℝ) (R₀ : ℕ), 0 ≤ c ∧ ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' Fstar1)
            - ((W'.totient : ℝ) / W' * Real.log R) ^ 6 * ((Jcal m Fstar1 : ℚ) : ℝ)|
          ≤ (c / Real.log R + A / Real.sqrt D)
                * ((W'.totient : ℝ) / W' * Real.log R) ^ 6 := fun m => qdiag_err_split m
  choose Aqd hAqd0 hqdbody using hqd_ex
  set AqdSum : ℝ := ∑ m : Fin 5, Aqd m with hAqdSumdef
  have hAqdSum0 : 0 ≤ AqdSum := Finset.sum_nonneg (fun m _ => hAqd0 m)
  have hAqd_le : ∀ m, Aqd m ≤ AqdSum := fun m =>
    Finset.single_le_sum (fun i _ => hAqd0 i) (Finset.mem_univ m)
  have hcf_ex : ∀ m : Fin 5, ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 300 ≤ Dthr ∧
      ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) → 48 * 5 ^ 2 ≤ D →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1)|
          ≤ (4 * Cs * CF * (5 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 5 R W' m (yF R W' Fstar1) :=
    fun m => s2_collision_floor m
  choose CFf hCFf0 Dthrf hDthrf300 hcfbody using hcf_ex
  set SCFJ : ℝ := ∑ m : Fin 5, CFf m * (Jc m + 1) with hSCFJdef
  have hSCFJ0 : 0 ≤ SCFJ :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (hCFf0 m) (by linarith [hJcpos m]))
  set DthrSum : ℕ := ∑ m : Fin 5, Dthrf m with hDthrSumdef
  have hDthrf_le : ∀ m, Dthrf m ≤ DthrSum := fun m =>
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
  have hCs0 : (0:ℝ) ≤ Cs := by rw [Cs]; norm_num
  -- === the cutoff `D₀` ===
  set Dthr_real : ℝ := 1750000 / Ic + 6 ^ 5 * AF * 1400000 / Ic
      + 300 * 6 ^ 5 * A1 * 1400000 / Ic + (AqdSum * 1400000 / Ic) ^ 2
      + 1000 * (4 * Cs * 5 ^ 2) * SCFJ * 700000 / (63 * Ic) + (2 * AqdSum) ^ 2 with hDthrrealdef
  have hDthrreal0 : 0 ≤ Dthr_real := by
    rw [hDthrrealdef]; positivity
  refine ⟨max (max 1200 DthrSum) ⌈Dthr_real⌉₊,
    le_trans (by norm_num) (le_trans (le_max_left 1200 DthrSum) (le_max_left _ _)), ?_⟩
  intro D hD C₀ hC₀
  -- === D-facts ===
  have hD1200 : 1200 ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
  have hD300 : 300 ≤ D := by omega
  have hDthrSumD : DthrSum ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
  have hDR : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDthrrealD : Dthr_real ≤ (D:ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hD)
  -- === modulus facts at `W' = primorial D` ===
  set W' : ℕ := primorial D with hW'def
  have hW'sqf : Squarefree W' := primorial_sqf' D
  have hW'pos : 0 < W' := primorial_pos'' D
  have hW'ne : (W' : ℝ) ≠ 0 := by exact_mod_cast hW'pos.ne'
  have hφW'pos : (0 : ℝ) < (W'.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW'pos
  have hφW'ne : (W'.totient : ℝ) ≠ 0 := hφW'pos.ne'
  have hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p := primorial_hDlt D
  have hκle : (W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D := primorial_ratio_le D (by omega)
  have hUpper : PhiUpperAtom W' := phiUpperAtom_final W' hW'pos.ne'
  set κ : ℝ := (W'.totient : ℝ) / (W' : ℝ) with hκdef
  have hκpos : 0 < κ := div_pos hφW'pos (by exact_mod_cast hW'pos)
  have hφeq : κ * (W' : ℝ) = (W'.totient : ℝ) := by
    rw [hκdef]; field_simp
  -- === W'-dependent constants (obtained before the `∀ᶠ N'`) ===
  obtain ⟨cF, hcF0, hybR⟩ := hyb W' D hW'sqf hW'pos hUpper (by omega) hDlt
  obtain ⟨c1, hc10, hMbR⟩ := hMb W' D hW'sqf hW'pos hUpper (by omega) hDlt
  have hqd2 : ∀ m : Fin 5, ∃ (c : ℝ) (R₀ : ℕ), 0 ≤ c ∧
      ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
      |Qdiag_mW 5 R W' m (yF R W' Fstar1)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6 * ((Jcal m Fstar1 : ℚ) : ℝ)|
        ≤ (c / Real.log R + Aqd m / Real.sqrt D)
              * ((W'.totient : ℝ) / W' * Real.log R) ^ 6 :=
    fun m => hqdbody m W' D hW'sqf hW'pos hUpper hD300 hDlt hκle
  choose cqd R0qd hcqd0 hqdR using hqd2
  set CqdSum : ℝ := ∑ m : Fin 5, cqd m with hCqdSumdef
  have hCqdSum0 : 0 ≤ CqdSum := Finset.sum_nonneg (fun m _ => hcqd0 m)
  have hcqd_le : ∀ m, cqd m ≤ CqdSum := fun m =>
    Finset.single_le_sum (fun i _ => hcqd0 i) (Finset.mem_univ m)
  have hcf2 : ∀ m : Fin 5, ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
      |Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1)|
        ≤ (4 * Cs * CFf m * (5 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 5 R W' m (yF R W' Fstar1) :=
    fun m => hcfbody m W' D hW'sqf hW'pos hUpper (le_trans (hDthrf_le m) hDthrSumD) hDlt hκle
      (le_trans (by norm_num) hD1200)
  choose R0cf hcfR using hcf2
  obtain ⟨Clam, hClam0, hClamle⟩ := S1_trivial_error_le'_uniform 5 W'
  obtain ⟨Cpas, hpasfun⟩ := phiAtom_upper_lossy W' hW'pos.ne'
  rw [← hκdef] at hpasfun
  set Rbig : ℕ := 2 + (∑ m : Fin 5, R0qd m) + (∑ m : Fin 5, R0cf m) with hRbigdef
  have hR0qd_le : ∀ m, R0qd m ≤ Rbig := fun m => by
    rw [hRbigdef]
    have := Finset.single_le_sum (f := R0qd) (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  have hR0cf_le : ∀ m, R0cf m ≤ Rbig := fun m => by
    rw [hRbigdef]
    have := Finset.single_le_sum (f := R0cf) (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  -- the common target constant for the truncation / herr absolute bounds
  set Kmain : ℝ := 63 * κ ^ 5 * Ic / ((W' : ℝ) * 700000) with hKmaindef
  have hKmain0 : 0 < Kmain := by
    rw [hKmaindef]; positivity
  -- === the `∀ᶠ N'` bundle ===
  filter_upwards [eventually_ge_atTop 8, deltaPi_upper_ev, eventually_R_ge Rbig,
    eventually_logR_ge 1, eventually_DL,
    eventually_div_logR_le (32 * cF) (Ic / 1400000) (by positivity),
    eventually_div_logR_le (12 * (5:ℝ)^2 / D * 32 * c1) (Ic / 1400000) (by positivity),
    eventually_div_logR_le CqdSum (Ic / 1400000) (by positivity),
    eventually_div_logR_le CqdSum (1 / 2) (by norm_num),
    eventually_poly_o_linear 22 Kmain (64 * Clam) hKmain0 (by positivity),
    eventually_polylog_ratio_le 12 14 (5 * C₀) Kmain (by norm_num) hKmain0 (by positivity),
    eventually_logR_ge (max (1 / κ) ((1 + Cpas) / κ))]
    with N' hN8 hΔπ hRge hlogR1 hDLev hbuckY hbuckM hqeL hqe1 hTRev hHerrev hXthr
  -- === abbreviations matching the goal ===
  set R : ℕ := ⌊(N':ℝ) ^ (1999 / 4000 : ℝ)⌋₊ with hRdef
  set LR : ℝ := Real.log (R : ℝ) with hLRdef
  set L : ℝ := Real.log (N' : ℝ) with hLdef
  set X : ℝ := κ * LR with hXdef
  set Base : ℝ := X ^ 5 / (W' : ℝ) with hBasedef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  -- basic facts
  have hN'1 : (1:ℝ) < (N':ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hLpos : 0 < L := Real.log_pos hN'1
  have hLnn : 0 ≤ L := hLpos.le
  have h2Rbig : 2 ≤ Rbig := by rw [hRbigdef]; omega
  have hR2 : 2 ≤ R := le_trans h2Rbig hRge
  have hRr : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hLR1 : (1:ℝ) ≤ LR := hlogR1
  have hLRpos : 0 < LR := by linarith
  have hκLR : X = κ * LR := hXdef
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hLRpos
  have hX0 : 0 ≤ X := hXpos.le
  have hX5pos : 0 < X ^ 5 := pow_pos hXpos 5
  have hX6pos : 0 < X ^ 6 := pow_pos hXpos 6
  have hBase0 : 0 < Base := by rw [hBasedef]; exact div_pos hX5pos (by exact_mod_cast hW'pos)
  have hLRthr : max (1 / κ) ((1 + Cpas) / κ) ≤ LR := hXthr
  have h1X : (1:ℝ) ≤ X := by
    have hle : 1 / κ ≤ LR := le_trans (le_max_left _ _) hLRthr
    rw [div_le_iff₀ hκpos] at hle
    rw [hXdef]; nlinarith [hle]
  have hXCpas : 1 + Cpas ≤ X := by
    have hle : (1 + Cpas) / κ ≤ LR := le_trans (le_max_right _ _) hLRthr
    rw [div_le_iff₀ hκpos] at hle
    rw [hXdef]; nlinarith [hle]
  have hPASnn : 0 ≤ PAS := by
    rw [hPASdef]; unfold Salt.Maynard.phiAtomSum
    exact Finset.sum_nonneg fun r _ => by positivity
  have hPASle : PAS ≤ 4 * X + Cpas := by
    have h := hpasfun R hR2
    rw [← hLRdef] at h
    -- h : phiAtomSum R W' ≤ 4 * (κ * LR) + Cpas
    rw [← hPASdef, ← hXdef] at h; exact h
  have hPAS6X : 1 + PAS ≤ 6 * X := by linarith [hPASle, hXCpas, h1X]
  -- expose and fold the goal
  unfold WinSlackM
  rw [← hW'def, ← hRdef, ← hLRdef, ← hLdef]
  set δ : ℝ := (63 - 1 / 100) * (N':ℝ) / L - 19 with hδdef
  set YS : ℝ := ∑ r ∈ kSieveIndex 5 R W', yF R W' Fstar1 r ^ 2 / ∏ i, ((r i).totient : ℝ)
    with hYSdef
  set MS : ℝ := ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, ((r i).totient : ℝ) with hMSdef
  set LAM : ℝ := ∑ d ∈ kSieveIndex 5 R W', |lam 5 R W' (yF R W' Fstar1) d| with hLAMdef
  simp only [show 2 * 5 + 2 = 12 from rfl, show 2 * 5 + 4 = 14 from rfl]
  -- === identities ===
  have hδ0 : 0 ≤ δ := by
    by_contra hc
    rw [not_le] at hc
    have hneg : δ * LR < 0 := mul_neg_of_neg_of_pos hc hLRpos
    have hnn : (0:ℝ) ≤ 31465 / 1000 * (N':ℝ) := by positivity
    linarith only [hDLev, hneg, hnn]
  have hXfull : (W'.totient : ℝ) / (W' : ℝ) * Real.log (R : ℝ) = X := by
    rw [← hκdef, ← hLRdef, ← hXdef]
  have hVid : δ / (W'.totient : ℝ) * X ^ 6 = δ * LR * Base := by
    have h1 : X ^ 6 = X ^ 5 * (κ * LR) := by rw [show X ^ 6 = X ^ 5 * X by ring, hXdef]
    rw [h1, hBasedef, hφeq.symm]; field_simp
  have hsimpY : ((simplexInt (sq (ofPoly Fstar1)) : ℚ) : ℝ) = Ic := by
    rw [simplexInt_sq_ofPoly_eq_Ical]
  have hsimpM : ((simplexInt (sq (ofPoly onePoly)) : ℚ) : ℝ) = 1 / 120 := by
    rw [simplexInt_sq_ofPoly_onePoly]; norm_num
  -- === YS / MS moment bounds ===
  set BY : ℝ := cF * (1 + X) ^ 5 / LR + AF * (1 + PAS) ^ 5 / (D : ℝ) with hBYdef
  set BM : ℝ := c1 * (1 + X) ^ 5 / LR + A1 * (1 + PAS) ^ 5 / (D : ℝ) with hBMdef
  have hYS : YS ≤ X ^ 5 * Ic + BY := by
    have h := (abs_le.mp (hybR R hLR1)).2
    have hYSeq : (∑ r ∈ kSieveIndex 5 R W',
        eval (ofPoly Fstar1) (fun i => Real.log (r i) / Real.log R) ^ 2
          / ∏ i, ((r i).totient : ℝ)) = YS := by
      rw [hYSdef]; refine Finset.sum_congr rfl (fun r hr => ?_)
      simp only [yF, if_pos hr]
    rw [hYSeq, hXfull, hsimpY, ← hLRdef, ← hPASdef] at h
    rw [hBYdef]; linarith [h]
  have hMS : MS ≤ X ^ 5 * (1 / 120) + BM := by
    have h := (abs_le.mp (hMbR R hLR1)).2
    have hMSeq : (∑ r ∈ kSieveIndex 5 R W',
        eval (ofPoly onePoly) (fun i => Real.log (r i) / Real.log R) ^ 2
          / ∏ i, ((r i).totient : ℝ)) = MS := by
      rw [hMSdef]; refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [eval_ofPoly_onePoly, one_pow]
    rw [hMSeq, hXfull, hsimpM, ← hLRdef, ← hPASdef] at h
    rw [hBMdef]; linarith [h]
  -- === bucket nonnegativity + relative bounds (BY/X⁵, BM/X⁵) ===
  have hLRnn : 0 ≤ LR := hLRpos.le
  have h1Xnn : 0 ≤ 1 + X := by linarith
  have hPAS1nn : 0 ≤ 1 + PAS := by linarith
  have hXpow5 : (1 + X) ^ 5 ≤ 32 * X ^ 5 := by
    calc (1 + X) ^ 5 ≤ (2 * X) ^ 5 := pow_le_pow_left₀ h1Xnn (by linarith) 5
      _ = 32 * X ^ 5 := by ring
  have hPASpow5 : (1 + PAS) ^ 5 ≤ 6 ^ 5 * X ^ 5 := by
    calc (1 + PAS) ^ 5 ≤ (6 * X) ^ 5 := pow_le_pow_left₀ hPAS1nn hPAS6X 5
      _ = 6 ^ 5 * X ^ 5 := by ring
  have hBY0 : 0 ≤ BY := by rw [hBYdef]; positivity
  have hBM0 : 0 ≤ BM := by rw [hBMdef]; positivity
  -- === square-root facts and `D`-thresholds ===
  have hsqDpos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDR
  have hsqrtD_sq : Real.sqrt D * Real.sqrt D = (D:ℝ) := Real.mul_self_sqrt hDR.le
  have hDexp : Dthr_real = 1750000 / Ic + 6 ^ 5 * AF * 1400000 / Ic
      + 300 * 6 ^ 5 * A1 * 1400000 / Ic + (AqdSum * 1400000 / Ic) ^ 2
      + 1000 * (4 * Cs * 5 ^ 2) * SCFJ * 700000 / (63 * Ic) + (2 * AqdSum) ^ 2 := hDthrrealdef
  have hn1 : (0:ℝ) ≤ 1750000 / Ic := by positivity
  have hn2 : (0:ℝ) ≤ 6 ^ 5 * AF * 1400000 / Ic := by positivity
  have hn3 : (0:ℝ) ≤ 300 * 6 ^ 5 * A1 * 1400000 / Ic := by positivity
  have hn4 : (0:ℝ) ≤ (AqdSum * 1400000 / Ic) ^ 2 := sq_nonneg _
  have hn5 : (0:ℝ) ≤ 1000 * (4 * Cs * 5 ^ 2) * SCFJ * 700000 / (63 * Ic) := by positivity
  have hn6 : (0:ℝ) ≤ (2 * AqdSum) ^ 2 := sq_nonneg _
  rw [hDexp] at hDthrrealD
  have hMmainD : 1750000 / Ic ≤ (D:ℝ) := by linarith only [hDthrrealD, hn2, hn3, hn4, hn5, hn6]
  have hybD : 6 ^ 5 * AF * 1400000 / Ic ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn3, hn4, hn5, hn6]
  have hMbD : 300 * 6 ^ 5 * A1 * 1400000 / Ic ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn4, hn5, hn6]
  have hqeD : (AqdSum * 1400000 / Ic) ^ 2 ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn3, hn5, hn6]
  have hcollD : 1000 * (4 * Cs * 5 ^ 2) * SCFJ * 700000 / (63 * Ic) ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn3, hn4, hn6]
  have hQdUpD : (2 * AqdSum) ^ 2 ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn3, hn4, hn5]
  have hsqrtD_ge : 2 * AqdSum ≤ Real.sqrt D := by
    rw [show (2:ℝ) * AqdSum = Real.sqrt ((2 * AqdSum) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hQdUpD
  have hAqdD_half : AqdSum / Real.sqrt D ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hsqDpos (by norm_num)]; linarith only [hsqrtD_ge]
  -- === per-`m` qdiag bounds ===
  set QEc : Fin 5 → ℝ := fun m => cqd m / LR + Aqd m / Real.sqrt D with hQEcdef
  have hQEc0 : ∀ m, 0 ≤ QEc m := fun m => by
    rw [hQEcdef]; apply add_nonneg <;> apply div_nonneg
    · exact hcqd0 m
    · exact hLRnn
    · exact hAqd0 m
    · exact hsqDpos.le
  have hQabs : ∀ m : Fin 5, |Qdiag_mW 5 R W' m (yF R W' Fstar1) - X ^ 6 * Jc m|
      ≤ QEc m * X ^ 6 := by
    intro m
    have h := hqdR m R (le_trans (hR0qd_le m) hRge) hLR1
    rw [hXfull, ← hLRdef] at h
    exact h
  have hQEc1 : ∀ m, QEc m ≤ 1 := by
    intro m
    have h1 : cqd m / LR ≤ CqdSum / LR := div_le_div_of_nonneg_right (hcqd_le m) hLRpos.le
    have h2 : Aqd m / Real.sqrt D ≤ AqdSum / Real.sqrt D :=
      div_le_div_of_nonneg_right (hAqd_le m) hsqDpos.le
    rw [hQEcdef]; simp only; linarith only [h1, h2, hqe1, hAqdD_half]
  have hQdnn : ∀ m : Fin 5, 0 ≤ Qdiag_mW 5 R W' m (yF R W' Fstar1) := by
    intro m; rw [qdiag_eq_yMsq_sum]
    exact Finset.sum_nonneg (fun u _ => div_nonneg (sq_nonneg _)
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)))
  have hQhi : ∀ m : Fin 5,
      Qdiag_mW 5 R W' m (yF R W' Fstar1) ≤ X ^ 6 * (Jc m + 1) := by
    intro m
    have h := (abs_le.mp (hQabs m)).2
    have h2 := mul_le_mul_of_nonneg_right (hQEc1 m) hX6pos.le
    have hexp : X ^ 6 * (Jc m + 1) = X ^ 6 * Jc m + X ^ 6 := by ring
    rw [hexp]; linarith only [h, h2]
  have hQlo : ∀ m : Fin 5, X ^ 6 * Jc m - QEc m * X ^ 6
      ≤ Qdiag_mW 5 R W' m (yF R W' Fstar1) := fun m => by
    linarith only [(abs_le.mp (hQabs m)).1]
  -- === the named quantities ===
  set QEcSum : ℝ := ∑ m : Fin 5, QEc m with hQEcSumdef
  have hQEcSum0 : 0 ≤ QEcSum := Finset.sum_nonneg (fun m _ => hQEc0 m)
  set U : ℝ := 63 * (N':ℝ) * Base * Ic with hUdef
  set V : ℝ := δ * LR * Base * SJ with hVdef
  set pqe : ℝ := δ * LR * Base * QEcSum with hpqedef
  set pcoll : ℝ :=
    1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * 5 ^ 2 / (D:ℝ)) * X ^ 6 * SCFJ
    with hpcolldef
  set pherr : ℝ := 5 * (C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14) with hpherrdef
  set p1 : ℝ := 63 * (N':ℝ) * Base * (5 / 2) / (D:ℝ) with hp1def
  set p2 : ℝ := 63 * (N':ℝ) / (W':ℝ) * BY with hp2def
  set p3 : ℝ := 63 * (N':ℝ) / (W':ℝ) * (12 * (5:ℝ) ^ 2 / (D:ℝ)) * BM with hp3def
  set pTR : ℝ := 64 * LAM ^ 2 with hpTRdef
  set CollUB : Fin 5 → ℝ := fun m =>
    1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ))
      * (X ^ 6 * (Jc m + 1))
    with hCollUBdef
  have hL14pos : 0 < L ^ 14 := pow_pos hLpos 14
  have hBasenn : 0 ≤ Base := hBase0.le
  -- === RHS main lower bound ===
  have hmain_ge : V - pqe
      ≤ ∑ m : Fin 5, δ / (W'.totient:ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1) := by
    have hVid2 : ∀ m : Fin 5, δ / (W'.totient:ℝ) * (X ^ 6 * Jc m - QEc m * X ^ 6)
        = δ * LR * Base * Jc m - δ * LR * Base * QEc m := by
      intro m
      rw [mul_sub, show δ / (W'.totient:ℝ) * (X ^ 6 * Jc m)
            = δ / (W'.totient:ℝ) * X ^ 6 * Jc m by ring, hVid,
        show δ / (W'.totient:ℝ) * (QEc m * X ^ 6)
            = δ / (W'.totient:ℝ) * X ^ 6 * QEc m by ring, hVid]
    have hper : ∀ m ∈ Finset.univ, δ * LR * Base * Jc m - δ * LR * Base * QEc m
        ≤ δ / (W'.totient:ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1) := by
      intro m _
      rw [← hVid2 m]
      exact mul_le_mul_of_nonneg_left (hQlo m) (div_nonneg hδ0 hφW'pos.le)
    have hsum := Finset.sum_le_sum hper
    have hsumeq : ∑ m : Fin 5, (δ * LR * Base * Jc m - δ * LR * Base * QEc m) = V - pqe := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hVdef, hpqedef,
        ← hSJdef, ← hQEcSumdef]
    linarith only [hsum, hsumeq.symm.le, hsumeq.le]
  -- === RHS collision + herr upper bound ===
  have hcolleq : ∑ m : Fin 5, CollUB m = pcoll := by
    rw [hpcolldef, hSCFJdef, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [hCollUBdef]; ring)
  have hcoll_le : ∑ m : Fin 5, (deltaPi 5 64 N' m / (W'.totient:ℝ)
        * (Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1))
      + C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14) ≤ pcoll + pherr := by
    have hper : ∀ m ∈ Finset.univ,
        deltaPi 5 64 N' m / (W'.totient:ℝ)
            * (Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1))
          + C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14
        ≤ CollUB m + C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14 := by
      intro m _
      have hcfm := hcfR m R (le_trans (hR0cf_le m) hRge) hLR1
      have hQds2 : Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1)
          ≤ 4 * Cs * CFf m * 5 ^ 2 / (D:ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1) :=
        le_trans (le_abs_self _) hcfm
      have hΔ0 : 0 ≤ deltaPi 5 64 N' m := deltaPi_nonneg 5 64 N' m (by norm_num)
      have hcoef0 : 0 ≤ 4 * Cs * CFf m * 5 ^ 2 / (D:ℝ) :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCs0) (hCFf0 m))
          (by norm_num)) hDR.le
      have hA'nn : 0 ≤ 1000 * (N':ℝ) / L / (W'.totient:ℝ)
          * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ)) :=
        mul_nonneg (div_nonneg (div_nonneg (by positivity) hLpos.le) hφW'pos.le) hcoef0
      have hs1 : deltaPi 5 64 N' m / (W'.totient:ℝ)
            * (Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1))
          ≤ deltaPi 5 64 N' m / (W'.totient:ℝ)
            * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1)) :=
        mul_le_mul_of_nonneg_left hQds2 (div_nonneg hΔ0 hφW'pos.le)
      have hAle : deltaPi 5 64 N' m / (W'.totient:ℝ) * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ))
          ≤ 1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ)) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hΔπ m) hφW'pos.le) hcoef0
      have hs2 : deltaPi 5 64 N' m / (W'.totient:ℝ)
            * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1))
          ≤ CollUB m := by
        rw [hCollUBdef]; simp only
        calc deltaPi 5 64 N' m / (W'.totient:ℝ)
                * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1))
            = deltaPi 5 64 N' m / (W'.totient:ℝ) * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ))
                * Qdiag_mW 5 R W' m (yF R W' Fstar1) := by ring
          _ ≤ 1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * CFf m * 5 ^ 2 / (D:ℝ))
                * (X ^ 6 * (Jc m + 1)) := mul_le_mul hAle (hQhi m) (hQdnn m) hA'nn
      linarith only [hs1, hs2]
    calc ∑ m : Fin 5, (deltaPi 5 64 N' m / (W'.totient:ℝ)
            * (Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1))
          + C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14)
        ≤ ∑ m : Fin 5, (CollUB m + C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14) :=
          Finset.sum_le_sum hper
      _ = (∑ m : Fin 5, CollUB m) + ∑ _m : Fin 5, C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14 :=
          Finset.sum_add_distrib
      _ = pcoll + pherr := by
          rw [hcolleq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hpherrdef]
          ring
  -- === auxiliary scalar facts ===
  have hCsval : Cs = 12 := rfl
  have hLRleL : LR ≤ L := by
    rw [hLRdef, hLdef]
    exact Real.log_le_log hRr (by exact_mod_cast R_le_N'_theta N' (by omega))
  have hδub : δ ≤ 63 * (N':ℝ) / L := by
    rw [hδdef]
    have hNL : 0 ≤ (N':ℝ) / L := div_nonneg (Nat.cast_nonneg N') hLpos.le
    have he : (63 - 1 / 100) * (N':ℝ) / L = (63 - 1 / 100) * ((N':ℝ) / L) := by ring
    have he2 : 63 * (N':ℝ) / L = 63 * ((N':ℝ) / L) := by ring
    rw [he, he2]; linarith only [hNL]
  have hδLR : δ * LR ≤ 63 * (N':ℝ) := by
    have h1 : δ * LR ≤ 63 * (N':ℝ) / L * LR := mul_le_mul_of_nonneg_right hδub hLRnn
    have h2 : 63 * (N':ℝ) / L * LR ≤ 63 * (N':ℝ) / L * L :=
      mul_le_mul_of_nonneg_left hLRleL (by positivity)
    have h3 : 63 * (N':ℝ) / L * L = 63 * (N':ℝ) := by field_simp
    linarith only [h1, h2, h3.le, h3.ge]
  have hX6φ : X ^ 6 / (W'.totient:ℝ) = Base * LR := by
    have h1 : X ^ 6 = X ^ 5 * (κ * LR) := by rw [show X ^ 6 = X ^ 5 * X by ring, hXdef]
    rw [h1, hBasedef, hφeq.symm]; field_simp
  have hDD2 : (D:ℝ) ≤ (D:ℝ) ^ 2 := by
    have h1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
    calc (D:ℝ) = (D:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (D:ℝ) ^ 2 := pow_le_pow_right₀ h1 (by norm_num)
  -- D-derived scalar bounds
  have hbuckYD : 6 ^ 5 * AF / (D:ℝ) ≤ Ic / 1400000 := by
    rw [div_le_div_iff₀ hDR (by norm_num)]
    linarith only [(div_le_iff₀ hIcpos).mp hybD]
  have hbuckMD2 : 12 * (5:ℝ) ^ 2 / (D:ℝ) * (A1 * (6 ^ 5 * X ^ 5) / (D:ℝ))
      ≤ Ic / 1400000 * X ^ 5 := by
    have hDD : 300 * 6 ^ 5 * A1 / (D:ℝ) ≤ Ic / 1400000 := by
      rw [div_le_div_iff₀ hDR (by norm_num)]
      linarith only [(div_le_iff₀ hIcpos).mp hMbD]
    have hDsq : 300 * 6 ^ 5 * A1 / (D:ℝ) ^ 2 ≤ 300 * 6 ^ 5 * A1 / (D:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hDR hDD2
    have hkey : 12 * (5:ℝ) ^ 2 / (D:ℝ) * (A1 * (6 ^ 5 * X ^ 5) / (D:ℝ))
        = (300 * 6 ^ 5 * A1 / (D:ℝ) ^ 2) * X ^ 5 := by ring
    rw [hkey]
    calc (300 * 6 ^ 5 * A1 / (D:ℝ) ^ 2) * X ^ 5
        ≤ (300 * 6 ^ 5 * A1 / (D:ℝ)) * X ^ 5 := mul_le_mul_of_nonneg_right hDsq hX5pos.le
      _ ≤ (Ic / 1400000) * X ^ 5 := mul_le_mul_of_nonneg_right hDD hX5pos.le
  have hAqdSqrtD : AqdSum / Real.sqrt D ≤ Ic / 1400000 := by
    have hsq : AqdSum * 1400000 / Ic ≤ Real.sqrt D := by
      rw [show AqdSum * 1400000 / Ic = Real.sqrt ((AqdSum * 1400000 / Ic) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt hqeD
    rw [div_le_div_iff₀ hsqDpos (by norm_num)]
    linarith only [(div_le_iff₀ hIcpos).mp hsq]
  have hGnn : 0 ≤ 63 * (N':ℝ) * Base :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N')) hBasenn
  have hcoeffW : 0 ≤ 63 * (N':ℝ) / (W':ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg W'); positivity
  -- === bucket bounds ===
  have hBYbound : BY ≤ X ^ 5 * (Ic / 700000) := by
    rw [hBYdef]
    have hb1 : cF * (1 + X) ^ 5 / LR ≤ Ic / 1400000 * X ^ 5 := by
      have s1 : cF * (1 + X) ^ 5 / LR ≤ cF * (32 * X ^ 5) / LR :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXpow5 hcF0) hLRpos.le
      have s2 : cF * (32 * X ^ 5) / LR = 32 * cF / LR * X ^ 5 := by ring
      have s3 : 32 * cF / LR * X ^ 5 ≤ Ic / 1400000 * X ^ 5 :=
        mul_le_mul_of_nonneg_right hbuckY hX5pos.le
      linarith only [s1, s2.le, s2.ge, s3]
    have hb2 : AF * (1 + PAS) ^ 5 / (D:ℝ) ≤ Ic / 1400000 * X ^ 5 := by
      have s1 : AF * (1 + PAS) ^ 5 / (D:ℝ) ≤ AF * (6 ^ 5 * X ^ 5) / (D:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPASpow5 hAF0) hDR.le
      have s2 : AF * (6 ^ 5 * X ^ 5) / (D:ℝ) = 6 ^ 5 * AF / (D:ℝ) * X ^ 5 := by ring
      have s3 : 6 ^ 5 * AF / (D:ℝ) * X ^ 5 ≤ Ic / 1400000 * X ^ 5 :=
        mul_le_mul_of_nonneg_right hbuckYD hX5pos.le
      linarith only [s1, s2.le, s2.ge, s3]
    have he : X ^ 5 * (Ic / 700000) = Ic / 1400000 * X ^ 5 + Ic / 1400000 * X ^ 5 := by ring
    linarith only [hb1, hb2, he.le, he.ge]
  have hBMbound : 12 * (5:ℝ) ^ 2 / (D:ℝ) * BM ≤ X ^ 5 * (Ic / 700000) := by
    rw [hBMdef, mul_add]
    have hb1 : 12 * (5:ℝ) ^ 2 / (D:ℝ) * (c1 * (1 + X) ^ 5 / LR) ≤ Ic / 1400000 * X ^ 5 := by
      have s1 : 12 * (5:ℝ) ^ 2 / (D:ℝ) * (c1 * (1 + X) ^ 5 / LR)
          ≤ 12 * (5:ℝ) ^ 2 / (D:ℝ) * (c1 * (32 * X ^ 5) / LR) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXpow5 hc10) hLRpos.le)
          (by positivity)
      have s2 : 12 * (5:ℝ) ^ 2 / (D:ℝ) * (c1 * (32 * X ^ 5) / LR)
          = 12 * (5:ℝ) ^ 2 / (D:ℝ) * 32 * c1 / LR * X ^ 5 := by ring
      have s3 : 12 * (5:ℝ) ^ 2 / (D:ℝ) * 32 * c1 / LR * X ^ 5 ≤ Ic / 1400000 * X ^ 5 :=
        mul_le_mul_of_nonneg_right hbuckM hX5pos.le
      linarith only [s1, s2.le, s2.ge, s3]
    have hb2 : 12 * (5:ℝ) ^ 2 / (D:ℝ) * (A1 * (1 + PAS) ^ 5 / (D:ℝ))
        ≤ Ic / 1400000 * X ^ 5 := by
      have s1 : 12 * (5:ℝ) ^ 2 / (D:ℝ) * (A1 * (1 + PAS) ^ 5 / (D:ℝ))
          ≤ 12 * (5:ℝ) ^ 2 / (D:ℝ) * (A1 * (6 ^ 5 * X ^ 5) / (D:ℝ)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPASpow5 hA10) hDR.le)
          (by positivity)
      linarith only [s1, hbuckMD2]
    have he : X ^ 5 * (Ic / 700000) = Ic / 1400000 * X ^ 5 + Ic / 1400000 * X ^ 5 := by ring
    linarith only [hb1, hb2, he.le, he.ge]
  -- === piece bounds (each ≤ U/700000) ===
  have hp1 : p1 ≤ U / 700000 := by
    rw [hp1def, hUdef]
    have hcoef : 5 / 2 / (D:ℝ) ≤ Ic / 700000 := by
      rw [div_le_div_iff₀ hDR (by norm_num)]
      linarith only [(div_le_iff₀ hIcpos).mp hMmainD]
    have h1 : 63 * (N':ℝ) * Base * (5 / 2 / (D:ℝ)) ≤ 63 * (N':ℝ) * Base * (Ic / 700000) :=
      mul_le_mul_of_nonneg_left hcoef hGnn
    have h2 : 63 * (N':ℝ) * Base * (5 / 2) / (D:ℝ)
        = 63 * (N':ℝ) * Base * (5 / 2 / (D:ℝ)) := by ring
    have h3 : 63 * (N':ℝ) * Base * (Ic / 700000) = 63 * (N':ℝ) * Base * Ic / 700000 := by ring
    linarith only [h1, h2.le, h2.ge, h3.le, h3.ge]
  have hp2 : p2 ≤ U / 700000 := by
    rw [hp2def]
    have h1 : 63 * (N':ℝ) / (W':ℝ) * BY
        ≤ 63 * (N':ℝ) / (W':ℝ) * (X ^ 5 * (Ic / 700000)) :=
      mul_le_mul_of_nonneg_left hBYbound hcoeffW
    have h2 : 63 * (N':ℝ) / (W':ℝ) * (X ^ 5 * (Ic / 700000)) = U / 700000 := by
      rw [hUdef, hBasedef]; field_simp
    linarith only [h1, h2.le, h2.ge]
  have hp3 : p3 ≤ U / 700000 := by
    rw [hp3def]
    have h1 : 63 * (N':ℝ) / (W':ℝ) * (12 * (5:ℝ) ^ 2 / (D:ℝ) * BM)
        ≤ 63 * (N':ℝ) / (W':ℝ) * (X ^ 5 * (Ic / 700000)) :=
      mul_le_mul_of_nonneg_left hBMbound hcoeffW
    have h2 : 63 * (N':ℝ) / (W':ℝ) * (12 * (5:ℝ) ^ 2 / (D:ℝ)) * BM
        = 63 * (N':ℝ) / (W':ℝ) * (12 * (5:ℝ) ^ 2 / (D:ℝ) * BM) := by ring
    have h3 : 63 * (N':ℝ) / (W':ℝ) * (X ^ 5 * (Ic / 700000)) = U / 700000 := by
      rw [hUdef, hBasedef]; field_simp
    linarith only [h1, h2.le, h2.ge, h3.le, h3.ge]
  have hQEcSum_bound : QEcSum ≤ Ic / 700000 := by
    rw [hQEcSumdef, hQEcdef]
    have hsplit : ∑ m : Fin 5, (cqd m / LR + Aqd m / Real.sqrt D)
        = (∑ m : Fin 5, cqd m) / LR + (∑ m : Fin 5, Aqd m) / Real.sqrt D := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    rw [hsplit, ← hCqdSumdef, ← hAqdSumdef]
    linarith only [hqeL, hAqdSqrtD]
  have hpqe : pqe ≤ U / 700000 := by
    rw [hpqedef]
    have h1 : δ * LR * Base * QEcSum ≤ 63 * (N':ℝ) * Base * QEcSum := by
      have hmul := mul_le_mul_of_nonneg_right hδLR (mul_nonneg hBasenn hQEcSum0)
      calc δ * LR * Base * QEcSum = δ * LR * (Base * QEcSum) := by ring
        _ ≤ 63 * (N':ℝ) * (Base * QEcSum) := hmul
        _ = 63 * (N':ℝ) * Base * QEcSum := by ring
    have h2 : 63 * (N':ℝ) * Base * QEcSum ≤ 63 * (N':ℝ) * Base * (Ic / 700000) :=
      mul_le_mul_of_nonneg_left hQEcSum_bound hGnn
    have h3 : 63 * (N':ℝ) * Base * (Ic / 700000) = U / 700000 := by rw [hUdef]; ring
    linarith only [h1, h2, h3.le, h3.ge]
  -- === truncation / herr common bound `Kmain·N' ≤ U/700000` ===
  have hKmainNle : Kmain * (N':ℝ) ≤ U / 700000 := by
    have hBaseexp : Base = κ ^ 5 * LR ^ 5 / (W':ℝ) := by rw [hBasedef, hXdef]; ring
    have hUexp : U / 700000 = 63 * (N':ℝ) * (κ ^ 5 * LR ^ 5) * Ic / ((W':ℝ) * 700000) := by
      rw [hUdef, hBaseexp]; field_simp
    have hKexp : Kmain * (N':ℝ) = 63 * (N':ℝ) * (κ ^ 5 * 1) * Ic / ((W':ℝ) * 700000) := by
      rw [hKmaindef]; field_simp
    rw [hUexp, hKexp]
    have hLR5 : (1:ℝ) ≤ LR ^ 5 := one_le_pow₀ hLR1
    have hfac : (0:ℝ) ≤ 63 * (N':ℝ) * κ ^ 5 * Ic :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N'))
        (pow_nonneg hκpos.le 5)) hIcpos.le
    have hab : 63 * (N':ℝ) * (κ ^ 5 * 1) * Ic ≤ 63 * (N':ℝ) * (κ ^ 5 * LR ^ 5) * Ic := by
      have hm := mul_le_mul_of_nonneg_left hLR5 hfac
      calc 63 * (N':ℝ) * (κ ^ 5 * 1) * Ic = 63 * (N':ℝ) * κ ^ 5 * Ic * 1 := by ring
        _ ≤ 63 * (N':ℝ) * κ ^ 5 * Ic * LR ^ 5 := hm
        _ = 63 * (N':ℝ) * (κ ^ 5 * LR ^ 5) * Ic := by ring
    exact div_le_div_of_nonneg_right hab (by positivity)
  -- === pcoll bound ===
  have hCsnn2 : (0:ℝ) ≤ 4 * Cs * 5 ^ 2 := by rw [hCsval]; norm_num
  have hX6eq : X ^ 6 = Base * LR * (W'.totient:ℝ) := by rw [← hX6φ]; field_simp
  have hpcoll : pcoll ≤ U / 700000 := by
    have hid : pcoll = 1000 * (4 * Cs * 5 ^ 2 / (D:ℝ)) * SCFJ * Base * ((N':ℝ) * LR / L) := by
      rw [hpcolldef, hX6eq]; field_simp
    rw [hid]
    have hNLRL : (N':ℝ) * LR / L ≤ (N':ℝ) := by
      rw [div_le_iff₀ hLpos]
      have hm := mul_le_mul_of_nonneg_left hLRleL (Nat.cast_nonneg (α:=ℝ) N')
      linarith only [hm]
    have hCleft : 0 ≤ 1000 * (4 * Cs * 5 ^ 2 / (D:ℝ)) * SCFJ * Base :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hCsnn2 hDR.le)) hSCFJ0) hBasenn
    have hstep1 : 1000 * (4 * Cs * 5 ^ 2 / (D:ℝ)) * SCFJ * Base * ((N':ℝ) * LR / L)
        ≤ 1000 * (4 * Cs * 5 ^ 2 / (D:ℝ)) * SCFJ * Base * (N':ℝ) :=
      mul_le_mul_of_nonneg_left hNLRL hCleft
    -- 1000*(4Cs5²/D)*SCFJ*Base*N' ≤ U/700000
    have hcoefbnd : 1000 * (4 * Cs * 5 ^ 2 / (D:ℝ)) * SCFJ ≤ 63 * Ic / 700000 := by
      have hd := (div_le_iff₀ (by positivity : (0:ℝ) < 63 * Ic)).mp hcollD
      have he : 1000 * (4 * Cs * 5 ^ 2 / (D:ℝ)) * SCFJ
          = 1000 * (4 * Cs * 5 ^ 2) * SCFJ / (D:ℝ) := by ring
      rw [he, div_le_div_iff₀ hDR (by norm_num)]
      linarith only [hd]
    have hstep2 : 1000 * (4 * Cs * 5 ^ 2 / (D:ℝ)) * SCFJ * Base * (N':ℝ)
        ≤ 63 * Ic / 700000 * Base * (N':ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefbnd hBasenn) (Nat.cast_nonneg N')
    have hUeq : 63 * Ic / 700000 * Base * (N':ℝ) = U / 700000 := by rw [hUdef]; ring
    linarith only [hstep1, hstep2, hUeq.le, hUeq.ge]
  -- === truncation bound ===
  have hpTR : pTR ≤ U / 700000 := by
    rw [hpTRdef]
    have h := hClamle R hR2 (yF R W' Fstar1) (fun r => yF_Fstar1_abs_le_one R W' r)
    rw [← hLRdef, ← hLAMdef, show 4 * 5 + 2 = 22 from rfl] at h
    have hstep1 : (64:ℝ) * LAM ^ 2 ≤ 64 * Clam * (R:ℝ) ^ 2 * (1 + LR) ^ 22 := by
      calc (64:ℝ) * LAM ^ 2 ≤ 64 * (Clam * (R:ℝ) ^ 2 * (1 + LR) ^ 22) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 64 * Clam * (R:ℝ) ^ 2 * (1 + LR) ^ 22 := by ring
    linarith only [hstep1, hTRev, hKmainNle]
  -- === herr bound ===
  have hpherr : pherr ≤ U / 700000 := by
    rw [hpherrdef]
    have hid : 5 * (C₀ * (1 + LR) ^ 12 * (N':ℝ) / L ^ 14)
        = 5 * C₀ * (1 + LR) ^ 12 / L ^ 14 * (N':ℝ) := by ring
    rw [hid]
    have h1 : 5 * C₀ * (1 + LR) ^ 12 / L ^ 14 * (N':ℝ) ≤ Kmain * (N':ℝ) :=
      mul_le_mul_of_nonneg_right hHerrev (Nat.cast_nonneg N')
    linarith only [h1, hKmainNle]
  -- === the certified ratio ===
  have hwin : 63 * (N':ℝ) * (1 + 1 / 100000) * Ic < δ * LR * SJ :=
    win_ratio_core (N':ℝ) δ LR Ic SJ (1 / 100000) hIcpos hcert hDLev
      (by exact_mod_cast (by omega : 0 < N')) (le_refl _)
  have hwin' : U + U / 100000 < V := by
    have heqU : U + U / 100000 = Base * (63 * (N':ℝ) * (1 + 1 / 100000) * Ic) := by
      rw [hUdef]; ring
    have heqV : V = Base * (δ * LR * SJ) := by rw [hVdef]; ring
    rw [heqU, heqV]; exact mul_lt_mul_of_pos_left hwin hBase0
  -- === LHS upper bound ===
  have hLHS_le : (64 - 1) * (N':ℝ) / (W':ℝ) * (YS + 12 * (5:ℝ) ^ 2 / (D:ℝ) * MS)
      + 2 ^ (5 + 1) * LAM ^ 2 ≤ U + p1 + p2 + p3 + pTR := by
    have hcoeff : 0 ≤ (64 - 1) * (N':ℝ) / (W':ℝ) := by
      apply div_nonneg _ (Nat.cast_nonneg W'); positivity
    have h300nn : 0 ≤ 12 * (5:ℝ) ^ 2 / (D:ℝ) := by positivity
    have hinner : YS + 12 * (5:ℝ) ^ 2 / (D:ℝ) * MS
        ≤ (X ^ 5 * Ic + BY) + 12 * (5:ℝ) ^ 2 / (D:ℝ) * (X ^ 5 * (1 / 120) + BM) :=
      add_le_add hYS (mul_le_mul_of_nonneg_left hMS h300nn)
    have hstep : (64 - 1) * (N':ℝ) / (W':ℝ) * (YS + 12 * (5:ℝ) ^ 2 / (D:ℝ) * MS)
        ≤ (64 - 1) * (N':ℝ) / (W':ℝ)
            * ((X ^ 5 * Ic + BY) + 12 * (5:ℝ) ^ 2 / (D:ℝ) * (X ^ 5 * (1 / 120) + BM)) :=
      mul_le_mul_of_nonneg_left hinner hcoeff
    have heq : (64 - 1) * (N':ℝ) / (W':ℝ)
        * ((X ^ 5 * Ic + BY) + 12 * (5:ℝ) ^ 2 / (D:ℝ) * (X ^ 5 * (1 / 120) + BM))
        = U + p1 + p2 + p3 := by
      rw [hUdef, hp1def, hp2def, hp3def, hBasedef]; field_simp; ring
    have hTReq : (2:ℝ) ^ (5 + 1) * LAM ^ 2 = pTR := by
      rw [show (2:ℝ) ^ (5 + 1) = 64 by norm_num, hpTRdef]
    linarith only [hstep, heq.le, heq.ge, hTReq.le, hTReq.ge]
  -- === closure ===
  linarith only [hLHS_le, hmain_ge, hcoll_le, hp1, hp2, hp3, hpqe, hpcoll, hpTR, hpherr, hwin']

/-! ## R2c — the unconditional capstone -/

/-- **R2c (THE RUNG CLOSES).**  Explicit bounded prime gaps `≤ 12`, unconditional
apart from the standing analytic inputs `WindowPNT` and `EHall`: for every `N`
there are two primes `p ≠ q > N` with `|q − p| ≤ 12`.  Assembles `winSlackM_ev`
(R2b) through `winFrontierMW_of` (R2a) — discharging the largeness bundle
`WinFrontierMW D₀` at the F-only cutoff `D₀` — and mirrors `gaps_le_twelve_of_frontierM`
at `(D₀, primorial D₀)` via the free-`W'` diam-12 pigeonhole
`bounded_gaps_reduces_twelve` and the unconditional sieve inequality `win_core_M`. -/
theorem gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  obtain ⟨D₀, hD₀300, hslackfun⟩ := winSlackM_ev
  have hFrontier : WinFrontierMW D₀ := winFrontierMW_of D₀ hD₀300 (hslackfun D₀ le_rfl)
  have hSeqlt : ∀ i : Fin 5, hSeq 5 i < D₀ := fun i => by
    have := hSeq_le_nineteen' i; omega
  refine bounded_gaps_reduces_twelve (primorial D₀) (fun N => ?_)
  obtain ⟨N', R, ν₀, δ, errEH, cval, hNN', hsol, hφpos, hcvnn, hδ0, hDpi, hQlow,
    hS2low, hslack⟩ := hFrontier hPNT hEH N
  refine ⟨N', R, ν₀, yF R (primorial D₀) Fstar1, hNN', ?_⟩
  exact win_core_M N' R ν₀ (primorial D₀) D₀ δ errEH cval
    (primorial_sqf' D₀) (primorial_hDlt D₀) hSeqlt (by omega) hsol hφpos hcvnn hδ0 hDpi
    hQlow hS2low hslack

end Salt.Twelve
