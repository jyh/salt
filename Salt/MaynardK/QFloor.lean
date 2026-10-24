/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.MaynardK.QBridge
import Salt.MaynardK.InnerS2Gen
import Salt.MaynardK.Frontier105
import Salt.MaynardK.Ratio
import Salt.Twelve.QdiagFloor

/-!
# B4.3d — the `Qdiag` floor, the `hQd` payload and the S₂ collision floor (C1, k = 105)

General-`n` ports of `Salt/Twelve/QdiagFloor.lean` (`qdiag_floor`, `qdiag_cmp`,
`s2_collision_floor`, k = 5) and of `Salt/Twelve/GapsFinal.lean`'s `s2_collision_yF_C`, for
a budget weight `yFg R W' P` bounded by `1`, with `J = simplexInt (sq (contractB m P)) > 0`
as a hypothesis. The `6⁶` bucket becomes `6^(n+2)`, the cutoff `300` becomes `12·(n+1)²`,
and `CF = 720000/J` becomes `72·10ⁿ/J` (F-only; every constant precedes `∀ W'`).

The k = 105 instances (`n = 104`, `P = F1`) close with `J1_pos`, which follows from
`ratio_cert_105` and `Iform_pos`. `D` is never a numeral. Nothing here bears on twin primes.
-/

open Finset

namespace Salt.MaynardK

open Salt.Maynard Salt.Twelve Salt.MaynardK

/-- From `⌈exp L⌉₊ ≤ R` conclude `L ≤ log R`. -/
private lemma qfloor_log_ge_of_ceil_exp (L : ℝ) (R : ℕ) (hR : ⌈Real.exp L⌉₊ ≤ R) :
    L ≤ Real.log R := by
  have hpos : (0 : ℝ) < Real.exp L := Real.exp_pos L
  have h1 : Real.exp L ≤ (⌈Real.exp L⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈Real.exp L⌉₊ : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
    _ ≤ Real.log R := Real.log_le_log hpos (le_trans h1 h2)

/-- **(1) The `Qdiag` floor at general `n`.** -/
theorem qdiag_floor_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hy1 : ∀ R W' : ℕ, ∀ s, |yFg R W' P s| ≤ 1)
    (hJ : 0 < ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)) :
    ∃ Dthr : ℕ, 12 * (n + 1) ^ 2 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
            * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ) / 2
          ≤ Qdiag_mW (n + 1) R W' m (yFg R W' P) := by
  obtain ⟨A, hA0, hbridge⟩ := qdiag_bridge_gen n hn P m hy1
  set J : ℝ := ((simplexInt (sq (contractB m P)) : ℚ) : ℝ) with hJdef
  have hJpos : 0 < J := hJ
  obtain ⟨K6, hK6⟩ : ∃ K : ℝ, K = (6 : ℝ) ^ (n + 2) := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ (n + 2) := ⟨_, rfl⟩
  have hK6nn : 0 ≤ K6 := by rw [hK6]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  refine ⟨max (12 * (n + 1) ^ 2) ⌈(30 * K6 * A / J) ^ 2 + 150 * K6 * A / J⌉₊,
    le_max_left _ _, ?_⟩
  intro W' D hW' hpos hUpper hDthr hDlt hκ
  have hDk : 12 * (n + 1) ^ 2 ≤ D := le_trans (le_max_left _ _) hDthr
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDk
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hM2nn : (0 : ℝ) ≤ 30 * K6 * A / J :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK6nn) hA0) hJpos.le
  have hM3nn : (0 : ℝ) ≤ 150 * K6 * A / J :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK6nn) hA0) hJpos.le
  have hTleD : (30 * K6 * A / J) ^ 2 + 150 * K6 * A / J ≤ (D : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hDthr)
  have hDge_sq : (30 * K6 * A / J) ^ 2 ≤ (D : ℝ) := by linarith [hM3nn, hTleD]
  have hM3leD : 150 * K6 * A / J ≤ (D : ℝ) := by
    linarith [sq_nonneg (30 * K6 * A / J), hTleD]
  have hsqD : Real.sqrt D * Real.sqrt D = (D : ℝ) := Real.mul_self_sqrt hDR.le
  have hsqDnn : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsqD_ge : 30 * K6 * A / J ≤ Real.sqrt D := by
    rw [← Real.sqrt_sq hM2nn]; exact Real.sqrt_le_sqrt hDge_sq
  have hJsD : 30 * K6 * A ≤ Real.sqrt D * J := (div_le_iff₀ hJpos).mp hsqD_ge
  have hDJ : 150 * K6 * A ≤ (D : ℝ) * J := (div_le_iff₀ hJpos).mp hM3leD
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
  set L : ℝ := max (max ((1 + Cpas) / κ) (1 / κ)) (6 * K2 * c / J) with hLdef
  refine ⟨max 2 ⌈Real.exp L⌉₊, ?_⟩
  intro R hR hlogR
  set X : ℝ := κ * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le one_pos hlogR
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hlogRpos
  have hXnn : 0 ≤ X := hXpos.le
  have hLlogR : L ≤ Real.log R :=
    qfloor_log_ge_of_ceil_exp L R (le_trans (le_max_right _ _) hR)
  have h1Cpas : 1 + Cpas ≤ X := by
    have hle : (1 + Cpas) / κ ≤ Real.log R :=
      le_trans (by rw [hLdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)) hLlogR
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  have h1X : (1 : ℝ) ≤ X := by
    have hle : (1 : ℝ) / κ ≤ Real.log R :=
      le_trans (by rw [hLdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)) hLlogR
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  have hclog : 6 * K2 * c / J ≤ Real.log R :=
    le_trans (by rw [hLdef]; exact le_max_right _ _) hLlogR
  have hpasR : PAS ≤ 4 * X + Cpas := by
    have h := hpas R hR2
    rw [← hXdef, ← hPASdef] at h; linarith [h]
  have hPASnn : 0 ≤ PAS := by
    rw [hPASdef]; unfold Salt.Maynard.phiAtomSum
    exact Finset.sum_nonneg fun r _ => by positivity
  -- atomise the power bases
  have hYnn : (0 : ℝ) ≤ 1 + X + PAS := by linarith
  have hY6X : 1 + X + PAS ≤ 6 * X := by linarith [hpasR, h1Cpas]
  have hYp : (1 + X + PAS) ^ (n + 2) ≤ K6 * X ^ (n + 2) := by
    calc (1 + X + PAS) ^ (n + 2) ≤ (6 * X) ^ (n + 2) := pow_le_pow_left₀ hYnn hY6X _
      _ = K6 * X ^ (n + 2) := by rw [mul_pow, hK6]
  have h1Xp : (1 + X) ^ (n + 2) ≤ K2 * X ^ (n + 2) := by
    calc (1 + X) ^ (n + 2) ≤ (2 * X) ^ (n + 2) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = K2 * X ^ (n + 2) := by rw [mul_pow, hK2]
  have hb2 := hb R hR2 hlogR
  rw [← hXdef, ← hPASdef] at hb2
  generalize hYdef : (1 + X + PAS) ^ (n + 2) = Yp at hYp hb2
  generalize hZdef : (1 + X) ^ (n + 2) = Zp at h1Xp hb2
  generalize hXPdef : X ^ (n + 2) = XP at hYp h1Xp hb2 ⊢
  have hXPnn : 0 ≤ XP := by rw [← hXPdef]; positivity
  have hbnd1 : c * Zp / Real.log R ≤ XP * J / 6 := by
    rw [div_le_iff₀ hlogRpos]
    have h384 : 6 * K2 * c ≤ Real.log R * J := (div_le_iff₀ hJpos).mp hclog
    calc c * Zp
        ≤ c * (K2 * XP) := mul_le_mul_of_nonneg_left h1Xp hc0
      _ = (K2 * c) * XP := by ring
      _ ≤ Real.log R * J / 6 * XP :=
          mul_le_mul_of_nonneg_right (by linarith [h384]) hXPnn
      _ = XP * J / 6 * Real.log R := by ring
  have hbnd2 : A * κinv * Yp / (D : ℝ) ≤ XP * J / 6 := by
    rw [div_le_iff₀ hDR]
    have hc1 : A * κinv * Yp ≤ A * κinv * (K6 * XP) :=
      mul_le_mul_of_nonneg_left hYp (mul_nonneg hA0 hκinv_pos.le)
    have hc2 : A * κinv * (K6 * XP) ≤ A * (5 * Real.sqrt D) * (K6 * XP) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ hA0)
        (mul_nonneg hK6nn hXPnn)
    have hc3 : A * (5 * Real.sqrt D) * (K6 * XP) ≤ XP * J / 6 * (D : ℝ) := by
      have hstep : (30 * K6 * A) * (XP * Real.sqrt D / 6)
          ≤ (Real.sqrt D * J) * (XP * Real.sqrt D / 6) :=
        mul_le_mul_of_nonneg_right hJsD (by positivity)
      calc A * (5 * Real.sqrt D) * (K6 * XP)
          = (30 * K6 * A) * (XP * Real.sqrt D / 6) := by ring
        _ ≤ (Real.sqrt D * J) * (XP * Real.sqrt D / 6) := hstep
        _ = XP * J / 6 * (Real.sqrt D * Real.sqrt D) := by ring
        _ = XP * J / 6 * (D : ℝ) := by rw [hsqD]
    linarith [hc1, hc2, hc3]
  have hbnd3 : A * κinv ^ 2 * Yp / (D : ℝ) ^ 2 ≤ XP * J / 6 := by
    rw [div_le_iff₀ (pow_pos hDR 2)]
    have hκinv2 : κinv ^ 2 ≤ 25 * (D : ℝ) := by
      have hfac : (0 : ℝ) ≤ (5 * Real.sqrt D - κinv) * (5 * Real.sqrt D + κinv) :=
        mul_nonneg (sub_nonneg.mpr hκ) (by linarith [hsqDnn, hκinv_pos.le])
      have heq : (5 * Real.sqrt D - κinv) * (5 * Real.sqrt D + κinv)
          = 25 * (Real.sqrt D * Real.sqrt D) - κinv ^ 2 := by ring
      rw [hsqD] at heq
      rw [heq] at hfac
      linarith [hfac]
    have hc1 : A * κinv ^ 2 * Yp ≤ A * κinv ^ 2 * (K6 * XP) :=
      mul_le_mul_of_nonneg_left hYp (mul_nonneg hA0 (sq_nonneg _))
    have hc2 : A * κinv ^ 2 * (K6 * XP) ≤ A * (25 * (D : ℝ)) * (K6 * XP) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκinv2 hA0)
        (mul_nonneg hK6nn hXPnn)
    have hc3 : A * (25 * (D : ℝ)) * (K6 * XP) ≤ XP * J / 6 * (D : ℝ) ^ 2 := by
      have hstep : (150 * K6 * A) * (XP * (D : ℝ) / 6)
          ≤ ((D : ℝ) * J) * (XP * (D : ℝ) / 6) :=
        mul_le_mul_of_nonneg_right hDJ (by positivity)
      calc A * (25 * (D : ℝ)) * (K6 * XP)
          = (150 * K6 * A) * (XP * (D : ℝ) / 6) := by ring
        _ ≤ ((D : ℝ) * J) * (XP * (D : ℝ) / 6) := hstep
        _ = XP * J / 6 * (D : ℝ) ^ 2 := by ring
    linarith [hc1, hc2, hc3]
  linarith [(abs_le.mp hb2).1, hbnd1, hbnd2, hbnd3]

/-- **(2) The pointwise `hQd` payload at general `n`**, `CF = 72·10ⁿ/J` (F-only). -/
theorem qdiag_cmp_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hy1 : ∀ R W' : ℕ, ∀ s, |yFg R W' P s| ≤ 1)
    (hJ : 0 < ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 12 * (n + 1) ^ 2 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        (Salt.Maynard.phiAtomSum R W' + lemma53Const * ((n + 1 : ℕ) : ℝ) * Real.log R / D) ^ 2
            * (2 * Salt.Maynard.phiAtomSum R W') ^ n
          ≤ CF * Qdiag_gv (n + 1) R W' m (yFg R W' P) := by
  obtain ⟨Dthr1, h12_1, hfloor⟩ := qdiag_floor_gen n hn P m hy1 hJ
  set J : ℝ := ((simplexInt (sq (contractB m P)) : ℚ) : ℝ) with hJdef
  have hJpos : 0 < J := hJ
  obtain ⟨K10, hK10⟩ : ∃ K : ℝ, K = (10 : ℝ) ^ n := ⟨_, rfl⟩
  have hK10nn : 0 ≤ K10 := by rw [hK10]; positivity
  set kR : ℝ := ((n + 1 : ℕ) : ℝ) with hkR
  have hkRnn : 0 ≤ kR := by rw [hkR]; positivity
  refine ⟨72 * K10 / J, div_nonneg (by positivity) hJpos.le,
    max Dthr1 ⌈(5 * kR * lemma53Const) ^ 2⌉₊, le_trans h12_1 (le_max_left _ _), ?_⟩
  intro W' D hW' hpos hUpper hDthr hDlt hκ
  obtain ⟨R₀1, hR₀1⟩ :=
    hfloor W' D hW' hpos hUpper (le_trans (le_max_left _ _) hDthr) hDlt hκ
  have hDk : 12 * (n + 1) ^ 2 ≤ D := le_trans h12_1 (le_trans (le_max_left _ _) hDthr)
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDk
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hL53nn : (0 : ℝ) ≤ lemma53Const := lemma53Const_nonneg
  have h25nn : (0 : ℝ) ≤ 5 * kR * lemma53Const := by positivity
  have hsqbound : (5 * kR * lemma53Const) ^ 2 ≤ (D : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hDthr)
  have hsqD : Real.sqrt D * Real.sqrt D = (D : ℝ) := Real.mul_self_sqrt hDR.le
  have hsqDnn : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsqD_ge : 5 * kR * lemma53Const ≤ Real.sqrt D := by
    rw [← Real.sqrt_sq h25nn]; exact Real.sqrt_le_sqrt hsqbound
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  set κinv : ℝ := (W' : ℝ) / W'.totient with hκinvdef
  have htotpos : 0 < W'.totient := Nat.totient_pos.mpr hpos
  have hW'R : (W' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have htotR : (W'.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr htotpos.ne'
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast htotpos) (by exact_mod_cast hpos)
  have hκinv_pos : 0 < κinv := by
    rw [hκinvdef]; exact div_pos (by exact_mod_cast hpos) (by exact_mod_cast htotpos)
  have hκκinv : κ * κinv = 1 := by
    rw [hκdef, hκinvdef, div_mul_div_comm, mul_comm (W'.totient : ℝ) (W' : ℝ),
      div_self (mul_ne_zero hW'R htotR)]
  obtain ⟨Cpas, hpas⟩ := phiAtom_upper_lossy W' hpos.ne'
  rw [← hκdef] at hpas
  refine ⟨max R₀1 (max 2 ⌈Real.exp (Cpas / κ)⌉₊), ?_⟩
  intro R hR hlogR
  set X : ℝ := κ * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  set ε : ℝ := lemma53Const * kR * Real.log R / D with hεdef
  have hR2 : 2 ≤ R := le_trans (le_trans (le_max_left 2 _) (le_max_right R₀1 _)) hR
  have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le one_pos hlogR
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hlogRpos
  have hXnn : 0 ≤ X := hXpos.le
  have hfl := hR₀1 R (le_trans (le_max_left _ _) hR) hlogR
  rw [← hXdef] at hfl
  have hQeq : Qdiag_mW (n + 1) R W' m (yFg R W' P) = Qdiag_gv (n + 1) R W' m (yFg R W' P) :=
    (Qdiag_mW_eq_s2FullFormM (n + 1) R W' m (yFg R W' P)).trans
      (s2FullFormM_eq_Qdiag (n + 1) R W' m (yFg R W' P))
  rw [hQeq] at hfl
  have hpasR : PAS ≤ 4 * X + Cpas := by
    have h := hpas R hR2; rw [← hXdef, ← hPASdef] at h; linarith [h]
  have hPASnn : 0 ≤ PAS := by
    rw [hPASdef]; unfold Salt.Maynard.phiAtomSum
    exact Finset.sum_nonneg fun r _ => by positivity
  have hεnn : 0 ≤ ε := by
    rw [hεdef]
    exact div_nonneg (mul_nonneg (mul_nonneg hL53nn hkRnn) hlogRpos.le) hDR.le
  have hXCpas : Cpas ≤ X := by
    have hle : Cpas / κ ≤ Real.log R :=
      qfloor_log_ge_of_ceil_exp (Cpas / κ) R
        (le_trans (le_trans (le_max_right 2 _) (le_max_right R₀1 _)) hR)
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  have h5Lκinv : lemma53Const * kR * κinv ≤ (D : ℝ) := by
    calc lemma53Const * kR * κinv
        ≤ lemma53Const * kR * (5 * Real.sqrt D) :=
          mul_le_mul_of_nonneg_left hκ (by positivity)
      _ = 5 * kR * lemma53Const * Real.sqrt D := by ring
      _ ≤ Real.sqrt D * Real.sqrt D := mul_le_mul_of_nonneg_right hsqD_ge hsqDnn
      _ = (D : ℝ) := hsqD
  have hκD : lemma53Const * kR ≤ κ * D := by
    have h := mul_le_mul_of_nonneg_left h5Lκinv hκpos.le
    have he : κ * (lemma53Const * kR * κinv) = lemma53Const * kR := by
      rw [show κ * (lemma53Const * kR * κinv) = lemma53Const * kR * (κ * κinv) by ring,
        hκκinv, mul_one]
    rw [he] at h; exact h
  have hεX : ε ≤ X := by
    rw [hεdef, hXdef, div_le_iff₀ hDR]
    nlinarith [mul_le_mul_of_nonneg_left hκD hlogRpos.le]
  have hPASε : PAS + ε ≤ 6 * X := by linarith [hpasR, hεX, hXCpas]
  have h2PAS : 2 * PAS ≤ 10 * X := by linarith [hpasR, hXCpas]
  have hsq : (PAS + ε) ^ 2 ≤ (6 * X) ^ 2 :=
    pow_le_pow_left₀ (by linarith [hPASnn, hεnn]) hPASε 2
  have hqn : (2 * PAS) ^ n ≤ (10 * X) ^ n :=
    pow_le_pow_left₀ (by linarith [hPASnn]) h2PAS n
  have hLHS : (PAS + ε) ^ 2 * (2 * PAS) ^ n ≤ (6 * X) ^ 2 * (10 * X) ^ n :=
    mul_le_mul hsq hqn (by positivity) (by positivity)
  have hpowX : (6 * X) ^ 2 * (10 * X) ^ n = 36 * K10 * X ^ (n + 2) := by
    rw [mul_pow, mul_pow, hK10, pow_add]; ring
  generalize hXPdef : X ^ (n + 2) = XP at hpowX hfl
  have hCFval : (72 * K10 / J) * (XP * J / 2) = 36 * K10 * XP := by
    field_simp; ring
  calc (PAS + ε) ^ 2 * (2 * PAS) ^ n
      ≤ (6 * X) ^ 2 * (10 * X) ^ n := hLHS
    _ = 36 * K10 * XP := hpowX
    _ = (72 * K10 / J) * (XP * J / 2) := hCFval.symm
    _ ≤ (72 * K10 / J) * Qdiag_gv (n + 1) R W' m (yFg R W' P) :=
        mul_le_mul_of_nonneg_left hfl (div_nonneg (by positivity) hJpos.le)

/-- **`s2_collision_yF_C` at general `k` for any weight `y`.** -/
theorem s2_collision_y_C_gen (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) (CF : ℝ)
    (hCF : 0 ≤ CF) (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hk : 1 ≤ k)
    (hDk : 48 * k ^ 2 ≤ D) (hInner : S2InnerBoundQC k R W' m y CF) :
    |Qdiag_mW k R W' m y - s2CompatFormM k R W' m y|
      ≤ (4 * Cs * CF * (k : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW k R W' m y := by
  have hfull : Qdiag_mW k R W' m y = s2FullFormM k R W' m y :=
    Qdiag_mW_eq_s2FullFormM k R W' m y
  have hgv : s2FullFormM k R W' m y = Qdiag_gv k R W' m y :=
    s2FullFormM_eq_Qdiag k R W' m y
  have hcompat : s2CompatFormM k R W' m y
      = s2FullFormM k R W' m y - s2CollisionForm k R W' m y :=
    s2_compat_eq_M k R W' m y
  have hcoll := s2_collision_le_QdiagW_C k R W' D m y CF hCF hInner hDlt hk hDk
  have hdiff : Qdiag_mW k R W' m y - s2CompatFormM k R W' m y
      = s2CollisionForm k R W' m y := by rw [hcompat, hfull]; ring
  have hQeq : Qdiag_mW k R W' m y = Qdiag_gv k R W' m y := hfull.trans hgv
  rw [hdiff, hQeq]
  exact hcoll

/-- **(3) The pointwise S₂ collision closure at general `n`.** -/
theorem s2_collision_floor_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hy1 : ∀ R W' : ℕ, ∀ s, |yFg R W' P s| ≤ 1)
    (hJ : 0 < ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 12 * (n + 1) ^ 2 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) → 48 * (n + 1) ^ 2 ≤ D →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW (n + 1) R W' m (yFg R W' P) - s2CompatFormM (n + 1) R W' m (yFg R W' P)|
          ≤ (4 * Cs * CF * ((n + 1 : ℕ) : ℝ) ^ 2 / (D : ℝ))
              * Qdiag_mW (n + 1) R W' m (yFg R W' P) := by
  obtain ⟨CF, hCF, Dthr, h12, hcmp⟩ := qdiag_cmp_gen n hn P m hy1 hJ
  refine ⟨CF, hCF, Dthr, h12, ?_⟩
  intro W' D hW' hpos hUpper hDthr hDlt hκ hDk
  obtain ⟨R₀, hR₀⟩ := hcmp W' D hW' hpos hUpper hDthr hDlt hκ
  refine ⟨max R₀ 2, ?_⟩
  intro R hR hlogR
  have hR2 : 2 ≤ R := le_trans (le_max_right R₀ 2) hR
  have hqd := hR₀ R (le_trans (le_max_left R₀ 2) hR) hlogR
  have hD12 : 12 * (n + 1) ^ 2 ≤ D := le_trans h12 hDthr
  have hysupp : ∀ s, s ∉ kSieveIndex (n + 1) R W' → yFg R W' P s = 0 := by
    intro s hs; unfold yFg; rw [if_neg hs]
  have hInner : S2InnerBoundQC (n + 1) R W' m (yFg R W' P) CF :=
    s2_inner_y_gen (n + 1) R W' D m (yFg R W' P) (hy1 R W') hysupp hR2 hW' hpos hDlt hD12
      CF hqd
  exact s2_collision_y_C_gen (n + 1) R W' D m (yFg R W' P) CF hCF hDlt (by omega) hDk hInner

/-! ## The k = 105 instances (`n = 104`, `P = F1`) -/

/-- `J1 = simplexInt (sq (contractB m F1)) = Jform/Qsum² > 0`. -/
theorem J1_pos (m : Fin 105) : 0 < ((simplexInt (sq (contractB m F1)) : ℚ) : ℝ) := by
  have hJform : (0 : ℚ) < Jform := by
    have h1 := ratio_cert_105
    have h2 := Iform_pos
    nlinarith
  have hQ : (0 : ℚ) < Qsum ^ 2 := pow_pos Qsum_pos 2
  have : (0 : ℚ) < simplexInt (sq (contractB m F1)) := by
    rw [simplexInt_sq_contractB_F1 m]; exact div_pos hJform hQ
  exact_mod_cast this

/-- The `Qdiag` floor at `k = 105`, coordinate `m`: a threshold `Dthr ≥ 12·105²` such that for
squarefree `W' > 0` with `PhiUpperAtom W'`, `D ≥ Dthr` below every prime `p ∤ W'`, and `W'/φ(W')
≤ 5√D`, from some `R₀` on (with `log R ≥ 1`), `(φ(W')/W' · log R)^{106} · simplexInt (sq
(contractB m F1)) / 2 ≤ Qdiag_mW 105 R W' m (yFg R W' F1)`. `qdiag_floor_gen` at `n = 104`, `P =
F1`, closed by `J1_pos`.
-/
theorem qdiag_floor_105 (m : Fin 105) :
    ∃ Dthr : ℕ, 12 * 105 ^ 2 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        ((W'.totient : ℝ) / W' * Real.log R) ^ 106
            * ((simplexInt (sq (contractB m F1)) : ℚ) : ℝ) / 2
          ≤ Qdiag_mW 105 R W' m (yFg R W' F1) :=
  qdiag_floor_gen 104 (by norm_num) F1 m yFg_F1_abs_le_one (J1_pos m)

/-- The `hQd` payload at `k = 105`, coordinate `m`: a `CF ≥ 0` and a threshold `Dthr ≥ 12·105²` such
that for squarefree `W' > 0` with `PhiUpperAtom W'`, `D ≥ Dthr` below every prime `p ∤ W'`, and
`W'/φ(W') ≤ 5√D`, from some `R₀` on (with `log R ≥ 1`), `(phiAtomSum R W' + lemma53Const · 105 ·
log R / D)² · (2 · phiAtomSum R W')^{104} ≤ CF · Qdiag_gv 105 R W' m (yFg R W' F1)`.
-/
theorem qdiag_cmp_105 (m : Fin 105) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 12 * 105 ^ 2 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        (Salt.Maynard.phiAtomSum R W' + lemma53Const * 105 * Real.log R / D) ^ 2
            * (2 * Salt.Maynard.phiAtomSum R W') ^ 104
          ≤ CF * Qdiag_gv 105 R W' m (yFg R W' F1) := by
  have h := qdiag_cmp_gen 104 (by norm_num) F1 m yFg_F1_abs_le_one (J1_pos m)
  have hc : ((104 + 1 : ℕ) : ℝ) = 105 := by norm_num
  rw [hc] at h
  exact h

/-- The S₂ collision floor at `k = 105`, coordinate `m`: a `CF ≥ 0` and a threshold `Dthr ≥ 12·105²`
such that under the same hypotheses as `qdiag_cmp_105` and `D ≥ 48·105²`, from some `R₀` on,
`|Qdiag_mW 105 R W' m (yFg R W' F1) − s2CompatFormM 105 R W' m (yFg R W' F1)| ≤ (4 · Cs · CF ·
105² / D) · Qdiag_mW 105 R W' m (yFg R W' F1)`.
-/
theorem s2_collision_floor_105 (m : Fin 105) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 12 * 105 ^ 2 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) → 48 * 105 ^ 2 ≤ D →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1)|
          ≤ (4 * Cs * CF * (105 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 105 R W' m (yFg R W' F1) := by
  have h := s2_collision_floor_gen 104 (by norm_num) F1 m yFg_F1_abs_le_one (J1_pos m)
  have hc : ((104 + 1 : ℕ) : ℝ) = 105 := by norm_num
  rw [hc] at h
  exact h

end Salt.MaynardK

