/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.GapsFinal
import Salt.Twelve.JcalPos
import Salt.Maynard.PhiAtom

/-!
# Rung 4a — R1b — the `Qdiag` floor and pointwise S₂ collision closure

Design: `docs/blueprints/explicit12-design.md`, endgame; `flags.md` 2026-07-11
Fable review, item 2 (the BYPASS-`hQd`, work-POINTWISE route).

The rung's endgame needs the S₂ collision bound at large-`D` primorial-type
moduli.  The packaging lemma `s2_inner_yF` demands a universally-quantified
`hQd` whose comparison must reach down to `D = 300` — undischargeable with the
landed `κ⁻¹ ≤ 5√D`.  Here we BYPASS `hQd` with an EXISTENTIAL `D`-threshold and
thread the estimates POINTWISE, in three layers:

1. `qdiag_floor` — `X⁶·J/2 ≤ Qdiag_mW` for all large `R`, `D` (from
   `qdiag_bridge`, the tie `simplexInt (sq (contractAt m Fstar1)) = Jcal m Fstar1`,
   the explicit `Jcal_Fstar1_eq`, and the lossy `phiAtom_upper_lossy`).
2. `qdiag_cmp` — the `hQd` payload at large `D`:
   `(PAS+ε)²·(2·PAS)⁴ ≤ CF·Qdiag_gv`, `CF = 720000/J` a closed rational.
3. `s2_collision_floor` — composed via `s2_inner_termwise` → `S2InnerBoundQC` →
   `s2_collision_yF_C`, the `Qdiag`-relative bound R2b consumes.

## Quantifier discipline (the project's recurring trap)

Every constant is produced BEFORE `W'` is quantified: `∃ CF Dthr, ∀ W' D, …`.
`qdiag_bridge`'s `A` is obtained first; `Dthr` is built from `A` and the fixed
`J`; the `W'`-dependent junk (`phiAtom_upper_lossy`'s `C_{W'}`, `qdiag_bridge`'s
per-`(W',D)` `c`) is absorbed into `R₀`, which is chosen AFTER `W'`.  The
`κ⁻¹ ≤ 5√D` hypothesis converts every `κ`-dependence into a `√D` bound, keeping
the `D`-thresholds `W'`-uniform.
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-- From `⌈exp L⌉₊ ≤ R` conclude `L ≤ log R`: cast, then `log`-monotonicity. -/
private lemma log_ge_of_ceil_exp (L : ℝ) (R : ℕ) (hR : ⌈Real.exp L⌉₊ ≤ R) :
    L ≤ Real.log R := by
  have hpos : (0 : ℝ) < Real.exp L := Real.exp_pos L
  have h1 : Real.exp L ≤ (⌈Real.exp L⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈Real.exp L⌉₊ : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
    _ ≤ Real.log R := Real.log_le_log hpos (le_trans h1 h2)

/-- **Layer (1) — the `Qdiag` floor.**  For every large `R`, `D`, the sharp S₂
diagonal `Qdiag_mW` sits above half its polynomial main term `X⁶·J`
(`X = (φW'/W')·log R`, `J = Jcal m Fstar1`).  The three `qdiag_bridge` error
terms (`c·(1+X)⁶/log R`, `A·κ⁻¹·Y⁶/D`, `A·κ⁻²·Y⁶/D²`) are each driven below
`X⁶·J/6`: the `1/log R` term via `R₀`, the `1/√D`/`1/D` terms via `Dthr` (built
from the pre-`W'` constant `A`), using `κ⁻¹ ≤ 5√D` and `Y ≤ 6X`. -/
theorem qdiag_floor (m : Fin 5) :
    ∃ Dthr : ℕ, 300 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        ((W'.totient : ℝ) / W' * Real.log R) ^ 6 * ((Jcal m Fstar1 : ℚ) : ℝ) / 2
          ≤ Qdiag_mW 5 R W' m (yF R W' Fstar1) := by
  obtain ⟨A, hA0, hbridge⟩ := qdiag_bridge Fstar1 m (le_of_eq Qabs_Fstar1)
  set J : ℝ := ((Jcal m Fstar1 : ℚ) : ℝ) with hJdef
  have hJpos : 0 < J := by rw [hJdef]; exact_mod_cast Jcal_Fstar1_pos m
  refine ⟨max 300 ⌈(30 * 6 ^ 6 * A / J) ^ 2 + 150 * 6 ^ 6 * A / J⌉₊,
    le_max_left _ _, ?_⟩
  intro W' D hW' hpos hUpper hDthr hDlt hκ
  -- basic `D` facts
  have hD300 : 300 ≤ D := le_trans (le_max_left _ _) hDthr
  have hDpos : 0 < D := by omega
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  -- threshold extraction from `Dthr ≤ D`
  have hM2nn : (0 : ℝ) ≤ 30 * 6 ^ 6 * A / J :=
    div_nonneg (mul_nonneg (by norm_num) hA0) hJpos.le
  have hM3nn : (0 : ℝ) ≤ 150 * 6 ^ 6 * A / J :=
    div_nonneg (mul_nonneg (by norm_num) hA0) hJpos.le
  have hTleD : (30 * 6 ^ 6 * A / J) ^ 2 + 150 * 6 ^ 6 * A / J ≤ (D : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hDthr)
  have hDge_sq : (30 * 6 ^ 6 * A / J) ^ 2 ≤ (D : ℝ) := by linarith [hM3nn, hTleD]
  have hM3leD : 150 * 6 ^ 6 * A / J ≤ (D : ℝ) := by
    linarith [sq_nonneg (30 * 6 ^ 6 * A / J), hTleD]
  -- sqrt facts
  have hsqD : Real.sqrt D * Real.sqrt D = (D : ℝ) := Real.mul_self_sqrt hDR.le
  have hsqDnn : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsqDpos : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hDR
  have hsqD_ge : 30 * 6 ^ 6 * A / J ≤ Real.sqrt D := by
    rw [← Real.sqrt_sq hM2nn]; exact Real.sqrt_le_sqrt hDge_sq
  have hJsD : 30 * 6 ^ 6 * A ≤ Real.sqrt D * J := (div_le_iff₀ hJpos).mp hsqD_ge
  have hDJ : 150 * 6 ^ 6 * A ≤ (D : ℝ) * J := (div_le_iff₀ hJpos).mp hM3leD
  -- specialize the bridge, then package `κ`
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
  -- `R₀` from the per-`(W',D)` `c`, the `W'`-junk `Cpas`, and the fixed `J`
  set L : ℝ := max (max ((1 + Cpas) / κ) (1 / κ)) (384 * c / J) with hLdef
  refine ⟨max 2 ⌈Real.exp L⌉₊, ?_⟩
  intro R hR hlogR
  set X : ℝ := κ * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le one_pos hlogR
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hlogRpos
  have hXnn : 0 ≤ X := hXpos.le
  have hX6pos : 0 < X ^ 6 := pow_pos hXpos 6
  have hX6nn : 0 ≤ X ^ 6 := hX6pos.le
  have hLlogR : L ≤ Real.log R := log_ge_of_ceil_exp L R (le_trans (le_max_right _ _) hR)
  -- unpack the `L`-threshold
  have h1Cpas : 1 + Cpas ≤ X := by
    have hle : (1 + Cpas) / κ ≤ Real.log R :=
      le_trans (by rw [hLdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)) hLlogR
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  have h1X : (1 : ℝ) ≤ X := by
    have hle : (1 : ℝ) / κ ≤ Real.log R :=
      le_trans (by rw [hLdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)) hLlogR
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  have hclog : 384 * c / J ≤ Real.log R :=
    le_trans (by rw [hLdef]; exact le_max_right _ _) hLlogR
  -- the lossy PAS bound at `R`
  have hpasR : PAS ≤ 4 * X + Cpas := by
    have h := hpas R hR2
    rw [← hXdef, ← hPASdef] at h; linarith [h]
  have hPASnn : 0 ≤ PAS := by
    rw [hPASdef]; unfold Salt.Maynard.phiAtomSum
    exact Finset.sum_nonneg fun r _ => by positivity
  -- `Y = 1 + X + PAS ≤ 6X`, hence `Y⁶ ≤ 6⁶·X⁶`; and `(1+X)⁶ ≤ 2⁶·X⁶`
  have hYnn : (0 : ℝ) ≤ 1 + X + PAS := by linarith
  have hY6X : 1 + X + PAS ≤ 6 * X := by linarith [hpasR, h1Cpas]
  have hY6 : (1 + X + PAS) ^ 6 ≤ 6 ^ 6 * X ^ 6 := by
    calc (1 + X + PAS) ^ 6 ≤ (6 * X) ^ 6 := pow_le_pow_left₀ hYnn hY6X 6
      _ = 6 ^ 6 * X ^ 6 := by rw [mul_pow]
  have h1X6 : (1 + X) ^ 6 ≤ 2 ^ 6 * X ^ 6 := by
    calc (1 + X) ^ 6 ≤ (2 * X) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = 2 ^ 6 * X ^ 6 := by rw [mul_pow]
  -- the three error-term bounds, each `≤ X⁶·J/6`
  have hbnd1 : c * (1 + X) ^ 6 / Real.log R ≤ X ^ 6 * J / 6 := by
    rw [div_le_iff₀ hlogRpos]
    have h384 : 384 * c ≤ Real.log R * J := (div_le_iff₀ hJpos).mp hclog
    calc c * (1 + X) ^ 6
        ≤ c * (2 ^ 6 * X ^ 6) := mul_le_mul_of_nonneg_left h1X6 hc0
      _ = 64 * c * X ^ 6 := by ring
      _ ≤ Real.log R * J / 6 * X ^ 6 :=
          mul_le_mul_of_nonneg_right (by linarith [h384]) hX6nn
      _ = X ^ 6 * J / 6 * Real.log R := by ring
  have hbnd2 : A * κinv * (1 + X + PAS) ^ 6 / (D : ℝ) ≤ X ^ 6 * J / 6 := by
    rw [div_le_iff₀ hDR]
    have hc1 : A * κinv * (1 + X + PAS) ^ 6 ≤ A * κinv * (6 ^ 6 * X ^ 6) :=
      mul_le_mul_of_nonneg_left hY6 (mul_nonneg hA0 hκinv_pos.le)
    have hc2 : A * κinv * (6 ^ 6 * X ^ 6) ≤ A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ hA0)
        (mul_nonneg (by norm_num) hX6nn)
    have hc3 : A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6) ≤ X ^ 6 * J / 6 * (D : ℝ) := by
      have hstep : (30 * 6 ^ 6 * A) * (X ^ 6 * Real.sqrt D / 6)
          ≤ (Real.sqrt D * J) * (X ^ 6 * Real.sqrt D / 6) :=
        mul_le_mul_of_nonneg_right hJsD (by positivity)
      calc A * (5 * Real.sqrt D) * (6 ^ 6 * X ^ 6)
          = (30 * 6 ^ 6 * A) * (X ^ 6 * Real.sqrt D / 6) := by ring
        _ ≤ (Real.sqrt D * J) * (X ^ 6 * Real.sqrt D / 6) := hstep
        _ = X ^ 6 * J / 6 * (Real.sqrt D * Real.sqrt D) := by ring
        _ = X ^ 6 * J / 6 * (D : ℝ) := by rw [hsqD]
    linarith [hc1, hc2, hc3]
  have hbnd3 : A * κinv ^ 2 * (1 + X + PAS) ^ 6 / (D : ℝ) ^ 2 ≤ X ^ 6 * J / 6 := by
    rw [div_le_iff₀ (pow_pos hDR 2)]
    have hκinv2 : κinv ^ 2 ≤ 25 * (D : ℝ) := by
      have hfac : (0 : ℝ) ≤ (5 * Real.sqrt D - κinv) * (5 * Real.sqrt D + κinv) :=
        mul_nonneg (sub_nonneg.mpr hκ) (by linarith [hsqDnn, hκinv_pos.le])
      have heq : (5 * Real.sqrt D - κinv) * (5 * Real.sqrt D + κinv)
          = 25 * (Real.sqrt D * Real.sqrt D) - κinv ^ 2 := by ring
      rw [hsqD] at heq
      rw [heq] at hfac
      linarith [hfac]
    have hc1 : A * κinv ^ 2 * (1 + X + PAS) ^ 6 ≤ A * κinv ^ 2 * (6 ^ 6 * X ^ 6) :=
      mul_le_mul_of_nonneg_left hY6 (mul_nonneg hA0 (sq_nonneg _))
    have hc2 : A * κinv ^ 2 * (6 ^ 6 * X ^ 6) ≤ A * (25 * (D : ℝ)) * (6 ^ 6 * X ^ 6) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκinv2 hA0)
        (mul_nonneg (by norm_num) hX6nn)
    have hc3 : A * (25 * (D : ℝ)) * (6 ^ 6 * X ^ 6) ≤ X ^ 6 * J / 6 * (D : ℝ) ^ 2 := by
      have hstep : (150 * 6 ^ 6 * A) * (X ^ 6 * (D : ℝ) / 6)
          ≤ ((D : ℝ) * J) * (X ^ 6 * (D : ℝ) / 6) :=
        mul_le_mul_of_nonneg_right hDJ (by positivity)
      calc A * (25 * (D : ℝ)) * (6 ^ 6 * X ^ 6)
          = (150 * 6 ^ 6 * A) * (X ^ 6 * (D : ℝ) / 6) := by ring
        _ ≤ ((D : ℝ) * J) * (X ^ 6 * (D : ℝ) / 6) := hstep
        _ = X ^ 6 * J / 6 * (D : ℝ) ^ 2 := by ring
    linarith [hc1, hc2, hc3]
  -- assemble via `qdiag_bridge`
  have hb2 := hb R hR2 hlogR
  have htie : ((simplexInt (sq (contractAt m Fstar1)) : ℚ) : ℝ) = J := by
    rw [hJdef]; exact_mod_cast simplexInt_sq_contractAt_eq_Jcal m Fstar1
  rw [← hXdef, ← hPASdef, htie] at hb2
  linarith [(abs_le.mp hb2).1, hbnd1, hbnd2, hbnd3]

/-- **Layer (2) — the pointwise `hQd` payload at large `D`.**  The comparison
`s2_inner_yF` universally quantifies as `hQd`, dischargeable POINTWISE:
`(PAS+ε)²·(2·PAS)⁴ ≤ CF·Qdiag_gv` for large `R`, `D`, with the CLOSED rational
`CF = 720000/J`.  From `qdiag_floor` (`Qdiag_gv ≥ X⁶·J/2`) plus the lossy PAS
bound and `ε ≤ X` (via `κ⁻¹ ≤ 5√D`, `√D ≥ 25·lemma53Const`), the LHS is
`≤ (6X)²·(10X)⁴ = 360000·X⁶ = CF·X⁶·J/2 ≤ CF·Qdiag_gv`. -/
theorem qdiag_cmp (m : Fin 5) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 300 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        (Salt.Maynard.phiAtomSum R W' + lemma53Const * 5 * Real.log R / D) ^ 2
            * (2 * Salt.Maynard.phiAtomSum R W') ^ 4
          ≤ CF * Qdiag_gv 5 R W' m (yF R W' Fstar1) := by
  obtain ⟨Dthr1, h300_1, hfloor⟩ := qdiag_floor m
  set J : ℝ := ((Jcal m Fstar1 : ℚ) : ℝ) with hJdef
  have hJpos : 0 < J := by rw [hJdef]; exact_mod_cast Jcal_Fstar1_pos m
  refine ⟨720000 / J, div_nonneg (by norm_num) hJpos.le,
    max Dthr1 ⌈(25 * lemma53Const) ^ 2⌉₊, le_trans h300_1 (le_max_left _ _), ?_⟩
  intro W' D hW' hpos hUpper hDthr hDlt hκ
  obtain ⟨R₀1, hR₀1⟩ :=
    hfloor W' D hW' hpos hUpper (le_trans (le_max_left _ _) hDthr) hDlt hκ
  -- `D` facts and the `ε`-threshold `√D ≥ 25·lemma53Const`
  have hD300 : 300 ≤ D := le_trans h300_1 (le_trans (le_max_left _ _) hDthr)
  have hDpos : 0 < D := by omega
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hL53nn : (0 : ℝ) ≤ lemma53Const := lemma53Const_nonneg
  have h25nn : (0 : ℝ) ≤ 25 * lemma53Const := by positivity
  have hsqbound : (25 * lemma53Const) ^ 2 ≤ (D : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hDthr)
  have hsqD : Real.sqrt D * Real.sqrt D = (D : ℝ) := Real.mul_self_sqrt hDR.le
  have hsqDnn : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsqD_ge : 25 * lemma53Const ≤ Real.sqrt D := by
    rw [← Real.sqrt_sq h25nn]; exact Real.sqrt_le_sqrt hsqbound
  -- package `κ`, `κ⁻¹` (with `κ·κ⁻¹ = 1`) and the lossy PAS bound
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
  set ε : ℝ := lemma53Const * 5 * Real.log R / D with hεdef
  have hR2 : 2 ≤ R := le_trans (le_trans (le_max_left 2 _) (le_max_right R₀1 _)) hR
  have hlogRpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le one_pos hlogR
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hlogRpos
  have hX6nn : 0 ≤ X ^ 6 := (pow_pos hXpos 6).le
  -- floor: `Qdiag_gv ≥ X⁶·J/2`
  have hfl := hR₀1 R (le_trans (le_max_left _ _) hR) hlogR
  rw [← hXdef] at hfl
  have hQeq : Qdiag_mW 5 R W' m (yF R W' Fstar1) = Qdiag_gv 5 R W' m (yF R W' Fstar1) :=
    (Qdiag_mW_eq_s2FullFormM 5 R W' m (yF R W' Fstar1)).trans
      (s2FullFormM_eq_Qdiag 5 R W' m (yF R W' Fstar1))
  rw [hQeq] at hfl
  -- lossy PAS bound, `X ≥ Cpas`, and `ε ≤ X`
  have hpasR : PAS ≤ 4 * X + Cpas := by
    have h := hpas R hR2; rw [← hXdef, ← hPASdef] at h; linarith [h]
  have hPASnn : 0 ≤ PAS := by
    rw [hPASdef]; unfold Salt.Maynard.phiAtomSum
    exact Finset.sum_nonneg fun r _ => by positivity
  have hεnn : 0 ≤ ε := by
    rw [hεdef]
    exact div_nonneg (mul_nonneg (mul_nonneg hL53nn (by norm_num)) hlogRpos.le) hDR.le
  have hXCpas : Cpas ≤ X := by
    have hle : Cpas / κ ≤ Real.log R :=
      log_ge_of_ceil_exp (Cpas / κ) R
        (le_trans (le_trans (le_max_right 2 _) (le_max_right R₀1 _)) hR)
    rw [hXdef, mul_comm]; exact (div_le_iff₀ hκpos).mp hle
  -- `ε ≤ X`: `5·L53·κ⁻¹ ≤ D`, then `5·L53 ≤ κ·D`, then clear `log R`
  have h5Lκinv : 5 * lemma53Const * κinv ≤ (D : ℝ) := by
    calc 5 * lemma53Const * κinv
        ≤ 5 * lemma53Const * (5 * Real.sqrt D) :=
          mul_le_mul_of_nonneg_left hκ (by positivity)
      _ = 25 * lemma53Const * Real.sqrt D := by ring
      _ ≤ Real.sqrt D * Real.sqrt D := mul_le_mul_of_nonneg_right hsqD_ge hsqDnn
      _ = (D : ℝ) := hsqD
  have hκD : 5 * lemma53Const ≤ κ * D := by
    have h := mul_le_mul_of_nonneg_left h5Lκinv hκpos.le
    have he : κ * (5 * lemma53Const * κinv) = 5 * lemma53Const := by
      rw [show κ * (5 * lemma53Const * κinv) = 5 * lemma53Const * (κ * κinv) by ring,
        hκκinv, mul_one]
    rw [he] at h; exact h
  have hεX : ε ≤ X := by
    rw [hεdef, hXdef, div_le_iff₀ hDR]
    nlinarith [mul_le_mul_of_nonneg_left hκD hlogRpos.le]
  -- LHS ≤ (6X)²·(10X)⁴ = 360000·X⁶
  have hPASε : PAS + ε ≤ 6 * X := by linarith [hpasR, hεX, hXCpas]
  have h2PAS : 2 * PAS ≤ 10 * X := by linarith [hpasR, hXCpas]
  have hsq : (PAS + ε) ^ 2 ≤ (6 * X) ^ 2 :=
    pow_le_pow_left₀ (by linarith [hPASnn, hεnn]) hPASε 2
  have hq4 : (2 * PAS) ^ 4 ≤ (10 * X) ^ 4 :=
    pow_le_pow_left₀ (by linarith [hPASnn]) h2PAS 4
  have hLHS : (PAS + ε) ^ 2 * (2 * PAS) ^ 4 ≤ (6 * X) ^ 2 * (10 * X) ^ 4 :=
    mul_le_mul hsq hq4 (by positivity) (by positivity)
  have hCFval : (720000 / J) * (X ^ 6 * J / 2) = 360000 * X ^ 6 := by
    field_simp; ring
  calc (PAS + ε) ^ 2 * (2 * PAS) ^ 4
      ≤ (6 * X) ^ 2 * (10 * X) ^ 4 := hLHS
    _ = 360000 * X ^ 6 := by ring
    _ = (720000 / J) * (X ^ 6 * J / 2) := hCFval.symm
    _ ≤ (720000 / J) * Qdiag_gv 5 R W' m (yF R W' Fstar1) :=
        mul_le_mul_of_nonneg_left hfl (div_nonneg (by norm_num) hJpos.le)

/-- **Layer (3) — the pointwise S₂ collision closure (what R2b consumes).**
Compose `qdiag_cmp` (the `hQd` payload) through the PUBLIC pointwise
`s2_inner_termwise` into the atom `S2InnerBoundQC`, then feed the pointwise
`s2_collision_yF_C` (mirrors `s2_inner_yF`'s 15-line body).  Yields the
`Qdiag`-relative S₂ collision bound at the point. -/
theorem s2_collision_floor (m : Fin 5) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 300 ≤ Dthr ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) → 48 * 5 ^ 2 ≤ D →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1)|
          ≤ (4 * Cs * CF * (5 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 5 R W' m (yF R W' Fstar1) := by
  obtain ⟨CF, hCF, Dthr, h300, hcmp⟩ := qdiag_cmp m
  refine ⟨CF, hCF, Dthr, h300, ?_⟩
  intro W' D hW' hpos hUpper hDthr hDlt hκ hDk
  obtain ⟨R₀, hR₀⟩ := hcmp W' D hW' hpos hUpper hDthr hDlt hκ
  refine ⟨max R₀ 2, ?_⟩
  intro R hR hlogR
  have hR2 : 2 ≤ R := le_trans (le_max_right R₀ 2) hR
  have hqd := hR₀ R (le_trans (le_max_left R₀ 2) hR) hlogR
  have hD300 : 300 ≤ D := le_trans h300 hDthr
  have hInner : S2InnerBoundQC 5 R W' m (yF R W' Fstar1) CF := by
    intro s hs α hα
    have htw := s2_inner_termwise Fstar1 m (le_of_eq Qabs_Fstar1) R W' D hR2 hW' hpos
      hDlt hD300 hs α hα
    refine le_trans htw ?_
    have hA : (0 : ℝ) ≤ 3 ^ s.primeFactors.card
        * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2) := by positivity
    have hreassoc : 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2) * CF
            * Qdiag_gv 5 R W' m (yF R W' Fstar1)
        = (3 ^ s.primeFactors.card * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2))
            * (CF * Qdiag_gv 5 R W' m (yF R W' Fstar1)) := by ring
    rw [hreassoc]
    exact mul_le_mul_of_nonneg_left hqd hA
  exact s2_collision_yF_C R W' D m Fstar1 CF hCF hDlt hDk hInner

end Salt.Twelve
