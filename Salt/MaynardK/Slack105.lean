/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.WinCore105
import Salt.MaynardK.QFloor
import Salt.MaynardK.SlackRho
import Salt.MaynardK.ISplit
import Salt.MaynardK.Ratio

/-!
# B4.5c — the slack discharge at k = 105 (C1)

`winSlackM105_ev`: there is an (existential) cutoff `D₀ ≥ 744` such that for every `D ≥ D₀`
and every `C₀ ≥ 0`, the M-based ratio slack `WinSlackM105 D C₀ N'` holds for all large `N'`.
Mirror of `Salt/Twelve/GapsUncond.lean`'s `winSlackM_ev` (k = 5) with window exponent `9999/40000`,
level `1/2`, `c_DL = 15746/1000`, `ε = 1/1000`, `h_max ≤ 743` (the hypothesis `hle` — the module is
generic in the tuple, `TupleChoice`), weight `F1`, certificate `ratio_cert_105`.

The per-`N'` arithmetic is isolated in `slack_closure_105`, a lemma over real atoms, so no
k = 105 power of a sum is ever expanded. `winFrontierMW105_all` composes the result with
`winFrontierMW105_of`. Nothing here bears on twin primes.
-/

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Finset Filter
open Salt.Maynard Salt.Twelve Salt.MaynardK

/-! ## The constant-one budget polynomial on 105 variables -/

/-- the constant `1` as a `BPoly 105` (one monomial, all exponents 0, budget power 0). -/
def one105 : BPoly 105 := [(0, 0, 1)]

omit [Salt.Maynard.TupleChoice] in
lemma eval_one105 (t : Fin 105 → ℝ) : eval one105 t = 1 := by
  simp [eval, one105]

omit [Salt.Maynard.TupleChoice] in
lemma simplexInt_one105_nonneg : (0 : ℝ) ≤ ((simplexInt one105 : ℚ) : ℝ) := by
  have h : (0 : ℚ) ≤ simplexInt one105 := by
    simp only [simplexInt, one105, DInt', List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, one_mul]
    positivity
  exact_mod_cast h

omit [Salt.Maynard.TupleChoice] in
lemma pas_nonneg105 (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg fun r _ => by positivity

/-! ## The scalar closure over real atoms -/

set_option maxHeartbeats 4000000 in
-- ~40 named scalar bounds threaded through one linear closure (the template's own budget is 10M).
omit [Salt.Maynard.TupleChoice] in
/-- The per-`N'` arithmetic of `winSlackM_ev` (template lines 656–1050), at k = 105, over
opaque atoms: `Xp = X^105`, `A1X = (1+X)^105`, `APAS = (1+PAS)^105`, `T2 = 2^105`, `S6 = 6^105`,
`P2 = 2^(105+1)`, `T212 = (1+LR)^212`, `L214 = L^214`, `T422 = (1+LR)^422`, `R2 = R^2`,
`Kp = κ^105`, `CsC = 4·Cs·105²`. Seven pieces, each `≤ U/700000`, against the certified
ratio slack `U/100000`. -/
theorem slack_closure_105
    (N' L LR κ X Xp W φ D Ic SJ Mc δ YS MS LAM Smain Scoll C₀ : ℝ)
    (cF AF c1 A1 A1X APAS T2 S6 P2 QEcSum SCFJ Clam R2 T422 T212 L214 Kp CsC : ℝ)
    (hN' : 0 < N') (hL : 0 < L) (hLR1 : 1 ≤ LR) (hLRleL : LR ≤ L)
    (hκ : 0 < κ) (hW : 0 < W) (hφeq : κ * W = φ) (hD1 : 1 ≤ D)
    (hX : X = κ * LR) (hXp : 0 < Xp) (hKp : Kp ≤ Xp)
    (hIc : 0 < Ic) (hcert : (40015 : ℝ) * Ic < 10000 * SJ)
    (hδdef : δ = (63 - 1 / 1000) * N' / L - 743)
    (hDL : (15746 : ℝ) / 1000 * N' ≤ δ * LR)
    (hYS : YS ≤ Xp * Ic + (cF * A1X / LR + AF * APAS / D))
    (hMS : MS ≤ Xp * Mc + (c1 * A1X / LR + A1 * APAS / D))
    (hcF : 0 ≤ cF) (hAF : 0 ≤ AF) (hc1 : 0 ≤ c1) (hA1 : 0 ≤ A1) (_hMc : 0 ≤ Mc)
    (hA1X : A1X ≤ T2 * Xp) (hAPAS : APAS ≤ S6 * Xp)
    (_hT2 : 0 ≤ T2) (hS6 : 0 ≤ S6) (hP2 : 0 ≤ P2)
    (hbuckY : T2 * cF / LR ≤ Ic / 1400000)
    (hbuckM : 12 * (105 : ℝ) ^ 2 / D * T2 * c1 / LR ≤ Ic / 1400000)
    (hybD : S6 * AF * 1400000 / Ic ≤ D)
    (hMbD : 12 * (105 : ℝ) ^ 2 * S6 * A1 * 1400000 / Ic ≤ D)
    (hMmainD : 12 * (105 : ℝ) ^ 2 * Mc * 700000 / Ic ≤ D)
    (hmain_ge : δ * LR * (Xp / W) * SJ - δ * LR * (Xp / W) * QEcSum ≤ Smain)
    (hQEcSum0 : 0 ≤ QEcSum) (hQEcSum : QEcSum ≤ Ic / 700000)
    (hcoll_le : Scoll ≤ 1000 * N' / L / φ * (CsC / D) * (Xp * X) * SCFJ
        + 105 * (C₀ * T212 * N' / L214))
    (hSCFJ0 : 0 ≤ SCFJ) (hCsC0 : 0 ≤ CsC)
    (hcollD : 1000 * CsC * SCFJ * 700000 / (63 * Ic) ≤ D)
    (hLAM : LAM ^ 2 ≤ Clam * R2 * T422)
    (hTRev : P2 * Clam * R2 * T422 ≤ 63 * Kp * Ic / (W * 700000) * N')
    (hHerrev : 105 * C₀ * T212 / L214 ≤ 63 * Kp * Ic / (W * 700000)) :
    (64 - 1) * N' / W * (YS + 12 * (105 : ℝ) ^ 2 / D * MS) + P2 * LAM ^ 2
      < Smain - Scoll := by
  have hDR : (0 : ℝ) < D := by linarith
  have hLRpos : 0 < LR := by linarith
  have hφpos : 0 < φ := by rw [← hφeq]; exact mul_pos hκ hW
  set Base : ℝ := Xp / W with hBasedef
  have hBase0 : 0 < Base := div_pos hXp hW
  set U : ℝ := 63 * N' * Base * Ic with hUdef
  set V : ℝ := δ * LR * Base * SJ with hVdef
  set pqe : ℝ := δ * LR * Base * QEcSum with hpqedef
  set pcoll : ℝ := 1000 * N' / L / φ * (CsC / D) * (Xp * X) * SCFJ with hpcolldef
  set pherr : ℝ := 105 * (C₀ * T212 * N' / L214) with hpherrdef
  set BY : ℝ := cF * A1X / LR + AF * APAS / D with hBYdef
  set BM : ℝ := c1 * A1X / LR + A1 * APAS / D with hBMdef
  set p1 : ℝ := 63 * N' * Base * (12 * (105 : ℝ) ^ 2 * Mc) / D with hp1def
  set p2 : ℝ := 63 * N' / W * BY with hp2def
  set p3 : ℝ := 63 * N' / W * (12 * (105 : ℝ) ^ 2 / D) * BM with hp3def
  set pTR : ℝ := P2 * LAM ^ 2 with hpTRdef
  set Kmain : ℝ := 63 * Kp * Ic / (W * 700000) with hKmaindef
  have hGnn : 0 ≤ 63 * N' * Base := by positivity
  have hcoeffW : 0 ≤ 63 * N' / W := by positivity
  -- δ facts
  have hδub : δ ≤ 63 * N' / L := by
    rw [hδdef]
    have hNL : 0 ≤ N' / L := div_nonneg hN'.le hL.le
    have he : (63 - 1 / 1000) * N' / L = (63 - 1 / 1000) * (N' / L) := by ring
    have he2 : 63 * N' / L = 63 * (N' / L) := by ring
    rw [he, he2]; linarith only [hNL]
  have hδ0 : 0 ≤ δ := by
    by_contra hc
    rw [not_le] at hc
    have hneg : δ * LR < 0 := mul_neg_of_neg_of_pos hc hLRpos
    have hnn : (0 : ℝ) ≤ 15746 / 1000 * N' := by positivity
    linarith only [hDL, hneg, hnn]
  have hδLR : δ * LR ≤ 63 * N' := by
    have h1 : δ * LR ≤ 63 * N' / L * LR := mul_le_mul_of_nonneg_right hδub hLRpos.le
    have h2 : 63 * N' / L * LR ≤ 63 * N' / L * L :=
      mul_le_mul_of_nonneg_left hLRleL (by positivity)
    have h3 : 63 * N' / L * L = 63 * N' := by field_simp
    linarith only [h1, h2, h3.le, h3.ge]
  -- D-derived scalar bounds
  have hbuckYD : S6 * AF / D ≤ Ic / 1400000 := by
    rw [div_le_div_iff₀ hDR (by norm_num)]
    linarith only [(div_le_iff₀ hIc).mp hybD]
  have hDD2 : D ≤ D ^ 2 := by rw [pow_two]; exact le_mul_of_one_le_left hDR.le hD1
  have hbuckMD2 : 12 * (105 : ℝ) ^ 2 / D * (A1 * (S6 * Xp) / D) ≤ Ic / 1400000 * Xp := by
    have hDD : 12 * (105 : ℝ) ^ 2 * S6 * A1 / D ≤ Ic / 1400000 := by
      rw [div_le_div_iff₀ hDR (by norm_num)]
      linarith only [(div_le_iff₀ hIc).mp hMbD]
    have hDsq : 12 * (105 : ℝ) ^ 2 * S6 * A1 / D ^ 2 ≤ 12 * (105 : ℝ) ^ 2 * S6 * A1 / D :=
      div_le_div_of_nonneg_left (by positivity) hDR hDD2
    have hkey : 12 * (105 : ℝ) ^ 2 / D * (A1 * (S6 * Xp) / D)
        = (12 * (105 : ℝ) ^ 2 * S6 * A1 / D ^ 2) * Xp := by ring
    rw [hkey]
    calc (12 * (105 : ℝ) ^ 2 * S6 * A1 / D ^ 2) * Xp
        ≤ (12 * (105 : ℝ) ^ 2 * S6 * A1 / D) * Xp := mul_le_mul_of_nonneg_right hDsq hXp.le
      _ ≤ (Ic / 1400000) * Xp := mul_le_mul_of_nonneg_right hDD hXp.le
  -- bucket bounds
  have hBYbound : BY ≤ Xp * (Ic / 700000) := by
    rw [hBYdef]
    have hb1 : cF * A1X / LR ≤ Ic / 1400000 * Xp := by
      have s1 : cF * A1X / LR ≤ cF * (T2 * Xp) / LR :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA1X hcF) hLRpos.le
      have s2 : cF * (T2 * Xp) / LR = T2 * cF / LR * Xp := by ring
      have s3 : T2 * cF / LR * Xp ≤ Ic / 1400000 * Xp :=
        mul_le_mul_of_nonneg_right hbuckY hXp.le
      linarith only [s1, s2.le, s2.ge, s3]
    have hb2 : AF * APAS / D ≤ Ic / 1400000 * Xp := by
      have s1 : AF * APAS / D ≤ AF * (S6 * Xp) / D :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAPAS hAF) hDR.le
      have s2 : AF * (S6 * Xp) / D = S6 * AF / D * Xp := by ring
      have s3 : S6 * AF / D * Xp ≤ Ic / 1400000 * Xp :=
        mul_le_mul_of_nonneg_right hbuckYD hXp.le
      linarith only [s1, s2.le, s2.ge, s3]
    have he : Xp * (Ic / 700000) = Ic / 1400000 * Xp + Ic / 1400000 * Xp := by ring
    linarith only [hb1, hb2, he.le, he.ge]
  have hBMbound : 12 * (105 : ℝ) ^ 2 / D * BM ≤ Xp * (Ic / 700000) := by
    rw [hBMdef, mul_add]
    have hb1 : 12 * (105 : ℝ) ^ 2 / D * (c1 * A1X / LR) ≤ Ic / 1400000 * Xp := by
      have s1 : 12 * (105 : ℝ) ^ 2 / D * (c1 * A1X / LR)
          ≤ 12 * (105 : ℝ) ^ 2 / D * (c1 * (T2 * Xp) / LR) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA1X hc1) hLRpos.le)
          (by positivity)
      have s2 : 12 * (105 : ℝ) ^ 2 / D * (c1 * (T2 * Xp) / LR)
          = 12 * (105 : ℝ) ^ 2 / D * T2 * c1 / LR * Xp := by ring
      have s3 : 12 * (105 : ℝ) ^ 2 / D * T2 * c1 / LR * Xp ≤ Ic / 1400000 * Xp :=
        mul_le_mul_of_nonneg_right hbuckM hXp.le
      linarith only [s1, s2.le, s2.ge, s3]
    have hb2 : 12 * (105 : ℝ) ^ 2 / D * (A1 * APAS / D) ≤ Ic / 1400000 * Xp := by
      have s1 : 12 * (105 : ℝ) ^ 2 / D * (A1 * APAS / D)
          ≤ 12 * (105 : ℝ) ^ 2 / D * (A1 * (S6 * Xp) / D) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAPAS hA1) hDR.le)
          (by positivity)
      linarith only [s1, hbuckMD2]
    have he : Xp * (Ic / 700000) = Ic / 1400000 * Xp + Ic / 1400000 * Xp := by ring
    linarith only [hb1, hb2, he.le, he.ge]
  -- piece bounds (each ≤ U/700000)
  have hp1 : p1 ≤ U / 700000 := by
    rw [hp1def, hUdef]
    have hcoef : 12 * (105 : ℝ) ^ 2 * Mc / D ≤ Ic / 700000 := by
      rw [div_le_div_iff₀ hDR (by norm_num)]
      linarith only [(div_le_iff₀ hIc).mp hMmainD]
    have h1 : 63 * N' * Base * (12 * (105 : ℝ) ^ 2 * Mc / D) ≤ 63 * N' * Base * (Ic / 700000) :=
      mul_le_mul_of_nonneg_left hcoef hGnn
    have h2 : 63 * N' * Base * (12 * (105 : ℝ) ^ 2 * Mc) / D
        = 63 * N' * Base * (12 * (105 : ℝ) ^ 2 * Mc / D) := by ring
    have h3 : 63 * N' * Base * (Ic / 700000) = 63 * N' * Base * Ic / 700000 := by ring
    linarith only [h1, h2.le, h2.ge, h3.le, h3.ge]
  have hp2 : p2 ≤ U / 700000 := by
    rw [hp2def]
    have h1 : 63 * N' / W * BY ≤ 63 * N' / W * (Xp * (Ic / 700000)) :=
      mul_le_mul_of_nonneg_left hBYbound hcoeffW
    have h2 : 63 * N' / W * (Xp * (Ic / 700000)) = U / 700000 := by
      rw [hUdef, hBasedef]; field_simp
    linarith only [h1, h2.le, h2.ge]
  have hp3 : p3 ≤ U / 700000 := by
    rw [hp3def]
    have h1 : 63 * N' / W * (12 * (105 : ℝ) ^ 2 / D * BM)
        ≤ 63 * N' / W * (Xp * (Ic / 700000)) :=
      mul_le_mul_of_nonneg_left hBMbound hcoeffW
    have h2 : 63 * N' / W * (12 * (105 : ℝ) ^ 2 / D) * BM
        = 63 * N' / W * (12 * (105 : ℝ) ^ 2 / D * BM) := by ring
    have h3 : 63 * N' / W * (Xp * (Ic / 700000)) = U / 700000 := by
      rw [hUdef, hBasedef]; field_simp
    linarith only [h1, h2.le, h2.ge, h3.le, h3.ge]
  have hpqe : pqe ≤ U / 700000 := by
    rw [hpqedef]
    have h1 : δ * LR * Base * QEcSum ≤ 63 * N' * Base * QEcSum := by
      have hmul := mul_le_mul_of_nonneg_right hδLR (mul_nonneg hBase0.le hQEcSum0)
      calc δ * LR * Base * QEcSum = δ * LR * (Base * QEcSum) := by ring
        _ ≤ 63 * N' * (Base * QEcSum) := hmul
        _ = 63 * N' * Base * QEcSum := by ring
    have h2 : 63 * N' * Base * QEcSum ≤ 63 * N' * Base * (Ic / 700000) :=
      mul_le_mul_of_nonneg_left hQEcSum hGnn
    have h3 : 63 * N' * Base * (Ic / 700000) = U / 700000 := by rw [hUdef]; ring
    linarith only [h1, h2, h3.le, h3.ge]
  -- truncation / herr common bound `Kmain·N' ≤ U/700000`
  have hKmainNle : Kmain * N' ≤ U / 700000 := by
    have hUexp : U / 700000 = 63 * N' * Xp * Ic / (W * 700000) := by
      rw [hUdef, hBasedef]; field_simp
    have hKexp : Kmain * N' = 63 * N' * Kp * Ic / (W * 700000) := by
      rw [hKmaindef]; field_simp
    rw [hUexp, hKexp]
    have hab : 63 * N' * Kp * Ic ≤ 63 * N' * Xp * Ic := by
      have h63 : 0 ≤ 63 * N' := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKp h63) hIc.le
    exact div_le_div_of_nonneg_right hab (by positivity)
  -- pcoll bound
  have hpcoll : pcoll ≤ U / 700000 := by
    have hid : pcoll = 1000 * (CsC / D) * SCFJ * Base * (N' * LR / L) := by
      rw [hpcolldef, hBasedef, hX, ← hφeq]; field_simp
    rw [hid]
    have hNLRL : N' * LR / L ≤ N' := by
      rw [div_le_iff₀ hL]
      have hm := mul_le_mul_of_nonneg_left hLRleL hN'.le
      linarith only [hm]
    have hCleft : 0 ≤ 1000 * (CsC / D) * SCFJ * Base := by positivity
    have hstep1 : 1000 * (CsC / D) * SCFJ * Base * (N' * LR / L)
        ≤ 1000 * (CsC / D) * SCFJ * Base * N' :=
      mul_le_mul_of_nonneg_left hNLRL hCleft
    have hcoefbnd : 1000 * (CsC / D) * SCFJ ≤ 63 * Ic / 700000 := by
      have hd := (div_le_iff₀ (by positivity : (0 : ℝ) < 63 * Ic)).mp hcollD
      have he : 1000 * (CsC / D) * SCFJ = 1000 * CsC * SCFJ / D := by ring
      rw [he, div_le_div_iff₀ hDR (by norm_num)]
      linarith only [hd]
    have hstep2 : 1000 * (CsC / D) * SCFJ * Base * N' ≤ 63 * Ic / 700000 * Base * N' :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefbnd hBase0.le) hN'.le
    have hUeq : 63 * Ic / 700000 * Base * N' = U / 700000 := by rw [hUdef]; ring
    linarith only [hstep1, hstep2, hUeq.le, hUeq.ge]
  -- truncation bound
  have hpTR : pTR ≤ U / 700000 := by
    rw [hpTRdef]
    have hstep1 : P2 * LAM ^ 2 ≤ P2 * Clam * R2 * T422 := by
      calc P2 * LAM ^ 2 ≤ P2 * (Clam * R2 * T422) := mul_le_mul_of_nonneg_left hLAM hP2
        _ = P2 * Clam * R2 * T422 := by ring
    linarith only [hstep1, hTRev, hKmainNle]
  -- herr bound
  have hpherr : pherr ≤ U / 700000 := by
    rw [hpherrdef]
    have hid : 105 * (C₀ * T212 * N' / L214) = 105 * C₀ * T212 / L214 * N' := by ring
    rw [hid]
    have h1 : 105 * C₀ * T212 / L214 * N' ≤ Kmain * N' :=
      mul_le_mul_of_nonneg_right hHerrev hN'.le
    linarith only [h1, hKmainNle]
  -- the certified ratio
  have hwin : 63 * N' * (1 + 1 / 100000) * Ic < δ * LR * SJ :=
    win_ratio_core_105 N' δ LR Ic SJ (1 / 100000) hIc hcert hDL hN' (le_refl _)
  have hwin' : U + U / 100000 < V := by
    have heqU : U + U / 100000 = Base * (63 * N' * (1 + 1 / 100000) * Ic) := by
      rw [hUdef]; ring
    have heqV : V = Base * (δ * LR * SJ) := by rw [hVdef]; ring
    rw [heqU, heqV]; exact mul_lt_mul_of_pos_left hwin hBase0
  -- LHS upper bound
  have hLHS_le : (64 - 1) * N' / W * (YS + 12 * (105 : ℝ) ^ 2 / D * MS)
      + P2 * LAM ^ 2 ≤ U + p1 + p2 + p3 + pTR := by
    have hcoeff : 0 ≤ (64 - 1) * N' / W := by positivity
    have h300nn : 0 ≤ 12 * (105 : ℝ) ^ 2 / D := by positivity
    have hinner : YS + 12 * (105 : ℝ) ^ 2 / D * MS
        ≤ (Xp * Ic + BY) + 12 * (105 : ℝ) ^ 2 / D * (Xp * Mc + BM) :=
      add_le_add hYS (mul_le_mul_of_nonneg_left hMS h300nn)
    have hstep : (64 - 1) * N' / W * (YS + 12 * (105 : ℝ) ^ 2 / D * MS)
        ≤ (64 - 1) * N' / W
            * ((Xp * Ic + BY) + 12 * (105 : ℝ) ^ 2 / D * (Xp * Mc + BM)) :=
      mul_le_mul_of_nonneg_left hinner hcoeff
    have heq : (64 - 1) * N' / W
        * ((Xp * Ic + BY) + 12 * (105 : ℝ) ^ 2 / D * (Xp * Mc + BM))
        = U + p1 + p2 + p3 := by
      rw [hUdef, hp1def, hp2def, hp3def, hBasedef]; field_simp; ring
    linarith only [hstep, heq.le, heq.ge]
  -- RHS
  have hmain' : V - pqe ≤ Smain := hmain_ge
  have hcoll' : Scoll ≤ pcoll + pherr := hcoll_le
  linarith only [hLHS_le, hmain', hcoll', hp1, hp2, hp3, hpqe, hpcoll, hpTR, hpherr, hwin']

/-! ## B4.5c — the slack discharge -/

set_option maxHeartbeats 10000000 in
-- The endgame assembly threads ~40 named bounds into `slack_closure_105`; the large local
-- context (105-indexed `choose`s, the `∀ᶠ` bundle) makes elaboration heartbeat-heavy. Same
-- budget as the k = 5 template.
theorem winSlackM105_ev (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743) :
    ∃ D₀ : ℕ, 744 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
    ∀ C₀ : ℝ, 0 ≤ C₀ → ∀ᶠ N' : ℕ in atTop, WinSlackM105 D C₀ N' := by
  classical
  -- === F-only constants (obtained before the cutoff `D₀`) ===
  set Ic : ℝ := ((simplexInt (sq F1) : ℚ) : ℝ) with hIcdef
  have hQ2 : (0 : ℚ) < Qsum ^ 2 := pow_pos Qsum_pos 2
  have hIcpos : 0 < Ic := by
    have h : (0 : ℚ) < simplexInt (sq F1) := by
      rw [simplexInt_sq_F1]; exact div_pos Iform_pos hQ2
    rw [hIcdef]; exact_mod_cast h
  set J1 : ℝ := ((Jform / Qsum ^ 2 : ℚ) : ℝ) with hJ1def
  have hJc : ∀ m : Fin 105, ((simplexInt (sq (contractB m F1)) : ℚ) : ℝ) = J1 := fun m => by
    rw [simplexInt_sq_contractB_F1 m]
  have hJ1pos : 0 < J1 := by rw [← hJc 0]; exact J1_pos 0
  set SJ : ℝ := 105 * J1 with hSJdef
  have hcert : (40015 : ℝ) * Ic < 10000 * SJ := by
    have h := div_lt_div_of_pos_right ratio_cert_105 hQ2
    have hq : (40015 : ℚ) * (Iform / Qsum ^ 2) < 10000 * (105 * (Jform / Qsum ^ 2)) := by
      have e1 : (40015 : ℚ) * (Iform / Qsum ^ 2) = 40015 * Iform / Qsum ^ 2 := by ring
      have e2 : (10000 : ℚ) * (105 * (Jform / Qsum ^ 2)) = 10000 * (105 * Jform) / Qsum ^ 2 := by
        ring
      rw [e1, e2]; exact h
    have hIc' : Ic = ((Iform / Qsum ^ 2 : ℚ) : ℝ) := by rw [hIcdef, simplexInt_sq_F1]
    rw [hIc', hSJdef, hJ1def]
    exact_mod_cast hq
  set Mc : ℝ := ((simplexInt one105 : ℚ) : ℝ) with hMcdef
  have hMc0 : 0 ≤ Mc := simplexInt_one105_nonneg
  obtain ⟨AF, hAF0, hyb⟩ := mv_I_split_gen 105 (by norm_num) (sq F1)
  obtain ⟨A1, hA10, hMb⟩ := mv_I_split_gen 105 (by norm_num) one105
  have hqd_ex : ∀ m : Fin 105, ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → 12 * 105 ^ 2 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ (c : ℝ) (R₀ : ℕ), 0 ≤ c ∧ ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 105 R W' m (yFg R W' F1)
            - ((W'.totient : ℝ) / W' * Real.log R) ^ 106
                * ((simplexInt (sq (contractB m F1)) : ℚ) : ℝ)|
          ≤ (c / Real.log R + A / Real.sqrt D)
                * ((W'.totient : ℝ) / W' * Real.log R) ^ 106 := fun m => qdiag_err_split_105 m
  choose Aqd hAqd0 hqdbody using hqd_ex
  set AqdSum : ℝ := ∑ m : Fin 105, Aqd m with hAqdSumdef
  have hAqdSum0 : 0 ≤ AqdSum := Finset.sum_nonneg (fun m _ => hAqd0 m)
  have hAqd_le : ∀ m, Aqd m ≤ AqdSum := fun m =>
    Finset.single_le_sum (fun i _ => hAqd0 i) (Finset.mem_univ m)
  have hcf_ex : ∀ m : Fin 105, ∃ CF : ℝ, 0 ≤ CF ∧ ∃ Dthr : ℕ, 12 * 105 ^ 2 ≤ Dthr ∧
      ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' → Dthr ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) → 48 * 105 ^ 2 ≤ D →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1)|
          ≤ (4 * Cs * CF * (105 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 105 R W' m (yFg R W' F1) :=
    fun m => s2_collision_floor_105 m
  choose CFf hCFf0 Dthrf hDthrfk hcfbody using hcf_ex
  set SCFJ : ℝ := ∑ m : Fin 105, CFf m * (J1 + 1) with hSCFJdef
  have hSCFJ0 : 0 ≤ SCFJ :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (hCFf0 m) (by linarith [hJ1pos]))
  set DthrSum : ℕ := ∑ m : Fin 105, Dthrf m with hDthrSumdef
  have hDthrf_le : ∀ m, Dthrf m ≤ DthrSum := fun m =>
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
  have hCs0 : (0:ℝ) ≤ Cs := by rw [Cs]; norm_num
  set S6 : ℝ := (6 : ℝ) ^ 105 with hS6def
  have hS60 : 0 ≤ S6 := by positivity
  -- === the cutoff `D₀` (existential, K7) ===
  set Dthr_real : ℝ := 12 * (105 : ℝ) ^ 2 * Mc * 700000 / Ic + S6 * AF * 1400000 / Ic
      + 12 * (105 : ℝ) ^ 2 * S6 * A1 * 1400000 / Ic + (AqdSum * 1400000 / Ic) ^ 2
      + 1000 * (4 * Cs * 105 ^ 2) * SCFJ * 700000 / (63 * Ic) + (2 * AqdSum) ^ 2
    with hDthrrealdef
  refine ⟨max (max (48 * 105 ^ 2) DthrSum) ⌈Dthr_real⌉₊,
    le_trans (by norm_num) (le_trans (le_max_left (48 * 105 ^ 2) DthrSum) (le_max_left _ _)), ?_⟩
  intro D hD C₀ hC₀
  -- === D-facts ===
  have hD48 : 48 * 105 ^ 2 ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
  have hD12 : 12 * 105 ^ 2 ≤ D := le_trans (by norm_num) hD48
  have hDthrSumD : DthrSum ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
  have hDR1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast (le_trans (by norm_num) hD48 : 1 ≤ D)
  have hDR : (0:ℝ) < (D:ℝ) := by linarith
  have hDthrrealD : Dthr_real ≤ (D:ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hD)
  -- === modulus facts at `W' = primorial D` ===
  set W' : ℕ := primorial D with hW'def
  have hW'sqf : Squarefree W' := primorial_sqf' D
  have hW'pos : 0 < W' := primorial_pos'' D
  have hW'r : (0 : ℝ) < (W' : ℝ) := by exact_mod_cast hW'pos
  have hφW'pos : (0 : ℝ) < (W'.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW'pos
  have hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p := primorial_hDlt D
  have hκle : (W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D := primorial_ratio_le D (by omega)
  have hUpper : PhiUpperAtom W' := phiUpperAtom_final W' hW'pos.ne'
  set κ : ℝ := (W'.totient : ℝ) / (W' : ℝ) with hκdef
  have hκpos : 0 < κ := div_pos hφW'pos hW'r
  have hφeq : κ * (W' : ℝ) = (W'.totient : ℝ) := by
    rw [hκdef]; field_simp
  -- === W'-dependent constants (obtained before the `∀ᶠ N'`) ===
  obtain ⟨cF, hcF0, hybR⟩ := hyb W' D hW'sqf hW'pos hUpper (by omega) hDlt
  obtain ⟨c1, hc10, hMbR⟩ := hMb W' D hW'sqf hW'pos hUpper (by omega) hDlt
  have hqd2 : ∀ m : Fin 105, ∃ (c : ℝ) (R₀ : ℕ), 0 ≤ c ∧
      ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
      |Qdiag_mW 105 R W' m (yFg R W' F1)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 106
              * ((simplexInt (sq (contractB m F1)) : ℚ) : ℝ)|
        ≤ (c / Real.log R + Aqd m / Real.sqrt D)
              * ((W'.totient : ℝ) / W' * Real.log R) ^ 106 :=
    fun m => hqdbody m W' D hW'sqf hW'pos hUpper hD12 hDlt hκle
  choose cqd R0qd hcqd0 hqdR using hqd2
  set CqdSum : ℝ := ∑ m : Fin 105, cqd m with hCqdSumdef
  have hCqdSum0 : 0 ≤ CqdSum := Finset.sum_nonneg (fun m _ => hcqd0 m)
  have hcqd_le : ∀ m, cqd m ≤ CqdSum := fun m =>
    Finset.single_le_sum (fun i _ => hcqd0 i) (Finset.mem_univ m)
  have hcf2 : ∀ m : Fin 105, ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
      |Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1)|
        ≤ (4 * Cs * CFf m * (105 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 105 R W' m (yFg R W' F1) :=
    fun m => hcfbody m W' D hW'sqf hW'pos hUpper (le_trans (hDthrf_le m) hDthrSumD) hDlt hκle
      hD48
  choose R0cf hcfR using hcf2
  obtain ⟨Clam, hClam0, hClamle⟩ := S1_trivial_error_le'_uniform 105 W'
  obtain ⟨Cpas, hpasfun⟩ := phiAtom_upper_lossy W' hW'pos.ne'
  rw [← hκdef] at hpasfun
  set Rbig : ℕ := 2 + (∑ m : Fin 105, R0qd m) + (∑ m : Fin 105, R0cf m) with hRbigdef
  have hR0qd_le : ∀ m, R0qd m ≤ Rbig := fun m => by
    rw [hRbigdef]
    have := Finset.single_le_sum (f := R0qd) (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  have hR0cf_le : ∀ m, R0cf m ≤ Rbig := fun m => by
    rw [hRbigdef]
    have := Finset.single_le_sum (f := R0cf) (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  set Kp : ℝ := κ ^ 105 with hKpdef
  set Kmain : ℝ := 63 * Kp * Ic / ((W' : ℝ) * 700000) with hKmaindef
  have hKmain0 : 0 < Kmain := by
    exact div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hκpos 105)) hIcpos)
      (mul_pos hW'r (by norm_num))
  -- === the `∀ᶠ N'` bundle ===
  filter_upwards [eventually_ge_atTop 32, deltaPi_upper_ev_105 hle, eventually_R_ge_rho Rbig,
    eventually_logR_ge_rho 1, eventually_DL_105,
    eventually_div_logR_le_rho ((2:ℝ) ^ 105 * cF) (Ic / 1400000) (by positivity),
    eventually_div_logR_le_rho (12 * (105:ℝ) ^ 2 / D * (2:ℝ) ^ 105 * c1) (Ic / 1400000)
      (by positivity),
    eventually_div_logR_le_rho CqdSum (Ic / 1400000) (by positivity),
    eventually_div_logR_le_rho CqdSum (1 / 2) (by norm_num),
    eventually_poly_o_linear_rho (4 * 105 + 2) Kmain ((2:ℝ) ^ (105 + 1) * Clam) hKmain0
      (mul_nonneg (pow_nonneg (by norm_num) _) hClam0),
    eventually_polylog_ratio_le_rho (2 * 105 + 2) (2 * 105 + 4) (105 * C₀) Kmain (by norm_num)
      hKmain0 (by positivity),
    eventually_logR_ge_rho (max (1 / κ) ((1 + Cpas) / κ))]
    with N' hN32 hΔπ hRge hlogR1 hDLev hbuckY hbuckM hqeL hqe1 hTRev hHerrev hXthr
  -- === abbreviations matching the goal ===
  set R : ℕ := ⌊(N':ℝ) ^ (9999 / 40000 : ℝ)⌋₊ with hRdef
  set LR : ℝ := Real.log (R : ℝ) with hLRdef
  set L : ℝ := Real.log (N' : ℝ) with hLdef
  set X : ℝ := κ * LR with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  -- basic facts
  have hN'1 : (1:ℝ) < (N':ℝ) := by exact_mod_cast (by omega : 1 < N')
  have hN'pos : (0:ℝ) < (N':ℝ) := by linarith
  have hLpos : 0 < L := Real.log_pos hN'1
  have h2Rbig : 2 ≤ Rbig := by rw [hRbigdef]; omega
  have hR2 : 2 ≤ R := le_trans h2Rbig hRge
  have hRr : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hLR1 : (1:ℝ) ≤ LR := hlogR1
  have hLRpos : 0 < LR := by linarith
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hκpos hLRpos
  have hXp : 0 < X ^ 105 := pow_pos hXpos 105
  have hLRthr : max (1 / κ) ((1 + Cpas) / κ) ≤ LR := hXthr
  have h1X : (1:ℝ) ≤ X := by
    have hle : 1 / κ ≤ LR := le_trans (le_max_left _ _) hLRthr
    rw [div_le_iff₀ hκpos] at hle
    rw [hXdef]; linarith only [hle]
  have hXCpas : 1 + Cpas ≤ X := by
    have hle : (1 + Cpas) / κ ≤ LR := le_trans (le_max_right _ _) hLRthr
    rw [div_le_iff₀ hκpos] at hle
    rw [hXdef]; linarith only [hle]
  have hPASnn : 0 ≤ PAS := by
    rw [hPASdef]; exact pas_nonneg105 R W'
  have hPASle : PAS ≤ 4 * X + Cpas := by
    have h := hpasfun R hR2
    rw [← hLRdef] at h
    rw [← hPASdef, ← hXdef] at h; exact h
  have hPAS6X : 1 + PAS ≤ 6 * X := by linarith [hPASle, hXCpas, h1X]
  have hLRleL : LR ≤ L := by
    rw [hLRdef, hLdef]
    exact Real.log_le_log hRr (by exact_mod_cast R_le_N'_rho N' (by omega))
  -- === atomised k = 105 power facts (K13) ===
  have hA1X : (1 + X) ^ 105 ≤ (2:ℝ) ^ 105 * X ^ 105 := by
    calc (1 + X) ^ 105 ≤ (2 * X) ^ 105 := pow_le_pow_left₀ (by linarith) (by linarith) 105
      _ = (2:ℝ) ^ 105 * X ^ 105 := mul_pow 2 X 105
  have hAPAS : (1 + PAS) ^ 105 ≤ S6 * X ^ 105 := by
    rw [hS6def]
    calc (1 + PAS) ^ 105 ≤ (6 * X) ^ 105 := pow_le_pow_left₀ (by linarith) hPAS6X 105
      _ = (6:ℝ) ^ 105 * X ^ 105 := mul_pow 6 X 105
  have hKpX : Kp ≤ X ^ 105 := by
    rw [hKpdef]
    have hκX : κ ≤ X := by
      rw [hXdef]; exact le_mul_of_one_le_right hκpos.le hLR1
    exact pow_le_pow_left₀ hκpos.le hκX 105
  -- expose and fold the goal
  unfold WinSlackM105
  rw [← hW'def, ← hRdef, ← hLRdef, ← hLdef]
  set δ : ℝ := (63 - 1 / 1000) * (N':ℝ) / L - 743 with hδdef
  set YS : ℝ := ∑ r ∈ kSieveIndex 105 R W', yFg R W' F1 r ^ 2 / ∏ i, ((r i).totient : ℝ)
    with hYSdef
  set MS : ℝ := ∑ r ∈ kSieveIndex 105 R W', 1 / ∏ i, ((r i).totient : ℝ) with hMSdef
  set LAM : ℝ := ∑ d ∈ kSieveIndex 105 R W', |lam 105 R W' (yFg R W' F1) d| with hLAMdef
  generalize hT212 : (1 + LR) ^ (2 * 105 + 2) = T212 at hHerrev ⊢
  generalize hL214 : L ^ (2 * 105 + 4) = L214 at hHerrev ⊢
  rw [hKmaindef] at hTRev hHerrev
  -- === identities ===
  have hδ0 : 0 ≤ δ := by
    by_contra hc
    rw [not_le] at hc
    have hneg : δ * LR < 0 := mul_neg_of_neg_of_pos hc hLRpos
    have hnn : (0:ℝ) ≤ 15746 / 1000 * (N':ℝ) := mul_nonneg (by norm_num) hN'pos.le
    linarith only [hDLev, hneg, hnn]
  have hXfull : (W'.totient : ℝ) / (W' : ℝ) * Real.log (R : ℝ) = X := by
    rw [← hκdef, ← hLRdef, ← hXdef]
  have hVid : ∀ a : ℝ, a / (W'.totient : ℝ) * X ^ 106 = a * LR * (X ^ 105 / (W' : ℝ)) := by
    intro a
    have hX : X = κ * LR := hXdef
    have hκne : κ ≠ 0 := hκpos.ne'
    have hWne : (W' : ℝ) ≠ 0 := hW'r.ne'
    calc a / (W'.totient : ℝ) * X ^ 106 = a / (κ * (W' : ℝ)) * (X ^ 105 * (κ * LR)) := by
          rw [hφeq, ← hX, pow_succ]
      _ = a * LR * (X ^ 105 / (W' : ℝ)) := by field_simp
  -- === YS / MS moment bounds ===
  have hYS : YS ≤ X ^ 105 * Ic
      + (cF * (1 + X) ^ 105 / LR + AF * (1 + PAS) ^ 105 / (D : ℝ)) := by
    have h := (abs_le.mp (hybR R hLR1)).2
    have hYSeq : (∑ r ∈ kSieveIndex 105 R W',
        eval (sq F1) (fun i => Real.log (r i) / Real.log R)
          / ∏ i, ((r i).totient : ℝ)) = YS := by
      rw [hYSdef]; refine Finset.sum_congr rfl (fun r hr => ?_)
      simp only [yFg, if_pos hr, eval_sq]
    rw [hYSeq, hXfull, ← hIcdef, ← hLRdef, ← hPASdef] at h
    exact sub_le_iff_le_add'.mp h
  have hMS : MS ≤ X ^ 105 * Mc
      + (c1 * (1 + X) ^ 105 / LR + A1 * (1 + PAS) ^ 105 / (D : ℝ)) := by
    have h := (abs_le.mp (hMbR R hLR1)).2
    have hMSeq : (∑ r ∈ kSieveIndex 105 R W',
        eval one105 (fun i => Real.log (r i) / Real.log R)
          / ∏ i, ((r i).totient : ℝ)) = MS := by
      rw [hMSdef]; refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [eval_one105]
    rw [hMSeq, hXfull, ← hMcdef, ← hLRdef, ← hPASdef] at h
    exact sub_le_iff_le_add'.mp h
  -- === square-root facts and `D`-thresholds ===
  have hsqDpos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDR
  have hn1 : (0:ℝ) ≤ 12 * (105 : ℝ) ^ 2 * Mc * 700000 / Ic :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMc0) (by norm_num)) hIcpos.le
  have hn2 : (0:ℝ) ≤ S6 * AF * 1400000 / Ic :=
    div_nonneg (mul_nonneg (mul_nonneg hS60 hAF0) (by norm_num)) hIcpos.le
  have hn3 : (0:ℝ) ≤ 12 * (105 : ℝ) ^ 2 * S6 * A1 * 1400000 / Ic :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hS60) hA10) (by norm_num))
      hIcpos.le
  have hn4 : (0:ℝ) ≤ (AqdSum * 1400000 / Ic) ^ 2 := sq_nonneg _
  have hCsC0 : (0:ℝ) ≤ 4 * Cs * 105 ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hCs0) (by norm_num)
  have hn5 : (0:ℝ) ≤ 1000 * (4 * Cs * 105 ^ 2) * SCFJ * 700000 / (63 * Ic) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCsC0) hSCFJ0) (by norm_num))
      (mul_nonneg (by norm_num) hIcpos.le)
  have hn6 : (0:ℝ) ≤ (2 * AqdSum) ^ 2 := sq_nonneg _
  rw [hDthrrealdef] at hDthrrealD
  have hMmainD : 12 * (105 : ℝ) ^ 2 * Mc * 700000 / Ic ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn2, hn3, hn4, hn5, hn6]
  have hybD : S6 * AF * 1400000 / Ic ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn3, hn4, hn5, hn6]
  have hMbD : 12 * (105 : ℝ) ^ 2 * S6 * A1 * 1400000 / Ic ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn4, hn5, hn6]
  have hqeD : (AqdSum * 1400000 / Ic) ^ 2 ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn3, hn5, hn6]
  have hcollD : 1000 * (4 * Cs * 105 ^ 2) * SCFJ * 700000 / (63 * Ic) ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn3, hn4, hn6]
  have hQdUpD : (2 * AqdSum) ^ 2 ≤ (D:ℝ) := by
    linarith only [hDthrrealD, hn1, hn2, hn3, hn4, hn5]
  have hsqrtD_ge : 2 * AqdSum ≤ Real.sqrt D := by
    rw [show (2:ℝ) * AqdSum = Real.sqrt ((2 * AqdSum) ^ 2) by
      rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hQdUpD
  have hAqdD_half : AqdSum / Real.sqrt D ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hsqDpos (by norm_num)]; linarith only [hsqrtD_ge]
  have hAqdSqrtD : AqdSum / Real.sqrt D ≤ Ic / 1400000 := by
    have hsq : AqdSum * 1400000 / Ic ≤ Real.sqrt D := by
      rw [show AqdSum * 1400000 / Ic = Real.sqrt ((AqdSum * 1400000 / Ic) ^ 2) by
        rw [Real.sqrt_sq (div_nonneg (mul_nonneg hAqdSum0 (by norm_num)) hIcpos.le)]]
      exact Real.sqrt_le_sqrt hqeD
    rw [div_le_div_iff₀ hsqDpos (by norm_num)]
    linarith only [(div_le_iff₀ hIcpos).mp hsq]
  -- === per-`m` qdiag bounds ===
  set QEc : Fin 105 → ℝ := fun m => cqd m / LR + Aqd m / Real.sqrt D with hQEcdef
  have hQEc0 : ∀ m, 0 ≤ QEc m := fun m => by
    rw [hQEcdef]; apply add_nonneg <;> apply div_nonneg
    · exact hcqd0 m
    · exact hLRpos.le
    · exact hAqd0 m
    · exact hsqDpos.le
  have hQabs : ∀ m : Fin 105, |Qdiag_mW 105 R W' m (yFg R W' F1) - X ^ 106 * J1|
      ≤ QEc m * X ^ 106 := by
    intro m
    have h := hqdR m R (le_trans (hR0qd_le m) hRge) hLR1
    rw [hXfull, ← hLRdef, hJc m] at h
    exact h
  have hQEc1 : ∀ m, QEc m ≤ 1 := by
    intro m
    have h1 : cqd m / LR ≤ CqdSum / LR := div_le_div_of_nonneg_right (hcqd_le m) hLRpos.le
    have h2 : Aqd m / Real.sqrt D ≤ AqdSum / Real.sqrt D :=
      div_le_div_of_nonneg_right (hAqd_le m) hsqDpos.le
    rw [hQEcdef]; simp only; linarith only [h1, h2, hqe1, hAqdD_half]
  have hQdnn : ∀ m : Fin 105, 0 ≤ Qdiag_mW 105 R W' m (yFg R W' F1) := by
    intro m; rw [qdiag_eq_yMsq_sum_gen]
    exact Finset.sum_nonneg (fun u _ => div_nonneg (sq_nonneg _)
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)))
  have hX106pos : 0 < X ^ 106 := pow_pos hXpos 106
  have hQhi : ∀ m : Fin 105,
      Qdiag_mW 105 R W' m (yFg R W' F1) ≤ X ^ 106 * (J1 + 1) := by
    intro m
    have h := (abs_le.mp (hQabs m)).2
    have h2 := mul_le_mul_of_nonneg_right (hQEc1 m) hX106pos.le
    have hexp : X ^ 106 * (J1 + 1) = X ^ 106 * J1 + X ^ 106 := by ring
    rw [hexp]; linarith only [h, h2]
  have hQlo : ∀ m : Fin 105, X ^ 106 * J1 - QEc m * X ^ 106
      ≤ Qdiag_mW 105 R W' m (yFg R W' F1) := fun m => by
    linarith only [(abs_le.mp (hQabs m)).1]
  set QEcSum : ℝ := ∑ m : Fin 105, QEc m with hQEcSumdef
  have hQEcSum0 : 0 ≤ QEcSum := Finset.sum_nonneg (fun m _ => hQEc0 m)
  have hQEcSum_bound : QEcSum ≤ Ic / 700000 := by
    rw [hQEcSumdef, hQEcdef]
    have hsplit : ∑ m : Fin 105, (cqd m / LR + Aqd m / Real.sqrt D)
        = (∑ m : Fin 105, cqd m) / LR + (∑ m : Fin 105, Aqd m) / Real.sqrt D := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    simp only
    rw [hsplit, ← hCqdSumdef, ← hAqdSumdef]
    linarith only [hqeL, hAqdSqrtD]
  -- === RHS main lower bound ===
  have hmain_ge : δ * LR * (X ^ 105 / (W' : ℝ)) * SJ - δ * LR * (X ^ 105 / (W' : ℝ)) * QEcSum
      ≤ ∑ m : Fin 105, δ / (W'.totient : ℝ) * Qdiag_mW 105 R W' m (yFg R W' F1) := by
    have hper : ∀ m ∈ (Finset.univ : Finset (Fin 105)),
        δ * LR * (X ^ 105 / (W' : ℝ)) * J1 - δ * LR * (X ^ 105 / (W' : ℝ)) * QEc m
          ≤ δ / (W'.totient : ℝ) * Qdiag_mW 105 R W' m (yFg R W' F1) := by
      intro m _
      have h1 : δ / (W'.totient : ℝ) * (X ^ 106 * J1 - QEc m * X ^ 106)
          = δ * LR * (X ^ 105 / (W' : ℝ)) * J1 - δ * LR * (X ^ 105 / (W' : ℝ)) * QEc m := by
        rw [mul_sub, show δ / (W'.totient : ℝ) * (X ^ 106 * J1)
              = δ / (W'.totient : ℝ) * X ^ 106 * J1 by ring, hVid,
          show δ / (W'.totient : ℝ) * (QEc m * X ^ 106)
              = δ / (W'.totient : ℝ) * X ^ 106 * QEc m by ring, hVid]
      rw [← h1]
      exact mul_le_mul_of_nonneg_left (hQlo m) (div_nonneg hδ0 hφW'pos.le)
    have hsum := Finset.sum_le_sum hper
    have hsumeq : ∑ m : Fin 105, (δ * LR * (X ^ 105 / (W' : ℝ)) * J1
          - δ * LR * (X ^ 105 / (W' : ℝ)) * QEc m)
        = δ * LR * (X ^ 105 / (W' : ℝ)) * SJ - δ * LR * (X ^ 105 / (W' : ℝ)) * QEcSum := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Finset.mul_sum, ← hQEcSumdef, nsmul_eq_mul, hSJdef]
      push_cast; ring
    linarith only [hsum, hsumeq.symm.le, hsumeq.le]
  -- === RHS collision + herr upper bound ===
  set CollUB : Fin 105 → ℝ := fun m =>
    1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ))
      * (X ^ 106 * (J1 + 1))
    with hCollUBdef
  have hcolleq : ∑ m : Fin 105, CollUB m
      = 1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * 105 ^ 2 / (D:ℝ)) * (X ^ 105 * X)
        * SCFJ := by
    rw [hSCFJdef, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [hCollUBdef]; ring)
  have hcoll_le : ∑ m : Fin 105, (deltaPi 105 64 N' m / (W'.totient:ℝ)
        * (Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1))
      + C₀ * T212 * (N':ℝ) / L214)
      ≤ 1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * 105 ^ 2 / (D:ℝ)) * (X ^ 105 * X)
          * SCFJ + 105 * (C₀ * T212 * (N':ℝ) / L214) := by
    have hper : ∀ m ∈ (Finset.univ : Finset (Fin 105)),
        deltaPi 105 64 N' m / (W'.totient:ℝ)
            * (Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1))
          + C₀ * T212 * (N':ℝ) / L214
        ≤ CollUB m + C₀ * T212 * (N':ℝ) / L214 := by
      intro m _
      have hcfm := hcfR m R (le_trans (hR0cf_le m) hRge) hLR1
      have hQds2 : Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1)
          ≤ 4 * Cs * CFf m * 105 ^ 2 / (D:ℝ) * Qdiag_mW 105 R W' m (yFg R W' F1) :=
        le_trans (le_abs_self _) hcfm
      have hΔ0 : 0 ≤ deltaPi 105 64 N' m := deltaPi_nonneg 105 64 N' m (by norm_num)
      have hcoef0 : 0 ≤ 4 * Cs * CFf m * 105 ^ 2 / (D:ℝ) :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCs0) (hCFf0 m))
          (by norm_num)) hDR.le
      have hA'nn : 0 ≤ 1000 * (N':ℝ) / L / (W'.totient:ℝ)
          * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ)) :=
        mul_nonneg (div_nonneg (div_nonneg (mul_nonneg (by norm_num) hN'pos.le) hLpos.le)
          hφW'pos.le) hcoef0
      have hs1 : deltaPi 105 64 N' m / (W'.totient:ℝ)
            * (Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1))
          ≤ deltaPi 105 64 N' m / (W'.totient:ℝ)
            * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ) * Qdiag_mW 105 R W' m (yFg R W' F1)) :=
        mul_le_mul_of_nonneg_left hQds2 (div_nonneg hΔ0 hφW'pos.le)
      have hAle : deltaPi 105 64 N' m / (W'.totient:ℝ) * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ))
          ≤ 1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ)) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hΔπ m) hφW'pos.le) hcoef0
      have hs2 : deltaPi 105 64 N' m / (W'.totient:ℝ)
            * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ) * Qdiag_mW 105 R W' m (yFg R W' F1))
          ≤ CollUB m := by
        rw [hCollUBdef]; simp only
        calc deltaPi 105 64 N' m / (W'.totient:ℝ)
                * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ) * Qdiag_mW 105 R W' m (yFg R W' F1))
            = deltaPi 105 64 N' m / (W'.totient:ℝ) * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ))
                * Qdiag_mW 105 R W' m (yFg R W' F1) := by ring
          _ ≤ 1000 * (N':ℝ) / L / (W'.totient:ℝ) * (4 * Cs * CFf m * 105 ^ 2 / (D:ℝ))
                * (X ^ 106 * (J1 + 1)) := mul_le_mul hAle (hQhi m) (hQdnn m) hA'nn
      exact add_le_add (le_trans hs1 hs2) le_rfl
    calc ∑ m : Fin 105, (deltaPi 105 64 N' m / (W'.totient:ℝ)
            * (Qdiag_mW 105 R W' m (yFg R W' F1) - s2CompatFormM 105 R W' m (yFg R W' F1))
          + C₀ * T212 * (N':ℝ) / L214)
        ≤ ∑ m : Fin 105, (CollUB m + C₀ * T212 * (N':ℝ) / L214) := Finset.sum_le_sum hper
      _ = (∑ m : Fin 105, CollUB m) + ∑ _m : Fin 105, C₀ * T212 * (N':ℝ) / L214 :=
          Finset.sum_add_distrib
      _ = _ := by
          rw [hcolleq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  -- === truncation ===
  have hLAM : LAM ^ 2 ≤ Clam * (R:ℝ) ^ 2 * (1 + LR) ^ (4 * 105 + 2) := by
    have h := hClamle R hR2 (yFg R W' F1) (fun r => yFg_F1_abs_le_one R W' r)
    rw [← hLRdef, ← hLAMdef] at h
    exact h
  -- === the closure ===
  exact slack_closure_105 (hN' := hN'pos) (hL := hLpos) (hLR1 := hLR1) (hLRleL := hLRleL)
    (hκ := hκpos) (hW := hW'r) (hφeq := hφeq) (hD1 := hDR1) (hX := hXdef) (hXp := hXp)
    (hKp := hKpX) (hIc := hIcpos) (hcert := hcert) (hδdef := hδdef) (hDL := hDLev)
    (hYS := hYS) (hMS := hMS) (hcF := hcF0) (hAF := hAF0) (hc1 := hc10) (hA1 := hA10)
    (_hMc := hMc0) (hA1X := hA1X) (hAPAS := hAPAS) (_hT2 := pow_nonneg (by norm_num) _)
    (hS6 := hS60) (hP2 := pow_nonneg (by norm_num) _) (hbuckY := hbuckY) (hbuckM := hbuckM)
    (hybD := hybD) (hMbD := hMbD) (hMmainD := hMmainD) (hmain_ge := hmain_ge)
    (hQEcSum0 := hQEcSum0) (hQEcSum := hQEcSum_bound) (hcoll_le := hcoll_le)
    (hSCFJ0 := hSCFJ0) (hCsC0 := hCsC0) (hcollD := hcollD) (hLAM := hLAM)
    (hTRev := hTRev) (hHerrev := hHerrev)

/-- CONTROL (the B4.6 composition): the slack discharges `WinFrontierMW105` at every `D ≥ D₀`. -/
theorem winFrontierMW105_all (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743) :
    ∃ D₀ : ℕ, 744 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → WinFrontierMW105 D := by
  obtain ⟨D₀, hD₀, hslack⟩ := winSlackM105_ev hle
  exact ⟨D₀, hD₀, fun D hD =>
    winFrontierMW105_of D (le_trans hD₀ hD) hle (fun C₀ hC₀ => hslack D hD C₀ hC₀)⟩

end Salt.MaynardK
