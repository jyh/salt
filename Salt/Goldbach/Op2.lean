/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Op

/-!
# G-OP2 — the two remaining operating-point discharges (`chen_goldbach`, wave W4)

The last pre-assembly executor for the Goldbach arc closes the two gaps G-OP flagged:

* **The count fold** (`gold_hcount_seam`): folds the `Ifun`/`hbjs` boundary error terms of
  `goldTripleSum_le_cbar_final` (fed by `gold_op_count_rows`) into the clean count-seam shape
  `log N · (goldTripleSum / φ(opQ)) ≤ (cbar + ecountOp C N) · ((∑Λ) / φ(opQ))`, byte-matching the
  twin's `Salt.Chen.hcount_seam` at `x := N`.  The Goldbach count is the UNRESTRICTED
  `goldTripleSum` divided by `φ(opQ)`, so — unlike the twin — there is NO equidistribution crumb;
  the `Ifun`/`hbjs` fold reuses the twin's `Salt.Chen.corr_le_at_op` VERBATIM at `x := N` (identical
  `S1set`/`Ifun`/`hbjs` carriers), and the leading `cbar/2 → cbar` conversion is the honest
  massLo/(N/2) ratio (mirroring `Salt.Chen.hcount_star_at_op`).

* **The survivor prices** (`gold_hBVblocksW_discharge'` at op): **STOP-AND-FLAG**.  A full op-point
  discharge needs, per `(j, k', k, i)` boundary survivor, a `medium_survivor_price_sqrtD`
  instantiation (about 30 numeric op-scale rows) at the `crtClassG` residue, then the annulus/piece
  budget arithmetic.  The twin assembles this over FIVE files (`FinA3`/`FinA3b`/`AggSum`/`PriceOne`/
  `PriceClose`: `box_price_indep`, `low/sym_price_indep`, `hSum_at_op`, `hRCE_at_op`,
  `hNum_close_of_tower`); its price bodies HARD-WIRE `crtClassW` (not `crtClassG`) and carry a
  SINGLE T-difference (no annulus axis).  No landed Goldbach `crtClassG` box-price supplier exists.
  Re-deriving all of it for `crtClassG` plus the extra per-annulus budget (the "one extra log",
  absorbed by BV at saving `A+1`), inside ONE new file, WITHOUT touching existing files, is not
  feasible.  See the G-OP2 report for the exact blocking step and reuse census.  The count seam
  IS landed and joins G-OP's `gold_a12_hA1` and G-OMEGA's A2 bundle at G-ASM.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace Salt.Goldbach

open Salt.Chen

/-! ## Part A — the count fold (`gold_hcount_seam`) -/

/-- The concrete count-seam error budget constant: `C = 4·cbar·D + 2·C_CORR + 4·cbar·Kmass + 2`
with `D = 4log2 + 16log3 + 32·Kcount` (the `goldTripleSum_le_cbar_final` correction coefficient)
and `C_CORR = 255log2 + 768` (the `corr_le_at_op` boundary bound). -/
noncomputable def goldSeamC (Kcount Kmass : ℝ) : ℝ :=
  4 * cbar * (4 * Real.log 2 + 16 * Real.log 3 + 32 * Kcount)
    + 2 * (255 * Real.log 2 + 768) + 4 * cbar * Kmass + 2

set_option maxRecDepth 8000 in
/-- **`gold_hcount_seam` — the Goldbach count seam at `goldTripleSum / φ(opQ)`.**  Past a threshold,
the Goldbach count line closes against the PNT window mass with leading constant `cbar` and an
explicit `o(1)` budget `ecountOp C N = C / log(opZ N)`.  The Goldbach mirror of
`Salt.Chen.hcount_seam` (`x := N`), but with the UNRESTRICTED `goldTripleSum` — no equidistribution
crumb.  Composes `goldCount_bound_uniformK` + `gold_op_count_rows` (geometry) + `corr_le_at_op`
(the boundary fold, reused) + `lambda_mass_lower` (the window mass). -/
theorem gold_hcount_seam : ∃ (C : ℝ) (x₁ : ℕ), 0 ≤ C ∧ ∀ N : ℕ, x₁ ≤ N →
    Real.log N * (goldTripleSum N (opZ N) (opY N) / (opQ.totient : ℝ))
      ≤ (cbar + ecountOp C N)
          * ((∑ n ∈ twinWindow N, vonMangoldt n) / (opQ.totient : ℝ)) := by
  obtain ⟨Kcount, hKc0, hpsi⟩ := psiTot_pnt
  obtain ⟨Kmass, hKm0, hmass⟩ := lambda_mass_lower
  obtain ⟨xc, hrows⟩ := gold_op_count_rows
  obtain ⟨xcorr, hcorr⟩ := corr_le_at_op
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hcbar := cbar_pos
  set D : ℝ := 4 * Real.log 2 + 16 * Real.log 3 + 32 * Kcount with hDdef
  set CC : ℝ := 255 * Real.log 2 + 768 with hCCdef
  have hDnn : 0 ≤ D := by rw [hDdef]; nlinarith [hlog2, hlog3, hKc0]
  have hCCnn : 0 ≤ CC := by rw [hCCdef]; nlinarith [hlog2]
  set C : ℝ := goldSeamC Kcount Kmass with hCsetdef
  have hCdef : C = 4 * cbar * D + 2 * CC + 4 * cbar * Kmass + 2 := by
    rw [hCsetdef, goldSeamC, ← hDdef, ← hCCdef]
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    nlinarith [mul_nonneg hcbar.le hDnn, hCCnn, mul_nonneg hcbar.le hKm0]
  -- thresholds
  obtain ⟨xLK, hxLK⟩ := a12_log_ge (4 * C * Kmass)
  obtain ⟨xLD, hxLD⟩ := a12_log_ge (4 * D)
  obtain ⟨xsqrt, hxsqrt⟩ := a12_logpow_le_rpow 1 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, max (max xc xcorr) (max (max xLK xLD)
      (max xsqrt (max 8 (max ⌈16 * cbar ^ 2⌉₊ ⌈4 * C⌉₊)))), hC0, fun N hN => ?_⟩
  -- unpack thresholds
  have hxc : xc ≤ N := by omega
  have hxcorr : xcorr ≤ N := by omega
  have hxLKn : xLK ≤ N := by omega
  have hxLDn : xLD ≤ N := by omega
  have hxsqrtn : xsqrt ≤ N := by omega
  have hx8 : 8 ≤ N := by omega
  have hx16 : ⌈16 * cbar ^ 2⌉₊ ≤ N := by omega
  have hx4C : ⌈4 * C⌉₊ ≤ N := by omega
  -- op-point geometry rows
  obtain ⟨hy6, hlogNz, hx1, hzR2, hzRyR, hlogz, hlogy, hzNle, hzNge, hyNle, hyNge⟩ :=
    hrows N hxc
  set L : ℝ := Real.log N with hLdef
  have hNRpos : (0 : ℝ) < (N : ℝ) := by linarith only [hx1]
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos hx1
  have hφpos : (0 : ℝ) < (opQ.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  -- freeze `ecountOp C N` opaque: its body carries `opZ N` and would `whnf`-loop downstream.
  set ec : ℝ := ecountOp C N with hecdef
  -- log(opY N) ≥ 7L/24 (from hlogNz and log(opZ N) ≤ L/8)
  have hzNpos : (0 : ℝ) < (opZ N : ℝ) := by
    have h0 : (2 : ℝ) ≤ (opZ N : ℝ) + 1 := le_trans hzR2 hzNge
    linarith only [h0]
  have hlogzN_le : Real.log (opZ N) ≤ L / 8 := by
    rw [← hlogz]; exact Real.log_le_log hzNpos hzNle
  have hyNpos : (0 : ℝ) < (opY N : ℝ) := by
    have h0 : (6 : ℝ) ≤ (opY N : ℝ) := by exact_mod_cast hy6
    linarith only [h0]
  have hlogyN_pos : 0 < Real.log (opY N) := Real.log_pos (by
    have h0 : (6 : ℝ) ≤ (opY N : ℝ) := by exact_mod_cast hy6
    linarith only [h0])
  have hlogyN_ge : 7 * L / 24 ≤ Real.log (opY N) := by
    linarith only [hlogNz, hlogzN_le]
  -- the count bound at op (K explicit)
  have hgts := goldCount_bound_uniformK hKc0 hpsi hy6 hlogNz hx1 hzR2 hzRyR hlogz hlogy
    hzNle hzNge hyNle hyNge
  -- the CORR fold (reused verbatim at x := N)
  have hyR0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hNRpos _
  have hcorrle := hcorr N hxcorr ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))
    hzR2 hyR0 hlogz hlogy
  -- abbreviations for the two RHS pieces
  set coef : ℝ := 1 + D / Real.log (opY N) with hcoefdef
  set gts : ℝ := goldTripleSum N (opZ N) (opY N) with hgtsdef
  set BIG : ℝ :=
    ( Ifun (N : ℝ) ((N : ℝ) ^ ((1 : ℝ) / 3)) (opZ N : ℝ) / (opZ N : ℝ)
        + Ifun (N : ℝ) ((N : ℝ) ^ ((1 : ℝ) / 3)) (opY N : ℝ) / (opY N : ℝ)
        + (21 / Real.log ((N : ℝ) ^ ((1 : ℝ) / 8)))
            * Ifun (N : ℝ) ((N : ℝ) ^ ((1 : ℝ) / 3)) ((N : ℝ) ^ ((1 : ℝ) / 8)) )
      + ∑ p₁ ∈ S1set N (opZ N) (opY N), (1 / (p₁ : ℝ))
          * ( hbjs (N : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
                / (↑(⌊Real.sqrt ((N : ℝ) / (p₁ : ℝ))⌋₊))
              + (21 / Real.log ((N : ℝ) ^ ((1 : ℝ) / 3)))
                  * hbjs (N : ℝ) (p₁ : ℝ) (Real.sqrt ((N : ℝ) / (p₁ : ℝ))) ) with hBIGdef
  -- restate the count bound and CORR fold with the abbreviations
  have hgts2 : gts ≤ coef * (cbar / 2) * ((N : ℝ) / L) + coef * ((N : ℝ) / 2) * BIG := hgts
  have hcorr2 : BIG ≤ CC / L ^ 2 := by rw [hCCdef, hLdef]; exact hcorrle
  -- freeze the abbreviations as opaque atoms (their bodies carry `opY N`/`opZ N`, which would
  -- make `field_simp`/`nlinarith` `whnf`-loop); the defining equations survive for `rw`.
  clear_value coef gts BIG C CC D L ec
  -- coef nonnegativity and upper bound (goals carry `opY N`; `linarith only` avoids `whnf`)
  have hcoef_nn : 0 ≤ coef := by
    rw [hcoefdef]; have h := div_nonneg hDnn hlogyN_pos.le; linarith only [h]
  have hcoef_ge : 1 ≤ coef := by
    rw [hcoefdef]; have h := div_nonneg hDnn hlogyN_pos.le; linarith only [h]
  have hDcoef : D / Real.log (opY N) ≤ 4 * D / L := by
    have h7 : D * L ≤ 4 * (D * (7 * L / 24)) := by
      linarith only [mul_nonneg hDnn hLpos.le]
    rw [le_div_iff₀ hLpos, div_mul_eq_mul_div, div_le_iff₀ hlogyN_pos]
    have hkey : D * (7 * L / 24) ≤ D * Real.log (opY N) :=
      mul_le_mul_of_nonneg_left hlogyN_ge hDnn
    set ly := Real.log (opY N) with hlydef
    linarith only [hkey, h7]
  have hcoef_le : coef ≤ 1 + 4 * D / L := by rw [hcoefdef]; linarith only [hDcoef]
  have hcoef_le2 : coef ≤ 2 := by
    have hLD : 4 * D ≤ L := by rw [hLdef]; exact (hxLD N hxLDn).2
    have hle1 : 4 * D / L ≤ 1 := by rw [div_le_one hLpos]; exact hLD
    linarith only [hcoef_le, hle1]
  -- window mass lower bound (matched to L)
  have hmassbd : (N : ℝ) / 2 - 1 - 2 * Kmass * (N : ℝ) / L
      ≤ ∑ n ∈ twinWindow N, vonMangoldt n := by rw [hLdef]; exact hmass N hx8
  have hSumnn : (0 : ℝ) ≤ ∑ n ∈ twinWindow N, vonMangoldt n :=
    Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
  -- the `ecountOp` lower bound (needs `opZ N`, established before the clear)
  have hzN2 : 2 ≤ opZ N :=
    Nat.le_floor (show ((2 : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) by exact_mod_cast hzR2)
  have hlogzN_pos : 0 < Real.log (opZ N) :=
    Real.log_pos (by exact_mod_cast (show 1 < opZ N by omega))
  have hecl : C / L ≤ ec := by
    rw [hecdef, ecountOp]
    exact div_le_div_of_nonneg_left hC0 hlogzN_pos (le_trans hlogzN_le (by linarith only [hLpos]))
  -- clear divisions: L² · gts bound (BIG absorbed by the CORR fold)
  have hcoefN2 : 0 ≤ coef * ((N : ℝ) / 2) := mul_nonneg hcoef_nn (by positivity)
  have hgtsB : gts ≤ coef * (cbar / 2) * ((N : ℝ) / L) + coef * ((N : ℝ) / 2) * (CC / L ^ 2) := by
    have hstep := mul_le_mul_of_nonneg_left hcorr2 hcoefN2
    linarith only [hgts2, hstep]
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- everything opY/opZ/rpow/BIG-bearing has now been distilled to clean-atom facts; drop the
  -- heavy hypotheses so the remaining `nlinarith`/`linarith` do NOT `whnf`-scan them.
  clear hgts hcorrle hgts2 hcorr2 hlogz hlogy hzR2 hzRyR hzNle hzNge hyNle hyNge
    hzNpos hyNpos hlogyN_pos hlogyN_ge hlogzN_le hzN2 hlogzN_pos hDcoef hcoefdef hcoefN2
    hgtsdef hBIGdef hCCdef hDdef hcoef_nn hcoef_ge hy6 hlogNz hrows hmass hcorr hpsi
    hecdef hCsetdef
  have hgtsL2 : L ^ 2 * gts
      ≤ coef * (cbar / 2) * (N : ℝ) * L + coef * ((N : ℝ) / 2) * CC := by
    have h := mul_le_mul_of_nonneg_left hgtsB (by positivity : (0 : ℝ) ≤ L ^ 2)
    have e : L ^ 2 * (coef * (cbar / 2) * ((N : ℝ) / L) + coef * ((N : ℝ) / 2) * (CC / L ^ 2))
        = coef * (cbar / 2) * (N : ℝ) * L + coef * ((N : ℝ) / 2) * CC := by
      field_simp
    rw [e] at h; exact h
  -- apply the coef bounds to reach a division-free budget bound
  have hcoefL : coef * L ≤ L + 4 * D := by
    have h := mul_le_mul_of_nonneg_right hcoef_le hLpos.le
    have e2 : (1 + 4 * D / L) * L = L + 4 * D := by field_simp
    rw [e2] at h; exact h
  have hcbN2 : 0 ≤ cbar / 2 * (N : ℝ) := mul_nonneg (by linarith only [hcbar]) hNRpos.le
  have hc1 : coef * (cbar / 2) * (N : ℝ) * L
      ≤ cbar / 2 * (N : ℝ) * L + 2 * cbar * D * (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hcoefL hcbN2
    have el : coef * L * (cbar / 2 * (N : ℝ)) = coef * (cbar / 2) * (N : ℝ) * L := by ring
    have er : (L + 4 * D) * (cbar / 2 * (N : ℝ))
        = cbar / 2 * (N : ℝ) * L + 2 * cbar * D * (N : ℝ) := by ring
    rw [el, er] at h; exact h
  have hN2CC : 0 ≤ (N : ℝ) / 2 * CC := mul_nonneg (by positivity) hCCnn
  have hc2 : coef * ((N : ℝ) / 2) * CC ≤ CC * (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hcoef_le2 hN2CC
    have el : coef * ((N : ℝ) / 2 * CC) = coef * ((N : ℝ) / 2) * CC := by ring
    have er : 2 * ((N : ℝ) / 2 * CC) = CC * (N : ℝ) := by ring
    rw [el, er] at h; exact h
  have hB : L ^ 2 * gts
      ≤ cbar / 2 * (N : ℝ) * L + 2 * cbar * D * (N : ℝ) + CC * (N : ℝ) := by
    linarith only [hgtsL2, hc1, hc2]
  -- threshold facts: N grows faster than L
  have hLK : 4 * C * Kmass ≤ L := by rw [hLdef]; exact (hxLK N hxLKn).2
  have hN16 : 16 * cbar ^ 2 ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx16)
  have hN4C : 4 * C ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx4C)
  have h4cbar : 4 * cbar ≤ Real.sqrt (N : ℝ) := by
    rw [show (4 : ℝ) * cbar = Real.sqrt ((4 * cbar) ^ 2) from
      (Real.sqrt_sq (by linarith only [hcbar])).symm]
    exact Real.sqrt_le_sqrt (by rw [show (4 * cbar) ^ 2 = 16 * cbar ^ 2 by ring]; exact hN16)
  have hLsqrt : L ≤ Real.sqrt (N : ℝ) := by
    have h := hxsqrt N hxsqrtn
    rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at h
    rw [hLdef]; exact h
  have hsqNsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNRpos.le
  -- abstract `√N` opaque; discharge with exact certificates via `linarith only` (tiny LP)
  set s : ℝ := Real.sqrt (N : ℝ) with hsdef
  clear_value s
  have hsnn : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  clear hsdef
  have h2cbarsq : 2 * cbar * s ≤ (N : ℝ) / 2 := by
    have key : 0 ≤ s * (s - 4 * cbar) := mul_nonneg hsnn (sub_nonneg.mpr h4cbar)
    have e : s * (s - 4 * cbar) = (N : ℝ) - 4 * cbar * s := by rw [mul_sub, hsqNsq]; ring
    linarith only [key, e.le, e.ge]
  have hNL : 2 * cbar * L + 2 * C ≤ (N : ℝ) := by
    have key2 : 0 ≤ 2 * cbar * (s - L) :=
      mul_nonneg (by linarith only [hcbar]) (sub_nonneg.mpr hLsqrt)
    have e2 : 2 * cbar * (s - L) = 2 * cbar * s - 2 * cbar * L := by ring
    linarith only [key2, e2.le, e2.ge, h2cbarsq, hN4C]
  -- the core polynomial inequality (all atoms opY/opZ-free)
  have hNLu : 2 * cbar * L + 2 * (4 * cbar * D + 2 * CC + 4 * cbar * Kmass + 2) ≤ (N : ℝ) :=
    hCdef ▸ hNL
  have hLKu : 4 * (4 * cbar * D + 2 * CC + 4 * cbar * Kmass + 2) * Kmass ≤ L := hCdef ▸ hLK
  -- drop the `Real.sqrt`/`Real.log`-bearing hypotheses before the final `nlinarith`
  clear hLsqrt hN16 hN4C h4cbar hsqNsq h2cbarsq hNL hLK hLdef hsnn s
  have h_a : 0 ≤ L * ((N : ℝ) - 2 * cbar * L
        - 2 * (4 * cbar * D + 2 * CC + 4 * cbar * Kmass + 2)) :=
    mul_nonneg hLpos.le (by linarith only [hNLu])
  have h_b : 0 ≤ (N : ℝ) * (L - 4 * (4 * cbar * D + 2 * CC + 4 * cbar * Kmass + 2) * Kmass) :=
    mul_nonneg hNRpos.le (by linarith only [hLKu])
  have hpoly : L * (cbar / 2 * (N : ℝ) * L + 2 * cbar * D * (N : ℝ) + CC * (N : ℝ))
      ≤ (cbar * L + C) * ((N : ℝ) / 2 * L - L - 2 * Kmass * (N : ℝ)) := by
    rw [hCdef]; linarith only [h_a, h_b]
  -- reassemble (I): L · gts ≤ (cbar + C/L) · massLo
  have hident : (cbar * L + C) * ((N : ℝ) / 2 * L - L - 2 * Kmass * (N : ℝ))
      = L ^ 2 * ((cbar + C / L) * ((N : ℝ) / 2 - 1 - 2 * Kmass * (N : ℝ) / L)) := by
    field_simp
  have hL2pos : (0 : ℝ) < L ^ 2 := by positivity
  have hI : L * gts ≤ (cbar + C / L) * ((N : ℝ) / 2 - 1 - 2 * Kmass * (N : ℝ) / L) := by
    have hBL := mul_le_mul_of_nonneg_left hB hLpos.le
    have hchain : L ^ 2 * (L * gts)
        ≤ L ^ 2 * ((cbar + C / L) * ((N : ℝ) / 2 - 1 - 2 * Kmass * (N : ℝ) / L)) := by
      calc L ^ 2 * (L * gts) = L * (L ^ 2 * gts) := by ring
        _ ≤ L * (cbar / 2 * (N : ℝ) * L + 2 * cbar * D * (N : ℝ) + CC * (N : ℝ)) := hBL
        _ ≤ (cbar * L + C) * ((N : ℝ) / 2 * L - L - 2 * Kmass * (N : ℝ)) := hpoly
        _ = L ^ 2 * ((cbar + C / L) * ((N : ℝ) / 2 - 1 - 2 * Kmass * (N : ℝ) / L)) := hident
    exact le_of_mul_le_mul_left hchain hL2pos
  -- the mass/budget bridges (hecl was established before the clear)
  have hcoefpos : 0 ≤ cbar + C / L := by
    have hd := div_nonneg hC0 hLpos.le; linarith only [hcbar, hd]
  have hII : (cbar + C / L) * ((N : ℝ) / 2 - 1 - 2 * Kmass * (N : ℝ) / L)
      ≤ (cbar + C / L) * (∑ n ∈ twinWindow N, vonMangoldt n) :=
    mul_le_mul_of_nonneg_left hmassbd hcoefpos
  have hIII : (cbar + C / L) * (∑ n ∈ twinWindow N, vonMangoldt n)
      ≤ (cbar + ec) * (∑ n ∈ twinWindow N, vonMangoldt n) :=
    mul_le_mul_of_nonneg_right (by linarith only [hecl]) hSumnn
  have hmain : L * gts ≤ (cbar + ec) * (∑ n ∈ twinWindow N, vonMangoldt n) :=
    le_trans hI (le_trans hII hIII)
  -- cancel φ(opQ)
  have hinv : (0 : ℝ) ≤ ((opQ.totient : ℝ))⁻¹ := inv_nonneg.mpr hφpos.le
  calc L * (gts / (opQ.totient : ℝ)) = (L * gts) * ((opQ.totient : ℝ))⁻¹ := by
        rw [div_eq_mul_inv]; ring
    _ ≤ ((cbar + ec) * (∑ n ∈ twinWindow N, vonMangoldt n)) * ((opQ.totient : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hmain hinv
    _ = (cbar + ec) * ((∑ n ∈ twinWindow N, vonMangoldt n) / (opQ.totient : ℝ)) := by
        rw [div_eq_mul_inv]; ring

end Salt.Goldbach
