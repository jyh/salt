/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SiegelCorr
import Salt.SW.ShiftVariants

/-!
# The forced μ↔χ correlation (S3-HB-R3b)

Design: `docs/exploration/s3-hb3-design.md` (FROZEN, gate `S3-HB3B-GATE`
GO-WITH-BLOCK). This module upgrades the HB-R2 correlation-or-silence
`dichotomy` (`SiegelCorr.lean`) to a **one-sided correlation statement**: it
refutes the silence branch by forcing the hypothesis's Siegel zero `β₁` INTO
the dispatcher's zero box (via the added box-entry clause of `CorrWindowStrong`)
and re-running the dispatcher's exceptional-case (S6b case-iii) template with
`β₁` as the box witness — `by_cases` collapses, no dichotomy, one conclusion.

## Honesty / death map (R4 — no branch selection smuggled, no twin claim)

* **`SiegelSequence` is STRICTLY STRONGER than the literature's hypothesis** —
  the squared-log coupling `(1−β)·(log q)² < c` is the corpus artifact of the
  dispatcher's `√log x` box floor, NOT number theory (see `SiegelCorr`'s honesty
  block). This rung consumes that strengthened HYPOTHESIS; it is **not** a proof
  of the Twin Prime Conjecture.
* **The correlation branch is selected only on the box-entry band.** The domain
  restriction to `CorrWindowStrong` (which contains the box-entry clause
  `1 − β ≤ 3c₄/√log x`) is EXPLICIT, not a hidden selection: outside the band
  nothing is claimed. Compare `siegel_correlation_dichotomy`, which selects no
  branch at all.
* **Death map** (design §ladder verdicts): **R3a** (the dispatcher box upgrade)
  is a documented **DEAD-END** — the `√log x` geometry is the de la Vallée
  Poussin optimum; a polynomial box degrades the saving to `x²·1`. **R4**
  (beyond-level-½ error control) is **THE PREDICTED DEATH RUNG** — Heath-Brown
  needs level `x^{1/2+δ}`, the corpus's cancellation stack stops at level ½ and
  Kloosterman/Weil is absent (the same wall as Chen's `TransposedBV` and
  Maynard's `GehTail`). **R5** (assembly) is gated behind R4 and unreachable
  this sprint. **R3c** (the χ-twisted sieve weight) is the boundary-entry rung
  with its own likely death at the signed twisted main term.
-/

open Complex DirichletCharacter Salt.SW

namespace Salt.TwinBar

/-- **The strong window.** `CorrWindow` (floor `x ≥ exp(16(log q+2)²)` + residue
cap `(1−β)·log x ≤ log(3/2)`) PLUS the box-entry clause `1 − β ≤ 3·c₄/√log x`.
The last encodes the dispatcher's box membership `σ₀ − w ≤ β` exactly:
`σ₀ − w = 1 − 3a/(2s)`, `a = 2c₄`, `s = √log x`, so `3a/(2s) = 3c₄/s`. `c₄` is the
EXPOSED dispatcher constant (never a pinned numeral — `a` is opaque behind two
existentials; pinning it is the HB2 self-refutation, gate Charge 1). -/
def CorrWindowStrong (c₄ : ℝ) (q : ℕ) (β x : ℝ) : Prop :=
  CorrWindow q β x ∧ (1 - β) ≤ 3 * c₄ / Real.sqrt (Real.log x)

/-- **The box-entry reduction** (the gate's Algebra probe). The strong-window
clause `1 − β ≤ 3c₄/s` gives the dispatcher's left-edge membership
`σ₀ − w = 1 − 3(2c₄)/(2s) ≤ β`, since `3(2c₄)/(2s) = 3c₄/s`. -/
theorem boxEntry_reduces {c₄ s β : ℝ} (hs : 0 < s) (h : 1 - β ≤ 3 * c₄ / s) :
    1 - 3 * (2 * c₄) / (2 * s) ≤ β := by
  have heq : 3 * (2 * c₄) / (2 * s) = 3 * c₄ / s := by
    rw [div_eq_div_iff (show (2:ℝ) * s ≠ 0 by positivity) (show s ≠ 0 by positivity)]; ring
  rw [heq]; linarith

set_option maxHeartbeats 4000000 in
-- Re-runs the full S6b case-iii contour assembly (CharDispatch L336–532) in one
-- `set`-heavy proof; like the dispatcher it needs headroom past the default.
/-- **The forced exceptional bound.** Re-derives the S6b dispatcher head
(`CharDispatch.psi1_char_bound`, L336–432) but, given a real quadratic zero `β₁`
of `L(·,χ)` sitting in the box (supplied by the box-entry clause
`1 − β₁ ≤ 3·c₄/√log x`, `c₄ = a/2`), skips the `by_cases`/forcing and re-runs the
case-iii template directly: `β₁` IS the box witness, so the clean disjunct never
arises. Returns `9/10 ≤ β₁` (for `residue_lower`) and the exceptional bound. -/
private theorem psi1_forced_exceptional :
    ∃ c₄ K₄ : ℝ, 0 < c₄ ∧ c₄ ≤ 1 / 60000 ∧ 0 < K₄ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        ∀ {x T β₁ : ℝ}, 3 ≤ x → T = Real.exp (Real.sqrt (Real.log x)) →
          Real.log ((q : ℝ) * (T + 4)) ≤ 2 * Real.sqrt (Real.log x) →
          LFunction χ (β₁ : ℂ) = 0 → β₁ < 1 →
          1 - β₁ ≤ 3 * c₄ / Real.sqrt (Real.log x) →
          9 / 10 ≤ β₁ ∧
            ‖psi1Chi x χ + (x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖
              ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x))) := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := zero_free_region_all
  obtain ⟨c₃, hc₃pos, _hc₃⟩ := zeta_zero_free_region
  set c₀' : ℝ := min (min c₀ c₃) (1 / 3750) with hc₀'def
  have hc₀'pos : 0 < c₀' := lt_min (lt_min hc₀pos hc₃pos) (by norm_num)
  have hc₀'c₀ : c₀' ≤ c₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₀'3750 : c₀' ≤ 1 / 3750 := min_le_right _ _
  set a : ℝ := c₀' / 8 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  have ha30000 : a ≤ 1 / 30000 := by rw [hadef]; linarith [hc₀'3750]
  have ha1 : a ≤ 1 := by linarith [ha30000]
  set Kb : ℝ := 1080 + 18 / (a * Real.log (7 / 6)) with hKbdef
  have hlog76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hden : 0 < a * Real.log (7 / 6) := by positivity
  have hKbpos : 0 < Kb := by rw [hKbdef]; positivity
  obtain ⟨K₄, hK₄pos, hE⟩ := E_shape_bound ha ha1 hKbpos
  refine ⟨a / 2, K₄, by positivity, by linarith [ha30000], hK₄pos, ?_⟩
  intro q iq χ hχprim hχ1 hsq x T β₁ hx hT hq hz hβ1 hboxcl
  -- basic x facts
  have hxpos : 0 < x := by linarith
  have hlogx1 : (1:ℝ) < Real.log x := by
    have : Real.log (Real.exp 1) < Real.log x :=
      Real.log_lt_log (Real.exp_pos 1)
        (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hx)
    rwa [Real.log_exp] at this
  set L := Real.log x with hL
  set s := Real.sqrt L with hs
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hspos : 0 < s := Real.sqrt_pos.mpr hLpos
  have hs1 : 1 ≤ s := by
    rw [hs, show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]; exact Real.sqrt_le_sqrt hL1
  have hss : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hsL : s ≤ L := by rw [← hss]; nlinarith [hs1]
  have hT_eq : T = Real.exp s := hT
  have hexps : 0 < Real.exp s := Real.exp_pos s
  have hTpos : 0 < T := by rw [hT_eq]; exact hexps
  have hTge2 : (2:ℝ) ≤ T := by
    rw [hT_eq]
    exact le_trans (le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)) (Real.exp_le_exp.mpr hs1)
  -- q ≥ 2, q ≥ 1
  have hq2 : 2 ≤ q := by
    have hcond : χ.conductor = q := hχprim
    have hc1 : χ.conductor ≠ 1 := fun h => hχ1 (eq_one_iff_conductor_eq_one.mpr h)
    rw [hcond] at hc1; have := NeZero.ne q; omega
  have hq1 : 1 ≤ q := by omega
  have hqR1 : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  -- parameters σ₀, w with the linear-in-w key relations
  set w : ℝ := a / (2 * s) with hwdef
  set σ₀ : ℝ := 1 - a / s with hσ₀def
  have hwpos : 0 < w := by rw [hwdef]; positivity
  have h2w : 2 * w = a / s := by rw [hwdef]; field_simp
  have h2ws : 2 * w * s = a := by rw [hwdef]; field_simp
  have hasa : a / s ≤ a := div_le_self ha.le hs1
  have hw_bound : w ≤ 1 / 60000 := by nlinarith [h2w, hasa, ha30000]
  have hσ₀_2w : σ₀ = 1 - 2 * w := by rw [hσ₀def, ← h2w]
  have hσ₀1 : σ₀ < 1 := by rw [hσ₀_2w]; linarith [hwpos]
  have hσ₀lo : 9 / 10 ≤ σ₀ := by rw [hσ₀_2w]; linarith [hw_bound]
  have hσ₀w : 9 / 10 ≤ σ₀ - w := by rw [hσ₀_2w]; linarith [hw_bound]
  have hσ₀dec : σ₀ ≤ 1 - a / s := le_of_eq hσ₀def
  -- log q ≤ 2s
  have hlogq : Real.log (q : ℝ) ≤ 2 * s := by
    have hmono : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (T + 4)) := by
      apply Real.log_le_log hqpos
      nlinarith [mul_nonneg hqpos.le (show (0:ℝ) ≤ T + 3 by linarith)]
    linarith [hmono, hq]
  -- the edge constant B
  set L4 : ℝ := Real.log (4 * (5 * (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))))
    with hL4def
  have hL4_9s : L4 ≤ 9 * s := logL4_le q hq1 hs1 hT_eq hlogq
  have hL4nn : 0 ≤ L4 := by
    rw [hL4def]; apply Real.log_nonneg
    have hp1 : (4:ℝ) ≤ 4 + T := by linarith [hTpos]
    have hsq1 : (1:ℝ) ≤ Real.sqrt (q : ℝ) := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hqR1
    have hlq : (1:ℝ) ≤ 1 + Real.log (q : ℝ) := by linarith [Real.log_nonneg hqR1]
    have h1 : (4:ℝ) ≤ (4 + T) * Real.sqrt (q : ℝ) := by
      calc (4:ℝ) = 4 * 1 := by ring
        _ ≤ (4 + T) * Real.sqrt (q : ℝ) := mul_le_mul hp1 hsq1 (by norm_num) (by linarith [hp1])
    have step : (1:ℝ) ≤ (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
      calc (1:ℝ) ≤ 4 * 1 := by norm_num
        _ ≤ (4 + T) * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) :=
            mul_le_mul h1 hlq (by norm_num) (by linarith [h1])
    nlinarith [step]
  set Bexpr : ℝ := 120 * L4 + L4 / Real.log (7 / 6) / w with hBexprdef
  have hB0 : 0 ≤ Bexpr := by rw [hBexprdef]; positivity
  have hBs : Bexpr ≤ Kb * L := by
    have hBform : Bexpr = 120 * L4 + 2 * s * L4 / (a * Real.log (7 / 6)) := by
      rw [hBexprdef, hwdef]; field_simp
    have hnum : 2 * s * L4 ≤ 18 * L := by rw [← hss]; nlinarith [hL4_9s, hs1, hL4nn]
    have hd2 : 2 * s * L4 / (a * Real.log (7 / 6)) ≤ 18 * L / (a * Real.log (7 / 6)) := by
      rw [div_le_div_iff_of_pos_right hden]; exact hnum
    have ht1 : 120 * L4 ≤ 1080 * L := by nlinarith [hL4_9s, hsL, hL4nn]
    rw [hBform, hKbdef]
    have hsplit : (1080 + 18 / (a * Real.log (7 / 6))) * L
        = 1080 * L + 18 * L / (a * Real.log (7 / 6)) := by field_simp
    rw [hsplit]; linarith [ht1, hd2]
  -- force the Siegel zero into the box: box entry from the strong-window clause
  have h3w_eq : 3 * (a / 2) / s = 3 * w := by rw [hwdef]; ring
  rw [h3w_eq] at hboxcl
  have hval : σ₀ - w = 1 - 3 * w := by rw [hσ₀_2w]; ring
  have hbox_entry : σ₀ - w ≤ β₁ := by rw [hval]; linarith [hboxcl]
  have hβ90 : 9 / 10 ≤ β₁ := le_trans hσ₀w hbox_entry
  have hβ1_ge : 1 - 3 * w ≤ β₁ := by linarith [hbox_entry, hval]
  -- Landau window for β₁
  have hlog4q : 0 < Real.log (4 * (q : ℝ)) := by apply Real.log_pos; nlinarith [hqR1]
  have hlog4q_le : Real.log (4 * (q : ℝ)) ≤ 2 * s := by
    have hmono : Real.log (4 * (q : ℝ)) ≤ Real.log ((q : ℝ) * (T + 4)) := by
      apply Real.log_le_log (by positivity)
      nlinarith [mul_nonneg hqpos.le hTpos.le]
    linarith [hmono, hq]
  have hβwin : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₁ := by
    have hkey : 3 * w ≤ (1 / 5000) / Real.log (4 * (q : ℝ)) := by
      rw [le_div_iff₀ hlog4q]
      nlinarith [mul_le_mul_of_nonneg_left hlog4q_le (show (0:ℝ) ≤ 3 * w by positivity),
        h2ws, ha30000, hspos, hwpos]
    linarith [hβ1_ge, hkey]
  have hsimple : analyticOrderAt (LFunction χ) (β₁ : ℂ) = 1 :=
    (landau_one_exceptional_at hχprim hχ1 hz hz hβwin hβwin).2
  -- the adaptive box
  set σ₀'' : ℝ := min σ₀ (β₁ - 2 * w) with hσ''def
  have hσ''le : σ₀'' ≤ σ₀ := min_le_left _ _
  have hσ''le2 : σ₀'' ≤ β₁ - 2 * w := min_le_right _ _
  have hσ''βsep : σ₀'' + w ≤ β₁ := by linarith [hσ''le2, hwpos]
  have hσ''dec : σ₀'' ≤ 1 - a / s := le_trans hσ''le hσ₀dec
  have hσ''1 : σ₀'' < 1 := lt_of_le_of_lt hσ''le hσ₀1
  have hσ''w : 9 / 10 ≤ σ₀'' - w := by
    have hA : 9 / 10 + w ≤ σ₀ := by rw [hσ₀_2w]; linarith [hw_bound]
    have hB : 9 / 10 + w ≤ β₁ - 2 * w := by linarith [hβ1_ge, hw_bound]
    have := le_min hA hB; rw [hσ''def]; linarith [this]
  have hσ''lo : 9 / 10 ≤ σ₀'' := by linarith [hσ''w, hwpos]
  -- hzf for the exceptional variant: every box zero equals β₁
  have hzfexc : ∀ ρ : ℂ, LFunction χ ρ = 0 → σ₀'' - w ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T + 2 →
      ρ = (β₁ : ℂ) := by
    intro ρ hρ0 hρre1 _hρre2 hρim
    have hρhalf : 1 / 2 ≤ ρ.re := by linarith [hρre1, hσ''w]
    have hσ''w_ge : 1 - 6 * w ≤ σ₀'' - w := by
      have hA : 1 - 6 * w + w ≤ σ₀ := by rw [hσ₀_2w]; linarith
      have hB : 1 - 6 * w + w ≤ β₁ - 2 * w := by linarith [hβ1_ge]
      have := le_min hA hB; rw [hσ''def]; linarith [this]
    have hρim0 : ρ.im = 0 := by
      by_contra hne
      have hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := Or.inr hne
      have hb2 : ρ.re ≤ 1 - c₀ / (2 * s) :=
        dispatch_zero_re_le χ hc₀pos (hc₀ q χ hχprim hχ1) hq1 hspos hq hρ0 hρhalf hρim hor
      have hc0_6a : 6 * a < c₀ := by rw [hadef]; nlinarith [hc₀'c₀, hc₀pos]
      have h6as : 6 * w < c₀ / (2 * s) := by
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * s)]; nlinarith [hc0_6a, h2ws]
      linarith [hρre1, hb2, hσ''w_ge, h6as]
    have hρeq : ρ = (ρ.re : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im]; exact hρim0
    have hzρ : LFunction χ (ρ.re : ℂ) = 0 := hρeq ▸ hρ0
    have hρwin : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ ρ.re := by
      have hρ_ge : 1 - 6 * w ≤ ρ.re := by linarith [hρre1, hσ''w_ge]
      have hkey : 6 * w ≤ (1 / 5000) / Real.log (4 * (q : ℝ)) := by
        rw [le_div_iff₀ hlog4q]
        nlinarith [mul_le_mul_of_nonneg_left hlog4q_le (show (0:ℝ) ≤ 6 * w by positivity),
          h2ws, ha30000, hspos, hwpos]
      linarith [hρ_ge, hkey]
    have heqβ : ρ.re = β₁ := (landau_one_exceptional_at hχprim hχ1 hzρ hz hρwin hβwin).1
    rw [hρeq, heqβ]
  -- assemble: no clean disjunct, β₁ is the box witness
  refine ⟨hβ90, le_trans
    (psi1_contour_shift_exceptional χ hχprim hq2 hx hTge2 hwpos hσ''w hσ''1 hσ''βsep hβ1
      hsimple hzfexc)
    (hE hx hT hσ''lo hσ''dec hB0 hBs)⟩

/-- **THE CORRELATION STATEMENT (HB-R3b).** Under `SiegelSequence`: there are
universal dispatcher constants `c₄, K₄ > 0` such that for every strength `c`
there exist exceptional data `(q, χ, β₁)` with `(1−β₁)(log q)² < c`, for which
(i) the strong window is INHABITED at the floor scale
`x₀ = exp(16(log q+2)²)` — the in-kernel anti-vacuity guard — and (ii) at EVERY
strong-window scale `x`, `ψ₁(x,χ)` is DEFINITIVELY large-negative:
`‖ψ₁ + x^{β₁+1}/(β₁(β₁+1))‖ ≤ K₄ x² e^{−c₄√log x}` while the residue is `≥ x²/3`.
No silence disjunct — the domain restriction to the box-entry band (the
`CorrWindowStrong` clause) is what forces the correlation.

NOT a twin claim. `SiegelSequence` is a (squared-log, strictly-stronger-than-
textbook) HYPOTHESIS; this rung selects the correlation branch only on the
box-entry band. Death map: R3a (box upgrade) DEAD-END; R4 (beyond-level-½ /
Kloosterman) THE PREDICTED DEATH RUNG; R5 (assembly) gated behind R4,
unreachable; R3c (χ-twisted sieve) the boundary-entry rung with its own likely
death. See `docs/exploration/s3-hb3-design.md` and the `SiegelCorr` honesty
block (one-way bridge; no branch smuggled). -/
theorem siegel_correlation_strong (hSeq : SiegelSequence) :
    ∃ c₄ K₄ : ℝ, 0 < c₄ ∧ 0 < K₄ ∧
      ∀ c : ℝ, 0 < c → ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β₁ : ℝ),
        1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
        LFunction χ (β₁ : ℂ) = 0 ∧ (1 - β₁) * (Real.log q) ^ 2 < c ∧ β₁ < 1 ∧
        CorrWindowStrong c₄ q β₁ (Real.exp (16 * (Real.log (q : ℝ) + 2) ^ 2)) ∧
        ∀ x : ℝ, CorrWindowStrong c₄ q β₁ x →
          x ^ 2 / 3 ≤ ‖(x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖ ∧
          ‖psi1Chi x χ + (x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖
              ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x))) := by
  obtain ⟨c₄, K₄, hc₄pos, hc₄small, hK₄pos, hforced⟩ := psi1_forced_exceptional
  refine ⟨c₄, K₄, hc₄pos, hK₄pos, ?_⟩
  intro c hc
  have hmin_pos : 0 < min c (c₄ / 10) := lt_min hc (by positivity)
  obtain ⟨q, hqz, χ, β₁, h1q, hprim, hsq, hne, hLzero, hcoup, hβ1⟩ :=
    hSeq (min c (c₄ / 10)) hmin_pos
  haveI := hqz
  have hcoup_c : (1 - β₁) * (Real.log q) ^ 2 < c := lt_of_lt_of_le hcoup (min_le_left _ _)
  have hcoup_10 : (1 - β₁) * (Real.log q) ^ 2 < c₄ / 10 := lt_of_lt_of_le hcoup (min_le_right _ _)
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h1q
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ q)
  have hlogq_pos : 0 < Real.log q := Real.log_pos hqR1
  have h1β : 0 < 1 - β₁ := by linarith
  have hlogq_lb : (0.6931 : ℝ) < Real.log q :=
    lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) hqR2)
  refine ⟨q, hqz, χ, β₁, h1q, hprim, hsq, hne, hLzero, hcoup_c, hβ1, ?_, ?_⟩
  · -- anti-vacuity witness at the floor scale x₀ = exp(16(log q + 2)²)
    have hln32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 / 3 by norm_num)
      rw [show (2:ℝ) / 3 = (3 / 2)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hstep2 : (1 - β₁) * (Real.log q) ^ 2 < 1 / 600000 := by linarith [hcoup_10, hc₄small]
    refine ⟨⟨le_refl _, ?_⟩, ?_⟩
    · -- residue cap: (1 − β₁) · log x₀ ≤ log(3/2)
      rw [Real.log_exp]
      have hstep1 : (1 - β₁) * (Real.log q + 2) ^ 2 ≤ 20 * ((1 - β₁) * (Real.log q) ^ 2) := by
        nlinarith [mul_nonneg h1β.le
          (show (0:ℝ) ≤ 20 * (Real.log q) ^ 2 - (Real.log q + 2) ^ 2 by
            nlinarith [hlogq_lb, sq_nonneg (Real.log q - 0.6931)])]
      calc (1 - β₁) * (16 * (Real.log q + 2) ^ 2)
          = 16 * ((1 - β₁) * (Real.log q + 2) ^ 2) := by ring
        _ ≤ 16 * (20 * ((1 - β₁) * (Real.log q) ^ 2)) :=
            mul_le_mul_of_nonneg_left hstep1 (by norm_num)
        _ = 320 * ((1 - β₁) * (Real.log q) ^ 2) := by ring
        _ ≤ 320 * (1 / 600000) := mul_le_mul_of_nonneg_left hstep2.le (by norm_num)
        _ ≤ Real.log (3 / 2) := by linarith [hln32]
    · -- box-entry clause: 1 − β₁ ≤ 3c₄/√log x₀
      have hsqrt0 : Real.sqrt (Real.log (Real.exp (16 * (Real.log (q : ℝ) + 2) ^ 2)))
          = 4 * (Real.log q + 2) := by
        rw [Real.log_exp,
          show (16:ℝ) * (Real.log (q : ℝ) + 2) ^ 2 = (4 * (Real.log q + 2)) ^ 2 by ring,
          Real.sqrt_sq (by nlinarith [hlogq_pos])]
      rw [hsqrt0, le_div_iff₀ (by nlinarith [hlogq_pos] : (0:ℝ) < 4 * (Real.log q + 2))]
      calc (1 - β₁) * (4 * (Real.log q + 2))
          ≤ (1 - β₁) * (30 * (Real.log q) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (by nlinarith [hlogq_lb, sq_nonneg (Real.log q - 0.6931)]) h1β.le
        _ = 30 * ((1 - β₁) * (Real.log q) ^ 2) := by ring
        _ ≤ 30 * (c₄ / 10) := by linarith [hcoup_10]
        _ = 3 * c₄ := by ring
  · -- every strong-window scale: residue lower bound AND the forced bound
    intro x hcws
    obtain ⟨hwin, hboxcl⟩ := hcws
    obtain ⟨hx3, hqbox⟩ := corrWindow_box hwin
    obtain ⟨h90, hbnd⟩ := hforced q χ hprim hne hsq hx3 rfl hqbox hLzero hβ1 hboxcl
    exact ⟨residue_lower h90 hβ1 hwin, hbnd⟩

end Salt.TwinBar
