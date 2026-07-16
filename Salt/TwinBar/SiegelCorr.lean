/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SiegelTwin
import Salt.SW.CharDispatch
import Salt.SW.LandauPage

/-!
# The μ↔χ correlation core (S3-HB-R2)

Design: `docs/exploration/s3-hb2-design.md` (FROZEN, decision **P1**; gate
`963a3b1` GO-WITH-APPENDIX-A). This module lands the *correlation-or-silence
dichotomy* — the honest lift of the residue term `−x^{β₁+1}/(β₁(β₁+1))` that the
landed dispatcher `Salt.SW.psi1_char_bound` (`CharDispatch.lean`) exposes in its
exceptional branch. Where the SW gate used that residue to KILL the exceptional
character, HB-R2 inverts the orientation: under a Siegel-zero *sequence*, the
primes either impersonate `χ` (ψ₁ ≈ −residue, residue provably `≥ x²/3`) or fall
silent (ψ₁ exponentially small). No third behavior; both branches
kernel-quantified.

## Honesty (R4 — no branch selection smuggled)

* **`SiegelSequence` is STRICTLY STRONGER than the literature's hypothesis.**
  Tao 2015 Thm 4 / HB 1983 take the *first-power* coupling `(1−β)·log q → 0`.
  `SiegelSequence` here carries the *squared-log* coupling `(1−β)·(log q)² < c`
  (`∀c∃` form). The extra `log` power is a **corpus artifact** of the
  dispatcher's `√log x` box floor (`log(q(T+4)) ≤ 2√log x` forces
  `x ≥ exp(16(log q+2)²)`), NOT number theory. This is recorded so the writeup
  never claims HB-R2 consumes the textbook hypothesis.
* **The bridge is one-way.** `siegelSequence_implies_infinitely` proves
  `SiegelSequence → InfinitelyManySiegelZeros` (the honesty direction: our
  strengthened input still entails the weak HB-R1 hypothesis). The converse is
  NOT proved — `InfinitelyManySiegelZeros` (∀c∃ at first power) does not supply
  the `q`-vs-`(1−β)` coupling the correlation window needs.
* **`HeathBrownStatement` is NOT wired to this core.** HB-R1's
  `HeathBrownStatement` (Siegel zeros ⇒ twin primes) stays decoupled;
  `siegel_correlation_dichotomy` selects no branch, so it does not close the
  twin-prime implication. Upgrading the box floor to the first-power coupling —
  and thereby selecting the correlation branch — is the **HB-R3+ door**.
-/

open Complex DirichletCharacter Salt.SW

namespace Salt.TwinBar

/-- **A Siegel-zero sequence** — the `∀c∃` hypothesis with the *squared-log*
coupling `(1−β)·(log q)² < c`. STRICTLY STRONGER than
`InfinitelyManySiegelZeros` (which has `1 − c/log q < β`, first power): the extra
`log` is the corpus artifact of the dispatcher's `√log x` box floor. Faithful to
the literature's "infinitely many Siegel zeros along a sequence `qₙ → ∞`"; the
`∀c∃` shape auto-entails `q → ∞`. This is HB-R2's hypothesis. -/
def SiegelSequence : Prop :=
  ∀ c : ℝ, 0 < c → ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β : ℝ),
    1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    LFunction χ β = 0 ∧ (1 - β) * (Real.log q) ^ 2 < c ∧ β < 1

/-- **The one-way honesty bridge.** The strengthened `SiegelSequence` still
entails HB-R1's `InfinitelyManySiegelZeros`: invoking the sequence at
`c·log 2` and using `log q ≥ log 2` (so `q ≥ 2`) converts the squared-log gap
into the first-power gap. The converse is NOT provable here (see the module
docstring). -/
theorem siegelSequence_implies_infinitely (h : SiegelSequence) :
    InfinitelyManySiegelZeros := by
  intro c hc
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨q, hqz, χ, β, h1q, hprim, hsq, hne, hLzero, hcoup, hβ1⟩ :=
    h (c * Real.log 2) (mul_pos hc hlog2pos)
  refine ⟨q, hqz, χ, β, h1q, hprim, hsq, hne, hLzero, ?_, hβ1⟩
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h1q
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ q)
  have hlogq_pos : 0 < Real.log q := Real.log_pos hqR1
  have hlog2q : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqR2
  have h1β : 0 < 1 - β := by linarith
  have key : (1 - β) * Real.log q < c := by
    have h1 : (1 - β) * Real.log q * Real.log 2 ≤ (1 - β) * (Real.log q) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlog2q (mul_nonneg h1β.le hlogq_pos.le)]
    have h2 : (1 - β) * Real.log q * Real.log 2 < c * Real.log 2 := lt_of_le_of_lt h1 hcoup
    exact lt_of_mul_lt_mul_right h2 hlog2pos.le
  have hfrac : 1 - β < c / Real.log q := by
    rw [lt_div_iff₀ hlogq_pos]; linarith [key]
  linarith [hfrac]

/-- **The correlation window** (two-sided, β-form). The floor
`x ≥ exp(16(log q+2)²)` supplies the dispatcher's box constraint; the cap
`(1−β)·log x ≤ log(3/2)` keeps the Siegel residue `≥ x²/3`. Both are consumed by
`corrWindow_box` / `residue_lower`. -/
def CorrWindow (q : ℕ) (β x : ℝ) : Prop :=
  Real.exp (16 * (Real.log q + 2) ^ 2) ≤ x ∧ (1 - β) * Real.log x ≤ Real.log (3 / 2)

/-- **The box-constraint discharge.** The window floor forces `√log x ≥ 4(log q+2)`,
hence `x ≥ 3` and the dispatcher's smallness hypothesis
`log(q(e^{√log x}+4)) ≤ 2√log x` at `T = e^{√log x}` (pure log/√ arithmetic:
`e^{√log x}+4 ≤ 2e^{√log x}` and `log q + log 2 ≤ √log x`). -/
theorem corrWindow_box {q : ℕ} {β x : ℝ} (h : CorrWindow q β x) :
    3 ≤ x ∧ Real.log ((q : ℝ) * (Real.exp (Real.sqrt (Real.log x)) + 4))
      ≤ 2 * Real.sqrt (Real.log x) := by
  obtain ⟨hfloor, _hcap⟩ := h
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hexppos : 0 < Real.exp (16 * (Real.log q + 2) ^ 2) := Real.exp_pos _
  have hxpos : 0 < x := lt_of_lt_of_le hexppos hfloor
  have hlogx_ge : 16 * (Real.log q + 2) ^ 2 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).mpr hfloor
  have h3x : 3 ≤ x := by
    have he : Real.exp (64 : ℝ) ≤ x :=
      le_trans (Real.exp_le_exp.mpr (by nlinarith [hlogq_nn])) hfloor
    have h65 : (65 : ℝ) ≤ Real.exp 64 := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  refine ⟨h3x, ?_⟩
  set s := Real.sqrt (Real.log x) with hs
  have hlogx_nn : 0 ≤ Real.log x := by nlinarith [hlogq_nn, hlogx_ge]
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs_ge : 4 * (Real.log q + 2) ≤ s := by
    have h1 : (4 * (Real.log q + 2)) ^ 2 ≤ Real.log x := by nlinarith [hlogx_ge]
    calc 4 * (Real.log q + 2)
        = Real.sqrt ((4 * (Real.log q + 2)) ^ 2) := (Real.sqrt_sq (by nlinarith [hlogq_nn])).symm
      _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt h1
      _ = s := hs.symm
  have hs8 : 8 ≤ s := by nlinarith [hs_ge, hlogq_nn]
  have hexps4 : 4 ≤ Real.exp s := by
    have hlog4le : Real.log 4 ≤ s := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith [hs8]
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp s := Real.exp_le_exp.mpr hlog4le
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · subst hq0; simp only [Nat.cast_zero, zero_mul, Real.log_zero]; linarith [hs_nn]
  · have hqRpos : 0 < (q : ℝ) := by exact_mod_cast hqpos
    have hexps4pos : 0 < Real.exp s + 4 := by positivity
    rw [Real.log_mul hqRpos.ne' hexps4pos.ne']
    have hle1 : Real.exp s + 4 ≤ 2 * Real.exp s := by linarith [hexps4]
    have hlog_es : Real.log (Real.exp s + 4) ≤ Real.log 2 + s := by
      calc Real.log (Real.exp s + 4)
          ≤ Real.log (2 * Real.exp s) := Real.log_le_log (by positivity) hle1
        _ = Real.log 2 + s := by
            rw [Real.log_mul (by norm_num) (Real.exp_pos s).ne', Real.log_exp]
    have hlogq_s : Real.log q + Real.log 2 ≤ s := by
      nlinarith [hs_ge, hlogq_nn, Real.log_two_lt_d9]
    linarith [hlog_es, hlogq_s]

/-- **The Siegel residue is `≥ x²/3`** — the quantitative separation. For
`β₁ ∈ [9/10, 1)` at a window scale, `‖x^{β₁+1}/(β₁(β₁+1))‖ ≥ x²/3`: the window cap
`(1−β₁)·log x ≤ log(3/2)` forces `x^{β₁+1} ≥ (2/3)x²`, and `β₁(β₁+1) < 2`. -/
theorem residue_lower {q : ℕ} {β₁ x : ℝ} (h90 : 9 / 10 ≤ β₁) (hβ1 : β₁ < 1)
    (hwin : CorrWindow q β₁ x) :
    x ^ 2 / 3 ≤ ‖(x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖ := by
  obtain ⟨hfloor, hcap⟩ := hwin
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hfloor
  have hβ1pos : 0 < β₁ := by linarith
  have hdpos : 0 < β₁ * (β₁ + 1) := mul_pos hβ1pos (by linarith)
  have hnum : ‖(x : ℂ) ^ ((β₁ : ℂ) + 1)‖ = x ^ (β₁ + 1 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp [Complex.add_re, Complex.one_re, Complex.ofReal_re]
  have hden : ‖(β₁ : ℂ) * ((β₁ : ℂ) + 1)‖ = β₁ * (β₁ + 1) := by
    rw [show ((β₁ : ℂ) + 1) = ((β₁ + 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
  rw [norm_div, hnum, hden]
  have hxr : x ^ (1 - β₁ : ℝ) ≤ 3 / 2 := by
    rw [Real.rpow_def_of_pos hxpos]
    calc Real.exp (Real.log x * (1 - β₁))
        ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr (by nlinarith [hcap])
      _ = 3 / 2 := Real.exp_log (by norm_num)
  have hx2 : x ^ (2 : ℝ) = x ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hprod : x ^ (β₁ + 1 : ℝ) * x ^ (1 - β₁ : ℝ) = x ^ 2 := by
    rw [← Real.rpow_add hxpos, show β₁ + 1 + (1 - β₁) = (2 : ℝ) by ring, hx2]
  have hRpos : 0 < x ^ (β₁ + 1 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hnumlow : 2 / 3 * x ^ 2 ≤ x ^ (β₁ + 1 : ℝ) := by
    have hslack : 0 ≤ 3 / 2 - x ^ (1 - β₁ : ℝ) := by linarith [hxr]
    nlinarith [hprod, mul_nonneg hRpos.le hslack]
  have hdlt : β₁ * (β₁ + 1) ≤ 2 := by
    nlinarith [mul_pos (show (0 : ℝ) < 1 - β₁ by linarith) (show (0 : ℝ) < β₁ + 2 by linarith)]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hdpos]
  nlinarith [hnumlow,
    mul_nonneg (sq_nonneg x) (by linarith [hdlt] : (0 : ℝ) ≤ 2 - β₁ * (β₁ + 1))]

/-- **The correlation-or-silence dichotomy** (the HB-R2 core). Under
`SiegelSequence`: for every strength `c` there are exceptional data `(q, χ, β₁)`
with `(1−β₁)(log q)² < c` such that at every window scale, either `ψ₁(x,χ)` tracks
the Siegel residue `−x^{β₁+1}/(β₁(β₁+1))` to exponential accuracy, or `ψ₁(x,χ)` is
exponentially small — while the residue itself is `≥ x²/3`. The primes either
impersonate `χ` or fall silent; no third behavior. No branch is selected: which
disjunct fires at a given scale is the HB-R3+ door, not decided here. -/
theorem siegel_correlation_dichotomy (hSeq : SiegelSequence) :
    ∃ c₄ K₄ : ℝ, 0 < c₄ ∧ 0 < K₄ ∧
      ∀ c : ℝ, 0 < c → ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β₁ : ℝ),
        1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
        LFunction χ (β₁ : ℂ) = 0 ∧ (1 - β₁) * (Real.log q) ^ 2 < c ∧ β₁ < 1 ∧
        ∀ x : ℝ, CorrWindow q β₁ x →
          x ^ 2 / 3 ≤ ‖(x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖ ∧
          (‖psi1Chi x χ + (x : ℂ) ^ ((β₁ : ℂ) + 1) / ((β₁ : ℂ) * ((β₁ : ℂ) + 1))‖
              ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x)))
            ∨ ‖psi1Chi x χ‖ ≤ K₄ * x ^ 2 * Real.exp (-(c₄ * Real.sqrt (Real.log x)))) := by
  obtain ⟨c₄, K₄, hc₄pos, hK₄pos, hdisp⟩ := psi1_char_bound
  refine ⟨c₄, K₄, hc₄pos, hK₄pos, ?_⟩
  intro c hc
  have hc'pos : 0 < min c (1 / 25000) := lt_min hc (by norm_num)
  obtain ⟨q, hqz, χ, β₁, h1q, hprim, hsq, hne, hLzero, hcoup, hβ1⟩ :=
    hSeq (min c (1 / 25000)) hc'pos
  haveI := hqz
  have hcoup_c : (1 - β₁) * (Real.log q) ^ 2 < c := lt_of_lt_of_le hcoup (min_le_left _ _)
  have hcoup_25 : (1 - β₁) * (Real.log q) ^ 2 < 1 / 25000 :=
    lt_of_lt_of_le hcoup (min_le_right _ _)
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h1q
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ q)
  have hqRpos : 0 < (q : ℝ) := by linarith
  have hlogq_pos : 0 < Real.log q := Real.log_pos hqR1
  have h1β : 0 < 1 - β₁ := by linarith
  have hlogq_lb : (0.6931 : ℝ) < Real.log q :=
    lt_of_lt_of_le (by linarith [Real.log_two_gt_d9]) (Real.log_le_log (by norm_num) hqR2)
  have hlq2ge : (0.48 : ℝ) ≤ (Real.log q) ^ 2 := by
    nlinarith [hlogq_lb, sq_nonneg (Real.log q - 0.6931)]
  have h90 : 9 / 10 ≤ β₁ := by
    nlinarith [hcoup_25, mul_le_mul_of_nonneg_left hlq2ge h1β.le]
  have hlog4q_pos : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by nlinarith [hqR2])
  have hlog4 : Real.log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    nlinarith [Real.log_two_lt_d9]
  have hlog4q : Real.log (4 * (q : ℝ)) ≤ 5 * (Real.log q) ^ 2 := by
    rw [Real.log_mul (by norm_num) hqRpos.ne']
    nlinarith [hlog4, hlogq_lb, sq_nonneg (Real.log q - 0.6931)]
  have hβwin_hyp : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₁ := by
    have hmul4 : (1 - β₁) * Real.log (4 * (q : ℝ)) ≤ (1 - β₁) * (5 * (Real.log q) ^ 2) :=
      mul_le_mul_of_nonneg_left hlog4q h1β.le
    have hkey : (1 - β₁) * Real.log (4 * (q : ℝ)) < 1 / 5000 := by nlinarith [hcoup_25, hmul4]
    have hfrac : 1 - β₁ ≤ (1 / 5000) / Real.log (4 * (q : ℝ)) := by
      rw [le_div_iff₀ hlog4q_pos]; linarith [hkey]
    linarith [hfrac]
  refine ⟨q, hqz, χ, β₁, h1q, hprim, hsq, hne, hLzero, hcoup_c, hβ1, ?_⟩
  intro x hwin
  refine ⟨residue_lower h90 hβ1 hwin, ?_⟩
  obtain ⟨hx3, hboxc⟩ := corrWindow_box hwin
  rcases hdisp q χ hprim hne hx3 rfl hboxc with hclean |
    ⟨β₁', hz', _horder', _hsq2, _h90lt, hβwin', hbnd'⟩
  · exact Or.inr hclean
  · have hid := landau_one_exceptional_at hprim hne hLzero hz' hβwin_hyp hβwin'
    rw [← hid.1] at hbnd'
    exact Or.inl hbnd'

end Salt.TwinBar
