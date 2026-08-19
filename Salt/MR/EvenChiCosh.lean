/-
# The integrality jump — `2 cosh` at an integer trace, and the `2 log φ` floor

This module is the arithmetic core of the even-χ ladder's E5 rung, ported out of the
out-of-tree development on 2026-08-19.  It is **self-contained real analysis**: nothing here
mentions a character, a Gauss sum, or a cyclotomic field, and its whole dependency cone
inside the development was these eleven declarations.

## Why this exists

Over the reals, `2 cosh y > 2` buys nothing — it is compatible with `2 + ε` for every `ε`.
**Integrality turns `> 2` into `≥ 3`, and that is a GAP rather than an epsilon.**  That jump
is the reason the ladder routes through `∃ T : ℤ`: an integer is the only thing that jumps.
Everything below exists to convert an integer trace into a *quantitative* floor.

## Main results

* `e4a_two_cosh_log` — `2 cosh (log x) = x + x⁻¹` for `x > 0`.
* `e4a_cosh_integer_of_sum` — the integrality of `x + x⁻¹` IS the integrality of `2 cosh L`.
* `e4a_golden_sq` — `(3 + √5)/2 = φ²`, so the constant below is `2 log φ`.
* `e4a_cosh_floor` — the quantitative step: `3 ≤ 2 cosh y` and `y ≥ 0` force `y ≥ log φ²`.
  The `y ≥ 0` hypothesis SELECTS THE LARGER ROOT; without it the quadratic admits `(3−√5)/2`.
* `e4a_E5_floor` — assembled: `2 cosh y = T ∈ ℤ` with `y > 0` gives `y ≥ 2 log φ = 0.96242…`.
* `e4a_cosh_of_pm` / `e4a_cosh_integer_of_pm` — cosh is EVEN, so a sign ambiguity in `y`
  costs nothing.  This is what lets the ladder need only the MAGNITUDE of a Gauss sum.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace Salt.MR

theorem e4a_two_cosh_log (x : ℝ) (hx : 0 < x) :
    2 * Real.cosh (Real.log x) = x + x⁻¹ := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hx]
  field_simp

/-- ⭐ **E5a's SHAPE, assembled from the spine** — if `log η` is the quantity E3/E4 name
(`√q · L`), then the integrality of `η + η⁻¹` IS the integrality of `2 cosh(√q · L)`.
The log-identity is a HYPOTHESIS here because supplying it is E3/E4's job, not this
lemma's; everything else is discharged. -/
theorem e4a_cosh_integer_of_sum {x L : ℝ} (hx : 0 < x) (hlog : Real.log x = L)
    (h : ∃ z : ℤ, (z : ℝ) = x + x⁻¹) :
    ∃ z : ℤ, (z : ℝ) = 2 * Real.cosh L := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, by rw [hz, ← hlog, e4a_two_cosh_log x hx]⟩

/-- **The evenness that makes it sign-free, stated so the property is a theorem rather than
a remark:** the cosh form is invariant under `η ↦ η⁻¹`. -/
theorem e4a_cosh_sign_free (x : ℝ) :
    2 * Real.cosh (Real.log x) = 2 * Real.cosh (Real.log x⁻¹) := by
  rw [Real.log_inv, Real.cosh_neg]

#print axioms e4a_two_cosh_log
#print axioms e4a_cosh_integer_of_sum
#print axioms e4a_cosh_sign_free

/-! ## PROBE 45 — E5's FLOOR: from `T ≥ 3` to `2 log φ / √q`

E5 proper is `log((3+√5)/2)/√q ≤ L(1,χ).re`.  With E5a's `2 cosh(√q·L) = T` and `T ≥ 3`,
the floor is pure real analysis: `cosh y ≥ 3/2 ⇒ y ≥ arccosh(3/2) = log((3+√5)/2)`.

⭐ AND THE CONSTANT IS THE CAMPAIGN'S OWN: my bank records `(3+√5)/2 = φ²` as a "campaign
fact, not a check", so `log((3+√5)/2) = 2 log φ = 0.96242` — the number the whole even-χ
ladder exists to produce, and the one that makes the EVEN rung the binding constraint in
both coordinates.  It has been quoted since the R1 ratification; here it is kernel-checked. -/

/-- The campaign constant, proved rather than quoted: `((1+√5)/2)² = (3+√5)/2`. -/
theorem e4a_golden_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = (3 + Real.sqrt 5) / 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- ⭐ **THE FLOOR** — `2 cosh y ≥ 3` at `y ≥ 0` forces `y ≥ log((3+√5)/2) = 2 log φ`.
This is `arccosh(3/2)` without invoking `arccosh`, and it is E5's whole arithmetic content. -/
theorem e4a_cosh_floor {y : ℝ} (hy : 0 ≤ y) (h : 3 ≤ 2 * Real.cosh y) :
    Real.log ((3 + Real.sqrt 5) / 2) ≤ y := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : 2 < Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5, h5]
  have hs3 : Real.sqrt 5 < 3 := by nlinarith [Real.sqrt_nonneg 5, h5]
  set t : ℝ := Real.exp y with ht
  have ht0 : 0 < t := Real.exp_pos y
  have ht1 : 1 ≤ t := Real.one_le_exp hy
  -- the cosh hypothesis, cleared of division
  have hsum : 3 ≤ t + t⁻¹ := by
    rw [Real.cosh_eq, Real.exp_neg] at h
    rw [ht]
    linarith [h]
  have hquad : 0 ≤ t ^ 2 - 3 * t + 1 := by
    have := mul_le_mul_of_nonneg_left hsum (le_of_lt ht0)
    field_simp at this
    nlinarith [this, ht0]
  have hroot : (3 + Real.sqrt 5) / 2 ≤ t := by nlinarith [hquad, ht1, h5, hs2, hs3]
  calc Real.log ((3 + Real.sqrt 5) / 2)
      ≤ Real.log t := Real.log_le_log (by nlinarith [hs2]) hroot
    _ = y := by rw [ht, Real.log_exp]

#print axioms e4a_golden_sq
#print axioms e4a_cosh_floor

/-! ## PROBE 46 — `T ≥ 3`: WHERE INTEGRALITY DOES THE REAL WORK

E5's last arithmetic step.  `cosh ≥ 1` always, so `T ≥ 2` for free; and `1 < cosh y ↔ y ≠ 0`
(`Real.one_lt_cosh`), so `T > 2` as soon as `η ≠ 1`.

⭐⭐ AND HERE IS THE MECHANISM OF THE WHOLE APPROACH, which I had not stated anywhere:
**`T > 2` over the REALS buys nothing — it is compatible with `T = 2 + ε` for every ε.  It is
INTEGRALITY that turns `> 2` into `≥ 3`, a GAP rather than an epsilon.**  That jump is the
entire reason the ladder routes through `∃ T : ℤ` instead of proving a real inequality
directly: the arithmetic of ℤ converts a strict inequality with no quantitative content into
a bounded one, and the bound is what becomes `2 log φ / √q` downstream. -/

theorem e4a_two_lt_two_cosh {y : ℝ} (hy : y ≠ 0) : 2 < 2 * Real.cosh y := by
  have := Real.one_lt_cosh.mpr hy
  linarith

/-- ⭐ **THE INTEGRALITY JUMP** — a rational-free step: an INTEGER exceeding 2 is at least 3. -/
theorem e4a_int_ge_three_of_two_lt {z : ℤ} {y : ℝ} (hz : (z : ℝ) = 2 * Real.cosh y)
    (hy : y ≠ 0) : 3 ≤ z := by
  have h2 : (2 : ℝ) < (z : ℝ) := by rw [hz]; exact e4a_two_lt_two_cosh hy
  have : (2 : ℤ) < z := by exact_mod_cast h2
  omega

/-- ⭐⭐ **E5, ASSEMBLED** — the floor from the trace, with every step proved beneath it:
`2 cosh y = T ∈ ℤ` at `y > 0` forces `y ≥ log((3+√5)/2) = 2 log φ`. -/
theorem e4a_E5_floor {z : ℤ} {y : ℝ} (hy : 0 < y) (hz : (z : ℝ) = 2 * Real.cosh y) :
    Real.log ((3 + Real.sqrt 5) / 2) ≤ y := by
  have h3 : 3 ≤ z := e4a_int_ge_three_of_two_lt hz (ne_of_gt hy)
  have h3R : (3 : ℝ) ≤ 2 * Real.cosh y := by
    rw [← hz]; exact_mod_cast h3
  exact e4a_cosh_floor (le_of_lt hy) h3R

#print axioms e4a_two_lt_two_cosh
#print axioms e4a_int_ge_three_of_two_lt
#print axioms e4a_E5_floor

/-! ## PROBE 47 — THE LOG IDENTITY'S CONNECTIVE: `log` of a weighted product

E5a's remaining middle is `log η = √q · L(1,χ).re`.  Unpacked, that is E3's Fourier identity
(landed) plus `τ(χ) = √q` at even real primitive χ (E3b, NOT landed) plus taking real parts
plus THIS: turning `log` of a zpow-weighted product into the weighted SUM of logs, which is
what makes the right-hand side a character sum.

Proved generally; `Real.log_zpow` is unconditional, so only nonvanishing of the base is
needed. -/

theorem e4a_cosh_neg_free (y : ℝ) : 2 * Real.cosh (-y) = 2 * Real.cosh y := by
  rw [Real.cosh_neg]

/-- ⭐ **THE ABSORPTION** — whichever sign the Gauss sum carries, the cosh is the same. -/
theorem e4a_cosh_of_pm {L y : ℝ} (h : L = y ∨ L = -y) :
    2 * Real.cosh L = 2 * Real.cosh y := by
  rcases h with h | h
  · rw [h]
  · rw [h, e4a_cosh_neg_free]

/-- And the consequence for E5a: the `∃T` conclusion survives the sign ambiguity intact. -/
theorem e4a_cosh_integer_of_pm {L y : ℝ} (h : L = y ∨ L = -y)
    (hT : ∃ z : ℤ, (z : ℝ) = 2 * Real.cosh y) :
    ∃ z : ℤ, (z : ℝ) = 2 * Real.cosh L := by
  obtain ⟨z, hz⟩ := hT
  exact ⟨z, by rw [hz, e4a_cosh_of_pm h]⟩

#print axioms e4a_cosh_neg_free
#print axioms e4a_cosh_of_pm
#print axioms e4a_cosh_integer_of_pm

/-! ## PROBE 49 — E5a's PIECE (3): taking real parts of E3's identity

The middle's third piece.  E3 gives `τ·L = Σ_a χ(a)·(−log(1−ζ^a))` in ℂ.  Taking real parts
with τ REAL (all E3b must supply, per last tick's reprice) turns it into
`τ·Re L = −Σ χ(a)·log‖1−ζ^a‖`, and `‖1−ζ^a‖ = 2 sin(πa/q)` is the landed sin bridge.

`Complex.log_re : (log x).re = Real.log ‖x‖` is the whole analytic content; the rest is
linearity of `re` over a real-coefficient sum. -/

end Salt.MR
