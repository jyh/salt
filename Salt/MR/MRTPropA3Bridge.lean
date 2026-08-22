/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The A.3 → `hMsup` bridge — the join, in one lemma

`lemma14_shortInterval_meansq` (`PerronMeanSq.lean:914`) carries four analytic
hypotheses; three are discharged by its `_concrete` variant and **`hMsup` is the
only survivor**, carried by every member of the family and passed upward at the
live application (`Eq26Compose.lean:493`).

Read from `docs/sources/1503.05121v3.pdf`, Appendix A: **`hMsup`'s producer in
MRT's own hand is Proposition A.3**, whose conclusion is

  `∫_{−T}^{T} |F(1+it)|² dt ≪ (T/(X/Q₁) + 1)·[bracket]`,   `F(s) = Σ_{X≤n≤2X, n∈S} f(n)/nˢ`

and `F(1 + it)` is exactly this corpus's `dpolyA` (`Lemma14Taylor.lean:283`),
with `Q₁ = h` in A.1's proof — so A.3's `X/Q₁` **is** `hMsup`'s `X/h₁`.  The two
sides are the same normalisation, not analogues.

This file proves the deduction, so the join stops being prose:

  A.3's shape at `2T`  +  block ⊆ symmetric window  ⇒  `hMsup` at `Msup = 3·B`.

## Why the constant is `3`

Containment costs the doubling `T ↦ 2T`; A.3 at `2T` gives `(2T/(X/h₁) + 1)·B`;
multiplying by `(X/h₁)/T` gives `(2 + (X/h₁)/T)·B`, and `T ≥ X/h₁` bounds the
tail term by `1`.  **`hMsup` is quantified over `T ≥ X/h₁` and the supremum sits
at the SMALLEST such `T`** — which is precisely why the trivial mean-value route
prices at `Θ(1)` and is useless here, and why MRT open A.3's proof by disposing
of it in one line: *"Since the mean value theorem gives the bound `O(T/X + 1)`,
we can assume `T ≤ X/2`."*  The strength must come from A.3's bracket, which is
pretentious — it contains `M(f;X)/exp(M(f;X))`, the quantity
`Salt.MR.mrtM_lam_lower` bounds below for `λ`.

⚠️ **This lemma is a DEDUCTION, not a proof of A.3.** It takes A.3's conclusion
as a hypothesis and is silent on whether A.3 holds.  Nothing here proves A.3 and
nothing assumes it globally.
-/
import Mathlib
import Salt.MR.Lemma14Taylor

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-- **THE JOIN.**  From MRT Proposition A.3's shape — `∫_{−T}^{T} ‖dpolyA‖² ≤
(T/(X/h₁) + 1)·B` for all `T ≥ 1` — the `hMsup` hypothesis of
`lemma14_shortInterval_meansq` follows at `Msup := 3·B`.

Integrability is *derived*, not assumed: `dpolyA` is continuous on `s0` with
positive members, so `‖dpolyA‖²` is interval-integrable on every interval. -/
theorem hMsup_of_propA3_shape
    (a : ℕ → ℂ) (s0 : Finset ℕ) {X h₁ B : ℝ}
    (hpos : ∀ m ∈ s0, 0 < m) (hXh : 0 < X / h₁) (hB : 0 ≤ B)
    (hA3 : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (-T)..T, ‖dpolyA a s0 t‖ ^ 2) ≤ (T / (X / h₁) + 1) * B) :
    ∀ T : ℝ, max 1 (X / h₁) ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ 3 * B := by
  have hcont : Continuous (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) :=
    ((dpolyA_continuous a s0 hpos).norm).pow 2
  have hI : ∀ u v : ℝ,
      IntervalIntegrable (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) volume u v :=
    fun u v => hcont.intervalIntegrable u v
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hTX : X / h₁ ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  -- the symmetric window splits into the two blocks and the middle
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (hI (-(2 * T)) (-T)) (hI (-T) T)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    ((hI (-(2 * T)) (-T)).trans (hI (-T) T)) (hI T (2 * T))
  have hmid : (0 : ℝ) ≤ ∫ t in (-T)..T, ‖dpolyA a s0 t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => by positivity)
  -- A.3 applied on the doubled window
  have h2T : (1 : ℝ) ≤ 2 * T := by linarith
  have hA := hA3 (2 * T) h2T
  -- containment: the two blocks sit inside the symmetric window
  have hcontain :
      (∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + (∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2)
      ≤ ∫ t in (-(2 * T))..(2 * T), ‖dpolyA a s0 t‖ ^ 2 := by linarith
  -- the scalar step: multiply by (X/h₁)/T and use (X/h₁)/T ≤ 1
  have hr : X / h₁ / T ≤ 1 := by
    rw [div_le_one hTpos]; exact hTX
  have hr0 : (0 : ℝ) ≤ X / h₁ / T := le_of_lt (div_pos hXh hTpos)
  have hkey : X / h₁ / T * (2 * T / (X / h₁) + 1) * B ≤ 3 * B := by
    -- make the quotient `X/h₁` ATOMIC before `field_simp`, or it splits into
    -- `X` and `h₁` and demands nonvanishing facts we do not have separately
    set u := X / h₁ with hu
    have hu0 : u ≠ 0 := ne_of_gt hXh
    have hT0 : T ≠ 0 := ne_of_gt hTpos
    have hid : u / T * (2 * T / u) = 2 := by field_simp
    have hexp : u / T * (2 * T / u + 1) = 2 + u / T := by
      rw [mul_add, mul_one, hid]
    rw [hexp]
    nlinarith [hB, hr]
  calc X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
          + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2)
      ≤ X / h₁ / T * (∫ t in (-(2 * T))..(2 * T), ‖dpolyA a s0 t‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hcontain hr0
    _ ≤ X / h₁ / T * ((2 * T / (X / h₁) + 1) * B) := by
        exact mul_le_mul_of_nonneg_left hA hr0
    _ = X / h₁ / T * (2 * T / (X / h₁) + 1) * B := by ring
    _ ≤ 3 * B := hkey

end Salt.MR
