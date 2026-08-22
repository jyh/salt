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
import Salt.MR.ParsevalSingle

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

/-! ## Closing the threshold gap the helm found

`hMsup_of_propA3_shape` concludes at `∀ T ≥ max 1 (X/h₁)`; `parseval_single_h`
requires `∀ T ≥ X/h`.  **Those are not the same threshold** — the bridge leaves
`T ∈ [X/h, 1)` uncovered whenever `X/h < 1`.  My "character-for-character" was
one word too strong: the INTEGRANDS are identical, the THRESHOLDS are not.

The gap closes, but on a **side condition**, not by identity: Parseval's own
hypotheses force `1 ≤ X/h`, and then `max 1 (X/h) = X/h`.  That is worth a lemma
rather than a remark, because a threshold that coincides only under someone
else's hypotheses is exactly the kind of joint that goes unstated. -/

/-- **Parseval's own hypotheses force `1 ≤ X / h`.**  From `exp 1 ≤ X` we get
`log X ≥ 1`, hence `(log X)^(−1/5) ≤ 1`, hence `h ≤ X`. -/
theorem one_le_X_div_h {X h : ℝ} (hX : Real.exp 1 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) : 1 ≤ X / h := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hle1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hhpos : (0 : ℝ) < h := by linarith
  have hhle : h ≤ X := by nlinarith [hXpos, hle1, hhX]
  rw [le_div_iff₀ hhpos]; linarith

/-- **THE BRIDGE AT PARSEVAL'S OWN THRESHOLD.**  Same conclusion as
`hMsup_of_propA3_shape`, but quantified over `T ≥ X/h` — the form
`parseval_single_h` actually consumes — using the side condition above. -/
theorem hMsup_of_propA3_shape_parseval
    (a : ℕ → ℂ) (s0 : Finset ℕ) {X h B : ℝ}
    (hpos : ∀ m ∈ s0, 0 < m) (hB : 0 ≤ B)
    (hXe : Real.exp 1 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hA3 : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (-T)..T, ‖dpolyA a s0 t‖ ^ 2) ≤ (T / (X / h) + 1) * B) :
    ∀ T : ℝ, X / h ≤ T →
      X / h / T * ((∫ t in T..(2 * T), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a s0 t‖ ^ 2) ≤ 3 * B := by
  have h1 := one_le_X_div_h hXe hh4 hhX
  have hXh : (0 : ℝ) < X / h := lt_of_lt_of_le zero_lt_one h1
  intro T hT
  exact hMsup_of_propA3_shape a s0 hpos hXh hB hA3 T (by rw [max_eq_right h1]; exact hT)

/-- **THE OTHER HALF OF THE COMPOSITION.**  `parseval_single_h`'s right-hand side
carries three `dpolyA` integrals besides `Msup`: an outer two-sided block
`[L, X/h] ∪ [−X/h, −L]` and an inner block `[−L, L]`.  **They tile
`[−X/h, X/h]` exactly**, so A.3's bound at `T = X/h` — where `T/(X/h) = 1` —
bounds all three together by `2B`.

*This is the thread nobody had written: with it and the threshold lemma above,
A.3's shape controls every `dpolyA` term Parseval's bound exposes.* -/
theorem parseval_dpolyA_terms_of_propA3_shape
    (a : ℕ → ℂ) (s0 : Finset ℕ) {X h B L : ℝ}
    (hpos : ∀ m ∈ s0, 0 < m) (hR1 : 1 ≤ X / h)
    (hA3 : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (-T)..T, ‖dpolyA a s0 t‖ ^ 2) ≤ (T / (X / h) + 1) * B) :
    ((∫ t in L..(X / h), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(X / h))..(-L), ‖dpolyA a s0 t‖ ^ 2)
      + (∫ t in (-L)..L, ‖dpolyA a s0 t‖ ^ 2) ≤ 2 * B := by
  have hcont : Continuous (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) :=
    ((dpolyA_continuous a s0 hpos).norm).pow 2
  have hI : ∀ u v : ℝ,
      IntervalIntegrable (fun t : ℝ => ‖dpolyA a s0 t‖ ^ 2) volume u v :=
    fun u v => hcont.intervalIntegrable u v
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (hI (-(X / h)) (-L)) (hI (-L) L)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    ((hI (-(X / h)) (-L)).trans (hI (-L) L)) (hI L (X / h))
  have hRpos : (0 : ℝ) < X / h := lt_of_lt_of_le zero_lt_one hR1
  have hA := hA3 (X / h) hR1
  rw [div_self (ne_of_gt hRpos)] at hA
  linarith

/-! ## The composition, run end to end

With the threshold lemma and the tiling lemma both in hand, A.3's shape controls
every term `parseval_single_h` exposes: `Msup` via the bridge (`= 3B`), and the
three `dpolyA` blocks via the tiling (`≤ 2B` together).  This theorem does the
substitution, so the chain

  A.3's shape  ⟶  hMsup  ⟶  parseval_single_h  ⟶  a bound in A.3's own `B`

is a single Lean object rather than three with prose between them.

⚠️ **This still does not prove A.3.** It takes A.3's conclusion as a hypothesis.
What it removes is the assembly step, which was the last thing between the stated
door and A.2's left-hand side. -/

/-- **THE CHAIN, COMPOSED.**  Given A.3's shape at constant `B`, the single-`h`
Parseval bound holds with every `dpolyA` term replaced by its `B`-multiple:
`Msup ↦ 3B` from the bridge, and the three spectral blocks together `↦ 2B` from
the tiling. -/
theorem parseval_bound_of_propA3_shape
    (a : ℕ → ℂ) (s0 : Finset ℕ) {X h B δ : ℝ} (N : ℕ)
    (hpos : ∀ m ∈ s0, 0 < m) (hB : 0 ≤ B)
    (hX : Real.exp 1 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hA3 : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (-T)..T, ‖dpolyA a s0 t‖ ^ 2) ≤ (T / (X / h) + 1) * B) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2)
          * ((205 * Real.pi * (2 * B) + 236160 * Real.pi * (3 * B))
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ N * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ N * δ)
                  + (8 * h / 2 ^ N) * (1 + Real.log (3 * X))) ^ 2)) := by
  have h1 := one_le_X_div_h hX hh4 hhX
  have hM := hMsup_of_propA3_shape_parseval a s0 hpos hB hX hh4 hhX hA3
  have hP := parseval_single_h a s0 N hX hh4 hhX hδ0 hδ1 ha hrange hM
  have hterms := parseval_dpolyA_terms_of_propA3_shape a s0
    (L := (Real.log X) ^ (1 / 45 : ℝ)) hpos h1 hA3
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hinv : (0 : ℝ) < 1 / (2 * Real.pi ^ 2) := by positivity
  refine le_trans hP ?_
  have hblocks : (205 : ℝ) * Real.pi
        * ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h), ‖dpolyA a s0 t‖ ^ 2)
          + ∫ t in (-(X / h))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
      + 205 * Real.pi
        * (∫ t in (-((Real.log X) ^ (1 / 45 : ℝ)))..((Real.log X) ^ (1 / 45 : ℝ)),
            ‖dpolyA a s0 t‖ ^ 2)
      ≤ 205 * Real.pi * (2 * B) := by
    have h205 : (0 : ℝ) ≤ 205 * Real.pi := by positivity
    nlinarith [hterms, h205]
  -- `gcongr` reduces to the spectral-block comparison and discharges it from `hblocks`
  gcongr

end Salt.MR
