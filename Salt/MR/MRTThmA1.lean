/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# MRT Theorem A.1 — the statement (the reduced spine's PRIMARY)

Transcribed from `docs/sources/1503.05121v3.pdf`, Appendix A, **read from the
PDF itself** rather than from any summary (including this repo's own
`docs/sources/mrt_extract.md`).  MRT's text, verbatim:

> **Theorem A.1.** Let `f` be a 1-bounded multiplicative function and let
> `M(f; X)` be as in (1.6).  Then, for `X ≥ h ≥ 10`,
> `(1/X) ∫_X^{2X} |(1/h) Σ_{x≤n≤x+h} f(n)|² dx ≪ exp(−M(f;X))·M(f;X)
>    + (log log h)²/(log h)² + 1/(log X)^{1/50}`

⛔ **ERRATUM 2026-08-25 (second pass).**  This block is introduced as *MRT's text,
verbatim*, and until now it read `(loglog h)²/(log h)` — **unsquared**.  The `46b7a5a9`
repair moved the STATEMENT at `:94` and `MRTPropA3.lean:3809` and left this QUOTATION
stale, so the file convicted its own theorem of an error the quote above it still
committed.  *A fix reaches where the pain was felt; the quotation is a separate surface
and it was not enumerated.*  Re-read at 200 dpi from p. 20 and corrected here.

## Three things the source settles, all of which the campaign had open

1. **`M(f; X)` is (1.6)'s — MRT write "as in (1.6)" in the statement itself.**
   (1.6) carries NO character.  This confirms the ratified `M`-vs-`M(Q)`
   separation from the source rather than from our re-derivation, and it is why
   `Salt.MR.lambda_nonpret`'s `χ = 1` shape is the SPECIFIED shape.
2. ⭐ **The `x`-integral runs over `[X, 2X]` and is the AVERAGE over the
   location `x`; the short interval has length `h`.**  This is the source
   confirmation of the refutation recorded in the scoping brief's erratum: the
   `[X,2X]` in A.1 is NOT the range of a typical-factorization set.
3. ⭐ **The middle error term carries `(loglog h)²` — SQUARED** — where Theorem
   1.7 carried `loglog h`.  Confirmed here so that nobody transcribes 1.7's
   shape into an A.1 proof.

⛔⛔ **THE REMARK IS NOT A STRENGTHENING — IT IS THE ONLY TRUE FORM, AND TAKING THE
"AS-STATED" ONE MADE THIS DEF FALSE FOR EVERY `C`.  Repaired 2026-08-25 (second pass).**

MRT record, immediately after the statement on p. 20 and again after A.2 on p. 21:
*"The factor `exp(−M(f;X))M(f;X)` can be replaced by `exp(−M(f;X))`, see the remark
following Proposition A.3."*

This file previously took the `exp(−M)·M` form and justified it: *"the form below is the
WEAKER, as-stated one; that is deliberate, since a door should be the weakest admissible
statement."*  **That rationale is the defect.**  `exp(−M)·M ≤ exp(−M) ⟺ M ≤ 1`, so the
`·M` form is weaker only for `M > 1` and **inverts below it** — at `M = 0` it is the
STRONGEST possible first term, namely `0`.

⛔ **COUNTEREXAMPLE, and it kills every `C`.**  Take `f ≡ 1`: it is 1-bounded, `f 1 = 1`,
and multiplicative, so it satisfies all three hypotheses.  `pretDistSq 1 (costwist 0) X`
sums `(1 − Re(1 · conj 1))/p = 0` over `p ≤ X`, and every term of `pretDistSq` is `≥ 0`,
so the infimum is attained: **`mrtM 1 X = 0`**.  The old first term was then
`exp(−0) · 0 = 0`.  Meanwhile `mrtShortMean 1 h x = (⌊x+h⌋ − ⌈x⌉ + 1)/h ≥ (h−1)/h ≥ 0.9`
for `h ≥ 10`, so the LHS is `≥ 0.81`, while the two remaining terms `→ 0` as `h, X → ∞`.
For any fixed `C`, choose `h` and `X` large: RHS `< 0.81 ≤` LHS.  **`MRTThmA1 C` was false
for every `C`, hence `MRTThmA1Statement` too** — and every consumer taking `hA1 : MRTThmA1 C`
was VACUOUSLY true, which is why nothing was red.

⇒ the def below takes **`exp(−M(f;X))`**, the remark's form, which at `M = 0` gives `1` and
correctly refuses to promise cancellation for a pretentious `f`.  Statement change under the
`46b7a5a9` faithfulness protocol: fidelity to the source is the iron rule's purpose, and the
remark IS the source.

## Multiplicativity is stated inline, on purpose

Mathlib's `IsMultiplicative` lives on `Nat.ArithmeticFunction`, so using it here
would force a `toArithmeticFunction` transport on a bare `f : ℕ → ℂ`.  Stated
over the object's own type there is nothing to transport, so the two defining
equations are written out directly.  (`IsMultiplicative` is named here so a
name-census of this corpus still finds this file.)

⚠️⚠️ **NON-VACUITY IS OWED, exactly as for `MRTProp24`.**  Lean's Bochner integral
is `0` on a non-integrable integrand, so **any eventual PROOF of `MRTThmA1` must
land integrability of `x ↦ ‖mrtShortMean f h x‖ ^ 2` on `[X, 2X]` first**, or the
bound is bought with `0 ≤ RHS`.  Nothing in this file proves `MRTThmA1` and
nothing assumes it.
-/
import Mathlib
import Salt.MR.MRTProp24

namespace Salt.MR

open scoped BigOperators

/-- **The short-interval mean `(1/h) Σ_{x ≤ n ≤ x+h} f(n)`** (MRT Theorem A.1).
The index set is the naturals in `[x, x+h]`; `mem_mrtShortWindow` proves that
reading is exact rather than assuming it. -/
noncomputable def mrtShortMean (f : ℕ → ℂ) (h x : ℝ) : ℂ :=
  (1 / (h : ℂ)) * ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, f n

/-- **Faithfulness of the index set, PROVED not asserted:** for `0 ≤ x` and
`0 ≤ h`, the naturals of `Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊` are exactly those with
`x ≤ n ≤ x + h`.  So the reals → naturals move in `mrtShortMean` costs nothing. -/
theorem mem_mrtShortWindow {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (n : ℕ) :
    n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊ ↔ x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h := by
  rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (by linarith)]

/-- **MRT Theorem A.1 at an explicit constant `C`** (`1503.05121v3`, Appendix A).
The `≪` is discharged as a single absolute `C`, uniform in `f`, `X` and `h`.

⛔ **FAITHFULNESS REPAIR 2026-08-25 — THE MIDDLE TERM'S DENOMINATOR WAS UNSQUARED AND
THE SOURCE'S IS SQUARED.**  This transcription read `(loglog h)^2 / log h`; the PDF
(`docs/sources/1503.05121v3.pdf` p. 20, read with two instruments — page image and
`pdftotext`) states

```
  ... ≪ exp(-M(f;X))M(f;X) + (log log h)^2/(log h)^2 + 1/(log X)^{1/50}
```

so the exponent on `log h` is **-2, not -1**, and the old form was a STRICTLY WEAKER
claim than MRT's.  Repaired here and at `MRTThmA2` (`MRTPropA3.lean`) in the same beat;
both moved identically, so `mrtThmA1_of_mrtThmA2_empty` matches unchanged.
*(2026-08-25 second pass: those two names are now `MRTThmA1GJ` and
`mrtThmA1_of_mrtThmA1GJ_empty` — the record above is left as written, with the pointers
annotated here so they still resolve.  See that file's erratum for why the `A.2` name went.)*  *Nothing
caught this for the same reason the kernel could not: it checks that A.2 implies A.1,
not that either is MRT's.*  Our own extract (`docs/sources/mrt_extract.md:53`) had it
right — the defect entered at the Lean step, not the extraction step. -/
def MRTThmA1 (C : ℝ) : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    ∀ X h : ℝ, 10 ≤ h → h ≤ X →
      (1 / X) * (∫ x in X..(2 * X), ‖mrtShortMean f h x‖ ^ 2)
        ≤ C * (Real.exp (-(mrtM f X))
              + (Real.log (Real.log h)) ^ 2 / Real.log h ^ 2
              + 1 / (Real.log X) ^ ((1 : ℝ) / 50))

/-! ## Non-vacuity — discharging the obligation this file's header names

The integrand of `MRTThmA1` is a **step function in `x`**, not a continuous one:
the index set `Icc ⌈x⌉₊ ⌊x+h⌋₊` jumps as `x` crosses an integer.  So the
continuity route used in `MRTPropA3Bridge` is unavailable here, and integrability
has to come from **measurable + bounded** instead. -/

/-- The short-interval mean is measurable in `x`.  The index-set endpoints are
measurable `ℝ → ℕ`, and **every** map out of `ℕ × ℕ` is measurable, so the sum
factors through a discrete space. -/
theorem measurable_mrtShortMean (f : ℕ → ℂ) (h : ℝ) :
    Measurable (fun x : ℝ => mrtShortMean f h x) := by
  have hpair : Measurable (fun x : ℝ => (⌈x⌉₊, ⌊x + h⌋₊)) :=
    Measurable.prod Nat.measurable_ceil
      (Nat.measurable_floor.comp (measurable_id.add_const h))
  have hsum : Measurable (fun x : ℝ => ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, f n) :=
    (Measurable.of_discrete (f := fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc p.1 p.2, f n)).comp hpair
  exact measurable_const.mul hsum

/-- A crude but `x`-free bound on the short-interval mean over `[X, 2X]`: the
index set has at most `⌊2X + h⌋₊ + 1` members and `f` is 1-bounded. -/
theorem norm_mrtShortMean_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {h X x : ℝ}
    (hh : 0 < h) (hx : x ≤ 2 * X) :
    ‖mrtShortMean f h x‖ ≤ ((⌊2 * X + h⌋₊ : ℝ) + 1) / h := by
  have hcard : ((Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).card : ℝ) ≤ (⌊2 * X + h⌋₊ : ℝ) + 1 := by
    have h1 : (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).card ≤ ⌊x + h⌋₊ + 1 := by
      rw [Nat.card_Icc]; omega
    have h2 : ⌊x + h⌋₊ ≤ ⌊2 * X + h⌋₊ := Nat.floor_le_floor (by linarith)
    have : (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).card ≤ ⌊2 * X + h⌋₊ + 1 := le_trans h1 (by omega)
    exact_mod_cast this
  have hsum : ‖∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, f n‖ ≤ (⌊2 * X + h⌋₊ : ℝ) + 1 := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun n _ => hf n)) ?_
    simpa using hcard
  have hnorm : ‖(1 / (h : ℂ))‖ = 1 / h := by simp [abs_of_pos hh]
  have hsplit : ((⌊2 * X + h⌋₊ : ℝ) + 1) / h = 1 / h * ((⌊2 * X + h⌋₊ : ℝ) + 1) := by ring
  unfold mrtShortMean
  rw [norm_mul, hnorm, hsplit]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **NON-VACUITY FOR `MRTThmA1`.**  The integrand of the statement is
interval-integrable on `[X, 2X]`, so the bound is a real bound and not the
Bochner integral's `0`-on-non-integrable junk value. -/
theorem intervalIntegrable_mrtThmA1_integrand {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {h X : ℝ} (hh : 0 < h) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x : ℝ => ‖mrtShortMean f h x‖ ^ 2) MeasureTheory.volume X (2 * X) := by
  set C : ℝ := (((⌊2 * X + h⌋₊ : ℝ) + 1) / h) ^ 2 with hC
  refine (intervalIntegrable_const (c := C)).mono_fun ?_ ?_
  · exact ((measurable_mrtShortMean f h).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hxmem
    have hx2 : x ≤ 2 * X := by
      rcases Set.mem_uIoc.mp hxmem with hc | hc
      · linarith [hc.2]
      · linarith [hc.1, hX]
    have hb := norm_mrtShortMean_le (X := X) hf hh hx2
    have hnn : (0 : ℝ) ≤ ((⌊2 * X + h⌋₊ : ℝ) + 1) / h := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have h0 : (0 : ℝ) ≤ ‖mrtShortMean f h x‖ := norm_nonneg _
    nlinarith [hb, h0, hnn]

/-! ## The `j`-union's arithmetic half

A.1's proof splits the mean square at `n ∈ S` and bounds the complement — the
integers missing a prime factor in some band `[Pⱼ, Qⱼ]`, `j ≤ J`.  That is a
**union over `j`**, and with MRT's profile `log Pⱼ / log Qⱼ = (1/j²)(log P₁/log Q₁)`
the union bound needs `Σ_{j≤J} 1/j²` bounded absolutely in `J`.

⭐ The corpus already had the tail: `Salt.BrunLower.sum_one_div_sq_le` gives
`Σ_{m ∈ Icc M K} 1/m² ≤ 1/(M−1)` for `2 ≤ M`.  It cannot be used at `M = 1`
(the bound would read `1/0`), which is exactly why the full-range form was
missing rather than merely unstated. -/

/-- **`Σ_{j=1}^{J} 1/j² ≤ 2`, uniformly in `J`** — the arithmetic the `j`-union
bound needs.  Split off the `j = 1` term and apply the landed tail bound at
`M = 2`, where it reads `≤ 1/(2−1) = 1`. -/
theorem sum_inv_sq_Icc_one_le_two (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  · have hsplit : Finset.Icc 1 J = insert 1 (Finset.Icc 2 J) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : (1 : ℕ) ∉ Finset.Icc 2 J := by simp
    have htail := Salt.BrunLower.sum_one_div_sq_le (M := 2) (K := J) (by norm_num)
    have htail' : ∑ m ∈ Finset.Icc 2 J, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 :=
      calc ∑ m ∈ Finset.Icc 2 J, (1 : ℝ) / (m : ℝ) ^ 2
          ≤ 1 / (((2 : ℕ) : ℝ) - 1) := htail
        _ = 1 := by norm_num
    have hone : (1 : ℝ) / (((1 : ℕ) : ℝ)) ^ 2 = 1 := by norm_num
    rw [hsplit, Finset.sum_insert hnot]
    linarith [htail', hone]

/-- **The door as a `Prop`**: `∃ C > 0`, A.1 holds at `C`.  A statement, not a
theorem — nothing in this development proves it and nothing assumes it. -/
def MRTThmA1Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTThmA1 C

/-- **A.1 at the θ=3/4 lane's tail rate (E34 V4)** — byte-identical to `MRTThmA1` except the
tail term's exponent `1/50 ↦ 1/70`.  Statement act under the helm's word in the E34
ladder-repair commission's fold (2026-08-31, in the private record); the 34-lane runs
THROUGH A.1 so it reaches the campaign's primary instead of dead-ending at A.2.  The old
name stays byte-untouched and citable. -/
def MRTThmA1_34 (C : ℝ) : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    ∀ X h : ℝ, 10 ≤ h → h ≤ X →
      (1 / X) * (∫ x in X..(2 * X), ‖mrtShortMean f h x‖ ^ 2)
        ≤ C * (Real.exp (-(mrtM f X))
              + (Real.log (Real.log h)) ^ 2 / Real.log h ^ 2
              + 1 / (Real.log X) ^ ((1 : ℝ) / 70))

/-- **The 34-lane door as a `Prop`** — `∃ C > 0`, `MRTThmA1_34` holds at `C`; the mechanical
sibling of `MRTThmA1Statement`. -/
def MRTThmA1Statement_34 : Prop := ∃ C : ℝ, 0 < C ∧ MRTThmA1_34 C

end Salt.MR
