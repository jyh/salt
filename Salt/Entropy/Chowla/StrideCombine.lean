/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F4a — THE OUTER COMBINE AT THE AFFINE FORMS (the K-block)

Tao arXiv:1509.05422 Lemma 3.2's transport and the outer Fubini assembly (`OuterCombine.lean`,
`Transport.lean`, `WeakUniform.lean`) at the affine F-function `fBridgeF_aff eps H a b h`
(`StrideBridge.lean:96`, the class filter `j + 1 ≡ p·b (mod a)` on the FIRST factor's index)
under the stride measure `logMeasureAff a x ω` (`StrideFork.lean:75`).  The consumer is the
affine shell (`StrideShell.lean`), which takes `outer_combine_aff`'s conclusion — the FILTERED
decoupled correlation — against the affine circle-method slot.

THE DESIGN (price brief `2026-09-04-math-PRICE-lbv-w2S-F4-entropy-half.md` §3, K-block).  The
chain `outer_combine_h → Transport → WeakUniform → ResidueUniform` touches the measure on `ℕ`
structurally at ONE leaf, `entropy_residueWindow_ge` (`ResidueUniform.lean:536`, consumed at
`WeakUniform.lean:197`).  Under the pushforward by `a * ·` the residue `(a·n : ZMod (PH eps H))`
is a UNIT multiple of `(n : ZMod (PH eps H))` — `Nat.Coprime a (PH eps H)` is the regime's own
receipt `coprime_PH_of_le` (`PrimeWindow.lean:145`, from `ha`/`hcoprime`/`Hlo ≤ H`) — so the
residue entropy at the stride measure EQUALS the landed one (`entropy_comp_of_injective`,
`Salt/Entropy/Basic.lean:124`, an equality): ResidueUniform's 91 `logMeasure` sites are
untouched, and the error term `κ + (log P_H − H[Y])` is numerically the landed one — there is
NO `shellError_aff`.  `hI` enters only at `decrement_markov_fintype` (`MarkovExtract.lean:150`,
`μ`-generic).  The Hoeffding/concentration substrate reads no measure on `ℕ` and F2 already
consumed it at the affine forms (`fBridge_aff_concentration_decoupled_sharp`,
`StrideBridge.lean:363`).  The class filter enters at TWO sites, spelled byte-identically to
`StrideBridge.lean:371-376`: the deviation set `badSet_aff` (site 1) and the conclusion of
`outer_combine_aff` (site 3); the box lemmas absorb it by one `split_ifs` (a filtered term is
`0` or the landed term).  The `FiniteSupport (logMeasureAff a x ω)` instance every
`integrable_of_finiteSupport _` needs is `StrideDecrement.finiteSupport_logMeasureAff`.

⛔ Degenerate values.  `a = 0`: the filter reads `j + 1 = p·b` in `ℤ`, the measure is the Dirac
mass at `0`, `Nat.Coprime 0 (PH eps H)` fails at `PH > 1` — every statement carrying `hcop` is
vacuous there and the rest are true as stated.  `a = 1, b = 0`: the filter is `True` (`ZMod 1`
a subsingleton) and every object is the landed `_h` member (`badSet_aff_one_zero`,
`outer_combine_aff_one_zero`).  `h = 0` inherits the `h`-lane's degeneracy.

HONEST LABEL.  Nothing here produces a door or bears on twin primes.  Every declaration below is
statement-only at the freeze (sorry-bodied, recipe in the docstring), built as a module through
`../saltbuild.sh`; NO executor fires before the helm's refuter verdict.  ⛔ MERGE FENCE (iron
rule 2): `math/lbv-w2s-f4a` never reaches `main` until every obligation in the four F4a files
lands sorry-free.
-/
import Salt.Entropy.Chowla.StrideDecrement
import Salt.Entropy.Chowla.StrideBridge
import Salt.Entropy.Chowla.OuterCombine
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## F4-K1 — residue uniformity at the stride measure: an injective relabel -/

/-- **F4-K1a (class B) — THE RELABEL.**  The residue window's entropy under the stride measure
equals its entropy under the plain measure when `a` is a unit mod `P_H`.  Recipe: `rw
[entropy_def, entropy_def]`; `unfold logMeasureAff; rw [Measure.map_map (measurable_residueWindow
eps H) measurable_from_nat]`; the composite `residueWindow eps H ∘ (a * ·)` is `(fun y => (a :
ZMod (PH eps H)) * y) ∘ residueWindow eps H` (`funext n; simp [residueWindow, Nat.cast_mul]`);
then `entropy_comp_of_injective (logMeasure x ω) (measurable_residueWindow eps H) _ hinj` with
`hinj` from `(ZMod.unitOfCoprime a hcop).mul_left_injective`-shape (`IsUnit.mul_left_injective`
at `ZMod.isUnit_iff_coprime`); `rw [← entropy_def]` both sides. -/
theorem entropy_residueWindow_aff_eq (eps : ℚ) (H : ℕ) {x ω a : ℕ}
    (hcop : Nat.Coprime a (PH eps H)) :
    H[residueWindow eps H ; logMeasureAff a x ω] = H[residueWindow eps H ; logMeasure x ω] := by
  sorry

/-- **F4-K1b (class A).**  Tao's (3.9) at the stride measure: `rw
[entropy_residueWindow_aff_eq eps H hcop]; exact entropy_residueWindow_ge eps H hx hω hωx`
(`ResidueUniform.lean:536`). -/
theorem entropy_residueWindow_ge_aff {x ω a : ℕ} (eps : ℚ) (H : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hcop : Nat.Coprime a (PH eps H)) :
    Real.log (PH eps H) - Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
      ≤ H[residueWindow eps H ; logMeasureAff a x ω] := by
  sorry

/-- **F4-K1c (class A) — Tao Lemma 3.2 at the spine, stride measure.**  `weakUniform_spine`
(`WeakUniform.lean:184`) with `entropy_residueWindow_ge_aff` for `hdefic` and
`weakUniform_generic` verbatim. -/
theorem weakUniform_spine_aff {x ω a : ℕ} (eps : ℚ) (H : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hcop : Nat.Coprime a (PH eps H))
    [IsProbabilityMeasure (logMeasure x ω)]
    {t g : ℝ} (hg : 0 < g) (x₀ : Fin H → ℤ) (E : Finset (ZMod (PH eps H)))
    (hgood : H[residueWindow eps H; logMeasureAff a x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀]
          ≤ t)
    (hE : Real.log (E.card : ℝ) ≤ Real.log (PH eps H : ℝ) - g) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀).real ↑E
      ≤ (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
          + Real.log 2) / g := by
  sorry

/-! ## F4-K2 — the deviation set at the affine forms (SITE 1 of the filter) -/

/-- **F4-K2a (def) — the deviation event at the affine forms.**  `badSet_h` (`Transport.lean:197`)
with `fBridgeF_aff eps H a b h` and the FILTERED decoupled mean; the set is spelled
byte-identically to `fBridge_aff_concentration_decoupled_sharp`'s (`StrideBridge.lean:371-376`,
site 2), so the transport's `hset` rewrite is `ext ω; simp [badSet_aff]`. -/
noncomputable def badSet_aff (eps : ℚ) (H : ℕ) (a b h : ℕ) (x₀ : Fin H → ℤ) (δ : ℝ) :
    Finset (ZMod (PH eps H)) :=
  letI := Classical.dec
  Finset.univ.filter fun ω =>
    δ ≤ |fBridgeF_aff eps H a b h x₀ ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
      ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H x₀ j : ℝ) * (windowVal H x₀ (j + (p : ℕ) * h) : ℝ) else 0|

/-- **F4-K2b (class B) — the `(1, 0)` compat.**  `ext ω; simp only [badSet_aff, badSet_h,
Finset.mem_filter, Finset.mem_univ, true_and, fBridgeF_aff_one_zero,
eq_iff_true_of_subsingleton, if_true]` — the filter at `ZMod 1` is `True` (the F2-B3 recipe),
the bridge is `fBridgeF_aff_one_zero` (`StrideBridge.lean:117`). -/
theorem badSet_aff_one_zero (eps : ℚ) (H h : ℕ) (x₀ : Fin H → ℤ) (δ : ℝ) :
    badSet_aff eps H 1 0 h x₀ δ = badSet_h eps H h x₀ δ := by
  sorry

/-! ## F4-K3 — the transport at the affine forms -/

/-- **F4-K3a (class A) — W3-a-3a at the affine forms.**  `badSet_transport_h`
(`Transport.lean:243`) with `fBridge_aff_concentration_decoupled_sharp` (site 2) in place of the
`_h` one, `badSet_aff` for `badSet_h`, and `weakUniform_spine_aff` (with `hcop`) for
`weakUniform_spine`; the empty-set branch, `uniformOn_univ_real_coe`, the log arithmetic are
verbatim (`Transport.lean:262-299`). -/
theorem badSet_transport_aff (eps : ℚ) (H : ℕ) (a b h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hcop : Nat.Coprime a (PH eps H))
    [IsProbabilityMeasure (logMeasure x ω)]
    {x₀ : Fin H → ℤ} (hx₀ : ∀ i, |x₀ i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ))
    {t : ℝ} (ht : 0 ≤ t)
    (hgood : H[residueWindow eps H; logMeasureAff a x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀]
          ≤ t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ δ ^ 2 * Real.log (H : ℝ) /
        (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2) - Real.log 2) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀).real
        ↑(badSet_aff eps H a b h x₀ δ)
      ≤ (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
          + Real.log 2) / g := by
  sorry

/-- **F4-K3b (class A) — the calibrated transport.**  `badSet_transport_at_calibration_h`
(`Transport.lean:302`): the ε-arithmetic (`(2 + ε²)² ≤ 9`, `hE_eq`) verbatim, then
`badSet_transport_aff`. -/
theorem badSet_transport_at_calibration_aff (eps : ℚ) (H : ℕ) (a b h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hcop : Nat.Coprime a (PH eps H))
    [IsProbabilityMeasure (logMeasure x ω)]
    {x₀ : Fin H → ℤ} (hx₀ : ∀ i, |x₀ i| ≤ 1) (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1)
    (hne : (primeWindow eps H).Nonempty)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ))
    {t : ℝ} (ht : 0 ≤ t)
    (hgood : H[residueWindow eps H; logMeasureAff a x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀]
          ≤ t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) / (18 * C₀ * Real.log (H : ℝ)) - Real.log 2) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀).real
        ↑(badSet_aff eps H a b h x₀ ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
      ≤ (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
          + Real.log 2) / g := by
  sorry

/-! ## F4-K4 — the box bounds at the affine forms -/

/-- **F4-K4a (class A).**  `fBridgeF_h_abs_le_boxSum` (`OuterCombine.lean:134`) with
`fBridgeG_aff_abs_le` (`StrideBridge.lean:131`, the same `H/p + 1`). -/
lemma fBridgeF_aff_abs_le_boxSum (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1) (y : ZMod (PH eps H)) :
    |fBridgeF_aff eps H a b h v y| ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  sorry

/-- **F4-K4b (class B).**  `decoupledMean_h_abs_le_boxSum` (`OuterCombine.lean:147`) with the
filtered inner sum: each term is `0` or a unit-bounded product (`split_ifs`;
`windowVal_prod_abs_le`, `abs_nonneg`), so the inner sum is still `≤ H`. -/
lemma decoupledMean_aff_abs_le_boxSum (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|
      ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  sorry

/-- **F4-K4c (class A).**  `(fBridgeF_aff_abs_le_boxSum …).trans (boxSum_le_grade eps H heps
hreg hH)`. -/
lemma fBridgeF_aff_abs_le_box (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (y : ZMod (PH eps H)) :
    |fBridgeF_aff eps H a b h v y| ≤ boxGrade eps H := by
  sorry

/-- **F4-K4d (class A).**  `(decoupledMean_aff_abs_le_boxSum …).trans (boxSum_le_grade eps H
heps hreg hH)`. -/
lemma decoupledMean_aff_abs_le_box (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|
      ≤ boxGrade eps H := by
  sorry

/-! ## F4-K5 — the bad-event disintegration at the stride measure -/

/-- **F4-K5a (class A).**  `outer_badMass_h_eq` (`OuterCombine.lean:482`) with `μ :=
logMeasureAff a x ω` and `badSet_aff`: `map_compProd_condDistrib`, `Measure.integral_compProd`,
`integral_indicator_one` — all `μ`-generic; the probability instance is
`isProbabilityMeasure_logMeasureAff`. -/
lemma outer_badMass_aff_eq (eps : ℚ) (H : ℕ) (a b h : ℕ) (x ω : ℕ)
    [IsProbabilityMeasure (logMeasure x ω)] (δ : ℝ) :
    (logMeasureAff a x ω).real
        {n | residueWindow eps H n ∈ badSet_aff eps H a b h (liouvilleWindow H n) δ}
      = ∫ x₀, ((condDistrib (residueWindow eps H) (liouvilleWindow H)
            (logMeasureAff a x ω) x₀).real ↑(badSet_aff eps H a b h x₀ δ))
          ∂((logMeasureAff a x ω).map (liouvilleWindow H)) := by
  sorry

/-- **F4-K5b (class B).**  `outer_badMass_h_le` (`OuterCombine.lean:526`) with the measure
renamed: `decrement_markov_fintype` (`MarkovExtract.lean:150`, verbatim — it consumes `hI`),
the indicator split on good/bad fibres with `badSet_transport_at_calibration_aff` (needs
`hcop`), `integrable_of_finiteSupport _` at the new instance. -/
lemma outer_badMass_aff_le (eps : ℚ) (H : ℕ) (a b h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hcop : Nat.Coprime a (PH eps H))
    [IsProbabilityMeasure (logMeasure x ω)]
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1) (hne : (primeWindow eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (hlog : 1 ≤ Real.log (H : ℝ))
    (hhead : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    {t : ℝ} (ht : 0 < t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ}
    (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasureAff a x ω] ≤ κ) :
    ∫ x₀, ((condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀).real
        ↑(badSet_aff eps H a b h x₀ ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))))
          ∂((logMeasureAff a x ω).map (liouvilleWindow H))
      ≤ (t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ) - H[residueWindow eps H; logMeasureAff a x ω])) / t := by
  sorry

/-! ## F4-K6 — THE OUTER FUBINI ASSEMBLY at the affine forms (SITE 3 of the filter) -/

/-- **F4-K6 (class B) — W3-a-3c at the affine forms.**  `outer_combine_h` (`OuterCombine.lean:620`)
with the measure renamed and the class filter in the conclusion: from the affine `(2.11)` input
`h211` (F2-C3's shape, `StrideBridge.lean:676`) the FILTERED decoupled correlation carries a lower
bound of the same `ε·H/log H` grade with the error term character-for-character the `h`-lane's
(the relabel is an equality, so `H[residueWindow; logMeasureAff]` is the landed value).  Chain:
`fBridgeF_aff_abs_le_box` + `decoupledMean_aff_abs_le_box` pointwise, integrate
(`integrable_of_finiteSupport _`, the new instance), `outer_badMass_aff_eq` +
`outer_badMass_aff_le`, triangle against `h211`.  ⚠ SITE 3: the conclusion's inner sum is
spelled as `badSet_aff`'s (site 1) and `fBridge_aff_concentration_decoupled_sharp`'s (site 2). -/
theorem outer_combine_aff (eps : ℚ) (H : ℕ) (a b h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hcop : Nat.Coprime a (PH eps H))
    [IsProbabilityMeasure (logMeasure x ω)]
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1) (hne : (primeWindow eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (hlog : 1 ≤ Real.log (H : ℝ))
    (hhead : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasureAff a x ω] ≤ κ)
    {c₁ : ℝ} (_hc₁ : 0 < c₁)
    (h211 : c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)|) :
    c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        - ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
              + (κ + (Real.log (PH eps H : ℝ)
                  - H[residueWindow eps H; logMeasureAff a x ω])) / t))
      ≤ |∫ m, (∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H (liouvilleWindow H m) j : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ) else 0)
          ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F4-K6a (class B) — the `(1, 0)` compat of the assembly**, stated at the LANDED conclusion of
`outer_combine_h` and discharged by `outer_combine_aff` at `(1, 0)`: `logMeasureAff_one`,
`fBridgeF_aff_one_zero` under the integral binder (`simp only`, not `rw`), the filter at `ZMod 1`
(`eq_iff_true_of_subsingleton`, `if_true`), and `hcop : Nat.Coprime 1 _ := Nat.coprime_one_left _`.
Records that the filter and the measure drift nowhere at the model point. -/
theorem outer_combine_aff_one_zero (eps : ℚ) (H h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1) (hne : (primeWindow eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (hlog : 1 ≤ Real.log (H : ℝ))
    (hhead : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasure x ω] ≤ κ)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (h211 : c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        - ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
              + (κ + (Real.log (PH eps H : ℝ)
                  - H[residueWindow eps H; logMeasure x ω])) / t))
      ≤ |∫ n, (∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ))
          ∂(logMeasure x ω)| := by
  sorry

end Salt.Entropy.Chowla
