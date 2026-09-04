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
  have hunit : IsUnit ((a : ℕ) : ZMod (PH eps H)) :=
    (ZMod.isUnit_iff_coprime a (PH eps H)).mpr hcop
  have hinj : Function.Injective
      (fun y : ZMod (PH eps H) => ((a : ℕ) : ZMod (PH eps H)) * y) :=
    hunit.mul_right_injective
  have hcomp : (residueWindow eps H) ∘ (fun n : ℕ => a * n)
      = (fun y : ZMod (PH eps H) => ((a : ℕ) : ZMod (PH eps H)) * y)
          ∘ (residueWindow eps H) := by
    funext n
    simp only [Function.comp_apply, residueWindow, Nat.cast_mul]
  have key := entropy_comp_of_injective (logMeasure x ω) (measurable_residueWindow eps H)
    (fun y : ZMod (PH eps H) => ((a : ℕ) : ZMod (PH eps H)) * y) hinj
  rw [entropy_def] at key
  rw [entropy_def]
  unfold logMeasureAff
  rw [Measure.map_map (measurable_residueWindow eps H) measurable_from_nat, hcomp]
  exact key

/-- **F4-K1b (class A).**  Tao's (3.9) at the stride measure: `rw
[entropy_residueWindow_aff_eq eps H hcop]; exact entropy_residueWindow_ge eps H hx hω hωx`
(`ResidueUniform.lean:536`). -/
theorem entropy_residueWindow_ge_aff {x ω a : ℕ} (eps : ℚ) (H : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hcop : Nat.Coprime a (PH eps H)) :
    Real.log (PH eps H) - Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
      ≤ H[residueWindow eps H ; logMeasureAff a x ω] := by
  rw [entropy_residueWindow_aff_eq eps H hcop]
  exact entropy_residueWindow_ge eps H hx hω hωx

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
  haveI : IsProbabilityMeasure
      (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀) :=
    inferInstance
  have hdefic := entropy_residueWindow_ge_aff eps H hx hω hωx hcop
  have hlb : Real.log (PH eps H : ℝ)
        - (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)))
      ≤ Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasureAff a x ω) x₀] := by
    linarith [hgood, hdefic]
  exact weakUniform_generic _ hg E hlb hE

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
  classical
  ext y
  simp only [badSet_aff, badSet_h, Finset.mem_filter, Finset.mem_univ, true_and,
    fBridgeF_aff_one_zero, eq_iff_true_of_subsingleton, if_true]

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
  classical
  rcases Nat.eq_zero_or_pos (badSet_aff eps H a b h x₀ δ).card with h0 | hpos
  · -- Empty bad set: its conditional mass is 0, and the bound is nonnegative.
    have hempty : badSet_aff eps H a b h x₀ δ = ∅ := Finset.card_eq_zero.mp h0
    rw [hempty, Finset.coe_empty, measureReal_empty]
    have hcorr : (0 : ℝ) ≤ Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)) := by
      apply Real.log_nonneg
      have hpos8 : (0 : ℝ) ≤ 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ) := by positivity
      linarith
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (by linarith) hg.le
  · -- Nonempty bad set: sharp concentration → log-card gap → transport.
    have hconc0 :=
      fBridge_aff_concentration_decoupled_sharp eps H a b h hx₀ heps hne hδ hC₀ hcard hlog
    set D := 2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 with hDdef
    have hset : {y : ZMod (PH eps H) | δ ≤ |fBridgeF_aff eps H a b h x₀ y -
          ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
            if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
              (windowVal H x₀ j : ℝ) * (windowVal H x₀ (j + (p : ℕ) * h) : ℝ) else 0|}
        = (↑(badSet_aff eps H a b h x₀ δ) : Set (ZMod (PH eps H))) := by
      ext y; simp [badSet_aff]
    rw [hset, uniformOn_univ_real_coe] at hconc0
    have hPHpos : (0 : ℝ) < (PH eps H : ℝ) := by exact_mod_cast PH_pos eps H
    have hcardposR : (0 : ℝ) < ((badSet_aff eps H a b h x₀ δ).card : ℝ) := by exact_mod_cast hpos
    have hcardR : ((badSet_aff eps H a b h x₀ δ).card : ℝ)
        ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) / D) * (PH eps H : ℝ) :=
      (div_le_iff₀ hPHpos).mp hconc0
    have hlogcard : Real.log ((badSet_aff eps H a b h x₀ δ).card : ℝ)
        ≤ Real.log (PH eps H : ℝ) - g := by
      have hstep := Real.log_le_log hcardposR hcardR
      rw [Real.log_mul (mul_ne_zero two_ne_zero (Real.exp_ne_zero _)) hPHpos.ne',
        Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp] at hstep
      have hxy : -δ ^ 2 * Real.log (H : ℝ) / D = -(δ ^ 2 * Real.log (H : ℝ) / D) := by ring
      rw [hxy] at hstep
      linarith [hstep, hgle]
    exact weakUniform_spine_aff eps H hx hω hωx hcop hg x₀
      (badSet_aff eps H a b h x₀ δ) hgood hlogcard

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
  have hL : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
  have he : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases Nat.eq_zero_or_pos H with hz | hz
    · exfalso; rw [hz, Nat.cast_zero, Real.log_zero] at hlog; linarith
    · exact_mod_cast hz
  have hδ : (0 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) :=
    div_nonneg (by positivity) hL.le
  have hene : (eps : ℝ) ≠ 0 := he.ne'
  have hLne : Real.log (H : ℝ) ≠ 0 := hL.ne'
  have hCne : C₀ ≠ 0 := hC₀.ne'
  have h2e : (2 + (eps : ℝ) ^ 2) ≠ 0 := by positivity
  have hE_eq : ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) ^ 2 * Real.log (H : ℝ) /
        (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)
      = (eps : ℝ) ^ 6 * (H : ℝ) / (2 * C₀ * Real.log (H : ℝ) * (2 + (eps : ℝ) ^ 2) ^ 2) := by
    field_simp
  have he2le : (eps : ℝ) ^ 2 ≤ 1 := by nlinarith [heps1, he.le]
  have h9 : (2 + (eps : ℝ) ^ 2) ^ 2 ≤ 9 := by
    nlinarith [he2le, sq_nonneg (eps : ℝ), mul_nonneg (sub_nonneg.mpr he2le) (sq_nonneg (eps : ℝ))]
  have hD18 : (0 : ℝ) < 18 * C₀ * Real.log (H : ℝ) :=
    mul_pos (mul_pos (by norm_num) hC₀) hL
  have hD2 : (0 : ℝ) < 2 * C₀ * Real.log (H : ℝ) * (2 + (eps : ℝ) ^ 2) ^ 2 :=
    mul_pos (mul_pos (mul_pos (by norm_num) hC₀) hL) (by positivity)
  have hEbound : (eps : ℝ) ^ 6 * (H : ℝ) / (18 * C₀ * Real.log (H : ℝ))
      ≤ ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) ^ 2 * Real.log (H : ℝ) /
        (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2) := by
    rw [hE_eq, div_le_div_iff₀ hD18 hD2]
    have hbase : (0 : ℝ) ≤ (eps : ℝ) ^ 6 * (H : ℝ) * C₀ * Real.log (H : ℝ) := by positivity
    nlinarith [mul_nonneg hbase (by linarith [h9] : (0 : ℝ) ≤ 9 - (2 + (eps : ℝ) ^ 2) ^ 2)]
  refine badSet_transport_aff eps H a b h hx hω hωx hcop hx₀ heps hne hδ hC₀ hcard hlog
    ht hgood hg ?_
  exact hgle.trans (sub_le_sub_right hEbound (Real.log 2))

/-! ## F4-K4 — the box bounds at the affine forms -/

/-- **F4-K4a (class A).**  `fBridgeF_h_abs_le_boxSum` (`OuterCombine.lean:134`) with
`fBridgeG_aff_abs_le` (`StrideBridge.lean:131`, the same `H/p + 1`). -/
lemma fBridgeF_aff_abs_le_boxSum (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1) (y : ZMod (PH eps H)) :
    |fBridgeF_aff eps H a b h v y| ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  unfold fBridgeF_aff
  calc |∑ p : primeWindow eps H, fBridgeG_aff eps H a b h v p (residueProj eps H p y)|
      ≤ ∑ p : primeWindow eps H, |fBridgeG_aff eps H a b h v p (residueProj eps H p y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) :=
        Finset.sum_le_sum (fun p _ => fBridgeG_aff_abs_le eps H a b h hv p _)

/-- **F4-K4b (class B).**  `decoupledMean_h_abs_le_boxSum` (`OuterCombine.lean:147`) with the
filtered inner sum: each term is `0` or a unit-bounded product (`split_ifs`;
`windowVal_prod_abs_le`, `abs_nonneg`), so the inner sum is still `≤ H`. -/
lemma decoupledMean_aff_abs_le_boxSum (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|
      ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos
  set F : ℕ → ℝ := fun j =>
    if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0 with hF
  have hFb : ∀ j : ℕ, |F j| ≤ (1 : ℝ) := by
    intro j
    rw [hF]
    dsimp only
    split_ifs with hc
    · exact windowVal_prod_abs_le hv j _
    · rw [abs_zero]; norm_num
  have hinner : |∑ j ∈ Finset.range H, F j| ≤ (H : ℝ) := by
    calc |∑ j ∈ Finset.range H, F j|
        ≤ ∑ j ∈ Finset.range H, |F j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range H, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hFb j)
      _ = (H : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
  have hstep : 1 / (p : ℝ) * |∑ j ∈ Finset.range H, F j| ≤ 1 / (p : ℝ) * (H : ℝ) :=
    mul_le_mul_of_nonneg_left hinner (by positivity)
  have hHp : 1 / (p : ℝ) * (H : ℝ) = (H : ℝ) / (p : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
  rw [hHp] at hstep; linarith

/-- **F4-K4c (class A).**  `(fBridgeF_aff_abs_le_boxSum …).trans (boxSum_le_grade eps H heps
hreg hH)`. -/
lemma fBridgeF_aff_abs_le_box (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (y : ZMod (PH eps H)) :
    |fBridgeF_aff eps H a b h v y| ≤ boxGrade eps H :=
  (fBridgeF_aff_abs_le_boxSum eps H a b h hv y).trans (boxSum_le_grade eps H heps hreg hH)

/-- **F4-K4d (class A).**  `(decoupledMean_aff_abs_le_boxSum …).trans (boxSum_le_grade eps H
heps hreg hH)`. -/
lemma decoupledMean_aff_abs_le_box (eps : ℚ) (H : ℕ) (a b h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|
      ≤ boxGrade eps H :=
  (decoupledMean_aff_abs_le_boxSum eps H a b h hv).trans (boxSum_le_grade eps H heps hreg hH)

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
  classical
  set μ := logMeasureAff a x ω
  set X := liouvilleWindow H
  set Y := residueWindow eps H
  set cd := condDistrib Y X μ
  set W := fun n => (X n, Y n) with hW
  set S : Set ((Fin H → ℤ) × ZMod (PH eps H)) := {q | q.2 ∈ badSet_aff eps H a b h q.1 δ} with hS
  have hXmeas : Measurable X := measurable_liouvilleWindow H
  have hYmeas : Measurable Y := measurable_residueWindow eps H
  have hWmeas : Measurable W := hXmeas.prodMk hYmeas
  have hSmeas : MeasurableSet S := (Set.to_countable _).measurableSet
  have hAeq : {n | Y n ∈ badSet_aff eps H a b h (X n) δ} = W ⁻¹' S := rfl
  have hρ : μ.map W = μ.map X ⊗ₘ cd := (map_compProd_condDistrib hYmeas hXmeas μ).symm
  haveI hpW : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hWmeas.aemeasurable
  haveI hpC : IsProbabilityMeasure (μ.map X ⊗ₘ cd) := hρ ▸ hpW
  have hint : Integrable (S.indicator 1) (μ.map X ⊗ₘ cd) :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  calc μ.real {n | Y n ∈ badSet_aff eps H a b h (X n) δ}
      = (μ.map W).real S := by
        rw [hAeq]; simp only [measureReal_def, Measure.map_apply hWmeas hSmeas]
    _ = (μ.map X ⊗ₘ cd).real S := by rw [hρ]
    _ = ∫ q, S.indicator 1 q ∂(μ.map X ⊗ₘ cd) := (integral_indicator_one hSmeas).symm
    _ = ∫ x₀, ∫ y, S.indicator 1 (x₀, y) ∂(cd x₀) ∂(μ.map X) :=
        MeasureTheory.Measure.integral_compProd hint
    _ = ∫ x₀, (cd x₀).real ↑(badSet_aff eps H a b h x₀ δ) ∂(μ.map X) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x₀ => ?_))
        change ∫ y, S.indicator 1 (x₀, y) ∂(cd x₀) = (cd x₀).real ↑(badSet_aff eps H a b h x₀ δ)
        rw [← integral_indicator_one (μ := cd x₀)
          (s := (↑(badSet_aff eps H a b h x₀ δ) : Set (ZMod (PH eps H))))
          ((Set.to_countable _).measurableSet)]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        simp only [Set.indicator_apply, Set.mem_setOf_eq, hS, Finset.mem_coe, Pi.one_apply]

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
  classical
  set μ := logMeasureAff a x ω with hμ
  set X := liouvilleWindow H
  set Y := residueWindow eps H
  set cd := condDistrib Y X μ with hcd
  set δcal := (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) with hδcal
  set baddef : Set (Fin H → ℤ) := {x₀ | t < H[Y; μ] - Hm[cd x₀]} with hbaddef
  set β := (t + 2 * Real.log 2) / g with hβ
  have hXmeas : Measurable X := measurable_liouvilleWindow H
  have hYmeas : Measurable Y := measurable_residueWindow eps H
  haveI hpX : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  have hbaddef_meas : MeasurableSet baddef := (Set.to_countable _).measurableSet
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hC₀ : (0 : ℝ) < 2 * Real.log 4 := by positivity
  have hcard := primeWindow_card_le_of_regime eps H hreg hH
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hcorr : Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    have : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ) ≤ 1 := (div_le_one hxpos).mpr hhead
    linarith
  have hae : ∀ᵐ x₀ ∂(μ.map X), ∀ i, |x₀ i| ≤ 1 := by
    rw [ae_iff, Measure.map_apply hXmeas ((Set.to_countable _).measurableSet)]
    have hpre : X ⁻¹' {x₀ : Fin H → ℤ | ¬ ∀ i, |x₀ i| ≤ 1} = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun i => abs_liouvilleWindow_le_one H n i
    rw [hpre, measure_empty]
  have hbound : ∀ᵐ x₀ ∂(μ.map X),
      (cd x₀).real ↑(badSet_aff eps H a b h x₀ δcal) ≤ β + baddef.indicator 1 x₀ := by
    filter_upwards [hae] with x₀ hx₀le
    haveI : IsProbabilityMeasure (cd x₀) := by rw [hcd]; infer_instance
    by_cases hgood : H[Y; μ] - Hm[cd x₀] ≤ t
    · have hnotmem : x₀ ∉ baddef := by
        rw [hbaddef]; simp only [Set.mem_setOf_eq, not_lt]; exact hgood
      rw [Set.indicator_of_notMem hnotmem, add_zero]
      have htrans := badSet_transport_at_calibration_aff eps H a b h hx hω hωx hcop hx₀le heps
        heps1 hne hC₀ hcard hlog ht.le hgood hg hgle
      refine htrans.trans ?_
      rw [hβ]
      exact div_le_div_of_nonneg_right (by linarith [hcorr]) hg.le
    · have hmem : x₀ ∈ baddef := by
        rw [hbaddef]; simp only [Set.mem_setOf_eq]; exact lt_of_not_ge hgood
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      calc (cd x₀).real ↑(badSet_aff eps H a b h x₀ δcal) ≤ 1 := measureReal_le_one
        _ ≤ β + 1 := by linarith
  have hbadmass : (μ.map X).real baddef
      ≤ (κ + (Real.log (PH eps H : ℝ) - H[Y; μ])) / t := by
    have hdm := decrement_markov_fintype (β := ZMod (PH eps H)) hXmeas hYmeas ht hI
    rwa [ZMod.card] at hdm
  calc ∫ x₀, (cd x₀).real ↑(badSet_aff eps H a b h x₀ δcal) ∂(μ.map X)
      ≤ ∫ x₀, (β + baddef.indicator 1 x₀) ∂(μ.map X) :=
        integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _) hbound
    _ = β + (μ.map X).real baddef := by
        rw [integral_add (integrable_const β) (integrable_of_finiteSupport _),
          integral_const, integral_indicator_one hbaddef_meas, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (t + 2 * Real.log 2) / g
        + (κ + (Real.log (PH eps H : ℝ) - H[Y; μ])) / t := by rw [← hβ]; linarith [hbadmass]

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
  classical
  set δc := (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) with hδc
  set f : ℕ → ℝ := fun m => fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
    with hf
  set gm : ℕ → ℝ := fun m => ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
      if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
        (windowVal H (liouvilleWindow H m) j : ℝ)
          * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ) else 0 with hgm
  set A : Set ℕ := {m | residueWindow eps H m ∈ badSet_aff eps H a b h (liouvilleWindow H m) δc}
    with hA
  have hA_meas : MeasurableSet A := (Set.to_countable _).measurableSet
  have hbox0 : 0 ≤ boxGrade eps H := by
    have hlp : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
    rw [boxGrade]; positivity
  have hδ0 : 0 ≤ δc := by
    have hlp : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
    rw [hδc]; positivity
  have hf_int : Integrable f (logMeasureAff a x ω) := integrable_of_finiteSupport _
  have hg_int : Integrable gm (logMeasureAff a x ω) := integrable_of_finiteSupport _
  -- step 1: pointwise deviation bound
  have hdevbnd : ∀ m, |f m - gm m| ≤ δc + A.indicator (fun _ => 2 * boxGrade eps H) m := by
    intro m
    have hx₀ : ∀ i, |liouvilleWindow H m i| ≤ 1 := abs_liouvilleWindow_le_one H m
    have hmemiff : m ∈ A ↔ δc ≤ |f m - gm m| := by
      rw [hA]
      simp [Set.mem_setOf_eq, badSet_aff, Finset.mem_filter, Finset.mem_univ, hf, hgm]
    by_cases hmem : m ∈ A
    · rw [Set.indicator_of_mem hmem]
      have h1 := fBridgeF_aff_abs_le_box eps H a b h hx₀ heps hreg hH (residueWindow eps H m)
      have h2 := decoupledMean_aff_abs_le_box eps H a b h hx₀ heps hreg hH
      have htri : |f m - gm m| ≤ |f m| + |gm m| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      have h1' : |f m| ≤ boxGrade eps H := by rw [hf]; exact h1
      have h2' : |gm m| ≤ boxGrade eps H := by rw [hgm]; exact h2
      linarith
    · rw [Set.indicator_of_notMem hmem, add_zero]
      have := (not_iff_not.mpr hmemiff).mp hmem
      linarith [not_le.mp this]
  -- step 2: integrate to the explicit error
  have hdev_le : ∫ m, |f m - gm m| ∂(logMeasureAff a x ω)
      ≤ δc + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ)
              - H[residueWindow eps H; logMeasureAff a x ω])) / t) := by
    have hmass : (logMeasureAff a x ω).real A
        ≤ (t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ)
              - H[residueWindow eps H; logMeasureAff a x ω])) / t := by
      rw [hA, outer_badMass_aff_eq eps H a b h x ω δc]
      exact outer_badMass_aff_le eps H a b h hx hω hωx hcop heps heps1 hne hreg hH hlog hhead
        ht hg hgle hI
    have hstep : ∫ m, |f m - gm m| ∂(logMeasureAff a x ω)
        ≤ ∫ m, (δc + A.indicator (fun _ => 2 * boxGrade eps H) m) ∂(logMeasureAff a x ω) :=
      integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _)
        (Filter.Eventually.of_forall hdevbnd)
    refine hstep.trans ?_
    rw [integral_add (integrable_const δc) (integrable_of_finiteSupport _),
      integral_const, integral_indicator_const _ hA_meas, probReal_univ, smul_eq_mul, one_mul,
      smul_eq_mul]
    nlinarith [hmass, hbox0]
  -- step 3: triangle against h211
  have htri : |(∫ m, f m ∂(logMeasureAff a x ω)) - (∫ m, gm m ∂(logMeasureAff a x ω))|
      ≤ ∫ m, |f m - gm m| ∂(logMeasureAff a x ω) := by
    rw [← integral_sub hf_int hg_int]; exact abs_integral_le_integral_abs
  have hfg : |∫ m, f m ∂(logMeasureAff a x ω)|
      ≤ |∫ m, gm m ∂(logMeasureAff a x ω)| + ∫ m, |f m - gm m| ∂(logMeasureAff a x ω) := by
    calc |∫ m, f m ∂(logMeasureAff a x ω)|
        = |(∫ m, gm m ∂(logMeasureAff a x ω))
            + ((∫ m, f m ∂(logMeasureAff a x ω))
              - (∫ m, gm m ∂(logMeasureAff a x ω)))| := by
          congr 1; ring
      _ ≤ |∫ m, gm m ∂(logMeasureAff a x ω)|
          + |(∫ m, f m ∂(logMeasureAff a x ω))
            - (∫ m, gm m ∂(logMeasureAff a x ω))| := abs_add_le _ _
      _ ≤ |∫ m, gm m ∂(logMeasureAff a x ω)|
          + ∫ m, |f m - gm m| ∂(logMeasureAff a x ω) := by linarith [htri]
  have hchain := le_trans h211 hfg
  linarith [hchain, hdev_le]

/-- **F4-K6a (class B) — the `(1, 0)` compat of the assembly, RESTATED v1.1 (verdict A2(a)) so
that it can fail.**  `hI` and `h211` are in the AFFINE vocabulary at `(a, b) = (1, 0)`
(`logMeasureAff 1 x ω`, `fBridgeF_aff eps H 1 0 h`); the conclusion is `outer_combine_h`'s
(`OuterCombine.lean:620`) VERBATIM at the landed `logMeasure x ω` (the entropy term, the measure,
the unfiltered inner sum).  Discharge: `outer_combine_aff eps H 1 0 h … (Nat.coprime_one_left _) …
hI h211`, then the bridges ON THE CONCLUSION — `logMeasureAff_one` (the measure and the entropy
term), the filter at `ZMod 1` (`eq_iff_true_of_subsingleton`, `if_true`) under the integral binder
(`simp only`, not `rw`).  The v1 form restated `outer_combine_h` up to `_hc₁ → hc₁` and could not
fail; here `logMeasureAff_one` and the `ZMod 1` collapse are LOAD-BEARING. -/
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
    {κ : ℝ} (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasureAff 1 x ω] ≤ κ)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (h211 : c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff eps H 1 0 h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff 1 x ω)|) :
    c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        - ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
              + (κ + (Real.log (PH eps H : ℝ)
                  - H[residueWindow eps H; logMeasure x ω])) / t))
      ≤ |∫ n, (∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ))
          ∂(logMeasure x ω)| := by
  have key := outer_combine_aff eps H 1 0 h hx hω hωx (Nat.coprime_one_left _) heps heps1 hne
    hreg hH hlog hhead ht hg hgle hI hc₁ h211
  rw [logMeasureAff_one] at key
  simpa only [eq_iff_true_of_subsingleton, if_true] using key

end Salt.Entropy.Chowla
