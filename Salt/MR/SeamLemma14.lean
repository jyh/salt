/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamCalibration
import Salt.MR.Lemma14

/-!
# `SeamLemma14` — THE JUNCTION: the closed seam row as `lemma14_contour`'s input

`SeamCalibration.seam_row_calibrated` is the seam row closed end to end — it bounds the
annular mean square

  `∫_{Ann(T₀,Tann)} ‖spoly N a t‖² dt ≤ 8S² + (the §8.1 level-1 term + the `P₁` term
    + Σ_j lemma12Rows) + 2(Tann/X+1)(log X)^{−θ₂₉₃+ε}`,

with `Ann(T₀,Tann) = {t : (log X)^{1/45} ≤ |t| ≤ Tann}` (`SeamSplit.seamAnn`).
`Lemma14.lemma14_contour` is its designed consumer: it needs, on its right-hand side, the
two *interval* integrals `∫_{T₀}^{X/h₁} ‖A(1+it)‖²` and `∫_{−X/h₁}^{−T₀} ‖A(1+it)‖²` of the
CONCRETE Dirichlet polynomial `dpolyA a s0`, plus the weighted max-term datum `Msup`.

Three shape gaps sit between supply and demand; this file closes all three.

* **The set/interval gap** (`seamAnn_integral_split`, J1).  The annulus is
  `[−Tann, −T₀] ∪ [T₀, Tann]`, and the two arms are DISJOINT exactly when `0 < T₀` —
  i.e. exactly when `1 < X`.  At `X = 1` they meet at `{0}` and the `Disjoint` step (hence
  `integral_union`) fails; the hypothesis `hT0 : 0 < seamT0 X` is therefore load-bearing,
  not decorative.
* **The polynomial gap** (`spoly_eq_dpolyA_filter`, J2).  `spoly N a t` sums over
  `Finset.Icc 1 N`; `dpolyA a s0 t` sums over an abstract `s0` on which `lemma14_contour`
  imposes `hrange : ∀ m ∈ s0, X ≤ m ≤ 4X`.  The row's own support hypothesis
  `hsupp : (n : ℝ) ≤ X → a n = 0` kills every index `Icc 1 N` carries below `X`, so the
  correct `s0` is `seamS0 N X = (Finset.Icc 1 N).filter (X < ·)`, on which `hrange` is a
  one-liner from `X ≤ N ≤ 2X`.  **`lemma14_contour`'s statement is not touched** (iron
  rule 1): the repair is entirely on the supply side.
* **The `Msup` gap** (`lemma14_contour_of_Msup_at`, J4′).  `lemma14_contour` takes
  `hMsup : ∀ T ≥ X/h₁, (X/h₁)/T·(∫_T^{2T} + ∫_{−2T}^{−T}) ≤ Msup`, but its proof fires that
  binder **once**, at `T = X/h₁` (where the weight is `1`).  The seam row supplies ONE
  annulus height at a time, so the `∀T` form is unsuppliable while the single instance is
  free.  `lemma14_contour_of_Msup_at` is the additive variant taking exactly that instance;
  its proof mirrors `lemma14_contour`'s, and — since `Lemma14`'s five-way-split scaffolding
  (`vdiffR`, `vSeg_split_five`, …) is `private` — §3 re-derives that scaffolding verbatim
  (the `PerronMeanSq` precedent).

## The gates the junction adds (flagged, never silent)

Three hypotheses are NOT in the seam row's surviving 69-binder frame and enter here:

* `ha : ∀ m ∈ s0, ‖a m‖ ≤ 1` — `lemma14_contour`'s coefficient bound.  The row carries
  1-boundedness for `g`, `c`, `b`, `cf` but NOT for `a` (whose contract is the Lemma-12
  factorization `a (p*m) = b m * c p`).  New binder.
* `2 ≤ h₁` — the truncation gate.  The far arm lives at `Tann = 2X/h₁`, and the row's frame
  already demands `Tann ≤ X`; `2X/h₁ ≤ X ⟺ h₁ ≥ 2`, so this is FORCED by the row rather than
  independent of it — spelled out because the consumer must meet it.  (J5's station carries
  AS-2's stronger MVT guard `Tann ≤ X/2`, i.e. `4 ≤ h₁` at that height.)
* `h₁ ≤ h₂ ≤ X(log X)^{−1/5}` — `lemma14_contour`'s own window frame, carried through.

## The exit

`lemma14_contour_seam_supplied` is the abstract junction (the row's bound at the two heights
as free reals `R₁`, `R₂`); `lemma14_contour_seam_supplied_calibrated` is the concrete one —
`seam_row_calibrated` instantiated at `Tann = 2X/h₁`, both of Lemma 14's analytic terms paid
by that single row (`seamAnn X (X/h₁) ⊆ seamAnn X (2X/h₁)`), `Msup` eliminated, and NO
integral anywhere on the right.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex
open scoped BigOperators

/-! ## §1 — J1/J2: the two shape gaps -/

/-- **J1 — the annulus is two intervals** (`seamAnn_integral_split`).
`Ann(T₀,T) = [−T, −T₀] ⊔ [T₀, T]`, so its set integral is the sum of two interval integrals.

The `{0}`-meeting trap: the two arms are disjoint **only** for `0 < T₀ = seamT0 X`; at
`T₀ = 0` they share `{0}` and `Disjoint` — the hypothesis of `integral_union` — is false.
`0 < seamT0 X` is `1 < X` (`seamT0 X = (log X)^{1/45}`, an `rpow` of `log X`). -/
theorem seamAnn_integral_split {F : ℝ → ℝ} (hF : Continuous F) {X T : ℝ}
    (hT0 : 0 < seamT0 X) (hT : seamT0 X ≤ T) :
    (∫ t in seamAnn X T, F t)
      = (∫ t in (seamT0 X)..T, F t) + ∫ t in (-T)..(-(seamT0 X)), F t := by
  have hset : seamAnn X T = Set.Icc (seamT0 X) T ∪ Set.Icc (-T) (-(seamT0 X)) := by
    ext t
    simp only [seamAnn, Set.mem_setOf_eq, Set.mem_union, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht] at h1 h2
        exact Or.inl ⟨h1, h2⟩
      · rw [abs_of_neg ht] at h1 h2
        exact Or.inr ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have ht : (0 : ℝ) ≤ t := le_trans hT0.le h1
        rw [abs_of_nonneg ht]; exact ⟨h1, h2⟩
      · have ht : t < 0 := lt_of_le_of_lt h2 (by linarith)
        rw [abs_of_neg ht]; exact ⟨by linarith, by linarith⟩
  have hdisj : Disjoint (Set.Icc (seamT0 X) T) (Set.Icc (-T) (-(seamT0 X))) := by
    rw [Set.disjoint_left]
    rintro t ht1 ht2
    rw [Set.mem_Icc] at ht1 ht2
    linarith [ht1.1, ht2.2]
  have hint1 : IntegrableOn F (Set.Icc (seamT0 X) T) volume := hF.integrableOn_Icc
  have hint2 : IntegrableOn F (Set.Icc (-T) (-(seamT0 X))) volume := hF.integrableOn_Icc
  rw [hset, setIntegral_union hdisj measurableSet_Icc hint1 hint2,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_of_le (by linarith : -T ≤ -(seamT0 X))]

/-- **The junction's index set** `s0 = {m ∈ [1, N] : X < m}` — `lemma14_contour`'s `s0` slot,
built from the row's own dyadic cutoff `N`. -/
def seamS0 (N : ℕ) (X : ℝ) : Finset ℕ := (Finset.Icc 1 N).filter (fun m : ℕ => X < (m : ℝ))

/-- **J2 — the polynomial gap** (`spoly_eq_dpolyA_filter`): under the row's support
hypothesis, `spoly N a = dpolyA a (seamS0 N X)`.  The discarded indices are exactly those
with `(m : ℝ) ≤ X`, where `a m = 0`. -/
theorem spoly_eq_dpolyA_filter {N : ℕ} {a : ℕ → ℂ} {X : ℝ}
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) (t : ℝ) :
    spoly N a t = dpolyA a (seamS0 N X) t := by
  simp only [spoly, dpolyA, seamS0]
  refine (Finset.sum_filter_of_ne ?_).symm
  intro n _ hne
  by_contra hc
  exact hne (by rw [hsupp n (not_lt.mp hc), zero_div])

/-- **J2's `hrange`** — the range contract `lemma14_contour` demands, DERIVED (not assumed)
on `seamS0 N X` from the row's dyadic gate `N ≤ 2X`.  Iron rule 1: the consumer's statement
is untouched; only the supply is repaired. -/
theorem seamS0_range {N : ℕ} {X : ℝ} (hN2 : (N : ℝ) ≤ 2 * X) :
    ∀ m ∈ seamS0 N X, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X := by
  intro m hm
  rw [seamS0, Finset.mem_filter, Finset.mem_Icc] at hm
  have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm.1.2
  exact ⟨hm.2.le, by linarith⟩

/-- Every index of `seamS0 N X` is positive (it exceeds `X ≥ 0`). -/
theorem seamS0_pos {N : ℕ} {X : ℝ} (hX0 : 0 ≤ X) : ∀ m ∈ seamS0 N X, 0 < m := by
  intro m hm
  rw [seamS0, Finset.mem_filter] at hm
  exact_mod_cast lt_of_le_of_lt hX0 hm.2

/-- `t ↦ ‖A(1+it)‖²` is continuous at the junction's index set — the integrand of both
sides of the junction. -/
theorem dpolyA_seamS0_normSq_continuous {N : ℕ} {a : ℕ → ℂ} {X : ℝ} (hX0 : 0 ≤ X) :
    Continuous (fun t : ℝ => ‖dpolyA a (seamS0 N X) t‖ ^ 2) :=
  ((dpolyA_continuous a (seamS0 N X) (seamS0_pos hX0)).norm).pow 2

/-- `t ↦ ‖spoly N a t‖²` is continuous — the integrand of the seam row's left-hand side,
in the form J1 consumes. -/
theorem spoly_normSq_continuous {N : ℕ} {a : ℕ → ℂ} {X : ℝ} (hX0 : 0 ≤ X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) :
    Continuous (fun t : ℝ => ‖spoly N a t‖ ^ 2) := by
  have hcong : (fun t : ℝ => ‖spoly N a t‖ ^ 2)
      = fun t : ℝ => ‖dpolyA a (seamS0 N X) t‖ ^ 2 := by
    funext t; rw [spoly_eq_dpolyA_filter hsupp t]
  rw [hcong]
  exact dpolyA_seamS0_normSq_continuous hX0

/-- `0 < seamT0 X` from `1 < X` — J1's disjointness gate, in the form the junction meets it.
-/
theorem seamT0_pos {X : ℝ} (hX1 : 1 < X) : 0 < seamT0 X := by
  rw [seamT0]
  exact Real.rpow_pos_of_pos (Real.log_pos hX1) _

/-! ## §2 — J3/J4: the row's annular datum, transferred to Lemma 14's interval integrals

Both stones read the seam row's left-hand side through J1 and J2 and hand `lemma14_contour`
the shape it asks for.  The row bound itself enters as a free real `R` — the SUPPLY is
instantiated once, at the exit (§5), so the row's sixty-binder frame is written down exactly
once in this file. -/

/-- **J3 — THE MID-RANGE** (`seam_midrange_bound`).  At annulus height `T` the row's datum
IS `lemma14_contour`'s second term:

  `∫_{T₀}^{T} ‖A(1+it)‖² + ∫_{−T}^{−T₀} ‖A(1+it)‖² ≤ R`.

The designed instance is `T := X/h₁` (`lemma14_contour`'s `W`). -/
theorem seam_midrange_bound {N : ℕ} {a : ℕ → ℂ} {X T R : ℝ} (hX1 : 1 < X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) (hT : seamT0 X ≤ T)
    (hrow : (∫ t in seamAnn X T, ‖spoly N a t‖ ^ 2) ≤ R) :
    (∫ t in (seamT0 X)..T, ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + ∫ t in (-T)..(-(seamT0 X)), ‖dpolyA a (seamS0 N X) t‖ ^ 2 ≤ R := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  simp only [spoly_eq_dpolyA_filter hsupp] at hrow
  rwa [seamAnn_integral_split (dpolyA_seamS0_normSq_continuous hX0) (seamT0_pos hX1) hT]
    at hrow

/-- The row at height `2W`, cut into its four `lemma14_contour` pieces:
`[T₀,W]`, `[W,2W]`, `[−2W,−W]`, `[−W,−T₀]`. -/
theorem seam_split_four {N : ℕ} {a : ℕ → ℂ} {X W : ℝ} (hX1 : 1 < X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) (hTW : seamT0 X ≤ W) :
    (∫ t in seamAnn X (2 * W), ‖spoly N a t‖ ^ 2)
      = ((∫ t in (seamT0 X)..W, ‖dpolyA a (seamS0 N X) t‖ ^ 2)
            + ∫ t in W..(2 * W), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + ((∫ t in (-(2 * W))..(-W), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
            + ∫ t in (-W)..(-(seamT0 X)), ‖dpolyA a (seamS0 N X) t‖ ^ 2) := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hT0 : 0 < seamT0 X := seamT0_pos hX1
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le hT0 hTW
  have hc := dpolyA_seamS0_normSq_continuous (N := N) (a := a) hX0
  have e1 : (∫ t in (seamT0 X)..(2 * W), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      = (∫ t in (seamT0 X)..W, ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + ∫ t in W..(2 * W), ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have e2 : (∫ t in (-(2 * W))..(-(seamT0 X)), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      = (∫ t in (-(2 * W))..(-W), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + ∫ t in (-W)..(-(seamT0 X)), ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  simp only [spoly_eq_dpolyA_filter hsupp]
  rw [seamAnn_integral_split hc hT0 (by linarith : seamT0 X ≤ 2 * W), e1, e2]

/-- **J4 — THE `Msup` BLOCK** (`seam_Msup`).  At annulus height `2W` the row pays for the two
far dyadic blocks — the ONLY instance of `lemma14_contour`'s `hMsup` binder that ever fires
(there at `T = W = X/h₁`, where the weight `(X/h₁)/T` is `1`):

  `∫_{W}^{2W} ‖A(1+it)‖² + ∫_{−2W}^{−W} ‖A(1+it)‖² ≤ R`.

**Flagged gate**: the designed instance is `W := X/h₁`, so `2W = 2X/h₁`, and the row's frame
demands `Tann ≤ X`.  That is `2X/h₁ ≤ X`, i.e. `2 ≤ h₁` — a binder the junction ADDS. -/
theorem seam_Msup {N : ℕ} {a : ℕ → ℂ} {X W R : ℝ} (hX1 : 1 < X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) (hTW : seamT0 X ≤ W)
    (hrow : (∫ t in seamAnn X (2 * W), ‖spoly N a t‖ ^ 2) ≤ R) :
    (∫ t in W..(2 * W), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + ∫ t in (-(2 * W))..(-W), ‖dpolyA a (seamS0 N X) t‖ ^ 2 ≤ R := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hT0 : 0 < seamT0 X := seamT0_pos hX1
  have hmid1 : (0 : ℝ) ≤ ∫ t in (seamT0 X)..W, ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hTW (fun _ _ => by positivity)
  have hmid2 : (0 : ℝ) ≤ ∫ t in (-W)..(-(seamT0 X)), ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  rw [seam_split_four hX1 hsupp hTW] at hrow
  linarith

/-- The tall row also pays for the mid-range (`seamAnn X W ⊆ seamAnn X (2W)`) — this is what
lets ONE instance of `seam_row_calibrated`, at `Tann = 2X/h₁`, discharge BOTH of Lemma 14's
analytic terms.  (The sharper two-height route is `seam_midrange_bound` at `T = X/h₁`.) -/
theorem seam_midrange_of_tall_row {N : ℕ} {a : ℕ → ℂ} {X W R : ℝ} (hX1 : 1 < X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) (hTW : seamT0 X ≤ W)
    (hrow : (∫ t in seamAnn X (2 * W), ‖spoly N a t‖ ^ 2) ≤ R) :
    (∫ t in (seamT0 X)..W, ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + ∫ t in (-W)..(-(seamT0 X)), ‖dpolyA a (seamS0 N X) t‖ ^ 2 ≤ R := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hT0 : 0 < seamT0 X := seamT0_pos hX1
  have hfar1 : (0 : ℝ) ≤ ∫ t in W..(2 * W), ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hfar2 : (0 : ℝ) ≤ ∫ t in (-(2 * W))..(-W), ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  rw [seam_split_four hX1 hsupp hTW] at hrow
  linarith


/-! ## §3 — `Lemma14`'s five-way-split scaffolding, RE-DERIVED

Every declaration between here and `lemma14_contour_of_Msup_at` is a **verbatim** copy of a
`private` declaration of `Salt.MR.Lemma14` (`coeff_sum_inv_le`, `norm_sum_five_sq_le`,
`integral_five_add`, `uSlab_eq_vSeg`, `vSeg_add_adjacent`, `vSeg_split_five`, `vdiffR`,
`vdiffR_continuous`, `vdiffR_eq`, `five_split_integral_bound`).  They are private there, so
they cannot be imported; the `PerronMeanSq` precedent applies — re-derive, byte for byte, and
say so.  Nothing here is new mathematics and nothing here is weakened. -/

/-- The coefficient mass of an `[X, 4X]`-supported index set: `∑_{m ∈ s0} 1/m ≤ 5`.
(`s0 ⊆ [0, ⌊4X⌋]` gives `card ≤ 4X + 1`, and each term is `≤ 1/X`.) -/
private lemma coeff_sum_inv_le {X : ℝ} (hX : 1 ≤ X) (s0 : Finset ℕ)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X) :
    (∑ m ∈ s0, 1 / (m : ℝ)) ≤ 5 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hsub : s0 ⊆ Finset.Icc 0 ⌊4 * X⌋₊ := by
    intro m hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.le_floor (hrange m hm).2⟩
  have hcard : (s0.card : ℝ) ≤ 4 * X + 1 := by
    have h1 : s0.card ≤ ⌊4 * X⌋₊ + 1 := by
      have h2 := Finset.card_le_card hsub
      rwa [Nat.card_Icc, Nat.sub_zero] at h2
    have h3 : ((⌊4 * X⌋₊ : ℕ) : ℝ) ≤ 4 * X := Nat.floor_le (by linarith)
    have h4 : (s0.card : ℝ) ≤ ((⌊4 * X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_add, Nat.cast_one] at h4
    linarith
  calc (∑ m ∈ s0, 1 / (m : ℝ)) ≤ ∑ _m ∈ s0, 1 / X :=
        Finset.sum_le_sum fun m hm => one_div_le_one_div_of_le hX0 (hrange m hm).1
    _ = s0.card * (1 / X) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * X + 1) * (1 / X) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 5 := by rw [mul_one_div, div_le_iff₀ hX0]; linarith

/-- `‖z₁+z₂+z₃+z₄+z₅‖² ≤ 5·(‖z₁‖²+⋯+‖z₅‖²)` — the five-way triangle/AM–QM step. -/
private lemma norm_sum_five_sq_le (z₁ z₂ z₃ z₄ z₅ : ℂ) :
    ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ^ 2
      ≤ 5 * (‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 + ‖z₃‖ ^ 2 + ‖z₄‖ ^ 2 + ‖z₅‖ ^ 2) := by
  have htri : ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ≤ ‖z₁‖ + ‖z₂‖ + ‖z₃‖ + ‖z₄‖ + ‖z₅‖ := by
    have t1 : ‖z₁ + z₂ + z₃ + z₄ + z₅‖ ≤ ‖z₁ + z₂ + z₃ + z₄‖ + ‖z₅‖ := norm_add_le _ _
    have t2 : ‖z₁ + z₂ + z₃ + z₄‖ ≤ ‖z₁ + z₂ + z₃‖ + ‖z₄‖ := norm_add_le _ _
    have t3 : ‖z₁ + z₂ + z₃‖ ≤ ‖z₁ + z₂‖ + ‖z₃‖ := norm_add_le _ _
    have t4 : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
    linarith
  refine (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans ?_
  nlinarith [sq_nonneg (‖z₁‖ - ‖z₂‖), sq_nonneg (‖z₁‖ - ‖z₃‖), sq_nonneg (‖z₁‖ - ‖z₄‖),
    sq_nonneg (‖z₁‖ - ‖z₅‖), sq_nonneg (‖z₂‖ - ‖z₃‖), sq_nonneg (‖z₂‖ - ‖z₄‖),
    sq_nonneg (‖z₂‖ - ‖z₅‖), sq_nonneg (‖z₃‖ - ‖z₄‖), sq_nonneg (‖z₃‖ - ‖z₅‖),
    sq_nonneg (‖z₄‖ - ‖z₅‖)]

/-- Additivity of an interval integral over a five-term sum. -/
private lemma integral_five_add {f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ} {p q : ℝ}
    (h₁ : IntervalIntegrable f₁ volume p q) (h₂ : IntervalIntegrable f₂ volume p q)
    (h₃ : IntervalIntegrable f₃ volume p q) (h₄ : IntervalIntegrable f₄ volume p q)
    (h₅ : IntervalIntegrable f₅ volume p q) :
    (∫ x in p..q, (f₁ x + f₂ x + f₃ x + f₄ x + f₅ x))
      = (∫ x in p..q, f₁ x) + (∫ x in p..q, f₂ x) + (∫ x in p..q, f₃ x)
        + (∫ x in p..q, f₄ x) + ∫ x in p..q, f₅ x := by
  rw [intervalIntegral.integral_add (((h₁.add h₂).add h₃).add h₄) h₅,
    intervalIntegral.integral_add ((h₁.add h₂).add h₃) h₄,
    intervalIntegral.integral_add (h₁.add h₂) h₃,
    intervalIntegral.integral_add h₁ h₂]

/-! ## E1 — the frequency split of the truncated Perron object -/

/-- The `U`-slab at truncation `T` IS the `V`-segment on `[−T, T]` (same normalization). -/
private lemma uSlab_eq_vSeg (A : ℝ → ℂ) (x h T : ℝ) : uSlab A x h T = vSeg A x h (-T) T := rfl

/-- Adjacent frequency segments add. -/
private lemma vSeg_add_adjacent {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (p q r : ℝ) :
    vSeg A x h p q + vSeg A x h q r = vSeg A x h p r := by
  have hc : Continuous (fun t : ℝ => A t * uKernel x h t) :=
    hA.mul (uKernel_continuous hx hxh)
  rw [vSeg, vSeg, vSeg, ← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]

/-- **The five-way frequency split** of the truncated Perron object:
`[−Tc, Tc] = [−Tc, −W] ∪ [−W, −T₀] ∪ [−T₀, T₀] ∪ [T₀, W] ∪ [W, Tc]`. -/
private lemma vSeg_split_five {A : ℝ → ℂ} (hA : Continuous A) {x h : ℝ}
    (hx : 0 < x) (hxh : 0 < x + h) (T₀ W Tc : ℝ) :
    vSeg A x h (-Tc) Tc
      = vSeg A x h (-Tc) (-W) + vSeg A x h (-W) (-T₀) + vSeg A x h (-T₀) T₀
        + vSeg A x h T₀ W + vSeg A x h W Tc := by
  have e : ∀ p q r : ℝ, vSeg A x h p q + vSeg A x h q r = vSeg A x h p r :=
    fun p q r => vSeg_add_adjacent hA hx hxh p q r
  rw [← e (-Tc) W Tc, ← e (-Tc) T₀ W, ← e (-Tc) (-T₀) T₀, ← e (-Tc) (-W) (-T₀)]

/-! ## E2 — the regularized weighted `V`-difference (continuity in `x`) -/

/-- The weighted `V`-difference on a frequency segment, written through the `max`-regularized
tail transform `tailTr` — globally continuous in `x`, and equal to the honest
`(1/h₁)·vSeg − (1/h₂)·vSeg` for `x ≥ X` (`vdiffR_eq`).  This is the device that makes every
`x`-integral in the assembly interval-integrable. -/
private def vdiffR (A : ℝ → ℂ) (X h₁ h₂ α β x : ℝ) : ℂ :=
  ((1 / h₁ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₁), tailTr A α β (X / 2) u)
    - ((1 / h₂ : ℝ) : ℂ) * (I * ∫ u in x..(x + h₂), tailTr A α β (X / 2) u)

private lemma vdiffR_continuous {A : ℝ → ℂ} (hA : Continuous A) {X : ℝ} (hX : 0 < X)
    (h₁ h₂ α β : ℝ) : Continuous (fun x : ℝ => vdiffR A X h₁ h₂ α β x) := by
  have hFr : Continuous (tailTr A α β (X / 2)) := tailTr_continuous hA α β (by linarith)
  simp only [vdiffR]
  exact (continuous_const.mul (continuous_const.mul (continuous_window_integral hFr h₁))).sub
    (continuous_const.mul (continuous_const.mul (continuous_window_integral hFr h₂)))

private lemma vdiffR_eq {A : ℝ → ℂ} (hA : Continuous A) {X x h₁ h₂ : ℝ}
    (hX : 0 < X) (hx : X ≤ x) (hh1 : 0 ≤ h₁) (hh2 : 0 ≤ h₂) {α β : ℝ} :
    vdiffR A X h₁ h₂ α β x
      = ((1 / h₁ : ℝ) : ℂ) * vSeg A x h₁ α β - ((1 / h₂ : ℝ) : ℂ) * vSeg A x h₂ α β := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx
  have key : ∀ h : ℝ, 0 ≤ h →
      vSeg A x h α β = I * ∫ u in x..(x + h), tailTr A α β (X / 2) u := by
    intro h hh
    rw [vSeg_eq_tailT_integral hA hx0 hh]
    congr 1
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by linarith : x ≤ x + h), Set.mem_Icc] at hu
    exact (tailTr_eq A α β (by linarith [hu.1] : X / 2 ≤ u)).symm
  simp only [vdiffR]
  rw [key h₁ hh1, key h₂ hh2]

/-- The five-way split of the `x`-integrated squared weighted Perron difference. -/
private lemma five_split_integral_bound {A : ℝ → ℂ} (hA : Continuous A) {X h₁ h₂ : ℝ}
    (hX : 0 < X) (hh1 : 0 < h₁) (hh2 : 0 < h₂) (T₀ W Tc : ℝ) :
    (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ Tc - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ Tc‖ ^ 2)
      ≤ 5 * ((∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ (-Tc) (-W) x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ (-W) (-T₀) x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ (-T₀) T₀ x‖ ^ 2)
          + (∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ T₀ W x‖ ^ 2)
          + ∫ x in X..(2 * X), ‖vdiffR A X h₁ h₂ W Tc x‖ ^ 2) := by
  have hX2 : X ≤ 2 * X := by linarith
  have hc : ∀ α β : ℝ, Continuous (fun x : ℝ => vdiffR A X h₁ h₂ α β x) :=
    fun α β => vdiffR_continuous hA hX h₁ h₂ α β
  have hsq : ∀ α β : ℝ, Continuous (fun x : ℝ => ‖vdiffR A X h₁ h₂ α β x‖ ^ 2) :=
    fun α β => ((hc α β).norm).pow 2
  have hsplit : ∀ x : ℝ, X ≤ x →
      ((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ Tc - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ Tc
        = vdiffR A X h₁ h₂ (-Tc) (-W) x + vdiffR A X h₁ h₂ (-W) (-T₀) x
          + vdiffR A X h₁ h₂ (-T₀) T₀ x + vdiffR A X h₁ h₂ T₀ W x
          + vdiffR A X h₁ h₂ W Tc x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX hx
    rw [vdiffR_eq hA hX hx hh1.le hh2.le, vdiffR_eq hA hX hx hh1.le hh2.le,
      vdiffR_eq hA hX hx hh1.le hh2.le, vdiffR_eq hA hX hx hh1.le hh2.le,
      vdiffR_eq hA hX hx hh1.le hh2.le, uSlab_eq_vSeg, uSlab_eq_vSeg,
      vSeg_split_five hA hx0 (show (0 : ℝ) < x + h₁ by linarith) T₀ W Tc,
      vSeg_split_five hA hx0 (show (0 : ℝ) < x + h₂ by linarith) T₀ W Tc]
    ring
  have hcongr : (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab A x h₁ Tc - ((1 / h₂ : ℝ) : ℂ) * uSlab A x h₂ Tc‖ ^ 2)
      = ∫ x in X..(2 * X),
          ‖vdiffR A X h₁ h₂ (-Tc) (-W) x + vdiffR A X h₁ h₂ (-W) (-T₀) x
            + vdiffR A X h₁ h₂ (-T₀) T₀ x + vdiffR A X h₁ h₂ T₀ W x
            + vdiffR A X h₁ h₂ W Tc x‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hX2, Set.mem_Icc] at hx
    rw [hsplit x hx.1]
  rw [hcongr]
  have hcs : Continuous (fun x : ℝ =>
      ‖vdiffR A X h₁ h₂ (-Tc) (-W) x + vdiffR A X h₁ h₂ (-W) (-T₀) x
        + vdiffR A X h₁ h₂ (-T₀) T₀ x + vdiffR A X h₁ h₂ T₀ W x
        + vdiffR A X h₁ h₂ W Tc x‖ ^ 2) :=
    ((((((hc _ _).add (hc _ _)).add (hc _ _)).add (hc _ _)).add (hc _ _)).norm).pow 2
  have hcm : Continuous (fun x : ℝ =>
      5 * (‖vdiffR A X h₁ h₂ (-Tc) (-W) x‖ ^ 2 + ‖vdiffR A X h₁ h₂ (-W) (-T₀) x‖ ^ 2
        + ‖vdiffR A X h₁ h₂ (-T₀) T₀ x‖ ^ 2 + ‖vdiffR A X h₁ h₂ T₀ W x‖ ^ 2
        + ‖vdiffR A X h₁ h₂ W Tc x‖ ^ 2)) :=
    continuous_const.mul
      (((((hsq _ _).add (hsq _ _)).add (hsq _ _)).add (hsq _ _)).add (hsq _ _))
  refine le_trans (intervalIntegral.integral_mono_on hX2 (hcs.intervalIntegrable _ _)
    (hcm.intervalIntegrable _ _) (fun x _ => norm_sum_five_sq_le _ _ _ _ _)) (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact integral_five_add ((hsq _ _).intervalIntegrable _ _) ((hsq _ _).intervalIntegrable _ _)
    ((hsq _ _).intervalIntegrable _ _) ((hsq _ _).intervalIntegrable _ _)
    ((hsq _ _).intervalIntegrable _ _)

/-- **J4′ — LEMMA 14 AT THE SINGLE `Msup` INSTANCE** (`lemma14_contour_of_Msup_at`).

`lemma14_contour`'s `hMsup` binder quantifies over every `T ≥ X/h₁`, but its proof reads that
binder EXACTLY ONCE, at `T = X/h₁`, where the weight `(X/h₁)/T` collapses to `1`.  The seam
row supplies one annulus height at a time, so the `∀T` form has no supply while the single
instance does (`seam_Msup`).  This is `lemma14_contour` with that instance in place of the
family — an ADDITIVE variant: `lemma14_contour` is untouched (iron rule 1), and this theorem
is strictly more applicable (`hMsup` at `T = X/h₁` gives `hMsupAt` by `div_self`).

Proof: `lemma14_contour`'s, verbatim, with the two lines

  `have hMsupW := hMsup (X / h₁) le_rfl` / `rw [div_self hWpos.ne', one_mul] at hMsupW`

replaced by `have hMsupW := hMsupAt`.  Everything else — the five-way split, S-B on the slab,
S-C on the four `V`-segments, the constants — is byte-identical. -/
theorem lemma14_contour_of_Msup_at (a : ℕ → ℂ) (s0 : Finset ℕ) {X h₁ h₂ Msup : ℝ}
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ s0, ‖a m‖ ≤ 1)
    (hrange : ∀ m ∈ s0, X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X)
    (hMsupAt : (∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2)
        + (∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2) ≤ Msup) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₁ (2 * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a s0) x h₂ (2 * (X / h₁))‖ ^ 2)
      ≤ 2000 * (Real.log X) ^ (-(14 / 45 : ℝ))
        + 820 * Real.pi * ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁),
              ‖dpolyA a s0 t‖ ^ 2)
            + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))), ‖dpolyA a s0 t‖ ^ 2)
        + 820 * Real.pi * Msup := by
  -- E4.0 — the arithmetic environment
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) < X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hLp : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hL1 : (1 : ℝ) ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2' : (0 : ℝ) < h₂ := by linarith
  have hLinv1 : (Real.log X) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hh2X' : h₂ ≤ X := by nlinarith
  have hh1X : h₁ ≤ X := le_trans hh12 hh2X'
  have hpos : ∀ m ∈ s0, 0 < m := by
    intro m hm
    have hm1 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) (hrange m hm).1
    exact_mod_cast hm1
  have hAc : Continuous (dpolyA a s0) := dpolyA_continuous a s0 hpos
  have hWpos : (0 : ℝ) < X / h₁ := div_pos hXpos hh1'
  have hT0pos : (0 : ℝ) < (Real.log X) ^ (1 / 45 : ℝ) := Real.rpow_pos_of_pos hLp _
  -- E4.1 — `T₀ ≤ W = X/h₁`
  have hT0W : (Real.log X) ^ (1 / 45 : ℝ) ≤ X / h₁ := by
    have hstep1 : (Real.log X) ^ (1 / 45 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hstep2 : (Real.log X) ^ (1 / 5 : ℝ) ≤ X / h₂ := by
      rw [le_div_iff₀ hh2']
      have hL5 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLp.le _
      calc (Real.log X) ^ (1 / 5 : ℝ) * h₂
          ≤ (Real.log X) ^ (1 / 5 : ℝ) * (X * (Real.log X) ^ (-(1 / 5 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hh2X hL5
        _ = X * ((Real.log X) ^ (1 / 5 : ℝ) * (Real.log X) ^ (-(1 / 5 : ℝ))) := by ring
        _ = X := by rw [← Real.rpow_add hLp]; norm_num
    have hstep3 : X / h₂ ≤ X / h₁ := by gcongr
    linarith
  -- E4.2 — the two far blocks are paid by `Msup` (the single affordable dyadic instance)
  have hMsupW := hMsupAt
  have hMnn : (0 : ℝ) ≤ Msup := by
    have hn1 : (0 : ℝ) ≤ ∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    have hn2 : (0 : ℝ) ≤ ∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
    linarith
  -- E4.3 — S-C: every `V`-segment
  have hSC : ∀ α β : ℝ, α ≤ β →
      1 / X * (∫ x in X..(2 * X), ‖vdiffR (dpolyA a s0) X h₁ h₂ α β x‖ ^ 2)
        ≤ 164 * Real.pi * ∫ t in α..β, ‖dpolyA a s0 t‖ ^ 2 := by
    intro α β hab
    have hcongr : (∫ x in X..(2 * X), ‖vdiffR (dpolyA a s0) X h₁ h₂ α β x‖ ^ 2)
        = ∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₁ α β
              - ((1 / h₂ : ℝ) : ℂ) * vSeg (dpolyA a s0) x h₂ α β‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by linarith : X ≤ 2 * X), Set.mem_Icc] at hx
      rw [vdiffR_eq hAc hXpos hx.1 hh1'.le hh2'.le]
    rw [hcongr]
    exact vtail_mean_sq_bound hAc hXpos hh1' hh2' hh1X hh2X' hab
  -- E4.4 — S-B: the slab, `x`-uniform
  have hSB : 1 / X * (∫ x in X..(2 * X),
      ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 45 : ℝ)))
        ((Real.log X) ^ (1 / 45 : ℝ)) x‖ ^ 2) ≤ 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by
    have hs5 : (∑ m ∈ s0, 1 / (m : ℝ)) ≤ 5 := coeff_sum_inv_le (by linarith) s0 hrange
    have hs0 : (0 : ℝ) ≤ ∑ m ∈ s0, 1 / (m : ℝ) := Finset.sum_nonneg fun m _ => by positivity
    have hsq25 : (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 ≤ 25 := by nlinarith
    have hLnn : (0 : ℝ) ≤ (Real.log X) ^ (-(14 / 45 : ℝ)) := Real.rpow_nonneg hLp.le _
    have hpt : ∀ x ∈ Set.Icc X (2 * X),
        ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 45 : ℝ)))
          ((Real.log X) ^ (1 / 45 : ℝ)) x‖ ^ 2
          ≤ 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by
      intro x hx
      rw [Set.mem_Icc] at hx
      rw [vdiffR_eq hAc hXpos hx.1 hh1'.le hh2'.le, ← uSlab_eq_vSeg, ← uSlab_eq_vSeg]
      refine le_trans (uSlab_taylor_main_sq a s0 hX1 hx.1 hh1 hh12 hh2X hpos ha) ?_
      calc 16 * (∑ m ∈ s0, 1 / (m : ℝ)) ^ 2 * (Real.log X) ^ (-(14 / 45 : ℝ))
          ≤ 16 * 25 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by gcongr
        _ = 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by norm_num
    have hmono := intervalIntegral.integral_mono_on (by linarith : X ≤ 2 * X)
      (((vdiffR_continuous hAc hXpos h₁ h₂ _ _).norm).pow 2 |>.intervalIntegrable _ _)
      (_root_.intervalIntegrable_const (μ := volume)) hpt
    have heval : (∫ _x in X..(2 * X), (400 * (Real.log X) ^ (-(14 / 45 : ℝ))))
        = 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) * X := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [heval] at hmono
    calc 1 / X * (∫ x in X..(2 * X),
          ‖vdiffR (dpolyA a s0) X h₁ h₂ (-((Real.log X) ^ (1 / 45 : ℝ)))
            ((Real.log X) ^ (1 / 45 : ℝ)) x‖ ^ 2)
        ≤ 1 / X * (400 * (Real.log X) ^ (-(14 / 45 : ℝ)) * X) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 400 * (Real.log X) ^ (-(14 / 45 : ℝ)) := by field_simp
  -- E4.5 — assemble
  have hstep := five_split_integral_bound hAc hXpos hh1' hh2'
    ((Real.log X) ^ (1 / 45 : ℝ)) (X / h₁) (2 * (X / h₁))
  have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 1 / X)
  have hb1 := hSC (-(2 * (X / h₁))) (-(X / h₁)) (by linarith)
  have hb2 := hSC (-(X / h₁)) (-((Real.log X) ^ (1 / 45 : ℝ))) (by linarith)
  have hb4 := hSC ((Real.log X) ^ (1 / 45 : ℝ)) (X / h₁) hT0W
  have hb5 := hSC (X / h₁) (2 * (X / h₁)) (by linarith)
  have hfar : 820 * Real.pi * ((∫ t in (X / h₁)..(2 * (X / h₁)), ‖dpolyA a s0 t‖ ^ 2)
        + ∫ t in (-(2 * (X / h₁)))..(-(X / h₁)), ‖dpolyA a s0 t‖ ^ 2)
      ≤ 820 * Real.pi * Msup :=
    mul_le_mul_of_nonneg_left hMsupW (by positivity)
  nlinarith [hmul, hb1, hb2, hb4, hb5, hSB, hfar]

/-! ## §4 — J6: THE EXIT, at the row's bound as a free real

`lemma14_contour_of_Msup_at` + J1–J4.  The seam row's own bound enters as `R₁`/`R₂`; §5
instantiates it. -/

/-- `T₀ = (log X)^{1/45} ≤ X/h₁` — `lemma14_contour`'s E4.1 step, isolated: the annulus floor
sits below the truncation, which is what lets J1's split feed Lemma 14's segments. -/
theorem seamT0_le_div {X h₁ h₂ : ℝ} (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) : seamT0 X ≤ X / h₁ := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by rw [Real.le_log_iff_exp_le hXpos]; exact hX
  have hLp : (0 : ℝ) < Real.log X := by linarith
  have hh1' : (0 : ℝ) < h₁ := by linarith
  have hh2' : (0 : ℝ) < h₂ := by linarith
  rw [seamT0]
  have hstep1 : (Real.log X) ^ (1 / 45 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hstep2 : (Real.log X) ^ (1 / 5 : ℝ) ≤ X / h₂ := by
    rw [le_div_iff₀ hh2']
    have hL5 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hLp.le _
    calc (Real.log X) ^ (1 / 5 : ℝ) * h₂
        ≤ (Real.log X) ^ (1 / 5 : ℝ) * (X * (Real.log X) ^ (-(1 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_left hh2X hL5
      _ = X * ((Real.log X) ^ (1 / 5 : ℝ) * (Real.log X) ^ (-(1 / 5 : ℝ))) := by ring
      _ = X := by rw [← Real.rpow_add hLp]; norm_num
  have hstep3 : X / h₂ ≤ X / h₁ := by gcongr
  linarith

/-- **J6 — THE JUNCTION** (`lemma14_contour_seam_supplied`), the two-height form.  Lemma 14's
`x`-averaged mean square, with BOTH analytic terms paid by seam rows: the mid-range by the row
at `Tann = X/h₁` (J3) and `Msup` by the row at `Tann = 2X/h₁` (J4).  No `Msup` binder, no
`∀T` family, no `hrange` assumption (J2 derives it), no integral over `Ann` left on the right.

The junction's added binders are `ha` (the coefficient bound — NOT in the row's frame) and
Lemma 14's own window frame `1 ≤ h₁ ≤ h₂ ≤ X(log X)^{−1/5}`. -/
theorem lemma14_contour_seam_supplied {N : ℕ} {a : ℕ → ℂ} {X h₁ h₂ R₁ R₂ : ℝ}
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ seamS0 N X, ‖a m‖ ≤ 1) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hrow1 : (∫ t in seamAnn X (X / h₁), ‖spoly N a t‖ ^ 2) ≤ R₁)
    (hrow2 : (∫ t in seamAnn X (2 * (X / h₁)), ‖spoly N a t‖ ^ 2) ≤ R₂) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a (seamS0 N X)) x h₁ (2 * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a (seamS0 N X)) x h₂ (2 * (X / h₁))‖ ^ 2)
      ≤ 2000 * (Real.log X) ^ (-(14 / 45 : ℝ)) + 820 * Real.pi * R₁
        + 820 * Real.pi * R₂ := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX1 : (1 : ℝ) < X := by linarith
  have hT0W : seamT0 X ≤ X / h₁ := seamT0_le_div hX hh1 hh12 hh2X
  have hmid := seam_midrange_bound hX1 hsupp hT0W hrow1
  have hfar := seam_Msup hX1 hsupp hT0W hrow2
  have hmain := lemma14_contour_of_Msup_at a (seamS0 N X) hX hh1 hh12 hh2X ha
    (seamS0_range hN2) hfar
  simp only [seamT0] at hmid
  have hstep := mul_le_mul_of_nonneg_left hmid (by positivity : (0 : ℝ) ≤ 820 * Real.pi)
  linarith

/-- **J6, the single-row form** (`lemma14_contour_seam_supplied_single`).  One seam row, at
`Tann = 2X/h₁`, pays for BOTH of Lemma 14's analytic terms — the mid-range because
`Ann(T₀, X/h₁) ⊆ Ann(T₀, 2X/h₁)` (`seam_midrange_of_tall_row`).  This is the form §5
instantiates: it writes the row's sixty-binder frame down once instead of twice.  The price is
a factor `2` on the row's own bound (`1640π` vs `820π + 820π` at two different heights). -/
theorem lemma14_contour_seam_supplied_single {N : ℕ} {a : ℕ → ℂ} {X h₁ h₂ R : ℝ}
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ h₂)
    (hh2X : h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ m ∈ seamS0 N X, ‖a m‖ ≤ 1) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hrow : (∫ t in seamAnn X (2 * (X / h₁)), ‖spoly N a t‖ ^ 2) ≤ R) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a (seamS0 N X)) x h₁ (2 * (X / h₁))
          - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a (seamS0 N X)) x h₂ (2 * (X / h₁))‖ ^ 2)
      ≤ 2000 * (Real.log X) ^ (-(14 / 45 : ℝ)) + 1640 * Real.pi * R := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX1 : (1 : ℝ) < X := by linarith
  have hT0W : seamT0 X ≤ X / h₁ := seamT0_le_div hX hh1 hh12 hh2X
  have hmid := seam_midrange_of_tall_row hX1 hsupp hT0W hrow
  have hfar := seam_Msup hX1 hsupp hT0W hrow
  have hmain := lemma14_contour_of_Msup_at a (seamS0 N X) hX hh1 hh12 hh2X ha
    (seamS0_range hN2) hfar
  simp only [seamT0] at hmid
  have hstep := mul_le_mul_of_nonneg_left hmid (by positivity : (0 : ℝ) ≤ 820 * Real.pi)
  linarith

/-! ## §5 — J6 CONCRETE: `seam_row_calibrated` in Lemma 14's slot -/

/-- **The seam row's right-hand side**, as a formula (`seam_row_calibrated`'s closed bound
verbatim: the ball leg `8S²`, §8.1's level-1 term, the `1536·Cs·e³` `P₁`-term, `Σ_j
lemma12Rows`, and the `𝒰`-residue `2(Tann/X+1)(log X)^{−θ₂₉₃+ε}`).  Naming it keeps the
junction's exit readable; nothing is rounded, and `Σ_j lemma12Rows` is left UN-PRICED — the
row is a formula, not a number. -/
def seamRowRHS (Cs H1 X Tann η ε S : ℝ) (A G Jb N Xd : ℕ) (a b c : ℕ → ℂ) : ℝ :=
  8 * S ^ 2
    + (2 * (calH H1 1 * Real.log ((calQ A G 1 : ℕ) : ℝ) + 1)
          * (Tann * ((calQ A G 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
          * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
          * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
              + 60 * (calH H1 1 / mrAlpha η 1)
                  * Real.exp (4 * mrAlpha η 1 / calH H1 1))
        + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
            * (1 / ((calP A G 1 : ℕ) : ℝ))
        + ∑ j ∈ Finset.Icc 1 Jb,
            lemma12Rows N Xd (calP A G j) (calQ A G j) (calH H1 j) Tann a b c)
    + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε))

set_option maxHeartbeats 1000000 in
-- the row's sixty-binder frame is instantiated wholesale at `Tann = 2X/h₁`; unification of
-- the eleven-field `CalFrame` plus the graded ladder exceeds the default budget
/-- **J6 CONCRETE — LEMMA 14, SEAM-SUPPLIED** (`lemma14_contour_seam_supplied_calibrated`).

`lemma14_contour`'s bound with BOTH analytic terms discharged by `seam_row_calibrated` at the
single height `Tann = 2X/h₁`:

  `(1/X)∫_X^{2X} ‖(1/h₁)P₁ − (1/h₂)P₂‖² ≤ 2000(log X)^{−14/45} + 1640π·(the seam row)`.

**No `Msup`. No `∫` on the right.**  The surviving frame is exactly `seam_row_calibrated`'s
(reproduced verbatim, binder for binder) plus five junction gates:

* `Tann = 2X/h₁` — the height at which the row is read (the truncation `Tcut = 2X/h₁` is
  FORCED by `Lemma14`'s own truncation page, not chosen here);
* `2 ≤ h₁` — this is the row's OWN `Tann ≤ X` read at that height (`2X/h₁ ≤ X`), so it is
  forced rather than added; it is spelled out because the consumer must meet it;
* `h₁ ≤ h₂` and `h₂ ≤ X(log X)^{−1/5}` — `lemma14_contour`'s window frame;
* `∀ m ∈ seamS0 N X, ‖a m‖ ≤ 1` — **the one genuinely new binder**: the row bounds `g`, `c`,
  `b`, `cf` by `1` but never `a`, whose only row-side contract is Lemma 12's factorization.

The row's `hSup` binder (with its `t₁`, `S`) survives here; `seam_row_calibrated_station`
(§6) is the stone that discharges it. -/
theorem lemma14_contour_seam_supplied_calibrated :
    ∃ Cq cq T₀ Ccol X₀ Cs : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann h₁ h₂ t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        -- ⟦THE STATION FRAME⟧ the eleven scalar gates, in place of every ladder hypothesis
        CalFrame η H1 A G Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        -- MR §2's cutoff, at the calibrated ladder
        Real.log ((calQ A G Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        -- the `VJ`-family, collapsed to its worst corner
        Real.exp (mrAlpha η Jb * Real.log ((calQ A G Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQ A G Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 Ccol → 0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        -- ⟦THE `𝒯`-SIDE FRAME⟧ the dyadic length and Lemma 12's coefficient contract
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQ A G j → ¬ p ∣ m →
          a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQ A G j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        -- ⟦THE JUNCTION'S OWN GATES⟧ flagged, never silent
        Tann = 2 * (X / h₁) → 2 ≤ h₁ → h₁ ≤ h₂ →
        h₂ ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
        (∀ m ∈ seamS0 N X, ‖a m‖ ≤ 1) →
        1 / X * (∫ x in X..(2 * X),
            ‖((1 / h₁ : ℝ) : ℂ) * uSlab (dpolyA a (seamS0 N X)) x h₁ (2 * (X / h₁))
              - ((1 / h₂ : ℝ) : ℂ) * uSlab (dpolyA a (seamS0 N X)) x h₂ (2 * (X / h₁))‖ ^ 2)
          ≤ 2000 * (Real.log X) ^ (-(14 / 45 : ℝ))
            + 1640 * Real.pi
                * seamRowRHS Cs H1 X (2 * (X / h₁)) η ε S A G Jb N Xd a b c := by
  obtain ⟨Cq, cq, T₀, Ccol, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hrow⟩ := seam_row_calibrated
  refine ⟨Cq, cq, T₀, Ccol, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G Jb m₀ Ms Mt kk
    H1 X Tann h₁ h₂ t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hpret hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
    hTdef hh1 hh12 hh2X ha
  subst hTdef
  have hrowinst : (∫ t in seamAnn X (2 * (X / h₁)), ‖spoly N a t‖ ^ 2)
      ≤ seamRowRHS Cs H1 X (2 * (X / h₁)) η ε S A G Jb N Xd a b c :=
    hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G Jb m₀ Ms Mt kk
      H1 X (2 * (X / h₁)) t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
      hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
      hVJg hMs hbudget hm₀2 hm₀ hMs4
      hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hpret hcoll hR0 hRrad hRlow
      hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
      hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
  exact lemma14_contour_seam_supplied_single hXe (by linarith) hh12 hh2X ha hN2 hsupp hrowinst

/-! ## §6 — J5: the graded station in the calibrated row's `hSup` slot -/

set_option maxHeartbeats 2000000 in
-- the row's sixty-binder frame and the station's crown binder block are instantiated
-- wholesale; the double unification is far past the default budget
/-- **J5 — THE SEAM ROW ON THE STATION'S BALL LEG**
(`seam_row_calibrated_station`).  `SupStation.seam_ball_leg_station_M` (AS-2) produces the
ball centre `t₁` — the compact minimizer of the pretentious distance over the enlarged
window — together with the pointwise sup bound that IS `seam_row_calibrated`'s `hSup` binder,
at

  `S := ballSupS X (C₁·e^{−M₀/(2e)} + 4(log X)^{−1/2+1/1000})`,

with `C₁` absolute and `M₀` any lower bound for `𝔻²(·; X)` on MRT's own window `|v| ≤ X`
(`M(f;X)` is the greatest such).  Mirrors `SupStation.prop_A3_T1_row_station`, but against
the CALIBRATED row: the ball machinery is predicate-free, so the plug is a composition with
no adapter, and the station's `|t₁| ≤ X` discharges the row's `ht₁` for free.

**What is discharged**: `hSup` and `|t₁| ≤ X`, and `S` disappears from the parameter list.
**What is carried** (the two antecedents of the exit): the station's own A-10 ball cap
`hMcap` at the produced centre — the seam's case split, not an analytic socket — and the
row's `𝒰`-side pretentious gate `𝔻²(ellLin g, t₁; X) ≤ (1/16)loglog X`, which is about the
row's `g` and NOT about the station's `seamCoeff (ellLin gst) 1 t₀`; the two families are
distinct objects and no identification is claimed here.
**What is ADDED**: the station threshold `Xs₀ ≤ X`, the coefficient identification
`a n = seamCoeff (ellLin gst) 1 t₀ n` for `n > X`, the window bound `hM₀`, and AS-2's MVT
guard `Tann ≤ X/2`.  ⚠ At the junction's far height `Tann = 2X/h₁` that guard reads
`2X/h₁ ≤ X/2`, i.e. **`4 ≤ h₁`** — strictly stronger than §5's `2 ≤ h₁`.  Composing J5 with
§5's exit therefore costs `h₁ ≥ 4`; the two stones are stated separately for that reason. -/
theorem seam_row_calibrated_station {gst : ℕ → ℂ} (hgst : ∀ p : ℕ, p.Prime → ‖gst p‖ ≤ 1)
    (t₀ : ℝ) :
    ∃ C₁ Xs₀ Cq cq T₀ Ccol X₀ Cs : ℝ,
      0 ≤ C₁ ∧ 0 < Xs₀ ∧ 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann M₀ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E : ℝ),
        -- ⟦THE STATION FRAME⟧ the eleven scalar gates, in place of every ladder hypothesis
        CalFrame η H1 A G Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        -- MR §2's cutoff, at the calibrated ladder
        Real.log ((calQ A G Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        -- the `VJ`-family, collapsed to its worst corner
        Real.exp (mrAlpha η Jb * Real.log ((calQ A G Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQ A G Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        collisionGate X 25 Ccol → 0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        -- ⟦THE `𝒯`-SIDE FRAME⟧ the dyadic length and Lemma 12's coefficient contract
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQ A G j → ¬ p ∣ m →
          a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQ A G j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        -- ⟦THE STATION'S OWN FRAME⟧
        Xs₀ ≤ X → Tann ≤ X / 2 →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin gst) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ X →
          M₀ ≤ pretDistSq (seamCoeff (ellLin gst) (fun _ => 1) t₀) (costwist v) X) →
        ∃ t₁ : ℝ, |t₁| ≤ X ∧
          ((∀ x : ℝ, X ≤ x → x ≤ 2 * X →
              pretDistSq (seamCoeff (ellLin gst) (fun _ => 1) t₀) (costwist t₁) x
                ≤ (1 / 16) * Real.log (Real.log X)) →
            pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
            (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
              ≤ seamRowRHS Cs H1 X Tann η ε
                  (ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
                    + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
                  A G Jb N Xd a b c) := by
  obtain ⟨C₁, Xs₀, hC₁0, hXs₀0, Hst⟩ := seam_ball_leg_station_M hgst t₀
  obtain ⟨Cq, cq, T₀, Ccol, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, hrow⟩ := seam_row_calibrated
  refine ⟨C₁, Xs₀, Cq, cq, T₀, Ccol, X₀, Cs, hC₁0, hXs₀0, hCq, hcq, hT₀, hX₀0, hCs, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G Jb m₀ Ms Mt kk
    H1 X Tann M₀ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hNXd hcoef hwin
    hXs hTX2 hDatum hM₀
  obtain ⟨t₁, ht₁X, hexit⟩ :=
    Hst X N Tann M₀ a hXs hXN hN2 (by linarith) hTX2 hsupp hDatum hM₀
  refine ⟨t₁, ht₁X, fun hMcap hpret => ?_⟩
  exact hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E _
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁X hpret hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp (hexit hMcap) hNXd hcoef hwin

end Salt.MR
