/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The bad-set transport (Tao arXiv:1509.05422v2 §3, Lemma 3.2 combine), spine node W3-a-3a

The OUTER combine's second step (`docs/exploration/s3-a3-design.md`, node
W3-a-3a): compose the sharp product-world concentration
(`fBridge_concentration_decoupled_sharp`, W2-b′ Tao-grade exponent) with the
weak-uniformity transport (`weakUniform_spine`, Tao's Lemma 3.2 at the spine)
to bound the CONDITIONAL probability of the F-bridge deviation event, given a
fixed window pattern `x₀ = liouvilleWindow`.

Route (three landed pieces snap together):

1. **Uniform smallness → card smallness.** `fBridge_concentration_decoupled_sharp`
   gives `(uniformOn univ).real ↑(badSet) ≤ 2·exp(−E)` with the one-log exponent
   `E = δ²·log H / (2 C₀ ε²H (2/ε²+1)²)`.  The uniform measure of a `Finset` on
   `ZMod P_H` is `card / P_H` (`uniformOn_univ_real_coe`), so
   `badSet.card ≤ P_H · 2·exp(−E)`.
2. **Card → log-card gap.** Taking logs, `log(badSet.card) ≤ log P_H − E + log 2
   = log P_H − g` where `g = E − log 2` (the empty bad set is handled separately:
   its conditional mass is `0 ≤` the nonnegative bound).
3. **The transport.** `weakUniform_spine` turns that log-card gap into the
   conditional `E`-mass bound `≤ (t + log(1 + 8 P_H² ω/x) + log 2)/g`, `t` the
   per-`x₀` entropy deficiency.
-/
import Salt.Entropy.Chowla.WeakUniform
import Salt.Entropy.Chowla.Decoupled
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- **The deviation event as a `Finset`.**  For a fixed window pattern `x₀`, the
residues `ω ∈ ZMod P_H` at which the F-bridge `fBridgeF eps H x₀` deviates from
the decoupled two-point mean `∑_{p ∈ 𝒫_H} (1/p) ∑_j (x₀)_j (x₀)_{j+p}` by at least
`δ`.  Membership predicate is byte-identical to the deviation set of
`fBridge_concentration_decoupled_sharp`. -/
noncomputable def badSet (eps : ℚ) (H : ℕ) (x₀ : Fin H → ℤ) (δ : ℝ) :
    Finset (ZMod (PH eps H)) :=
  letI := Classical.dec
  Finset.univ.filter fun ω =>
    δ ≤ |fBridgeF eps H x₀ ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
      ∑ j ∈ Finset.range H,
        (windowVal H x₀ j : ℝ) * (windowVal H x₀ (j + (p : ℕ)) : ℝ)|

/-- The uniform probability of a `Finset` on the full residue space `ZMod P_H` is
`card / P_H`. -/
lemma uniformOn_univ_real_coe (eps : ℚ) (H : ℕ) (S : Finset (ZMod (PH eps H))) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real (↑S : Set (ZMod (PH eps H)))
      = (S.card : ℝ) / (PH eps H : ℝ) := by
  rw [uniformOn_real Set.finite_univ, Set.univ_inter, Nat.card_coe_set_eq,
    Set.ncard_coe_finset, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card,
    ZMod.card]

/-- **W3-a-3a, the bad-set transport** (Tao Lemma 3.2 combine, sharp exponent).
For a fixed window pattern `x₀`, the CONDITIONAL probability (given
`liouvilleWindow = x₀`) that the F-bridge deviates from the decoupled two-point
mean by at least `δ` is bounded by `(t + log(1 + 8 P_H² ω/x) + log 2)/g`, where
`t` is the per-`x₀` residue-entropy deficiency and `g ≤ E − log 2` with `E` the
sharp product-world concentration exponent
`δ²·log H / (2 C₀ ε²H (2/ε²+1)²)` (W2-b′ grade).  Composes
`fBridge_concentration_decoupled_sharp` (uniform smallness → card smallness) with
`weakUniform_spine` (card smallness → conditional-mass bound).  The nonnegativity
`ht : 0 ≤ t` handles the empty-bad-set case cleanly (see the report note). -/
theorem badSet_transport (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    {x₀ : Fin H → ℤ} (hx₀ : ∀ i, |x₀ i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ))
    {t : ℝ} (ht : 0 ≤ t)
    (hgood : H[residueWindow eps H; logMeasure x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀] ≤ t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ δ ^ 2 * Real.log (H : ℝ) /
        (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2) - Real.log 2) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
        ↑(badSet eps H x₀ δ)
      ≤ (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
          + Real.log 2) / g := by
  rcases Nat.eq_zero_or_pos (badSet eps H x₀ δ).card with h0 | hpos
  · -- Empty bad set: its conditional mass is 0, and the bound is nonnegative.
    have hempty : badSet eps H x₀ δ = ∅ := Finset.card_eq_zero.mp h0
    rw [hempty, Finset.coe_empty, measureReal_empty]
    have hcorr : (0 : ℝ) ≤ Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)) := by
      apply Real.log_nonneg
      have hpos8 : (0 : ℝ) ≤ 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ) := by positivity
      linarith
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (by linarith) hg.le
  · -- Nonempty bad set: sharp concentration → log-card gap → transport.
    have hconc0 := fBridge_concentration_decoupled_sharp eps H hx₀ heps hne hδ hC₀ hcard hlog
    set D := 2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 with hDdef
    have hset : {ω : ZMod (PH eps H) | δ ≤ |fBridgeF eps H x₀ ω -
          ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
            (windowVal H x₀ j : ℝ) * (windowVal H x₀ (j + (p : ℕ)) : ℝ)|}
        = (↑(badSet eps H x₀ δ) : Set (ZMod (PH eps H))) := by
      ext ω; simp [badSet]
    rw [hset, uniformOn_univ_real_coe] at hconc0
    have hPHpos : (0 : ℝ) < (PH eps H : ℝ) := by exact_mod_cast PH_pos eps H
    have hcardposR : (0 : ℝ) < ((badSet eps H x₀ δ).card : ℝ) := by exact_mod_cast hpos
    have hcardR : ((badSet eps H x₀ δ).card : ℝ)
        ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) / D) * (PH eps H : ℝ) :=
      (div_le_iff₀ hPHpos).mp hconc0
    have hlogcard : Real.log ((badSet eps H x₀ δ).card : ℝ)
        ≤ Real.log (PH eps H : ℝ) - g := by
      have hstep := Real.log_le_log hcardposR hcardR
      rw [Real.log_mul (mul_ne_zero two_ne_zero (Real.exp_ne_zero _)) hPHpos.ne',
        Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp] at hstep
      have hxy : -δ ^ 2 * Real.log (H : ℝ) / D = -(δ ^ 2 * Real.log (H : ℝ) / D) := by ring
      rw [hxy] at hstep
      linarith [hstep, hgle]
    exact weakUniform_spine eps H hx hω hωx hg x₀ (badSet eps H x₀ δ) hgood hlogcard

/-- **W3-a-3a at the W2-b′ calibration threshold.**  Specialising `badSet_transport`
to `δ = ε²H/log H`, the sharp exponent lower-bounds to the tower-fundable
`E ≥ ε⁶H/(18 C₀ log H)` (using `(2/ε²+1)² ≤ 9/ε⁴` for `0 < ε ≤ 1`), so the consumer
may take any `g ≤ ε⁶H/(18 C₀ log H) − log 2`.  This is the shape the outer Fubini
(W3-a-3c) meets: the deficiency budget `t` need only sit below the one-log grade
`ε⁶H/(18 C₀ log H)`, whose tower telescope `Σ 1/(n log n)` diverges. -/
theorem badSet_transport_at_calibration (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    {x₀ : Fin H → ℤ} (hx₀ : ∀ i, |x₀ i| ≤ 1) (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1)
    (hne : (primeWindow eps H).Nonempty)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ))
    {t : ℝ} (ht : 0 ≤ t)
    (hgood : H[residueWindow eps H; logMeasure x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀] ≤ t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) / (18 * C₀ * Real.log (H : ℝ)) - Real.log 2) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
        ↑(badSet eps H x₀ ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
      ≤ (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
          + Real.log 2) / g := by
  have hL : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
  have he : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases Nat.eq_zero_or_pos H with h | h
    · exfalso; rw [h, Nat.cast_zero, Real.log_zero] at hlog; linarith
    · exact_mod_cast h
  have hδ : (0 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) :=
    div_nonneg (by positivity) hL.le
  have hene : (eps : ℝ) ≠ 0 := he.ne'
  have hLne : Real.log (H : ℝ) ≠ 0 := hL.ne'
  have hCne : C₀ ≠ 0 := hC₀.ne'
  have h2e : (2 + (eps : ℝ) ^ 2) ≠ 0 := by positivity
  -- The sharp exponent at `δ = ε²H/log H` simplifies to `ε⁶H/(2 C₀ log H (2+ε²)²)`.
  have hE_eq : ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) ^ 2 * Real.log (H : ℝ) /
        (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)
      = (eps : ℝ) ^ 6 * (H : ℝ) / (2 * C₀ * Real.log (H : ℝ) * (2 + (eps : ℝ) ^ 2) ^ 2) := by
    field_simp
  -- `(2+ε²)² ≤ 9` for `0 < ε ≤ 1`, so the exponent dominates `ε⁶H/(18 C₀ log H)`.
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
  refine badSet_transport eps H hx hω hωx hx₀ heps hne hδ hC₀ hcard hlog ht hgood hg ?_
  exact hgle.trans (sub_le_sub_right hEbound (Real.log 2))

/-! ### The same deviation set at shift `h` (W-F3 wave B, node B-1)

`badSet` is the `h = 1` member of a family indexed by the offset multiplier: replace the
bridge `fBridgeF` by `fBridgeF_h` (wave A) and the decoupled two-point mean's second index
`j + p` by `j + p·h`.  Byte-identity at shift `h` is a THREE-site obligation — this
predicate, the concentration lemma's deviation set, and `outer_combine`'s own conclusion,
which spells the offset independently — and wave A fixed the target spelling
`windowVal H v (j + (p : ℕ) * h)` at `OuterCombine.lean:150`.  This definition matches it
verbatim; the other two sites are waves B-2/B-3 and B-4.

Nothing about `h` is used here: the set is a filter, and the offset only rides inside the
term being filtered on. -/

/-- **The deviation event as a `Finset`, at shift `h`.**  For a fixed window pattern `x₀`,
the residues `ω ∈ ZMod P_H` at which the shift-`h` F-bridge `fBridgeF_h eps H h x₀` deviates
from the shifted decoupled two-point mean `∑_{p ∈ 𝒫_H} (1/p) ∑_j (x₀)_j (x₀)_{j+p·h}` by at
least `δ`.  `badSet` is the `h = 1` member (`badSet_h_one`). -/
noncomputable def badSet_h (eps : ℚ) (H h : ℕ) (x₀ : Fin H → ℤ) (δ : ℝ) :
    Finset (ZMod (PH eps H)) :=
  letI := Classical.dec
  Finset.univ.filter fun ω =>
    δ ≤ |fBridgeF_h eps H h x₀ ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
      ∑ j ∈ Finset.range H,
        (windowVal H x₀ j : ℝ) * (windowVal H x₀ (j + (p : ℕ) * h) : ℝ)|

/-- **The `h = 1` compat.**  NOT `rfl`-grade, and it fails on BOTH of its two sites: the
bridge needs `fBridgeF_h_one`, and the mean's window index needs `Nat.mul_one`, because
`(p : ℕ) * 1` is stuck for a variable `p` (`Nat.mul` recurses on its second argument).
Measured: `rfl` reports the two sides not definitionally equal, dropping `Nat.mul_one` from
the rewrite leaves `j + ↑p * 1` against `j + ↑p`, and dropping `fBridgeF_h_one` leaves
`fBridgeF_h eps H 1` against `fBridgeF`. -/
theorem badSet_h_one (eps : ℚ) (H : ℕ) (x₀ : Fin H → ℤ) (δ : ℝ) :
    badSet_h eps H 1 x₀ δ = badSet eps H x₀ δ := by
  classical
  ext ω
  simp only [badSet_h, badSet, Finset.mem_filter, Finset.mem_univ, true_and,
    fBridgeF_h_one, Nat.mul_one]

/-! ### The transport at shift `h` (W-F3 wave B, node B-4)

The `h`-ports of `badSet_transport` and `badSet_transport_at_calibration`.  Neither theorem
reads the offset directly: both are statements about `badSet_h` (B-1) composed with
`fBridge_h_concentration_decoupled_sharp` (B-2/B-3, site 2) and the offset-blind
`weakUniform_spine`.  Because the offset is sealed inside `badSet_h`, the exponent, the
`(2+ε²)² ≤ 9` calibration step and every arithmetic bound transfer character-for-character:
the shift costs NOTHING in the transport, exactly as it cost nothing in the concentration
grade.  `uniformOn_univ_real_coe` and `weakUniform_spine` are `h`-free and REUSED VERBATIM.

THE `h = 1` RECOVERY IS A THIRD SHAPE: ONE REWRITE.  B-1 needed `fBridgeF_h_one` +
`Nat.mul_one`; B-2/B-3 needed either that pair or `fBridgeF_h_one` + `fBridgeG_h_one`.  Here
the statement mentions NEITHER the bridge nor the product index in the clear — both are sealed
behind `badSet_h` — so the whole recovery is the single rewrite `badSet_h_one`, B-1's compat
EQUATION doing the work of two.  Measured with negative controls, not assumed: `rfl` reports
the two sides not definitionally equal, and with no rewrite the residual goal is
`badSet_h eps H 1 x₀ δ` against `badSet eps H x₀ δ` (a single site, not two). -/

/-- **W3-a-3a at shift `h`** — the `h`-port of `badSet_transport`.  For a fixed window pattern
`x₀`, the CONDITIONAL probability that the shift-`h` F-bridge deviates from the SHIFTED
decoupled two-point mean by at least `δ` obeys the same
`(t + log(1 + 8 P_H² ω/x) + log 2)/g` bound, with the same sharp exponent
`δ²·log H / (2 C₀ ε²H (2/ε²+1)²)`: the offset never enters the estimate.  Composes
`fBridge_h_concentration_decoupled_sharp` (site 2) with the offset-blind `weakUniform_spine`.
`badSet_transport` is the `h = 1` member (recovered by `badSet_h_one` alone). -/
theorem badSet_transport_h (eps : ℚ) (H h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    {x₀ : Fin H → ℤ} (hx₀ : ∀ i, |x₀ i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ))
    {t : ℝ} (ht : 0 ≤ t)
    (hgood : H[residueWindow eps H; logMeasure x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀] ≤ t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ δ ^ 2 * Real.log (H : ℝ) /
        (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2) - Real.log 2) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
        ↑(badSet_h eps H h x₀ δ)
      ≤ (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
          + Real.log 2) / g := by
  rcases Nat.eq_zero_or_pos (badSet_h eps H h x₀ δ).card with h0 | hpos
  · -- Empty bad set: its conditional mass is 0, and the bound is nonnegative.
    have hempty : badSet_h eps H h x₀ δ = ∅ := Finset.card_eq_zero.mp h0
    rw [hempty, Finset.coe_empty, measureReal_empty]
    have hcorr : (0 : ℝ) ≤ Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)) := by
      apply Real.log_nonneg
      have hpos8 : (0 : ℝ) ≤ 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ) := by positivity
      linarith
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (by linarith) hg.le
  · -- Nonempty bad set: sharp concentration → log-card gap → transport.
    have hconc0 := fBridge_h_concentration_decoupled_sharp eps H h hx₀ heps hne hδ hC₀ hcard hlog
    set D := 2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 with hDdef
    have hset : {ω : ZMod (PH eps H) | δ ≤ |fBridgeF_h eps H h x₀ ω -
          ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
            (windowVal H x₀ j : ℝ) * (windowVal H x₀ (j + (p : ℕ) * h) : ℝ)|}
        = (↑(badSet_h eps H h x₀ δ) : Set (ZMod (PH eps H))) := by
      ext ω; simp [badSet_h]
    rw [hset, uniformOn_univ_real_coe] at hconc0
    have hPHpos : (0 : ℝ) < (PH eps H : ℝ) := by exact_mod_cast PH_pos eps H
    have hcardposR : (0 : ℝ) < ((badSet_h eps H h x₀ δ).card : ℝ) := by exact_mod_cast hpos
    have hcardR : ((badSet_h eps H h x₀ δ).card : ℝ)
        ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) / D) * (PH eps H : ℝ) :=
      (div_le_iff₀ hPHpos).mp hconc0
    have hlogcard : Real.log ((badSet_h eps H h x₀ δ).card : ℝ)
        ≤ Real.log (PH eps H : ℝ) - g := by
      have hstep := Real.log_le_log hcardposR hcardR
      rw [Real.log_mul (mul_ne_zero two_ne_zero (Real.exp_ne_zero _)) hPHpos.ne',
        Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp] at hstep
      have hxy : -δ ^ 2 * Real.log (H : ℝ) / D = -(δ ^ 2 * Real.log (H : ℝ) / D) := by ring
      rw [hxy] at hstep
      linarith [hstep, hgle]
    exact weakUniform_spine eps H hx hω hωx hg x₀ (badSet_h eps H h x₀ δ) hgood hlogcard

/-- **W3-a-3a at shift `h`, at the W2-b′ calibration threshold** — the `h`-port of
`badSet_transport_at_calibration`.  Specialising `badSet_transport_h` to `δ = ε²H/log H`; the
exponent lower bound `E ≥ ε⁶H/(18 C₀ log H)` and its `(2/ε²+1)² ≤ 9/ε⁴` step are
character-for-character the `h = 1` ones, because the offset is sealed inside `badSet_h` and
never reaches the arithmetic.  This is the shape the shifted outer Fubini (`outer_combine_h`)
meets. -/
theorem badSet_transport_at_calibration_h (eps : ℚ) (H h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    {x₀ : Fin H → ℤ} (hx₀ : ∀ i, |x₀ i| ≤ 1) (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1)
    (hne : (primeWindow eps H).Nonempty)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ))
    {t : ℝ} (ht : 0 ≤ t)
    (hgood : H[residueWindow eps H; logMeasure x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀] ≤ t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) / (18 * C₀ * Real.log (H : ℝ)) - Real.log 2) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
        ↑(badSet_h eps H h x₀ ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
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
  -- The sharp exponent at `δ = ε²H/log H` simplifies to `ε⁶H/(2 C₀ log H (2+ε²)²)`.
  have hE_eq : ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) ^ 2 * Real.log (H : ℝ) /
        (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)
      = (eps : ℝ) ^ 6 * (H : ℝ) / (2 * C₀ * Real.log (H : ℝ) * (2 + (eps : ℝ) ^ 2) ^ 2) := by
    field_simp
  -- `(2+ε²)² ≤ 9` for `0 < ε ≤ 1`, so the exponent dominates `ε⁶H/(18 C₀ log H)`.
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
  refine badSet_transport_h eps H h hx hω hωx hx₀ heps hne hδ hC₀ hcard hlog ht hgood hg ?_
  exact hgle.trans (sub_le_sub_right hEbound (Real.log 2))

end Salt.Entropy.Chowla
