/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The bad-set transport (Tao 1509.05422 §3, Lemma 3.2 combine), spine node W3-a-3a

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

end Salt.Entropy.Chowla
