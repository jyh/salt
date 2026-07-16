/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Surv

/-!
# G-BANDCLOSE — the A₃ band close: the y-floor vanish + the high-pass ratios

The compositional layer that discharges the `hwide` residual left open by `Surv.lean` (its flagged
item 2).  The route is the y-floor: BOTH band carriers cap the large prime `p₂` from above by the
PIECE scale (`blockAlphaLow`: `p₂ ≤ pieceN k'`; `blockAlphaSym`: `p₂ ≤ pieceM k'`), while the same
carriers demand `p₂ > opY N` (low) resp. `p₂ > max(opY N, pieceN k')` (sym).  So on a piece whose
cap sits at or below `opY N` the carrier is IDENTICALLY zero — the survivor sum vanishes.  This
gives the `kp`-floor `2^{k'} > opY N` for every NON-vanishing survivor, without any liveness gate.

This file lands (the `(A)+(B)` split, `BandClose.lean`):

* **(A) the y-floor vanish** — `gold_band_low_vanish` / `gold_band_sym_vanish` (the survivor sum is
  `0` when the piece cap is `≤ opY N`), plus the `kp`-floor corollaries
  `gold_band_low_kp_floor` / `gold_band_sym_kp_floor` (`opY N < 2^{k'}`-shaped on every
  non-vanishing survivor).  The mechanism: the carrier vanishes identically
  (`blockAlphaLow_eq_zero_of_cap_le` / `blockAlphaSym_eq_zero_of_cap_le`), so
  `apDiscBilinCutoff_eq_zero_of_alpha` collapses the price to `0`.
* **(B) the high-pass ratios** — `gold_band_hratio` / `gold_band_hNXM`: the `hratio`/`hNXM`
  hypotheses of `gold_band_survsum_geoN` at the floored `kp`, via the boundary corner
  `2^i·(Ne+1) ≤ goldCut N (k+1) ≤ N/2` and the `kp`-floor (the `(10/31)` ratio WITHOUT liveness).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 0. The zero-collapse plumbing -/

/-- **A `restrictAlpha` of an identically-zero coefficient is identically zero.** -/
private theorem restrictAlpha_eq_zero_of_alpha {α : ℕ → ℂ} (h : ∀ m, α m = 0) (a b m : ℕ) :
    restrictAlpha α a b m = 0 := by
  unfold restrictAlpha
  split_ifs
  · exact h m
  · rfl

/-- **`apDiscBilinCutoff` of an identically-zero `α` vanishes.**  Both guarded counts multiply by
`α m`, so an identically-zero coefficient collapses the cutoff carrier to `0` — via
`apDiscBilinCutoff_congr` to the zero coefficient, then `apDiscBilinCutoff_zero`. -/
private theorem apDiscBilinCutoff_eq_zero_of_alpha {α β : ℕ → ℂ} {X Y N₀ d T : ℕ}
    (hα : ∀ m, α m = 0) : apDiscBilinCutoff α β X Y N₀ d T = 0 := by
  rw [apDiscBilinCutoff_congr (α' := fun _ => (0 : ℂ)) (fun m _ => hα m)]
  exact apDiscBilinCutoff_zero β X Y N₀ d T

/-! ## 1. The carrier y-floor vanish (deliverable A)

Both band carriers pin the large prime `p₂` between a lower `opY N`-scale threshold and an upper
PIECE-scale cap.  When the cap collapses to (or below) the threshold the support is empty. -/

/-- **`blockAlphaLow` vanishes below its `p₂`-cap threshold.**  The support demands `y < p₂ ≤ N`,
so `y < N`; if the cap `N ≤ y` the semiprime set is empty and the coefficient is `0`. -/
theorem blockAlphaLow_eq_zero_of_cap_le {z y : ℕ} {ε₀ : ℝ} {j N : ℕ} (h : N ≤ y) (m : ℕ) :
    blockAlphaLow z y ε₀ j N m = 0 := by
  unfold blockAlphaLow
  rw [if_neg]
  rintro ⟨_p₁, _p₂, _, _, _, _, hyp2, hp2N, _, _⟩
  omega

/-- **`blockAlphaSym` vanishes below its `p₂`-cap threshold.**  The support demands
`max y N < p₂ ≤ M`, so `max y N < M`; if the cap `M ≤ max y N` the semiprime set is empty. -/
theorem blockAlphaSym_eq_zero_of_cap_le {z y : ℕ} {ε₀ : ℝ} {j N M : ℕ} (h : M ≤ max y N) (m : ℕ) :
    blockAlphaSym z y ε₀ j N M m = 0 := by
  unfold blockAlphaSym
  rw [if_neg]
  rintro ⟨_p₁, _p₂, _, _, _, _, hmaxp2, hp2M, _, _⟩
  omega

/-- **`gold_band_low_vanish` (deliverable A, low leg).**  On a piece `k'` whose large-prime cap
`pieceN k'` sits at or below `opY N`, the low-band survivor price is identically `0`: the carrier
`blockAlphaLow (opZ N) (opY N) ε₀ j (pieceN k')` vanishes, so both cutoff carriers do. -/
theorem gold_band_low_vanish (N Q a Ps : ℕ) (ε₀ : ℝ) (bound : ℝ) (j k' k i : ℕ)
    (hfloor : pieceN k' ≤ opY N) :
    goldLowSurvSum N Q a Ps ε₀ bound j k' k i = 0 := by
  have hz : ∀ m, goldLowSub N ε₀ j k' i m = 0 := by
    intro m
    unfold goldLowSub
    exact restrictAlpha_eq_zero_of_alpha
      (fun m' => restrictAlpha_eq_zero_of_alpha
        (fun m'' => blockAlphaLow_eq_zero_of_cap_le hfloor m'') _ _ m') _ _ m
  unfold goldLowSurvSum
  simp only [apDiscBilinCutoff_eq_zero_of_alpha hz, norm_zero, Finset.sum_const_zero, add_zero]

/-- **`gold_band_sym_vanish` (deliverable A, sym leg).**  On a piece `k'` whose large-prime cap
`pieceM k'` sits at or below `opY N`, the sym-band survivor price is identically `0`: the carrier
`blockAlphaSym (opZ N) (opY N) ε₀ j (pieceN k') (pieceM k')` vanishes (`pieceM k' ≤ opY N ≤
max (opY N) (pieceN k')`), so both cutoff carriers do.  This is the `max`-indicator vanish of the
house design, routed through the coefficient's `p₂`-cap. -/
theorem gold_band_sym_vanish (N Q a Ps : ℕ) (ε₀ : ℝ) (bound : ℝ) (j k' k i : ℕ)
    (hfloor : pieceM k' ≤ opY N) :
    goldSymSurvSum N Q a Ps ε₀ bound j k' k i = 0 := by
  have hcap : pieceM k' ≤ max (opY N) (pieceN k') := le_trans hfloor (le_max_left _ _)
  have hz : ∀ m, goldSymSub N ε₀ j k' i m = 0 := by
    intro m
    unfold goldSymSub
    exact restrictAlpha_eq_zero_of_alpha
      (fun m' => blockAlphaSym_eq_zero_of_cap_le hcap m') _ _ m
  unfold goldSymSurvSum
  simp only [apDiscBilinCutoff_eq_zero_of_alpha hz, norm_zero, Finset.sum_const_zero, add_zero]

/-- **`gold_band_low_kp_floor` (the low `kp`-floor).**  A non-vanishing low survivor forces
`opY N < pieceN k'` — i.e. `opY N < 2^{k'} − 1`, the `kp`-floor `2^{k'} > opY N + 1` that the
high-pass ratio consumes. -/
theorem gold_band_low_kp_floor {N Q a Ps : ℕ} {ε₀ : ℝ} {bound : ℝ} {j k' k i : ℕ}
    (h : goldLowSurvSum N Q a Ps ε₀ bound j k' k i ≠ 0) :
    opY N < pieceN k' := by
  by_contra hc
  exact h (gold_band_low_vanish N Q a Ps ε₀ bound j k' k i (Nat.le_of_not_lt hc))

/-- **`gold_band_sym_kp_floor` (the sym `kp`-floor).**  A non-vanishing sym survivor forces
`opY N < pieceM k'` — i.e. `opY N < 2^{k'+1} − 1`. -/
theorem gold_band_sym_kp_floor {N Q a Ps : ℕ} {ε₀ : ℝ} {bound : ℝ} {j k' k i : ℕ}
    (h : goldSymSurvSum N Q a Ps ε₀ bound j k' k i ≠ 0) :
    opY N < pieceM k' := by
  by_contra hc
  exact h (gold_band_sym_vanish N Q a Ps ε₀ bound j k' k i (Nat.le_of_not_lt hc))

/-! ## 2. The high-pass ratios at the floored `kp` (deliverable B)

The floored survivor satisfies the boundary corner `2^i·2^{k'} ≤ goldCut N (ka+1) ≤ N/2` AND the
`kp`-floor `opY N < 2^{k'}`.  In `log₂`-scale (`T := log N / log 2`): `i + kp + 1 ≤ T` (corner) and
`kp ≥ T/3 − 1` (floor, via `log(opY N) ≥ log N/3 − log 2`), and `T ≥ 2·10⁹` (`gold_op_scales`).
These force `21·kp ≥ 10·i + 20` — the `(10/31)` ratio, WITHOUT the liveness gate. -/

/-- **The `hratio` linear core.**  Scaled by `w = log 2 > 0`: from the corner `(ii+kk+1)·w ≤ l`, the
floor `l/3 − w ≤ kk·w`, and `l ≥ 2·10⁹`, the `(10/31)` ratio holds (`123·w ≤ l` suffices, and
`123 ≤ 2·10⁹`). -/
private lemma band_ratio_core {ii kk l w : ℝ} (hw1 : w ≤ 1)
    (h3 : (ii + kk + 1) * w ≤ l) (h4 : l / 3 - w ≤ kk * w)
    (hl : (2 * 10 ^ 9 : ℝ) ≤ l) :
    (10 / 31 : ℝ) * ((ii + kk + 2) * w) ≤ kk * w := by
  have hlw : (123 : ℝ) * w ≤ l := by nlinarith [hl, hw1]
  nlinarith [h3, h4, hlw]

/-- **`gold_band_geoN_inputs` (deliverable B).**  The three `gold_band_survsum_geoN` analytic inputs
— `hL1` (`1 ≤ log(X·M)`), `hratio` (the `(10/31)` high-pass ratio), and `hNXM`
(`log N ≤ 4·log(X·M)`) — hold on EVERY dyadic-boundary survivor of a floored piece
(`opY N < pieceN kp`), past a tower
threshold.  No liveness gate: the `kp`-floor (from the y-floor vanish) replaces it. -/
theorem gold_band_geoN_inputs : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ (kp ka i K : ℕ),
    i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (opZ N * opY N) K →
    opY N < pieceN kp →
    (1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)))
    ∧ ((10 / 31 : ℝ) * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))
        ≤ Real.log ((2 ^ kp : ℕ) : ℝ))
    ∧ (Real.log N ≤ 4 * Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ))) := by
  obtain ⟨xs, hs⟩ := gold_op_scales
  refine ⟨xs, fun N hN kp ka i K hi hfloor => ?_⟩
  obtain ⟨hN2, _hZ1, hy6, _, _, hlogY_ge, hlogN, _, _, _, _, _, _⟩ := hs N hN
  set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) with hLdef
  -- log-2 scale
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  -- the boundary corner `2^i·(pieceN kp + 1) ≤ goldCut N (ka+1)`
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨_, hcorner, _, _⟩ := hi
  -- Nat size facts
  have h2kp1 : (1 : ℕ) ≤ 2 ^ kp := Nat.one_le_pow _ _ (by norm_num)
  have hpc : pieceN kp + 1 = 2 ^ kp := by unfold pieceN; omega
  have hpNM : pieceN kp ≤ pieceM kp := by
    have : (2 : ℕ) ^ (kp + 1) = 2 * 2 ^ kp := by rw [pow_succ]; ring
    unfold pieceN pieceM; omega
  have hX1 : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
    have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hM1 : (1 : ℕ) ≤ pieceM kp := by
    have : (2 : ℕ) ≤ 2 ^ (kp + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (kp + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold pieceM; omega
  have hXR1 : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1
  have hMR1 : (1 : ℝ) ≤ (pieceM kp : ℝ) := by exact_mod_cast hM1
  have hprodpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by nlinarith
  have hoypos : (0 : ℝ) < (opY N : ℝ) := by exact_mod_cast (by omega : 0 < opY N)
  -- (h3) the real corner `(i + kp + 1)·log 2 ≤ log N`
  have hcornerR : (2 : ℝ) ^ i * (2 : ℝ) ^ kp ≤ (N : ℝ) / 2 := by
    have hc1 : 2 ^ i * 2 ^ kp ≤ goldCut N (ka + 1) := by rw [← hpc]; exact hcorner
    have hc2 : 2 ^ i * 2 ^ kp ≤ N / 2 := le_trans hc1 (goldCut_le_half N (ka + 1))
    calc (2 : ℝ) ^ i * (2 : ℝ) ^ kp = ((2 ^ i * 2 ^ kp : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hc2
      _ ≤ (N : ℝ) / 2 := Nat.cast_div_le
  have h3 : ((i : ℝ) + (kp : ℝ) + 1) * Real.log 2 ≤ Real.log N := by
    have hle := Real.log_le_log (by positivity) hcornerR
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div hNne (by norm_num)] at hle
    nlinarith [hle]
  -- (h4) the floor `log N/3 − log 2 ≤ kp·log 2`
  have hoy : (opY N : ℝ) ≤ (2 : ℝ) ^ kp := by
    have hlt : opY N < 2 ^ kp := by unfold pieceN at hfloor; omega
    calc (opY N : ℝ) ≤ ((2 ^ kp : ℕ) : ℝ) := by exact_mod_cast hlt.le
      _ = (2 : ℝ) ^ kp := by push_cast; ring
  have hlogoy : Real.log (opY N : ℝ) ≤ (kp : ℝ) * Real.log 2 := by
    have := Real.log_le_log hoypos hoy
    rwa [Real.log_pow] at this
  have h4 : Real.log N / 3 - Real.log 2 ≤ (kp : ℝ) * Real.log 2 := le_trans hlogY_ge hlogoy
  have hcore := band_ratio_core hlog2le1 h3 h4 hlogN
  have hMpos : (0 : ℝ) < (pieceM kp : ℝ) := by linarith [hMR1]
  -- L's upper bound `L ≤ (i + kp + 2)·log 2`
  have hprod_ub : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)
      ≤ (2 : ℝ) ^ (i + kp + 2) := by
    have hXub : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
      calc ((2 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le _ _
        _ = (2 : ℝ) ^ (i + 1) := by push_cast; ring
    have hMub : (pieceM kp : ℝ) ≤ (2 : ℝ) ^ (kp + 1) := by
      unfold pieceM
      calc ((2 ^ (kp + 1) - 1 : ℕ) : ℝ) ≤ ((2 ^ (kp + 1) : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le _ _
        _ = (2 : ℝ) ^ (kp + 1) := by push_cast; ring
    calc ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)
        ≤ (2 : ℝ) ^ (i + 1) * (2 : ℝ) ^ (kp + 1) :=
          mul_le_mul hXub hMub (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (i + kp + 2) := by ring
  have hLub : L ≤ ((i : ℝ) + (kp : ℝ) + 2) * Real.log 2 := by
    rw [hLdef]
    have hmono := Real.log_le_log hprodpos hprod_ub
    rw [Real.log_pow] at hmono
    push_cast at hmono; nlinarith [hmono]
  -- L's lower bound `log N/3 − log 2 ≤ L`
  have hLlb : Real.log N / 3 - Real.log 2 ≤ L := by
    rw [hLdef]
    have hoyM : (opY N : ℝ) ≤ (pieceM kp : ℝ) := by
      have : opY N < pieceM kp := lt_of_lt_of_le hfloor hpNM
      exact_mod_cast this.le
    have hMprod : (pieceM kp : ℝ)
        ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ) := by nlinarith
    have hchain : Real.log (opY N : ℝ)
        ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM kp : ℝ)) :=
      le_trans (Real.log_le_log hoypos hoyM) (Real.log_le_log hMpos hMprod)
    linarith [hlogY_ge, hchain]
  refine ⟨?_, ?_, ?_⟩
  · -- hL1
    linarith [hLlb, hlogN, hlog2le1]
  · -- hratio
    have hRHS : Real.log ((2 ^ kp : ℕ) : ℝ) = (kp : ℝ) * Real.log 2 := by
      rw [show ((2 ^ kp : ℕ) : ℝ) = (2 : ℝ) ^ kp by push_cast; ring, Real.log_pow]
    rw [hRHS]
    have step1 : (10 / 31 : ℝ) * L ≤ (10 / 31 : ℝ) * (((i : ℝ) + (kp : ℝ) + 2) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hLub (by norm_num)
    exact le_trans step1 hcore
  · -- hNXM
    linarith [hLlb, hlogN, hlog2le1]

/-- **`gold_band_survsum_geoN_floored` (deliverable B, the composition — item 2 ratio route).**
Given the WIDE box price `hbox` (`P ≤ boxPriceKerr Kc kp i`) and the y-floor `opY N < pieceN kp`
(from a NON-vanishing survivor), the survivor price lands at the outer geo grade
`(4^{12}·gboxConst)·Kc·goldCut N (ka+1)/(log N)^{12}` — the `hgeoLow` grade the terminal consumes —
WITHOUT any liveness gate.  This is exactly Surv's flagged item-2 obstruction, discharged by the
y-floor. -/
theorem gold_band_survsum_geoN_floored : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∀ (kp ka i K : ℕ) (Kc P : ℝ), 1 ≤ Kc →
    i ∈ dyadicBoundary (pieceN kp) (pieceM kp)
      (goldCut N ka) (goldCut N (ka + 1)) (opZ N * opY N) K →
    opY N < pieceN kp → P ≤ boxPriceKerr Kc kp i →
    P ≤ ((4 : ℝ) ^ 12 * gboxConst) * Kc * (goldCut N (ka + 1) : ℝ) / (Real.log N) ^ 12 := by
  obtain ⟨xin, hin⟩ := gold_band_geoN_inputs
  obtain ⟨xs, hs⟩ := gold_op_scales
  refine ⟨max xin xs, fun N hN kp ka i K Kc P hKc hi hfloor hbox => ?_⟩
  have hNin : xin ≤ N := le_trans (le_max_left _ _) hN
  have hNs : xs ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨_, _, _, _, _, _, hlogN, _, _, _, _, _, _⟩ := hs N hNs
  obtain ⟨hL1, hratio, hNXM⟩ := hin N hNin kp ka i K hi hfloor
  have hlogN0 : 0 < Real.log N := by linarith [hlogN]
  exact gold_band_survsum_geoN hKc hi hL1 hratio hlogN0 (by norm_num : (1 : ℝ) ≤ 4) hNXM hbox

end Salt.Goldbach
