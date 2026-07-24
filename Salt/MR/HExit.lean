/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszIdentity
import Salt.MR.RampSliver
import Salt.MR.ShortIntervalPsi
import Salt.MR.HalaszHead

/-!
# H-EXIT (unconditional) — the ramp-sliver bridge (`HExit`)

The campaign-closing stone of the H-5 v5 wave.  `HalaszIdentity.prop21_unconditional`
carries a single hypothesis `hsliver : ‖rampTerm g_{t₀} X h y η‖ ≤ E_ramp` — the ramp
residue of the window un-truncation, defined (`HalaszIdentity.rampTerm`) as the
`2•∫∫` of the hat-smoothed coefficient difference `alignedCoeffFull − alignedCoeff`.

This module discharges `hsliver` and lands **`prop21_unconditional_final`**, the S1′
representation with NO conditional hypotheses.  The bridge (`ramp_norm_le_sliverMass`)
is the ⟦R⟧ block of the design (`docs/exploration/h5-v5-design.md`, stone V5-5): the
joint-squeeze support reduction of the four-factor coefficient difference to the
two-index `rampSliverMass`, priced unconditionally by `rampSliverMass_bound_unconditional`
(the Selberg-sieve short-interval Chebyshev GRAIN, `ShortIntervalPsi`).

## The bridge, in one line

`‖rampTerm g X h y η‖ ≤ 8 · rampSliverMass g X h y` (the constant chain: the leading
`2•`, the `∫∫` over `[0,η]²` bounded by `η² ≤ 1`, the `hatK ≤ 1` and shift-decay
`n^{-α}, n^{-α-2β} ≤ 1` factors dropped, the per-`N` difference collapsed by the joint
squeeze to `2·rampSliverMass` twice — once per squeeze leg).  The reduction, per `N` on
the hat support `N ≤ X+h`:

* **Spectator collapse** (`ramp_spectator_collapse`): the smooth `𝒮` and large `𝓛`
  legs (`= W`) act as the identity on the difference, because the difference is
  supported on `j > X` (`window_pair_untrunc`) and `w · j ≤ X+h < 2X` forces the
  spectator index `w = 1` (`W 1 = 1`).  So `D(N) = D₂(N)`, the pure window-pair
  difference `(Λ_ℓ⍟Λ_ℓ − winCoeff⍟winCoeff)(N)`.
* **Squeeze support** (`sliver_termwise_le` + `refold`): a nonzero window-pair
  difference at `k·l ∈ (X, X+h]` forces `k` or `l` into the squeeze
  `(⌊y⌋, ⌊y+y·h/X⌋]`; its partner then lands in `(⌊X/·⌋, ⌊(X+h)/·⌋]` — exactly the
  `rampSliverMass` index structure.

Provenance chain: P21-2X → P21-3K (`prop21RHS_hat_rep_aligned`) → V5-0 (seam
un-windowing) → the v5 collapse (`aligned_collapse_assembled`) → this stone.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open ArithmeticFunction
open scoped BigOperators LSeries.notation

/-! ## Convolution bookkeeping -/

/-- Reassociate/commute a four-fold Dirichlet convolution so the middle pair
`(b, c)` is convolved first and the outer pair `(a, d)` second.  Pure
`conv_assoc`/`conv_comm`. -/
lemma conv_rearrange2 (a b c d : ℕ → ℂ) :
    ((a ⍟ b) ⍟ c) ⍟ d = (b ⍟ c) ⍟ (a ⍟ d) := by
  rw [conv_assoc a b c, conv_assoc a (b ⍟ c) d, conv_comm a ((b ⍟ c) ⍟ d),
    conv_assoc (b ⍟ c) d a, conv_comm d a]

/-- **The aligned coefficient, spectator-factored.**  `alignedCoeff` with the two
window legs `(Pw ⍟ Qw)` pulled to the front and the smooth/large spectators
`W = 𝒮 ⍟ E` behind. -/
lemma alignedCoeff_eq_conv (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) :
    alignedCoeff y g X α β
      = (shiftCoeff (-(α : ℂ)) (winCoeff g X y)
          ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y))
        ⍟ (ellLin (restrictBelow y g)
          ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (ellLin (restrictAbove y g))) := by
  rw [alignedCoeff, conv_rearrange2]

/-- **The un-truncated aligned coefficient, spectator-factored.**  Same as
`alignedCoeff_eq_conv` with the window legs promoted to the full log-derivative
`lambdaLin (restrictAbove)`. -/
lemma alignedCoeffFull_eq_conv (y : ℝ) (g : ℕ → ℂ) (α β : ℝ) :
    alignedCoeffFull y g α β
      = (shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g))
          ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g)))
        ⍟ (ellLin (restrictBelow y g)
          ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (ellLin (restrictAbove y g))) := by
  rw [alignedCoeffFull, conv_rearrange2]

/-! ## Small norm / support facts -/

/-- The window coefficient is norm-dominated by the full log-derivative coefficient. -/
lemma norm_winCoeff_le (g : ℕ → ℂ) (X y : ℝ) (n : ℕ) :
    ‖winCoeff g X y n‖ ≤ ‖lambdaLin (restrictAbove y g) n‖ := by
  unfold winCoeff
  split_ifs with h
  · exact le_refl _
  · simp

/-- **The defect fact.**  If the full log-derivative coefficient is nonzero at `k`
but the window coefficient vanishes there (a "defect" leg), then `k ≥ X/y`, i.e.
`X ≤ k·y`. -/
lemma winCoeff_zero_defect (g : ℕ → ℂ) {X y : ℝ} (hy : 0 < y) {k : ℕ}
    (hkΛ : lambdaLin (restrictAbove y g) k ≠ 0) (hkw : winCoeff g X y k = 0) :
    X ≤ (k : ℝ) * y := by
  have hky : y < (k : ℝ) := lambdaLin_restrictAbove_gt hkΛ
  have hklo : ⌊y⌋₊ < k := by
    have hfloor : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy.le
    exact_mod_cast lt_of_le_of_lt hfloor hky
  -- `k` is not in the window, so `k ≥ ⌈X/y⌉`
  have hnotmem : k ∉ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ := by
    intro hmem
    rw [winCoeff, if_pos hmem] at hkw
    exact hkΛ hkw
  have hkhi : ⌈X / y⌉₊ ≤ k := by
    rw [Finset.mem_Ioo, not_and, not_lt] at hnotmem
    exact hnotmem hklo
  have hceil : X / y ≤ (k : ℝ) := le_trans (Nat.le_ceil (X / y)) (by exact_mod_cast hkhi)
  rw [div_le_iff₀ hy] at hceil
  exact hceil

/-! ## The spectator collapse -/

/-- **Generic spectator collapse.**  If `D₂` is supported on `j > X` and `W 1 = 1`,
then on the hat support `N ≤ X+h` (with `h ≤ X`, so `w · j ≤ X+h < 2X` forces the
spectator index `w = 1`) the convolution `D₂ ⍟ W` reduces to `D₂` itself. -/
lemma conv_spectator_collapse {D2 W : ℕ → ℂ} {X h : ℝ} (hhX : h ≤ X) (hX0 : 0 ≤ X)
    (hW1 : W 1 = 1) (hD2supp : ∀ j : ℕ, (j : ℝ) ≤ X → D2 j = 0)
    {N : ℕ} (hN : (N : ℝ) ≤ X + h) :
    (D2 ⍟ W) N = D2 N := by
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [LSeries.convolution_map_zero]
    exact (hD2supp 0 (by exact_mod_cast hX0)).symm
  · have hmem : ((N, 1) : ℕ × ℕ) ∈ N.divisorsAntidiagonal := by
      rw [Nat.mem_divisorsAntidiagonal]; exact ⟨mul_one N, hNpos.ne'⟩
    have hzero : ∀ p ∈ N.divisorsAntidiagonal, p ≠ ((N, 1) : ℕ × ℕ) →
        D2 p.1 * W p.2 = 0 := by
      intro p hp hpne
      obtain ⟨j, w⟩ := p
      rw [Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨hprod, _⟩ := hp
      have hw2 : 2 ≤ w := by
        rcases Nat.lt_or_ge w 2 with hlt | hge
        · exfalso
          interval_cases w
          · simp only [Nat.mul_zero] at hprod; omega
          · rw [Nat.mul_one] at hprod
            exact hpne (by rw [Prod.mk.injEq]; exact ⟨hprod, rfl⟩)
        · exact hge
      have hjhalf : 2 * j ≤ N := by
        calc 2 * j ≤ w * j := Nat.mul_le_mul hw2 (le_refl j)
          _ = N := by rw [Nat.mul_comm w j]; exact hprod
      have hjX : (j : ℝ) ≤ X := by
        have h1 : (2 : ℝ) * (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjhalf
        linarith [hN, hhX]
      simp only [hD2supp j hjX, zero_mul]
    have hconv : (D2 ⍟ W) N = ∑ p ∈ N.divisorsAntidiagonal, D2 p.1 * W p.2 := by
      rw [LSeries.convolution_def]
    rw [hconv, Finset.sum_eq_single_of_mem ((N, 1) : ℕ × ℕ) hmem hzero, hW1, mul_one]

/-- **The ramp difference collapses to the window-pair difference.**  On the hat
support `N ≤ X+h` (`h ≤ X`), the four-factor coefficient difference
`alignedCoeffFull − alignedCoeff` equals the pure two-window-leg difference
`(Λ_ℓ⍟Λ_ℓ − winCoeff⍟winCoeff)(N)` — the smooth/large spectators drop out. -/
lemma ramp_spectator_collapse (y : ℝ) (g : ℕ → ℂ) (X α β : ℝ) (hy : 0 < y)
    {h : ℝ} (hhX : h ≤ X) (hX0 : 0 ≤ X) {N : ℕ} (hN : (N : ℝ) ≤ X + h) :
    alignedCoeffFull y g α β N - alignedCoeff y g X α β N
      = (shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g))
            ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g))) N
        - (shiftCoeff (-(α : ℂ)) (winCoeff g X y)
            ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y)) N := by
  rw [alignedCoeffFull_eq_conv y g α β, alignedCoeff_eq_conv y g X α β]
  set Pf := shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)) with hPf
  set Qf := shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g)) with hQf
  set Pw := shiftCoeff (-(α : ℂ)) (winCoeff g X y) with hPw
  set Qw := shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y) with hQw
  set W := ellLin (restrictBelow y g)
    ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (ellLin (restrictAbove y g)) with hW
  have hsub : ((Pf ⍟ Qf) ⍟ W) N - ((Pw ⍟ Qw) ⍟ W) N
      = ((fun n => (Pf ⍟ Qf) n - (Pw ⍟ Qw) n) ⍟ W) N := by
    rw [convolution_sub_left]
  rw [hsub]
  have hW1 : W 1 = 1 := by
    simp [hW, LSeries.convolution_def, Nat.divisorsAntidiagonal_one, shiftCoeff, ellLin_one,
      Complex.one_cpow]
  have hsupp : ∀ j : ℕ, (j : ℝ) ≤ X →
      (fun n => (Pf ⍟ Qf) n - (Pw ⍟ Qw) n) j = 0 := by
    intro j hj
    have hwp := window_pair_untrunc y g hy X α β j hj
    rw [← hPf, ← hQf, ← hPw, ← hQw] at hwp
    simp only [hwp, sub_self]
  rw [conv_spectator_collapse hhX hX0 hW1 hsupp hN]

/-! ## The squeeze support and the per-term difference bound -/

/-- A `shiftCoeff` with non-positive real exponent is norm-dominated by its base
coefficient at every `n ≥ 1`. -/
lemma norm_shiftCoeff_le_of_reNonpos {w : ℂ} (hw : w.re ≤ 0) {a : ℕ → ℂ} {n : ℕ}
    (hn : 1 ≤ n) : ‖shiftCoeff w a n‖ ≤ ‖a n‖ := by
  have hn0 : 0 < n := hn
  rw [shiftCoeff, norm_mul, Complex.norm_natCast_cpow_of_pos hn0]
  have hle1 : (n : ℝ) ^ w.re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) hw
  calc ‖a n‖ * (n : ℝ) ^ w.re ≤ ‖a n‖ * 1 := mul_le_mul_of_nonneg_left hle1 (norm_nonneg _)
    _ = ‖a n‖ := mul_one _

/-- **The defect forces its partner into the squeeze.**  If `k` is a defect leg
(`lambdaLin` nonzero, `winCoeff` vanishing — so `k ≥ X/y`) with a prime-power partner
`l` (`lambdaLin` nonzero) and `k·l ≤ X+h`, then `l` lands in the squeeze interval
`(⌊y⌋, ⌊y+y·h/X⌋]`. -/
lemma defect_partner_in_squeeze (g : ℕ → ℂ) {X h y : ℝ} (hy : 0 < y) (hX : 0 < X) {k l : ℕ}
    (hklhi : (k : ℝ) * (l : ℝ) ≤ X + h)
    (hkΛ : lambdaLin (restrictAbove y g) k ≠ 0) (hkw : winCoeff g X y k = 0)
    (hlΛ : lambdaLin (restrictAbove y g) l ≠ 0) :
    l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊ := by
  have hky : X ≤ (k : ℝ) * y := winCoeff_zero_defect g hy hkΛ hkw
  have hk0 : k ≠ 0 := by
    rintro rfl; apply hkΛ; unfold lambdaLin; rw [if_neg not_isPrimePow_zero]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hylt : y < (l : ℝ) := lambdaLin_restrictAbove_gt hlΛ
  rw [Finset.mem_Ioc]
  refine ⟨(Nat.floor_lt hy.le).mpr hylt, ?_⟩
  -- `l ≤ y + y·h/X`
  have hlX : (l : ℝ) * X ≤ y * X + y * h := by
    nlinarith [mul_le_mul_of_nonneg_left hky (Nat.cast_nonneg l : (0 : ℝ) ≤ (l : ℝ)),
      mul_le_mul_of_nonneg_right hklhi hy.le]
  have hl_le : (l : ℝ) ≤ y + y * h / X := by
    have hstep : (l : ℝ) * X ≤ (y + y * h / X) * X := by
      rw [add_mul, div_mul_cancel₀ (y * h) hX.ne']; exact hlX
    exact le_of_mul_le_mul_right hstep hX
  exact Nat.le_floor hl_le

/-- **The per-term squeeze bound.**  On the ramp `X < k·l ≤ X+h` (with `0 < α`-`β`
shift decay), the two-window-leg coefficient difference at `(k, l)` is bounded by
`2‖Λ_ℓ k‖‖Λ_ℓ l‖` and is supported where `k` or `l` lies in the squeeze — the exact
`rampSliverMass` index structure. -/
lemma norm_shiftPair_diff_le (y : ℝ) (g : ℕ → ℂ)
    {X h α β : ℝ} (hy : 0 < y) (hX : 0 < X) (hα : 0 ≤ α) (hβ : 0 ≤ β) {k l : ℕ}
    (hkl_lo : X < (k : ℝ) * (l : ℝ)) (hkl_hi : (k : ℝ) * (l : ℝ) ≤ X + h) :
    ‖shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)) k
        * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g)) l
      - shiftCoeff (-(α : ℂ)) (winCoeff g X y) k
        * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y) l‖
      ≤ 2 * (‖lambdaLin (restrictAbove y g) k‖ * ‖lambdaLin (restrictAbove y g) l‖)
        * ((if k ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊ then (1 : ℝ) else 0)
          + (if l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊ then (1 : ℝ) else 0)) := by
  set Lam := lambdaLin (restrictAbove y g) with hLamdef
  set w_ := winCoeff g X y with hw_def
  set sq := Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊ with hsqdef
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk; · simp at hkl_lo; linarith [hX]
    exact hk
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with rfl | hl; · simp at hkl_lo; linarith [hX]
    exact hl
  -- the `.re ≤ 0` facts
  have hαre : (-(α : ℂ)).re ≤ 0 := by rw [Complex.neg_re, Complex.ofReal_re]; linarith
  have hβre : (-(α : ℂ) - 2 * (β : ℂ)).re ≤ 0 := by
    rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
    have h2 : (2 * (β : ℂ)).re = 2 * β := by rw [Complex.mul_re]; simp
    rw [h2]; linarith
  -- the norm bound `‖diff‖ ≤ 2‖Lamk‖‖Laml‖`
  have h1 : ‖shiftCoeff (-(α : ℂ)) Lam k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) Lam l‖
      ≤ ‖Lam k‖ * ‖Lam l‖ := by
    rw [norm_mul]
    exact mul_le_mul (norm_shiftCoeff_le_of_reNonpos hαre hk1)
      (norm_shiftCoeff_le_of_reNonpos hβre hl1) (norm_nonneg _) (norm_nonneg _)
  have h2 : ‖shiftCoeff (-(α : ℂ)) w_ k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) w_ l‖
      ≤ ‖Lam k‖ * ‖Lam l‖ := by
    rw [norm_mul]
    exact mul_le_mul
      (le_trans (norm_shiftCoeff_le_of_reNonpos hαre hk1) (norm_winCoeff_le g X y k))
      (le_trans (norm_shiftCoeff_le_of_reNonpos hβre hl1) (norm_winCoeff_le g X y l))
      (norm_nonneg _) (norm_nonneg _)
  have hnorm_le : ‖shiftCoeff (-(α : ℂ)) Lam k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) Lam l
        - shiftCoeff (-(α : ℂ)) w_ k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) w_ l‖
      ≤ 2 * (‖Lam k‖ * ‖Lam l‖) := by
    calc ‖shiftCoeff (-(α : ℂ)) Lam k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) Lam l
            - shiftCoeff (-(α : ℂ)) w_ k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) w_ l‖
        ≤ ‖shiftCoeff (-(α : ℂ)) Lam k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) Lam l‖
          + ‖shiftCoeff (-(α : ℂ)) w_ k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) w_ l‖ :=
          norm_sub_le _ _
      _ ≤ ‖Lam k‖ * ‖Lam l‖ + ‖Lam k‖ * ‖Lam l‖ := add_le_add h1 h2
      _ = 2 * (‖Lam k‖ * ‖Lam l‖) := by ring
  -- support: off the squeeze the difference vanishes
  have hagree : k ∉ sq → l ∉ sq →
      shiftCoeff (-(α : ℂ)) Lam k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) Lam l
        = shiftCoeff (-(α : ℂ)) w_ k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) w_ l := by
    intro hknk hlnl
    by_cases hLamk : Lam k = 0
    · have hwk : w_ k = 0 := by rw [hw_def]; unfold winCoeff; split_ifs with h; exacts [hLamk, rfl]
      simp only [shiftCoeff, hLamk, hwk, zero_mul]
    · by_cases hLaml : Lam l = 0
      · have hwl : w_ l = 0 := by
          rw [hw_def]; unfold winCoeff; split_ifs with h; exacts [hLaml, rfl]
        simp only [shiftCoeff, hLaml, hwl, zero_mul, mul_zero]
      · have hwk : w_ k = Lam k := by
          by_cases hmemk : k ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊
          · rw [hw_def, hLamdef]; unfold winCoeff; rw [if_pos hmemk]
          · exfalso
            have hwk0 : w_ k = 0 := by rw [hw_def]; unfold winCoeff; rw [if_neg hmemk]
            exact hlnl (defect_partner_in_squeeze g hy hX hkl_hi hLamk hwk0 hLaml)
        have hwl : w_ l = Lam l := by
          by_cases hmeml : l ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊
          · rw [hw_def, hLamdef]; unfold winCoeff; rw [if_pos hmeml]
          · exfalso
            have hwl0 : w_ l = 0 := by rw [hw_def]; unfold winCoeff; rw [if_neg hmeml]
            refine hknk (defect_partner_in_squeeze g hy hX ?_ hLaml hwl0 hLamk)
            rw [mul_comm]; exact hkl_hi
        simp only [shiftCoeff, hwk, hwl]
  -- combine
  by_cases hind : k ∈ sq ∨ l ∈ sq
  · have hind1 : (1 : ℝ) ≤ (if k ∈ sq then (1 : ℝ) else 0) + (if l ∈ sq then (1 : ℝ) else 0) := by
      rcases hind with hk | hl
      · rw [if_pos hk]; have : (0 : ℝ) ≤ (if l ∈ sq then (1 : ℝ) else 0) := by positivity
        linarith
      · rw [if_pos hl]; have : (0 : ℝ) ≤ (if k ∈ sq then (1 : ℝ) else 0) := by positivity
        linarith
    calc ‖shiftCoeff (-(α : ℂ)) Lam k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) Lam l
            - shiftCoeff (-(α : ℂ)) w_ k * shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) w_ l‖
        ≤ 2 * (‖Lam k‖ * ‖Lam l‖) := hnorm_le
      _ = 2 * (‖Lam k‖ * ‖Lam l‖) * 1 := (mul_one _).symm
      _ ≤ 2 * (‖Lam k‖ * ‖Lam l‖)
            * ((if k ∈ sq then (1 : ℝ) else 0) + (if l ∈ sq then (1 : ℝ) else 0)) :=
          mul_le_mul_of_nonneg_left hind1 (by positivity)
  · rw [not_or] at hind
    obtain ⟨hknk, hlnl⟩ := hind
    rw [hagree hknk hlnl, sub_self, norm_zero]
    positivity

/-! ## The refold onto `rampSliverMass` -/

/-- `rampSliverMass` as a single sum over the pair-set `{(k, l) : l ∈ squeeze,
k ∈ (⌊X/l⌋, ⌊(X+h)/l⌋]}`. -/
lemma rampSliverMass_eq_biUnion (g : ℕ → ℂ) (X h y : ℝ) :
    rampSliverMass g X h y
      = ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊).biUnion (fun l =>
          (Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊).image (fun k => ((k, l) : ℕ × ℕ))),
        ‖lambdaLin (restrictAbove y g) p.1‖ * ‖lambdaLin (restrictAbove y g) p.2‖ := by
  rw [rampSliverMass, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_image (fun k1 _ k2 _ he => by rw [Prod.mk.injEq] at he; exact he.1)]
  · intro l1 _ l2 _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro p ⟨k1, _, hk1⟩ ⟨k2, _, hk2⟩
    rw [← hk1, Prod.mk.injEq] at hk2
    exact hne hk2.2.symm

/-- If `X < k·l ≤ X+h` and `l ≥ 1`, then `k` lies in the ramp run
`(⌊X/l⌋, ⌊(X+h)/l⌋]` — the `rampSliverMass` inner index set. -/
lemma partner_in_Ioc {X h : ℝ} (hX : 0 < X) {l k : ℕ} (hl1 : 1 ≤ l)
    (hlo : X < (k : ℝ) * (l : ℝ)) (hhi : (k : ℝ) * (l : ℝ) ≤ X + h) :
    k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊ := by
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
  have hXhnn : (0 : ℝ) ≤ X + h := (lt_trans hX (lt_of_lt_of_le hlo hhi)).le
  rw [Finset.mem_Ioc]
  refine ⟨?_, ?_⟩
  · rw [Nat.floor_lt (by positivity), div_lt_iff₀ hlpos]; linarith
  · rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hlpos]; linarith

/-- **The window-pair difference sum, bounded by `4·rampSliverMass`.**  Summed over the
hat support `N ≤ X+h`, the norm of the window-pair difference is dominated by
`4·rampSliverMass`: drop `N ≤ X` (`window_pair_untrunc`), bound each surviving `N` by
its antidiagonal via the per-term squeeze bound, flatten, and refold each squeeze leg
onto `rampSliverMass`. -/
lemma sum_D2_le_rampSliverMass (y : ℝ) (g : ℕ → ℂ)
    {X h α β : ℝ} (hy : 0 < y) (hX : 0 < X) (hh : 0 < h) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∑ N ∈ Finset.range (⌊X + h⌋₊ + 1),
        ‖(shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g))
              ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g))) N
          - (shiftCoeff (-(α : ℂ)) (winCoeff g X y)
              ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y)) N‖
      ≤ 4 * rampSliverMass g X h y := by
  set Pf := shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g)) with hPf
  set Qf := shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g)) with hQf
  set Pw := shiftCoeff (-(α : ℂ)) (winCoeff g X y) with hPw
  set Qw := shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y) with hQw
  set Lam := lambdaLin (restrictAbove y g) with hLamdef
  set sq := Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊ with hsqdef
  set M := ⌊X + h⌋₊ with hMdef
  set F : ℕ × ℕ → ℝ := fun p => ‖Lam p.1‖ * ‖Lam p.2‖ with hF
  set filt := (Finset.range (M + 1)).filter (fun N => ⌊X⌋₊ < N) with hfilt
  set B' := filt.biUnion (fun N => N.divisorsAntidiagonal) with hB'
  -- disjointness of the antidiagonals over `filt`
  have hdisj : (↑filt : Set ℕ).PairwiseDisjoint (fun N => N.divisorsAntidiagonal) := by
    intro N1 _ N2 _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro q hq1 hq2
    rw [Nat.mem_divisorsAntidiagonal] at hq1 hq2
    exact hne (hq1.1.symm.trans hq2.1)
  -- bounds carried by every pair in `B'`
  have hB'_bounds : ∀ p ∈ B', X < (p.1 : ℝ) * (p.2 : ℝ)
      ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X + h ∧ 1 ≤ p.1 ∧ 1 ≤ p.2 := by
    intro p hp
    rw [hB', Finset.mem_biUnion] at hp
    obtain ⟨N, hNfilt, hpN⟩ := hp
    rw [hfilt, Finset.mem_filter, Finset.mem_range] at hNfilt
    obtain ⟨hNlt, hNX⟩ := hNfilt
    rw [Nat.mem_divisorsAntidiagonal] at hpN
    obtain ⟨hprodN, hN0⟩ := hpN
    have hp11 : 1 ≤ p.1 :=
      Nat.one_le_iff_ne_zero.mpr (fun hh0 => hN0 (by rw [← hprodN, hh0, zero_mul]))
    have hp21 : 1 ≤ p.2 :=
      Nat.one_le_iff_ne_zero.mpr (fun hh0 => hN0 (by rw [← hprodN, hh0, mul_zero]))
    have hcast : (p.1 : ℝ) * (p.2 : ℝ) = (N : ℝ) := by rw [← Nat.cast_mul, hprodN]
    refine ⟨?_, ?_, hp11, hp21⟩
    · rw [hcast]
      have hstep : ⌊X⌋₊ + 1 ≤ N := hNX
      have : (⌊X⌋₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hstep
      linarith [Nat.lt_floor_add_one X]
    · rw [hcast]
      have hNM : (N : ℝ) ≤ (M : ℝ) := by rw [hMdef]; exact_mod_cast (by omega : N ≤ ⌊X + h⌋₊)
      have hMX : (M : ℝ) ≤ X + h := by rw [hMdef]; exact Nat.floor_le (add_nonneg hX.le hh.le)
      linarith
  have hsq_ge1 : ∀ m ∈ sq, 1 ≤ m := by
    intro m hm; rw [hsqdef, Finset.mem_Ioc] at hm; omega
  -- (A) drop `N ≤ X`
  have hAdrop : ∑ N ∈ Finset.range (M + 1), ‖(Pf ⍟ Qf) N - (Pw ⍟ Qw) N‖
      = ∑ N ∈ filt, ‖(Pf ⍟ Qf) N - (Pw ⍟ Qw) N‖ := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro N hNrange hNnf
    have hNle : (N : ℝ) ≤ X := by
      rw [Finset.mem_filter, not_and] at hNnf
      have hle : N ≤ ⌊X⌋₊ := not_lt.mp (hNnf hNrange)
      calc (N : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hle
        _ ≤ X := Nat.floor_le hX.le
    have hwp := window_pair_untrunc y g hy X α β N hNle
    rw [← hPf, ← hQf, ← hPw, ← hQw] at hwp
    rw [hwp, sub_self, norm_zero]
  -- (B) per-`N` bound on `filt` via the per-term squeeze bound
  have hperN : ∀ N ∈ filt, ‖(Pf ⍟ Qf) N - (Pw ⍟ Qw) N‖
      ≤ ∑ p ∈ N.divisorsAntidiagonal,
          2 * (‖Lam p.1‖ * ‖Lam p.2‖)
            * ((if p.1 ∈ sq then (1 : ℝ) else 0) + (if p.2 ∈ sq then (1 : ℝ) else 0)) := by
    intro N hN
    have hsub : (Pf ⍟ Qf) N - (Pw ⍟ Qw) N
        = ∑ p ∈ N.divisorsAntidiagonal, (Pf p.1 * Qf p.2 - Pw p.1 * Qw p.2) := by
      rw [LSeries.convolution_def, LSeries.convolution_def, ← Finset.sum_sub_distrib]
    rw [hsub]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have hcast : (p.1 : ℝ) * (p.2 : ℝ) = (N : ℝ) := by rw [← Nat.cast_mul, hp.1]
    rw [hfilt, Finset.mem_filter, Finset.mem_range] at hN
    obtain ⟨hNlt, hNX⟩ := hN
    have hlo : X < (p.1 : ℝ) * (p.2 : ℝ) := by
      rw [hcast]
      have hstep : ⌊X⌋₊ + 1 ≤ N := hNX
      have : (⌊X⌋₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hstep
      linarith [Nat.lt_floor_add_one X]
    have hhi : (p.1 : ℝ) * (p.2 : ℝ) ≤ X + h := by
      rw [hcast]
      have hNM : (N : ℝ) ≤ (M : ℝ) := by rw [hMdef]; exact_mod_cast (by omega : N ≤ ⌊X + h⌋₊)
      have hMX : (M : ℝ) ≤ X + h := by rw [hMdef]; exact Nat.floor_le (add_nonneg hX.le hh.le)
      linarith
    exact norm_shiftPair_diff_le y g hy hX hα hβ hlo hhi
  -- combine (A), (B), flatten
  rw [hAdrop]
  refine le_trans (Finset.sum_le_sum hperN) ?_
  rw [← Finset.sum_biUnion hdisj, ← hB']
  -- split the `Bnd` into the two squeeze-leg sums
  have hsplit : ∑ p ∈ B',
        2 * (‖Lam p.1‖ * ‖Lam p.2‖)
          * ((if p.1 ∈ sq then (1 : ℝ) else 0) + (if p.2 ∈ sq then (1 : ℝ) else 0))
      = 2 * (∑ p ∈ B', F p * (if p.1 ∈ sq then (1 : ℝ) else 0))
        + 2 * (∑ p ∈ B', F p * (if p.2 ∈ sq then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hF]; ring
  rw [hsplit]
  -- each leg refolds to `rampSliverMass`
  have hlpart : ∑ p ∈ B', F p * (if p.2 ∈ sq then (1 : ℝ) else 0) ≤ rampSliverMass g X h y := by
    have heq : ∑ p ∈ B', F p * (if p.2 ∈ sq then (1 : ℝ) else 0)
        = ∑ p ∈ B'.filter (fun p => p.2 ∈ sq), F p := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_ite, mul_one, mul_zero])
    rw [heq, rampSliverMass_eq_biUnion]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by rw [hF]; positivity)
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpB', hp2sq⟩ := hp
    obtain ⟨hlo, hhi, _, _⟩ := hB'_bounds p hpB'
    rw [Finset.mem_biUnion]
    exact ⟨p.2, hp2sq, Finset.mem_image.mpr ⟨p.1,
      partner_in_Ioc hX (hsq_ge1 p.2 hp2sq) hlo hhi, rfl⟩⟩
  have hkpart : ∑ p ∈ B', F p * (if p.1 ∈ sq then (1 : ℝ) else 0) ≤ rampSliverMass g X h y := by
    have heq : ∑ p ∈ B', F p * (if p.1 ∈ sq then (1 : ℝ) else 0)
        = ∑ p ∈ B'.filter (fun p => p.1 ∈ sq), F p := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_ite, mul_one, mul_zero])
    rw [heq, rampSliverMass_eq_biUnion]
    have hswapeq : ∑ p ∈ B'.filter (fun p => p.1 ∈ sq), F p
        = ∑ q ∈ (B'.filter (fun p => p.1 ∈ sq)).image Prod.swap, F q := by
      rw [Finset.sum_image (fun a _ b _ hab => Prod.swap_injective hab)]
      exact Finset.sum_congr rfl (fun p _ => by
        simp only [hF, Prod.fst_swap, Prod.snd_swap]; ring)
    rw [hswapeq]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by rw [hF]; positivity)
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hps, hpq⟩ := hq
    rw [Finset.mem_filter] at hps
    obtain ⟨hpB', hp1sq⟩ := hps
    obtain ⟨hlo, hhi, _, _⟩ := hB'_bounds p hpB'
    rw [← hpq, Finset.mem_biUnion]
    refine ⟨p.1, hp1sq,
      Finset.mem_image.mpr ⟨p.2, partner_in_Ioc hX (hsq_ge1 p.1 hp1sq) ?_ ?_, rfl⟩⟩
    · rw [mul_comm]; exact hlo
    · rw [mul_comm]; exact hhi
  linarith [hlpart, hkpart]

/-! ## The norm bridge -/

/-- **THE NORM BRIDGE.**  The ramp residue is bounded by a constant times the
`rampSliverMass`: `‖rampTerm g X h y η‖ ≤ 8 · rampSliverMass g X h y`.  The `2•`
Jacobian, the `∫∫` over `[0,η]²` (`≤ η² ≤ 1`), `hatK ≤ 1`, and the shift decay are the
bounded factors; the per-`N` collapse (`ramp_spectator_collapse`) and the squeeze
refold (`sum_D2_le_rampSliverMass`) provide the `4·rampSliverMass` inner bound. -/
lemma ramp_norm_le_sliverMass (y : ℝ) (g : ℕ → ℂ)
    {X h η : ℝ} (hy : 0 < y) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ‖rampTerm g X h y η‖ ≤ 8 * rampSliverMass g X h y := by
  set R := rampSliverMass g X h y with hR
  have hRnn : (0 : ℝ) ≤ R := rampSliverMass_nonneg g X h y
  -- the inner uniform bound: `‖∑' N, D·hatK‖ ≤ 4R` for `α, β ≥ 0`
  have hinner : ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      ‖∑' N, (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖
        ≤ 4 * R := by
    intro α β hα hβ
    have htsum :
        (∑' N, (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ))
          = ∑ N ∈ Finset.range (⌊X + h⌋₊ + 1),
              (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ) :=
      tsum_eq_sum (fun N hN => by rw [hatK_ofReal_eq_zero_of_notMem hh hN, mul_zero])
    rw [htsum]
    calc ‖∑ N ∈ Finset.range (⌊X + h⌋₊ + 1),
            (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖
        ≤ ∑ N ∈ Finset.range (⌊X + h⌋₊ + 1),
            ‖(alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ N ∈ Finset.range (⌊X + h⌋₊ + 1),
            ‖alignedCoeffFull y g α β N - alignedCoeff y g X α β N‖ := by
          refine Finset.sum_le_sum (fun N _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hatK_nonneg hh N)]
          calc ‖alignedCoeffFull y g α β N - alignedCoeff y g X α β N‖ * hatK X h N
              ≤ ‖alignedCoeffFull y g α β N - alignedCoeff y g X α β N‖ * 1 :=
                mul_le_mul_of_nonneg_left (hatK_le_one hh N) (norm_nonneg _)
            _ = ‖alignedCoeffFull y g α β N - alignedCoeff y g X α β N‖ := mul_one _
      _ = ∑ N ∈ Finset.range (⌊X + h⌋₊ + 1),
            ‖(shiftCoeff (-(α : ℂ)) (lambdaLin (restrictAbove y g))
                  ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (lambdaLin (restrictAbove y g))) N
              - (shiftCoeff (-(α : ℂ)) (winCoeff g X y)
                  ⍟ shiftCoeff (-(α : ℂ) - 2 * (β : ℂ)) (winCoeff g X y)) N‖ := by
          refine Finset.sum_congr rfl (fun N hN => ?_)
          rw [Finset.mem_range] at hN
          have hNXh : (N : ℝ) ≤ X + h := by
            have h1 : (N : ℝ) ≤ (⌊X + h⌋₊ : ℝ) := by
              exact_mod_cast (by omega : N ≤ ⌊X + h⌋₊)
            have h2 : (⌊X + h⌋₊ : ℝ) ≤ X + h := Nat.floor_le (add_nonneg hX.le hh.le)
            linarith
          rw [ramp_spectator_collapse y g X α β hy hhX hX.le hNXh]
      _ ≤ 4 * R := sum_D2_le_rampSliverMass y g hy hX hh hα hβ
  -- integrate: `‖∫_0^η Inner dβ‖ ≤ 4R·η`
  have hG : ∀ α : ℝ, 0 ≤ α →
      ‖∫ β in (0 : ℝ)..η,
          ∑' N, (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖
        ≤ 4 * R * η := by
    intro α hα
    have hbd : ∀ β ∈ Set.Ioc (min 0 η) (max 0 η),
        ‖∑' N, (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖
          ≤ 4 * R := by
      intro β hβmem
      rw [min_eq_left hη0, max_eq_right hη0, Set.mem_Ioc] at hβmem
      exact hinner α β hα (le_of_lt hβmem.1)
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rwa [sub_zero, abs_of_nonneg hη0] at hbound
  -- integrate again: `‖∫∫‖ ≤ 4R·η²`
  have houter :
      ‖∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          ∑' N, (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖
        ≤ 4 * R * η * η := by
    have hbd : ∀ α ∈ Set.Ioc (min 0 η) (max 0 η),
        ‖∫ β in (0 : ℝ)..η,
            ∑' N, (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖
          ≤ 4 * R * η := by
      intro α hαmem
      rw [min_eq_left hη0, max_eq_right hη0, Set.mem_Ioc] at hαmem
      exact hG α (le_of_lt hαmem.1)
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rwa [sub_zero, abs_of_nonneg hη0] at hbound
  -- assemble the constant chain
  rw [rampTerm, norm_smul, Real.norm_ofNat]
  calc (2 : ℝ) * ‖∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
          ∑' N, (alignedCoeffFull y g α β N - alignedCoeff y g X α β N) * (hatK X h N : ℂ)‖
      ≤ 2 * (4 * R * η * η) := by
        apply mul_le_mul_of_nonneg_left houter (by norm_num)
    _ ≤ 8 * R := by
        have hηη : η * η ≤ 1 := by nlinarith [hη0, hη1]
        nlinarith [mul_le_mul_of_nonneg_left hηη hRnn]

/-! ## H-EXIT (unconditional) — `prop21_unconditional_final` -/

/-- **H-EXIT — `prop21_unconditional_final`.  THE S1′ REPRESENTATION STANDS
UNCONDITIONALLY.**  With every regime hypothesis of the H-5 v5 assembly discharged, the
S1′ representation holds with NO conditional hypothesis: under route (i) (`f = ellLin g`),
`h = X / √(log X)`, `η = 1/log y`, and the gates `√(log X) ≤ y ≤ √X`, `10 ≤ y`, the twisted
hat-smoothed sum equals the frozen `prop21RHS` up to an error of the E-grade shape

  `C_E · ((X+h)/log(X+h)) · log y  +  C_R · (X/log X) · log y`,

the two summands being the MS-A+MS-B endpoint mass (`prop21_unconditional`'s
`mult_shiu_MS_EXIT` term, `C_E`) and the ramp-sliver mass (`C_R = 8·C`, the ramp residue
`E_ramp` discharged here via the norm bridge `ramp_norm_le_sliverMass` composed with the
Selberg-sieve GRAIN `rampSliverMass_bound_unconditional`).

Consumes `prop21_unconditional` VERBATIM (iron rule 1): the single hypothesis `hsliver` is
supplied, not weakened.  The per-window regime `hreg` is carried as the honest union with
`rampSliverMass_bound_unconditional`'s regime set (its `hgrain` is the Selberg-sieve
short-interval Chebyshev bound, `ShortIntervalPsi`).

Provenance: P21-2X → P21-3K → V5-0 → the v5 collapse (`aligned_collapse_assembled`) →
this stone. -/
theorem prop21_unconditional_final (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ)
    {X h c₀ y η : ℝ} (hX : Real.exp 1 ≤ X) (hh : h = X / Real.sqrt (Real.log X))
    (hc₀ : 1 < c₀) (hη : η = 1 / Real.log y) (hc' : 0 < c₀ - 2 * η)
    (hy10 : 10 ≤ y) (hyX : y ≤ Real.sqrt X) (hygate : Real.sqrt (Real.log X) ≤ y)
    (hreg : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
        (65536 : ℝ) ≤ X / (l : ℝ) ∧
        X / (l : ℝ) ≤ (h / (l : ℝ)) * Real.sqrt (Real.sqrt (Real.sqrt (X / (l : ℝ)))) ∧
        h / (l : ℝ) ≤ X / (l : ℝ)) :
    ∃ C_E C_R : ℝ, ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ))
        - prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
      ≤ C_E * ((X + h) / Real.log (X + h)) * Real.log y
        + C_R * (X / Real.log X) * Real.log y := by
  -- regime facts
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX1 : (1 : ℝ) ≤ X := le_trans (by linarith) hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hsqlogX : (0 : ℝ) < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr (by linarith)
  have hsqge1 : (1 : ℝ) ≤ Real.sqrt (Real.log X) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogX1
  have hh0 : (0 : ℝ) < h := by rw [hh]; exact div_pos hXpos hsqlogX
  have hhX : h ≤ X := by rw [hh, div_le_iff₀ hsqlogX]; nlinarith [hsqge1, hXpos]
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hexp10 : Real.exp 1 ≤ 10 := by linarith [Real.exp_one_lt_three]
  have hylog1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (le_trans hexp10 hy10)
  have hη0 : (0 : ℝ) ≤ η := by rw [hη]; exact le_of_lt (div_pos one_pos hlogy)
  have hη1 : η ≤ 1 := by rw [hη, div_le_one hlogy]; exact hylog1
  -- the twisted datum
  have hgtw : ∀ p, p.Prime → ‖(fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀ hp.one_lt.le, mul_one]
    exact hg p hp
  -- the unconditional sliver mass bound
  obtain ⟨C, hCbound⟩ := rampSliverMass_bound_unconditional
    (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) hgtw hX hh hy10 hygate hreg
  -- the norm bridge, then the discharge of `hsliver`
  have hsliver : ‖rampTerm (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) X h y η‖
      ≤ 8 * (C * (X / Real.log X) * Real.log y) := by
    refine le_trans (ramp_norm_le_sliverMass y (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I))
      hy0 hXpos hh0 hhX hη0 hη1) ?_
    exact mul_le_mul_of_nonneg_left hCbound (by norm_num)
  -- consume `prop21_unconditional` verbatim
  obtain ⟨C_E, hCE⟩ := prop21_unconditional g hg t₀ hX1 hh0 hc₀ hη hc' hy10 hyX hsliver
  refine ⟨C_E, 8 * C, ?_⟩
  have heq : (8 * C) * (X / Real.log X) * Real.log y
      = 8 * (C * (X / Real.log X) * Real.log y) := by ring
  rw [heq]
  exact hCE

end Salt.MR

/-! ## H-EXIT (consumer-facing) — `prop21_unconditional_clean`

`prop21_unconditional_final` discharges the ramp residue but still carries the
per-window regime `hreg` (the `rampSliverMass_bound_unconditional` grain's regime set).
This section discharges `hreg` from the OUTER regime, leaving the S1′ representation
with only the consumer-facing hypotheses (an ∃-packaged `X`-threshold, the `h`-pin, the
`c₀/η/y` gates, and `hg`).

The discharge, per window `l ∈ (⌊y⌋, ⌊y+y·h/X⌋]`:

* `l ≤ y + y·h/X ≤ 2y ≤ 2√X` (`h ≤ X` from the pin, `y ≤ √X` from the gate), so
  `X/l ≥ √X/2`.
* **(a)** `65536 ≤ X/l`: `√X/2 ≥ 65536` once `X ≥ (2·65536)² = 17179869184`.
* **(b)** `X/l ≤ (h/l)·√√√(X/l)`: with `h/l = (X/l)/√(log X)` and `s := √√√(X/l)`
  (`s⁸ = X/l`), the condition is `√(log X) ≤ s`, i.e. `(log X)⁴ ≤ X/l`; and
  `X/l ≥ √X/2 ≥ (log X)⁴` at large `X` (the `log⁴ = o(√X)` threshold, ∃-packaged by
  `logpow4_le_sqrt_eventually`).
* **(c)** `h/l ≤ X/l`: `h ≤ X` from the pin.
-/

namespace Salt.MR

open Complex Filter Asymptotics
open scoped BigOperators

/-- **The `log⁴ = o(√X)` threshold (∃-packaged).**  There is an `X₁` beyond which
`(log X)⁴ ≤ √X/2` — the growth fact behind the middle window condition (b), obtained
from `isLittleO_log_rpow_rpow_atTop` at exponents `4` and `1/2`. -/
private lemma logpow4_le_sqrt_eventually :
    ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X → (Real.log X) ^ 4 ≤ Real.sqrt X / 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (4 : ℝ)) =o[atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound := hlo.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max a 1, fun X hX => ?_⟩
  have hXa : a ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hlogXnn : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hkey := ha X hXa
  have h1nn : (0 : ℝ) ≤ Real.log X ^ (4 : ℝ) := Real.rpow_nonneg hlogXnn 4
  have h2nn : (0 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h1nn, Real.norm_of_nonneg h2nn,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow] at hkey
  linarith [hkey]

/-- **H-EXIT — the consumer-facing clean form (`prop21_unconditional_clean`).**
`prop21_unconditional_final` with the per-window regime `hreg` DISCHARGED from the outer
regime.  For `X` beyond the (existentially packaged) threshold `X₀`, and under the outer
gates — the `h`-pin, `1 < c₀`, the `η`-pin, `0 < c₀ − 2η`, `10 ≤ y ≤ √X`,
`√(log X) ≤ y` — the S1′ representation holds:

  `‖(∑' n, seamCoeff (ellLin g) 1 t₀ n · hatK) − prop21RHS‖ ≤ C_E·((X+h)/log(X+h))·log y
      + C_R·(X/log X)·log y`.

The window regime is derived internally (`l ≤ 2√X ⟹ X/l ≥ √X/2`, then `√X/2 ≥ 65536`
and `√X/2 ≥ (log X)⁴` at large `X`), so the only hypotheses are the outer regime. -/
theorem prop21_unconditional_clean (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ X₀ : ℝ, ∀ {X h c₀ y η : ℝ}, X₀ ≤ X →
        h = X / Real.sqrt (Real.log X) → 1 < c₀ → η = 1 / Real.log y →
        0 < c₀ - 2 * η → 10 ≤ y → y ≤ Real.sqrt X → Real.sqrt (Real.log X) ≤ y →
      ∃ C_E C_R : ℝ, ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ))
          - prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
        ≤ C_E * ((X + h) / Real.log (X + h)) * Real.log y
          + C_R * (X / Real.log X) * Real.log y := by
  obtain ⟨X₁, hX₁⟩ := logpow4_le_sqrt_eventually
  refine ⟨max X₁ 17179869184, ?_⟩
  intro X h c₀ y η hXlb hh hc₀ hη hc' hy10 hyX hygate
  -- outer-regime facts
  have hXbig : (17179869184 : ℝ) ≤ X := le_trans (le_max_right _ _) hXlb
  have hXX₁ : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hX : Real.exp 1 ≤ X :=
    (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 17179869184)).trans hXbig
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hsqlogX : (0 : ℝ) < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr hlogXpos
  have hsqge1 : (1 : ℝ) ≤ Real.sqrt (Real.log X) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogX1
  have hh0 : (0 : ℝ) < h := by rw [hh]; exact div_pos hXpos hsqlogX
  have hhX : h ≤ X := by rw [hh, div_le_iff₀ hsqlogX]; nlinarith [hsqge1, hXpos]
  have hy0 : (0 : ℝ) < y := by linarith
  have hsqrtXnn : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hsqrtXge : (131072 : ℝ) ≤ Real.sqrt X := by
    have h1 : ((131072 : ℝ)) ^ 2 ≤ X := by nlinarith [hXbig]
    calc (131072 : ℝ) = Real.sqrt (131072 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt h1
  have hlog4 : (Real.log X) ^ 4 ≤ Real.sqrt X / 2 := hX₁ X hXX₁
  -- the discharged regime
  have hreg : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
      (65536 : ℝ) ≤ X / (l : ℝ) ∧
      X / (l : ℝ) ≤ (h / (l : ℝ)) * Real.sqrt (Real.sqrt (Real.sqrt (X / (l : ℝ)))) ∧
      h / (l : ℝ) ≤ X / (l : ℝ) := by
    intro l hl
    rw [Finset.mem_Ioc] at hl
    obtain ⟨hllo, hlhi⟩ := hl
    have hl1 : 1 ≤ l := by omega
    have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
    have hyhX_nn : (0 : ℝ) ≤ y + y * h / X :=
      add_nonneg hy0.le (div_nonneg (mul_nonneg hy0.le hh0.le) hXpos.le)
    have hyh : y * h / X ≤ y := by
      rw [mul_div_assoc]
      have hhX1 : h / X ≤ 1 := by rw [div_le_one hXpos]; exact hhX
      calc y * (h / X) ≤ y * 1 := mul_le_mul_of_nonneg_left hhX1 hy0.le
        _ = y := mul_one y
    have hle2sqrt : (l : ℝ) ≤ 2 * Real.sqrt X := by
      have hlhiR : (l : ℝ) ≤ y + y * h / X := by
        calc (l : ℝ) ≤ (⌊y + y * h / X⌋₊ : ℝ) := by exact_mod_cast hlhi
          _ ≤ y + y * h / X := Nat.floor_le hyhX_nn
      linarith [hyh, hyX]
    have hXl_ge : Real.sqrt X / 2 ≤ X / (l : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hlpos]
      nlinarith [Real.mul_self_sqrt hXpos.le, mul_le_mul_of_nonneg_left hle2sqrt hsqrtXnn]
    have hXlpos : (0 : ℝ) < X / (l : ℝ) := div_pos hXpos hlpos
    refine ⟨?_, ?_, ?_⟩
    · -- (a) 65536 ≤ X/l
      have h65 : (65536 : ℝ) ≤ Real.sqrt X / 2 := by linarith [hsqrtXge]
      linarith [hXl_ge]
    · -- (b) X/l ≤ (h/l)·√√√(X/l)
      set Xl := X / (l : ℝ) with hXldef
      set s := Real.sqrt (Real.sqrt (Real.sqrt Xl)) with hsdef
      have hs8 : s ^ 8 = Xl := by
        have ha4 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt Xl) := Real.sqrt_nonneg _
        have ha2 : (0 : ℝ) ≤ Real.sqrt Xl := Real.sqrt_nonneg _
        have e2 : s ^ 2 = Real.sqrt (Real.sqrt Xl) := Real.sq_sqrt ha4
        have e4 : s ^ 4 = Real.sqrt Xl := by
          rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, e2, Real.sq_sqrt ha2]
        rw [show s ^ 8 = (s ^ 4) ^ 2 by ring, e4, Real.sq_sqrt hXlpos.le]
      have hspos : (0 : ℝ) < s :=
        Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hXlpos))
      have hkey8 : (Real.sqrt (Real.log X)) ^ 8 ≤ s ^ 8 := by
        rw [hs8, show (Real.sqrt (Real.log X)) ^ 8 = ((Real.sqrt (Real.log X)) ^ 2) ^ 4 by ring,
          Real.sq_sqrt hlogXpos.le]
        exact le_trans hlog4 hXl_ge
      have hkey : Real.sqrt (Real.log X) ≤ s :=
        le_of_pow_le_pow_left₀ (by norm_num) hspos.le hkey8
      have hhl : h / (l : ℝ) = Xl / Real.sqrt (Real.log X) := by
        rw [hXldef, hh, div_right_comm]
      rw [hhl, div_mul_eq_mul_div, le_div_iff₀ hsqlogX]
      exact mul_le_mul_of_nonneg_left hkey hXlpos.le
    · -- (c) h/l ≤ X/l
      exact div_le_div_of_nonneg_right hhX hlpos.le
  exact prop21_unconditional_final g hg t₀ hX hh hc₀ hη hc' hy10 hyX hygate hreg

/-! ## The head wire — connecting the S1′ representation to the T-chain

`T1_decay_trivial`/`hhead_supplier_trivial` (`HalaszHead`) consume the ball head as a
NAMED hypothesis

  `hhead : Uhead ≤ C₁·X·((1 + M)·exp(−M))`,  `M = 𝔻(seamCoeff f 1 t₀, costwist t; X)²`,

the S2′ centered head "K4′/S1′-conditional".  `prop21_unconditional_clean` now
discharges the **S1′ representation leg** of that conditionality UNCONDITIONALLY: the
seam sum equals `prop21RHS` up to the E-grade error.  The wire below composes the two —
it bounds the seam sum's NORM by the ball-head shape `C₁·X·(1+M)e^{−M}` **plus the
(now-unconditional) E error**, carrying the single remaining analytic input as the named
hypothesis `hRHS`.

**The one residual `hRHS` (honest frontier).**  `hRHS` bounds `‖prop21RHS‖` by the
ball-head main term `C₁·X·(1+M)e^{−M}`.  This is the S2′ step — bounding `prop21RHS`'s
`t`-integrand `𝒮·𝓛·P·P·hatKernel` by (the four-factor sup of `𝒮·𝓛` over the ball) ×
(the kernel-weighted window cross-integral of `P·P`), the sup then decaying like
`(1+M)e^{−M}` by the Halász/Euler-product pretentious bound.  Its ingredients are NOT in
the landed corpus:

* the four-factor sup bound `sup_{ball} ‖smoothSeries · largeSeries‖ ≤ C·e^{−M}` (the
  Halász mean-value / Euler-product decay in the pretentious distance `M`) — ABSENT;
* the integral-representation factoring `‖prop21RHS‖ ≤ X·supF·crossInt` linking the
  `α,β,t` triple integral to the K4′ window cross-integral — ABSENT;
* the window cross-integral → diagonal leg IS landed (`contour_A13_A14_head_sharp`,
  `k4_plan_le_diag_sharp`), and the sharp diagonal `(π/c)·(Σ‖lambdaLin g‖/nᶜ)²` supplies
  the `(1+M)` factor of the shape.

So `hRHS` is the exact residual the wire isolates; once it lands, the seam-sum head
bound follows unconditionally (this lemma), and — after the §8 `int_U`/moment assembly
routes the E error through the ball-integrated secondary term (`prop_A3'_assembly`, NOT a
pointwise inequality: the pointwise E is main-term-sized when `log y ≍ log X`, and only
its ball-`L²` mass is tail-grade) — `T1_decay_trivial` delivers the frozen T1 grade.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  The `hRHS` binder's distance `M` is GHS
Lemma 1's range-minimum `M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T` (was the
center value `pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X`); the
center-M deviation was the drift problem's source, while `M_range` never drifts below the
landed floor (`Mrange_one_floor`) and restores the frozen `prop_A3'` semantics.  The
per-frequency `t` parameter is subsumed by the range's offset variable and replaced by
the range parameter `T`. -/
/- ⟦CORRECTION 2026-07-22 night (M-BRIDGE-SCOPE, maestro-applied):
the (1+M) factor in hRHS is NOT supplied by the sharp diagonal (that
leg is the 1/sigma weight, log^2-grade); it is born in the
sigma-integral two-regime cutoff -- GHS Cor 1.2 p.13: split at
sigma* = e^M/log X between the pretentious bound e^{-M} log X and
the trivial bound 1/sigma; verified numerically exact (ratio 1.000).
The (1+M) is genuine and necessary: the tighter pure-e^{-M} bound is
FALSE, and grade_EM's factor 2 is load-bearing.
⟧ SUPERSEDED by AMENDMENT B4 (JYH-ratified 2026-07-23): the (1+M) is
an artifact of the sigma_cutoff two-regime split; the elementary
B-ladder replaces that arm with B3's pretentious cutoff -- the
sigma-uniform bound C(1/sigma)exp(-c D^2(e^{1/sigma})) (c = 1/e),
whose flat integral CONVERGES (2c = 2/e < 1) to <= 3.78 e^{-cM} L
directly, with NO (1+M) accumulation and NO factor-2 collapse. So on
the B-route hRHS re-shapes to C1*X*e^{-cM} (this lemma). The old
sigma_cutoff / joint_grade_assembly arm stays LANDED as heritage. -/
/- ⟦CODA 2026-07-23 (PIN-WAVE)⟧ The two ABSENT hRHS ingredients above are
now PLACED:
 • The MASS half (the integral-representation factoring / window
   cross-integral, `‖prop21RHS‖ ≤ X·supF·crossInt`) LANDED since this
   note -- `prop21RHS_le_head` (this file), `crossKer_grade_decayed`
   (`HeadGrade`), `window_mass_eval` (`GrandComp`).
 • The DECAY half (the four-factor sup `≤ C·e^{-M}`) correctly routes
   NOT through a ∀-t pointwise sup -- the supF-pretentious wall (the
   four-factor does not decay at the twist-trivial frequency;
   GRAND-COMP's structural finding) forbids that -- but through the
   ANNULAR object: the M_range-window L² mass of the seam polynomial,
   `annHead` (`Salt/MR/AnnHead.lean`), graded by `annHead_grade` and
   over-satisfying this bare-X socket via `annHead_le_socket`. -/
theorem T1_head_wire (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ T : ℝ) :
    ∃ X₀ : ℝ, ∀ {X h c₀ y η C₁ : ℝ}, X₀ ≤ X →
        h = X / Real.sqrt (Real.log X) → 1 < c₀ → η = 1 / Real.log y →
        0 < c₀ - 2 * η → 10 ≤ y → y ≤ Real.sqrt X → Real.sqrt (Real.log X) ≤ y →
        ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
          ≤ C₁ * X * Real.exp (-(1 / Real.exp 1)
              * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) →
      ∃ C_E C_R : ℝ,
        ‖∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ)‖
          ≤ C₁ * X * Real.exp (-(1 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
            + (C_E * ((X + h) / Real.log (X + h)) * Real.log y
              + C_R * (X / Real.log X) * Real.log y) := by
  obtain ⟨X₀, hclean⟩ := prop21_unconditional_clean g hg t₀
  refine ⟨X₀, ?_⟩
  intro X h c₀ y η C₁ hXlb hh hc₀ hη hc' hy10 hyX hygate hRHS
  obtain ⟨C_E, C_R, hrep⟩ := hclean hXlb hh hc₀ hη hc' hy10 hyX hygate
  refine ⟨C_E, C_R, ?_⟩
  set S := ∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ) with hS
  set R := prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η with hR
  have hid : R + (S - R) = S := by ring
  have htri : ‖S‖ ≤ ‖R‖ + ‖S - R‖ := by
    calc ‖S‖ = ‖R + (S - R)‖ := by rw [hid]
      _ ≤ ‖R‖ + ‖S - R‖ := norm_add_le _ _
  exact htri.trans (add_le_add hRHS hrep)

end Salt.MR

/-! ## LEG II — the integral factoring (`prop21RHS_le_head`)

The middle leg of the `hRHS` chain (`T1_head_wire`'s named residual).  `prop21RHS`
(`HalaszRepAsm:472`) is the `2·∫₀^η∫₀^η (1/2π)∫_t 𝒮·𝓛·P·P·hatKernel` triple integral
(the frozen GHS Prop-2.1 object, `s = c₀ + (t−t₀)·I`).  This leg FACTORS its norm into
`(explicit constant)·F0·(kernel L¹ mass)·(window coefficient-mass²)`, the honest
interface a downstream bridge combines with (iii-b)'s `(1+M)` decay.

**The socket hypotheses.**  Two analytic inputs are carried as NAMED hypotheses (the
conditional-assembly house form, cf. `contour_A13_A14_head`, `hhead_supplier_trivial`):

* `hsupF` — the four-factor sup `‖𝒮(s−α−β)·𝓛(s+β)‖ ≤ F0` over the `(α,β)∈[0,η]²` box
  (this is the leg-(i) Halász/Euler-product decay `F0 ≍ e^{−M}·L`, scoped separately);
* `hKint` — the kernel L¹ mass `∫_t ‖hatKernel X h (c₀−α−β) (t−t₀)‖ ≤ Kmass`, uniform
  over the box (the bridge supplies the ledger-sharp value; the split-height `Tsplit`
  bookkeeping — `HalaszKernel.tsplit_ledger` — is the bridge's, NOT this leg's).

**The factoring, discharged unconditionally.**  The `𝒮·𝓛` factor is pulled out by
`hsupF`; the two `P`-legs are bounded POINTWISE by their `n^{−c}`-weighted coefficient
mass (`norm_windowSum_le_mass`, retaining the decay leg-(iii) needs), uniformly over
`β∈[0,η]` at the worst-case line `c₀−η`; the kernel is the only `t`-dependent factor, so
its L¹ mass `Kmass` is the sole surviving integral.  The `(α,β)` double integral then
collapses via `intervalIntegral.norm_integral_le_of_norm_le_const` (each level pays a
factor `η`), and the leading `2·(1/2π) = 1/π` assembles the constant.  The window mass
appears SQUARED — exactly the `(Σ‖lambdaLin g‖/nᶜ)²` shape of `k4_plan_le_diag_sharp`. -/

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-- **The window Dirichlet polynomial's `n^{−c}`-weighted coefficient-mass bound.**
`‖windowSum g X y w‖ ≤ ∑_{n∈window} ‖lambdaLin (restrictAbove y g) n‖ / n^a` whenever
`a ≤ Re w`.  Pointwise triangle inequality (`‖n^{−w}‖ = n^{−Re w}`) followed by the
exponent monotonicity `1/n^{Re w} ≤ 1/n^a` (`n ≥ 1`, `a ≤ Re w`).  This RETAINS the
`n^{−c}` decay (the M-independent factor the terminal chain needs); the worst-case line
`a = c₀ − η` makes the bound uniform over the `β`-shift. -/
theorem norm_windowSum_le_mass (g : ℕ → ℂ) (X y a : ℝ) {w : ℂ} (hw : a ≤ w.re) :
    ‖windowSum g X y w‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
          ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ a := by
  unfold windowSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  rw [Finset.mem_Ioo] at hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < n := hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  rw [norm_div, Complex.norm_natCast_cpow_of_pos hnpos]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) a)
    (Real.rpow_le_rpow_of_exponent_le hnR hw)

/-- **LEG II — the integral factoring (`prop21RHS_le_head`).**  The norm of `prop21RHS`
factors into `(η²/π)·F0·Kmass·(window coefficient-mass²)`, where `F0` is the four-factor
`𝒮·𝓛` sup over the `(α,β)∈[0,η]²` box (`hsupF`) and `Kmass` is the kernel's uniform L¹
mass (`hKint`).  The window mass is the `n^{−c}`-weighted `∑_{n∈(y,X/y)}‖lambdaLin
(restrictAbove y g) n‖/n^{c₀−η}` — SQUARED, matching `k4_plan_le_diag_sharp`'s diagonal
shape.  Unconditional in the two carried inputs; the sharp `Kmass ≍ X` (via `Tsplit`) and
the `(1+M)e^{−M}` decay of `F0` are the bridge's, isolating the honest interface

  `‖prop21RHS‖ ≤ (η²/π)·F0·Kmass·(Σ‖lambdaLin (restrictAbove y g)‖/n^{c₀−η})²`.

Composition with `T1_head_wire`: the bridge supplies `hsupF`/`hKint`, obtains this bound,
then via (iii-b)'s `(1+M)` bridge (`k4_plan_le_diag_sharp` → `(1+M)`) and `Kmass ≍ X`
rewrites the RHS to `C₁·X·(1+M)e^{−M}` — exactly `T1_head_wire`'s `hRHS` binder. -/
theorem prop21RHS_le_head {g : ℕ → ℂ} {t₀ X h c₀ y η F0 Kmass : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (hF0 : 0 ≤ F0)
    (hsupF : ∀ α ∈ Set.Icc (0 : ℝ) η, ∀ β ∈ Set.Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ F0)
    (hKint : ∀ α ∈ Set.Icc (0 : ℝ) η, ∀ β ∈ Set.Icc (0 : ℝ) η,
      ∫ t : ℝ, ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ ≤ Kmass) :
    ‖prop21RHS g t₀ X h c₀ y η‖
      ≤ η ^ 2 / Real.pi * F0 * Kmass
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
              ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - η)) ^ 2 := by
  set Sη := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - η) with hSη
  have hSη0 : 0 ≤ Sη := by
    rw [hSη]; exact Finset.sum_nonneg (fun n _ => by positivity)
  -- Per-`(α,β)` inner bound: the `t`-integral's norm ≤ F0·Sη²·Kmass.
  have hInner : ∀ α ∈ Set.Icc (0 : ℝ) η, ∀ β ∈ Set.Icc (0 : ℝ) η,
      ‖∫ t : ℝ, smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀)‖
        ≤ F0 * Sη * Sη * Kmass := by
    intro α hα β hβ
    have hα0 := hα.1; have hαη := hα.2; have hβ0 := hβ.1; have hβη := hβ.2
    have hc : 0 < c₀ - α - β := by linarith
    have hIntg : Integrable
        (fun t : ℝ => F0 * Sη * Sη * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) :=
      (((integrable_hatKernel hX hh hc).comp_sub_right t₀).norm).const_mul (F0 * Sη * Sη)
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      hIntg (Filter.Eventually.of_forall (fun t => ?_))).trans ?_
    · -- pointwise: ‖𝒮·𝓛·P·P·hatK‖ ≤ F0·Sη·Sη·‖hatK‖
      have hP1 : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖ ≤ Sη := by
        rw [hSη]
        exact norm_windowSum_le_mass g X y (c₀ - η)
          (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp];
              linarith)
      have hP2 : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Sη := by
        rw [hSη]
        exact norm_windowSum_le_mass g X y (c₀ - η)
          (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp];
              linarith)
      have hSL := hsupF α hα β hβ t
      dsimp only
      rw [norm_mul, norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine mul_le_mul ?_ hP2 (norm_nonneg _) (mul_nonneg hF0 hSη0)
      exact mul_le_mul hSL hP1 (norm_nonneg _) hF0
    · -- ∫ (F0·Sη·Sη·‖hatK‖) = F0·Sη·Sη·∫‖hatK‖ ≤ F0·Sη·Sη·Kmass
      rw [MeasureTheory.integral_const_mul (F0 * Sη * Sη)
        (fun t : ℝ => ‖hatKernel X h (c₀ - α - β) (t - t₀)‖)]
      exact mul_le_mul_of_nonneg_left (hKint α hα β hβ)
        (mul_nonneg (mul_nonneg hF0 hSη0) hSη0)
  -- Per-`α` middle bound: the `β`-integral's norm ≤ (1/2π)·(F0·Sη²·Kmass)·η.
  have hMid : ∀ α ∈ Set.Icc (0 : ℝ) η,
      ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi)) •
        ∫ t : ℝ, smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀)‖
        ≤ (1 / (2 * Real.pi)) * (F0 * Sη * Sη * Kmass) * η := by
    intro α hα
    have hconst : ∀ β ∈ Set.uIoc (0 : ℝ) η,
        ‖(1 / (2 * Real.pi)) •
          ∫ t : ℝ, smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
            * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
            * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
            * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
            * hatKernel X h (c₀ - α - β) (t - t₀)‖
          ≤ (1 / (2 * Real.pi)) * (F0 * Sη * Sη * Kmass) := by
      intro β hβ
      have hβ' : β ∈ Set.Icc (0 : ℝ) η := by
        rw [Set.uIoc_of_le hη0] at hβ; exact Set.Ioc_subset_Icc_self hβ
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
      exact mul_le_mul_of_nonneg_left (hInner α hα β hβ') (by positivity)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hconst
    rw [sub_zero, abs_of_nonneg hη0] at h1
    exact h1
  -- Outer `α`-integral collapse + the leading `2·(1/2π) = 1/π` assembly.
  have houter : ∀ α ∈ Set.uIoc (0 : ℝ) η,
      ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi)) •
        ∫ t : ℝ, smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀)‖
        ≤ (1 / (2 * Real.pi)) * (F0 * Sη * Sη * Kmass) * η := by
    intro α hα
    have hα' : α ∈ Set.Icc (0 : ℝ) η := by
      rw [Set.uIoc_of_le hη0] at hα; exact Set.Ioc_subset_Icc_self hα
    exact hMid α hα'
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const houter
  rw [sub_zero, abs_of_nonneg hη0] at h2
  simp only [prop21RHS]
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc (2 : ℝ) * ‖∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi)) •
        ∫ t : ℝ, smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
          * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
          * hatKernel X h (c₀ - α - β) (t - t₀)‖
      ≤ 2 * ((1 / (2 * Real.pi)) * (F0 * Sη * Sη * Kmass) * η * η) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = η ^ 2 / Real.pi * F0 * Kmass * Sη ^ 2 := by ring

end Salt.MR

/-! ## STONE 1 — the kernel L¹ mass ledger (`kernel_mass_ledger`)

Discharges `prop21RHS_le_head`'s `hKint` socket at honest depth.  Translation-invariance
(`integral_add_right_eq_self`) drops the `t₀` shift; the DOMINANT (`1/‖s‖²`) branch of
`hat_mellin_bound` bounds `‖hatKernel X h c t‖ ≤ (X+h)^c·2(X+h)/(h(c²+t²))`, and the
full-line Lorentzian mass `∫_ℝ (c²+t²)⁻¹ = π/c` closes the integral.  (`Salt.SW.
integral_inv_sq_add` sits in `SW/ShiftAssembly`, OUTSIDE `HExit`'s import cone, so its
short pure-mathlib proof is replicated inline in `kernel_L1_mass`.)

**Grade honestly achieved.**  `Kmass ≍ (X+h)^{c₀}·(2(X+h)/h)·(π/(c₀−2η))`.  At the
frozen `h = X·L^{−1/2}`, `c₀ = 1+1/L` (#253) this is `X·√L`-grade — the CRUDE mass.  The
`Tsplit`-truncated refinement to `X·log L`-grade (branch-1 `2(X+h)^c/√(c²+t²)` on
`|t| ≤ Tsplit` via an `arcsinh`/`Real.arsinh` interval-integral, plus `hat_tail` — landed
— for the `|t| > Tsplit` tail at `X·L^{−7/2}`) is NOT landed: the `arcsinh` main-part
evaluation is absent from the corpus.  So the crude branch-2 form lands; the sharp `Kmass
≍ X` (which would need the arcsinh piece and still carries a `log L`) remains the bridge's. -/

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-- **The seam kernel's full-line L¹ mass (crude branch-2 form).**  Per-line value:
`∫_t ‖hatKernel X h c (t−t₀)‖ ≤ (X+h)^c·(2(X+h)/h)·(π/c)`.  Route: translation-invariance
drops `t₀`; the dominant branch of `hat_mellin_bound` dominates by `(X+h)^c·(2(X+h)/
(h(c²+t²)))`; `∫_ℝ (c²+t²)⁻¹ = π/c` (Lorentzian mass, replicated inline). -/
theorem kernel_L1_mass {X h c t₀ : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) :
    ∫ t : ℝ, ‖hatKernel X h c (t - t₀)‖
      ≤ (X + h) ^ c * (2 * (X + h) / h) * (Real.pi / c) := by
  have hXh0 : (0 : ℝ) < X + h := by linarith
  set A : ℝ := (X + h) ^ c * (2 * (X + h) / h) with hA
  -- the Lorentzian mass π/c (ShiftAssembly.integral_inv_sq_add, replicated: that lemma is
  -- outside HExit's import cone; the proof is pure mathlib)
  have hpois : (∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹) = Real.pi / c := by
    have hcne : c ≠ 0 := hc.ne'
    have hpt' : (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹)
        = fun t : ℝ => (c ^ 2)⁻¹ * (1 + (t / c) ^ 2)⁻¹ := by
      funext t; rw [div_pow, ← mul_inv]; congr 1; field_simp
    have hcomp : (∫ t : ℝ, (1 + (t / c) ^ 2)⁻¹) = |c| • ∫ u : ℝ, (1 + u ^ 2)⁻¹ :=
      MeasureTheory.Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) c
    rw [hpt', MeasureTheory.integral_const_mul, hcomp, integral_univ_inv_one_add_sq,
      smul_eq_mul, abs_of_pos hc]
    field_simp
  -- pointwise domination by the dominant branch of `hat_mellin_bound`
  have hpt : ∀ t : ℝ, ‖hatKernel X h c t‖ ≤ A * (c ^ 2 + t ^ 2)⁻¹ := by
    intro t
    have hnorm : ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
      rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    have hb := hat_mellin_bound hX hh hc t
    have hXhc : (0 : ℝ) ≤ (X + h) ^ c := Real.rpow_nonneg hXh0.le _
    calc ‖hatKernel X h c t‖
        ≤ (X + h) ^ c * min (2 / ‖(c : ℂ) + (t : ℂ) * I‖)
            (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := hb
      _ ≤ (X + h) ^ c * (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := by
          gcongr; exact min_le_right _ _
      _ = A * (c ^ 2 + t ^ 2)⁻¹ := by
          rw [hnorm, hA]
          have hct : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
          field_simp
  have hIntKs : Integrable (fun t : ℝ => ‖hatKernel X h c t‖) :=
    (integrable_hatKernel hX hh hc).norm
  have hIntg : Integrable (fun t : ℝ => A * (c ^ 2 + t ^ 2)⁻¹) :=
    (Salt.SW.integrable_inv_c_sq_add_sq hc).const_mul A
  have htrans : ∫ t : ℝ, ‖hatKernel X h c (t - t₀)‖ = ∫ t : ℝ, ‖hatKernel X h c t‖ := by
    have hsr := integral_add_right_eq_self (μ := volume) (fun t : ℝ => ‖hatKernel X h c t‖) (-t₀)
    simpa [sub_eq_add_neg] using hsr
  rw [htrans]
  calc ∫ t : ℝ, ‖hatKernel X h c t‖
      ≤ ∫ t : ℝ, A * (c ^ 2 + t ^ 2)⁻¹ := integral_mono hIntKs hIntg hpt
    _ = A * ∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹ :=
        MeasureTheory.integral_const_mul A (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹)
    _ = A * (Real.pi / c) := by rw [hpois]

/-- **STONE 1 — `hKint` discharged (box-uniform crude mass).**  Directly the
`prop21RHS_le_head` kernel socket: uniform over the `(α,β) ∈ [0,η]²` box, at the
worst-case line `c = c₀−α−β ∈ [c₀−2η, c₀]` (numerator `(X+h)^c` increasing, reciprocal
`π/c` decreasing),

  `∫_t ‖hatKernel X h (c₀−α−β) (t−t₀)‖ ≤ (X+h)^{c₀}·(2(X+h)/h)·(π/(c₀−2η))  =: Kmass`.

Plug as `prop21RHS_le_head`'s `hKint` with this `Kmass` (the honest crude `X√L`-grade). -/
theorem kernel_mass_ledger {X h c₀ η t₀ : ℝ} (hX : 1 ≤ X) (hh : 0 < h)
    (hc2η : 0 < c₀ - 2 * η) :
    ∀ α ∈ Set.Icc (0 : ℝ) η, ∀ β ∈ Set.Icc (0 : ℝ) η,
      ∫ t : ℝ, ‖hatKernel X h (c₀ - α - β) (t - t₀)‖
        ≤ (X + h) ^ c₀ * (2 * (X + h) / h) * (Real.pi / (c₀ - 2 * η)) := by
  intro α hα β hβ
  obtain ⟨hα0, hαη⟩ := hα
  obtain ⟨hβ0, hβη⟩ := hβ
  have hc : 0 < c₀ - α - β := by linarith
  have hXh1 : (1 : ℝ) ≤ X + h := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  refine (kernel_L1_mass hX hh hc).trans ?_
  have hcle : c₀ - α - β ≤ c₀ := by linarith
  have h2η : c₀ - 2 * η ≤ c₀ - α - β := by linarith
  have hrpow : (X + h) ^ (c₀ - α - β) ≤ (X + h) ^ c₀ :=
    Real.rpow_le_rpow_of_exponent_le hXh1 hcle
  have hpi : Real.pi / (c₀ - α - β) ≤ Real.pi / (c₀ - 2 * η) :=
    div_le_div_of_nonneg_left Real.pi_pos.le hc2η h2η
  have hfac : (0 : ℝ) ≤ 2 * (X + h) / h := div_nonneg (by linarith) hh.le
  have hpi0 : (0 : ℝ) ≤ Real.pi / (c₀ - α - β) := (div_pos Real.pi_pos hc).le
  calc (X + h) ^ (c₀ - α - β) * (2 * (X + h) / h) * (Real.pi / (c₀ - α - β))
      ≤ (X + h) ^ c₀ * (2 * (X + h) / h) * (Real.pi / (c₀ - α - β)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrpow hfac) hpi0
    _ ≤ (X + h) ^ c₀ * (2 * (X + h) / h) * (Real.pi / (c₀ - 2 * η)) :=
        mul_le_mul_of_nonneg_left hpi (mul_nonneg (Real.rpow_nonneg hXh0.le c₀) hfac)

/-! ## STONE 2 — the `(1+M)` two-regime σ-cutoff (`sigma_cutoff`)

The self-contained socket for the `σ`-integral that BIRTHS the `(1+M)` factor of the
`hRHS` funnel (GHS Cor 1.2 p.13; cf. the 2026-07-22 CORRECTION comment above
`T1_head_wire`).  Given an abstract nonneg `Fbound` with the two leg-(i) F-sockets — the
pretentious bound `Fbound σ ≤ e^{−M}·L` and the trivial bound `Fbound σ ≤ 1/σ` on
`[1/L, 2η]` — the weighted integral splits at `σ* = e^M/L`:

* FLAT regime `[1/L, σ*]`: `Fbound σ/σ ≤ e^{−M}L·σ⁻¹`, integrating to `e^{−M}L·log(σ*L)
  = e^{−M}L·M` (as `σ*L = e^M`, `log(e^M) = M`);
* TAIL regime `[σ*, 2η]`: `Fbound σ/σ ≤ (σ²)⁻¹`, integrating to `σ*⁻¹ − (2η)⁻¹ ≤ σ*⁻¹
  = L·e^{−M}`.

Sum `= (1+M)e^{−M}L` (so the honest constant is `C = 1`).  The corner `e^M/L > 2η` (where
the flat regime already covers `[1/L, 2η]`) is handled by the top-level case split.  Pure
interval-integral real analysis; zero number theory. -/

/-- **STONE 2 — the `(1+M)` σ-cutoff.**  For `L ≥ 3`, `M ≥ 0`, `1/L ≤ 2η`, an abstract
`Fbound` (weighted term `Fbound σ/σ` interval-integrable on `[1/L, 2η]`) obeying the two
F-sockets `hpret` (`≤ e^{−M}L`) and `htriv` (`≤ 1/σ`) on `[1/L, 2η]`:

  `∫_{1/L}^{2η} Fbound σ/σ dσ ≤ (1 + M)·e^{−M}·L`  (honest constant `C = 1`).

The two-regime split at `σ* = e^M/L`: the flat piece contributes `e^{−M}L·M`, the tail
piece `L·e^{−M}`.  Leg (i) plugs `Fbound = ‖𝒮·𝓛‖` (or its box-sup) into the sockets. -/
theorem sigma_cutoff {L M η : ℝ} (Fbound : ℝ → ℝ)
    (hL : 3 ≤ L) (hM : 0 ≤ M) (hlo : 1 / L ≤ 2 * η)
    (hint : IntervalIntegrable (fun σ => Fbound σ / σ) MeasureTheory.volume (1 / L) (2 * η))
    (hpret : ∀ σ ∈ Set.Icc (1 / L) (2 * η), Fbound σ ≤ Real.exp (-M) * L)
    (htriv : ∀ σ ∈ Set.Icc (1 / L) (2 * η), Fbound σ ≤ 1 / σ) :
    (∫ σ in (1 / L)..(2 * η), Fbound σ / σ) ≤ (1 + M) * Real.exp (-M) * L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have heML0 : (0 : ℝ) ≤ Real.exp (-M) * L := by positivity
  -- flat-regime value: `∫_a^b Fbound σ/σ ≤ e^{−M}L·log(b/a)` on any subinterval away from 0
  have flat : ∀ a b : ℝ, 0 < a → a ≤ b → Set.Icc a b ⊆ Set.Icc (1 / L) (2 * η) →
      (∫ σ in a..b, Fbound σ / σ) ≤ Real.exp (-M) * L * Real.log (b / a) := by
    intro a b ha hab hsub
    have h0uIcc : (0 : ℝ) ∉ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab, Set.mem_Icc]; rintro ⟨h0, _⟩; linarith
    have hsub' : Set.uIcc a b ⊆ Set.uIcc (1 / L) (2 * η) := by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hlo]; exact hsub
    have hIntF : IntervalIntegrable (fun σ => Fbound σ / σ) MeasureTheory.volume a b :=
      hint.mono_set hsub'
    have hcont : ContinuousOn (fun σ : ℝ => Real.exp (-M) * L * σ⁻¹) (Set.uIcc a b) := by
      have h0 : ∀ σ ∈ Set.uIcc a b, σ ≠ 0 := by
        intro σ hσ
        rw [Set.uIcc_of_le hab, Set.mem_Icc] at hσ
        exact (lt_of_lt_of_le ha hσ.1).ne'
      exact continuousOn_const.mul (continuousOn_id.inv₀ h0)
    have hIntb : IntervalIntegrable (fun σ : ℝ => Real.exp (-M) * L * σ⁻¹)
        MeasureTheory.volume a b := hcont.intervalIntegrable
    have hmono : (∫ σ in a..b, Fbound σ / σ)
        ≤ ∫ σ in a..b, Real.exp (-M) * L * σ⁻¹ := by
      apply intervalIntegral.integral_mono_on hab hIntF hIntb
      intro σ hσ
      have hσpos : (0 : ℝ) < σ := lt_of_lt_of_le ha hσ.1
      have hFb := hpret σ (hsub hσ)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hFb (by positivity)
    have hval : (∫ σ in a..b, Real.exp (-M) * L * σ⁻¹)
        = Real.exp (-M) * L * Real.log (b / a) := by
      rw [intervalIntegral.integral_const_mul, integral_inv h0uIcc]
    rw [hval] at hmono
    exact hmono
  rcases le_total (2 * η) (Real.exp M / L) with hcorner | hmain
  · -- CORNER `2η ≤ e^M/L`: flat bound covers `[1/L, 2η]`
    have hbase := flat (1 / L) (2 * η) hLinv0 hlo subset_rfl
    have hdiv : (2 * η) / (1 / L) = 2 * η * L := by rw [div_div_eq_mul_div, div_one]
    rw [hdiv] at hbase
    have h2ηpos : (0 : ℝ) < 2 * η := lt_of_lt_of_le hLinv0 hlo
    have h2ηL_pos : (0 : ℝ) < 2 * η * L := mul_pos h2ηpos hL0
    have h2ηL_le : 2 * η * L ≤ Real.exp M := by
      calc 2 * η * L ≤ (Real.exp M / L) * L := mul_le_mul_of_nonneg_right hcorner hL0.le
        _ = Real.exp M := div_mul_cancel₀ _ hL0.ne'
    have hlogle : Real.log (2 * η * L) ≤ M := by
      have h := Real.log_le_log h2ηL_pos h2ηL_le
      rwa [Real.log_exp] at h
    calc (∫ σ in (1 / L)..(2 * η), Fbound σ / σ)
        ≤ Real.exp (-M) * L * Real.log (2 * η * L) := hbase
      _ ≤ Real.exp (-M) * L * M := mul_le_mul_of_nonneg_left hlogle heML0
      _ ≤ (1 + M) * Real.exp (-M) * L := by
          have hid : (1 + M) * Real.exp (-M) * L
              = Real.exp (-M) * L * M + Real.exp (-M) * L := by ring
          rw [hid]; linarith [heML0]
  · -- MAIN `e^M/L ≤ 2η`: split at `s = e^M/L`
    set s : ℝ := Real.exp M / L with hs_def
    have hs_pos : (0 : ℝ) < s := by rw [hs_def]; positivity
    have hexpM_ge : (1 : ℝ) ≤ Real.exp M := Real.one_le_exp hM
    have h1Ls : 1 / L ≤ s := by
      rw [hs_def]; exact div_le_div_of_nonneg_right hexpM_ge hL0.le
    have hs2η : s ≤ 2 * η := hmain
    have hsub1 : Set.uIcc (1 / L) s ⊆ Set.uIcc (1 / L) (2 * η) := by
      rw [Set.uIcc_of_le h1Ls, Set.uIcc_of_le hlo]
      exact Set.Icc_subset_Icc_right hs2η
    have hIntF1 : IntervalIntegrable (fun σ => Fbound σ / σ) MeasureTheory.volume (1 / L) s :=
      hint.mono_set hsub1
    have hsub2 : Set.uIcc s (2 * η) ⊆ Set.uIcc (1 / L) (2 * η) := by
      rw [Set.uIcc_of_le hs2η, Set.uIcc_of_le hlo]
      exact Set.Icc_subset_Icc_left h1Ls
    have hIntF2 : IntervalIntegrable (fun σ => Fbound σ / σ) MeasureTheory.volume s (2 * η) :=
      hint.mono_set hsub2
    have hsplit : (∫ σ in (1 / L)..(2 * η), Fbound σ / σ)
        = (∫ σ in (1 / L)..s, Fbound σ / σ) + ∫ σ in s..(2 * η), Fbound σ / σ :=
      (intervalIntegral.integral_add_adjacent_intervals hIntF1 hIntF2).symm
    -- REGION 1 (flat): `≤ e^{−M}L·M`
    have hR1 : (∫ σ in (1 / L)..s, Fbound σ / σ) ≤ Real.exp (-M) * L * M := by
      have hf1 := flat (1 / L) s hLinv0 h1Ls (Set.Icc_subset_Icc_right hs2η)
      have hsL : s / (1 / L) = Real.exp M := by
        rw [hs_def, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hL0.ne']
      rw [hsL, Real.log_exp] at hf1
      exact hf1
    -- REGION 2 (tail): `≤ L·e^{−M}`
    have hIntb2 : IntervalIntegrable (fun σ : ℝ => (σ ^ 2)⁻¹) MeasureTheory.volume s (2 * η) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀ (continuousOn_pow 2)
      intro σ hσ
      rw [Set.uIcc_of_le hs2η, Set.mem_Icc] at hσ
      exact pow_ne_zero 2 (lt_of_lt_of_le hs_pos hσ.1).ne'
    have hR2mono : (∫ σ in s..(2 * η), Fbound σ / σ) ≤ ∫ σ in s..(2 * η), (σ ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on hs2η hIntF2 hIntb2
      intro σ hσ
      have hσpos : (0 : ℝ) < σ := lt_of_lt_of_le hs_pos hσ.1
      have hFb := htriv σ ⟨le_trans h1Ls hσ.1, hσ.2⟩
      rw [div_eq_mul_inv]
      calc Fbound σ * σ⁻¹ ≤ (1 / σ) * σ⁻¹ := mul_le_mul_of_nonneg_right hFb (by positivity)
        _ = (σ ^ 2)⁻¹ := by rw [one_div, ← mul_inv, ← pow_two]
    have hR2val : (∫ σ in s..(2 * η), (σ ^ 2)⁻¹) = s⁻¹ - (2 * η)⁻¹ := by
      have hderiv : ∀ σ ∈ Set.uIcc s (2 * η), HasDerivAt (fun x => -x⁻¹) ((σ ^ 2)⁻¹) σ := by
        intro σ hσ
        rw [Set.uIcc_of_le hs2η, Set.mem_Icc] at hσ
        have hσne : σ ≠ 0 := (lt_of_lt_of_le hs_pos hσ.1).ne'
        have hd := (hasDerivAt_inv hσne).neg
        rw [neg_neg] at hd
        exact hd
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntb2
      rw [hftc]; ring
    have hsinv : s⁻¹ = L * Real.exp (-M) := by
      rw [hs_def, inv_div, Real.exp_neg, div_eq_mul_inv]
    have hR2 : (∫ σ in s..(2 * η), Fbound σ / σ) ≤ L * Real.exp (-M) := by
      have h1 : (∫ σ in s..(2 * η), Fbound σ / σ) ≤ s⁻¹ - (2 * η)⁻¹ := hR2mono.trans_eq hR2val
      have h2ηpos : (0 : ℝ) < 2 * η := lt_of_lt_of_le hs_pos hs2η
      have h2ηnn : (0 : ℝ) ≤ (2 * η)⁻¹ := inv_nonneg.mpr h2ηpos.le
      calc (∫ σ in s..(2 * η), Fbound σ / σ) ≤ s⁻¹ - (2 * η)⁻¹ := h1
        _ ≤ s⁻¹ := by linarith
        _ = L * Real.exp (-M) := hsinv
    rw [hsplit]
    have heq : Real.exp (-M) * L * M + L * Real.exp (-M) = (1 + M) * Real.exp (-M) * L := by ring
    linarith [hR1, hR2, heq]

end Salt.MR

/-! ## SF-EXIT / J3 — the JOINT grade assembly and the T1-decay frontier

The joint-head route's terminal composition (design: `docs/exploration/supf-design.md`,
⟦JOINT-SCOPE VERDICT⟧, J3).  J1/J2 (`Salt.MR.JointHead`) deliver the σ-live bound
`‖prop21RHS‖ ≤ (1/π)·∫∫ supF·crossKer` and the per-`α` σ-cutoff `∫β supF·crossKer ≤
Kα·(1+M)e^{−M}L`.  J3 assembles the grade (the α-integral supplies the `1/L` that cancels
the σ-cutoff's `L`, per `HalaszSeam`'s LEDGER: `X·(1+M)e^{−M}·L^{κ−1} = X·(1+M)e^{−M}`),
discharges `T1_head_wire`'s `hRHS` binder, and reaches the seam-sum head bound — the prize:
`hRHS` discharged via the joint route.

**The grade page (written before Lean, per the design law).**  With `L := log X`,
`h = X·L^{−1/2}`, `c₀ = 1+1/L`, kernel scale `(X+h)^{c₀−α−β}·2(X+h)/h ≍ X·√L` (crude
`kernel_mass_ledger`) or `≍ X` (the `Tsplit`-sharp `arcsinh` refinement, the bridge's):
`‖prop21RHS‖ ≤ (1/π)∫₀^η∫₀^η supF·crossKer`  [J1]
  `≤ (1/π)∫₀^η Kα·(1+M)e^{−M}L dα`  [J2, per α; `σ = β+1/L`]
  `= (1/π)·(1+M)e^{−M}L·∫₀^η Kα dα`  [const pull]
  `≤ (1/π)·(1+M)e^{−M}L·(C·X/L)`  [α-integral: `∫₀^η X^{1−α}dα ≤ X/L` — the crucial `1/L`]
  `= (C/π)·X·(1+M)e^{−M}`.
So `Agrade := (1/π)·L·∫₀^η Kα dα ≤ C₁·X` is the ONE grade socket; the `L` from the
σ-cutoff and the `1/L` from the α-integral cancel EXACTLY (`κ=1`, LEDGER PASSES). No
log-power gap: `Agrade ≤ C₁·X` is at grade iff the kernel-scale α-integral is `X/L`-grade,
which the crude `X·√L` mass overshoots by `√L·L = L^{3/2}` — the KNOWN excess absorbed by
the `Tsplit`/`arcsinh` sharpening (the bridge's residual, flagged in `kernel_mass_ledger`).

The residual hypothesis set of the frontier (enumerated on `T1_decay_conditional_final`):
the joint bound `hjoint` (J1∘J2∘α-integral, itself resting on `supF`'s pretentious socket
`hpret` and the mixed-line bridge `hbridge`), the grade socket `hgrade` (`Agrade ≤ C₁X`,
the `Tsplit`-sharp kernel mass), and `T1_decay_trivial`'s standard binders (`hsplit`,
`htail`, `hfloor`, and `hhead` — the §8 `int_U`/moment routing of the seam sum into
`Uhead`, out of this leg's scope). -/

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-- **J3 stone 1 — `hRHS` discharged from the joint route (`hRHS_discharged_joint`).**  The
joint grade bound `hjoint` (`‖prop21RHS‖ ≤ Agrade·e^{−cM}`, the B-ladder's J1∘J2∘α-integral)
plus the grade socket `hgrade` (`Agrade ≤ C₁·X`, the kernel-scale α-integral `≍ X/L` after the
`L` from the pretentious cutoff cancels) yield exactly `T1_head_wire`'s `hRHS` binder shape at
the `M_range` (J0) datum.  `M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T`.

**AMENDMENT B4 (JYH-ratified 2026-07-23).**  `hjoint`/conclusion re-frozen from
`Agrade·(1+M)e^{−M}` / `C₁·X·(1+M)e^{−M}` to the elementary B-route `·e^{−cM}` shape
(`c = 1/Real.exp 1`): the B-ladder's B3 pretentious cutoff replaces the `sigma_cutoff` arm,
producing `C·e^{−cM}·L` with no `(1+M)` accumulation.  `_hM0` is now vestigial (the shape is
`Real.exp_nonneg`, no `0 ≤ 1+M` needed) but retained for interface stability.  The old
`sigma_cutoff`/`joint_grade_assembly` `(1+M)` arm stays LANDED as heritage. -/
theorem hRHS_discharged_joint {g : ℕ → ℂ} {t₀ X h c₀ y η T Agrade C₁ : ℝ}
    (_hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
    (hjoint : ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
        ≤ Agrade * Real.exp (-(1 / Real.exp 1)
            * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T))
    (hgrade : Agrade ≤ C₁ * X) :
    ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
      ≤ C₁ * X * Real.exp (-(1 / Real.exp 1)
          * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) :=
  hjoint.trans (mul_le_mul_of_nonneg_right hgrade (Real.exp_nonneg _))

/-- **J3 stone 2 — the seam-sum head bound via the joint route (`T1_head_supplied_joint`).**
Composes `hRHS_discharged_joint` with the landed `T1_head_wire`: once the joint grade bound
`hjoint` + the grade socket `hgrade` discharge `hRHS`, `T1_head_wire` delivers the seam
sum's head bound `C₁·X·e^{−cM} + E` UNCONDITIONALLY in those two joint sockets.  **This
is the prize: `hRHS` discharged through the σ-live joint head** (the box-collapse's fatal
defect repaired).  `M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T`.  (AMENDMENT B4,
JYH-ratified 2026-07-23: the `e^{−cM}` shape, `c = 1/e`, tracking `hRHS_discharged_joint`.) -/
theorem T1_head_supplied_joint (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ T : ℝ) :
    ∃ X₀ : ℝ, ∀ {X h c₀ y η C₁ Agrade : ℝ}, X₀ ≤ X →
        h = X / Real.sqrt (Real.log X) → 1 < c₀ → η = 1 / Real.log y →
        0 < c₀ - 2 * η → 10 ≤ y → y ≤ Real.sqrt X → Real.sqrt (Real.log X) ≤ y →
        0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
        ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
            ≤ Agrade * Real.exp (-(1 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) →
        Agrade ≤ C₁ * X →
      ∃ C_E C_R : ℝ,
        ‖∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ)‖
          ≤ C₁ * X * Real.exp (-(1 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
            + (C_E * ((X + h) / Real.log (X + h)) * Real.log y
              + C_R * (X / Real.log X) * Real.log y) := by
  obtain ⟨X₀, hwire⟩ := T1_head_wire g hg t₀ T
  refine ⟨X₀, ?_⟩
  intro X h c₀ y η C₁ Agrade hXlb hh hc₀ hη hc' hy10 hyX hygate hM0 hjoint hgrade
  exact hwire hXlb hh hc₀ hη hc' hy10 hyX hygate
    (hRHS_discharged_joint hM0 hjoint hgrade)

/-- **J3 stone 3 — the T1-decay frontier (`T1_decay_conditional_final`).**  The terminal
statement: the `≪ X·(log X)^{−1/(32e)+o(1)}` decay of the ball contribution `U` for the FULL
twisted seam datum, at the `M_range` (J0) distance, conditional on the ENUMERATED residual
set (AMENDMENT B4, JYH-ratified 2026-07-23: the grade re-frozen to `hhead` in the `e^{−cM}`
shape / conclusion `(log X)^{−c/32}`, `c = 1/e`, coefficient `C₁ + C₂`).  The joint head
(J1/J2 + `T1_head_supplied_joint`) discharges `hRHS` and delivers the
seam-sum head bound; the remaining inputs are `T1_decay_trivial`'s standard binders —
`hsplit` (the ball head/tail split), `htail` (`s2_tail_ledger`, landed), `hfloor` (the R3.1
`(1/32)loglog` floor, `Mrange_one_floor`-backed), and `hhead` (the §8 `int_U`/moment
routing of the seam-sum head bound into `Uhead`, out of this leg's scope: the pointwise `E`
is main-term-sized when `log y ≍ log X`, only its ball-`L²` mass is tail-grade).

**Remaining hypothesis set (the honest frontier).**  Modulo `T1_decay_trivial`'s standard
binders, the SOLE joint-route residuals are: `supF`'s pretentious socket (`hpret` in
`sigma_wiring`, SupF's general-`g` distance split — PENDING at `σ > 1/L`), the mixed-line
Plancherel bridge (`hbridge` in `sigma_wiring` — the flagged medium risk, a genuinely new
three-line variant), and the grade socket (`hgrade` — the `Tsplit`-sharp kernel mass `≍ X`,
the `arcsinh` refinement flagged in `kernel_mass_ledger`).  Everything else is landed. -/
theorem T1_decay_conditional_final {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t T X ε U Uhead Utail C₁ C₂ : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X
        * Real.exp (-(1 / Real.exp 1) * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2))
    (hfloor : (1 / 32) * Real.log (Real.log X)
        ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) :
    U ≤ (C₁ + C₂) * X *
        ((Real.log X) ^ (-(1 / Real.exp 1) / 32) + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) :=
  T1_decay_trivial (ellLin_norm_le_one g hg) t₀ t hX hε hC₁ hC₂ hsplit hhead htail hfloor

end Salt.MR
