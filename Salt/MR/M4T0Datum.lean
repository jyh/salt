/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4DoorRow
import Salt.MR.CofactorSupplier

/-!
# `M4T0Datum` — THE `T₀`-BAND DATUM SUPPLIER AT THE DOOR'S SIEVED χ-TWISTED DATUM

`M4DoorRow`'s ⟦THE `T₀`-BAND, NAMED⟧ recorded the last analytic item of the door row: no
landed supplier reaches `M4MeanSq.m4_meansq_per_chi_gen`'s `hT0band` slot at the door datum

  `a = winCutH X_d (doorChiCoeff χ M)`,   `doorChiCoeff χ M = 1_𝒮·λχ̄` (UN-PHASED),

because `M4Seam.m4_hT0band_at_row` needs the deleted `blockOmega P P`-support pin and
`M4MeanSq.m4_t0band_of_live` needs agreement with the UNSIEVED seam coefficient (the A2-5
clash).  The only open route is `M4Seam.cfb_t0band_supply_of_sup` at a CARRIED per-frequency
polynomial sup

  `hsup : ∀ |t| ≤ seamT0 X, ∀ m ≤ N, ‖spolyA a t m‖ ≤ S·m`,

and this file supplies it — the supplier genre's THIRD performance (after
`CofactorSupplier`'s socket and `CaseAWide`'s wide centre), at the SAME four-piece split.

## THE ROUTE, PIECE BY PIECE

1. **§1 — the split rides through the cut.**  `CofactorSupplier.doorCofactor0_split` at the
   shift `Ps := 1` (`M4DoorRow.doorCofactor0_door_eq`) writes `doorChiCoeff χ M` as the signed
   sum of the `2² = 4` completely multiplicative pieces `λχ̄·g_𝒥`, `𝒥 ⊆ [1,2]`, with
   unimodular coefficients.  ⟦THE CUT COMMUTES⟧: `winCutH` is multiplication by the indicator
   `1_{(X_d,2X_d]}`, and multiplication by a scalar distributes over the finite sum
   POINTWISE — so the cut datum is the same signed sum of the CUT pieces
   (`winCutH_doorChiCoeff_split`).  No hypothesis is needed; the identity is at every `n`.
2. **§2 — `spolyA` is linear in its coefficient slot** (`spolyA_sum_finset`, the twin of
   `CofactorSupplier.ramR_sum_finset`), so the door's polynomial sup is `4×` the pieces'
   (`norm_spolyA_of_pieces`).
3. **§3 — the per-piece sup at the HALF-OPEN cut** (`cfb_sup_of_center_cut`).
   `T0BandCapFree.cfb_sup_of_center` asks its datum to agree with the centre datum on ALL of
   `n > X`; the half-open cut agrees only on `(X_d, 2X_d]`.  On the live range that costs
   nothing: `spolyA a t m` reads `n ≤ m ≤ N ≤ 2X_d`, so the re-cut is `BallSup.spolyA_datum_split`
   with the top end supplied by `N ≤ 2X_d` instead of by a datum hypothesis.
4. **§4 — the piece's centre bound** (`piece_center_of_inner`): `SPartStation.hCenter_dissected`
   (Route III, `cSq = 20736` explicit) at `F := pieceDatum χ 𝒥`, `t₀ = 0`.  The piece is
   COMPLETELY multiplicative (`pieceDatum_mul`, no coprimality) hence multiplicative in
   mathlib's sense (`pieceDatum_isMultiplicative`), and `1`-bounded — the two binders Route III
   reads.  ⟦THE UNDAMPED PIECE⟧: `CofactorSupplier` §8's `caseA_dissect_gen` is the same page at
   the DAMPED datum `b·x^{ω}`; it is NOT specialisable here, because `dampDatum b P Q x` at
   `x = 1` is `b` only on the nose (`dampDatum b P Q 1 = b`, `one_pow`) while the CONSUMER
   `caseASocketGen_of_inner` binds `x` over `[0,1]` through `CaseASocketGen` and carries a
   `cofactorMfl` floor the band does not have.  The piece is fed to `hCenter_dissected`
   DIRECTLY — one call, no damping page.
5. **§5 — the inner sums** (`piece_center_of_wide`): `CaseAWide.center_halasz_supply_wideA`
   at the datum `g := pieceDatum χ 𝒥` and the centre `t₀ := 0`, `t₁ := t`.  ⟦THE HOIST IS
   WHAT MAKES THIS COMPOSE⟧ — the `∃X₀` sits BEFORE the datum, so ONE threshold serves all
   four pieces at once (a per-piece `X₀(𝒥)` would need a `max` over the powerset; available,
   but the hoist makes it free).  The dilated window `[X_w, 2X]` is entered exactly as
   `SPartStation.seam_ball_leg_station_M_gen` does it: the gate `D·(X_w+1) ≤ X−1` puts every
   `⌊k/d⌋`, `d ≤ D`, above `X_w`.
6. **§6 — the assembly** (`m4_t0datum_sup`): the `hsup` binder at the door datum, at the grade
   `8·S₀` (`4` pieces × the cut's factor `2`).
7. **§7 — the slot** (`m4_hT0band_at_door`): `M4Seam.cfb_t0band_supply_of_sup` composed, i.e.
   `m4_meansq_per_chi_gen`'s `hT0band` slot at `C₁′ = cfbC₁ X C₁`, at the door datum.
8. **§8 — the band floor at the piece** (`band_floor_M0_pieceDatum`), the input the `hRHS`
   binder of §5 is priced against.  ⟦THE U1 PRICING HOOK⟧ the mask debit does not change the
   SHAPE of `M₀`: `cfbM0 K q X − D = cfbM0 (K + D) q X` (`cfbM0_add_debit`), so the floor at
   the masked piece is still `cfbM0`-shaped and `M4WaveClosed.m4_rawMS_priced_decay`'s route
   stays reachable at the shifted constant.  At the door's own ladder the debit is `X`-FREE
   (`CofactorSupplier.blockWindow_calibrated_debit_sum` at `J = 2`), which is what keeps the
   shifted constant regime-absorbable.

## WHAT IS CARRIED, AND WHY

Nothing here is proved about the door's arithmetic beyond what is already landed.  The gates
carried symbolically, in the order they appear:

* `hSle` — the grade comparison `8·S₀ ≤ 2(C₁·e^{−M₀/2e} + 4(log X)^{−1/2+1/1000})` and `hErr`,
  both verbatim from `cfb_t0band_supply_of_sup` (§7);
* the wide supply's four `Y`-gates and its `hRHS` at the piece, and the dissection gates
  `1 ≤ D`, `√X ≤ X_w`, `D·(X_w+1) ≤ X−1` (§5) — all `SPartStation`'s own;
* the floor's threshold and the mask debit bound (§8), both `X`-free at the door's ladder.

**No constant is a numeral chosen here.**  `cSq = 20736` is Route III's, `cfbC₁`/`cfbM0` are
`T0BandCapFree`'s, and the `8 = 4×2` is the powerset card times the cut's split.

## ⚠ ⟦THE PRICING RESIDUE, NAMED⟧ — the `hRHS` binder's two floors

§5's `hRHS` is carried at a FREE `B`.  A consumer must price it, and the corpus's landed
pricer is `SPartStation.dilated_scale_grade` — datum-generic (`hg : ∀ p prime, ‖g p‖ ≤ 1`), so
it DOES apply at the piece verbatim.  What it costs is a wider floor: its `hM₀` binder asks

  `∀ |v| ≤ Rad, M₀ ≤ 𝔻²(ℓ(g), n^{iv}; X)`,   `Rad ≥ |t₁| + Tstar(k, log k)`,

and `FarStar.Tstar k L = L⁴·k^{1/(4 log L)}` at `k ≍ X` is `X^{o(1)}` — incomparably wider
than the band's own `|v| ≤ 2·seamT0 X + 1 = 2(log X)^{1/45} + 1`.  So the two floors available
at the piece sit on different ranges:

| floor | range | coefficient | landed as |
|---|---|---|---|
| band | `|v| ≤ 2·seamT0 X + 1` | `7/30` less the mask debit | §8 (`band_floor_M0_pieceDatum`) |
| box | `|v| ≤ 3X` (covers `Tstar`) | `1/32` less the mask debit | `capFreeFloor3_pieceDatum` |

The dissection is FORCED here — the door's datum is completely multiplicative but NOT
squarefree-linearised, so Route III is the only way into `ellLin`'s landed supply — and the
dissection's pricer reads the BOX range.  ⚠ The design arithmetic (NOT kernel-checked; the
theorems below carry the gate symbolically and choose nothing): `T0BandCapFree`'s own header
records that the box's `1/32 = 0.03125` is `6×` SHORT of the exit's decay gate
`(103/1500)·e ≈ 0.18665`, so a consumer that prices `B` through `dilated_scale_grade` gets an
`M₀` at box strength and the first exit summand `8448·cfbC₁²·e^{−M₀/e}` does not decay — the
`(log X)^{1/30}` inside `cfbC₁` (the crude fold's whole price) is not paid back.  The escapes
are both design-tier and both OUTSIDE this file: price `hRHS` at the band frequency directly
on the wide scale window (a new pricing page, the `dilated_scale_grade` genre with the ball
radius replaced by the band), or re-cut the crude fold so `√(seamT0 X)` is not paid.  Recorded,
not attempted — §5's `B` is free precisely so that either escape plugs in unchanged.

## ⟦THE TRAPS RESPECTED⟧

* **the four log scales** — every `log` here is at the block scale `X = X_d`; `seamT0 X` is
  the `X`-scale band `(log X)^{1/45}` and is never read at `log(X/P)` or `loglog X`;
* **`liouChi`, never `lamChi`** — the pieces are `liouChi χ · g_𝒥` (the sum-side datum); the
  floor transport to the pretentious side is `pretDistSq_liouChi_eq`, inside the landed
  `band_floor_M0_liouChi`;
* **the un-phased pin** — every datum here is at the frequency `0` (`doorChiCoeff` bare,
  `t₀ := 0` at both Route III and the wide supply); the band frequency `t` enters only as the
  TWIST `eIu (−t)`;
* **the half-open cut** — `winCutH`, never `winCut`; §3 is where the half-openness is paid;
* **strict gates** — `1 ≤ D`, `X − 1 < k` and `Xd < m` are carried strictly, never weakened.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory
open scoped BigOperators

/-! ## §1 — THE SPLIT RIDES THROUGH THE HALF-OPEN CUT

`winCutH X_d F = 1_{(X_d,2X_d]}·F` is multiplication by a `0/1` scalar, and scalar
multiplication distributes over a finite signed sum at every point.  So a datum written as a
signed `Finset` combination stays one after the cut, with the SAME coefficients and the pieces
cut by the SAME window. -/

/-- **THE CUT COMMUTES WITH A SIGNED `Finset` COMBINATION** (`winCutH_sum_finset`). -/
theorem winCutH_sum_finset {ι : Type*} (s : Finset ι) (Xd : ℕ) (ε : ι → ℂ) (bp : ι → ℕ → ℂ)
    {F : ℕ → ℂ} (hF : ∀ n, F n = ∑ i ∈ s, ε i * bp i n) (n : ℕ) :
    winCutH Xd F n = ∑ i ∈ s, ε i * winCutH Xd (bp i) n := by
  simp only [winCutH]
  split_ifs with hc
  · exact hF n
  · simp

/-- **THE DOOR'S CUT DATUM, SPLIT** (`winCutH_doorChiCoeff_split`).  At every `n`,

  `winCutH X_d (1_𝒮·λχ̄) (n) = Σ_{𝒥 ⊆ [1,2]} (−1)^{|𝒥|}·g_𝒥(1) · winCutH X_d (λχ̄·g_𝒥) (n)`.

`CofactorSupplier.doorCofactor0_split` at the shift `Ps := 1` (which `M4DoorRow`'s
`doorCofactor0_door_eq` identifies with the door datum) composed with `winCutH_sum_finset`. -/
theorem winCutH_doorChiCoeff_split {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd n : ℕ) :
    winCutH Xd (doorChiCoeff χ M) n
      = ∑ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          pieceSign 𝒥 (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 1
            * winCutH Xd (pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M))
                (calQK (Adoor M) (3072 * M) M)) n := by
  refine winCutH_sum_finset _ Xd _ _ (fun m => ?_) n
  rw [← doorCofactor0_door_eq χ M]
  exact doorCofactor0_split χ _ _ 2 1 le_rfl m

/-- The door's split has exactly `4` pieces: `#𝒫([1,2]) = 2² = 4`. -/
theorem door_powerset_card : ((Finset.Icc 1 2).powerset).card = 4 := by
  rw [Finset.card_powerset, Nat.card_Icc]
  norm_num

/-! ## §2 — `spolyA` IS LINEAR IN ITS COEFFICIENT SLOT

The twin of `CofactorSupplier.ramR_sum_finset` at the `T₀`-band's own polynomial. -/

/-- **`spolyA` IS LINEAR OVER A `Finset` COMBINATION** (`spolyA_sum_finset`). -/
theorem spolyA_sum_finset {ι : Type*} (s : Finset ι) (ε : ι → ℂ) (bp : ι → ℕ → ℂ) (t : ℝ)
    (m : ℕ) :
    spolyA (fun n => ∑ i ∈ s, ε i * bp i n) t m = ∑ i ∈ s, ε i * spolyA (bp i) t m := by
  simp only [spolyA, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => by ring

/-- **THE POLYNOMIAL SUP ADDS OVER THE PIECES** (`norm_spolyA_of_pieces`).  Unimodular
coefficients and a uniform per-piece sup give the combination's sup at `#s` times it. -/
theorem norm_spolyA_of_pieces {ι : Type*} {s : Finset ι} {a : ℕ → ℂ} {ε : ι → ℂ}
    {bp : ι → ℕ → ℂ} {t S : ℝ} {m : ℕ}
    (hε : ∀ i ∈ s, ‖ε i‖ ≤ 1) (ha : ∀ n, a n = ∑ i ∈ s, ε i * bp i n)
    (hb : ∀ i ∈ s, ‖spolyA (bp i) t m‖ ≤ S) :
    ‖spolyA a t m‖ ≤ (s.card : ℝ) * S := by
  have haeq : a = fun n => ∑ i ∈ s, ε i * bp i n := funext ha
  rw [haeq, spolyA_sum_finset]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ s, ‖ε i * spolyA (bp i) t m‖ ≤ S := by
    intro i hi
    rw [norm_mul]
    calc ‖ε i‖ * ‖spolyA (bp i) t m‖ ≤ 1 * S :=
          mul_le_mul (hε i hi) (hb i hi) (norm_nonneg _) (by norm_num)
      _ = S := one_mul S
  calc ∑ i ∈ s, ‖ε i * spolyA (bp i) t m‖ ≤ ∑ _i ∈ s, S := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * S := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §3 — THE PER-FREQUENCY SUP AT THE HALF-OPEN CUT

`T0BandCapFree.cfb_sup_of_center` reads its datum hypothesis as `∀ n > X, a n = f n` — an
agreement on the WHOLE upper range.  The door's cut agrees only on `(X_d, 2X_d]`.  The live
range never leaves that window (`m ≤ N ≤ 2X_d`), so the missing agreement is supplied by the
window pin instead of by a hypothesis.  Everything else is `BallSup.spolyA_datum_split`'s
argument verbatim. -/

/-- **THE CUT DATUM'S POLYNOMIAL IS A DIFFERENCE OF PARTIAL SUMS**
(`spolyA_winCutH_split`).  For `X_d < m ≤ N ≤ 2X_d`,

  `A_t(m) = Σ_{n≤m} F(n)n^{−it} − Σ_{n≤X_d} F(n)n^{−it}`.

Both ends are exact: the bottom is the half-open cut's own edge (`winCutH_supp0`), the top is
the window pin `N ≤ 2X_d` (`winCutH_of_mem`). -/
theorem spolyA_winCutH_split {Xd N m : ℕ} {F : ℕ → ℂ} (t : ℝ)
    (hmN : m ≤ N) (hN : N ≤ 2 * Xd) (hm : Xd < m) :
    spolyA (winCutH Xd F) t m
      = (∑ n ∈ Finset.Icc 1 m, F n * eIu (-t) n)
        - ∑ n ∈ Finset.Icc 1 Xd, F n * eIu (-t) n := by
  classical
  have hAe : spolyA (winCutH Xd F) t m
      = ∑ n ∈ Finset.Icc 1 m, winCutH Xd F n * eIu (-t) n := by
    unfold spolyA
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact div_cpow_eq_eIu (winCutH Xd F n) t (by omega)
  have hsub : Finset.Icc 1 Xd ⊆ Finset.Icc 1 m := Finset.Icc_subset_Icc_right hm.le
  have h1 : (∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 Xd, F n * eIu (-t) n)
      + ∑ n ∈ Finset.Icc 1 Xd, F n * eIu (-t) n
      = ∑ n ∈ Finset.Icc 1 m, F n * eIu (-t) n := Finset.sum_sdiff hsub
  have h2 : (∑ n ∈ Finset.Icc 1 m, winCutH Xd F n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 Xd, winCutH Xd F n * eIu (-t) n := by
    refine (Finset.sum_subset Finset.sdiff_subset ?_).symm
    intro n hn hn'
    have hnX : n ∈ Finset.Icc 1 Xd := by
      by_contra hc
      exact hn' (Finset.mem_sdiff.mpr ⟨hn, hc⟩)
    have hle : n ≤ Xd := (Finset.mem_Icc.mp hnX).2
    rw [winCutH_supp0 F (by exact_mod_cast hle), zero_mul]
  have h3 : (∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 Xd, winCutH Xd F n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 Xd, F n * eIu (-t) n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_sdiff.mp hn
    have hgt : Xd < n := by
      by_contra hc
      exact hn2 (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn1).1, by omega⟩)
    have hup : n ≤ 2 * Xd := le_trans (le_trans (Finset.mem_Icc.mp hn1).2 hmN) hN
    rw [winCutH_of_mem F hgt hup]
  rw [hAe, h2, h3, ← h1]
  ring

/-- **THE CUT-DATUM PER-FREQUENCY SUP** (`cfb_sup_of_center_cut`).
`T0BandCapFree.cfb_sup_of_center` at the HALF-OPEN cut: if the centre datum's own partial sums
at the frequency `t` are `≤ S₀·k` on `[X_d, N]`, then

  `‖A_t(m)‖ ≤ 2·S₀·m`  for every `m ≤ N`,   provided `N ≤ 2X_d`.

No cap, no transfer, no radius — hypothesis and conclusion speak the SAME frequency. -/
theorem cfb_sup_of_center_cut {Xd N : ℕ} {F : ℕ → ℂ} {t S₀ : ℝ} (hS₀ : 0 ≤ S₀)
    (hN : N ≤ 2 * Xd)
    (hCenter : ∀ k : ℕ, Xd ≤ k → k ≤ N →
      ‖∑ n ∈ Finset.Icc 1 k, F n * eIu (-t) n‖ ≤ S₀ * (k : ℝ)) :
    ∀ m : ℕ, m ≤ N → ‖spolyA (winCutH Xd F) t m‖ ≤ 2 * S₀ * (m : ℝ) := by
  intro m hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases le_or_gt m Xd with hcase | hcase
  · -- below the block bottom the cut polynomial is empty
    have hz : spolyA (winCutH Xd F) t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      rw [winCutH_supp0 F (by exact_mod_cast le_trans hnm hcase), zero_div]
    rw [hz, norm_zero]
    nlinarith
  · have hXdN : Xd ≤ N := le_trans hcase.le hm
    have hsplit := spolyA_winCutH_split (F := F) t hm hN hcase
    have h1 := hCenter m hcase.le hm
    have h2 := hCenter Xd le_rfl hXdN
    have hfl : ((Xd : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hcase.le
    have hmono : S₀ * ((Xd : ℕ) : ℝ) ≤ S₀ * (m : ℝ) := mul_le_mul_of_nonneg_left hfl hS₀
    rw [hsplit]
    have htri := norm_sub_le (∑ n ∈ Finset.Icc 1 m, F n * eIu (-t) n)
      (∑ n ∈ Finset.Icc 1 Xd, F n * eIu (-t) n)
    linarith

/-! ## §4 — THE PIECE'S CENTRE BOUND: ROUTE III AT THE UNDAMPED PIECE

`SPartStation.hCenter_dissected` reads two facts about its datum: multiplicativity (mathlib's,
i.e. on coprimes) and `1`-boundedness.  The piece has both, and the first for free from
COMPLETE multiplicativity. -/

/-- The piece is multiplicative in mathlib's sense (`pieceDatum_isMultiplicative`) — the
binder `hCenter_dissected` reads.  Complete multiplicativity (`pieceDatum_mul`) is strictly
stronger; the coprimality hypothesis is simply discarded. -/
theorem pieceDatum_isMultiplicative {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) :
    (toArithmeticFunction (pieceDatum χ 𝒥 Pseq Qseq)).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [toAF_apply, pieceDatum_one χ 𝒥 Pseq Qseq], fun {m n} hm hn _ => ?_⟩
  simp only [toAF_apply, if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn]
  exact pieceDatum_mul χ 𝒥 Pseq Qseq m n

/-- **THE PIECE'S CENTRE BOUND FROM THE DILATED INNER SUMS** (`piece_center_of_inner`).
Route III (`SPartStation.hCenter_dissected`, `cSq = 20736` explicit) at `F := λχ̄·g_𝒥`,
`t₀ = 0`: a common grade `S` for the LINEARISED sums `ℓ(λχ̄·g_𝒥)` at every dilated scale
`⌊k/d⌋`, `d ≤ D`, gives the piece's own twisted partial sum at `cSq·S + cSq·D^{−1/4}`.

⟦THE UNDAMPED PIECE⟧ this is NOT `CofactorSupplier.caseA_dissect_gen` at `x = 1`: that page's
consumer binds `x` over `[0,1]` and carries a `cofactorMfl` window floor, neither of which the
band has.  The piece goes into Route III directly. -/
theorem piece_center_of_inner {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) {D k : ℕ} {t S : ℝ} (hD : 1 ≤ D) (hDk : D ≤ k) (hS : 0 ≤ S)
    (hInner : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      ‖∑ m ∈ Finset.Icc 1 (k / d),
          seamCoeff (ellLin (pieceDatum χ 𝒥 Pseq Qseq)) (fun _ => 1) 0 m * eIu (-t) m‖
        ≤ S * ((k / d : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n‖
      ≤ (cSq * S + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ) := by
  have h := hCenter_dissected (F := pieceDatum χ 𝒥 Pseq Qseq)
    (pieceDatum_isMultiplicative χ 𝒥 Pseq Qseq) (norm_pieceDatum_le_one χ 𝒥 Pseq Qseq)
    0 t hD hDk hS hInner
  rwa [sum_seamCoeff_zero_center] at h

/-! ## §5 — THE INNER SUMS: THE HOISTED WIDE CENTRE SUPPLY AT THE PIECE

`CaseAWide.center_halasz_supply_wideA` is `SPartStation.center_halasz_supply_wide` with the
`∃X₀` quantified BEFORE the datum.  That is exactly what a four-piece split wants: ONE
threshold, four data.  The dilated window is entered as in
`SPartStation.seam_ball_leg_station_M_gen` — the gate `D·(X_w+1) ≤ X−1` puts every `⌊k/d⌋`
above the wide window's floor `X_w ≥ √X`. -/

/-- The floor of a real quotient dominates any `z` one unit below it (Nat division) — the
dissection's window arithmetic.  A private clone of `SPartStation`'s own (`private` there). -/
private lemma t0d_le_natDiv_of_le {k d : ℕ} {z : ℝ} (hd : 1 ≤ d)
    (h : z + 1 ≤ (k : ℝ) / (d : ℝ)) : z ≤ ((k / d : ℕ) : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmod : (d : ℝ) * ((k / d : ℕ) : ℝ) + ((k % d : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.div_add_mod k d
  have hlt : ((k % d : ℕ) : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.mod_lt k (show 0 < d by omega)
  have h2 : (k : ℝ) / (d : ℝ) - 1 < ((k / d : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd0]
    nlinarith
  linarith

/-- **THE PIECE'S CENTRE BOUND, FULLY REDUCED** (`piece_center_of_wide`).  §4 ∘ the hoisted
wide supply: at every scale `k` above `X−1` and below `N`, the piece's twisted partial sum is

  `‖Σ_{n≤k} (λχ̄·g_𝒥)(n)·n^{−it}‖ ≤ (cSq·(B + 4(log X)^{−1/2+1/1000}) + cSq·D^{−1/4})·k`.

The `∃X₀` is hoisted OUT of the character, the piece index and the frequency — one threshold
for the whole four-piece split at every band frequency. -/
theorem piece_center_of_wide (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ)
        (X Xw B : ℝ) (N D : ℕ) (t : ℝ),
        X₀ ≤ Real.sqrt X → Real.sqrt X ≤ Xw → 0 ≤ B → 1 ≤ D →
        (D : ℝ) * (Xw + 1) ≤ X - 1 → (N : ℝ) ≤ 2 * X →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            ‖prop21RHS (fun p => pieceDatum χ 𝒥 Pseq Qseq p
                  * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I)) (0 + t)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
        ∀ k : ℕ, X - 1 < (k : ℝ) → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n‖
            ≤ (cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
                + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ))) * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := center_halasz_supply_wideA Y
  refine ⟨X₀, hX₀0, ?_⟩
  intro q χ 𝒥 Pseq Qseq X Xw B N D t hXlb hXw hB0 hD hDgate hN2 hY10 hYsq hYlow hYlog hRHS
    k hkX hkN
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le hX₀0 hXlb
  have hXw0 : (0 : ℝ) < Xw := lt_of_lt_of_le hsq0 hXw
  have hDR : (D : ℝ) ≤ X - 1 := by
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    nlinarith
  have hDk : D ≤ k := by
    have hlt : (D : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast le_of_lt hlt
  have hP0 : (0 : ℝ) ≤ 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg (by
      have hX1 : (1 : ℝ) ≤ X := by nlinarith
      exact Real.log_nonneg hX1) _
    linarith
  have hS0 : (0 : ℝ) ≤ B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := by linarith
  have hSupplyAt := hsupply (pieceDatum χ 𝒥 Pseq Qseq)
    (fun p _ => norm_pieceDatum_le_one χ 𝒥 Pseq Qseq p) 0 t X Xw B hXlb hXw hB0
    hY10 hYsq hYlow hYlog hRHS
  refine piece_center_of_inner χ 𝒥 Pseq Qseq hD hDk hS0 ?_
  intro d hd1 hdD
  have hdD' : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hulow : Xw ≤ ((k / d : ℕ) : ℝ) := by
    refine t0d_le_natDiv_of_le hd1 ?_
    rw [le_div_iff₀ hd0]
    have h1 : (Xw + 1) * (d : ℝ) ≤ (Xw + 1) * (D : ℝ) :=
      mul_le_mul_of_nonneg_left hdD' (by linarith)
    have h2 : (Xw + 1) * (D : ℝ) = (D : ℝ) * (Xw + 1) := by ring
    linarith
  have huup : ((k / d : ℕ) : ℝ) ≤ 2 * X := by
    have h1 : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.div_le_self k d
    have h2 : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
    linarith
  exact hSupplyAt (k / d) hulow huup

/-! ## §6 — THE ASSEMBLY: THE `hsup` BINDER AT THE DOOR DATUM

§1 (the split) ∘ §2 (linearity) ∘ §3 (the cut sup): four pieces, each paying the cut's factor
`2`, gives the door's own per-frequency polynomial sup at `8·S₀`. -/

/-- **THE DOOR DATUM'S PER-FREQUENCY BAND SUP** (`m4_t0datum_sup`).  With the per-piece,
per-frequency centre bound `S₀` on `[X_d, N]`,

  `‖spolyA (winCutH X_d (doorChiCoeff χ M)) t m‖ ≤ 8·S₀·m`,  `|t| ≤ seamT0 X`, `m ≤ N`,

which is `M4Seam.cfb_t0band_supply_of_sup`'s `hsup` slot at the door datum.  The `8` is
`4 = #𝒫([1,2])` pieces times the half-open cut's factor `2`; no other constant appears. -/
theorem m4_t0datum_sup {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd N : ℕ} {X S₀ : ℝ}
    (hN : N ≤ 2 * Xd) (hS₀ : 0 ≤ S₀)
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ)) :
    ∀ t : ℝ, |t| ≤ seamT0 X → ∀ m : ℕ, m ≤ N →
      ‖spolyA (winCutH Xd (doorChiCoeff χ M)) t m‖ ≤ (8 * S₀) * (m : ℝ) := by
  intro t ht m hm
  have hb : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      ‖spolyA (winCutH Xd (pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M))) t m‖ ≤ 2 * S₀ * (m : ℝ) :=
    fun 𝒥 h𝒥 => cfb_sup_of_center_cut hS₀ hN (hpiece 𝒥 h𝒥 t ht) m hm
  have hmain := norm_spolyA_of_pieces
    (s := (Finset.Icc 1 2).powerset)
    (ε := fun 𝒥 => pieceSign 𝒥 (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 1)
    (fun 𝒥 _ => norm_pieceSign_le_one 𝒥 _ _ 1)
    (winCutH_doorChiCoeff_split χ M Xd) hb
  rw [door_powerset_card] at hmain
  have h4 : ((4 : ℕ) : ℝ) * (2 * S₀ * (m : ℝ)) = (8 * S₀) * (m : ℝ) := by push_cast; ring
  linarith [hmain, h4.le, h4.ge]

/-! ## §7 — THE SLOT: `hT0band` AT THE DOOR DATUM

`M4Seam.cfb_t0band_supply_of_sup` composed with §6.  Every remaining binder is that theorem's
own, carried verbatim — this file adds no arithmetic to the plug. -/

/-- **THE `hT0band` SLOT AT THE DOOR DATUM** (`m4_hT0band_at_door`).

  `∫_{−T₀}^{T₀} ‖dpolyA (winCutH X_d (doorChiCoeff χ M)) (seamS0 N X) t‖² dt
     ≤ t0BandB X (cfbC₁ X C₁) M₀`,   `T₀ = seamT0 X = (log X)^{1/45}`,

i.e. `ThmA2Rows.thm_a2'_of_rows`'s (hence `M4MeanSq.m4_meansq_per_chi_gen`'s) `hT0band` slot at
`C₁′ := cfbC₁ X C₁`, AT THE DOOR'S SIEVED χ-TWISTED UN-PHASED DATUM.  This is the item
`M4DoorRow`'s ⟦THE `T₀`-BAND, NAMED⟧ recorded as open.

The support pin is free (`M4DoorRow.winCutH_supp0`); `hSle` and `hErr` are
`cfb_t0band_supply_of_sup`'s own binders at the grade `S = 8·S₀`. -/
theorem m4_hT0band_at_door {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd N : ℕ}
    {X C₁ M₀ S₀ : ℝ}
    (hX3 : (3 : ℝ) ≤ X) (hXd : ((Xd : ℕ) : ℝ) = X) (hXdN : Xd ≤ N) (hN : N ≤ 2 * Xd)
    (hC₁ : 1 ≤ C₁) (hS₀ : 0 ≤ S₀)
    (hSle : 8 * S₀ ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hXN : X ≤ (N : ℝ) := by
    rw [← hXd]; exact Nat.cast_le.mpr hXdN
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at this
    linarith
  refine cfb_t0band_supply_of_sup hX3 hXN hN2 hC₁ ?_ (by linarith) hSle ?_ hErr
  · intro n hn
    exact winCutH_supp0 _ (by rw [hXd]; exact hn)
  · exact m4_t0datum_sup χ M hN hS₀ hpiece

/-- **THE SLOT, FULLY REDUCED TO THE WIDE SUPPLY** (`m4_hT0band_at_door_of_wide`).  §5 ∘ §7:
the door datum's `hT0band` slot from the hoisted wide centre supply's OWN binders, with no
per-piece hand-off left in the middle.  This is the kernel witness that the two shapes fit —
§5 delivers its bound on `X−1 < k ≤ N`, §7 asks for it on `X_d ≤ k ≤ N`, and `(X_d : ℝ) = X`
is what identifies them.

The `∃X₀` is `center_halasz_supply_wideA`'s, hoisted through the whole composition: ONE
threshold for every character, every piece and every band frequency.  The grade gate
(`hgrade`) and `hErr` are the only arithmetic asked of the consumer; both are
`cfb_t0band_supply_of_sup`'s own shape, read at `S = 8·(cSq·(B + 4P) + cSq·D^{−1/4})`. -/
theorem m4_hT0band_at_door_of_wide (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd N D : ℕ) (X Xw B C₁ M₀ : ℝ),
        (3 : ℝ) ≤ X → ((Xd : ℕ) : ℝ) = X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        X₀ ≤ Real.sqrt X → Real.sqrt X ≤ Xw → 0 ≤ B → 1 ≤ D →
        (D : ℝ) * (Xw + 1) ≤ X - 1 →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
          ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            ‖prop21RHS (fun p => pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M))
                    (calQK (Adoor M) (3072 * M) M) p
                  * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I)) (0 + t)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
        8 * (cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
              + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)))
            ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨X₀, hX₀0, hwide⟩ := piece_center_of_wide Y
  refine ⟨X₀, hX₀0, ?_⟩
  intro q χ M Xd N D X Xw B C₁ M₀ hX3 hXd hXdN hN hC₁ hXlb hXw hB0 hD hDgate hY10 hYsq
    hYlow hYlog hRHS hgrade hErr
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have h : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at h
    linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hcS : (0 : ℝ) ≤ cSq := by rw [cSq]; norm_num
  have hDp : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hS₀ : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
      + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) :=
      mul_nonneg hcS (by linarith)
    have h2 : (0 : ℝ) ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := mul_nonneg hcS hDp
    linarith
  refine m4_hT0band_at_door χ M hX3 hXd hXdN hN hC₁ hS₀ hgrade ?_ hErr
  intro 𝒥 h𝒥 t ht k hk1 hk2
  have hkX : X - 1 < (k : ℝ) := by
    have h : ((Xd : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
    rw [hXd] at h
    linarith
  exact hwide χ 𝒥 _ _ X Xw B N D t hXlb hXw hB0 hD hDgate hN2 hY10 hYsq hYlow hYlog
    (hRHS 𝒥 h𝒥 t ht) k hkX hk2

/-! ## §8 — THE BAND FLOOR AT THE PIECE, AND THE U1 PRICING HOOK

The `hRHS` binder of §5 is priced against a LOWER bound on the piece's pretentious distance at
band height.  `T0BandCapFree.band_floor_M0_liouChi` is that bound at the ROW datum `λχ̄`;
`CofactorSupplier.pretDistSq_pieceDatum_ge` transports it to the masked piece at the cost of
the mask debit, and `cfbM0_add_debit` shows the debit does not change the SHAPE of `M₀`. -/

/-- ⟦THE U1 PRICING HOOK⟧ (`cfbM0_add_debit`).  Subtracting an `X`-free debit from the band
floor value is the SAME function at a shifted constant:

  `cfbM0 K q X − D = cfbM0 (K + D) q X`.

So a floor stated at the masked piece is still `cfbM0`-shaped, and
`M4WaveClosed.m4_rawMS_priced_decay` (whose first gate reads `m4DecayGrade K q X C₁` at
`M₀ = cfbM0 K q X`) applies verbatim at `K + D`. -/
theorem cfbM0_add_debit (K D : ℝ) (q : ℕ) (X : ℝ) :
    cfbM0 (K + D) q X = cfbM0 K q X - D := by
  unfold cfbM0
  ring

/-- **THE BAND FLOOR AT THE MASKED PIECE** (`band_floor_M0_pieceDatum`).  For every finite
modulus range `Q` there is one `X`-free, `q`-free `K ≥ 0` with

  `cfbM0 (K + D) q X ≤ 𝔻²(λχ̄·g_𝒥, n^{iv}; X)`

for every `q ≤ Q`, every `χ mod q`, every `X ≥ exp(exp 1)`, every band frequency
`|v| ≤ 2·seamT0 X + 1` and every `D` dominating the mask's Mertens debit.

`band_floor_M0_liouChi` (band strength `7/30`, NOT the box's `1/16`) less the debit, through
`pretDistSq_pieceDatum_ge` — factor `1`, because the mask is `gxDatum` at `x = 0`. -/
theorem band_floor_M0_pieceDatum (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X v D : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
        cfbM0 (K + D) q X ≤ pretDistSq (pieceDatum χ 𝒥 Pseq Qseq) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := band_floor_M0_liouChi Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ Pseq Qseq 𝒥 X v D hq hX hv hdebit
  have hfloor := hK q χ X v hq hX hv
  have htr := pretDistSq_pieceDatum_ge χ Pseq Qseq
    (fun p _ => le_of_eq (costwist_norm v p)) X 𝒥
  rw [cfbM0_add_debit]
  linarith

/-- The door's calibrated exponent ladder clears `2` at every index: `e_j = A·G^{j−1}·(j!)²`
with `A = Adoor M ≥ 2^18`.  (`CofactorSupplier.blockWindow_calibrated_debit_sum`'s `hE`.) -/
theorem two_le_calE_door {M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    2 ≤ calE (Adoor M) (3072 * M) j := by
  have hA : 2 ^ 18 ≤ Adoor M := Adoor_ge_old M
  have h1 : 1 ≤ (3072 * M) ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (Nat.factorial j) ^ 2 := Nat.one_le_pow _ _ (Nat.factorial_pos j)
  have hstep : Adoor M ≤ Adoor M * (3072 * M) ^ (j - 1) * (Nat.factorial j) ^ 2 := by
    calc Adoor M = Adoor M * 1 * 1 := by ring
      _ ≤ Adoor M * (3072 * M) ^ (j - 1) * (Nat.factorial j) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  unfold calE
  omega

/-- **THE BAND FLOOR AT THE DOOR'S OWN PIECES** (`band_floor_M0_doorPiece`).  The masked band
floor at the door's calibrated ladder, with the debit EVALUATED: `X`-free, and at `J = 2` it
is `2·(log(4M) + 25)`.

The floor's constant is therefore `K + 2(log(4M)+25)` — still `X`-free, still `cfbM0`-shaped
(`cfbM0_add_debit`), which is what keeps the U1 pricing route reachable. -/
theorem band_floor_M0_doorPiece (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M : ℕ)
      (𝒥 : Finset ℕ) (X v : ℝ), q ≤ Q → 1 ≤ M → 𝒥 ⊆ Finset.Icc 1 2 →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
        cfbM0 (K + 2 * (Real.log (4 * (M : ℝ)) + 25)) q X
          ≤ pretDistSq (pieceDatum χ 𝒥 (calP (Adoor M) (3072 * M))
              (calQK (Adoor M) (3072 * M) M)) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := band_floor_M0_pieceDatum Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ M 𝒥 X v hq hM h𝒥 hX hv
  have hdeb := blockWindow_calibrated_debit_sum (Adoor M) (3072 * M) M 2 (𝒥 := 𝒥) X h𝒥 hM
    (two_le_calE_door hM)
  have hval : ((2 : ℕ) : ℝ) * (Real.log (((2 : ℕ) : ℝ) ^ 2 * (M : ℝ)) + 25)
      = 2 * (Real.log (4 * (M : ℝ)) + 25) := by norm_num
  rw [hval] at hdeb
  exact hK q χ _ _ 𝒥 X v _ hq hX hv hdeb

/-! ## §GK — the G-lever twin

The `T₀`-datum page at `G := s13GK K M`.  A pure literal swap: the split's pieces are read at
the levered K-family, `doorCofactor0_door_eq_gk` supplies the middle step, and the analytic
composition (`cfb_sup_of_center_cut`, `norm_spolyA_of_pieces`, `cfb_t0band_supply_of_sup`,
`piece_center_of_wide`) is `G`-generic and is reused verbatim.

⟦ABSTAINED, per the dispatch⟧ `two_le_calE_door` and `band_floor_M0_doorPiece` — off the
compose cone; no `_gk` sibling is minted for them here. -/

/-- **THE DOOR DATUM'S FOUR-PIECE SPLIT, AT THE G-LEVER** (`winCutH_doorChiCoeff_split_gk`)
-- the levered K-family in the pieces, `doorCofactor0_door_eq_gk` in the middle. -/
theorem winCutH_doorChiCoeff_split_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd n : ℕ) :
    winCutH Xd (doorChiCoeff_gk K χ M) n
      = ∑ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          pieceSign 𝒥 (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 1
            * winCutH Xd (pieceDatum χ 𝒥 (calP (Adoor M) (s13GK K M))
                (calQK (Adoor M) (s13GK K M) M)) n := by
  refine winCutH_sum_finset _ Xd _ _ (fun m => ?_) n
  rw [← doorCofactor0_door_eq_gk K χ M]
  exact doorCofactor0_split χ _ _ 2 1 le_rfl m

/-- **THE DOOR DATUM'S PER-FREQUENCY BAND SUP, AT THE G-LEVER** (`m4_t0datum_sup_gk`).  The
`8` is `4 = #𝒫([1,2])` pieces times the half-open cut's factor `2`, exactly as landed. -/
theorem m4_t0datum_sup_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ)
    {Xd N : ℕ} {X S₀ : ℝ}
    (hN : N ≤ 2 * Xd) (hS₀ : 0 ≤ S₀)
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ)) :
    ∀ t : ℝ, |t| ≤ seamT0 X → ∀ m : ℕ, m ≤ N →
      ‖spolyA (winCutH Xd (doorChiCoeff_gk K χ M)) t m‖ ≤ (8 * S₀) * (m : ℝ) := by
  intro t ht m hm
  have hb : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      ‖spolyA (winCutH Xd (pieceDatum χ 𝒥 (calP (Adoor M) (s13GK K M))
        (calQK (Adoor M) (s13GK K M) M))) t m‖ ≤ 2 * S₀ * (m : ℝ) :=
    fun 𝒥 h𝒥 => cfb_sup_of_center_cut hS₀ hN (hpiece 𝒥 h𝒥 t ht) m hm
  have hmain := norm_spolyA_of_pieces
    (s := (Finset.Icc 1 2).powerset)
    (ε := fun 𝒥 => pieceSign 𝒥 (calP (Adoor M) (s13GK K M))
      (calQK (Adoor M) (s13GK K M) M) 1)
    (fun 𝒥 _ => norm_pieceSign_le_one 𝒥 _ _ 1)
    (winCutH_doorChiCoeff_split_gk K χ M Xd) hb
  rw [door_powerset_card] at hmain
  have h4 : ((4 : ℕ) : ℝ) * (2 * S₀ * (m : ℝ)) = (8 * S₀) * (m : ℝ) := by push_cast; ring
  linarith [hmain, h4.le, h4.ge]

/-- **THE `hT0band` SLOT AT THE DOOR DATUM, AT THE G-LEVER** (`m4_hT0band_at_door_gk`). -/
theorem m4_hT0band_at_door_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd N : ℕ}
    {X C₁ M₀ S₀ : ℝ}
    (hX3 : (3 : ℝ) ≤ X) (hXd : ((Xd : ℕ) : ℝ) = X) (hXdN : Xd ≤ N) (hN : N ≤ 2 * Xd)
    (hC₁ : 1 ≤ C₁) (hS₀ : 0 ≤ S₀)
    (hSle : 8 * S₀ ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_gk K χ M)) (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hXN : X ≤ (N : ℝ) := by
    rw [← hXd]; exact Nat.cast_le.mpr hXdN
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at this
    linarith
  refine cfb_t0band_supply_of_sup hX3 hXN hN2 hC₁ ?_ (by linarith) hSle ?_ hErr
  · intro n hn
    exact winCutH_supp0 _ (by rw [hXd]; exact hn)
  · exact m4_t0datum_sup_gk K χ M hN hS₀ hpiece

/-- **THE SLOT, FULLY REDUCED TO THE WIDE SUPPLY, AT THE G-LEVER**
(`m4_hT0band_at_door_of_wide_gk`).  The `∃X₀` is `center_halasz_supply_wideA`'s, unmoved by
the lever: the wide centre supply never reads `G`. -/
theorem m4_hT0band_at_door_of_wide_gk (K : ℕ) (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd N D : ℕ) (X Xw B C₁ M₀ : ℝ),
        (3 : ℝ) ≤ X → ((Xd : ℕ) : ℝ) = X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        X₀ ≤ Real.sqrt X → Real.sqrt X ≤ Xw → 0 ≤ B → 1 ≤ D →
        (D : ℝ) * (Xw + 1) ≤ X - 1 →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
          ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            ‖prop21RHS (fun p => pieceDatum χ 𝒥 (calP (Adoor M) (s13GK K M))
                    (calQK (Adoor M) (s13GK K M) M) p
                  * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I)) (0 + t)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
        8 * (cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
              + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)))
            ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff_gk K χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨X₀, hX₀0, hwide⟩ := piece_center_of_wide Y
  refine ⟨X₀, hX₀0, ?_⟩
  intro q χ M Xd N D X Xw B C₁ M₀ hX3 hXd hXdN hN hC₁ hXlb hXw hB0 hD hDgate hY10 hYsq
    hYlow hYlog hRHS hgrade hErr
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have h : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at h
    linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hcS : (0 : ℝ) ≤ cSq := by rw [cSq]; norm_num
  have hDp : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hS₀ : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
      + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) :=
      mul_nonneg hcS (by linarith)
    have h2 : (0 : ℝ) ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := mul_nonneg hcS hDp
    linarith
  refine m4_hT0band_at_door_gk K χ M hX3 hXd hXdN hN hC₁ hS₀ hgrade ?_ hErr
  intro 𝒥 h𝒥 t ht k hk1 hk2
  have hkX : X - 1 < (k : ℝ) := by
    have h : ((Xd : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
    rw [hXd] at h
    linarith
  exact hwide χ 𝒥 _ _ X Xw B N D t hXlb hXw hB0 hD hDgate hN2 hY10 hYsq hYlow hYlog
    (hRHS 𝒥 h𝒥 t ht) k hkX hk2

-- #audit (temporary)

end Salt.MR
