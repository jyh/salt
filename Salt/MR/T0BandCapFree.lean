/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.T0Band
import Salt.MR.CapFreeAssembly
import Salt.MR.HalaszHead

/-!
# CFB — THE CAP-FREE `T₀`-BAND (`T0BandCapFree`)

`T0Band.t0_band_supply` produces the `hT0band` datum of `ThmA2Rows.thm_a2'_of_rows` — but it
carries the PRETENTIOUSNESS CAP `hMcap` (`𝔻²(f, n^{i·0}; X) ≤ (1/16)loglog X`), which is
false for the `λ`-datum by a factor `~8` and is not suppliable at any centre.  This file
lands the same conclusion WITHOUT the cap, by the route the M4-plan refuter pass specified
(flags, "THE M4-PLAN REFUTER PASS", kill K3):

* **the weighted-sup mirror does not exist cap-free** — the `1/(1+|t|)` weight comes only
  from `BallSup.transfer_at_scale`, whose hypothesis IS the cap.  It is not attempted here;
* instead the sup is taken **PER FREQUENCY**: `SupplyGeneric.center_halasz_supply_Y` is
  instantiated at `t₁ := t` for each `t` in the band (it is genuinely cap-free — four
  `Y`-gates and `hRHS`, nothing else, and its `t₁` is quantified INSIDE the single `∃X₀`),
  which gives the UNWEIGHTED sup at every band frequency with no recentring at all;
* the band integral is then the **crude fold** `∫_{−T₀}^{T₀} ≤ 2T₀·sup²`.

The price is exactly one factor `T₀ = seamT0 X = (log X)^{1/15}` on the main term, i.e.
`(log X)^{1/30}` inside the interface's `C₁′` (catch #253: an `X`-DEPENDENT `C₁′`, named and
carried symbolically — `cfbC₁`).  The gate that pays for it is in-statement.

## The five stones

* §1 `cfb_sup_of_center` / `cfb_sup_supplied_Y` — the per-frequency UNWEIGHTED sup.  No
  `transfer_at_scale`, no `ballErr`, no `hMcap`: at `t₁ = t` the datum split
  (`BallSup.spolyA_datum_split`) already gives `‖A_t(m)‖ ≤ S₀·m + S₀·⌊X⌋₊ ≤ 2S₀·m`.
* §2 `band_integral_of_sup_crude` — `∫_{−R}^{R} ‖dpolyA‖² ≤ 8R·S²` from the UNWEIGHTED sup
  (the weighted `T0Band.band_integral_of_sup` gives `8S²`; the crude form is what a cap-free
  sup can feed, and it costs the single factor `2R`).
* §3 the BAND FLOOR — `cfb_band_loglog` / `cfb_band_logloglog` (the drifts evaluated ON THE
  BAND, where they are `logloglog X + 1`, not the bulk's `loglog X + log 2`),
  `chi_floor_band_strength` (real `χ`, `k = 2`, coefficient **1/4**),
  `chi_floor_band_nonreal` (non-real `χ`, the 3-4-1 mid branch at the band height,
  coefficient **7/30**), and `band_floor_M0` / `band_floor_M0_liouChi`, the assembled
  uniform floor `cfbM0`.
* §4 the two named thresholds — `cfb_gate_decay` (the gate `M₀ ≥ (103/1500)e·loglog X` turns
  `T₀·e^{−M₀/e}` into `(log X)^{−1/500}`, an EXACT identity: `1/15 − 103/1500 = −1/500`) and
  `cfb_floor_clears_gate` (the band floor clears that gate), plus the minor side condition
  `cfb_ballerr_le`.
* §5 `cfbC₁` / `cfb_t0band_supply` / `cfb_t0band_supply_chi` — THE EXIT, in the byte shape
  `ThmA2Rows.thm_a2'_of_rows` demands at its `hT0band` slot:
  `∫_{−T₀}^{T₀} ‖dpolyA a (seamS0 N X) t‖² ≤ t0BandB X C₁′ M₀` with `C₁′ := cfbC₁ X C₁`.

## THE GRADE NOTE (every factor written out, no `o(1)`)

Write `E := e^{−M₀/(2e)}`, `P := (log X)^{−1/2+1/1000}`, `S₀ := C₁·E + 4P`,
`T₀ := seamT0 X = (log X)^{1/15}`.  §1 gives `‖A_t(m)‖ ≤ 2S₀·m` for every `|t| ≤ T₀`; §2
folds it to

  `∫_{−T₀}^{T₀} ‖dpolyA‖² ≤ 8·T₀·(2S₀)² = 32·T₀·S₀²`.

With `4P ≤ E` (the side condition `cfb_ballerr_le` discharges) and `C₁ ≥ 1`,
`S₀ ≤ (C₁+1)E`, so the bound is `≤ 32·T₀·(C₁+1)²E²`, and

  `t0BandB X (cfbC₁ X C₁) M₀ ≥ 8·(2√2·cfbC₁ X C₁·E)² = 64·(C₁+1)²·T₀·E²`

since `cfbC₁ X C₁ = (C₁+1)·√T₀`.  The plug is therefore honest with a factor `2` to spare.
Downstream, `thm_a2'_of_rows`'s first summand becomes

  `8448·(C₁+1)²·(log X)^{1/15}·e^{−M₀/e}`,

and §4's gate `M₀ ≥ (103/1500)·e·loglog X ≈ 0.18665·loglog X` sends it under
`8448·(C₁+1)²·(log X)^{−1/500}` — the interface's third summand's own shape.

## THE BAND FLOOR, per class (the whole point of the band)

On `|v| ≤ 2T₀ + 1` the `k = 2` drift `(3/4)·loglog(|2v|+3)` is NOT the bulk's
`(3/4)(loglog X + log 2)`: `|2v| + 3 ≤ 9·(log X)^{1/15}` gives
`loglog(|2v|+3) ≤ logloglog X + 1`.  So the bracket keeps its full `loglog X` and the `/k²`
delivers `1/4`, not the bulk's `1/16`:

| class | supplier | delivery on the band |
|---|---|---|
| `χ²=1`, `1/2 ≤ \|v\|` | `chi_floor_of_order` at `k=2` | `(1/4)L−(23/16)ℓ−(1/4)q−C` |
| `χ²=1`, `\|v\| ≤ 1/2` | `chi_floor_band_uniform Q` | `L − C` (coefficient 1) |
| `χ² ≠ 1` | `chi_Llower_341_height` at `2T₀+1` | `(7/30)L − (3/4)log q − C` |

(suppliers live in `ChiFloor`, `SiegelBand`, `VkTwistClose` respectively.)

(`L := loglog X`, `ℓ := logloglog X`.)  The non-real arm pays `(1/4)·log(3+2T)` for the band
HEIGHT, i.e. `(1/60)L`, so its coefficient is `1/4 − 1/60 = 7/30 = 0.2333…` rather than the
real arms' `1/4`; `band_floor_M0` states the uniform coefficient `7/30`, and `7/30` still
clears the gate's `0.18665` with margin `0.0467·loglog X`.  **No VK socket is consumed** —
the mid branch's growth input (`LFunction_norm_le_level`) is unconditional on a bounded
height window, and the band IS bounded.  The Siegel-band arm is the only ineffective input
(`siegelBandB`'s EVT minimum, POISON 2), confined to `χ² = 1, |v| ≤ 1/2` exactly as
`CapFreeAssembly` confines it.

## Traps observed (the brief's list, each pinned)

* **the shifted variable** — the floor is read at `t₀ + t`, never at `t`;
  `HalaszHead.seamCoeff_trivial_dist_eq` is the adapter and `cfb_seam_floor_of_band` is the
  only place it is used.  The honest uniform range is `|t₀ + t| ≤ 2·seamT0 X + 1`, which is
  what `band_floor_M0` quantifies over, and it needs `|t₀| ≤ seamT0 X + 1` from the consumer.
* **`seamT0` vs `seamRad`** — everything here is `seamT0 X = (log X)^{1/15}`; `seamRad`
  (`(log X)^{1/16}`) never appears.
* **the `lam` collision** — `lamChi χ` is the pretentious datum (prime-correct only);
  `liouChi χ` is the sum-side datum.  §3's floors are stated on `lamChi` and transported to
  `liouChi` by `CapFreeAssembly.pretDistSq_liouChi_eq` (an EQUALITY).  The exit's `g`-slot
  takes `liouChi χ`.
* **`dpolyA` vs `spolyA`** — the slot integrates `‖dpolyA a (seamS0 N X) t‖²`; the sup is on
  `spolyA`; `SeamLemma14.spoly_eq_dpolyA_filter` + `SeamSplit.spoly_abel_sup` are the bridge
  (both already landed, both used verbatim).
* **strict vs `≤`** — every threshold here is non-strict (`≤`); the STRICT thresholds belong
  to `CapFreeFloor`, which this file does not produce.

**LIVE GUARD** (inherited from `CenterSupply`/`SupplyGeneric`/`T0Band`): the exponent is the
BALL arm's halved constant `c = 1/(2e)`; a §8.3 consumer citing this head is a STOP.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory
open scoped BigOperators

/-! ## §1 — THE PER-FREQUENCY, UNWEIGHTED, CAP-FREE SUP

The cap enters `T0Band.band_sup_of_center` at exactly one place: `transfer_at_scale`, which
moves a partial sum from the frequency `t` to the ball CENTRE `t₁ ≠ t` and pays the
pretentiousness cap for the move.  At `t₁ = t` there is nothing to move — the centre supply
already speaks the frequency the integrand is evaluated at — so the whole transfer page, the
`ballErr` majorant and `hMcap` all disappear, and the weight `1/(1+|t−t₁|) = 1` with them. -/

/-- **CFB-1 — the per-frequency sup (`cfb_sup_of_center`).**  If the datum's own partial sums
at the frequency `t` are `≤ S₀·k` on the dyadic window, then

  `‖A_t(m)‖ ≤ 2·S₀·m`  for every `m ≤ N`.

The proof is `BallSup.spolyA_datum_split` and the triangle inequality: `A_t(m)` is the
difference of the partial sums at `m` and at `⌊X⌋₊`, and `⌊X⌋₊ ≤ m` on the live range.
Below the window the polynomial is empty (`hsupp`).

**No cap, no transfer, no radius** — the hypothesis and the conclusion speak the SAME
frequency.  This is the cap-free replacement for `T0Band.band_sup_of_center`, and it is
weaker by exactly the Cauchy weight: `2S₀·m` instead of `bandSupS X R S₀·m/(1+|t−t₁|)`. -/
theorem cfb_sup_of_center {N : ℕ} {a f : ℕ → ℂ} {X t S₀ : ℝ}
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hS₀ : 0 ≤ S₀)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hDatum : ∀ n : ℕ, X < (n : ℝ) → a n = f n)
    (hCenter : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖∑ n ∈ Finset.Icc 1 k, f n * eIu (-t) n‖ ≤ S₀ * (k : ℝ)) :
    ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ 2 * S₀ * (m : ℝ) := by
  intro m hm
  have hX0 : (0 : ℝ) ≤ X := hX.le
  have hkN : ⌊X⌋₊ ≤ N := Nat.cast_le.mp (le_trans (Nat.floor_le hX0) hXN)
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases le_or_gt m ⌊X⌋₊ with hcase | hcase
  · -- below the dyadic window the polynomial is empty
    have hz : spolyA a t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      have hle : (n : ℝ) ≤ X :=
        le_trans (Nat.cast_le.mpr (le_trans hnm hcase)) (Nat.floor_le hX0)
      rw [hsupp n hle, zero_div]
    rw [hz, norm_zero]
    have : (0 : ℝ) ≤ 2 * S₀ := by linarith
    exact mul_nonneg this hm0
  · have hkm : ⌊X⌋₊ ≤ m := le_of_lt hcase
    have hsplit := spolyA_datum_split hX0 hsupp hDatum t hkm
    have h1 := hCenter m hkm hm
    have h2 := hCenter ⌊X⌋₊ le_rfl hkN
    have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hkm
    have hmono : S₀ * ((⌊X⌋₊ : ℕ) : ℝ) ≤ S₀ * (m : ℝ) := mul_le_mul_of_nonneg_left hfl hS₀
    have hnorm : ‖spolyA a t m‖
        ≤ ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
          + ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    linarith

/-! ## §2 — THE CRUDE BAND INTEGRAL

`T0Band.band_integral_of_sup` consumes the WEIGHTED sup `S·m/(1+|t|)` and pays the whole
band by the Cauchy page `∫_ℝ (1+|u|)^{−2} ≤ 2`, giving `8S²` with NO measure factor.  A
cap-free sup is unweighted, so the weighted page is unavailable and the honest fold is
`measure × sup²`.  Feeding the unweighted `S` into the weighted lemma (as `S·(1+R)`) would
cost `(1+R)² ≍ R²`; the direct crude fold below costs `R` alone, which is why it is worth
its own stone. -/

/-- **CFB-2 — the crude band integral (`band_integral_of_sup_crude`).**  From the UNWEIGHTED
sup on `[−R,R]`,

  `∫_{−R}^{R} ‖dpolyA a (seamS0 N X) t‖² dt ≤ 8·R·S²`.

`SeamLemma14.spoly_eq_dpolyA_filter` identifies the integrand with `‖spoly N a t‖²`, the
landed Abel inequality `SeamSplit.spoly_abel_sup` gives `‖spoly N a t‖ ≤ 2S` pointwise, and
the constant majorant is integrated on an interval of length `2R`. -/
theorem band_integral_of_sup_crude {N : ℕ} {a : ℕ → ℂ} {X R S : ℝ}
    (hX : 0 < X) (hR : 0 ≤ R)
    (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, |t| ≤ R → ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * (m : ℝ)) :
    (∫ t in (-R)..R, ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ 8 * R * S ^ 2 := by
  have hcont : Continuous fun t : ℝ => ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    dpolyA_seamS0_normSq_continuous hX.le
  have hdom : ∀ t ∈ Set.Icc (-R) R, ‖dpolyA a (seamS0 N X) t‖ ^ 2 ≤ (2 * S) ^ 2 := by
    intro t ht
    have habs : |t| ≤ R := abs_le.mpr ⟨(Set.mem_Icc.mp ht).1, (Set.mem_Icc.mp ht).2⟩
    have hpt : ‖spoly N a t‖ ≤ 2 * S := spoly_abel_sup hX hXN hN2 hsupp (hSup t habs)
    rw [← spoly_eq_dpolyA_filter hsupp t]
    exact pow_le_pow_left₀ (norm_nonneg _) hpt 2
  calc (∫ t in (-R)..R, ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ ∫ _t in (-R)..R, (2 * S) ^ 2 :=
        intervalIntegral.integral_mono_on (by linarith)
          (hcont.intervalIntegrable _ _) intervalIntegrable_const hdom
    _ = (R - -R) * (2 * S) ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ = 8 * R * S ^ 2 := by ring

/-! ## §3 — THE BAND FLOOR

Two drift lemmas evaluated ON THE BAND, three arms, one assembly.  Everything is stated in
the BARE frequency `v`; the shift to `t₀ + t` happens once, in §5. -/

/-- The band's frequency range: `|t₀ + t| ≤ 2·seamT0 X + 1` for `|t| ≤ seamT0 X` and
`|t₀| ≤ seamT0 X + 1`.  Kept as a plain expression (not a `def`) in every statement below —
this abbreviation is documentation only. -/
private lemma cfb_seamT0_one_le {X : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) :
    1 ≤ seamT0 X := by
  obtain ⟨_, hlogX, _, _⟩ := cff_scale_facts hX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  unfold seamT0
  calc (1 : ℝ) = Real.log X ^ (0 : ℝ) := (Real.rpow_zero _).symm
    _ ≤ Real.log X ^ (1 / 15 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)

private lemma cfb_seamT0_log {X : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) :
    Real.log (seamT0 X) = (1 / 15) * Real.log (Real.log X) := by
  obtain ⟨_, hlogX, _, _⟩ := cff_scale_facts hX
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  unfold seamT0
  rw [Real.log_rpow hL0]

/-- `log 9 ≤ 2.21` — from `log 3 ≤ 3/e` (one `log x ≤ x − 1`) and `e > 2.7182818283`. -/
private lemma cfb_log_nine : Real.log 9 ≤ 2.21 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h3 : Real.log 3 ≤ 3 / Real.exp 1 := by
    have hpos : (0 : ℝ) < 3 / Real.exp 1 := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by norm_num) (Real.exp_ne_zero 1), Real.log_exp] at h
    linarith
  have hd : (3 : ℝ) / Real.exp 1 ≤ 1.105 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  linarith

/-- `log 22 ≤ 3.1` — the same device one exponent up (`log(22/e³) ≤ 22/e³ − 1`, `e³ > 20`). -/
private lemma cfb_log_twentytwo : Real.log 22 ≤ 3.1 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he3 : (20 : ℝ) < Real.exp 3 := by
    have hsplit : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [hsplit]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hpos : (0 : ℝ) < 22 / Real.exp 3 := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (by norm_num) (Real.exp_ne_zero 3), Real.log_exp] at h
  have hd : (22 : ℝ) / Real.exp 3 ≤ 1.1 := by
    rw [div_le_iff₀ (Real.exp_pos 3)]
    nlinarith
  linarith

/-- **BAND DRIFT 1 — `loglog(|2v|+3) ≤ logloglog X + 1` on the band.**

This is the inequality the whole cap-free band rests on.  On the CONTOUR BOX
(`|v| ≤ 3X`, `CapFreeAssembly.cff_box_loglog`) the same quantity is only
`loglog X + log 2` — a full `loglog X`, which is what forces the bulk's `1/16`.  On the BAND
`|v| ≤ 2·seamT0 X + 1` we have `|2v| + 3 ≤ 9·(log X)^{1/15}`, so the inner log is
`log 9 + (1/15)loglog X` and the outer one is `logloglog X + O(1)`: the `k = 2` bracket keeps
its full `loglog X` and the `/k² = /4` delivers the coefficient `1/4`. -/
theorem cfb_band_loglog {X v : ℝ} (hX : Real.exp (Real.exp 1) ≤ X)
    (hv : |v| ≤ 2 * seamT0 X + 1) :
    Real.log (Real.log (|2 * v| + 3)) ≤ Real.log (Real.log (Real.log X)) + 1 := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hT1 : (1 : ℝ) ≤ seamT0 X := cfb_seamT0_one_le hX
  have hTlog := cfb_seamT0_log hX
  have habs : |2 * v| = 2 * |v| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hbox : |2 * v| + 3 ≤ 9 * seamT0 X := by
    rw [habs]; linarith
  have hpos : (0 : ℝ) < |2 * v| + 3 := by positivity
  have h1 : Real.log (|2 * v| + 3) ≤ Real.log 9 + (1 / 15) * Real.log (Real.log X) := by
    have hle := Real.log_le_log hpos hbox
    rw [Real.log_mul (by norm_num) (by linarith : seamT0 X ≠ 0), hTlog] at hle
    exact hle
  have hlog9 := cfb_log_nine
  have hinner : (1 : ℝ) < |2 * v| + 3 := by linarith [abs_nonneg (2 * v)]
  have hipos : (0 : ℝ) < Real.log (|2 * v| + 3) := Real.log_pos hinner
  have hstep : Real.log (|2 * v| + 3) ≤ Real.exp 1 * Real.log (Real.log X) := by
    have hmul : (2.7182818283 : ℝ) * Real.log (Real.log X)
        ≤ Real.exp 1 * Real.log (Real.log X) :=
      mul_le_mul_of_nonneg_right he.le hLL0.le
    linarith
  have h2 := Real.log_le_log hipos hstep
  rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hLL0), Real.log_exp] at h2
  linarith

/-- **BAND DRIFT 2 — `logloglog(|2v|+16) ≤ logloglog X + 1` on the band.**  The same
doubling one level up: `|2v| + 16 ≤ 22·(log X)^{1/15}`, so `loglog(|2v|+16) ≤ 2 + logloglog X`
and one more `log` (with `log(2+u) ≤ 1+u`) lands the claim. -/
theorem cfb_band_logloglog {X v : ℝ} (hX : Real.exp (Real.exp 1) ≤ X)
    (hv : |v| ≤ 2 * seamT0 X + 1) :
    Real.log (Real.log (Real.log (|2 * v| + 16)))
      ≤ Real.log (Real.log (Real.log X)) + 1 := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hT1 : (1 : ℝ) ≤ seamT0 X := cfb_seamT0_one_le hX
  have hTlog := cfb_seamT0_log hX
  have habs : |2 * v| = 2 * |v| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hbox : |2 * v| + 16 ≤ 22 * seamT0 X := by
    rw [habs]; linarith
  have hpos : (0 : ℝ) < |2 * v| + 16 := by positivity
  have h1 : Real.log (|2 * v| + 16) ≤ Real.log 22 + (1 / 15) * Real.log (Real.log X) := by
    have hle := Real.log_le_log hpos hbox
    rw [Real.log_mul (by norm_num) (by linarith : seamT0 X ≠ 0), hTlog] at hle
    exact hle
  have hlog22 := cfb_log_twentytwo
  -- the inner log exceeds `1` (because `|2v| + 16 ≥ 16 > e`), so the outer logs are honest
  have he1lt : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
  have he16 : Real.exp 1 < |2 * v| + 16 := by linarith [abs_nonneg (2 * v)]
  have hin1 : (1 : ℝ) < Real.log (|2 * v| + 16) := (Real.lt_log_iff_exp_lt hpos).mpr he16
  have hin0 : (0 : ℝ) < Real.log (|2 * v| + 16) := by linarith
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hstep : Real.log (|2 * v| + 16) ≤ Real.exp 2 * Real.log (Real.log X) := by
    have hE2 : (7 : ℝ) ≤ Real.exp 2 := by rw [he2]; nlinarith
    have hmul : (7 : ℝ) * Real.log (Real.log X) ≤ Real.exp 2 * Real.log (Real.log X) :=
      mul_le_mul_of_nonneg_right hE2 hLL0.le
    linarith
  have h2 := Real.log_le_log hin0 hstep
  rw [Real.log_mul (Real.exp_ne_zero 2) (ne_of_gt hLL0), Real.log_exp] at h2
  -- level 3: one more `log`, paid by `log(2 + u) ≤ 1 + u`
  have h2pos : (0 : ℝ) < Real.log (Real.log (|2 * v| + 16)) := Real.log_pos hin1
  have h3 := Real.log_le_log h2pos h2
  have h4 : Real.log (2 + Real.log (Real.log (Real.log X)))
      ≤ 1 + Real.log (Real.log (Real.log X)) := by
    have hp : (0 : ℝ) < 2 + Real.log (Real.log (Real.log X)) := by linarith
    have := Real.log_le_sub_one_of_pos hp
    linarith
  linarith

/-- **ARM 1 (band, `χ² = 1`) — THE BAND-STRENGTH `k = 2` FLOOR (`chi_floor_band_strength`).**

For every character with `χ² = 1` (principal INCLUDED), every `X ≥ exp(exp 1)` and every
frequency with `1/2 ≤ |v| ≤ 2·seamT0 X + 1`:

  `(1/4)·loglog X − (23/16)·logloglog X − (1/4)·q − C ≤ 𝔻²(λ·χ̄, n^{iv}; X)`.

`ChiFloor.chi_floor_of_order` at `k = 2` with the two BAND drifts of this section (not
`CapFreeAssembly`'s box drifts) and `primeDivSum_le_modulus`.  **The coefficient is `1/4`,
four times the contour box's `1/16`** — the band's whole payoff, and the reason the
`(103/1500)e ≈ 0.18665` gate is clearable at all.  `C` is uniform in `q`, `χ`, `X`, `v`. -/
theorem chi_floor_band_strength :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≠ 0 → χ ^ 2 = 1 →
      Real.exp (Real.exp 1) ≤ X → 1 / 2 ≤ |v| → |v| ≤ 2 * seamT0 X + 1 →
        (1 / 4) * Real.log (Real.log X)
            - (23 / 16) * Real.log (Real.log (Real.log X))
            - (1 / 4) * (q : ℝ) - C
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨C₀, hC₀⟩ := chi_floor_of_order
  refine ⟨(C₀ + 23 / 4) / 4, ?_⟩
  intro q χ X v hq hχ2 hX hv2 hvband
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hXe : Real.exp 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact le_trans (Real.exp_le_exp.mpr h1) hX
  have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hkt : (1 : ℝ) ≤ |((2 : ℕ) : ℝ) * v| := by
    rw [hcast, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hmain := hC₀ q χ 2 X v (by norm_num) ⟨1, by norm_num⟩ hχ2 hXe hkt
  rw [hcast, show ((2 : ℝ)) ^ 2 = 4 by norm_num] at hmain
  have hA := cfb_band_loglog (X := X) (v := v) hX hvband
  have hB := cfb_band_logloglog (X := X) (v := v) hX hvband
  have hP := primeDivSum_le_modulus (q := q) hq X
  linarith

/-- **ARM 2 (band, `χ² ≠ 1`) — THE 3-4-1 MID BRANCH AT THE BAND HEIGHT
(`chi_floor_band_nonreal`).**

For every NON-REAL `χ mod q`, every `X ≥ exp(exp 1)` and every `|v| ≤ 2·seamT0 X + 1`:

  `(7/30)·loglog X − (3/4)·log q − C ≤ 𝔻²(λ·χ̄, n^{iv}; X)`.

`VkTwistClose.chi_Llower_341_height` at the height cap `T := 2·seamT0 X + 1` composed with
`ChiFloorLow.chi_floor_low_of_Llower` (coefficient exactly `1`).  The debit expands as

  `2log4 + (3/4)log(1+log X) + (1/4)log(3(3+2T)q²(1+log q))
     ≤ (3/4 + 1/60)·loglog X + (3/4)·log q + [2log4 + (3/4)log2 + (1/4)log27]`,

using `3(3+2T) ≤ 27·(log X)^{1/15}` and `1 + log q ≤ q`.  The surviving coefficient is
`1 − 3/4 − 1/60 = 7/30`.

**No VK socket is consumed**: the mid branch's growth input is `LFunction_norm_le_level`,
whose Pólya–Vinogradov shape is linear in the height and therefore harmless on a BOUNDED
window — and the `T₀`-band is bounded.  The `(1/60)·loglog X` is exactly the price of the
window's `X`-dependence, `(1/4)·log((log X)^{1/15})`. -/
theorem chi_floor_band_nonreal :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), χ ^ 2 ≠ 1 →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
        (7 / 30) * Real.log (Real.log X) - (3 / 4) * Real.log q - C
          ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨K, hK⟩ := chi_floor_low_of_Llower
  refine ⟨K + 2 * Real.log 4 + (3 / 4) * Real.log 2 + (1 / 4) * Real.log 27, ?_⟩
  intro q _ χ X v hχ2 hX hv
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hXe : Real.exp 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact le_trans (Real.exp_le_exp.mpr h1) hX
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hT1 : (1 : ℝ) ≤ seamT0 X := cfb_seamT0_one_le hX
  have hTlog := cfb_seamT0_log hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  -- the `L`-lower bound at the band height
  have hLow := chi_Llower_341_height χ hχ2 X v (2 * seamT0 X + 1) hXe (by linarith) hv
  have hfloor := hK q χ X v _ hXe hLow
  -- debit piece 1: `(3/4)·log(1 + log X) ≤ (3/4)(log 2 + loglog X)`
  have hd1 : Real.log (1 + Real.log X) ≤ Real.log 2 + Real.log (Real.log X) := by
    have hle : Real.log (1 + Real.log X) ≤ Real.log (2 * Real.log X) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_mul (by norm_num) (ne_of_gt hL0)] at hle
  -- debit piece 2: the height/modulus factor
  have hlq : (1 : ℝ) + Real.log q ≤ (q : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (q : ℝ))
    linarith
  have hprod : 3 * (3 + 2 * (2 * seamT0 X + 1)) * (q : ℝ) ^ 2 * (1 + Real.log q)
      ≤ 27 * seamT0 X * (q : ℝ) ^ 3 := by
    have h1 : 3 * (3 + 2 * (2 * seamT0 X + 1)) ≤ 27 * seamT0 X := by linarith
    have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := by positivity
    have hBq : (0 : ℝ) ≤ 1 + Real.log q := by linarith
    have h27 : (0 : ℝ) ≤ 27 * seamT0 X * (q : ℝ) ^ 2 :=
      mul_nonneg (by linarith) hq2
    calc 3 * (3 + 2 * (2 * seamT0 X + 1)) * (q : ℝ) ^ 2 * (1 + Real.log q)
        ≤ 27 * seamT0 X * (q : ℝ) ^ 2 * (1 + Real.log q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hq2) hBq
      _ ≤ 27 * seamT0 X * (q : ℝ) ^ 2 * (q : ℝ) := mul_le_mul_of_nonneg_left hlq h27
      _ = 27 * seamT0 X * (q : ℝ) ^ 3 := by ring
  have hppos : (0 : ℝ) < 3 * (3 + 2 * (2 * seamT0 X + 1)) * (q : ℝ) ^ 2 * (1 + Real.log q) := by
    have : (0 : ℝ) < 1 + Real.log q := by linarith
    have h2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    have h3 : (0 : ℝ) < 3 * (3 + 2 * (2 * seamT0 X + 1)) := by linarith
    positivity
  have hd2 : Real.log (3 * (3 + 2 * (2 * seamT0 X + 1)) * (q : ℝ) ^ 2 * (1 + Real.log q))
      ≤ Real.log 27 + (1 / 15) * Real.log (Real.log X) + 3 * Real.log q := by
    have hle := Real.log_le_log hppos hprod
    have hsplit : Real.log (27 * seamT0 X * (q : ℝ) ^ 3)
        = Real.log 27 + Real.log (seamT0 X) + 3 * Real.log q := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
        (by linarith : seamT0 X ≠ 0), Real.log_pow]
      push_cast
      ring
    rw [hsplit, hTlog] at hle
    linarith
  linarith

/-- **THE ASSEMBLED BAND FLOOR VALUE** (`cfbM0`).  `M₀` as a named function of the assembled
constant `K`, the modulus `q` and the scale `X`:

  `cfbM0 K q X = (7/30)·loglog X − (23/16)·logloglog X − (3/4)·log q − (1/4)·q − K`.

The coefficient `7/30` is the weakest of the three arms (the non-real mid branch); the two
real arms deliver `1/4` and `1` and are downgraded to it in `band_floor_M0`. -/
def cfbM0 (K : ℝ) (q : ℕ) (X : ℝ) : ℝ :=
  (7 / 30) * Real.log (Real.log X) - (23 / 16) * Real.log (Real.log (Real.log X))
    - (3 / 4) * Real.log q - (1 / 4) * (q : ℝ) - K

/-- **CFB-3 — THE UNIFORM BAND FLOOR (`band_floor_M0`).**  For every finite modulus range `Q`
there is a single `K ≥ 0` with

  `cfbM0 K q X ≤ 𝔻²(λ·χ̄, n^{iv}; X)`

for every `q ≤ Q`, EVERY `χ mod q`, every `X ≥ exp(exp 1)` and every `|v| ≤ 2·seamT0 X + 1`.

Three arms, one `χ²`-split and one `|v|`-split, exactly as `CapFreeAssembly` does on the
contour box — but every arm is read AT BAND HEIGHT, which is what turns the box's `1/16`
into `7/30`.  `K` is `X`-free and `q`-free (it depends on `Q` alone), so the threshold that
consumes it is regime-absorbable. -/
theorem band_floor_M0 (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
        cfbM0 K q X ≤ pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Kb, hKb⟩ := chi_floor_band_strength
  obtain ⟨Kn, hKn⟩ := chi_floor_band_nonreal
  obtain ⟨Ks, hKs⟩ := chi_floor_band_arm Q
  refine ⟨max 0 (max Kb (max Kn Ks)), le_max_left _ _, ?_⟩
  set K : ℝ := max 0 (max Kb (max Kn Ks)) with hKdef
  have hKb' : Kb ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKn' : Kn ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKs' : Ks ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  intro q _ χ X v hq hX hv
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  unfold cfbM0
  by_cases hsq : χ ^ 2 = 1
  · by_cases hband : |v| ≤ 1 / 2
    · -- the Siegel band arm, coefficient `1`
      have h := hKs q χ X v hq hX hband
      linarith
    · -- the `k = 2` band arm, coefficient `1/4`
      have h := hKb q χ X v hq0 hsq hX (le_of_lt (not_le.mp hband)) hv
      linarith
  · -- the non-real mid branch, coefficient `7/30`
    have h := hKn q χ X v hsq hX hv
    linarith

/-- **The band floor at the SUM-SIDE datum** (`band_floor_M0_liouChi`).  The same conclusion
for `liouChi χ = liouvilleC·χ̄` — the datum the row consumer sums over integers.  The
transport is `CapFreeAssembly.pretDistSq_liouChi_eq`, an EQUALITY of distances (the two data
agree at every prime, which is all `pretDistSq` reads). -/
theorem band_floor_M0_liouChi (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
        cfbM0 K q X ≤ pretDistSq (liouChi χ) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := band_floor_M0 Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ X v hq hX hv
  rw [pretDistSq_liouChi_eq]
  exact hK q χ X v hq hX hv

/-! ## §4 — THE TWO NAMED THRESHOLDS

The gate is `M₀ ≥ e·(1/15 + 1/500)·loglog X = (103/1500)·e·loglog X ≈ 0.18665·loglog X`.
`SiegelBand.band_gate_threshold_cfb` already states the regime-side arm at coefficient `1`;
the two stones here are the ANALYTIC content — what the gate buys (§4a) and that the band
floor pays it (§4b, at the floor's own coefficient `7/30`). -/

/-- **THRESHOLD 1 — THE GATE (`cfb_gate_decay`).**  Under
`M₀ ≥ (103/1500)·e·loglog X`,

  `seamT0 X · e^{−M₀/e} ≤ (log X)^{−1/500}`.

The exponent arithmetic is EXACT, not an estimate: `e^{−M₀/e} ≤ (log X)^{−103/1500}` and
`1/15 − 103/1500 = 100/1500 − 103/1500 = −3/1500 = −1/500`.  This is the whole reason the
gate's constant is `103/1500` and not something rounder. -/
theorem cfb_gate_decay {X M₀ : ℝ} (hX : Real.exp (Real.exp 1) ≤ X)
    (hgate : 103 / 1500 * Real.exp 1 * Real.log (Real.log X) ≤ M₀) :
    seamT0 X * Real.exp (-(1 / Real.exp 1) * M₀) ≤ Real.log X ^ (-(1 : ℝ) / 500) := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hstep : Real.exp (-(1 / Real.exp 1) * M₀) ≤ Real.log X ^ (-(103 : ℝ) / 1500) := by
    rw [Real.rpow_def_of_pos hL0]
    refine Real.exp_le_exp.mpr ?_
    have hinv : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgate hinv
    have hid : (1 / Real.exp 1) * (103 / 1500 * Real.exp 1 * Real.log (Real.log X))
        = 103 / 1500 * Real.log (Real.log X) := by
      field_simp
    rw [hid] at hmul
    nlinarith [hmul]
  have hT0 : (0 : ℝ) ≤ seamT0 X := seamT0_nonneg hL0.le
  calc seamT0 X * Real.exp (-(1 / Real.exp 1) * M₀)
      ≤ seamT0 X * Real.log X ^ (-(103 : ℝ) / 1500) :=
        mul_le_mul_of_nonneg_left hstep hT0
    _ = Real.log X ^ (-(1 : ℝ) / 500) := by
        unfold seamT0
        rw [← Real.rpow_add hL0]
        norm_num

/-- **THRESHOLD 2 — THE BAND FLOOR CLEARS THE GATE (`cfb_floor_clears_gate`).**  With
`L := loglog X` and the floor's own debits `D := (23/16)·logloglog X + (3/4)log q + (1/4)q + K`,

  `22·D ≤ L  ⟹  (103/1500)·e·L ≤ cfbM0 K q X`.

The margin is `7/30 − (103/1500)e ≥ 0.04667 ≥ 1/22`: the band's coefficient `7/30 = 0.2333`
against the gate's `0.18665`.  (`e < 2.7182818286` is the only numeric input.)  Compare
`CapFreeFloor`'s `1/32 = 0.03125`, which is `6×` SHORT of the gate — the refuter's K3
finding, and the reason this file re-derives the floor at band strength instead of consuming
`CapFreeAssembly.capFreeFloor3_all_chi`. -/
theorem cfb_floor_clears_gate {K : ℝ} {q : ℕ} {X : ℝ}
    (hLL : 0 ≤ Real.log (Real.log X))
    (hthr : 22 * ((23 / 16) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log q
              + (1 / 4) * (q : ℝ) + K) ≤ Real.log (Real.log X)) :
    103 / 1500 * Real.exp 1 * Real.log (Real.log X) ≤ cfbM0 K q X := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hmul : Real.exp 1 * Real.log (Real.log X)
      ≤ 2.7182818286 * Real.log (Real.log X) :=
    mul_le_mul_of_nonneg_right he.le hLL
  unfold cfbM0
  linarith

/-- **The ball-error side condition (`cfb_ballerr_le`).**  The centre bound's own additive
error `4·(log X)^{−1/2+1/1000}` must sit under the main exponential `e^{−M₀/(2e)}` for the
`C₁′`-rescale of §5 to be a rescale of `C₁` alone.  It does, with room: at the band floor
`M₀ ≈ (7/30)loglog X ≤ loglog X` the exponential is `≥ (log X)^{−1/(2e)} ≥ (log X)^{−0.184}`,
against `(log X)^{−0.499}`.  The named threshold is `4 ≤ (log X)^{315/1000}` — implied by any
of the corpus's `loglog X` gates many times over. -/
theorem cfb_ballerr_le {X M₀ : ℝ} (hX : Real.exp (Real.exp 1) ≤ X)
    (hM : M₀ ≤ Real.log (Real.log X))
    (hthr : 4 ≤ Real.log X ^ ((315 : ℝ) / 1000)) :
    4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith [Real.exp_one_gt_d9]
  have hP0 : (0 : ℝ) < Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_pos_of_pos hL0 _
  -- (i) the exponential is at least `(log X)^{−184/1000}`
  have hstep1 : Real.exp (-(1 / (2 * Real.exp 1)) * Real.log (Real.log X))
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) := by
    refine Real.exp_le_exp.mpr ?_
    have hc : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
    nlinarith [hM, hc]
  have hstep2 : Real.log X ^ (-(184 : ℝ) / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * Real.log (Real.log X)) := by
    rw [Real.rpow_def_of_pos hL0]
    refine Real.exp_le_exp.mpr ?_
    have hc : (1 : ℝ) / (2 * Real.exp 1) ≤ 184 / 1000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith [hLL, hc]
  -- (ii) the named threshold moves `4` across
  have hstep3 : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.log X ^ (-(184 : ℝ) / 1000) := by
    have hmul := mul_le_mul_of_nonneg_right hthr hP0.le
    have hsum : Real.log X ^ ((315 : ℝ) / 1000) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        = Real.log X ^ (-(184 : ℝ) / 1000) := by
      rw [← Real.rpow_add hL0]
      norm_num
    rw [hsum] at hmul
    linarith
  linarith

/-! ## §5 — THE EXIT

`cfbC₁` is the `C₁′` of the interface: the `X`-DEPENDENT coefficient catch #253 predicted,
carried symbolically with its `(log X)^{1/30}` factor explicit. -/

/-- **THE CAP-FREE BAND COEFFICIENT** (`cfbC₁`).  `C₁′ = (C₁ + 1)·√(seamT0 X)`, i.e.

  `cfbC₁ X C₁ = (C₁ + 1)·(log X)^{1/30}`.

The `(log X)^{1/30}` is the crude fold's whole price (`√` of the band's length `2T₀`), and
the `+1` absorbs the centre bound's additive error term `4(log X)^{−1/2+1/1000}` under the
side condition `cfb_ballerr_le`.  Catch #253: an `X`-dependent interface constant is
EXPECTED here — it is named, not hidden, and the gate of §4 is what pays for it. -/
def cfbC₁ (X C₁ : ℝ) : ℝ := (C₁ + 1) * Real.sqrt (seamT0 X)

lemma cfbC₁_sq {X C₁ : ℝ} (hX : 0 ≤ Real.log X) :
    cfbC₁ X C₁ ^ 2 = (C₁ + 1) ^ 2 * seamT0 X := by
  unfold cfbC₁
  rw [mul_pow, Real.sq_sqrt (seamT0_nonneg hX)]

lemma cfbC₁_nonneg {X C₁ : ℝ} (hC₁ : 1 ≤ C₁) : 0 ≤ cfbC₁ X C₁ := by
  unfold cfbC₁
  have : (0 : ℝ) ≤ C₁ + 1 := by linarith
  positivity

/-- **THE GATE, APPLIED TO THE INTERFACE SUMMAND** (`cfb_exit_summand_le`).  The first
summand of `ThmA2Rows.thm_a2'_of_rows`'s conclusion, read at this file's `C₁′`, is

  `8448·(cfbC₁ X C₁)²·e^{−M₀/e} = 8448·(C₁+1)²·(log X)^{1/15}·e^{−M₀/e}`

(`cfbC₁_sq`), and the gate `M₀ ≥ (103/1500)·e·loglog X` sends it under
`8448·(C₁+1)²·(log X)^{−1/500}` — the interface's own third-summand shape.  This is the whole
arithmetic purpose of the `(log X)^{1/30}` inside `cfbC₁`: it is paid for, in-statement, by
the gate, and `cfb_floor_clears_gate` is what makes the gate available from the band floor. -/
theorem cfb_exit_summand_le {X C₁ M₀ : ℝ} (hX : Real.exp (Real.exp 1) ≤ X) (hC₁ : 1 ≤ C₁)
    (hgate : 103 / 1500 * Real.exp 1 * Real.log (Real.log X) ≤ M₀) :
    8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
      ≤ 8448 * (C₁ + 1) ^ 2 * Real.log X ^ (-(1 : ℝ) / 500) := by
  obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hX
  have hL0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hlogX
  have hdec := cfb_gate_decay hX hgate
  have hsq := cfbC₁_sq (X := X) (C₁ := C₁) hL0.le
  have hc : (0 : ℝ) ≤ 8448 * (C₁ + 1) ^ 2 := by positivity
  calc 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
      = 8448 * (C₁ + 1) ^ 2 * (seamT0 X * Real.exp (-(1 / Real.exp 1) * M₀)) := by
        rw [hsq]; ring
    _ ≤ 8448 * (C₁ + 1) ^ 2 * Real.log X ^ (-(1 : ℝ) / 500) :=
        mul_le_mul_of_nonneg_left hdec hc

/-- **CFB-5 — THE CAP-FREE `T₀`-BAND SUPPLY (`cfb_t0band_supply`).**  The conclusion of
`T0Band.t0_band_supply`, WITHOUT `hMcap`:

  `∫_{−T₀}^{T₀} ‖dpolyA a (seamS0 N X) t‖² dt ≤ t0BandB X (cfbC₁ X C₁) M₀`,
  `T₀ = seamT0 X = (log X)^{1/15}`,

which is literally `ThmA2Rows.thm_a2'_of_rows`'s `hT0band` slot at `C₁′ := cfbC₁ X C₁` (the
slot's `C₁′` and `M₀` are free reals, so the plug is an instantiation, not a re-statement).

**What is carried, and why each binder is honest:**

* the four `Y`-gates and `hRHS` — upstream's own (`SupplyGeneric.center_halasz_supply_Y`),
  except that `hRHS` is now demanded at EVERY band frequency `t` rather than at the single
  centre `0`.  That is the entire cost of going cap-free: the joint head is graded per
  frequency, which is exactly what the head's own statement already quantifies over;
* `hfloor` — the band floor `M₀ ≤ 𝔻²(datum, n^{it}; X)` on `|t| ≤ T₀`, supplied by
  §3 (`band_floor_M0`) through the shift adapter `cfb_seam_floor_of_band`.  This REPLACES
  `hMcap`: an upper bound on the distance (false for `λ`) becomes a LOWER bound (true, and
  the stronger the better);
* `hErr` — the side condition `4(log X)^{−1/2+1/1000} ≤ e^{−M₀/(2e)}` of `cfb_ballerr_le`.

`hMcap` does not appear.  `transfer_at_scale`, `ballErr`, `bandSupS`'s error term and the
Cauchy weight are all unused (the exit's `t0BandB` still MENTIONS the error term — it is the
slot's own shape — but this proof only ever needs its nonnegativity). -/
theorem cfb_t0band_supply {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (C₁ M₀ : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 1 ≤ C₁ →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ t : ℝ, |t| ≤ seamT0 X → ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t : ℝ) : ℂ) * I)) (t₀ + t)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)) →
        (∀ t : ℝ, |t| ≤ seamT0 X →
            M₀ ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨X₁, hX₁0, hsupply⟩ := center_halasz_supply_Y hg t₀ Y
  refine ⟨max X₁ 3, lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro X N C₁ M₀ a hXlb hXN hN2 hC₁ hsupp hDatum hY10 hYsq hYlow hYlog hRHS hfloor hErr
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _) hXlb
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hT0 : (0 : ℝ) ≤ seamT0 X := seamT0_nonneg hlogX0
  set E : ℝ := Real.exp (-(1 / (2 * Real.exp 1)) * M₀) with hEdef
  set P : ℝ := Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) with hPdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hP0 : (0 : ℝ) ≤ P := Real.rpow_nonneg hlogX0 _
  have hB0 : (0 : ℝ) ≤ C₁ * E := by positivity
  have hS₀0 : (0 : ℝ) ≤ C₁ * E + 4 * P := by linarith
  -- §1 at every band frequency: the per-frequency, unweighted, cap-free sup
  have hsup : ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ (2 * (C₁ * E + 4 * P)) * (m : ℝ) := by
    intro t ht
    have hRHS' : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t : ℝ) : ℂ) * I)) (t₀ + t)
            (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
            (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
          ≤ (C₁ * E) * (k : ℝ) := by
      intro k h1 h2
      have h := hRHS t ht k h1 h2
      have hmono : Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X) ≤ E := by
        refine Real.exp_le_exp.mpr ?_
        have hc : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
        nlinarith [hfloor t ht, hc]
      have hk0 : (0 : ℝ) ≤ C₁ * (k : ℝ) := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
      have hstep : C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
          ≤ C₁ * (k : ℝ) * E := mul_le_mul_of_nonneg_left hmono hk0
      calc ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t : ℝ) : ℂ) * I)) (t₀ + t)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
          ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X) := h
        _ ≤ C₁ * (k : ℝ) * E := hstep
        _ = (C₁ * E) * (k : ℝ) := by ring
    have hcen := hsupply t X N (C₁ * E) hX1 hXN hN2 hB0 hY10 hYsq hYlow hYlog hRHS'
    exact cfb_sup_of_center hX0 hXN hS₀0 hsupp hDatum hcen
  -- §2: the crude fold
  have hint := band_integral_of_sup_crude (N := N) (a := a) (X := X) (R := seamT0 X)
    (S := 2 * (C₁ * E + 4 * P)) hX0 hT0 hXN hN2 hsupp hsup
  refine le_trans hint ?_
  -- the plug: `8·T₀·(2S₀)² ≤ 8·(2√2·C₁′·E)² ≤ t0BandB X C₁′ M₀`
  have hC1'0 : (0 : ℝ) ≤ cfbC₁ X C₁ := cfbC₁_nonneg hC₁
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htail : (0 : ℝ) ≤ bandTail X (seamT0 X) * (1 + seamT0 X) :=
    mul_nonneg (bandTail_nonneg hX3 hT0) (by linarith)
  have hinner : 2 * Real.sqrt 2 * (cfbC₁ X C₁ * E) ≤ t0BandS X (cfbC₁ X C₁) M₀ := by
    unfold t0BandS bandSupS
    nlinarith [hP0, hsqrt2, htail]
  have hinner0 : (0 : ℝ) ≤ 2 * Real.sqrt 2 * (cfbC₁ X C₁ * E) := by positivity
  have hsq : (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2 ≤ (t0BandS X (cfbC₁ X C₁) M₀) ^ 2 :=
    pow_le_pow_left₀ hinner0 hinner 2
  have hexpand : (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2
      = 8 * ((C₁ + 1) ^ 2 * seamT0 X * E ^ 2) := by
    have : (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2
        = 4 * Real.sqrt 2 ^ 2 * (cfbC₁ X C₁ ^ 2 * E ^ 2) := by ring
    rw [this, hsq2, cfbC₁_sq hlogX0]
    ring
  -- `S₀ ≤ (C₁+1)·E` by the side condition, so `S₀² ≤ (C₁+1)²E²`
  have hS₀le : C₁ * E + 4 * P ≤ (C₁ + 1) * E := by
    have hexp : (C₁ + 1) * E = C₁ * E + E := by ring
    rw [hexp]
    linarith [hErr]
  have hS₀sq : (C₁ * E + 4 * P) ^ 2 ≤ ((C₁ + 1) * E) ^ 2 :=
    pow_le_pow_left₀ hS₀0 hS₀le 2
  have hfinal : 8 * seamT0 X * (2 * (C₁ * E + 4 * P)) ^ 2
      ≤ 8 * (t0BandS X (cfbC₁ X C₁) M₀) ^ 2 := by
    have h1 : 8 * seamT0 X * (2 * (C₁ * E + 4 * P)) ^ 2
        ≤ 32 * seamT0 X * ((C₁ + 1) ^ 2 * E ^ 2) := by
      have hE2 : (0 : ℝ) ≤ E ^ 2 := sq_nonneg E
      nlinarith [hS₀sq, hT0]
    have h2 : 32 * seamT0 X * ((C₁ + 1) ^ 2 * E ^ 2)
        ≤ 8 * (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2 := by
      rw [hexpand]
      nlinarith [hT0, sq_nonneg E, sq_nonneg (C₁ + 1)]
    have h3 : 8 * (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2
        ≤ 8 * (t0BandS X (cfbC₁ X C₁) M₀) ^ 2 := by linarith
    linarith
  unfold t0BandB
  linarith

/-! ### The floor's delivery into the exit's `hfloor` slot

One adapter, one use.  `HalaszHead.seamCoeff_trivial_dist_eq` translates the frequency by
`t₀` EXACTLY (no error term, since the trivial indicator puts every prime in window), and
`CapFreeArm.pretDistSq_ellLin_eq` says the linearisation is invisible to `𝔻²`. -/

/-- **THE SHIFT ADAPTER (`cfb_seam_floor_of_band`).**  A band floor stated in the BARE
frequency `v` on `|v| ≤ 2·seamT0 X + 1` supplies the exit's `hfloor` at the seam datum
`seamCoeff (ellLin (liouChi χ)) 1 t₀`, provided the seam frequency itself is band-sized
(`|t₀| ≤ seamT0 X + 1`).

**The trap, pinned**: the floor is read at `t + t₀`, never at `t`.  `|t| ≤ seamT0 X` and
`|t₀| ≤ seamT0 X + 1` give `|t + t₀| ≤ 2·seamT0 X + 1`, which is exactly the range
`band_floor_M0` quantifies over — the two ranges were chosen to match, and neither is
`seamRad`-sized. -/
theorem cfb_seam_floor_of_band {q : ℕ} (χ : DirichletCharacter ℂ q) {X t₀ M : ℝ}
    (ht₀ : |t₀| ≤ seamT0 X + 1)
    (hband : ∀ v : ℝ, |v| ≤ 2 * seamT0 X + 1 → M ≤ pretDistSq (liouChi χ) (costwist v) X) :
    ∀ t : ℝ, |t| ≤ seamT0 X →
      M ≤ pretDistSq (seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀) (costwist t) X := by
  intro t ht
  rw [seamCoeff_trivial_dist_eq, pretDistSq_ellLin_eq]
  refine hband (t + t₀) ?_
  calc |t + t₀| ≤ |t| + |t₀| := abs_add_le t t₀
    _ ≤ seamT0 X + (seamT0 X + 1) := add_le_add ht ht₀
    _ = 2 * seamT0 X + 1 := by ring

/-- **CFB-5′ — THE EXIT AT THE `χ`-DATUM (`cfb_t0band_supply_chi`).**  `cfb_t0band_supply`
with `g := liouChi χ` and the floor slot DISCHARGED from §3: for every finite modulus range
`Q` there is a `K ≥ 0` (the assembled band constant) such that, past the scale floor and the
band's own threshold, the `hT0band` datum holds at

  `C₁′ = cfbC₁ X C₁ = (C₁+1)(log X)^{1/30}`,  `M₀ = cfbM0 K q X`.

The remaining binders are upstream's (`Y`-gates, `hRHS` per band frequency) plus the two
band-geometry hypotheses `|t₀| ≤ seamT0 X + 1` and the `cfb_ballerr_le` side condition.  This
is the statement the M4 datum consumes; `cfb_floor_clears_gate` + `cfb_gate_decay` are what
turn its `M₀` into the interface's `(log X)^{−1/500}`. -/
theorem cfb_t0band_supply_chi (Q : ℕ) :
    ∃ (K : ℝ) (X₀ : ℝ), 0 ≤ K ∧ 0 < X₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t₀ : ℝ) (Y : ℝ → ℝ), q ≤ Q →
        ∃ X₁ : ℝ, 0 < X₁ ∧
          ∀ (X : ℝ) (N : ℕ) (C₁ : ℝ) (a : ℕ → ℂ),
            X₁ ≤ X → X₀ ≤ X → Real.exp (Real.exp 1) ≤ X →
            X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 1 ≤ C₁ → |t₀| ≤ seamT0 X + 1 →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, X < (n : ℝ) →
              a n = seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀ n) →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ Y (k : ℝ)) →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
                Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
            (∀ t : ℝ, |t| ≤ seamT0 X → ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
                ‖prop21RHS (fun p => liouChi χ p * (p : ℂ) ^ (-((t₀ + t : ℝ) : ℂ) * I))
                    (t₀ + t) (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
                    (1 + 1 / Real.log (k : ℝ)) (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
                  ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                      * pretDistSq (seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀)
                          (costwist t) X)) →
            4 ≤ Real.log X ^ ((315 : ℝ) / 1000) →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X (cfbC₁ X C₁) (cfbM0 K q X) := by
  obtain ⟨K, hK0, hK⟩ := band_floor_M0_liouChi Q
  refine ⟨K, Real.exp (Real.exp 1), hK0, Real.exp_pos _, ?_⟩
  intro q _ χ t₀ Y hq
  obtain ⟨X₁, hX₁0, hexit⟩ :=
    cfb_t0band_supply (g := liouChi χ) (fun p _ => norm_liouChi_le_one χ p) t₀ Y
  refine ⟨X₁, hX₁0, ?_⟩
  intro X N C₁ a hX1 _hX0 hXe hXN hN2 hC₁ ht₀ hsupp hDatum hY10 hYsq hYlow hYlog hRHS hthr
  -- `M₀ ≤ loglog X` is not a binder: the floor's own shape gives it (all debits are `≥ 0`)
  have hM0 : cfbM0 K q X ≤ Real.log (Real.log X) := by
    obtain ⟨hX8, hlogX, hLL, hLLL⟩ := cff_scale_facts hXe
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
    unfold cfbM0
    linarith
  refine hexit X N C₁ (cfbM0 K q X) a hX1 hXN hN2 hC₁ hsupp hDatum hY10 hYsq hYlow hYlog
    hRHS ?_ ?_
  · exact cfb_seam_floor_of_band χ ht₀ (fun v hv => hK q χ X v hq hXe hv)
  · exact cfb_ballerr_le hXe hM0 hthr

end Salt.MR
