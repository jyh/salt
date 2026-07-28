/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.T0BandCapFree

/-!
# M4-6 — THE QUALITY SUPPLY (`M4Quality`)

The M4 row needs one thing from the floor library: that the `M₀` slot the mean-square exit
carries can be instantiated at a value which **exceeds the constant-in-`X` demand**

  `M₀ ≥ (5e/2)·log W`,   `W = (log H)^{12}` the door's modulus cap.

Nothing else about the floor is consumed — `ThmA2Rows.thm_a2'` carries `M₀` as a FREE real,
gated only by `hT0band`, and the summand it feeds is

  `8448·C₁′²·exp(−M₀/e)`

(**`exp(−M₀/e)`, never `exp(−M₀/2)`** — the stale halving understates the demand by `2.7×`;
`ThmA2Rows.lean:691` is the byte).  `m4_exit_decay_of_quality` below prints exactly what the
demand buys: `exp(−M₀/e) ≤ W^{−5/2}`, the `W`-saving the χ-sum of M4-3 spends.

## The rewire (council C3 + SIEGEL-REGIME)

This file consumes the LANDED floor library and NOTHING retired: **not**
`chi_floor_real_door_12`, **not** `L1LowerEffective`.  Two suppliers, at two coefficients:

| branch | supplier | coefficient on `loglog X` |
|---|---|---|
| the `T₀`-band `M₀` the exit carries | `T0BandCapFree.band_floor_M0_liouChi` | `7/30` |
| the bounded band `|t| ≤ 1`, per class | `SiegelBand.siegelBandB_spec` (D3-2) | `1` |

The C3 upgrade is the second row: on the band the floor's coefficient is `1`, so the demand
is subsumed by the single threshold `loglog X ≥ C + (5e/2)·log W` — no `30/7` inflation, no
`logloglog` debit, no `q`-content beyond the constant.  At the door's `W` the demand reads
`30e·loglog H ≈ 81.55·loglog H` (`m4Demand_door`) — the flags entry's `81.6·loglog Hhi`.

## THE THREE LOG-SCALES, pinned per line (the sharpest point on the road)

* **the demand** `(5e/2)·log W` is `loglog H`-grade — `H` is the window length, `X` never
  enters it.  It is CONSTANT in `X`; that is the whole reason the regime lever can pay it.
* **the floors** `cfbM0 K q X`, `loglog X − siegelBandB Q` are `loglog X`-grade.
* **the thresholds** mix them: `loglog X ≥ (Hhi-only constant)`.  Every threshold below is
  stated with `loglog X` alone on the right and `Hhi`-only material on the left, EXCEPT
  `m4_quality_of_band`, which keeps the floor's own `logloglog X` debit in-statement (the
  exact arithmetic); `m4_log_le_div_eighty` is the one absorption step that removes it, at
  the anchor `loglog X ≥ 1000`.

## The `Bfun` slot (the regime arm)

`SiegelBand`'s `siegelBandB`, `CapFreeAssembly`'s `cffK` and this file's `cfbK` are three
`Classical.choose` constants of the same genre: `X`-free, `Q`-only, ineffective (they inherit
the EVT minimum of `SiegelArm`'s `LFunction_band_lower`).  `m4QualityB` is the SINGLE named
constant dominating all of them (plus the VK/mid debits, `m4VKdebit`), and `m4JointThr` is
the SINGLE inequality the spine's `g`-arm clears:

  `m4JointThr Bfun Hhi ≤ loglog x`.

It is a four-armed `max`: the absorption anchor `1000`, the quality arm (the `T₀`-band `M₀`
against the demand), the band arm (coefficient `1`), and the cap-free arm (`CapFreeFloor3`'s
own `40·logloglog + 32(…+25)` threshold, absorbed).  `Bfun : ℕ → ℝ` stays a PARAMETER
throughout — the row's mean-square exit (`M4MeanSq.m4_meansq_per_chi`, and upstream
`cfb_t0band_supply_chi`) carries its band constant `Kb` as a LEADING existential and prices
`exp(−cfbM0 Kb q X/e)`, so its consumer instantiates `Bfun := fun _ => Kb` (or the `max` with
`m4QualityB`) INSIDE the `obtain` — refuter catch K6, the regime must be drawn inside the
capstone's existential scope.  A consumer on the named-choice route takes
`Bfun := m4QualityB` directly.  `m4_quality_of_joint`'s `hK : K ≤ Bfun (m4Wnat Hhi)` is the
slot both routes use.

## Datum hygiene (the `lam` collision)

Floors may speak `lamChi χ = lam·χ̄` (prime-equal to the truth); the ROW sums its datum over
integers and must be fed `liouChi χ` (`M4Residue.liouvilleC`-built).  Every statement below
names which datum it speaks, and `CapFreeAssembly.pretDistSq_liouChi_eq` is the (equality)
transport.  `cfbK_spec` is stated at `liouChi` because that is what the exit consumes.
-/

namespace Salt.MR

/-! ## §1 — the door's modulus cap and the demand

`W = (log H)^{12}` is `H`-only (the `arcDen 12 H` of `BigXiArc`, in `ℕ`-power form — the
shape `M4Residue.logH_pow_twelve_lt` and `SiegelBand.modulus_bound_mono` both speak).  The
demand is `(5e/2)·log W`: a CONSTANT in `X`. -/

/-- **The door's modulus cap** `W(H) = (log H)^{12}`.  `H`-scale; `X` does not occur. -/
noncomputable def m4W (H : ℕ) : ℝ := Real.log (H : ℝ) ^ (12 : ℕ)

/-- The cap as a `ℕ` modulus range — the `Q` slot of every finite-range floor
(`siegelBandB`, `cffK`, `cfbK`). -/
noncomputable def m4Wnat (H : ℕ) : ℕ := ⌈m4W H⌉₊

/-- **THE QUALITY DEMAND** `M(datum; X) ≥ (5e/2)·log W`.  Constant in `X`; the `5e/2` is
forced by the exit's `exp(−M₀/e)` (see `m4_exit_decay_of_quality`), NOT by a stale
`exp(−M₀/2)`. -/
noncomputable def m4Demand (W : ℝ) : ℝ := 5 * Real.exp 1 / 2 * Real.log W

/-- **The demand at the door's cap**: `(5e/2)·log((log H)^{12}) = 30e·loglog H ≈ 81.55·loglog H`
— the `81.6·loglog Hhi` of the SIEGEL-REGIME entry.  `Real.log_pow` is unconditional, so
this identity carries no side condition. -/
theorem m4Demand_door (H : ℕ) :
    m4Demand (m4W H) = 30 * Real.exp 1 * Real.log (Real.log (H : ℝ)) := by
  unfold m4Demand m4W
  rw [Real.log_pow]
  push_cast
  ring

/-- `1 ≤ W(H)` from `1 ≤ log H` — the only positivity the thresholds need. -/
theorem one_le_m4W {H : ℕ} (h : 1 ≤ Real.log (H : ℝ)) : 1 ≤ m4W H :=
  one_le_pow₀ h

/-- The demand is nonnegative once the cap is (`log W ≥ 0`). -/
theorem m4Demand_nonneg {W : ℝ} (hW : 1 ≤ W) : 0 ≤ m4Demand W := by
  have h1 : (0 : ℝ) ≤ Real.log W := Real.log_nonneg hW
  have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  unfold m4Demand
  positivity

/-! ## §2 — what the exit consumes

`thm_a2'`'s `M₀` is a free real gated by `hT0band`; the row's price is `8448·C₁′²·exp(−M₀/e)`.
The quality demand is consumed as an EXCEEDANCE only — never the floor's magnitude. -/

/-- **THE PROVENANCE PIN** (`exp(−M₀/e)`, not `exp(−M₀/2)`).  The demand `M₀ ≥ (5e/2)·log W`
turns the exit summand's exponential into the `W`-saving `W^{−5/2}`:

  `exp(−M₀/e) ≤ W^{−5/2}`.

The `e` in `5e/2` cancels the `1/e` in the exponent EXACTLY — that is where the constant
comes from, and why halving it (`exp(−M₀/2)` would demand only `5·log W/2 · 2/2`) understates
the target by the factor `e/2 ≈ 1.36` per unit and `2.7×` in the constant. -/
theorem m4_exit_decay_of_quality {W M₀ : ℝ} (hW : 1 ≤ W) (hM : m4Demand W ≤ M₀) :
    Real.exp (-(1 / Real.exp 1) * M₀) ≤ W ^ (-(5 : ℝ) / 2) := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  unfold m4Demand at hM
  have h := mul_le_mul_of_nonneg_left hM (le_of_lt (one_div_pos.mpr he))
  have hid : 1 / Real.exp 1 * (5 * Real.exp 1 / 2 * Real.log W) = 5 / 2 * Real.log W := by
    field_simp
  rw [hid] at h
  rw [Real.rpow_def_of_pos hW0]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [h]

/-! ## §3 — THE QUALITY SUPPLY AT THE `T₀`-BAND `M₀` (deliverable 1)

`cfbM0 K q X = (7/30)·loglog X − (23/16)·logloglog X − (3/4)·log q − (1/4)·q − K` is the
value the exit's `M₀` slot actually receives (`cfb_t0band_supply_chi`).  Its coefficient is
the weakest of CFB's three arms (`7/30`, the non-real mid branch), so the composition against
the demand is the `30/7`-inflated one. -/

/-- The band floor is antitone in its assembled constant: a LARGER `K` is a weaker floor.
This is what lets every threshold be stated at one dominating constant. -/
theorem cfbM0_antitone_K {K K' : ℝ} (h : K ≤ K') (q : ℕ) (X : ℝ) :
    cfbM0 K' q X ≤ cfbM0 K q X := by
  unfold cfbM0
  linarith

/-- **`m4_quality_of_band` — THE QUALITY STATEMENT, exact form.**  `M₀ := cfbM0 K q X` is
ADMISSIBLE for the demand `(5e/2)·log W` once

  `(30/7)·( (5e/2)·log W + (23/16)·logloglog X + (3/4)·log q + (1/4)·q + K ) ≤ loglog X`.

Pure arithmetic composition of CFB's coefficients: the `30/7` is the reciprocal of the
floor's `7/30`, and every debit of `cfbM0` appears once inside the bracket.  The
`logloglog X` stays IN-STATEMENT here — this is the sharp form; `m4_quality_of_band_hhi`
absorbs it into an `Hhi`-only threshold. -/
theorem m4_quality_of_band {K W : ℝ} {q : ℕ} {X : ℝ}
    (hthr : (30 / 7) * (m4Demand W + (23 / 16) * Real.log (Real.log (Real.log X))
              + (3 / 4) * Real.log q + (1 / 4) * (q : ℝ) + K) ≤ Real.log (Real.log X)) :
    m4Demand W ≤ cfbM0 K q X := by
  unfold cfbM0
  linarith

/-- **The `logloglog` absorption** (`log L ≤ L/80` for `L ≥ 1000`).  The one step that turns
an `X`-dependent debit into a threshold arm.  Proof: `log L = log 128 + log(L/128) ≤
log 128 + L/128 − 1` and `log 128 = 7·log 2 < 4.8521`, so `log L ≤ L/128 + 3.8521`; the gap
`1/80 − 1/128 = 3/640` then pays it, since `(3/640)·1000 = 4.6875 ≥ 3.8521`. -/
theorem m4_log_le_div_eighty {L : ℝ} (hL : 1000 ≤ L) : Real.log L ≤ L / 80 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsplit : Real.log L = Real.log 128 + Real.log (L / 128) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have hsub : Real.log (L / 128) ≤ L / 128 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlog128 : Real.log 128 ≤ 4.8521 := by
    have h7 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h7]
    linarith [Real.log_two_lt_d9]
  linarith

/-- **`m4_quality_of_band_hhi` — the `Hhi`-only quality threshold.**  With the `logloglog`
debit absorbed (`7/30 − 23/1280 ≥ 1/5`) and the `q`-content pushed to the cap `W`, the whole
demand clears at

  `loglog X ≥ 1000`  and  `5·( (5e/2)·log W + (3/4)·log W + (1/4)·W + K ) ≤ loglog X`,

a threshold in `W` and `K` ALONE — no `X` on the left.  Both are `Hhi`-only at `W = m4W Hhi`,
which is exactly what the regime lever absorbs.  (The `(1/4)·W` debit is astronomically
large in `Hhi` and completely harmless: it is `X`-free.) -/
theorem m4_quality_of_band_hhi {K W : ℝ} {q : ℕ} {X : ℝ}
    (hq1 : (1 : ℝ) ≤ (q : ℝ)) (hqW : (q : ℝ) ≤ W)
    (hL : 1000 ≤ Real.log (Real.log X))
    (hthr : 5 * (m4Demand W + (3 / 4) * Real.log W + (1 / 4) * W + K)
              ≤ Real.log (Real.log X)) :
    m4Demand W ≤ cfbM0 K q X := by
  have habs : Real.log (Real.log (Real.log X)) ≤ Real.log (Real.log X) / 80 :=
    m4_log_le_div_eighty hL
  have hlogq : Real.log q ≤ Real.log W :=
    Real.log_le_log (by linarith) hqW
  unfold cfbM0
  linarith

/-! ## §4 — THE PER-CLASS UPGRADE: the band branch at coefficient `1` (deliverable 2)

`SiegelBand`'s stone 2 (`chi_floor_band_uniform`, named at `siegelBandB`) delivers
`loglog X − C ≤ 𝔻²` on `|t| ≤ 1` with coefficient EXACTLY `1` — no `k²` division, no
`primeDivSum`, no per-χ `X₀`, no `q`-gate.  Against a demand that is CONSTANT in `X` the
composition is therefore a single subtraction: the band branch subsumes the demand trivially,
at `loglog X ≥ C + (5e/2)·log W`.  Compare §3's `30/7`-inflated threshold: the band branch is
`4.3×` cheaper in `loglog X`, which is why C3 rewires the band here. -/

/-- **THE C3 BRANCH LEMMA (pretentious datum).**  On `|t| ≤ 1`, every `χ mod q` with
`q ≤ Q` clears the demand once `loglog X ≥ B + (5e/2)·log W`, for any `B ≥ siegelBandB Q`.
`SiegelBand.quality_gate_threshold` is the arithmetic; `siegelBandB_spec` is the floor. -/
theorem m4_quality_band_coeff_one (Q : ℕ) {B : ℝ} (hB : siegelBandB Q ≤ B) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
      ∀ X t W : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        B + m4Demand W ≤ Real.log (Real.log X) →
        m4Demand W ≤ pretDistSq (lamChi χ) (costwist t) X := by
  intro q _ χ hq X t W hX ht hthr
  have h := siegelBandB_spec Q q χ hq X t hX ht
  linarith

/-- **THE C3 BRANCH LEMMA at the ROW's datum.**  The same at `liouChi χ` (the
`liouvilleC`-built datum the row sums over integers) — `pretDistSq_liouChi_eq` is an
EQUALITY, so nothing is lost crossing the `lam` collision. -/
theorem m4_quality_band_coeff_one_liouChi (Q : ℕ) {B : ℝ} (hB : siegelBandB Q ≤ B) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
      ∀ X t W : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        B + m4Demand W ≤ Real.log (Real.log X) →
        m4Demand W ≤ pretDistSq (liouChi χ) (costwist t) X := by
  intro q _ χ hq X t W hX ht hthr
  rw [pretDistSq_liouChi_eq]
  exact m4_quality_band_coeff_one Q hB q χ hq X t W hX ht hthr

/-- **The band branch at the door's cap.**  The threshold in the flags entry's own numerals:
`loglog X ≥ B + 30e·loglog Hhi` (`30e ≈ 81.55`). -/
theorem m4_quality_band_door (Q : ℕ) {B : ℝ} (hB : siegelBandB Q ≤ B) {Hhi : ℕ} :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        B + 30 * Real.exp 1 * Real.log (Real.log (Hhi : ℝ)) ≤ Real.log (Real.log X) →
        m4Demand (m4W Hhi) ≤ pretDistSq (liouChi χ) (costwist t) X := by
  intro q _ χ hq X t hX ht hthr
  refine m4_quality_band_coeff_one_liouChi Q hB q χ hq X t (m4W Hhi) hX ht ?_
  rw [m4Demand_door]
  exact hthr

/-! ## §5 — THE `W`-MONOTONICITY GLUE (deliverable 3)

The door quantifies over `q ≤ W(H)` at EVERY window length `H` in `[Hlo, Hhi]`; the regime
consumes at `Hhi` alone.  `SiegelBand.modulus_bound_mono` is the `ℕ`-ceiling form; the two
lemmas here are the real-valued pin the door actually produces
(`(q : ℝ) ≤ (log H)^{12}`, `M4Residue.logH_pow_twelve_lt`'s genre) and the bridge into the
`ℕ` modulus range the floors take. -/

/-- `W` is monotone in the window length (`log ≥ 0` needs `1 ≤ H`; that is the honest floor,
without it the `12`-th power is not monotone). -/
theorem m4W_mono {H Hhi : ℕ} (hH : 1 ≤ H) (hle : H ≤ Hhi) : m4W H ≤ m4W Hhi := by
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlog0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg hH1
  have hlogle : Real.log (H : ℝ) ≤ Real.log (Hhi : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hle)
  exact pow_le_pow_left₀ hlog0 hlogle 12

/-- **The real-valued transport.**  A modulus admitted at window length `H` is admitted at
every `Hhi ≥ H`. -/
theorem m4_modulus_le {H Hhi q : ℕ} (hH : 1 ≤ H) (hle : H ≤ Hhi)
    (hq : (q : ℝ) ≤ m4W H) : (q : ℝ) ≤ m4W Hhi :=
  le_trans hq (m4W_mono hH hle)

/-- **The bridge into the `ℕ` modulus range.**  From the door's real-valued pin
`(q : ℝ) ≤ (log H)^{12}` to the `Q`-slot `q ≤ m4Wnat Hhi` that `siegelBandB`, `cffK` and
`cfbK` all quantify over — one instantiation at `Hhi` serves the whole window range. -/
theorem m4_modulus_nat_le {H Hhi q : ℕ} (hH : 1 ≤ H) (hle : H ≤ Hhi)
    (hq : (q : ℝ) ≤ m4W H) : q ≤ m4Wnat Hhi := by
  have h : (q : ℝ) ≤ m4W Hhi := m4_modulus_le hH hle hq
  have h2 : ⌈(q : ℝ)⌉₊ ≤ ⌈m4W Hhi⌉₊ := Nat.ceil_mono h
  rwa [Nat.ceil_natCast] at h2

/-- `m4Wnat` inherits `SiegelBand.modulus_bound_mono` verbatim (the two are the same
ceiling). -/
theorem m4Wnat_mono {H Hhi q : ℕ} (hH : 1 ≤ H) (hle : H ≤ Hhi) (hq : q ≤ m4Wnat H) :
    q ≤ m4Wnat Hhi :=
  modulus_bound_mono hH hle hq

/-- **THE WINDOW CAPSTONE.**  The quality supply at a SINGLE constant
`B ≥ siegelBandB (m4Wnat Hhi)` and a SINGLE demand `m4Demand (m4W Hhi)`, valid for every
window length `H ≤ Hhi` and every modulus the door admits at that `H`.  This is the shape the
regime arm consumes: everything on the left of the threshold is `Hhi`-only. -/
theorem m4_quality_band_window {H Hhi : ℕ} (hH : 1 ≤ H) (hle : H ≤ Hhi) {B : ℝ}
    (hB : siegelBandB (m4Wnat Hhi) ≤ B) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ m4W H →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        B + m4Demand (m4W Hhi) ≤ Real.log (Real.log X) →
        m4Demand (m4W Hhi) ≤ pretDistSq (liouChi χ) (costwist t) X := by
  intro q _ χ hq X t hX ht hthr
  exact m4_quality_band_coeff_one_liouChi (m4Wnat Hhi) hB q χ
    (m4_modulus_nat_le hH hle hq) X t (m4W Hhi) hX ht hthr

/-! ## §6 — THE REGIME ARM (deliverable 4)

Three `Classical.choose` constants of one genre live on this road: `siegelBandB` (the band
floor, `SiegelBand`), `cffK` (the cap-free box floor, `CapFreeAssembly`) and `cfbK` (the
`T₀`-band `M₀`, minted here from `band_floor_M0_liouChi`).  A fourth `Q`-only debit, the
VK/mid pair, is `q`-dependent inside the range and is maxed here (`m4VKdebit`).

`m4QualityB` is the SINGLE named constant dominating all four; `m4JointThr` is the SINGLE
threshold the `g`-arm clears.  All four ride SYMBOLICALLY — the pearl (the ineffective EVT
minimum) is inside `siegelBandB` and never evaluated. -/

/-- **The `T₀`-band `M₀` constant, named** (`cfbK`).  `siegelBandB`'s genre: the `K` of
`band_floor_M0_liouChi`, at the ROW's datum (`liouChi`). -/
noncomputable def cfbK (Q : ℕ) : ℝ := Classical.choose (band_floor_M0_liouChi Q)

theorem cfbK_nonneg (Q : ℕ) : 0 ≤ cfbK Q :=
  (Classical.choose_spec (band_floor_M0_liouChi Q)).1

/-- The defining property of `cfbK` — `band_floor_M0_liouChi`'s body at the chosen
constant. -/
theorem cfbK_spec (Q : ℕ) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X v : ℝ), q ≤ Q →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
        cfbM0 (cfbK Q) q X ≤ pretDistSq (liouChi χ) (costwist v) X :=
  (Classical.choose_spec (band_floor_M0_liouChi Q)).2

/-- **The VK/mid debit, maxed over the modulus range.**  `vkDebitConst (vkEulerCorr q ·
vkTwistConst q) + vkMidDebit q` is `X`-free but `q`-dependent; over the FINITE range `q ≤ Q`
a single sup serves.  (`vkMidDebit ≈ (1/4)e^{100}`-grade — symbolic, never evaluated.) -/
noncomputable def m4VKdebit (Q : ℕ) : ℝ :=
  (Finset.range (Q + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero Q))
    (fun q => vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q)

theorem m4VKdebit_spec {Q q : ℕ} (hq : q ≤ Q) :
    vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q ≤ m4VKdebit Q :=
  Finset.le_sup' (fun q => vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))

/-- **THE SINGLE NAMED CONSTANT the regime `g`-arm consumes.**  Dominates the three floor
constants and the VK/mid debit at one modulus range.  `X`-free, `Q`-only, ineffective. -/
noncomputable def m4QualityB (Q : ℕ) : ℝ :=
  max (cfbK Q) (max (siegelBandB Q) (max (cffK Q) (m4VKdebit Q)))

theorem cfbK_le_m4QualityB (Q : ℕ) : cfbK Q ≤ m4QualityB Q := le_max_left _ _

theorem siegelBandB_le_m4QualityB (Q : ℕ) : siegelBandB Q ≤ m4QualityB Q :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem cffK_le_m4QualityB (Q : ℕ) : cffK Q ≤ m4QualityB Q :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)

theorem m4VKdebit_le_m4QualityB (Q : ℕ) : m4VKdebit Q ≤ m4QualityB Q :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

theorem m4QualityB_nonneg (Q : ℕ) : 0 ≤ m4QualityB Q :=
  le_trans (cfbK_nonneg Q) (cfbK_le_m4QualityB Q)

/-- **Arm 1 — the quality arm** (`§3`'s `Hhi`-only threshold at `W = m4W Hhi`). -/
noncomputable def m4QualArm (B : ℝ) (Hhi : ℕ) : ℝ :=
  5 * (m4Demand (m4W Hhi) + (3 / 4) * Real.log (m4W Hhi) + (1 / 4) * m4W Hhi + B)

/-- **Arm 2 — the band arm** (`§4`'s coefficient-`1` threshold). -/
noncomputable def m4BandArm (B : ℝ) (Hhi : ℕ) : ℝ := B + m4Demand (m4W Hhi)

/-- **Arm 3 — the cap-free arm**: `CapFreeAssembly.cffK_spec`'s own threshold
`40·logloglog X + 32·((1/8)log q + (1/4)q + vkDebit + K + 25) < loglog X`, with the
`logloglog` absorbed (`40·log L ≤ L/2` at `L ≥ 1000`), the `q`-content pushed to `W`, and
both `K` and the VK/mid debit paid by the single `B` (hence the `2·B`).  The trailing `+1`
is what makes the consumed inequality STRICT. -/
noncomputable def m4CffArm (B : ℝ) (Hhi : ℕ) : ℝ :=
  64 * ((1 / 8) * Real.log (m4W Hhi) + (1 / 4) * m4W Hhi + 2 * B + 25) + 1

/-- **THE JOINT THRESHOLD — the ONE inequality the spine's `g` clears.**

  `m4JointThr Bfun Hhi ≤ loglog x`,

a four-armed `max`: the absorption anchor `1000`, the quality arm, the band arm and the
cap-free arm, each read at `Bfun (m4Wnat Hhi)`.  EVERY arm is `Hhi`-only — no `x` occurs — so
the regime lever (`g R.Hhi R.ω ≤ R.x`, `RegimeHead.gJoin`'s genre: a `⌈exp exp(·)⌉₊` arm)
absorbs it wholesale.  `Bfun : ℕ → ℝ` is a PARAMETER slot (the `X0MR` idiom): instantiate at
`m4QualityB` on the named-choice route, or at `fun _ => K` inside a capstone's `obtain`. -/
noncomputable def m4JointThr (Bfun : ℕ → ℝ) (Hhi : ℕ) : ℝ :=
  max 1000
    (max (m4QualArm (Bfun (m4Wnat Hhi)) Hhi)
      (max (m4BandArm (Bfun (m4Wnat Hhi)) Hhi) (m4CffArm (Bfun (m4Wnat Hhi)) Hhi)))

theorem m4JointThr_anchor (Bfun : ℕ → ℝ) (Hhi : ℕ) : 1000 ≤ m4JointThr Bfun Hhi :=
  le_max_left _ _

theorem m4JointThr_qual (Bfun : ℕ → ℝ) (Hhi : ℕ) :
    m4QualArm (Bfun (m4Wnat Hhi)) Hhi ≤ m4JointThr Bfun Hhi :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem m4JointThr_band (Bfun : ℕ → ℝ) (Hhi : ℕ) :
    m4BandArm (Bfun (m4Wnat Hhi)) Hhi ≤ m4JointThr Bfun Hhi :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)

theorem m4JointThr_cff (Bfun : ℕ → ℝ) (Hhi : ℕ) :
    m4CffArm (Bfun (m4Wnat Hhi)) Hhi ≤ m4JointThr Bfun Hhi :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

/-! ### The three discharges from the one inequality -/

/-- **DISCHARGE 1 — the quality supply.**  Under the joint threshold, the exit's `M₀` slot at
`cfbM0 K q X` exceeds the demand, for every modulus the door admits at any `H ≤ Hhi` and
every `K` the capstone's existential produced (paid by `Bfun (m4Wnat Hhi)`). -/
theorem m4_quality_of_joint {Bfun : ℕ → ℝ} {Hhi H q : ℕ} {X K : ℝ}
    (hH : 1 ≤ H) (hle : H ≤ Hhi) (hq1 : 1 ≤ q) (hqW : (q : ℝ) ≤ m4W H)
    (hK : K ≤ Bfun (m4Wnat Hhi))
    (hL : m4JointThr Bfun Hhi ≤ Real.log (Real.log X)) :
    m4Demand (m4W Hhi) ≤ cfbM0 K q X := by
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqHhi : (q : ℝ) ≤ m4W Hhi := m4_modulus_le hH hle hqW
  have hanchor : (1000 : ℝ) ≤ Real.log (Real.log X) :=
    le_trans (m4JointThr_anchor Bfun Hhi) hL
  have harm : m4QualArm (Bfun (m4Wnat Hhi)) Hhi ≤ Real.log (Real.log X) :=
    le_trans (m4JointThr_qual Bfun Hhi) hL
  refine m4_quality_of_band_hhi hq1R hqHhi hanchor ?_
  unfold m4QualArm at harm
  linarith

/-- **DISCHARGE 2 — the band branch at coefficient `1`.**  The C3 upgrade, from the same
inequality. -/
theorem m4_band_of_joint {Bfun : ℕ → ℝ} {Hhi H : ℕ} (hH : 1 ≤ H) (hle : H ≤ Hhi)
    (hB : siegelBandB (m4Wnat Hhi) ≤ Bfun (m4Wnat Hhi)) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ m4W H →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        m4JointThr Bfun Hhi ≤ Real.log (Real.log X) →
        m4Demand (m4W Hhi) ≤ pretDistSq (liouChi χ) (costwist t) X := by
  intro q _ χ hq X t hX ht hL
  refine m4_quality_band_window hH hle hB q χ hq X t hX ht ?_
  have harm : m4BandArm (Bfun (m4Wnat Hhi)) Hhi ≤ Real.log (Real.log X) :=
    le_trans (m4JointThr_band Bfun Hhi) hL
  unfold m4BandArm at harm
  linarith

/-- **DISCHARGE 3 — the row's cap-free branch.**  The same inequality also clears
`CapFreeAssembly.cffK_spec`'s threshold, so the row's `CapFreeFloor3` side condition comes
free at the ROW's datum.  Stated at the named-choice inhabitant `Bfun := m4QualityB` (that is
what `cffK_spec` is stated at). -/
theorem m4_capfree_of_joint {Hhi H q : ℕ} {X : ℝ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hH : 1 ≤ H) (hle : H ≤ Hhi)
    (hq1 : 1 ≤ q) (hqW : (q : ℝ) ≤ m4W H)
    (hX : Real.exp (Real.exp 1) ≤ X)
    (hL : m4JointThr m4QualityB Hhi ≤ Real.log (Real.log X)) :
    CapFreeFloor3 (liouChi χ) X := by
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqHhi : (q : ℝ) ≤ m4W Hhi := m4_modulus_le hH hle hqW
  have hqQ : q ≤ m4Wnat Hhi := m4_modulus_nat_le hH hle hqW
  have hanchor : (1000 : ℝ) ≤ Real.log (Real.log X) :=
    le_trans (m4JointThr_anchor m4QualityB Hhi) hL
  have harm : m4CffArm (m4QualityB (m4Wnat Hhi)) Hhi ≤ Real.log (Real.log X) :=
    le_trans (m4JointThr_cff m4QualityB Hhi) hL
  -- the two absorptions: `40·logloglog X ≤ (loglog X)/2` and the `q`-content at `W`
  have habs : Real.log (Real.log (Real.log X)) ≤ Real.log (Real.log X) / 80 :=
    m4_log_le_div_eighty hanchor
  have hlogq : Real.log q ≤ Real.log (m4W Hhi) :=
    Real.log_le_log (by linarith) hqHhi
  have hvk : vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q
      ≤ m4QualityB (m4Wnat Hhi) :=
    le_trans (m4VKdebit_spec hqQ) (m4VKdebit_le_m4QualityB _)
  have hcff : cffK (m4Wnat Hhi) ≤ m4QualityB (m4Wnat Hhi) := cffK_le_m4QualityB _
  refine capFreeFloor3_liouChi_of_lamChi χ (cffK_spec (m4Wnat Hhi) q χ X hqQ hX ?_)
  unfold m4CffArm at harm
  linarith

end Salt.MR
