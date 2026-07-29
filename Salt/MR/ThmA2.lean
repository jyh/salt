/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2Spine
import Salt.MR.T0Band
import Salt.MR.CapFreeArm
import Salt.MR.DoorFrameH1
import Salt.MR.SPartStation
import Salt.MR.MWindowBridge
import Salt.MR.SeamRowWindowed
import Salt.MR.ThmA2Open
import Salt.MR.SieveGlue

/-!
# S8 ladder, node A2-7 — **THE FROZEN `thm_A2′`** (`ThmA2`)

Freeze: `docs/exploration/s8-freeze-0727.md`, row A2-7, **with all seven amendments A–G**.

**What lands here.**  (§4) `thm_a2'_of_rows` — the FROZEN FIVE-SUMMAND STATEMENT with the
complete side-condition list, every constant an explicit numeral, taking the weighted
seam-row family and the `T₀`-band as binders; (§2) the band grade; (§3) the Perron defect's
passage to the limit; (§5) the branch ROUTING LEMMA at the `|v| ≤ X` box, the door frame at
the row's own scale, and the `∀Tann` bookkeeping bundle `A2Frame`.  **What does not** (§6,
named exactly): the two `hrows` suppliers `a2Rows_of_capfree` / `a2Rows_of_cap` — one
application each of the landed cap-free / socketed row, plus the weighting arithmetic whose
four numerals are already `a2Mrow`'s.

## The five summands (⟦AMENDMENT A⟧'s pinned literal + ⟦F⟧'s fifth + A2-3-BAND's fourth)

  `(1/X)∫_X^{2X} ‖(1/h)·Σ_{x<n≤x+h, n∈𝒮_K} F(n)‖² dx`
  `  ≤ C₁·exp(−M₀/e)                       ` the `M`-term, **NO `M`-shaped factor**
  `   + C₂·(log Q₁)^{1/3}/P₁^{1/12}        ` §8.1 at the doorH1 pin (G6 fixed)
  `   + C₃·(log X)^{−1/500}                ` the `𝒰`-leg grade
  `   + C₄·(log X)^{−43/45}·(1+loglog X)²  ` the band residue (A2-3-BAND's honest grade)
  `   + C₅/h                               ` the spine's fifth summand, never absorbed

`M₀` is the ball centre's own pretentious distance
`𝔻²(seamCoeff (ellLin g) 1 t₀, n^{i·0}; X)` — the object `T0Band.t0_band_supply` produces
and `MWindowBridge.M_window_bridge_seam` supplies from `M(f;X,W)`.  The `M`-term enters
through the `T₀`-BAND, not through the seam row's ball leg: on **both** branches the row's
`8S²` summand is zero (`CapFreeArm.ball_leg_vacuous_at_zero` at `t₁ := 0` is
datum-free), and the `M`-dependence of the answer lives entirely in `B₀`.

## The branch routing (⟦AMENDMENT B⟧/⟦E⟧, the honest form)

`by_cases` on `CapFreeArm.CapFreeFloor g X` — the STRICT `(1/32)loglog X + 25` floor on the
BARE datum at the `|v| ≤ X` box, which `CapFreeArm.box_gate_le_X` (S10) makes the right
box, so the dichotomy is exhaustive:

* **floor holds** ⟹ `seam_row_number_capfree`: no row cap, no collision gate, no produced
  centre, `8S² = 0`.  The `M`-term is never *produced* on this branch; `C₁·exp(−M₀/e) ≥ 0`
  absorbs it trivially and the branch is bounded by the other four summands.
* **floor fails** ⟹ a witness `v₀`, `|v₀| ≤ X`, with `𝔻²(g, p^{iv₀}; X) ≤ (1/32)L + 25`,
  hence (past `800 < loglog X`) the ROW CAP `𝔻²(ℓg, p^{iv₀}; X) ≤ (1/16)L` at `t₁ := v₀`
  — `pocketSocket_of_row`'s hypothesis on the nose (`pretDistSq_ellLin_eq` moves the bare
  datum onto `ℓg`).  The row then runs through `seam_row_number_nocap` at `t₁ := v₀`, and
  its `hSup` binder is supplied by `SPartStation.seam_ball_leg_station_M_gen` at the
  centre `v₀` (⚠ **the T3 gap**: the station minimises the `t₀`-SHIFTED datum, so the
  witness gives NO `hMcap` at `v₀` — that cap is carried as an in-statement, conditional
  hypothesis `A2Frame.station_cap`, exactly as ⟦AMENDMENT B⟧ flagged).

## The bookkeeping (⟦AMENDMENT F⟧'s residuals)

The `∀Tann` frame instantiation across `[2X/h, X]` is packaged as ONE hypothesis bundle,
`A2Frame`, whose `Tann`-dependent members are ∀-quantified over that window (two are stated
at the window's top and transferred by `A2Frame.box_at` / `A2Frame.ksGate_at` — the
monotonicity is proved, not asserted).  `calFrameK_doorH1_at` inhabits the frame field at
the corrected door (`calFrameK_satisfiable_doorH1`) at every `X_d ≥ Q_{Jb}`, which is what
the seam row's `X_d ≍ X` needs; full-bundle satisfiability is NOT claimed.

## Deviations, all in-statement (law #253)

* the `h`-CEILING `5 ≤ loglog(2X/h)` and `h ≥ 4` — thm_A2′ cannot state MRT's bare `h ≥ 3`;
* `[P₁,Q₁] ⊆ [1,h]` enters only as `Q₁ ≤ h` (`log_calQK_door_one` is the log identity);
* the `×4` SAFE COVER of ⟦AMENDMENT G⟧: the row's `480·(Tann/X_d+1)·(…)` summand is priced
  at `1920` in `a2Mrow` — `second_window_le_first_row` is the number that pays for it, and
  no landed statement is edited;
* the `𝒮_K`↔seam-datum identification is the A2-5/Route-III seam: the statement's `a` is
  the coefficient sequence, and the two readings of it — `1_{𝒮_K}·F` (via
  `SieveGlue.memS_calFamily`, the `MemS (calP A G) (calQK A G M) 2` identification) and the
  station/band datum `seamCoeff (ellLin g) 1 t₀` — are supplied to the two consumers, never
  derived from one another here.

## Glyph traps honoured

`T₀` below is ALWAYS `seamT0 X = (log X)^{1/45}` (never MRT's set `𝒯₀`, never the contour
height `(log X)²`); `N` is the coefficient cutoff and `K` the Perron dyadic depth (the
spine's rename); the two `(1/16)`-caps are named apart (`row_cap` vs `station_cap`).
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex
open scoped BigOperators

/-! ## §1 — the graded row constant `a2Mrow`

The seam row's right-hand side is `Tann`-LINEAR; the spine consumes the WEIGHTED family
`(X/h)/T · ∫_{Ann(T₀,2T)}`, and the weight is what makes the family grade-flat.  With
`Tann = 2T`, `X/h ≤ T`, `2T ≤ X`, `X/4 ≤ X_d` and `Q₁ ≤ h` the four `Tann`-linear factors
weigh in at

  `(X/h)/T·(2T·Q₁/X_d + 1) ≤ 8Q₁/h + 1 ≤ 9`,
  `(X/h)/T·(4T/X_d + 240)  ≤ 16/h + 240 ≤ 244`,
  `(X/h)/T·(2T/X_d + 1)    ≤ 8/h + 1 ≤ 3`,
  `(X/h)/T·(2T/X + 1)      ≤ 2/h + 1 ≤ 3/2`,

which are the numerals below.  The `480 → 1920` inflation is ⟦AMENDMENT G⟧'s `×4` cover. -/

/-- The §8.1 LEVEL-1 GRADE at the corrected door pin: `(log Q₁)^{1/3}/P₁^{1/12}` — MR §8.1's
own `(log Q₁)^{1/3}/P₁^{1/6−η}` at `η = 1/12`, the object `DoorFrameH1.level1_term_door_decays`
delivers (and the whole content of the G6 repair: it DECAYS in `P₁`). -/
def a2Level1 (M : ℕ) : ℝ :=
  (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
    / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)

/-- The Lemma-12 row sum of the seam row's right-hand side, at the door family and `Jb = 2`
(`Tann`-FREE — which is why it survives the weighting untouched). -/
def a2RowsSum (M Xd : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 2,
    ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
        * (Real.exp 1 / (Xd : ℝ) ^ 2))
      + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
      + 1 / (Xd : ℝ))

/-- **THE FLAT ROW NUMBER.**  `a2Mrow Cs C M Xd X ε` is the weighted seam row's bound,
uniform over the whole family `X/h ≤ T`, `2T ≤ X`, at the corrected door family
(`A = Adoor M`, `G = 3072M`, `Jb = 2`, `H₁ = H1door M`, `η = 1/12`).  Four summands:
the §8.1 level-1 term at the G6-fixed grade, the `Cs`-row, the Lemma-12 rows at
⟦AMENDMENT G⟧'s `×4` cover (`480·3 → 5760`), and the `𝒰`-leg. -/
def a2Mrow (Cs C : ℝ) (M Xd : ℕ) (X ε : ℝ) : ℝ :=
  47520 * a2Level1 M
    + 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    + 5760 * (a2RowsSum M Xd + C * (2 / (M : ℝ)))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-! ## §2 — the `T₀`-band bound, graded

`T0Band.t0BandB X C₁ M₀ = 8·(2√2·S₀ + bandTail X T₀·(1+T₀))²` with
`S₀ = C₁·e^{−M₀/(2e)} + 4(log X)^{−1/2+1/1000}`.  Two `(u+v)² ≤ 2u²+2v²` steps and the
radius arithmetic give the honest `−43/45` band residue. -/

/-- The band's log factor at the `T₀` radius is `≤ 3·(1 + loglog X)`: with `log X ≥ 1`,
`3 + T₀(1+log 2X) ≤ 6·(log X)^{46/45}`, so
`1 + log(3 + T₀(1+log 2X)) ≤ 1 + log 6 + (46/45)·loglog X ≤ 3·(1 + loglog X)`. -/
lemma bandLterm_seamT0_le {X : ℝ} (hX : 3 ≤ X) :
    bandLterm X (seamT0 X) ≤ 3 * (1 + Real.log (Real.log X)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXe : Real.exp 1 ≤ X := by linarith [Real.exp_one_lt_d9]
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hT0 : seamT0 X = (Real.log X) ^ ((1 : ℝ) / 45) := rfl
  have hlog2X : Real.log (2 * X) = Real.log 2 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
  have hlog2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hfac : 1 + Real.log (2 * X) ≤ 2.7 * Real.log X := by rw [hlog2X]; linarith
  have hT0nn : (0 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 45) := Real.rpow_nonneg hL0.le _
  have hsplit : (Real.log X) ^ ((46 : ℝ) / 45)
      = (Real.log X) ^ ((1 : ℝ) / 45) * Real.log X := by
    rw [show (46 : ℝ) / 45 = (1 : ℝ) / 45 + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
  have h16 : (1 : ℝ) ≤ (Real.log X) ^ ((46 : ℝ) / 45) := by
    calc (1 : ℝ) = (Real.log X) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (Real.log X) ^ ((46 : ℝ) / 45) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hprod : (Real.log X) ^ ((1 : ℝ) / 45) * (1 + Real.log (2 * X))
      ≤ 2.7 * (Real.log X) ^ ((46 : ℝ) / 45) := by
    calc (Real.log X) ^ ((1 : ℝ) / 45) * (1 + Real.log (2 * X))
        ≤ (Real.log X) ^ ((1 : ℝ) / 45) * (2.7 * Real.log X) :=
          mul_le_mul_of_nonneg_left hfac hT0nn
      _ = 2.7 * (Real.log X) ^ ((46 : ℝ) / 45) := by rw [hsplit]; ring
  have hinner : 3 + seamT0 X * (1 + Real.log (2 * X))
      ≤ 6 * (Real.log X) ^ ((46 : ℝ) / 45) := by rw [hT0]; linarith
  have hlogmono : Real.log (3 + seamT0 X * (1 + Real.log (2 * X)))
      ≤ Real.log (6 * (Real.log X) ^ ((46 : ℝ) / 45)) := by
    refine Real.log_le_log ?_ hinner
    have hnn : (0 : ℝ) ≤ seamT0 X * (1 + Real.log (2 * X)) := by
      refine mul_nonneg ?_ ?_
      · rw [hT0]; exact hT0nn
      · rw [hlog2X]; linarith [Real.log_nonneg (le_of_lt (by norm_num : (1 : ℝ) < 2))]
    linarith
  have hrhs : Real.log (6 * (Real.log X) ^ ((46 : ℝ) / 45))
      = Real.log 6 + (46 / 45) * Real.log (Real.log X) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL0]
  have hlog6 : Real.log 6 ≤ 2 := by
    have hexp2 : (6 : ℝ) ≤ Real.exp 2 := by
      have hsplit2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_gt_d9]
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr hexp2
  unfold bandLterm
  rw [hrhs] at hlogmono
  linarith

/-- `8(2√2·S + q)² ≤ 128S² + 16q²` — the first `(u+v)² ≤ 2u²+2v²` step of the band grade,
isolated so that `√2` never enters a large `nlinarith` call. -/
private lemma band_sq_split (S q : ℝ) :
    8 * (2 * Real.sqrt 2 * S + q) ^ 2 ≤ 128 * S ^ 2 + 16 * q ^ 2 := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [sq_nonneg (2 * Real.sqrt 2 * S - q), Real.sqrt_nonneg 2]

/-- **THE BAND BOUND, GRADED** (`t0BandB_grade`).  `T0Band.t0BandB` — the `B₀` of
`ThmA2Spine.thm_a2_spine`'s `hT0band` binder — split into the interface's `M`-term and the
honest `−43/45` band residue:

  `8·(2√2·S₀ + bandTail X T₀·(1+T₀))²`
  `  ≤ 256·C₁²·e^{−M₀/e} + 4096·(log X)^{−1+1/500}`
  `    + 9216·ballSupC²·(log X)^{−43/45}·(1 + loglog X)²`.

Two `(u+v)² ≤ 2u²+2v²` steps, `(√(log X))² = log X`, `(1+T₀)² ≤ 4·(log X)^{2/45}` and
`bandLterm ≤ 3(1+loglog X)`.  The second summand sits under `(log X)^{−1/500}` and the
third IS A2-3-BAND's fourth interface summand — **no `o(1)`**. -/
theorem t0BandB_grade {X C₁ M₀ : ℝ} (hX : 3 ≤ X) :
    t0BandB X C₁ M₀
      ≤ 256 * C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500)
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXe : Real.exp 1 ≤ X := by linarith [Real.exp_one_lt_d9]
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  set E : ℝ := Real.exp (-(1 / (2 * Real.exp 1)) * M₀) with hEdef
  set P : ℝ := (Real.log X) ^ (-(1 : ℝ) / 2 + 1 / 1000) with hPdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hP0 : (0 : ℝ) < P := Real.rpow_pos_of_pos hL0 _
  have hEsq : E ^ 2 = Real.exp (-(1 / Real.exp 1) * M₀) := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    have he0 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    push_cast
    field_simp
  have hPsq : P ^ 2 = (Real.log X) ^ (-(1 : ℝ) + 1 / 500) := by
    rw [hPdef, ← Real.rpow_natCast ((Real.log X) ^ (-(1 : ℝ) / 2 + 1 / 1000)) 2,
      ← Real.rpow_mul hL0.le]
    norm_num
  set T₀ : ℝ := seamT0 X with hT₀def
  have hT₀eq : T₀ = (Real.log X) ^ ((1 : ℝ) / 45) := rfl
  have hT₀1 : (1 : ℝ) ≤ T₀ := by
    rw [hT₀eq]
    calc (1 : ℝ) = (Real.log X) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (Real.log X) ^ ((1 : ℝ) / 45) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hT₀sq : T₀ ^ 2 = (Real.log X) ^ ((2 : ℝ) / 45) := by
    rw [hT₀eq, ← Real.rpow_natCast ((Real.log X) ^ ((1 : ℝ) / 45)) 2, ← Real.rpow_mul hL0.le]
    norm_num
  have hband0 : (0 : ℝ) ≤ bandLterm X T₀ := le_of_lt (bandLterm_pos hX (by linarith))
  have hbandle : bandLterm X T₀ ≤ 3 * (1 + Real.log (Real.log X)) := bandLterm_seamT0_le hX
  have hC0 := ballSupC_pos
  have hsqrt : Real.sqrt (Real.log X) ^ 2 = Real.log X := Real.sq_sqrt hL0.le
  have hsqrt0 : (0 : ℝ) < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr hL0
  have hq2 : (bandTail X T₀ * (1 + T₀)) ^ 2
      ≤ 576 * ballSupC ^ 2 * ((Real.log X) ^ (-(43 : ℝ) / 45)
          * (1 + Real.log (Real.log X)) ^ 2) := by
    have hexpand : (bandTail X T₀ * (1 + T₀)) ^ 2
        = 16 * ballSupC ^ 2 * bandLterm X T₀ ^ 2 * (1 + T₀) ^ 2 / Real.log X := by
      have hbt : bandTail X T₀
          = 4 * ballSupC * bandLterm X T₀ / Real.sqrt (Real.log X) := rfl
      rw [hbt, div_mul_eq_mul_div, div_pow, hsqrt]
      congr 1
      ring
    have hb2 : bandLterm X T₀ ^ 2 ≤ 9 * (1 + Real.log (Real.log X)) ^ 2 := by nlinarith
    have ht2 : (1 + T₀) ^ 2 ≤ 4 * (Real.log X) ^ ((2 : ℝ) / 45) := by
      rw [← hT₀sq]; nlinarith
    have hsplit : (Real.log X) ^ ((2 : ℝ) / 45)
        = (Real.log X) ^ (-(43 : ℝ) / 45) * Real.log X := by
      rw [show (2 : ℝ) / 45 = -(43 : ℝ) / 45 + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    rw [hexpand, div_le_iff₀ hL0]
    calc 16 * ballSupC ^ 2 * bandLterm X T₀ ^ 2 * (1 + T₀) ^ 2
        ≤ 16 * ballSupC ^ 2 * (9 * (1 + Real.log (Real.log X)) ^ 2) * (1 + T₀) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ ≤ 16 * ballSupC ^ 2 * (9 * (1 + Real.log (Real.log X)) ^ 2)
            * (4 * (Real.log X) ^ ((2 : ℝ) / 45)) :=
          mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ = 576 * ballSupC ^ 2 * ((Real.log X) ^ (-(43 : ℝ) / 45)
              * (1 + Real.log (Real.log X)) ^ 2) * Real.log X := by rw [hsplit]; ring
  have hS₀ : t0BandS X C₁ M₀ = 2 * Real.sqrt 2 * (C₁ * E + 4 * P)
      + bandTail X T₀ * (1 + T₀) := rfl
  have hfinal : t0BandB X C₁ M₀
      ≤ 128 * (C₁ * E + 4 * P) ^ 2 + 16 * (bandTail X T₀ * (1 + T₀)) ^ 2 := by
    unfold t0BandB
    rw [hS₀]
    exact band_sq_split _ _
  have hmid : 128 * (C₁ * E + 4 * P) ^ 2
      ≤ 256 * C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) := by
    rw [← hEsq, ← hPsq]
    nlinarith [sq_nonneg (C₁ * E - 4 * P)]
  linarith

/-! ## §3 — the Perron defect vanishes

`ThmA2Spine.thm_a2_spine` carries A2-1's Perron defect `Egap(K,δ)` for FREE `K` and `δ`;
the five-summand interface has no such term.  Along `K = 2m`, `δ = 2^{−m}` the defect is
`O(m²·2^{−m})` and the interface is recovered by `le_of_forall_pos_le_add`. -/

/-- `(x + 2.8y)² ≤ 2x² + 15.68y²` — the `(u+v)² ≤ 2u²+2v²` step of the defect bound, on
fresh variables so that no `set` body is ever unfolded by `nlinarith`. -/
private lemma sq_split_2p8 (x y : ℝ) : (x + 2.8 * y) ^ 2 ≤ 2 * x ^ 2 + 15.68 * y ^ 2 := by
  nlinarith [sq_nonneg (x - 2.8 * y)]

/-- **THE DEFECT IS ARBITRARILY SMALL** (`egap_small`).  For every `ε > 0` there are `K` and
`δ ∈ (0,1]` with `Egap(K,δ) ≤ ε`.  The witness is `K := 2m`, `δ := 2^{−m}`, at which

  `Egap ≤ (1152·(12h+8h·Cc)² + 69120·c²)·2^{−m} + 541901·m²·2^{−m}`,
  `c = π + 2log(1+X/h)`, `Cc = 1 + log 3X`,

and both `2^{−m}` and `m²·2^{−m}` vanish (`tendsto_pow_const_div_const_pow_of_one_lt`). -/
theorem egap_small {X h : ℝ} (hX : 3 ≤ X) (hh : 4 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
      34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
        + 1152 * (12 * h / (2 ^ K * δ) + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2
      ≤ ε := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  set A : ℝ := X / h with hAdef
  have hA0 : (0 : ℝ) ≤ A := le_of_lt (div_pos hX0 hh0)
  set Cc : ℝ := 1 + Real.log (3 * X) with hCdef
  have hCc0 : (0 : ℝ) ≤ Cc := by
    have : (0 : ℝ) ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
    rw [hCdef]; linarith
  set c : ℝ := Real.pi + 2 * Real.log (1 + A) with hcdef
  have hlogA : (0 : ℝ) ≤ Real.log (1 + A) := Real.log_nonneg (by linarith)
  have hc0 : (0 : ℝ) ≤ c := by have := Real.pi_pos; rw [hcdef]; linarith
  set B : ℝ := 12 * h + 8 * h * Cc with hBdef
  have hB0 : (0 : ℝ) ≤ B := by rw [hBdef]; nlinarith
  set Pc : ℝ := 1152 * B ^ 2 + 69120 * c ^ 2 with hPdef
  have hP0 : (0 : ℝ) ≤ Pc := by rw [hPdef]; positivity
  have hlim : Filter.Tendsto
      (fun m : ℕ => Pc * (1 / 2 : ℝ) ^ m + 541901 * ((m : ℝ) ^ 2 / 2 ^ m))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) ^ 2 / 2 ^ m)) Filter.atTop (nhds 0) :=
      tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
    have h3 := (h1.const_mul Pc).add (h2.const_mul (541901 : ℝ))
    simpa using h3
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h1le2 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hhalf : ((1 : ℝ) / 2) ^ m = 1 / 2 ^ m := by rw [div_pow]; norm_num
  rw [hhalf] at hm
  refine ⟨2 * m, (1 / 2 : ℝ) ^ m, by positivity, pow_le_one₀ (by norm_num) (by norm_num), ?_⟩
  have h2m : ((2 : ℝ) ^ (2 * m)) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [h2m, hhalf]
  have hden : (2 : ℝ) ^ m * 2 ^ m * (1 / 2 ^ m) = 2 ^ m := by
    rw [mul_one_div, mul_div_assoc, div_self hpow2.ne', mul_one]
  have hMM : (1 : ℝ) ≤ (2 : ℝ) ^ m * 2 ^ m := by nlinarith
  -- ⟦term 2⟧
  have hu0 : (0 : ℝ) ≤ 12 * h / ((2 : ℝ) ^ m * 2 ^ m * (1 / 2 ^ m))
      + (8 * h / ((2 : ℝ) ^ m * 2 ^ m)) * Cc := by
    rw [hden]; positivity
  have hule : 12 * h / ((2 : ℝ) ^ m * 2 ^ m * (1 / 2 ^ m))
      + (8 * h / ((2 : ℝ) ^ m * 2 ^ m)) * Cc ≤ B / 2 ^ m := by
    rw [hden, hBdef]
    have hstep : (8 * h / ((2 : ℝ) ^ m * 2 ^ m)) * Cc ≤ (8 * h / 2 ^ m) * Cc := by
      refine mul_le_mul_of_nonneg_right ?_ hCc0
      rw [div_le_div_iff₀ (by positivity) hpow2]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * h) hpow2.le)
        (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ m - 1)]
    have hsum : (12 * h + 8 * h * Cc) / 2 ^ m = 12 * h / 2 ^ m + (8 * h / 2 ^ m) * Cc := by
      field_simp
    rw [hsum]; linarith
  have hu2 : 1152 * (12 * h / ((2 : ℝ) ^ m * 2 ^ m * (1 / 2 ^ m))
        + (8 * h / ((2 : ℝ) ^ m * 2 ^ m)) * Cc) ^ 2
      ≤ 1152 * B ^ 2 * (1 / 2 ^ m) := by
    have hsq : (12 * h / ((2 : ℝ) ^ m * 2 ^ m * (1 / 2 ^ m))
        + (8 * h / ((2 : ℝ) ^ m * 2 ^ m)) * Cc) ^ 2 ≤ (B / 2 ^ m) ^ 2 :=
      pow_le_pow_left₀ hu0 hule 2
    have hval : (B / 2 ^ m) ^ 2 ≤ B ^ 2 * (1 / 2 ^ m) := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have hid : B ^ 2 * (1 / 2 ^ m) * ((2 : ℝ) ^ m) ^ 2 = B ^ 2 * 2 ^ m := by
        field_simp
      rw [hid]
      nlinarith [mul_nonneg (sq_nonneg B) (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ m - 1)]
    linarith
  -- ⟦term 1⟧
  set v : ℝ := Real.pi + 2 * Real.log (1 + (2 : ℝ) ^ m * 2 ^ m * A) with hvdef
  have hinner : (1 : ℝ) ≤ 1 + (2 : ℝ) ^ m * 2 ^ m * A := by
    nlinarith [mul_nonneg (mul_pos hpow2 hpow2).le hA0]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hv0 : (0 : ℝ) ≤ v := by
    have h1 := Real.log_nonneg hinner
    have h2 := Real.pi_pos
    rw [hvdef]; linarith
  have hvle : v ≤ c + 2.8 * (m : ℝ) := by
    have hle : 1 + (2 : ℝ) ^ m * 2 ^ m * A ≤ ((2 : ℝ) ^ m * 2 ^ m) * (1 + A) := by
      linarith [hMM]
    have hlog : Real.log (1 + (2 : ℝ) ^ m * 2 ^ m * A)
        ≤ Real.log (((2 : ℝ) ^ m * 2 ^ m) * (1 + A)) := Real.log_le_log (by linarith) hle
    have hexp : Real.log (((2 : ℝ) ^ m * 2 ^ m) * (1 + A))
        = 2 * (m : ℝ) * Real.log 2 + Real.log (1 + A) := by
      rw [Real.log_mul (by positivity) (by linarith), ← pow_add, Real.log_pow]
      push_cast; ring
    have hl2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
    rw [hexp] at hlog
    have hprod : (m : ℝ) * Real.log 2 ≤ (m : ℝ) * 0.7 := mul_le_mul_of_nonneg_left hl2 hm0
    rw [hvdef, hcdef]
    linarith
  have hsq : v ^ 2 ≤ 2 * c ^ 2 + 15.68 * (m : ℝ) ^ 2 := by
    have h1 : v ^ 2 ≤ (c + 2.8 * (m : ℝ)) ^ 2 := pow_le_pow_left₀ hv0 hvle 2
    linarith [sq_split_2p8 c (m : ℝ)]
  have hwpos : (0 : ℝ) < 1 / (2 : ℝ) ^ m := by positivity
  have hv2 : 34560 * (1 / (2 : ℝ) ^ m) * v ^ 2
      ≤ 69120 * c ^ 2 * (1 / 2 ^ m) + 541901 * ((m : ℝ) ^ 2 / 2 ^ m) := by
    have hstep : 34560 * (1 / (2 : ℝ) ^ m) * v ^ 2
        ≤ 34560 * (1 / (2 : ℝ) ^ m) * (2 * c ^ 2 + 15.68 * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    have hid : 34560 * (1 / (2 : ℝ) ^ m) * (2 * c ^ 2 + 15.68 * (m : ℝ) ^ 2)
        = 69120 * c ^ 2 * (1 / 2 ^ m) + 541900.8 * ((m : ℝ) ^ 2 / 2 ^ m) := by ring
    have hlast : (0 : ℝ) ≤ (m : ℝ) ^ 2 / 2 ^ m := by positivity
    linarith
  have hPexp : Pc * (1 / (2 : ℝ) ^ m)
      = 1152 * B ^ 2 * (1 / 2 ^ m) + 69120 * c ^ 2 * (1 / 2 ^ m) := by rw [hPdef]; ring
  rw [hPexp] at hm
  linarith


/-! ## §4 — THE FROZEN STATEMENT, given the row family

The spine's four-term exit is turned into the interface's FIVE summands here: the row
number is graded (§1's gates), the band is graded (§2), and the Perron defect is passed to
the limit (§3).  Every constant is an explicit numeral except `C₁ = 8448·C₁'²` (the centre
bound's own coefficient, a parameter of `T0Band.t0_band_supply`) and
`C₄ = 304128·ballSupC²` (`BallSup.ballSupC`, a landed name). -/

/-- The `π`-arithmetic of the spine's prefactor `1/(2π²)`, isolated:
`236365/(2π) ≤ 37620`, `205/(2π) ≤ 33`, `39674880/(2π) ≤ 6315000`. -/
private lemma spine_scale {p Mr Bd w Eg eg : ℝ} (hp1 : 3.141592 < p)
    (hMr : 0 ≤ Mr) (hBd : 0 ≤ Bd) (hw : 0 ≤ w) (hEg : Eg ≤ 2 * p ^ 2 * eg) :
    1 / (2 * p ^ 2) * (236365 * p * Mr + 205 * p * Bd + 39674880 * p * w + Eg)
      ≤ 37620 * Mr + 33 * Bd + 6315000 * w + eg := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2pos : (0 : ℝ) < 2 * p ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hp2pos]
  have h1 : 236365 * p ≤ 75240 * p ^ 2 := by nlinarith
  have h2 : 205 * p ≤ 66 * p ^ 2 := by nlinarith
  have h3 : 39674880 * p ≤ 12630000 * p ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hMr, mul_le_mul_of_nonneg_right h2 hBd,
    mul_le_mul_of_nonneg_right h3 hw]

/-- **thm_A2′, GIVEN THE ROW FAMILY** (`thm_a2'_of_rows`).  The frozen five-summand
interface, with the weighted seam-row family and the `T₀`-band supplied as binders (the
two branches of §5 are its two suppliers):

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·(log X)^{−1/500}`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

**The complete side-condition list**, all in-statement (law #253):  `1 ≤ M` (the door's
parameter); `e ≤ X` and `3 ≤ X`; `4 ≤ h` (the AS-2 MVT guard — NOT `3`);
`h ≤ X(log X)^{−1/5}` (Lemma 14's window frame); `X ≤ N ≤ 2X` and `a` supported above `X`
with `‖aₙ‖ ≤ 1`; `TannGate X (2X/h)` and `5 ≤ loglog(2X/h)` — equivalently the freeze's
`h`-CEILING `h ≤ 2X·e^{−e⁵}`, the honest deviation from MRT's bare `h ≥ 3`; the three
GRADING GATES (`hgP1`, `hgRows`, `hL4096`) and the `𝒰`-leg's exponent room
`0 ≤ ε ≤ θ₂₉₃ − 1/500` with `θ₂₉₃ = 1/(32(3e+1))` (so `1/500 < θ₂₉₃`, with room). -/
theorem thm_a2'_of_rows {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1 M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hrp500 : (0 : ℝ) < (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_pos_of_pos hL0 _
  have hrp13 : (0 : ℝ) < (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_pos_of_pos hL0 _
  -- the level-1 grade is nonnegative
  have hlogQ1 := one_le_log_calQK_door_one hM
  have hP64 := calP_door_one_ge M
  have hlvl0 : (0 : ℝ) ≤ a2Level1 M := by
    unfold a2Level1
    have h1 : (0 : ℝ) ≤ (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_nonneg h1 h2.le
  -- ⟦the row number, graded⟧
  have hMrowLe : a2Mrow Cs Ccc M Xd X ε
      ≤ 47520 * a2Level1 M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500) := by
    unfold a2Mrow
    have hθ : theta293 < 1 / 32 := theta293_lt_one_div_32
    have hU : (Real.log X) ^ (-theta293 + ε) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hεwin.1, hεwin.2])
    linarith
  have hMrow'0 : (0 : ℝ) ≤ 47520 * a2Level1 M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500) := by
    nlinarith
  -- ⟦the band, graded, with the `4096` summand absorbed⟧
  have h4096 : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500)
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hsp : (Real.log X) ^ (-(1 : ℝ) / 500)
        = (Real.log X) ^ (1 - (1 : ℝ) / 250) * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [hsp]
    exact mul_le_mul_of_nonneg_right hL4096
      (le_of_lt (Real.rpow_pos_of_pos hL0 _))
  have hBandLe : t0BandB X C₁' M₀
      ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + (Real.log X) ^ (-(1 : ℝ) / 500)
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have := t0BandB_grade (X := X) (C₁ := C₁') (M₀ := M₀) hX3
    linarith
  have hBand'0 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + (Real.log X) ^ (-(1 : ℝ) / 500)
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have h1 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by positivity
    have h2 : (0 : ℝ) ≤ 9216 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by positivity
    linarith
  -- ⟦the Perron defect, to the limit⟧
  refine le_of_forall_pos_le_add (fun eg heg => ?_)
  have hpi := Real.pi_gt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨K, δ, hδ0, hδ1, hEg⟩ :=
    egap_small (X := X) (h := h) hX3 hh4 (show (0 : ℝ) < 2 * Real.pi ^ 2 * eg by positivity)
  have hspine := thm_a2_spine (N := N) (a := a) (X := X) (h := h)
    (Mrow := a2Mrow Cs Ccc M Xd X ε) (B₀ := t0BandB X C₁' M₀) (δ := δ) K
    hX hh4 hhX hδ0 hδ1 ha hsupp hN2 hTann hceil hrows hT0band
  refine hspine.trans ?_
  -- monotonicity in `Mrow` and `B₀`, then the `π`-arithmetic
  have hmono : 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * a2Mrow Cs Ccc M Xd X ε
            + 205 * Real.pi * t0BandB X C₁' M₀ + 39674880 * Real.pi / h
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))
      ≤ 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * (47520 * a2Level1 M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500))
            + 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + (Real.log X) ^ (-(1 : ℝ) / 500)
                + 9216 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
            + 39674880 * Real.pi * (1 / h)
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2)) := by
    have hpre : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have e1 : 236365 * Real.pi * a2Mrow Cs Ccc M Xd X ε
        ≤ 236365 * Real.pi * (47520 * a2Level1 M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500)) :=
      mul_le_mul_of_nonneg_left hMrowLe (by positivity)
    have e2 : 205 * Real.pi * t0BandB X C₁' M₀
        ≤ 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + (Real.log X) ^ (-(1 : ℝ) / 500)
            + 9216 * ballSupC ^ 2
              * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hBandLe (by positivity)
    have e3 : 39674880 * Real.pi / h = 39674880 * Real.pi * (1 / h) := by ring
    rw [e3]
    linarith
  refine hmono.trans ?_
  have hscale := spine_scale (p := Real.pi)
    (Mr := 47520 * a2Level1 M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500))
    (Bd := 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + (Real.log X) ^ (-(1 : ℝ) / 500)
        + 9216 * ballSupC ^ 2
          * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
    (w := 1 / h) (eg := eg) hpi hMrow'0 hBand'0 (by positivity) hEg
  refine hscale.trans ?_
  have hw : 6315000 * (1 / h) = 6315000 / h := by ring
  rw [hw]
  linarith


/-! ## §5 — the branch routing and the `∀Tann` bookkeeping

Two stones land here and one residual is named.

* `calFrameK_doorH1_at` — the corrected door frame at the ROW's own dyadic scale.  The
  landed inhabitant `DoorFrameH1.calFrameK_satisfiable_doorH1` pins `X_d = Q_{Jb}` (with
  `Q_le_Xd` at equality); the seam row needs `X_d ≍ X`.  Exactly ONE field mentions `X_d`,
  so the generalization is field-for-field free.
* `a2_row_cap_of_not_capFreeFloor` — THE ROUTING LEMMA.  `CapFreeArm.box_gate_le_X` (S10)
  tightened the pocket's box to `|t₁'| ≤ X`, which is the box `CapFreeFloor` lives on, so
  the `by_cases` on `CapFreeFloor g X` is EXHAUSTIVE; and on the failing branch the witness
  is precisely `pocketSocket_of_row`'s hypothesis, through `pretDistSq_ellLin_eq`.
* `A2Frame` — the `∀Tann` bundle (⟦AMENDMENT F⟧'s first residual). -/

/-- **THE DOOR FRAME AT THE ROW'S SCALE.**  `CalFrameK` at `η = 1/12`, `A = Adoor M`,
`G = 3072M`, `Jb = 2`, `H₁ = H1door M` and ANY `X_d ≥ Q_{Jb}` — the landed inhabitant with
its single `X_d`-mentioning field (`Q_le_Xd`) relaxed from equality.  This is what lets the
seam row run at its own dyadic scale `X_d ≍ X` while the door keeps its `P`/`Q` ladder.
Every other field is `DoorFrameH1.calFrameK_satisfiable_doorH1`'s, verbatim. -/
theorem calFrameK_doorH1_at (M Xd : ℕ) (hM : 1 ≤ M)
    (hXd : calQK (Adoor M) (3072 * M) M 2 ≤ Xd) :
    CalFrameK (1 / 12) (H1door M) (Adoor M) (3072 * M) M 2 Xd := by
  have hF := calFrameK_satisfiable_doorH1 M hM
  exact ⟨hF.eta_pos, hF.eta_lt, hF.one_le_Jb, hF.one_le_G, hF.one_le_M, hF.G_gateK,
    hF.A_gate_lin, hF.A_gate_logK, hF.A_floor, hF.H1_two, hF.H1_pin, hXd⟩

/-- **THE ROUTING LEMMA** (`a2_row_cap_of_not_capFreeFloor`).  If the cap-free datum floor
FAILS on the box `|v| ≤ X`, then some `v₀` in that box carries the ROW CAP
`𝔻²(ℓg, p^{iv₀}; X) ≤ (1/16)loglog X` — `CofactorDist.pocket_collision_window`'s hypothesis
as `CapFreeArm.pocketSocket_of_row` states it.

The arithmetic is the freeze's own break-even: the floor's failure gives
`𝔻² ≤ (1/32)loglog X + 25`, and `25 ≤ (1/32)loglog X` exactly past `loglog X = 800`
(⟦AMENDMENT E⟧'s T-NEW-1 threshold, which is why `800` and not `7273`).
`CapFreeArm.pretDistSq_ellLin_eq` (S1) is what moves the bare datum onto `ℓg`.

⚠ This is a statement about the DATUM, never a negation of `hrow` (trap T3): the failing
branch produces a bare-datum witness at the row's own scale `X`, which is what the row cap
is stated at — the station's `t₀`-shifted minimisation is a different object and is NOT
touched here. -/
theorem a2_row_cap_of_not_capFreeFloor {g : ℕ → ℂ} {X : ℝ}
    (hLL : 800 < Real.log (Real.log X)) (hfl : ¬ CapFreeFloor g X) :
    ∃ v₀ : ℝ, |v₀| ≤ X ∧
      pretDistSq (ellLin g) (costwist v₀) X ≤ (1 / 16) * Real.log (Real.log X) := by
  rw [CapFreeFloor] at hfl
  push Not at hfl
  obtain ⟨v₀, hv₀, hle⟩ := hfl
  refine ⟨v₀, hv₀, ?_⟩
  rw [pretDistSq_ellLin_eq]
  linarith

/-- **THE `∀Tann` FRAME BUNDLE** (`A2Frame`) — ⟦AMENDMENT F⟧'s first bookkeeping residual,
packaged.  `ThmA2Spine.thm_a2_spine` reads the seam row at EVERY height `Tann = 2T` with
`X/h ≤ T`, `2T ≤ X`, i.e. across the window `[2X/h, X]`; these are exactly the binders of
`CapFreeArm.seam_row_number_nocap` that mention `Tann`, quantified over that window.

Two fields are stated at the window's TOP, `Tann = X`, because they are *anti*-monotone:

* `box` — bigger `Tann` means a bigger `|t|`-range, so the instance at `X` is the strongest
  and implies every other (`A2Frame.box_at`);
* `ksGate` — `log(2·Tann) ≤ log(2X)`, so the instance at `X` implies every other
  (`A2Frame.ksGate_at`).

The remaining ten are stated per-`Tann` (six are monotone in `Tann` and would follow from
one endpoint; `thin`, `blocks` and `err` are genuinely per-instance).  `E` is FREE in the
row, so `err` fixes it at the row's own ceiling and the row's `hErow` binder then holds by
`le_rfl` — that is the honest way the `E`-pair collapses to one field. -/
structure A2Frame (g cf a : ℕ → ℂ) (N Xd P Q A G M Jb : ℕ) (Ms Mt kk : ℕ → ℕ)
    (H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ) : Prop where
  /-- MR's contour gate at every admissible height. -/
  tannGate : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → TannGate X Tann
  /-- The height is a genuine height. -/
  one_lt : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → 1 < Tann
  /-- The row's own floor `T₀` (`seam_row_number_nocap`'s existential, `3 ≤ T₀`). -/
  T0_le : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → T₀ ≤ Tann
  /-- The `h`-ceiling, read at the height (monotone; the freeze's `5 ≤ loglog(2X/h)`). -/
  loglog5 : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → 5 ≤ Real.log (Real.log Tann)
  /-- `1 ≤ log Tann` (free from `loglog5`, kept as a field to mirror the row). -/
  one_le_log : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → 1 ≤ Real.log Tann
  /-- The `L`-budget (monotone in `Tann`). -/
  log_le_L : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X → Real.log Tann ≤ L
  /-- The thin-bundle demand on the `Ms`-ladder, per height. -/
  thin : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
    ∀ j ∈ ramI (H83 X theta293) P Q,
      thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb) * X ^ (1 - 2 * η)
        ≤ ((Ms j : ℕ) : ℝ)
  /-- The §8.3 block gates, per height. -/
  blocks : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
    ∀ j ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk Tann L (1 / Real.exp 1) Cb X
        theta293 Rrad j
  /-- The contour box (S10), at the window's TOP — anti-monotone, see `A2Frame.box_at`. -/
  box : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X
  /-- The kernel/short-interval gate, at the window's TOP — see `A2Frame.ksGate_at`. -/
  ksGate : 32 * (Real.log X) ^ (2 + 2 * theta293)
      * (20512 * δ' ^ 2 * (1 + Real.log (2 * X))) ≤ (Real.log X) ^ (-theta293)
  /-- The Ramaré error mass, per height, at the row's own ceiling (so `hErow` is `le_rfl`). -/
  err : ∀ Tann : ℝ, 2 * (X / h) ≤ Tann → Tann ≤ X →
    (∫ t in (-Tann)..Tann, ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2)
      ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2)

namespace A2Frame

variable {g cf a : ℕ → ℂ} {N Xd P Q A G M Jb : ℕ} {Ms Mt kk : ℕ → ℕ}
  {H1 X h δ' VJ L η Cb Rrad EP2 cq T₀ : ℝ}

/-- The contour box at any admissible height, from the top instance (anti-monotone). -/
theorem box_at (F : A2Frame g cf a N Xd P Q A G M Jb Ms Mt kk H1 X h δ' VJ L η Cb Rrad
      EP2 cq T₀) {Tann : ℝ} (hTX : Tann ≤ X) :
    ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
      |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ X :=
  fun j hj t ht => F.box j hj t (le_trans ht hTX)

/-- The kernel gate at any admissible height, from the top instance (monotone in `Tann`
through `log(2Tann) ≤ log(2X)`). -/
theorem ksGate_at (F : A2Frame g cf a N Xd P Q A G M Jb Ms Mt kk H1 X h δ' VJ L η Cb Rrad
      EP2 cq T₀) {Tann : ℝ} (hT0 : 0 < Tann) (hTX : Tann ≤ X) (hL0 : 0 ≤ Real.log X) :
    32 * (Real.log X) ^ (2 + 2 * theta293)
        * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) := by
  refine le_trans ?_ F.ksGate
  have hlog : Real.log (2 * Tann) ≤ Real.log (2 * X) :=
    Real.log_le_log (by linarith) (by linarith)
  have hrp : (0 : ℝ) ≤ (Real.log X) ^ (2 + 2 * theta293) := Real.rpow_nonneg hL0 _
  have hδ : (0 : ℝ) ≤ 20512 * δ' ^ 2 := by positivity
  nlinarith [mul_nonneg hrp hδ]

end A2Frame

/-! ## §6 — the residual, named exactly (the Zeno line)

What is NOT in this file, stated so the next session can pick it up in one read:

**`a2Rows_of_capfree` / `a2Rows_of_cap`** — the two suppliers of `thm_a2'_of_rows`'
`hrows` binder.  Each is ONE application of `CapFreeArm.seam_row_number_capfree`
(resp. `CapFreeArm.seam_row_number_nocap` at `t₁ := v₀` from
`a2_row_cap_of_not_capFreeFloor` + `CapFreeArm.pocketSocket_of_row`, with `hSup` from
`SPartStation.seam_ball_leg_station_M_gen`) at `Tann := 2T`, fed by `A2Frame` and the
~45 `Tann`-free binders, followed by the WEIGHTING ARITHMETIC:

  `(X/h)/T·(2T·Q₁/X_d + 1) ≤ 9`,  `(X/h)/T·(4T/X_d + 240) ≤ 244`,
  `(X/h)/T·(2T/X_d + 1) ≤ 3`,     `(X/h)/T·(2T/X + 1) ≤ 3/2`,

(from `X/h ≤ T`, `2T ≤ X`, `X/4 ≤ X_d` — the row's `2X_d ≤ N ≤ 4X_d` with `X ≤ N ≤ 2X` —
and `Q₁ ≤ h`, the `[P₁,Q₁] ⊆ [1,h]` gate), plus `DoorFrameH1.level1_term_door_decays` at
`R := 9` for the §8.1 summand and ⟦AMENDMENT G⟧'s `×4` cover (`480·3 → 5760`) on the
Lemma-12 summand.  Those four numerals are exactly `a2Mrow`'s.  It is bookkeeping, not
design: no new estimate is needed, and `thm_a2'_of_rows` is stated to receive it.

The **T3 gap** is the one genuine obligation on the cap branch: the station's `hMcap` at
the produced centre `v₀` is NOT derivable from the routing witness (the station minimises
the `t₀`-shifted datum), so it must be carried as a conditional in-statement hypothesis
`∀ v, |v| ≤ X → 𝔻²(g, p^{iv}; X) ≤ (1/32)loglog X + 25 → (the A-10 cap at v)`.
⟦AMENDMENT B⟧ flagged it; nothing here hides it. -/

end Salt.MR
