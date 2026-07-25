/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LambdaMass
import Salt.MR.SmallStones
import Salt.MR.BridgeAdapt
import Salt.MR.PretSupply

/-!
# CENTER-SUPPLY — the `HCENTER` closure (A-8/A-9)

The assembly stone of the `HCENTER` ladder (`docs/exploration/hsup-design.md`, the
⟦HCENTER FREEZE⟧ + ⟦AMENDMENT V2⟧ + ⟦TWO-M⟧ blocks): the pointwise Halász bound at the
ball CENTRE, in exactly `BallSup.ball_sup_of_center`'s `hCenter` binder shape at the seam
datum `f := seamCoeff (ellLin g) (fun _ => 1) t₀`.

## The composition (the route actually taken)

`center_halasz_supply` composes, per scale `k ∈ [⌊X⌋₊, N]`:

1. **the twist combine** (§1, `seamCoeff_twist_combine`) — `seamCoeff f 1 t₀ n · eIu(−t₁) n
   = seamCoeff f 1 (t₀+t₁) n`, the `n^{−it₀}·n^{−it₁} = n^{−i(t₀+t₁)}` algebra.  This is what
   lets the S1′ machinery — stated at ONE free centre — see the ball frequency `t₁` as a
   re-centring of the seam's own `t₀`;
2. **the desmooth** (`HalaszSeam.prop21_desmooth_reduction`) at scale `k`, cost `h+1`;
3. **the S1′ representation** (`LambdaMass.prop21_uniform_at_scale_absC`) at scale `k` —
   the datum-hoisted uniform form (A-7b), whose `(X₀, C_E, C_R)` precede `(g, t₀)`, which is
   what makes the constants uniform over the `X`-dependent centre `t₀+t₁`;
4. **the grade page** (§2) — the `k`-uniform conversion of the desmooth `(h+1)` and the
   `E`-error into the single `(log X)^{−1/2+1/1000}` term, at the pinned `ε = 1/1000`
   (`BridgeAdapt.loglog_absorb_pow_pin`).

## The named residual (`hRHS`) — why it is a binder and not a proof

The remaining leg is `‖prop21RHS‖ ≤ C₁·k·e^{−M/(2e)}`.  Its chain is landed to the
penultimate step (`joint_cs_factoring` → `bridge_adapter` → `joint_sigma_integral` at the
concrete `Fbound` of `supF_pret_majorant_sigma`, with `crossKer_sigma_bound` supplying
`crossKer ≤ Kα/σ`), but the terminal **grade socket `Agrade ≤ C₁·X` does NOT discharge on
this route** — `JointHead`'s own HGRADE record proves the honest deficit: the crude kernel
face gives `Agrade ≍ X·L^{3/2}` and the `Tsplit`-sharp face `Agrade ≍ X·log log X`; a
genuine `log log X` survives, and per iron rule 1 / the SF-EXIT law it is NOT forced.  So
`hRHS` is carried here as a NAMED hypothesis, in the freeze's **M-shape** (the explicit
distance `pretDistSq (seamCoeff (ellLin g) 1 t₀) (costwist t₁) X`, no numeral — ⟦AMENDMENT
V2⟧ item 4, the μ²-refutation).  The consumer instantiates `t₁` at the global minimizer
(⟦TWO-M⟧); nothing here fixes it, and nothing here needs `hmin`: the distance rides through
the composition untouched, which is precisely why the free-distance form is the honest one.

## The exponent

`c = 1/(2e)` — the BALL arm's halved constant (S-3, route-scoped).  **THE LIVE GUARD: a
§8.3 consumer citing this head is a STOP** (⟦AMENDMENT V2⟧ item 5).

## §4 — the crown

`ball_sup_supplied` feeds `center_halasz_supply` into `BallSup.ball_sup_of_center`,
discharging `SeamBallWeighted.ball_leg_of_sup_weighted`'s `hSup′` binder at the centre.
Two datum facts stay named there (`hfmul` — multiplicativity of the seam datum; `hMball` —
the A.4 ball dichotomy in Mertens-mass form, `SmallStones.hMball_of_A4_cap`'s input); §3's
`pretDistSq_twist_slot` is the twist-slot half of the latter, discharged here.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §1 — the twist algebra: `n^{−it₀}·n^{−it₁} = n^{−i(t₀+t₁)}` -/

/-- The seam's centre twist in `eIu` form: `n^{−it} = e^{−it·log n}` for `n ≠ 0`.  (The
corpus writes `n^{iu}` as `exp(I·u·log n)`; `cpow`'s norm lemmas are gated off `Re s = 0`.) -/
lemma cpow_neg_ofReal_mul_I_eq_eIu (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ^ (-(t : ℂ) * I) = eIu (-t) n := by
  have h := div_cpow_eq_eIu 1 t hn
  rw [one_mul, one_div] at h
  rw [← h, ← Complex.cpow_neg, neg_mul]

/-- **A-8 — the twist combine (`seamCoeff_twist_combine`).**  Multiplying the seam
coefficient at centre `t₀` by the ball twist `e^{−it₁ log n}` re-centres it at `t₀+t₁`:

  `seamCoeff f g_J t₀ n · eIu(−t₁) n = seamCoeff f g_J (t₀+t₁) n`.

This is the hinge of the whole `HCENTER` closure: `ball_sup_of_center`'s `hCenter` binder
asks for the seam datum at `t₀` TWISTED by `−t₁`, while the S1′ machinery
(`prop21_uniform_at_scale_absC`, `prop21_desmooth_reduction`) is stated at a single free
centre.  The two meet here, with no analytic content: `n^{−it₀}·n^{−it₁} = n^{−i(t₀+t₁)}`
(`eIu_add`), and the `n = 0` slot is `0` on both sides by `seamCoeff`'s own convention
(catch #254). -/
theorem seamCoeff_twist_combine (f gJ : ℕ → ℂ) (t₀ t₁ : ℝ) (n : ℕ) :
    seamCoeff f gJ t₀ n * eIu (-t₁) n = seamCoeff f gJ (t₀ + t₁) n := by
  unfold seamCoeff
  split_ifs with h
  · rw [zero_mul]
  · rw [cpow_neg_ofReal_mul_I_eq_eIu t₀ h, cpow_neg_ofReal_mul_I_eq_eIu (t₀ + t₁) h,
      show -(t₀ + t₁) = -t₀ + -t₁ from by ring, eIu_add]
    ring

/-- The conjugate of the `costwist` at frequency `t` is the `eIu` twist at `−t`. -/
lemma conj_costwist (t : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (costwist t n) = eIu (-t) n := by
  unfold costwist
  rw [← Complex.exp_conj, eIu_eq]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **A-9 sub-residual (1/2) — the twist-slot transfer (`pretDistSq_twist_slot`).**  The
pretentious distance to the `costwist t₁` datum equals the distance of the `−t₁`-twisted
function to the TRIVIAL datum:

  `𝔻²(f, p^{it₁}; x) = 𝔻²(f·e^{−it₁·log ·}, 1; x)`.

Exactly the slot conversion between the `HCENTER` supplier's `M`-shape (which carries
`pretDistSq f (costwist t₁) X`) and `ball_sup_of_center`'s `hMball` binder (which is stated
at `pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1)`).  A `Finset.sum_congr` over the
conjugation identity — no analysis. -/
theorem pretDistSq_twist_slot (f : ℕ → ℂ) (t₁ x : ℝ) :
    pretDistSq f (costwist t₁) x
      = pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [map_one, mul_one, conj_costwist]

/-! ## §2 — the grade page: the `k`-uniform error conversion -/

/-- `L^{−1/2} = 1/√L`. -/
private lemma rpow_neg_half_eq {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 : ℝ) / 2) = (Real.sqrt L)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `2·log X ≤ X` for `X ≥ 16` (the `√X`-route: `log X = 2 log √X ≤ 2(√X−1)`, then
`4√X − 4 ≤ X` is `(√X−2)² ≥ 0`). -/
private lemma two_log_le_self {X : ℝ} (hX : 16 ≤ X) : 2 * Real.log X ≤ X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs4 : (4 : ℝ) ≤ Real.sqrt X := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h16]
    exact Real.sqrt_le_sqrt hX
  have hlog : Real.log (Real.sqrt X) ≤ Real.sqrt X - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  nlinarith [hs4, hlog, hsq, hhalf]

/-- `25 ≤ exp 8` (used only to place the threshold above `16`). -/
private lemma twentyfive_le_exp_eight : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- **THE GRADE PAGE (`center_error_grade`).**  The two error legs of the centre
composition — the desmooth cost `h+1 = k/√(log k) + 1` and the S1′ `E`-error, already
reduced to `D·k·loglog k/log k` — are converted into the SINGLE `X`-scale term
`4·k·(log X)^{−1/2+1/1000}`, uniformly over the dyadic window `X−1 < k ≤ 2X`.

The three conversions, each elementary: `log k ∈ [L/2, 2L]` (the window, `L := log X`);
`loglog k / log k ≤ 4·loglog X / log X`, absorbed by `hB` (A-6 at the pinned `ε = 1/1000`);
`1/√(log k) ≤ 2/√L` and `1 ≤ k/√L` (the latter from `2·log X ≤ X`, `two_log_le_self`). -/
private lemma center_error_grade {D X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ)) (hk2 : (k : ℝ) ≤ 2 * X)
    (hB : 4 * D * Real.log (Real.log X) * Real.log X ^ (-(1 : ℝ))
        ≤ Real.log X ^ (-(1 : ℝ) + 1 / 1000)) :
    D * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight hX8
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hkX2 : X / 2 ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  set L := Real.log X with hLdef
  have hL8 : (8 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos 8) hX8
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set Lk := Real.log (k : ℝ) with hLkdef
  have hLklo : L - Real.log 2 ≤ Lk := by
    have h1 : Real.log (X / 2) ≤ Lk := Real.log_le_log (by linarith) hkX2
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hLkhi : Lk ≤ L + Real.log 2 := by
    have h1 : Lk ≤ Real.log (2 * X) := Real.log_le_log hk0 hk2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hLk1 : (1 : ℝ) ≤ Lk := by linarith
  have hLk0 : (0 : ℝ) < Lk := by linarith
  have hLkhalf : L / 2 ≤ Lk := by linarith
  have hLk2L : Lk ≤ 2 * L := by linarith
  have hlogLk0 : (0 : ℝ) ≤ Real.log Lk := Real.log_nonneg hLk1
  have hlogL0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  -- STEP A/B/C — `loglog k / log k ≤ 4·loglog X / log X`
  have hlogLk : Real.log Lk ≤ 2 * Real.log L := by
    have h1 : Real.log Lk ≤ Real.log (2 * L) := Real.log_le_log hLk0 hLk2L
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hstepC : Real.log Lk / Lk ≤ 4 * (Real.log L / L) := by
    have hq0 : (0 : ℝ) ≤ 4 * (Real.log L / L) := by positivity
    have h1 : 4 * (Real.log L / L) * (L / 2) ≤ 4 * (Real.log L / L) * Lk :=
      mul_le_mul_of_nonneg_left hLkhalf hq0
    have h2 : 4 * (Real.log L / L) * (L / 2) = 2 * Real.log L := by
      field_simp
      ring
    rw [div_le_iff₀ hLk0]
    linarith
  -- STEP D — the A-6 absorption at the pin
  have hLinv : L ^ (-(1 : ℝ)) = 1 / L := by rw [Real.rpow_neg_one, one_div]
  have hPmono : L ^ (-(1 : ℝ) + 1 / 1000) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hstepD : D * (Real.log Lk / Lk) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : D * (Real.log Lk / Lk) ≤ D * (4 * (Real.log L / L)) :=
      mul_le_mul_of_nonneg_left hstepC hD0
    have h2 : D * (4 * (Real.log L / L)) = 4 * D * Real.log L * L ^ (-(1 : ℝ)) := by
      rw [hLinv]; field_simp
    linarith
  -- STEP E — the desmooth leg
  have hsqL0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsqL2 : Real.sqrt L / 2 ≤ Real.sqrt Lk := by
    have hq : Real.sqrt (L / 4) = Real.sqrt L / 2 := by
      rw [show L / 4 = L * (1 / 2) ^ 2 from by ring, Real.sqrt_mul hL0.le,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    calc Real.sqrt L / 2 = Real.sqrt (L / 4) := hq.symm
      _ ≤ Real.sqrt Lk := Real.sqrt_le_sqrt (by linarith)
  have hsqL20 : (0 : ℝ) < Real.sqrt L / 2 := by linarith
  have hdes : (k : ℝ) / Real.sqrt Lk ≤ 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
    have h1 : (k : ℝ) / Real.sqrt Lk ≤ (k : ℝ) / (Real.sqrt L / 2) :=
      div_le_div_of_nonneg_left hk0.le hsqL20 hsqL2
    have h2 : (k : ℝ) / (Real.sqrt L / 2) = 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
      rw [rpow_neg_half_eq hL0]
      field_simp
    linarith
  -- STEP F — `1 ≤ k·L^{−1/2}`
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
    linarith
  -- STEP G — assemble
  have hPnn : (0 : ℝ) ≤ L ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hGmono : L ^ (-(1 : ℝ) / 2) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hterm1 : D * ((k : ℝ) * (Real.log Lk / Lk))
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h := mul_le_mul_of_nonneg_left hstepD hk0.le
    calc D * ((k : ℝ) * (Real.log Lk / Lk)) = (k : ℝ) * (D * (Real.log Lk / Lk)) := by ring
      _ ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := h
  have hterm2 : (k : ℝ) * L ^ (-(1 : ℝ) / 2)
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left hGmono hk0.le
  linarith

/-! ## §3 — THE CLOSURE: `center_halasz_supply` -/

/-- **A-9 — THE `HCENTER` CLOSURE (`center_halasz_supply`).**  The pointwise Halász bound at
the ball centre, in exactly `BallSup.ball_sup_of_center`'s `hCenter` binder shape at the seam
datum `f := seamCoeff (ellLin g) (fun _ => 1) t₀`:

  `∀ k ∈ [⌊X⌋₊, N],  ‖∑_{n≤k} f n · e^{−it₁ log n}‖ ≤ S₀·k`,
  `S₀ = C₁·exp(−(1/(2e))·𝔻²(f, p^{it₁}; X)) + 4·(log X)^{−1/2+1/1000}`.

**M-SHAPED, no numeral** (⟦AMENDMENT V2⟧ item 4): the distance rides through the whole
composition as an opaque real; the consumer instantiates `t₁` at the global minimizer
(⟦THE TWO-M READING⟧).  `ε = 1/1000` is the pinned absorption exponent (V2 repair 3), below
both caps (`1/(192e) ≈ 0.00184`, `1/(64e) − 1/500 ≈ 0.00375`).

**The composition.**  Per scale `k`: `seamCoeff_twist_combine` re-centres the twisted seam
datum at `t₀+t₁`; `prop21_desmooth_reduction` passes to the hat-smoothed sum at cost
`h+1`; `prop21_uniform_at_scale_absC` — the datum-hoisted A-7b form, whose constants
precede `(g, t₀)` and are therefore uniform over the `X`-dependent centre `t₀+t₁` — replaces
the smoothed sum by `prop21RHS` at cost `E`; `center_error_grade` converts `h+1` and `E`
into the single `X`-scale tail.  Each gate of the S1′ pin (`h = k/√(log k)`, `c₀ = 1+1/log k`,
`y = (log k)⁴`, `η = 1/log y`) is discharged inside `prop21_uniform_at_scale_absC` from the
single threshold, so the only scale hypothesis here is `X₀ ≤ X`.

**The ONE named residual `hRHS`** (the honest frontier, per the module docstring): the
`‖prop21RHS‖ ≤ C₁·k·e^{−M/(2e)}` leg.  Its chain is landed to the terminal grade socket
`Agrade ≤ C₁·X`, which `JointHead`'s HGRADE record proves does NOT discharge on this route
(a genuine `log log X` survives even at the `Tsplit`-sharp kernel face).  It is carried, not
forced.

**LIVE GUARD**: `c = 1/(2e)` is the BALL arm's halved constant; a §8.3 consumer citing this
head is a STOP. -/
theorem center_halasz_supply {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (C₁ : ℝ), X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ C₁ →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
              ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)) →
      ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨XA, C_E, C_R, hCE0, hCR0, hrep⟩ := prop21_uniform_at_scale_absC
  obtain ⟨XB, _hXB0, hB⟩ :=
    loglog_absorb_pow_pin (C := 4 * (8 * C_E + 4 * C_R)) (by positivity) 1
  refine ⟨max (max (XA + 1) XB) (Real.exp 8),
    lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro X N C₁ hXlb hXN hN2 hC₁0 hRHS k hkfl hkN
  -- the threshold split
  have hX8 : Real.exp 8 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXA1 : XA + 1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXB : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight hX8
  have hX0 : (0 : ℝ) < X := by linarith
  -- the dyadic `k`-window
  have hfl : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hk1 : X - 1 < (k : ℝ) := by
    have h : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkfl
    linarith
  have hk2 : (k : ℝ) ≤ 2 * X := le_trans (Nat.cast_le.mpr hkN) hN2
  have hkXA : XA ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1le : (1 : ℝ) ≤ (k : ℝ) := by linarith
  -- `log k ≥ 1` (the window: `log k ≥ log X − log 2 ≥ 8 − 0.7`)
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL8 : (8 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hX8
  have hLklo : Real.log X - Real.log 2 ≤ Real.log (k : ℝ) := by
    have h1 : Real.log (X / 2) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hLk1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by linarith
  have hLk0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hsqLk1 : (1 : ℝ) ≤ Real.sqrt (Real.log (k : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hLk1
  have hsqLk0 : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hh0 : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by positivity
  have hhX : (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) ≤ (k : ℝ) := by
    rw [div_le_iff₀ hsqLk0]; nlinarith
  -- the two landed legs, at scale `k`
  have hdes := prop21_desmooth_reduction (f := ellLin g) (gJ := fun _ => 1) (t₀ + t₁)
    (fun n => ellLin_norm_le_one g hg n) (fun _ => by simp)
    (X := (k : ℝ)) (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) hk1le hh0 hhX
  rw [Nat.floor_natCast] at hdes
  have hr := hrep g hg (t₀ + t₁) (k : ℝ) hkXA
  have hR := hRHS k hkfl hkN
  -- the twist combine
  have hsum : (∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
      = ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n :=
    Finset.sum_congr rfl (fun n _ => seamCoeff_twist_combine _ _ t₀ t₁ n)
  rw [hsum]
  -- the triangle chain
  set A := ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n with hAdef
  set B := ∑' n, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n
    * (hatK (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) n : ℂ) with hBdef
  set R := prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
    (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
    (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4)) with hRdef
  have hid : A = (A - B) + ((B - R) + R) := by ring
  have htri : ‖A‖ ≤ ‖A - B‖ + (‖B - R‖ + ‖R‖) := by
    calc ‖A‖ = ‖(A - B) + ((B - R) + R)‖ := by rw [← hid]
      _ ≤ ‖A - B‖ + ‖(B - R) + R‖ := norm_add_le _ _
      _ ≤ ‖A - B‖ + (‖B - R‖ + ‖R‖) := by
          linarith [norm_add_le (B - R) R]
  -- the `E`-error, reduced to the `D·k·loglog k/log k` shape
  have hlogpow : Real.log (Real.log (k : ℝ) ^ 4) = 4 * Real.log (Real.log (k : ℝ)) := by
    rw [Real.log_pow]; norm_num
  have hlogLk0 : (0 : ℝ) ≤ Real.log (Real.log (k : ℝ)) := Real.log_nonneg hLk1
  have hu0 : (0 : ℝ) < (k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hulogb : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
    Real.log_le_log hk0 (by linarith)
  have huq : ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
        / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
      ≤ 2 * (k : ℝ) / Real.log (k : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) hLk0]
    nlinarith
  have hEle : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
          / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
        * Real.log (Real.log (k : ℝ) ^ 4)
      + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Real.log (k : ℝ) ^ 4)
      ≤ (8 * C_E + 4 * C_R)
          * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
    rw [hlogpow]
    have h1 : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
            / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
          * (4 * Real.log (Real.log (k : ℝ)))
        ≤ C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ))) := by
      have hq : (0 : ℝ) ≤ 4 * Real.log (Real.log (k : ℝ)) := by linarith
      have := mul_le_mul_of_nonneg_left huq hCE0
      exact mul_le_mul_of_nonneg_right this hq
    have h2 : C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
          + C_R * ((k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
        = (8 * C_E + 4 * C_R)
            * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
      field_simp
      ring
    linarith
  -- the grade page
  have hgrade := center_error_grade (D := 8 * C_E + 4 * C_R) (X := X) (k := k)
    (by positivity) hX8 hk1 hk2 (hB X hXB)
  have hexpand : (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
        + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith

/-! ## §4 — THE CROWN: the `hSup′` discharge at the centre -/

/-- The seam datum is normalised: `seamCoeff (ellLin g) 1 t₀ 1 = 1`. -/
lemma seamCoeff_ellLin_one (g : ℕ → ℂ) (t₀ : ℝ) :
    seamCoeff (ellLin g) (fun _ => 1) t₀ 1 = 1 := by
  simp [seamCoeff, ellLin]

/-- **The seam datum is multiplicative** (`ball_sup_of_center`'s `hfmul`).  `ellLin g` is
coprime-multiplicative (`ellLin_mul_coprime`) and the centre twist `n ↦ n^{−it₀}` is
completely multiplicative on the positive reals (`eIu_mul`, through §1's `eIu` bridge); the
`0`-slot is handled by `seamCoeff`'s own convention. -/
lemma seamCoeff_ellLin_mul_coprime (g : ℕ → ℂ) (t₀ : ℝ) (p q : ℕ) (hco : Nat.Coprime p q) :
    seamCoeff (ellLin g) (fun _ => 1) t₀ (p * q)
      = seamCoeff (ellLin g) (fun _ => 1) t₀ p * seamCoeff (ellLin g) (fun _ => 1) t₀ q := by
  rcases eq_or_ne p 0 with hp | hp
  · subst hp
    have hq : q = 1 := by simpa [Nat.coprime_zero_left] using hco
    subst hq
    simp [seamCoeff]
  rcases eq_or_ne q 0 with hq | hq
  · subst hq
    have hp1 : p = 1 := by simpa [Nat.coprime_zero_right] using hco
    subst hp1
    simp [seamCoeff]
  have hpq : p * q ≠ 0 := Nat.mul_ne_zero hp hq
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  unfold seamCoeff
  rw [if_neg hpq, if_neg hp, if_neg hq, ellLin_mul_coprime g hp hq hco,
    cpow_neg_ofReal_mul_I_eq_eIu t₀ hpq, cpow_neg_ofReal_mul_I_eq_eIu t₀ hp,
    cpow_neg_ofReal_mul_I_eq_eIu t₀ hq,
    show ((p * q : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) from by push_cast; ring,
    eIu_mul (-t₀) hpr hqr]
  ring

/-- **THE CROWN (`ball_sup_supplied`).**  `center_halasz_supply` fed into
`BallSup.ball_sup_of_center`: the pointwise weighted ball bound in exactly
`SeamBallWeighted.ball_leg_of_sup_weighted`'s `hSup′` binder shape,

  `∀ t ∈ Ann ∩ ball, ∀ m ≤ N,  ‖spolyA a t m‖ ≤ ballSupS X S₀ · m/(1+|t−t₁|)`,
  `S₀ = C₁·exp(−(1/(2e))·𝔻²(f, p^{it₁}; X)) + 4·(log X)^{−1/2+1/1000}`,

at the seam datum `f = seamCoeff (ellLin g) (fun _ => 1) t₀`.  The datum facts `hf1`/`hfmul`
/`hfle` are DISCHARGED here (`seamCoeff_ellLin_one`, `seamCoeff_ellLin_mul_coprime`,
`norm_seamCoeff_le`); the `hMball` binder is discharged from the **A.4 ball cap in the
supplier's own M-shape** (`hMcap`, the distance at `costwist t₁`) through §1's
`pretDistSq_twist_slot` and `SmallStones.hMball_of_A4_cap` — the UNASSIGNED-3 twist-slot
sub-residual, closed.

**The four remaining binders, all honest and all named upstream**: `hsupp`/`hDatum` (the
dyadic bridge — the row's, not this leg's), `hRHS` (the joint-head grade socket; see the
module docstring), and `hMcap` (the A-10 ball-centre dichotomy — the ball's live band
`[(1/32)loglog, (1/16)loglog)`).  Nothing else is assumed. -/
theorem ball_sup_supplied {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (T C₁ : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ C₁ →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
              ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
            pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
              ≤ (1 / 16) * Real.log (Real.log X)) →
      ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
        ∀ m : ℕ, m ≤ N →
          ‖spolyA a t m‖
            ≤ ballSupS X (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|) := by
  obtain ⟨X₁, hX₁0, hsupply⟩ := center_halasz_supply hg t₀ t₁
  refine ⟨max X₁ ballMertensThreshold, lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro X N T C₁ a hXlb hXN hN2 hC₁0 hsupp hDatum hRHS hMcap
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hXth : ballMertensThreshold ≤ X := le_trans (le_max_right _ _) hXlb
  have hX3 : (3 : ℝ) ≤ X := le_trans three_le_ballMertensThreshold hXth
  have hlogX0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hS₀ : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) :=
      mul_nonneg hC₁0 (Real.exp_nonneg _)
    have h2 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hlogX0 _
    linarith
  have hMball : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
          (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8 := by
    refine hMball_of_A4_cap hXth ?_
    intro x h1 h2
    rw [← pretDistSq_twist_slot]
    exact hMcap x h1 h2
  exact ball_sup_of_center hX3 hXN hN2 (seamCoeff_ellLin_one g t₀)
    (seamCoeff_ellLin_mul_coprime g t₀)
    (fun n => norm_seamCoeff_le (fun m => ellLin_norm_le_one g hg m) (fun _ => by simp) t₀ n)
    hS₀ hsupp hDatum (hsupply X N C₁ hX1 hXN hN2 hC₁0 hRHS) hMball

end Salt.MR
