/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SiegelBand
import Salt.MR.EvenChiDescent

/-!
# POINT→BAND, step 1 — the band `L`-lower with a STATED RATE in `q` (`BandRated`)

`QUEUE.md` P2 item 6, commissioned at WORKER tier by helm ruling 2026-08-26 06:0x.
**Standing instruction, adopted verbatim: SPEND NOTHING ON GRADE.**

## What this file is for

`SiegelBand.chi_Llower_band_uniform` produces a band constant `B(Q)` by a bare induction-max over
the characters of every modulus `q ≤ Q`, and its own header records the consequence: *"it has no
known growth rate in `Q`"*.  That is the ineffectivity the `K_vt` cushion inherits — and the
cushion evaluates it at `Qm = ⌈(log H₊)^12⌉₊`, i.e. at an argument that grows with the same `H₊`
that funds the budget, so **an unrated constant there is not slack, it is a demanded exponent**
(`arc.md` §4's struck R-1; measured `Qm^0.083 → 1/12`).

This file starts the repair at the one seam that needs it.  `chi_floor_band_uniform` composes
`chi_Llower_band_uniform` into `ChiFloorLow.chi_floor_low_of_Llower`; **replacing only the first
factor** with a RATED band lower bound carries the composition through.

## The rate, and where it comes from

`SiegelArm` §6 already built the uniform arm conditional on ONE input — a lower bound for
`(L(1,χ)).re` — in `chi_Llower_real_of_L1`.  `EvenChiDescent.l1LowerEffective_goldenGate` supplies
exactly that input, **effectively**, for every real nonprincipal `χ`:
`L1LowerEffective (log((3+√5)/2)) (5/2)`.  Instantiating one at the other is this file's content.

⭐ **THE POINT OF THE STATEMENT BELOW: its only existential is `Z`, and `Z` is `q`-FREE and
`χ`-FREE** (a compact maximum over the fixed box `[1,2] × [−1,1]`, `SiegelArm.zeta_upper_band`).
Every `q`-dependence is on the page: `−log L₁ = (5/2)·log q + log(1/c)` and
`diskConst q = 27/2·√q·(1+log q)·q` (`Salt/SW/SiegelFinal.lean:53`), both explicit.  **That is the
whole difference from `chi_Llower_band_uniform`, whose `B(Q)` has no stated growth at all.**

⚠️ **AND IT IS WHY THE COEFFICIENT DROPS.**  The bound carries `(3/4)·log(1 + log X)`, which is
`X`-DEPENDENT, so through `chi_floor_low_of_Llower` the floor becomes `(1/4)·loglog X − …` where the
landed band arm gives coefficient `1`.  **That trade is structural and unrecoverable** — every
effective arm in this corpus pays that term (32 sites, 7 files), and the only arm that avoids it is
the compact-minimum one, i.e. the ineffective route.  *Coefficient 1 was the ineffectivity wearing
a better coefficient.*  The consumer demand is `(1/32)·loglog X + 25 + D` and `1/32 < 1/4`, so the
shape survives; re-deriving `capFreeFloor3_margin_all_chi_vt`'s threshold at `1/4` is the
commission's remaining content and is NOT attempted here.

⛔ **SCOPE.**  Real nonprincipal `χ` only (`χ ≠ 1`, `χ² = 1`).  That is not a gap: the cushion's band
arm is consumed **only** at `χ² = 1` with `|v| ≤ 1/2` (`VkMidSharp.capFreeFloor3_margin_all_chi_vt`
splits on `χ² = 1` first, sending `χ² ≠ 1` to the VK pointwise arm, which Wave K's numeral stones
already made effective).  The principal character's own band bound is separately EXPLICIT
(`SiegelArm.LFunction_band_lower_principal`, `δ/q`).
-/

namespace Salt.MR

open Complex DirichletCharacter Salt.SW

/-! ## §1 — the golden `L₁`, as a named function of `q` -/

/-- **The effective `L(1,χ)` floor as a function of the modulus** — `goldenGate`'s value at `q`.
`c/q^{5/2}` with `c = log((3+√5)/2) = 2·log φ`, the constant `EvenChiDescent` lands at both
parities.  Named so the rate is readable at every call site rather than inlined. -/
noncomputable def goldenL1 (q : ℕ) : ℝ :=
  Real.log ((3 + Real.sqrt 5) / 2) / (q : ℝ) ^ (5 / 2 : ℝ)

/-- `√5 < 2.3`, by squaring.  Local because it is used twice and mathlib has no numeral form. -/
private lemma sqrt_five_lt : Real.sqrt 5 < 2.3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

/-- `c = log((3+√5)/2) ≤ 1`: the argument is `≈ 2.618 < e`. -/
lemma log_golden_le_one : Real.log ((3 + Real.sqrt 5) / 2) ≤ 1 := by
  have hlt : (3 + Real.sqrt 5) / 2 < Real.exp 1 := by
    have := sqrt_five_lt
    nlinarith [Real.exp_one_gt_d9]
  have hpos : (0 : ℝ) < (3 + Real.sqrt 5) / 2 := by
    have := Real.sqrt_nonneg 5; linarith
  have hlog := Real.log_lt_log hpos hlt
  rw [Real.log_exp] at hlog
  linarith

/-- `0 < goldenL1 q` at every nonzero modulus. -/
lemma goldenL1_pos (q : ℕ) [NeZero q] : 0 < goldenL1 q := by
  have hq : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  exact div_pos e4a_log_golden_pos (Real.rpow_pos_of_pos hq _)

/-- `goldenL1 q ≤ 1`: the numerator is `≤ 1` and the denominator is `≥ 1`. -/
lemma goldenL1_le_one (q : ℕ) [NeZero q] : goldenL1 q ≤ 1 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hden : (1 : ℝ) ≤ (q : ℝ) ^ (5 / 2 : ℝ) :=
    Real.one_le_rpow hq1 (by norm_num)
  rw [goldenL1, div_le_one (by linarith : (0:ℝ) < (q : ℝ) ^ (5 / 2 : ℝ))]
  linarith [log_golden_le_one]

/-- **`goldenGate`, unfolded at `goldenL1`** — the hypothesis `chi_Llower_real_of_L1` asks for. -/
lemma goldenL1_le_LFunction_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hsq : χ ^ 2 = 1) :
    goldenL1 q ≤ (DirichletCharacter.LFunction χ 1).re :=
  l1LowerEffective_goldenGate q χ hne hsq

/-! ## §2 — the rated band `L`-lower at real nonprincipal `χ` -/

/-- ⭐ **POINT→BAND STEP 1** (`chi_Llower_band_real_rated`).  `SiegelArm.chi_Llower_real_of_L1` with
its `L₁` slot filled by the LANDED effective floor `goldenL1 q`, so the bound's entire
`q`-dependence is explicit:

`−(log 2 − log L₁ + 2log4 + (3/4)log(1+log X) + (1/4)log(16·q·Z·diskConst q / L₁))`
  `  ≤ log‖L(1+1/log X − it, χ)‖`

at `L₁ = c/q^{5/2}`, so `−log L₁ = (5/2)log q + log(1/c)`.

**The only existential is `Z`, and it is `q`-free and `χ`-free** — the compact maximum of
`SiegelArm.zeta_upper_band` over the fixed box.  Contrast `chi_Llower_band_uniform`, whose `B(Q)`
is a bare induction-max with no stated growth: *that* is the difference the `K_vt` cushion needs,
because the cushion evaluates its constant at an argument growing with `H₊`.

The scale gate `32·diskConst q / goldenL1 q ≤ log X` is `chi_Llower_real_of_L1`'s own and is
CARRIED, not discharged — at the door's range it clears with enormous room (`loglog X ≥ log H₊ − 14`
against a demand polynomial in `q`), but that discharge belongs to the consumer, not here. -/
theorem chi_Llower_band_real_rated :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 / 2 →
        32 * diskConst q / goldenL1 q ≤ Real.log X →
          -(Real.log 2 - Real.log (goldenL1 q)
              + (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
                + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q)))
            ≤ Real.log ‖DirichletCharacter.LFunction χ
                (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨Z, hZ1, hL⟩ := chi_Llower_real_of_L1
  refine ⟨Z, hZ1, ?_⟩
  intro q _ χ hne hsq X t hX ht hgate
  exact hL q χ hne hsq X t (goldenL1 q) hX ht (goldenL1_pos q) (goldenL1_le_one q)
    (goldenL1_le_LFunction_one χ hne hsq) hgate

/-! ## §3 — the principal arm with the constant HOISTED OUT of `∀ q` -/

/-- **The band rate at real nonprincipal `χ`, named.**  Exactly §2's bound, as a function, so the
join below can majorise it.  Every `q`-dependence is inside: `−log (goldenL1 q)` contributes
`(5/2)·log q + log(1/c)`, and `diskConst q` is the explicit `27/2·√q·(1+log q)·q`. -/
noncomputable def bandRateReal (Z : ℝ) (q : ℕ) (X : ℝ) : ℝ :=
  Real.log 2 - Real.log (goldenL1 q)
    + (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
      + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q))

/-- §2 restated against `bandRateReal`, so the join can weaken into a `max`. -/
theorem chi_Llower_band_real_rated' :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 / 2 →
        32 * diskConst q / goldenL1 q ≤ Real.log X →
          -(bandRateReal Z q X)
            ≤ Real.log ‖DirichletCharacter.LFunction χ
                (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨Z, hZ1, hL⟩ := chi_Llower_band_real_rated
  refine ⟨Z, hZ1, ?_⟩
  intro q _ χ hne hsq X t hX ht hgate
  simpa [bandRateReal] using hL q χ hne hsq X t hX ht hgate

/-- ⭐ **POINT→BAND STEP 2a** (`LFunction_band_lower_principal_uniform`).
`SiegelArm.LFunction_band_lower_principal` with its constant **HOISTED OUT of `∀ q`**.

⛔ **WHY THE HOIST IS THE WHOLE POINT AND NOT COSMETIC.**  The landed statement reads
`∀ q, ∃ m, … m/q ≤ ‖L‖`, so `m` is formally a function of `q` and the bound carries **no rate**:
`−log(m q) + log q` is only rated if `m` is bounded below uniformly.  Its PROOF takes `m` from
`ZetaLowerAllT.zeta_lower_small_t`, which is `q`-free — so the uniformity was always there and only
the quantifier order hid it.  ⇒ ***A CONSTANT QUANTIFIED INSIDE `∀ q` IS UNRATED BY CONSTRUCTION,
EVEN WHEN ITS WITNESS IS `q`-FREE; THE RATE LIVES IN THE PREFIX, NOT THE PROOF.***

Body is `LFunction_band_lower_principal`'s verbatim (`SiegelArm` §3): `ζ`'s pole only helps, and
the Euler product over `q.primeFactors` costs at most `q` (`eulerFactor_prod_lower`). -/
theorem LFunction_band_lower_principal_uniform :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ) [NeZero q], ∀ d t : ℝ, 0 < d → d ≤ 1 → |t| ≤ 1 →
      δ / (q : ℝ) ≤ ‖LFunction (1 : DirichletCharacter ℂ q)
        (((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨δ, hδ, hsmall⟩ := zeta_lower_small_t
  refine ⟨δ, hδ, ?_⟩
  intro q _ d t hd0 hd1 ht
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  set s : ℂ := ((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1 + d := by
    rw [hsdef]
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hsre
    linarith
  have hz : δ ≤ ‖riemannZeta s‖ := by
    have h := hsmall d (-t) hd0.le hd1 (by rw [abs_neg]; linarith) (fun hc => absurd hc.1 hd0.ne')
    have hpt : ((1 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = s := by
      rw [hsdef]; push_cast; ring
    rwa [hpt] at h
  have hprod : 1 / (q : ℝ) ≤ ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ :=
    eulerFactor_prod_lower q (by rw [hsre]; linarith)
  have hfac : LFunction (1 : DirichletCharacter ℂ q) s
      = (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
    LFunctionTrivChar_eq_mul_riemannZeta hs1
  rw [hfac, norm_mul]
  have hmul : (1 / (q : ℝ)) * δ
      ≤ ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖ :=
    mul_le_mul hprod hz hδ.le (norm_nonneg _)
  have hdiv : δ / (q : ℝ) = (1 / (q : ℝ)) * δ := by field_simp
  linarith [hdiv.le, hdiv.symm.le, hmul]

/-! ## §4 — the join: a RATED band `L`-lower for the whole `χ² = 1` class -/

/-- ⭐⭐ **POINT→BAND STEP 2** (`chi_Llower_band_realclass_rated`) — the rated replacement for
`SiegelBand.chi_Llower_band_uniform` on the class the `K_vt` cushion actually consumes.

`capFreeFloor3_margin_all_chi_vt` splits on `χ² = 1` FIRST and sends `χ² ≠ 1` to the VK pointwise
arm (which Wave K's numeral stones already made effective), so **the band arm is consumed only at
`χ² = 1`** — principal and real-nonprincipal together, which is exactly this statement's range.

**BOTH constants are hoisted and neither depends on `q` or `χ`:** `Z` is `zeta_upper_band`'s compact
max, `δ` is `zeta_lower_small_t`'s.  The `q`-dependence is the explicit `max (log q − log δ)
(bandRateReal Z q X)` — a `log q` rate on the principal branch and `O(log q) + (3/4)log(1+log X)` on
the real branch.  ⇒ **contrast `chi_Llower_band_uniform`, whose `B(Q)` is a bare induction-max over
every modulus `≤ Q` with no stated growth**: that unrated constant is what the cushion inherits, and
this statement is what replaces it.

⚠️ The `X`-dependent `(3/4)log(1+log X)` inside `bandRateReal` is what costs the floor's coefficient
`1 → 1/4` downstream — structural, unrecoverable, and already ruled acceptable
(`QUEUE.md` P2 item 6:
the consumer demand `(1/32)·loglog X + 25 + D` still clears `1/4`).
⛔ The scale gate is carried, not discharged. -/
theorem chi_Llower_band_realclass_rated :
    ∃ Z δ : ℝ, 1 ≤ Z ∧ 0 < δ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 / 2 →
        32 * diskConst q / goldenL1 q ≤ Real.log X →
          -(max (Real.log q - Real.log δ) (bandRateReal Z q X))
            ≤ Real.log ‖DirichletCharacter.LFunction χ
                (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨Z, hZ1, hreal⟩ := chi_Llower_band_real_rated'
  obtain ⟨δ, hδ, hprin⟩ := LFunction_band_lower_principal_uniform
  refine ⟨Z, δ, hZ1, hδ, ?_⟩
  intro q _ χ hsq X t hX ht hgate
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  by_cases hχ1 : χ = 1
  · -- principal: the hoisted `δ/q`, then weaken into the `max`
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
    have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
    have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
    have hb := hprin q (1 / Real.log X) t hd0 hd1 (by linarith [abs_nonneg t])
    rw [hχ1]
    have hpos : (0 : ℝ) < δ / (q : ℝ) := div_pos hδ hqR
    have hlog := Real.log_le_log hpos hb
    have hsplit : Real.log (δ / (q : ℝ)) = Real.log δ - Real.log q :=
      Real.log_div (ne_of_gt hδ) (ne_of_gt hqR)
    rw [hsplit] at hlog
    have hmax : Real.log q - Real.log δ
        ≤ max (Real.log q - Real.log δ) (bandRateReal Z q X) := le_max_left _ _
    linarith
  · -- real nonprincipal: §2', then weaken into the `max`
    have hb := hreal q χ hχ1 hsq X t hX ht hgate
    have hmax : bandRateReal Z q X
        ≤ max (Real.log q - Real.log δ) (bandRateReal Z q X) := le_max_right _ _
    linarith

/-! ## §5 — step (ii): the rated band FLOOR, through `chi_floor_low_of_Llower` -/

/-- ⭐⭐ **POINT→BAND STEP 3** (`chi_floor_band_realclass_rated`) — §4 composed with
`ChiFloorLow.chi_floor_low_of_Llower`, giving the χ-quality FLOOR with a stated rate.

This is the rated counterpart of `SiegelBand.chi_floor_band_uniform`, and it is reached the same
way — that file composes `chi_Llower_band_uniform` into `chi_floor_low_of_Llower`; **this composes
§4 into the very same lemma.**  The seam really was one factor.

⚠️ **READ THE COEFFICIENT CAREFULLY — it is 1 on `loglog X` HERE, and the `1/4` appears only after
`B` is unfolded.**  `chi_floor_low_of_Llower` returns `loglog X − B − K` at coefficient EXACTLY 1
(that is its whole point: no `k²` division, no `min` with the `orderOf χ` branch).  Our `B` carries
`bandRateReal`, which contains `(3/4)·log(1 + log X)`; so once `B` is expanded the surviving growth
is `(1/4)·loglog X − O(log q) − O(1)`.  ⇒ ***THE `1/4` IS INSIDE `B`, NOT A DIFFERENT COEFFICIENT ON
THE STATEMENT — a consumer that reads the coefficient off this statement without unfolding `B` will
over-credit the floor by a factor of four.***

⛔ **NOT DONE HERE — the commission's remaining content:** `capFreeFloor3_margin_all_chi_vt`'s
`linarith` threshold is calibrated against the coefficient-1 band arm and must be RE-DERIVED against
this one.  The consumer demand `(1/32)·loglog X + 25 + D` clears `1/4`, so the shape survives; the
arithmetic does not transfer for free. -/
theorem chi_floor_band_realclass_rated :
    ∃ Z δ K : ℝ, 1 ≤ Z ∧ 0 < δ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 / 2 →
        32 * diskConst q / goldenL1 q ≤ Real.log X →
          Real.log (Real.log X) - max (Real.log q - Real.log δ) (bandRateReal Z q X) - K
            ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨K, hK⟩ := chi_floor_low_of_Llower
  obtain ⟨Z, δ, hZ1, hδ, hband⟩ := chi_Llower_band_realclass_rated
  refine ⟨Z, δ, K, hZ1, hδ, ?_⟩
  intro q _ χ hsq X t hX ht hgate
  exact hK q χ X t (max (Real.log q - Real.log δ) (bandRateReal Z q X)) hX
    (hband q χ hsq X t hX ht hgate)

/-! ## §6 — step (iii)a: the floor in the consumer's shape, `(1/4)·loglog X − (X-free) − K` -/

/-- `log (1 + log X) ≤ log 2 + loglog X`.  `VkMidSharp.vt_log_one_add_log_le` and
`VkTwistClose.vk_log_one_add_log_le` are both `private`; this is the same three lines, which is
the idiom those two files already established for it. -/
private lemma br_log_one_add_log_le {X : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.log (1 + Real.log X) ≤ Real.log 2 + Real.log (Real.log X) := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  calc Real.log (1 + Real.log X) ≤ Real.log (2 * Real.log X) :=
        Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + Real.log (Real.log X) := Real.log_mul (by norm_num) (by linarith)

/-- **The band rate's `X`-FREE part** — `bandRateReal` with its one `X`-dependent term replaced by
the constant it contributes after `br_log_one_add_log_le`, joined against the principal branch.
This is the object a consumer's threshold arithmetic can actually carry: it depends on `q`, `Z`, `δ`
and nothing else, and its growth is `O(log q)`. -/
noncomputable def bandConstQ (Z δ : ℝ) (q : ℕ) : ℝ :=
  max (Real.log q - Real.log δ)
    (Real.log 2 - Real.log (goldenL1 q) + (2 * Real.log 4 + (3 / 4) * Real.log 2
      + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q)))

/-- ⭐⭐⭐ **POINT→BAND STEP 4** (`chi_floor_band_realclass_quarter`) — the rated band floor in the
shape the assembly consumes: **`(1/4)·loglog X − C(q) − K`, with `C(q)` `X`-FREE and `O(log q)`.**

This is where the `1 → 1/4` trade becomes visible in the statement instead of hiding inside `B`, and
it is deliberately a separate step from §5 for exactly that reason — §5's coefficient-1 form is the
one a reader can misread by a factor of four.

The single move is `br_log_one_add_log_le`: `bandRateReal` carries `(3/4)·log(1 + log X)`, which is
`≤ (3/4)·log 2 + (3/4)·loglog X`, so the `X`-dependence separates into a clean `(3/4)·loglog X`
subtracted from the floor's own `loglog X`.  The `max` survives the split because the extra
`(3/4)·loglog X` is NONNEGATIVE at this scale (`X ≥ exp(exp 1)`), which is why the scale floor is
`exp(exp 1)` here and `exp 1` in §5.

⛔ **STILL NOT (iii) ITSELF.**  `capFreeFloor3_margin_all_chi_vt`'s threshold is calibrated against a
coefficient-1 band arm; re-deriving it against THIS statement is the commission's last piece.  What
this step buys is that the re-derivation now has an `X`-free `C(q)` to carry, instead of a rate
tangled with `log(1 + log X)`. -/
theorem chi_floor_band_realclass_quarter :
    ∃ Z δ K : ℝ, 1 ≤ Z ∧ 0 < δ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp (Real.exp 1) ≤ X → |t| ≤ 1 / 2 →
        32 * diskConst q / goldenL1 q ≤ Real.log X →
          (1 / 4) * Real.log (Real.log X) - bandConstQ Z δ q - K
            ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨Z, δ, K, hZ1, hδ, hfloor⟩ := chi_floor_band_realclass_rated
  refine ⟨Z, δ, K, hZ1, hδ, ?_⟩
  intro q _ χ hsq X t hX ht hgate
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogXe : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith [Real.exp_pos (1 : ℝ)]
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    have := (Real.le_log_iff_exp_le hlogXpos).mpr hlogXe
    linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := by linarith
  have hbase := hfloor q χ hsq X t hXe ht hgate
  have hone := br_log_one_add_log_le hXe
  have hmax : max (Real.log q - Real.log δ) (bandRateReal Z q X)
      ≤ bandConstQ Z δ q + (3 / 4) * Real.log (Real.log X) := by
    refine max_le ?_ ?_
    · have h := le_max_left (Real.log q - Real.log δ)
        (Real.log 2 - Real.log (goldenL1 q) + (2 * Real.log 4 + (3 / 4) * Real.log 2
          + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q)))
      simp only [bandConstQ]
      linarith
    · have h := le_max_right (Real.log q - Real.log δ)
        (Real.log 2 - Real.log (goldenL1 q) + (2 * Real.log 4 + (3 / 4) * Real.log 2
          + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / goldenL1 q)))
      simp only [bandConstQ, bandRateReal]
      linarith
  linarith

/-! ## §7 — step (iii): the margin threshold, RE-DERIVED against the `1/4` floor -/

/-- ⭐⭐⭐ **POINT→BAND STEP 5 — THE COMMISSION'S LAST PIECE** (`margin_band_threshold_rated`).
`VkMidSharp.capFreeFloor3_margin_all_chi_vt`'s **band branch**, re-derived against the rated
`1/4`-effective floor instead of the coefficient-1 band arm.

⛔ **WHY A SIBLING AND NOT AN EDIT.**  The landed `capFreeFloor3_margin_all_chi_vt` is consumed
across the cushion chain; its `χ² ≠ 1` and `|v| > 1/2` branches are UNCHANGED by this work (Wave K's
numeral stones already made `Kvk`/`Kbulk` effective).  Only the `χ² = 1`, `|v| ≤ 1/2` branch —
the one that reads the band arm — needed the re-derivation, so only that branch is restated.

📐 **THE ARITHMETIC, which is the whole of step (iii).**  The landed branch consumed
`loglog X − C ≤ 𝔻²` and needed `(1/32)·loglog X + 25 + D < loglog X − C`, i.e. `C + 25 + D` under
`(31/32)·loglog X`.  Ours consumes `(1/4)·loglog X − bandConstQ − K ≤ 𝔻²`
(`chi_floor_band_realclass_quarter`) and therefore needs

  `bandConstQ + K + 25 + D  <  (1/4 − 1/32)·loglog X = (7/32)·loglog X`.

⭐ **AND THE LANDED THRESHOLD SHAPE ALREADY CLEARS IT WITH ROOM TO SPARE.**  A hypothesis of the
family `32·(… + 25 + D) < loglog X` gives `… + 25 + D < (1/32)·loglog X`, and
`(1/32) ≤ (7/32)`.  ⇒ ***THE COEFFICIENT DROP `1 → 1/4` COSTS A FACTOR 7 OF SLACK IN A THRESHOLD
THAT WAS ALREADY SPENDING 1/32 OF ITS BUDGET — WHICH IS WHY THE SHAPE SURVIVED THE TRADE.***  The
`1/32` on the consumer side and the `1/4` on the supply side never had to meet closely; the census's
"the shape survives" is now the kernel's statement rather than an estimate.

📌 The threshold is carried EXPLICITLY and `q`-dependently (`bandConstQ Z δ q` in the hypothesis),
per `CapFreeAssembly` §4's own law: the demand a consumer must meet is on the page, not folded into
an opaque constant.  That is also what makes it *rated* — the whole point of the commission. -/
theorem margin_band_threshold_rated :
    ∃ Z δ K : ℝ, 1 ≤ Z ∧ 0 < δ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X D : ℝ), χ ^ 2 = 1 →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      32 * diskConst q / goldenL1 q ≤ Real.log X →
      32 * (bandConstQ Z δ q + K + 25 + D) < Real.log (Real.log X) →
      ∀ v : ℝ, |v| ≤ 1 / 2 →
        (1 / 32) * Real.log (Real.log X) + 25 + D
          < pretDistSq (lamChi χ) (costwist v) X := by
  obtain ⟨Z, δ, K, hZ1, hδ, hquarter⟩ := chi_floor_band_realclass_quarter
  refine ⟨Z, δ, K, hZ1, hδ, ?_⟩
  intro q _ χ X D hsq hX hD0 hgate hthr v hv
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXe : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr he1) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hlogXe : Real.exp 1 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith [Real.exp_pos (1 : ℝ)]
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := by
    have := (Real.le_log_iff_exp_le hlogXpos).mpr hlogXe
    linarith [Real.exp_pos (1 : ℝ)]
  have hfl := hquarter q χ hsq X v hX hv hgate
  linarith

end Salt.MR
