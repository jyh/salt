/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SiegelArm
import Mathlib.Data.Fintype.Lattice

/-!
# The D3 stones — the UNIFORM bounded-band χ-quality floor (`SiegelBand`)

`SiegelArm.lean` lands the per-character band bound `chi_Llower_band`: for every `q ≠ 0`
and every `χ mod q` there is an `X`-INDEPENDENT `B` with
`−B ≤ log‖L(1 + 1/log X − it, χ)‖` for all `X ≥ e`, `|t| ≤ 1`.  Its scope line records the
missing piece as "uniformity in `q`", and reads that as needing the ineffective
`L(1,χ) ≫_ε q^{−ε}` port.  **For a FINITE range of moduli it needs no port at all.**

That is this file.  The consumer of the floor is a REGIME statement: the head builder
(`log_chowla_two_budget_head_g` / `budget_head_grade_closed_g`) carries an arbitrary
`g : ℕ → ℕ → ℕ` with `g R.Hhi R.ω ≤ R.x`, so the outer scale `x` may be pushed above any
threshold that depends on `Hhi` and `ω` ALONE.  The modulus range the door quantifies over
is `q ≤ W` with `W = (log H)^{12}` — an `H`-only, hence `Hhi`-only, quantity.  So:

* `{χ mod q : q ≤ Q}` is a FINITE family (`MulChar.finite`, and induction on `Q`);
* the max of its per-character constants is a single real `B(Q)` — `X`-free by construction,
  and `Q`-only, hence `Hhi`-only downstream;
* every consumer demand of the shape "floor beats `α·loglog X + β`" then clears at an
  `Hhi`-only threshold on `loglog X`, which the regime lever supplies for free.

**The general law behind it** (recorded at `docs/blueprints/flags.md`, "SIEGEL-REGIME:
RETIRES-D3 CONFIRMED"): regime enlargement absorbs any `X`-INDEPENDENT debit and can never
touch an `X`-dependent one.  `B(Q)` is `X`-independent; that is the whole argument.

**The ineffectivity is not dissolved, it is confined and priced.**  `B(Q)` is built from
`LFunction_band_lower`'s extreme-value minimum (`SiegelArm.lean` §2, "POISON 2"), so it has
no known growth rate in `Q`.  It does not need one: it enters only through a threshold that
the regime lever pushes past.  The ODD lane keeps its effective route (`L1_lower_odd`), so
the ineffective set is exactly the even-χ band corner.

## Contents

* `chi_Llower_band_single` (D3-1a) — the per-MODULUS max over the finite character group.
* `chi_Llower_band_uniform` (D3-1) — the per-`Q` max, by induction on `Q`.
* `chi_floor_band_uniform` (D3-2) — composed with `chi_floor_low_of_Llower`
  (`ChiFloorLow.lean` §F1, coefficient EXACTLY `1` on `loglog X`, no `k²` division, no
  `primeDivSum`): `loglog X − C ≤ 𝔻(λ·χ̄, n^{it}; X)²` for every `q ≤ Q`, every `χ`, every
  `|t| ≤ 1`.
* `chi_floor_band_uniform_twisted` (D3-2′) — the same in the MRT shape
  `𝔻(λ, χ·n^{it}; X)²` that the quality infimum `M(λ;X,W)` ranges over.
* `capfree_threshold` / `capfree_threshold_lt`, `band_gate_threshold`,
  `band_gate_threshold_cfb`, `quality_gate_threshold` (D3-3) — the three regime-side
  consumer arms, as standalone real inequalities.
* `siegelBandB` / `siegelBandB_spec` (D3-4) — the floor's constant as a NAMED function of
  `Q`, ready for the `Bfun : ℕ → ℝ` parameter slot of the regime-cut arm.
* `modulus_bound_mono` — the `W`-monotonicity the `Hhi`-only reading needs: the door's
  modulus cap `⌈(log H)^{12}⌉₊` is monotone in the window length, so a bound at `Hhi`
  covers every `H ≤ Hhi`.

## The three log-scales (the glyph trap)

Stones 1–3 speak `X` only (`loglog X` is the floor's scale).  Stone 4's monotonicity speaks
`H` only (window length; `log H` is the door's scale).  Nothing here mixes them: the bridge
`W = (log Hhi)^{12}` is drawn by the caller, which is exactly why `Q` here is an opaque `ℕ`.
-/

namespace Salt.MR

open Complex DirichletCharacter

/-! ## D3-1 — the uniform band `L`-lower bound

The only mathematical content is that the character group is finite; the rest is a running
max.  Note that `chi_Llower_band` carries NO per-χ `X₀`, no `q`-gate and no `G`-gate — the
compact band box `[1,2] × [−1,1]` already contains every bridge point `1 + 1/log X − it`
for `X ≥ e`, `|t| ≤ 1` — so `B_χ` is the ONLY per-character datum and one finite max over
it suffices. -/

/-- **D3-1a — the band bound, uniform over the characters of ONE modulus.**  For fixed
`q ≠ 0` there is a single `B` serving every `χ mod q`: the character group is finite
(`MulChar.finite`), so the per-character constants of `chi_Llower_band` have a max. -/
theorem chi_Llower_band_single (q : ℕ) [NeZero q] :
    ∃ B : ℝ, ∀ (χ : DirichletCharacter ℂ q) (X t : ℝ), Real.exp 1 ≤ X → |t| ≤ 1 →
      -B ≤ Real.log ‖DirichletCharacter.LFunction χ
            (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  haveI : Nonempty (DirichletCharacter ℂ q) := ⟨1⟩
  choose f hf using fun χ : DirichletCharacter ℂ q => chi_Llower_band χ
  obtain ⟨χ₀, hχ₀⟩ := Finite.exists_max f
  refine ⟨f χ₀, ?_⟩
  intro χ X t hX ht
  have hb := hf χ X t hX ht
  have hle : f χ ≤ f χ₀ := hχ₀ χ
  linarith

/-- **D3-1 — THE UNIFORM BAND `L`-LOWER BOUND.**  For every `Q` there is a single constant
`B` — independent of `q`, of `χ`, of `X` and of `t` — with

  `−B ≤ log‖L(1 + 1/log X − it, χ)‖`

for EVERY modulus `q ≤ Q`, EVERY `χ mod q`, every `X ≥ e` and every `|t| ≤ 1`.

Induction on `Q`: the base case is vacuous (`q ≤ 0` contradicts `NeZero q`), and each step
takes the max of the inductive constant with `chi_Llower_band_single (Q+1)`.  The dependent
type is handled by quantifying `q` and `χ` TOGETHER inside the existential — no sigma-type
supremum is formed, and `B` never sees a character's type. -/
theorem chi_Llower_band_uniform (Q : ℕ) :
    ∃ B : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        -B ≤ Real.log ‖DirichletCharacter.LFunction χ
              (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  induction Q with
  | zero =>
    refine ⟨0, ?_⟩
    intro q hq0 χ hq X t _ _
    haveI := hq0
    have : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    omega
  | succ Q ih =>
    obtain ⟨B₀, hB₀⟩ := ih
    haveI : NeZero (Q + 1) := ⟨Nat.succ_ne_zero Q⟩
    obtain ⟨B₁, hB₁⟩ := chi_Llower_band_single (Q + 1)
    refine ⟨max B₀ B₁, ?_⟩
    intro q hq0 χ hq X t hX ht
    haveI := hq0
    rcases Nat.lt_or_ge q (Q + 1) with hlt | hge
    · have hb := hB₀ q χ (Nat.lt_succ_iff.mp hlt) X t hX ht
      have : B₀ ≤ max B₀ B₁ := le_max_left _ _
      linarith
    · have hqe : q = Q + 1 := le_antisymm hq hge
      subst hqe
      have hb := hB₁ χ X t hX ht
      have : B₁ ≤ max B₀ B₁ := le_max_right _ _
      linarith

/-! ## D3-2 — the uniform band FLOOR

`chi_floor_low_of_Llower` (`ChiFloorLow.lean` §F1) is the clean interface: its `K` is the
`chi_dist_bridge` constant verbatim — `q`-free, `χ`-free, `X`-free, `t`-free — and the
`loglog X` coefficient is EXACTLY `1`.  Composing it with D3-1 costs one `linarith`.

This is deliberately NOT `chi_floor_all_complete`: that statement's `min` drags the
`orderOf χ` branch back in, dividing the floor by `k² = (2·ord χ)²`.  On the band
`|t| ≤ 1` the H2 branch alone is what the consumer wants, at coefficient `1`. -/

/-- **D3-2 — THE UNIFORM BOUNDED-BAND χ-QUALITY FLOOR.**  For every `Q` there is a single
constant `C` with

  `loglog X − C ≤ 𝔻(λ·χ̄, n^{it}; X)²`

for EVERY modulus `q ≤ Q`, EVERY `χ mod q`, every `X ≥ e` and every `|t| ≤ 1`.  The
coefficient on `loglog X` is `1`, and `C = B(Q) + K` with `B(Q)` from `chi_Llower_band_uniform`
and `K` from `chi_floor_low_of_Llower`.

This is the statement that retires the even-χ/Siegel corner on the regime road: `C` does not
depend on `X`, so any consumer demand of the form `α·loglog X + β ≤ floor` with `α < 1`
clears once `loglog X` exceeds a `Q`-only threshold — and the regime lever supplies exactly
such thresholds (see §D3-3).  The band `|t| ≤ 1` strictly contains the corpus's conditional
region `|t| < 1/(2·orderOf χ) ≤ 1/4`. -/
theorem chi_floor_band_uniform (Q : ℕ) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        Real.log (Real.log X) - C ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨K, hK⟩ := chi_floor_low_of_Llower
  obtain ⟨B, hB⟩ := chi_Llower_band_uniform Q
  refine ⟨B + K, ?_⟩
  intro q _ χ hq X t hX ht
  have h := hK q χ X t B hX (hB q χ hq X t hX ht)
  linarith

/-- **D3-2′ — the uniform band floor in the MRT shape.**  `𝔻(λ, χ·n^{it}; X)²` is the object
the quality infimum `M(λ; X, W) = inf_{q ≤ W, χ, |t| ≤ …} 𝔻(λ, χ n^{it}; X)²` ranges over;
one rewrite through `pretDistSq_lam_chi_twist` (`ChiFloor.lean` §the twist transfer) carries
D3-2 there.  The twist TRANSLATES nothing here — the frequency `t` is untouched — so the
shift-variable caveat does not bite at this statement. -/
theorem chi_floor_band_uniform_twisted (Q : ℕ) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        Real.log (Real.log X) - C
          ≤ pretDistSq lam (fun n => χ (n : ZMod q) * costwist t n) X := by
  obtain ⟨C, hC⟩ := chi_floor_band_uniform Q
  refine ⟨C, ?_⟩
  intro q _ χ hq X t hX ht
  rw [pretDistSq_lam_chi_twist χ t X]
  exact hC q χ hq X t hX ht

/-! ## D3-3 — the three regime-side thresholds

Each is a standalone real inequality with explicit hypotheses — no regime types, no `X`.
The caller reads `L := loglog X` and `B + C := siegelBandB Q`-grade debits; the regime lever
(`g R.Hhi R.ω ≤ R.x`) is what makes the hypothesis available, since every threshold below
depends on `Q` (hence `Hhi`) alone.  Genre match: `log_scale_threshold` /
`regime_hthr_of_scale` (`DoorFloor.lean`). -/

/-- **D3-3a — the cap-free gate.**  The uniform floor `L − B − C` beats the CapFreeFloor
demand `(1/32)·L + 25` once the scale clears `(32/31)·(B + C + 25)`.  (`31/32 = 1 − 1/32`
is the whole content: the floor's coefficient is `1` and the demand's is `1/32`.) -/
theorem capfree_threshold (B C L : ℝ) (hthr : (32 / 31) * (B + C + 25) ≤ L) :
    (1 / 32) * L + 25 ≤ L - B - C := by linarith

/-- **D3-3a (strict)** — the same with a strict scale hypothesis, for consumers that need a
strict inequality. -/
theorem capfree_threshold_lt (B C L : ℝ) (hthr : (32 / 31) * (B + C + 25) < L) :
    (1 / 32) * L + 25 < L - B - C := by linarith

/-- **D3-3b — the band gate, in general form.**  For any demand coefficient `M₀ < 1`, the
uniform floor `L − B − C` clears `M₀·L` once `L ≥ (B + C)/(1 − M₀)`.  The `M₀ < 1` guard is
the honest one: at `M₀ ≥ 1` no `X`-independent debit can ever be absorbed, which is the
regime law's negative half. -/
theorem band_gate_threshold {M₀ B C L : ℝ} (hM : M₀ < 1)
    (hthr : (B + C) / (1 - M₀) ≤ L) : M₀ * L ≤ L - B - C := by
  have h1 : (0 : ℝ) < 1 - M₀ := by linarith
  rw [div_le_iff₀ h1] at hthr
  nlinarith

/-- **D3-3b (concrete) — the CFB gate at `M₀ = (103/1500)·e`.**  The repriced cap-free-band
demand is `M₀ ≥ e·(1/15 + 1/500)·loglog X`, i.e. the coefficient `(103/1500)·e ≈ 0.18665`;
it clears at `loglog X ≥ (B + C)/(1 − (103/1500)e)`.  The side condition
`(103/1500)·e < 1` is `e < 1500/103 ≈ 14.56`, discharged from `Real.exp_one_lt_d9`. -/
theorem band_gate_threshold_cfb {B C L : ℝ}
    (hthr : (B + C) / (1 - 103 / 1500 * Real.exp 1) ≤ L) :
    103 / 1500 * Real.exp 1 * L ≤ L - B - C :=
  band_gate_threshold (by linarith [Real.exp_one_lt_d9]) hthr

/-- **D3-3c — the quality gate.**  M4-7 consumes only the EXCEEDANCE of
`M₀ := (5e/2)·log W`, never the floor's magnitude, so the arm it needs is the plain
rearrangement: the floor clears `(5e/2)·log W` once `L ≥ B + C + (5e/2)·log W`.  Stated with
`log W` as an opaque real — `W` is the door's modulus cap, an `Hhi`-only quantity, so the
threshold is `Hhi`-only as the regime lever requires. -/
theorem quality_gate_threshold (B C L W : ℝ)
    (hthr : B + C + 5 * Real.exp 1 / 2 * Real.log W ≤ L) :
    5 * Real.exp 1 / 2 * Real.log W ≤ L - B - C := by linarith

/-! ## D3-4 — the constant as a named function, and the `W`-monotonicity

The regime-cut arm takes a `Bfun : ℕ → ℝ` parameter slot (the `X0MR` idiom); `siegelBandB`
is the inhabitant, and `siegelBandB_spec` its defining property.  Choice is used exactly
once, here — the floor's constant is an opaque existential by construction (the EVT minimum
of `LFunction_band_lower`), so naming it costs `Classical.choose` and nothing more. -/

/-- **D3-4 — the uniform band floor's constant, as a function of the modulus range.**
`siegelBandB Q` is the `C` of `chi_floor_band_uniform Q`; it is `X`-free and `t`-free by
construction, and depends on `Q` alone. -/
noncomputable def siegelBandB (Q : ℕ) : ℝ := Classical.choose (chi_floor_band_uniform Q)

/-- **The defining property of `siegelBandB`.**  Exactly `chi_floor_band_uniform`'s body at
the chosen constant — the shape a regime-side consumer applies. -/
theorem siegelBandB_spec (Q : ℕ) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
        Real.log (Real.log X) - siegelBandB Q ≤ pretDistSq (lamChi χ) (costwist t) X :=
  Classical.choose_spec (chi_floor_band_uniform Q)

/-- **The `W`-monotonicity of the door's modulus cap.**  The door quantifies over
`q ≤ ⌈(log H)^{12}⌉₊`; since `log` and `x ↦ x^{12}` and `⌈·⌉₊` are all monotone on the
relevant range, a modulus admitted at window length `H` is admitted at every `Hhi ≥ H`.
This is what lets the caller instantiate `siegelBandB` at the SINGLE value
`Q := ⌈(log Hhi)^{12}⌉₊` and have it serve the whole window range `[Hlo, Hhi]`.

The hypothesis `1 ≤ H` is the honest floor: it is what makes `log H ≥ 0`, without which the
`12`-th power is not monotone. -/
theorem modulus_bound_mono {H Hhi q : ℕ} (hH : 1 ≤ H) (hle : H ≤ Hhi)
    (hq : q ≤ ⌈Real.log (H : ℝ) ^ (12 : ℕ)⌉₊) :
    q ≤ ⌈Real.log (Hhi : ℝ) ^ (12 : ℕ)⌉₊ := by
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlog0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg hH1
  have hlogle : Real.log (H : ℝ) ≤ Real.log (Hhi : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hle)
  have hpow : Real.log (H : ℝ) ^ (12 : ℕ) ≤ Real.log (Hhi : ℝ) ^ (12 : ℕ) :=
    pow_le_pow_left₀ hlog0 hlogle 12
  exact le_trans hq (Nat.ceil_mono hpow)

end Salt.MR
