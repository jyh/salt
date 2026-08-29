/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.RegimeParam
import Salt.MR.DoorFloor
import Salt.MR.NonPretClose

/-!
# S10b — the CHOICE-JOIN `g`-builder and the head-shaped regime existence

MR-gate freeze rung S10b (`docs/exploration/mr-freeze.md:20`,
`docs/exploration/door-road-0724.md:75`):

> S10b `chowlaRegime_exists_param_head` (`g : ℕ → ℕ → ℕ`): `∃ R, R.eps = eps ∧
> Hlo₀ ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x` — rerun `RegimeParam:380` Sec C; ALL
> `x`-constraints one-sided lower bounds (`Regime.lean:73,75,88,103,116,133,136+`
> — verified).  `g` = CHOICE-JOIN (FLAW-2 repair): `max`(numeral anchor
> `ω·⌈exp exp(max(8 log⁵H₊, 10²⁴))⌉`, choice-extracted `x₀^{S5}(log⁵H₊)`, C-arm
> `exp exp(4(M₀ + C(log⁵H₊)))`, `sup_{H ≤ H₊} X₀^{MR}`, ω-arm if staging demands).

The landed `chowlaRegime_exists_param` (`Salt/Entropy/Chowla/RegimeParam.lean:380`)
exposes only `R.eps = eps ∧ Hlo₀ ≤ R.Hlo`: the outer scale `x` it builds is
internal and single-exponential in `H₊`, which is what the freeze's FLAW-2 records
as insufficient for the A-arm (S5's `x₀(Q)` and `C(Q)` at `Q := log⁵H₊` are opaque
— Siegel-ineffective — so no numeral can dominate them).  This file supplies the
missing lever.

## The three pieces

1. **`regimeEnlargeX`** — the observation that makes everything cheap: EVERY
   `x`-constraint of `ChowlaRegime` is a one-sided LOWER bound on `x`
   (`hx`, `hωx`, `hheadroom`, `hheadroom'`, `hPHheadroom`, `hxbig`; the last two
   through a cast, `hheadroom`/`hheadroom'` through `Nat.div_le_div_right`).  So a
   regime may have its outer scale replaced by ANY larger natural number, with
   every other parameter — in particular `eps`, `Hlo`, `Hhi`, `ω` — untouched.

2. **`gJoin`** — the CHOICE-JOIN itself: the four-armed `max`, with the two opaque
   arms supplied by `Classical.choose` on `lambda_nonpret` (S5, landed
   unconditional at `Salt/MR/NonPretClose.lean:49`).  `s5x0`/`s5C` are the
   choice-extracted parameter FUNCTIONS `Q ↦ x₀(Q), C(Q)` — total on `ℝ` by
   choosing at `max 1 Q`, which is the only reason `gJoin` can be a `def` at all.
   Acyclicity (the freeze's own guard) is visible in the types: `s5x0`/`s5C`
   depend only on `Q`, and `Q = sieveW Hhi` depends only on `Hhi`, so `gJoin`
   depends only on `(Hhi, ω)` — never on `x`, never on `R`.

3. **`chowlaRegime_exists_param_head`** — the head form, at an ARBITRARY
   `g : ℕ → ℕ → ℕ` (strictly stronger than the freeze's demand, and no monotonicity
   hypothesis on `g` is needed: enlargement is unconditional).  The `∃`-binder
   order is byte-fit to the freeze: `R.eps = eps`, then `Hlo₀ ≤ R.Hlo`, then
   `g R.Hhi R.ω ≤ R.x`; `eps` and `Hlo₀` and `g` all sit BEFORE the `∃ R`, which is
   what keeps the S11 compose non-circular (cf. the same discipline in
   `log_chowla_two_budget_head`, where `ε` and `δ₀` precede `∀ extraFloor`).

## The S10a hand-off (B-3)

`regime_W_headroom_of_H0door` (`Salt/MR/DoorFloor.lean:214`) has two binders the
head can now discharge from its own floor slot: `H0door δ₀ ≤ R.Hhi` (demand it of
`Hlo₀`) and the `ε`-arm `log(1/(4·log2·ε²)) + 3 ≤ log H₊ / 2` (demand `epsFloor eps`
of `Hlo₀` as well — `epsFloor` is exactly the exponential that turns that arm into a
floor).  `regime_head_W_headroom` is the composite: one statement carrying the
regime, the door floor, the `g`-clearance, and Tao's W-constraint
`W = (log H₊)⁵ ≤ (log X_min)^{1/125}`.

## The S11 boundary (why this file stops where it does)

The `g`-clearance CANNOT be bolted onto `budget_head_grade_closed`
(`Salt/MR/DoorFloor.lean:244`) from outside: that theorem's regime is chosen inside
`log_chowla_two_budget_head`, and its payload `MRTUniformityXi R δ →
¬ logChowla2Fails R.eps R.x R.ω` mentions `R.x` on BOTH sides (through
`logMeasure R.x R.ω`).  Enlarging `x` after the fact therefore produces a DIFFERENT
statement rather than a consequence — `regimeEnlargeX` is sound for the regime's own
field constraints, all one-sided, but not for a door hypothesis already discharged
at the smaller scale.  Threading `g` in is exactly the freeze's S11 "head-builder
rerun of `SpineFinal.lean:749-829`", which must happen INSIDE `SpineFinal.lean`
(its `spine_False_core_xi` is private).  This file supplies the lever S11 calls at
that point; `regime_head_W_headroom` is the furthest the composition reaches from
outside.

## Posture

Nonconstructive by construction (`Classical.choose` on an ineffective existence,
`Nat.ceil` of a double exponential): the registered "asymptotic-only, no effective
`x`" posture of `mr-freeze.md:42`.  The `10²⁴` numeral is a SANITY ANCHOR only —
it cannot dominate the opaque arms and is never evaluated.
-/

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ### Section 1 — the `x`-enlargement of a regime

Every `x`-constraint of `ChowlaRegime` is one-sided (a lower bound on `x`), so the
outer scale can always be pushed up.  This is the whole mechanism of S10b. -/

/-- **The outer-scale enlargement.**  A regime with its outer scale `x` replaced by
any `x' ≥ x`.  Legal because the structure constrains `x` only from below:
`hx : 2 ≤ x`, `hωx : ω ≤ x`, `hheadroom : Hhi ≤ x / ω`, `hheadroom'`, `hPHheadroom`,
`hxbig` (`Regime.lean:73,75,88,103,116,133,136`).  Every other field — `eps`, `ω`,
`a`, `Hlo`, `Hhi`, `C0`, `J` — is carried VERBATIM, which is what lets the head form
inherit `R.eps = eps` and `Hlo₀ ≤ R.Hlo` from the landed builder unchanged. -/
def regimeEnlargeX (R : ChowlaRegime) {x' : ℕ} (h : R.x ≤ x') : ChowlaRegime where
  x := x'
  ω := R.ω
  a := R.a
  eps := R.eps
  Hlo := R.Hlo
  Hhi := R.Hhi
  C0 := R.C0
  J := R.J
  hx := le_trans R.hx h
  hω := R.hω
  hωx := le_trans R.hωx h
  ha := R.ha
  heps := R.heps
  heps1 := R.heps1
  hHlo := R.hHlo
  hHlohi := R.hHlohi
  hC0 := R.hC0
  hHlo_floor := R.hHlo_floor
  hheadroom := le_trans R.hheadroom (Nat.div_le_div_right h)
  hcoprime := R.hcoprime
  hfit := R.hfit
  hJcon := R.hJcon
  hPNTwindow := R.hPNTwindow
  hωbig := R.hωbig
  hheadroom' := le_trans R.hheadroom' (by exact_mod_cast Nat.div_le_div_right h)
  hPHheadroom := le_trans R.hPHheadroom (by exact_mod_cast h)
  hxbig := le_trans R.hxbig (by exact_mod_cast h)

@[simp] theorem regimeEnlargeX_x (R : ChowlaRegime) {x' : ℕ} (h : R.x ≤ x') :
    (regimeEnlargeX R h).x = x' := rfl

@[simp] theorem regimeEnlargeX_omega (R : ChowlaRegime) {x' : ℕ} (h : R.x ≤ x') :
    (regimeEnlargeX R h).ω = R.ω := rfl

@[simp] theorem regimeEnlargeX_eps (R : ChowlaRegime) {x' : ℕ} (h : R.x ≤ x') :
    (regimeEnlargeX R h).eps = R.eps := rfl

@[simp] theorem regimeEnlargeX_Hlo (R : ChowlaRegime) {x' : ℕ} (h : R.x ≤ x') :
    (regimeEnlargeX R h).Hlo = R.Hlo := rfl

@[simp] theorem regimeEnlargeX_Hhi (R : ChowlaRegime) {x' : ℕ} (h : R.x ≤ x') :
    (regimeEnlargeX R h).Hhi = R.Hhi := rfl

/-! ### Section 2 — the choice-extracted S5 parameter functions

`lambda_nonpret` (`Salt/MR/NonPretClose.lean:49`) is `∀ Q ≥ 1, ∃ x₀ C, …`.  The
`g`-builder needs `x₀` and `C` as FUNCTIONS of `Q`; `Classical.choose` at `max 1 Q`
supplies them totally on `ℝ`.  These are the "choice" of CHOICE-JOIN. -/

/-- **The S5 scale threshold `x₀(Q)`**, choice-extracted from `lambda_nonpret`.
Total on `ℝ` by evaluating the source at `max 1 Q` (its `1 ≤ Q` binder).  Opaque:
Siegel-ineffective, dominated by no numeral — the reason the `g`-builder exists. -/
noncomputable def s5x0 (Q : ℝ) : ℝ :=
  Classical.choose (lambda_nonpret (max 1 Q) (le_max_left 1 Q))

/-- **The S5 quality constant `C(Q)`**, choice-extracted from `lambda_nonpret`
alongside `s5x0`.  Feeds the `g`-builder's C-arm `exp exp(4·(M₀ + C(Q)))`. -/
noncomputable def s5C (Q : ℝ) : ℝ :=
  Classical.choose (Classical.choose_spec (lambda_nonpret (max 1 Q) (le_max_left 1 Q)))

/-- **The defining property of the extracted pair.**  Above `s5x0 Q`, at every
height `|t| ≤ max 1 Q · x`, the λ-pretentious distance clears
`(1/4)·loglog x − 4·logloglog(|t|+16) − s5C Q`. -/
theorem s5_spec (Q : ℝ) {x t : ℝ} (hx : s5x0 Q ≤ x) (ht : |t| ≤ max 1 Q * x) :
    (1 / 4) * Real.log (Real.log x)
        - 4 * Real.log (Real.log (Real.log (|t| + 16))) - s5C Q
      ≤ pretDistSq lam (costwist t) x :=
  Classical.choose_spec
    (Classical.choose_spec (lambda_nonpret (max 1 Q) (le_max_left 1 Q))) x t hx ht

/-- The same, at the unshifted height range `|t| ≤ Q·x` (the form the A-arm reads),
for `0 ≤ x`. -/
theorem s5_spec_of_le (Q : ℝ) {x t : ℝ} (hx0 : 0 ≤ x) (hx : s5x0 Q ≤ x)
    (ht : |t| ≤ Q * x) :
    (1 / 4) * Real.log (Real.log x)
        - 4 * Real.log (Real.log (Real.log (|t| + 16))) - s5C Q
      ≤ pretDistSq lam (costwist t) x :=
  s5_spec Q hx (le_trans ht (mul_le_mul_of_nonneg_right (le_max_right 1 Q) hx0))

/-! ### Section 3 — the CHOICE-JOIN `g`-builder -/

/-- **The A-arm height/quality parameter** `Q = (log H₊)⁵`.  [Docstring corrected
2026-07-26 per s9-design-0726.md ⟦AMENDMENT A⟧: historically named after — and
mis-documented as — "the door's sieve parameter W at S7's B₅ = 5".  It is NOT
the §4 port's `W` (now `(log H)^{12}`, B₅ = 12): MRT's quality `M(g;X,Q)` is an
inf over `q ≤ Q`, `|t| ≤ Q·x`, so any `Q ≥ 1` serves the A-arm, and `(log H₊)⁵`
overserves.  The two parameters are DECOUPLED; nothing here moves with B₅.]
This is the `Q` at which the A-arm reads S5, and the only channel by which
`gJoin` sees `Hhi`. -/
noncomputable def sieveW (H : ℕ) : ℝ := Real.log (H : ℝ) ^ (5 : ℕ)

/-- **The CHOICE-JOIN `g`-builder** (S10b, the FLAW-2 repair).  Four arms, joined
by `max`, all depending on `(Hhi, ω)` ONLY — never on `x`, so the head form's
`g R.Hhi R.ω ≤ R.x` demand is acyclic:

* the **numeral anchor** `ω · ⌈exp exp(max(8·W, 10²⁴))⌉₊` (a SANITY anchor: it
  carries the `ω`-arm as its factor, and pins the double-exponential shape, but
  cannot dominate the opaque arms);
* the **S5 scale arm** `⌈x₀^{S5}(W)⌉₊` — choice-extracted, ineffective;
* the **C-arm** `⌈exp exp(4·(M₀ + C^{S5}(W)))⌉₊`, where `M₀` is the MRT quality
  fixed by `δ₀` (a parameter here: it is chosen upstream, at S11);
* the **MR threshold arm** `sup_{H ≤ H₊} X₀^{MR}(H)`, at a threshold family
  `X0MR : ℕ → ℕ` supplied as a parameter — S9's `X₀^{MR}` is not yet in Lean, and
  parametrising it is what lets S10b land ahead of S9 (any later concrete family
  instantiates this slot).

Numerals are anchors only (`mr-freeze.md:20`); nothing here is ever evaluated. -/
noncomputable def gJoin (M0 : ℝ) (X0MR : ℕ → ℕ) (Hhi ω : ℕ) : ℕ :=
  max
    (max (ω * ⌈Real.exp (Real.exp (max (8 * sieveW Hhi) ((10 : ℝ) ^ (24 : ℕ))))⌉₊)
      ⌈s5x0 (sieveW Hhi)⌉₊)
    (max ⌈Real.exp (Real.exp (4 * (M0 + s5C (sieveW Hhi))))⌉₊
      ((Finset.range (Hhi + 1)).sup X0MR))

/-- Arm 1 — the numeral anchor (with its `ω` factor) is below the join. -/
theorem anchor_le_gJoin (M0 : ℝ) (X0MR : ℕ → ℕ) (Hhi ω : ℕ) :
    ω * ⌈Real.exp (Real.exp (max (8 * sieveW Hhi) ((10 : ℝ) ^ (24 : ℕ))))⌉₊
      ≤ gJoin M0 X0MR Hhi ω :=
  le_trans (le_max_left _ _) (le_max_left _ _)

/-- Arm 2 — the choice-extracted S5 scale threshold is below the join. -/
theorem s5x0_le_gJoin (M0 : ℝ) (X0MR : ℕ → ℕ) (Hhi ω : ℕ) :
    ⌈s5x0 (sieveW Hhi)⌉₊ ≤ gJoin M0 X0MR Hhi ω :=
  le_trans (le_max_right _ _) (le_max_left _ _)

/-- Arm 3 — the C-arm is below the join. -/
theorem carm_le_gJoin (M0 : ℝ) (X0MR : ℕ → ℕ) (Hhi ω : ℕ) :
    ⌈Real.exp (Real.exp (4 * (M0 + s5C (sieveW Hhi))))⌉₊ ≤ gJoin M0 X0MR Hhi ω :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- Arm 4 — every MR threshold in the regime's window range is below the join.
(The `sup` is taken over `H ≤ H₊`; `Finset.range (Hhi+1)` is that range.) -/
theorem mrThreshold_le_gJoin (M0 : ℝ) (X0MR : ℕ → ℕ) {Hhi ω H : ℕ} (hH : H ≤ Hhi) :
    X0MR H ≤ gJoin M0 X0MR Hhi ω := by
  have hmem : H ∈ Finset.range (Hhi + 1) := Finset.mem_range.mpr (by omega)
  exact le_trans (Finset.le_sup (f := X0MR) hmem)
    (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The ω-arm, read off the anchor: the join dominates the window width. -/
theorem omega_le_gJoin (M0 : ℝ) (X0MR : ℕ → ℕ) (Hhi ω : ℕ) : ω ≤ gJoin M0 X0MR Hhi ω := by
  refine le_trans ?_ (anchor_le_gJoin M0 X0MR Hhi ω)
  have h1 : 1 ≤ ⌈Real.exp (Real.exp (max (8 * sieveW Hhi) ((10 : ℝ) ^ (24 : ℕ))))⌉₊ :=
    Nat.ceil_pos.mpr (Real.exp_pos _)
  calc ω = ω * 1 := (mul_one ω).symm
    _ ≤ ω * ⌈Real.exp (Real.exp (max (8 * sieveW Hhi) ((10 : ℝ) ^ (24 : ℕ))))⌉₊ :=
        Nat.mul_le_mul (le_refl ω) h1

/-- The join is positive (it dominates a positive ceiling). -/
theorem gJoin_pos (M0 : ℝ) (X0MR : ℕ → ℕ) (Hhi ω : ℕ) : 0 < gJoin M0 X0MR Hhi ω :=
  lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) (carm_le_gJoin M0 X0MR Hhi ω)

/-! ### Section 4 — the head form (B-2) -/

/-- **S10b — `chowlaRegime_exists_param_head`.**  The `(ε, H₋)`-parametric regime
builder in HEAD shape: for ANY `ε ∈ (0, 1/2]`, ANY floor `Hlo₀`, and ANY
`g : ℕ → ℕ → ℕ`, a `ChowlaRegime` exists with `R.eps = ε`, `Hlo₀ ≤ R.Hlo`, AND the
outer-scale clearance `g R.Hhi R.ω ≤ R.x`.

Proof: run the landed `chowlaRegime_exists_param` (`RegimeParam.lean:380`), then
push the outer scale to `max R.x (g R.Hhi R.ω)` by `regimeEnlargeX` — legal because
every `x`-constraint is a one-sided lower bound, and harmless because `eps`, `Hlo`,
`Hhi`, `ω` are carried verbatim (so the `g`-argument does not move under the
enlargement).  No monotonicity or measurability hypothesis on `g` is required.

Binder discipline: `ε`, `Hlo₀`, `g` are ALL fixed before the `∃ R`, so a caller may
let `g` depend on anything fixed earlier (`ε`, `δ₀`, `M₀`, `K`) but never on `R`. -/
theorem chowlaRegime_exists_param_head (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x := by
  obtain ⟨R, hReps, hRHlo⟩ := chowlaRegime_exists_param eps heps heps1 Hlo₀
  exact ⟨regimeEnlargeX R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRHlo, le_max_right _ _⟩

/-- **The binder-position certificate.**  The head form recovers the landed
`chowlaRegime_exists_param` (`RegimeParam.lean:380`) verbatim at the trivial demand
`g := fun _ _ => 0` — so the head is a STRICT generalisation, drop-in at every
existing call site (in particular `SpineFinal.lean:759`, inside `∀ extraFloor`,
where `ε` is already fixed).  The compile is the check. -/
theorem chowlaRegime_exists_param_of_head (eps : ℚ) (heps : 0 < eps)
    (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo := by
  obtain ⟨R, hReps, hRHlo, -⟩ :=
    chowlaRegime_exists_param_head eps heps heps1 Hlo₀ (fun _ _ => 0)
  exact ⟨R, hReps, hRHlo⟩

/-- **The head at the CHOICE-JOIN builder** — S10b's payload in one statement:
a regime at the prescribed `ε` and floor whose outer scale clears every arm of
`gJoin` (in particular the two opaque, Siegel-ineffective ones). -/
theorem chowlaRegime_exists_param_head_gJoin (eps : ℚ) (heps : 0 < eps)
    (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) (M0 : ℝ) (X0MR : ℕ → ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧
      gJoin M0 X0MR R.Hhi R.ω ≤ R.x :=
  chowlaRegime_exists_param_head eps heps heps1 Hlo₀ (gJoin M0 X0MR)

/-! ### Section 5 — what the join buys at the regime (the A-arm discharge) -/

/-- The S5 scale threshold at the door's sieve parameter is cleared by the regime's
own outer scale, once the `gJoin` demand holds. -/
theorem s5x0_le_of_gJoin {M0 : ℝ} {X0MR : ℕ → ℕ} {R : ChowlaRegime}
    (hg : gJoin M0 X0MR R.Hhi R.ω ≤ R.x) : s5x0 (sieveW R.Hhi) ≤ (R.x : ℝ) := by
  refine le_trans (Nat.le_ceil _) ?_
  exact_mod_cast le_trans (s5x0_le_gJoin M0 X0MR R.Hhi R.ω) hg

/-- **The A-ARM DISCHARGE** (the freeze's new obligation).  At a regime whose outer
scale clears the CHOICE-JOIN, S5 fires AT THE REGIME'S OWN SCALE `x = R.x` and at
every height `|t| ≤ W·R.x`, `W = (log H₊)⁵` — which is exactly the range/quality
split the MRT major-arc reduction reads (`mr-freeze.md:20`, "S5 at `Q := log⁵H₊`,
quality `M₀(δ₀)` fixed"). -/
theorem s5_at_regime {M0 : ℝ} {X0MR : ℕ → ℕ} {R : ChowlaRegime}
    (hg : gJoin M0 X0MR R.Hhi R.ω ≤ R.x) {t : ℝ}
    (ht : |t| ≤ sieveW R.Hhi * (R.x : ℝ)) :
    (1 / 4) * Real.log (Real.log (R.x : ℝ))
        - 4 * Real.log (Real.log (Real.log (|t| + 16))) - s5C (sieveW R.Hhi)
      ≤ pretDistSq lam (costwist t) (R.x : ℝ) :=
  s5_spec_of_le (sieveW R.Hhi) (Nat.cast_nonneg _) (s5x0_le_of_gJoin hg) ht

/-- Every MR threshold in the regime's window range `H ≤ H₊` sits below the outer
scale — the `sup_{H ≤ H₊} X₀^{MR}` arm, read at the regime. -/
theorem mrThreshold_le_x {M0 : ℝ} {X0MR : ℕ → ℕ} {R : ChowlaRegime}
    (hg : gJoin M0 X0MR R.Hhi R.ω ≤ R.x) {H : ℕ} (hH : H ≤ R.Hhi) : X0MR H ≤ R.x :=
  le_trans (mrThreshold_le_gJoin M0 X0MR hH) hg

/-! ### Section 6 — the S10a threshold hand-off (B-3) -/

/-- **The `ε`-arm floor.**  `regime_W_headroom_of_H0door` (`DoorFloor.lean:214`)
carries the binder `log(1/(4·log2·ε²)) + 3 ≤ log H₊ / 2`, which is a demand on the
window endpoint stated in terms of `ε` alone.  `epsFloor ε` is the natural number
that turns it into a FLOOR demand — and floors are precisely what the head's `Hlo₀`
slot accepts. -/
noncomputable def epsFloor (eps : ℚ) : ℕ :=
  ⌈Real.exp (2 * (Real.log (1 / (4 * Real.log 2 * (eps : ℝ) ^ 2)) + 3))⌉₊

/-- **The `ε`-arm, discharged from the floor.**  Once the regime's upper endpoint
clears `epsFloor R.eps`, the `ε`-side binder of `regime_W_headroom_of_H0door` holds.
No positivity hypothesis on `ε` is needed: the argument is pure `exp`/`log`
monotonicity through the ceiling. -/
theorem heps_arm_of_epsFloor {R : ChowlaRegime} (h : epsFloor R.eps ≤ R.Hhi) :
    Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3 ≤ Real.log (R.Hhi : ℝ) / 2 := by
  set A : ℝ := 2 * (Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3) with hAdef
  have hcast : ((⌈Real.exp A⌉₊ : ℕ) : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h
  have hle : Real.exp A ≤ (R.Hhi : ℝ) := le_trans (Nat.le_ceil _) hcast
  have hlog := Real.log_le_log (Real.exp_pos A) hle
  rw [Real.log_exp] at hlog
  rw [hAdef] at hlog
  linarith

/-- **B-3 — the head, the door floor, the `g`-clearance, and Tao's W-constraint in
ONE statement.**  For any `ε ∈ (0, 1/2]`, any door threshold `δ₀ > 0` below
`6250000^{-5/4}` (at the spine's `δ₀ ≈ 2·10⁻⁴⁹`, ~40 orders of slack), any extra
floor demand, and any CHOICE-JOIN parameters, there is a regime that

* sits at `ε` and above BOTH the caller's floor and the MR door floor `H₀door δ₀`;
* clears the CHOICE-JOIN `gJoin` at its outer scale (so the A-arm fires,
  `s5_at_regime`); and
* satisfies Tao arXiv:1509.05422v2 Prop 2.4's W-constraint `(log H₊)⁶²⁵ ≤ log X_min`, i.e.
  `W = (log H₊)⁵ ≤ (log X_min)^{1/125}` (S10a, `regime_W_headroom_of_floor`).

The `ε`-arm of S10a is discharged internally by demanding `epsFloor ε` of the SAME
floor slot — the trick that makes the hand-off hypothesis-free. -/
theorem regime_head_W_headroom (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hsmall : δ₀ ≤ (6250000 : ℝ) ^ (-(5 / 4 : ℝ)))
    (extraFloor : ℕ) (M0 : ℝ) (X0MR : ℕ → ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ extraFloor ≤ R.Hlo ∧ H0door δ₀ ≤ R.Hlo ∧
      gJoin M0 X0MR R.Hhi R.ω ≤ R.x ∧
      (Real.log (R.Hhi : ℝ)) ^ (625 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) := by
  obtain ⟨R, hReps, hRHlo, hRg⟩ :=
    chowlaRegime_exists_param_head_gJoin eps heps heps1
      (max (max extraFloor (H0door δ₀)) (epsFloor eps)) M0 X0MR
  have hextra : extraFloor ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRHlo
  have hdoor : H0door δ₀ ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo
  have hepsF : epsFloor R.eps ≤ R.Hhi := by
    rw [hReps]
    exact le_trans (le_trans (le_max_right _ _) hRHlo) R.hHlohi
  refine ⟨R, hReps, hextra, hdoor, hRg, ?_⟩
  exact regime_W_headroom_of_H0door R hδ₀ hsmall (le_trans hdoor R.hHlohi)
    (heps_arm_of_epsFloor hepsF)

end Salt.MR
