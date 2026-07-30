/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.BallSup
import Salt.MR.SeamBallWeighted
import Salt.MR.CenterSupply
import Salt.MR.CofactorSupplier
import Salt.MR.LambdaChiRamare
import Salt.MR.PortClose

/-!
# `BallSupChi` — THE BALL-LEG SUP AT THE DOOR'S `pieceDatum` (council C5, `R-A4-2`)

The leg `REF-A4-MATH` §`R-A4-2` found unpriced (`docs/blueprints/flags.md`, 2026-07-30):
the χ-lift of `BallSup.ball_sup_of_center` at `CofactorSupplier.pieceDatum`, exiting in
`SeamBallWeighted.ball_leg_of_sup_weighted`'s `hSup` binder

  `∀ t, seamT0 X ≤ |t| → |t| ≤ T → |t − t₁| ≤ seamRad X →
     ∀ m ≤ N, ‖spolyA a t m‖ ≤ S·m/(1+|t−t₁|)`

— the RENORMALISED shape (the flat form was replaced as divergent), on the ANNULUS
`seamT0 X ≤ |t| ≤ T` (disjoint from the T₀-band), around the centre `t₁`.  Everything here
is ADDITIVE: no landed declaration is touched.

## THE `hCenter` ROUTE VERDICT — route (a) LIVES, route (b) is NOT AN INSTANTIATION

The brief's two candidate supplies for the centre bound
`‖∑_{n≤k} f(n)n^{−it₁}‖ ≤ S₀·k`, `⌊X⌋₊ ≤ k ≤ N`, at `f = pieceDatum χ 𝒥 = λ·χ̄·g_𝒥`:

* **(a) the landed χ-twisted rates — TAKEN.**  `pieceDatum χ {j} Pseq Qseq` is *exactly*
  `LambdaChiRamare.lamGr (Pseq j) (Qseq j) 0` twisted by `χ̄` (§1: `0^{ω} = 1_{ω = 0}` is the
  block-avoidance indicator `gJ` at a single block), and `pieceDatum χ ∅` is the bare `λχ̄`.
  So the twisted partial sums ARE `MlamGrChi χ (−t₁) (Pseq j) (Qseq j) 0 k` and
  `MlambdaChi χ (−t₁) k`, and this morning's `MlamGrChi_rate` / the landed `MlambdaChi_rate`
  price them at `C·k/(log k)^A` for EVERY saving `A > 0` — a power-log centre bound, with no
  pretentious distance and no `hRHS`-style grade socket anywhere.  `MmuChiRate` is landed
  (`PortClose.mmuChiRate_holds_gated`), so the supply below is UNCONDITIONAL modulo the two
  named window-mass hypotheses (the `M`/`ε` pages of O6, which are the consumer's).

  **THE HEIGHT GATE — the one real restriction, and it is IN THE STATEMENT.**  The two folds
  `MmuChiRate → MlambdaChi_rate → MlamGrChi_rate` each halve the height range:
  `|t| ≤ y` ↝ `|t| ≤ ⌊√y⌋` ↝ `|t| ≤ ⌊√⌊√y⌋⌋`.  At `y = k ≍ X` that is `|t₁| ≲ X^{1/4}`,
  and the seam's annulus reaches `Tann ≤ X` (`ThmA2.lean:669`), so **a centre above `X^{1/4}`
  is NOT covered by this route** — the honest statement of the death the brief anticipated.
  It does not bite at the door: `M4DoorClose.lean:61` pins the socket's ball centre at
  **`t₁ := 0`** (`Ps := 1`, `J := 2`, `Tann := X`, `Rrad := seamRad X`), and `|0| ≤ anything`
  — see `ball_leg_pieceDatum_at_zero`, where the gate is discharged outright.

* **(b) χ-lifting the `q = 1` supplier — NOT AVAILABLE AS AN INSTANTIATION.**  The `q = 1`
  `hCenter` is `CenterSupply.center_halasz_supply`, whose whole S1′ chain
  (`LambdaMass.prop21_uniform_at_scale_absC`, `HalaszSeam.prop21_desmooth_reduction`) is
  stated at the datum `seamCoeff (ellLin g) 1 t₀` — and `ellLin`
  (`HalaszLambda.lean:45`) is **supported on squarefree `n`**.  `pieceDatum` is COMPLETELY
  multiplicative and does not vanish off the squarefrees (`pieceDatum χ 𝒥 4 = χ̄(4)g_𝒥(4)`),
  so it is not `ellLin g` for any `g`: route (b) is not a substitution, it is a re-proof of
  the S1′ hat representation at a general completely-multiplicative datum, and it would
  still land the `hRHS` grade socket (`JointHead`'s HGRADE record) as a named residual.
  Route (a) needs neither.  **PRICE, if the tall-centre case is ever wanted:** the S1′
  re-proof at a completely multiplicative datum ≈ 1.5–3k ln, class C/D, plus `hRHS`.

## WHAT IS PROVED

* **§1** the twist bridge — `pieceDatum_twist_eq_lamGr` / `_eq_liouville` and the two sum
  identities.  No analysis: `eIu (−t₁) n` and `chiBarTwist χ (−t₁) n` are the same phase.
* **§2** `center_of_log_rate` — the `k`-uniformisation page: a rate `C·k/(log k)^A` valid on
  `[⌊X⌋₊, N]` is a single `S₀·k` at `S₀ = pieceCenterS0 C X A = C/(log(X/2))^A`.
* **§3** `center_halasz_pieceDatum_block` (𝒥 a SINGLE block) and
  `center_halasz_pieceDatum_empty` (𝒥 = ∅) — **THE `hCenter` SUPPLY**, in
  `ball_sup_of_center`'s literal binder shape, unconditional.
* **§4** `hMball_pieceDatum` — the A.4 ball dichotomy in Mertens-mass form at the twisted
  piece.  **χ-free and 𝒥-free**, as expected: `CenterSupply.pretDistSq_twist_slot` and
  `SmallStones.hMball_of_A4_cap` are both datum-generic, so the lift is a conversion of the
  A.4 cap and nothing else.  The cap itself stays a named hypothesis (it is the row's).
* **§5** `ball_sup_pieceDatum` (the `hSup` binder), `ball_leg_pieceDatum` (the `8S²` leg) and
  `ball_leg_pieceDatum_at_zero` (the door's `t₁ := 0` pin, height gate discharged).

`χ` is bound BEFORE `t₁` in every statement, so a consumer with per-χ centres instantiates
`t₁ := t₁ χ` for free (C2-SCOPE K-3: the pretentious minimizer is per-χ).

## WHAT IS OWED — the ONE piece this file does not cover

At the door `J = 2`, so the inclusion–exclusion has four pieces `𝒥 ∈ {∅, {1}, {2}, {1,2}}`.
§3 covers `∅`, `{1}`, `{2}`.  The **`𝒥 = {1,2}` union mask is NOT covered**: `MlamGrChi_rate`
is stated at a single block `[P,Q]` (`lamGr P Q r`), and the λ-side has no mask/union twin —
the Möbius side does (`MobiusChiRamareUnion.MmuGrChiU_rate`, `MmuGrChiMask_rate`).  The
missing statement is exactly the λ-twin of `MmuGrChiU_rate`: `MlamGrChiU_rate` at
`unionMask P₁ Q₁ P₂ Q₂`, which is `REF-A4-4`'s already-priced "union-mask twin for
`𝒥 = {1,2}`'s two disjoint blocks (~300–500 ln, B/C)".  It is D3's page, not this leg's, and
nothing here assumes it.

## THE FOUR LOG SCALES, KEPT APART

`log X` (the seam scale, where `S₀`, `ballTail` and `seamRad` are read), `log k`
(`k ∈ [⌊X⌋₊, N]`, where the rate fires — bridged to `log(X/2)` in §2 and nowhere else),
`log(X/2)` (the uniformised denominator and the conductor gate) and `log Q/log P` (the
WINDOW scale, confined to the named mass hypotheses `Mmass`/`ε`, exactly as in O6).
`Pseq`, `Qseq` appear in no other scale.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open Complex

/-! ## §1 — the twist bridge: the piece's twisted partial sum IS a landed summatory -/

/-- `eIu` in the phase spelling the χ-twisted summatories use: `n^{iu} = e^{(u·log n)i}`.
(`Renormalise.eIu` writes the same number as `exp(I·u·log n)`.) -/
lemma eIu_phase (u y : ℝ) :
    eIu u y = Complex.exp (((u * Real.log y : ℝ) : ℂ) * Complex.I) := by
  rw [eIu_eq]
  congr 1
  push_cast
  ring

/-- **The single-block mask is the `r = 0` damping.**  `g_{j}(n) = 0^{ω(n; P_j, Q_j)}`: both
sides are `1` when `n` has no prime factor in the block and `0` otherwise.  This is the
identity that lets `MlamGrChi_rate` — stated at `lamGr P Q r` — be read at `pieceDatum`. -/
lemma gJ_singleton_eq_zero_pow (j : ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    gJ ({j} : Finset ℕ) Pseq Qseq n = (0 : ℂ) ^ blockOmega (Pseq j) (Qseq j) n := by
  unfold gJ
  by_cases h : blockOmega (Pseq j) (Qseq j) n = 0
  · rw [if_pos (by simpa using h), h, pow_zero]
  · rw [if_neg (by simpa using h), zero_pow h]

/-- **The single-block piece, twisted, is `lamGr`'s summand.**  Termwise:
`λ(n)χ̄(n)g_{j}(n)·n^{−it₁} = (λ·g_0)(n)·χ̄(n)n^{−it₁}`. -/
lemma pieceDatum_twist_eq_lamGr {q : ℕ} (χ : DirichletCharacter ℂ q) (j : ℕ)
    (Pseq Qseq : ℕ → ℕ) (t₁ : ℝ) (n : ℕ) :
    pieceDatum χ ({j} : Finset ℕ) Pseq Qseq n * eIu (-t₁) n
      = ((lamGr (Pseq j) (Qseq j) 0 n : ℝ) : ℂ) * chiBarTwist χ (-t₁) n := by
  simp only [pieceDatum, liouChi, liouvilleC, chiBarTwist, lamGr_apply,
    gJ_singleton_eq_zero_pow, eIu_phase]
  push_cast
  ring

/-- **The empty piece, twisted, is `MlambdaChi`'s summand.** -/
lemma pieceDatum_twist_eq_liouville {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Pseq Qseq : ℕ → ℕ) (t₁ : ℝ) (n : ℕ) :
    pieceDatum χ (∅ : Finset ℕ) Pseq Qseq n * eIu (-t₁) n
      = ((ArithmeticFunction.liouville n : ℤ) : ℂ) * chiBarTwist χ (-t₁) n := by
  simp only [pieceDatum, liouChi, liouvilleC, chiBarTwist, gJ_empty, eIu_phase]
  push_cast
  ring

/-- **THE BRIDGE (single block).**  The centre-twisted partial sum of the `{j}`-piece IS the
landed damped summatory at `r = 0`. -/
theorem sum_pieceDatum_twist_eq_MlamGrChi {q : ℕ} (χ : DirichletCharacter ℂ q) (j : ℕ)
    (Pseq Qseq : ℕ → ℕ) (t₁ : ℝ) (k : ℕ) :
    (∑ n ∈ Finset.Icc 1 k, pieceDatum χ ({j} : Finset ℕ) Pseq Qseq n * eIu (-t₁) n)
      = MlamGrChi χ (-t₁) (Pseq j) (Qseq j) 0 k := by
  unfold MlamGrChi
  exact Finset.sum_congr rfl fun n _ => pieceDatum_twist_eq_lamGr χ j Pseq Qseq t₁ n

/-- **THE BRIDGE (empty mask).**  The centre-twisted partial sum of the `∅`-piece IS the
landed twisted Liouville summatory. -/
theorem sum_pieceDatum_twist_eq_MlambdaChi {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Pseq Qseq : ℕ → ℕ) (t₁ : ℝ) (k : ℕ) :
    (∑ n ∈ Finset.Icc 1 k, pieceDatum χ (∅ : Finset ℕ) Pseq Qseq n * eIu (-t₁) n)
      = MlambdaChi χ (-t₁) k := by
  unfold MlambdaChi
  exact Finset.sum_congr rfl fun n _ => pieceDatum_twist_eq_liouville χ Pseq Qseq t₁ n

/-! ## §2 — the uniformisation page: a `k`-rate is one `S₀` -/

/-- **The exit centre constant.**  `S₀ = C/(log(X/2))^A` — the rate's constant read at the
BOTTOM of the dyadic `k`-window `[⌊X⌋₊, N]`, which is where `(log k)^{−A}` is largest. -/
def pieceCenterS0 (C X A : ℝ) : ℝ := C / Real.log (X / 2) ^ A

lemma pieceCenterS0_pos {C X A : ℝ} (hC : 0 < C) (hX : (8 : ℝ) ≤ X) :
    0 < pieceCenterS0 C X A := by
  have hlog : (0 : ℝ) < Real.log (X / 2) := Real.log_pos (by linarith)
  unfold pieceCenterS0
  positivity

lemma pieceCenterS0_nonneg {C X A : ℝ} (hC : 0 < C) (hX : (8 : ℝ) ≤ X) :
    0 ≤ pieceCenterS0 C X A := (pieceCenterS0_pos hC hX).le

/-- The dyadic window's bottom: every `k ≥ ⌊X⌋₊` has `k ≥ X/2`. -/
lemma half_le_cast_of_floor_le {X : ℝ} {k : ℕ} (hX : (2 : ℝ) ≤ X) (hk : ⌊X⌋₊ ≤ k) :
    X / 2 ≤ (k : ℝ) := by
  have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
  linarith

/-- **THE UNIFORMISATION PAGE.**  A power-log rate `‖F k‖ ≤ C·k/(log k)^A` holding on the
dyadic window `[⌊X⌋₊, N]` is exactly `ball_sup_of_center`'s `hCenter` binder at the single
constant `S₀ = pieceCenterS0 C X A`.  (`log k ≥ log(X/2) > 0` on the window, and `x ↦ x^A` is
monotone for `A > 0`; this is the ONLY place `log k` is compared to `log X`.) -/
lemma center_of_log_rate (F : ℕ → ℂ) {X C A : ℝ} {N : ℕ}
    (hX : (8 : ℝ) ≤ X) (hA : 0 < A) (hC : 0 ≤ C)
    (hrate : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → ‖F k‖ ≤ C * (k : ℝ) / Real.log (k : ℝ) ^ A) :
    ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → ‖F k‖ ≤ pieceCenterS0 C X A * (k : ℝ) := by
  intro k hk1 hk2
  have hhalf : X / 2 ≤ (k : ℝ) := half_le_cast_of_floor_le (by linarith) hk1
  have hX2pos : (0 : ℝ) < X / 2 := by linarith
  have hlogpos : (0 : ℝ) < Real.log (X / 2) := Real.log_pos (by linarith)
  have hlogk : Real.log (X / 2) ≤ Real.log (k : ℝ) := Real.log_le_log hX2pos hhalf
  have hDpos : (0 : ℝ) < Real.log (X / 2) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hD : Real.log (X / 2) ^ A ≤ Real.log (k : ℝ) ^ A :=
    Real.rpow_le_rpow hlogpos.le hlogk hA.le
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc ‖F k‖ ≤ C * (k : ℝ) / Real.log (k : ℝ) ^ A := hrate k hk1 hk2
    _ ≤ C * (k : ℝ) / Real.log (X / 2) ^ A :=
        div_le_div_of_nonneg_left (by positivity) hDpos hD
    _ = pieceCenterS0 C X A * (k : ℝ) := by
        unfold pieceCenterS0
        rw [div_mul_eq_mul_div]

/-! ## §3 — THE `hCenter` SUPPLY at `pieceDatum` -/

/-- **THE `hCenter` SUPPLY, single block (`𝒥 = {j}`).**  For every saving `A > 0` there are
`C > 0` and a threshold `x₀` such that, at every seam scale `X` with `2x₀ ≤ X`, every modulus
`q ≤ (log(X/2))^{10}`, every `χ mod q`, every block index `j` and every centre `t₁` inside
the fold's height range,

  `∀ k ∈ [⌊X⌋₊, N],  ‖∑_{n≤k} pieceDatum χ {j} n · n^{−it₁}‖ ≤ pieceCenterS0 C X A · k`,

i.e. `BallSup.ball_sup_of_center`'s `hCenter` binder at `S₀ = C·(log(X/2))^{−A}`.

**UNCONDITIONAL** — the only landed slot consumed is `MmuChiRate`, discharged by
`PortClose.mmuChiRate_holds_gated`.  What is CARRIED, and why:

* `hq` — the conductor gate `q ≤ (log(X/2))^{10}`, the fold's own (two exponents were spent
  by the two hyperbola folds; `REF-A4-4`'s range fit has `(log H)^{12} ≤ (log y)^{10}` with
  two exponents to spare at `ℓ ≥ 1.09λ`);
* `ht₁` — **the height gate** `|t₁| ≤ ⌊√⌊√⌊X⌋₊⌋⌋`, the honest `X^{1/4}` ceiling of the
  two folds.  This is where a TALL centre would break the route (module docstring); at the
  door's pinned `t₁ = 0` it is free;
* `hmass`, `htail` — O6's two window-mass pages at the damping `r = 0`, in `MlamGrChi_rate`'s
  literal shape.  They read the WINDOW scale `log Q/log P` and nothing else, and they are the
  consumer's (`REF-A4-4`'s "mass page" and "Rankin-tail page"). -/
theorem center_halasz_pieceDatum_block (A : ℝ) (hA : 0 < A) {Mmass : ℝ} (hMmass : 0 ≤ Mmass) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ (X : ℝ) (N : ℕ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (j : ℕ) (t₁ : ℝ),
        (8 : ℝ) ≤ X → (x₀ : ℝ) ≤ X / 2 → (N : ℝ) ≤ 2 * X →
        (q : ℝ) ≤ Real.log (X / 2) ^ (10 : ℕ) →
        |t₁| ≤ (Nat.sqrt (Nat.sqrt ⌊X⌋₊) : ℝ) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Icc 1 (Nat.sqrt k),
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ Mmass) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Ioc (Nat.sqrt k) k,
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ 1 / Real.log (k : ℝ) ^ A) →
        ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ ({j} : Finset ℕ) Pseq Qseq n * eIu (-t₁) n‖
            ≤ pieceCenterS0 C X A * (k : ℝ) := by
  obtain ⟨C, x₀, hCpos, hrate⟩ :=
    MlamGrChi_rate mmuChiRate_holds_gated A hA hMmass
  refine ⟨C, x₀, hCpos, ?_⟩
  intro X N q hne χ Pseq Qseq j t₁ hX8 hx₀ _hN2 hq ht₁ hmass htail
  haveI : NeZero q := hne
  refine center_of_log_rate
    (fun k => ∑ n ∈ Finset.Icc 1 k, pieceDatum χ ({j} : Finset ℕ) Pseq Qseq n * eIu (-t₁) n)
    hX8 hA hCpos.le ?_
  intro k hk1 hk2
  -- the window bottom, and the two gates transported from `X/2` to `k`
  have hhalf : X / 2 ≤ (k : ℝ) := half_le_cast_of_floor_le (by linarith) hk1
  have hx₀k : x₀ ≤ k := Nat.cast_le.mp (le_trans hx₀ hhalf)
  have hX2pos : (0 : ℝ) < X / 2 := by linarith
  have hlogpos : (0 : ℝ) < Real.log (X / 2) := Real.log_pos (by linarith)
  have hlogk : Real.log (X / 2) ≤ Real.log (k : ℝ) := Real.log_le_log hX2pos hhalf
  have hqk : (q : ℝ) ≤ Real.log (k : ℝ) ^ (10 : ℕ) :=
    le_trans hq (pow_le_pow_left₀ hlogpos.le hlogk 10)
  have hht : |(-t₁)| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    rw [abs_neg]
    refine le_trans ht₁ ?_
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  rw [sum_pieceDatum_twist_eq_MlamGrChi]
  exact hrate k hx₀k q χ hqk (-t₁) hht (Pseq j) (Qseq j) 0 le_rfl zero_le_one
    (hmass k hk1 hk2) (htail k hk1 hk2)

/-- **THE `hCenter` SUPPLY, empty mask (`𝒥 = ∅`).**  The unmasked piece `pieceDatum χ ∅ = λχ̄`
is priced by the landed `MlambdaChi_rate` directly — ONE fold instead of two, so the gates are
strictly wider: `q ≤ (log(X/2))^{11}` and `|t₁| ≤ ⌊√⌊X⌋₊⌋`, and no window-mass page at all. -/
theorem center_halasz_pieceDatum_empty (A : ℝ) (hA : 0 < A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ (X : ℝ) (N : ℕ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (t₁ : ℝ),
        (8 : ℝ) ≤ X → (x₀ : ℝ) ≤ X / 2 → (N : ℝ) ≤ 2 * X →
        (q : ℝ) ≤ Real.log (X / 2) ^ (11 : ℕ) →
        |t₁| ≤ (Nat.sqrt ⌊X⌋₊ : ℝ) →
        ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ (∅ : Finset ℕ) Pseq Qseq n * eIu (-t₁) n‖
            ≤ pieceCenterS0 C X A * (k : ℝ) := by
  obtain ⟨C, x₀, hCpos, hrate⟩ := MlambdaChi_rate mmuChiRate_holds_gated A hA
  refine ⟨C, x₀, hCpos, ?_⟩
  intro X N q hne χ Pseq Qseq t₁ hX8 hx₀ _hN2 hq ht₁
  haveI : NeZero q := hne
  refine center_of_log_rate
    (fun k => ∑ n ∈ Finset.Icc 1 k, pieceDatum χ (∅ : Finset ℕ) Pseq Qseq n * eIu (-t₁) n)
    hX8 hA hCpos.le ?_
  intro k hk1 hk2
  have hhalf : X / 2 ≤ (k : ℝ) := half_le_cast_of_floor_le (by linarith) hk1
  have hx₀k : x₀ ≤ k := Nat.cast_le.mp (le_trans hx₀ hhalf)
  have hX2pos : (0 : ℝ) < X / 2 := by linarith
  have hlogpos : (0 : ℝ) < Real.log (X / 2) := Real.log_pos (by linarith)
  have hlogk : Real.log (X / 2) ≤ Real.log (k : ℝ) := Real.log_le_log hX2pos hhalf
  have hqk : (q : ℝ) ≤ Real.log (k : ℝ) ^ (11 : ℕ) :=
    le_trans hq (pow_le_pow_left₀ hlogpos.le hlogk 11)
  have hht : |(-t₁)| ≤ (Nat.sqrt k : ℝ) := by
    rw [abs_neg]
    refine le_trans ht₁ ?_
    exact_mod_cast Nat.sqrt_le_sqrt hk1
  rw [sum_pieceDatum_twist_eq_MlambdaChi]
  exact hrate k hx₀k q χ hqk (-t₁) hht

/-! ## §4 — the `hMball` lift: χ-free, 𝒥-free -/

/-- **THE `hMball` LIFT.**  `ball_sup_of_center`'s `hMball` binder at the twisted piece, from
the A.4 ball cap in the supplier's own M-shape (the distance at `costwist t₁`).

**It is χ-free and 𝒥-free**, as item 3 of the brief anticipated and as the bytes confirm: the
mass lives entirely on the pretentious distance, and both stones —
`CenterSupply.pretDistSq_twist_slot` (the slot conversion `𝔻²(f, p^{it₁}) = 𝔻²(f·n^{−it₁}, 1)`)
and `SmallStones.hMball_of_A4_cap` (the `(1/16)loglog X ↝ P(x)/8` conversion) — are generic
in the datum.  The cap `hcap` itself is NOT discharged here: it is the row's A.4 dichotomy
(the ball's live band), and forcing it would be exactly the iron-rule-1 violation. -/
theorem hMball_pieceDatum {q : ℕ} (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) {X t₁ : ℝ} (hX : ballMertensThreshold ≤ X)
    (hcap : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (pieceDatum χ 𝒥 Pseq Qseq) (costwist t₁) x
        ≤ (1 / 16) * Real.log (Real.log X)) :
    ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t₁) n) (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8 := by
  refine hMball_of_A4_cap hX ?_
  intro x h1 h2
  rw [← pretDistSq_twist_slot]
  exact hcap x h1 h2

/-! ## §5 — THE EXIT: `ball_leg_of_sup_weighted`'s binder at the door's piece -/

/-- `8 ≤ X` from the ball's Mertens threshold `e^{e^{40}}`. -/
lemma eight_le_of_ballMertensThreshold {X : ℝ} (hX : ballMertensThreshold ≤ X) :
    (8 : ℝ) ≤ X := by
  refine le_trans ?_ hX
  unfold ballMertensThreshold
  have h41 : (41 : ℝ) ≤ Real.exp 40 := exp_forty_ge
  have hmono : Real.exp 41 ≤ Real.exp (Real.exp 40) := Real.exp_le_exp.mpr h41
  have h8 : (8 : ℝ) ≤ Real.exp 41 := by
    have := Real.add_one_le_exp (41 : ℝ)
    linarith
  linarith

/-- **THE BINDER, ASSEMBLED.**  `ball_sup_of_center` at `f := pieceDatum χ 𝒥 Pseq Qseq`, with
the three structural datum facts DISCHARGED (`pieceDatum_one`, `pieceDatum_mul`,
`norm_pieceDatum_le_one` — free, as the refuter said) and `hMball` supplied from the A.4 cap
by §4.  What remains in front are the row's own binders (`hsupp`/`hDatum`, the dyadic bridge),
the A.4 cap, and the centre bound — which §3 supplies for `𝒥 = ∅` and `𝒥 = {j}`. -/
theorem ball_sup_of_pieceCenter {N : ℕ} {a : ℕ → ℂ} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ)
    {X T t₁ S₀ : ℝ} (hX : ballMertensThreshold ≤ X)
    (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hS₀ : 0 ≤ S₀)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hDatum : ∀ n : ℕ, X < (n : ℝ) → a n = pieceDatum χ 𝒥 Pseq Qseq n)
    (hCenter : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t₁) n‖ ≤ S₀ * (k : ℝ))
    (hcap : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (pieceDatum χ 𝒥 Pseq Qseq) (costwist t₁) x
        ≤ (1 / 16) * Real.log (Real.log X)) :
    ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ ballSupS X S₀ * m / (1 + |t - t₁|) := by
  have hX8 : (8 : ℝ) ≤ X := eight_le_of_ballMertensThreshold hX
  exact ball_sup_of_center (by linarith) hXN hN2 (pieceDatum_one χ 𝒥 Pseq Qseq)
    (fun p r _ => pieceDatum_mul χ 𝒥 Pseq Qseq p r)
    (norm_pieceDatum_le_one χ 𝒥 Pseq Qseq) hS₀ hsupp hDatum hCenter
    (hMball_pieceDatum χ 𝒥 Pseq Qseq hX hcap)

/-- **THE `hSup` DISCHARGE (single block).**  `SeamBallWeighted.ball_leg_of_sup_weighted`'s
binder, at the door's `{j}`-piece, per `χ`, with every gate in the statement:

  `∀ t, seamT0 X ≤ |t| → |t| ≤ T → |t−t₁| ≤ seamRad X →
     ∀ m ≤ N, ‖spolyA a t m‖ ≤ ballSupS X S₀ · m/(1+|t−t₁|)`,
  `S₀ = C·(log(X/2))^{−A}`  for EVERY saving `A > 0`.

`χ` precedes `t₁`, so a per-χ centre `t₁ χ` instantiates for free (C2-SCOPE K-3). -/
theorem ball_sup_pieceDatum (A : ℝ) (hA : 0 < A) {Mmass : ℝ} (hMmass : 0 ≤ Mmass) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ (X T : ℝ) (N : ℕ) (a : ℕ → ℂ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (j : ℕ) (t₁ : ℝ),
        ballMertensThreshold ≤ X → (x₀ : ℝ) ≤ X / 2 →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        (q : ℝ) ≤ Real.log (X / 2) ^ (10 : ℕ) →
        |t₁| ≤ (Nat.sqrt (Nat.sqrt ⌊X⌋₊) : ℝ) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Icc 1 (Nat.sqrt k),
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ Mmass) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Ioc (Nat.sqrt k) k,
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ 1 / Real.log (k : ℝ) ^ A) →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = pieceDatum χ ({j} : Finset ℕ) Pseq Qseq n) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (pieceDatum χ ({j} : Finset ℕ) Pseq Qseq) (costwist t₁) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N →
            ‖spolyA a t m‖ ≤ ballSupS X (pieceCenterS0 C X A) * m / (1 + |t - t₁|) := by
  obtain ⟨C, x₀, hCpos, hcenter⟩ := center_halasz_pieceDatum_block A hA hMmass
  refine ⟨C, x₀, hCpos, ?_⟩
  intro X T N a q hne χ Pseq Qseq j t₁ hXth hx₀ hXN hN2 hq ht₁ hmass htail hsupp hDatum hcap
  haveI : NeZero q := hne
  have hX8 : (8 : ℝ) ≤ X := eight_le_of_ballMertensThreshold hXth
  exact ball_sup_of_pieceCenter χ ({j} : Finset ℕ) Pseq Qseq hXth hXN hN2
    (pieceCenterS0_nonneg hCpos hX8) hsupp hDatum
    (hcenter X N q χ Pseq Qseq j t₁ hX8 hx₀ hN2 hq ht₁ hmass htail) hcap

/-- **THE CROWN — the weighted ball leg at the door's `{j}`-piece.**
`ball_sup_pieceDatum` fed into `SeamBallWeighted.ball_leg_of_sup_weighted`:

  `∫_{Ann(X,T) ∩ ball(t₁)} ‖spoly N a t‖² ≤ 8·(ballSupS X S₀)²`,

with NO `r`-factor (the divergence the weighted leg was built to kill) and
`S₀ = C·(log(X/2))^{−A}` at every saving `A > 0`. -/
theorem ball_leg_pieceDatum (A : ℝ) (hA : 0 < A) {Mmass : ℝ} (hMmass : 0 ≤ Mmass) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ (X T : ℝ) (N : ℕ) (a : ℕ → ℂ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (j : ℕ) (t₁ : ℝ),
        ballMertensThreshold ≤ X → (x₀ : ℝ) ≤ X / 2 → 0 ≤ T →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        (q : ℝ) ≤ Real.log (X / 2) ^ (10 : ℕ) →
        |t₁| ≤ (Nat.sqrt (Nat.sqrt ⌊X⌋₊) : ℝ) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Icc 1 (Nat.sqrt k),
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ Mmass) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Ioc (Nat.sqrt k) k,
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ 1 / Real.log (k : ℝ) ^ A) →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = pieceDatum χ ({j} : Finset ℕ) Pseq Qseq n) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (pieceDatum χ ({j} : Finset ℕ) Pseq Qseq) (costwist t₁) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2)
          ≤ 8 * ballSupS X (pieceCenterS0 C X A) ^ 2 := by
  obtain ⟨C, x₀, hCpos, hsup⟩ := ball_sup_pieceDatum A hA hMmass
  refine ⟨C, x₀, hCpos, ?_⟩
  intro X T N a q hne χ Pseq Qseq j t₁ hXth hx₀ hT hXN hN2 hq ht₁ hmass htail hsupp hDatum hcap
  haveI : NeZero q := hne
  have hX8 : (8 : ℝ) ≤ X := eight_le_of_ballMertensThreshold hXth
  refine ball_leg_of_sup_weighted (by linarith) hXN hN2 hT
    (Real.log_nonneg (by linarith)) hsupp ?_
  exact hsup X T N a q χ Pseq Qseq j t₁ hXth hx₀ hXN hN2 hq ht₁ hmass htail hsupp hDatum hcap

/-- **THE DOOR INSTANCE — the height gate discharged at the pinned centre.**
`M4DoorClose.lean:61` pins the socket's ball data at `Ps := 1`, `J := 2`, `Tann := X`,
**`t₁ := 0`**, `Rrad := seamRad X`.  At `t₁ = 0` the route's one real restriction — the
`X^{1/4}` height ceiling of the two hyperbola folds — is discharged outright, so the ball leg
at the door's `{j}`-piece carries NO centre-height hypothesis at all. -/
theorem ball_leg_pieceDatum_at_zero (A : ℝ) (hA : 0 < A) {Mmass : ℝ} (hMmass : 0 ≤ Mmass) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧
      ∀ (X T : ℝ) (N : ℕ) (a : ℕ → ℂ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (Pseq Qseq : ℕ → ℕ) (j : ℕ),
        ballMertensThreshold ≤ X → (x₀ : ℝ) ≤ X / 2 → 0 ≤ T →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        (q : ℝ) ≤ Real.log (X / 2) ^ (10 : ℕ) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Icc 1 (Nat.sqrt k),
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ Mmass) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (∑ b ∈ Finset.Ioc (Nat.sqrt k) k,
              ramTailWeight (Pseq j) (Qseq j) 0 b / (b : ℝ)) ≤ 1 / Real.log (k : ℝ) ^ A) →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = pieceDatum χ ({j} : Finset ℕ) Pseq Qseq n) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (pieceDatum χ ({j} : Finset ℕ) Pseq Qseq) (costwist 0) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        (∫ t in seamAnn X T ∩ seamBall X 0, ‖spoly N a t‖ ^ 2)
          ≤ 8 * ballSupS X (pieceCenterS0 C X A) ^ 2 := by
  obtain ⟨C, x₀, hCpos, hleg⟩ := ball_leg_pieceDatum A hA hMmass
  refine ⟨C, x₀, hCpos, ?_⟩
  intro X T N a q hne χ Pseq Qseq j hXth hx₀ hT hXN hN2 hq hmass htail hsupp hDatum hcap
  haveI : NeZero q := hne
  have ht₁ : |(0 : ℝ)| ≤ (Nat.sqrt (Nat.sqrt ⌊X⌋₊) : ℝ) := by
    rw [abs_zero]
    positivity
  exact hleg X T N a q χ Pseq Qseq j 0 hXth hx₀ hT hXN hN2 hq ht₁ hmass htail hsupp hDatum hcap

end Salt.MR

end
