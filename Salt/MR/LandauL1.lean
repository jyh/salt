/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SiegelArm
import Salt.SW.Hyperbola

/-!
# The `L₁` slot — the effective `L(1,χ)` lower bound at real `χ`, and its absorption

`Salt/MR/SiegelArm.lean` closes ROUTE A's real-character branch **modulo one slot**: its
`chi_floor_real_of_L1` (`SiegelArm.lean:725`) takes a number `L₁` with

  `0 < L₁`,  `L₁ ≤ 1`,  `L₁ ≤ (L(1,χ)).re`,  `32·diskConst q/L₁ ≤ log X`

and returns the growing floor with the debit `log 2 − log L₁ + 2log4 +
(1/4)log(16 q Z diskConst q/L₁)`.  `exists_L1_lower` inhabits the slot **per character**
(so the interface is not vacuous), but with no `q`-uniformity: that uniformity is exactly
Siegel's theorem, and in its ineffective form it is D-tier.

This module does three things.

1. **Names the byte-shaped target** (`L1LowerEffective`, `L1_lower_real_effective`) as a
   `Prop`-valued interface — no `sorry`, no axiom, no smuggled branch.
2. **Proves the absorption** (`door_L1_absorbed`, `door_L1_debit_absorbed`): at the door's
   pin `q ≤ (loglog X)⁵`, a grade `L₁ = c·q^{−A}` costs `A·log q + log(1/c) ≤
   5A·logloglog X + O(1)`, which is `o(loglog X)` — so ANY polynomial grade discharges the
   door, not merely `q^{−1/2}`.  Both statements carry their gate explicitly (law #253).
3. **Plugs the consumer** (`chi_floor_real_uniform`): the `q`-uniform ROUTE-A floor, proven
   from the interface alone.

## THE ROUTE VERDICT (the scope pass, recorded)

The mission offered two routes.  Both were probed against the corpus and mathlib; **neither
lands the `q^{−1/2}` grade in-session**, and the reasons are different in kind.

### (a) The class-number-formula route — BLOCKED IN MATHLIB (a missing factorization)

mathlib HAS the analytic class number formula:
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`
(`Mathlib/NumberTheory/NumberField/DedekindZeta.lean:78`), with the residue
`NumberField.dedekindZeta_residue K = (2^r₁·(2π)^r₂·regulator K·classNumber K)/
(torsionOrder K·√|discr K|)` and `dedekindZeta_residue_pos` (so `h ≥ 1` is available:
`NumberField.classNumber_pos`).

What is ABSENT is the only bridge that would connect it to `L(1,χ)`: the quadratic-field
factorization `ζ_K(s) = ζ(s)·L(s,χ_d)`, equivalently the ideal-counting identity
`#{I ⊴ 𝒪_K : N(I) = n} = Σ_{d ∣ n} χ_d(d)`.  A `grep` for `dedekindZeta` outside its
defining file returns NOTHING — the definition has no consumers at all.  Landing the
factorization means: the splitting law for quadratic fields, ideal norms, and a
convolution identity — a campaign, not a node.  The residue also carries `regulator`,
`torsionOrder` and `discr K` for `K = ℚ(√d)`, each needing its own explicit evaluation.

### (b) The Landau hyperbola route — BLOCKED MATHEMATICALLY (this is the finding)

The corpus is unusually well stocked here.  `Salt/SW/DHDetector.lean` already has the whole
lower half of Landau's argument for `a = 1 ∗ χ_ℝ`:

* `dhA` (`DHDetector.lean:142`), `dhA_nonneg` (`:206`), `dhA_square_ge_one` (`:219`),
* `dhA_mass_floor` / `dhA_mass_floor_real` (`:239` / `:264`): `Σ_{n≤N} a(n) ≥ √N − 1`,
* `dhA_log_average_square_floor` (`:292`), `dhA_hyperbola` (`:325`),
* `sum_divisors_eq_hyperbola_symm` / `dhA_hyperbola_symm` (`Salt/SW/Hyperbola.lean:55` /
  `:184`) — the symmetric `√N` split.

§4 below adds the missing weight: `dhA_sqrt_weighted_floor`, `Σ_{n≤N} a(n)/√n ≥
Σ_{m≤√N} 1/m`, the exact floor Landau's argument consumes.

**But the upper half cannot be made to bite.**  Write `S(x) = Σ_{n≤x} a(n)/√n` and split the
hyperbola at `d ≤ y`, using `Σ_{e≤u} e^{−1/2} = 2√u + c₀ + O(u^{−1/2})` and Abel summation
against `|Σ_{d≤u} χ(d)| ≤ min(u, q)`:

  `S(x) = 2√x·L(1,χ) + O(q√x/y) + O(√q) + O(y/√x)`,   optimally `y = √(qx)`:
  `S(x) = 2√x·L(1,χ) + O(√q)`.

Against the floor `S(x) ≥ Σ_{m≤√x} 1/m ≥ (1/2)log x` this gives
`L(1,χ) ≥ ((1/2)log x − C√q)/(2√x)`, maximized at `log x = 2C√q + 2`, i.e.

  **`L(1,χ) ≫ exp(−C√q)`  — and no better.**

The additive error is a fixed power of `q` while the floor grows only like `log x`; the
optimization is therefore forced to `x = exp(Θ(√q))`.  The unweighted variant is worse: floor
`√x`, main `x·L(1,χ)`, error `O(√(qx))` — the error DOMINATES the floor, so it yields
nothing at all.  Pólya–Vinogradov (`Salt/BV/PolyaVinogradov.lean:234`, available) improves
`√q ↝ √q log q` in the wrong place and does not change the shape.

This is the classical situation and not a defect of the port: **Dirichlet's hyperbola
argument proves NON-VANISHING `L(1,χ) ≠ 0`, with only an exponentially weak effective
constant.**  The `q^{−1/2}` grade is a class-number statement (`h ≥ 1`, plus `log ε ≥
log((1+√5)/2)` in the real-quadratic case), or — for ODD real primitive `χ` only — a
Gauss-sum/functional-equation statement.  So the flags entry's premise
("the remaining stone is the ordinary Landau hyperbola port [C, 400–800] effective at
`q^{−1/2}`") is OPTIMISTIC: the hyperbola port is real work that lands `exp(−C√q)`, not
`q^{−1/2}`.  **Recorded as a correction, not routed around.**

### (c) mathlib's `s = 1` API for real `χ` — what exists

`DirichletCharacter.LFunction` and `LFunction_eq_LSeries` (`Dirichlet.lean`), the
non-vanishing `LFunction_ne_zero_of_one_le_re` (`Nonvanishing.lean`), and the FUNCTIONAL
EQUATION `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`
(`DirichletContinuation.lean:284`) with `rootNumber` (`:272`).  Salt adds
`Salt.SW.LFunction_apply_one_pos` (`0 < L(1,χ)` in the `ComplexOrder` sense, real `χ`).
There is NO quantitative lower bound at `s = 1` anywhere, in either.

**The functional-equation lane is the cheapest genuine `q^{−A}`, and it is half a stone.**
For `χ` odd real primitive, `Λ(χ,1) = q^{−1/2}·W(χ)·Λ(χ,0)`, `Γ`-factors are `1/π` and `1`,
`|W(χ)| = 1`, and `L(0,χ) = −(1/q)Σ_{a<q} χ(a)·a ∈ (1/q)ℤ \ {0}`, giving the fully effective
`L(1,χ) ≥ π·q^{−3/2}` — a power, hence (by `door_L1_absorbed`) enough for the door.  For `χ`
EVEN the identity degenerates (`L(0,χ) = 0`) and the anchor becomes the regulator: no
elementary substitute.  Since the door quantifies over BOTH parities, this lane is not a
stone on its own.  It is recorded here as the cheapest live continuation.

## THE ZENO (exact)

`L1_lower_real_effective` is a NAMED `Prop`, not a theorem and not an axiom.  Everything
downstream of it in this file — the absorption and the consumer plug — is unconditional.
The residual is precisely: exhibit `c > 0` with `c·q^{−A} ≤ (L(1,χ)).re` for all real
nonprincipal `χ mod q`, at ANY fixed `A ≥ 0`.  Three continuations, priced:

* **FE/Gauss-sum, odd `χ` only** [C, ~400]: `A = 3/2`, effective, elementary; needs
  `|rootNumber χ| = 1` (from `|gaussSum| = √q` at primitive `χ`) plus `L(0,χ)` evaluated as
  `−(1/q)Σ aχ(a)` plus `Γ(1/2) = √π`.  Does not cover even `χ`.
* **Class number formula** [D-adjacent, campaign]: needs `ζ_K = ζ·L` for quadratic `K`.
  Covers both parities at `A = 1/2`.
* **Hyperbola** [C, ~400–800]: lands `exp(−C√q)`, NOT a power.  By
  `door_L1_absorbed_subexp` (§2) this still discharges a door pinned at
  `q ≤ (loglog X)^w` for any `w < 2` — so it is a genuine fallback IF the door's `W`-exponent
  is a free parameter rather than the pinned `5`.

## Honesty

Nothing here proves the `L₁` lower bound.  §2 and §3 are unconditional theorems ABOUT the
slot; §4 is one new unconditional Landau stone (`dhA_sqrt_weighted_floor`).  The slot itself
remains open, with the verdict above as its map.
-/

namespace Salt.MR

open Complex DirichletCharacter Salt.SW

/-! ## §1 — the interface (the byte-shaped target) -/

/-- **The effective `L(1,χ)` lower bound at grade `A`.**  `c·q^{−A} ≤ (L(1,χ)).re` for every
real (`χ² = 1`) nonprincipal character, uniformly in `q`.  This is the `L₁` slot of
`chi_floor_real_of_L1` in its `q`-uniform form.  `A = 1/2` is Landau's grade (the class
number bound); `A = 3/2` is the Gauss-sum grade for odd `χ`; by `door_L1_absorbed` the door
is indifferent to which `A ≥ 0` is supplied.

Primitivity is deliberately NOT required: the consumer `chi_floor_real_of_L1` quantifies over
all real nonprincipal `χ`, so a route that needs primitivity must first descend to the
inducing character (a separate, unlanded step). -/
def L1LowerEffective (c A : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
    c / (q : ℝ) ^ A ≤ (DirichletCharacter.LFunction χ 1).re

/-- **The target, in the mission's shape** — `∃ c > 0, c/√q ≤ (L(1,χ)).re` at every real
nonprincipal `χ`.  A `Prop`, NOT a theorem: this is the Zeno.  See the module docstring for
the route verdict and the three priced continuations. -/
def L1_lower_real_effective : Prop := ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ L1LowerEffective c (1 / 2)

/-- The mission-shaped target unfolds to the graded interface at `A = 1/2`, i.e.
`c / Real.sqrt q ≤ (L(1,χ)).re`.  (`√q = q^{1/2}` for `q ≥ 0`.) -/
lemma L1LowerEffective_half_iff (c : ℝ) :
    L1LowerEffective c (1 / 2) ↔
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
        c / Real.sqrt (q : ℝ) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hr : ∀ q : ℕ, Real.sqrt (q : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) := fun q => Real.sqrt_eq_rpow _
  constructor
  · intro h q _ χ hχ hsq
    rw [hr q]; exact h q χ hχ hsq
  · intro h q _ χ hχ hsq
    have := h q χ hχ hsq
    rwa [hr q] at this

/-! ## §2 — the absorption arithmetic (law #253: gates in-statement) -/

/-- `log Y ≤ 2√Y` for `Y > 0` — the sub-linearity used by every absorption below
(`log Y = 2 log √Y ≤ 2(√Y − 1)`). -/
lemma log_le_two_mul_sqrt {Y : ℝ} (hY : 0 < Y) : Real.log Y ≤ 2 * Real.sqrt Y := by
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have h1 : Real.log (Real.sqrt Y) ≤ Real.sqrt Y - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log Y = 2 * Real.log (Real.sqrt Y) := by
    rw [Real.log_sqrt hY.le]; ring
  linarith

/-- **The absorption kernel.**  A debit `K₁ + K₂·log q` at `q ≤ Y^w` is `≤ ε·Y` past an
EXPLICIT gate `G` on `Y` (law #253: `G` is produced, and the gate `G ≤ Y` is a hypothesis of
the conclusion, not an "eventually").  The mechanism: `log q ≤ w·log Y ≤ 2w·√Y = o(Y)`. -/
theorem logq_absorbed {K₁ K₂ w ε : ℝ} (hK₂ : 0 ≤ K₂) (hw : 0 ≤ w) (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (Y : ℝ) (q : ℕ), 1 ≤ q → G ≤ Y → (q : ℝ) ≤ Y ^ w →
      K₁ + K₂ * Real.log q ≤ ε * Y := by
  refine ⟨max 1 (max ((4 * K₂ * w / ε + 1) ^ 2) (2 * |K₁| / ε)), lt_of_lt_of_le one_pos
    (le_max_left _ _), ?_⟩
  intro Y q hq hGY hqY
  have hY1 : (1 : ℝ) ≤ Y := le_trans (le_max_left _ _) hGY
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos hY1
  have hs0 : (0 : ℝ) ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hssq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
  -- the two explicit gate consequences
  have hg1 : 4 * K₂ * w / ε + 1 ≤ Real.sqrt Y := by
    have hbase : (0 : ℝ) ≤ 4 * K₂ * w / ε + 1 := by positivity
    have hle : (4 * K₂ * w / ε + 1) ^ 2 ≤ Y :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hGY
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hbase] at this
  have hg2 : 2 * |K₁| / ε ≤ Y :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hGY
  -- `log q ≤ 2w√Y`
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : Real.log q ≤ w * Real.log Y := by
    have h := Real.log_le_log hq0 hqY
    rwa [Real.log_rpow hY0] at h
  have hlogY : Real.log Y ≤ 2 * Real.sqrt Y := log_le_two_mul_sqrt hY0
  have hKq : K₂ * Real.log q ≤ K₂ * w * (2 * Real.sqrt Y) := by
    have h1 : K₂ * Real.log q ≤ K₂ * (w * Real.log Y) :=
      mul_le_mul_of_nonneg_left hlogq hK₂
    have h2 : K₂ * (w * Real.log Y) ≤ K₂ * (w * (2 * Real.sqrt Y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogY hw) hK₂
    calc K₂ * Real.log q ≤ K₂ * (w * (2 * Real.sqrt Y)) := le_trans h1 h2
      _ = K₂ * w * (2 * Real.sqrt Y) := by ring
  -- the two halves of `ε·Y`
  have hK₁half : K₁ ≤ ε / 2 * Y := by
    have habs : K₁ ≤ |K₁| := le_abs_self K₁
    have : 2 * |K₁| ≤ ε * Y := by
      rw [div_le_iff₀ hε] at hg2; linarith
    linarith
  have hKqhalf : K₂ * w * (2 * Real.sqrt Y) ≤ ε / 2 * Y := by
    have hKw : 4 * K₂ * w ≤ ε * Real.sqrt Y := by
      have h := (div_le_iff₀ hε).mp (le_trans (le_add_of_nonneg_right zero_le_one) hg1)
      linarith
    nlinarith [hs0, hssq]
  linarith

/-- **The door's absorption, polynomial grade.**  At the door's pin `q ≤ (loglog X)⁵`, a slot
value `L₁ = c·q^{−A}` costs `log(1/L₁) = A·log q + log(1/c) ≤ 5A·logloglog X + log(1/c)`,
which is below `ε·loglog X` past an explicit gate `G` on `loglog X`.

So **any** polynomial grade discharges the door — `A = 1/2` (Landau/class number),
`A = 3/2` (Gauss sum, odd `χ`), anything.  This is the precise sense in which the ineffective
Siegel theorem stays off the critical path. -/
theorem door_L1_absorbed {c A ε : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (X : ℝ) (q : ℕ), 1 ≤ q →
      G ≤ Real.log (Real.log X) →
      (q : ℝ) ≤ Real.log (Real.log X) ^ (5 : ℝ) →
        Real.log (1 / (c / (q : ℝ) ^ A)) ≤ ε * Real.log (Real.log X) := by
  obtain ⟨G, hG0, hG⟩ :=
    logq_absorbed (K₁ := -Real.log c) (K₂ := A) (w := 5) (ε := ε) hA (by norm_num) hε
  refine ⟨G, hG0, ?_⟩
  intro X q hq hGY hqY
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpow : (0 : ℝ) < (q : ℝ) ^ A := Real.rpow_pos_of_pos hq0 A
  have hrw : Real.log (1 / (c / (q : ℝ) ^ A)) = -Real.log c + A * Real.log q := by
    rw [one_div, Real.log_inv, Real.log_div (ne_of_gt hc) (ne_of_gt hpow), Real.log_rpow hq0]
    ring
  rw [hrw]
  exact hG _ q hq hGY hqY

/-- **The door's absorption, sub-exponential grade** — the fallback the hyperbola route
actually supplies.  A slot value costing `K₁ + B·q^θ` is absorbed at a door pinned at
`q ≤ Y^w` **exactly when `θ·w < 1`**.

The hyperbola port lands `L₁ ≫ exp(−C√q)`, i.e. `θ = 1/2`: it discharges a door pinned at
`q ≤ (loglog X)^w` for every `w < 2`, and FAILS at the current `w = 5`.  This is the
actionable form of the route verdict — it prices exactly how much door-width the elementary
route can buy. -/
theorem door_L1_absorbed_subexp {K₁ B θ w ε : ℝ} (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hw : 0 ≤ w)
    (hθw : θ * w < 1) (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (Y : ℝ) (q : ℕ), 1 ≤ q → G ≤ Y → (q : ℝ) ≤ Y ^ w →
      K₁ + B * (q : ℝ) ^ θ ≤ ε * Y := by
  set δ : ℝ := 1 - θ * w with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  refine ⟨max 1 (max (((2 * B + 2 * |K₁| + 2) / ε + 1) ^ (1 / δ)) 1),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro Y q hq hGY hqY
  have hY1 : (1 : ℝ) ≤ Y := le_trans (le_max_left _ _) hGY
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos hY1
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- `q^θ ≤ Y^(w·θ)`
  have hqθ : (q : ℝ) ^ θ ≤ Y ^ (θ * w) := by
    have h1 : (q : ℝ) ^ θ ≤ (Y ^ w) ^ θ := Real.rpow_le_rpow hq0.le hqY hθ
    rwa [← Real.rpow_mul hY0.le, mul_comm w θ] at h1
  have hYwθ : (0 : ℝ) < Y ^ (θ * w) := Real.rpow_pos_of_pos hY0 _
  -- the explicit gate: `Y^δ ≥ (2B + 2|K₁| + 2)/ε + 1`
  have hbase : (0 : ℝ) < (2 * B + 2 * |K₁| + 2) / ε + 1 := by positivity
  have hgate : ((2 * B + 2 * |K₁| + 2) / ε + 1) ^ (1 / δ) ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hGY
  have hYδ : (2 * B + 2 * |K₁| + 2) / ε + 1 ≤ Y ^ δ := by
    have h1 : (((2 * B + 2 * |K₁| + 2) / ε + 1) ^ (1 / δ)) ^ δ ≤ Y ^ δ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hgate hδ0.le
    rwa [← Real.rpow_mul hbase.le, one_div, inv_mul_cancel₀ (ne_of_gt hδ0),
      Real.rpow_one] at h1
  -- `Y^(θw) · Y^δ = Y`
  have hsplit : Y ^ (θ * w) * Y ^ δ = Y := by
    rw [← Real.rpow_add hY0, hδdef]; ring_nf; rw [Real.rpow_one]
  -- assemble
  have hkey : (2 * B + 2 * |K₁| + 2) / ε ≤ Y ^ δ := by linarith
  have hD : 2 * B + 2 * |K₁| + 2 ≤ Y ^ δ * ε := (div_le_iff₀ hε).mp hkey
  have hmain : (2 * B + 2 * |K₁| + 2) * Y ^ (θ * w) ≤ ε * Y :=
    calc (2 * B + 2 * |K₁| + 2) * Y ^ (θ * w)
        ≤ Y ^ δ * ε * Y ^ (θ * w) := mul_le_mul_of_nonneg_right hD hYwθ.le
      _ = ε * (Y ^ (θ * w) * Y ^ δ) := by ring
      _ = ε * Y := by rw [hsplit]
  have hone : (1 : ℝ) ≤ Y ^ (θ * w) := Real.one_le_rpow hY1 (mul_nonneg hθ hw)
  have habs : K₁ ≤ |K₁| := le_abs_self K₁
  have habs0 : (0 : ℝ) ≤ |K₁| := abs_nonneg K₁
  have hBq : B * (q : ℝ) ^ θ ≤ B * Y ^ (θ * w) := mul_le_mul_of_nonneg_left hqθ hB
  nlinarith [hBq, habs, hmain, mul_nonneg habs0 (by linarith : (0 : ℝ) ≤ Y ^ (θ * w) - 1),
    mul_nonneg hB hYwθ.le, hYwθ.le]

/-- **The whole `chi_floor_real_of_L1` debit is `O(log q)` at a polynomial grade.**  Its
bracket is `log 2 − log L₁ + 2log4 + (1/4)log(16 q Z diskConst q/L₁)`; with
`L₁ = c·q^{−A}` and `diskConst q = (27/2)·√q·(1+log q)·q`, every piece is a constant plus a
multiple of `log q` (the `(1+log q)` factor contributes `log(1+log q) ≤ log q + 1` for
`q ≥ 1`).  Explicitly the bracket is `≤ K₁ + K₂·log q` with

  `K₁ = log 2 − log c + 2log4 + (1/4)(log 16 + log Z + log(27/2) + 1)`,
  `K₂ = A + (1/4)(1 + 1/2 + 1 + 1 + A) = A + (1/4)(7/2 + A)`.

Combined with `logq_absorbed` this is what `door_L1_debit_absorbed` states. -/
lemma debit_le_affine_log {c A Z : ℝ} (hc : 0 < c) (hZ : 1 ≤ Z)
    {q : ℕ} (hq : 1 ≤ q) :
    Real.log 2 - Real.log (c / (q : ℝ) ^ A) + 2 * Real.log 4
        + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / (c / (q : ℝ) ^ A))
      ≤ (Real.log 2 - Real.log c + 2 * Real.log 4
            + (1 / 4) * (Real.log 16 + Real.log Z + Real.log (27 / 2) + 1 - Real.log c))
          + (A + (1 / 4) * (7 / 2 + A)) * Real.log q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hpow : (0 : ℝ) < (q : ℝ) ^ A := Real.rpow_pos_of_pos hq0 A
  have hL1 : (0 : ℝ) < c / (q : ℝ) ^ A := div_pos hc hpow
  have hZ0 : (0 : ℝ) < Z := lt_of_lt_of_le one_pos hZ
  -- `diskConst q = 27/2 * √q * (1 + log q) * q`
  have hsq : (0 : ℝ) < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq0
  have hlog1 : (0 : ℝ) < 1 + Real.log q := by linarith
  have hD0 : (0 : ℝ) < diskConst q := by
    rw [diskConst]; positivity
  -- split the big log
  have hsplit : Real.log (16 * (q : ℝ) * Z * diskConst q / (c / (q : ℝ) ^ A))
      = Real.log 16 + Real.log q + Real.log Z + Real.log (diskConst q)
        - Real.log c + A * Real.log q := by
    rw [Real.log_div (by positivity) (ne_of_gt hL1),
      Real.log_div (ne_of_gt hc) (ne_of_gt hpow), Real.log_rpow hq0,
      Real.log_mul (by positivity) (ne_of_gt hD0),
      Real.log_mul (by positivity) (ne_of_gt hZ0),
      Real.log_mul (by norm_num) (ne_of_gt hq0)]
    ring
  have hDlog : Real.log (diskConst q)
      ≤ Real.log (27 / 2) + 1 + (5 / 2) * Real.log q := by
    rw [diskConst, Real.log_mul (by positivity) (ne_of_gt hq0),
      Real.log_mul (by positivity) (ne_of_gt hlog1),
      Real.log_mul (by norm_num) (ne_of_gt hsq), Real.log_sqrt hq0.le]
    have h1 : Real.log (1 + Real.log q) ≤ Real.log q := by
      have := Real.log_le_sub_one_of_pos hlog1
      linarith
    linarith
  have hL1log : Real.log (c / (q : ℝ) ^ A) = Real.log c - A * Real.log q := by
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hpow), Real.log_rpow hq0]
  rw [hsplit, hL1log]
  linarith

/-- **The door's absorption for the FULL `chi_floor_real_of_L1` debit.**  At the door's pin
`q ≤ (loglog X)⁵` and a polynomial slot `L₁ = c·q^{−A}`, the entire bracket the ROUTE-A floor
subtracts is `≤ ε·loglog X` past an explicit gate.  The floor's `H2` branch is therefore
`loglog X − (3/4)log(1+log X) − o(loglog X) − CH2`, i.e. the `(1/4)loglog X(1−o(1))` shape
the door consumes.  (Law #253: the gate `G ≤ loglog X` is in-statement.) -/
theorem door_L1_debit_absorbed {c A Z ε : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hZ : 1 ≤ Z)
    (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (X : ℝ) (q : ℕ), 1 ≤ q →
      G ≤ Real.log (Real.log X) →
      (q : ℝ) ≤ Real.log (Real.log X) ^ (5 : ℝ) →
        Real.log 2 - Real.log (c / (q : ℝ) ^ A) + 2 * Real.log 4
            + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / (c / (q : ℝ) ^ A))
          ≤ ε * Real.log (Real.log X) := by
  obtain ⟨G, hG0, hG⟩ := logq_absorbed
    (K₁ := Real.log 2 - Real.log c + 2 * Real.log 4
      + (1 / 4) * (Real.log 16 + Real.log Z + Real.log (27 / 2) + 1 - Real.log c))
    (K₂ := A + (1 / 4) * (7 / 2 + A)) (w := 5) (ε := ε) (by linarith) (by norm_num) hε
  refine ⟨G, hG0, ?_⟩
  intro X q hq hGY hqY
  exact le_trans (debit_le_affine_log hc hZ hq) (hG _ q hq hGY hqY)

/-! ## §3 — the consumer plug: the `q`-uniform ROUTE-A floor -/

/-- **`chi_floor_real_uniform` — the door's shape, from the `L₁` interface alone.**
`chi_floor_real_of_L1` (`SiegelArm.lean:725`) instantiated at the uniform slot value
`L₁ := c·q^{−A}`.  The three side conditions are discharged here: `0 < c·q^{−A}` and
`c·q^{−A} ≤ 1` (from `c ≤ 1`, `q ≥ 1`, `A ≥ 0`) and the interface supplies
`c·q^{−A} ≤ (L(1,χ)).re`.  What remains a hypothesis of the CONCLUSION is the `diskConst`
gate `32·diskConst q/L₁ ≤ log X`, exactly as in the consumer — the door's `q ≤ (loglog X)⁵`
regime is what discharges it downstream, and `door_L1_debit_absorbed` prices the debit. -/
theorem chi_floor_real_uniform {c A : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hA : 0 ≤ A)
    (hL : L1LowerEffective c A) :
    ∃ CH1 CH2 Z : ℝ, 1 ≤ Z ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X →
        32 * diskConst q / (c / (q : ℝ) ^ A) ≤ Real.log X →
          min (Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
                - (Real.log 2 - Real.log (c / (q : ℝ) ^ A) + 2 * Real.log 4
                  + (1 / 4) * Real.log
                      (16 * (q : ℝ) * Z * diskConst q / (c / (q : ℝ) ^ A))) - CH2)
              ((Real.log (Real.log X)
                  - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                  - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                  - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
            ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, CH2, Z, hZ1, hC⟩ := chi_floor_real_of_L1
  refine ⟨CH1, CH2, Z, hZ1, ?_⟩
  intro q _ χ hχ1 hsq X t hX hgate
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : q ≠ 0 := NeZero.ne q
    exact_mod_cast Nat.pos_of_ne_zero this
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ A := Real.one_le_rpow hq1 hA
  have hpow0 : (0 : ℝ) < (q : ℝ) ^ A := lt_of_lt_of_le one_pos hpow
  exact hC q χ hχ1 hsq X t (c / (q : ℝ) ^ A) hX (div_pos hc hpow0)
    (by rw [div_le_one hpow0]; linarith) (hL q χ hχ1 hsq) hgate

/-- **The door's shape, debit absorbed.**  `chi_floor_real_uniform` composed with
`door_L1_debit_absorbed`: at the door's pin `q ≤ (loglog X)⁵` and past an explicit gate `G` on
`loglog X`, the ROUTE-A floor's bounded-band branch reads

  `loglog X − (3/4)·log(1 + log X) − ε·loglog X − CH2`,

for ANY prescribed `ε > 0` — the whole `L₁`/`q`/`diskConst` debit has vanished into `ε`.
Since `(3/4)·log(1 + log X) = (3/4)·loglog X + O(1)`, this is the `(1/4 − ε)·loglog X` shape
the door consumes.  Everything here is unconditional GIVEN the interface `hL`; the interface
itself is the Zeno (module docstring). -/
theorem chi_floor_real_door {c A ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hA : 0 ≤ A) (hε : 0 < ε)
    (hL : L1LowerEffective c A) :
    ∃ CH1 CH2 G : ℝ, 0 < G ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → G ≤ Real.log (Real.log X) →
        (q : ℝ) ≤ Real.log (Real.log X) ^ (5 : ℝ) →
        32 * diskConst q / (c / (q : ℝ) ^ A) ≤ Real.log X →
          min (Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
                - ε * Real.log (Real.log X) - CH2)
              ((Real.log (Real.log X)
                  - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                  - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                  - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
            ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, CH2, Z, hZ1, hC⟩ := chi_floor_real_of_L1
  obtain ⟨G, hG0, hG⟩ := door_L1_debit_absorbed (c := c) (A := A) (Z := Z) hc hA hZ1 hε
  refine ⟨CH1, CH2, G, hG0, ?_⟩
  intro q _ χ hχ1 hsq X t hX hGate hqY hgate
  have hqN : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqN
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ A := Real.one_le_rpow hq1 hA
  have hpow0 : (0 : ℝ) < (q : ℝ) ^ A := lt_of_lt_of_le one_pos hpow
  have hfloor := hC q χ hχ1 hsq X t (c / (q : ℝ) ^ A) hX (div_pos hc hpow0)
    (by rw [div_le_one hpow0]; linarith) (hL q χ hχ1 hsq) hgate
  refine le_trans (min_le_min ?_ (le_refl _)) hfloor
  have := hG X q hqN hGate hqY
  linarith

/-! ## §4 — the Landau lower half, `√n`-weighted (new, unconditional) -/

/-- **The `√n`-weighted detector floor** — `Σ_{n≤N} a(n)/√n ≥ Σ_{m≤√N} 1/m`, for
`a = 1 ∗ χ_ℝ` at any real `χ`.

This is the exact floor Landau's hyperbola argument consumes, and the missing weight beside
`Salt.SW.dhA_mass_floor` (weight `1`) and `Salt.SW.dhA_log_average_square_floor` (weight
`1/n`).  Mechanism, unchanged from those: `a ≥ 0` everywhere (`dhA_nonneg`), `a(m²) ≥ 1`
(`dhA_square_ge_one`), and `1/√(m²) = 1/m` — so the full sum dominates its restriction to the
perfect squares, which is the harmonic sum up to `⌊√N⌋`.

Since `Σ_{m≤M} 1/m ≥ log M`, this floor grows like `(1/2)log N`, whereas the hyperbola's
upper half is `2√N·L(1,χ) + O(√q)`.  The optimization `log N ≍ √q` is forced, which is why
the route yields `L(1,χ) ≫ exp(−C√q)` and NOT a power of `q` — see the module docstring. -/
theorem dhA_sqrt_weighted_floor {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), 1 / (m : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n / Real.sqrt n := by
  have hsub : (Finset.Icc 1 (Nat.sqrt N)).image (fun m => m ^ 2) ⊆ Finset.Icc 1 N := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨m, ⟨hm1, hmM⟩, rfl⟩ := hx
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_pow _ _ (by omega), ?_⟩
    calc m ^ 2 ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left hmM 2
      _ ≤ N := Nat.sqrt_le' N
  have hroot : ∀ m : ℕ, Real.sqrt ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) := by
    intro m
    rw [show (((m ^ 2 : ℕ)) : ℝ) = (m : ℝ) ^ 2 by push_cast; ring]
    exact Real.sqrt_sq (Nat.cast_nonneg m)
  calc ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), 1 / (m : ℝ)
      = ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), 1 / Real.sqrt ((m ^ 2 : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hroot m]
    _ ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt N), dhA χ (m ^ 2) / Real.sqrt ((m ^ 2 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_Icc] at hm
        rw [hroot m]
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have h1 : (1 : ℝ) ≤ dhA χ (m ^ 2) := dhA_square_ge_one χ hsq hm.1
        gcongr
    _ = ∑ x ∈ (Finset.Icc 1 (Nat.sqrt N)).image (fun m => m ^ 2),
          dhA χ x / Real.sqrt (x : ℝ) := by
        rw [Finset.sum_image (fun a _ b _ hab => Nat.pow_left_injective (by norm_num) hab)]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, dhA χ n / Real.sqrt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => by
          rw [Finset.mem_Icc] at hn
          exact div_nonneg (dhA_nonneg χ hsq (by omega)) (Real.sqrt_nonneg _))

end Salt.MR
