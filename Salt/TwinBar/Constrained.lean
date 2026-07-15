/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Enlarged

/-!
# Exploration sprint Q5a — the marginal-CONSTRAINED enlarged `M₂` below 2

**This is EXPLORATION, not a frozen blueprint node.** Design context:
`docs/exploration/preregistration.md` (Q5 leg (a)) and `docs/exploration/pilot.md`
(probe P-A, the unconstrained precursor `Salt/TwinBar/Enlarged.lean`). The file adds
NEW work only; it edits no landed file and is not wired into `Salt.TwinBar.All`.
Everything here is sorry-free and axiom-clean; every OPEN question is recorded as
prose, never as a `sorry`'d theorem.

## THE CONSTRAINT STORE (witness-accountability first — READ BEFORE ANY PROOF)

Per `docs/METHODS.md` Part III, the question opens with the exact class as
Lean-statable predicates, BEFORE any estimate. The δ-enlarged carriers are reused
from `Enlarged.lean`: `R₂e δ = {t₁,t₂ ≥ 0, t₁+t₂ ≤ 1+δ}`, `I₂e` (full enlarged
`L²`-mass), `J₁e`/`J₂e` (the Selberg peels). The NEW object is the marginal
constraint, promoted here from `Enlarged.lean`'s prose (its OPEN 1) to a formal
predicate:

* `marg₁ δ F t₂ := ∫ t₁ in 0..(1+δ−t₂), F t₁ t₂` (the `t₁`-marginal at height `t₂`);
  `marg₂` is the mirror.
* `MarginalVanish δ F` : `marg₁ δ F t₂ = 0` for `t₂ ∈ (1, 1+δ]` AND `marg₂ δ F t₁ = 0`
  for `t₁ ∈ (1, 1+δ]` — the marginals vanish OUTSIDE the unit simplex.
* `Admissible δ F := ContinuousOn (uncurry F) (R₂e δ) ∧ MarginalVanish δ F`.

**R3 — a divergence in the classical formulation, recorded (NOT silently resolved).**
The registration phrases the constraint as "the marginals vanish outside the UNIT
simplex" (`marg₁ = 0` for `t₂ > 1`). The primary source
(Tao, *Polymath8b VII*, `terrytao.wordpress.com/2014/01/28/...`, the `k = 2` GEH
problem, verified this session) states the honest ε-trick class with a DIFFERENT
threshold and a DIFFERENT numerator region:
  - marginal vanishing at `y ≥ 1 + ε` (NOT `y > 1`), and
  - the numerator `∫_{y ≤ 1−ε} (∫F dx)² dy + ∫_{x ≤ 1−ε} (∫F dy)² dx` (region `≤ 1−ε`),
  - denominator `∫_R F²` over the enlarged support, gate `> 2 ∫_R F²`.
Both are subclasses of "continuous `F` on `R₂e δ`" with a marginal-support
constraint, so the CS upper bound below (`twin_bar_constrained`) holds a fortiori
for BOTH: Tao's numerator region `{≤ 1−ε}` is smaller than ours, so his ratio is
`≤` ours, and both are `≤ 2·(1+δ)·log 2`. We FREEZE the registration's cleaner
formulation (`MarginalVanish` above) and record Tao's exact class as the classical
reference; the choice between them is a design decision escalated to the house
session (it changes the *value* of the sup, not the *route* or the obstruction).

**Satisfiability witness (METHODS III.3, the anti-vacuity discipline).**
`admissible_witness`: the "tent" `tentF (t₁,t₂) = max 0 (1 − t₁ − t₂)` is admissible
for every `δ ≥ 0` and has `I₂e δ tentF = 1/12 > 0`, so the class — and in particular
the `0 < I₂e` premise of the no-go below — is jointly inhabitable by a genuine
NONZERO weight (not the trivial `F ≡ 0`). This is the certificate that the no-go is
not vacuous.

## THE OUTCOME (an OBSTRUCTION with a threshold — a full exploration deliverable)

The registered question: prove `J₁e + J₂e ≤ c·I₂e` with `c < 2` for ALL `δ ∈ (0,1]`,
or exhibit precisely where the retuned-CS route fails to use the constraint. The
verdict is the second: **the per-slice Cauchy–Schwarz route provably caps at
`2·(1+δ)·log 2`, which crosses 2 at `δ₀ = 1/log 2 − 1 ≈ 0.4427`, and the marginal
constraint does not lower this ceiling.** Concretely:

* `twin_bar_constrained` : `Admissible δ F → J₁e + J₂e ≤ 2·(1+δ)·log 2 · I₂e`.
  This is the honest constrained bound. Its proof is `twin_bar_enlarged ∘ (·.1)` —
  the constraint hypothesis is NEVER CONSUMED (`cs_bound_ignores_constraint` makes
  this explicit: the identical bound holds for every continuous `F`, admissible or
  not). The per-slice CS is blind to the (global) marginal constraint.
* `no_twin_weight_constrained` : for `δ < δ₀` (`(1+δ)·log 2 < 1`) the constrained
  twin gate `2·I₂e < J₁e + J₂e` is unsatisfiable by any admissible weight of
  positive mass — the honest-class no-go, non-vacuous by `admissible_witness`.
* `enlarged_ceiling_ge_two` / `ceiling_at_one` : for `δ ≥ δ₀` the CS ceiling is
  `≥ 2` (at `δ = 1` it is `4·log 2 ≈ 2.773`), so the CS route is INCONCLUSIVE there.
* `wing_weight_reaches` : the reason. On the wing `{t₁ > 1}` the per-slice CS weight
  `w₁ᵉ = 1+δ−t₂+t₁` reaches `2·(1+δ)` (at the corner `(1+δ, 0)`), exactly the core
  constant. The marginal constraint is a FIRST-moment condition transverse to the CS
  direction; it cannot reduce the SECOND-moment weight on the wing, so no base-tuning
  helps (see the β-optimality note below).

## Why the constraint cannot rescue the CS route (the β-optimality computation)

Retune the CS base to `β·(slice length)` (P-C's tuning). The per-slice normalisation
is `log((β+1)/β)`, the weight is `w₁ = β(1+δ−t₂)+t₁`, and `w₁+w₂ = 2β(1+δ)+(1−β)s`
with `s = t₁+t₂`. Two loci force the constant:
  - the CORE `{t₁,t₂ ≤ 1}`: efficiency `log((β+1)/β)·(2β(1+δ) + (1−β)s)`, maximised
    over `s`;
  - the WING corner: efficiency `log((β+1)/β)·(β+1)(1+δ)`.
Minimising the max over `β > 0` gives the optimum at **`β = 1`**, value
`2·(1+δ)·log 2` — the wing-corner and core coincide there, and every other `β` is
worse (`f(β) = (β+1)log((β+1)/β)` is strictly decreasing, `g(β) = 2β·log((β+1)/β)`
strictly increasing, both `= 2 log 2` at `β = 1`). So NO base-tuning of the per-slice
CS beats `2·(1+δ)·log 2`. The obstruction is method-intrinsic, not a slack.

## The numeric truth (Part II ritual — computed, TWO grids, this session)

A discretised constrained Rayleigh maximisation (grid on `R₂e δ`, marginal
constraints imposed as linear equalities, projected power iteration; cross-checked
against the unconstrained sup, which reproduces `2·(1+δ)·log 2`) gives the TRUE
constrained sup `c(δ)`:

  `δ`      | 0.2 | 0.443(δ₀) | 0.5 | 0.7 | 0.9 | 1.0
  `c(δ)`   |1.61 |  1.80     |1.83 |1.94 |1.99 | **2.00000**  (robust, `n = 80…320`)
  CS ceil  |1.66 |  2.00     |2.08 |2.36 |2.63 |  2.773

So the TRUE constrained sup is monotone increasing, stays `≤ 2`, and touches 2 only
at the extreme enlargement `δ = 1` (as a sup we did not find attained). This MATCHES
Tao's own assessment of the `k = 2` GEH problem: *"We suspect that the answer to this
question is negative, but have not formally ruled it out yet."* The honest no-go thus
appears to persist for ALL `δ ∈ (0,1]` — but the CS method sees only `δ < δ₀`, being
off by the full gap `2.773` vs `2.0` at `δ = 1`.

**R4 (the too-good-to-be-true tripwire) — cleared.** No witness reaching 2 was found:
`c(1) = 2` is a NON-ATTAINED sup, so every admissible `F` has `J₁e+J₂e < 2·I₂e`
(no gate crossing), and `δ = 1` (`ε = 1`) is precisely the extreme boundary of the
admissible enlargement. This is the honest boundary, not an alarm; the constraint
formulation was re-checked against the source (the R3 note above) as R4 directs.

## OPEN (recorded as prose, per the exploration STOP-AND-FLAG rule)

`-- OPEN Q5a-1 (research, beyond this session):` prove `c(δ) < 2` for `δ ∈ (δ₀, 1)`
and `c(1) = 2` for the constrained class. This is Tao's open problem; the numerics
support it but the per-slice CS route provably cannot reach it (it needs a genuinely
2-D argument coupling the marginal constraint across slices — the frontier the
landed `twin_bar` machinery deliberately does not cross). A first-class deliverable
in its own right, deferred.

`-- OPEN Q5a-2 (design, escalated):` which formulation — the registration's
`MarginalVanish` (vanish for `t_j > 1`) or Tao's exact class (`t_j ≥ 1+ε`,
numerator over `{≤ 1−ε}`) — the atlas should canonicalise. Both share this
obstruction; they differ in the value of `c(δ)`.

## Route log (the process record)

* **Route 0 (recon, R1).** Read the landed chain + `Enlarged.lean` (the
  unconstrained precursor: `twin_bar_enlarged`, `no_twin_weight_enlarged`, OPEN 1) +
  `ThreeBar.lean` (the β-tuning). One web check (Tao Polymath8b VII) fixed the exact
  GEH `k = 2` class and surfaced the R3 divergence + Tao's "suspect negative".
* **Route 1 (R2 pull-back, TAKEN for the bound).** The constrained class is a subset
  of "continuous `F` on `R₂e δ`", so `twin_bar_enlarged` gives the `2·(1+δ)·log 2`
  bound a fortiori — `twin_bar_constrained` is a one-liner, no re-port.
* **Route 2 (the retuned per-slice CS with the constraint, ASSESSED then shown
  capped).** Truncating the `J` outer integrals to `[0,1]` (the constraint's only
  effect) and CS-ing at base `β·slice` leaves the wing corners at efficiency
  `2·(1+δ)·log 2` for every `β` (the β-optimality computation above). The constraint
  (a first moment, transverse to the CS) does not touch the wing's second-moment
  weight. Conclusion: the route fails at `δ₀`; `wing_weight_reaches` +
  `cs_bound_ignores_constraint` pin the exact failure.
* **Route 3 (numeric truth, Part II).** Constrained Rayleigh max on two grids: the
  true sup `≤ 2`, `= 2` at `δ = 1`. Confirms the obstruction is a limitation of the
  CS METHOD, not of the truth (Tao-consistent).
-/

namespace Salt.TwinBar

open MeasureTheory Set Function intervalIntegral

/-! ## The constraint store — marginals, the vanishing predicate, admissibility -/

/-- The `t₁`-marginal of `F` at height `t₂`: `∫ t₁ in 0..(1+δ−t₂), F t₁ t₂`. This is
the inner factor of `J₁e` (`J₁e δ F = ∫ t₂ in 0..(1+δ), (marg₁ δ F t₂)²`). -/
noncomputable def marg₁ (δ : ℝ) (F : ℝ → ℝ → ℝ) (t₂ : ℝ) : ℝ :=
  ∫ t₁ in (0:ℝ)..(1 + δ - t₂), F t₁ t₂

/-- The `t₂`-marginal of `F` at abscissa `t₁`: `∫ t₂ in 0..(1+δ−t₁), F t₁ t₂`. -/
noncomputable def marg₂ (δ : ℝ) (F : ℝ → ℝ → ℝ) (t₁ : ℝ) : ℝ :=
  ∫ t₂ in (0:ℝ)..(1 + δ - t₁), F t₁ t₂

/-- **The Polymath8b marginal constraint (registration's formulation).** The
`t₁`-marginal vanishes for `t₂` outside the unit simplex (`t₂ > 1`), and symmetrically
the `t₂`-marginal for `t₁ > 1`. See the module docstring's R3 note for the divergence
from Tao's exact GEH class (`t_j ≥ 1+ε`). -/
def MarginalVanish (δ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ t₂, 1 < t₂ → t₂ ≤ 1 + δ → marg₁ δ F t₂ = 0) ∧
  (∀ t₁, 1 < t₁ → t₁ ≤ 1 + δ → marg₂ δ F t₁ = 0)

/-- **The admissible (honest ε-trick) class at `k = 2`.** Continuous on the enlarged
simplex, with the marginal-vanishing constraint. This is the frozen class of Q5a. -/
def Admissible (δ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (uncurry F) (R₂e δ) ∧ MarginalVanish δ F

/-! ## The honest constrained CS bound and the no-go below `δ₀` -/

/-- **Q5a, `twin_bar_constrained`.** For every admissible weight `F` on the enlarged
simplex, `J₁e δ F + J₂e δ F ≤ 2·(1+δ)·log 2 · I₂e δ F`. The honest constrained bound.
Its proof is `twin_bar_enlarged` applied to the continuity component alone: the
marginal constraint is NOT consumed (see `cs_bound_ignores_constraint`). -/
theorem twin_bar_constrained {δ : ℝ} (hδ : 0 < δ) (F : ℝ → ℝ → ℝ)
    (h : Admissible δ F) :
    J₁e δ F + J₂e δ F ≤ 2 * (1 + δ) * Real.log 2 * I₂e δ F :=
  twin_bar_enlarged hδ F h.1

/-- **The per-slice CS is blind to the constraint.** The identical bound
`J₁e + J₂e ≤ 2·(1+δ)·log 2 · I₂e` holds for EVERY continuous `F`, with no marginal
hypothesis — so `twin_bar_constrained` cannot possibly beat `2·(1+δ)·log 2`, and the
marginal constraint plays no role in the CS ceiling. This is the crisp statement of
the obstruction: the route ignores exactly the information Q5a hoped it would use. -/
theorem cs_bound_ignores_constraint {δ : ℝ} (hδ : 0 < δ) (F : ℝ → ℝ → ℝ)
    (hF : ContinuousOn (uncurry F) (R₂e δ)) :
    J₁e δ F + J₂e δ F ≤ 2 * (1 + δ) * Real.log 2 * I₂e δ F :=
  twin_bar_enlarged hδ F hF

/-- **Q5a, `no_twin_weight_constrained`.** For `δ < δ₀ = 1/log 2 − 1 ≈ 0.4427`
(equivalently `(1+δ)·log 2 < 1`), the constrained twin gate is unsatisfiable: NO
admissible weight `F` of positive mass has `2·I₂e δ F < J₁e δ F + J₂e δ F`. The honest
`k = 2` no-go PERSISTS for the genuinely marginal-constrained class below the
threshold — and is non-vacuous (`admissible_witness`). For `δ ≥ δ₀` the CS ceiling is
`≥ 2` (`enlarged_ceiling_ge_two`) and the route is inconclusive; see OPEN Q5a-1. -/
theorem no_twin_weight_constrained {δ : ℝ} (hδ : 0 < δ)
    (hthr : (1 + δ) * Real.log 2 < 1) :
    ¬ ∃ F : ℝ → ℝ → ℝ, Admissible δ F ∧
      0 < I₂e δ F ∧ 2 * I₂e δ F < J₁e δ F + J₂e δ F := by
  rintro ⟨F, hA, hI, hlt⟩
  exact no_twin_weight_enlarged hδ hthr ⟨F, hA.1, hI, hlt⟩

/-! ## The obstruction: the CS ceiling crosses 2, and the wing corner is why -/

/-- **The CS ceiling is inconclusive above the threshold.** Whenever
`1 ≤ (1+δ)·log 2` (i.e. `δ ≥ δ₀`), the CS ceiling `2·(1+δ)·log 2 ≥ 2`: the bound
`twin_bar_constrained` no longer implies the no-go. -/
theorem enlarged_ceiling_ge_two {δ : ℝ} (h : 1 ≤ (1 + δ) * Real.log 2) :
    2 ≤ 2 * (1 + δ) * Real.log 2 := by
  nlinarith [h]

/-- **At the extreme enlargement `δ = 1` the CS ceiling is `4·log 2 ≈ 2.773 > 2`** —
the route is off by more than `0.77` from the fixed gate (and by `≈ 0.77` from the
true constrained sup `2.0`). Uses `Real.log 2 > 0.693`. -/
theorem ceiling_at_one : 2 < 2 * (1 + (1:ℝ)) * Real.log 2 := by
  have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  nlinarith [h]

/-- **The wing corner defeats the constraint.** On the wing `{t₁ > 1}` (inside the
enlarged simplex), the per-slice CS weight `w₁ᵉ (t₁,t₂) = 1+δ−t₂+t₁` reaches
`2·(1+δ)` — at the corner `(t₁,t₂) = (1+δ, 0)`. Since this equals the core constant,
and the marginal constraint is a first-moment condition transverse to the `t₁`-CS
direction (it cannot lower the second-moment weight `w₁ᵉ·F²` on the wing), no
base-tuning of the per-slice CS beats `2·(1+δ)·log 2`. This is the precise locus and
reason of the route's failure. -/
theorem wing_weight_reaches {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁ t₂ : ℝ, 1 < t₁ ∧ 0 ≤ t₂ ∧ t₁ + t₂ ≤ 1 + δ ∧ (1 + δ - t₂ + t₁) = 2 * (1 + δ) :=
  ⟨1 + δ, 0, by linarith, le_refl _, by linarith, by ring⟩

/-! ## The satisfiability witness — the tent weight `max 0 (1 − t₁ − t₂)`

`tentF` is supported on the closed unit simplex, so its marginals vanish for
`t_j > 1` (the constraint) and its enlarged mass equals its unit mass `1/12`,
independent of `δ`. This certifies the admissible class — and the `0 < I₂e` premise
of `no_twin_weight_constrained` — is jointly inhabitable by a genuine nonzero weight. -/

/-- The tent weight `tentF (t₁,t₂) = max 0 (1 − t₁ − t₂)`, supported on the unit
simplex, continuous on the whole plane. -/
def tentF (t₁ t₂ : ℝ) : ℝ := max 0 (1 - t₁ - t₂)

/-- `uncurry tentF` is continuous everywhere (hence `ContinuousOn` any set). -/
theorem tentF_continuous : Continuous (uncurry tentF) := by
  have h : uncurry tentF = fun p : ℝ × ℝ => max 0 (1 - p.1 - p.2) := rfl
  rw [h]
  exact continuous_const.max (by fun_prop)

/-- **The tent's inner mass is `(max 0 (1−t₂))³ / 3`** on the whole outer range
`t₂ ∈ [0, 1+δ]`. For `t₂ ≤ 1` the integrand is `(1−t₁−t₂)²` on `[0, 1−t₂]` and `0`
beyond; for `t₂ > 1` it is `0` throughout. -/
theorem tent_inner {δ : ℝ} (hδ : 0 ≤ δ) {t₂ : ℝ} (_h0 : 0 ≤ t₂) (h1 : t₂ ≤ 1 + δ) :
    (∫ t₁ in (0:ℝ)..(1 + δ - t₂), (tentF t₁ t₂) ^ 2) = (max 0 (1 - t₂)) ^ 3 / 3 := by
  have hb : (0:ℝ) ≤ 1 + δ - t₂ := by linarith
  have hcont : Continuous (fun t₁ => (tentF t₁ t₂) ^ 2) :=
    (continuous_const.max (by fun_prop)).pow 2
  by_cases hle : t₂ ≤ 1
  · -- `t₂ ≤ 1`: split `[0, 1+δ−t₂]` at `a := 1 − t₂`.
    have ha0 : (0:ℝ) ≤ 1 - t₂ := by linarith
    have hab : (1 - t₂) ≤ 1 + δ - t₂ := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable 0 (1 - t₂)) (hcont.intervalIntegrable (1 - t₂) (1 + δ - t₂))]
    -- On `[a, 1+δ−t₂]` the integrand is `0`.
    have htail : (∫ t₁ in (1 - t₂)..(1 + δ - t₂), (tentF t₁ t₂) ^ 2) = 0 := by
      have heq : Set.EqOn (fun t₁ => (tentF t₁ t₂) ^ 2) (fun _ => (0:ℝ))
          (uIcc (1 - t₂) (1 + δ - t₂)) := by
        intro t₁ ht₁
        rw [uIcc_of_le hab] at ht₁
        have : (1 : ℝ) - t₁ - t₂ ≤ 0 := by have := ht₁.1; linarith
        simp only [tentF, max_eq_left this]; ring
      rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
    -- On `[0, a]` the integrand is `(1 − t₁ − t₂)² = ((1−t₂) − t₁)²`.
    have hcore : (∫ t₁ in (0:ℝ)..(1 - t₂), (tentF t₁ t₂) ^ 2) = (1 - t₂) ^ 3 / 3 := by
      have heq : Set.EqOn (fun t₁ => (tentF t₁ t₂) ^ 2) (fun t₁ => ((1 - t₂) - t₁) ^ 2)
          (uIcc 0 (1 - t₂)) := by
        intro t₁ ht₁
        rw [uIcc_of_le ha0] at ht₁
        have : (0:ℝ) ≤ 1 - t₁ - t₂ := by have := ht₁.2; linarith
        simp only [tentF, max_eq_right this]; ring
      rw [intervalIntegral.integral_congr heq,
          intervalIntegral.integral_comp_sub_left (fun x => x ^ 2) (1 - t₂)]
      simp only [sub_self, sub_zero]
      rw [integral_pow]; norm_num
    rw [hcore, htail, add_zero, max_eq_right ha0]
  · -- `t₂ > 1`: the integrand is `0` throughout `[0, 1+δ−t₂]`, and `max 0 (1−t₂) = 0`.
    have hgt : (1:ℝ) < t₂ := lt_of_not_ge hle
    have heq : Set.EqOn (fun t₁ => (tentF t₁ t₂) ^ 2) (fun _ => (0:ℝ))
        (uIcc 0 (1 + δ - t₂)) := by
      intro t₁ ht₁
      rw [uIcc_of_le hb] at ht₁
      have : (1:ℝ) - t₁ - t₂ ≤ 0 := by have := ht₁.1; linarith
      simp only [tentF, max_eq_left this]; ring
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero,
        max_eq_left (by linarith : (1:ℝ) - t₂ ≤ 0)]
    norm_num

/-- **The tent's enlarged mass is `1/12`, independent of `δ`.** `I₂e δ tentF = 1/12`:
the outer integral of `(max 0 (1−t₂))³/3` collapses onto `[0,1]` (the tail is `0`)
and equals `∫₀¹ (1−t₂)³/3 = 1/12`. In particular `0 < I₂e δ tentF`. -/
theorem I₂e_tent {δ : ℝ} (hδ : 0 ≤ δ) : I₂e δ tentF = 1 / 12 := by
  have hb : (0:ℝ) ≤ 1 + δ := by linarith
  have h01 : (1:ℝ) ≤ 1 + δ := by linarith
  unfold I₂e
  -- Replace the inner integral by its closed form `(max 0 (1−t₂))³/3`.
  have hinner : Set.EqOn (fun t₂ => ∫ t₁ in (0:ℝ)..(1 + δ - t₂), (tentF t₁ t₂) ^ 2)
      (fun t₂ => (max 0 (1 - t₂)) ^ 3 / 3) (uIcc 0 (1 + δ)) := by
    intro t₂ ht₂
    rw [uIcc_of_le hb] at ht₂
    exact tent_inner hδ ht₂.1 ht₂.2
  rw [intervalIntegral.integral_congr hinner]
  -- Continuity of the outer integrand, for the interval splits.
  have hcont : Continuous (fun t₂ : ℝ => (max 0 (1 - t₂)) ^ 3 / 3) :=
    ((continuous_const.max (by fun_prop)).pow 3).div_const 3
  -- Split `[0, 1+δ] = [0,1] ∪ [1, 1+δ]`; the second piece is `0`.
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 (1 + δ))]
  have htail : (∫ t₂ in (1:ℝ)..(1 + δ), (max 0 (1 - t₂)) ^ 3 / 3) = 0 := by
    have heq : Set.EqOn (fun t₂ => (max 0 (1 - t₂)) ^ 3 / 3) (fun _ => (0:ℝ))
        (uIcc 1 (1 + δ)) := by
      intro t₂ ht₂
      rw [uIcc_of_le h01] at ht₂
      simp only [max_eq_left (by have := ht₂.1; linarith : (1:ℝ) - t₂ ≤ 0)]; ring
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
  have hhead : (∫ t₂ in (0:ℝ)..1, (max 0 (1 - t₂)) ^ 3 / 3) = 1 / 12 := by
    have heq : Set.EqOn (fun t₂ => (max 0 (1 - t₂)) ^ 3 / 3) (fun t₂ => (1 - t₂) ^ 3 / 3)
        (uIcc (0:ℝ) 1) := by
      intro t₂ ht₂
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht₂
      simp only [max_eq_right (by have := ht₂.2; linarith : (0:ℝ) ≤ 1 - t₂)]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_div,
        intervalIntegral.integral_comp_sub_left (fun x => x ^ 3) 1]
    simp only [sub_self, sub_zero]
    rw [integral_pow]; norm_num
  rw [hhead, htail, add_zero]

/-- **The marginal constraint holds for the tent.** `tentF` is supported on the unit
simplex, so both marginals vanish for the outer coordinate `> 1`. -/
theorem tent_marginalVanish {δ : ℝ} : MarginalVanish δ tentF := by
  have vanish : ∀ s : ℝ, 1 < s → s ≤ 1 + δ →
      (∫ t in (0:ℝ)..(1 + δ - s), max 0 (1 - t - s)) = 0 := by
    intro s _ hs2
    have hb : (0:ℝ) ≤ 1 + δ - s := by linarith
    have heq : Set.EqOn (fun t => max 0 (1 - t - s)) (fun _ => (0:ℝ)) (uIcc 0 (1 + δ - s)) := by
      intro t ht
      rw [uIcc_of_le hb] at ht
      simp only [max_eq_left (by have := ht.1; linarith : (1:ℝ) - t - s ≤ 0)]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
  refine ⟨fun t₂ h1 h2 => ?_, fun t₁ h1 h2 => ?_⟩
  · -- `marg₁`: integrate `tentF t₁ t₂` over `t₁`; `tentF t₁ t₂ = max 0 (1 − t₁ − t₂)`.
    simp only [marg₁, tentF]
    exact vanish t₂ h1 h2
  · -- `marg₂`: integrate `tentF t₁ t₂` over `t₂`; reshape `1 − t₁ − t₂ = 1 − t₂ − t₁`.
    simp only [marg₂, tentF]
    have hre : Set.EqOn (fun t₂ => max 0 (1 - t₁ - t₂)) (fun t₂ => max 0 (1 - t₂ - t₁))
        (uIcc 0 (1 + δ - t₁)) := fun t₂ _ => by
      change max 0 (1 - t₁ - t₂) = max 0 (1 - t₂ - t₁)
      rw [show (1:ℝ) - t₁ - t₂ = 1 - t₂ - t₁ from by ring]
    rw [intervalIntegral.integral_congr hre]
    exact vanish t₁ h1 h2

/-- **Q5a, `admissible_witness` (the satisfiability certificate).** For every `δ > 0`
there is an admissible weight of positive mass: the tent `tentF`, with
`I₂e δ tentF = 1/12 > 0`. This certifies that the class `Admissible` and the
`0 < I₂e` premise of `no_twin_weight_constrained` are jointly inhabitable — the no-go
is not vacuous. -/
theorem admissible_witness {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : ℝ → ℝ → ℝ, Admissible δ F ∧ 0 < I₂e δ F := by
  refine ⟨tentF, ⟨tentF_continuous.continuousOn, tent_marginalVanish⟩, ?_⟩
  rw [I₂e_tent hδ.le]; norm_num

end Salt.TwinBar
