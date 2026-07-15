/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Impossibility

/-!
# Exploration pilot P-A/P-B — the δ-enlarged simplex at `k = 2`

**This is EXPLORATION, not a frozen blueprint node.** Design context:
`docs/exploration/pilot.md` (probes P-A, P-B) and `docs/writeup/pre-outline.md` §7.
The file adds NEW work only; it edits no landed file and is not wired into
`Salt.TwinBar.All`. Everything here is sorry-free and axiom-clean; the OPEN
questions are recorded as prose, never as a `sorry`'d theorem.

## What is delivered (summary)

* **P-B (hygiene corollaries).** `twin_bar_asymmetric`, `twin_bar_signed`:
  near-`exact` restatements of the landed `twin_bar` whose names make the
  symmetry-freedom and sign-freedom of the bound citable; plus
  `density_bridge_question`, a *stated-but-unproved* `Prop` (a `def`, not a
  theorem) pinning the continuous-vs-`L²` bridge precisely.
* **P-A (the δ-enlarged delimitation).** `twin_bar_enlarged`: for every
  `δ > 0` and every continuous `F` on the enlarged simplex `R₂e δ`,
  `J₁e δ F + J₂e δ F ≤ 2·(1+δ)·log 2 · I₂e δ F`, i.e. the enlarged
  Selberg ratio is bounded by `2·(1+δ)·log 2`. `no_twin_weight_enlarged`:
  whenever `(1+δ)·log 2 < 1` (e.g. `δ ≤ 2/5`) the enlarged twin gate
  `2·I₂e < J₁e + J₂e` is unsatisfiable — the no-go PERSISTS under the
  ε-enlargement below the threshold `δ₀ = 1/log 2 − 1 ≈ 0.4427`.

## The carrier-shape decision (the load-bearing design choice — READ THIS)

The δ-enlargement admits (at least) two honest shapes, and *they change the
answer*, so this was escalated as a design decision (see the OPEN note below).

* **Shape A (support enlarged, prime-detection marginal unenlarged):** `F`
  supported on `R₂e δ = {t₁+t₂ ≤ 1+δ}`; `I` over all of `R₂e δ`; but the
  `Jᵢ` OUTER integral stays on `[0,1]` (the non-prime coordinate still obeys
  the level-of-distribution constraint `≤ 1`). This is what `pilot.md`
  describes ("the J-integrals' OUTER variable stays on [0,1]").
* **Shape B (fully enlarged):** `I` and both `Jᵢ` outer integrals over
  `[0,1+δ]`. This is the *unit* problem rescaled by `(1+δ)`; by the scaling
  `s ↦ (1+δ)s` it is equivalent to the landed `twin_bar` and gives exactly
  the same constant `2·(1+δ)·log 2` (see `*_scale` lemmas).

**The honest sieve functional is Shape A WITH a marginal-support constraint.**
The Polymath8b enlargement (Tao, "Polymath8b IV/VI") optimizes over symmetric
`F` supported in the enlarged simplex *subject to the constraint that the
marginals `∫ F dtᵢ` are supported in the ORIGINAL simplex* `{≤ 1}`. Under that
constraint the `Jᵢ` marginal vanishes on `(1, 1+δ]`, so Shape A and Shape B
**coincide on the numerators**, while `I` is the full enlarged mass in both.
Hence the theorem we land — proved for Shape B, i.e. for arbitrary continuous
`F` with NO marginal constraint — is an *upper bound valid a fortiori for the
constrained honest problem*: `M₂^{[δ]} ≤ 2·(1+δ)·log 2`.

**Why Shape A *without* the constraint is NOT the honest functional (the catch
that forced the escalation).** Take `F ≡ 1` on `R₂e δ`. Unconstrained Shape A
gives ratio `(J₁+J₂)/I = (4/3)·(1+3δ+3δ²)/(1+δ)²`, which exceeds `2` for
`δ` near `1` (e.g. `δ = 1`: ratio `7/3`). If unconstrained Shape A were the
honest sieve functional this would prove `DHL[2,2]` under EH — i.e. twin
primes — which is open. The resolution is exactly the marginal-support
constraint: `F ≡ 1` violates it (`∫₀^{1+δ−t₂} 1 dt₁ = 1+δ−t₂ ≠ 0` for
`t₂ ∈ (1,1+δ]`), so `F ≡ 1` is inadmissible for the honest problem. A naive
executor that fixed on unconstrained Shape A would have "refuted" the no-go;
the constraint is what a designer supplies.

## The threshold, and what it does and does not say

`2·(1+δ)·log 2 < 2 ⟺ (1+δ)·log 2 < 1 ⟺ δ < δ₀ := 1/log 2 − 1 ≈ 0.4427`.

So for `0 < δ ≤ δ₀` the honest enlarged constant is `< 2`: the ε-enlargement
CANNOT cross the twin gate (`no_twin_weight_enlarged`) — a delimitation, to our
knowledge not previously recorded at `k = 2`. For `δ > δ₀` the bound
`2·(1+δ)·log 2` exceeds `2` and is INCONCLUSIVE: it does not decide whether the
*marginally-constrained* honest `M₂^{[δ]}` reaches `2`. That is an OPEN
question (see below); the unconstrained `F ≡ 1` witness does NOT settle it
because it is inadmissible.

Two readings of the threshold, both honest and worth stating:
1. Against the FIXED gate `2`: no-go for `δ ≤ δ₀`, open above.
2. Against a θ-adjusted gate: if enlarging the support to `1+δ` is paid for by
   a level-of-distribution factor (so the honest gate scales to `2·(1+δ)`),
   then `2·(1+δ)·log 2 < 2·(1+δ)` for ALL `δ` (as `log 2 < 1`): the `log 2 < 1`
   shortfall is scale-invariant and the enlargement buys nothing at `k = 2`.
   Which reading is correct is a sieve-interpretation question (the exact form
   of Polymath8b's criterion), flagged below.

## OPEN (recorded as prose, per the exploration STOP-AND-FLAG rule)

`-- OPEN 1 (design decision, escalated to the house session):` the honest
sieve interpretation of the enlarged `k = 2` variational problem — specifically
(a) whether the twin gate stays `2` or scales to `2·(1+δ)` under enlargement,
and (b) the exact marginal-support constraint (Shape A + marginals in `{≤1}`).
Both change the *interpretation* of the landed inequality but not its truth.
The precise failing/undecided inequality for reading (1) above `δ₀`:
`does there exist continuous F on R₂e δ with marginals supported in {t ≤ 1}`
`and 2·I₂e δ F < J₁e δ F + J₂e δ F, for some δ ∈ (δ₀, 1]?` — undecided by the
CS machinery (its bound `2·(1+δ)·log 2 ≥ 2` there).

`-- OPEN 2:` the L²/density bridge (`density_bridge_question`) — the landed
bounds are per-continuous-`F`; Polymath8b's `M₂` is an `L²`-sup. Stated, not
attempted.

## The proof route that landed (and the ones abandoned) — the process log

* **Route 0 (recon).** Read the landed chain (`Defs`/`LogWeight`/`SliceCS`/
  `Tonelli`/`Impossibility`/`Witness`). Confirmed the CS uses weight base
  `a = 1−t₂ =` slice length, giving the a-uniform `log 2`, and the magic
  `w₁+w₂ = 2`.
* **Route 1 (the pilot's suggested "re-tuned weight", partially pursued then
  set aside as the primary path).** On the enlarged slice `t₁ ∈ [0, 1+δ−t₂]`,
  RE-BASE the CS weight to `c = 1+δ−t₂ =` the *new* slice length. Then
  `∫₀^{c}(c+t)⁻¹ = log 2` again (uniform — the pilot's feared corner
  divergence `∫₀^δ t⁻¹` is avoided precisely by moving the base), and
  `w₁+w₂ = 2+2δ` (still constant). Direct assembly then needs (i) enlarged
  marginal integrability, (ii) an enlarged Tonelli swap, and (iii) a NEW
  "wing" combine (`R₂e δ = core ⊔ wing₁ ⊔ wing₂`, with only one weight present
  on each wing) — ~200 lines with genuinely new 2-D combinatorics. Abandoned
  as the primary path in favor of Route 2 (same constant, far less plumbing),
  but the re-tuning insight is the mathematical resolution of the pilot's
  stated obstruction and is recorded here.
* **Route 2 (LANDED): reduce to the landed `twin_bar` by scaling.** Shape A's
  `Jᵢ` are `≤` Shape B's (extend the outer integral `[0,1] ⊆ [0,1+δ]`, nonneg
  integrand), and Shape B is the unit problem scaled by `(1+δ)`:
  `I₂e = (1+δ)²·I₂ ∘ scale`, `Jᵢe = (1+δ)³·Jᵢ ∘ scale`. Applying `twin_bar`
  to the scaled weight gives `Jᵢe`-bounds with constant `2·(1+δ)·log 2`,
  reusing the entire landed CS+Tonelli chain wholesale via three unconditional
  change-of-variables identities (`intervalIntegral.integral_comp_mul_left`).
  No new integrability, no re-port of Tonelli. This is why the delivered
  theorem is stated with the fully-enlarged (Shape B) carriers, which equal
  the honest Shape A carriers under the marginal constraint.
* **Route 3 (Shape A ≤ Shape B, NOT formalized — a deliberate stop).** Proving
  `J₁e^{ShapeA}(outer [0,1]) ≤ J₁e^{ShapeB}(outer [0,1+δ])` for a merely
  `ContinuousOn` `F` needs interval-integrability of the *squared marginal*
  `(∫F)²` on `[0,1+δ]`, which needs the marginal continuous/measurable — and
  mathlib's parametric-integral continuity wants GLOBAL joint continuity
  (`continuous_parametric_intervalIntegral_of_continuous`), unavailable for a
  `ContinuousOn`-only weight without a Tietze extension. The landed `twin_bar`
  deliberately avoided exactly this (`integral_mono_of_nonneg` + Fubini
  marginals). Since Shape A = Shape B under the honest marginal constraint,
  formalizing the unconstrained `≤` buys nothing for the honest statement, so
  it was stopped rather than ground out. (Calibration note for T3: this is the
  kind of "plumbing that the landed proof engineered around" that eats an
  executor's budget for no mathematical gain — recognize and route past it.)
-/

namespace Salt.TwinBar

open MeasureTheory Set Function intervalIntegral

/-! ## P-B — the hygiene corollaries (symmetry- and sign-freedom made citable) -/

/-- **P-B, `twin_bar_asymmetric`.** The landed twin bound holds for weights with
NO symmetry hypothesis: there is no assumption that `F t₁ t₂ = F t₂ t₁`. This is
a verbatim restatement of `twin_bar` whose name makes the symmetry-freedom of the
`k = 2` no-go citable — the discriminant Cauchy–Schwarz (`interval_CS`) and the
Tonelli swap (`simplex_swap`) never use symmetry. -/
theorem twin_bar_asymmetric (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (uncurry F) R₂) :
    J₁ F + J₂ F ≤ 2 * Real.log 2 * I₂ F :=
  twin_bar F hF

/-- **P-B, `twin_bar_signed`.** The landed twin bound holds for SIGN-INDEFINITE
weights (the Maynard `Fstar` has negative coefficients): here demonstrated on the
sign-flipped weight `-F`, for which the same bound holds. The proof is
sign-agnostic because every carrier is a square (`I₂`, `J₁`, `J₂` are even in `F`)
and the interval Cauchy–Schwarz is the discriminant form, needing no nonnegativity
of `F`. -/
theorem twin_bar_signed (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (uncurry F) R₂) :
    J₁ (fun t₁ t₂ => -F t₁ t₂) + J₂ (fun t₁ t₂ => -F t₁ t₂)
      ≤ 2 * Real.log 2 * I₂ (fun t₁ t₂ => -F t₁ t₂) :=
  twin_bar _ hF.neg

/-- **P-B, `density_bridge_question` (OPEN — stated precisely, NOT proved).**
The landed bounds (`twin_bar`, `M₂_squeeze`) are per-`F` over CONTINUOUS weights;
Polymath8b's `M₂` (eq. 33) is an `L²`-sup over the whole admissible class. The
density bridge would assert that the continuous-`F` bound `2·log 2` already holds
for every square-integrable weight on the simplex — i.e. that continuity may be
relaxed to `L²(R₂)` without changing the bound, so that the continuous-`F` sup
equals Polymath8b's `L²`-sup. This is the exact proposition; it is left as a
`def` (a stated question), never proved here. -/
def density_bridge_question : Prop :=
  ∀ F : ℝ → ℝ → ℝ,
    Integrable (fun p : ℝ × ℝ => (uncurry F p) ^ 2) (volume.restrict R₂) →
    J₁ F + J₂ F ≤ 2 * Real.log 2 * I₂ F

/-! ## P-A — the δ-enlarged carriers (fully-enlarged / Shape B form)

`R₂e δ` is the `(1+δ)`-simplex. `I₂e` is the full `L²`-mass over it; `J₁e`, `J₂e`
are the Selberg peels with the outer integral over `[0, 1+δ]`. Under the honest
ε-trick marginal-support constraint (marginals supported in `{≤ 1}`) these `Jᵢe`
equal their Shape-A (outer `[0,1]`) counterparts; without the constraint they are
`≥`, so the bound below is an upper bound valid for the honest constrained
problem. See the module docstring's carrier-shape decision. -/

/-- The closed `(1+δ)`-enlarged simplex `R₂e δ = {0 ≤ t₁, 0 ≤ t₂, t₁+t₂ ≤ 1+δ}`. -/
def R₂e (δ : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 + δ}

/-- The enlarged `L²`-mass carrier `I₂e δ F = ∬_{R₂e δ} F²`. -/
noncomputable def I₂e (δ : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₂ in (0:ℝ)..(1 + δ), ∫ t₁ in (0:ℝ)..(1 + δ - t₂), (F t₁ t₂) ^ 2

/-- The enlarged first Selberg peel `J₁e` (outer over `[0,1+δ]`). -/
noncomputable def J₁e (δ : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₂ in (0:ℝ)..(1 + δ), (∫ t₁ in (0:ℝ)..(1 + δ - t₂), F t₁ t₂) ^ 2

/-- The enlarged second Selberg peel `J₂e` (outer over `[0,1+δ]`). -/
noncomputable def J₂e (δ : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t₁ in (0:ℝ)..(1 + δ), (∫ t₂ in (0:ℝ)..(1 + δ - t₁), F t₁ t₂) ^ 2

/-- The `(1+δ)`-scaling of a weight: `Gsc δ F (s₁,s₂) = F ((1+δ)s₁, (1+δ)s₂)`.
It carries the enlarged problem back onto the unit simplex. -/
noncomputable def Gsc (δ : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun s₁ s₂ => F ((1 + δ) * s₁) ((1 + δ) * s₂)

/-- The scaled weight is continuous on the unit simplex `R₂` when `F` is
continuous on the enlarged simplex `R₂e δ`, because `(s₁,s₂) ↦ ((1+δ)s₁,(1+δ)s₂)`
maps `R₂` into `R₂e δ`. -/
theorem Gsc_continuousOn {δ : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (uncurry F) (R₂e δ)) :
    ContinuousOn (uncurry (Gsc δ F)) R₂ := by
  have hpos : (0:ℝ) < 1 + δ := by linarith
  have hmap : MapsTo (fun p : ℝ × ℝ => ((1 + δ) * p.1, (1 + δ) * p.2)) R₂ (R₂e δ) := by
    rintro p ⟨h1, h2, h3⟩
    refine ⟨mul_nonneg hpos.le h1, mul_nonneg hpos.le h2, ?_⟩
    have hre : (1 + δ) * p.1 + (1 + δ) * p.2 = (1 + δ) * (p.1 + p.2) := by ring
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left h3 hpos.le]
  have hcont : Continuous (fun p : ℝ × ℝ => ((1 + δ) * p.1, (1 + δ) * p.2)) := by fun_prop
  have hEq : uncurry (Gsc δ F)
      = (uncurry F) ∘ (fun p : ℝ × ℝ => ((1 + δ) * p.1, (1 + δ) * p.2)) := rfl
  rw [hEq]
  exact hF.comp hcont.continuousOn hmap

/-! ## The three scaling identities (unconditional change of variables) -/

/-- `I₂e δ F = (1+δ)² · I₂ (Gsc δ F)`: the enlarged mass is the unit mass of the
scaled weight, times the Jacobian `(1+δ)²`. -/
private theorem I₂e_scale {δ : ℝ} (hδ : 0 < δ) (F : ℝ → ℝ → ℝ) :
    I₂e δ F = (1 + δ) ^ 2 * I₂ (Gsc δ F) := by
  have hpos : (0:ℝ) < 1 + δ := by linarith
  have hne : (1 + δ) ≠ 0 := hpos.ne'
  have hinner : ∀ s₂ : ℝ, (∫ s₁ in (0:ℝ)..(1 - s₂), (Gsc δ F s₁ s₂) ^ 2)
      = (1 + δ)⁻¹ * ∫ t₁ in (0:ℝ)..(1 + δ - (1 + δ) * s₂), (F t₁ ((1 + δ) * s₂)) ^ 2 := by
    intro s₂
    rw [show (1 + δ - (1 + δ) * s₂) = (1 + δ) * (1 - s₂) from by ring]
    have h := integral_comp_mul_left (fun t₁ => (F t₁ ((1 + δ) * s₂)) ^ 2) hne
      (a := 0) (b := 1 - s₂)
    simpa [Gsc, smul_eq_mul, mul_zero] using h
  have step : I₂ (Gsc δ F)
      = (1 + δ)⁻¹ * ∫ s₂ in (0:ℝ)..1,
          ∫ t₁ in (0:ℝ)..(1 + δ - (1 + δ) * s₂), (F t₁ ((1 + δ) * s₂)) ^ 2 := by
    unfold I₂
    rw [intervalIntegral.integral_congr (fun s₂ _ => hinner s₂),
      intervalIntegral.integral_const_mul]
  rw [step]
  have h2 := integral_comp_mul_left
    (fun t₂ => ∫ t₁ in (0:ℝ)..(1 + δ - t₂), (F t₁ t₂) ^ 2) hne (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one] at h2
  rw [h2]
  unfold I₂e
  field_simp

/-- `J₁e δ F = (1+δ)³ · J₁ (Gsc δ F)`. -/
private theorem J₁e_scale {δ : ℝ} (hδ : 0 < δ) (F : ℝ → ℝ → ℝ) :
    J₁e δ F = (1 + δ) ^ 3 * J₁ (Gsc δ F) := by
  have hpos : (0:ℝ) < 1 + δ := by linarith
  have hne : (1 + δ) ≠ 0 := hpos.ne'
  have hinner : ∀ s₂ : ℝ, ((∫ s₁ in (0:ℝ)..(1 - s₂), Gsc δ F s₁ s₂) ^ 2)
      = (1 + δ)⁻¹ ^ 2 * (∫ t₁ in (0:ℝ)..(1 + δ - (1 + δ) * s₂), F t₁ ((1 + δ) * s₂)) ^ 2 := by
    intro s₂
    have h' : (∫ s₁ in (0:ℝ)..(1 - s₂), Gsc δ F s₁ s₂)
        = (1 + δ)⁻¹ * ∫ t₁ in (0:ℝ)..(1 + δ - (1 + δ) * s₂), F t₁ ((1 + δ) * s₂) := by
      rw [show (1 + δ - (1 + δ) * s₂) = (1 + δ) * (1 - s₂) from by ring]
      have h := integral_comp_mul_left (fun t₁ => F t₁ ((1 + δ) * s₂)) hne (a := 0) (b := 1 - s₂)
      simpa [Gsc, smul_eq_mul, mul_zero] using h
    rw [h']; ring
  have step : J₁ (Gsc δ F)
      = (1 + δ)⁻¹ ^ 2 * ∫ s₂ in (0:ℝ)..1,
          (∫ t₁ in (0:ℝ)..(1 + δ - (1 + δ) * s₂), F t₁ ((1 + δ) * s₂)) ^ 2 := by
    unfold J₁
    rw [intervalIntegral.integral_congr (fun s₂ _ => hinner s₂),
      intervalIntegral.integral_const_mul]
  rw [step]
  have h2 := integral_comp_mul_left
    (fun t₂ => (∫ t₁ in (0:ℝ)..(1 + δ - t₂), F t₁ t₂) ^ 2) hne (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one] at h2
  rw [h2]
  unfold J₁e
  field_simp

/-- `J₂e δ F = (1+δ)³ · J₂ (Gsc δ F)` (the mirror of `J₁e_scale`). -/
private theorem J₂e_scale {δ : ℝ} (hδ : 0 < δ) (F : ℝ → ℝ → ℝ) :
    J₂e δ F = (1 + δ) ^ 3 * J₂ (Gsc δ F) := by
  have hpos : (0:ℝ) < 1 + δ := by linarith
  have hne : (1 + δ) ≠ 0 := hpos.ne'
  have hinner : ∀ s₁ : ℝ, ((∫ s₂ in (0:ℝ)..(1 - s₁), Gsc δ F s₁ s₂) ^ 2)
      = (1 + δ)⁻¹ ^ 2 * (∫ t₂ in (0:ℝ)..(1 + δ - (1 + δ) * s₁), F ((1 + δ) * s₁) t₂) ^ 2 := by
    intro s₁
    have h' : (∫ s₂ in (0:ℝ)..(1 - s₁), Gsc δ F s₁ s₂)
        = (1 + δ)⁻¹ * ∫ t₂ in (0:ℝ)..(1 + δ - (1 + δ) * s₁), F ((1 + δ) * s₁) t₂ := by
      rw [show (1 + δ - (1 + δ) * s₁) = (1 + δ) * (1 - s₁) from by ring]
      have h := integral_comp_mul_left (fun t₂ => F ((1 + δ) * s₁) t₂) hne (a := 0) (b := 1 - s₁)
      simpa [Gsc, smul_eq_mul, mul_zero] using h
    rw [h']; ring
  have step : J₂ (Gsc δ F)
      = (1 + δ)⁻¹ ^ 2 * ∫ s₁ in (0:ℝ)..1,
          (∫ t₂ in (0:ℝ)..(1 + δ - (1 + δ) * s₁), F ((1 + δ) * s₁) t₂) ^ 2 := by
    unfold J₂
    rw [intervalIntegral.integral_congr (fun s₁ _ => hinner s₁),
      intervalIntegral.integral_const_mul]
  rw [step]
  have h2 := integral_comp_mul_left
    (fun t₁ => (∫ t₂ in (0:ℝ)..(1 + δ - t₁), F t₁ t₂) ^ 2) hne (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, mul_one] at h2
  rw [h2]
  unfold J₂e
  field_simp

/-! ## The δ-enlarged delimitation theorem and the persisting no-go -/

/-- **P-A, `twin_bar_enlarged`.** For every `δ > 0` and every continuous weight
`F` on the enlarged simplex `R₂e δ`,
`J₁e δ F + J₂e δ F ≤ 2·(1+δ)·log 2 · I₂e δ F`. The enlarged Selberg ratio is
bounded by `2·(1+δ)·log 2` — the landed `2·log 2` scaled by `(1+δ)`. Proof:
reduce to the landed `twin_bar` for the `(1+δ)`-scaled weight `Gsc δ F` via the
three change-of-variables identities (`I₂e/J₁e/J₂e_scale`). See the module
docstring for the carrier-shape honesty contract. -/
theorem twin_bar_enlarged {δ : ℝ} (hδ : 0 < δ) (F : ℝ → ℝ → ℝ)
    (hF : ContinuousOn (uncurry F) (R₂e δ)) :
    J₁e δ F + J₂e δ F ≤ 2 * (1 + δ) * Real.log 2 * I₂e δ F := by
  have hbar := twin_bar (Gsc δ F) (Gsc_continuousOn hδ hF)
  rw [I₂e_scale hδ, J₁e_scale hδ, J₂e_scale hδ]
  have hcube : (0:ℝ) ≤ (1 + δ) ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hbar hcube]

/-- **P-A, `no_twin_weight_enlarged`.** Whenever `(1+δ)·log 2 < 1` (equivalently
`δ < δ₀ = 1/log 2 − 1 ≈ 0.4427`; e.g. `δ ≤ 2/5` suffices), the ε-enlarged twin
gate is unsatisfiable: NO continuous weight `F` on `R₂e δ` with positive mass has
`2·I₂e δ F < J₁e δ F + J₂e δ F`. The `k = 2` no-go PERSISTS under the
δ-enlargement below the threshold — a delimitation, to our knowledge not recorded
at `k = 2`. (For `δ ≥ δ₀` the bound `2·(1+δ)·log 2 ≥ 2` and the method is
inconclusive; see OPEN 1.) -/
theorem no_twin_weight_enlarged {δ : ℝ} (hδ : 0 < δ) (hthr : (1 + δ) * Real.log 2 < 1) :
    ¬ ∃ F : ℝ → ℝ → ℝ, ContinuousOn (uncurry F) (R₂e δ) ∧
      0 < I₂e δ F ∧ 2 * I₂e δ F < J₁e δ F + J₂e δ F := by
  rintro ⟨F, hF, hI, hlt⟩
  have hbar := twin_bar_enlarged hδ F hF
  nlinarith [hbar, hlt,
    mul_pos (show (0:ℝ) < 2 - 2 * (1 + δ) * Real.log 2 by nlinarith [hthr]) hI]

/-- A concrete admissible threshold: `δ = 2/5` satisfies `(1+δ)·log 2 < 1`, so the
enlarged no-go holds there (witnessing that the persistence range is non-empty and
explicit). -/
theorem two_fifths_below_threshold : (1 + (2/5 : ℝ)) * Real.log 2 < 1 := by
  have h : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  nlinarith [h, Real.log_pos (by norm_num : (1:ℝ) < 2)]

end Salt.TwinBar
