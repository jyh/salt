/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Abel
import Salt.MR.M4Close

/-!
# M4-B2 — THE PHASE BRIDGE and THE PARTIAL-SUM FAMILY (`M4BridgePhase`)

⟦THE FIVE OPEN BRIDGES⟧ #2 of `M4Close`'s header, landed:

> **the Abel drift kill inside the door window** — `M4Abel.norm_phase_sum_arcDen_drift` is
> landed for `∑_{M<m≤N} eR(θm)A(m)`; the bridge is `absWindowSum`'s own phase
> (`Complex.exp (2πiα·)`) to `eR`, and the partial-sum family `S(K)`, `K ≤ H`, which makes
> the mean-square obligation UNIFORM over sub-window lengths.

## §1 — THE `eR` BRIDGE (the `2π` placement, both directions)

Two spellings of the same additive character meet here:

* `M4Window.absWindowSum` writes its phase **inline and left-associated**,
  `Complex.exp (2 * ↑π * I * ↑α * ↑m)` (`M4Window.lean:95`);
* `Salt.ExpSum.eR x = Complex.exp (2 * ↑π * I * ↑x)` (`ExpSum/Basic.lean:43`) — the `2π` is
  **inside** the character, which is why `M4Abel`'s Lipschitz constant is `2π` and not `1`.

The conversion is therefore *not* a normalisation but a re-association plus one cast:

```
Complex.exp (2 * ↑π * I * ↑α * ↑m)  =  eR (α * m)          (`exp_phase_eq_eR`)
eR (α * m)  =  Complex.exp (2 * ↑π * I * ↑α * ↑m)           (`eR_eq_exp_phase`)
```

Both directions are named, and the whole file's phase algebra flows through them.  No `2π`
is ever introduced or cancelled: `↑(α * m) = ↑α * ↑m` is the only content (`push_cast`).

**The index type.**  `Salt.ExpSum`'s A-process is written over `ℤ`-windows, but `eR : ℝ → ℂ`
itself is index-free and `M4Abel` runs over `ℕ`-`Finset`s (`Finset.Ioc M N`, `M N : ℕ`) with
`ℂ` weights — exactly `absWindowSum`'s own index type.  So the `ℤ/ℕ` seam of `ExpSum` is
never crossed here; the only cast is `ℕ → ℝ → ℂ` on the summation variable.

## §2 — THE PARTIAL-SUM FAMILY

`M4Abel`'s partial sums are `S(K) = ∑_{M < m ≤ K} A(m)` with `A` the *phase-carrying*
coefficient.  At the door, `M = n`, `N = n + H`, and `A(m) = a(m)·e(βm)` for the rational
approximant `β = b/q` — so `S` is not a new object at all:

```
∑_{n < m ≤ n+K} a(m) e(βm)  =  absWindowSum a K n β                (`sum_Ioc_phaseCoeff_eq`)
```

**the length-`K` prefix of the window sum is the window sum at length `K`.**  `S(H)` is the
full sum on the nose (`absWindowSum_eq_phaseCoeff_sum` at `K = H`; no `±1` slack — the
half-open `Ioc n (n+K)` convention of M4-0 pays again).  The sup form
(`subWindowSup`) is a `Finset.sup'` over `Icc 0 H` in the **length** `K`, and
`abel_sup'_eq_subWindowSup` identifies it byte-exactly with the endpoint-indexed
`Finset.sup'` over `Icc n (n+H)` that `M4Abel.norm_phase_sum_arcDen_drift_sup` produces.

## §3 — THE DRIFT COMPOSITION

At a tight-major `α` (`NearRatTight (arcDen 12 H) H α`, `BigXiArc.lean:566`) the witness
gives `α = b/q + θ` with `0 < q ≤ arcDen`, `|θ| ≤ arcDen/(qH)`.  Splitting the phase
(`eR_mul_split`) turns the window sum at `α` into `M4Abel`'s shape at `θ` with coefficients
`a(m)e((b/q)m)`, and the landed payload fires:

```
‖absWindowSum a H n α‖  ≤  (1 + 2π·arcDen 12 H / q) · sup_{K ≤ H} ‖absWindowSum a K n (b/q)‖
```

(`norm_absWindowSum_le_drift_tight`).  The right-hand sup is **the class-restricted content**:
every `S(K)` sits at the *rational* frequency `b/q`, which is what makes B-1's residue-class
split (bridge #1) its supplier — `e(bm/q)` is constant on classes mod `q`.

The `q`-grading is kept in the sharp statement and thrown away only in the uniform corollary
(`norm_absWindowSum_le_ratPartial`, `q ≥ 1`), where the price becomes `1 + 2π·arcDen 12 H`.

## §4 — THE UNIFORMITY HOOK (what the mean-square side must supply)

`M4Close.M4SievedDoorSq` asks for the mean square of the sieved λ-window sum **at `α`**.
§3 is a pointwise-in-`n` bound with an `n`-independent constant, so it integrates: the
obligation moves to the mean square of the **sub-window sup at the rational**,

```
∫ (sup_{K ≤ H} ‖absWindowSum (1_𝒮λ) K n (b/q)‖)² ∂logMeasure  ≤  Braw' H · H²
```

named `M4SievedDoorSqSup`, and `m4_sievedDoorSq_of_sup` discharges the socket from it at the
grade cost `(1 + 2π·arcDen 12 H)²` — i.e. `(log H)^{24}`-scale, comfortably inside the
`W^{−5/2} = (log H)^{−30}` saving that `M4Close.§2` prices against
(`√((log H)^{24}·(log H)^{−30}) = (log H)^{−3} ≤ C(log H)^{−11/4}loglog H`).

Anti-vacuity is discharged in the same shape as `M4Close.m4_sievedDoorSq_trivial`:
`m4_sievedDoorSqSup_trivial` inhabits the sup obligation at the trivial grade `Braw' ≡ 1`.

## Conventions

* **One log scale**: `arcDen 12 H = (log H)^{12}` only, and it is never evaluated — it is
  `Real.rpow`-valued, so `arcDen_nonneg` (`BigXiArc.lean:620`) is the *only* fact used.
* **Nothing is re-derived**: `M4Abel`'s Abel identity, its `2π`-Lipschitz phase step and its
  `arcDen` payload are consumed verbatim; so are `M4Window.absWindowSum` and
  `ShiftCorr.integral_logMeasure_eq` (so no integrability side condition is ever incurred).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.ExpSum
open Salt.Entropy.Chowla

/-! ## §1 — THE `eR` BRIDGE

`absWindowSum`'s inline phase versus `Salt.ExpSum.eR`.  The `2π` lives inside `eR`, so the
identity is an association/cast fact and carries no normalising factor. -/

/-- **THE BRIDGE IDENTITY**, `exp → eR`: the window sum's inline phase
`exp(2πi·α·m)` is `eR` evaluated at the *product* `α·m`.

The only content is `↑(α * m) = ↑α * ↑m` (`push_cast`) plus re-association: `eR` binds its
argument last (`2 * ↑π * I * ↑x`), `absWindowSum` binds `α` and `m` separately
(`2 * ↑π * I * ↑α * ↑m`).  No `2π` is created or destroyed. -/
theorem exp_phase_eq_eR (α : ℝ) (m : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))
      = eR (α * (m : ℝ)) := by
  rw [eR]
  congr 1
  push_cast
  ring

/-- **THE BRIDGE IDENTITY**, `eR → exp`: the same statement read the other way, so a consumer
holding an `eR`-shaped sum can descend to `absWindowSum`'s spelling without re-deriving. -/
theorem eR_eq_exp_phase (α : ℝ) (m : ℕ) :
    eR (α * (m : ℝ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ)) :=
  (exp_phase_eq_eR α m).symm

/-- **The phase split at a shifted frequency**: `e((β+θ)m) = e(θm)·e(βm)`.  The factor order
is `M4Abel`'s (`eR (θ * ↑m) * A m`), not the arithmetic one — the drift weight comes first. -/
theorem eR_mul_split (β θ : ℝ) (m : ℕ) :
    eR ((β + θ) * (m : ℝ)) = eR (θ * (m : ℝ)) * eR (β * (m : ℝ)) := by
  rw [add_mul, eR_add]
  ring

/-- The window sum in `eR` spelling, weight-first (`M4Abel`'s term order). -/
theorem absWindowSum_eq_eR_sum (a : ℕ → ℂ) (H n : ℕ) (α : ℝ) :
    absWindowSum a H n α = ∑ m ∈ Finset.Ioc n (n + H), eR (α * (m : ℝ)) * a m := by
  unfold absWindowSum
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [exp_phase_eq_eR]
  ring

/-! ## §2 — THE PARTIAL-SUM FAMILY

`M4Abel` strips the drift phase `e(θ·)` and leaves the coefficient `A(m) = a(m)e(βm)` at the
rational approximant `β`.  Its partial sums are then window sums of shorter length. -/

/-- **The Abel coefficient at the rational approximant**: `A(m) = a(m)·e(βm)`.  This is the
sequence `M4Abel.norm_phase_sum_arcDen_drift` quantifies over; §3 instantiates `β = b/q`, at
which `e(bm/q)` is constant on residue classes mod `q` (bridge #1's entry point). -/
def phaseCoeff (a : ℕ → ℂ) (β : ℝ) : ℕ → ℂ := fun m => a m * eR (β * (m : ℝ))

/-- **THE PARTIAL-SUM FAMILY, IDENTIFIED.**  `S(K) = ∑_{n < m ≤ n+K} a(m)e(βm)` *is* the
window sum of length `K`: the length-`K` prefix of the door window carries no new object.

Half-open throughout (`Ioc n (n+K)`, M4-0's convention), so there is no `±1` slack: at
`K = 0` both sides are the empty sum, at `K = H` both sides are the full window sum. -/
theorem sum_Ioc_phaseCoeff_eq (a : ℕ → ℂ) (β : ℝ) (n K : ℕ) :
    ∑ m ∈ Finset.Ioc n (n + K), phaseCoeff a β m = absWindowSum a K n β := by
  unfold absWindowSum phaseCoeff
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [exp_phase_eq_eR]

/-- The same, **endpoint-indexed** — the shape `M4Abel`'s `hpart` binder actually presents
(`∀ K, M ≤ K → K ≤ N → ‖∑_{M<m≤K} A m‖ ≤ B` with `M = n`): an absolute endpoint `K ≥ n`
becomes the length `K − n`. -/
theorem sum_Ioc_phaseCoeff_eq_sub (a : ℕ → ℂ) (β : ℝ) {n K : ℕ} (h : n ≤ K) :
    ∑ m ∈ Finset.Ioc n K, phaseCoeff a β m = absWindowSum a (K - n) n β := by
  have hK : n + (K - n) = K := by omega
  rw [← sum_Ioc_phaseCoeff_eq a β n (K - n), hK]

/-- `S(H)` is the full window sum — the family's top element, stated once. -/
theorem absWindowSum_eq_phaseCoeff_sum (a : ℕ → ℂ) (H n : ℕ) (β : ℝ) :
    absWindowSum a H n β = ∑ m ∈ Finset.Ioc n (n + H), phaseCoeff a β m :=
  (sum_Ioc_phaseCoeff_eq a β n H).symm

/-- **THE SUB-WINDOW SUP** — `sup_{K ≤ H} ‖S(K)‖`, indexed by the *length* `K`.  This is the
object the mean-square side must eventually bound (§4), and the one the drift kill consumes
(§3).  `Finset.Icc 0 H` is nonempty for every `H` (it contains `0`), so no hypothesis. -/
def subWindowSup (a : ℕ → ℂ) (H n : ℕ) (β : ℝ) : ℝ :=
  (Finset.Icc 0 H).sup' ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
    (fun K => ‖absWindowSum a K n β‖)

/-- Every sub-window is under the sup. -/
theorem le_subWindowSup (a : ℕ → ℂ) (H n : ℕ) (β : ℝ) {K : ℕ} (hK : K ≤ H) :
    ‖absWindowSum a K n β‖ ≤ subWindowSup a H n β :=
  Finset.le_sup' (f := fun K => ‖absWindowSum a K n β‖)
    (Finset.mem_Icc.mpr ⟨Nat.zero_le K, hK⟩)

/-- The full window sum is under the sup (`K = H`). -/
theorem norm_absWindowSum_le_subWindowSup (a : ℕ → ℂ) (H n : ℕ) (β : ℝ) :
    ‖absWindowSum a H n β‖ ≤ subWindowSup a H n β :=
  le_subWindowSup a H n β le_rfl

/-- The sup of norms is nonnegative (it dominates `‖S(0)‖ = 0`). -/
theorem subWindowSup_nonneg (a : ℕ → ℂ) (H n : ℕ) (β : ℝ) : 0 ≤ subWindowSup a H n β :=
  le_trans (norm_nonneg _) (le_subWindowSup a H n β (Nat.zero_le H))

/-- A uniform bound over sub-window lengths bounds the sup — the `sup'`-elimination the
mean-square supplier will use. -/
theorem subWindowSup_le {a : ℕ → ℂ} {H n : ℕ} {β B : ℝ}
    (hB : ∀ K, K ≤ H → ‖absWindowSum a K n β‖ ≤ B) : subWindowSup a H n β ≤ B :=
  Finset.sup'_le _ _ (fun K hK => hB K (Finset.mem_Icc.mp hK).2)

/-- The trivial bound at a 1-bounded coefficient sequence: every sub-window has at most `H`
terms of modulus `≤ 1` (`M4Window.norm_absWindowSum_le`, consumed). -/
theorem subWindowSup_le_of_norm_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (H n : ℕ) (β : ℝ) :
    subWindowSup a H n β ≤ (H : ℝ) :=
  subWindowSup_le (fun K hK =>
    le_trans (norm_absWindowSum_le ha K n β) (by exact_mod_cast hK))

/-- **THE `sup'` RECONCILIATION.**  `M4Abel.norm_phase_sum_arcDen_drift_sup` produces the sup
over *endpoints* `K ∈ Icc n (n+H)`; `subWindowSup` is the sup over *lengths* `K ∈ Icc 0 H`.
They are equal — the reindexing `K ↦ K − n` is a bijection of the two `Icc`s, and
`sum_Ioc_phaseCoeff_eq_sub` transports the summand. -/
theorem abel_sup'_eq_subWindowSup (a : ℕ → ℂ) (H n : ℕ) (β : ℝ) :
    (Finset.Icc n (n + H)).sup' ⟨n, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_add_right n H⟩⟩
        (fun K => ‖∑ m ∈ Finset.Ioc n K, phaseCoeff a β m‖)
      = subWindowSup a H n β := by
  refine le_antisymm (Finset.sup'_le _ _ fun K hK => ?_) ?_
  · rw [Finset.mem_Icc] at hK
    rw [sum_Ioc_phaseCoeff_eq_sub a β hK.1]
    exact le_subWindowSup a H n β (by omega)
  · unfold subWindowSup
    refine Finset.sup'_le _ _ fun K hK => ?_
    rw [Finset.mem_Icc] at hK
    rw [absWindowSum_eq_phaseCoeff_sum a K n β]
    exact Finset.le_sup' (f := fun K => ‖∑ m ∈ Finset.Ioc n K, phaseCoeff a β m‖)
      (Finset.mem_Icc.mpr ⟨Nat.le_add_right n K, by omega⟩)

/-! ## §3 — THE DRIFT COMPOSITION

The window sum at a shifted frequency, fed straight into `M4Abel`'s landed payload. -/

/-- **The window sum at `β + θ`, in `M4Abel`'s shape.**  `e((β+θ)m) = e(θm)·e(βm)` term by
term, so the door's window sum at the shifted frequency IS the drift-weighted sum of the
partial-sum family's coefficients — byte-matching
`M4Abel.norm_phase_sum_arcDen_drift`'s `∑ m ∈ Finset.Ioc M N, eR (θ * ↑m) * A m`. -/
theorem absWindowSum_add_eq_phase_sum (a : ℕ → ℂ) (H n : ℕ) (β θ : ℝ) :
    absWindowSum a H n (β + θ)
      = ∑ m ∈ Finset.Ioc n (n + H), eR (θ * (m : ℝ)) * phaseCoeff a β m := by
  unfold absWindowSum phaseCoeff
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [exp_phase_eq_eR, eR_mul_split]
  ring

/-- **THE DRIFT COMPOSITION, split form.**  At a residual frequency `θ` inside the tight
major-arc radius `arcDen/(qH)`, the door window sum at `β + θ` costs the `H`-free factor
`1 + 2π·arcDen/q` over the sub-window sup at `β`.

This is `M4Abel.norm_phase_sum_arcDen_drift` consumed at `M = n`, `N = n + H` (so
`N − M = H` exactly, the half-open window paying) with `A = phaseCoeff a β` and
`B = subWindowSup a H n β`. -/
theorem norm_absWindowSum_le_drift {B₅ : ℝ} {H q n : ℕ} (hq : 0 < q) (hH : 0 < H)
    {β θ : ℝ} (hθ : |θ| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ))) (a : ℕ → ℂ) :
    ‖absWindowSum a H n (β + θ)‖
      ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ))) * subWindowSup a H n β := by
  rw [absWindowSum_add_eq_phase_sum]
  refine norm_phase_sum_arcDen_drift (M := n) (N := n + H) (A := phaseCoeff a β)
    (B := subWindowSup a H n β) (Nat.le_add_right n H) hq hH (by omega) hθ
    (subWindowSup_nonneg a H n β) ?_
  intro K h1 h2
  rw [sum_Ioc_phaseCoeff_eq_sub a β h1]
  exact le_subWindowSup a H n β (by omega)

/-- **THE DRIFT COMPOSITION AT A TIGHT-MAJOR FREQUENCY.**  `NearRatTight (arcDen B₅ H) H α`
delivers `a/q` with `0 < q ≤ arcDen` and `|α − a/q| ≤ arcDen/(qH)`; the window sum at `α` is
then within `1 + 2π·arcDen/q` of the sub-window sup **at the rational** `a/q`.

The witnesses are carried in the conclusion on purpose: the `S(K)` content lives at `b/q`,
where the phase `e(bm/q)` is constant on residue classes mod `q` — so B-1's class-restricted
sums are exactly what may be substituted for it. -/
theorem norm_absWindowSum_le_drift_tight {B₅ : ℝ} {H n : ℕ} (hH : 0 < H) {α : ℝ}
    (hα : NearRatTight (arcDen B₅ H) H α) (a : ℕ → ℂ) :
    ∃ (b : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ arcDen B₅ H ∧
      ‖absWindowSum a H n α‖
        ≤ (1 + 2 * Real.pi * (arcDen B₅ H / (q : ℝ)))
            * subWindowSup a H n ((b : ℝ) / (q : ℝ)) := by
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  refine ⟨b, q, hq, hqQ, ?_⟩
  have h := norm_absWindowSum_le_drift (B₅ := B₅) (H := H) (q := q) (n := n)
    (β := (b : ℝ) / (q : ℝ)) (θ := α - (b : ℝ) / (q : ℝ)) hq hH hd a
  have he : (b : ℝ) / (q : ℝ) + (α - (b : ℝ) / (q : ℝ)) = α := by ring
  rwa [he] at h

/-- The `q`-grading dropped (`q ≥ 1`): against a bound `B` uniform over **all** admissible
rationals and **all** sub-window lengths, the window sum at any tight-major `α` is
`≤ (1 + 2π·arcDen B₅ H)·B`.  This is the shape a supplier that has no `q`-uniformity to
spare will read. -/
theorem norm_absWindowSum_le_ratPartial {B₅ : ℝ} {H n : ℕ} (hH : 0 < H) {α : ℝ}
    (hα : NearRatTight (arcDen B₅ H) H α) (a : ℕ → ℂ) {B : ℝ}
    (hrat : ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen B₅ H → ∀ K, K ≤ H →
      ‖absWindowSum a K n ((b : ℝ) / (q : ℝ))‖ ≤ B) :
    ‖absWindowSum a H n α‖ ≤ (1 + 2 * Real.pi * arcDen B₅ H) * B := by
  obtain ⟨b, q, hq, hqQ, h⟩ := norm_absWindowSum_le_drift_tight hH hα a
  refine h.trans ?_
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : arcDen B₅ H / (q : ℝ) ≤ arcDen B₅ H := div_le_self (arcDen_nonneg B₅ H) hq1
  have hS : subWindowSup a H n ((b : ℝ) / (q : ℝ)) ≤ B :=
    subWindowSup_le (fun K hK => hrat b q hq hqQ K hK)
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hbig : (0 : ℝ) ≤ 1 + 2 * Real.pi * arcDen B₅ H := by
    nlinarith [arcDen_nonneg B₅ H]
  refine mul_le_mul ?_ hS (subWindowSup_nonneg a H n _) hbig
  nlinarith

/-! ## §4 — THE UNIFORMITY HOOK

§3 is pointwise in the door variable `n` with an `n`-independent constant, so it integrates
against `logMeasure`.  Two elementary integral facts are needed; both go through
`ShiftCorr.integral_logMeasure_eq` (the integral IS a finite harmonic sum), so **no
integrability side condition is incurred and no hypothesis on the regime is used**. -/

/-- Monotonicity of the door integral — hypothesis-free (the harmonic weights `1/n` and the
normaliser `Z⁻¹` are nonnegative for every `x`, `ω`). -/
theorem integral_logMeasure_mono {x ω : ℕ} {f g : ℕ → ℝ} (h : ∀ n, f n ≤ g n) :
    (∫ n, f n ∂(logMeasure x ω)) ≤ ∫ n, g n ∂(logMeasure x ω) := by
  rw [integral_logMeasure_eq, integral_logMeasure_eq]
  have hZ : (0 : ℝ) ≤ (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹ :=
    inv_nonneg.mpr (Finset.sum_nonneg fun n _ => by positivity)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hZ
  exact mul_le_mul_of_nonneg_right (h n) (by positivity)

/-- Scalars pass through the door integral. -/
theorem integral_logMeasure_const_mul {x ω : ℕ} (c : ℝ) (f : ℕ → ℝ) :
    (∫ n, c * f n ∂(logMeasure x ω)) = c * ∫ n, f n ∂(logMeasure x ω) := by
  have hs : ∑ n ∈ Finset.Ioc (x / ω) x, c * f n * (n : ℝ)⁻¹
      = c * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [integral_logMeasure_eq, integral_logMeasure_eq, hs]
  ring

/-- **THE SUB-WINDOW-UNIFORM SOCKET** — `M4Close.M4SievedDoorSq`'s obligation, moved to the
sub-window sup at the rational approximant.

Byte-for-byte `M4SievedDoorSq`'s statement with two changes, and only these two:
* the frequency is the *rational* `b/q` (`0 < q ≤ arcDen 12 H`), not the tight-major `α`;
* the integrand is the sup over sub-window lengths `K ≤ H`, not the full window sum.

The band transport is carried as the same premise, so the ⟦A2-5⟧ binder stays visible and is
never unfolded. -/
def M4SievedDoorSqSup (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H →
        (∫ n, (subWindowSup (memSCoeff (calP (Adoor M) (3072 * M))
              (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n ((b : ℝ) / (q : ℝ))) ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (H : ℝ) ^ 2

/-- **THE HOOK — bridge #2's deliverable.**  The sub-window-uniform mean square at the
rationals discharges `M4Close`'s socket, at the drift price `(1 + 2π·arcDen 12 H)²` on the
grade.

The whole of §3 is used once, pointwise in the door variable `n`: the approximant `b/q` is
chosen from `α` alone, so the constant is `n`-free and the bound survives the integral. -/
theorem m4_sievedDoorSq_of_sup {R : ChowlaRegime} {M : ℕ} {Braw Braw' : ℕ → ℝ}
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (1 + 2 * Real.pi * arcDen 12 H) ^ 2 * Braw' H ≤ Braw H)
    (hsup : M4SievedDoorSqSup R M Braw') : M4SievedDoorSq R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  set c := memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC
    with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : arcDen 12 H / (q : ℝ) ≤ arcDen 12 H := div_le_self (arcDen_nonneg 12 H) hq1
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hbig : (0 : ℝ) ≤ 1 + 2 * Real.pi * arcDen 12 H := by
    nlinarith [arcDen_nonneg (12 : ℝ) H]
  -- ⟦the pointwise drift bound, squared⟧
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi * arcDen 12 H) ^ 2 * (subWindowSup c H n β) ^ 2 := by
    intro n
    have h := norm_absWindowSum_le_drift (B₅ := 12) (H := H) (q := q) (n := n)
      (β := β) (θ := α - β) hq hH hd c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    have h2 : ‖absWindowSum c H n α‖ ≤ (1 + 2 * Real.pi * arcDen 12 H) * subWindowSup c H n β := by
      refine h.trans (mul_le_mul ?_ le_rfl (subWindowSup_nonneg c H n β) hbig)
      nlinarith
    calc ‖absWindowSum c H n α‖ ^ 2
        ≤ ((1 + 2 * Real.pi * arcDen 12 H) * subWindowSup c H n β) ^ 2 := by
          gcongr
      _ = (1 + 2 * Real.pi * arcDen 12 H) ^ 2 * (subWindowSup c H n β) ^ 2 := by ring
  -- ⟦the integral, and the grade⟧
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi * arcDen 12 H) ^ 2 * (subWindowSup c H n β) ^ 2
          ∂(logMeasure R.x R.ω) := integral_logMeasure_mono hpt
    _ = (1 + 2 * Real.pi * arcDen 12 H) ^ 2
          * ∫ n, (subWindowSup c H n β) ^ 2 ∂(logMeasure R.x R.ω) :=
        integral_logMeasure_const_mul _ _
    _ ≤ (1 + 2 * Real.pi * arcDen 12 H) ^ 2 * (Braw' H * (H : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsup htr H hlo hhi b q hq hqQ) (sq_nonneg _)
    _ = ((1 + 2 * Real.pi * arcDen 12 H) ^ 2 * Braw' H) * (H : ℝ) ^ 2 := by ring
    _ ≤ Braw H * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (sq_nonneg _)

/-- **THE SUP SOCKET IS INHABITED** (the anti-vacuity duty, mirroring
`M4Close.m4_sievedDoorSq_trivial`).  At the trivial grade `Braw' ≡ 1` every sub-window
carries at most `H` terms of modulus `≤ 1`, so the sup is `≤ H` and its square `≤ H²`; the
door's measure is a probability measure, so the integral inherits the pointwise bound.

So the sup obligation's hypothesis list is satisfiable, and all of its content is the grade.
-/
theorem m4_sievedDoorSqSup_trivial (R : ChowlaRegime) (M : ℕ) :
    M4SievedDoorSqSup R M (fun _ => 1) := by
  intro _ H _ _ _ b q _ _
  refine integral_logMeasure_le_of_le R.hx R.hω (fun n => ?_)
  have hle := subWindowSup_le_of_norm_le_one
    (a := memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) H n
    ((b : ℝ) / (q : ℝ))
  have h0 := subWindowSup_nonneg
    (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    H n ((b : ℝ) / (q : ℝ))
  nlinarith

end Salt.MR
