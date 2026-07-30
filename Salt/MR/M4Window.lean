/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ExitClose
import Salt.Entropy.Chowla.MRTDoor
import Salt.Entropy.Chowla.ShiftCorr

/-!
# M4-0 — the window rewrite at the S7 approximant

The first stone of the MRT §4 port (`docs/exploration/s9-freeze-0726.md`,
⟦AMENDMENT B⟧ row `M4-0`).  Two jobs, and only these two:

1. **The phase re-basing** (`offWindowSum_eq_rebase`, `windowExpSum_eq_rebase`).
   The MRT door's carrier is the *offset-indexed* window sum
   `∑_{i<H} λ(n+i+1) e(α(i+1))` (`windowExpSum`, `MRTDoor.lean:37`); every
   line of MRT §4 is written for the *absolute-indexed* sum
   `∑_{n<m≤n+H} λ(m) e(αm)`.  They differ by the unit-modulus factor `e(−αn)`.
   The freeze (`:151–156`) rules that this modulus-1 factor must be a NAMED
   lemma proved once — "the kernel cannot police a sign consumed only through a
   modulus" — so it is proved here, at a general coefficient sequence
   `a : ℕ → ℂ`, and instantiated at `λ` exactly once.

2. **The arc adapter** (`nearRatTight_of_bigXiArcTight`,
   `mrtUniformityXi_of_absWindowBound`, `…_twelve`).  The S7 gate is DISSOLVED:
   `bigXiArcTight_twelve` (`ExitClose.lean:773`) is landed unconditional, so it
   is CONSUMED here, never re-derived.  The adapter turns the remaining M4
   obligation — a bound on the *absolute-indexed* λ-window sum at every
   tight-major frequency — into the door shape `MRTUniformityXi`
   (`MRTDoor.lean:109`) that the spine head consumes.

## Conventions pinned in this file

* **Half-open**: the absolute window is `Finset.Ioc n (n+H)` = `{n+1,…,n+H}`,
  matching `liouvilleWindow H n i = λ(n+i+1)` term for term (the freeze's
  "inner `Ioc n (n+H)`", `:161`; the endpoint genre is documented at
  `SieveGlue.lean:77–80`).  The re-basing bijection is `i ↦ m = n+i+1`, with no
  `±1` slack anywhere: `Ioc n (n+H)` is *exactly* the image of `Fin H`.
* **One log scale**: this file speaks `log H` and nothing else.  The only
  quantitative object it touches is `arcDen B₅ H = (log H)^{B₅}`
  (`BigXiArc.lean:148`), at the frozen `B₅ = 12`.  No `log X`, no `log x`.
* **The sign seam** fires exactly once, in `nearRatTight_of_bigXiArcTight`:
  `BigXiArcTight` speaks at `+ξ.val/H`, the door at `−ξ.val/H`, and
  `nearRatTight_neg` (`BigXiArc.lean:614`) is the only bridge used.
* **NOT here** (freeze `:274`, and the trap at `:152–156`): no `q ∣ H` clause,
  no exact-denominator route.  The approximant is the tight, `q`-dependent
  Dirichlet radius `|α − a/q| ≤ (log H)^{12}/(qH)` with `q ≤ (log H)^{12}`,
  i.e. `NearRatTight (arcDen 12 H) H α` (`BigXiArc.lean:566`), and nothing
  stronger is assumed or produced.

## What this file does NOT prove

The analytic content — MRT's (4.2) integration by parts (M4-0′) and everything
downstream — is *not* here.  It enters the adapters as the hypothesis `hbd`:
the bound on `∫ ‖absWindowSum lamCoeff H · α‖` over `logMeasure`, uniform over
tight-major `α`.  M4-0 is the transcription seam, and only that.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the two window shapes -/

/-- **The Liouville coefficient sequence**, `ℂ`-valued: `lamCoeff m = λ(m)`.
This is the `a` at which the general re-basing is instantiated. -/
def lamCoeff : ℕ → ℂ := fun m => (ArithmeticFunction.liouville m : ℂ)

/-- `λ` is 1-bounded (unconditionally: `λ(0) = 0`, and `λ(m) = ±1` for `m ≠ 0`). -/
theorem norm_lamCoeff_le_one (m : ℕ) : ‖lamCoeff m‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [lamCoeff]
  · have hm0 : m ≠ 0 := by omega
    rw [lamCoeff, ArithmeticFunction.liouville_apply hm0]
    push_cast
    simp

/-- **The offset-indexed window sum** at a general coefficient sequence:
`∑_{i<H} a(n+i+1) e(α(i+1))`.  At `a = lamCoeff` this is `windowExpSum H n α`
(`windowExpSum_eq_offWindowSum`) — the shape the MRT door quantifies. -/
def offWindowSum (a : ℕ → ℂ) (H n : ℕ) (α : ℝ) : ℂ :=
  ∑ i : Fin H, a (n + (i : ℕ) + 1) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (((i : ℕ) : ℂ) + 1))

/-- **The absolute-indexed window sum**: `∑_{n<m≤n+H} a(m) e(αm)`, on the
half-open window `Ioc n (n+H)`.  This is the shape MRT §4 is written in. -/
def absWindowSum (a : ℕ → ℂ) (H n : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc n (n + H), a m *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))

/-- The door's carrier is the offset-indexed sum at `λ`: definitional unfolding
of `windowExpSum` through `liouvilleWindow H n i = λ(n+i+1)`. -/
theorem windowExpSum_eq_offWindowSum (H n : ℕ) (α : ℝ) :
    windowExpSum H n α = offWindowSum lamCoeff H n α := by
  unfold windowExpSum offWindowSum lamCoeff
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [liouvilleWindow_apply]

/-! ## §2 — the phase re-basing (the freeze's NAMED modulus-1 lemma) -/

/-- The phase algebra behind the re-basing, one term: `e(−αn)·e(αm) = e(α(m−n))`
evaluated at `m = n+i+1`, where `m − n = i+1`.  Pure `Complex.exp_add`; the
`push_cast` is the `ℕ → ℂ` transport of `m = n+i+1`. -/
private lemma exp_rebase_step (α : ℝ) (n i : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-α : ℝ) : ℂ) * ((n : ℕ) : ℂ))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (((n + i + 1 : ℕ) : ℂ)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (((i : ℕ) : ℂ) + 1)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The half-open window `Ioc n (n+H)` is *exactly* the image of `Fin H` under
the re-basing map `i ↦ n+i+1`.  This is the endpoint bookkeeping in one place:
no `±1` slack is created or absorbed anywhere else in the file. -/
theorem Ioc_eq_map_rebase (H n : ℕ) :
    Finset.Ioc n (n + H)
      = (Finset.univ : Finset (Fin H)).map
          ⟨fun i : Fin H => n + (i : ℕ) + 1, by
            intro x y hxy
            dsimp only at hxy
            exact Fin.val_injective (by omega)⟩ := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨m - n - 1, by omega⟩, ?_⟩
    change n + (m - n - 1) + 1 = m
    omega
  · rintro ⟨i, rfl⟩
    have := i.isLt
    omega

/-- **THE PHASE RE-BASING LEMMA** (freeze `:151–156`), at a general coefficient
sequence `a : ℕ → ℂ`:

`∑_{i<H} a(n+i+1) e(α(i+1)) = e(−αn) · ∑_{n<m≤n+H} a(m) e(αm)`.

The offset-indexed window sum equals the absolute-indexed one times the
unit-modulus factor `e(−αn)`.  Proved once, here; every later reference is to
this name.  No hypothesis on `a` (1-boundedness is only needed downstream, and
enters through `norm_absWindowSum_le`). -/
theorem offWindowSum_eq_rebase (a : ℕ → ℂ) (H n : ℕ) (α : ℝ) :
    offWindowSum a H n α
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-α : ℝ) : ℂ) * ((n : ℕ) : ℂ))
        * absWindowSum a H n α := by
  unfold offWindowSum absWindowSum
  rw [Ioc_eq_map_rebase H n, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [← exp_rebase_step α n (i : ℕ)]
  ring

/-- **The re-basing at `λ`** — the door's carrier, absolutely indexed:
`windowExpSum H n α = e(−αn) · ∑_{n<m≤n+H} λ(m) e(αm)`. -/
theorem windowExpSum_eq_rebase (H n : ℕ) (α : ℝ) :
    windowExpSum H n α
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-α : ℝ) : ℂ) * ((n : ℕ) : ℂ))
        * absWindowSum lamCoeff H n α := by
  rw [windowExpSum_eq_offWindowSum, offWindowSum_eq_rebase]

/-! ## §3 — the modulus, and the trivial bound -/

/-- The additive phase `e(βk)` has modulus 1 (`β : ℝ`, `k : ℕ`) — the single
place this file inspects a real part. -/
private lemma norm_exp_phase (β : ℝ) (k : ℕ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The re-basing is invisible to the door, which only ever sees a modulus. -/
theorem norm_offWindowSum (a : ℕ → ℂ) (H n : ℕ) (α : ℝ) :
    ‖offWindowSum a H n α‖ = ‖absWindowSum a H n α‖ := by
  rw [offWindowSum_eq_rebase, norm_mul, norm_exp_phase, one_mul]

/-- **The door-integrand rewrite**: `‖windowExpSum H n α‖ = ‖∑_{n<m≤n+H} λ(m)
e(αm)‖`.  This is what passes under `∫ · ∂(logMeasure)` in the adapters. -/
theorem norm_windowExpSum_eq_absWindowSum (H n : ℕ) (α : ℝ) :
    ‖windowExpSum H n α‖ = ‖absWindowSum lamCoeff H n α‖ := by
  rw [windowExpSum_eq_offWindowSum, norm_offWindowSum]

/-- **The trivial bound** at a 1-bounded coefficient sequence: `H` terms of
modulus `≤ 1`.  (The `Ioc n (n+H)` card is `H` on the nose — the half-open
convention paying off.) -/
theorem norm_absWindowSum_le {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (H n : ℕ) (α : ℝ) :
    ‖absWindowSum a H n α‖ ≤ (H : ℝ) := by
  unfold absWindowSum
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ Finset.Ioc n (n + H),
      ‖a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))‖ ≤ 1 := by
    intro m _
    rw [norm_mul, norm_exp_phase, mul_one]
    exact ha m
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp [Nat.card_Ioc]

/-- The trivial bound at `λ`, in the door's own carrier. -/
theorem norm_windowExpSum_le (H n : ℕ) (α : ℝ) : ‖windowExpSum H n α‖ ≤ (H : ℝ) := by
  rw [norm_windowExpSum_eq_absWindowSum]
  exact norm_absWindowSum_le norm_lamCoeff_le_one H n α

/-! ## §4 — the arc adapter (consuming `BigXiArcTight`) -/

/-- **The sign seam, fired once.**  `BigXiArcTight B₅` states the tight
Dirichlet approximant at `+ξ.val/H`; the MRT door is fired at `−ξ.val/H`
(`MRTDoor.lean:102, 110`).  `nearRatTight_neg` (`BigXiArc.lean:614`) transports
it, the witness denominator `q` unchanged.  This is the only place in the M4
chain where the door frequency's sign is touched. -/
theorem nearRatTight_of_bigXiArcTight {B₅ : ℝ} (harc : BigXiArcTight B₅)
    {eps : ℚ} (heps : 0 < eps) :
    ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXi eps H,
      NearRatTight (arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
  obtain ⟨H₀, hH₀⟩ := harc eps heps
  refine ⟨H₀, ?_⟩
  intro H _ hH ξ hξ
  rw [neg_div]
  exact nearRatTight_neg.mpr (hH₀ H hH ξ hξ)

/-- **THE M4 DOOR ADAPTER.**  Given

* an arc supply at floor `H₀` (every large-spectrum door frequency `−ξ.val/H`
  is tight-major with denominator cap `arcDen B₅ H`), with `H₀` under the
  regime's window floor, and
* the M4 analytic obligation `hbd`: at *every* tight-major `α`, the
  absolute-indexed λ-window sum has `logMeasure`-`L¹` norm `≤ δH`,

the `Ξ_H`-restricted MRT door `MRTUniformityXi R δ` holds.  The `∀ ξ`-outside
doctrine is preserved verbatim: `hbd`'s `∀ α` is outside its integral, and the
conclusion's `∀ ξ` is outside the door's.

Binder shapes are byte-matched to `MRTUniformityXi` (`MRTDoor.lean:109–111`):
`∀ H, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → …`. -/
theorem mrtUniformityXi_of_absWindowBound (R : ChowlaRegime) (δ : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXi R.eps H,
      NearRatTight (arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hbd : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)) :
    MRTUniformityXi R δ := by
  intro H _ hlo hhi ξ hξ
  have hrw : (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ∂(logMeasure R.x R.ω))
      = ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))‖ ∂(logMeasure R.x R.ω) :=
    integral_congr_ae (Filter.Eventually.of_forall
      (fun n => norm_windowExpSum_eq_absWindowSum H n (-(ξ.val : ℝ) / (H : ℝ))))
  rw [hrw]
  exact hbd H hlo hhi _ (harc H (le_trans hfloor hlo) ξ hξ)

/-- **The adapter at the frozen exponent `B₅ = 12`**, with the S7 gate
DISSOLVED: `bigXiArcTight_twelve` (`ExitClose.lean:773`, unconditional) supplies
the arc.

Non-vacuity: `H₀` is produced from `ε` alone, *before* the regime — matching
`log_chowla_two_budget_head`'s `∀ extraFloor : ℕ, ∃ R, R.eps = ε ∧ extraFloor ≤
R.Hlo` interface (`SpineFinal.lean:749`), which is exactly how the head is asked
to place a floor.  (Stating it as `∃ H₀, H₀ ≤ R.Hlo → …` for a *given* `R` would
be vacuous — take `H₀ := R.Hlo + 1`.) -/
theorem mrtUniformityXi_of_absWindowBound_twelve (eps : ℚ) (heps : 0 < eps) :
    ∃ H₀ : ℕ, ∀ R : ChowlaRegime, R.eps = eps → H₀ ≤ R.Hlo → ∀ δ : ℝ,
      (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
        NearRatTight (arcDen 12 H) H α →
          (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)) →
        MRTUniformityXi R δ := by
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiArcTight bigXiArcTight_twelve heps
  refine ⟨H₀, fun R hReps hfloor δ hbd => ?_⟩
  refine mrtUniformityXi_of_absWindowBound R δ hfloor ?_ hbd
  intro H _ hH ξ hξ
  rw [hReps] at hξ
  exact hH₀ H hH ξ hξ

/-! ## §5 — THE `L²`-SUMMED ARC ADAPTER (⟦THE L² RESTRUCTURE⟧, stone 6)

The `L²` twin of §4.  §4 hands the door one frequency at a time and pays a full
`δ` at each of the `|Ξ_H| ≤ K` of them; the restructure
(`docs/exploration/l2-restructure-freeze-0730.md`) keeps the second Fourier
factor and so reads the whole `Ξ_H`-SUM at once, at the SQUARED scale:

    Σ_{ξ∈Ξ_H} (1/H²)∫‖windowExpSum(−ξ.val/H)‖² dμ ≤ K·(2·Bsieve) + 2·Binsert.

Two things about that line, and they are the whole point:

* **The count `K` multiplies ONLY the sieved (α-dependent) leg.**  The socket's
  grade `Bsieve H` is a bound at *each* tight-major `α`, so summing it over `Ξ_H`
  costs the cardinality — that is the `K`.
* **The insert leg is paid ONCE.**  `Binsert` bounds the *already-summed*
  insert energy: the raw−sieved difference is `α`-INDEPENDENT, so its total
  Fourier mass is a single object (⟦the refuter's α-independence census⟧: the
  two `α`-independent debits, the glue `δ/4` and the tail `4·2^k/x`, are ONE
  object and ride together).  No `K` multiplies it.  Supplying `Binsert` is the
  Parseval stone's job (the sibling `parseval_insert_budget_door`); this stone
  takes it as the named hypothesis `hins` and never opens it.

The split is the refuter's re-derivation `(a+b)² ≤ 2a² + 2b²` — hence the two
`2`s, and hence `2·K·Bsieve` (not `K·Bsieve`) in the freeze's budget line.

⟦THE FUSE, LIVE⟧ The conclusion is byte-shaped to the payload of
`MRTUniformityXiL2` (`MRTDoor.lean:187`, the sibling stone, LANDED): Σ-form,
`(1/H²)` normalisation, `‖·‖ ^ 2`, the `∀ ξ` *inside* the Σ and the Σ *outside*
the integral — the MRTDoor seam warning applies verbatim, this is a finite sum
of integrals with no sup inside, implied by the per-`α` door.
`mrtUniformityXiL2_of_absWindowSqBound` below closes onto that predicate; the
only thing it owes beyond this adapter is `hρ`, an `H`-uniform ceiling for the
`H`-dependent right-hand side `K·(2·Bsieve H) + 2·Binsert`.

⟦THE INSERT SUPPLIER⟧ `Binsert` is supplied by
`Salt.MR.parseval_insert_budget_door` (`M4ParsevalStone.lean:341`), which is
DOWNSTREAM of this file (it imports `M4Window`).  So the budget cannot be cited
here and enters as the named hypothesis `hins`; the composition is stone 7's.
`…_parseval` below states `hins` in that supplier's exact spelling — `(1/H²)`
outside the Σ, integrand the *difference of two window sums* — so the plug is
byte-for-byte. -/

/-- `absWindowSum` is additive in its coefficient sequence (the window and the
phase are shared; only the coefficient splits). -/
theorem absWindowSum_add_coeff (a e : ℕ → ℂ) (H n : ℕ) (α : ℝ) :
    absWindowSum (fun m => a m + e m) H n α
      = absWindowSum a H n α + absWindowSum e H n α := by
  unfold absWindowSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **The refuter's split, pointwise**: `‖u+v‖² ≤ 2‖u‖² + 2‖v‖²` at the door's
carrier.  This is the ONLY place the restructure's factor `2` is created. -/
theorem norm_absWindowSum_sq_split (a e : ℕ → ℂ) (H n : ℕ) (α : ℝ) :
    ‖absWindowSum (fun m => a m + e m) H n α‖ ^ 2
      ≤ 2 * ‖absWindowSum a H n α‖ ^ 2 + 2 * ‖absWindowSum e H n α‖ ^ 2 := by
  rw [absWindowSum_add_coeff]
  have htri := norm_add_le (absWindowSum a H n α) (absWindowSum e H n α)
  have h0 := norm_nonneg (absWindowSum a H n α)
  have h1 := norm_nonneg (absWindowSum e H n α)
  nlinarith [sq_nonneg (‖absWindowSum a H n α‖ - ‖absWindowSum e H n α‖),
    norm_nonneg (absWindowSum a H n α + absWindowSum e H n α)]

/-- The split, integrated against the door's measure.  Proved through
`ShiftCorr.integral_logMeasure_eq` (the integral IS a finite harmonic sum), so
**no integrability side condition is incurred** — the route every `logMeasure`
inequality in the M4 chain takes. -/
theorem integral_norm_absWindowSum_sq_split (x ω H : ℕ) (a e : ℕ → ℂ) (α : ℝ) :
    (∫ n, ‖absWindowSum (fun m => a m + e m) H n α‖ ^ 2 ∂(logMeasure x ω))
      ≤ 2 * (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure x ω))
        + 2 * ∫ n, ‖absWindowSum e H n α‖ ^ 2 ∂(logMeasure x ω) := by
  rw [integral_logMeasure_eq, integral_logMeasure_eq, integral_logMeasure_eq]
  have hZ : (0 : ℝ) ≤ (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹ :=
    inv_nonneg.mpr (Finset.sum_nonneg fun n _ => by positivity)
  have hkey : (∑ n ∈ Finset.Ioc (x / ω) x,
        ‖absWindowSum (fun m => a m + e m) H n α‖ ^ 2 * (n : ℝ)⁻¹)
      ≤ 2 * (∑ n ∈ Finset.Ioc (x / ω) x, ‖absWindowSum a H n α‖ ^ 2 * (n : ℝ)⁻¹)
        + 2 * ∑ n ∈ Finset.Ioc (x / ω) x, ‖absWindowSum e H n α‖ ^ 2 * (n : ℝ)⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hpt := norm_absWindowSum_sq_split a e H n α
    nlinarith
  calc (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
        * ∑ n ∈ Finset.Ioc (x / ω) x,
            ‖absWindowSum (fun m => a m + e m) H n α‖ ^ 2 * (n : ℝ)⁻¹
      ≤ (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * (2 * (∑ n ∈ Finset.Ioc (x / ω) x, ‖absWindowSum a H n α‖ ^ 2 * (n : ℝ)⁻¹)
            + 2 * ∑ n ∈ Finset.Ioc (x / ω) x,
                ‖absWindowSum e H n α‖ ^ 2 * (n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hkey hZ
    _ = 2 * ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
            * ∑ n ∈ Finset.Ioc (x / ω) x, ‖absWindowSum a H n α‖ ^ 2 * (n : ℝ)⁻¹)
          + 2 * ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
            * ∑ n ∈ Finset.Ioc (x / ω) x, ‖absWindowSum e H n α‖ ^ 2 * (n : ℝ)⁻¹) := by
        ring

/-- **THE `L²`-SUMMED ARC ADAPTER.**  Given

* the arc supply at floor `H₀` (`harc`: every large-spectrum door frequency
  `−ξ.val/H` is tight-major with denominator cap `arcDen B₅ H`), with `H₀` under
  the regime's window floor — the SAME gate §4 rides, unweakened;
* the coefficient split `hsplit : λ = a + e` (`a` the sieved sequence the road's
  `L²` socket speaks about, `e` its α-independent insert complement);
* `hB0`: the socket's grade is a grade;
* the road's `L²` socket `hsock` — `M4Close.M4SievedDoorSq`'s per-`α` shape
  (`M4Close.lean:368–375`) transcribed at the abstract coefficient sequence `a`,
  because `M4SievedDoorSq` is defined DOWNSTREAM of this file and is instantiated
  by the consumer;
* `hXi`: the large-spectrum count gate `|Ξ_H| ≤ K` (`bigXi_bounded`'s payload);
* `hins`: the **already-summed** insert budget `Binsert` (the Parseval stone),

the `Ξ_H`-summed `L²` door bound holds at `K·(2·Bsieve H) + 2·Binsert`.

`K` multiplies the sieved leg ONLY; `Binsert` is paid once.  Every gate is
named: no floor, no count and no grade is smuggled. -/
theorem sum_bigXi_norm_windowExpSum_sq_le (R : ChowlaRegime) (a e : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hsplit : ∀ m, lamCoeff m = a m + e m)
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXi R.eps H,
      NearRatTight (arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXi R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Binsert) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert := by
  intro H _ hlo hhi
  have hH0 : H ≠ 0 := NeZero.ne H
  have hHpos : (0 : ℝ) < (H : ℝ) := by positivity
  have hinvpos : (0 : ℝ) < 1 / (H : ℝ) ^ 2 := by positivity
  have hfun : lamCoeff = fun m => a m + e m := funext hsplit
  -- ⟦the per-frequency line⟧ arc → socket → the `(a+b)²` split, at one `ξ`.
  have hterm : ∀ ξ ∈ bigXi R.eps H,
      (1 / (H : ℝ) ^ 2) * (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ 2 * Bsieve H + 2 * ((1 / (H : ℝ) ^ 2) *
            ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω)) := by
    intro ξ hξ
    have harcξ := harc H (le_trans hfloor hlo) ξ hξ
    have hrw : (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        = ∫ n, ‖absWindowSum (fun m => a m + e m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasure R.x R.ω) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
      simp only [norm_windowExpSum_eq_absWindowSum, hfun]
    rw [hrw]
    have hspl := integral_norm_absWindowSum_sq_split R.x R.ω H a e (-(ξ.val : ℝ) / (H : ℝ))
    have hs := hsock H hlo hhi (-(ξ.val : ℝ) / (H : ℝ)) harcξ
    have hA : (1 / (H : ℝ) ^ 2) * (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
        ∂(logMeasure R.x R.ω)) ≤ Bsieve H := by
      have h := mul_le_mul_of_nonneg_left hs hinvpos.le
      have heq : (1 / (H : ℝ) ^ 2) * (Bsieve H * (H : ℝ) ^ 2) = Bsieve H := by
        field_simp
      linarith [h, heq.le, heq.ge]
    have hmul := mul_le_mul_of_nonneg_left hspl hinvpos.le
    have hexp : (1 / (H : ℝ) ^ 2) *
        (2 * (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))
          + 2 * ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))
        = 2 * ((1 / (H : ℝ) ^ 2) * ∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))
          + 2 * ((1 / (H : ℝ) ^ 2) * ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω)) := by ring
    rw [hexp] at hmul
    linarith
  -- ⟦the census⟧ the sieved leg pays the count `K`; the insert leg pays once.
  have hcard := hXi H hlo hhi
  have hI := hins H hlo hhi
  have h2B : (0 : ℝ) ≤ 2 * Bsieve H := by have := hB0 H; linarith
  have hKB := mul_le_mul_of_nonneg_right hcard h2B
  calc (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
          ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∑ _ξ ∈ bigXi R.eps H, (2 * Bsieve H + 2 * ((1 / (H : ℝ) ^ 2) *
          ∫ n, ‖absWindowSum e H n (-(_ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasure R.x R.ω))) := Finset.sum_le_sum hterm
    _ = ((bigXi R.eps H).card : ℝ) * (2 * Bsieve H)
          + 2 * ∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
              ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
                ∂(logMeasure R.x R.ω) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    _ ≤ K * (2 * Bsieve H) + 2 * Binsert := by linarith

/-- **The adapter at the subtractive spelling of the split** — for a supplier
whose insert leg is delivered as `λ − a` rather than as a named `e`.  Same
theorem; `hsplit` is discharged by `ring`. -/
theorem sum_bigXi_norm_windowExpSum_sq_le_sub (R : ChowlaRegime) (a : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXi R.eps H,
      NearRatTight (arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXi R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum (fun m => lamCoeff m - a m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Binsert) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert :=
  sum_bigXi_norm_windowExpSum_sq_le R a (fun m => lamCoeff m - a m) Bsieve K Binsert
    (fun m => by ring) hfloor harc hB0 hsock hXi hins

/-- **The adapter at the Parseval stone's own spelling** — the byte-plug for
`parseval_insert_budget_door` (`M4ParsevalStone.lean:341`), whose exit carries
the `(1/H²)` OUTSIDE the `ξ`-sum and whose integrand is the *difference of two
window sums* `absWindowSum λ − absWindowSum a`, not a window sum of a difference
sequence.  The two spellings are identified through `absWindowSum_add_coeff` and
`Finset.mul_sum`; no new analysis. -/
theorem sum_bigXi_norm_windowExpSum_sq_le_parseval (R : ChowlaRegime) (a : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXi R.eps H,
      NearRatTight (arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXi R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXi R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω) ≤ Binsert) :
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
        ≤ K * (2 * Bsieve H) + 2 * Binsert := by
  refine sum_bigXi_norm_windowExpSum_sq_le_sub R a Bsieve K Binsert hfloor harc hB0
    hsock hXi ?_
  intro H _ hlo hhi
  have hsub : ∀ (n : ℕ) (α : ℝ),
      absWindowSum (fun m => lamCoeff m - a m) H n α
        = absWindowSum lamCoeff H n α - absWindowSum a H n α := by
    intro n α
    have h := absWindowSum_add_coeff a (fun m => lamCoeff m - a m) H n α
    have hfun : (fun m => a m + (lamCoeff m - a m)) = lamCoeff := funext fun m => by ring
    rw [hfun] at h
    rw [h]
    ring
  have hcongr : (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum (fun m => lamCoeff m - a m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
      = (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXi R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    simp only [hsub]
  rw [hcongr]
  exact hins H hlo hhi

/-- **The `L²` adapter at the frozen exponent `B₅ = 12`**, the arc gate
DISSOLVED exactly as in §4: `bigXiArcTight_twelve` (`ExitClose.lean:773`,
unconditional) supplies it, `nearRatTight_of_bigXiArcTight` transports the sign.

Non-vacuity is §4's, verbatim: `H₀` is produced from `ε` alone, BEFORE the
regime, matching `log_chowla_two_budget_head`'s `∀ extraFloor, ∃ R, …` interface
(`SpineFinal.lean:749`).  Stating it as `∃ H₀, H₀ ≤ R.Hlo → …` for a *given* `R`
would be vacuous. -/
theorem sum_bigXi_norm_windowExpSum_sq_le_twelve (eps : ℚ) (heps : 0 < eps) :
    ∃ H₀ : ℕ, ∀ R : ChowlaRegime, R.eps = eps → H₀ ≤ R.Hlo →
      ∀ (a e : ℕ → ℂ) (Bsieve : ℕ → ℝ) (K Binsert : ℝ),
        (∀ m, lamCoeff m = a m + e m) →
        (∀ H : ℕ, 0 ≤ Bsieve H) →
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
          NearRatTight (arcDen 12 H) H α →
            (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
              ≤ Bsieve H * (H : ℝ) ^ 2) →
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          ((bigXi R.eps H).card : ℝ) ≤ K) →
        (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
            ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω)) ≤ Binsert) →
        ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
          (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
            ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
              ∂(logMeasure R.x R.ω))
            ≤ K * (2 * Bsieve H) + 2 * Binsert := by
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiArcTight bigXiArcTight_twelve heps
  refine ⟨H₀, fun R hReps hfloor a e Bsieve K Binsert hsplit hB0 hsock hXi hins => ?_⟩
  refine sum_bigXi_norm_windowExpSum_sq_le R a e Bsieve K Binsert hsplit hfloor ?_
    hB0 hsock hXi hins
  intro H _ hH ξ hξ
  rw [hReps] at hξ
  exact hH₀ H hH ξ hξ

/-- **THE CLOSE ONTO THE SUMMED DOOR** — this adapter, delivered as the sibling
stone's predicate `MRTUniformityXiL2 R ρ` (`MRTDoor.lean:187`).

`hρ` is the one thing the adapter itself cannot supply: the door's grade `ρ` is
`H`-free, while the adapter's right-hand side carries the socket grade at the
running `H`.  Any `H`-uniform ceiling over the window range `[R.Hlo, R.Hhi]`
does it — on the road that ceiling is the pricing's monotone bound on `Braw`.

Note what is NOT here: no `|Ξ_H| ≤ K` hypothesis is consumed by the *seam*
(`contradiction_of_mrtDoorXiL2` has none).  The count is consumed HERE, once,
against the sieved leg only — the `K`-free `δ` of the freeze's budget line. -/
theorem mrtUniformityXiL2_of_absWindowSqBound (R : ChowlaRegime) (a e : ℕ → ℂ)
    (Bsieve : ℕ → ℝ) (K Binsert ρ : ℝ) {B₅ : ℝ} {H₀ : ℕ}
    (hsplit : ∀ m, lamCoeff m = a m + e m)
    (hfloor : H₀ ≤ R.Hlo)
    (harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXi R.eps H,
      NearRatTight (arcDen B₅ H) H (-(ξ.val : ℝ) / (H : ℝ)))
    (hB0 : ∀ H : ℕ, 0 ≤ Bsieve H)
    (hsock : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen B₅ H) H α →
        (∫ n, ‖absWindowSum a H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
          ≤ Bsieve H * (H : ℝ) ^ 2)
    (hXi : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      ((bigXi R.eps H).card : ℝ) ≤ K)
    (hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum e H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)) ≤ Binsert)
    (hρ : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → K * (2 * Bsieve H) + 2 * Binsert ≤ ρ) :
    MRTUniformityXiL2 R ρ := by
  intro H _ hlo hhi
  exact le_trans (sum_bigXi_norm_windowExpSum_sq_le R a e Bsieve K Binsert hsplit hfloor
    harc hB0 hsock hXi hins H hlo hhi) (hρ H hlo hhi)

/-- **THE FREEZE'S BUDGET LINE, named** (`l2-restructure-freeze-0730.md:21`).
At the insert budget `Binsert := δ/4 + 4·2^k/x` — the glue spelling the `L¹`
road already carries (`M4Close.lean:506`, `M4ClassPrice.lean:708`) — this
adapter's right-hand side IS `2·K·Braw + δ/2 + 8·2^k/x`.  The `δ` the summed
door reads is therefore `K`-FREE, which is the entire content of the
restructure. -/
theorem l2_budget_line (K B δ x : ℝ) (k : ℕ) :
    K * (2 * B) + 2 * (δ / 4 + 4 * 2 ^ k / x) = 2 * K * B + δ / 2 + 8 * 2 ^ k / x := by
  ring

end Salt.MR
