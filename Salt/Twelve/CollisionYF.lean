/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.CollisionQuantW
import Salt.Maynard.CrossCollision
import Salt.Maynard.CollisionQuant
import Salt.Twelve.QdiagBridge

/-!
# Node B (NB-1) — the non-tensor S₁ collision bound for Maynard's weight `yF`

Design: `docs/blueprints/explicit12-design.md`, card **NB-1**.  The goal is the
frozen deliverable

```
collision_yF_le : |s1CollisionForm 5 R W' (yF R W' F)|
    ≤ (12·5²/D) · ∑_r 1/∏φ(rᵢ)
```

via constant-tensor domination: `yF` is bounded (`|yF r| ≤ 1` when `Qabs F ≤ 1`,
landed `yF_abs_le_Qabs`), so `|yF r| ≤ ONEw r` where `ONEw` is the constant
tensor (`f₀ ≡ 1`).  The signed collision form is dominated by the **absolute**
collision majorant `s1AbsCollisionForm`, which is monotone in `|y|`, so

```
|s1CollisionForm (yF)| ≤ s1AbsCollisionForm (yF) ≤ s1AbsCollisionForm ONEw
```

(the `μ`-signs on `lam` make `s1AbsCollisionForm ONE ≠ s1CollisionForm ONE`, so
the majorant is the correct object — see the mono chain below).

## What lands here (sorry-free, axiom-clean)

* `ONEw` (frozen def), `ONEw_nonneg`, `yF_abs_le_ONEw`.
* `wSum_abs_le`, `lam_abs_mono`, `s1AbsCollisionForm_mono` — the `|y|`-monotonicity
  of the absolute collision majorant.
* `collision_yF_le_of_innerYF` (reduction **A′**, RECOMMENDED) — `collision_yF_le`
  FOLLOWS from the canonical inner atom `S1InnerBound 5 R W' (yF)` by black-boxing
  the landed `collision_lower_orderW_of` (no assembly copy).  The atom is a
  genuinely TRUE per-assignment bound; it is the exact thing Node A abstracts.
* `collision_yF_le_of_absONE` (reduction **B**, the design's mono chain) —
  `collision_yF_le` FOLLOWS from `s1AbsCollisionForm ONEw ≤ (12·5²/D)·∑1/∏φ`.

`collision_yF_le` itself is NOT landed unconditionally: both atoms are the same
`private`-helper balloon (below).  Reduction A′ isolates the *canonical* atom and
is the preferred entry point.

## The remaining atom (FLAGGED — a genuine balloon past a `private` wall)

The reduction bottoms out at `s1AbsCollisionForm 5 R W' (ONEw) ≤ 12k²/D·M`
(`M = ∑1/∏φ`).  This does NOT reduce to the landed `inner_abs_le` /
`collision_lower_orderW_of`: those bound the SIGNED collision form
`|s1CollisionForm|` (via the Möbius `t`-expansion), or — internally — the
`(u)`-level termwise majorant `∑_u |∏φ·ŷ_fst·ŷ_snd|`.  Neither equals the
`(d,e)`-level majorant `s1AbsCollisionForm` (the `inner_exact` diagonalisation
that turns the collision form into the `u`-sum is a signed identity; `|·|`
breaks it).  Closing the atom requires the CORRECT route A′:

  * a TERMWISE variant of `inner_abs_le` — its own proof from `hterm` onward,
    concluding `∑_u |∏φ·ŷ_fst·ŷ_snd| ≤ 3^ω·∏(p−1)⁻²·yside` (the first
    `abs_sum_le_sum_abs` step of `inner_abs_le` DROPPED) — at `f₀ ≡ 1`, plus
  * a constant-`M` copy of `collision_lower_orderW_of`
    (`S1InnerBound`'s `yside` replaced by a free `B ≥ 0`),

both of which live behind the `private` helpers `yhat_side_le`, `erasure_bound`,
`erase_branch` in `CollisionQuant.lean` and so cannot be reused from here — a
~1000-line re-derivation.  Recommended fix (Fable/statement-tier): expose an
`inner_abs_termwise_le` and an `S1InnerBoundConst`-parameterised assembly in the
Maynard track, after which `collision_yF_le` is a two-line corollary of
`collision_yF_le_of_absONE` (the mono chain is done here).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Twelve

open Salt.Maynard

/-- **NB-1 constant tensor.** `ONEw R W' r = 1` on the sieve box, `0` off it —
the `f₀ ≡ 1` tensor that majorises `|yF|` (a legal divisor-decreasing tensor:
`1 ≤ 1`). -/
def ONEw (R W' : ℕ) : (Fin 5 → ℕ) → ℝ :=
  fun r => if r ∈ kSieveIndex 5 R W' then 1 else 0

/-- `ONEw` is nonnegative. -/
theorem ONEw_nonneg (R W' : ℕ) (r : Fin 5 → ℕ) : 0 ≤ ONEw R W' r := by
  unfold ONEw; split_ifs <;> norm_num

/-- **Step 4 (pointwise domination).** With `Qabs F ≤ 1`, Maynard's weight is
dominated by the constant tensor: `|yF R W' F r| ≤ ONEw R W' r`.  On the box
`|yF| ≤ Qabs F ≤ 1 = ONEw`; off the box both sides are `0`. -/
theorem yF_abs_le_ONEw (R W' : ℕ) (F : Poly) (hQ : Qabs F ≤ 1) (r : Fin 5 → ℕ) :
    |yF R W' F r| ≤ ONEw R W' r := by
  unfold ONEw
  split_ifs with hr
  · calc |yF R W' F r| ≤ ((Qabs F : ℚ) : ℝ) := yF_abs_le_Qabs R W' F r
      _ ≤ 1 := by exact_mod_cast hQ
  · rw [show yF R W' F r = 0 from by unfold yF; rw [if_neg hr]]
    rw [abs_zero]

/-! ## The `|y|`-monotonicity of the absolute collision majorant -/

/-- The divisor-shifted inner sum is dominated in absolute value by the
`|y|`-majorant's inner sum: `|wSum y₁ u| ≤ wSum y₂ u` whenever `|y₁ r| ≤ y₂ r`
pointwise.  (The hypothesis forces `y₂ r ≥ |y₁ r| ≥ 0`, so `wSum y₂ u ≥ 0`.) -/
theorem wSum_abs_le {k R W : ℕ} {y₁ y₂ : (Fin k → ℕ) → ℝ}
    (hle : ∀ r, |y₁ r| ≤ y₂ r) (u : Fin k → ℕ) :
    |wSum k R W y₁ u| ≤ wSum k R W y₂ u := by
  unfold wSum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro r hr
  have hφ : (0 : ℝ) ≤ ∏ i, (Nat.totient (r i) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  split_ifs with h
  · rw [abs_div, abs_of_nonneg hφ]
    exact div_le_div_of_nonneg_right (hle r) hφ
  · rw [abs_zero]

/-- **Step 3 core (`lam_abs_mono`).** `|lam y₁ d| ≤ |lam y₂ d|` whenever
`|y₁ r| ≤ y₂ r` pointwise: `lam y d = (∏ᵢ μ(dᵢ)dᵢ)·wSum y d`, and the `μ`/`d`
prefactor cancels in the ratio, leaving `|wSum y₁ d| ≤ |wSum y₂ d|`
(`wSum_abs_le` + `le_abs_self`). -/
theorem lam_abs_mono {k R W : ℕ} {y₁ y₂ : (Fin k → ℕ) → ℝ}
    (hle : ∀ r, |y₁ r| ≤ y₂ r) (d : Fin k → ℕ) :
    |lam k R W y₁ d| ≤ |lam k R W y₂ d| := by
  unfold lam
  rw [abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact le_trans (wSum_abs_le hle d) (le_abs_self _)

/-- **Step 3 (`s1AbsCollisionForm_mono`).** The absolute collision majorant is
monotone in `|y|`: `s1AbsCollisionForm y₁ ≤ s1AbsCollisionForm y₂` whenever
`|y₁ r| ≤ y₂ r` pointwise.  Termwise via `lam_abs_mono` (numerator monotone,
`∏lcm ≥ 0`). -/
theorem s1AbsCollisionForm_mono {k R W : ℕ} {y₁ y₂ : (Fin k → ℕ) → ℝ}
    (hle : ∀ r, |y₁ r| ≤ y₂ r) :
    s1AbsCollisionForm k R W y₁ ≤ s1AbsCollisionForm k R W y₂ := by
  unfold s1AbsCollisionForm
  apply Finset.sum_le_sum; intro d _
  apply Finset.sum_le_sum; intro e _
  split_ifs with h
  · have hnum : |lam k R W y₁ d| * |lam k R W y₁ e|
        ≤ |lam k R W y₂ d| * |lam k R W y₂ e| :=
      mul_le_mul (lam_abs_mono hle d) (lam_abs_mono hle e)
        (abs_nonneg _) (abs_nonneg _)
    exact div_le_div_of_nonneg_right hnum (prod_lcm_nonneg d e)
  · exact le_refl 0

/-! ## Reduction A′ — black-boxing the landed assembly via `S1InnerBound (yF)` -/

/-- **NB-1 reduction A′ (sorry-free, recommended).** The frozen `collision_yF_le`
FOLLOWS from the canonical inner atom `S1InnerBound 5 R W' (yF)` by BLACK-BOXING
the landed `collision_lower_orderW_of` (no assembly copy):

```
|s1CollisionForm (yF)| ≤ 12k²/D · ∑ (yF r)²/∏φ    -- collision_lower_orderW_of, given S1InnerBound
                       ≤ 12k²/D · ∑ 1/∏φ.          -- (yF r)² ≤ 1  (yF_abs_le_Qabs + hQ)
```

This is the correct isolation: `S1InnerBound (yF)` is a genuinely TRUE atom (the
per-assignment Cauchy–Schwarz bound), and it is exactly the tensor-dependent
hypothesis that Node A (`collision_lower_orderW_of`) abstracts.  It cannot be
discharged by pointwise `|yF| ≤ ONEw` domination alone — domination proves the
inner bound only with the LARGER moment `M = ∑1/∏φ` on the right (overshooting
`yside[yF] = ∑(yF)²/∏φ`), whereas `S1InnerBound` demands `yside[yF]`.  Closing it
needs either a Cauchy–Schwarz argument or a constant-`M` variant of the assembly
fed by the termwise `inner_abs_le` (see the module docstring). -/
theorem collision_yF_le_of_innerYF (R W' D : ℕ) (F : Poly) (hQ : Qabs F ≤ 1)
    (hSIB : S1InnerBound 5 R W' (yF R W' F))
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hDk : 12 * 5 ^ 2 ≤ D) :
    |s1CollisionForm 5 R W' (yF R W' F)|
      ≤ (12 * (5 : ℝ) ^ 2 / D) * ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) := by
  have hy0 : ∀ r, r ∉ kSieveIndex 5 R W' → yF R W' F r = 0 := by
    intro r hr; unfold yF; rw [if_neg hr]
  have hmain := collision_lower_orderW_of 5 R W' D (yF R W' F) hy0 hSIB hDlt (by norm_num) hDk
  have hyside : ∑ r ∈ kSieveIndex 5 R W', (yF R W' F r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
      ≤ ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    have hφ : (0 : ℝ) ≤ ∏ i, (Nat.totient (r i) : ℝ) :=
      Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have hy2 : (yF R W' F r) ^ 2 ≤ 1 := by
      have h1 : |yF R W' F r| ≤ 1 :=
        le_trans (yF_abs_le_Qabs R W' F r) (by exact_mod_cast hQ)
      nlinarith [abs_nonneg (yF R W' F r), sq_abs (yF R W' F r)]
    exact div_le_div_of_nonneg_right hy2 hφ
  have hcoef : (0 : ℝ) ≤ 12 * (5 : ℝ) ^ 2 / (D : ℝ) := by positivity
  exact le_trans hmain (mul_le_mul_of_nonneg_left hyside hcoef)

/-! ## Reduction B — the design's mono chain, via the constant-tensor majorant -/

/-- **NB-1 reduction (sorry-free).** The frozen `collision_yF_le` FOLLOWS from
the single collision atom `s1AbsCollisionForm ONEw ≤ (12·5²/D)·∑1/∏φ` by the
`|y|`-mono chain

```
|s1CollisionForm (yF)| ≤ s1AbsCollisionForm (yF)    -- s1CollisionForm_abs_le (landed)
                       ≤ s1AbsCollisionForm ONEw    -- s1AbsCollisionForm_mono + yF_abs_le_ONEw
                       ≤ (12·5²/D)·∑1/∏φ.            -- habsONE
```

The remaining atom `habsONE` is the genuine content (see the module docstring):
it is the constant-tensor collision estimate, blocked here by the `private`
erasure helpers in `CollisionQuant.lean`. -/
theorem collision_yF_le_of_absONE (R W' D : ℕ) (F : Poly) (hQ : Qabs F ≤ 1)
    (habsONE : s1AbsCollisionForm 5 R W' (ONEw R W')
      ≤ (12 * (5 : ℝ) ^ 2 / D) * ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ)) :
    |s1CollisionForm 5 R W' (yF R W' F)|
      ≤ (12 * (5 : ℝ) ^ 2 / D) * ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) := by
  calc |s1CollisionForm 5 R W' (yF R W' F)|
      ≤ s1AbsCollisionForm 5 R W' (yF R W' F) := s1CollisionForm_abs_le 5 R W' (yF R W' F)
    _ ≤ s1AbsCollisionForm 5 R W' (ONEw R W') :=
        s1AbsCollisionForm_mono (yF_abs_le_ONEw R W' F hQ)
    _ ≤ _ := habsONE

end Salt.Twelve
