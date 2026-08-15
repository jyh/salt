/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.WallUnconditional

/-!
# The parity wall at CORRELATION granularity (wall-L2)

Design provenance: the 08/14 wall-dream lens `L2-sieve-weight`, refuter verdict
WOUNDED-BUT-ALIVE (the surviving organ (ii): "`parity_wall_corr_stable`'s core
identity is correct … a genuine STRENGTHENING").  The dream's positive rung and its
headline are DEAD and are not touched here; see the file's honesty block below.

## What this file lands

The landed wall (`Salt/TwinBar/Wall.lean`, `WallUnconditional.lean`) caps every
lower-bound certificate that is tolerant with respect to `SieveAgree` — equality on
the three fields the sieve's main term consumes (`prodPrimes`, `nu`, `totalMass`)
plus a shared Rosser remainder budget.  A natural hope is that a certificate allowed
to read MORE of the sieve than those fields escapes the cap.  This file settles the
first such widening, at the wall's own witnesses:

* `corr2` — the shift-2 correlation functional of a sieve, read off its own fields:
  `corr₂ s = ∑_{n ∈ s.support} s.weights n · s.weights (n + 2)`.
* `SieveAgreeCorr` — `SieveAgree` with the interface WIDENED by that field: the two
  sieves must additionally agree on `corr₂` to within a budget `B₂`.
* `corr2_witness_diff` / `corr2_witness_diff_Mlambda` — **the core identity**: at the
  Selberg witness pair the `λλ` cross-term CANCELS, because `(1 ± λ(n))(1 ± λ(n+2))`
  carries `λ(n)λ(n+2)` with the SAME sign in both witnesses.  What is left is
  one-point: `corr₂(s₊ x) − corr₂(s₋ x) = 2·(M_λ(x) + M_λ(x+2))`.
* `corr2_witness_budget` — hence the pair's correlation-field disagreement is
  controlled by the landed Liouville summatory rate (`Salt.SW.mmuRate_holds` through
  `LambdaSummatory_of_MmuRate`): `≤ 8·c_λ·x/(log x)^A` for every `A > 0`,
  unconditionally.  The widened interface is met at a *sublinear* budget, so the
  strengthened hypothesis class is not being satisfied by slack.
* `parity_wall_corr` / `parity_wall_corr_stable` — **the strengthening**: since
  `SieveAgreeCorr → SieveAgree`, tolerance with respect to `SieveAgreeCorr` is a
  WEAKER demand on `Φ`, and the identical cap still holds at `s₋ x`.  Adjoining a
  shift-2 correlation field to the sieve interface does not unlock the certificate
  cap.

## Honesty block (read before quoting anything here)

* This is a **wall strengthening at the real witnesses**, and nothing else.  It is
  zero progress on twin primes, and it upgrades no positive sieve rung.
* Nothing here escapes, crosses, or evades the wall, and no object in this file may
  be described that way.  The parity-twisted certificates the L2 dream considered are
  *constant* on `SieveAgree` classes — they are the paradigm tolerant functionals —
  so widening the tolerance relation is the only honest question to ask, and the
  answer landed here is that the cap survives the widening.
* The dream's positive program (a `λ`-Bombieri–Vinogradov consumed through
  `brun_lower`) is refuted at its interface: `brun_lower`'s remainder slot is a
  pointwise `ℓ^∞` majorant, an `ℓ¹` average cannot discharge it, and the honest gate
  is the named `brun_lower_ell1` question.  None of that is claimed here.
-/

open ArithmeticFunction Finset

namespace Salt.TwinBar

/-! ## The correlation field and the widened agreement relation -/

/-- The **shift-2 correlation functional** of a sieve, read off the sieve's own
fields: `corr₂ s = ∑_{n ∈ s.support} s.weights n · s.weights (n + 2)`.  This is the
smallest piece of information beyond `SieveAgree`'s three fields that a twin-adjacent
certificate could plausibly want. -/
noncomputable def corr2 (s : BoundingSieve) : ℝ :=
  ∑ n ∈ s.support, s.weights n * s.weights (n + 2)

/-- **`SieveAgreeCorr s t D B B₂`** — the sieve interface WIDENED by the shift-2
correlation field: `SieveAgree s t D B` (equality on `prodPrimes`, `nu`, `totalMass`,
shared Rosser budget `B` at level `D`) together with agreement on `corr₂` to within
`B₂`.  It is a strictly stronger relation than `SieveAgree`, so tolerance with
respect to it is a strictly weaker hypothesis on a certificate. -/
def SieveAgreeCorr (s t : BoundingSieve) (D : ℕ) (B B₂ : ℝ) : Prop :=
  SieveAgree s t D B ∧ |corr2 s - corr2 t| ≤ B₂

/-- The widened relation refines the landed one. -/
lemma SieveAgreeCorr.toSieveAgree {s t : BoundingSieve} {D : ℕ} {B B₂ : ℝ}
    (h : SieveAgreeCorr s t D B B₂) : SieveAgree s t D B := h.1

/-- Every `SieveAgree`-tolerant certificate is `SieveAgreeCorr`-tolerant: the widened
hypothesis class CONTAINS the landed one (anti-vacuity — in particular the landed
lower consumer `phiLowerR` inhabits it, via `phiLowerR_tolerant`). -/
lemma tolerant_corr_of_tolerant {Φ : BoundingSieve → ℝ} {D : ℕ} {B : ℝ}
    (htol : ∀ s t, SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B) :
    ∀ (B₂ : ℝ) (s t), SieveAgreeCorr s t D B B₂ → |Φ s - Φ t| ≤ 2 * B :=
  fun _ s t h => htol s t h.1

/-- The landed lower-Möbius floor is tolerant for the WIDENED relation too (the
inhabitation witness, carried across the strengthening). -/
theorem phiLowerR_tolerant_corr (muMinus : ℕ → ℝ) (D : ℕ) (s t : BoundingSieve)
    (B B₂ : ℝ) (h : SieveAgreeCorr s t D B B₂) :
    |phiLowerR muMinus D s - phiLowerR muMinus D t| ≤ 2 * B :=
  phiLowerR_tolerant muMinus D s t B h.1

/-! ## The core identity — the `λλ` cross-term cancels between the witnesses -/

/-- **The cross-term cancellation.**  `(1 + λ(n))(1 + λ(n+2))` and
`(1 − λ(n))(1 − λ(n+2))` carry the product `λ(n)·λ(n+2)` with the SAME sign, so the
two-point content of the Selberg witness pair cancels in the difference and only the
one-point sums survive:
`corr₂(s₊ x) − corr₂(s₋ x) = 2·∑_{n ≤ x} (λ(n) + λ(n+2))`. -/
lemma corr2_witness_diff (x : ℕ) :
    corr2 (sPlus x) - corr2 (sMinus x)
      = 2 * ∑ n ∈ Finset.Icc 1 x, ((liouville n : ℝ) + (liouville (n + 2) : ℝ)) := by
  simp only [corr2, sPlus_support, sMinus_support, sPlus_weights, sMinus_weights]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- `M_λ(2) = λ(1) + λ(2) = 1 − 1 = 0`. -/
lemma Mlambda_two : Mlambda 2 = 0 := by
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [Mlambda, hIcc, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), liouville_real_one,
    liouville_real_prime Nat.prime_two]
  norm_num

/-- The shifted one-point sum is a summatory value on the nose:
`∑_{1 ≤ n ≤ x} λ(n+2) = M_λ(x+2)` (the two dropped terms `λ(1) + λ(2)` cancel). -/
lemma sum_liouville_shift_two (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, ((liouville (n + 2) : ℤ) : ℝ) = Mlambda (x + 2) := by
  induction x with
  | zero => simpa using Mlambda_two.symm
  | succ k ih =>
      have hstep : Mlambda (k + 1 + 2) = Mlambda (k + 2) + ((liouville (k + 3) : ℤ) : ℝ) := by
        rw [Mlambda, Mlambda, show k + 1 + 2 = (k + 2) + 1 from rfl,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 2 + 1)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih, hstep]

/-- **The core identity in summatory form**: the witness pair's shift-2 correlation
gap is `2·(M_λ(x) + M_λ(x+2))` — one-point, and therefore governed by the landed
Liouville summatory rate rather than by any two-point (Chowla-type) input. -/
lemma corr2_witness_diff_Mlambda (x : ℕ) :
    corr2 (sPlus x) - corr2 (sMinus x) = 2 * (Mlambda x + Mlambda (x + 2)) := by
  rw [corr2_witness_diff, Finset.sum_add_distrib, sum_liouville_shift_two]
  rfl

/-! ## The correlation budget is sublinear, unconditionally -/

/-- **The witness pair meets the widened interface at a sublinear budget.**  For every
saving `A > 0` there is a `C > 0` with
`|corr₂(s₊ x) − corr₂(s₋ x)| ≤ C·x/(log x)^A` for all large `x`.  Unconditional: the
one-point content is discharged by the landed `Salt.SW.mmuRate_holds` through
`LambdaSummatory_of_MmuRate`.  This is what makes the strengthening below non-vacuous
— the pair `SieveAgreeCorr`s at a budget `o(x)`, not merely at a huge one. -/
theorem corr2_witness_budget (A : ℝ) (hA : 0 < A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      |corr2 (sPlus x) - corr2 (sMinus x)| ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨cLam, nLam, hcLam, hbd⟩ := LambdaSummatory_of_MmuRate Salt.SW.mmuRate_holds A hA
  refine ⟨8 * cLam, max 2 nLam, by positivity, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxl : nLam ≤ x := le_trans (le_max_right _ _) hx
  have hxl2 : nLam ≤ x + 2 := by omega
  have hx1R : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hlogx : 0 < Real.log x := Real.log_pos hx1R
  have hLpos : (0 : ℝ) < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogx A
  have h1 := hbd x hxl
  have h2 := hbd (x + 2) hxl2
  -- the shifted rate, re-based at `log x`
  have hmono : (Real.log x) ^ A ≤ (Real.log ((x + 2 : ℕ) : ℝ)) ^ A := by
    refine Real.rpow_le_rpow hlogx.le (Real.log_le_log (by linarith) ?_) hA.le
    push_cast
    linarith
  have hcast3 : (((x + 2 : ℕ) : ℝ)) ≤ 3 * (x : ℝ) := by push_cast; linarith
  have h2' : |Mlambda (x + 2)| ≤ cLam * (3 * (x : ℝ)) / (Real.log x) ^ A := by
    refine le_trans h2 ?_
    gcongr
  calc |corr2 (sPlus x) - corr2 (sMinus x)|
      = |2 * (Mlambda x + Mlambda (x + 2))| := by rw [corr2_witness_diff_Mlambda]
    _ = 2 * |Mlambda x + Mlambda (x + 2)| := by
          rw [abs_mul]; norm_num
    _ ≤ 2 * (|Mlambda x| + |Mlambda (x + 2)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 2 * (cLam * (x : ℝ) / (Real.log x) ^ A + cLam * (3 * (x : ℝ)) / (Real.log x) ^ A) := by
          gcongr
    _ = 8 * cLam * (x : ℝ) / (Real.log x) ^ A := by ring

/-! ## The strengthening: the cap survives the widened interface -/

/-- **The parity wall at correlation granularity** (the algebraic layer, mirroring
`parity_wall`).  For a level `D`, a Rosser budget `B` the pair both meets, and ANY
correlation budget `B₂` the pair meets, every certificate that is tolerant only with
respect to the WIDENED relation `SieveAgreeCorr` still obeys `Φ(s₋ x) ≤ 2 + 2B` —
while the true sifted sum of `s₋ x` is `2(π(x) − π(√x))`. -/
theorem parity_wall_corr (x : ℕ) (hx : 2 ≤ x) (D : ℕ) (B B₂ : ℝ)
    (hplus : Salt.Chen.rosserRemainder (sPlus x) (D : ℝ) ≤ B)
    (hminus : Salt.Chen.rosserRemainder (sMinus x) (D : ℝ) ≤ B)
    (hcorr : |corr2 (sPlus x) - corr2 (sMinus x)| ≤ B₂)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ s t, SieveAgreeCorr s t D B B₂ → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    Φ (sMinus x) ≤ 2 + 2 * B := by
  have hagree : SieveAgreeCorr (sPlus x) (sMinus x) D B B₂ :=
    ⟨sieveAgree_pair x D B hplus hminus, hcorr⟩
  have htol' := htol (sPlus x) (sMinus x) hagree
  have hcertp : Φ (sPlus x) ≤ 2 := by
    have := hcert (sPlus x)
    rwa [siftedSum_sPlus x hx] at this
  rcases abs_le.mp htol' with ⟨h1, _⟩
  linarith

/-- **`parity_wall_corr_stable` — the wall is stable under adjoining the shift-2
correlation field.**  The cap of `parity_wall_unconditional` holds VERBATIM at `s₋ x`
for the strictly larger class of certificates that need only be tolerant with respect
to `SieveAgreeCorr`: reading the sieves' shift-2 correlation, on top of the three
main-term fields, buys a certificate nothing at the wall's own witnesses.

Why this is a strengthening and not a restatement: `SieveAgreeCorr → SieveAgree`, so
`htol` here is a WEAKER hypothesis than the landed wall's.  It has content only
because the witness pair really does agree in the widened field —
`corr2_witness_diff_Mlambda` cancels the `λλ` cross-term and `corr2_witness_budget`
puts the surviving one-point gap at `O(x/(log x)^A)` unconditionally.

Scope, stated plainly: this is a strengthening of a NEGATIVE theorem at the real
witnesses.  It proves no lower bound, opens no positive rung, and says nothing about
twin primes. -/
theorem parity_wall_corr_stable (A : ℝ) (hA : 0 < A)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ (D : ℕ) (B B₂ : ℝ), ∀ s t, SieveAgreeCorr s t D B B₂ → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      Φ (sMinus x)
        ≤ 2 + 2 * ((Nat.sqrt x : ℝ) + C * x * (1 + Real.log x) / (Real.log x) ^ A) := by
  obtain ⟨cLam, nLam, hcLam, hbd⟩ := LambdaSummatory_of_MmuRate Salt.SW.mmuRate_holds A hA
  refine ⟨cLam * (4 : ℝ) ^ A, max 16 (nLam ^ 2), by positivity, ?_⟩
  intro x hx
  have hx16 : 16 ≤ x := le_trans (le_max_left _ _) hx
  have hxl : nLam ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ x := by omega
  have hplus := witness_rosserRemainder_le hA hcLam hbd x hx16 hxl (sPlus x)
    (sPlus_prodPrimes x) (sPlus_rem_bound x)
  have hminus := witness_rosserRemainder_le hA hcLam hbd x hx16 hxl (sMinus x)
    (sMinus_prodPrimes x) (sMinus_rem_bound x)
  set B := (Nat.sqrt x : ℝ) + cLam * (4 : ℝ) ^ A * x * (1 + Real.log x) / (Real.log x) ^ A
    with hB
  exact parity_wall_corr x hx2 (Nat.sqrt x) B |corr2 (sPlus x) - corr2 (sMinus x)|
    hplus hminus le_rfl Φ (htol (Nat.sqrt x) B _) hcert

end Salt.TwinBar
