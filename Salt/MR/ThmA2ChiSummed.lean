/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ThmA2

/-!
# ⟦A4-D1⟧ — THE `Σ_χ` CROSSING TWINS, AT THE INDEXED-FAMILY SHAPE (`ThmA2ChiSummed`)

Design provenance: `docs/exploration/a4-bridge-freeze-0730.md`, the A4 BRIDGE freeze,
**v2 addendum, amendment ⟦A1⟧** (the refuter-forced shape; v1 §6's wording is superseded).
This is the night-tail half of the bridge: the `y`-aspect-vs-`t`-aspect crossing lifted from
`q = 1` to the character sum, stated at the shape the crossing itself forces and at NOTHING
else.

## ⟦A1⟧ — WHY INDEXED FAMILIES, AND NOT THE SUM INSIDE

`ThmA2Spine.thm_a2_spine`'s `Mrow` is a SINGLE SCALAR uniform over the whole `T`-family
(`SeamLemma14.seam_Msup_family` consumes it as a constant, once per height).  The freeze v1
worded the `Σ_χ` slot with the character sum INSIDE the `T`-binders; the refuter (REF-A4-SHAPE,
`R-A4-5`) showed the two forms are inequivalent — they differ by a `sup_T ∑_χ` vs `∑_χ sup_T`
exchange worth up to `φ(q)` — and that the pointwise-in-`χ` lift forces the INDEXED-FAMILY
form: constants `Mrow B₀ : DirichletCharacter ℂ q → ℝ`, the character sum taken on the
CONSTANTS after the per-character crossing has fired.

The indexed form SUBSUMES the sum-inside form (take `Mrow χ := MrowΣ` for every `χ`); the
converse fails.  So this file is fork-neutral: whatever supplier wins the morning council's
leg census, these bytes stand.

## ⟦THE LIFT IS THREE MOVES⟧

The crossing layer (`Lemma14*`, `Seam*`, `Parseval*`, `ThmA2*`) is CHARACTER-BLIND (verbatim
grep: zero `χ`) and MONOTONE in the row datum, so the `q = 1` theorems apply VERBATIM at each
`a χ`.  The lift is therefore the corpus's landed three-move pattern — exemplars
`M4ChiSummed.m4_chiSummedShiftBlock_of_freeRow` and `HybridMoments.lemma12_meansq_all_chi`:

1. instantiate the `q = 1` theorem at the character's OWN datum `a χ` and its OWN constants;
2. `Finset.sum_le_sum` over `χ : DirichletCharacter ℂ q`;
3. split the affine right-hand side: `Finset.sum_add_distrib`, `← Finset.mul_sum` on the
   datum-carrying summands, `Finset.sum_const` on the `χ`-FREE ones.

There is no cross-`χ` coupling anywhere: the datum is a GENERIC family
`a : DirichletCharacter ℂ q → ℕ → ℂ`, pinned to neither `chiBarCoeff` nor `doorChiCoeff`
(they agree up to one `mul_comm`, and pinning would import a supplier choice this file must
not make).

## ⟦THE φ(q) LEDGER⟧ — paid where stated, never hidden

Move 3 is the whole price.  Each `χ`-FREE summand of the `q = 1` right-hand side is summed
over a set of size `φ(q)` and therefore acquires the factor `(q.totient : ℝ)`, carried
EXPLICITLY in the conclusion (the doctrine of `M4ChiSummed`'s header, ⟦THE φ(q) LEDGER⟧):

* the spine twin — `39674880π/h` and the whole Perron defect `Egap(K, δ)` pick up `φ(q)`;
  the row summand carries `∑_χ Mrow χ` and the band summand `∑_χ B₀ χ`, both un-debited;
* the `thm_a2'` twin — FOUR of the five summands (`a2Level1`, the `(log X)^{−1/500}` grade,
  the band residue, `6315000/h`) pick up `φ(q)`; only the `T₀`-band summand
  `8448·C₁'(χ)²·e^{−M₀(χ)/e}` carries a genuine character sum.

⟦OUT OF SCOPE, BY ⟦A2⟧⟧ the ARITHMETIC of those debits — the six-debit classification
(g-arm-absorbable `X`-side vs ⟦gate 8⟧-tightening `P₁/M`-side) — is COUNCIL work and appears
nowhere below.  This file states the price; it does not pay it.

## Contents

* §1 the character count and the two sum-splitting shapes, cited once for this file;
* §2 `thm_a2_spine_chiSummed` — the composition spine's `Σ_χ` twin;
* §3 `thm_a2'_of_rows_chiSummed` — the frozen five-summand interface's `Σ_χ` twin.

⟦THE FOUR LOG SCALES⟧ nothing below conflates them: only `log X` and `loglog(2T)` occur, and
both are read verbatim from the `q = 1` binders.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

/-! ## §1 — THE CHARACTER COUNT AND THE TWO SPLITS

The count is mathlib's `card_eq_totient_of_hasEnoughRootsOfUnity`, restated once for this
file (the corpus idiom: `M4ChiSummed.card_dirichletCharacter_nat`,
`HybridMoments.card_dirichletChar`, `HalaszIntegersChiClose.card_chars_totient_real` — the
layers are import-incomparable, so each cites the same mathlib lemma at its own name). -/

/-- The number of Dirichlet characters mod `q` is `φ(q)`. -/
theorem a2_card_chars (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- `∑_{χ mod q} C = φ(q)·C` — the ⟦φ(q) LEDGER⟧'s only mechanism. -/
theorem a2_sum_const_chars (q : ℕ) [NeZero q] (C : ℝ) :
    (∑ _χ : DirichletCharacter ℂ q, C) = (q.totient : ℝ) * C := by
  rw [Finset.sum_const, Finset.card_univ, a2_card_chars q, nsmul_eq_mul]

/-- **THE AFFINE SPLIT, TWO DATA** (the spine twin's shape): two `χ`-indexed constants with
scalar coefficients, plus one `χ`-free tail that pays `φ(q)`. -/
theorem a2_sum_affine_split (q : ℕ) [NeZero q] (c₁ c₂ : ℝ)
    (u v : DirichletCharacter ℂ q → ℝ) (w : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, (c₁ * u χ + c₂ * v χ + w))
      = c₁ * (∑ χ : DirichletCharacter ℂ q, u χ)
        + c₂ * (∑ χ : DirichletCharacter ℂ q, v χ) + (q.totient : ℝ) * w := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    a2_sum_const_chars]

/-- **THE AFFINE SPLIT, ONE DATUM** (the `thm_a2'` twin's shape): one `χ`-indexed head, one
`χ`-free tail that pays `φ(q)`. -/
theorem a2_sum_head_split (q : ℕ) [NeZero q] (u : DirichletCharacter ℂ q → ℝ) (w : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, (u χ + w))
      = (∑ χ : DirichletCharacter ℂ q, u χ) + (q.totient : ℝ) * w := by
  rw [Finset.sum_add_distrib, a2_sum_const_chars]

/-! ## §2 — THE COMPOSITION SPINE, `Σ_χ`

`ThmA2Spine.thm_a2_spine` at the indexed-family shape.  The scalar frame `N X h δ K` stays
GLOBAL (it is the window geometry, not a character datum); the datum `a`, the row constant
`Mrow` and the band constant `B₀` become families. -/

/-- **⟦A4-D1a⟧ THE `Σ_χ` COMPOSITION SPINE** (`thm_a2_spine_chiSummed`).  The character sum of
`ThmA2Spine.thm_a2_spine`'s single-`h` mean square, at a GENERIC `χ`-indexed coefficient
family and INDEXED constants `Mrow B₀ : DirichletCharacter ℂ q → ℝ` (amendment ⟦A1⟧):

`∑_χ (1/X)∫_X^{2X} ‖(1/h)·S_χ(x)‖² dx`
`  ≤ (1/2π²)·[ 236365π·∑_χ Mrow χ + 205π·∑_χ B₀ χ`
`             + φ(q)·( 39674880π/h + Egap(K,δ) ) ]`.

Every per-character hypothesis of the `q = 1` statement is quantified `∀ χ` at the family —
the coefficient bound `‖a χ n‖ ≤ 1`, the support condition, the weighted row family
`hrowsSum` (whose `T`-quantification `X/h ≤ T`, `2T ≤ X`, `TannGate X (2T)`,
`5 ≤ loglog(2T)` survives the character sum UNCHANGED: it is inside the `∀ χ`), and the
`T₀`-band `hT0bandSum`.  The window frame (`hX`, `hh4`, `hhX`, `hδ0`, `hδ1`, `hN2`, `hTann`,
`hceil`) is character-blind and stays global.

⟦THE LEDGER⟧ the two datum-carrying summands are un-debited; the crude moment tail
`39674880π/h` and the Perron defect `Egap` — the two summands NO character datum reaches —
each pay one `φ(q)`, carried explicitly. -/
theorem thm_a2_spine_chiSummed {q : ℕ} [NeZero q] {N : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h δ : ℝ}
    {Mrow B₀ : DirichletCharacter ℂ q → ℝ} (K : ℕ)
    (hX : Real.exp 1 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2) ≤ Mrow χ)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2) ≤ B₀ χ) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2)
          * (236365 * Real.pi * (∑ χ : DirichletCharacter ℂ q, Mrow χ)
            + 205 * Real.pi * (∑ χ : DirichletCharacter ℂ q, B₀ χ)
            + (q.totient : ℝ)
                * (39674880 * Real.pi / h
                  + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
                    + 1152 * (12 * h / (2 ^ K * δ)
                        + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))) := by
  -- ⟦move 1⟧ the `q = 1` spine at each character's OWN datum and OWN constants
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
        ≤ 1 / (2 * Real.pi ^ 2)
            * (236365 * Real.pi * Mrow χ + 205 * Real.pi * B₀ χ
              + (39674880 * Real.pi / h
                + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
                  + 1152 * (12 * h / (2 ^ K * δ)
                      + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))) := by
    intro χ _
    have hspine := thm_a2_spine (N := N) (a := a χ) (X := X) (h := h)
      (Mrow := Mrow χ) (B₀ := B₀ χ) (δ := δ) K hX hh4 hhX hδ0 hδ1 (ha χ) (hsupp χ) hN2
      hTann hceil (hrowsSum χ) (hT0bandSum χ)
    refine le_trans hspine (le_of_eq ?_)
    ring
  -- ⟦move 2⟧ the character sum
  refine le_trans (Finset.sum_le_sum hper) ?_
  -- ⟦move 3⟧ the affine split, the `φ(q)` paid on the two datum-free summands
  rw [← Finset.mul_sum, a2_sum_affine_split]

/-! ## §3 — THE FROZEN FIVE-SUMMAND INTERFACE, `Σ_χ`

`ThmA2.thm_a2'_of_rows` at the indexed-family shape.  Here the row constant is not free: it
is `a2Mrow Cs Ccc M Xd X ε`, so ⟦A1⟧'s indexing lands on the CONSTANTS `Cs Ccc C₁' M₀ ε`
that build the two grades — each becomes a family, and with them the two grading gates
`hgP1`/`hgRows` and the `𝒰`-leg exponent room `hεwin`.  The door parameters `M Xd` and the
window frame stay global. -/

/-- **⟦A4-D1b⟧ THE `Σ_χ` FROZEN INTERFACE** (`thm_a2'_of_rows_chiSummed`).  The character sum
of `ThmA2.thm_a2'_of_rows`' five-summand bound, at a GENERIC `χ`-indexed coefficient family
and INDEXED constant families `Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ`:

`∑_χ (1/X)∫_X^{2X} ‖(1/h)·S_χ(x)‖² dx`
`  ≤ ∑_χ 8448·C₁'(χ)²·exp(−M₀(χ)/e)`
`   + φ(q)·[ 1787702400·a2Level1 M`
`          + 188133·(log X)^{−1/500}`
`          + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
`          + 6315000/h ]`.

⟦THE LEDGER, ITEMISED⟧ ONE summand — the `T₀`-band's, the only one carrying a character
datum — is a genuine character sum; the other FOUR are `χ`-free and each pays exactly one
`φ(q)`.  The v2 addendum's ⟦A2⟧ six-debit classification (which of these are g-arm-absorbable
`X`-side and which tighten ⟦gate 8⟧ on the `P₁/M`-side) is COUNCIL arithmetic and is
deliberately absent here: this statement exhibits the debits, it does not price them.

Every per-character hypothesis is quantified `∀ χ`: the coefficient bound, the support
condition, the weighted row family at `a2Mrow (Cs χ) (Ccc χ) M Xd X (ε χ)`, the `T₀`-band at
`t0BandB X (C₁' χ) (M₀ χ)`, the two grading gates, and the exponent room.  The frame
(`hM`, `hX`, `hX3`, `hh4`, `hhX`, `hN2`, `hTann`, `hceil`, `hL4096`) is character-blind and
stays global. -/
theorem thm_a2'_of_rows_chiSummed {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum M Xd + Ccc χ * (2 / (M : ℝ)))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : ∀ χ : DirichletCharacter ℂ q, 0 ≤ ε χ ∧ ε χ ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1 M
              + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  -- ⟦move 1⟧ the `q = 1` interface at each character's OWN datum and OWN constants
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
        ≤ 8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ)
          + (1787702400 * a2Level1 M
            + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h) := by
    intro χ _
    have hrow := thm_a2'_of_rows (N := N) (M := M) (Xd := Xd) (a := a χ) (X := X) (h := h)
      (Cs := Cs χ) (Ccc := Ccc χ) (C₁' := C₁' χ) (M₀ := M₀ χ) (ε := ε χ)
      hM hX hX3 hh4 hhX (ha χ) (hsupp χ) hN2 hTann hceil (hrowsSum χ) (hT0bandSum χ)
      (hgP1 χ) (hgRows χ) (hεwin χ) hL4096
    refine le_trans hrow (le_of_eq ?_)
    ring
  -- ⟦move 2⟧ the character sum, then ⟦move 3⟧ the split: `φ(q)` on the four `χ`-free summands
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [a2_sum_head_split]

/-! ## §GK — the G-lever twin

The `χ`-summed crossing at `G := s13GK K M`.  The conclusion is BYTE-IDENTICAL to the landed
one (`a2Level1 M` is level-1 and therefore K-invariant); the two moved hypothesis slots are
`hrowsSum` (at `a2Mrow_gk`) and `hgRows` (at `a2RowsSum_gk`), plus `hgP1`'s `𝒫₁` written at
the lever's base — the same symbol.  Proved by ⟦THE `Ccc`-SHIFT⟧ (`ThmA2.a2Mrow_shift_gk`),
per character. -/

/-- **thm_A2′ χ-SUMMED, AT THE G-LEVER** (`thm_a2'_of_rows_chiSummed_gk`). -/
theorem thm_a2'_of_rows_chiSummed_gk (K : ℕ) {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow_gk K (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum_gk K M Xd + Ccc χ * (2 / (M : ℝ)))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : ∀ χ : DirichletCharacter ℂ q, 0 ≤ ε χ ∧ ε χ ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1 M
              + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  refine thm_a2'_of_rows_chiSummed (Xd := Xd) (Cs := Cs) (Ccc := fun χ =>
      Ccc χ + (M : ℝ) / 2 * (a2RowsSum_gk K M Xd - a2RowsSum M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0bandSum ?_ ?_ hεwin hL4096
  · intro χ T h1 h2 h3 h4
    exact (hrowsSum χ T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow_shift_gk K (Cs χ) (Ccc χ) (M := M) Xd X (ε χ) hM).symm)
  · intro χ
    rw [← calP_door_one_gk (K := K)]
    exact hgP1 χ
  · intro χ
    rw [a2RowsSum_shift_gk K (Ccc χ) (M := M) Xd hM]
    exact hgRows χ

-- #audit (temporary)

end Salt.MR
