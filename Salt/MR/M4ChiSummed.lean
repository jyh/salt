/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4CoprimeSupply
import Salt.MR.M4DoorClose

/-!
# ⟦D-2⟧ — THE χ-SUMMED FREE-BASE SOCKET AND ITS MIRRORS (`M4ChiSummed`)

Wave ④ of the second-road freeze v2 (`docs/exploration/second-road-freeze-0729.md`),
stages S-1 and S-2.  The socket is ⟦REF-SHAPE A-C1⟧'s replacement for the freeze v1 socket
that had **no instances at any stratum `d ≥ 2`** (the dilated base `⌊A/d⌋` can never be named
by a ladder form): the corpus's own FREE-BASE row family is the right genre, and this file
states its **`Σ_χ` twin** and re-runs the landed free-base chain under the character sum.

## ⟦WHY A `Σ_χ` SOCKET AT ALL⟧ — the one place the second road beats the first

The landed per-χ road prices a residue class by splitting the window into `q` classes and
Cauchy–Schwarzing: that costs `q²` (`M4ClassPrice` §4, ⟦F2⟧'s wall).  The second road never
splits: it expands the coprimality indicator over characters and pays the Gauss sum's own
second moment `∑_χ ‖τ_b(χ̄)‖² = φ(q)²`, which cancels the `1/φ(q)²` of the expansion EXACTLY
(prefactor `1`).  What survives is `∑_χ ‖(the per-χ window sum)‖²` — the χ-SUM, not `φ(q)`
copies of a per-χ bound.  A per-χ socket would re-import a factor `φ(q)`; the χ-summed
socket is what makes the composition `O(1)`.

So the datum is the SUM over `χ` of the row mean squares, and every mirror below is the
landed free-base step run **pointwise in `χ` and then summed**.

## ⟦THE φ(q) LEDGER⟧ — where the character count does appear, honestly

Two steps in the landed chain are charged at the ABSOLUTE grade (no row datum is read):
the shifted block's drop residue `8·(2^j)²` and the maximal step's trivial half
`A·(2^j)²` at `j < j₀`.  Under `∑_χ` each is multiplied by `φ(q) ≤ q ≤ arcDen 12 H`.  Both
are carried EXPLICITLY at `arcDen 12 H` (never at `q`, so the predicates stay `q`-free):

* the shift block's residue is `(2·F + 8·arcDen)·(2^j)²`;
* the maximal step's trivial half raises ⟦G1⟧ from `2·arcDen²  ≤ Ftr` to
  `2·arcDen³ ≤ Ftr` — one further power of `arcDen` on a WITNESSED envelope, i.e. a
  threshold, not a saving (`M4CoprimeSupply`'s header, ⟦THE TWO GATES⟧).

This is the honest price of the `Σ_χ` mirror and it is stated where it is paid.

## Contents

* §1 THE SOCKET — `chiFreeRowSq`, `M4ChiSummedFreeRow`, the anti-vacuity witness at
  `RS j H := 4·arcDen 12 H`, and the bridge down to the landed per-χ family.
* §2 THE SHIFTED BRIDGE, MIRRORED — `chiFreeShift_pointwise` (the landed proof at a FREE
  per-χ constant), `M4ChiSummedFreeShiftBlock`, `m4_chiSummedShiftBlock_of_freeRow`.
* §3 THE MAXIMAL STEP, MIRRORED — `M4ChiSummedBlockMeanSqN`,
  `m4_chiSummedBlockN_of_shiftBlock`, and the assembled supply
  `m4_chiSummedN_supplied`.

## ⟦THE TRAPS RESPECTED⟧

* the four log scales — `Nat.log 2` for the dyadic index, `arcDen 12 H` (never evaluated)
  for the modulus range and for the `φ(q)` ledger; no `log X`, no `loglog`;
* `liouChi`, never `lamChi`; the datum is `doorChiCoeff χ M` BARE, at the frequency `0`;
* half-open throughout (`doorSievedWindow`, `seamS0`'s strict filter, `Finset.Ioc` blocks);
* strict gates (`0 < q`, `0 < A`, `R.Hlo ≤ H ≤ R.Hhi`, `4 ≤ L`) carried, never weakened;
* the `Fintype (DirichletCharacter ℂ q)` instance is mathlib's `.ofFinite`; the character
  count is `card_eq_totient_of_hasEnoughRootsOfUnity`, never re-derived.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE SOCKET

`M4CoprimeSupply.M4ChiFreeRowMeanSq`'s row datum, named once as a function of the base, and
the `Σ_χ` predicate over it. -/

/-- **THE FREE-BASE ROW MEAN SQUARE, PER CHARACTER** (`chiFreeRowSq χ M j X`) — the door's
sieved, χ-twisted, UN-PHASED datum in `ThmA2.thm_a2'_of_rows`' own currency at the dyadic
window length `2^j` and the scale `X`, with the capstone's two pins `X_d = X`, `N = 2X_d`.

It is `M4CoprimeSupply.M4ChiFreeRowMeanSq`'s body at `X := A + s`, named so the `Σ_χ` socket
can quantify over it. -/
def chiFreeRowSq {q : ℕ} (χ : DirichletCharacter ℂ q) (M j X : ℕ) : ℝ :=
  1 / ((X : ℕ) : ℝ)
    * (∫ y in ((X : ℕ) : ℝ)..(2 * ((X : ℕ) : ℝ)),
        ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
            * shortSum (doorChiCoeff χ M) (seamS0 (2 * X) ((X : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖ ^ 2)

/-- The row mean square is nonnegative (`M4BridgeIntegral.meanSq_nonneg`). -/
theorem chiFreeRowSq_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (M j : ℕ) {X : ℕ}
    (hX : 0 < X) : 0 ≤ chiFreeRowSq χ M j X := by
  have hX0 : (0 : ℝ) < ((X : ℕ) : ℝ) := by exact_mod_cast hX
  exact meanSq_nonneg (doorChiCoeff χ M) (seamS0 (2 * X) ((X : ℕ) : ℝ)) ((2 ^ j : ℕ) : ℝ) hX0

/-- **THE ABSOLUTE GRADE `4`** — `M4DoorClose.doorRow_trivial_grade`, re-read at the name.
This is what makes the socket's anti-vacuity witness `q`-free. -/
theorem chiFreeRowSq_le_four {q : ℕ} (χ : DirichletCharacter ℂ q) (M j : ℕ) {X : ℕ}
    (hX : 0 < X) : chiFreeRowSq χ M j X ≤ 4 :=
  doorRow_trivial_grade χ M j hX

/-- The character count, in `ℕ` — mathlib's, cited once. -/
theorem card_dirichletCharacter_nat (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- **⟦A-C1⟧ THE χ-SUMMED FREE-BASE ROW SOCKET** (`M4ChiSummedFreeRow R M RS`).

The second road's ONE analytic input.  Read at:

* a FREE base `A` (`0 < A`) and a FREE shift `s ≤ L` — the strata's dilated bases
  `⌊A/d⌋` are named by no ladder, which is what killed freeze v1's socket;
* CAP-GENERAL `∀ L ≤ H` and WINDOW-DYADIC `2^j`, `j ≤ log₂ L` — non-dyadic lengths never
  reach the row;
* EVERY modulus `0 < q ≤ arcDen 12 H`, with `RS : ℕ → ℕ → ℝ` **`q`-free** (length-graded
  `j`, ambient `H`) — the reduced moduli `q/d` of the strata are covered by the same `RS`;
* the SUM over `χ : DirichletCharacter ℂ q`, not a per-χ bound (⟦WHY A `Σ_χ` SOCKET⟧).

⟦NO ENDPOINT ANTECEDENT⟧ (`D-5`, R-E confirmed): `seamS0` is strict at the bottom, the
tiling is half-open, and no consumer reads the closed endpoint — the endpoint obligation
belongs to whatever SUPPLIES this socket, not to the socket. -/
def M4ChiSummedFreeRow (R : ChowlaRegime) (M : ℕ) (RS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ A : ℕ, 0 < A → ∀ s ≤ L,
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s) ≤ RS j H

/-- **THE SOCKET IS INHABITED** (the house's anti-vacuity duty) — at
`RS j H := 4·arcDen 12 H` the socket holds outright: each of the `φ(q)` terms is at most the
absolute grade `4` (`chiFreeRowSq_le_four`), and `φ(q) ≤ q ≤ arcDen 12 H` is the modulus
range's own gate.  So ALL of the socket's content is the grade, and the anti-vacuity witness
is `q`-FREE — which is what the `q`-free `RS` demands. -/
theorem m4_chiSummedFreeRow_trivial (R : ChowlaRegime) (M : ℕ) :
    M4ChiSummedFreeRow R M (fun _ H => 4 * arcDen 12 H) := by
  intro H _ _ L _ q hq hqQ j _ A hA s _
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hterm : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      chiFreeRowSq χ M j (A + s) ≤ 4 := fun χ _ => chiFreeRowSq_le_four χ M j hAs
  have hsum : ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
      ≤ ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
    calc ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
        ≤ ∑ _χ : DirichletCharacter ℂ q, (4 : ℝ) := Finset.sum_le_sum hterm
      _ = ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_dirichletCharacter_nat q] at hsum
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  linarith

/-- **THE BRIDGE DOWN** (`m4_chiFreeRow_of_chiSummed`) — the χ-summed socket dominates the
landed per-χ free-base row family at the SAME grade, because every term of a sum of
nonnegatives is under the sum.

Recorded so the per-χ road stays available as a fallback (⟦D-8⟧'s honest condition: taking
it re-imports WALLS D and F5).  Nothing below this line uses it. -/
theorem m4_chiFreeRow_of_chiSummed {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    (h : M4ChiSummedFreeRow R M RS) : M4ChiFreeRowMeanSq R M RS := by
  intro H hlo hhi L hLH q hq hqQ χ j hjL A hA s hsL
  have hAs : 0 < A + s := by omega
  have hle : chiFreeRowSq χ M j (A + s)
      ≤ ∑ χ' : DirichletCharacter ℂ q, chiFreeRowSq χ' M j (A + s) :=
    Finset.single_le_sum (f := fun χ' => chiFreeRowSq χ' M j (A + s))
      (fun χ' _ => chiFreeRowSq_nonneg χ' M j hAs) (Finset.mem_univ χ)
  exact le_trans hle (h H hlo hhi L hLH q hq hqQ j hjL A hA s hsL)

/-! ## §2 — THE SHIFTED BRIDGE, MIRRORED

`M4CoprimeSupply.m4_chiFreeShiftBlock_of_freeRow` re-run at a FREE per-χ constant, so that
the `Σ_χ` can be taken AFTER the per-χ derivation instead of before it.  This is the whole
content of the mirror: the landed statement's grade is χ-uniform, and summing a χ-uniform
bound over `χ` costs `φ(q)` — the very factor the socket exists to avoid. -/

/-- **THE POINTWISE SHIFTED BRIDGE** (`chiFreeShift_pointwise`) — `⟦W3⟧` at a per-χ constant
`c` in place of the χ-uniform grade `MS j H`.

Byte-for-byte `M4CoprimeSupply.m4_chiFreeShiftBlock_of_freeRow`'s proof with the row datum
read at `c`: the slack-`4` block bound at the shifted block, the harmonic→flat exchange
against `B + s ≤ 2(A+s)` (which is `4 ≤ L`), and the two comparisons the free block affords.
Nothing new is estimated. -/
theorem chiFreeShift_pointwise {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ)
    {L j s A B : ℕ} {c : ℝ} (hjL : j ≤ Nat.log 2 L) (hsL : s ≤ L) (hA : 0 < A) (hL4 : 4 ≤ L)
    (hfit : B + L ≤ 2 * A + 4) (hc : chiFreeRowSq χ M j (A + s) ≤ c) :
    ∑ n ∈ Finset.Ioc (A + s) (B + s),
        ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
      ≤ 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum at the constant `c`, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ c := by
    rw [doorCoeffPhase_zero]
    exact hc
  have hc0 : (0 : ℝ) ≤ c :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff χ M) (fun m => norm_doorChiCoeff_le_one χ M m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := c) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
      = 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * c * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero] using hfinal

/-- **THE χ-SUMMED SHIFTED FIXED-LENGTH DATUM** (`M4ChiSummedFreeShiftBlock`) — the `Σ_χ`
twin of `M4CoprimeSupply.M4ChiFreeShiftBlockMeanSq`.

⟦THE φ(q) LEDGER, first entry⟧ the drop residue `8·(2^j)²` is charged at the ABSOLUTE grade
per character, so under `∑_χ` it is `8·φ(q)·(2^j)²`; it is carried at `8·arcDen 12 H·(2^j)²`,
which keeps the predicate `q`-free. -/
def M4ChiSummedFreeShiftBlock (R : ChowlaRegime) (M : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∀ A B : ℕ, 0 < A → 4 ≤ L → B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc (A + s) (B + s),
            ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (2 * F j H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2

/-- **ANTI-VACUITY** for the χ-summed shifted family, at the trivial grade
`F j H := arcDen 12 H`: each of the `φ(q) ≤ arcDen` characters contributes at most
`A·(2^j)²` (window sums bounded by their length, `B − A ≤ A`). -/
theorem m4_chiSummedShiftBlock_trivial (R : ChowlaRegime) (M : ℕ) :
    M4ChiSummedFreeShiftBlock R M (fun _ H => arcDen 12 H) := by
  intro H _ _ L _ q hq hqQ j _ s _ A B hA hL4 hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := le_trans (by positivity) hqQ
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro χ _
    have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
        ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro n _
      have h := norm_sum_doorSievedWindow_le χ M (2 ^ j) n
      have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hcast : ((B + s - (A + s) : ℕ) : ℝ) ≤ (A : ℝ) := by
      have hnat : B + s - (A + s) ≤ A := by omega
      exact_mod_cast hnat
    nlinarith
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletCharacter_nat q] at hsum
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  have hmid : (q.totient : ℝ) * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ arcDen 12 H * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    refine mul_le_mul_of_nonneg_right hφarc ?_
    positivity
  nlinarith [hsum, hmid, mul_nonneg harc0 hP0]

/-- **⟦S-2a⟧ THE SHIFTED BRIDGE, MIRRORED** (`m4_chiSummedShiftBlock_of_freeRow`) — the
χ-summed socket becomes the χ-summed shifted block datum at the grade `2·RS`.

The step IS genuinely pointwise-in-χ (⟦the mechanicalness spot-check⟧ of the freeze's
residual-risk list): `chiFreeShift_pointwise` is applied at each `χ` with the constant
`c := chiFreeRowSq χ M j (A+s)` — the character's OWN row datum — and only then summed.
There is no cross-χ coupling anywhere in the step; the only character-dependent charge is
the absolute drop residue, which is the ⟦φ(q) LEDGER⟧'s first entry. -/
theorem m4_chiSummedShiftBlock_of_freeRow {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    (hrow : M4ChiSummedFreeRow R M RS) :
    M4ChiSummedFreeShiftBlock R M (fun j H => 2 * RS j H) := by
  intro H hlo hhi L hLH q hq hqQ j hjL s hsL A B hA hL4 hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  -- ⟦the pointwise bound at each character's OWN row datum⟧
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ 2 * chiFreeRowSq χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (4 * chiFreeRowSq χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := fun χ _ =>
    chiFreeShift_pointwise χ M hjL hsL hA hL4 hfit le_rfl
  refine le_trans (Finset.sum_le_sum hper) ?_
  -- ⟦the sum splits into the row sum and the absolute residue⟧
  have hsplit : ∑ χ : DirichletCharacter ℂ q,
      (2 * chiFreeRowSq χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * chiFreeRowSq χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
      = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s))
          * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
        + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
            * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    calc ∑ χ : DirichletCharacter ℂ q,
          (2 * chiFreeRowSq χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (4 * chiFreeRowSq χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        = ∑ χ : DirichletCharacter ℂ q,
            (chiFreeRowSq χ M j (A + s)
                * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
              + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
          Finset.sum_congr rfl fun χ _ => by ring
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
              * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2))
            + ∑ _χ : DirichletCharacter ℂ q, 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s))
            * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
          + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
              * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
          rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsplit, card_dirichletCharacter_nat q]
  have hrowsum := hrow H hlo hhi L hLH q hq hqQ j hjL A hA s hsL
  have hrow0 : (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s) :=
    Finset.sum_nonneg fun χ _ => chiFreeRowSq_nonneg χ M j hAs
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  have hfac0 : (0 : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    positivity
  have h1 : (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s))
        * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ RS j H * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hrowsum hfac0
  have h2 : (q.totient : ℝ) * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ arcDen 12 H * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    refine mul_le_mul_of_nonneg_right hφarc ?_
    positivity
  nlinarith [h1, h2]

/-! ## §3 — THE MAXIMAL STEP, MIRRORED

`M4CoprimeSupply.m4_coprimeChiN_of_freeShiftBlock` re-run with the character sum taken
BEFORE the dyadic assembly instead of after it.  Every step of the landed argument is a
pointwise-in-`χ` inequality between nonnegative families with the input entering linearly,
so the mirror is the same proof at the summed integrand `Y j t n := ∑_χ X_χ j t n`.  The
ONE place the character count is visible is the trivial half (`j < j₀`), which reads no row
datum at all and is therefore charged `φ(q) ≤ arcDen 12 H` times the absolute grade — the
⟦φ(q) LEDGER⟧'s second entry, and the reason ⟦G1⟧ rises to `arcDen³`. -/

/-- **THE χ-SUMMED NARROWED BLOCK MEAN SQUARE** (`M4ChiSummedBlockMeanSqN`) — the `Σ_χ` twin
of `M4CoprimeSupply.M4CoprimeChiBlockMeanSqN`: the same free half-open block `(A, B]`, the
same free length `L` with ⟦THE NARROWING⟧ `H ≤ arcDen·L`, the same slack-`4` fit, with the
sum over characters on the left instead of a χ-uniform bound.

This is what the stratified Gauss consumer reads: the Cauchy–Schwarz against the Gauss sum's
second moment leaves exactly `∑_χ (per-χ sup)²` and no `φ(q)`. -/
def M4ChiSummedBlockMeanSqN (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H ^ 3 * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- **ANTI-VACUITY** for the χ-summed block family, at the trivial grade `5·arcDen 12 H`:
each of the `φ(q) ≤ arcDen` characters contributes at most `5·L²·A`. -/
theorem m4_chiSummedBlockN_trivial (R : ChowlaRegime) (M : ℕ) :
    M4ChiSummedBlockMeanSqN R M (fun H => 5 * arcDen 12 H) := by
  intro H hlo hhi L hLH hnar q hq hqQ A B hA hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have harc0 : (0 : ℝ) ≤ arcDen 12 H := le_trans (by positivity) hqQ
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := sq_nonneg _
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2 ≤ 5 * (L : ℝ) ^ 2 * (A : ℝ) := by
    intro χ _
    have hterm : ∀ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2 ≤ (L : ℝ) ^ 2 := by
      intro n _
      have h := doorChiSup_le_len χ M L n
      have h0 := doorChiSup_nonneg χ M L n
      nlinarith
    have hsum : ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
        ≤ ((Finset.Ioc A B).card : ℝ) * (L : ℝ) ^ 2 := by
      calc ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
          ≤ ∑ _n ∈ Finset.Ioc A B, (L : ℝ) ^ 2 := Finset.sum_le_sum hterm
        _ = ((Finset.Ioc A B).card : ℝ) * (L : ℝ) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.Ioc A B).card : ℝ) ≤ 5 * (A : ℝ) := by
      rw [Nat.card_Ioc]
      have hn : B - A ≤ 5 * A := by omega
      exact_mod_cast hn
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletCharacter_nat q] at hsum
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  have hmid : (q.totient : ℝ) * (5 * (L : ℝ) ^ 2 * (A : ℝ))
      ≤ arcDen 12 H * (5 * (L : ℝ) ^ 2 * (A : ℝ)) := by
    refine mul_le_mul_of_nonneg_right hφarc ?_
    positivity
  nlinarith [hsum, hmid]

set_option maxHeartbeats 3200000 in
-- the dyadic assembly is `M4CoprimeSupply`'s at a free block with ONE further summation
-- layer (the character sum), so the triple-nested `Finset` sums are re-elaborated against
-- `∑_χ` as well as the free `(A, B]` and `L` — that re-elaboration is what costs the
-- heartbeats (no tactic search below is unbounded: every arithmetic step is `linarith` or
-- `nlinarith` with explicit hints)
/-- **⟦S-2b⟧ THE MAXIMAL STEP, MIRRORED** (`m4_chiSummedBlockN_of_shiftBlock`) — the χ-summed
block mean square from the χ-summed shifted fixed-length datum, at the graded price
`m4BclGraded j₀ Fan Ftr`.

⟦THE LEDGER, mirrored⟧ — the three charges of `M4CoprimeSupply`'s header, each read under
`∑_χ`:

1. the analytic half (`j₀ ≤ j`) reads the χ-SUMMED datum, so it lands on the grade's first
   summand exactly as before — **no `φ(q)` appears**, which is the whole point of the socket;
2. the trivial half (`j < j₀`) reads no datum and is charged `φ(q)` times the absolute grade
   `1`; bounded by `arcDen 12 H`, it is what raises ⟦G1⟧ to `2·arcDen³ ≤ Ftr`;
3. the slack-`4` residue arrives from the shifted datum already carrying its `8·arcDen`
   (⟦φ(q) LEDGER⟧ entry 1) and is charged, with the trivial half's `(4/3)^{j₀}` piece,
   against the head's first summand — ⟦G2⟧ at `108/5·Fan + 432/5·arcDen`.

Both gates are thresholds on WITNESSED envelopes, `H`-only and one-sided. -/
theorem m4_chiSummedBlockN_of_shiftBlock {R : ChowlaRegime} {M : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ^ 7 ≤ Ftr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      108 / 5 * Fan H + 432 / 5 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ))
    (hfix : M4ChiSummedFreeShiftBlock R M F) :
    M4ChiSummedBlockMeanSqN R M (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi L hLH hnar q hq hqQ A B hA hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H :=
    m4BclGraded_nonneg (hFan0 H) (hFtr0 H)
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have harc30 : (0 : ℝ) < arcDen 12 H ^ 3 := by positivity
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left
      (by have := harc8 H hlo hhi; linarith :
        arcDen 12 H ^ 3 * 8 ≤ arcDen 12 H ^ 3 * (L : ℝ)) harc30
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    have hzero : ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2 = 0 := by
      intro χ
      rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    rw [Finset.sum_congr rfl (fun χ _ => hzero χ), Finset.sum_const, smul_zero]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  set X : DirichletCharacter ℂ q → ℕ → ℕ → ℕ → ℝ := fun χ j t n =>
    ‖∑ m ∈ doorSievedWindow M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set Y : ℕ → ℕ → ℕ → ℝ := fun j t n => ∑ χ : DirichletCharacter ℂ q, X χ j t n with hY
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound per character, with the sums already commuted
  have hchi : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
        ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
    intro χ
    have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
        ≤ ∑ n ∈ Finset.Ioc A B, SL
            * ∑ j ∈ Finset.range (Lg + 1),
                (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j :=
      Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic χ M L n
    have hswap : ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm
    exact hswap ▸ hstep1
  -- ⟦STEP 1′⟧ the character sum, taken through the assembly
  have hsummed : ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum fun χ _ => hchi χ) (le_of_eq ?_)
    calc ∑ χ : DirichletCharacter ℂ q, SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ χ : DirichletCharacter ℂ q, ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1), ∑ χ : DirichletCharacter ℂ q,
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.sum_comm]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_comm]
  -- ⟦STEP 2⟧ each (scale, offset) pair is a shifted fixed-length block sum, summed over χ
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshiftY : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      = ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2 := by
    intro j t
    rw [hY, Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => ?_
    exact sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2)
      A B _
  -- ⟦the analytic half: the χ-summed datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshiftY j t]
    have hd := hfix H hlo hhi L hLH q hq hqQ j hjLg (2 ^ (j + 1) * t) (hsle j t ht) A B hA
      (by omega) hfit
    have hFle := han j H hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, φ(q) times⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      ≤ arcDen 12 H * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshiftY j t]
    have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro χ _
      have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
            ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
        intro n _
        have h := norm_sum_doorSievedWindow_le χ M (2 ^ j) n
        have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
        nlinarith
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
        have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
        exact_mod_cast hnat
      have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
      nlinarith
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletCharacter_nat q] at hsum
    have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have hmid : (q.totient : ℝ) * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        ≤ arcDen 12 H * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_right hφarc ?_
      positivity
    nlinarith [hsum, hmid]
  -- ⟦STEP 3⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) := by
          ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            arcDen 12 H * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (arcDen 12 H * (A : ℝ)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((arcDen 12 H * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 4⟧ THE SPLIT
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H) := by
    have := hFan0 H; nlinarith
  have harcA0 : (0 : ℝ) ≤ arcDen 12 H * (A : ℝ) := by positivity
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg harcA0 (hWw0 j))
      _ = (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, then the mirrored ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hg0 : (0 : ℝ) < (3 / 2 : ℝ) ^ (Nat.log 2 H) := by positivity
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, at `arcDen³`⟧ the two consequences the mirrored weighted head needs
  have harc2 : (1 : ℝ) ≤ arcDen 12 H ^ 2 := by nlinarith
  have harc3 : (1 : ℝ) ≤ arcDen 12 H ^ 3 := by nlinarith
  have hG1H := hG1 H hlo hhi
  have hFtrL : 2 * arcDen 12 H * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have hchain : 2 * arcDen 12 H * (H : ℝ) ≤ 2 * arcDen 12 H ^ 4 * (L : ℝ) := by
      have h1 : 2 * arcDen 12 H * (H : ℝ)
          ≤ 2 * arcDen 12 H * (arcDen 12 H ^ 3 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hnar (by positivity)
      nlinarith [h1]
    have hle47 : arcDen 12 H ^ 4 ≤ arcDen 12 H ^ 7 := by
      calc arcDen 12 H ^ 4 = arcDen 12 H ^ 4 * 1 := by ring
        _ ≤ arcDen 12 H ^ 4 * arcDen 12 H ^ 3 :=
            mul_le_mul_of_nonneg_left harc3 (by positivity)
        _ = arcDen 12 H ^ 7 := by ring
    have hle : 2 * arcDen 12 H ^ 4 ≤ 2 * arcDen 12 H ^ 7 := by linarith
    have hstep : 2 * arcDen 12 H ^ 4 * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (le_trans hle hG1H) hL0R.le
    linarith
  have hFtrL2 : arcDen 12 H * (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H ^ 3 * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    have hstep : arcDen 12 H * (H : ℝ) ^ 2 ≤ arcDen 12 H ^ 7 * (L : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq harc0.le]
    have hstep2 : arcDen 12 H ^ 7 * (L : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hG1H (sq_nonneg ((L : ℝ)))]
    linarith
  -- ⟦the first budget line⟧
  have hEkey : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg) * (H : ℝ)
        ≤ arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H))
            * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ)))
      nlinarith [h, hH0R.le]
    have hmain : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H))
          * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
        + arcDen 12 H * (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hg2 := hG2 H hlo hhi
    have hstep : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
          ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hg2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ)
            * (arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg))) := by
      have hbig : (1 : ℝ) ≤ arcDen 12 H * (3 / 2 : ℝ) ^ Lg := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbig
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧
  have hres2 : arcDen 12 H * (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
              * (arcDen 12 H * (H : ℝ) ^ 2) := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * arcDen 12 H * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
            * (arcDen 12 H * (H : ℝ) ^ 2)
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (54 / 5 * (L : ℝ) ^ 2)
        + (arcDen 12 H * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := hsummed
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (arcDen 12 H * (A : ℝ)) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by
        ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (54 / 5 * (L : ℝ) ^ 2)
          + (arcDen 12 H * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead harcA0
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-! ## §4 — THE ASSEMBLED χ-SUMMED SUPPLY

The two mirrors composed: the socket → the χ-summed shifted family (§2) → the χ-summed
block mean square (§3).  The grade emitted is `m4BclGraded j₀ (2·RSan) (2·RStr)` — the same
SHAPE the landed per-χ arm emits, so the stratified consumer reads a familiar object. -/

/-- **THE χ-SUMMED SUPPLY, ASSEMBLED** (`m4_chiSummedN_supplied`).

⟦THE CONSUMPTION LIST⟧, beyond the socket: the two envelope nonnegativities, the analytic
envelope gate `RS j H ≤ RSan H` at `j₀ ≤ j`, and the three `H`-only class-(a) gates — ⟦G1⟧
at `arcDen³` (the mirror's price, `M4CoprimeSupply`'s `arcDen²` plus one character-count
power), ⟦G2⟧ at `44·RSan + 87·arcDen`, and the regime fact `8·arcDen ≤ H`. -/
theorem m4_chiSummedN_supplied {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    {RSan RStr : ℕ → ℝ} (j₀ : ℕ)
    (hRSan0 : ∀ H : ℕ, 0 ≤ RSan H) (hRStr0 : ∀ H : ℕ, 0 ≤ RStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ))
    (hrow : M4ChiSummedFreeRow R M RS) :
    M4ChiSummedBlockMeanSqN R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) := by
  refine m4_chiSummedBlockN_of_shiftBlock (F := fun j H => 2 * RS j H) j₀ ?_ ?_ ?_ ?_ ?_ harc8
    (m4_chiSummedShiftBlock_of_freeRow hrow)
  · intro H; have := hRSan0 H; linarith
  · intro H; have := hRStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro H hlo hhi; have := hG1 H hlo hhi; linarith
  · intro H hlo hhi
    have hg2 := hG2 H hlo hhi
    have h0 := hRSan0 H
    have harc := arcDen_nonneg 12 H
    linarith

end Salt.MR

end
