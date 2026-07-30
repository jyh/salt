/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TLegExit
import Salt.MR.USetChiTS

/-!
# TLegChi — the `χ`-FACTORIZATION PAGE: the graded `𝒯`-leg at twisted data (C5, wave A4)

`TLegExit`'s two exits — `TLeg_bound` (H-3) and `TLeg_feeds_capstone` (H-4) — are **fully
datum-generic**: they quantify over `∀ (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq) (Hseq) (η) …`
and never look inside the coefficient sequences.  Everything they ask of the datum is one of
four carried hypotheses:

1. the **Ramaré factorization** `a (p·m) = b j m · c p` on the block `P_j ≤ p ≤ Q_j`, `p ∤ m`;
2. the two **`1`-bounds** `‖b j m‖ ≤ 1`, `‖c p‖ ≤ 1`;
3. the **dyadic window** `c p · b j m ≠ 0 → X_d ≤ p·m ≤ 2X_d`;
4. the character-free ladder gates (`LevelGates`, `ramRbot`, `2 ≤ H₁`, `P₁ ≤ Q₁`, …).

So the `χ`-lift of the whole leg is an INSTANTIATION, not a port: this file hands the two
exits the twisted datum

  `c := chiBarCoeff q χ c₀`,  `a := chiBarCoeff q χ a₀`,  `b j := chiBarCoeff q χ (b₀ j)`

and lifts (1)–(3).  Item (4) is untouched — the gates never mention the datum.  (This is
C2-SCOPE's ⟦THE 𝒯-LEG RE-PRICE⟧: the census item was misdiagnosed as a 1.5–3k class-C lift of
the `𝒯`-machinery; the missing half was always the GRADED A3, not this leg.)

## Where the character actually enters, and where it does not

* **(1) lifts by COMPLETE MULTIPLICATIVITY of the twist and nothing else.**  `χ̄` is
  `conj ∘ χ` with `χ` a `MulChar` on `ZMod q`, so `χ̄(p·m) = χ̄(p)·χ̄(m)` at EVERY pair of
  naturals — no coprimality, no unit hypothesis, no `NeZero q`
  (`HybridMoments.conj_chi_natCast_mul`, LANDED).  The factorization then re-associates:
  `χ̄(pm)·a(pm) = (χ̄(m)·b j m)·(χ̄(p)·c p)`, which is exactly the twisted `b`-slot against the
  twisted `c`-slot (`HybridMoments.chiBar_hcoef`, LANDED at one block — this file owes only
  the level-indexed repackaging).  **The prime factor keeps the `c`-slot and the co-factor
  keeps the `b`-slot** — the twist does not move the seam.
* **(2) lifts by `‖χ̄(n)‖ ≤ 1`** (`HybridMoments.norm_chiBarCoeff_le_one`); this is the one
  place `[NeZero q]` is needed (`DirichletCharacter.norm_le_one` wants the modulus nonzero),
  and it is supplied from `0 < q` inside each proof rather than carried in the statements.
* **(3) lifts because the twisted support is a SUBSET of the untwisted one**: a product of
  twisted coefficients is nonzero only if both untwisted coefficients are
  (`chiBarCoeff_window`).  The window is therefore twist-invariant in the direction the leg
  consumes it, with no gate added.
* **NO `φ(q)` is spent anywhere in this file.**  The per-`χ` conclusions are character-uniform
  in shape and in every constant; the only place a `φ(q)` appears is the summed corollary,
  where it rides VISIBLY as `S.card` / `q.totient` in front of the two character-free terms
  (A2's discipline: the ledger factor is never absorbed).

## The partition datum is per-`χ`, automatically — design (ii)'s fibrewise shape

`TLeg_bound`'s partition set is `seamTtotG c Pseq Qseq Hseq (mrAlpha η) Jb` at `fb := c`, the
Ramaré prime coefficient the block factor carries (MR (21)'s gain bites at that datum or not
at all).  Under the twist the datum becomes `chiBarCoeff q χ c₀`, so the leg's set is
**`𝒯totG(χ̄c₀)` — one set per character**, which is precisely C2's ratified fibrewise
spelling `𝔄 : Set (DirichletCharacter ℂ q × ℝ)` read as `χ ↦ 𝔄_χ`.  Nothing has to be
arranged for this: it falls out of the instantiation.

## Scope (the honest fence)

This page is the LEG'S SUPPLY ONLY.  It stops exactly where `TLegExit` stops: the closed
`𝒯`-leg bound and the capstone feed, now at twisted data.  The row assembly (the `q = 1`
consumer is `SeamNumber.seam_row_number`, which fuses the leg's exit with
`TypicalPriceK`'s pricing of `Σ_j lemma12Rows` under six `X_d`-side reconciliation gates) is
**not attempted here** — the twisted pricing side does not exist yet, and manufacturing a
per-`χ` fuse before it does would be a vacuous composition.  `TLeg_feeds_capstone_chi`
carries the graded capstone row as a hypothesis for the same reason its `q = 1` parent does
(see `TLegExit`'s H-4 docstring: the shapes fit; the simultaneous satisfiability of the two
gate families is a station-level reconciliation, recorded, not hidden).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §8.1–§8.2 pp. 25–27, p.24 (eq (20));
`docs/blueprints/flags.md` ⟦THE 𝒯-LEG RE-PRICE⟧ (C2-SCOPE, 2026-07-30) and THE 0730 COUNCIL
(C5); `Salt/MR/HybridMoments.lean` §1 (the `χ̄`-twisted datum), `Salt/MR/USetChiTS.lean` §1
(the landed twisted `ramR` bridges).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — the three datum lifts

The whole content of the page: complete multiplicativity (`§1.1`), the norm bound (`§1.2`)
and the support inclusion (`§1.3`).  Each is stated in the EXACT shape `TLegExit`'s two exits
carry it, so the instantiations of §2–§3 are `exact`-level. -/

/-! ### §1.1 — complete multiplicativity of the twist

Both halves are LANDED in `HybridMoments`: `conj_chi_natCast_mul` (`χ̄(mn) = χ̄(m)χ̄(n)` at
every pair of naturals — `Nat.cast_mul` then two `map_mul`s; no coprimality, no unit
hypothesis, no `NeZero q`) and `chiBar_hcoef` (the one-block factorization lift).  Only the
LEVEL-INDEXED repackaging is owed here — `TLegExit` carries the hypothesis as a family over
`j ∈ [1, Jb]` with `(P_j, Q_j, b j)` varying, and `chiBar_hcoef`'s `P`/`Q`/`b` are implicit,
so the family lift is one `fun`. -/

/-- **THE FACTORIZATION LIFT, in `TLegExit`'s carried shape.**  The level-indexed Ramaré
hypothesis of `TLeg_bound`/`TLeg_feeds_capstone`, transported to twisted data with every
side condition (`p.Prime`, `P_j ≤ p ≤ Q_j`, `p ∤ m`) untouched — the twist is blind to all
four.  `HybridMoments.chiBar_hcoef` at each level. -/
lemma chiBarCoeff_ramare (q : ℕ) (χ : DirichletCharacter ℂ q) (c a : ℕ → ℂ)
    (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Jb : ℕ)
    (hcoef : ∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
      a (p * m) = b j m * c p) :
    ∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
      chiBarCoeff q χ a (p * m)
        = chiBarCoeff q χ (b j) m * chiBarCoeff q χ c p :=
  fun j hj => chiBar_hcoef q χ (hcoef j hj)

/-! ### §1.2 — the `1`-bounds -/

/-- The `b`-family's `1`-bound lifts level by level (`‖χ̄(m)·b j m‖ ≤ ‖b j m‖ ≤ 1`). -/
lemma chiBarCoeff_bfam_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {b : ℕ → ℕ → ℂ} (hb : ∀ j m, ‖b j m‖ ≤ 1) : ∀ j m, ‖chiBarCoeff q χ (b j) m‖ ≤ 1 :=
  fun j m => norm_chiBarCoeff_le_one χ (fun n => hb j n) m

/-- The prime coefficient's `1`-bound lifts (`‖χ̄(p)·c p‖ ≤ ‖c p‖ ≤ 1`). -/
lemma chiBarCoeff_cseq_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {c : ℕ → ℂ} (hc : ∀ p, ‖c p‖ ≤ 1) : ∀ p, ‖chiBarCoeff q χ c p‖ ≤ 1 :=
  fun p => norm_chiBarCoeff_le_one χ hc p

/-! ### §1.3 — the dyadic window -/

/-- **THE WINDOW LIFT.**  `TLegExit`'s support hypothesis is stated as an implication out of
`c p · b j m ≠ 0`, and the twisted product is nonzero only when both untwisted coefficients
are — so the twisted window follows from the untwisted one with NO gate added and no
hypothesis on `χ` (a vanishing character value only shrinks the support). -/
lemma chiBarCoeff_window (q : ℕ) (χ : DirichletCharacter ℂ q) (c : ℕ → ℂ)
    (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Jb Xd : ℕ)
    (hwin : ∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
      c p * b j m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) :
    ∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
      chiBarCoeff q χ c p * chiBarCoeff q χ (b j) m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) := by
  intro j hj p m hp hP hQ hne
  rw [chiBarCoeff_apply, chiBarCoeff_apply] at hne
  exact hwin j hj p m hp hP hQ
    (mul_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
      (right_ne_zero_of_mul (right_ne_zero_of_mul hne)))

/-! ## §2 — the graded `𝒯`-leg at twisted data (H-3 at `χ̄`) -/

/-- **THE `χ`-TWISTED GRADED `𝒯`-LEG** (`TLeg_bound_chi`).

`TLegExit.TLeg_bound` at the twisted datum `(χ̄c₀, χ̄a₀, χ̄b₀)`.  The hypotheses are stated on
the UNTWISTED sequences — that is the point of the page: a consumer holding the Ramaré
factorization of the actual seam coefficient gets the bound for the twisted polynomial, and
pays nothing for the twist.

* the constant `C` is the SAME universal constant `TLeg_bound` produces (it is bound outside
  `q` and outside `χ`): **character-uniform, modulus-uniform**;
* the bound's right-hand side is `TLeg_bound`'s verbatim, with the coefficient sequences
  twisted only inside `lemma12Rows` — the level-1 term and the `1536·C·e³(2T/X_d+240)/P₁` term
  are character-FREE;
* the integration set is `𝒯totG(χ̄c₀)`, one set per character (see the module header). -/
theorem TLeg_bound_chi :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q)
      (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jb N Xd P1 : ℕ) (X T t₁ : ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jb → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jb, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      -- ⟦THE RAMARÉ FACTORIZATION, UNTWISTED⟧
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
        a (p * m) = b j m * c p) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
        c p * b j m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      (∫ t in (seamAnn X T \ seamBall X t₁)
          ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq (mrAlpha η) Jb,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
              * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
              * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
              * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                    * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                  + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
          + 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) * (1 / (P1 : ℝ))
          + ∑ j ∈ Finset.Icc 1 Jb,
              lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T (chiBarCoeff q χ a)
                (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c) := by
  obtain ⟨C, hC, hleg⟩ := TLeg_bound
  refine ⟨C, hC, ?_⟩
  intro q hq χ c a b Pseq Qseq Hseq η Jb N Xd P1 X T t₁ hη h6 hJb hXd hN hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin
  haveI : NeZero q := ⟨by omega⟩
  exact hleg (chiBarCoeff q χ c) (chiBarCoeff q χ a) (fun j => chiBarCoeff q χ (b j))
    Pseq Qseq Hseq η Jb N Xd P1 X T t₁ hη h6 hJb hXd hN hT hP1 hG hH1 hP1s hPQ1 hbot1
    (chiBarCoeff_ramare q χ c a b Pseq Qseq Jb hcoef)
    (chiBarCoeff_bfam_le_one χ hb) (chiBarCoeff_cseq_le_one χ hc)
    (chiBarCoeff_window q χ c b Pseq Qseq Jb Xd hwin)

/-! ## §3 — the seam row in closed shape at twisted data (H-4 at `χ̄`) -/

/-- **THE `χ`-TWISTED SEAM ROW IN CLOSED SHAPE** (`TLeg_feeds_capstone_chi`).

`TLegExit.TLeg_feeds_capstone` at the twisted datum.  The carried capstone row is
`GradedCapstone.hUG34_unconditional`'s conclusion at the twisted polynomial and the twisted
partition datum (`fb := χ̄c₀`, `αseq := mrAlpha η`); the conclusion replaces its `𝒯`-integral
by §2's bound.  As in the `q = 1` parent, what the kernel certifies is the SHAPE fit and the
composition — not the simultaneous satisfiability of the two gate families (module header). -/
theorem TLeg_feeds_capstone_chi :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q)
      (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jset N Xd P1 : ℕ) (X Tann t₁ S ε : ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jset → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ Tann → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jset, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      -- ⟦THE RAMARÉ FACTORIZATION, UNTWISTED⟧
      (∀ j ∈ Finset.Icc 1 Jset, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
        a (p * m) = b j m * c p) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jset, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
        c p * b j m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      -- ⟦THE CAPSTONE ROW⟧ at `fb := χ̄c₀` and `αseq := mrAlpha η`, twisted polynomial
      (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq (mrAlpha η) Jset,
                ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) →
      (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 8 * S ^ 2
          + (2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
                * (Tann * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
                * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
                * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                      * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                    + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
              + 1536 * C * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240) * (1 / (P1 : ℝ))
              + ∑ j ∈ Finset.Icc 1 Jset,
                  lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) Tann (chiBarCoeff q χ a)
                    (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c))
          + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨C, hC, hfeed⟩ := TLeg_feeds_capstone
  refine ⟨C, hC, ?_⟩
  intro q hq χ c a b Pseq Qseq Hseq η Jset N Xd P1 X Tann t₁ S ε hη h6 hJ hXd hN hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin hcap
  haveI : NeZero q := ⟨by omega⟩
  exact hfeed (chiBarCoeff q χ c) (chiBarCoeff q χ a) (fun j => chiBarCoeff q χ (b j))
    Pseq Qseq Hseq η Jset N Xd P1 X Tann t₁ S ε hη h6 hJ hXd hN hT hP1 hG hH1 hP1s hPQ1 hbot1
    (chiBarCoeff_ramare q χ c a b Pseq Qseq Jset hcoef)
    (chiBarCoeff_bfam_le_one χ hb) (chiBarCoeff_cseq_le_one χ hc)
    (chiBarCoeff_window q χ c b Pseq Qseq Jset Xd hwin) hcap

/-! ## §4 — the character-summed leg: the `φ(q)` in the open

The shape the per-`χ` partition chain consumes.  §2's two character-free terms are paid ONCE
per character, so they come out with the character count in front — `S.card` at a general
family, `q.totient` at the full family — and the `Σ_j lemma12Rows` stays under the `Σ_χ`,
where the twisted pricing side will meet it.  Nothing is absorbed into a constant (A2). -/

/-- **THE `𝒯`-LEG SUMMED OVER A CHARACTER FAMILY** (`TLeg_bound_chiSummed`).

§2 collected over any `S : Finset (DirichletCharacter ℂ q)`.  The left-hand side is the
fibrewise object — each character integrates its OWN partition set `𝒯totG(χ̄c₀)` — and the
right-hand side is `S.card` times the character-free part plus the honest `Σ_χ Σ_j` of
Lemma 12's rows.  The constant `C` is still the universal one (bound outside `q`, `S`, `χ`). -/
theorem TLeg_bound_chiSummed :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ (S : Finset (DirichletCharacter ℂ q))
      (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jb N Xd P1 : ℕ) (X T t₁ : ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jb → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jb, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
        a (p * m) = b j m * c p) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
        c p * b j m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      (∑ χ ∈ S, ∫ t in (seamAnn X T \ seamBall X t₁)
            ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq (mrAlpha η) Jb,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ (S.card : ℝ)
            * (2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
                  * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
                  * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                      + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
              + 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) * (1 / (P1 : ℝ)))
          + ∑ χ ∈ S, ∑ j ∈ Finset.Icc 1 Jb,
              lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T (chiBarCoeff q χ a)
                (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c) := by
  obtain ⟨C, hC, hper⟩ := TLeg_bound_chi
  refine ⟨C, hC, ?_⟩
  intro q hq S c a b Pseq Qseq Hseq η Jb N Xd P1 X T t₁ hη h6 hJb hXd hN hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin
  -- the character-free head of §2's right-hand side, named once
  set K : ℝ := 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
        * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
        * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
        * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
              * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
            + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
      + 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) * (1 / (P1 : ℝ)) with hK
  have hstep : ∀ χ ∈ S,
      (∫ t in (seamAnn X T \ seamBall X t₁)
          ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq (mrAlpha η) Jb,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ K + ∑ j ∈ Finset.Icc 1 Jb,
            lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T (chiBarCoeff q χ a)
              (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c) := by
    intro χ _
    rw [hK]
    exact hper q hq χ c a b Pseq Qseq Hseq η Jb N Xd P1 X T t₁ hη h6 hJb hXd hN hT hP1 hG
      hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum

/-- **THE `𝒯`-LEG SUMMED OVER ALL `φ(q)` CHARACTERS** (`TLeg_bound_chi_totient`).

`TLeg_bound_chiSummed` at `S := Finset.univ`, with the count named:
`#{χ mod q} = φ(q)` (`DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity` over `ℂ`).
The `φ(q)` rides visibly in front of the two character-free terms and is compared to nothing
(A2: no ledger page here). -/
theorem TLeg_bound_chi_totient (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 < C ∧ ∀ (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jb N Xd P1 : ℕ) (X T t₁ : ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jb → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jb, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
        a (p * m) = b j m * c p) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
        c p * b j m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      (∑ χ : DirichletCharacter ℂ q, ∫ t in (seamAnn X T \ seamBall X t₁)
            ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq (mrAlpha η) Jb,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ (q.totient : ℝ)
            * (2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
                  * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
                  * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                      + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
              + 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) * (1 / (P1 : ℝ)))
          + ∑ χ : DirichletCharacter ℂ q, ∑ j ∈ Finset.Icc 1 Jb,
              lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T (chiBarCoeff q χ a)
                (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c) := by
  obtain ⟨C, hC, hsum⟩ := TLeg_bound_chiSummed
  refine ⟨C, hC, ?_⟩
  intro c a b Pseq Qseq Hseq η Jb N Xd P1 X T t₁ hη h6 hJb hXd hN hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ)
      = (q.totient : ℝ) := by
    rw [Finset.card_univ, card_dirichletChar q]
  have h := hsum q hq Finset.univ c a b Pseq Qseq Hseq η Jb N Xd P1 X T t₁
    hη h6 hJb hXd hN hT hP1 hG hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin
  rw [hcard] at h
  exact h

end Salt.MR
