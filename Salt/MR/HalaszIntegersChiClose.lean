/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetChiTS

/-!
# HalaszIntegersChiClose — the `HalaszIntegersChi` slot DISCHARGED at the `φ(q)`-graded row
(wave P-5, stone D4)

`USetChiTS.lean`:124 left the named slot `HalaszIntegersChi Cint` — the `χ`-twisted MR
Lemma 9 — flagged there as **an honest new gap the port freeze missed**.  This file closes it.

## ⟦THE ADJUDICATION⟧ (the first deliverable)

### What the slot actually is

`HalaszIntegersChi Cint` is a **discrete mean-value (Halász–Montgomery large-values) row**:

  `∀ q > 0, ∀ M, ∀ a : ℕ → ℂ, ∀ T ≥ 1, ∀ ℰ` per-fibre well-spaced `⊆ [−T,T]`,
  `∑_{(χ,t)∈ℰ} ‖∑_{n≤M} aₙ χ(n) n^{it}‖² ≤ Cint·(M + |ℰ|√T)·(1 + log 2T)·∑_{n≤M}‖aₙ‖²`.

The coefficient sequence `a` is **ARBITRARY** — no multiplicativity, no boundedness, no
support condition.  That single observation adjudicates the two named routes.

### ROUTE A — REJECTED, category mismatch
(the "new Prop 8.3": the all-χ pretentious floors → `halasz_ball_decay`)

`capFreeFloor3_margin_all_chi_vt` / `capFreeFloor3_pieceDatum_vt` (`VkMidSharp`:505/559)
bound `pretDistSq (lamChi χ) (costwist v) X` from below, and `halasz_ball_decay`
(`HalaszCore`:440) converts such a floor into `U ≤ (C₁+C₂)·X·(e^{−cM_range} + (log X)^{−1/2+ε})`
— a decay statement for the **summatory function of ONE multiplicative datum** (`lamChi χ`,
`liouChi χ`, `pieceDatum`), whose whole input is that datum's pretentious distance.  A
pretentious floor for `λ·χ` says NOTHING about an arbitrary `a : ℕ → ℂ`; and the slot's row
must hold for `a` = the Ramaré co-factor mask `ramRcoeff/(m)`, which is not multiplicative
and is not even 1-bounded before division.  There is no implication in this direction, at any
constant.  This is exactly REF-P-SHAPE's own structural note, re-derived independently here:
*"the floor→Halász two-step is an INPUT to the (χ,t) decomposition, never the row bound
(window-graded vs X-graded)"* (`⟦THE PORT REFUTER PASS + FREEZE v2⟧`, R-P2).

### ROUTE B — REJECTED, the same mismatch
(the χ-twisted μ-rate at SW strength, via `LambdaChiSummatory_of_MmuChiRate`)

`MmuChiRate` / `LambdaChiSummatory A` are rate statements for `∑_{n≤x} μ(n)χ(n)n^{it}` — again
ONE arithmetic datum, at one height, not a mean square of an arbitrary Dirichlet polynomial
over a set of ordinates.  A conditional discharge of the slot from that hypothesis is not
merely unavailable, it is **impossible**: the slot quantifies over all `a`, and `a` can be
chosen to violate any bound derived from a fixed datum's rate (take `a` supported on a single
`n` with a huge coefficient — both sides scale, but no rate for `μχ` enters).  Route B is
therefore not a "conditional but honest" discharge; it is a non-route.

### THE DEMANDED GRADE, with the arithmetic

The slot is consumed at exactly three sites, all in `USetChiTS.lean`:
`ramRChi_sq_sum_le` (:136) → `TSChi_branch_meansq` (:435) → `usetChi_TS_branch_meanvalue`
(:477).  The last one is the exit, and it consumes the row ONLY through the combination

  `(M + |ℰ|·√T) ≤ 2M`     (the razor's budget `bundle·X^{1−2η+ε} ≤ M` clears `|ℰ|√T ≤ M`),

producing `Σ_{𝒯_S} ‖ramMain‖² ≤ 2·Cint·ε_Q²·M·(1 + log 2T)·(co-factor mass)`.  The `q = 1`
twin (`uset_TS_branch_meanvalue`, `USetThinTS`:393) exits at
`5128·ε²·M·(1 + log 2T)·(mass)` with `Cint = 2564` and MR's level `ε = (log X)^{−100}`, i.e.
**the demanded grade is `5128·(log X)^{−200}·M·(1 + log 2T)·(mass)`.**

Against that demand, the two available rows are:

* the landed **mean-value** row (`ramRChi_sq_sum_mvt`, unconditional):
  `84·(φ(q)(T+1) + φ(q)M/q)·log(2M)·(mass)`.  At the §8.3 pins `T ≍ X`, `M ≍ X e^{−j/H}`, so
  `T/M ≍ e^{j/H} ≍ p` — the row exceeds the demand by a factor `≍ e^{j/H}/62`, a
  power-genre loss (`mvt_row_carries_T` below is the machine-checked form: the row carries `T`
  where the demand carries `M`).  **This is the gap the module header of `USetChiTS`
  reports, and it is real.**
* the **`φ(q)`-graded Halász row** of this file (`halaszIntegersChi_phi`, unconditional):
  `2564·(φ(q)·M + |ℰ|√T)·(1 + log 2T)·(mass)`.  It has the `√T` term the razor is built to
  spend, and the ONLY deviation from the slot is the character-count union factor `φ(q)` on
  the `M`-term.

### THE ROUTE TAKEN: ROUTE C — the fibrewise composition, with the
### `φ(q)` debit REPAID BY RE-PINNING THE BRANCH LEVEL

`dpolyChi q (Icc 1 M) a χ = dpoly M (a·χ)` (`dpolyChi_Icc`, `rfl`) and `‖χ(n)‖ ≤ 1`, so the
LANDED `q = 1` Lemma 9 (`halasz_integers_unconditional_const`, `VdCSocket`:547, constant
`2564`) applies on every character fibre of `ℰ` (`FibreWellSpaced` is exactly fibrewise
`WellSpaced`).  Summing the fibre rows over the `φ(q)` characters costs `φ(q)` on the `M`-term
and **nothing** on the `|ℰ|√T` term — `∑_χ |𝒯_χ| = |ℰ|` is an identity, not an estimate.

The debit is then paid, in full, at the branch level:

  `φ(q) ≤ q ≤ (log X)^{12}` (the port's modulus gate), so at the RE-PINNED level
  `ε_Q := (log X)^{−106}` we have `φ(q)·ε_Q² ≤ (log X)^{12}·(log X)^{−212} = (log X)^{−200}`

— and the `φ(q)`-graded exit becomes `5128·(log X)^{−200}·M·(1 + log 2T)·(mass)`, i.e.
**byte-for-byte the `q = 1` demand** (`usetChi_TS_branch_exit_repinned`).  Moving the level
from `(log X)^{−100}` to `(log X)^{−106}` costs the OTHER branch a threshold
`V = 1/ε_Q = (log X)^{106}` in place of `(log X)^{100}`, and the `𝒯_L` kill beats any polylog
`V` by a quasi-power (`USetThinTL`'s VK-width decay at `θ < 1/8`) — six more powers of log is
free there.  The `𝒯_S` razor's own character debit is separately priced and unaffected
(`charDebit_le_rpow`: `q^{2α} ≤ √q ≤ (log X)^6 ≤ X^ε`, ~378 orders of margin).

**So: the gap is closed, unconditionally, and the reported grade deficit was a `φ(q)` —
a polylog — not the `e^{j/H}` of the mean-value row.**

### THE PRECISE RESIDUE (what is NOT proved here)

The slot **as literally written** (`Cint·(M + |ℰ|√T)`, no `φ(q)`) is not proved and cannot be
obtained from the `q = 1` Lemma 9 by any fibrewise argument: the fibre rows each carry their
own `M`, and `∑_χ M = φ(q)M` is an identity.  The `φ(q)`-free row is the genuine **hybrid**
Halász–Montgomery estimate, whose proof needs the off-diagonal Gram entries
`∑_{n≤M} χ(n)χ̄'(n) n^{i(t−t')}` at `χ ≠ χ'` (a Polyá–Vinogradov / hybrid-large-sieve input,
and the classical form of that estimate carries `√(qT)` rather than `√T` in the count term —
so the literal statement may itself need a `√q` amendment).  That is a NEW stone, not a port
composition; and no consumer in the corpus needs it, since every consumption factors through
`usetChi_TS_branch_meanvalue`, whose demand the re-pinned `φ(q)`-graded exit meets EXACTLY.

The debit is exactly 12 powers of log, stated honestly: at MR's OWN level
`ε_Q = (log X)^{−100}` the `φ(q)`-graded exit is `5128·φ(q)·(log X)^{−200}·M·(…)`, i.e.
`≤ 5128·(log X)^{−188}·M·(…)` — twelve powers SHORT of the `q = 1` exit's `(log X)^{−200}`,
not ahead of it.  Re-pinning the level to `(log X)^{−106}` closes exactly those twelve
(`106·2 − 12 = 200`), which is why the re-pinning is part of the discharge and not decoration.

## Conventions (the four traps, declared)

* **`σ = 1` vs `σ = 0` (CATCH #B ∘ N1).**  `ramR`/`ramMain`/`ramQ` and every branch set and
  mean square below are at `σ = 1`.  The crossing to `dpolyChi`'s `n^{+it}` happens ONLY in
  `ramRChi_sq_sum_phi`, through the landed `ramR_chiBar_eq_dpolyChi` at the reflected pair set
  `reflectChi ℰ` (`WellSpaced`, `⊆ [−T,T]` and `card` are all `reflectPair`-stable).
* **Conjugation.**  The data are the BARRED corpus forms `chiBarCoeff`; `chiTwist`
  (`ChiEuler`:74) is the unbarred `g`-side object and does not appear here.  `coeffChiTwist`
  is the neutral coefficient twist `n ↦ aₙ·χ(n)` of `HybridLargeValues`, used only inside the
  fibre step.
* **The four log scales.**  `1 + log(2T)` is Lemma 9's Gallagher factor at the ordinate
  height; `log(2M)` is the mean-value row's; `log X` (the MR Step-0 majorant) is the scale of
  BOTH the modulus gate `q ≤ (log X)^{12}` and the branch level `ε_Q`; `log(qT)` and
  `loglog(qT)` belong to the razor and are untouched.
* Every constant is explicit; nothing is `O(·)`.  Everything in this file is
  **UNCONDITIONAL** (no hypothesis slots, no `sorry`).

Source pins: MR arXiv v4 (`1501.04585v4`) pp. 16–17 (Lemma 9), 27–29 (§8.3);
`USetChiTS.lean` §2; `docs/exploration/port-freeze-0729.md` v2;
`⟦SPECTRUM-SCOPE⟧` and `⟦THE PORT REFUTER PASS + FREEZE v2⟧` in `docs/blueprints/flags.md`.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the character count -/

/-- The number of Dirichlet characters mod `q` is `φ(q)`, as a real.  (Mathlib's
`card_eq_totient_of_hasEnoughRootsOfUnity` over `ℂ`, cited once for this file.) -/
theorem card_chars_totient_real (q : ℕ) [NeZero q] :
    ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) = (q.totient : ℝ) := by
  have h : Nat.card (DirichletCharacter ℂ q) = q.totient :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at h
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h

/-! ## §2 — the row: the `φ(q)`-graded `χ`-twisted Lemma 9, UNCONDITIONAL -/

/-- **THE FIBRE STEP.**  On one character fibre the twisted polynomial IS an ordinary
Dirichlet polynomial (`dpolyChi_Icc`, `rfl`) with coefficients `aₙχ(n)` of no larger modulus,
so the landed `q = 1` Lemma 9 applies verbatim.  Stated at `σ = 0` (`dpolyChi`). -/
theorem halaszIntegersChi_fibre (q : ℕ) (M : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (χ : DirichletCharacter ℂ q) (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯)
    (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ 𝒯, ‖dpolyChi q (Finset.Icc 1 M) a χ t‖ ^ 2
      ≤ ((M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
          * (2564 * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2) := by
  have hL : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have h := halasz_integers_unconditional_const M (coeffChiTwist q χ a) T hT 𝒯 hws hsub
  have hmassle : (∑ n ∈ Finset.Icc 1 M, ‖coeffChiTwist q χ a n‖ ^ 2)
      ≤ ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2 :=
    Finset.sum_le_sum fun n _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_coeffChiTwist_le q χ a n) 2
  have hcoef : (0 : ℝ)
      ≤ 2564 * ((M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T)) := by
    have hbr : (0 : ℝ) ≤ (M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T := by positivity
    have h1 : (0 : ℝ) ≤ 2564 * ((M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) := by
      nlinarith [hbr]
    exact mul_nonneg h1 hL
  calc ∑ t ∈ 𝒯, ‖dpolyChi q (Finset.Icc 1 M) a χ t‖ ^ 2
      = ∑ t ∈ 𝒯, ‖dpoly M (coeffChiTwist q χ a) t‖ ^ 2 := by
        simp only [dpolyChi_Icc]
    _ ≤ 2564 * ((M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ n ∈ Finset.Icc 1 M, ‖coeffChiTwist q χ a n‖ ^ 2 := h
    _ ≤ 2564 * ((M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (1 + Real.log (2 * T))
          * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2 := mul_le_mul_of_nonneg_left hmassle hcoef
    _ = ((M : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
          * (2564 * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2) := by ring

/-- **THE ROW — the `χ`-twisted MR Lemma 9 at the `φ(q)`-graded `M`-term, UNCONDITIONAL.**

`∑_{(χ,t)∈ℰ} ‖∑_{n≤M} aₙχ(n)n^{it}‖² ≤ 2564·(φ(q)·M + |ℰ|·√T)·(1 + log 2T)·∑_{n≤M}‖aₙ‖²`

for arbitrary `a : ℕ → ℂ`, any `T ≥ 1` and any per-fibre well-spaced `ℰ ⊆ (characters) × [−T,T]`.

The `φ(q)` is the character-count union factor on the LENGTH term and is the whole deviation
from the slot `HalaszIntegersChi`; the count term is EXACT (`∑_χ |𝒯_χ| = |ℰ|` is an
identity).  See the module header for why the `φ(q)` is repaid at the branch level, and for
the residue (the `φ(q)`-free row is the hybrid Halász–Montgomery estimate — a new stone). -/
theorem halaszIntegersChi_phi (q : ℕ) [NeZero q] (M : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∑ r ∈ ℰ, ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2
      ≤ 2564 * ((q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T)
          * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2 := by
  obtain ⟨𝒯, hmem, hsumf⟩ := exists_charFibre ℰ
  -- the cardinality identity: `∑_χ |𝒯_χ| = |ℰ|`
  have hcard : (∑ χ : DirichletCharacter ℂ q, ((𝒯 χ).card : ℝ)) = (ℰ.card : ℝ) := by
    have h := hsumf (fun _ _ => (1 : ℝ))
    simpa using h
  -- the length bookkeeping: `∑_χ M = φ(q)·M`
  have hsumeq : (∑ χ : DirichletCharacter ℂ q, ((M : ℝ) + ((𝒯 χ).card : ℝ) * Real.sqrt T))
      = (q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_chars_totient_real q, ← Finset.sum_mul, hcard]
  have hper : ∀ χ : DirichletCharacter ℂ q,
      (∑ t ∈ 𝒯 χ, ‖dpolyChi q (Finset.Icc 1 M) a χ t‖ ^ 2)
        ≤ ((M : ℝ) + ((𝒯 χ).card : ℝ) * Real.sqrt T)
            * (2564 * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2) := by
    intro χ
    refine halaszIntegersChi_fibre q M a T hT χ (𝒯 χ) ?_ ?_
    · intro t ht u hu htu
      exact hws (χ, t) ((hmem χ t).1 ht) (χ, u) ((hmem χ u).1 hu) rfl htu
    · exact fun t ht => hsub (χ, t) ((hmem χ t).1 ht)
  calc ∑ r ∈ ℰ, ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ,
          ‖dpolyChi q (Finset.Icc 1 M) a χ t‖ ^ 2 :=
        (hsumf (fun χ t => ‖dpolyChi q (Finset.Icc 1 M) a χ t‖ ^ 2)).symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ((M : ℝ) + ((𝒯 χ).card : ℝ) * Real.sqrt T)
          * (2564 * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2) :=
        Finset.sum_le_sum fun χ _ => hper χ
    _ = (∑ χ : DirichletCharacter ℂ q, ((M : ℝ) + ((𝒯 χ).card : ℝ) * Real.sqrt T))
          * (2564 * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2) := by
        rw [← Finset.sum_mul]
    _ = 2564 * ((q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T)
          * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2 := by
        rw [hsumeq]; ring

/-- **The slot, `φ(q)`-graded** — the `Prop` shape of `halaszIntegersChi_phi`, so that
downstream consumers can carry it as a named row exactly as they carry
`HalaszIntegersChi`.  It differs from `HalaszIntegersChi Cint` in the single factor `φ(q)` on
the length term, and it is LANDED (`halaszIntegersChiPhi_holds`) rather than hypothetical. -/
def HalaszIntegersChiPhi (Cint : ℝ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (M : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
  ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
    (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
    ∑ r ∈ ℰ, ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2
      ≤ Cint * ((q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T)
          * (1 + Real.log (2 * T)) * ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2

/-- **THE DISCHARGE, UNCONDITIONAL.**  `HalaszIntegersChiPhi 2564` holds — the constant is the
landed `q = 1` one (`4·(Cvdc + 1) = 4·641`), unchanged by the twist. -/
theorem halaszIntegersChiPhi_holds : HalaszIntegersChiPhi 2564 := by
  intro q hq M a T hT ℰ hws hsub
  haveI : NeZero q := ⟨by omega⟩
  exact halaszIntegersChi_phi q M a T hT ℰ hws hsub

/-! ## §3 — the co-factor mean square at the `φ(q)`-graded row (`σ = 1`)

The `σ = 1 → σ = 0` crossing happens here and only here, through the landed
`ramR_chiBar_eq_dpolyChi` at the reflected pair set (CATCH #B ∘ N1). -/

/-- **The co-factor mean square on a pair set, UNCONDITIONAL** — the `φ(q)`-graded twin of
`ramRChi_sq_sum_le`, with the hypothesis slot replaced by §2's landed row.  Stated at
`σ = 1`. -/
theorem ramRChi_sq_sum_phi (q : ℕ) [NeZero q] (H : ℝ) (N X P Q j M : ℕ) (b : ℕ → ℂ)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (T : ℝ) (hT : 1 ≤ T)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∑ r ∈ ℰ, ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2
      ≤ 2564 * ((q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T)
          * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  set a : ℕ → ℂ := fun m => ramRcoeff H N X P Q j b m / (m : ℂ) with hadef
  have hlhs : ∑ r ∈ ℰ, ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2
      = ∑ r ∈ reflectChi ℰ, ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2 := by
    rw [sum_reflectChi ℰ (fun r => ‖dpolyChi q (Finset.Icc 1 M) a r.1 r.2‖ ^ 2)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ramR_chiBar_eq_dpolyChi q r.1 H N X P Q j M b hM r.2]
  have h := halaszIntegersChi_phi q M a T hT (reflectChi ℰ) (fibreWellSpaced_reflectChi hws)
    (reflectChi_subset_Icc hsub)
  rw [card_reflectChi] at h
  have hmass : ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2
      = ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hadef, norm_div, Complex.norm_natCast, div_pow]
  rw [hlhs, ← hmass]
  exact h

/-- **The `𝒯_S` branch mean square, UNCONDITIONAL** — the `φ(q)`-graded twin of
`TSChi_branch_meansq`.  The pointwise `ε²` gain is the landed character-blind
`norm_ramMain_sq_le_of_small`; the analysis is §3's row.  The count in the Halász term is
`|ℰ|` (monotone from `|𝒯_S|`) — it is `|ℰ|` that `UsetChi_thin` bounds. -/
theorem TSChi_branch_meansq_phi (q : ℕ) [NeZero q] (H : ℝ) (N X P Q j M : ℕ) (b c : ℕ → ℂ)
    (hM : ramRrange H N X j ⊆ Finset.Icc 1 M) (ε : ℝ) (T : ℝ) (hT : 1 ≤ T)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) :
    ∑ r ∈ TsetSmallChi q H P Q j c ε ℰ,
        ‖ramMain H N X P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2
      ≤ ε ^ 2 * (2564 * ((q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T)
          * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
  have hsubT : TsetSmallChi q H P Q j c ε ℰ ⊆ ℰ := TsetSmallChi_subset q H P Q j c ε ℰ
  have h1 : ∑ r ∈ TsetSmallChi q H P Q j c ε ℰ,
        ‖ramMain H N X P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2
      ≤ ∑ r ∈ TsetSmallChi q H P Q j c ε ℰ,
          ε ^ 2 * ‖ramR H N X P Q j (chiBarCoeff q r.1 b) r.2‖ ^ 2 :=
    Finset.sum_le_sum (fun r hr =>
      norm_ramMain_sq_le_of_small H N X P Q j (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c)
        ε r.2 (mem_TsetSmallChi.mp hr).2)
  rw [← Finset.mul_sum] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg ε))
  have h9 := ramRChi_sq_sum_phi q H N X P Q j M b hM T hT
    (TsetSmallChi q H P Q j c ε ℰ) (fibreWellSpaced_of_subset hsubT hws)
    (fun r hr => hsub r (hsubT hr))
  refine h9.trans ?_
  have hcard : ((TsetSmallChi q H P Q j c ε ℰ).card : ℝ) ≤ (ℰ.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubT
  have hA : ((TsetSmallChi q H P Q j c ε ℰ).card : ℝ) * Real.sqrt T
      ≤ (ℰ.card : ℝ) * Real.sqrt T :=
    mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg T)
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N X P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (mul_nonneg hlog hmass)]

/-! ## §4 — the exit at the `φ(q)`-graded row -/

/-- **U-5, `χ`-LIFTED (exit), UNCONDITIONAL — the `𝒯_S` branch at the `φ(q)`-graded row.**
The `φ(q)`-graded twin of `usetChi_TS_branch_meanvalue`, with the hypothesis slot gone: once
the razor's budget clears the co-factor length (`bundle·X^{1−2η+ε} ≤ M`), the branch is priced
at `5128·φ(q)·ε_Q²·M·(1 + log 2T)·(mass)`.  The Halász term has vanished — that is what the
`𝒰`-thinness bought — and the razor's own character debit rode inside the exponent `ε`
(`charDebit_le_rpow`).  The remaining `φ(q)` is repaid by `usetChi_TS_branch_exit_repinned`. -/
theorem usetChi_TS_branch_meanvalue_phi (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb)
    (hJbJ : Jb ≤ J) (hδ0 : 0 < δ) (T V : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hV : 1 ≤ V) (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetChi q f Pseq Qseq δ J)
    (α η X ε : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * α) ≤ X ^ ε)
    (H : ℝ) (N Xd P Q j M : ℕ) (b c : ℕ → ℂ) (εQ : ℝ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η + ε)
      ≤ (M : ℝ)) :
    ∑ r ∈ TsetSmallChi q H P Q j c εQ ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2
      ≤ 5128 * (q.totient : ℝ) * εQ ^ 2 * (M : ℝ) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  have hbranch := TSChi_branch_meansq_phi q H N Xd P Q j M b c hM εQ T hT1 ℰ hws hsub
  have hkill := UsetChi_thin_sqrt_kill_absorbed q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V
    hT1 hqT hV hVinv hP3 hQT hκ30 hLL5 ℰ hws hsub hU α η X ε hVα hα hη2 hTX hX0 hdebit
  have hcnt : (ℰ.card : ℝ) * Real.sqrt T ≤ (M : ℝ) := le_trans hkill hbudget
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    have h := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast h
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  refine hbranch.trans ?_
  have hbr : (q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T
      ≤ 2 * ((q.totient : ℝ) * (M : ℝ)) := by nlinarith [hcnt, hφ1, hM0]
  have hstep : 2564 * ((q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T)
        * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ 5128 * (q.totient : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
    have hcoef : (0 : ℝ) ≤ 2564 * ((1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hbr hcoef]
  nlinarith [mul_le_mul_of_nonneg_left hstep (sq_nonneg εQ)]

/-! ## §5 — the `φ(q)` debit repaid: the level re-pinning -/

/-- `φ(q) ≤ q`, transported through the port's modulus gate `q ≤ (log X)^{12}`. -/
lemma totient_le_logpow (q : ℕ) (X : ℝ) (hq : (q : ℝ) ≤ (Real.log X) ^ 12) :
    (q.totient : ℝ) ≤ (Real.log X) ^ 12 := by
  have h : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  linarith

/-- **THE `φ(q)` DEBIT, PRICED AND REPAID.**  At the port's modulus gate
`q ≤ (log X)^{12}` and the RE-PINNED branch level `ε_Q = (log X)^{−106}`,

  `φ(q)·ε_Q² ≤ (log X)^{12}·(log X)^{−212} = (log X)^{−200}`

— the exact grade MR's `ε = (log X)^{−100}` delivers at `q = 1`.  Six extra powers of log on
the level is the whole price of the character lift's length term; it is charged to the `𝒯_L`
branch as `V = (log X)^{106}` in place of `(log X)^{100}`, where a quasi-power decay
(`USetThinTL`, `θ < 1/8`) beats any polylog `V`. -/
theorem phi_debit_level_repin (q : ℕ) (X : ℝ) (hL0 : 0 < Real.log X)
    (hq : (q : ℝ) ≤ (Real.log X) ^ 12) :
    (q.totient : ℝ) * ((Real.log X) ^ (-106 : ℝ)) ^ 2 ≤ (Real.log X) ^ (-200 : ℝ) := by
  have hsq : ((Real.log X) ^ (-106 : ℝ)) ^ 2 = (Real.log X) ^ (-212 : ℝ) := by
    rw [← Real.rpow_natCast ((Real.log X) ^ (-106 : ℝ)) 2, ← Real.rpow_mul hL0.le]
    norm_num
  have hnat : (Real.log X) ^ 12 = (Real.log X) ^ (12 : ℝ) := by
    rw [← Real.rpow_natCast (Real.log X) 12]
    norm_num
  have hadd : (Real.log X) ^ (12 : ℝ) * (Real.log X) ^ (-212 : ℝ)
      = (Real.log X) ^ (-200 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  calc (q.totient : ℝ) * ((Real.log X) ^ (-106 : ℝ)) ^ 2
      = (q.totient : ℝ) * (Real.log X) ^ (-212 : ℝ) := by rw [hsq]
    _ ≤ (Real.log X) ^ (12 : ℝ) * (Real.log X) ^ (-212 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
        rw [← hnat]; exact totient_le_logpow q X hq
    _ = (Real.log X) ^ (-200 : ℝ) := hadd

/-- **THE EXIT, RE-PINNED — the `χ`-lifted `𝒯_S` branch AT THE `q = 1` GRADE, UNCONDITIONAL.**

At the port's modulus gate `q ≤ (log X)^{12}` and the branch level `ε_Q = (log X)^{−106}`,

  `∑_{𝒯_S} ‖Q_{j,H}·R_{j,H}(χ̄, 1+it)‖² ≤ 5128·(log X)^{−200}·M·(1 + log 2T)·(co-factor mass)`

— **byte-for-byte the `q = 1` exit `uset_TS_branch_meanvalue` (`USetThinTS`:393) at MR's own
level `ε = (log X)^{−100}`.**  This is the discharge of the `HalaszIntegersChi` slot's job:
the whole character cost of MR Lemma 9 under the `χ`-lift is six powers of log on the branch
level, paid on the `𝒯_L` side where a quasi-power beats it.  Unconditional: no hypothesis
slot, no `sorry`; the analytic input is the LANDED `q = 1` Lemma 9. -/
theorem usetChi_TS_branch_exit_repinned (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb)
    (hJbJ : Jb ≤ J) (hδ0 : 0 < δ) (T V : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hV : 1 ≤ V) (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetChi q f Pseq Qseq δ J)
    (α η X ε : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * α) ≤ X ^ ε)
    (hL0 : 0 < Real.log X) (hqlog : (q : ℝ) ≤ (Real.log X) ^ 12)
    (H : ℝ) (N Xd P Q j M : ℕ) (b c : ℕ → ℂ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η + ε)
      ≤ (M : ℝ)) :
    ∑ r ∈ TsetSmallChi q H P Q j c ((Real.log X) ^ (-106 : ℝ)) ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 c) j r.2‖ ^ 2
      ≤ 5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  have hraw := usetChi_TS_branch_meanvalue_phi q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V
    hT1 hqT hV hVinv hP3 hQT hκ30 hLL5 ℰ hws hsub hU α η X ε hVα hα hη2 hTX hX0 hdebit
    H N Xd P Q j M b c ((Real.log X) ^ (-106 : ℝ)) hM hbudget
  refine hraw.trans ?_
  have hrepin := phi_debit_level_repin q X hL0 hqlog
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hcoef : (0 : ℝ) ≤ 5128 * ((M : ℝ) * ((1 + Real.log (2 * T))
      * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2))) := by
    have h1 : (0 : ℝ) ≤ (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) :=
      mul_nonneg hlog hmass
    have h2 : (0 : ℝ) ≤ (M : ℝ) * ((1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)) :=
      mul_nonneg hM0 h1
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hrepin hcoef]

/-! ## §6 — the grade comparison: why the landed mean-value row cannot do this

The two lemmas below are the machine-checked form of the header's arithmetic: the landed
mean-value row (`ramRChi_sq_sum_mvt`) carries the ORDINATE HEIGHT `T` where the demand carries
the co-factor LENGTH `M`, and at the §8.3 pins `T/M ≍ e^{j/H}`; while the `φ(q)`-graded
Halász row of §2, under the razor's budget, carries `M`. -/

/-- **The mean-value row carries `T`.**  For `1 ≤ M ≤ T`, the landed row
`84·(φ(q)(T+1) + φ(q)M/q)·log(2M)` is at least `(T/M)` times the same row read at length `M`.
At the §8.3 pins (`T ≍ X`, `M ≍ X e^{−j/H}`) that ratio is `≍ e^{j/H} ≍ p` — the loss the
`USetChiTS` header reports, and the reason the `𝒯_S` branch cannot run at the mean-value
grade.  (`_hMT : M ≤ T` is the regime marker — the inequality itself holds for every `T`;
the CONTENT is that the row's `T` is where the demand has `M`.) -/
lemma mvt_row_carries_T (q : ℕ) (M T : ℝ) (hM : 1 ≤ M) (_hMT : M ≤ T) :
    (T / M) * (84 * (q.totient : ℝ) * M * Real.log (2 * M))
      ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * M / (q : ℝ))
          * Real.log (2 * M) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hlog : (0 : ℝ) ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
  have hkey : (T / M) * (84 * (q.totient : ℝ) * M) = 84 * ((q.totient : ℝ) * T) := by
    field_simp
  have hextra : (0 : ℝ) ≤ (q.totient : ℝ) * M / (q : ℝ) := by positivity
  calc (T / M) * (84 * (q.totient : ℝ) * M * Real.log (2 * M))
      = ((T / M) * (84 * (q.totient : ℝ) * M)) * Real.log (2 * M) := by ring
    _ = (84 * ((q.totient : ℝ) * T)) * Real.log (2 * M) := by rw [hkey]
    _ ≤ 84 * ((q.totient : ℝ) * (T + 1) + (q.totient : ℝ) * M / (q : ℝ))
          * Real.log (2 * M) := by
        refine mul_le_mul_of_nonneg_right ?_ hlog
        nlinarith [hφ0, hextra]

/-- **The `φ(q)`-graded Halász row carries `M`.**  Under the razor's budget `|ℰ|√T ≤ M` the
row of §2 collapses to `5128·φ(q)·M·(1 + log 2T)` — the `T`-dependence survives only inside
the Gallagher factor `1 + log 2T`.  This is the inequality
`usetChi_TS_branch_meanvalue_phi` runs on, isolated. -/
lemma phi_row_carries_M (q : ℕ) (hq : 1 ≤ q.totient) (M s L : ℝ) (hM : 0 ≤ M) (hs : s ≤ M)
    (hL : 0 ≤ L) :
    2564 * ((q.totient : ℝ) * M + s) * L ≤ 5128 * (q.totient : ℝ) * M * L := by
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast hq
  have hbr : (q.totient : ℝ) * M + s ≤ 2 * ((q.totient : ℝ) * M) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hbr hL]

end Salt.MR
