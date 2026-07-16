/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Siegel
import Salt.Basic

/-!
# The Heath-Brown statement — Siegel zeros ⇒ twin primes (S3-HB-R1)

Design: `docs/exploration/s3-hb1-design.md` (FROZEN, gate GO-WITH-AMENDMENTS
A1–A5). Primary source: Tao 2015, "Heath-Brown's theorem on prime twins and
Siegel zeroes", Theorem 1; Heath-Brown 1983 (PLMS) for provenance.

This module lands the *statement layer* only — the four Props and the proven
propositional glue between them (the `Brun.BrunStatement` pattern). The analytic
core (the μ↔χ correlation) is HB-R2, which consumes `InfinitelyManySiegelZeros`
as its hypothesis.

## What this is (and is not)

Everything here is **conditional on `InfinitelyManySiegelZeros`, which is believed
FALSE**: Siegel's theorem bounds any exceptional zero *ineffectively* (the landed
`siegel_theorem`, `Salt/SW/SiegelClose.lean`, gives only `β ≤ 1 − C(ε)/q^ε`), and
no Siegel zero has ever been found. So Heath-Brown is a *conditional* twin-prime
theorem, not an unconditional one.

## No contradiction with the parity wall (the non-contradiction triple)

The corpus's unconditional `no_parity_beating_certificate_unconditional`
(`Salt/TwinBar/WallUnconditional.lean`) is a *parity-wall* obstruction: it kills
every `SieveAgree`-**tolerant** lower certificate. Heath-Brown does NOT beat it,
because a Siegel-zero input is **character-sighted**, not tolerant — it sees the
quadratic character `χ` the wall's certificates are blind to. Three honesty checks:

* **Blindness vs sight.** The wall bounds certificates that agree up to level `D`
  (tolerant); the Siegel-zero hypothesis is a statement about `L(·,χ)` for a
  specific quadratic `χ`. Different objects, no collision.
* **`MmuRate` stays TRUE.** The effective Möbius rate `MmuRate`
  (`Salt/SW/MobiusRateClose.lean`) is ζ-governed — the `1/ζ` Perron spine on the
  *principal* line. A Siegel zero lives on `L(·,χ)` for a **non-principal** `χ`,
  so it never touches the ζ spine; `MmuRate` remains true under the hypothesis.
* **The carved-out zero.** The corpus's zero-free region `zero_free_region_all`
  (`Salt/SW/ZeroFreeReal.lean`) is proven with the side condition
  `χ² ≠ 1 ∨ Im ρ ≠ 0` — it *deliberately carves out exactly* the real zero of a
  real character (`χ² = 1 ∧ Im ρ = 0`). That carve-out is precisely where a Siegel
  zero would sit; the region does not exclude it.

## Quantifier discipline (A5)

`InfinitelyManySiegelZeros` is stated in the **∀c∃** order (the witness AFTER `c`),
matching the exact negation of `NoSiegelZeros`. The **∃∀** mis-freeze (`BadHyp`:
one `β` beating *every* `c`) is provably FALSE — `badHyp_false` in this file
exhibits the trap as a theorem (as `β < 1` while `c → 0` forces `β ≥ 1`). We use
the STRICT `1 − c/log q < β` (not Tao's closed `1 − c/log q ≤ β`): the two forms
differ only at the single endpoint, which is absorbed by the existential `c`, and
strict gives the *exact* negation of the `≤` in `NoSiegelZeros`.

## Where the hypothesis sits

Between Landau–Page and Siegel. `siegel_theorem` gives the ineffective
`β ≤ 1 − C(ε)/q^ε`, which for large `q` is WEAKER than the `log q` gap asserted
here — so the corpus genuinely does not decide `InfinitelyManySiegelZeros`; it is a
real, open hypothesis (cf. Landau–Page for the effective one-exception bound,
Siegel for the ineffective `q^ε` bound).
-/

open Complex DirichletCharacter

namespace Salt.TwinBar

/-- **NO Siegel zeros.** Some `c > 0` pushes every real primitive quadratic
character's real zeros below `1 − c/log q`. (Tao Thm 1 (ii); the effective
zero-free gap for exceptional characters.) -/
def NoSiegelZeros : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    1 < q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ β : ℝ, LFunction χ β = 0 → β < 1 →
      β ≤ 1 - c / Real.log q

/-- **Infinitely many Siegel zeros** — the `¬ NoSiegelZeros` unfolding, stated
POSITIVELY in the `∀c∃` order (the witness comes AFTER `c`). The `∃∀` order is
provably FALSE — see `badHyp_false`. This is HB-R2's hypothesis. -/
def InfinitelyManySiegelZeros : Prop :=
  ∀ c : ℝ, 0 < c → ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β : ℝ),
    1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    LFunction χ β = 0 ∧ 1 - c / Real.log q < β ∧ β < 1

/-- **The Heath-Brown 1983 statement** (qualitative form): a Siegel zero forces
the Twin Prime Conjecture. -/
def HeathBrownStatement : Prop :=
  InfinitelyManySiegelZeros → TwinPrimeConjecture

/-- **The dichotomy corollary shape**: either the Twin Prime Conjecture holds, or
there is an effective no-Siegel-zeros gap. -/
def HeathBrownDichotomy : Prop :=
  TwinPrimeConjecture ∨ NoSiegelZeros

/-- **The `∃∀` MIS-freeze** — one `β` beating *every* `c` at a fixed `q, χ`.
Exhibited here ONLY to be refuted in `badHyp_false`; this is NOT the live
hypothesis (that is `InfinitelyManySiegelZeros`, the `∀c∃` form). -/
def BadHyp : Prop :=
  ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β : ℝ),
    (1 < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧ LFunction χ β = 0 ∧ β < 1) ∧
    ∀ c : ℝ, 0 < c → 1 - c / Real.log q < β

/-- The live hypothesis is the exact negation of the effective gap: infinitely
many Siegel zeros ↔ there is NO no-Siegel-zeros constant. The `∀c∃` order and the
`<`/`≤` boundary pairing are pinned by this equivalence holding. -/
theorem infinitely_iff_not_noSiegel :
    InfinitelyManySiegelZeros ↔ ¬ NoSiegelZeros := by
  constructor
  · rintro h ⟨c, hc, hP⟩
    obtain ⟨q, hqz, χ, β, h1q, hprim, hsq, hne, hL, hlt, hβ1⟩ := h c hc
    haveI := hqz
    exact (not_le.mpr hlt) (hP q χ h1q hprim hsq hne β hL hβ1)
  · intro h c hc
    by_contra hcon
    apply h
    refine ⟨c, hc, ?_⟩
    intro q hq0 χ h1q hprim hsq hne β hL hβ1
    by_contra hle
    rw [not_le] at hle
    exact hcon ⟨q, hq0, χ, β, h1q, hprim, hsq, hne, hL, hle, hβ1⟩

/-- The dual reading: an effective no-Siegel-zeros gap exists iff there are NOT
infinitely many Siegel zeros. -/
theorem noSiegelZeros_iff_not_infinitely :
    NoSiegelZeros ↔ ¬ InfinitelyManySiegelZeros := by
  rw [infinitely_iff_not_noSiegel, not_not]

/-- **The dichotomy is the statement.** `HeathBrownStatement`
(Siegel zeros ⇒ twin primes) is propositionally equivalent to the dichotomy
`TwinPrimeConjecture ∨ NoSiegelZeros` — the classical `(¬N → T) ↔ (T ∨ N)`. -/
theorem heathBrown_iff_dichotomy :
    HeathBrownStatement ↔ HeathBrownDichotomy := by
  unfold HeathBrownStatement HeathBrownDichotomy
  rw [infinitely_iff_not_noSiegel]
  constructor
  · intro h
    by_cases hN : NoSiegelZeros
    · exact Or.inr hN
    · exact Or.inl (h hN)
  · rintro (hT | hN) hnN
    · exact hT
    · exact absurd hN hnN

/-- **The `∃∀` mis-freeze is FALSE** (the trap, exhibited as a theorem). A single
`β < 1` cannot beat `1 − c/log q` for *every* `c > 0`: instantiating at
`c := (1 − β)·log q / 2 > 0` forces `1 < β`, contradicting `β < 1`. This is why
the live hypothesis must be the `∀c∃` order, not `∃∀`. -/
theorem badHyp_false : ¬ BadHyp := by
  rintro ⟨q, -, -, β, ⟨h1q, -, -, -, -, hβ1⟩, hall⟩
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h1q
  have hlogpos : 0 < Real.log q := Real.log_pos hq1
  have hlogne : Real.log q ≠ 0 := ne_of_gt hlogpos
  have h1mβ : 0 < 1 - β := by linarith
  set c : ℝ := (1 - β) * Real.log q / 2 with hc
  have hcpos : 0 < c := div_pos (mul_pos h1mβ hlogpos) (by norm_num)
  have hlt : 1 - c / Real.log q < β := hall c hcpos
  have hdiv : c / Real.log q = (1 - β) / 2 := by
    rw [hc]; field_simp
  rw [hdiv] at hlt
  linarith

end Salt.TwinBar
