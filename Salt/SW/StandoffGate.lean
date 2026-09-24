/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Gate
import Salt.Fulcrum.Dichotomy

/-!
# Siegel–Walfisz from a fixed standoff — the DESIGN-TIER STATEMENT FREEZE

⛔ **Nothing in this file bears on twin primes.** Siegel–Walfisz (`siegelWalfisz_holds`,
`Gate.lean:150`) is already an unconditional theorem of this corpus. What this file changes,
once its wave lands, is the PROOF TERM's dependence on one ineffective input, and nothing else.

## Status: FROZEN STATEMENTS, NO PROOFS (track branch only; never `main` with a `sorry`)

Provenance: GOLDMINE lane (a) pull 1 (`docs/QUEUE.md` item 15, O13; the sweep brief
`2026-09-24-math-GOLDMINE-sweep1.md` §3), the helm's routing of 2026-09-24 03:07 and its
gate-write of 07:26, and kill-check 1 answered kernel-side by the non-author reader
(`2026-09-24-h2c-KC1-goldmine/`): the closures of `psi1_char_bound`, `psi1_trivchar_bound`
and `psi1_transfer` reach NONE of `siegel_theorem` / `siegel_L_one_exceptional` /
`L1_lower_siegel`. The only exceptional-zero module in any of their closures is
`Salt.SW.LandauPage` — Landau's per-modulus one-exceptional-zero theorem, EFFECTIVE,
`c₁ = 1/5000`.

## The demand, measured

`psi1AP_main_bound` (`Fold.lean:157`) reads Siegel's theorem at ONE site, `Fold.lean:167`:
`siegel_theorem ε` at `ε = 1/(4C)`, used only in the exceptional branch to get
`Cₛ/f^ε ≤ 1 − β₁`, hence `f^ε ≤ (log x)^{1/4}` and the kill of the residue term. Its one
code consumer is `siegelWalfisz_holds` at `Gate.lean:154`, which is parametric in the main
bound at that line. A FIXED standoff `1 − β₁ ≥ c/log f` serves every `(A, C)` at once: with
`f ≤ (log x)^C`, `x^{−(1−β₁)} ≤ exp(−c·log x/(C·log log x))`, which beats every power of
`log x`. The ∀ε family collapses to one strength.

## The label (h2c's closure facts, the helm's wording, 2026-09-24 07:26)

**"Siegel–Walfisz's only INEFFECTIVE dependence on Siegel-zero theory is one standoff
constant"** — and Landau's per-modulus theorem (`LandauPage.lean`, effective) sits beside it
in the closure. NEVER "effective Siegel–Walfisz": under `¬F` the standoff `c` is
`min(c_iso(Q₀), 1/C)` and `c_iso` is nonconstructive (`ContinuousAt.eventually_ne`, the
fulcrum Pass-2 caveat, owed at `Fulcrum/Basic.lean:169`). The theorems below remove Siegel's
`C(ε)`; they do not make `c` computable.

## What makes the claim checkable — a Prop cannot see it

`Salt.BV.SiegelWalfisz` is the same Prop either way and `#print axioms` is the same three
either way. The claim is a property of the PROOF TERM: the transitive constant closure of
`siegelWalfisz_of_standoff` must exclude `siegel_theorem`, `siegel_L_one_exceptional` and
`L1_lower_siegel`, with `siegelWalfisz_holds` REACHING `siegel_theorem` (proof-only) as the
positive control. That certificate is the committed module `Salt.SW.StandoffCert` — a check
that can FAIL, never a `#print axioms` line alone. ⚠️ At this freeze every proof below is
`sorry`, so the certificate's NOT-REACHED verdicts on these names are the VACUOUS half; it is
armed for the wave, and the wave is not landed until the certificate is green on real proofs.

## Kill-checks: status and owners (the non-author read's C6, 2026-09-24)

* KC1 (a second Siegel path): ANSWERED — NOT REACHED, kernel-side (h2c, above).
* KC2 (is the standoff strong enough at SMALL conductors, `f = 3` included; no `f`-dependence
  left in the eventual-in-`x` absorption): **OPEN — owner: the refuter pass.**
* KC3 (is it new; no survey run; any prose follows the claim law, "first in any PUBLIC
  artifact as of <survey date>", and credits the textbook statement): **OPEN — owner: the
  refuter pass.**
* KC4 (the honest scope of "effective"): the label above.

## Token checks (order clause 7): the wave changes no landed statement

* `NoSiegelZerosAt` is the body of `Salt.TwinBar.NoSiegelZeros` at one `c`, byte-for-byte
  after `∃ c : ℝ, 0 < c ∧` — witnessed by `noSiegelZeros_iff_exists_at := Iff.rfl`, which is
  a CHECK (it fails to elaborate if the body drifts), not a proof of the candidate.
* The conclusion of `psi1AP_main_bound_of_standoff` is the TYPE of `psi1AP_main_bound`, and
  the conclusion of `siegelWalfisz_of_standoff` is the TYPE of `siegelWalfisz_holds`, each
  compared as `Expr`s by `StandoffCert`'s `#assert_conclusion_is` (syntactic, not defeq).
-/

open Complex DirichletCharacter

namespace Salt.SW

/-- **The standoff at ONE fixed `c`** — the body of `Salt.TwinBar.NoSiegelZeros` with its
leading `∃ c, 0 < c ∧` removed. Every real primitive quadratic character `χ ≠ 1` mod `q > 1`
has its real zeros below `1 − c/log q`. The `c` is the one strength Siegel–Walfisz reads. -/
def NoSiegelZerosAt (c : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    1 < q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ β : ℝ, LFunction χ β = 0 → β < 1 →
      β ≤ 1 - c / Real.log q

/-- **Token check, not a proof:** `NoSiegelZerosAt` is exactly the body of `NoSiegelZeros`.
If this line stops elaborating as `Iff.rfl`, the frozen statement has drifted. -/
theorem noSiegelZeros_iff_exists_at :
    Salt.TwinBar.NoSiegelZeros ↔ ∃ c : ℝ, 0 < c ∧ NoSiegelZerosAt c := Iff.rfl

/-- **S6c from a fixed standoff.** `psi1AP_main_bound` (`Fold.lean:157`) with the Siegel
kill at `Fold.lean:167` replaced by the standoff `hS`: the exceptional branch reads
`1 − β₁ ≥ c/log f` at the conductor `f = χ.conductor` (with `1 < f` from primitivity and
`χ ≠ 1`), and `f ≤ (log x)^C` turns `x^{−(1−β₁)}` into a saving beyond every power of
`log x`, absorbed into `x₀` by one more `tendsto`. **Conclusion: `Fold.lean:157`, verbatim**
(certified by `StandoffCert`). FROZEN; class B. -/
theorem psi1AP_main_bound_of_standoff {c : ℝ} (hc : 0 < c) (hS : NoSiegelZerosAt c) :
    ∀ A C : ℝ, 0 < A → 0 < C → ∃ K x₀ : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] {a : ℕ}, a < q → Nat.Coprime q a → ∀ {x : ℝ}, x₀ ≤ x →
      (q : ℝ) ≤ (Real.log x) ^ C →
      |(q.totient : ℝ) * psi1AP x q a - x ^ 2 / 2| ≤ K * x ^ 2 / (Real.log x) ^ A := by
  sorry

/-- **THE GATE FROM A STANDOFF.** `siegelWalfisz_holds` (`Gate.lean:150`) with
`psi1AP_main_bound` at `Gate.lean:154` replaced by `psi1AP_main_bound_of_standoff hc hS`;
the de-smoothing through `psi1AP_sandwich` is untouched. **Conclusion:
`Salt.BV.SiegelWalfisz`, verbatim** (certified by `StandoffCert`). Its proof term must not
reach `siegel_theorem`, `siegel_L_one_exceptional` or `L1_lower_siegel` — that is the whole
result, and `StandoffCert` is what says so. FROZEN; class B, mechanical. -/
theorem siegelWalfisz_of_standoff {c : ℝ} (hc : 0 < c) (hS : NoSiegelZerosAt c) :
    Salt.BV.SiegelWalfisz := by
  sorry

/-- **The `¬F` horn, cashed.** The fulcrum dichotomy's right arm
(`not_fulcrum_implies_noSiegelZeros`, `Fulcrum/Dichotomy.lean:82`) delivers `NoSiegelZeros`;
unfolding it through `noSiegelZeros_iff_exists_at` hands `siegelWalfisz_of_standoff` its
`c`. So under `¬ FulcrumQualityMin C`, Siegel–Walfisz is proved with no Siegel input — at a
standoff `c` that is nonconstructive (see the label above). FROZEN; class A once the two
above land. -/
theorem not_fulcrum_siegelFree_SW {C : ℝ} (hC : 0 < C)
    (hnF : ¬ Salt.Fulcrum.FulcrumQualityMin C) :
    ∃ c : ℝ, 0 < c ∧ NoSiegelZerosAt c ∧ Salt.BV.SiegelWalfisz := by
  sorry

end Salt.SW
