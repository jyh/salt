/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.LS.PsiDefs

/-!
# The BV rung (`bv`) — V0 named gate: `SiegelWalfisz` + trivia

Design: `docs/blueprints/bv.md`, node V0.1. The Siegel–Walfisz hypothesis is
the single named analytic gate of the rung (absent from every Lean artifact
as of 2026-07): `ψ(x; q, a) = x/φ(q) + O_A(x/(log x)^A)` uniformly for
`q ≤ (log x)^C`. Statement FROZEN by Fable; landed here verbatim (module
cast/packaging) plus consumer-facing trivia:

* `siegelWalfisz_mono` — the bound at exponent `A` is usable at any smaller
  saving `A' ≤ A` (same `K`, for `log x ≥ 1`);
* `psiAP_one`/`siegelWalfisz_psiTot` — the `q = 1` instance: `psiAP x 1 a`
  is exactly `psiTot x`, so `SiegelWalfisz` gives an unconditional
  PNT-error-shaped bound on `psiTot`;
* `coprime_mod_left` — the residue-normalization fact (`a` vs. `a % q`
  coprimality to `q`) consumers need when reducing to least residues.
-/

open Salt.LS

namespace Salt.BV

/-- Siegel–Walfisz: ψ(x; q, a) = x/φ(q) + O_A(x/(log x)^A) uniformly for
q ≤ (log x)^C. The single assumed analytic input of this rung (absent from
every Lean artifact as of 2026-07; supplied by future formalization or
upstream). ψ-form, in this repo's carriers. -/
def SiegelWalfisz : Prop :=
  ∀ A C : ℝ, 0 < A → 0 < C → ∃ K : ℝ, 0 ≤ K ∧ ∀ x q a : ℕ, 2 ≤ x →
    0 < q → ((q : ℝ) ≤ (Real.log x) ^ C) → Nat.Coprime a q →
    |psiAP x q a - (x : ℝ) / q.totient| ≤ K * x / (Real.log x) ^ A

/-! ## Monotonicity in the saving exponent `A` -/

/-- **Monotonicity trivia.** `SiegelWalfisz` gives, at exponent `A`, a bound
`K·x/(log x)^A`; since `log x ≥ 1` makes `(log x)^A` monotone in the exponent,
the SAME `K` also bounds the discrepancy at any smaller saving `A' ≤ A`
(a weaker exponent gives a weaker/looser bound for free) — the "usability at
any exponent ≤ A" extraction consumers want without re-invoking `hSW`. -/
lemma siegelWalfisz_mono (hSW : SiegelWalfisz) {A C A' : ℝ} (hA : 0 < A)
    (hC : 0 < C) (_hA' : 0 < A') (hle : A' ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x q a : ℕ, 2 ≤ x → 1 ≤ Real.log x → 0 < q →
      ((q : ℝ) ≤ (Real.log x) ^ C) → Nat.Coprime a q →
      |psiAP x q a - (x : ℝ) / q.totient| ≤ K * x / (Real.log x) ^ A' := by
  obtain ⟨K, hK0, hK⟩ := hSW A C hA hC
  refine ⟨K, hK0, fun x q a hx hlogx hq hqc hcop => ?_⟩
  have hbound := hK x q a hx hq hqc hcop
  have hlogxpos : 0 < Real.log x := by linarith
  have hmono : (Real.log x) ^ A' ≤ (Real.log x) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hlogx hle
  have hnum : 0 ≤ K * (x : ℝ) := mul_nonneg hK0 (by positivity)
  exact hbound.trans (div_le_div_of_nonneg_left hnum (Real.rpow_pos_of_pos hlogxpos A') hmono)

/-! ## The `q = 1` instance -/

/-- The trivial modulus: `psiAP x 1 a = psiTot x` for any `a` (every `n` is
congruent to `a` mod `1`, so the residue filter is vacuous). -/
lemma psiAP_one (x a : ℕ) : psiAP x 1 a = psiTot x := by
  unfold psiAP psiTot
  congr 1
  apply Finset.filter_true_of_mem
  intro n _
  simp [Nat.mod_one]

/-- **`q = 1` instance of `SiegelWalfisz`**: an unconditional
(PNT-error-shaped) bound on `psiTot` for `x ≥ 3` (`log x ≥ 1` is exactly
what makes `q = 1 ≤ (log x)^C` hold; the `x = 2` edge is dropped rather than
absorbed into `K`, executor latitude per dispatch). -/
lemma siegelWalfisz_psiTot (hSW : SiegelWalfisz) {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℕ, 3 ≤ x →
      |psiTot x - (x : ℝ)| ≤ K * x / (Real.log x) ^ A := by
  obtain ⟨K, hK0, hK⟩ := hSW A 1 hA one_pos
  refine ⟨K, hK0, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := by omega
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog1 : 1 ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      _ ≤ (x : ℝ) := hxR
  have hqcond : ((1 : ℕ) : ℝ) ≤ (Real.log x) ^ (1 : ℝ) := by
    simp only [Nat.cast_one, Real.rpow_one]
    exact hlog1
  have hbound := hK x 1 0 hx2 one_pos hqcond (Nat.coprime_one_right 0)
  simpa [psiAP_one, Nat.totient_one] using hbound

/-! ## Residue normalization -/

/-- **Residue normalization.** `a` is coprime to `q` iff `a % q` is — lets
consumers freely replace `a` by its least residue `a % q` (matching the
`Salt.Maynard` congruence-class convention `n % q = a % q`). -/
lemma coprime_mod_left (a q : ℕ) : Nat.Coprime a q ↔ Nat.Coprime (a % q) q :=
  (ZMod.coprime_mod_iff_coprime a q).symm

end Salt.BV
