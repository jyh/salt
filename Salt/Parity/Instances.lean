/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Parity.Z
import Salt.HB.All
import Salt.TwinBar.All
import Salt.Chen.All
import Salt.BrunLower.All
import Salt.Brun.All
import Salt.Goldbach.All

/-!
# Parity — L0 instances: the landed corpus sits inside the parity-invariant cone

This module is the kernel-visible census promised by the `L0` insensitivity
closure schema `Salt.Parity.parityInv_of_closed` (`Salt/Parity/Z.lean`).  Each
headline theorem of the landed corpus is a *closed* proposition — one that never
reads a completion `a : ℕ → ℝ` — hence, by `parityInv_of_closed`, it is a
`ParityInv θ A₀` membership at every grade `(θ, A₀)`.  This is the formal
content of "𝒟(¬F) ⊆ ParityInv" under semantic invariance: the entire corpus
sits inside the parity-invariant cone.

Honest label (ratified R4): these certificates are *type-level* — a closed
proposition cannot read a completion, so cone membership carries no arithmetic
information.  The arithmetic insensitivity content lives in the witness
completions (`twinFree`, `L2`), not here.

This file imports the corpus (`Salt.HB`/`Salt.TwinBar`/`Salt.Chen`/…); the
demand-spec module `Salt/Parity/Z.lean` deliberately does NOT, keeping `Z`
oracle-clean by import list alone (ratified module invariant J4).
-/

/-- HB Lemma 2 lower half `S⁽¹⁾ ≤ S⁽²⁾` (`Salt.HB.S1_le_S2`) sits in the
    parity-invariant cone. -/
theorem parityInv_S1_le_S2 (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
        ∀ A : Finset ℕ, Salt.HB.S1 A ≤ Salt.HB.S2 χ A) :=
  Salt.Parity.parityInv_of_closed θ A₀ (@Salt.HB.S1_le_S2)

/-- The Polymath8b `k = 2` twin bar `J₁ + J₂ ≤ 2·log 2·I₂` (`Salt.TwinBar.twin_bar`)
    sits in the parity-invariant cone. -/
theorem parityInv_twin_bar (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => ∀ (F : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry F) Salt.TwinBar.R₂ →
        Salt.TwinBar.J₁ F + Salt.TwinBar.J₂ F ≤ 2 * Real.log 2 * Salt.TwinBar.I₂ F) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.TwinBar.twin_bar

/-- The θ-parameterised gate failure `θ·(J₁+J₂) ≤ 2·I₂` (`Salt.TwinBar.twin_gate_fails`)
    sits in the parity-invariant cone. -/
theorem parityInv_twin_gate_fails (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => ∀ (F : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry F) Salt.TwinBar.R₂ →
        ∀ (t : ℝ), 0 < t → t ≤ 1 →
          t * (Salt.TwinBar.J₁ F + Salt.TwinBar.J₂ F) ≤ 2 * Salt.TwinBar.I₂ F) :=
  Salt.Parity.parityInv_of_closed θ A₀ (@Salt.TwinBar.twin_gate_fails)

/-- The headline impossibility `no_twin_weight` (no continuous weight crosses the
    twin gate) sits in the parity-invariant cone. -/
theorem parityInv_no_twin_weight (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => ¬ ∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) Salt.TwinBar.R₂ ∧
        0 < Salt.TwinBar.I₂ F ∧
          2 * Salt.TwinBar.I₂ F < Salt.TwinBar.J₁ F + Salt.TwinBar.J₂ F) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.TwinBar.no_twin_weight

/-- The Siegel-zero dichotomy `NoSiegelZeros ↔ ¬InfinitelyManySiegelZeros`
    (`Salt.TwinBar.noSiegelZeros_iff_not_infinitely`, the 𝒟(¬F)-cone anchor) sits
    in the parity-invariant cone. -/
theorem parityInv_noSiegel_iff (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => Salt.TwinBar.NoSiegelZeros ↔ ¬ Salt.TwinBar.InfinitelyManySiegelZeros) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.TwinBar.noSiegelZeros_iff_not_infinitely

/-- Chen's theorem `chen_headline` (∞-many primes `p` with `p+2` a `P₂`) sits in
    the parity-invariant cone. -/
theorem parityInv_chen_headline (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => {p : ℕ | p.Prime ∧ Salt.Chen.IsP2 2 (p + 2)}.Infinite) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.Chen.chen_headline

/-- The twin almost-prime headline `Ω(n(n+2)) ≤ 20` infinitely often
    (`Salt.BrunLower.twin_almost_prime`) sits in the parity-invariant cone. -/
theorem parityInv_twin_almost_prime (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀
      (fun _ => {n : ℕ | ArithmeticFunction.cardFactors (n * (n + 2)) ≤ 20}.Infinite) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.BrunLower.twin_almost_prime

/-- Brun's theorem `BrunStatement` (twin reciprocal sum converges, via
    `Salt.N6.N6_2`) sits in the parity-invariant cone. -/
theorem parityInv_N6_2 (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀ (fun _ => BrunStatement) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.N6.N6_2

/-- The Selberg twin counting bound `TwinCountingBigO` (via `Salt.M5BigO.N5_3`)
    sits in the parity-invariant cone. -/
theorem parityInv_N5_3 (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀ (fun _ => TwinCountingBigO) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.M5BigO.N5_3

/-- Chen's second theorem `chen_goldbach` (every sufficiently large even `N`
    is `p + q` with `p` prime and `q` a `P₂`) sits in the parity-invariant
    cone. -/
theorem parityInv_chen_second (θ A₀ : ℝ) :
    Salt.Parity.ParityInv θ A₀ (fun _ => ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ Salt.Chen.IsP2 2 q) :=
  Salt.Parity.parityInv_of_closed θ A₀ Salt.Goldbach.chen_goldbach
