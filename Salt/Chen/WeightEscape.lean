/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TwinDeficit

/-!
# S2-B1 — the weight escape (WeightEscape)

**This is EXPLORATION, not a frozen blueprint node.**  Design context:
`docs/exploration/s2-b1-design.md` (File 2, frozen 2026-07-17; the gate verdict
GO-WITH-AMENDMENTS, amendment A2 binds the N4 route).  This file adds NEW work only; it edits no
landed file.  Everything here is sorry-free and axiom-clean (audited in-build via `Salt.Chen.All`).

## What this file says (the escape, stated honestly)

The three landed decorations — `omegaLe y` (distinct prime factors `≤ y`), `sqStrip y` (the
prime-power strip `≤ y`), `tripleT y` (Chen's triple pattern with its small factor `≤ y`) — all
read only prime-factor structure **at or below `y`**.  A window prime `p > y` and a heavy
semiprime `p·q` with `y < p, q` are therefore decoration-identical: BOTH read `(0, 0, 0)`.

* **N3 (`readableWeight_blind`).**  The FULL decoration algebra is blind: for ANY
  `f : ℝ → ℝ → ℝ → ℝ`, the readable weight `f (ω_{≤y}) (1_T) (S)` takes the SAME value `f 0 0 0`
  at a window prime and at every heavy semiprime.  No retuning of the readable weight — no
  reweighting of the three decorations by any function whatsoever — can separate the two point
  types.  This is why the P₁-form of the razor must pay the entire E2 mass (`e2PrimeSum`): the
  landed weight's decorations cannot see the P₂-but-not-P₁ mass poured into heavy semiprimes.

* **N4 (`bigOmegaGt_prime` / `bigOmegaGt_heavy`).**  The MINIMAL decoration that DOES separate is
  `bigOmegaGt y` — the count of prime factors ABOVE `y`, WITH multiplicity.  It reads `1` at a
  window prime and `2` at EVERY heavy E2 point, INCLUDING the square point `p²` (whose
  multiplicity-2 factor defeats the distinct-count variant — the freeze-time catch, see the N4
  docstring).  But `bigOmegaGt` is not a route to twins: the carrier row it would need is a LOWER
  bound on the heavy-semiprime mass, which is exactly **GAP-E** (the B2 census's named missing
  theorem, `TwinDeficit`'s `hE2lo`-shaped hypothesis).  GAP-E is parity-sensitive — the
  fundamental barrier.  The escape is the NAME of where twin progress must come from, not a route.

## R4 (the too-good-to-be-true tripwire) — armed, and structurally CLEAR

Every Lean conclusion below is an EQUALITY of readings (`= f 0 0 0`, `= 1`, `= 2`).  No conclusion
lower-bounds the twin mass; no twin-prime-adjacent existence claim appears anywhere.  The escape
`bigOmegaGt` is stated as two separation equalities and nothing more — its carrier (GAP-E) is
declared open, not discharged.
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — N3: the full decoration algebra is blind, pointwise

The heavy side reuses the landed vanishing triple (`omegaLe_eq_zero_of_heavy` /
`sqStrip_eq_zero_of_heavy` / `not_tripleP_of_heavy`, TwinDeficit.lean).  The prime side needs the
same three facts for a bare prime `p > y`, proved here (a prime's only prime factor is `p`, which
the `≤ y` cut removes; a prime is not a 3-almost-prime). -/

/-- `ω_{≤y}` vanishes at a prime `> y`: its only prime factor is `p`, filtered out by `· ≤ y`. -/
theorem omegaLe_eq_zero_of_prime_gt {y p : ℕ} (hp : p.Prime) (hyp : y < p) :
    omegaLe y p = 0 := by
  rw [omegaLe, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r hr
  rw [hp.primeFactors, Finset.mem_singleton] at hr
  subst hr
  exact not_le.mpr hyp

/-- The prime-power strip vanishes at a prime `> y` (same reason: the `≤ y` cut is empty). -/
theorem sqStrip_eq_zero_of_prime_gt {y p : ℕ} (hp : p.Prime) (hyp : y < p) :
    sqStrip y p = 0 := by
  rw [sqStrip, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r hr hcon
  rw [hp.primeFactors, Finset.mem_singleton] at hr
  subst hr
  exact absurd hcon.1 (not_le.mpr hyp)

/-- A prime is not a Chen triple: `p = p₁p₂p₃` with three primes forces `Ω(p) = 3 ≠ 1`. -/
theorem not_tripleP_of_prime {y p : ℕ} (hp : p.Prime) : ¬ TripleP y p := by
  rintro ⟨p₁, p₂, p₃, hp1, hp2, hp3, hprod, -, -, -⟩
  have h1 : cardFactors p = 1 := cardFactors_apply_prime hp
  have hp12 : cardFactors (p₁ * p₂) = cardFactors p₁ + cardFactors p₂ :=
    cardFactors_mul hp1.ne_zero hp2.ne_zero
  have hp123 : cardFactors (p₁ * p₂ * p₃) = cardFactors (p₁ * p₂) + cardFactors p₃ :=
    cardFactors_mul (mul_ne_zero hp1.ne_zero hp2.ne_zero) hp3.ne_zero
  have ha : cardFactors p₁ = 1 := cardFactors_apply_prime hp1
  have hb : cardFactors p₂ = 1 := cardFactors_apply_prime hp2
  have hc : cardFactors p₃ = 1 := cardFactors_apply_prime hp3
  rw [hprod] at h1
  omega

/-- **N3 — the readable weight.**  Any function of the three landed y-capped decorations. -/
noncomputable def readableWeight (f : ℝ → ℝ → ℝ → ℝ) (y m : ℕ) : ℝ :=
  f (omegaLe y m : ℝ) (tripleT y m) (sqStrip y m : ℝ)

/-- Every readable weight reads `f 0 0 0` at a heavy semiprime: all three decorations vanish. -/
theorem readableWeight_heavy (f : ℝ → ℝ → ℝ → ℝ) {y p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hyp : y < p) (hyq : y < q) :
    readableWeight f y (p * q) = f 0 0 0 := by
  have ht : tripleT y (p * q) = 0 := by
    unfold tripleT; rw [if_neg (not_tripleP_of_heavy hp hq hyp hyq)]
  rw [readableWeight, omegaLe_eq_zero_of_heavy hp hq hyp hyq,
    sqStrip_eq_zero_of_heavy hp hq hyp hyq, ht]
  simp only [Nat.cast_zero]

/-- Every readable weight reads `f 0 0 0` at a window prime `> y`: all three decorations vanish. -/
theorem readableWeight_window_prime (f : ℝ → ℝ → ℝ → ℝ) {y p : ℕ}
    (hp : p.Prime) (hyp : y < p) :
    readableWeight f y p = f 0 0 0 := by
  have ht : tripleT y p = 0 := by
    unfold tripleT; rw [if_neg (not_tripleP_of_prime hp)]
  rw [readableWeight, omegaLe_eq_zero_of_prime_gt hp hyp,
    sqStrip_eq_zero_of_prime_gt hp hyp, ht]
  simp only [Nat.cast_zero]

/-- **THE BLINDNESS.**  No readable weight can separate a heavy semiprime from a window prime:
both read the identical value `f 0 0 0`, for EVERY `f`.  This is the pointwise statement behind
the impostor's invisibility to the landed decorations. -/
theorem readableWeight_blind (f : ℝ → ℝ → ℝ → ℝ) {y p q p' : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime)
    (hyp : y < p) (hyq : y < q) (hyp' : y < p') :
    readableWeight f y (p * q) = readableWeight f y p' := by
  rw [readableWeight_heavy f hp hq hyp hyq, readableWeight_window_prime f hp' hyp']

/-! ## Part B — N4: the escape, the minimal separating decoration

`bigOmegaGt y m` counts the prime factors of `m` that exceed `y`, WITH multiplicity.  It is the
minimal decoration the impostor's E2-redistribution cannot survive: it reads `1` at a window
prime and `2` at EVERY heavy E2 point.  Crucially this INCLUDES the heavy square `p²` — whose
single distinct prime factor `p` carries multiplicity `2`, so the DISTINCT-count variant reads
`1` there and FAILS to separate (the freeze-time catch, N4 case table).  The multiplicity count
reads `2` uniformly, so it is the frozen escape.

But `bigOmegaGt` is NOT a route to twins.  The carrier row a certificate reading it would need is
a LOWER bound on the heavy-semiprime mass — exactly **GAP-E**, the B2 census's named missing
theorem (`TwinDeficit`'s `hE2lo`-shaped hypothesis `XW·e2lo ≤ e2PrimeSum`).  The corpus bounds the
triple mass from ABOVE; nothing bounds the E2 mass from BELOW, and that lower bound is
parity-sensitive — the fundamental barrier.  The escape NAMES where twin progress must come from;
it is not itself progress.  Only the two separation equalities below are asserted in Lean. -/

/-- **N4 — the escape.**  The count of prime factors of `m` above `y`, WITH multiplicity. -/
def bigOmegaGt (y m : ℕ) : ℕ :=
  ∑ p ∈ m.primeFactors.filter (fun p => y < p), m.factorization p

/-- `bigOmegaGt` reads `1` at a window prime `> y`: the single prime factor `p` (multiplicity 1)
survives the `y <` cut. -/
theorem bigOmegaGt_prime {y p : ℕ} (hp : p.Prime) (hyp : y < p) :
    bigOmegaGt y p = 1 := by
  have hfilter : p.primeFactors.filter (fun r => y < r) = p.primeFactors := by
    apply Finset.filter_true_of_mem
    intro r hr
    rw [hp.primeFactors, Finset.mem_singleton] at hr
    subst hr
    exact hyp
  rw [bigOmegaGt, hfilter, ← cardFactors_eq_sum_pf, cardFactors_apply_prime hp]

/-- `bigOmegaGt` reads `2` at EVERY heavy semiprime `p·q` (`y < p, q`) — including the square
point `p²` (take `q = p`: the statement never assumes `p ≠ q`, and `factorization p² p = 2`
supplies the second unit that defeats the distinct-count variant).  Route (gate amendment A2):
every prime factor of `p·q` exceeds `y` (`heavy_semiprime_factors`), so the `y <` filter keeps ALL
of `primeFactors`; then `bigOmegaGt = Ω(p·q) = Ω(p) + Ω(q) = 1 + 1`.  No `p = q` case split. -/
theorem bigOmegaGt_heavy {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) :
    bigOmegaGt y (p * q) = 2 := by
  have hfilter : (p * q).primeFactors.filter (fun r => y < r) = (p * q).primeFactors :=
    Finset.filter_true_of_mem (heavy_semiprime_factors hp hq hyp hyq)
  have hΩ : bigOmegaGt y (p * q) = cardFactors (p * q) := by
    rw [bigOmegaGt, hfilter, ← cardFactors_eq_sum_pf]
  have hmul : cardFactors (p * q) = cardFactors p + cardFactors q :=
    cardFactors_mul hp.ne_zero hq.ne_zero
  have hp1 : cardFactors p = 1 := cardFactors_apply_prime hp
  have hq1 : cardFactors q = 1 := cardFactors_apply_prime hq
  omega

end Salt.Chen
