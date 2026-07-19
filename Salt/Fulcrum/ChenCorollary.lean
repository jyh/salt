/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenTheorem

/-!
# A small Chen corollary — `Ω(p·(p+2)) ≤ 3` infinitely often (`fulcrum`)

Provenance: `docs/exploration/fulcrum-pass3.md` (verdict D1 bundled this A-class
corollary) and `docs/exploration/pass2_e2.md` §3 (the statement-level observation:
"`chen_headline` gives `Ω(p·(p+2)) ≤ 3` infinitely often"). This lands that
observation as a named theorem, on top of the unconditional `chen_headline`.

The arithmetic is completely-additive `Ω = cardFactors`: for a prime `p`,
`Ω(p) = 1`, and Chen's `IsP2 2 (p+2)` gives `Ω(p+2) ≤ 2` (prime ⟹ `1`; a product
of two primes ⟹ `1 + 1`), so `Ω(p·(p+2)) = Ω(p) + Ω(p+2) ≤ 3`. The target set is
therefore a SUPERSET of `chen_headline`'s set, and `Set.Infinite.mono` transports
the infinitude. (`Ω ≤ 3 → twins` is exactly the parity step — this is a Chen
by-product, not twin progress; verdict "honest-shape law".)

Placed under `Salt/Fulcrum/` per the D1 commission (single-writer: this file does
not touch the landed `Salt/Chen/` surfaces it consumes).
-/

open ArithmeticFunction Salt.Chen

namespace Salt.Fulcrum

/-- **Chen's almost-prime corollary**: there are infinitely many primes `p` with
`Ω(p·(p+2)) ≤ 3` (`Ω = cardFactors`, prime factors with multiplicity). A superset
of `chen_headline`'s set: `Ω(p) = 1` and `IsP2 2 (p+2)` forces `Ω(p+2) ≤ 2`. -/
theorem chen_omega_prod_le_three :
    {p : ℕ | p.Prime ∧ cardFactors (p * (p + 2)) ≤ 3}.Infinite := by
  apply chen_headline.mono
  intro p hp
  obtain ⟨hpp, hP2⟩ := hp
  have hp0 : p ≠ 0 := hpp.ne_zero
  have hp20 : p + 2 ≠ 0 := by omega
  have hΩp : cardFactors p = 1 := cardFactors_apply_prime hpp
  have hΩp2 : cardFactors (p + 2) ≤ 2 := by
    rcases hP2 with hpr | ⟨a, b, ha, hb, hab, -, -⟩
    · have h1 : cardFactors (p + 2) = 1 := cardFactors_apply_prime hpr
      omega
    · have h2 : cardFactors (p + 2) = 2 := by
        rw [hab, cardFactors_mul ha.ne_zero hb.ne_zero,
          cardFactors_apply_prime ha, cardFactors_apply_prime hb]
      omega
  refine ⟨hpp, ?_⟩
  rw [cardFactors_mul hp0 hp20, hΩp]
  omega

end Salt.Fulcrum
