/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TwinDeficit
import Salt.Chen.WeightFamily

/-!
# The weight no-go atlas (WeightNoGo)

**Honest headline: no y-capped decoration certificate certifies P₁.**  The three landed
decorations of Chen's weight (`omegaLe y`, `tripleT y`, `sqStrip y`) read only prime-factor
structure at or below `y`.  A window prime and a heavy semiprime `p·q` (with `y < p, q`) are
therefore decoration-identical — both read `(0, 0, 0)` (`TwinDeficit.heavy_semiprime_obstruction`).

Consequence, made abstract here: over the corpus-certified constraint set on the six observables
`(a₁, a₂, a₃, s, p₁, e₂)` (the four carrier rows plus the twin/two-factor split), the **impostor**
— same four carrier-row values, all P₂ mass poured into `e₂`, twin mass `p₁` zeroed — satisfies
every constraint (`impostor_feasible`).  So any certificate `Φ` reading only the four carrier-row
values and valid over the feasible set can lower-bound the twin mass by nothing positive
(`no_readable_certificate` : `Φ ≤ 0`).  The absence of a positive `p₁`-row *is* the theorem.

## Scope (binding, R4)

* The theorem covers every certificate readable from the **y-capped** decoration data.  It says
  NOTHING about decorations reading structure **above** `y` — that region is open and is exactly
  the parity barrier / GAP-E (the minimal escape is the above-`y` factor count, whose carrier is
  GAP-E; see `Salt.Chen.WeightEscape`).
* Every Lean conclusion below is an upper cap (`Φ … ≤ 0`) or an identity of readings.  NO
  twin-prime-adjacent existence claim appears anywhere.
* The impostor is the primal witness to the landed `deficit_floor_of_certs`: it places the entire
  P₂ mass in `e₂` (with `p₁ = 0`), consistent with the razor's certified VALUE floor
  `XW/200 ≤ p2RazorLHS`.  This is read at the razor VALUE level only — never as the mass-level
  `e2lo`-vs-`a1up` comparison (the GAP-U erratum, `TwinDeficit`'s Part F).

This module imports `Salt.Chen.TwinDeficit` (the decorations, the carrier rows via `Assembly`, the
split, and the certified floor) and `Salt.Chen.WeightFamily` (only for `chenWeightA`, used by the
affine-family instance in Part C).  Everything here is sorry-free and axiom-clean.
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the abstract no-go (the flagship, standalone) -/

/-- **The corpus-certified constraint set** on the six observables
`(a₁, a₂, a₃, s, p₁, e₂)` — the four carrier rows (`a₁` = the A₁ prime mass with a lower AND an
upper cap; `a₂, a₃, s` = the three decoration carriers, each nonneg with an upper cap), plus the
twin/two-factor split (`p₁, e₂ ≥ 0`), the trivial mass cap `p₁ + e₂ ≤ a₁` (the `p2Ind ≤ 1`
bound, granted to the certificate on purpose), and the razor floor
`a₁ − a₂/2 − a₃/2 − s/2 ≤ p₁ + e₂` (the landed `razor_reduction`, in split form).  Parametric in
the row-bound constants so the certificate may be granted every cap. -/
def Feasible (A₁lo A₁hi A₂hi A₃hi Shi : ℝ)
    (a₁ a₂ a₃ s p₁ e₂ : ℝ) : Prop :=
  A₁lo ≤ a₁ ∧ a₁ ≤ A₁hi ∧
  0 ≤ a₂ ∧ a₂ ≤ A₂hi ∧
  0 ≤ a₃ ∧ a₃ ≤ A₃hi ∧
  0 ≤ s ∧ s ≤ Shi ∧
  0 ≤ p₁ ∧ 0 ≤ e₂ ∧
  p₁ + e₂ ≤ a₁ ∧
  a₁ - a₂ / 2 - a₃ / 2 - s / 2 ≤ p₁ + e₂

/-- **The impostor.**  Same four carrier rows, twin mass `p₁` zeroed, all P₂ mass poured into
`e₂` (`p₁ + e₂`): it satisfies every constraint the corpus certifies.  Clauses 1–8 are untouched
(the `a`-values are fixed); clause 9 becomes `0 ≤ 0`; clause 10 becomes `0 ≤ p₁ + e₂`; clause 11
becomes `0 + (p₁ + e₂) ≤ a₁` (was clause 11); clause 12's RHS is the unchanged sum.  No clause
detects the move. -/
theorem impostor_feasible {A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ : ℝ}
    (h : Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂) :
    Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s 0 (p₁ + e₂) := by
  unfold Feasible at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, le_refl 0, by linarith, by linarith, by linarith⟩

/-- **THE FLAGSHIP.**  Any certificate `Φ` reading only the four carrier-row values
`(a₁, a₂, a₃, s)`, valid over the corpus-certified feasible set (`hΦ : Φ ≤ p₁` on every feasible
point), certifies NOTHING: its guaranteed twin mass is `≤ 0`.  Note the quantifier order — `Φ` is
bound AFTER the row-bound constants, so `Φ` may encode every certified constant freely; the
theorem still kills it (apply `hΦ` at the impostor, whose `p₁`-slot is literally `0`). -/
theorem no_readable_certificate {A₁lo A₁hi A₂hi A₃hi Shi : ℝ}
    (Φ : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hΦ : ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ →
      Φ a₁ a₂ a₃ s ≤ p₁) :
    ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ →
      Φ a₁ a₂ a₃ s ≤ 0 := by
  intro a₁ a₂ a₃ s p₁ e₂ hf
  exact hΦ a₁ a₂ a₃ s 0 (p₁ + e₂) (impostor_feasible hf)

/-- **The III.3″ schematic witness** — a twin-void configuration sitting exactly ON the certified
razor floor.  Parameters `(1, 21/20, 1, 1, 1)`, values `(1, 199/300, 199/300, 199/300, 0, 1/200)`;
clause 12 holds at EQUALITY (`1 − 3·(199/300)/2 = 1/200 = 0 + 1/200`), the worst case.  So a
configuration with zero twin mass is feasible. -/
example : Feasible 1 (21/20) 1 1 1
    1 (199/300) (199/300) (199/300) 0 (1/200) := by
  norm_num [Feasible]

/-! ## Part B — the corpus realization (the operating-point III.3″ witness) -/

/-- The P₂ carrier is capped by the A₁ carrier alone: `p2Ind ≤ 1` pointwise (a P₂ indicator is
`0` or `1`), then `Finset.sum_le_sum`.  This is the trivial GAP-U mass cap — clause 11 of
`Feasible` in split form, granted to the certificate on purpose. -/
theorem p2PrimeSum_le_A1primeSum (x z P : ℕ) : p2PrimeSum x z P ≤ A1primeSum x P := by
  rw [p2PrimeSum, A1primeSum]
  apply Finset.sum_le_sum
  intro n _
  have hp2 : p2Ind z (n + 2) ≤ 1 := by unfold p2Ind; split_ifs <;> norm_num
  have hnn : 0 ≤ vonMangoldt n * keepR P n :=
    mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)
  calc vonMangoldt n * keepR P n * p2Ind z (n + 2)
      ≤ vonMangoldt n * keepR P n * 1 := mul_le_mul_of_nonneg_left hp2 hnn
    _ = vonMangoldt n * keepR P n := mul_one _

/-- **N0 — the corpus realizes `Feasible`.**  At a landed operating tuple, the four decoration
carriers, the twin carrier `p1PrimeSum`, and the two-factor carrier `e2PrimeSum` satisfy every
clause of `Feasible`, under the corpus-certified structural + carrier-link hypotheses (the subset
of `p2RazorLHS_ge_of_certs`'s package that a `Feasible` clause actually consumes, plus `hyx` for
`razor_reduction` and the strip cap `stripBd`; the razor-floor certificate constants are not a
`Feasible` clause, so they are not carried).  The `A₁hi` slot instantiates reflexively (`a₁ ≤ a₁`);
clause 11 (mass cap) is the split + `p2PrimeSum_le_A1primeSum`; clause 12 (razor floor) is
`razor_reduction` + the split.  Combined with the landed `deficit_floor_of_certs`, the impostor's
E2 mass lives in the band `[XW/200, XW·a1up]` — read at the razor VALUE level. -/
theorem corpus_feasible {x z P y : ℕ} {mainA1 mainA2 mainA3 stripBd : ℝ}
    (hx : 2 ≤ x) (hyx : x < (y + 1) ^ 3)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : triplePrimeSum x P y ≤ mainA3)
    (hstrip : stripPrimeSum x P y ≤ stripBd) :
    Feasible mainA1 (A1primeSum x P) mainA2 mainA3 stripBd
      (A1primeSum x P) (omegaPrimeSum x P y) (triplePrimeSum x P y)
      (stripPrimeSum x P y) (p1PrimeSum x P) (e2PrimeSum x z P) := by
  have hsplit := p2PrimeSum_split x z P
  have hcap := p2PrimeSum_le_A1primeSum x z P
  have hrazor := razor_reduction hx hyx hPfull
  unfold Feasible
  exact ⟨hA1, le_refl _, omegaPrimeSum_nonneg x P y, hA2,
    triplePrimeSum_nonneg x P y, hA3, stripPrimeSum_nonneg x P y, hstrip,
    p1PrimeSum_nonneg x P, e2PrimeSum_nonneg x z P, by linarith, by linarith⟩

/-! ## Part C — the registered affine family reads exactly the four rows -/

/-- **The affine decoration family** — an arbitrary real-affine functional of the three landed
`y`-capped decorations `(omegaLe y, tripleT y, sqStrip y)`.  This is the whole registered class of
readable weights: `chenWeightA α` is the member `(c₀, c₁, c₂, c₃) = (1, −α, −α, −α)`. -/
noncomputable def readableAffineWeight (c₀ c₁ c₂ c₃ : ℝ) (y m : ℕ) : ℝ :=
  c₀ + c₁ * (omegaLe y m : ℝ) + c₂ * tripleT y m + c₃ * (sqStrip y m : ℝ)

/-- `chenWeightA α` is the affine member with coefficients `(1, −α, −α, −α)` (ring-closed: `sub`
vs `+neg` are not defeq). -/
theorem readableAffineWeight_chenWeightA (α : ℝ) (y m : ℕ) :
    chenWeightA α y m = readableAffineWeight 1 (-α) (-α) (-α) y m := by
  unfold chenWeightA readableAffineWeight
  ring

/-- **The carrier identity.**  Summing `Λ·keep·readableAffineWeight` over the SAME index set and
`Λ·keep` weight as `A1primeSum` collapses to a real-affine combination of the four landed
carriers — so every affine readable weight is certified purely by the four row values.  Pure
`Finset.mul_sum` + `Finset.sum_add_distrib`. -/
theorem affine_carrier_identity (c₀ c₁ c₂ c₃ : ℝ) (x P y : ℕ) :
    (∑ n ∈ twinWindow x,
        vonMangoldt n * keepR P n * readableAffineWeight c₀ c₁ c₂ c₃ y (n + 2))
      = c₀ * A1primeSum x P + c₁ * omegaPrimeSum x P y
        + c₂ * triplePrimeSum x P y + c₃ * stripPrimeSum x P y := by
  rw [A1primeSum, omegaPrimeSum, triplePrimeSum, stripPrimeSum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [readableAffineWeight]
  ring

/-- **Corollary — the affine class certifies nothing.**  For any real coefficients
`(c₀, c₁, c₂, c₃)`, if the affine functional `c₀·a₁ + c₁·a₂ + c₂·a₃ + c₃·s` of the four carrier
rows lower-bounds the twin mass `p₁` over the corpus-certified feasible set, then it is `≤ 0`
there: the registered class of readable weights delivers no positive twin certificate.  Instance
of `no_readable_certificate` at the affine `Φ`. -/
theorem no_affine_certificate {A₁lo A₁hi A₂hi A₃hi Shi : ℝ} (c₀ c₁ c₂ c₃ : ℝ)
    (hΦ : ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ →
      c₀ * a₁ + c₁ * a₂ + c₂ * a₃ + c₃ * s ≤ p₁) :
    ∀ a₁ a₂ a₃ s p₁ e₂,
      Feasible A₁lo A₁hi A₂hi A₃hi Shi a₁ a₂ a₃ s p₁ e₂ →
      c₀ * a₁ + c₁ * a₂ + c₂ * a₃ + c₃ * s ≤ 0 := by
  intro a₁ a₂ a₃ s p₁ e₂ hf
  exact no_readable_certificate
    (fun a₁ a₂ a₃ s => c₀ * a₁ + c₁ * a₂ + c₂ * a₃ + c₃ * s) hΦ a₁ a₂ a₃ s p₁ e₂ hf

end Salt.Chen
