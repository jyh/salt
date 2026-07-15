/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TwinDeficit

/-!
# Q5b Axis C — the weight-family optimality (the α knob, and the (z,y) operating point)

**This is EXPLORATION, not a frozen blueprint node.**  Design context:
`docs/exploration/q5b-class.md` (Axis C, frozen by registration amendment A2).  The file adds NEW
work only; it edits no landed file and is not wired into `Salt.Chen.All`.  Everything here is
sorry-free and axiom-clean; every OPEN question is recorded as prose, never as a `sorry`'d theorem.

## THE CONSTRAINT STORE (the α-family, its admissible range, the margin — READ BEFORE ANY PROOF)

**The knob.**  The landed Chen weight (`WeightTrivia.chenWeight`) is

  `chenWeight y m = 1 − ½·ω_{≤y}(m) − ½·1_T(m) − ½·S(m)`,

a single coefficient `½` sitting IDENTICALLY on all three decorations `ω_{≤y}` (small distinct
prime factors), `1_T` (the `p₁≤y<p₂≤p₃` triple pattern) and `S` (the prime-power strip count).
Axis C promotes that `½` to a knob `α`:

  `chenWeightA α y m := 1 − α·ω_{≤y}(m) − α·1_T(m) − α·S(m)`   (`chenWeightA`).

`chenWeightA (1/2) = chenWeight` (`chenWeightA_half`, the anti-vacuity regression).

**Admissibility = α ≥ 1/2, EXACTLY.**  The weight earns its keep only as a lower-bounding sieve
weight, i.e. through the domination `chenWeightA α y m ≤ 1_{P₂}(m)` at every sifted `m` (all prime
factors `≥ z`, `m < (y+1)³`).  The honest constraint is read off the landed structural dichotomy
`WeightTrivia.chen_weight_struct`: a sifted non-`P₂` `m` has `ω_{≤y}(m) + 1_T(m) + S(m) ≥ 2`.
Hence on a non-`P₂` point `chenWeightA α = 1 − α·(≥2)`, which is `≤ 0 = 1_{P₂}` iff `1 − 2α ≤ 0`,
i.e. **`α ≥ 1/2`** (`chenWeightA_le_indicator_of_sifted`, sufficiency; `admissible_worst_case`,
the scalar iff at the worst case).  The floor is TIGHT, not vacuous: at `m = 30 = 2·3·5`,
`z = 2`, `y = 3` the decoration sum is exactly `2` (`omegaLe_30 = 2`, `sqStrip_30 = 0`,
`tripleT_30 = 0`; `not_isP2_30`), so any `α < 1/2` OVERSHOOTS the `P₂` indicator there
(`admissible_necessary`).  The weight itself is NOT required nonnegative — it may go negative for
large `α`; the only honest constraint is domination, and it is `α ≥ 1/2`.

**The margin, and WHICH terms carry α.**  Summing `Λ·keep·chenWeightA α (n+2)` over the landed
window/keep multiplies each decoration's carrier by `α`, so the certified scalar razor
(`RazorClose.razor_scalar_margin`, the three normalised terms) becomes

  `M(α) = 9779/10000 − (3 + 43/75)·(log 6/4)·α − c̄·(3/8)·(243/100)·α`   (`marginFn`),

with the strip (a fourth, `O(1/log z)`) term `→ 0`.  Of the three surviving terms, the MAIN term
`A₁ = 9779/10000` (the sifted prime mass, the `1·1` of the weight) is **α-independent**; the two
SUBTRACTED terms — `A₂ = (3+43/75)·(log 6/4)` (the `ω`-count) and `A₃ = c̄·(3/8)·(243/100)` (the
triple count through the switch) — BOTH scale linearly with `α`.  So `M` is affine in `α`:

  `M(α) = 9779/10000 − K·α`,  `K = (3+43/75)·(log 6/4) + c̄·(3/8)·(243/100) > 0`

(`marginFn_linear`, `marginK_pos`).

**The optimum.**  `K > 0` ⟹ `M` is strictly decreasing (`marginFn_antitone`), so over the
admissible family `α ≥ 1/2` the margin is MAXIMISED at the smallest admissible `α`:

  **`alpha_half_optimal : 1/2 ≤ α → M(α) ≤ M(1/2)`**  (strict for `α > 1/2`, `alpha_half_strict`).

The landed `α = 1/2` is optimal within the family, with margin `M(1/2) = razor_scalar_margin
≥ 1/100` (`marginFn_half_ge`).  It sits at the boundary of admissibility: nothing smaller is a
valid weight, and everything larger only shrinks the margin.  (Numerically `M(1/2) ≈ 0.012151`
and `K ≈ 1.9315`, so `M(α) > 0` only for `α ∈ [1/2, 0.50629)` — the family dies almost
immediately past `½`; the exact `α_max = A₁/K` needs a LOWER bound on `c̄`, which the corpus does
not carry, so it is a numeric observation, not kernel-checked here.)

## R4 (the too-good-to-be-true tripwire) — armed, and structurally CLEAR

No `α` makes the razor reach the twin target.  The optimum only recovers the landed `P₂` margin;
the P₁ deficit is untouched, and by the invisibility corollary CANNOT be touched by any `α`:
at a heavy semiprime `p·q` (`y < p,q`) every decoration vanishes, so `chenWeightA α = chenWeight
= 1` for EVERY `α` (`chenWeightA_eq_one_of_heavy`), while the point is not P₁ and is E2
(`retune_invisible_at_heavy`, consuming the sibling `TwinDeficit.heavy_semiprime_obstruction`).
The E2-above-`y` mass — Axis B's deficit driver — is identically blind to the `α` knob, so the
in-family margin improvement (which is zero: `½` is optimal) does not and cannot change Axis B's
P₁-deficit conclusion.  Every statement here is an equality/upper-cap; none implies twins.

## The (z, y) operating grid — NUMERIC only, deliberately NOT in this file

The second Axis-C question — is `(z,y) = (x^{1/8}, x^{1/3})` optimal, and what margin is on the
table over a rational exponent grid — was mapped numerically (a `python3`/`mpmath` sweep of the
switch constant `c̄(a,b) = ∫_{a}^{b} log(2−3t)/(t(1−t)) dt` and the directly exponent-dependent
factors) and is reported in the probe's writeup with the honest caveat that the other razor
constants (`9779/10000`, the `243/100` switch bound, the `3/8` W-ratio, the `log 6` window cost)
are `(a,b)`-dependent only through the full Rosser cascade and would each need re-derivation per
grid point.  Per scope discipline, NO numeric-only claim is placed in this Lean file.
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the constraint store: the α-family weight -/

/-- **The α-family Chen weight** `1 − α·ω_{≤y} − α·1_T − α·S`.  The landed `WeightTrivia.chenWeight`
is the `α = ½` member; `α` is the single coefficient the landed argument fixes at `½`. -/
noncomputable def chenWeightA (α : ℝ) (y m : ℕ) : ℝ :=
  1 - α * (omegaLe y m : ℝ) - α * tripleT y m - α * (sqStrip y m : ℝ)

/-- **Anti-vacuity regression.**  At `α = ½` the family recovers the landed weight verbatim. -/
theorem chenWeightA_half (y m : ℕ) : chenWeightA (1 / 2) y m = chenWeight y m := by
  unfold chenWeightA chenWeight; ring

/-! ## Part B — admissibility: `α ≥ 1/2` is exactly forced

Sufficiency consumes the landed dichotomy `chen_weight_struct`; the scalar iff and the concrete
`m = 30` witness pin `1/2` as the tight floor (the constraint is not merely sufficient). -/

/-- **Sufficiency (the razor reduction's validity).**  For `α ≥ 1/2` the α-weight is dominated by
the `P₂` indicator at every sifted `m` (`2 ≤ m`, all prime factors `≥ z`, `m < (y+1)³`) — the
α-analogue of `chen_weight_le_indicator`, consuming `chen_weight_struct`.  This is exactly the
property that makes `chenWeightA α` a valid lower-bounding sieve weight. -/
theorem chenWeightA_le_indicator_of_sifted {z y m : ℕ} {α : ℝ} (hα : 1 / 2 ≤ α)
    (hm2 : 2 ≤ m) (hcop : ∀ p ∈ m.primeFactors, z ≤ p) (hmy : m < (y + 1) ^ 3) :
    chenWeightA α y m ≤ p2Ind z m := by
  have hα0 : 0 ≤ α := by linarith
  have hTnn : 0 ≤ tripleT y m := tripleT_nonneg y m
  have ho : 0 ≤ (omegaLe y m : ℝ) := by positivity
  have hs : 0 ≤ (sqStrip y m : ℝ) := by positivity
  unfold p2Ind
  by_cases hp2 : IsP2 z m
  · rw [if_pos hp2, chenWeightA]
    nlinarith [mul_nonneg hα0 ho, mul_nonneg hα0 hTnn, mul_nonneg hα0 hs]
  · rw [if_neg hp2, chenWeightA]
    have hstruct := chen_weight_struct hm2 hcop hmy hp2
    nlinarith [hstruct, hα,
      mul_nonneg (by linarith : (0 : ℝ) ≤ α - 1 / 2)
        (by linarith [hstruct] : (0 : ℝ) ≤ (omegaLe y m : ℝ) + tripleT y m + (sqStrip y m : ℝ))]

/-- **The scalar admissibility floor.**  Domination at the WORST-CASE decoration sum `2` (the floor
of `chen_weight_struct`) holds iff `α ≥ 1/2`.  This is the honest necessity: below `1/2` the
α-weight fails to dominate at a decoration sum of exactly `2`. -/
theorem admissible_worst_case (α : ℝ) : 1 - α * 2 ≤ 0 ↔ 1 / 2 ≤ α := by
  constructor <;> intro h <;> linarith

/-- `(30).primeFactors = {2, 3, 5}` — the arithmetic behind the tightness witness. -/
private theorem pf30 : (30 : ℕ).primeFactors = {2, 3, 5} := by
  rw [show (30 : ℕ) = 2 * 3 * 5 by norm_num]
  rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num)]
  decide

/-- At `m = 30`, `y = 3`: two small prime factors `2, 3`, so `ω_{≤3}(30) = 2`. -/
theorem omegaLe_30 : omegaLe 3 30 = 2 := by unfold omegaLe; rw [pf30]; decide

/-- At `m = 30`, `y = 3`: squarefree, so the prime-power strip is empty. -/
theorem sqStrip_30 : sqStrip 3 30 = 0 := by unfold sqStrip; rw [pf30]; decide

/-- `30` has no `p₁≤3<p₂≤p₃` triple factorisation: two prime factors `> 3` would force the product
`≥ 2·5·5 = 50 > 30`.  Hence the triple pattern fails. -/
theorem not_tripleP_30 : ¬ TripleP 3 30 := by
  rintro ⟨p₁, p₂, p₃, hp1, hp2, hp3, hprod, _hp1y, hp2y, hp23⟩
  have h1 : 2 ≤ p₁ := hp1.two_le
  have h2 : 5 ≤ p₂ := by
    have : p₂ ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hp2
    omega
  have h3 : 5 ≤ p₃ := le_trans h2 hp23
  have hge : 50 ≤ p₁ * p₂ * p₃ :=
    le_trans (by norm_num) (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3)
  omega

/-- At `m = 30`, `y = 3`: the triple indicator is `0`. -/
theorem tripleT_30 : tripleT 3 30 = 0 := by unfold tripleT; rw [if_neg not_tripleP_30]

/-- `30` is not `P₂` (it is `2·3·5`, three primes): no prime and no product of two primes. -/
theorem not_isP2_30 : ¬ IsP2 2 30 := by
  rintro (h | ⟨p, q, hp, hq, hpq, -, -⟩)
  · exact (by decide : ¬ Nat.Prime 30) h
  · have h2p := hp.two_le
    have h2q := hq.two_le
    have hp15 : p ≤ 15 := by nlinarith [hpq]
    have hq15 : q ≤ 15 := by nlinarith [hpq]
    interval_cases p <;> interval_cases q <;>
      first
        | exact absurd hpq (by decide)
        | exact absurd hp (by decide)
        | exact absurd hq (by decide)

/-- The α-weight at the witness point: `chenWeightA α 3 30 = 1 − 2α` (decoration sum `2`). -/
theorem chenWeightA_30 (α : ℝ) : chenWeightA α 3 30 = 1 - 2 * α := by
  rw [chenWeightA, omegaLe_30, sqStrip_30, tripleT_30]; push_cast; ring

/-- **Necessity — the floor is tight.**  For any `α < 1/2` the α-weight OVERSHOOTS the `P₂`
indicator at the sifted non-`P₂` point `m = 30` (`z = 2`, `y = 3`): `p2Ind = 0 < 1 − 2α =
chenWeightA α`.  So `chenWeightA_le_indicator_of_sifted`'s hypothesis `α ≥ 1/2` cannot be
relaxed — `½` is the exact admissibility boundary, and the necessity is non-vacuous. -/
theorem admissible_necessary {α : ℝ} (hα : α < 1 / 2) : p2Ind 2 30 < chenWeightA α 3 30 := by
  have hp2 : p2Ind 2 30 = 0 := by unfold p2Ind; rw [if_neg not_isP2_30]
  rw [chenWeightA_30, hp2]; linarith

/-! ## Part C — the margin function `M(α)` at the certified constants -/

/-- **The α-parametrised scalar razor margin.**  The certified three-term razor
(`razor_scalar_margin`) with the `α` knob restored on the two subtracted (decoration) carriers;
the main term `9779/10000` is `α`-independent.  The strip term is `O(1/log z) → 0`. -/
noncomputable def marginFn (α : ℝ) : ℝ :=
  9779 / 10000 - (3 + 43 / 75) * (Real.log 6 / 4) * α - cbar * (3 / 8) * (243 / 100) * α

/-- At `α = ½` the margin function is literally the certified `razor_scalar_margin` RHS. -/
theorem marginFn_half :
    marginFn (1 / 2) = 9779 / 10000 - (3 + 43 / 75) * (Real.log 6 / 4) / 2
        - cbar * (3 / 8) * (243 / 100) / 2 := by
  unfold marginFn; ring

/-- **Anti-vacuity + the landed value.**  `M(1/2) ≥ 1/100` — the landed certified margin,
consuming `razor_scalar_margin` (hence `cbar_lt` and the `LogToolkit` log sandwiches). -/
theorem marginFn_half_ge : (1 : ℝ) / 100 ≤ marginFn (1 / 2) := by
  rw [marginFn_half]; exact razor_scalar_margin

/-- **`M` is affine in `α`.**  `M(α) = 9779/10000 − K·α` with `K` the total decoration cost. -/
theorem marginFn_linear (α : ℝ) :
    marginFn α = 9779 / 10000
      - ((3 + 43 / 75) * (Real.log 6 / 4) + cbar * (3 / 8) * (243 / 100)) * α := by
  unfold marginFn; ring

/-- **The slope is strictly negative.**  `K = (3+43/75)·(log 6/4) + c̄·(3/8)·(243/100) > 0`
(`log 6 > 0`, `c̄ > 0`), so raising `α` strictly shrinks the margin. -/
theorem marginK_pos :
    0 < (3 + 43 / 75) * (Real.log 6 / 4) + cbar * (3 / 8) * (243 / 100) := by
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hc : 0 < cbar := cbar_pos
  have t1 : 0 < (3 + 43 / 75) * (Real.log 6 / 4) :=
    mul_pos (by norm_num) (by linarith)
  have t2 : 0 < cbar * (3 / 8) * (243 / 100) :=
    mul_pos (mul_pos hc (by norm_num)) (by norm_num)
  linarith

/-- **`M` is antitone.**  From `K > 0`: `α ≤ β ⟹ M(β) ≤ M(α)`. -/
theorem marginFn_antitone {α β : ℝ} (h : α ≤ β) : marginFn β ≤ marginFn α := by
  have hK := marginK_pos
  have hdiff : marginFn α - marginFn β
      = ((3 + 43 / 75) * (Real.log 6 / 4) + cbar * (3 / 8) * (243 / 100)) * (β - α) := by
    unfold marginFn; ring
  have hprod : 0 ≤ ((3 + 43 / 75) * (Real.log 6 / 4) + cbar * (3 / 8) * (243 / 100)) * (β - α) :=
    mul_nonneg hK.le (by linarith)
  linarith [hdiff, hprod]

/-- **`alpha_half_optimal` — the headline.**  Over the admissible family `α ≥ 1/2`, the razor
margin is MAXIMISED at the landed knob `α = 1/2`: `M(α) ≤ M(1/2)`.  Combined with
`marginFn_half_ge` (`M(1/2) ≥ 1/100`), the landed `½` is the in-family optimum, sitting exactly
at the boundary of admissibility (nothing smaller is a valid weight; everything larger costs
margin). -/
theorem alpha_half_optimal {α : ℝ} (hα : 1 / 2 ≤ α) : marginFn α ≤ marginFn (1 / 2) :=
  marginFn_antitone hα

/-- The optimum is strict: any `α > 1/2` STRICTLY loses margin. -/
theorem alpha_half_strict {α : ℝ} (hα : 1 / 2 < α) : marginFn α < marginFn (1 / 2) := by
  have hK := marginK_pos
  have hdiff : marginFn (1 / 2) - marginFn α
      = ((3 + 43 / 75) * (Real.log 6 / 4) + cbar * (3 / 8) * (243 / 100)) * (α - 1 / 2) := by
    unfold marginFn; ring
  have hprod : 0 <
      ((3 + 43 / 75) * (Real.log 6 / 4) + cbar * (3 / 8) * (243 / 100)) * (α - 1 / 2) :=
    mul_pos hK (by linarith)
  linarith [hdiff, hprod]

/-! ## Part D — the invisibility corollary (complements `heavy_semiprime_obstruction`) -/

/-- **The α-family collapses on heavy semiprimes.**  At `p·q` with `y < p, q` every decoration
vanishes (`omegaLe_eq_zero_of_heavy`, `sqStrip_eq_zero_of_heavy`, `not_tripleP_of_heavy`), so
`chenWeightA α y (p·q) = 1` for EVERY `α` — the knob has no effect there. -/
theorem chenWeightA_eq_one_of_heavy {α : ℝ} {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) : chenWeightA α y (p * q) = 1 := by
  have ht : tripleT y (p * q) = 0 := by
    unfold tripleT; rw [if_neg (not_tripleP_of_heavy hp hq hyp hyq)]
  rw [chenWeightA, omegaLe_eq_zero_of_heavy hp hq hyp hyq,
    sqStrip_eq_zero_of_heavy hp hq hyp hyq, ht]
  push_cast; ring

/-- **THE INVISIBILITY COROLLARY.**  At a heavy semiprime `p·q` (`z ≤ p,q`, `y < p,q`) the ENTIRE
α-family agrees with the landed weight — `chenWeightA α y (p·q) = chenWeight y (p·q) = 1` for
every `α` — while the point is not P₁ (`p1Ind = 0`) and IS E2 (`e2Ind = 1`).  Consuming the
sibling `TwinDeficit.heavy_semiprime_obstruction`, this pins the Axis-C ⟷ Axis-B connection: the
E2-above-`y` mass (Axis B's deficit driver) is identically blind to the knob Axis C tunes, so the
in-family margin optimisation (which yields nothing beyond the landed `½`, `alpha_half_optimal`)
does not and cannot change the P₁-deficit conclusion. -/
theorem retune_invisible_at_heavy {α : ℝ} {z y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hzp : z ≤ p) (hzq : z ≤ q) (hyp : y < p) (hyq : y < q) :
    chenWeightA α y (p * q) = chenWeight y (p * q)
      ∧ p1Ind (p * q) = 0 ∧ e2Ind z (p * q) = 1 := by
  obtain ⟨hcw, hp1, he2⟩ := heavy_semiprime_obstruction hp hq hzp hzq hyp hyq
  exact ⟨by rw [chenWeightA_eq_one_of_heavy hp hq hyp hyq, hcw], hp1, he2⟩

end Salt.Chen
