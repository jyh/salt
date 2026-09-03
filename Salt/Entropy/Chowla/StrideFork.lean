/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦STRIDE FORK⟧ — the foundation of the stride/offset de-specialisation of the log-Chowla
spine, λ-BV wave 2-S step F1 (2026-09-03)

The landed spine is Tao arXiv:1509.05422 Theorem 2.3 at the model point `(a, b) = (1, 0)`;
`ShiftFork` opened the shift-`h` axis beside it and `AffineFork` stated the failure Prop
`logChowlaFailsAff a b h` and the supply demand `LogChowlaAffSupply a b h` at the affine forms
`a·n + b`, `a·n + b + h`.  This module opens the OBJECTS Tao's general-stride proof runs on,
beside the landed ones, exactly as `ShiftFork` did for `h`: every landed declaration keeps its
bytes and its arity; the compat lemmas pin the landed objects as the `(1, 0)` members.

⟦THE DESIGN, IN FOUR LINES — freeze `2026-09-03-math-FREEZE-lambda-bv-wave2S-stride.md` §1⟧
* Tao's entropy argument at stride `a` runs on the tuple `(g(a·n + j))_{j ≤ H}` with `n`
  log-random (Prop 2.6, textdump:719-724; Lemma 3.4, :1288-1302).  In the corpus that tuple is
  `liouvilleWindow H m` at `m = a·n`, i.e. the landed windows under the PUSHFORWARD measure
  `logMeasureAff a x ω := (logMeasure x ω).map (a * ·)`.  The measure carries the stride; the
  windows, the residue data and the entropy inequalities are the landed objects.
* The offset `b` enters ONLY through the class filter `j ≡ p·b (mod a)` on the window index
  inside the prime-averaged correlation (Tao (3.16), :1288-1290) and, after the Fourier
  expansion of that filter, through the frequency set `Ξ_H` (Lemma 3.4).  It never enters the
  measure and never enters the entropy decrement.
* The frequency set is Tao's `Ξ_H` with the `η ∈ ℤ/aℤ` union made VISIBLE (`bigXiAff`); with
  `a ∣ H` (the tower's `dvd_chowlaTower`, Tao's "H a multiple of a", :1360) every frequency it
  produces lies on the landed `1/H` grid, so `bigXi_bounded` transfers by a fibre count and the
  constants of the circle-method estimate are `a`-FREE (the `H/a` of the class sum cancels the
  `a` of the `η`-sum, :1364-1370).
* The door stays at the UNTWISTED `ξ` (the `h`-fork's law, `ShiftFork` D3), now integrated
  against `logMeasureAff`.  Its supply is the `h`-lane's supply read at the modulus parameter
  `a·h` plus an exact `x`-scaling identity (freeze §1(D)); this module states the door and its
  seam, not the supply.

⛔ **Degenerate values.**  `a = 0`: `logMeasureAff 0 x ω` is the Dirac mass at `0`, `bigXiAff
0 b h` is `∅` (`Finset.range 0`), and `logChowlaFailsAff 0 0 h` is false at every regime
(`liouville 0 = 0`, `AffineFork`'s header).  Every statement below that manufactures an
`H`-uniform constant or reads a window at `a·n ≥ 1` carries `0 < a` EXPLICITLY.  `h = 0`
inherits `ShiftFork`'s degeneracy (`gcd 0 H = H`); the fibre bounds carry `0 < h`.  `b` is
unconstrained here — the cardinality bounds are uniform in `b` because a translate has the
same card; `b ≤ Hlo` (Tao Lemma 2.5's `|r| ≤ H₋`) is the regime field `ChowlaRegimeAff.hb`.

⚖️ **The stride is named ONCE (refuter verdict 2026-09-03 13:30, kill A4).**  The doors and the
seams take `(R : ChowlaRegimeAff)` and read `R.a`, `R.b` — the regime's own stride is the ONLY
source of `a ∣ H` (`dvd_chowlaTower` at `R.a`) and of `hcoprime`, so a free `a` beside a plain
regime would elaborate at `a ≠ R.a` and mean nothing.  The `(1, 0)` compats are stated at
`ChowlaRegimeAff.ofRegime R 0 _` under `R.a = 1` (every landed builder pins `a := 1`).  The
Finset `bigXiAff` and the normalisation nodes keep free `(a, b, h)`: they are about a set and a
Prop, not a regime.

Scope: definitional/foundational only.  No claim about Chowla, about the door, or about twins
is made or moved by this file.  Import direction: `Salt.Entropy`-internal (`AffineFork`,
`ShiftFork`, `Regime`, `GoldbachEnergyKcH` for the pinned ceiling); nothing from `Salt/MR` or
`Salt/TwinBar`.  Registered in `Salt/Entropy/All.lean` so CI builds it.  Nothing here bears on
twin primes.
-/
import Salt.Entropy.Chowla.ShiftFork
import Salt.Entropy.Chowla.AffineFork
import Salt.Entropy.Chowla.Regime
import Salt.Entropy.Chowla.GoldbachEnergyKcH
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## F1-M — the stride measure -/

/-- **F1-M1 (def).**  The log-measure of the window `(x/ω, x]` pushed forward along `n ↦ a·n`:
the law of `a·n` for `n` log-random.  Tao's entropy argument at stride `a` runs on the tuple
`(λ(a·n + j))_{j ≤ H}` (Prop 2.6, textdump:719-724), which is `liouvilleWindow H m` at `m = a·n`
— so the landed windows are read under THIS measure and nothing in them changes.  At `a = 1` it
is `logMeasure x ω` (`logMeasureAff_one`).  At `a = 0` it is the Dirac mass at `0`. -/
noncomputable def logMeasureAff (a x ω : ℕ) : Measure ℕ :=
  Measure.map (fun n => a * n) (logMeasure x ω)

/-- **F1-M2 (class A).**  `(fun n => 1 * n) = id` by `funext` + `one_mul`, then
`MeasureTheory.Measure.map_id`. -/
theorem logMeasureAff_one (x ω : ℕ) : logMeasureAff 1 x ω = logMeasure x ω := by
  sorry

/-- **F1-M3 (class A).**  The change of variables: every integral against the stride measure
is the integral of the composite against `logMeasure`.  `MeasureTheory.integral_map` with
`(measurable_from_nat).aemeasurable` (ℕ carries `⊤`, so every map out of it is measurable) and
`(measurable_from_nat).aestronglyMeasurable` for the integrand (ℝ-valued, so
`Measurable.aestronglyMeasurable` applies with no side condition). -/
theorem integral_logMeasureAff (a x ω : ℕ) (f : ℕ → ℝ) :
    ∫ m, f m ∂(logMeasureAff a x ω) = ∫ n, f (a * n) ∂(logMeasure x ω) := by
  sorry

/-- **F1-M4 (class A, an `instance`).**  The stride measure is a probability measure whenever
`logMeasure` is:
`Measure.isProbabilityMeasure_map (measurable_from_nat (f := fun n => a * n)).aemeasurable`
(`MeasureTheory.Measure.isProbabilityMeasure_map`, Probability.lean:124 — NOT the bare
`isProbabilityMeasure_map`, which resolves to nothing; the corpus spells it right at
`InvarianceHead.lean:163`). -/
instance isProbabilityMeasure_logMeasureAff (a x ω : ℕ)
    [IsProbabilityMeasure (logMeasure x ω)] : IsProbabilityMeasure (logMeasureAff a x ω) := by
  sorry

/-! ## F1-N — the (2.4) ⇒ (2.6) normalisation at the affine forms -/

/-- **F1-N1 (class B).**  Stmt 1 at the affine forms: Tao (2.4) ⇒ (2.6) — the failure of the
affine atom at margin `ε` gives `ε/2 ≤ |E λ(a·n+b)λ(a·n+b+h)|` under the log-measure.  The
twin of `singleCorr_of_fails_h` (`ChowlaFailure.lean:197`), whose proof is SUMMAND-AGNOSTIC:
the integral-to-sum identity with `f := fun n => λ(a*n+b)·λ(a*n+b+h)`, then
`harmonic_window_bounds` (`LogMeasure.lean:115`) and the same `nlinarith` — copy the body and
replace the summand.  ⛔ The identity `logMeasure_integral_eq` (`ChowlaFailure.lean:40`) is
PRIVATE to its module: copy it VERBATIM as a private lemma here (its proof is `f`-generic —
`logMeasure` is a scaled finite sum of Dirac masses).  No `0 < a` needed (the identity holds
for every summand).  Kill-check: at `a = b = 0` the hypothesis is FALSE at every
window (`liouville 0 = 0`), so the statement is vacuously fine there. -/
theorem singleCorr_of_failsAff (a b h : ℕ) (eps : ℚ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ))
    (hfail : logChowlaFailsAff a b h eps x ω) :
    (eps : ℝ) / 2 ≤
      |∫ n, (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) ∂(logMeasure x ω)| := by
  sorry

/-- **F1-N2 (class A).**  The same seed read under the stride measure, in the form the entropy
half consumes (windows at `m = a·n`): `integral_logMeasureAff` at
`f := fun m => λ(m+b)·λ(m+b+h)` rewrites the right-hand side of F1-N1 (the composite is
`λ(a*n+b)·λ(a*n+b+h)` syntactically). -/
theorem singleCorr_of_failsAff' (a b h : ℕ) (eps : ℚ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ))
    (hfail : logChowlaFailsAff a b h eps x ω) :
    (eps : ℝ) / 2 ≤
      |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
        * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| := by
  sorry

/-! ## F1-X — the large-spectrum set with the `η ∈ ℤ/aℤ` union made visible -/

/-- **F1-X0 (def).**  The `η`-offset of the affine frequency, as an element of `ZMod H`:
`c_η := (b + h)·η·(H/a)`.  With `a ∣ H` this is Tao's `(b+h)η/a` on the `1/H` grid
(`(b+h)η/a = (b+h)η(H/a)/H`, textdump:1296-1300, :1360). -/
def affOffset (a b h : ℕ) (H : ℕ) [NeZero H] (η : ℕ) : ZMod H :=
  (((b + h) * η * (H / a) : ℕ) : ZMod H)

/-- **F1-X1 (def).**  Tao's `Ξ_H` at stride `a`, offset `b`, shift `h` (Lemma 3.4,
textdump:1296-1302): the `ξ ∈ ℤ/Hℤ` for which `|S_H(−((b+h)η/a + hξ/H))| ≥ ε²/log H` for SOME
`η ∈ ℤ/aℤ`.  Spelled as the union over `η ∈ range a` of the `bigXi`-membership of
`c_η + h·ξ` — the inner expression is EXACTLY `bigXi`'s predicate at the point
`affOffset a b h H η + (h : ZMod H) * ξ`, so `mem_bigXiAff_iff` is a definitional unfolding.

At `(a, b) = (1, 0)` the union has one member (`η = 0`) with `c₀ = 0`, and the set is the
landed `bigXiH h` (`bigXiAff_one_zero`).  At `a = 0` the set is `∅`.  THE TWIST LIVES HERE AND
ONLY HERE: the door below is stated at the untwisted `ξ`, as in `ShiftFork`. -/
noncomputable def bigXiAff (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] : Finset (ZMod H) := by
  classical
  exact Finset.univ.filter (fun ξ : ZMod H =>
    ∃ η ∈ Finset.range a,
      (eps : ℝ) ^ 2 / Real.log (H : ℝ)
        ≤ ‖expSum eps H
            (-(((affOffset a b h H η + (h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖)

/-- **F1-X2 (class A).**  The membership unfolding: `ξ ∈ bigXiAff` iff some offset shifts
`h·ξ` into the landed `bigXi`.  `unfold bigXiAff bigXi`, then
`simp only [Finset.mem_filter, Finset.mem_univ, true_and]` on both sides (the inner predicate
is `bigXi`'s at the shifted point by construction). -/
theorem mem_bigXiAff_iff {a b h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] {ξ : ZMod H} :
    ξ ∈ bigXiAff a b h eps H
      ↔ ∃ η ∈ Finset.range a, affOffset a b h H η + (h : ZMod H) * ξ ∈ bigXi eps H := by
  sorry

/-- **F1-X3 (class B) — the `(1, 0)` compat.**  `Finset.filter_congr`; `∃ η ∈ range 1, P η ↔
P 0` (`Finset.mem_range`, `Nat.lt_one_iff`); at `η = 0`, `affOffset 1 0 h H 0 = 0` by
`(0 + h) * 0 * (H / 1) = 0` (`mul_zero`, `zero_mul`) and `Nat.cast_zero`; then `zero_add`
turns the point into `bigXiH`'s `(h : ZMod H) * ξ`. -/
theorem bigXiAff_one_zero (h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] :
    bigXiAff 1 0 h eps H = bigXiH h eps H := by
  sorry

/-- **F1-X4 (class B) — THE `a`-SPELLING TRIPWIRE.**  No other statement in this file depends on
`H / a` being the right factor (`bigXiAff_one_zero` is provable under ANY `H/a`-shaped expression:
at `a = 1`, `η = 0` kills it).  This one does: under `a ∣ H`, `a` times the offset's value is
`(b+h)·η·H` modulo `H·a`.  `ZMod.val_natCast` (`(n : ZMod H).val = n % H`), then
`Nat.ModEq`: write `H = a * m` (`Nat.div_mul_cancel hdvd`), so `((b+h)ηm % (am)) · a ≡ (b+h)ηma
[MOD (am)a]` — `Nat.mod_add_div` and `Nat.ModEq` arithmetic, or `Nat.ModEq.mul_right` after
`Nat.mod_modEq`.  If `affOffset` had the wrong grid, this is the statement that fails. -/
theorem affOffset_spec {a b h H : ℕ} [NeZero H] (hdvd : a ∣ H) (η : ℕ) :
    (affOffset a b h H η).val * a ≡ (b + h) * η * H [MOD H * a] := by
  sorry

/-! ## F1-C — the fibre bounds (`ShiftFork` T2 at a translated target) -/

/-- **F1-C0a (class A, a copy).**  `ShiftFork.lean:151-156` `dvd_of_coprime_factor`, VERBATIM
(private there; the fibre lemma below needs it). -/
private lemma dvd_of_coprime_factor_aff {d a' b' v : ℕ} (hd : 0 < d)
    (hcop : Nat.Coprime b' a') (hdvd : d * b' ∣ d * a' * v) : b' ∣ v := by
  sorry

/-- **F1-C0b (class A, a copy).**  `ShiftFork.lean:158-178` `val_dvd_of_mul_eq_zero`, VERBATIM
(uses `dvd_of_coprime_factor_aff` in place of the private original). -/
private lemma val_dvd_of_mul_eq_zero_aff {H : ℕ} [NeZero H] (h : ℕ) {z : ZMod H}
    (hz : (h : ZMod H) * z = 0) : H / Nat.gcd h H ∣ z.val := by
  sorry

/-- **F1-C0 (class A, a copy).**  `ShiftFork.lean:179-222` `card_fiber_le`, VERBATIM with the two
helpers above (all three are `private` to `ShiftFork`; no import edit to the landed file).
Every fibre of `ξ ↦ (h : ZMod H) * ξ` has at most `gcd(h,H)` elements. -/
private lemma card_fiber_le_aff {H : ℕ} [NeZero H] (h : ℕ) (t : ZMod H) :
    (Finset.univ.filter (fun x : ZMod H => (h : ZMod H) * x = t)).card
      ≤ Nat.gcd h H := by
  sorry

/-- **F1-C1 (class B) — the fibre bound at a translated target, for ANY target set.**
`ShiftFork.bigXiH_card_le_gcd_mul`'s proof with `bigXi` replaced by an arbitrary `T` and the
map `ξ ↦ c + h·ξ`: `Finset.card_le_mul_card_image_of_maps_to (f := fun ξ => c + (h : ZMod H) * ξ)
(t := T)`; the fibre over `t` is `{ξ : c + h·ξ = t} = {ξ : h·ξ = t − c}` (`Finset.filter_congr`
with `eq_sub_iff_add_eq'`), bounded by `card_fiber_le_aff h (t - c)`. -/
theorem card_affPreimage_le {H : ℕ} [NeZero H] (h : ℕ) (c : ZMod H) (T : Finset (ZMod H)) :
    (Finset.univ.filter (fun ξ : ZMod H => c + (h : ZMod H) * ξ ∈ T)).card
      ≤ Nat.gcd h H * T.card := by
  sorry

/-- **F1-C2 (class B) — THE COUNT: `|Ξ^{(a,b,h)}_H| ≤ a · gcd(h,H) · |Ξ_H|`.**  `bigXiAff` is
the `biUnion` over `η ∈ range a` of the translated preimages (`Finset.ext` + `mem_bigXiAff_iff`
+ `Finset.mem_biUnion` + `Finset.mem_filter`), so `Finset.card_biUnion_le` gives a sum of `a`
terms each `≤ gcd(h,H) · |bigXi|` by `card_affPreimage_le`
(`Finset.sum_le_card_nsmul` / `Finset.card_range`, `smul_eq_mul`).  Uniform in `b`. -/
theorem bigXiAff_card_le (a b h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] :
    (bigXiAff a b h eps H).card ≤ a * (Nat.gcd h H * (bigXi eps H).card) := by
  sorry

/-- **F1-C3 (class A).**  `gcd(h,H) ≤ h` at `0 < h` (`Nat.gcd_le_left`), as `ShiftFork`'s
`bigXiH_card_le_mul`. -/
theorem bigXiAff_card_le_mul (a b h : ℕ) (hh : 0 < h) (eps : ℚ) (H : ℕ) [NeZero H] :
    (bigXiAff a b h eps H).card ≤ a * h * (bigXi eps H).card := by
  sorry

/-- **F1-C4 (class A) — the transfer of Tao Lemma 3.5.**  `bigXi_bounded`
(`GoldbachEnergyFinal.lean:502`, unconditional) through F1-C3 with the constant `a·h·C`, as
`ShiftFork.bigXiH_bounded` does with `h·C`.  `a`, `b`, `h` are bound INSIDE the `∃ C` (refuter
repair B2): the constant is `a`-free in the kernel, not in prose; `0 < h` for the fibre bound.
No re-proof of the restriction theorem on the `ℤ/aHℤ` grid: under `a ∣ H` every affine
frequency already lies on `ℤ/Hℤ` (S-0 census §5(ii)). -/
theorem bigXiAff_bounded (eps : ℚ) (heps : 0 < eps) (heps2 : (eps : ℝ) ^ 2 < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (a b h : ℕ), 0 < h → ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXiAff a b h eps H).card : ℝ) ≤ (a : ℝ) * (h : ℝ) * C := by
  sorry

set_option exponentiation.threshold 4000 in
/-- **F1-C5 (class B) — THE PINNED CEILING at the affine lane's own pin `ε = 1/(500·a·h)`**, the
twin of `bigXiH_bounded_ceiling_of_pin` (`GoldbachEnergyKcH.lean:224-227`), carrying the terminal
road's rider `C ≤ 2^539`.  The existential-only bound above is exactly the shape whose absence at
`h` "made `Kc ≤ 2^539` unreachable" (`GoldbachEnergyKcH.lean:215-218`) — added at F1 so F5 does
not re-walk it.  Proof: the `h`-twin's script with `h ↦ a·h` in every arithmetic line —
`h_le_1096_of_log_le_seven` at `a * h` (the cap `log(a·h) ≤ 7`), `bigXi_bounded_explicit` at the
pin, then `bigXiAff_card_le_mul` in place of `bigXiH_card_le_mul`; the witness is
`32·exp 40·2^70·500^10·(a·h)^15 ≤ 2^379.53 < 2^539` at `a·h ≤ 1096`.  Uniform in `b`. -/
theorem bigXiAff_bounded_ceiling_of_pin (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (ε : ℚ) (hε : ε = 1 / (500 * ((a * h : ℕ) : ℚ))) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 ^ 539 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXiAff a b h ε H).card : ℝ) ≤ C := by
  sorry

/-! ## F1-R — the regime with an offset (the statement act) -/

/-- **F1-R1 (structure, Fable statement act).**  The regime of Tao §2 at a general stride AND
offset: `ChowlaRegime` (`Regime.lean:56`, which already carries the stride `a` with `hHlo :
a ≤ Hlo`, `hcoprime`, `hfit`, `hJcon` at stride `a`) EXTENDED by the offset `b` and Lemma
2.5's `|r| ≤ H₋` (textdump:683-684) — the mirror of `hHlo`.  The extension idiom is the
corpus's own (`ChowlaRegimeFlat extends ChowlaRegime`, `TowerFlatRegime.lean:122`): no landed
builder is re-fired, and a plain regime becomes an affine one by supplying two fields
(`ChowlaRegimeAff.ofRegime`).  `b` reads into `bigXiAff` and `logChowlaFailsAff` only; no
tower, entropy or headroom field mentions it (S-0 census §5(iii)).  CONSUMERS IN THIS FILE
(refuter kill A4): the two doors and the two seams read `R.a`, `R.b`; the compats instantiate
`ofRegime R 0`. -/
structure ChowlaRegimeAff extends ChowlaRegime where
  /-- the arithmetic-progression offset (`a·n + b`) -/
  b : ℕ
  /-- Tao Lemma 2.5's `|r| ≤ H₋`, stated at the corpus's stronger lower endpoint -/
  hb : b ≤ Hlo

/-- **F1-R2 (class A).**  Any regime with an offset below its lower endpoint is an affine
regime: the anonymous constructor `{ R with b := b, hb := hb }`. -/
def ChowlaRegimeAff.ofRegime (R : ChowlaRegime) (b : ℕ) (hb : b ≤ R.Hlo) : ChowlaRegimeAff :=
  { R with b := b, hb := hb }

/-- **F1-R3 (class A).**  The affine regime's underlying regime is the one it was built from
(`rfl` on the structure eta). -/
theorem ChowlaRegimeAff.ofRegime_toChowlaRegime (R : ChowlaRegime) (b : ℕ) (hb : b ≤ R.Hlo) :
    (ChowlaRegimeAff.ofRegime R b hb).toChowlaRegime = R := by
  sorry

/-- **F1-R0a (class A) — the stride is a re-basing of the tower.**  `chowlaTower C0 a Hlo j =
chowlaTower C0 1 (a * Hlo) j`: the bases agree up to `one_mul` (`Regime.lean:37`, `chowlaTower C0 a
Hlo 0 = a * Hlo`) and the step is the same function of the previous value — `induction j` with
`simp [chowlaTower, ih]` (or `rw [chowlaTower, chowlaTower, ih]`).  This is what makes every
stride-`1` tower lemma (`towerJmin_spec`, `chowlaTower_base_ge`, `dropSum_exceeds_log_two_base`,
all stated at the literal stride `1` over a general base `B ≥ 4·10⁶`) available at stride `a`. -/
theorem chowlaTower_eq_base_one (C0 a Hlo j : ℕ) :
    chowlaTower C0 a Hlo j = chowlaTower C0 1 (a * Hlo) j := by
  sorry

/-- **F1-R0b (class A).**  The telescoped decrement re-bases the same way: `unfold towerDropSum`,
`Finset.sum_congr rfl`, `rw [chowlaTower_eq_base_one]`. -/
theorem towerDropSum_eq_base_one (C0 a Hlo J : ℕ) :
    towerDropSum C0 a Hlo J = towerDropSum C0 1 (a * Hlo) J := by
  sorry

/-- **F1-R4 (class B) — the flat regime at a general stride EXISTS, with the coprimality floor
paid by the flat base.**  The mirror of `chowlaRegimeFlat_exists_param_gen`
(`TowerFlatBuilder.lean:228-330`, which builds at `a := 1` and returns a `ChowlaRegimeFlat`), read
at stride `a` and returned as a plain `ChowlaRegime` with the SAME lower endpoint
`Hlo = max (flatDesignFloor A) (max Hlo₀ (4·⌈1/ε⌉₊⁴))` — spelled EXACTLY as that builder spells it
(at `A ≥ 162` the `Salt.MR` side knows `flatDesignFloor A = flatDesignBase A`,
`S16FlatTerminalLinear.lean:1211`; this file cannot import it, so the consumer rewrites).
The two stride-sensitive fields are supplied by the caller at the base they transfer from:
`hHloa : a ≤ flatDesignFloor A` gives `hHlo` by `flatDesignFloor A ≤ Hlo`; `hcopa :
(a : ℚ) ≤ ε²·flatDesignFloor A / 2` gives `hcoprime` by the same monotonicity (`ε² ≥ 0`).  The
tower: `J := towerJmin 2 1 (a * Hlo)` and `Hhi := chowlaTower 2 1 (a * Hlo) J`, so `hfit` is
`le_of_eq (chowlaTower_eq_base_one …)`, `hJcon` is `towerJmin_spec` (`TowerExport.lean:582`, base
`a * Hlo ≥ Hlo ≥ 4·10⁶` by `Nat.le_mul_of_pos_left`) through `towerDropSum_eq_base_one`, and
`hHlohi` is `chowlaTower_base_ge` at that base composed with `Hlo ≤ a * Hlo`.  Everything else —
`hHlo_floor`, `hPNTwindow` (the builder's `hPNT` from `4·m⁴ ≤ Hlo`, verbatim), and the outer scale
`(x, ω)` with `hheadroom`/`hheadroom'`/`hPHheadroom`/`hωbig`/`hxbig` from `regime_outer_param eps
heps heps1 Hhi (4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊) hHhi_floor` — is the builder's own script with `a := a`,
`ha := ha` in the record.  No flat tower fields are built (a plain regime is what the door supply
and the consumers read).  `_hA : 26 ≤ A` is UNUSED here (no flat field is built, so
`flatFloor_of_design` never fires — refuter kill A2) and is kept underscored so F5 spells the
builder's signature; the consumers instantiate at `A ≥ 162`. -/
theorem chowlaRegime_exists_flat_stride (a : ℕ) (ha : 1 ≤ a) (A : ℝ) (_hA : 26 ≤ A)
    (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ)
    (hHloa : a ≤ flatDesignFloor A)
    (hcopa : (a : ℚ) ≤ eps ^ 2 * (flatDesignFloor A : ℚ) / 2) :
    ∃ R : ChowlaRegime, R.a = a ∧ R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
  sorry

/-! ## F1-D — the `Ξ`-restricted MRT door at the affine forms, and its seam -/

/-- **F1-D1 (def).**  The `Ξ`-restricted MRT uniformity door at `(a, b, h)`:
`MRTUniformityXiH h` (`ShiftFork.lean:296`) with the binder over `bigXiAff a b h R.eps H` and
the integral against the STRIDE measure `logMeasureAff a R.x R.ω` — the window's DFT is read at
`m = a·n`, which is Tao's (2.8) (textdump:672-679, the Fourier-uniformity at the dilated
variable, obtained from (2.7) by Lemma 2.5).  The frequency `α = −ξ.val/H` is UNTWISTED and the
quantifier stays OUTSIDE the integral — both load-bearing, neither policed by the kernel
(`ShiftFork` D3's two warnings apply verbatim).

The stride and the offset are the REGIME'S (`R.a`, `R.b`; refuter kill A4): `R.a` is the only
source of `a ∣ H` and `hcoprime`, and `R.hb` is Lemma 2.5's `|r| ≤ H₋`.  At `R.a = 1`, `R.b = 0`
it is `MRTUniformityXiH h` (`mrtUniformityXiH_eq_xiAff_one_zero`).  THE PRODUCER
STORY: nothing here produces it.  Its supply is wave 2-S-F3 (freeze §1(D)): the `h`-lane's
door supply read at the modulus parameter `a·h` (the bridge `bigXiAff → NearRatTight
(a·h·arcDen 12 H)`) composed with the exact `x`-scaling of the stride measure. -/
noncomputable def MRTUniformityXiAff (h : ℕ) (R : ChowlaRegimeAff) (δ : ℝ) : Prop :=
  ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ ξ ∈ bigXiAff R.a R.b h R.eps H,
    (∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ∂(logMeasureAff R.a R.x R.ω))
      ≤ δ * (H : ℝ)

/-- **F1-D2 (def).**  The `Ξ`-SUMMED `L²` door at `(a, b, h)`: `MRTUniformityXiL2H h`
(`ShiftFork.lean:538`) with the set and the measure swapped.  This is the door the live lane
walks (the `L²` road, `DoorReceipt`); the `L¹` door above is its Jensen shadow. -/
noncomputable def MRTUniformityXiL2Aff (h : ℕ) (R : ChowlaRegimeAff) (ρ : ℝ) : Prop :=
  ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
    ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasureAff R.a R.x R.ω)
      ≤ ρ

/-- **F1-D3 (class B) — the `(1, 0)` compat for the `L¹` door, stated APPLIED** at the affine
regime `ChowlaRegimeAff.ofRegime R 0 (Nat.zero_le _)` of a regime with `R.a = 1` (every landed
builder's).  `propext`; both directions `intro hd H _ hlo hhi ξ hξ`; the affine regime's fields
are `R`'s definitionally (`ofRegime_toChowlaRegime`), so after `show`/`simp only
[ChowlaRegimeAff.ofRegime]` the set is `bigXiAff R.a 0 h R.eps H`, which `rw [hR1,
bigXiAff_one_zero]` turns into `bigXiH h R.eps H`, and the measure `logMeasureAff R.a R.x R.ω`
is `logMeasure R.x R.ω` by `rw [hR1, logMeasureAff_one]`.  It records that the fork is
CONSERVATIVE at `(1, 0)` and nothing more — the offset is invisible there, so this lemma cannot
police the door's spelling; `affOffset_spec` and the seam below are the tripwires. -/
theorem mrtUniformityXiH_eq_xiAff_one_zero (h : ℕ) (R : ChowlaRegime) (hR1 : R.a = 1) (δ : ℝ) :
    MRTUniformityXiH h R δ
      = MRTUniformityXiAff h (ChowlaRegimeAff.ofRegime R 0 (Nat.zero_le _)) δ := by
  sorry

/-- **F1-D4 (class B) — the `(1, 0)` compat for the `L²` door.**  As F1-D3 with
`MRTUniformityXiL2H` (`ShiftFork.lean:538`). -/
theorem mrtUniformityXiL2H_eq_xiL2Aff_one_zero (h : ℕ) (R : ChowlaRegime) (hR1 : R.a = 1)
    (ρ : ℝ) :
    MRTUniformityXiL2H h R ρ
      = MRTUniformityXiL2Aff h (ChowlaRegimeAff.ofRegime R 0 (Nat.zero_le _)) ρ := by
  sorry

/-- **F1-D5 (class B) — THE `L¹` SEAM AT `(a, b, h)`, THE TRIPWIRE.**  The clone of
`contradiction_of_mrtDoorXiH` (`ShiftFork.lean:338-376`) with the set and the measure swapped:
`c₀ε ≤ Σ_{ξ∈Ξ^{aff}}(1/H)∫‖…‖ ≤ Σ(1/H)(δH) = card·δ ≤ K·δ < c₀ε`.  The termwise step fires
the door at `ξ` and must land on the goal's summand; with the door at the untwisted
`−ξ.val/H` the two are the same term and the `calc` closes.  Copy the landed body verbatim
(`Finset.sum_le_sum`, the three-line `calc`, `Finset.sum_const`, `nsmul_eq_mul`, the final
`linarith`); only the names of the set, the measure and the door change.  `0 < h` not required:
`K` is supplied by the caller.  The stride and offset are `R.a`, `R.b` (kill A4). -/
theorem contradiction_of_mrtDoorXiAff (h : ℕ) (R : ChowlaRegimeAff) {δ c₀ ε K : ℝ} {H : ℕ}
    [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) (hH : 0 < H) (hδ : 0 ≤ δ)
    (hdoor : MRTUniformityXiAff h R δ)
    (hXi : ((bigXiAff R.a R.b h R.eps H).card : ℝ) ≤ K)
    (hsmall : K * δ < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXiAff R.a R.b h R.eps H,
        (1 / (H : ℝ)) * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖
          ∂(logMeasureAff R.a R.x R.ω)) :
    False := by
  sorry

/-- **F1-D6 (class A) — THE `L²` SEAM AT `(a, b, h)`.**  The clone of
`contradiction_of_mrtDoorXiL2H` (`ShiftFork.lean:572-582`): `have hd := hdoor H hlo hhi;
linarith`.  No `K`, no `|Ξ| ≤ K`: the door's grade `ρ` is already the total over the set. -/
theorem contradiction_of_mrtDoorXiL2Aff (h : ℕ) (R : ChowlaRegimeAff) {ρ c₀ ε : ℝ} {H : ℕ}
    [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hdoor : MRTUniformityXiL2Aff h R ρ)
    (hsmall : ρ < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXiAff R.a R.b h R.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ m, ‖windowExpSum H m (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasureAff R.a R.x R.ω)) :
    False := by
  sorry

/-! ## F1-S — the exact `x`-scaling of the stride measure (the supply's first half) -/

/-- **F1-S1 (class B/C) — the stride measure is `a` times the log-measure of the scaled
window restricted to the multiples of `a`, EXACTLY on the summands.**  For `n ∈ (x/ω, x]`,
`m = a·n` runs over the multiples of `a` in `(a·(x/ω), a·x]` and `1/n = a·(1/m)`; so for every
`f`, `∑_{n ∈ Ioc (x/ω) x} f (a*n) / n = a · ∑_{m ∈ (Ioc (x/ω) x).image (a * ·)} f m / m`.
This is `Finset.sum_image` (injectivity of `(a * ·)` at `0 < a`, `Nat.eq_of_mul_eq_mul_left`)
plus `Nat.cast_mul` and `field_simp` on each summand.  An exact reindexing on the UNFILTERED
window — it needs neither Lemma 2.5 nor `dilation_error` (refuter §C).  Stated on the sums so the
consumer (F3's `x`-scaling of the door) can normalise either side; the image window is
`a·⌊x/ω⌋ < m ≤ a·x`, which differs from the `x`-scaled regime's `⌊a·x/ω⌋` by at most one
multiple of `a` — F3 names that term, never absorbs it. -/
theorem sum_window_aff_eq (a x ω : ℕ) (ha : 0 < a) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc (x / ω) x, f (a * n) / (n : ℝ)
      = (a : ℝ) * ∑ m ∈ (Finset.Ioc (x / ω) x).image (fun n => a * n), f m / (m : ℝ) := by
  sorry

end Salt.Entropy.Chowla
