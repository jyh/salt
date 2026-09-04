/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.CrownChain
import Salt.HB.CrownAssembly
import Salt.HB.MOne
import Salt.HB.Lemma7Prod
import Salt.HB.Lemma7EF
import Salt.HB.DoorBridge
import Salt.SW.TBalTall
import Salt.SW.DensityCrude
import Salt.SW.SiegelClose
import Salt.SW.LandauPage
import Salt.Fulcrum.Dichotomy
import Salt.Fulcrum.CZeroNumeral

/-!
# THE CROWN, N9 — Heath-Brown 1983 Theorem 1 and the door hand-over: STATEMENTS ONLY

**STATUS: FROZEN, statements only (2026-09-04).  Every theorem here is `sorry`-bodied BY
DESIGN.  No executor fires before the helm's refuter verdict on the freeze brief.**  This file
is the wave table for N9: each docstring carries the class, the line cap, the red-first idea,
and the CONSUMER by Lean name; the freeze brief carries the kill-checks and the price.

## What N9 is

HB's Theorem 1 (p.195): for a real primitive `χ` mod `q` with a real zero `β₀`, `η := 1/((1−β₀)L)`,
`L := log q`, uniformly on `q^250 ≤ x ≤ q^500`,

    Σ_{x < n ≤ 2x} Λ(n)Λ(n+2) = 𝔖·C(4)·x·(1 + O(1/log log η)).

Its proof (p.200) is Lemma 4 (N8's `hb_lemma4_l2cWindow`) + the two-sided p.200 bracket (N8's
`hb_p200_upper/lower` fed by N7's `Lemma5Eval`) + Lemma 7 (N4's `(L1)` two-sided and `(L2)`)
+ the cancellation `κS₁·(L′/L)² = x𝔖C(α)`, at `z₀ = A·log log η`, `z = q^{1/z₀}`.

## What this freeze found at the object (the brief §A carries the receipts)

1. **The zero side is the crown's open design, not N4's "composition".**  N8's L3 and N4's
   `(L1)` both carry `hceil` over ALL zeros (undischargeable: every landed ceiling is a box) and a
   `Sinv` antecedent on a zero set `Z` whose only export is "zeros with multiplicity" — the
   consumer cannot bound `Σ m` for an opaque `Z`.  The `Z` is in fact the partial-fraction zero
   set of `ball 2 (3/2)` (`LFunction_partialFraction_remainder_diff`), and the landed bodies
   call `Z`-INPUT lemmas (`neg_re_logDeriv_differenced_mult`, `pretenseSum_le_differenced`), so
   the repair is to obtain `Z` ONCE with its ball membership, discharge the floor and `Sinv` on
   it (§3 here), and re-run the three short bodies against it.
2. **The landed Deuring–Heilbronn contract has exponent `k = 14`** (`dh_repulsion_tall`,
   `⟨680, c, 14⟩`).  The floor it yields is `(log(ηL) − log(1/c) − 14·log(log(4q)+2))/(680·log 4q)`,
   POSITIVE only when `log η > 13·log log q + log(1/c)`.  So the engine's threshold on `η` is
   **coupled to `q`**: `n9Ell q η` below must clear a constant, and `n9Ell` carries
   `dhK·log(log(4q)+2)`.  HB (Jutila's Thm 2) has `k = 1` and a pure `η`-threshold.  The crown's
   frozen `HeathBrownDichotomy = TPC ∨ NoSiegelZeros` sits at the `c/log q` scale; against the
   landed supply the engine fires only from a POLYLOG quality `1 − β₀ ≤ 1/(C·(log q)^{1+dhK})`.
   §6 states the crown FAMILY `HeathBrownDichotomyPoly k`, whose `k = 1` member is the frozen
   crown (byte-untouched), and lands the engine at `k = 1 + dhK = 15`.  Which member is the
   campaign's crown — or whether D–H is re-proved at `k ≤ 1` — is the Captain's ruling, not this
   file's.
3. **`(L2)`'s six binders are not "every piece proved".**  `hcorr`'s producer needs `hlimP`
   (never produced — the CHAR-TRIO flag), `htail`'s producer hides an existential `X₀` after `q`
   and a `hreal` binder with no producer, `hseg`'s feeder carries the same zero-side antecedents
   as `(L1)`.  §4 books each as a row.
4. **`fulcrum_zero_real_zfr`'s `hcal` is unsatisfiable as stated** (it quantifies over every
   `c₀` that satisfies the ZFR, including arbitrarily small ones); the live route is
   `fulcrum_zero_real` + `zero_free_region_all_numeral` at `c₀ = 1/126848`.  §6 uses that.
5. **`card_divisors_le_rpow`'s `∃ C` is not printable** and N9's star term needs `ε ≍ 1/z₀`
   (an `η`-dependent `ε`), so the divisor constant must be an explicit function of `ε` (§5, T0).

Honest label: N9 assembles Theorem 1 CONDITIONALLY on N7's exit (`N7Exit`, a hypothesis until
Wave C lands) and on the regime `N9Regime`, whose `ellB` field is the coupled threshold.  Nothing
here bears on twin primes; `hEngine` stays a binder until N7, the rows here, and the Captain's
crown ruling land.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction
open Salt.TwinBar
open Salt.BrunLower
open Salt.SW
open Salt.Fulcrum
open MeasureTheory Set Filter Topology

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the operating point (definitions; no obligation) -/

/-- The Deuring–Heilbronn exponent `b` of the landed contract (`dh_repulsion_tall`'s witness,
`TBalTall.lean:2194`: `⟨680, c, 14, …⟩`). -/
noncomputable def dhB : ℝ := 680

/-- The Deuring–Heilbronn log-exponent `k` of the landed contract — **THE COUPLING**: HB (Jutila's
Theorem 2) has `k = 1`; the landed proof has `k = 14`, which is why the floor below is positive
only when `log η > 13·log log q + log(1/c)`. -/
noncomputable def dhK : ℝ := 14

/-- **The landed D–H contract with its exponents PRINTED.**  `dh_repulsion_tall` exports `∃ b c k`
and hides `680`/`14` behind the existential; the crown's strength IS `1 + k`, so N9 needs them
visible.  Class **A**, cap 60 — its proof is the last four lines of `dh_repulsion_tall`'s
(`TBalTall.lean:2194-2210`), which name `680`, `14` and the eleven-arm `c` explicitly; it needs the
private `dh_repulsion_inst_tall` and that `c`, so it is PROVED IN `TBalTall.lean` (appended, no
landed proof changed) or after an un-`private` ruling — the helm's call (freeze §4 K2).
Consumer: `dhC`, `dh_spec`. -/
theorem dh_repulsion_tall_at : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im ≠ 0 →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK := by
  sorry

/-- The Deuring–Heilbronn constant `c`, chosen once (`log(1/c) ≈ 90` in the landed proof). -/
noncomputable def dhC : ℝ := Classical.choose dh_repulsion_tall_at

/-- **The D–H contract at the chosen `c`.**  Class **A**, cap 20: `Classical.choose_spec`.
Consumer: `dh_repulsion_tall_real`, `dh_floor_ball`. -/
theorem dh_spec : 0 < dhC ∧ dhC ≤ 1 ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im ≠ 0 →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ dhC * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK := by
  sorry

/-- The Prachar near-one constant of `invSq_sum_split_le`, chosen once. -/
noncomputable def invSqC : ℝ := Classical.choose invSq_sum_split_le

/-- Class **A**, cap 20.  Consumer: `sinv_ball`. -/
theorem invSqC_spec : 0 < invSqC ∧
    ∀ {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → 2 ≤ f →
      ∀ {r0 J : ℝ}, 0 < r0 → ∀ {Z : Finset ℂ} {m : ℂ → ℕ},
        (∀ ρ ∈ Z, r0 ≤ ‖ρ - 1‖) →
        (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) →
        (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) →
        (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ J →
        ∑ ρ ∈ Z, (m ρ : ℝ) / ‖ρ - 1‖ ^ 2
          ≤ invSqC * (1 / r0 ^ 2 + Real.log ((f : ℝ) + 2) / r0) + 16 * J := by
  sorry

/-- **`ℓ′` — the effective `log η`.**  The numerator of the D–H floor at base `4q`:
`log(ηL) − log(1/dhC) − 14·log(log(4q) + 2)`; with `log(1/dhC) ≈ 90` this is
`log η − 13·log log q − 90 + o(1)`: the `η`–`q` COUPLING lives here, in the one term
`dhK·log(log(4q)+2)`.  Every `log η` of HB's is `ℓ′` in this file — at HB's `k = 1` the two
agree up to `O(1)`; at the landed `k = 14` they differ by `13·log log q`. -/
noncomputable def n9Ell (q : ℕ) (η : ℝ) : ℝ :=
  Real.log (η * Real.log q) - Real.log (1 / dhC)
    - dhK * Real.log (Real.log (4 * (q : ℝ)) + 2)

/-- **The D–H floor at base `4q`**: every zero `ρ ≠ β₀` of `L(·,χ)` in `ball 2 (3/2)` has
`n9Floor q η ≤ ‖ρ − 1‖` (`dh_floor_ball`).  `= ℓ′/(dhB·log 4q)`. -/
noncomputable def n9Floor (q : ℕ) (η : ℝ) : ℝ := n9Ell q η / (dhB * Real.log (4 * (q : ℝ)))

/-- **The `Cs` of the `(L1)`/L3 packet, made a constant**: the inverse-square zero sum at the
floor is `≤ n9Cs·(2L)²/ℓ′` (`sinv_ball`).  `invSqC·(dhB² + dhB)` prices the near shell,
`3400` the far shell (`16·J` with `J = 822·log(4.5q)` from `zeroCountM_le` at `T = 3/2`). -/
noncomputable def n9Cs : ℝ := invSqC * (dhB ^ 2 + dhB) + 3400

/-- HB's `A` in `z₀ = A·log log η`.  Forced `< 1/5000` by the master's middle term
(`ℓ′^{2505A}` against `1/√ℓ′`, freeze v2 §5 item 2); `1/10000` leaves `ℓ′^{1/4}` of room. -/
noncomputable def hbZ0A : ℝ := 1 / 10000

/-- **`z₀ = A·log ℓ′`** — HB's `z₀ = A·log log η` (p.198) with `log η` replaced by the effective
`ℓ′` (`n9Ell`), so that every balance in the proof (`e^{5·z0}` against the pretense rate `1/√ℓ′`,
the FL gain `4^{−z₀/3}`) closes from a threshold on `ℓ′` ALONE.  Theorem 1's error is then
`O(1/log ℓ′)`, which is HB's `O(1/log log η)` at `k = 1` and strictly weaker at `k = 14`. -/
noncomputable def hbZ0 (q : ℕ) (η : ℝ) : ℝ := hbZ0A * Real.log (n9Ell q η)

/-- **THE `z` WITNESS (seam S3 of the census).**  `z := ⌈q^{1/z₀}⌉`, so `log z ≥ L/z₀` and
`z^{z₀} ≥ q`.  This is HB's `z`, NOT `L2cGlue.zwit` (which was built for a hypothesis the master
no longer has). -/
noncomputable def hbZ (q : ℕ) (η : ℝ) : ℕ := ⌈(q : ℝ) ^ (1 / hbZ0 q η)⌉₊

/-- **HB's sieve level ratio `s = z₀/3`**, spelled so that P±'s `hD : 3·s·log z ≤ L` is an
equality: `s := L/(3·log z)`.  Non-vacuity of P− needs `s ≥ levelE Λ₄ + 2` (`hbZ_packet`). -/
noncomputable def hbS (q : ℕ) (η : ℝ) : ℝ := Real.log q / (3 * Real.log (hbZ q η : ℝ))

/-- **THE SEAM WITH N7: `LL = L′/L(1,χ)` IS THIS TERM.**  `Lemma5Eval`'s free real `LL` is
instantiated here, and Wave C-2 (row C2-10) must produce its `Lemma5Eval` at exactly this
term (the scout's `logDeriv_LFunction_eq` route lands it as `logDeriv (LFunction χ) 1`; for a
real `χ` the imaginary part is `0`).  N4's `(L1)` bounds this term two-sidedly (§3). -/
noncomputable def hbLL [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  (logDeriv (DirichletCharacter.LFunction χ) (1 : ℂ)).re

/-- **THE SEAM WITH N7 AND N4: `κ` IS THIS TERM.**  `hbKappa` at `α = 4` with the L-value entering
as the ordered Euler product at the split point `z − 1` (N4's `(L2)` takes a FREE real split
point; K1 `hbS1_eq_W` identifies `hbS1 χ 4 (z−1)` with the sieve's `W`). -/
noncomputable def hbKappaN9 (χ : DirichletCharacter ℂ q) (x z : ℕ) : ℝ :=
  hbKappa χ 4 (x : ℝ) (hbL1 χ ((z : ℝ) - 1))

/-- **The threshold on `ℓ′`** (a CEILING, pre-authorised to move UP).  `ℓ′ ≥ e^{3·10⁶}` puts
`z₀ = 10⁻⁴·log ℓ′ ≥ 300` (the sieve level `hbS ≥ 99 ≥ levelE Λ₄ + 2`), and `η ≥ e^{ℓ′}` covers
M-ONE's `15000`, `(L2)`'s `500`, the ordering's `2/c₀ = 253696`; the `(e^{300}(802+4·n9Cs))^8`
part closes `hsmall`'s kill term and the master's middle term (`ℓ′^{1/4}` against
`e^{280}(1+n9Cs)·log ℓ′`). -/
noncomputable def n9E0 : ℝ :=
  Real.exp (3 * 10 ^ 6) + (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8

/-- **THE REGIME — N9's packet, bundled.**  Every field is either HB's hypothesis (1.11) at the
twin instance, a largeness threshold, or one of the two seams this freeze found:
* `ηmax` — `β₀` is the LARGEST real zero (the T-BAL-UNORDERED binder `hord`, supplied at the
  hand-over by `beta0_max_of_zero`);
* `ηq` — `η ≤ q^{e^{−401}}`: HB's "`η ≪ q`" (Davenport ch.14 (14)); the corpus has no
  class-number bound, so the hand-over supplies it from `siegel_theorem` — INEFFECTIVE, consistent
  with the dichotomy's declared ineffectivity;
* `ellBig` — **THE COUPLED THRESHOLD**: `ℓ′ ≥ n9E0`, where
  `ℓ′ = log(ηL) − log(1/dhC) − 14·log(log(4q)+2)` carries `13·log log q`.  From the polylog
  quality `1 − β₀ ≤ 1/(C·(log q)^{15})` it is a threshold on `C`; from `FulcrumQualityMin C`
  (`k = 1`) it is NOT reachable — freeze §5.
Derived, not carried: `1 ≤ ℓ′`, `(2·680)² ≤ ℓ′` (the `hσ'r` quadratic at `ell := ℓ′`),
`17·ℓ′ ≤ 680·log 4q` (the `16/17` strip: `ℓ′ ≤ log(ηL) ≤ 2e^{−401}L`), `1/2 < β₀`,
`3 ≤ q`, `η ≥ 15000`. -/
structure N9Regime (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β₀ η : ℝ) : Prop where
  prim : χ.IsPrimitive
  sq : χ ^ 2 = 1
  ne : χ ≠ 1
  zero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0
  β1 : β₀ < 1
  ηdef : η = 1 / ((1 - β₀) * Real.log q)
  ηmax : ∀ β : ℝ, DirichletCharacter.LFunction χ (β : ℂ) = 0 → β < 1 → β ≤ β₀
  ηq : Real.exp 401 * Real.log η ≤ Real.log q
  ellBig : n9E0 ≤ n9Ell q η

/-- **N7's exit, as the ∀-statement N9 consumes.**  Wave C-2 (row C2-10) produces `Lemma5Eval`
at the N8 wire with UNIFORM `Cerr CA CA' CC` and per-instance `C₀ A A'`; `LL` and `κ` are the two
seams above.  A HYPOTHESIS of every row from T1 on, until Wave C lands. -/
def N7Exit (Cerr CA CA' CC : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ), ∃ (C₀ : ℝ) (A A' : ℕ → ℝ),
      Lemma5Eval (hbDataN8 χ hsq hz x) 4 x (Real.log q) (hbLL χ) (hbKappaN9 χ x z)
        C₀ Cerr CA CA' CC A A'

/-- **The constant of Theorem 1** — a CEILING in the four N7 constants and `n9Cs`; the `2^40`
absorbs `L2cCmain = 2^31`, the `1/(250·A)` of the first master term, and the door's `4`. -/
noncomputable def n9K (Cerr CA CA' CC : ℝ) : ℝ :=
  2 ^ 40 * (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr) / hbZ0A

/-! ## §2 — the `z` witness (seam S3) -/

/-- **`z` brackets `q^{1/z₀}`.**  Class **A**, cap 30: `Nat.le_ceil`, `Nat.ceil_lt_add_one`.
Consumer: `hbZ_packet`. -/
theorem hbZ_bounds (q : ℕ) (η : ℝ) (hz0 : 0 < hbZ0 q η) :
    (q : ℝ) ^ (1 / hbZ0 q η) ≤ (hbZ q η : ℝ) ∧ (hbZ q η : ℝ) < (q : ℝ) ^ (1 / hbZ0 q η) + 1 := by
  sorry

/-- **THE `z` PACKET — every `z`-binder of L4, P±, `(L2)`, K1 at once.**  Class **B**, cap 300.
Red-first: `log z ≥ L/z₀ = 10⁴·L/log ℓ′`; `ηq` gives `log ℓ′ ≤ log L`, so
`log z ≥ 10⁴·L/log L` — beats `16·log 100` (hz100), `8·log(1000L)` (hz8 via `Lwin x ≤ log(3q^500)`),
`e^{400}` (hzt via `zThresh_facts`, needs `log log z ≥ 400`); `z³ ≤ x` from `3/z₀ ≤ 250`; the
level: `hbS = L/(3 log z) ∈ [z₀/3.01, z₀/3]` and `levelE Λ₄ ≤ 2/Λ₄ + 2 ≤ 66` at `λ = 1/4`,
`log log z ≥ 400`, so `hbS ≥ 68` needs `z₀ ≥ 205`, i.e. `log ℓ′ ≥ 2.05·10⁶` — inside `ellBig`.
Consumer: `hb_lemma4_at_hb_point`, `hb_S3_at_hb_point`, `hb_L2_at_hb_point`. -/
theorem hbZ_packet [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ} (hR : N9Regime q χ β₀ η)
    {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500) :
    2 ≤ hbZ q η ∧ 100 ^ 16 ≤ hbZ q η ∧ Lwin x ^ 8 ≤ (hbZ q η : ℝ)
      ∧ (hbZ q η : ℝ) ^ 3 ≤ x ∧ zThresh (1 / 4) ≤ (hbZ q η : ℝ)
      ∧ 32 ≤ (hbZ q η : ℝ) - 1 ∧ (4 : ℝ) < (hbZ q η : ℝ) - 1
      ∧ 3 * hbS q η * Real.log (hbZ q η : ℝ) ≤ Real.log q
      ∧ levelE (Lam4 (1 / 4) (hbZ q η : ℝ)) + 2 ≤ hbS q η
      ∧ (3 : ℝ) ≤ (hbZ q η : ℝ) - 1 := by
  sorry

/-! ## §3 — THE ZERO SIDE, MADE CONSUMABLE (the `(L1)`/L3 packet discharged) -/

/-- **Ordering: no non-real zero of the ball sits above `β₀`** (T-BAL-UNORDERED, for `Z`).
Class **B**, cap 120.  Red-first: `zero_free_region_all_numeral` at `Or.inr him` gives
`ρ.re ≤ 1 − c₀/log(q(|Im ρ|+2)) ≤ 1 − c₀/log(3.5q)`, and `β₀ = 1 − 1/(ηL) ≥ 1 − c₀/log(3.5q)` once
`η ≥ 2/c₀` (`ellBig`).  Consumer: `dh_floor_ball`. -/
theorem re_le_beta0_of_ne [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (hball : ρ ∈ Metric.ball (2 : ℂ) (3 / 2)) (him : ρ.im ≠ 0) :
    ρ.re ≤ β₀ := by
  sorry

/-- **D–H FOR A SECOND REAL ZERO.**  The landed contract carries `ρ.im ≠ 0` only to feed the ZFR
floor `hfloor` into the private instance `dh_repulsion_inst_tall` (`TBalTall.lean:1684`), whose
body never reads `hρim` (measured: no occurrence in lines 1705–2085).  For a real `ρ ≠ β₀`,
Landau's floor `ρ ≤ 1 − (1/5000)/log(4q)` (`landau_one_exceptional_at`, contrapositive: `β₀` is
the unique real zero in that window) is STRONGER than the ZFR floor, so the same instance fires.
Class **B**, cap 150 IF `dh_repulsion_inst_tall` is un-`private`d (one-word edit in a landed
file — the helm rules); class **C**, cap 450 if its body is re-run here.
Consumer: `dh_floor_ball`. -/
theorem dh_repulsion_tall_real :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im = 0 →
        ρ.re ≤ 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ dhC * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK := by
  sorry

/-- **THE FLOOR ON THE BALL — `hceil` and `hfloor` discharged where they are USED.**
Every zero `ρ ≠ β₀` of `L(·,χ)` in `ball 2 (3/2)` is at distance `≥ n9Floor q η` from `1`.
Class **C**, cap 400.  Red-first, four cases on `ρ`: (i) `Re ρ < 16/17`: `‖ρ−1‖ ≥ 1 − Re ρ > 1/17
≥ n9Floor` by `ℓ′ ≤ 2e^{−401}L` (`ηq`); (ii) non-real, `16/17 ≤ Re ρ < 1`: `re_le_beta0_of_ne`
gives `Re ρ ≤ β₀`,
`dh_spec` gives the contract at base `q(|Im ρ|+2) ≤ 4q`, `repulsion_ceiling_of_contract` +
`repulsionCeiling_mono` (needs `hN`, i.e. `1 ≤ ℓ′`) put `Re ρ ≤ repulsionCeiling dhB dhC dhK (4q)
(1−β₀)`, and `one_sub_ceiling_le_dist_one` is the floor; (iii) real, `ρ < β₀` (by `ηmax`): Landau's
window + `dh_repulsion_tall_real`, then as (ii); (iv) `Re ρ ≥ 1`: impossible
(`LFunction_ne_zero_of_one_le_re`).  Consumer: `hb_zero_data`. -/
theorem dh_floor_ball [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (hball : ρ ∈ Metric.ball (2 : ℂ) (3 / 2)) (hne : ρ ≠ (β₀ : ℂ)) :
    n9Floor q η ≤ ‖ρ - 1‖ := by
  sorry

/-- **`Sinv` DISCHARGED: the inverse-square zero sum at the floor is `≤ n9Cs·(2L)²/ℓ′`.**
Class **B**, cap 250.  Red-first: `invSqC_spec` at `r0 := n9Floor` on `Z.erase β₀` with
`J := 137·6·log(4.5q)` from `zeroCountM_le` at `σ = 1/2`, `T = 3/2` (`Z ⊆ boxZeros χ (1/2) 1 (3/2)`
because a zero has `Re < 1`); then `1/r0² = (dhB log 4q)²/ℓ′² ≤ dhB²·(1.07L)²/ℓ′²`,
`log(q+2)/r0 ≤ dhB·1.07·L·(L+1)/ℓ′`, and `ℓ′ ≤ log(ηL) ≤ 1.01·L` (`ηq`) fold `16J` into the
`3400`.  Consumer: `hb_zero_data`. -/
theorem sinv_ball [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {Z : Finset ℂ} {m : ℂ → ℕ}
    (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.ball (2 : ℂ) (3 / 2) ∧ DirichletCharacter.LFunction χ ρ = 0)
    (hm : ∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) :
    ∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2
      ≤ n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η) := by
  sorry

/-- **THE ZERO PACKET AT HB's POINT — the one `Z` every `(L1)`/L3/kill row re-runs against.**
`LFunction_partialFraction_remainder_diff`'s `Z m` with its ball membership KEPT, the floor
(`dh_floor_ball`) and the inverse-square sum (`sinv_ball`) discharged on it.  Class **B**,
cap 150 (three `obtain`s and two `fun`s).  Consumer: `hb_L1_lower_at_hb_point`,
`hb_L1_upper_at_hb_point`, `pretenseSum_at_hb_point`, `chiOne_kill_at_hb_point`. -/
theorem hb_zero_data [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z, ρ ∈ Metric.ball (2 : ℂ) (3 / 2) ∧ DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ z ∈ Metric.ball (2 : ℂ) (3 / 2), DirichletCharacter.LFunction χ z = 0 →
        z ∈ Z ∧ 1 ≤ m z) ∧
      (∀ ρ ∈ Z, m ρ = Salt.SW.zeroMult χ ρ) ∧
      (∀ σ σ' : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ σ' → σ' ≤ 2 →
        ‖(logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)
            - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
          - (logDeriv (DirichletCharacter.LFunction χ) (σ' : ℂ)
            - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))‖
          ≤ 1600 * Real.log (80 * Real.sqrt q * (1 + Real.log q)) * |σ - σ'|) ∧
      (∀ ρ ∈ Z.erase ((β₀ : ℂ)), n9Floor q η ≤ ‖ρ - 1‖) ∧
      (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2
        ≤ n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η)) := by
  sorry

/-- **`(L1)`, LOWER SIDE, DISCHARGED: `L′/L(1,χ) ≥ ηL − (1606 + 8·n9Cs)·L/√ℓ′`.**
Class **B**, cap 200.  Red-first: `hb_zero_data`; `zeroMult_eq_one_of_eta` (M-ONE, `η ≥ 15000`)
pins `m β₀ = 1`; `neg_re_logDeriv_differenced_mult` at `σ = 1`, `σ′ = 1 + √ℓ′/(2L)` with
`hs'top := neg_re_logDeriv_LFunction_le`; `l1_error_collapse` at `Lp := 2L`, `ell := ℓ′`,
`Cs := n9Cs`, `CR := 1600·log(80√q(1+log q)) ≤ 800·(2L)` (`ηq` gives `L ≥ 20`); then
`ηL = 1/(1−β₀)`.  This is `neg_re_logDeriv_one_le_mult`'s body (`Lemma7L.lean:190-230`) with its
two antecedents paid.  Consumer: `hb_S3_at_hb_point`. -/
theorem hb_L1_lower_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    η * Real.log q - (1606 + 8 * n9Cs) * (Real.log q / Real.sqrt (n9Ell q η)) ≤ hbLL χ := by
  sorry

/-- **The `s′`-side input, LOWER form** — the mirror of `neg_re_logDeriv_LFunction_le`:
`−Re L′/L(σ,χ) ≥ −(1/(σ−1) + 1)` on `1 < σ ≤ 2`, from `|χ_ℝ| ≤ 1`, `Λ ≥ 0` and
`Salt.SW.neg_logDeriv_zeta_le`.  Class **A**, cap 60 (the same `tsum` with `neg_abs_le`).
Consumer: `neg_re_logDeriv_differenced_mult_ge`. -/
theorem neg_re_logDeriv_LFunction_ge {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(1 / (σ - 1) + 1) ≤ (-logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  sorry

/-- **The differencing, LOWER form** — the mirror of `neg_re_logDeriv_differenced_mult`
(`TwistedMertens.lean:486`): the same partial-fraction difference with every inequality reversed;
the zero-difference sum is bounded in ABSOLUTE value by `4(σ′−σ)·Sinv` there already, and the
remainder is a norm.  Class **B**, cap 250.  Consumer: `hb_L1_upper_at_hb_point`. -/
theorem neg_re_logDeriv_differenced_mult_ge {Lf : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}
    {σ σ' β₀ r0 Sinv Rrem : ℝ}
    (hσ1 : 1 ≤ σ) (hlt : σ ≤ σ') (hβ1 : β₀ < 1)
    (hβZ : (β₀ : ℂ) ∈ Z)
    (hr0 : 0 < r0) (hσr : σ - 1 ≤ r0 / 2) (hσ'r : σ' - 1 ≤ r0 / 2)
    (hfloor : ∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖)
    (hSinv : ∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv)
    (hrem : ‖(logDeriv Lf (σ : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
            - (logDeriv Lf (σ' : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))‖ ≤ Rrem)
    (hs'bot : -(1 / (σ' - 1) + 1) ≤ (-logDeriv Lf (σ' : ℂ)).re) :
    -((m (β₀ : ℂ) : ℝ) / (σ - β₀)) - (1 / (σ' - 1) + 1)
        + (m (β₀ : ℂ) : ℝ) / (σ' - β₀) - 4 * (σ' - σ) * Sinv - Rrem
      ≤ (-logDeriv Lf (σ : ℂ)).re := by
  sorry

/-- **`(L1)`, UPPER SIDE: `L′/L(1,χ) ≤ ηL + (1606 + 8·n9Cs)·L/√ℓ′`** — ABSENT in the corpus
(`hb_L1_one_sided` is the lower side only), REQUIRED by N9 twice: for `B = L + |LL|` in the
`n8C6·B·L` error of BOTH p.200 rows, and for Theorem 1's upper half.  Class **B**, cap 200: the
mirror of `hb_L1_lower_at_hb_point` on `neg_re_logDeriv_differenced_mult_ge`.
Consumer: `hb_S3_at_hb_point`. -/
theorem hb_L1_upper_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    hbLL χ ≤ η * Real.log q + (1606 + 8 * n9Cs) * (Real.log q / Real.sqrt (n9Ell q η)) := by
  sorry

/-- **L3 DISCHARGED: the pretense sum at `N = 2x + 2` on the window.**  Class **B**, cap 150.
Red-first: `hb_zero_data`; `pretenseSum_le_differenced` at `σ = 1 + 1/(2L)`, `σ′ = 1 + √ℓ′/(2L)`;
`hbCoreRate_at_hb_optimum_absorbed` at `Lp := 2L`, `ell := ℓ′`; `N^{1/(2L)} ≤ (3q^{500})^{1/(2L)}
≤ e^{251}`.  This is `pretenseSum_at_repulsion_floor`'s body with `Z` visible.
Consumer: `hb_lemma4_at_hb_point` (into `lemma4Err`'s `PretenseSum χ (2x+2)`). -/
theorem pretenseSum_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500) :
    PretenseSum χ (2 * x + 2)
      ≤ Real.exp 251 * ((1 - β₀) * (2 * Real.log q) ^ 2
          + (2 + (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η)))) / 2 := by
  sorry

/-- **The `χ(p)=1` kill on `[z, X]`, DISCHARGED** — `hb_chiOne_kill_at_window`'s conclusion with
its two zero-side antecedents paid on `hb_zero_data`'s `Z`.  Class **B**, cap 150.
Consumer: `hb_L2_at_hb_point` (as `hb_hseg_closed`'s `hkill`). -/
theorem chiOne_kill_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {z X : ℝ} (hz : 3 ≤ z) (hX : 0 ≤ X)
    (hwin : Real.log X ≤ 500 * Real.log q) :
    2 * ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
          (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1),
        wLog n * ArithmeticFunction.vonMangoldt n
      ≤ Real.exp 250 * ((1 - β₀) * (2 * Real.log q) ^ 2
          + (2 + (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η)))) / Real.log z := by
  sorry

/-! ## §4 — N4's COMPOSITION: `(L2)` at HB's operating point -/

/-- **Real zeros other than `β₀` lie below every EF ceiling** — the `hreal` binder of
`logChiSum_tendsto_zfr_hundred`, which has NO producer in the corpus.  Class **B**, cap 120.
Red-first: for real `ρ ≠ β₀`, `ηmax` gives `ρ < β₀`; `landau_one_exceptional_at` (contrapositive,
`β₀ ≥ 1 − (1/5000)/log 4q` from `ellBig`) gives `ρ ≤ 1 − (1/5000)/log(4q)`, and
`1/5000 ≥ c₀·log(4q)/log(q(efT0 q t + 3))` at `c₀ = 1/126848`.
Consumer: `logChiSum_tail_at_window`. -/
theorem real_zeros_below_zfrCeil [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    ∀ t : ℝ, ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im = 0 → ρ ≠ (β₀ : ℂ) →
      9 / 10 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ efT0 q t + 1 →
      ρ.re ≤ efZfrCeil q (1 / 126848) t := by
  sorry

/-- **`htail` at the window, with the threshold PRINTED.**  `logChiSum_tendsto_zfr_hundred`
hides `∃ X₀` AFTER `q` (the consumer cannot place `x ∈ [q^250, q^500]` above an unknown `X₀`);
its proof's threshold is `X ≥ exp((m + 255)²)` at `m = 1` plus an `X₁` the refuter must read.
⚠ If `X₁` is not a literal, this row's `hX` moves and the row is class C.  Class **B/C**, cap 250.
Consumer: `hb_L2_at_hb_point`, `hcorr_at_split`. -/
theorem logChiSum_tail_at_window [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {X : ℝ} (hX : Real.exp 70000 ≤ X) :
    ∃ S : ℂ, Tendsto (fun Y : ℝ => logChiSum χ X Y) atTop (𝓝 S) ∧
      ‖S + (Salt.SW.zeroMult χ (β₀ : ℂ) : ℂ)
          * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖
        ≤ 100 / Real.sqrt (Real.log X) := by
  sorry

/-- **`hlimP` — the ordered Euler log-product converges** (the CHAR-TRIO flag's step 1, never
produced; `hb_hcorr_closed` carries it).  Class **C**, cap 300.  Red-first: `hbEulerLog χ z Y` is
a partial sum of `Σ_{p ≥ z} −log(1 − χ(p)/p)`, absolutely convergent by comparison with
`Σ 1/p²` PLUS the conditionally convergent `Σ χ(p)/p` — the latter from the tail limit of
`logChiSum` (`logChiSum_tail_at_window`) and `logChiSum`'s definition.
Consumer: `hcorr_at_split`. -/
theorem hbEulerLog_tendsto [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {z : ℝ} (hz : Real.exp 70000 ≤ z) :
    ∃ A : ℝ, Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A) := by
  sorry

/-- **`hcorr` at the split point** — the bridge `hb_hcorr_closed` lacks: its `A′` is the limit of
`(logChiSum χ z Y).re`, while `(L2)` wants `(logChiSum χ z X).re + Stail.re`; `logChiSum_add`
(`Lemma7EF.lean:1160`) splits `[z, Y] = [z, X] ∪ [X, Y]` and the tail limit is `S`.
Class **B**, cap 200.  Consumer: `hb_L2_at_hb_point`. -/
theorem hcorr_at_split [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {z X : ℝ} (hz : Real.exp 70000 ≤ z) (hzX : z ≤ X)
    {S : ℂ} (hS : Tendsto (fun Y : ℝ => logChiSum χ X Y) atTop (𝓝 S)) :
    |Real.log (hbF χ z) - ((logChiSum χ z X).re + S.re)|
      ≤ 2 / (⌊z⌋₊ : ℝ) + 10 / Real.sqrt (⌊z⌋₊ : ℝ) := by
  sorry

/-- **The `(L2)` constant** (a ceiling): the `e^{250}` of the kill times the packet's `Cs`. -/
noncomputable def n9K2 : ℝ := Real.exp 260 * (802 + 4 * n9Cs)

/-- **`(L2)` AT HB's OPERATING POINT — N4's composition wave, as one row.**
`hb_L2_at_split_point_charTrio` at `X := x`, `z := hbZ − 1`, `L := log q`, with its six binders
paid: `hm1` ← `zeroMult_eq_one_of_eta` (`η ≥ 15000`, `L = log q`); `htail` ←
`logChiSum_tail_at_window` at `X = x ≥ q^250 ≥ e^{70000}`; `hseg` ← `hb_hseg_closed` with
`hb_coprime_segment` and `chiOne_kill_at_hb_point`; `hcorr` ← `hcorr_at_split`; `hP` ←
`hb_mertens_third_real`; `hsmall` ← the ledger: `4·Etail ≤ 400/√(250L)`, `4·Ekill ≤
4e^{250}(802+4n9Cs)·2L/(√ℓ′·log z)` with `log z ≥ 10⁴L/log log η`, the `e^{300}`-part of
`n9E0` closes it.  Class **C**, cap 500 (the ledger is the risk).  The `δ`-bound's shape:
`log ℓ′/√ℓ′` from the kill (`L/log z ≤ z₀ = A·log ℓ′`), `1/√L` from `Etail`.
Consumer: `hb_S3_at_hb_point`. -/
theorem hb_L2_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500) :
    ∃ δ : ℝ,
      hbKappaN9 χ x (hbZ q η) * hbS1 χ 4 ((hbZ q η : ℝ) - 1)
        = (1 + δ) * ((x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4
            / (η * Real.log q) ^ 2)
      ∧ |δ| ≤ n9K2 * (Real.log (n9Ell q η) / Real.sqrt (n9Ell q η)
            + 1 / Real.sqrt (Real.log q)) := by
  sorry

/-! ## §5 — THE ASSEMBLY: Lemma 4 + the p.200 bracket + the cancellation = Theorem 1 -/

/-- **The divisor bound with its constant PRINTED.**  `card_divisors_le_rpow` gives `∃ C` after
`ε`; N9's star term needs `ε := 1/(1000·z₀)` — an `η`-dependent `ε` — so `C` must be a FUNCTION of
`ε` the threshold can see: `τ(n) ≤ (3/ε)^{2^{1/ε}}·n^ε` (primes `p ≥ 2^{1/ε}` contribute `≤ 1`,
each smaller prime `≤ 3/ε`).  Class **B**, cap 200 if `TauSpike.lean:92`'s proof already carries
the literal; **C**, cap 350 if not.  Consumer: `hb_lemma4_at_hb_point`. -/
theorem card_divisors_le_rpow_explicit {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ (3 / ε) ^ ((2 : ℝ) ^ (1 / ε)) * (n : ℝ) ^ ε := by
  sorry

/-- **HB LEMMA 4 AT THE POINT: `|S⁽⁰⁾ − S⁽³⁾| ≤ 2^40·x/z₀`.**  Class **B**, cap 300.
Red-first: `hb_lemma4_l2cWindow` on `hbZ_packet` with `ε := 1/(2000·z₀)`, `C := (3/ε)^{2^{1/ε}}`
(`card_divisors_le_rpow_explicit`); then `lemma4Err` term by term: swap `2(ω(q)+z)·Lwin² ≤ x/z₀`
(`z ≤ q^{1/z₀}+1`, `ω(q) ≤ L`); master-1 `2^31·x/(z0 z x)` with `z0 z x = Lwin x/log z ≥ 250·z₀`;
master-2 `2^31·(x/log x)·e^{5·z0}·PretenseSum ≤ x/z₀` — `pretenseSum_at_hb_point`, `z0 z x ≤
501·z₀`, `e^{2505·z₀} = ℓ′^{2505·A} = ℓ′^{1/4}` against `1/√ℓ′`: THE `A < 1/5000` INEQUALITY,
closed by `n9E0`'s eighth power; master-3 `e^{2·z0}·(x/z^{1/8} + x^{9/10})·Lwin³ ≤ x/z₀`
(`z^{1/8} = q^{1/(8z₀)}` beats `ℓ′^{1/10}·L³·z₀`); star `2(C(2x+2)^ε log(2x+2))²·(2x/z + √(2x+2))`
— `x^{2ε} ≤ q^{1/(2z₀)} = √(q^{1/z₀})` at `ε = 1/(2000z₀)`, `C² = e^{2·2^{2000z₀}·log(6000 z₀)}`
with `2^{2000 z₀} = ℓ′^{0.139}` beaten by `q^{1/(2z₀)} = e^{5000·L/log ℓ′}` via `ηq`.
Consumer: `hb_theorem1`. -/
theorem hb_lemma4_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500) :
    |S1 (Finset.Ioc x (2 * x)) - S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)|
      ≤ 2 ^ 40 * (x : ℝ) / hbZ0 q η := by
  sorry

/-- **The p.200 constant** (a ceiling in the N7 constants). -/
noncomputable def n9K3 (Cerr CA CA' CC : ℝ) : ℝ :=
  Real.exp 300 * (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr)

/-- **THE p.200 CLOSING MOVE, BOTH SIGNS: `S⁽³⁾ = x𝔖C(4)·(1 + δ₃)`.**  Class **C**, cap 500.
Red-first: `hb_p200_upper/lower` at `hbZ_packet`'s binders, `lam := 1/4`, `sRatio := hbS`,
`kappa := hbKappaN9`, `LL := hbLL`; `hbS1_eq_W` turns `κ·W` into `(L2)`'s left side
(`hb_L2_at_hb_point`); the two `(L1)` sides bound `LL² = (ηL)²(1 + O(1/√ℓ′))` and
`B = L + |LL| ≤ 3ηL`; `n8ErrSum_le` prices the sieve error `Cerr·x·L⁴/z·e^{4m}(log z)⁴ ≤ x/z₀`;
`flConst(1/4)(Λ₄) ≤ 14` at `log log z ≥ 400`; the FL term is `e^{−(log 4)·hbS}`; the
`n8C6·B·L` term is `≤ 3n8C6/η` relative.  Every relative error is one of the four shapes in the
bound.  Consumer: `hb_theorem1`. -/
theorem hb_S3_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500)
    {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    ∃ δ₃ : ℝ,
      S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)
        = (1 + δ₃) * ((x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4)
      ∧ |δ₃| ≤ n9K3 Cerr CA CA' CC
          * (Real.log (n9Ell q η) / Real.sqrt (n9Ell q η) + 1 / Real.sqrt (Real.log q)
              + 1 / η + Real.exp (-(Real.log 4) * hbS q η)) := by
  sorry

/-- **HB THEOREM 1 (p.195) AT THE TWIN INSTANCE — N9's terminal.**

    S1 (Ioc x (2x)) = 𝔖·C(4)·x·(1 + δ),   |δ| ≤ n9K/log log η,   uniformly on q^250 ≤ x ≤ q^500,

CONDITIONALLY on N7's exit and on the regime (whose `ellB` couples `η` to `log log q` through the
landed D–H's `dhK`).  Class **B**, cap 250.  Red-first: `hb_lemma4_at_hb_point` +
`hb_S3_at_hb_point`; `2^40·x/z₀ = 2^40·x/(A·log ℓ′)`; the four `δ₃` shapes are each
`≤ 1/log ℓ′` in the regime (`√ℓ′ ≥ (log ℓ′)²` from `ellBig`; `√L ≥ log ℓ′` from `ηq`;
`η ≥ e^{ℓ′} ≥ log ℓ′`; `hbS ≥ z₀/3.01` so `4^{−hbS} ≤ ℓ′^{−A/2.2} ≤ 1/log ℓ′`).
Consumer: `hb_theorem1_lower` → `crown_handover` → `twinPrimeConjecture_of_frequently_S1`. -/
theorem hb_theorem1 [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500)
    {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    ∃ δ : ℝ,
      S1 (Finset.Ioc x (2 * x))
        = (1 + δ) * ((x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4)
      ∧ |δ| ≤ n9K Cerr CA CA' CC / Real.log (n9Ell q η) := by
  sorry

/-! ## §6 — THE DOOR AND THE CROWN FAMILY (N10 reduced, N11 closed, N12 parametrised) -/

/-- **The lower half of Theorem 1, as the door reads it.**  Class **A**, cap 60.
Consumer: `crown_handover`. -/
theorem hb_theorem1_lower [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500)
    {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC)
    (hK : 2 * n9K Cerr CA CA' CC ≤ Real.log (n9Ell q η)) :
    (x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4 / 2
      ≤ S1 (Finset.Ioc x (2 * x)) := by
  sorry

/-- **The fulcrum quality at POLYLOG strength `k`**: infinitely many real primitive `χ` with a
zero `ρ` inside `‖1 − ρ‖ ≤ 1/(C·(log q)^k)`.  At `k = 1` this is `FulcrumQualityMin C`
(`fulcrumQualityPoly_one_iff`).  The landed engine fires at `k = 1 + dhK = 15` (finding 2). -/
def FulcrumQualityPoly (C k : ℝ) : Prop :=
  ∀ Q : ℕ, ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    Q < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 : ℂ) - ρ‖ * (C * Real.log q ^ k) ≤ 1

/-- **No Siegel zeros at polylog strength `k`**: `β ≤ 1 − c/(log q)^k`.  At `k = 1` this is
`NoSiegelZeros` (`noSiegelZerosPoly_one_iff`); for `k > 1` it is WEAKER (still open, still
effective in form). -/
def NoSiegelZerosPoly (k : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    1 < q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ β : ℝ, DirichletCharacter.LFunction χ β = 0 → β < 1 →
      β ≤ 1 - c / Real.log q ^ k

/-- **THE CROWN FAMILY.**  `k = 1` is the frozen `HeathBrownDichotomy` (byte-untouched, in
`Salt/TwinBar/SiegelTwin.lean`); the landed supply reaches `k = 1 + dhK = 15`.  Which member is the
campaign's crown is the Captain's ruling (freeze brief §5). -/
def HeathBrownDichotomyPoly (k : ℝ) : Prop :=
  TwinPrimeConjecture ∨ NoSiegelZerosPoly k

/-- Class **A**, cap 30: `Real.rpow_one`. -/
theorem fulcrumQualityPoly_one_iff (C : ℝ) : FulcrumQualityPoly C 1 ↔ FulcrumQualityMin C := by
  sorry

/-- Class **A**, cap 30: `Real.rpow_one`. -/
theorem noSiegelZerosPoly_one_iff : NoSiegelZerosPoly 1 ↔ NoSiegelZeros := by
  sorry

/-- **The `¬F` horn at strength `k`** — the mirror of `not_fulcrum_implies_noSiegelZeros`.
Class **B**, cap 300.  Red-first: `¬F` gives `Q` with every `q > Q` at quality worse than
`1/(C(log q)^k)`, i.e. `1 − β > 1/(C(log q)^k)`; for `q ≤ Q` finitely many characters, each with
finitely many real zeros below `1` (`boxZeros χ (1/2) 1 0` is a `Finset`, `L(1,χ) ≠ 0`), take the
minimum gap — the compactness gadget's own argument (`Salt/Fulcrum/Gadget.lean`) at `(log q)^k`
in place of `log q`.  Consumer: `fulcrum_dichotomy_poly`. -/
theorem not_fulcrumPoly_implies_noSiegelZerosPoly {C k : ℝ} (hC : 0 < C) (hk : 1 ≤ k)
    (hnF : ¬ FulcrumQualityPoly C k) : NoSiegelZerosPoly k := by
  sorry

/-- **THE DICHOTOMY AT STRENGTH `k`.**  Class **A**, cap 30 (`by_cases`, as `fulcrum_dichotomy`).
Consumer: `heathBrownDichotomyPoly_of_N7`. -/
theorem fulcrum_dichotomy_poly {C k : ℝ} (hC : 0 < C) (hk : 1 ≤ k)
    (hEngine : FulcrumQualityPoly C k → TwinPrimeConjecture) :
    HeathBrownDichotomyPoly k := by
  sorry

/-- **The largest real zero exists** (the `ηmax` field, supplied at the hand-over).  Given a real
zero `β` of `L(·,χ)` with `1/2 ≤ β < 1`, there is a real zero `β₀ ≥ β`, `β₀ < 1`, above every
other real zero below `1`.  Class **B**, cap 150.  Red-first: `boxZeros χ β 1 0` is a `Finset` of
the real zeros in `[β, 1]`; `L(1,χ) ≠ 0` (`LFunction_apply_one_pos`) excludes `1`; take
`Finset.max'`.  Consumer: `crown_handover`. -/
theorem beta0_max_of_zero [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hsq : χ ^ 2 = 1) (hne : χ ≠ 1) {β : ℝ}
    (hβ : DirichletCharacter.LFunction χ (β : ℂ) = 0) (hlo : 1 / 2 ≤ β) (hhi : β < 1) :
    ∃ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 ∧ β ≤ β₀ ∧ β₀ < 1 ∧
      ∀ β' : ℝ, DirichletCharacter.LFunction χ (β' : ℂ) = 0 → β' < 1 → β' ≤ β₀ := by
  sorry

/-- **The crown's quality constant — HB's `C⁽¹⁾ = exp exp{2A/(𝔖C(α))}` (p.223), in this file's
currency**: `1 − β₀ ≤ 1/(n9Cq·(log q)^{15})` puts `ℓ′ ≥ n9E0 + e^{2·n9K}` (so `hK` holds) —
`ℓ′ ≥ log C + log L − log(1/dhC) − 14·log 2` from the quality at `q ≥ e^4`. -/
noncomputable def n9Cq (Cerr CA CA' CC : ℝ) : ℝ :=
  Real.exp (n9E0 + Real.exp (2 * n9K Cerr CA CA' CC) + 10) / dhC

/-- **THE HAND-OVER: from the polylog fulcrum to the door's hypothesis.**  Class **C**, cap 400.
Red-first: for `N`, take the witness at `Q := N + e^{e^{70000}}`; reality by `fulcrum_zero_real`
with `zero_free_region_all_numeral` (`c₀ = 1/126848`, `C·c₀ ≥ 2` from `n9Cq`); the largest real
zero by `beta0_max_of_zero` (its quality is at least the witness's); `ηq` from `siegel_theorem`
at `ε := e^{−402}` — INEFFECTIVE, absorbed into the `∃ x` (the threshold `Q` may depend on Siegel's
`C(ε)`; nothing here is claimed effective); the remaining regime fields from the quality;
`x := q^250`; `hb_theorem1_lower` with `hK` from the quality; then `x𝔖C(4)/2 > 4√(2x+2)·log³(2x+2)`
at `x ≥ q^250`.  Consumer: `hEngine_poly_of_N7`. -/
theorem crown_handover {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC)
    (hF : FulcrumQualityPoly (n9Cq Cerr CA CA' CC) (1 + dhK)) :
    ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧
      4 * Real.sqrt (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) ^ 3
        < S1 (Finset.Ioc x (2 * x)) := by
  sorry

/-- **THE ENGINE AT STRENGTH `1 + dhK = 15`, CONDITIONAL ON N7.**  Class **A**, cap 40:
`twinPrimeConjecture_of_frequently_S1 (crown_handover hN7 hF)`.  Consumer:
`heathBrownDichotomyPoly_of_N7`. -/
theorem hEngine_poly_of_N7 {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    FulcrumQualityPoly (n9Cq Cerr CA CA' CC) (1 + dhK) → TwinPrimeConjecture := by
  sorry

/-- **THE CROWN, AT THE STRENGTH THE LANDED SUPPLY REACHES, CONDITIONAL ON N7.**
`TPC ∨ NoSiegelZerosPoly 15`.  The frozen crown is the `k = 1` member; reaching it needs
either a D–H contract at `k ≤ 1` (HB's Jutila form) or the Captain's re-anchoring.  Class **A**,
cap 20.  Consumer: none yet — the crown row. -/
theorem heathBrownDichotomyPoly_of_N7 {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    HeathBrownDichotomyPoly (1 + dhK) := by
  sorry

end Salt.HB
