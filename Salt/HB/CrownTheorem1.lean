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

**STATUS: FROZEN v2, statements only (2026-09-04; v1 `f13d09a3`, this v2 on the helm's 12:38
refuter verdict — REPAIR-THEN-FIRE, 4/4 — with every kill repaired at the object, and on the
Captain's 12:39 ruling on the crown's statement).  Every theorem here is `sorry`-bodied BY
DESIGN until the wave lands.**  This file is the wave table for N9: each docstring carries the
class, the line cap, the red-first idea, and the CONSUMER by Lean name; the freeze brief carries
the kill→repair ledger, the kill-checks and the price.

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
   `dhK·log(log(4q)+2)`; the refuters sharpened it (K0(b)): the elided term of `HSigmaComp`'s
   `hlarge` is QUADRATIC in `log log q` and dominant, and the coupling's source is the EXPONENT
   `k`, not the base — no re-basing removes it, only `k ≤ 1` does (K0(e)).  HB (Jutila's Thm 2)
   has `k = 1`.  Against the landed supply the engine fires from a POLYLOG quality
   `1 − β₀ ≤ 1/(C·(log q)^{dhK})` — at `k = dhK = 14`, not `1 + dhK` (the refuters' U1: the
   identity `ηL = 1/(1−β₀)` already supplies one power of `L`, so `n9Cq` closes `ellBig` and `hK`
   at `k = 14`).  §6 states the crown FAMILY `HeathBrownDichotomyPoly k`, whose `k = 1` member is
   the frozen crown (byte-untouched, `heathBrownDichotomyPoly_one_iff`), and lands the engine at
   `k = 14`.  **The Captain ruled (2026-09-04 12:39): the crown is HEATH-BROWN's EXACTLY, `k = 1`
   (Arm B — re-prove D–H at `k ≤ 1`, the crown's next design block); `HeathBrownDichotomyPoly 14`
   lands here as the INTERMEDIATE member.**
3. **`(L2)`'s six binders are not "every piece proved".**  `hcorr`'s producer needs `hlimP`
   (never produced — the CHAR-TRIO flag), `htail`'s only producer is the RANGE-B tail
   `logChiSum_tendsto_zfr_hundred`, whose threshold `X₀` is `q`-dependent and superpolynomial in
   `q` (the verdict's one FATAL: `log X₀ ≥ (log q + 7)²`, so NO `x ∈ [q^250, q^500]` clears it,
   ever — the Range-B ceiling decays only above `exp(20·L·log L/c₀)`), and a `hreal` binder with
   no producer; `hseg`'s feeder carries the same zero-side antecedents as `(L1)`.  §4 books each
   as a row; the tail is built here at the REPULSION ceiling (Range A, `C2`), where the decay is
   real from `q^250` on.
4. **`fulcrum_zero_real_zfr`'s `hcal` is unsatisfiable as stated** (it quantifies over every
   `c₀` that satisfies the ZFR, including arbitrarily small ones); the live route is
   `fulcrum_zero_real` + `zero_free_region_all_numeral` at `c₀ = 1/126848`.  §6 uses that.
5. **`card_divisors_le_rpow`'s `∃ C` is not printable** and N9's star term needs `ε ≍ 1/z₀`
   (an `η`-dependent `ε`), so the divisor constant must be an explicit function of `ε` (§5, T0).

Honest label: N9 assembles Theorem 1 CONDITIONALLY on N7's exit (`N7Exit`, a hypothesis until
Wave C lands) and on the regime `N9Regime`, whose `ellBig` field is the coupled threshold.  Four
constants are existential (`dhC`, `invSqC`, `merC`, `segC` — each a `Classical.choose` of a landed
`∃ C` with its spec re-exported; no prose numeral about any of them is a theorem) and one
threshold is ineffective (Siegel's `C(ε)` for `ηq`).  The crown reached is
`HeathBrownDichotomyPoly 14`, conditional on N7; the frozen `HeathBrownDichotomy` (`k = 1`) is
NOT reached here — it is Arm B's, the next design block.  Nothing here bears on twin primes;
`hEngine` stays a binder until N7, the rows here, and Arm B land.
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

/-- **The landed D–H contract with its exponents PRINTED and BOTH ARMS AT ONE `c`.**
`dh_repulsion_tall` exports `∃ b c k` and hides `680`/`14` behind the existential; N9 needs them
visible, and (the verdict's A2) the real-zero arm and the `Im ρ ≠ 0` arm must be delivered at the
SAME `c`, or `Classical.choose` forgets the witness and the real arm is unprovable.  The two arms:
(1) `Im ρ ≠ 0` — the landed contract verbatim; (2) ANY zero carrying the ZFR-shaped floor
`Re ρ ≤ 1 − (1/126848)/log(q(|Im ρ|+2))` — the form the instance actually consumes, which a REAL
zero `ρ ≠ β₀` reaches through Landau (`dh_repulsion_tall_real`).  Class **A**, cap 60:
`obtain ⟨c, …⟩ := Salt.SW.dh_repulsion_tall_of_floor (c₀ := 1/126848) (by norm_num) (by norm_num)`
(the theorem appended to `TBalTall.lean` under the helm's ruling, class B there), arm (2) is it
verbatim with `dhB`/`dhK` unfolded, arm (1) is it with the floor from
`zero_free_region_all_numeral … (Or.inr hρim)`.  Consumer: `dhC`, `dh_spec`. -/
theorem dh_repulsion_tall_at : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im ≠ 0 →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - (1 / 126848) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ c * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK) := by
  obtain ⟨c, hcpos, hc1, hc⟩ :=
    Salt.SW.dh_repulsion_tall_of_floor (c₀ := 1 / 126848) (by norm_num) (by norm_num)
  refine ⟨c, hcpos, hc1, ?_, ?_⟩
  · intro q _ χ hprim hne hsq hq β₀ hβ0 hβlo hβhi ρ hρ hρim hlo hhi hord
    have hfloor : ρ.re ≤ 1 - 1 / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
      Salt.Fulcrum.zero_free_region_all_numeral q χ hprim hne hρ (by linarith) (Or.inr hρim)
    simpa [dhB, dhK] using hc q χ hprim hne hsq hq β₀ hβ0 hβlo hβhi ρ hρ hfloor hlo hhi hord
  · intro q _ χ hprim hne hsq hq β₀ hβ0 hβlo hβhi ρ hρ hfloor hlo hhi hord
    simpa [dhB, dhK] using hc q χ hprim hne hsq hq β₀ hβ0 hβlo hβhi ρ hρ hfloor hlo hhi hord

/-- The Deuring–Heilbronn constant `c`, chosen once.  The landed proof's WITNESS has
`log(1/c) = 86.23` (the binding arm `(c₀/32)^{17/3}` at `c₀ = 1/126848`); `Classical.choose` does
not remember it, so no prose numeral about `dhC` is a theorem — the file keeps `log(1/dhC)`
symbolic everywhere and uses only `0 < dhC ≤ 1`. -/
noncomputable def dhC : ℝ := Classical.choose dh_repulsion_tall_at

/-- **The D–H contract at the chosen `c`, both arms.**  Class **A**, cap 20:
`Classical.choose_spec`.  Consumer: `dh_repulsion_tall_real`, `dh_ceiling_box`. -/
theorem dh_spec : 0 < dhC ∧ dhC ≤ 1 ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im ≠ 0 →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ dhC * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - (1 / 126848) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ dhC * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK) := by
  exact Classical.choose_spec dh_repulsion_tall_at

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
  exact Classical.choose_spec invSq_sum_split_le

/-- **Mertens' third constant, chosen once** (the verdict's A5: `hb_mertens_third_real` exports
`∃ C`; its proof's witness `29` is NOT exported, and `hsmall` in `(L2)` cannot be discharged
against an opaque constant unless the regime's threshold carries it — `n9E0` does, through
`exp(merC + segC)`). -/
noncomputable def merC : ℝ := Classical.choose hb_mertens_third_real

/-- Class **A**, cap 20: `Classical.choose_spec`.  Consumer: `hb_L2_at_hb_point` (the `hP`
binder and `hsmall`'s `8·EP` term). -/
theorem merC_spec : 0 ≤ merC ∧ ∀ z : ℝ, 3 ≤ z →
    |Real.log (primeProdBelow z) + Real.log (Real.log z) + Real.eulerMascheroniConstant|
      ≤ merC / Real.log z := by
  exact Classical.choose_spec hb_mertens_third_real

/-- **The coprime-segment constant, chosen once** (`hb_coprime_segment`'s `∃ C`; witness `50`
in the proof, not exported).  Consumer: `hb_L2_at_hb_point` (through `hb_hseg_closed`'s `hC`). -/
noncomputable def segC : ℝ := Classical.choose hb_coprime_segment

/-- Class **A**, cap 20: `Classical.choose_spec`.  Consumer: `hb_L2_at_hb_point`. -/
theorem segC_spec : 0 ≤ segC ∧ ∀ (q : ℕ), 0 < q → ∀ {z X : ℝ}, 3 ≤ z → z ≤ X →
    |(∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
          wLog n * ArithmeticFunction.vonMangoldt n)
        - (Real.log (Real.log X) - Real.log (Real.log z))|
      ≤ ppDefect z X + segC / Real.log z + (Real.log q / Real.log z) / z := by
  exact Classical.choose_spec hb_coprime_segment

/-- **`ℓ′` — the effective `log η`.**  The numerator of the D–H floor at base `4q`:
`log(ηL) − log(1/dhC) − 14·log(log(4q) + 2)`; with `log(1/dhC) ≈ 90` this is
`log η − 13·log log q − 90 + o(1)`: the `η`–`q` COUPLING lives here, in the one term
`dhK·log(log(4q)+2)`.  Every `log η` of HB's is `ℓ′` in this file — at HB's `k = 1` the two
agree up to `O(1)`; at the landed `k = 14` they differ by `13·log log q`. -/
noncomputable def n9Ell (q : ℕ) (η : ℝ) : ℝ :=
  Real.log (η * Real.log q) - Real.log (1 / dhC)
    - dhK * Real.log (Real.log (4 * (q : ℝ)) + 2)

/-- **The D–H numerator at the box top `Q = q(T+2)`** — `hN` of `re_le_repulsionCeiling_of_ne`
with `1/(1−β₀) = ηL`; the ceiling over the box `|Im ρ| ≤ T` is non-vacuous iff this is `≥ 0`.
`n9Ell q η = n9EllAt q η 2` (`n9EllAt_two`).  The Range-A tail (`logChiSum_tail_at_window`)
uses it at `T = efT0 q u + 1`, where it stays positive up to a triple-exponential height and
the ceiling is `> 1` (vacuous, harmless) beyond. -/
noncomputable def n9EllAt (q : ℕ) (η T : ℝ) : ℝ :=
  Real.log (η * Real.log q) - Real.log (1 / dhC)
    - dhK * Real.log (Real.log ((q : ℝ) * (T + 2)) + 2)

/-- Class **A**, cap 10: `unfold; ring_nf` (`4·q = q·(2+2)`).  Consumer: `dh_floor_ball`. -/
theorem n9EllAt_two (q : ℕ) (η : ℝ) : n9EllAt q η 2 = n9Ell q η := by
  have h : (q : ℝ) * (2 + 2) = 4 * (q : ℝ) := by ring
  simp only [n9EllAt, n9Ell, h]

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
part closes `hsmall`'s kill term and the master's middle term (`ℓ′^{2505·A}` against
`e^{280}(1+n9Cs)·log ℓ′`); the `e^{merC + segC}` part (the verdict's A5) closes `hsmall`'s
two Mertens terms: `ℓ′ ≥ e^{merC+segC}` with `L ≥ e^{401}·ℓ′` gives
`log z ≥ 10⁴·e^{401}·e^{merC+segC}/(merC+segC)`, so `8·merC/log z + 4·segC/log z ≪ 1/4`.
Read through `ηq`, this threshold ALSO forces `L > e^{3·10⁶}` (so `250 ≤ L`, `L ≥ 8000`,
`3 ≤ q`, `1/2 < β₀`, `ℓ′ ≤ 1.01·L`) — `ηq` alone forces nothing (vacuous at `η < 1`). -/
noncomputable def n9E0 : ℝ :=
  Real.exp (3 * 10 ^ 6) + (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 + Real.exp (merC + segC)

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
absorbs `L2cCmain = 2^31`, the `1/(250·A)` of the first master term, and the door's `4`; the
`e^{300}` (the verdict's A3) absorbs `4·n9K3`: at the regime's edge `log ℓ′ = 3·10⁶` the FL shape
`4^{−hbS}` is only `e^{−138}` while T3's allowance is `n9K/log ℓ′`, so without it T3 does not
follow from T1 (deficit `e^{140}`; the composition first closes at `log ℓ′ ≈ 6.05·10⁶`). -/
noncomputable def n9K (Cerr CA CA' CC : ℝ) : ℝ :=
  2 ^ 40 * Real.exp 300 * (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr) / hbZ0A

/-! ## §2 — the `z` witness (seam S3) -/

/-- **`z` brackets `q^{1/z₀}`.**  Class **A**, cap 30: `Nat.le_ceil`, `Nat.ceil_lt_add_one`.
Consumer: `hbZ_packet`. -/
theorem hbZ_bounds (q : ℕ) (η : ℝ) (hz0 : 0 < hbZ0 q η) :
    (q : ℝ) ^ (1 / hbZ0 q η) ≤ (hbZ q η : ℝ) ∧ (hbZ q η : ℝ) < (q : ℝ) ^ (1 / hbZ0 q η) + 1 := by
  have _hz0 := hz0
  have hnn : (0 : ℝ) ≤ (q : ℝ) ^ (1 / hbZ0 q η) :=
    Real.rpow_nonneg (Nat.cast_nonneg q) _
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hnn⟩

/-- **THE `z` PACKET — every `z`-binder of L4, P±, `(L2)`, K1 at once.**  Class **B**, cap 300.
Red-first: `log z ≥ L/z₀ = 10⁴·L/log ℓ′`; `ηq` gives `log ℓ′ ≤ log L`, so
`log z ≥ 10⁴·L/log L` — beats `16·log 100` (hz100), `8·log(1000L)` (hz8 via `Lwin x ≤ log(3q^500)`),
`e^{400}` (hzt via `zThresh_facts`, needs `log log z ≥ 400`); `z³ ≤ x` from `3/z₀ ≤ 250`; the
level: `hbS = L/(3 log z) ∈ [z₀/3.01, z₀/3]` and `levelE Λ₄ ≤ 2/Λ₄ + 2 ≤ 66` at `λ = 1/4`,
`log log z ≥ 400`, so `hbS ≥ 68` needs `z₀ ≥ 205`, i.e. `log ℓ′ ≥ 2.05·10⁶` — inside `ellBig`.
The last conjunct (the verdict's A4) licenses the corpus's ONLY numeral bound on the FL constant,
`flConst_quarter_le` (`flConst (1/4) Λ ≤ 14·e^{31}` at `Λ ≥ 1/10`, i.e. `log log z ≥ 1500`):
`log log z ≥ log(10⁴·L/log ℓ′) ≥ 9.2 + log L − log log ℓ′ ≥ 3·10⁶` via `ηq` + `ellBig`.
Consumer: `hb_lemma4_at_hb_point`, `hb_S3_at_hb_point`, `hb_L2_at_hb_point`. -/
theorem hbZ_packet [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ} (hR : N9Regime q χ β₀ η)
    {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500) :
    2 ≤ hbZ q η ∧ 100 ^ 16 ≤ hbZ q η ∧ Lwin x ^ 8 ≤ (hbZ q η : ℝ)
      ∧ (hbZ q η : ℝ) ^ 3 ≤ x ∧ zThresh (1 / 4) ≤ (hbZ q η : ℝ)
      ∧ 32 ≤ (hbZ q η : ℝ) - 1 ∧ (4 : ℝ) < (hbZ q η : ℝ) - 1
      ∧ 3 * hbS q η * Real.log (hbZ q η : ℝ) ≤ Real.log q
      ∧ levelE (Lam4 (1 / 4) (hbZ q η : ℝ)) + 2 ≤ hbS q η
      ∧ (3 : ℝ) ≤ (hbZ q η : ℝ) - 1
      ∧ (1 : ℝ) / 10 ≤ Lam4 (1 / 4) (hbZ q η : ℝ) := by
  sorry

/-! ## §3 — THE ZERO SIDE, MADE CONSUMABLE (the `(L1)`/L3 packet discharged) -/

/-- The regime forces `2 ≤ q`: at `q = 1` the effective `ℓ′` is `−log(1/dhC) − 14·log(log 4 + 2)`,
which is negative, while `n9E0 > 0` — so `ellBig` is contradicted. -/
private lemma n9_two_le_q [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) : 2 ≤ q := by
  rcases Nat.lt_or_ge q 2 with hlt | hge
  swap
  · exact hge
  exfalso
  have hq1 : q = 1 := by have := Nat.pos_of_ne_zero (NeZero.ne q); omega
  have hqR : ((q : ℕ) : ℝ) = 1 := by rw [hq1]; norm_num
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hpos : 0 < Real.log (Real.log 4 + 2) := Real.log_pos (by linarith)
  have hdk : dhK = 14 := rfl
  have hE : n9Ell q η < 0 := by
    simp only [n9Ell, hqR, Real.log_one, mul_zero, Real.log_zero, mul_one, hdk]
    linarith
  have hE0 : 0 < n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    have hc : (0 : ℝ) < Real.exp (3 * 10 ^ 6) := Real.exp_pos _
    simp only [n9E0]; linarith
  have := hR.ellBig
  linarith

/-- **Ordering over a BOX: no zero in the strip `9/10 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` sits above `β₀`**
(T-BAL-UNORDERED — the `hord` binder of `re_le_repulsionCeiling_of_ne`, at every height `T` at
which the D–H numerator is non-negative; the ball `2 (3/2)` is `T = 3/2`).  Restated over the
box in v2 (the verdict's K6 repair: the Range-A tail needs it at `T = efT0 q u + 1`).
Class **B**, cap 150.  Red-first: real `ρ` — `Re ρ < 1` (`LFunction_ne_zero_of_one_le_re`) and
`ηmax`; non-real `ρ` — `zero_free_region_all_numeral` at `Or.inr` gives
`Re ρ ≤ 1 − c₀/log(q(|Im ρ|+2)) ≤ 1 − c₀/log(q(T+2))`, and `β₀ = 1 − 1/(ηL) ≥ 1 − c₀/log(q(T+2))`
⟸ `log(q(T+2)) ≤ c₀·ηL` ⟸ (from `hN`) `log(q(T+2)) + 2 ≤ (ηL)^{1/14}` and `(ηL)^{13/14} ≥ 1/c₀`
(from `ellBig`: `η ≥ e^{ℓ′}`).  Consumer: `dh_ceiling_box`. -/
theorem re_le_beta0_of_ne [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {T : ℝ} (hT : 0 ≤ T) (hN : 0 ≤ n9EllAt q η T)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (hlo : 9 / 10 ≤ ρ.re) (hhi : ρ.re ≤ 1) (him : |ρ.im| ≤ T) :
    ρ.re ≤ β₀ := by
  have _hT := hT
  have hlt1 : ρ.re < 1 := by
    rcases lt_or_eq_of_le hhi with h | h
    · exact h
    · exact absurd hρ (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
        (Or.inl hR.ne) (le_of_eq h.symm))
  by_cases him0 : ρ.im = 0
  · have hcoe : ((ρ.re : ℝ) : ℂ) = ρ := by
      apply Complex.ext <;> simp [him0]
    exact hR.ηmax ρ.re (by rw [hcoe]; exact hρ) hlt1
  have hq2 : 2 ≤ q := n9_two_le_q hR
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hL : 0 < Real.log q := Real.log_pos (by linarith)
  have hLne : Real.log q ≠ 0 := ne_of_gt hL
  have hβpos : 0 < 1 - β₀ := by have := hR.β1; linarith
  have hne : (1 : ℝ) - β₀ ≠ 0 := ne_of_gt hβpos
  have hηL : η * Real.log q = 1 / (1 - β₀) := by rw [hR.ηdef]; field_simp
  have hηLpos : 0 < η * Real.log q := by rw [hηL]; positivity
  have hzfr : ρ.re ≤ 1 - 1 / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
    Salt.Fulcrum.zero_free_region_all_numeral q χ hR.prim hR.ne hρ (by linarith) (Or.inr him0)
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  -- the D–H numerator at the box top, read as a bound on `log(q(T+2))`
  have hNa : dhK * Real.log (Real.log ((q : ℝ) * (T + 2)) + 2)
      ≤ Real.log (η * Real.log q) := by
    simp only [n9EllAt] at hN; linarith
  -- `ellBig` makes `log(ηL)` astronomically large
  have hlog4q : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hMbig : Real.exp (3 * 10 ^ 6) ≤ Real.log (η * Real.log q) := by
    have h2 : 0 ≤ dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      mul_nonneg (by norm_num [dhK]) (Real.log_nonneg (by linarith))
    have hEll := hR.ellBig
    simp only [n9Ell] at hEll
    have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
      have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
      have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
      simp only [n9E0]; linarith
    linarith
  have hMge : (200000 : ℝ) ≤ Real.log (η * Real.log q) := by
    have h1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    linarith
  -- the zero's own height is below the box top
  have hWpos : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg ρ.im])
  have hWle : Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ Real.log ((q : ℝ) * (T + 2)) :=
    Real.log_le_log (by nlinarith [abs_nonneg ρ.im]) (by nlinarith [abs_nonneg ρ.im])
  have hM14 : Real.log ((q : ℝ) * (T + 2)) + 2
      ≤ Real.exp (Real.log (η * Real.log q) / 14) := by
    have h1 : Real.log (Real.log ((q : ℝ) * (T + 2)) + 2)
        ≤ Real.log (η * Real.log q) / 14 := by
      have hdk : dhK = 14 := rfl
      rw [hdk] at hNa; linarith
    calc Real.log ((q : ℝ) * (T + 2)) + 2
        = Real.exp (Real.log (Real.log ((q : ℝ) * (T + 2)) + 2)) := by
          have hWTpos : 0 < Real.log ((q : ℝ) * (T + 2)) := by linarith
          exact (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr h1
  have hbig : (126848 : ℝ) ≤ Real.exp (13 * Real.log (η * Real.log q) / 14) := by
    have h1 := Real.add_one_le_exp (13 * Real.log (η * Real.log q) / 14)
    linarith
  have hkey : 126848 * Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ η * Real.log q := by
    have hE : (0 : ℝ) < Real.exp (Real.log (η * Real.log q) / 14) := Real.exp_pos _
    have hsplit : Real.exp (Real.log (η * Real.log q))
        = Real.exp (Real.log (η * Real.log q) / 14)
          * Real.exp (13 * Real.log (η * Real.log q) / 14) := by
      rw [← Real.exp_add]; ring_nf
    calc 126848 * Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ 126848 * Real.exp (Real.log (η * Real.log q) / 14) := by nlinarith [hWle, hM14]
      _ ≤ Real.exp (13 * Real.log (η * Real.log q) / 14)
            * Real.exp (Real.log (η * Real.log q) / 14) := by nlinarith [hbig, hE]
      _ = Real.exp (Real.log (η * Real.log q)) := by rw [hsplit]; ring
      _ = η * Real.log q := Real.exp_log hηLpos
  have h1 : (1 - β₀) * (η * Real.log q) = 1 := by rw [hηL]; field_simp
  have hfin : 1 - β₀ ≤ 1 / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left hkey hβpos.le
    linarith
  linarith

/-- **D–H FOR A SECOND REAL ZERO, with Landau's floor** — a PROJECTION of `dh_spec`'s second arm
(the verdict's A2: as frozen in v1 this was stated at `dhC` with a spec that covered only
`Im ρ ≠ 0` — not provable; now both arms sit at one `c`).  For a real `ρ`, Landau's window
`Re ρ ≤ 1 − (1/5000)/log(4q)` implies the ZFR-shaped floor `Re ρ ≤ 1 − (1/126848)/log(q(0+2))`
(`(1/5000)/log 4q ≥ (1/126848)/log 2q` ⟸ `log 4q/log 2q ≤ 25.4`, true for `q ≥ 2`).
Class **A**, cap 40.  Consumer: `dh_ceiling_box`. -/
theorem dh_repulsion_tall_real :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → 2 ≤ q →
      ∀ β₀ : ℝ, DirichletCharacter.LFunction χ (β₀ : ℂ) = 0 → 1 / 2 < β₀ → β₀ < 1 →
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im = 0 →
        ρ.re ≤ 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) →
        16 / 17 ≤ ρ.re → ρ.re < 1 → ρ.re ≤ β₀ →
        (1 - β₀) ≥ dhC * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
          / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK := by
  intro q _ χ hprim hne hsq hq β₀ hβ0 hβlo hβhi ρ hρ hρim hlandau hlo hhi hord
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have habs : |ρ.im| = 0 := by rw [hρim]; simp
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hA : Real.log 4 ≤ Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    rw [habs]
    exact Real.log_le_log (by norm_num) (by nlinarith [hqR])
  have hApos : (0 : ℝ) < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    rw [hl4] at hA; linarith
  have hB : Real.log (4 * (q : ℝ)) = Real.log 2 + Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    rw [habs, show (4 : ℝ) * (q : ℝ) = 2 * ((q : ℝ) * (0 + 2)) by ring,
      Real.log_mul (by norm_num) (by nlinarith [hqR])]
  have hBpos : (0 : ℝ) < Real.log (4 * (q : ℝ)) := by rw [hB]; linarith
  have hfloor : ρ.re ≤ 1 - 1 / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
    have hdiv : (1 : ℝ) / 126848 / Real.log ((q : ℝ) * (|ρ.im| + 2))
        ≤ 1 / 5000 / Real.log (4 * (q : ℝ)) := by
      rw [div_le_div_iff₀ hApos hBpos, hB]
      rw [hl4] at hA
      linarith
    linarith
  exact dh_spec.2.2.2 q χ hprim hne hsq hq β₀ hβ0 hβlo hβhi ρ hρ hfloor hlo hhi hord

/-- The regime's arithmetic packet, read once: `q ≥ 2`, `L > 0`, `1 − β₀ > 0`, the identity
`ηL = 1/(1−β₀)`, `η > 0`, `log η ≥ n9E0` (the `14·log(log 4q + 2) ≥ log L` step absorbs the
`log L` of `log(ηL) = log η + log L`), and `β₀ > 1/2`. -/
private lemma n9_regime_facts [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    (2 : ℝ) ≤ (q : ℝ) ∧ 0 < Real.log q ∧ 0 < 1 - β₀
      ∧ η * Real.log q = 1 / (1 - β₀) ∧ 0 < η ∧ n9E0 ≤ Real.log η ∧ 1 / 2 < β₀ := by
  have hq2 : 2 ≤ q := n9_two_le_q hR
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hL : 0 < Real.log q := Real.log_pos (by linarith)
  have hLne : Real.log q ≠ 0 := ne_of_gt hL
  have hβpos : 0 < 1 - β₀ := by have := hR.β1; linarith
  have hne : (1 : ℝ) - β₀ ≠ 0 := ne_of_gt hβpos
  have hηL : η * Real.log q = 1 / (1 - β₀) := by rw [hR.ηdef]; field_simp
  have hηLpos : 0 < η * Real.log q := by rw [hηL]; positivity
  have hηpos : 0 < η := by
    rcases lt_or_ge 0 η with h | h
    · exact h
    · exact absurd hηLpos (not_lt.mpr (by nlinarith))
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  have hlog4q : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hLle : Real.log q ≤ Real.log (4 * (q : ℝ)) + 2 := by
    have : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hlogLle : Real.log (Real.log q) ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
    Real.log_le_log hL hLle
  have hXnn : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
    Real.log_nonneg (by linarith)
  have hdk : dhK = 14 := rfl
  have hEll := hR.ellBig
  simp only [n9Ell] at hEll
  have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
    Real.log_mul (ne_of_gt hηpos) hLne
  have hηbig : n9E0 ≤ Real.log η := by rw [hdk] at hEll; rw [hsplit] at hEll; linarith
  -- `β₀ > 1/2`: `1 − β₀ = 1/(ηL)` and `ηL = exp(log ηL)` is astronomically large
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
  have hηge : (3000001 : ℝ) ≤ Real.log η := by linarith
  have hηval : Real.exp (3000001 : ℝ) ≤ η := by
    have h := Real.exp_le_exp.mpr hηge
    rwa [Real.exp_log hηpos] at h
  have hηnum : (3000002 : ℝ) ≤ η := by
    have := Real.add_one_le_exp (3000001 : ℝ); linarith
  have hone : (1 - β₀) * (η * Real.log q) = 1 := by rw [hηL]; field_simp
  have hLbig : (1 : ℝ) / 2 ≤ Real.log q := by
    have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hqR
    have := Real.log_two_gt_d9
    linarith
  have hβhalf : 1 / 2 < β₀ := by nlinarith [hone, hβpos, hηnum, hLbig]
  exact ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩

/-- **THE REPULSION CEILING OVER A BOX — `hceil` discharged at every height at which the
contract speaks.**  Every zero `ρ ≠ β₀` in the strip `9/10 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` has
`Re ρ ≤ repulsionCeiling dhB dhC dhK (q(T+2)) (1−β₀)`, provided the numerator at the box top is
non-negative (`hN`).  This is `re_le_repulsionCeiling_of_ne` (`Lemma7EF.lean:661`) with its four
binders paid: `hrep` ← `dh_spec`'s first arm (the contract, height-free, in the `≤ 1 − β₀`
direction); `hord` ← `re_le_beta0_of_ne`; `hreal` ← for a real `ρ ≠ β₀`, Landau's window
(`landau_one_exceptional_at`, contrapositive; `β₀` is inside it by `ellBig`) then
`dh_repulsion_tall_real` gives the contract at base `2q`, `repulsion_ceiling_of_contract` +
`repulsionCeiling_mono` (to `q(T+2)`, `hN`) the ceiling; `hceil16` ⟸
`n9EllAt q η T ≤ 40·log(q(T+2))` ⟸ `n9EllAt ≤ log(ηL) ≤ 2e^{−401}L` (`ηq`); `hN` is `n9EllAt`
with `1/(1−β₀) = ηL` (`ηdef`).
Class **C**, cap 350.  Consumer: `dh_floor_ball` (at `T = 3/2`), `logChiSum_tail_at_window`
(at `T = efT0 q u + 1`). -/
theorem dh_ceiling_box [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {T : ℝ} (hT : 0 ≤ T) (hN : 0 ≤ n9EllAt q η T) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) →
      9 / 10 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
      ρ.re ≤ repulsionCeiling dhB dhC dhK ((q : ℝ) * (T + 2)) (1 - β₀) := by
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hdhB : dhB = 680 := rfl
  have hdhK : dhK = 14 := rfl
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  have hQ1 : (1 : ℝ) < (q : ℝ) * (T + 2) := by nlinarith
  have hlogQ : 0 < Real.log ((q : ℝ) * (T + 2)) := Real.log_pos hQ1
  have hlogid : Real.log (1 / (1 - β₀)) = Real.log (η * Real.log q) := by rw [hηL]
  have hNc : 0 ≤ Real.log (1 / (1 - β₀)) - Real.log (1 / dhC)
      - dhK * Real.log (Real.log ((q : ℝ) * (T + 2)) + 2) := by
    rw [hlogid]; simp only [n9EllAt] at hN; linarith
  -- the height-free contract, at the chosen `c`
  have hrep : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im ≠ 0 → 16 / 17 ≤ ρ.re →
      ρ.re < 1 → ρ.re ≤ β₀ →
      dhC * ((q : ℝ) * (|ρ.im| + 2)) ^ (-(dhB * (1 - ρ.re)))
        / (Real.log ((q : ℝ) * (|ρ.im| + 2)) + 2) ^ dhK ≤ 1 - β₀ := by
    intro ρ hz him hwin hlt hle
    exact dh_spec.2.2.1 q χ hR.prim hR.ne hR.sq hq2 β₀ hR.zero hβhalf hR.β1 ρ hz him hwin hlt hle
  -- T-BAL-UNORDERED at this height
  have hord : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 9 / 10 ≤ ρ.re → ρ.re ≤ 1 →
      |ρ.im| ≤ T → ρ.re ≤ β₀ :=
    fun ρ hz hlo hhi him => re_le_beta0_of_ne hR hT hN hz hlo hhi him
  -- the `16/17` strip is free: the ceiling itself is above it
  have hlogQge : Real.log q ≤ Real.log ((q : ℝ) * (T + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlogηL : Real.log (η * Real.log q) ≤ 2 * Real.log q := by
    have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
      Real.log_mul (ne_of_gt hηpos) (ne_of_gt hL)
    have hηq := hR.ηq
    have he401 := Real.add_one_le_exp (401 : ℝ)
    have h1 : Real.log η ≤ Real.log q := by
      rcases le_or_gt 0 (Real.log η) with h | h
      · nlinarith
      · linarith
    have h2 : Real.log (Real.log q) ≤ Real.log q := by
      have := Real.log_le_sub_one_of_pos hL; linarith
    linarith
  have hceil16 : (16 : ℝ) / 17 ≤ repulsionCeiling dhB dhC dhK ((q : ℝ) * (T + 2)) (1 - β₀) := by
    rw [repulsionCeiling]
    have hden : 0 < dhB * Real.log ((q : ℝ) * (T + 2)) := by
      rw [hdhB]; linarith
    have hkey : (Real.log (1 / (1 - β₀)) - Real.log (1 / dhC)
        - dhK * Real.log (Real.log ((q : ℝ) * (T + 2)) + 2))
        / (dhB * Real.log ((q : ℝ) * (T + 2))) ≤ 1 / 17 := by
      rw [div_le_iff₀ hden, hdhB, hlogid]
      have hXnn : 0 ≤ dhK * Real.log (Real.log ((q : ℝ) * (T + 2)) + 2) := by
        rw [hdhK]
        have : 0 ≤ Real.log (Real.log ((q : ℝ) * (T + 2)) + 2) :=
          Real.log_nonneg (by linarith)
        linarith
      linarith
    linarith
  -- the real-zero binder, through Landau's window
  have hwβ : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₀ := by
    have hlog4q : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
    have hl4 : Real.log (4 * (q : ℝ)) ≤ 2 + Real.log q := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have h2 := Real.log_two_lt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      linarith
    have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
      have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
      have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
      simp only [n9E0]; linarith
    have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    have hηge : (3000001 : ℝ) ≤ Real.log η := by linarith
    have hηnum : (30000 : ℝ) ≤ η := by
      have h := Real.exp_le_exp.mpr hηge
      rw [Real.exp_log hηpos] at h
      have := Real.add_one_le_exp (3000001 : ℝ)
      linarith
    have hLbig : (1 : ℝ) / 2 ≤ Real.log q := by
      have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hqR
      have := Real.log_two_gt_d9
      linarith
    have hprod : 30000 * Real.log q ≤ η * Real.log q :=
      mul_le_mul_of_nonneg_right hηnum hL.le
    have hcross : 5000 * Real.log (4 * (q : ℝ)) ≤ η * Real.log q := by linarith
    have hone : (1 - β₀) * (η * Real.log q) = 1 := by
      rw [hηL]; field_simp
    have hfin : 1 - β₀ ≤ 1 / 5000 / Real.log (4 * (q : ℝ)) := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [hcross, hβpos, hone]
    linarith
  have hreal : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im = 0 → ρ ≠ (β₀ : ℂ) →
      9 / 10 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
      ρ.re ≤ repulsionCeiling dhB dhC dhK ((q : ℝ) * (T + 2)) (1 - β₀) := by
    intro ρ hz him0 hne hlo hhi him
    rcases le_or_gt (16 / 17 : ℝ) ρ.re with hwin | hwin
    · have hcoe : ((ρ.re : ℝ) : ℂ) = ρ := by apply Complex.ext <;> simp [him0]
      have hzr : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by rw [hcoe]; exact hz
      have hlt1 : ρ.re < 1 := by
        rcases lt_or_eq_of_le hhi with h | h
        · exact h
        · exact absurd hz (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
            (Or.inl hR.ne) (le_of_eq h.symm))
      have hlandau : ρ.re ≤ 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) := by
        rcases le_or_gt ρ.re (1 - (1 / 5000) / Real.log (4 * (q : ℝ))) with h | h
        · exact h
        · exfalso
          have heq := (landau_one_exceptional_at hR.prim hR.ne hzr hR.zero h.le hwβ).1
          exact hne (by rw [← hcoe, heq])
      have hcon := dh_repulsion_tall_real q χ hR.prim hR.ne hR.sq hq2 β₀ hR.zero hβhalf hR.β1
        ρ hz him0 hlandau hwin hlt1 (hord ρ hz hlo hhi him)
      have hQρ1 : (1 : ℝ) < (q : ℝ) * (|ρ.im| + 2) := by nlinarith [abs_nonneg ρ.im]
      have hQρle : (q : ℝ) * (|ρ.im| + 2) ≤ (q : ℝ) * (T + 2) := by
        nlinarith [abs_nonneg ρ.im]
      have hstep := repulsion_ceiling_of_contract (σ := ρ.re) (by rw [hdhB]; norm_num)
        hdhCpos hQρ1 hβpos hcon
      exact le_trans hstep (repulsionCeiling_mono (by rw [hdhB]; norm_num)
        (by rw [hdhK]; norm_num) hQρ1 hQρle hNc)
    · linarith [hceil16]
  exact re_le_repulsionCeiling_of_ne hR.ne (by rw [hdhB]; norm_num) hdhCpos
    (by rw [hdhK]; norm_num) hq2 hR.β1 hrep hord hreal hceil16 hNc

/-- **THE FLOOR ON THE BALL — `hfloor` discharged where it is USED.**
Every zero `ρ ≠ β₀` of `L(·,χ)` in `ball 2 (3/2)` is at distance `≥ n9Floor q η` from `1`.
Class **B**, cap 150.  Red-first: `Re ρ < 1` (`LFunction_ne_zero_of_one_le_re`); if `Re ρ < 9/10`
then `‖ρ−1‖ ≥ 1 − Re ρ > 1/10 ≥ n9Floor` (`n9Floor ≤ 2e^{−401}/680` by `ηq`); else
`dh_ceiling_box` at `T = 3/2` (`hN`: `n9EllAt q η (3/2) ≥ n9Ell ≥ n9E0 > 0`, since
`log(3.5q) ≤ log(4q)`) gives `Re ρ ≤ repulsionCeiling … (3.5q) …`, `repulsionCeiling_mono` moves
the base to `4q = q(2+2)` (`hN` there is `n9Ell ≥ 0`, `n9EllAt_two`), and
`one_sub_ceiling_le_dist_one` is the floor (`n9Floor = 1 − repulsionCeiling dhB dhC dhK (4q) (1−β₀)`
with `log(1/(1−β₀)) = log(ηL)`).  Consumer: `hb_zero_data`. -/
theorem dh_floor_ball [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (hball : ρ ∈ Metric.ball (2 : ℂ) (3 / 2)) (hne : ρ ≠ (β₀ : ℂ)) :
    n9Floor q η ≤ ‖ρ - 1‖ := by
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hdhB : dhB = 680 := rfl
  have hdhK : dhK = 14 := rfl
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  have hlogid : Real.log (1 / (1 - β₀)) = Real.log (η * Real.log q) := by rw [hηL]
  have hlog4q : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hLle4 : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hEllpos : 0 < n9Ell q η := by
    have h1 := Real.exp_pos (3 * 10 ^ 6 : ℝ)
    have h2 := hR.ellBig
    linarith
  have hEll := hEllpos
  simp only [n9Ell] at hEll
  have hlogηL : Real.log (η * Real.log q) ≤ 2 * Real.log q := by
    have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
      Real.log_mul (ne_of_gt hηpos) (ne_of_gt hL)
    have hηq := hR.ηq
    have he401 := Real.add_one_le_exp (401 : ℝ)
    have h1 : Real.log η ≤ Real.log q := by
      rcases le_or_gt 0 (Real.log η) with h | h
      · nlinarith
      · linarith
    have h2 : Real.log (Real.log q) ≤ Real.log q := by
      have := Real.log_le_sub_one_of_pos hL; linarith
    linarith
  have hXnn : 0 ≤ dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := by
    rw [hdhK]
    have : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) := Real.log_nonneg (by linarith)
    linarith
  have hEllle : n9Ell q η ≤ 2 * Real.log q := by simp only [n9Ell]; linarith
  have hfloorle : n9Floor q η ≤ 1 / 10 := by
    rw [n9Floor, div_le_iff₀ (by rw [hdhB]; linarith), hdhB]
    linarith
  rw [Metric.mem_ball, dist_eq_norm] at hball
  have him : |ρ.im| ≤ 3 / 2 := by
    have h1 : |(ρ - 2).im| ≤ ‖ρ - 2‖ := Complex.abs_im_le_norm _
    have h2 : (ρ - 2).im = ρ.im := by simp
    rw [h2] at h1; linarith
  have hlt1 : ρ.re < 1 := by
    rcases lt_or_ge ρ.re 1 with h | h
    · exact h
    · exact absurd hρ (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hR.ne) h)
  rcases lt_or_ge ρ.re (9 / 10 : ℝ) with hlo | hlo
  · have habs : |(ρ - 1).re| ≤ ‖ρ - 1‖ := Complex.abs_re_le_norm _
    have hre : (ρ - 1).re = ρ.re - 1 := by simp
    rw [hre] at habs
    have hcase : (1 : ℝ) - ρ.re ≤ |ρ.re - 1| := by
      rcases abs_cases (ρ.re - 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    linarith
  · have hT : (0 : ℝ) ≤ 3 / 2 := by norm_num
    have hQ1 : (1 : ℝ) < (q : ℝ) * (3 / 2 + 2) := by nlinarith
    have hQQ : (q : ℝ) * (3 / 2 + 2) ≤ 4 * (q : ℝ) := by nlinarith
    have hlogQ1 : (0 : ℝ) < Real.log ((q : ℝ) * (3 / 2 + 2)) := Real.log_pos hQ1
    have hlogmono : Real.log ((q : ℝ) * (3 / 2 + 2)) ≤ Real.log (4 * (q : ℝ)) :=
      Real.log_le_log (by linarith) hQQ
    have hNbox : 0 ≤ n9EllAt q η (3 / 2) := by
      have h3 : dhK * Real.log (Real.log ((q : ℝ) * (3 / 2 + 2)) + 2)
          ≤ dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := by
        rw [hdhK]
        have := Real.log_le_log (by linarith) (by linarith :
          Real.log ((q : ℝ) * (3 / 2 + 2)) + 2 ≤ Real.log (4 * (q : ℝ)) + 2)
        linarith
      simp only [n9EllAt]
      linarith
    have hstep := dh_ceiling_box hR hT hNbox ρ hρ hne hlo (le_of_lt hlt1) him
    have hN4 : 0 ≤ Real.log (1 / (1 - β₀)) - Real.log (1 / dhC)
        - dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := by rw [hlogid]; linarith
    have hmono := repulsionCeiling_mono (b := dhB) (c := dhC) (k := dhK) (u := 1 - β₀)
      (by rw [hdhB]; norm_num) (by rw [hdhK]; norm_num) hQ1 hQQ hN4
    have hfin := one_sub_ceiling_le_dist_one (le_trans hstep hmono)
    have heq : (Real.log (1 / (1 - β₀)) - Real.log (1 / dhC)
        - dhK * Real.log (Real.log (4 * (q : ℝ)) + 2)) / (dhB * Real.log (4 * (q : ℝ)))
        = n9Floor q η := by
      rw [n9Floor, hlogid]; simp only [n9Ell]
    rw [heq] at hfin
    exact hfin

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
  classical
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hdhB : dhB = 680 := rfl
  have hdhK : dhK = 14 := rfl
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  have hWpos : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
  have hPbig : (3000001 : ℝ) ≤ n9Ell q η := by have := hR.ellBig; linarith
  have hPpos : 0 < n9Ell q η := by linarith
  have hEllEq : n9Ell q η = Real.log (η * Real.log q) - Real.log (1 / dhC)
      - dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := rfl
  have hXnn : 0 ≤ dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := by
    rw [hdhK]
    have : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) := Real.log_nonneg (by linarith)
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
    Real.log_mul (ne_of_gt hηpos) (ne_of_gt hL)
  have hηq := hR.ηq
  have he401 := Real.add_one_le_exp (401 : ℝ)
  have hlogηle : Real.log η ≤ Real.log q / 200 := by
    rcases le_or_gt 0 (Real.log η) with h | h
    · nlinarith
    · linarith
  have hlogLle : Real.log (Real.log q) ≤ Real.log q := by
    have := Real.log_le_sub_one_of_pos hL; linarith
  have hLhuge : (1500000 : ℝ) ≤ Real.log q := by linarith
  -- `log L ≤ L/200` from `L ≤ exp(L/200)`
  have hlogLsmall : Real.log (Real.log q) ≤ Real.log q / 200 := by
    have h400 := Real.add_one_le_exp (Real.log q / 400)
    have hnn : (0 : ℝ) ≤ Real.log q / 400 + 1 := by linarith
    have hprod : (Real.log q / 400 + 1) * (Real.log q / 400 + 1)
        ≤ Real.exp (Real.log q / 400) * Real.exp (Real.log q / 400) :=
      mul_le_mul h400 h400 hnn (le_of_lt (Real.exp_pos _))
    have hsq : Real.exp (Real.log q / 200)
        = Real.exp (Real.log q / 400) * Real.exp (Real.log q / 400) := by
      rw [← Real.exp_add]; ring_nf
    have hge : Real.log q ≤ Real.exp (Real.log q / 200) := by
      rw [hsq]; nlinarith [hprod, hLhuge]
    have := Real.log_le_log hL hge
    rwa [Real.log_exp] at this
  have hPsmall : n9Ell q η ≤ Real.log q / 100 := by linarith
  have hW2L : Real.log (4 * (q : ℝ)) ≤ 2 * Real.log q := by
    have h4 : Real.log (4 * (q : ℝ)) = Real.log 4 + Real.log q :=
      Real.log_mul (by norm_num) (by linarith)
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith
  have hq2L : Real.log ((q : ℝ) + 2) ≤ 2 * Real.log q := by
    have h1 : Real.log ((q : ℝ) + 2) ≤ Real.log ((q : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have h45L : Real.log ((q : ℝ) * (3 / 2 + 3)) ≤ 2 * Real.log q := by
    have h4 : Real.log ((q : ℝ) * (3 / 2 + 3)) = Real.log q + Real.log (3 / 2 + 3) := by
      rw [Real.log_mul (by linarith) (by norm_num)]
    have h5 : Real.log (3 / 2 + 3 : ℝ) ≤ Real.log 8 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h6 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; ring
    linarith
  -- the floor on the erased ball
  have hfloor : ∀ ρ ∈ Z.erase ((β₀ : ℂ)), n9Floor q η ≤ ‖ρ - 1‖ := by
    intro ρ hρ
    exact dh_floor_ball hR (hZ ρ (Finset.mem_of_mem_erase hρ)).2
      (hZ ρ (Finset.mem_of_mem_erase hρ)).1 (Finset.ne_of_mem_erase hρ)
  have hr0pos : 0 < n9Floor q η := by
    rw [n9Floor, hdhB]; exact div_pos hPpos (by linarith)
  -- the mass of the erased ball, off the crude density count
  have hsub : Z.erase ((β₀ : ℂ)) ⊆ Salt.SW.boxZeros χ (1 / 2) 1 (3 / 2) := by
    intro ρ hρ
    obtain ⟨hball, hzero⟩ := hZ ρ (Finset.mem_of_mem_erase hρ)
    rw [Metric.mem_ball, dist_eq_norm] at hball
    have hre : |(ρ - 2).re| ≤ ‖ρ - 2‖ := Complex.abs_re_le_norm _
    have him : |(ρ - 2).im| ≤ ‖ρ - 2‖ := Complex.abs_im_le_norm _
    have e1 : (ρ - 2).re = ρ.re - 2 := by simp
    have e2 : (ρ - 2).im = ρ.im := by simp
    rw [e1] at hre; rw [e2] at him
    have hre' := abs_lt.mp (lt_of_le_of_lt hre hball)
    have him' := abs_lt.mp (lt_of_le_of_lt him hball)
    have hlt1 : ρ.re < 1 := by
      rcases lt_or_ge ρ.re 1 with h | h
      · exact h
      · exact absurd hzero
          (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hR.ne) h)
    refine (Salt.SW.mem_boxZeros hR.ne).mpr ⟨hzero, by linarith [hre'.1], le_of_lt hlt1, ?_⟩
    rw [abs_le]; constructor <;> linarith [him'.1, him'.2]
  have hmass : (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ))
      ≤ 137 * (2 * (3 / 2) + 3) * Real.log ((q : ℝ) * (3 / 2 + 3)) := by
    have hstep1 : (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ))
        ≤ ∑ ρ ∈ Z.erase ((β₀ : ℂ)), (Salt.SW.zeroMult χ ρ : ℝ) :=
      Finset.sum_le_sum (fun ρ hρ => hm ρ (Finset.mem_of_mem_erase hρ))
    have hstep2 : (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (Salt.SW.zeroMult χ ρ : ℝ))
        ≤ ∑ ρ ∈ Salt.SW.boxZeros χ (1 / 2) 1 (3 / 2), (Salt.SW.zeroMult χ ρ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have hstep3 := Salt.SW.zeroCountM_le χ hR.prim hq2 (σ := 1 / 2) (T := 3 / 2)
      (by norm_num) (by norm_num)
    simp only [Salt.SW.zeroCountM, Salt.SW.efMultTotal] at hstep3
    linarith
  -- the Prachar split at the floor
  have hspec := invSqC_spec.2 χ hR.prim hq2 hr0pos hfloor
    (fun ρ hρ => (hZ ρ (Finset.mem_of_mem_erase hρ)).2)
    (fun ρ hρ => hm ρ (Finset.mem_of_mem_erase hρ)) hmass
  -- the arithmetic
  have hAinv := invSqC_spec.1
  have hWnn : (0 : ℝ) ≤ Real.log (4 * (q : ℝ)) := hWpos.le
  have hq2nn : (0 : ℝ) ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hL2nn : (0 : ℝ) ≤ 4 * Real.log q ^ 2 := by positivity
  have hG : 1 / n9Floor q η = 680 * Real.log (4 * (q : ℝ)) / n9Ell q η := by
    rw [n9Floor, hdhB]; field_simp
  have hGsq : 1 / n9Floor q η ^ 2 = (680 * Real.log (4 * (q : ℝ)) / n9Ell q η) ^ 2 := by
    rw [← hG, div_pow, one_pow]
  have hW2 : Real.log (4 * (q : ℝ)) ^ 2 ≤ 4 * Real.log q ^ 2 := by
    have h := mul_self_le_mul_self hWnn hW2L
    linarith only [h]
  have hPP : n9Ell q η ≤ n9Ell q η ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_left hPpos.le (by linarith only [hPbig])
  have hα : 1 / n9Floor q η ^ 2 ≤ 680 ^ 2 * (4 * Real.log q ^ 2 / n9Ell q η) := by
    rw [hGsq, div_pow, mul_pow,
      show (680 : ℝ) ^ 2 * (4 * Real.log q ^ 2 / n9Ell q η)
        = 680 ^ 2 * (4 * Real.log q ^ 2) / n9Ell q η by ring,
      div_le_div_iff₀ (pow_pos hPpos 2) hPpos]
    have s1 : Real.log (4 * (q : ℝ)) ^ 2 * n9Ell q η
        ≤ 4 * Real.log q ^ 2 * n9Ell q η := mul_le_mul_of_nonneg_right hW2 hPpos.le
    have s2 : 4 * Real.log q ^ 2 * n9Ell q η ≤ 4 * Real.log q ^ 2 * n9Ell q η ^ 2 :=
      mul_le_mul_of_nonneg_left hPP hL2nn
    linarith only [s1, s2]
  have hβbd : Real.log ((q : ℝ) + 2) / n9Floor q η
      ≤ 680 * (4 * Real.log q ^ 2 / n9Ell q η) := by
    rw [div_eq_mul_one_div, hG,
      show Real.log ((q : ℝ) + 2) * (680 * Real.log (4 * (q : ℝ)) / n9Ell q η)
        = Real.log ((q : ℝ) + 2) * (680 * Real.log (4 * (q : ℝ))) / n9Ell q η by ring,
      show (680 : ℝ) * (4 * Real.log q ^ 2 / n9Ell q η)
        = 680 * (4 * Real.log q ^ 2) / n9Ell q η by ring,
      div_le_div_iff₀ hPpos hPpos]
    have s0 : Real.log ((q : ℝ) + 2) * Real.log (4 * (q : ℝ))
        ≤ 2 * Real.log q * (2 * Real.log q) :=
      mul_le_mul hq2L hW2L hWnn (by linarith only [hL])
    have s2 : Real.log ((q : ℝ) + 2) * Real.log (4 * (q : ℝ)) * n9Ell q η
        ≤ 4 * Real.log q ^ 2 * n9Ell q η :=
      mul_le_mul_of_nonneg_right (by linarith only [s0]) hPpos.le
    linarith only [s2]
  have hγ : 16 * (137 * (2 * (3 / 2) + 3) * Real.log ((q : ℝ) * (3 / 2 + 3)))
      ≤ 3400 * (4 * Real.log q ^ 2 / n9Ell q η) := by
    rw [show (3400 : ℝ) * (4 * Real.log q ^ 2 / n9Ell q η)
        = 3400 * (4 * Real.log q ^ 2) / n9Ell q η by ring, le_div_iff₀ hPpos]
    have s1 : Real.log ((q : ℝ) * (3 / 2 + 3)) * n9Ell q η
        ≤ 2 * Real.log q * (Real.log q / 100) :=
      mul_le_mul h45L hPsmall hPpos.le (by linarith only [hL])
    linarith only [s1, sq_nonneg (Real.log q)]
  have hfinal : invSqC * (1 / n9Floor q η ^ 2
        + Real.log ((q : ℝ) + 2) / n9Floor q η)
      + 16 * (137 * (2 * (3 / 2) + 3) * Real.log ((q : ℝ) * (3 / 2 + 3)))
      ≤ n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η) := by
    have hstep : invSqC * (1 / n9Floor q η ^ 2 + Real.log ((q : ℝ) + 2) / n9Floor q η)
        ≤ invSqC * (680 ^ 2 * (4 * Real.log q ^ 2 / n9Ell q η)
            + 680 * (4 * Real.log q ^ 2 / n9Ell q η)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hα, hβbd]) hAinv.le
    have hcs : n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η)
        = invSqC * (680 ^ 2 * (4 * Real.log q ^ 2 / n9Ell q η)
            + 680 * (4 * Real.log q ^ 2 / n9Ell q η))
          + 3400 * (4 * Real.log q ^ 2 / n9Ell q η) := by
      simp only [n9Cs, hdhB]; ring
    rw [hcs]; linarith only [hstep, hγ]
  linarith only [hspec, hfinal]

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
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  obtain ⟨Z, m, h1, h2, h3, h4⟩ :=
    Salt.SW.LFunction_partialFraction_remainder_diff χ hR.prim hq2
  have hm : ∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ) := by
    intro ρ hρ
    exact le_of_eq (by exact_mod_cast h3 ρ hρ)
  refine ⟨Z, m, h1, h2, h3, h4, ?_, sinv_ball hR h1 hm⟩
  intro ρ hρ
  exact dh_floor_ball hR (h1 ρ (Finset.mem_of_mem_erase hρ)).2
    (h1 ρ (Finset.mem_of_mem_erase hρ)).1 (Finset.ne_of_mem_erase hρ)

/-- **`(L1)`, LOWER SIDE, DISCHARGED: `L′/L(1,χ) ≥ ηL − (1606 + 8·n9Cs)·L/√ℓ′`.**
Class **B**, cap 200.  Red-first: `hb_zero_data`; `zeroMult_eq_one_of_eta` (M-ONE, `η ≥ 15000`)
pins `m β₀ = 1`; `neg_re_logDeriv_differenced_mult` at `σ = 1`, `σ′ = 1 + √ℓ′/(2L)` with
`hs'top := neg_re_logDeriv_LFunction_le`; `l1_error_collapse` at `Lp := 2L`, `ell := ℓ′`,
`Cs := n9Cs`, `CR := 1600·log(80√q(1+log q)) ≤ 800·(2L)` (`ηq` gives `L ≥ 20`); then
`ηL = 1/(1−β₀)`.  This is `neg_re_logDeriv_one_le_mult`'s body (`Lemma7L.lean:190-230`) with its
two antecedents paid — the `ell`-FREE entry point (`hσ'r : √ell/Lp ≤ r0/2` is ITS binder, at
`ell = ℓ′`: `ℓ′ ≥ 680²(1 + 1.39/L)²`, inside `n9E0`).  ⛔ NOT `hb_L1_one_sided`
(`Lemma7L.lean:231`): it hard-wires `ell := log η` in its rate AND its `hSinvC`, and
`log η/ℓ′ = 1 + (13·log L + 86)/ℓ′` is UNBOUNDED in the regime (fix `ℓ′`, let `q` grow), so
`sinv_ball`'s `ℓ′`-scale bound cannot feed it.  Consumer: `hb_S3_at_hb_point`. -/
theorem hb_L1_lower_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    η * Real.log q - (1606 + 8 * n9Cs) * (Real.log q / Real.sqrt (n9Ell q η)) ≤ hbLL χ := by
  sorry

/-- **The `s′`-side input, LOWER form** — the mirror of `neg_re_logDeriv_LFunction_le`:
`−Re L′/L(σ,χ) ≥ −(1/(σ−1) + 1)` on `1 < σ ≤ 2`.  Class **A**, cap 60.  Red-first (the verdict's
A6 — the `tsum` route runs through four `private` lemmas of `TwistedMertens.lean` and cannot be
cited from here): the PUBLIC `vmPairS_le_pole` (`TwistedMertens.lean:252`) at `N := 0`,
`0 ≤ vmPairS χ 0 σ` by `Finset.sum_nonneg` from `one_add_chiRe_nonneg` and `vonMangoldt_nonneg`,
and `linarith`.  Consumer: `neg_re_logDeriv_differenced_mult_ge`. -/
theorem neg_re_logDeriv_LFunction_ge {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(1 / (σ - 1) + 1) ≤ (-logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have h := vmPairS_le_pole χ 0 h1 h2
  have h0 : vmPairS χ 0 σ = 0 := by simp [vmPairS, vmPairW]
  rw [h0] at h
  linarith

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

/-- The regime's numeric packet used by the pretense rows: `L` is astronomically large,
`ℓ′ ∈ [3000001, L/100]`, `log 4q ≤ 2L`, and the Borel–Carathéodory remainder constant
`1600·log(80√q(1+log q))` sits under `800·(2L)`. -/
private lemma n9_num_facts [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    (2 : ℝ) ≤ (q : ℝ) ∧ (1500000 : ℝ) ≤ Real.log q ∧ (3000001 : ℝ) ≤ n9Ell q η
      ∧ n9Ell q η ≤ Real.log q / 100
      ∧ 0 < Real.log (4 * (q : ℝ)) ∧ Real.log (4 * (q : ℝ)) ≤ 2 * Real.log q
      ∧ 1600 * Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q))
          ≤ 800 * (2 * Real.log q) := by
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hdhK : dhK = 14 := rfl
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  have hWpos : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
  have hPbig : (3000001 : ℝ) ≤ n9Ell q η := by have := hR.ellBig; linarith
  have hEllEq : n9Ell q η = Real.log (η * Real.log q) - Real.log (1 / dhC)
      - dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := rfl
  have hXnn : 0 ≤ dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := by
    rw [hdhK]
    have : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) := Real.log_nonneg (by linarith)
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
    Real.log_mul (ne_of_gt hηpos) (ne_of_gt hL)
  have hηq := hR.ηq
  have he401 := Real.add_one_le_exp (401 : ℝ)
  have hlogηle : Real.log η ≤ Real.log q / 200 := by
    rcases le_or_gt 0 (Real.log η) with h | h
    · nlinarith
    · linarith
  have hlogLle : Real.log (Real.log q) ≤ Real.log q := by
    have := Real.log_le_sub_one_of_pos hL; linarith
  have hLhuge : (1500000 : ℝ) ≤ Real.log q := by linarith
  have hlogLsmall : Real.log (Real.log q) ≤ Real.log q / 200 := by
    have h400 := Real.add_one_le_exp (Real.log q / 400)
    have hnn : (0 : ℝ) ≤ Real.log q / 400 + 1 := by linarith
    have hprod : (Real.log q / 400 + 1) * (Real.log q / 400 + 1)
        ≤ Real.exp (Real.log q / 400) * Real.exp (Real.log q / 400) :=
      mul_le_mul h400 h400 hnn (le_of_lt (Real.exp_pos _))
    have hsq : Real.exp (Real.log q / 200)
        = Real.exp (Real.log q / 400) * Real.exp (Real.log q / 400) := by
      rw [← Real.exp_add]; ring_nf
    have hge : Real.log q ≤ Real.exp (Real.log q / 200) := by
      rw [hsq]; nlinarith [hprod, hLhuge]
    have := Real.log_le_log hL hge
    rwa [Real.log_exp] at this
  have hPsmall : n9Ell q η ≤ Real.log q / 100 := by linarith
  have hW2L : Real.log (4 * (q : ℝ)) ≤ 2 * Real.log q := by
    have h4 : Real.log (4 * (q : ℝ)) = Real.log 4 + Real.log q :=
      Real.log_mul (by norm_num) (by linarith)
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hsqq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := Real.mul_self_sqrt hqpos.le
  have hexp4 : Real.exp (Real.log q / 4) ^ 4 = (q : ℝ) := by
    rw [← Real.exp_nat_mul]
    push_cast
    rw [show (4 : ℝ) * (Real.log q / 4) = Real.log q by ring, Real.exp_log hqpos]
  have hsqrtq : 80 * (1 + Real.log q) ≤ Real.sqrt (q : ℝ) := by
    rw [Real.le_sqrt (by positivity) hqpos.le]
    have hA : (Real.log q / 4) ^ 4 ≤ (Real.log q / 4 + 1) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hB : (Real.log q / 4 + 1) ^ 4 ≤ Real.exp (Real.log q / 4) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (Real.log q / 4)]) 4
    have h2 : (6553600 : ℝ) ≤ Real.log q ^ 2 := by nlinarith only [hLhuge]
    have h3 : (80 * (1 + Real.log q)) ^ 2 ≤ (Real.log q / 4) ^ 4 := by
      nlinarith only [h2, hLhuge, sq_nonneg (Real.log q)]
    linarith only [hA, hB, h3, hexp4]
  have hCR : 1600 * Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q))
      ≤ 800 * (2 * Real.log q) := by
    have hmm : 80 * (1 + Real.log q) * Real.sqrt (q : ℝ)
        ≤ Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) :=
      mul_le_mul_of_nonneg_right hsqrtq (Real.sqrt_nonneg _)
    rw [hsqq] at hmm
    have h1 : 80 * Real.sqrt (q : ℝ) * (1 + Real.log q) ≤ (q : ℝ) := by linarith only [hmm]
    have h2 : Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q)) ≤ Real.log q :=
      Real.log_le_log (by positivity) h1
    linarith only [h2, hLhuge]
  exact ⟨hqR, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩

/-- **The pretense sum at the operating point, at any window height.**  `pretenseSum_le_differenced`
at `σ = 1 + 1/(2L)`, `σ′ = 1 + √ℓ′/(2L)` against `hb_zero_data`'s `Z`, with the core rate absorbed
by `hbCoreRate_at_hb_optimum_absorbed`; the window enters only through `N^{1/(2L)} ≤ e^E`. -/
private lemma n9_two_pretense_le [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {N : ℕ} {E : ℝ}
    (hlogN : Real.log (N : ℝ) ≤ 2 * E * Real.log q) :
    2 * PretenseSum χ N ≤ Real.exp E * ((1 - β₀) * (2 * Real.log q) ^ 2
      + (2 + (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η)))) := by
  obtain ⟨hqR, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  have hL : 0 < Real.log q := by linarith only [hLhuge]
  have hPpos : 0 < n9Ell q η := by linarith only [hPbig]
  have hdhB : dhB = 680 := rfl
  have hLp : (0 : ℝ) < 2 * Real.log q := by linarith only [hL]
  -- `√ℓ′` facts
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n9Ell q η) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith only [hPbig])
  have hsmul : Real.sqrt (n9Ell q η) * Real.sqrt (n9Ell q η) = n9Ell q η :=
    Real.mul_self_sqrt hPpos.le
  have hsnn : (0 : ℝ) ≤ Real.sqrt (n9Ell q η) := Real.sqrt_nonneg _
  have hs2L : Real.sqrt (n9Ell q η) ≤ 2 * Real.log q := by
    nlinarith only [hsmul, hPsmall, hs1, hL, hsnn]
  have hs1360 : (1360 : ℝ) ≤ Real.sqrt (n9Ell q η) := by
    nlinarith only [hsmul, hPbig, hs1, hsnn]
  -- the floor and the two proximity conditions
  have hr0eq : n9Floor q η = n9Ell q η / (680 * Real.log (4 * (q : ℝ))) := by
    rw [n9Floor, hdhB]
  have hr0pos : 0 < n9Floor q η := by
    rw [hr0eq]; exact div_pos hPpos (by linarith only [hWpos])
  have hσr : 1 / (2 * Real.log q) ≤ n9Floor q η / 2 := by
    rw [hr0eq, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [hW2L, hL, mul_le_mul_of_nonneg_left hPbig hL.le]
  have hσ'r : Real.sqrt (n9Ell q η) / (2 * Real.log q) ≤ n9Floor q η / 2 := by
    rw [hr0eq, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hp1 : 1360 * Real.sqrt (n9Ell q η) ≤ n9Ell q η := by
      have h := mul_le_mul_of_nonneg_right hs1360 hsnn
      rw [hsmul] at h; exact h
    have hp2 : Real.log (4 * (q : ℝ)) * Real.sqrt (n9Ell q η)
        ≤ 2 * Real.log q * Real.sqrt (n9Ell q η) :=
      mul_le_mul_of_nonneg_right hW2L hsnn
    have hp3 : 2 * Real.log q * (1360 * Real.sqrt (n9Ell q η))
        ≤ 2 * Real.log q * n9Ell q η := mul_le_mul_of_nonneg_left hp1 (by linarith only [hL])
    linarith only [hp2, hp3]
  -- the zero packet
  obtain ⟨Z, m, hZ, hZall, hmz, hrem, hfloor, hSinv⟩ := hb_zero_data hR
  have hb1 := hR.β1
  have hβhalf : 1 / 2 < β₀ := (n9_regime_facts hR).2.2.2.2.2.2
  have hβball : ((β₀ : ℝ) : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : ((β₀ : ℝ) : ℂ) - 2 = ((β₀ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith only [hβhalf], by linarith only [hb1]⟩
  obtain ⟨hβZ, hmβ⟩ := hZall ((β₀ : ℝ) : ℂ) hβball hR.zero
  -- the two abscissae
  have hσ1 : (1 : ℝ) < 1 + 1 / (2 * Real.log q) := by
    have h : (0 : ℝ) < 1 / (2 * Real.log q) := by positivity
    linarith only [h]
  have hσ2 : 1 + 1 / (2 * Real.log q) ≤ 2 := by
    have h : 1 / (2 * Real.log q) ≤ 1 := by rw [div_le_one hLp]; linarith only [hLhuge]
    linarith only [h]
  have hlt : 1 + 1 / (2 * Real.log q) ≤ 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q) := by
    have h : 1 / (2 * Real.log q) ≤ Real.sqrt (n9Ell q η) / (2 * Real.log q) := by gcongr
    linarith only [h]
  have hσ'2 : 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q) ≤ 2 := by
    have h : Real.sqrt (n9Ell q η) / (2 * Real.log q) ≤ 1 := by
      rw [div_le_one hLp]; linarith only [hs2L]
    linarith only [h]
  have hkey := pretenseSum_le_differenced χ N
    (σ := 1 + 1 / (2 * Real.log q)) (σ' := 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))
    (β₀ := β₀) (r0 := n9Floor q η)
    (Sinv := n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η))
    (Rrem := 1600 * Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q))
      * |(1 + 1 / (2 * Real.log q)) - (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))|)
    hσ1 hσ2 hlt hσ'2 hb1 hβZ hmβ hr0pos (by linarith only [hσr]) (by linarith only [hσ'r])
    hfloor hSinv
    (hrem (1 + 1 / (2 * Real.log q)) (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))
      (by linarith only [hσ1]) hσ2 (by linarith only [hσ1, hlt]) hσ'2)
  -- the rate, absorbed
  have hCsnn : (0 : ℝ) ≤ n9Cs := by
    have hA := invSqC_spec.1
    have hprod : (0 : ℝ) ≤ invSqC * (dhB ^ 2 + dhB) :=
      mul_nonneg hA.le (by rw [hdhB]; norm_num)
    simp only [n9Cs]; linarith only [hprod]
  have habs : |(1 + 1 / (2 * Real.log q)) - (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))|
      = (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) - (1 + 1 / (2 * Real.log q)) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hlt])]
  have hrate := hbCoreRate_at_hb_optimum_absorbed (Lp := 2 * Real.log q) (ell := n9Ell q η)
    (Cs := n9Cs) (CR := 1600 * Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q)))
    (by linarith only [hPbig]) (by linarith only [hPsmall, hL]) hCsnn le_rfl hCR
  rw [habs] at hkey
  -- the window factor
  have hexpo : (1 + 1 / (2 * Real.log q)) - 1 = 1 / (2 * Real.log q) := by ring
  have hwin : ((N : ℕ) : ℝ) ^ ((1 + 1 / (2 * Real.log q)) - 1) ≤ Real.exp E := by
    rcases Nat.eq_zero_or_pos N with hN0 | hN0
    · rw [hN0]
      rw [show (((0 : ℕ) : ℝ)) = 0 by norm_num,
        Real.zero_rpow (by rw [hexpo]; positivity)]
      exact (Real.exp_pos E).le
    · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
      rw [Real.rpow_def_of_pos hNpos]
      apply Real.exp_le_exp.mpr
      rw [hexpo, mul_one_div, div_le_iff₀ hLp]
      linarith only [hlogN]
  -- assemble
  have hpole : (1 - β₀) / ((1 + 1 / (2 * Real.log q)) - 1) ^ 2
      = (1 - β₀) * (2 * Real.log q) ^ 2 := by
    rw [show (1 + 1 / (2 * Real.log q)) - 1 = 1 / (2 * Real.log q) by ring]
    field_simp
  rw [hpole] at hkey
  have hinnernn : (0 : ℝ) ≤ (1 - β₀) * (2 * Real.log q) ^ 2
      + (2 + (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η))) := by
    have h1 : (0 : ℝ) ≤ (1 - β₀) * (2 * Real.log q) ^ 2 := by
      apply mul_nonneg (by linarith only [hb1]) (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η)) :=
      mul_nonneg (by linarith only [hCsnn]) (div_nonneg (by linarith only [hL]) hsnn)
    linarith only [h1, h2]
  have hcd : (1 - β₀) * (2 * Real.log q) ^ 2
        + hbCoreRate (1 + 1 / (2 * Real.log q))
          (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))
          (n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η))
          (1600 * Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q))
            * ((1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))
              - (1 + 1 / (2 * Real.log q))))
      ≤ (1 - β₀) * (2 * Real.log q) ^ 2
        + (2 + (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η))) := by
    linarith only [hrate]
  have hAnn : (0 : ℝ) ≤ ((N : ℕ) : ℝ) ^ ((1 + 1 / (2 * Real.log q)) - 1) :=
    Real.rpow_nonneg (by positivity) _
  have hstep1 := mul_le_mul_of_nonneg_left hcd hAnn
  have hstep2 := mul_le_mul_of_nonneg_right hwin hinnernn
  linarith only [hkey, hstep1, hstep2]

/-- **L3 DISCHARGED: the pretense sum at `N = 2x + 2` on the window.**  Class **B**, cap 150.
Red-first: `hb_zero_data`; `pretenseSum_le_differenced` at `σ = 1 + 1/(2L)`, `σ′ = 1 + √ℓ′/(2L)`;
`hbCoreRate_at_hb_optimum_absorbed` at `Lp := 2L`, `ell := ℓ′`; `N^{1/(2L)} ≤ (3q^{500})^{1/(2L)}
≤ e^{251}`.  This is `pretenseSum_at_repulsion_floor`'s body with `Z` visible — a BODY RE-RUN,
not a call: `two_mul_pretenseSum_le_at_window` has the hard `hwin : log X ≤ 500·L` (here
`log N ≤ 500L + log 3`) and the literal `e^{250}`, and the landed L3 wrapper's `hSinvC` is in the
`log η` currency (`sinv_ball` delivers the `ℓ′` currency, and `log η/ℓ′` is unbounded in the
regime).  Consumer: `hb_lemma4_at_hb_point` (into `lemma4Err`'s `PretenseSum χ (2x+2)`). -/
theorem pretenseSum_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500) :
    PretenseSum χ (2 * x + 2)
      ≤ Real.exp 251 * ((1 - β₀) * (2 * Real.log q) ^ 2
          + (2 + (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η)))) / 2 := by
  obtain ⟨hqR, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  have hL : 0 < Real.log q := by linarith only [hLhuge]
  have hNpos : (0 : ℝ) < 2 * (x : ℝ) + 2 := by positivity
  have hq500 : (1 : ℝ) ≤ (q : ℝ) ^ 500 := one_le_pow₀ (by linarith only [hqR])
  have hNle : 2 * (x : ℝ) + 2 ≤ 4 * (q : ℝ) ^ 500 := by linarith only [hx', hq500]
  have hNlog : Real.log ((2 * x + 2 : ℕ) : ℝ) ≤ 2 * 251 * Real.log q := by
    have hcast : ((2 * x + 2 : ℕ) : ℝ) = 2 * (x : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    have h1 : Real.log (2 * (x : ℝ) + 2) ≤ Real.log (4 * (q : ℝ) ^ 500) :=
      Real.log_le_log hNpos hNle
    have h2 : Real.log (4 * (q : ℝ) ^ 500) = Real.log 4 + 500 * Real.log q := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    have hl2 := Real.log_two_lt_d9
    linarith only [h1, h2, hl4, hl2, hLhuge]
  have hmain := n9_two_pretense_le hR (E := 251) hNlog
  linarith only [hmain]

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
  obtain ⟨hqR, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  have hL : 0 < Real.log q := by linarith only [hLhuge]
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith only [hz])
  have hkill := chiOne_prime_logWeighted_le χ (z := z) (X := X) hz
  have hNlog : Real.log ((⌊X⌋₊ : ℕ) : ℝ) ≤ 2 * 250 * Real.log q := by
    rcases Nat.eq_zero_or_pos ⌊X⌋₊ with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith only [hL]
    · have h1 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX
      have h2 : (0 : ℝ) < ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h0
      have h3 := Real.log_le_log h2 h1
      linarith only [h3, hwin]
  have hpre := n9_two_pretense_le hR (E := 250) hNlog
  have hstep : 2 * PretenseSum χ ⌊X⌋₊ / Real.log z
      ≤ Real.exp 250 * ((1 - β₀) * (2 * Real.log q) ^ 2
          + (2 + (802 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η)))) / Real.log z :=
    div_le_div_of_nonneg_right hpre hlogz.le
  have hchain : 2 * ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter
        (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1),
        wLog n * ArithmeticFunction.vonMangoldt n
      ≤ 2 * PretenseSum χ ⌊X⌋₊ / Real.log z := by
    rw [mul_div_assoc]
    linarith only [hkill]
  linarith only [hchain, hstep]

/-! ## §4 — N4's COMPOSITION: `(L2)` at HB's operating point -/

/-- **Real zeros other than `β₀` lie below every EF ceiling** — the `hreal` binder of
`logChiSum_tendsto_zfr_hundred`, which has NO producer in the corpus.  Class **B**, cap 120.
Red-first: for real `ρ ≠ β₀`, `ηmax` gives `ρ < β₀`; `landau_one_exceptional_at` (contrapositive,
`β₀ ≥ 1 − (1/5000)/log 4q` from `ellBig`) gives `ρ ≤ 1 − (1/5000)/log(4q)`, and
`1/5000 ≥ c₀·log(4q)/log(q(efT0 q t + 3))` at `c₀ = 1/126848`.  Character-for-character the
`hreal` binder of `logChiSum_tendsto_zfr_hundred` (verified, K6).
Consumer: `hbEulerLog_tendsto` (that producer's `hreal`), `logChiSum_tail_at_window` (the
`efZfrCeil` half of the `min` ceiling). -/
theorem real_zeros_below_zfrCeil [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    ∀ t : ℝ, ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.im = 0 → ρ ≠ (β₀ : ℂ) →
      9 / 10 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ efT0 q t + 1 →
      ρ.re ≤ efZfrCeil q (1 / 126848) t := by
  sorry

/-- **`htail` AT THE WINDOW, RANGE A — the tail built at the REPULSION ceiling.**  v1 re-exported
the landed Range-B tail `logChiSum_tendsto_zfr_hundred` at a printed `e^{70000}`; the verdict's
one FATAL (K6): that producer's `X₀` is `Classical.choose`d from
`efEnvelope_zfr_eventually_le_sharp`, whose rows force `log X₀ ≥ (log q + 7)²` and
`log X₀ ≳ 1.5·10^{17}` — `q`-dependent and
superpolynomial — NO `x ∈ [q^250, q^500]` clears it, and the Range-B ceiling's decay at `u = q^b`
is a CONSTANT `e^{−c₀ b}`, so no threshold repair exists there.  Range A is where the decay is
real: the repulsion ceiling's `u^{bceil−1} = exp(−n9EllAt·log u/(680·log(q(T₀+3))))` is
`≤ exp(−ℓ′/5000)` from `u ≥ q^250` on.  Class **C**, cap 600 (the eventually-lemma re-proved,
~230 ln in the landed Range-B version).  Red-first: `hm1 := zeroMult_eq_one_of_eta`; the ceiling
function `bceil u := min (repulsionCeiling dhB dhC dhK (q(efT0 q u + 3)) (1−β₀)) (efZfrCeil q
(1/126848) u)` — continuous on `Ici X` (`continuousOn_efZfrCeil`; the repulsion half is `log ∘ log`
of `efT0`), VALID at every `u` (`psiDefect_norm_le_envelope`'s `hceil` over `|Im ρ| ≤ efT0 q u + 1`:
the `efZfrCeil` half from `zero_free_region_all_numeral` + `real_zeros_below_zfrCeil`; the repulsion
half from `dh_ceiling_box` at `T = efT0 q u + 1` when `0 ≤ n9EllAt q η T`, and trivial — the
ceiling is `> 1 ≥ Re ρ` — when it is not; the `min` needs no case split in the statement);
`efEnvelope_le_ledger_sharp` is ceiling-generic (`bceil` enters only row (iv) `10³M³N·u^{bceil−1}`);
rows (i)–(iii) verbatim from the landed proof (`ledger_const_le_of_window` takes exactly
`hwin : 250·log q ≤ log u`); row (iv) killed by the repulsion decay below the crossover and by
the Range-B decay `exp(−c₀·log u/(7·log log u))` above it (the crossover sits at
`log log(qu) ≈ (ηL)^{1/14}/6`, far above `exp(20·L·log L/c₀)`); `logChiSum_tendsto_of_envelope`
and the landed `key` arithmetic give the grade (row (i) is ceiling-independent, so `100/√log X`
is unchanged).  Consumer: `hb_L2_at_hb_point` (as `htail` at `X = x` and as `hcorr_at_split`'s
`hS`). -/
theorem logChiSum_tail_at_window [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {X : ℝ} (hX : (q : ℝ) ^ 250 ≤ X) :
    ∃ S : ℂ, Tendsto (fun Y : ℝ => logChiSum χ X Y) atTop (𝓝 S) ∧
      ‖S + (Salt.SW.zeroMult χ (β₀ : ℂ) : ℂ)
          * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖
        ≤ 100 / Real.sqrt (Real.log X) := by
  sorry

/-- **`hlimP` — the ordered Euler log-product converges** (the CHAR-TRIO flag's step 1, never
produced — every occurrence in the corpus is a hypothesis; `hb_hcorr_closed` carries it).
Class **C**, cap 300.  Red-first (the verdict's A1 re-route — NOT through
`logChiSum_tail_at_window`; a pure convergence statement needs no printed threshold):
`hbEulerLog χ z Y = P(z,Y) + R(Y)` with `R(Y) = Σ_{z<p≤Y}(−log(1−χ(p)/p) − χ(p)/p)` termwise
non-negative and bounded by `2/⌊z⌋` (`hbEulerLog_sub_primeSum_termwise` +
`sum_two_div_sq_windowPrimes_le`), hence convergent by monotone convergence; `P(z,Y)` is
`(logChiSum χ z Y).re` minus a prime-power part, itself monotone and bounded by `10/√⌊z⌋`; and
`(logChiSum χ z Y).re` converges because `logChiSum_tendsto_zfr_hundred` at its OWN existential
`X₀` (any `X ≥ max X₀ z`, however large — `hreal` from `real_zeros_below_zfrCeil`, `hZFR` from
`zero_free_region_all_numeral`, `250 ≤ L` from the regime, `σa = 9/10`, `σb = 19/20 ≤ β₀`) plus
`logChiSum_add` (`Lemma7EF.lean:1155`) moves the base point down to `z`.
Consumer: `hcorr_at_split`. -/
theorem hbEulerLog_tendsto [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {z : ℝ} (hz : 3 ≤ z) :
    ∃ A : ℝ, Tendsto (fun Y : ℝ => hbEulerLog χ z Y) atTop (𝓝 A) := by
  sorry

/-- **`hcorr` at the split point** — the bridge `hb_hcorr_closed` lacks: its `A′` is the limit of
`(logChiSum χ z Y).re`, while `(L2)` wants `(logChiSum χ z X).re + Stail.re`; `logChiSum_add`
(`Lemma7EF.lean:1155`) splits `[z, Y] = [z, X] ∪ [X, Y]` and the tail limit is `S`
(`hS`, produced by `logChiSum_tail_at_window` at `X = x`).  Class **B**, cap 200.
Consumer: `hb_L2_at_hb_point`. -/
theorem hcorr_at_split [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {z X : ℝ} (hz : 3 ≤ z) (hzX : z ≤ X)
    {S : ℂ} (hS : Tendsto (fun Y : ℝ => logChiSum χ X Y) atTop (𝓝 S)) :
    |Real.log (hbF χ z) - ((logChiSum χ z X).re + S.re)|
      ≤ 2 / (⌊z⌋₊ : ℝ) + 10 / Real.sqrt (⌊z⌋₊ : ℝ) := by
  sorry

/-- **The `(L2)` constant** (a ceiling): the `e^{250}` of the kill times the packet's `Cs`. -/
noncomputable def n9K2 : ℝ := Real.exp 260 * (802 + 4 * n9Cs)

/-- **`(L2)` AT HB's OPERATING POINT — N4's composition wave, as one row.**
`hb_L2_at_split_point_charTrio` at `X := x`, `z := hbZ − 1`, `L := log q`, with its six binders
paid: `hm1` ← `zeroMult_eq_one_of_eta` (`η ≥ 15000`, `hη` by `one_div`); `htail` ←
`logChiSum_tail_at_window` at `X = x ≥ q^250`; `hseg` ← `hb_hseg_closed` with `segC_spec` and
`chiOne_kill_at_hb_point`; `hcorr` ← `hcorr_at_split` with `hbEulerLog_tendsto` and the `S` of
`logChiSum_tail_at_window`; `hP` ← `merC_spec`; `hsmall` ← the ledger: `4·Etail ≤ 400/√(250L)`,
`4·Ekill ≤ 4e^{250}(802+4n9Cs)·2L/(√ℓ′·log z)` with `log z ≥ 10⁴L/log ℓ′` (the
`(e^{300}(802+4n9Cs))^8`-part of `n9E0` closes it — a square would), `8·EP = 8·merC/log z` and
`Eseg`'s `segC/log z` (the `e^{merC+segC}`-part of `n9E0`, with `L ≥ e^{401}ℓ′`), `2·64/z`.
Class **C**, cap 500 (the ledger is the risk).  The `δ`-bound's shape: `log ℓ′/√ℓ′` from the
kill (`L/log z ≤ z₀ = A·log ℓ′`), `1/√L` from `Etail`; the Mertens terms sit under the `1/√L`
shape with room `e^{401}`.  Consumer: `hb_S3_at_hb_point`. -/
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
`ε`; N9's star term needs `ε := 1/(2000·z₀)` — an `ℓ′`-dependent `ε` (⛔ NOT `1/(1000·z₀)`: there
`x^{2ε} ≤ q^{1/z₀} = z` eats the whole `2x/z` gain) — so `C` must be a FUNCTION of `ε` the
threshold can see.  The landed proof (`TauSpike.lean:92-104`) carries the witness
`g^{⌈2^{1/ε}⌉}` with `g = 1 + (ε·log 2)⁻¹ ≤ 3/ε` for `ε ≤ 1`, and the CEILING costs one more
factor (the verdict's A7: at `ε = 0.9` the ceiling-free `(3/ε)^{2^{1/ε}}` is FALSE as a
re-export), so the exponent carries `+ 1`.  Class **B**, cap 200: `Nat.ceil_lt_add_one`,
`pow_le_pow_left₀` twice, `Real.rpow_natCast`.  Consumer: `hb_lemma4_at_hb_point`. -/
theorem card_divisors_le_rpow_explicit {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ (3 / ε) ^ ((2 : ℝ) ^ (1 / ε) + 1) * (n : ℝ) ^ ε := by
  sorry

/-- **HB LEMMA 4 AT THE POINT: `|S⁽⁰⁾ − S⁽³⁾| ≤ 2^40·x/z₀`.**  Class **B**, cap 300.
Red-first: `hb_lemma4_l2cWindow` on `hbZ_packet` with `ε := 1/(2000·z₀)`, `C := (3/ε)^{2^{1/ε}}`
(`card_divisors_le_rpow_explicit`); then `lemma4Err` term by term: swap `2(ω(q)+z)·Lwin² ≤ x/z₀`
(`z ≤ q^{1/z₀}+1`, `ω(q) ≤ L/log 2` — NOT `≤ L`, false at `q = 6`); master-1 `2^31·x/(z0 z x)`
with `z0 z x = Lwin x/log z ≥ 250·z₀`; master-2 `2^31·(x/log x)·e^{5·z0}·PretenseSum ≤ x/z₀` —
`pretenseSum_at_hb_point`, `z0 z x ≤ 501·z₀`, `e^{2505·z₀} = ℓ′^{2505·hbZ0A} = ℓ′^{0.2505}`
(spell it `2505·hbZ0A`, not `1/4`, so the `rpow` arithmetic matches) against `1/√ℓ′`: THE
`A < 1/5000` INEQUALITY, closed by `n9E0`'s eighth power (margin `e^{347}`); master-3
`e^{2·z0}·(x/z^{1/8} + x^{9/10})·Lwin³ ≤ x/z₀` (`z^{1/8} = q^{1/(8z₀)}` beats `ℓ′^{1/10}·L³·z₀`);
star `2(C(2x+2)^ε log(2x+2))²·(2x/z + √(2x+2))` — `x^{2ε} ≤ q^{1/(2z₀)} = √(q^{1/z₀})` at
`ε = 1/(2000z₀)`, `C² = (6000z₀)^{2(2^{2000z₀}+1)}` with `2^{2000 z₀} = ℓ′^{0.1386}` beaten by
`q^{1/(2z₀)} = e^{5000·L/log ℓ′}` via `ηq` (room `L^{0.86}/log L`; the extra `+1` factor is one
more `6000·z₀`).  Consumer: `hb_theorem1`. -/
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
`kappa := hbKappaN9`, `LL := hbLL`, plus the two side conditions they demand that v1 omitted:
`hPα : Nat.Coprime (hbDataN8 …).P 4` (from `HBSieveData.P_odd`) and `hκ : 0 ≤ hbKappaN9 χ x z`
(no landed `hbKappa_nonneg`; build it from `hbWfac_pos`, `Lemma7Kappa.lean:307`, and the
multipliability at `:330`) — ~40 ln of the cap; `hbS1_eq_W` turns `κ·W` into `(L2)`'s left side
(`hb_L2_at_hb_point`); the two `(L1)` sides bound `LL² = (ηL)²(1 ± 2(1606+8n9Cs)/(η√ℓ′) + …)` —
the RELATIVE deviation is `η` times smaller than `1/√ℓ′` and belongs under the `1/η` shape —
and `B = L + |LL| ≤ 3ηL` (`η ≥ 2`); `n8ErrSum_le` prices the sieve error
`Cerr·x·L⁴/z·e^{4·mertens2C}(log z)⁴ ≤ x/z₀` (`e^{67.6}` against `log z ≥ 10⁴L/log ℓ′`); the
FL term `flConst(1/4)(Λ₄ z)·4^{−hbS}` with `flConst (1/4) (Lam4 (1/4) z) ≤ 14·e^{31}` by
`flConst_quarter_le` at the packet's last conjunct (`Λ₄ ≥ 1/10`); the `n8C6·B·L` term is
`≤ 3n8C6/η` relative; `CC ≥ 0` is NOT a `Lemma5Eval` field — derive it from `C₀_le` at
`L > 0` before using `n8C6 ≥ 0` / `n9K3 > 0`.  Every relative error is one of the four shapes in
the bound (verified exhaustive, K9).  Consumer: `hb_theorem1`. -/
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

    S1 (Ioc x (2x)) = 𝔖·C(4)·x·(1 + δ),   |δ| ≤ n9K/log ℓ′,   uniformly on q^250 ≤ x ≤ q^500,

CONDITIONALLY on N7's exit and on the regime (whose `ellBig` couples `η` to `log log q` through
the landed D–H's `dhK`; at HB's `k = 1`, `log ℓ′ = log log η + O(1)`).  Class **B**, cap 250.
Red-first: `hb_lemma4_at_hb_point` + `hb_S3_at_hb_point`; `2^40·x/z₀ = 2^40·x/(A·log ℓ′)`
(against `x𝔖C(4)`: `2^40/(2𝔖·hbZ0A)`, `hbCalpha 4 = 2`, `twinSingularSeries_pos`); the four
`δ₃` shapes are each `≤ 1/log ℓ′` in the regime (`√ℓ′ ≥ (log ℓ′)²` from `ellBig`; `√L ≥ log ℓ′`
from `ηq`; `η ≥ e^{ℓ′} ≥ log ℓ′`; `hbS ≥ z₀/3.01` so `4^{−hbS} ≤ ℓ′^{−A/2.2} ≤ 1/log ℓ′`), and
`n9K ≥ 4·n9K3·e^{0}`… precisely `n9K/log ℓ′ ≥ 4·n9K3·(1/log ℓ′)` needs the `e^{300}` of `n9K`
(A3) — without it the FL shape alone is `e^{140}` over budget at the regime's edge.
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
(`fulcrumQualityPoly_one_iff`).  The landed engine fires at `k = dhK = 14` (finding 2). -/
def FulcrumQualityPoly (C k : ℝ) : Prop :=
  ∀ Q : ℕ, ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    Q < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 : ℂ) - ρ‖ * (C * Real.log q ^ k) ≤ 1

/-- **No Siegel zeros at polylog strength `k`**: `β ≤ 1 − c/(log q)^k`.  At `k = 1` this is
`NoSiegelZeros` (`noSiegelZerosPoly_one_iff`); for `k ≤ k′` the `k` form implies the `k′` form
(`noSiegelZerosPoly_mono` — it needs `log q ≥ 1`, i.e. `3 ≤ q`, which `χ ≠ 1` supplies:
`three_le_of_ne_one`; at `q = 2` the polylog form would be STRICTLY STRONGER, vacuously).
Still open, still effective in form. -/
def NoSiegelZerosPoly (k : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    1 < q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ β : ℝ, DirichletCharacter.LFunction χ β = 0 → β < 1 →
      β ≤ 1 - c / Real.log q ^ k

/-- **THE CROWN FAMILY.**  `k = 1` is the frozen `HeathBrownDichotomy` (byte-untouched, in
`Salt/TwinBar/SiegelTwin.lean`; `heathBrownDichotomyPoly_one_iff`); the landed supply reaches
`k = dhK = 14`.  **The Captain's ruling (2026-09-04 12:39): the campaign's crown is the `k = 1`
member — HB's exactly — reached through Arm B (D–H re-proved at `k ≤ 1`, the next design block);
this file lands `k = 14` as the INTERMEDIATE member.** -/
def HeathBrownDichotomyPoly (k : ℝ) : Prop :=
  TwinPrimeConjecture ∨ NoSiegelZerosPoly k

/-- Class **A**, cap 30: `Real.rpow_one`. -/
theorem fulcrumQualityPoly_one_iff (C : ℝ) : FulcrumQualityPoly C 1 ↔ FulcrumQualityMin C := by
  sorry

/-- Class **A**, cap 30: `Real.rpow_one`. -/
theorem noSiegelZerosPoly_one_iff : NoSiegelZerosPoly 1 ↔ NoSiegelZeros := by
  sorry

/-- **The frozen crown IS the `k = 1` member** — the sentence made a theorem (the verdict's K12
note).  Class **A**, cap 20: `or_congr Iff.rfl noSiegelZerosPoly_one_iff`.
Consumer: the crown ruling (Arm B's target). -/
theorem heathBrownDichotomyPoly_one_iff : HeathBrownDichotomyPoly 1 ↔ HeathBrownDichotomy := by
  sorry

/-- **A non-trivial Dirichlet character has modulus `≥ 3`** (the verdict's A9): mod `1` and
mod `2` the only character is `1` (`(ZMod 2)ˣ` is trivial).  Class **A**, cap 30.
Consumer: `noSiegelZerosPoly_mono` (`log q ≥ 1`). -/
theorem three_le_of_ne_one [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : 3 ≤ q := by
  sorry

/-- **The family is monotone in `k`**: `c/(log q)^{k′} ≤ c/(log q)^k` for `k ≤ k′` once
`log q ≥ 1`.  This is the theorem behind "`Poly 14` is weaker than the frozen crown" (with
`noSiegelZerosPoly_one_iff` at `k = 1`).  Class **A**, cap 40: `three_le_of_ne_one`,
`Real.rpow_le_rpow_of_exponent_le`, `div_le_div_of_nonneg_left`.
Consumer: the crown ruling. -/
theorem noSiegelZerosPoly_mono {k k' : ℝ} (hk : 1 ≤ k) (hkk' : k ≤ k')
    (h : NoSiegelZerosPoly k) : NoSiegelZerosPoly k' := by
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
currency**: `1 − β₀ ≤ 1/(n9Cq·(log q)^{14})` puts `ℓ′ ≥ n9E0 + e^{2·n9K} + 1` (so `ellBig` and
`hK` hold): `ηL = 1/(1−β₀) ≥ C·L^{14}` gives `log(ηL) ≥ log C + 14·log L`, and
`14·log(log 4q + 2) ≤ 14·log L + 8.6` at `L ≥ 4`, so `ℓ′ ≥ log C − log(1/dhC) − 8.6`; the `/dhC`
here cancels the `−log(1/dhC)` exactly (the verdict's U1: `k = 14`, not `15`). -/
noncomputable def n9Cq (Cerr CA CA' CC : ℝ) : ℝ :=
  Real.exp (n9E0 + Real.exp (2 * n9K Cerr CA CA' CC) + 10) / dhC

/-- **THE HAND-OVER: from the polylog fulcrum to the door's hypothesis.**  Class **C**, cap 400.
Red-first: for `N`, take the witness at a `Q ≥ N` with `Real.exp 402 * (n9E0 + 1) ≤ Real.log Q`
(SYMBOLIC — the verdict's U2: `ellBig` + `ηq` force `L ≥ e^{402}·n9E0`, i.e.
`q ≥ exp(exp(3·10⁶ + 402))`, a tower level above v1's `e^{e^{70000}}`, and Siegel's `C(ε)` sits
on top of it); reality by `fulcrum_zero_real` with `zero_free_region_all_numeral`
(`c₀ = 1/126848`, `C·c₀ ≥ 2` from `n9Cq`; it takes `3 ≤ q` explicitly — `three_le_of_ne_one`);
the largest real zero by `beta0_max_of_zero` (its quality is at least the witness's); `ηq` from
`siegel_theorem` at `ε := e^{−402}` — INEFFECTIVE, absorbed into the `∃ x` (the threshold `Q` may
depend on Siegel's `C(ε)`; nothing here is claimed effective); the remaining regime fields from
the quality at `k = 14` (`n9Cq`'s docstring); `x := q^250`; `hb_theorem1_lower` with `hK` from
the quality; then `x𝔖C(4)/2 > 4√(2x+2)·log³(2x+2)` at `x ≥ q^250`.
Consumer: `hEngine_poly_of_N7`. -/
theorem crown_handover {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC)
    (hF : FulcrumQualityPoly (n9Cq Cerr CA CA' CC) 14) :
    ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧
      4 * Real.sqrt (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) ^ 3
        < S1 (Finset.Ioc x (2 * x)) := by
  sorry

/-- **THE ENGINE AT STRENGTH `14`, CONDITIONAL ON N7.**  Class **A**, cap 40:
`twinPrimeConjecture_of_frequently_S1 (crown_handover hN7 hF)`.  Consumer:
`heathBrownDichotomyPoly_of_N7`. -/
theorem hEngine_poly_of_N7 {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    FulcrumQualityPoly (n9Cq Cerr CA CA' CC) 14 → TwinPrimeConjecture := by
  sorry

/-- **THE INTERMEDIATE CROWN, AT THE STRENGTH THE LANDED SUPPLY REACHES, CONDITIONAL ON N7:
`TPC ∨ NoSiegelZerosPoly 14`.**  Stated at the LITERAL `14`, not at `dhK` (the verdict's U4: a
headline whose exponent is a mutable `def` in the same file would silently re-anchor if `dhK`
were ever edited).  The frozen crown is the `k = 1` member (`heathBrownDichotomyPoly_one_iff`);
reaching it is Arm B — a D–H contract at `k ≤ 1` (HB's Jutila form) — by the Captain's ruling.
Class **A**, cap 20.  Consumer: none yet — the intermediate crown row. -/
theorem heathBrownDichotomyPoly_of_N7 {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    HeathBrownDichotomyPoly 14 := by
  sorry

end Salt.HB
