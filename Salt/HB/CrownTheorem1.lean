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

**STATUS: FROZEN v3, the wave FIRING (2026-09-04; v1 `f13d09a3`; v2 `235d618b` on the helm's
12:38 refuter verdict — REPAIR-THEN-FIRE, 4/4 — with every kill repaired at the object, and on
the Captain's 12:39 ruling on the crown's statement; v3 on the desk's own finding 3 below, which
the wave's first hour surfaced).  Rows are `sorry`-bodied until their executor lands them.**
This file is the wave table for N9: each docstring carries the
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
   `k = 14` — before finding 3.  **The Captain ruled (2026-09-04 12:39): the crown is
   HEATH-BROWN's EXACTLY, `k = 1` (Arm B — re-prove D–H at `k ≤ 1`, the crown's next design
   block); the member this file reaches lands as the INTERMEDIATE member — `k = 30` after
   finding 3, not `14`.**
3. **`(L2)`'s six binders are not "every piece proved".**  `hcorr`'s producer needs `hlimP`
   (never produced — the CHAR-TRIO flag), `htail`'s only producer is the RANGE-B tail
   `logChiSum_tendsto_zfr_hundred`, whose threshold `X₀` is `q`-dependent and superpolynomial in
   `q` (the verdict's one FATAL: `log X₀ ≥ (log q + 7)²`, so NO `x ∈ [q^250, q^500]` clears it,
   ever — the Range-B ceiling decays only above `exp(20·L·log L/c₀)`), and a `hreal` binder with
   no producer; `hseg`'s feeder carries the same zero-side antecedents as `(L1)`.  §4 books each
   as a row; the tail is built here at the REPULSION ceiling (Range A, `C2`), where the decay is
   real from `q^250` on.
4. **THE TAIL CARRIES A `k`-INDEPENDENT POWER OF `log q`, AND THE REGIME MUST PAY IT (v3).**  The
   Range-A ledger's row (iv) is `10³·M³·N·u^{bceil−1}` (`efEnvelope_le_ledger_sharp`,
   `Lemma7EF.lean:2624-2632`; `M = log(qu)+2 ≈ 251·L` at `u = q^250`, `N ≈ L`) — the CRUDE zero
   count of the near-1 strip (`DensityCrude.lean:459`: on `16/17 < σ ≤ 1` the density shape
   degenerates and `N(σ,T) ≤` the count, polylog in `L`) — against the repulsion decay
   `exp(−0.368·ℓ′)` at the window edge.  The grade needs `exp(0.368·ℓ′) ≥ 10^{10}·L^{4.5}`, i.e.
   `ℓ′ ≥ 74 + 12.2·log L` (`12.2 = 4.5·b/250` at `b = 680`).  A CONSTANT threshold on `ℓ′` cannot
   supply it: the regime bounds `L` only from below (`ηq`), so the corner `ℓ′ = n9E0`, `L → ∞` is
   inside it and there v2's C2 was unreachable (the 08/06 TAU-SHARP refuter's K3(c)2,
   `flags.md:20655-20662`, had named this term: "the lever is `b/s`, not `k`").  HB has no such
   term because at p.209 he prices the block by Jutila's LOG-FREE density (4.9) shell by shell
   ("using `q^{15/2} ≤ x^{1/4}`" is that sum); our N2 is the crude count there by design.  The
   repair: the regime field `ellL : n9E0 + 16·log log(4q) ≤ ℓ′` (16 = 12.2 + room), which the
   polylog quality supplies only at `k = 14 + 16 = 30` — so the intermediate crown is
   `HeathBrownDichotomyPoly 30`.  Every other row is `L`-free at a constant `ℓ′` (checked: Z6, Z8,
   Z11, `hsmall`'s four terms, the star term, the FL term).  For Arm B this means `k = 1` needs
   BOTH a `k ≤ 1` contract AND a log-free density on the near-1 strip (class D, both).
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
`HeathBrownDichotomyPoly 30`, conditional on N7 (the `16` of `ellL` on top of the D–H `14`); the
frozen `HeathBrownDichotomy` (`k = 1`) is NOT reached here — it is Arm B's, the next design
block, and needs a log-free near-1 density as well as a `k ≤ 1` contract.  Nothing here bears on
twin primes; `hEngine` stays a binder until N7, the rows here, and Arm B land.
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
  quality `1 − β₀ ≤ 1/(C·(log q)^{14})` it is a threshold on `C`; from `FulcrumQualityMin C`
  (`k = 1`) it is NOT reachable — freeze §5;
* `ellL` — **THE TAIL'S OWN DEMAND (finding 4)**: `ℓ′ ≥ n9E0 + 16·log log(4q)`, the price of the
  crude near-1 zero count in `logChiSum_tail_at_window`'s row (iv); implies `ellBig`
  (`log(4q) > 1`).  The polylog quality supplies it at `k = 30` and at no smaller `k`.
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
  ellL : n9E0 + 16 * Real.log (Real.log (4 * (q : ℝ))) ≤ n9Ell q η

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

/-- `log t ≤ t/M` once `t ≥ 4M²`: `t ≤ (t/2M + 1)² ≤ exp(t/M)`.  The one largeness step
the `z` packet needs, used at `M = 2`, `M = e^{10⁶}`. -/
private lemma n9_log_le_div {t M : ℝ} (hM : 0 < M) (ht : 4 * M ^ 2 ≤ t) :
    Real.log t ≤ t / M := by
  have hMne : M ≠ 0 := ne_of_gt hM
  have hMsq : (0 : ℝ) < 4 * M ^ 2 := by positivity
  have htpos : 0 < t := lt_of_lt_of_le hMsq ht
  have hu : (0 : ℝ) ≤ t / (2 * M) := by positivity
  have hexp : t / (2 * M) + 1 ≤ Real.exp (t / (2 * M)) := Real.add_one_le_exp _
  have hsq : Real.exp (t / M) = Real.exp (t / (2 * M)) * Real.exp (t / (2 * M)) := by
    rw [← Real.exp_add]; ring_nf
  have hprod : (t / (2 * M) + 1) * (t / (2 * M) + 1) ≤ Real.exp (t / M) := by
    rw [hsq]
    exact mul_le_mul hexp hexp (by linarith only [hu]) (Real.exp_pos _).le
  have hid : t / (2 * M) * (t / (2 * M)) = t * t / (4 * M ^ 2) := by
    field_simp; ring
  have h2 : t * (4 * M ^ 2) ≤ t * t := mul_le_mul_of_nonneg_left ht htpos.le
  have h3 : t ≤ t * t / (4 * M ^ 2) := by
    rw [le_div_iff₀ hMsq]; linarith only [h2]
  have hkey : t ≤ (t / (2 * M) + 1) * (t / (2 * M) + 1) := by
    nlinarith only [hid, h3, hu]
  have h := Real.log_le_log htpos (le_trans hkey hprod)
  rwa [Real.log_exp] at h

/-- `log T ≤ log Y` transports to `T ≤ Y` on the positives. -/
private lemma n9_le_of_log_le {T Y : ℝ} (hT : 0 < T) (hY : 0 < Y)
    (h : Real.log T ≤ Real.log Y) : T ≤ Y := by
  have h2 := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hT, Real.exp_log hY] at h2

/-- The regime facts the `z` packet needs, derived here because §3's `n9_two_le_q` and
`n9_num_facts` come LATER in the file: `q ≥ 2`, `L > 0`, `ℓ′ ≥ e^{3·10⁶}`, `e^{3·10⁶} ≤ 2L`
(so `L` is astronomically large), and `log ℓ′ ≤ log L` (from `ℓ′ ≤ L`). -/
private lemma n9_z_regime [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    (2 : ℝ) ≤ (q : ℝ) ∧ 0 < Real.log q ∧ Real.exp (3 * 10 ^ 6) ≤ n9Ell q η
      ∧ Real.exp (3 * 10 ^ 6) ≤ 2 * Real.log q
      ∧ Real.log (n9Ell q η) ≤ Real.log (Real.log q) := by
  have hdhCpos := dh_spec.1
  have hdhC1 := dh_spec.2.1
  have hinv : 0 ≤ Real.log (1 / dhC) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hEll : Real.exp (3 * 10 ^ 6) ≤ n9Ell q η := le_trans hE0 hR.ellBig
  have hEllpos : 0 < n9Ell q η := lt_of_lt_of_le (Real.exp_pos _) hEll
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
    rcases Nat.lt_or_ge q 2 with hlt | hge
    · exfalso
      have hq1 : q = 1 := by have := Nat.pos_of_ne_zero (NeZero.ne q); omega
      have hqR : ((q : ℕ) : ℝ) = 1 := by rw [hq1]; norm_num
      have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have hpos : 0 < Real.log (Real.log 4 + 2) := Real.log_pos (by linarith)
      have hdk : dhK = 14 := rfl
      have hEneg : n9Ell q η < 0 := by
        simp only [n9Ell, hqR, Real.log_one, mul_zero, Real.log_zero, mul_one, hdk]
        linarith
      linarith
    · exact_mod_cast hge
  have hL : 0 < Real.log q := Real.log_pos (by linarith)
  have hβpos : 0 < 1 - β₀ := by have := hR.β1; linarith
  have hηL : η * Real.log q = 1 / (1 - β₀) := by rw [hR.ηdef]; field_simp
  have hηLpos : 0 < η * Real.log q := by rw [hηL]; positivity
  have hηpos : 0 < η := by
    rcases lt_or_ge 0 η with h | h
    · exact h
    · exact absurd hηLpos (not_lt.mpr (by nlinarith))
  have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
    Real.log_mul (ne_of_gt hηpos) (ne_of_gt hL)
  have hXnn : 0 ≤ dhK * Real.log (Real.log (4 * (q : ℝ)) + 2) := by
    have hlog4q : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
    have h : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) := Real.log_nonneg (by linarith)
    have hdk : dhK = 14 := rfl
    rw [hdk]; linarith
  have hEllub : n9Ell q η ≤ Real.log η + Real.log (Real.log q) := by
    simp only [n9Ell]; linarith
  have he401 : (2 : ℝ) ≤ Real.exp 401 := by
    have h := Real.add_one_le_exp (401 : ℝ); linarith only [h]
  have hηq := hR.ηq
  have hlogη2 : Real.log η ≤ Real.log q / 2 := by
    rcases le_or_gt 0 (Real.log η) with h | h
    · nlinarith only [hηq, he401, h, hL]
    · linarith only [h, hL]
  have hlogLsub : Real.log (Real.log q) ≤ Real.log q - 1 := Real.log_le_sub_one_of_pos hL
  have hLhuge : Real.exp (3 * 10 ^ 6) ≤ 2 * Real.log q := by
    linarith only [hEll, hEllub, hlogη2, hlogLsub, hL]
  have h16 : 4 * (2 : ℝ) ^ 2 ≤ Real.log q := by
    have h := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    linarith only [h, hLhuge]
  have hlogLhalf : Real.log (Real.log q) ≤ Real.log q / 2 :=
    n9_log_le_div (by norm_num) h16
  have hEllleL : n9Ell q η ≤ Real.log q := by
    linarith only [hEllub, hlogη2, hlogLhalf]
  exact ⟨hq2, hL, hEll, hLhuge, Real.log_le_log hEllpos hEllleL⟩

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
  obtain ⟨hqR, hL, hEll, hLhuge, hPleL⟩ := n9_z_regime hR
  have hEllpos : 0 < n9Ell q η := lt_of_lt_of_le (Real.exp_pos _) hEll
  have hLnum : (1500000 : ℝ) ≤ Real.log q := by
    have h := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    linarith only [h, hLhuge]
  have hPlog : (3 : ℝ) * 10 ^ 6 ≤ Real.log (n9Ell q η) := by
    have h := Real.log_le_log (Real.exp_pos (3 * 10 ^ 6 : ℝ)) hEll
    rwa [Real.log_exp] at h
  have hPpos : 0 < Real.log (n9Ell q η) := by linarith only [hPlog]
  have hPne : Real.log (n9Ell q η) ≠ 0 := ne_of_gt hPpos
  -- `z₀ = 10⁻⁴·log ℓ′ ≥ 300`, and the exponent `W = L/z₀`, kept opaque
  have hz0 : hbZ0 q η = 1 / 10000 * Real.log (n9Ell q η) := by
    simp only [hbZ0, hbZ0A]
  have hz0pos : 0 < hbZ0 q η := by rw [hz0]; linarith only [hPpos]
  have hz0ne : hbZ0 q η ≠ 0 := ne_of_gt hz0pos
  have hz0ge : (300 : ℝ) ≤ hbZ0 q η := by rw [hz0]; linarith only [hPlog]
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Real.log q / hbZ0 q η := ⟨_, rfl⟩
  have hWpos : 0 < W := by rw [hWdef]; exact div_pos hL hz0pos
  have hWz0 : W * hbZ0 q η = Real.log q := by rw [hWdef]; field_simp
  have hWP : W * Real.log (n9Ell q η) = 10000 * Real.log q := by
    have hPz0 : Real.log (n9Ell q η) = 10000 * hbZ0 q η := by rw [hz0]; ring
    rw [hPz0]
    calc W * (10000 * hbZ0 q η) = 10000 * (W * hbZ0 q η) := by ring
      _ = 10000 * Real.log q := by rw [hWz0]
  have hWle : W ≤ Real.log q / 300 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 300)]
    have h := mul_le_mul_of_nonneg_left hz0ge hWpos.le
    linarith only [h, hWz0]
  -- `log L ≤ L/e^{10⁶}`, hence `W ≥ 10⁴·e^{10⁶}`
  have hMpos : (0 : ℝ) < Real.exp (10 ^ 6 : ℝ) := Real.exp_pos _
  have hexp1 : (1000001 : ℝ) ≤ Real.exp (10 ^ 6 : ℝ) := by
    have h := Real.add_one_le_exp (10 ^ 6 : ℝ); linarith only [h]
  have hMle : 4 * Real.exp (10 ^ 6 : ℝ) ^ 2 ≤ Real.log q := by
    have hsq : Real.exp (10 ^ 6 : ℝ) ^ 2 = Real.exp (2 * 10 ^ 6 : ℝ) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have h2pos : (0 : ℝ) < Real.exp (2 * 10 ^ 6 : ℝ) := Real.exp_pos _
    have hmul : Real.exp (10 ^ 6 : ℝ) * Real.exp (2 * 10 ^ 6 : ℝ)
        = Real.exp (3 * 10 ^ 6 : ℝ) := by
      rw [← Real.exp_add]; ring_nf
    have hprod : 1000001 * Real.exp (2 * 10 ^ 6 : ℝ)
        ≤ Real.exp (10 ^ 6 : ℝ) * Real.exp (2 * 10 ^ 6 : ℝ) :=
      mul_le_mul_of_nonneg_right hexp1 h2pos.le
    rw [hmul] at hprod
    rw [hsq]
    linarith only [hprod, hLhuge, h2pos]
  have hlogL : Real.log (Real.log q) ≤ Real.log q / Real.exp (10 ^ 6 : ℝ) :=
    n9_log_le_div hMpos hMle
  have hPL : Real.exp (10 ^ 6 : ℝ) * Real.log (n9Ell q η) ≤ Real.log q := by
    have h1 : Real.log (n9Ell q η) ≤ Real.log q / Real.exp (10 ^ 6 : ℝ) :=
      le_trans hPleL hlogL
    rw [le_div_iff₀ hMpos] at h1
    linarith only [h1]
  have hWbig : 10000 * Real.exp (10 ^ 6 : ℝ) ≤ W := by
    have hmul : 10000 * Real.exp (10 ^ 6 : ℝ) * Real.log (n9Ell q η)
        ≤ W * Real.log (n9Ell q η) := by
      rw [hWP]; linarith only [hPL]
    exact le_of_mul_le_mul_right hmul hPpos
  have hWhuge : (1000000 : ℝ) ≤ W := by linarith only [hWbig, hexp1, hMpos]
  -- `z` brackets `exp W`
  obtain ⟨hzlo, hzhi⟩ := hbZ_bounds q η hz0pos
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith only [hqR]
  have hrp : (q : ℝ) ^ (1 / hbZ0 q η) = Real.exp W := by
    rw [hWdef, Real.rpow_def_of_pos hqpos, mul_one_div]
  have hzge : Real.exp W ≤ (hbZ q η : ℝ) := by rw [← hrp]; exact hzlo
  have hzpos : (0 : ℝ) < (hbZ q η : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hzge
  have hzhi' : (hbZ q η : ℝ) < Real.exp W + 1 := by rw [← hrp]; exact hzhi
  have hzle : (hbZ q η : ℝ) ≤ Real.exp (W + 1) := by
    have hE : (1 : ℝ) ≤ Real.exp W := by
      have h := Real.add_one_le_exp W
      linarith only [h, hWpos]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ); linarith only [h]
    rw [Real.exp_add]
    nlinarith only [hzhi', hE, he1]
  have hlogzge : W ≤ Real.log (hbZ q η : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hzge
    rwa [Real.log_exp] at h
  have hlogzle : Real.log (hbZ q η : ℝ) ≤ W + 1 := by
    have h := Real.log_le_log hzpos hzle
    rwa [Real.log_exp] at h
  have hlogzpos : 0 < Real.log (hbZ q η : ℝ) := lt_of_lt_of_le hWpos hlogzge
  -- (1) `2 ≤ z`
  have hlog2z : Real.log 2 ≤ Real.log (hbZ q η : ℝ) := by
    have hl2 := Real.log_two_lt_d9
    linarith only [hl2, hlogzge, hWhuge]
  have hz2R : (2 : ℝ) ≤ (hbZ q η : ℝ) := n9_le_of_log_le (by norm_num) hzpos hlog2z
  have hz2 : 2 ≤ hbZ q η := by exact_mod_cast hz2R
  -- (2) `100^16 ≤ z`
  have hlog100 : Real.log ((100 : ℝ) ^ 16) ≤ Real.log (hbZ q η : ℝ) := by
    have h1 : Real.log ((100 : ℝ) ^ 16) = 16 * Real.log 100 := by
      rw [Real.log_pow]; push_cast; ring
    have h2 : Real.log (100 : ℝ) ≤ 99 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100)
      linarith only [h]
    linarith only [h1, h2, hlogzge, hWhuge]
  have hz100R : ((100 : ℝ)) ^ 16 ≤ (hbZ q η : ℝ) :=
    n9_le_of_log_le (by positivity) hzpos hlog100
  have hz100 : 100 ^ 16 ≤ hbZ q η := by
    have hcast : (((100 ^ 16 : ℕ)) : ℝ) ≤ (hbZ q η : ℝ) := by
      push_cast; linarith only [hz100R]
    exact_mod_cast hcast
  have hzhuge : (33 : ℝ) ≤ (hbZ q η : ℝ) := by
    have h : (33 : ℝ) ≤ (100 : ℝ) ^ 16 := by norm_num
    linarith only [h, hz100R]
  -- the window, and `log L ≤ 2√L`
  have hx0 : (1 : ℝ) ≤ (x : ℝ) := by
    have hq250 : (1 : ℝ) ≤ (q : ℝ) ^ 250 := one_le_pow₀ (by linarith only [hqR])
    linarith only [hx, hq250]
  have hsqrtL : Real.log (Real.log q) ≤ 2 * Real.sqrt (Real.log q) := by
    have hs : 0 < Real.sqrt (Real.log q) := Real.sqrt_pos.mpr hL
    have h1 : Real.log (Real.sqrt (Real.log q)) = Real.log (Real.log q) / 2 :=
      Real.log_sqrt hL.le
    have h2 : Real.log (Real.sqrt (Real.log q)) ≤ Real.sqrt (Real.log q) - 1 :=
      Real.log_le_sub_one_of_pos hs
    linarith only [h1, h2]
  have hkeyLL : (4008 + 8 * Real.log (Real.log q)) * Real.log (Real.log q)
      ≤ 10000 * Real.log q := by
    have hs : 0 < Real.sqrt (Real.log q) := Real.sqrt_pos.mpr hL
    have hss : Real.sqrt (Real.log q) * Real.sqrt (Real.log q) = Real.log q :=
      Real.mul_self_sqrt hL.le
    have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.log q) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith only [hLnum])
    have hX0 : (0 : ℝ) ≤ Real.log (Real.log q) :=
      Real.log_nonneg (by linarith only [hLnum])
    have hp1 : Real.log (Real.log q) * Real.log (Real.log q)
        ≤ 2 * Real.sqrt (Real.log q) * (2 * Real.sqrt (Real.log q)) :=
      mul_le_mul hsqrtL hsqrtL hX0 (by linarith only [hs])
    have hp2 : Real.sqrt (Real.log q) * 1
        ≤ Real.sqrt (Real.log q) * Real.sqrt (Real.log q) :=
      mul_le_mul_of_nonneg_left hs1 hs.le
    linarith only [hp1, hp2, hss, hsqrtL, hX0]
  -- (3) `Lwin x ^ 8 ≤ z`
  have hLwin0 : 0 ≤ Lwin x := by
    rw [Lwin]; exact Real.log_nonneg (by linarith only [hx0])
  have hLwinle : Lwin x ≤ 502 * Real.log q := by
    have hq500 : (1 : ℝ) ≤ (q : ℝ) ^ 500 := one_le_pow₀ (by linarith only [hqR])
    have h1 : 2 * (x : ℝ) + 2 ≤ 4 * (q : ℝ) ^ 500 := by linarith only [hx', hq500]
    have h2 : Real.log (2 * (x : ℝ) + 2) ≤ Real.log (4 * (q : ℝ) ^ 500) :=
      Real.log_le_log (by linarith only [hx0]) h1
    have h3 : Real.log (4 * (q : ℝ) ^ 500) = Real.log 4 + 500 * Real.log q := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have h4 : Real.log (4 : ℝ) ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith only [h]
    rw [Lwin]
    linarith only [h2, h3, h4, hLnum]
  have hzLwin : Lwin x ^ 8 ≤ (hbZ q η : ℝ) := by
    have hlog502 : Real.log (502 * Real.log q) ≤ 501 + Real.log (Real.log q) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hL)]
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 502)
      linarith only [h]
    have hX0 : (0 : ℝ) ≤ Real.log (Real.log q) :=
      Real.log_nonneg (by linarith only [hLnum])
    have h1 : 8 * Real.log (502 * Real.log q) ≤ 4008 + 8 * Real.log (Real.log q) := by
      linarith only [hlog502]
    have hA : 8 * Real.log (502 * Real.log q) * Real.log (n9Ell q η)
        ≤ (4008 + 8 * Real.log (Real.log q)) * Real.log (n9Ell q η) :=
      mul_le_mul_of_nonneg_right h1 hPpos.le
    have hB : (4008 + 8 * Real.log (Real.log q)) * Real.log (n9Ell q η)
        ≤ (4008 + 8 * Real.log (Real.log q)) * Real.log (Real.log q) :=
      mul_le_mul_of_nonneg_left hPleL (by linarith only [hX0])
    have hstep : 8 * Real.log (502 * Real.log q) ≤ W := by
      have hmul : 8 * Real.log (502 * Real.log q) * Real.log (n9Ell q η)
          ≤ W * Real.log (n9Ell q η) := by
        rw [hWP]; linarith only [hA, hB, hkeyLL]
      exact le_of_mul_le_mul_right hmul hPpos
    have hpow : Real.log ((502 * Real.log q) ^ 8) = 8 * Real.log (502 * Real.log q) := by
      rw [Real.log_pow]; push_cast; ring
    have hpowle : (502 * Real.log q) ^ 8 ≤ (hbZ q η : ℝ) := by
      refine n9_le_of_log_le (by positivity) hzpos ?_
      rw [hpow]
      linarith only [hstep, hlogzge]
    have hLw : Lwin x ^ 8 ≤ (502 * Real.log q) ^ 8 :=
      pow_le_pow_left₀ hLwin0 hLwinle 8
    linarith only [hLw, hpowle]
  -- (4) `z³ ≤ x`
  have hz3 : (hbZ q η : ℝ) ^ 3 ≤ (x : ℝ) := by
    refine n9_le_of_log_le (by positivity) (by linarith only [hx0]) ?_
    have h1 : Real.log ((hbZ q η : ℝ) ^ 3) = 3 * Real.log (hbZ q η : ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    have h2 : Real.log ((q : ℝ) ^ 250) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by positivity) hx
    have h3 : Real.log ((q : ℝ) ^ 250) = 250 * Real.log q := by
      rw [Real.log_pow]; push_cast; ring
    rw [h1]
    linarith only [h2, h3, hlogzle, hWle, hLnum]
  -- (5) `zThresh (1/4) ≤ z`
  have hexp400 : Real.exp (400 : ℝ) ≤ Real.log (hbZ q η : ℝ) := by
    have h1 : Real.exp (400 : ℝ) ≤ Real.exp (10 ^ 6 : ℝ) :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith only [h1, hMpos, hWbig, hlogzge]
  have hzThresh : zThresh (1 / 4 : ℝ) ≤ (hbZ q η : ℝ) := by
    have hzt : zThresh (1 / 4 : ℝ) = Real.exp (Real.exp 400) := by
      rw [zThresh]; norm_num
    rw [hzt]
    have h := Real.exp_le_exp.mpr hexp400
    rwa [Real.exp_log hzpos] at h
  -- (8) the sieve level is an identity
  have hSeq : 3 * hbS q η * Real.log (hbZ q η : ℝ) = Real.log q := by
    rw [hbS]; field_simp
  -- (9)/(11) the ladder scale and the level
  have hSge : (99 : ℝ) ≤ hbS q η := by
    rw [hbS, le_div_iff₀ (by linarith only [hlogzpos])]
    linarith only [hlogzle, hWle, hLnum]
  have hloglogz : (10 ^ 6 : ℝ) ≤ Real.log (Real.log (hbZ q η : ℝ)) := by
    have h1 : Real.exp (10 ^ 6 : ℝ) ≤ Real.log (hbZ q η : ℝ) := by
      linarith only [hMpos, hWbig, hlogzge]
    have h3 := Real.log_le_log (Real.exp_pos (10 ^ 6 : ℝ)) h1
    rwa [Real.log_exp] at h3
  have hLam4 : (1 : ℝ) / 10 ≤ Lam4 (1 / 4) (hbZ q η : ℝ) := by
    have hllpos : (0 : ℝ) < Real.log (Real.log (hbZ q η : ℝ)) := by
      linarith only [hloglogz]
    have h1 : 300 / Real.log (Real.log (hbZ q η : ℝ)) ≤ 300 / 10 ^ 6 := by
      rw [div_le_div_iff₀ hllpos (by norm_num)]
      linarith only [hloglogz]
    have h2 : (0 : ℝ) ≤ 300 / Real.log (Real.log (hbZ q η : ℝ)) := by positivity
    rw [Lam4]
    linarith only [h1, h2]
  have hlevel : levelE (Lam4 (1 / 4) (hbZ q η : ℝ)) + 2 ≤ hbS q η := by
    have h1 : levelE (Lam4 (1 / 4) (hbZ q η : ℝ)) ≤ levelE (1 / 10 : ℝ) :=
      levelE_anti (by norm_num) hLam4
    have h2 := levelE_tenth_le
    linarith only [h1, h2, hSge]
  exact ⟨hz2, hz100, hzLwin, hz3, hzThresh, by linarith only [hzhuge],
    by linarith only [hzhuge], le_of_eq hSeq, hlevel, by linarith only [hzhuge], hLam4⟩

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
  obtain ⟨hqR, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  obtain ⟨-, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hb1 := hR.β1
  have hPpos : 0 < n9Ell q η := by linarith only [hPbig]
  have hLp : (0 : ℝ) < 2 * Real.log q := by linarith only [hL]
  have hdhB : dhB = 680 := rfl
  -- `η ≥ 15000`, so M-ONE pins the multiplicity
  have hηbig' : (15000 : ℝ) ≤ η := by
    have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
      have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
      have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
      simp only [n9E0]; linarith
    have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    have hlogη : (15000 : ℝ) ≤ Real.log η := by linarith only [hηbig, hE0, hE1]
    have h := Real.exp_le_exp.mpr hlogη
    rw [Real.exp_log hηpos] at h
    have := Real.add_one_le_exp (15000 : ℝ)
    linarith only [h, this]
  have hm1 : Salt.SW.zeroMult χ ((β₀ : ℝ) : ℂ) = 1 :=
    zeroMult_eq_one_of_eta hR.prim hR.ne hR.zero (by rw [hR.ηdef, one_div]) hηbig'
  -- `√ℓ′` facts and the proximity condition at the floor
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n9Ell q η) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith only [hPbig])
  have hsnn : (0 : ℝ) ≤ Real.sqrt (n9Ell q η) := Real.sqrt_nonneg _
  have hsmul : Real.sqrt (n9Ell q η) * Real.sqrt (n9Ell q η) = n9Ell q η :=
    Real.mul_self_sqrt hPpos.le
  have hs2L : Real.sqrt (n9Ell q η) ≤ 2 * Real.log q := by
    nlinarith only [hsmul, hPsmall, hs1, hL, hsnn]
  have hs1360 : (1360 : ℝ) ≤ Real.sqrt (n9Ell q η) := by
    nlinarith only [hsmul, hPbig, hs1, hsnn]
  have hr0eq : n9Floor q η = n9Ell q η / (680 * Real.log (4 * (q : ℝ))) := by
    rw [n9Floor, hdhB]
  have hr0pos : 0 < n9Floor q η := by
    rw [hr0eq]; exact div_pos hPpos (by linarith only [hWpos])
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
  -- the second abscissa
  have hd0 : (0 : ℝ) < Real.sqrt (n9Ell q η) / (2 * Real.log q) := by positivity
  have hσ'1 : (1 : ℝ) < 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q) := by linarith only [hd0]
  have hσ'2 : 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q) ≤ 2 := by
    have h : Real.sqrt (n9Ell q η) / (2 * Real.log q) ≤ 1 := by
      rw [div_le_one hLp]; linarith only [hs2L]
    linarith only [h]
  -- the zero packet
  obtain ⟨Z, m, hZ, hZall, hmult, hdiff, hfloor, hSinv⟩ := hb_zero_data hR
  have hβball : ((β₀ : ℝ) : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : ((β₀ : ℝ) : ℂ) - 2 = ((β₀ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith only [hβhalf], by linarith only [hb1]⟩
  obtain ⟨hβZ, hmβ⟩ := hZall ((β₀ : ℝ) : ℂ) hβball hR.zero
  have hrem := hdiff 1 (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) le_rfl (by norm_num)
    hσ'1.le hσ'2
  have habs : |(1 : ℝ) - (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))|
      = (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) - 1 := by
    rw [abs_of_nonpos (by linarith only [hd0])]; ring
  rw [habs] at hrem
  have hs'top := neg_re_logDeriv_LFunction_le χ hσ'1 hσ'2
  have hmain := neg_re_logDeriv_differenced_mult
    (Lf := DirichletCharacter.LFunction χ) (Z := Z) (m := m)
    (σ := 1) (σ' := 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) (β₀ := β₀)
    (r0 := n9Floor q η) (Sinv := n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η))
    le_rfl (by linarith only [hd0]) hb1 hβZ hr0pos (by linarith only [hr0pos])
    (by linarith only [hσ'r]) hfloor hSinv hrem hs'top
  rw [Complex.ofReal_one] at hmain
  have hmzeq : (m ((β₀ : ℝ) : ℂ) : ℝ) = 1 := by
    have h := hmult ((β₀ : ℝ) : ℂ) hβZ
    rw [hm1] at h
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  rw [hmzeq] at hmain
  -- the error collapse
  have hCsnn : (0 : ℝ) ≤ n9Cs := by
    have hA := invSqC_spec.1
    have hprod : (0 : ℝ) ≤ invSqC * (dhB ^ 2 + dhB) :=
      mul_nonneg hA.le (by rw [hdhB]; norm_num)
    simp only [n9Cs]; linarith only [hprod]
  have hcol := l1_error_collapse (Lp := 2 * Real.log q) (ell := n9Ell q η)
    (Sinv := n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η)) (Cs := n9Cs)
    (CR := 1600 * Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q)))
    (mβ := 1) (β₀ := β₀)
    (by linarith only [hPbig]) (by linarith only [hPsmall, hL]) hCsnn (by norm_num) hb1
    le_rfl hCR
  -- the pole, in the `η` currency
  have hpole : (1 : ℝ) / (1 - β₀) = η * Real.log q := hηL.symm
  have hneg : (-logDeriv (DirichletCharacter.LFunction χ) (1 : ℂ)).re = -hbLL χ := by
    simp [hbLL]
  rw [hneg] at hmain
  have hrate : (802 + 1 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η))
      = (1606 + 8 * n9Cs) * (Real.log q / Real.sqrt (n9Ell q η)) := by ring
  linarith only [hmain, hcol, hpole, hrate]

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
  classical
  have hσ'1 : (1 : ℝ) ≤ σ' := le_trans hσ1 hlt
  have hdβ : (0 : ℝ) < σ - β₀ := by linarith
  have hdβ' : (0 : ℝ) < σ' - β₀ := by linarith
  set S : ℝ := (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ)).re with hS
  set S' : ℝ := (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ)).re with hS'
  set A : ℝ := (logDeriv Lf (σ : ℂ)).re with hA
  set A' : ℝ := (logDeriv Lf (σ' : ℂ)).re with hA'
  have hproj : (A - S) - (A' - S') ≤ Rrem := by
    refine le_trans ?_ hrem
    have habs := Complex.abs_re_le_norm
      ((logDeriv Lf (σ : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
        - (logDeriv Lf (σ' : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ)))
    have hre : ((logDeriv Lf (σ : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) - ρ))
        - (logDeriv Lf (σ' : ℂ) - ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ' : ℂ) - ρ))).re
        = (A - S) - (A' - S') := by
      simp [hA, hA', hS, hS']
    rw [hre] at habs
    linarith [(abs_le.mp habs).2]
  have hsumre : ∀ τ : ℝ, (∑ ρ ∈ Z, (m ρ : ℂ) / ((τ : ℂ) - ρ)).re
      = ∑ ρ ∈ Z, ((m ρ : ℂ) / ((τ : ℂ) - ρ)).re := by
    intro τ; exact Complex.re_sum Z _
  have hdiff : S' - S = ∑ ρ ∈ Z,
      (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re) := by
    rw [hS, hS', hsumre σ, hsumre σ', ← Finset.sum_sub_distrib]
  have hsplit : ∑ ρ ∈ Z, (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re)
      = ((((m (β₀ : ℂ)) : ℂ) / ((σ' : ℂ) - (β₀ : ℂ))).re
          - (((m (β₀ : ℂ)) : ℂ) / ((σ : ℂ) - (β₀ : ℂ))).re)
        + ∑ ρ ∈ Z.erase ((β₀ : ℂ)),
            (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re) :=
    (Finset.add_sum_erase Z _ hβZ).symm
  have hβreal : ∀ τ : ℝ, 0 < τ - β₀ →
      (((m (β₀ : ℂ)) : ℂ) / ((τ : ℂ) - (β₀ : ℂ))).re = (m (β₀ : ℂ) : ℝ) / (τ - β₀) := by
    intro τ _
    have hc : ((τ : ℂ) - (β₀ : ℂ)) = (((τ - β₀ : ℝ)) : ℂ) := by push_cast; ring
    rw [hc, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  have hβterm : (((m (β₀ : ℂ)) : ℂ) / ((σ' : ℂ) - (β₀ : ℂ))).re
      - (((m (β₀ : ℂ)) : ℂ) / ((σ : ℂ) - (β₀ : ℂ))).re
      = (m (β₀ : ℂ) : ℝ) / (σ' - β₀) - (m (β₀ : ℂ) : ℝ) / (σ - β₀) := by
    rw [hβreal σ' hdβ', hβreal σ hdβ]
  -- the remaining zeros, in ABSOLUTE value (the mirror needs the lower half)
  have hstep : ∀ ρ ∈ Z.erase ((β₀ : ℂ)),
      |((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re|
        ≤ 4 * (σ' - σ) * ((m ρ : ℝ) / ‖ρ - 1‖ ^ 2) := by
    intro ρ hρ
    have hfl := hfloor ρ hρ
    have hρ0 : 0 < ‖ρ - 1‖ := lt_of_lt_of_le hr0 hfl
    have hnorm := per_zero_inv_diff_le (σ := σ) (σ' := σ') (r0 := r0) (ρ := ρ)
      hσ1 hlt hσr hσ'r hr0 hfl
    have heq : ((m ρ : ℂ) / ((σ' : ℂ) - ρ)) - ((m ρ : ℂ) / ((σ : ℂ) - ρ))
        = -((m ρ : ℂ) * (1 / ((σ : ℂ) - ρ) - 1 / ((σ' : ℂ) - ρ))) := by ring
    have hre : (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re)
        = (-((m ρ : ℂ) * (1 / ((σ : ℂ) - ρ) - 1 / ((σ' : ℂ) - ρ)))).re := by
      rw [← heq, Complex.sub_re]
    rw [hre]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    have hmn : ‖((m ρ : ℕ) : ℂ)‖ = (m ρ : ℝ) := by simp
    rw [norm_neg, norm_mul, hmn]
    calc (m ρ : ℝ) * ‖1 / ((σ : ℂ) - ρ) - 1 / ((σ' : ℂ) - ρ)‖
        ≤ (m ρ : ℝ) * (4 * (σ' - σ) / ‖ρ - 1‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 4 * (σ' - σ) * ((m ρ : ℝ) / ‖ρ - 1‖ ^ 2) := by ring
  have hother : -(4 * (σ' - σ) * Sinv)
      ≤ ∑ ρ ∈ Z.erase ((β₀ : ℂ)),
          (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re) := by
    have h1 : |∑ ρ ∈ Z.erase ((β₀ : ℂ)),
          (((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re)|
        ≤ ∑ ρ ∈ Z.erase ((β₀ : ℂ)),
          |((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ ρ ∈ Z.erase ((β₀ : ℂ)),
          |((m ρ : ℂ) / ((σ' : ℂ) - ρ)).re - ((m ρ : ℂ) / ((σ : ℂ) - ρ)).re|
        ≤ 4 * (σ' - σ) * Sinv := by
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hSinv (by linarith)
    have h3 := abs_le.mp (le_trans h1 h2)
    linarith [h3.1]
  have hneg : (-logDeriv Lf (σ : ℂ)).re = -A := by rw [hA, Complex.neg_re]
  have hneg' : (-logDeriv Lf (σ' : ℂ)).re = -A' := by rw [hA', Complex.neg_re]
  rw [hneg'] at hs'bot
  rw [hneg]
  have hSS : (m (β₀ : ℂ) : ℝ) / (σ' - β₀) - (m (β₀ : ℂ) : ℝ) / (σ - β₀)
        - 4 * (σ' - σ) * Sinv ≤ S' - S := by
    rw [hdiff, hsplit, hβterm]; linarith [hother]
  linarith

/-- **`(L1)`, UPPER SIDE: `L′/L(1,χ) ≤ ηL + (1606 + 8·n9Cs)·L/√ℓ′`** — ABSENT in the corpus
(`hb_L1_one_sided` is the lower side only), REQUIRED by N9 twice: for `B = L + |LL|` in the
`n8C6·B·L` error of BOTH p.200 rows, and for Theorem 1's upper half.  Class **B**, cap 200: the
mirror of `hb_L1_lower_at_hb_point` on `neg_re_logDeriv_differenced_mult_ge`.
Consumer: `hb_S3_at_hb_point`. -/
theorem hb_L1_upper_at_hb_point [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    hbLL χ ≤ η * Real.log q + (1606 + 8 * n9Cs) * (Real.log q / Real.sqrt (n9Ell q η)) := by
  obtain ⟨hqR, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  obtain ⟨-, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hb1 := hR.β1
  have hPpos : 0 < n9Ell q η := by linarith only [hPbig]
  have hLp : (0 : ℝ) < 2 * Real.log q := by linarith only [hL]
  have hdhB : dhB = 680 := rfl
  -- `η ≥ 15000`, so M-ONE pins the multiplicity
  have hηbig' : (15000 : ℝ) ≤ η := by
    have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
      have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
      have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
      simp only [n9E0]; linarith
    have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    have hlogη : (15000 : ℝ) ≤ Real.log η := by linarith only [hηbig, hE0, hE1]
    have h := Real.exp_le_exp.mpr hlogη
    rw [Real.exp_log hηpos] at h
    have := Real.add_one_le_exp (15000 : ℝ)
    linarith only [h, this]
  have hm1 : Salt.SW.zeroMult χ ((β₀ : ℝ) : ℂ) = 1 :=
    zeroMult_eq_one_of_eta hR.prim hR.ne hR.zero (by rw [hR.ηdef, one_div]) hηbig'
  -- `√ℓ′` facts and the proximity condition at the floor
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n9Ell q η) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith only [hPbig])
  have hsnn : (0 : ℝ) ≤ Real.sqrt (n9Ell q η) := Real.sqrt_nonneg _
  have hsmul : Real.sqrt (n9Ell q η) * Real.sqrt (n9Ell q η) = n9Ell q η :=
    Real.mul_self_sqrt hPpos.le
  have hs2L : Real.sqrt (n9Ell q η) ≤ 2 * Real.log q := by
    nlinarith only [hsmul, hPsmall, hs1, hL, hsnn]
  have hs1360 : (1360 : ℝ) ≤ Real.sqrt (n9Ell q η) := by
    nlinarith only [hsmul, hPbig, hs1, hsnn]
  have hr0eq : n9Floor q η = n9Ell q η / (680 * Real.log (4 * (q : ℝ))) := by
    rw [n9Floor, hdhB]
  have hr0pos : 0 < n9Floor q η := by
    rw [hr0eq]; exact div_pos hPpos (by linarith only [hWpos])
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
  -- the second abscissa
  have hd0 : (0 : ℝ) < Real.sqrt (n9Ell q η) / (2 * Real.log q) := by positivity
  have hσ'1 : (1 : ℝ) < 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q) := by linarith only [hd0]
  have hσ'2 : 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q) ≤ 2 := by
    have h : Real.sqrt (n9Ell q η) / (2 * Real.log q) ≤ 1 := by
      rw [div_le_one hLp]; linarith only [hs2L]
    linarith only [h]
  -- the zero packet
  obtain ⟨Z, m, hZ, hZall, hmult, hdiff, hfloor, hSinv⟩ := hb_zero_data hR
  have hβball : ((β₀ : ℝ) : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : ((β₀ : ℝ) : ℂ) - 2 = ((β₀ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith only [hβhalf], by linarith only [hb1]⟩
  obtain ⟨hβZ, hmβ⟩ := hZall ((β₀ : ℝ) : ℂ) hβball hR.zero
  have hrem := hdiff 1 (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) le_rfl (by norm_num)
    hσ'1.le hσ'2
  have habs : |(1 : ℝ) - (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q))|
      = (1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) - 1 := by
    rw [abs_of_nonpos (by linarith only [hd0])]; ring
  rw [habs] at hrem
  have hs'bot := neg_re_logDeriv_LFunction_ge χ hσ'1 hσ'2
  have hmain := neg_re_logDeriv_differenced_mult_ge
    (Lf := DirichletCharacter.LFunction χ) (Z := Z) (m := m)
    (σ := 1) (σ' := 1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) (β₀ := β₀)
    (r0 := n9Floor q η) (Sinv := n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η))
    le_rfl (by linarith only [hd0]) hb1 hβZ hr0pos (by linarith only [hr0pos])
    (by linarith only [hσ'r]) hfloor hSinv hrem hs'bot
  rw [Complex.ofReal_one] at hmain
  have hmzeq : (m ((β₀ : ℝ) : ℂ) : ℝ) = 1 := by
    have h := hmult ((β₀ : ℝ) : ℂ) hβZ
    rw [hm1] at h
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  rw [hmzeq] at hmain
  have hCsnn : (0 : ℝ) ≤ n9Cs := by
    have hA := invSqC_spec.1
    have hprod : (0 : ℝ) ≤ invSqC * (dhB ^ 2 + dhB) :=
      mul_nonneg hA.le (by rw [hdhB]; norm_num)
    simp only [n9Cs]; linarith only [hprod]
  have hcol := l1_error_collapse (Lp := 2 * Real.log q) (ell := n9Ell q η)
    (Sinv := n9Cs * ((2 * Real.log q) ^ 2 / n9Ell q η)) (Cs := n9Cs)
    (CR := 1600 * Real.log (80 * Real.sqrt (q : ℝ) * (1 + Real.log q)))
    (mβ := 1) (β₀ := β₀)
    (by linarith only [hPbig]) (by linarith only [hPsmall, hL]) hCsnn (by norm_num) hb1
    le_rfl hCR
  have hβnn : (0 : ℝ)
      ≤ 1 / ((1 + Real.sqrt (n9Ell q η) / (2 * Real.log q)) - β₀) := by
    apply div_nonneg (by norm_num)
    linarith only [hb1, hd0]
  have hpole : (1 : ℝ) / (1 - β₀) = η * Real.log q := hηL.symm
  have hneg : (-logDeriv (DirichletCharacter.LFunction χ) (1 : ℂ)).re = -hbLL χ := by
    simp [hbLL]
  rw [hneg] at hmain
  have hrate : (802 + 1 + 4 * n9Cs) * ((2 * Real.log q) / Real.sqrt (n9Ell q η))
      = (1606 + 8 * n9Cs) * (Real.log q / Real.sqrt (n9Ell q η)) := by ring
  linarith only [hmain, hcol, hpole, hrate, hβnn]


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
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hb1 := hR.β1
  -- `1 − β₀ = 1/(ηL) ≤ (1/5000)/log 4q`: Landau's window contains `β₀`
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
  have hηnum : (30000 : ℝ) ≤ η := by
    have hηge : (3000001 : ℝ) ≤ Real.log η := by linarith only [hηbig, hE0, hE1]
    have h := Real.exp_le_exp.mpr hηge
    rw [Real.exp_log hηpos] at h
    have h2 := Real.add_one_le_exp (3000001 : ℝ)
    linarith only [h, h2]
  have hone : (1 - β₀) * (η * Real.log q) = 1 := by rw [hηL]; field_simp
  have hcross : 5000 * Real.log (4 * (q : ℝ)) ≤ η * Real.log q := by
    have hprod : 30000 * Real.log q ≤ η * Real.log q :=
      mul_le_mul_of_nonneg_right hηnum hL.le
    linarith only [hprod, hW2L, hLhuge]
  have hwβ : 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) ≤ β₀ := by
    have hfin : 1 - β₀ ≤ 1 / 5000 / Real.log (4 * (q : ℝ)) := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [hcross, hβpos, hone]
    linarith only [hfin]
  -- the two numeric comparisons of the ceilings
  have hlog4 : Real.log (4 * (q : ℝ)) = Real.log 4 + Real.log q :=
    Real.log_mul (by norm_num) (by linarith only [hqR])
  have hlog3 : Real.log (3 * (q : ℝ)) = Real.log 3 + Real.log q :=
    Real.log_mul (by norm_num) (by linarith only [hqR])
  have h4le : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h]
  have h3ge : (1 : ℝ) ≤ Real.log (3 : ℝ) := by
    have he := Real.exp_one_lt_d9
    have h := Real.log_le_log (Real.exp_pos 1) (by linarith only [he] : Real.exp 1 ≤ (3 : ℝ))
    rwa [Real.log_exp] at h
  intro t ρ hρ him0 hne hlo hhi _him
  have hcoe : ((ρ.re : ℝ) : ℂ) = ρ := by apply Complex.ext <;> simp [him0]
  have hzr : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by rw [hcoe]; exact hρ
  have hlandau : ρ.re ≤ 1 - (1 / 5000) / Real.log (4 * (q : ℝ)) := by
    rcases le_or_gt ρ.re (1 - (1 / 5000) / Real.log (4 * (q : ℝ))) with h | h
    · exact h
    · exfalso
      have heq := (landau_one_exceptional_at hR.prim hR.ne hzr hR.zero h.le hwβ).1
      exact hne (by rw [← hcoe, heq])
  have hT0 : (0 : ℝ) ≤ efT0 q t := by rw [efT0]; positivity
  have hbase : (3 : ℝ) * (q : ℝ) ≤ (q : ℝ) * (efT0 q t + 3) := by nlinarith [hqR, hT0]
  have hlog3q : 0 < Real.log (3 * (q : ℝ)) := by rw [hlog3]; linarith only [h3ge, hL]
  have hmono : Real.log (3 * (q : ℝ)) ≤ Real.log ((q : ℝ) * (efT0 q t + 3)) :=
    Real.log_le_log (by linarith only [hqR]) hbase
  have hXpos : 0 < Real.log ((q : ℝ) * (efT0 q t + 3)) := by linarith only [hmono, hlog3q]
  have hkey : 1 / 126848 / Real.log ((q : ℝ) * (efT0 q t + 3))
      ≤ 1 / 5000 / Real.log (4 * (q : ℝ)) := by
    rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 5000 * Real.log (4 * (q : ℝ)) ≤ 5000 * (3 + Real.log q) := by
      rw [hlog4]; linarith only [h4le]
    have h2 : 126848 * Real.log (3 * (q : ℝ))
        ≤ 126848 * Real.log ((q : ℝ) * (efT0 q t + 3)) := by linarith only [hmono]
    have h3 : 126848 * (1 + Real.log q) ≤ 126848 * Real.log (3 * (q : ℝ)) := by
      rw [hlog3]; linarith only [h3ge]
    nlinarith only [h1, h2, h3, hL]
  rw [efZfrCeil]
  linarith only [hlandau, hkey]

/-- `log t ≤ 2√t` — the largeness step the `m3` and star rows need against `log L`. -/
private lemma n9_log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h := n9_log_le_div (t := t) (M := Real.sqrt t / 2) (by linarith)
    (by nlinarith only [hsq])
  have heq : t / (Real.sqrt t / 2) = 2 * Real.sqrt t := by
    rw [eq_comm, eq_div_iff (ne_of_gt (by linarith : (0 : ℝ) < Real.sqrt t / 2))]
    linear_combination hsq
  rwa [heq] at h

/-- `y^k ≤ e^E` once `k·log y ≤ E` — the ledger's polynomial-against-exponential step, in the
`log` currency (the `√` currency of §14 is far too lossy for the repulsion row). -/
private lemma n9_pow_le_exp {y E : ℝ} {k : ℕ} (hy : 0 < y) (h : (k : ℝ) * Real.log y ≤ E) :
    y ^ k ≤ Real.exp E := by
  have h1 : Real.exp ((k : ℝ) * Real.log y) = y ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hy]
  calc y ^ k = Real.exp ((k : ℝ) * Real.log y) := h1.symm
    _ ≤ Real.exp E := Real.exp_le_exp.mpr h

/-- **THE RANGE-A CEILING** — the repulsion ceiling at the box top `q(T₀(u)+3)`, capped by the
Range-B zero-free ceiling.  The `min` is valid at EVERY `u` (the repulsion arm is trivially
`> 1` where its numerator goes negative), and each arm can be used alone in the ledger. -/
private noncomputable def n9BceilA (q : ℕ) (β₀ u : ℝ) : ℝ :=
  repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀)
    ⊓ efZfrCeil q (1 / 126848) u

/-- The Range-A ceiling is continuous — `continuousOn_efEnvelope_ceilFun`'s hypothesis. -/
private lemma n9_cont_bceilA {q : ℕ} (hq : 2 ≤ q) (β₀ : ℝ) :
    ContinuousOn (fun u : ℝ => n9BceilA q β₀ u) (Set.Ici (3 : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqu : ContinuousOn (fun u : ℝ => (q : ℝ) * u) (Set.Ici (3 : ℝ)) :=
    continuousOn_const.mul continuousOn_id
  have hlogqu : ContinuousOn (fun u : ℝ => Real.log ((q : ℝ) * u)) (Set.Ici (3 : ℝ)) :=
    Real.continuousOn_log.comp hqu (fun u hu => by
      have h3 : (3 : ℝ) ≤ u := hu
      exact ne_of_gt (by nlinarith))
  have hT : ContinuousOn (fun u : ℝ => efT0 q u) (Set.Ici (3 : ℝ)) := by
    simp only [efT0]
    exact (hlogqu.add continuousOn_const).pow 6
  have hQ : ContinuousOn (fun u : ℝ => (q : ℝ) * (efT0 q u + 1 + 2)) (Set.Ici (3 : ℝ)) :=
    continuousOn_const.mul ((hT.add continuousOn_const).add continuousOn_const)
  have hQ10 : ∀ u ∈ Set.Ici (3 : ℝ), (10 : ℝ) ≤ (q : ℝ) * (efT0 q u + 1 + 2) := by
    intro u hu
    have h3 : (3 : ℝ) ≤ u := hu
    have h2 := two_le_efT0 hq h3
    nlinarith
  have hlogQ : ContinuousOn (fun u : ℝ => Real.log ((q : ℝ) * (efT0 q u + 1 + 2)))
      (Set.Ici (3 : ℝ)) :=
    Real.continuousOn_log.comp hQ (fun u hu => ne_of_gt (by linarith [hQ10 u hu]))
  have hlogQpos : ∀ u ∈ Set.Ici (3 : ℝ),
      (0 : ℝ) < Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) := by
    intro u hu
    exact Real.log_pos (by linarith [hQ10 u hu])
  have hrep : ContinuousOn (fun u : ℝ =>
      repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀))
      (Set.Ici (3 : ℝ)) := by
    simp only [repulsionCeiling]
    refine continuousOn_const.sub (ContinuousOn.div ?_ ?_ ?_)
    · refine (continuousOn_const.sub continuousOn_const).sub
        (continuousOn_const.mul (Real.continuousOn_log.comp (hlogQ.add continuousOn_const)
          (fun u hu => ne_of_gt (by linarith [hlogQpos u hu]))))
    · exact continuousOn_const.mul hlogQ
    · intro u hu
      have h := hlogQpos u hu
      have hb : dhB = 680 := rfl
      rw [hb]
      exact ne_of_gt (by linarith)
  simp only [n9BceilA]
  exact ContinuousOn.inf hrep (continuousOn_efZfrCeil hq (1 / 126848))

/-- **THE RANGE-A CEILING IS VALID AT EVERY `u`.**  The `efZfrCeil` arm is
`re_le_efZfrCeil` on `zero_free_region_all_numeral` + `real_zeros_below_zfrCeil`; the repulsion
arm is `dh_ceiling_box` at `T = efT0 q u + 1` when its numerator is non-negative, and trivial
(the ceiling exceeds `1`) when it is not. -/
private lemma n9_re_le_bceilA [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {u : ℝ} (hu : 3 ≤ u) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) → 9 / 10 ≤ ρ.re →
      ρ.re ≤ 1 → |ρ.im| ≤ efT0 q u + 1 → ρ.re ≤ n9BceilA q β₀ u := by
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hT2 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq2 hu
  have hTpos : (0 : ℝ) ≤ efT0 q u + 1 := by linarith
  have hQ10 : (10 : ℝ) ≤ (q : ℝ) * (efT0 q u + 1 + 2) := by nlinarith
  have hlogQ : (0 : ℝ) < Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) :=
    Real.log_pos (by linarith)
  intro ρ hz hne hlo hhi him
  refine le_inf ?_ ?_
  · by_cases hN : 0 ≤ n9EllAt q η (efT0 q u + 1)
    · exact dh_ceiling_box hR hTpos hN ρ hz hne hlo hhi him
    · push Not at hN
      have hval : repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀)
          = 1 - n9EllAt q η (efT0 q u + 1)
              / (dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2))) := by
        have hid : Real.log (1 / (1 - β₀)) = Real.log (η * Real.log q) := by rw [hηL]
        simp only [repulsionCeiling, n9EllAt, hid]
      have hb : dhB = 680 := rfl
      have hden : (0 : ℝ) < dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) := by
        rw [hb]; linarith
      have hfrac : n9EllAt q η (efT0 q u + 1)
          / (dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2))) < 0 :=
        div_neg_of_neg_of_pos hN hden
      rw [hval]; linarith
  · exact re_le_efZfrCeil hq2 (by norm_num)
      (fun ρ' hρ' hre' hor' => zero_free_region_all_numeral q χ hR.prim hR.ne hρ' hre' hor')
      (real_zeros_below_zfrCeil hR u) ρ hz hne hlo hhi him

/-- **THE REPULSION DECAY.**  `u^{bceil−1} ≤ e^{−A}` at the repulsion arm as soon as
`A·(680·log(q(T₀+3))) ≤ ℓ′(T₀+1)·log u` — the Range-A mirror of `efZfrCeil_rpow_le`. -/
private lemma n9_rep_rpow_le [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {u A : ℝ} (hu : 3 ≤ u) (_hA : 0 ≤ A)
    (hAle : A * (dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2)))
      ≤ n9EllAt q η (efT0 q u + 1) * Real.log u) :
    u ^ (repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀) - 1)
      ≤ Real.exp (-A) := by
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hu0 : (0 : ℝ) < u := by linarith
  have hT2 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq2 hu
  have hQ10 : (10 : ℝ) ≤ (q : ℝ) * (efT0 q u + 1 + 2) := by nlinarith
  have hlogQ : (0 : ℝ) < Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) :=
    Real.log_pos (by linarith)
  have hb : dhB = 680 := rfl
  have hden : (0 : ℝ) < dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) := by rw [hb]; linarith
  have hval : repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀)
      = 1 - n9EllAt q η (efT0 q u + 1)
          / (dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2))) := by
    have hid : Real.log (1 / (1 - β₀)) = Real.log (η * Real.log q) := by rw [hηL]
    simp only [repulsionCeiling, n9EllAt, hid]
  have hkey : Real.log u
      * (repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀) - 1) ≤ -A := by
    rw [hval]
    have heq : Real.log u * (1 - n9EllAt q η (efT0 q u + 1)
          / (dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2))) - 1)
        = -(n9EllAt q η (efT0 q u + 1) * Real.log u
            / (dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2)))) := by
      field_simp
      ring
    rw [heq, neg_le_neg_iff, le_div_iff₀ hden]
    linarith
  rw [Real.rpow_def_of_pos hu0]
  exact Real.exp_le_exp.mpr hkey

set_option maxHeartbeats 1000000 in
-- Four ledger rows over one window context, the last of them a two-case decay argument.
/-- **THE RANGE-A LEDGER, POINTWISE ON THE WINDOW.**  `G(u) ≤ (m+255)/log u` at EVERY
`u` with `q^{250} ≤ u` — no existential threshold.  Rows (i)–(iii) are §14's, re-proved
pointwise from the window edge; row (iv) is Range A's own: below the crossover
(`700·log M ≤ L`) the repulsion decay `exp(−ℓ′·log u/(680·log(q(T₀+3))))` pays it, and the
regime's `ellL` is exactly what makes `ℓ′` beat the `5·log log u` the row costs; above it
(`700·log M > L`, so `log u ≥ e^{2141}`) the Range-B decay pays it with room to spare. -/
private lemma n9_env_le_window [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) (m : ℕ) {u : ℝ} (hu : 3 ≤ u)
    (hwin : 250 * Real.log q ≤ Real.log u) :
    efEnvelope q β₀ (n9BceilA q β₀ u) m (9 / 10) (19 / 20) u
      ≤ ((m : ℝ) + 255) / Real.log u := by
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, hPbig, hPsmall, hlog4qpos, hW2L, -⟩ := n9_num_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hu0 : (0 : ℝ) < u := by linarith only [hu]
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = Real.log u := ⟨_, rfl⟩
  have hy : (375000000 : ℝ) ≤ y := by rw [hydef]; linarith only [hwin, hLhuge]
  have hy0 : (0 : ℝ) < y := by linarith only [hy]
  have hyu : Real.exp y = u := by rw [hydef]; exact Real.exp_log hu0
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Real.log ((q : ℝ) * u) + 2 := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Real.log q + 11 * Real.log M := ⟨_, rfl⟩
  have hMeq : M = Real.log q + y + 2 := by
    rw [hMdef, hydef, Real.log_mul (ne_of_gt (by linarith only [hqR] : (0 : ℝ) < (q : ℝ)))
      (ne_of_gt hu0)]
  have hLy : Real.log q ≤ y / 250 := by rw [hydef]; linarith only [hwin]
  have hMy : y ≤ M := by rw [hMeq]; linarith only [hL]
  have hM2y : M ≤ 2 * y := by rw [hMeq]; linarith only [hLy, hy]
  have hM3 : (3 : ℝ) ≤ M := by rw [hMeq]; linarith only [hL, hy]
  have hM0 : (0 : ℝ) < M := by linarith only [hM3]
  have hsy : (19364 : ℝ) ≤ Real.sqrt y := by
    rw [show (19364 : ℝ) = Real.sqrt (19364 ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19364)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith only [hy])
  have hsqy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  have hlogy : Real.log y ≤ y / 9682 := by
    have h1 := n9_log_le_two_sqrt hy0
    nlinarith only [h1, hsy, hsqy, Real.sqrt_nonneg y]
  have hlogy0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hlogM : Real.log M ≤ Real.log y + 1 := by
    have h1 : Real.log M ≤ Real.log (2 * y) := Real.log_le_log hM0 hM2y
    have h2 : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) (ne_of_gt hy0)
    have h3 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith only [h1, h2, h3]
  have hlogM0 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by linarith only [hM3])
  have hNy : N ≤ y / 150 := by
    rw [hNdef]; linarith only [hLy, hlogM, hlogy, hy]
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; linarith only [hL, hlogM0]
  have hled := efEnvelope_le_ledger_sharp (β₀ := β₀) (bceil := n9BceilA q β₀ u) (m := m)
    (M := M) (N := N) (σa := 9 / 10) (σb := 19 / 20) hq2 hu hMdef hNdef le_rfl (by norm_num)
    (by norm_num) (by norm_num) (le_of_lt hR.β1)
  have hCled : 2 * 10 ^ 6 * N ^ 2 / M ^ 2 ≤ 250 :=
    ledger_const_le_of_window hq2 hu hMdef hNdef (by linarith only [hLhuge]) hwin
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  -- (i) the `1/M` grade
  have hi : ((m : ℝ) + 2 + 2 * 10 ^ 6 * N ^ 2 / M ^ 2) / M ≤ ((m : ℝ) + 252) / y := by
    have hstep1 : ((m : ℝ) + 2 + 2 * 10 ^ 6 * N ^ 2 / M ^ 2) / M ≤ ((m : ℝ) + 252) / M := by
      rw [div_le_div_iff₀ hM0 hM0]; nlinarith only [hCled, hM0]
    have hstep2 : ((m : ℝ) + 252) / M ≤ ((m : ℝ) + 252) / y := by
      rw [div_le_div_iff₀ hM0 hy0]; nlinarith only [hMy, hmnn]
    linarith only [hstep1, hstep2]
  -- (ii) the de-smoothing constant
  have hii : M / u ≤ 1 / y := by
    rw [div_le_div_iff₀ hu0 hy0, one_mul]
    have h3 : y ^ 3 ≤ Real.exp y := n9_pow_le_exp hy0 (by push_cast; linarith only [hlogy, hy])
    have h2 : M * y ≤ 2 * y * y := by nlinarith only [hM2y, hy0]
    have h4 : 2 * y * y ≤ y ^ 3 := by nlinarith only [hy, sq_nonneg y]
    rw [← hyu]; linarith only [h2, h3, h4]
  -- (iii) the left edge
  have hiii : 10 ^ 6 * M ^ 9 * N ^ 2 * u ^ ((19 : ℝ) / 20 - 1) ≤ 1 / y := by
    have hrp : u ^ ((19 : ℝ) / 20 - 1) = Real.exp (-(y / 20)) := by
      rw [Real.rpow_def_of_pos hu0, ← hydef]
      congr 1; ring
    have hE0 : (0 : ℝ) < Real.exp (-(y / 20)) := Real.exp_pos _
    rw [hrp, le_div_iff₀ hy0]
    have hM9 : M ^ 9 ≤ (2 * y) ^ 9 := pow_le_pow_left₀ hM0.le hM2y 9
    have hN2 : N ^ 2 ≤ (y / 150) ^ 2 := pow_le_pow_left₀ hN0 hNy 2
    have hstep : 10 ^ 6 * M ^ 9 * N ^ 2 ≤ 10 ^ 6 * (2 * y) ^ 9 * (y / 150) ^ 2 := by
      have h1 : 10 ^ 6 * M ^ 9 ≤ 10 ^ 6 * (2 * y) ^ 9 :=
        mul_le_mul_of_nonneg_left hM9 (by norm_num)
      exact mul_le_mul h1 hN2 (by positivity) (by positivity)
    have hstepy : 10 ^ 6 * M ^ 9 * N ^ 2 * y ≤ 10 ^ 6 * (2 * y) ^ 9 * (y / 150) ^ 2 * y :=
      mul_le_mul_of_nonneg_right hstep hy0.le
    have heq : 10 ^ 6 * (2 * y) ^ 9 * (y / 150) ^ 2 * y = (512 * 10 ^ 6 / 22500) * y ^ 12 := by
      ring
    have h12 : (0 : ℝ) ≤ y ^ 12 := by positivity
    have hcst : (512 * 10 ^ 6 / 22500 : ℝ) * y ^ 12 ≤ y ^ 13 := by
      have hpow : y ^ 13 = y * y ^ 12 := by ring
      nlinarith only [hy, h12, hpow]
    have hcoef : 10 ^ 6 * M ^ 9 * N ^ 2 * y ≤ y ^ 13 := by
      linarith only [hstepy, heq, hcst]
    have hexp13 : y ^ 13 ≤ Real.exp (y / 20) :=
      n9_pow_le_exp hy0 (by push_cast; linarith only [hlogy, hy])
    calc 10 ^ 6 * M ^ 9 * N ^ 2 * Real.exp (-(y / 20)) * y
        = (10 ^ 6 * M ^ 9 * N ^ 2 * y) * Real.exp (-(y / 20)) := by ring
      _ ≤ Real.exp (y / 20) * Real.exp (-(y / 20)) :=
          mul_le_mul_of_nonneg_right (le_trans hcoef hexp13) hE0.le
      _ = 1 := by rw [← Real.exp_add]; simp
  -- (iv) the erased spend, at the Range-A ceiling
  have hiv : 10 ^ 3 * M ^ 3 * N * u ^ (n9BceilA q β₀ u - 1) ≤ 1 / y := by
    obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 5 * Real.log y + 4 := ⟨_, rfl⟩
    have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; linarith only [hlogy0]
    have he4 : (54 : ℝ) ≤ Real.exp 4 := by
      have h1 := Real.exp_one_gt_d9
      have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      have h3 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 4
      have h4 : (54 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 := by norm_num
      rw [h2]; linarith only [h3, h4]
    have hy5 : y ^ 5 = Real.exp (5 * Real.log y) := by
      rw [show (5 : ℝ) * Real.log y = ((5 : ℕ) : ℝ) * Real.log y by norm_num,
        Real.exp_nat_mul, Real.exp_log hy0]
    have hcoef : 10 ^ 3 * M ^ 3 * N * y ≤ Real.exp A := by
      have hM3p : M ^ 3 ≤ (2 * y) ^ 3 := pow_le_pow_left₀ hM0.le hM2y 3
      have hstep : 10 ^ 3 * M ^ 3 * N ≤ 10 ^ 3 * (2 * y) ^ 3 * (y / 150) := by
        have h1 : 10 ^ 3 * M ^ 3 ≤ 10 ^ 3 * (2 * y) ^ 3 :=
          mul_le_mul_of_nonneg_left hM3p (by norm_num)
        exact mul_le_mul h1 hNy hN0 (by positivity)
      have heq : 10 ^ 3 * (2 * y) ^ 3 * (y / 150) * y = (8 * 10 ^ 3 / 150) * y ^ 5 := by ring
      have hAsplit : Real.exp A = Real.exp 4 * Real.exp (5 * Real.log y) := by
        rw [hAdef, ← Real.exp_add]; congr 1; ring
      have h5nn : (0 : ℝ) ≤ y ^ 5 := by positivity
      calc 10 ^ 3 * M ^ 3 * N * y ≤ 10 ^ 3 * (2 * y) ^ 3 * (y / 150) * y :=
            mul_le_mul_of_nonneg_right hstep hy0.le
        _ = (8 * 10 ^ 3 / 150) * y ^ 5 := heq
        _ ≤ 54 * y ^ 5 := by nlinarith only [h5nn]
        _ ≤ Real.exp 4 * Real.exp (5 * Real.log y) := by
            rw [hy5]; exact mul_le_mul_of_nonneg_right he4 (Real.exp_pos _).le
        _ = Real.exp A := hAsplit.symm
    have hdecay : u ^ (n9BceilA q β₀ u - 1) ≤ Real.exp (-A) := by
      by_cases hcase : 700 * Real.log M ≤ Real.log q
      · have hmin : n9BceilA q β₀ u - 1
            ≤ repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀) - 1 := by
          have h : repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀)
              ⊓ efZfrCeil q (1 / 126848) u
              ≤ repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀) :=
            inf_le_left
          simp only [n9BceilA]
          linarith only [h]
        refine le_trans (Real.rpow_le_rpow_of_exponent_le (by linarith only [hu]) hmin) ?_
        refine n9_rep_rpow_le hR hu hA0 ?_
        rw [← hydef]
        have hT2 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq2 hu
        have hQ3 : (q : ℝ) * (efT0 q u + 1 + 2) = (q : ℝ) * (efT0 q u + 3) := by ring
        have hlogQ : Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) ≤ Real.log q + 7 * Real.log M := by
          rw [hQ3]; exact log_q_efT0_add3_le hq2 hu hMdef
        have hQ10 : (10 : ℝ) ≤ (q : ℝ) * (efT0 q u + 1 + 2) := by
          nlinarith only [hT2, hqR]
        have h4qle : Real.log (4 * (q : ℝ)) ≤ Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) := by
          refine Real.log_le_log (by linarith only [hqR]) ?_
          nlinarith only [hT2, hqR]
        have h4qlog : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
          Real.log_le_log (by linarith only [hL, hqR]) (by linarith only [hqR])
        have hb1 : (0 : ℝ) < Real.log (4 * (q : ℝ)) + 2 := by linarith only [hlog4qpos]
        have hw0 : (0 : ℝ) ≤ 7 * Real.log M / Real.log q := by positivity
        have hwq : 7 * Real.log M / Real.log q * Real.log q = 7 * Real.log M := by
          field_simp
        have hratio : Real.log (Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) + 2)
            - Real.log (Real.log (4 * (q : ℝ)) + 2) ≤ 7 * Real.log M / Real.log q := by
          have hdiv : Real.log (Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) + 2)
              - Real.log (Real.log (4 * (q : ℝ)) + 2)
              = Real.log ((Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) + 2)
                  / (Real.log (4 * (q : ℝ)) + 2)) := by
            rw [Real.log_div (by linarith only [hb1, h4qle]) (by linarith only [hb1])]
          rw [hdiv]
          have hle1 := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < (Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) + 2)
              / (Real.log (4 * (q : ℝ)) + 2) from
              div_pos (by linarith only [hb1, h4qle]) hb1)
          have hstep : (Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) + 2)
              / (Real.log (4 * (q : ℝ)) + 2) ≤ 7 * Real.log M / Real.log q + 1 := by
            rw [div_le_iff₀ hb1]
            nlinarith only [hlogQ, hwq, hw0, h4qlog, hlogM0, hL,
              mul_nonneg hw0 (sub_nonneg.mpr h4qlog)]
          linarith only [hle1, hstep]
        have hEllAt : n9Ell q η - 98 * Real.log M / Real.log q
            ≤ n9EllAt q η (efT0 q u + 1) := by
          have hk : dhK = 14 := rfl
          have hmul : (14 : ℝ) * (7 * Real.log M / Real.log q) = 98 * Real.log M / Real.log q := by
            ring
          simp only [n9Ell, n9EllAt, hk]
          linarith only [hratio, hmul]
        have hcase' : 7 * Real.log M ≤ Real.log q / 100 := by linarith only [hcase, hlogM0]
        have h98 : 98 * Real.log M / Real.log q ≤ 14 / 100 := by
          rw [div_le_div_iff₀ hL (by norm_num)]
          linarith only [hcase']
        have hEllAt' : n9Ell q η - 14 / 100 ≤ n9EllAt q η (efT0 q u + 1) := by
          linarith only [hEllAt, h98]
        have hlogQ' : Real.log ((q : ℝ) * (efT0 q u + 1 + 2)) ≤ 101 / 100 * Real.log q := by
          linarith only [hlogQ, hcase']
        have p1 : Real.log q * Real.log y
            ≤ Real.log q * Real.log (Real.log q) + y - Real.log q := by
          have hsplit : Real.log y = Real.log (Real.log q) + Real.log (y / Real.log q) := by
            rw [← Real.log_mul (ne_of_gt hL) (by positivity)]
            congr 1
            field_simp
          have hle := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < y / Real.log q by positivity)
          have hqy : Real.log y ≤ Real.log (Real.log q) + (y / Real.log q - 1) := by
            linarith only [hsplit, hle]
          have h := mul_le_mul_of_nonneg_left hqy hL.le
          have heq : Real.log q * (y / Real.log q) = y := by field_simp
          nlinarith only [h, heq]
        have hE0nn : (0 : ℝ) ≤ n9E0 := by
          have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
          have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
          have hc : (0 : ℝ) < Real.exp (3 * 10 ^ 6 : ℝ) := Real.exp_pos _
          simp only [n9E0]; linarith only [ha, hb, hc]
        have h16 : 16 * Real.log (Real.log q) ≤ n9Ell q η := by
          have hll : Real.log (Real.log q) ≤ Real.log (Real.log (4 * (q : ℝ))) :=
            Real.log_le_log hL h4qlog
          linarith only [hR.ellL, hll, hE0nn]
        have p2 : 16 * (Real.log q * Real.log (Real.log q)) ≤ Real.log q * n9Ell q η := by
          nlinarith only [h16, hL]
        have p3 : 250 * (Real.log q * n9Ell q η) ≤ y * n9Ell q η := by
          have hE : (0 : ℝ) ≤ n9Ell q η := by linarith only [hPbig]
          nlinarith only [hLy, hE, hy0]
        have p4 : 3435 * y ≤ (1415 / 10000) * (y * n9Ell q η) := by
          nlinarith only [hPbig, hy0]
        have hb : dhB = 680 := rfl
        have hstep1 : A * (dhB * Real.log ((q : ℝ) * (efT0 q u + 1 + 2)))
            ≤ A * (680 * (101 / 100 * Real.log q)) := by
          rw [hb]
          refine mul_le_mul_of_nonneg_left ?_ hA0
          linarith only [hlogQ']
        have hstep2 : A * (680 * (101 / 100 * Real.log q))
            = 3434 * (Real.log q * Real.log y) + 13736 / 5 * Real.log q := by
          rw [hAdef]; ring
        have hstep3 : (n9Ell q η - 14 / 100) * y ≤ n9EllAt q η (efT0 q u + 1) * y :=
          mul_le_mul_of_nonneg_right hEllAt' hy0.le
        have hfin : 3434 * (Real.log q * Real.log y) + 13736 / 5 * Real.log q
            ≤ (n9Ell q η - 14 / 100) * y := by
          linarith only [p1, p2, p3, p4, hL, hy0]
        linarith only [hstep1, hstep2, hstep3, hfin]
      · push Not at hcase
        have hmin : n9BceilA q β₀ u - 1 ≤ efZfrCeil q (1 / 126848) u - 1 := by
          have h : repulsionCeiling dhB dhC dhK ((q : ℝ) * (efT0 q u + 1 + 2)) (1 - β₀)
              ⊓ efZfrCeil q (1 / 126848) u ≤ efZfrCeil q (1 / 126848) u := inf_le_right
          simp only [n9BceilA]
          linarith only [h]
        refine le_trans (Real.rpow_le_rpow_of_exponent_le (by linarith only [hu]) hmin) ?_
        refine efZfrCeil_rpow_le hq2 hu hMdef hA0 ?_
        rw [← hydef]
        obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.log y := ⟨_, rfl⟩
        have hMt : Real.log M ≤ t + 1 := by rw [htdef]; exact hlogM
        have ht : (2141 : ℝ) ≤ t := by linarith only [hcase, hMt, hLhuge]
        have ht0 : (0 : ℝ) < t := by linarith only [ht]
        have hyt : Real.exp t = y := by rw [htdef]; exact Real.exp_log hy0
        have h8 : (t / 8) ^ 8 ≤ y := by
          have h1 : t / 8 ≤ Real.exp (t / 8) := by
            linarith only [Real.add_one_le_exp (t / 8)]
          have h2 : (t / 8) ^ 8 ≤ Real.exp (t / 8) ^ 8 :=
            pow_le_pow_left₀ (by positivity) h1 8
          have h3 : Real.exp (t / 8) ^ 8 = Real.exp t := by
            rw [show t = ((8 : ℕ) : ℝ) * (t / 8) by push_cast; ring, Real.exp_nat_mul]
            congr 2
            push_cast; ring
          rw [← hyt]; linarith only [h2, h3]
        have ht6 : (2141 : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht 6
        have ht2 : (0 : ℝ) ≤ t ^ 2 := by positivity
        have hykey : (492000000 : ℝ) * t ^ 2 ≤ y := by
          have hpow : t ^ 8 = t ^ 6 * t ^ 2 := by ring
          have hstep : (2141 : ℝ) ^ 6 * t ^ 2 ≤ t ^ 8 := by
            rw [hpow]; exact mul_le_mul_of_nonneg_right ht6 ht2
          have heq : (t / 8) ^ 8 = t ^ 8 / 16777216 := by ring
          rw [heq] at h8
          nlinarith only [hstep, h8, ht2]
        have hAt : A ≤ 5 * t + 4 := by rw [hAdef, htdef]
        have hsum : Real.log q + 7 * Real.log M ≤ 707 * (t + 1) := by
          linarith only [hcase, hMt, hlogM0]
        calc A * (Real.log q + 7 * Real.log M)
            ≤ (5 * t + 4) * (707 * (t + 1)) := by
              refine mul_le_mul hAt hsum ?_ ?_
              · linarith only [hL, hlogM0]
              · linarith only [ht0]
          _ ≤ 1 / 126848 * y := by nlinarith only [hykey, ht, ht0]
    have hEA : (0 : ℝ) < Real.exp A := Real.exp_pos _
    rw [le_div_iff₀ hy0]
    calc 10 ^ 3 * M ^ 3 * N * u ^ (n9BceilA q β₀ u - 1) * y
        = 10 ^ 3 * M ^ 3 * N * y * u ^ (n9BceilA q β₀ u - 1) := by ring
      _ ≤ Real.exp A * Real.exp (-A) :=
          mul_le_mul hcoef hdecay (Real.rpow_nonneg hu0.le _) hEA.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hcollect : ((m : ℝ) + 255) / y
      = ((m : ℝ) + 252) / y + 1 / y + 1 / y + 1 / y := by ring
  rw [hydef] at hi hii hiii hiv hcollect
  linarith only [hled, hi, hii, hiii, hiv, hcollect]

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
`hwin : 250·log q ≤ log u`); row (iv) below the crossover is
`10³·M³·N·exp(−n9EllAt·log u/(680·log(q(T₀+3))))` — at `u = X = q^{250}` that is
`≈ 1.6·10⁷·L⁴·exp(−0.368·n9EllAt)` and the tail integral of it `≈ 4·10^{10}·L⁴·e^{−0.368ℓ′}/ℓ′`,
so the grade `100/√log X` needs `ℓ′ ≥ 74 + 12.2·log L` — PAID BY THE REGIME'S `ellL`
(finding 4; `n9EllAt ≥ ℓ′ − 84·log(251L)/L`), NOT by `ellBig` alone; above the crossover
(`log log(qu) ≈ (ηL)^{1/14}/6`, far above `exp(20·L·log L/c₀)`) the Range-B decay
`exp(−c₀·log u/(7·log log u))` dominates `M³N`; `logChiSum_tendsto_of_envelope` and the landed
`key` arithmetic give the grade (row (i) is ceiling-independent).
Consumer: `hb_L2_at_hb_point` (as `htail` at `X = x` and as `hcorr_at_split`'s `hS`). -/
theorem logChiSum_tail_at_window [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {X : ℝ} (hX : (q : ℝ) ^ 250 ≤ X) :
    ∃ S : ℂ, Tendsto (fun Y : ℝ => logChiSum χ X Y) atTop (𝓝 S) ∧
      ‖S + (Salt.SW.zeroMult χ (β₀ : ℂ) : ℂ)
          * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖
        ≤ 100 / Real.sqrt (Real.log X) := by
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, hPbig, hPsmall, hlog4qpos, hW2L, -⟩ := n9_num_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  -- `η ≥ 15000`: the multiplicity is one (M-ONE)
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
  have hηnum : (15000 : ℝ) ≤ η := by
    have hge : (3000001 : ℝ) ≤ Real.log η := by linarith
    have h := Real.exp_le_exp.mpr hge
    rw [Real.exp_log hηpos] at h
    have h2 := Real.add_one_le_exp (3000001 : ℝ)
    linarith
  have hm1 : zeroMult χ (β₀ : ℂ) = 1 :=
    zeroMult_eq_one_of_eta hR.prim hR.ne hR.zero (by rw [hR.ηdef, one_div]) hηnum
  have hone : (1 - β₀) * (η * Real.log q) = 1 := by rw [hηL]; field_simp
  have hprod : (20 : ℝ) ≤ η * Real.log q := by
    have h := mul_le_mul_of_nonneg_right hηnum hL.le
    linarith only [h, hLhuge]
  have hβ19 : (19 : ℝ) / 20 ≤ β₀ := by nlinarith only [hone, hβpos, hprod]
  -- the window edge
  have hq250 : Real.exp (250 * Real.log q) = (q : ℝ) ^ (250 : ℕ) := by
    rw [show (250 : ℝ) * Real.log q = ((250 : ℕ) : ℝ) * Real.log q by norm_num,
      Real.exp_nat_mul, Real.exp_log hqpos]
  have hX250 : Real.exp (250 * Real.log q) ≤ X := by rw [hq250]; exact hX
  have hXbig : (375000000 : ℝ) ≤ X := by
    have h := Real.add_one_le_exp (250 * Real.log q)
    linarith
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : 250 * Real.log q ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos (250 * Real.log q)) hX250
    rwa [Real.log_exp] at h
  have hlogXbig : (375000000 : ℝ) ≤ Real.log X := by linarith
  have hlogX0 : (0 : ℝ) < Real.log X := by linarith
  -- the envelope at the Range-A ceiling
  set m : ℕ := zeroMult χ (β₀ : ℂ) with hmdef
  set G : ℝ → ℝ := fun t => efEnvelope q β₀ (n9BceilA q β₀ t) m (9 / 10) (19 / 20) t with hGdef
  have hsub : Set.Ici X ⊆ Set.Ici (3 : ℝ) := fun t ht => le_trans hX3 ht
  have hGc : ContinuousOn G (Set.Ici X) :=
    (continuousOn_efEnvelope_ceilFun hq2 (β₀ := β₀) (B := fun t => n9BceilA q β₀ t) m
      (n9_cont_bceilA hq2 β₀) (by norm_num)).mono hsub
  have hG0 : ∀ t ∈ Set.Ici X, 0 ≤ G t := fun t ht =>
    efEnvelope_nonneg hq2 (le_trans hX3 ht) (by norm_num) (by norm_num) (by norm_num)
  have hEF : ∀ t ∈ Set.Ici X, ‖psiDefect χ β₀ m t‖ ≤ t * G t := fun t ht =>
    psiDefect_norm_le_envelope χ hR.prim hq2 (le_trans hX3 ht) le_rfl (by norm_num)
      (by norm_num) (le_of_lt hR.β1) hβ19 hR.zero (n9_re_le_bceilA hR (le_trans hX3 ht))
  have hle : ∀ t ∈ Set.Ici X, G t ≤ ((m : ℝ) + 255) / Real.log t := by
    intro t ht
    have ht3 : (3 : ℝ) ≤ t := le_trans hX3 ht
    have htw : 250 * Real.log q ≤ Real.log t := by
      have h := Real.log_le_log hX0 (show X ≤ t from ht)
      linarith
    exact n9_env_le_window hR m ht3 htw
  have hev : ∀ᶠ t : ℝ in atTop, G t ≤ ((m : ℝ) + 255) / Real.log t := by
    filter_upwards [eventually_ge_atTop X] with t ht
    exact hle t ht
  have hGint : IntegrableOn (fun t : ℝ => G t / (t * Real.log t)) (Set.Ioi X) :=
    integrableOn_div_of_eventually_le hX3 hGc hG0 hev
  have hGlim : Tendsto (fun t : ℝ => G t / Real.log t) atTop (𝓝 0) := by
    refine tendsto_div_log_of_eventually_le ?_ hev
    filter_upwards [eventually_ge_atTop X] with t ht
    exact hG0 t ht
  obtain ⟨S, hS, hbound⟩ :=
    logChiSum_tendsto_of_envelope χ (by linarith) hR.β1 m hX3 hGc hG0 hEF hGint hGlim
  refine ⟨S, hS, le_trans hbound (le_trans (tail_le_of_pointwise hX3 hGc hG0 hle) ?_)⟩
  -- `C/(log X)² + 2C/log X ≤ 100/√(log X)` at `C = 256`, `√(log X) ≥ 19364`
  have hC : ((m : ℝ) + 255) = 256 := by norm_num [hm1]
  rw [hC]
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log X) := ⟨_, rfl⟩
  have hsq : s ^ 2 = Real.log X := by rw [hsdef]; exact Real.sq_sqrt hlogX0.le
  have hs : (19364 : ℝ) ≤ s := by
    rw [hsdef, show (19364 : ℝ) = Real.sqrt (19364 ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19364)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hs0 : (0 : ℝ) < s := by linarith
  rw [← hsdef, ← hsq]
  have e1 : (256 : ℝ) / (s ^ 2) ^ 2 ≤ 1 / s := by
    rw [div_le_div_iff₀ (by positivity) hs0]
    nlinarith [hs, hs0]
  have e2 : 2 * ((256 : ℝ) / s ^ 2) ≤ 99 / s := by
    rw [show 2 * ((256 : ℝ) / s ^ 2) = 512 / s ^ 2 by ring,
      div_le_div_iff₀ (by positivity) hs0]
    nlinarith [hs, hs0]
  have e3 : (1 : ℝ) / s + 99 / s = 100 / s := by ring
  linarith

/-- **Bounded window sums of a non-negative integrand ⇒ summable.**  The monotone-convergence
half of `hbEulerLog_tendsto`: `g` vanishes at and below `N`, is non-negative, and every window
sum `∑_{N < n ≤ M} g` is `≤ C`. -/
private lemma n9_summable_window {N : ℕ} {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (hzero : ∀ n, n ≤ N → g n = 0) {C : ℝ} (hC : ∀ M : ℕ, ∑ n ∈ Finset.Ioc N M, g n ≤ C) :
    Summable g := by
  classical
  refine summable_of_sum_range_le (c := C) hg (fun m => ?_)
  have heq : ∑ n ∈ Finset.range m, g n
      = ∑ n ∈ (Finset.range m).filter (fun n => N < n), g n := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hn' => ?_)).symm
    have hlt : ¬ N < n := fun h => hn' (Finset.mem_filter.mpr ⟨hn, h⟩)
    exact hzero n (not_lt.mp hlt)
  have hsub : (Finset.range m).filter (fun n => N < n) ⊆ Finset.Ioc N m := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ioc.mpr ⟨hn.2, le_of_lt hn.1⟩
  rw [heq]
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hg n)) (hC m)

/-- The window sum of a summable integrand vanishing at and below `N` converges as `Y → ∞`. -/
private lemma n9_window_tendsto {N : ℕ} {g : ℕ → ℝ} (hg : Summable g)
    (hzero : ∀ n, n ≤ N → g n = 0) :
    Tendsto (fun Y : ℝ => ∑ n ∈ Finset.Ioc N ⌊Y⌋₊, g n) atTop (𝓝 (∑' n, g n)) := by
  classical
  have hnat : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, g n) atTop (𝓝 (∑' n, g n)) :=
    hg.hasSum.tendsto_sum_nat
  have hfl : Tendsto (fun Y : ℝ => ⌊Y⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun Y : ℝ => Nat.le_succ ⌊Y⌋₊) tendsto_nat_floor_atTop
  refine (hnat.comp hfl).congr (fun Y => ?_)
  simp only [Function.comp_apply]
  refine (Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)).symm
  · rw [Finset.mem_Ioc] at hn
    exact Finset.mem_range.mpr (by omega)
  · rw [Finset.mem_range] at hn
    have hlt : ¬ N < n := fun h => hn' (Finset.mem_Ioc.mpr ⟨h, by omega⟩)
    exact hzero n (not_lt.mp hlt)

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
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, -, -, -, -, -⟩ := n9_num_facts hR
  have hq2 : 2 ≤ q := n9_two_le_q hR
  have hN3 : 3 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  -- `β₀ ≥ 19/20`: `1 − β₀ = 1/(ηL)` with `η ≥ 20` and `L ≥ 1.5·10⁶`
  have hone : (1 - β₀) * (η * Real.log q) = 1 := by rw [hηL]; field_simp
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha0 : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb0 : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hηnum : (20 : ℝ) ≤ η := by
    have hE1 := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    have hge : (3000001 : ℝ) ≤ Real.log η := by linarith
    have h := Real.exp_le_exp.mpr hge
    rw [Real.exp_log hηpos] at h
    have h2 := Real.add_one_le_exp (3000001 : ℝ)
    linarith
  have hprod : (20 : ℝ) ≤ η * Real.log q := by
    have h := mul_le_mul_of_nonneg_right hηnum hL.le
    linarith only [h, hLhuge]
  have hβ19 : (19 : ℝ) / 20 ≤ β₀ := by nlinarith only [hone, hβpos, hprod]
  -- the analytic input: the `Λ`-series converges from a high base point, hence from `z`
  obtain ⟨X₀, -, hX₀⟩ :=
    logChiSum_tendsto_zfr_hundred (σa := 9 / 10) (σb := 19 / 20) (c₀ := 1 / 126848)
      χ hR.prim hq2 (by linarith) le_rfl (by norm_num) (by norm_num) (by norm_num)
      (by linarith) hR.β1 hβ19 hR.zero (by norm_num)
      (fun ρ hρ hre hor => zero_free_region_all_numeral q χ hR.prim hR.ne hρ hre hor)
      (real_zeros_below_zfrCeil hR)
  obtain ⟨S, hS, -⟩ := hX₀ (max X₀ z) (le_max_left _ _)
  have hzX : z ≤ max X₀ z := le_max_right _ _
  have hlimre : Tendsto (fun Y : ℝ => (logChiSum χ z Y).re) atTop
      (𝓝 ((logChiSum χ z (max X₀ z)).re + S.re)) := by
    have hXre : Tendsto (fun Y : ℝ => (logChiSum χ (max X₀ z) Y).re) atTop (𝓝 S.re) :=
      (Complex.continuous_re.tendsto S).comp hS
    have hsum : Tendsto (fun Y : ℝ => (logChiSum χ z (max X₀ z)).re
        + (logChiSum χ (max X₀ z) Y).re) atTop
        (𝓝 ((logChiSum χ z (max X₀ z)).re + S.re)) := tendsto_const_nhds.add hXre
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (max X₀ z)] with Y hY
    rw [← Complex.add_re, ← logChiSum_add χ hzX hY]
  -- the three non-negative windows: the log-series remainder and the two detector halves
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun n => if ⌊z⌋₊ < n ∧ Nat.Prime n then
      -Real.log (1 - Salt.TwinBar.chiRe χ n / (n : ℝ)) - Salt.TwinBar.chiRe χ n / (n : ℝ)
    else 0 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun n =>
      if ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1 then
        2 * (wLog n * ArithmeticFunction.vonMangoldt n) else 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun n =>
      if ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q then
        wLog n * ArithmeticFunction.vonMangoldt n else 0 := ⟨_, rfl⟩
  have hxabs : ∀ n : ℕ, Nat.Prime n → |Salt.TwinBar.chiRe χ n / (n : ℝ)| ≤ 1 / 2 := by
    intro n hn
    have hp2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
    have hp0 : (0 : ℝ) < (n : ℝ) := by linarith
    rw [abs_div, abs_of_pos hp0, div_le_div_iff₀ hp0 (by norm_num)]
    linarith [chiReTB_abs_le_one χ n]
  have hepos : ∀ n, 0 ≤ e n := by
    intro n
    simp only [he]
    by_cases hcase : ⌊z⌋₊ < n ∧ Nat.Prime n
    · rw [if_pos hcase]
      have hx := abs_le.mp (hxabs n hcase.2)
      have h1 : (0 : ℝ) < 1 - Salt.TwinBar.chiRe χ n / (n : ℝ) := by linarith [hx.2]
      have h2 := Real.log_le_sub_one_of_pos h1
      linarith
    · rw [if_neg hcase]
  have hwΛ : ∀ n : ℕ, ⌊z⌋₊ < n → 0 ≤ wLog n * ArithmeticFunction.vonMangoldt n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact mul_nonneg (wLog_nonneg hn1) vonMangoldt_nonneg
  have hapos : ∀ n, 0 ≤ a n := by
    intro n
    simp only [ha]
    by_cases hcase : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1
    · rw [if_pos hcase]; linarith [hwΛ n hcase.1]
    · rw [if_neg hcase]
  have hbpos : ∀ n, 0 ≤ b n := by
    intro n
    simp only [hb]
    by_cases hcase : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q
    · rw [if_pos hcase]; exact hwΛ n hcase.1
    · rw [if_neg hcase]
  have hezero : ∀ n, n ≤ ⌊z⌋₊ → e n = 0 := by
    intro n hn; simp only [he]; exact if_neg (fun h => absurd h.1 (not_lt.mpr hn))
  have hazero : ∀ n, n ≤ ⌊z⌋₊ → a n = 0 := by
    intro n hn; simp only [ha]; exact if_neg (fun h => absurd h.1 (not_lt.mpr hn))
  have hbzero : ∀ n, n ≤ ⌊z⌋₊ → b n = 0 := by
    intro n hn; simp only [hb]; exact if_neg (fun h => absurd h.1 (not_lt.mpr hn))
  -- the `e`-window IS the log-series remainder
  have hcE : ∀ Y : ℝ, ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, e n
      = hbEulerLog χ z Y - ∑ p ∈ windowPrimes z Y, Salt.TwinBar.chiRe χ p / (p : ℝ) := by
    intro Y
    have hstep : ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, e n
        = ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, if Nat.Prime n then
            -Real.log (1 - Salt.TwinBar.chiRe χ n / (n : ℝ))
              - Salt.TwinBar.chiRe χ n / (n : ℝ) else 0 := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_Ioc] at hn
      simp only [he]
      by_cases hp : Nat.Prime n
      · rw [if_pos (⟨hn.1, hp⟩ : ⌊z⌋₊ < n ∧ Nat.Prime n), if_pos hp]
      · rw [if_neg (fun h : ⌊z⌋₊ < n ∧ Nat.Prime n => hp h.2), if_neg hp]
    rw [hstep, ← Finset.sum_filter, hbEulerLog, windowPrimes, ← Finset.sum_sub_distrib]
  have hppd : ∀ Y : ℝ, ppDefect z Y
      = ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊,
          if ¬ Nat.Prime n then wLog n * ArithmeticFunction.vonMangoldt n else 0 := by
    intro Y; rw [ppDefect, Finset.sum_filter]
  have hcA : ∀ Y : ℝ, ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, a n ≤ 2 * ppDefect z Y := by
    intro Y
    rw [hppd Y, Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mem_Ioc] at hn
    have hw := hwΛ n hn.1
    simp only [ha]
    by_cases hp : Nat.Prime n
    · rw [if_neg (fun h : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1 => h.2.1 hp),
        if_neg (not_not.mpr hp)]
      norm_num
    · rw [if_pos hp]
      by_cases hc : Salt.TwinBar.chiRe χ n = 1
      · rw [if_pos (⟨hn.1, hp, hc⟩ :
          ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1)]
      · rw [if_neg (fun h : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1 =>
          hc h.2.2)]
        linarith
  have hcB : ∀ Y : ℝ, ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, b n ≤ ppDefect z Y := by
    intro Y
    rw [hppd Y]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mem_Ioc] at hn
    have hw := hwΛ n hn.1
    simp only [hb]
    by_cases hp : Nat.Prime n
    · rw [if_neg (fun h : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q => h.2.1 hp),
        if_neg (not_not.mpr hp)]
    · rw [if_pos hp]
      by_cases hc : Nat.Coprime n q
      · rw [if_pos (⟨hn.1, hp, hc⟩ : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q)]
      · rw [if_neg (fun h : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q => hc h.2.2)]
        linarith
  -- the three uniform ceilings
  have hEbnd : ∀ M : ℕ, ∑ n ∈ Finset.Ioc ⌊z⌋₊ M, e n ≤ 2 / (⌊z⌋₊ : ℝ) := by
    intro M
    have h := hcE (M : ℝ)
    rw [Nat.floor_natCast M] at h
    rw [h]
    refine le_trans (le_abs_self _) ?_
    exact le_trans (hbEulerLog_sub_primeSum_termwise χ z (M : ℝ))
      (sum_two_div_sq_windowPrimes_le (by linarith : (1 : ℝ) ≤ z))
  have hppdle : ∀ M : ℕ, ppDefect z (M : ℝ) ≤ 10 / Real.sqrt (⌊z⌋₊ : ℝ) := by
    intro M
    rcases le_or_gt z (M : ℝ) with hM | hM
    · exact ppDefect_le hz hM
    · have hMle : M ≤ ⌊z⌋₊ := Nat.le_floor hM.le
      have hemp : Finset.Ioc ⌊z⌋₊ ⌊(M : ℝ)⌋₊ = ∅ := by
        rw [Nat.floor_natCast M]; exact Finset.Ioc_eq_empty (by omega)
      rw [ppDefect, hemp, Finset.filter_empty, Finset.sum_empty]
      positivity
  have hAbnd : ∀ M : ℕ, ∑ n ∈ Finset.Ioc ⌊z⌋₊ M, a n
      ≤ 2 * (10 / Real.sqrt (⌊z⌋₊ : ℝ)) := by
    intro M
    have h := hcA (M : ℝ)
    rw [Nat.floor_natCast M] at h
    linarith [hppdle M]
  have hBbnd : ∀ M : ℕ, ∑ n ∈ Finset.Ioc ⌊z⌋₊ M, b n ≤ 10 / Real.sqrt (⌊z⌋₊ : ℝ) := by
    intro M
    have h := hcB (M : ℝ)
    rw [Nat.floor_natCast M] at h
    linarith [hppdle M]
  have hse : Summable e := n9_summable_window hepos hezero hEbnd
  have hsa : Summable a := n9_summable_window hapos hazero hAbnd
  have hsb : Summable b := n9_summable_window hbpos hbzero hBbnd
  have hlimd : Tendsto (fun Y : ℝ => ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, (e n - a n + b n)) atTop
      (𝓝 ((∑' n, e n) - (∑' n, a n) + (∑' n, b n))) := by
    have h1 := n9_window_tendsto hse hezero
    have h2 := n9_window_tendsto hsa hazero
    have h3 := n9_window_tendsto hsb hbzero
    refine ((h1.sub h2).add h3).congr (fun Y => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  -- the identity: `hbEulerLog = (logChiSum).re + (e − a + b)-window`
  have hid : ∀ Y : ℝ, (logChiSum χ z Y).re
      + ∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, (e n - a n + b n) = hbEulerLog χ z Y := by
    intro Y
    have hptw : ∀ n ∈ Finset.Ioc ⌊z⌋₊ ⌊Y⌋₊, e n - a n + b n
        = (if Nat.Prime n then -Real.log (1 - Salt.TwinBar.chiRe χ n / (n : ℝ)) else 0)
          - wLog n * ArithmeticFunction.vonMangoldt n * Salt.TwinBar.chiRe χ n := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      by_cases hp : Nat.Prime n
      · have hp2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
        have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
        have hwl : wLog (n : ℝ) * ArithmeticFunction.vonMangoldt n = 1 / (n : ℝ) := by
          rw [wLog, vonMangoldt_apply_prime hp]
          field_simp
        have hna : ¬ (⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1) :=
          fun h => h.2.1 hp
        have hnb : ¬ (⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q) := fun h => h.2.1 hp
        simp only [he, ha, hb]
        rw [if_pos (⟨hn.1, hp⟩ : ⌊z⌋₊ < n ∧ Nat.Prime n), if_pos hp, if_neg hna, if_neg hnb,
          hwl]
        ring
      · have hchi := chiRe_eq_two_mul_ind_sub χ hR.sq n
        obtain ⟨I1, hI1⟩ : ∃ I1 : ℝ,
            I1 = (if Salt.TwinBar.chiRe χ n = 1 then (1 : ℝ) else 0) := ⟨_, rfl⟩
        obtain ⟨I2, hI2⟩ : ∃ I2 : ℝ,
            I2 = (if Nat.Coprime n q then (1 : ℝ) else 0) := ⟨_, rfl⟩
        rw [← hI1, ← hI2] at hchi
        have hA : a n = 2 * (wLog (n : ℝ) * ArithmeticFunction.vonMangoldt n) * I1 := by
          rw [hI1]; simp only [ha]
          by_cases hc : Salt.TwinBar.chiRe χ n = 1
          · rw [if_pos (⟨hn.1, hp, hc⟩ :
              ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1), if_pos hc]
            ring
          · rw [if_neg (fun h : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1 =>
              hc h.2.2), if_neg hc]
            ring
        have hB : b n = (wLog (n : ℝ) * ArithmeticFunction.vonMangoldt n) * I2 := by
          rw [hI2]; simp only [hb]
          by_cases hc : Nat.Coprime n q
          · rw [if_pos (⟨hn.1, hp, hc⟩ : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q),
              if_pos hc]
            ring
          · rw [if_neg (fun h : ⌊z⌋₊ < n ∧ ¬ Nat.Prime n ∧ Nat.Coprime n q => hc h.2.2),
              if_neg hc]
            ring
        have hE : e n = 0 := by
          simp only [he]
          exact if_neg (fun h : ⌊z⌋₊ < n ∧ Nat.Prime n => hp h.2)
        rw [hE, hA, hB, if_neg hp, hchi]
        ring
    rw [Finset.sum_congr rfl hptw, Finset.sum_sub_distrib, ← Finset.sum_filter,
      ← logChiSum_re_eq_sum χ hR.sq z Y]
    simp only [hbEulerLog, windowPrimes]
    ring
  exact ⟨(logChiSum χ z (max X₀ z)).re + S.re
    + ((∑' n, e n) - (∑' n, a n) + (∑' n, b n)), (hlimre.add hlimd).congr (fun Y => hid Y)⟩

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
  obtain ⟨A, hlimP⟩ := hbEulerLog_tendsto hR hz
  have hXre : Tendsto (fun Y : ℝ => (logChiSum χ X Y).re) atTop (𝓝 S.re) :=
    (Complex.continuous_re.tendsto S).comp hS
  have hlimS : Tendsto (fun Y : ℝ => (logChiSum χ z Y).re) atTop
      (𝓝 ((logChiSum χ z X).re + S.re)) := by
    have hsum : Tendsto (fun Y : ℝ => (logChiSum χ z X).re + (logChiSum χ X Y).re) atTop
        (𝓝 ((logChiSum χ z X).re + S.re)) := tendsto_const_nhds.add hXre
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop X] with Y hY
    rw [← Complex.add_re, ← logChiSum_add χ hzX hY]
  exact hb_hcorr_closed χ hR.sq hz hlimP hlimS

/-- **The `(L2)` constant** (a ceiling): the `e^{250}` of the kill times the packet's `Cs`. -/
noncomputable def n9K2 : ℝ := Real.exp 260 * (802 + 4 * n9Cs)

/-- `t² ≤ 4·e^t` on the non-negatives (`e^{t/2} ≥ t/2`, squared). -/
private lemma n9_sq_le_exp {t : ℝ} (ht : 0 ≤ t) : t ^ 2 ≤ 4 * Real.exp t := by
  have h := Real.add_one_le_exp (t / 2)
  have h2 : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  nlinarith only [h, h2, ht, (Real.exp_pos (t / 2)).le]

/-- **THE `z`-SCALE PACKET** — the arithmetic core of `hbZ_packet`, re-exported for the two
ledgers: `z₀ = 10⁻⁴·log ℓ′ ≥ 300`, the exponent `W = L/z₀ ≥ 10⁴·e^{10⁶}` (and `≤ L/300`), and
`log z` bracketed by `W` and `W + 1`. -/
private lemma n9_scale [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) :
    0 < hbZ0 q η ∧ 300 ≤ hbZ0 q η
      ∧ 10000 * Real.exp (10 ^ 6 : ℝ) ≤ Real.log q / hbZ0 q η
      ∧ Real.log q / hbZ0 q η ≤ Real.log q / 300
      ∧ Real.log q / hbZ0 q η ≤ Real.log (hbZ q η : ℝ)
      ∧ Real.log (hbZ q η : ℝ) ≤ Real.log q / hbZ0 q η + 1 := by
  obtain ⟨hqR, hL, hEll, hLhuge, hPleL⟩ := n9_z_regime hR
  have hEllpos : 0 < n9Ell q η := lt_of_lt_of_le (Real.exp_pos _) hEll
  have hLnum : (1500000 : ℝ) ≤ Real.log q := by
    have h := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    linarith only [h, hLhuge]
  have hPlog : (3 : ℝ) * 10 ^ 6 ≤ Real.log (n9Ell q η) := by
    have h := Real.log_le_log (Real.exp_pos (3 * 10 ^ 6 : ℝ)) hEll
    rwa [Real.log_exp] at h
  have hPpos : 0 < Real.log (n9Ell q η) := by linarith only [hPlog]
  have hz0 : hbZ0 q η = 1 / 10000 * Real.log (n9Ell q η) := by simp only [hbZ0, hbZ0A]
  have hz0pos : 0 < hbZ0 q η := by rw [hz0]; linarith only [hPpos]
  have hz0ge : (300 : ℝ) ≤ hbZ0 q η := by rw [hz0]; linarith only [hPlog]
  have hMpos : (0 : ℝ) < Real.exp (10 ^ 6 : ℝ) := Real.exp_pos _
  have hexp1 : (1000001 : ℝ) ≤ Real.exp (10 ^ 6 : ℝ) := by
    have h := Real.add_one_le_exp (10 ^ 6 : ℝ); linarith only [h]
  have hMle : 4 * Real.exp (10 ^ 6 : ℝ) ^ 2 ≤ Real.log q := by
    have hsq : Real.exp (10 ^ 6 : ℝ) ^ 2 = Real.exp (2 * 10 ^ 6 : ℝ) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have h2pos : (0 : ℝ) < Real.exp (2 * 10 ^ 6 : ℝ) := Real.exp_pos _
    have hmul : Real.exp (10 ^ 6 : ℝ) * Real.exp (2 * 10 ^ 6 : ℝ)
        = Real.exp (3 * 10 ^ 6 : ℝ) := by rw [← Real.exp_add]; ring_nf
    have hprod : 1000001 * Real.exp (2 * 10 ^ 6 : ℝ)
        ≤ Real.exp (10 ^ 6 : ℝ) * Real.exp (2 * 10 ^ 6 : ℝ) :=
      mul_le_mul_of_nonneg_right hexp1 h2pos.le
    rw [hmul] at hprod
    rw [hsq]
    linarith only [hprod, hLhuge, h2pos]
  have hlogL : Real.log (Real.log q) ≤ Real.log q / Real.exp (10 ^ 6 : ℝ) :=
    n9_log_le_div hMpos hMle
  have hPL : Real.exp (10 ^ 6 : ℝ) * Real.log (n9Ell q η) ≤ Real.log q := by
    have h1 : Real.log (n9Ell q η) ≤ Real.log q / Real.exp (10 ^ 6 : ℝ) :=
      le_trans hPleL hlogL
    rw [le_div_iff₀ hMpos] at h1
    linarith only [h1]
  have hWbig : 10000 * Real.exp (10 ^ 6 : ℝ) ≤ Real.log q / hbZ0 q η := by
    have heq : 10000 * Real.exp (10 ^ 6 : ℝ) * (1 / 10000 * Real.log (n9Ell q η))
        = Real.exp (10 ^ 6 : ℝ) * Real.log (n9Ell q η) := by ring
    rw [le_div_iff₀ hz0pos, hz0, heq]
    exact hPL
  have hWle : Real.log q / hbZ0 q η ≤ Real.log q / 300 :=
    div_le_div_of_nonneg_left hL.le (by norm_num) hz0ge
  have hWpos : 0 < Real.log q / hbZ0 q η := div_pos hL hz0pos
  obtain ⟨hzlo, hzhi⟩ := hbZ_bounds q η hz0pos
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith only [hqR]
  have hrp : (q : ℝ) ^ (1 / hbZ0 q η) = Real.exp (Real.log q / hbZ0 q η) := by
    rw [Real.rpow_def_of_pos hqpos, mul_one_div]
  have hzge : Real.exp (Real.log q / hbZ0 q η) ≤ (hbZ q η : ℝ) := by rw [← hrp]; exact hzlo
  have hzpos : (0 : ℝ) < (hbZ q η : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hzge
  have hzhi' : (hbZ q η : ℝ) < Real.exp (Real.log q / hbZ0 q η) + 1 := by
    rw [← hrp]; exact hzhi
  have hzle : (hbZ q η : ℝ) ≤ Real.exp (Real.log q / hbZ0 q η + 1) := by
    have hE : (1 : ℝ) ≤ Real.exp (Real.log q / hbZ0 q η) := by
      have h := Real.add_one_le_exp (Real.log q / hbZ0 q η)
      linarith only [h, hWpos]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ); linarith only [h]
    rw [Real.exp_add]
    nlinarith only [hzhi', hE, he1]
  have hlogzge : Real.log q / hbZ0 q η ≤ Real.log (hbZ q η : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hzge
    rwa [Real.log_exp] at h
  have hlogzle : Real.log (hbZ q η : ℝ) ≤ Real.log q / hbZ0 q η + 1 := by
    have h := Real.log_le_log hzpos hzle
    rwa [Real.log_exp] at h
  exact ⟨hz0pos, hz0ge, hWbig, hWle, hlogzge, hlogzle⟩

set_option maxHeartbeats 1000000 in
-- One ledger over the six binders of `hb_L2_at_split_point_charTrio`, with the opaque
-- constants `merC`, `segC`, `invSqC` absorbed by the two exponential parts of `n9E0`.
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
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, hPbig, hPsmall, hlog4qpos, hW2L, -⟩ := n9_num_facts hR
  obtain ⟨hz0pos, hz0ge, hWbig, hWle, hlogzge, hlogzle⟩ := n9_scale hR
  obtain ⟨hz2, -, -, hzx, -, h32, h4z, -, -, -, -⟩ := hbZ_packet hR hx hx'
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hqpos : 0 < q := by omega
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith only [hqR]
  have hLne : Real.log q ≠ 0 := ne_of_gt hL
  -- `ℓ′` and its four largeness facts
  have hEpos : (0 : ℝ) < n9Ell q η := by linarith only [hPbig]
  have hEsqrt : (0 : ℝ) < Real.sqrt (n9Ell q η) := Real.sqrt_pos.mpr hEpos
  have hEsq : Real.sqrt (n9Ell q η) ^ 2 = n9Ell q η := Real.sq_sqrt hEpos.le
  have hlogE : (14 : ℝ) ≤ Real.log (n9Ell q η) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3000001) hPbig
    have h2 : (14 : ℝ) ≤ Real.log 3000001 := by
      rw [show (14 : ℝ) = Real.log (Real.exp 14) by rw [Real.log_exp]]
      refine Real.log_le_log (Real.exp_pos _) ?_
      have he : Real.exp 14 = Real.exp 1 ^ 14 := by
        rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      have h1 := Real.exp_one_lt_d9
      have h3 : Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt h1) 14
      rw [he]; norm_num at h3 ⊢; linarith only [h3]
    linarith only [h, h2]
  have hlogEsq : Real.log (n9Ell q η) ≤ 2 * Real.sqrt (n9Ell q η) :=
    n9_log_le_two_sqrt hEpos
  -- the constant `ec = 802 + 4·n9Cs`
  obtain ⟨ec, hecdef⟩ : ∃ ec : ℝ, ec = 802 + 4 * n9Cs := ⟨_, rfl⟩
  have hn9Cs : (3400 : ℝ) ≤ n9Cs := by
    have h := invSqC_spec.1
    simp only [n9Cs, dhB]
    nlinarith only [h]
  have hec : (14402 : ℝ) ≤ ec := by rw [hecdef]; linarith only [hn9Cs]
  have hec0 : (0 : ℝ) < ec := by linarith only [hec]
  -- `ℓ′ ≥ (e^{300}·ec)^8` and `ℓ′ ≥ e^{merC+segC}`
  have hE0parts : (Real.exp 300 * ec) ^ 8 ≤ n9Ell q η ∧ Real.exp (merC + segC) ≤ n9Ell q η := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * ec) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    have hc : (0 : ℝ) < Real.exp (3 * 10 ^ 6 : ℝ) := Real.exp_pos _
    have h := hR.ellBig
    simp only [n9E0, ← hecdef] at h
    exact ⟨by linarith only [h, hb, hc], by linarith only [h, ha, hc]⟩
  obtain ⟨hEec, hEms⟩ := hE0parts
  have hS0 : (0 : ℝ) ≤ merC + segC := by
    have := merC_spec.1; have := segC_spec.1; linarith
  have hSlog : merC + segC ≤ Real.log (n9Ell q η) := by
    have h := Real.log_le_log (Real.exp_pos (merC + segC)) hEms
    rwa [Real.log_exp] at h
  -- `ℓ′ ≤ log η`, hence `η ≥ e^{300}·L^{16}`
  have hEllLogη : n9Ell q η ≤ Real.log η := by
    have hinv : 0 ≤ Real.log (1 / dhC) :=
      Real.log_nonneg (by rw [le_div_iff₀ dh_spec.1]; linarith [dh_spec.2.1])
    have hLle : Real.log q ≤ Real.log (4 * (q : ℝ)) + 2 := by
      have h : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
        Real.log_le_log hqR0 (by linarith only [hqR0])
      linarith only [h]
    have hlogLle : Real.log (Real.log q) ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      Real.log_le_log hL hLle
    have hXnn : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      Real.log_nonneg (by linarith only [hlog4qpos])
    have hdk : dhK = 14 := rfl
    have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
      Real.log_mul (ne_of_gt hηpos) hLne
    simp only [n9Ell, hdk, hsplit]
    linarith only [hinv, hlogLle, hXnn]
  have hloglog : Real.log (Real.log q) ≤ Real.log (Real.log (4 * (q : ℝ))) := by
    refine Real.log_le_log hL ?_
    exact Real.log_le_log hqR0 (by linarith only [hqR0])
  have hE0nn : (0 : ℝ) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    have hc : (0 : ℝ) < Real.exp (3 * 10 ^ 6 : ℝ) := Real.exp_pos _
    simp only [n9E0]; linarith only [ha, hb, hc]
  have hE0big : (300 : ℝ) ≤ n9E0 := by
    have hc := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith only [ha, hb, hc]
  have h16L : 16 * Real.log (Real.log q) + 300 ≤ n9Ell q η := by
    linarith only [hR.ellL, hloglog, hE0big]
  have hηhuge : Real.exp 300 * Real.log q ^ 16 ≤ η := by
    have h1 : Real.exp (300 + 16 * Real.log (Real.log q)) ≤ Real.exp (Real.log η) :=
      Real.exp_le_exp.mpr (by linarith only [h16L, hEllLogη])
    rw [Real.exp_log hηpos] at h1
    have h2 : Real.exp (300 + 16 * Real.log (Real.log q))
        = Real.exp 300 * Real.log q ^ 16 := by
      rw [Real.exp_add, show (16 : ℝ) * Real.log (Real.log q)
        = ((16 : ℕ) : ℝ) * Real.log (Real.log q) by norm_num, Real.exp_nat_mul,
        Real.exp_log hL]
    linarith only [h1, h2]
  have hηnum : (3000002 : ℝ) ≤ η := by
    have h1 : Real.exp (3000001 : ℝ) ≤ η := by
      have h := Real.exp_le_exp.mpr (show (3000001 : ℝ) ≤ Real.log η by
        linarith only [hEllLogη, hPbig])
      rwa [Real.exp_log hηpos] at h
    have h2 := Real.add_one_le_exp (3000001 : ℝ)
    linarith only [h1, h2]
  have hm1 : zeroMult χ (β₀ : ℂ) = 1 :=
    zeroMult_eq_one_of_eta (η := η) hR.prim hR.ne hR.zero (by rw [hR.ηdef, one_div])
      (by linarith only [hηnum])
  -- the split point `z = hbZ − 1`
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = (hbZ q η : ℝ) - 1 := ⟨_, rfl⟩
  have hz32 : (32 : ℝ) ≤ z := by rw [hzdef]; exact h32
  have hz3 : (3 : ℝ) ≤ z := by linarith only [hz32]
  have hz4 : (4 : ℝ) < z := by rw [hzdef]; exact h4z
  have hZ2 : (2 : ℝ) ≤ (hbZ q η : ℝ) := by exact_mod_cast hz2
  have hfl : (⌊z⌋₊ : ℝ) = z := by
    have h1 : (1 : ℕ) ≤ hbZ q η := le_trans (by norm_num) hz2
    have h2 : z = ((hbZ q η - 1 : ℕ) : ℝ) := by
      rw [hzdef, Nat.cast_sub h1]; norm_num
    rw [h2, Nat.floor_natCast]
  -- `log z ≥ 5000·L/log ℓ′`
  have hWpos : (0 : ℝ) < Real.log q / hbZ0 q η := div_pos hL hz0pos
  have hlogz : 5000 * Real.log q / Real.log (n9Ell q η) ≤ Real.log z := by
    have hzhalf : (hbZ q η : ℝ) / 2 ≤ z := by rw [hzdef]; linarith only [hZ2]
    have hlogzge' : Real.log ((hbZ q η : ℝ) / 2) ≤ Real.log z :=
      Real.log_le_log (by linarith only [hZ2]) hzhalf
    have hsplit : Real.log ((hbZ q η : ℝ) / 2) = Real.log (hbZ q η : ℝ) - Real.log 2 :=
      Real.log_div (by linarith only [hZ2]) (by norm_num)
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
    have hz0small : hbZ0 q η ≤ Real.log q / 10000 := by
      have hz0eq : hbZ0 q η = 1 / 10000 * Real.log (n9Ell q η) := by
        simp only [hbZ0, hbZ0A]
      have hle : Real.log (n9Ell q η) ≤ Real.log q := by
        have h1 : Real.log (n9Ell q η) ≤ n9Ell q η := by
          linarith only [Real.log_le_sub_one_of_pos hEpos]
        linarith only [h1, hPsmall, hL]
      rw [hz0eq]; linarith only [hle]
    have hWhalf : Real.log q / hbZ0 q η / 2 ≤ Real.log q / hbZ0 q η - 1 := by
      have h2 : (10000 : ℝ) ≤ Real.log q / hbZ0 q η := by
        rw [le_div_iff₀ hz0pos]
        nlinarith only [hz0small, hL, hz0pos]
      linarith only [h2]
    have hWeq : Real.log q / hbZ0 q η = 10000 * Real.log q / Real.log (n9Ell q η) := by
      have hz0 : hbZ0 q η = 1 / 10000 * Real.log (n9Ell q η) := by
        simp only [hbZ0, hbZ0A]
      rw [hz0]
      have hPpos : (0 : ℝ) < Real.log (n9Ell q η) := by linarith only [hlogE]
      field_simp
    have h5000 : 5000 * Real.log q / Real.log (n9Ell q η)
        = 10000 * Real.log q / Real.log (n9Ell q η) / 2 := by ring
    rw [h5000, ← hWeq]
    linarith only [hlogzge, hlogzge', hsplit, hlog2, hWhalf]
  have hlogzpos : (0 : ℝ) < Real.log z := by
    have h1 : (0 : ℝ) < 5000 * Real.log q / Real.log (n9Ell q η) := by
      have : (0 : ℝ) < Real.log (n9Ell q η) := by linarith only [hlogE]
      positivity
    linarith only [hlogz, h1]
  -- `log z ≥ 25000·√L` and `z ≥ 10⁸·L`
  have hsqL : Real.sqrt (Real.log q) ^ 2 = Real.log q := Real.sq_sqrt hL.le
  have hsqLpos : (0 : ℝ) < Real.sqrt (Real.log q) := Real.sqrt_pos.mpr hL
  have hsqLbig : (1224 : ℝ) ≤ Real.sqrt (Real.log q) := by
    rw [show (1224 : ℝ) = Real.sqrt (1224 ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1224)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith only [hLhuge])
  have hEsqL : 10 * Real.sqrt (n9Ell q η) ≤ Real.sqrt (Real.log q) := by
    have h1 : Real.sqrt (100 * n9Ell q η) ≤ Real.sqrt (Real.log q) :=
      Real.sqrt_le_sqrt (by linarith only [hPsmall])
    have h2 : Real.sqrt (100 * n9Ell q η) = 10 * Real.sqrt (n9Ell q η) := by
      rw [show (100 : ℝ) * n9Ell q η = 10 ^ 2 * n9Ell q η by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10)]
    linarith only [h1, h2]
  have hlogzsq : 25000 * Real.sqrt (Real.log q) ≤ Real.log z := by
    have h1 : 5000 * Real.log q / Real.log (n9Ell q η)
        ≥ 2500 * Real.log q / Real.sqrt (n9Ell q η) := by
      rw [ge_iff_le, div_le_div_iff₀ hEsqrt (by linarith only [hlogE])]
      nlinarith only [hlogEsq, hL, hEsqrt]
    have h2 : 2500 * Real.log q / Real.sqrt (n9Ell q η) ≥ 25000 * Real.sqrt (Real.log q) := by
      rw [ge_iff_le, le_div_iff₀ hEsqrt]
      nlinarith only [hEsqL, hsqL, hsqLpos, hEsqrt]
    linarith only [hlogz, h1, h2]
  have hzsq : Real.log z ^ 2 ≤ 4 * z := by
    have h1 : Real.log z ^ 2 ≤ 4 * Real.exp (Real.log z) := n9_sq_le_exp hlogzpos.le
    rw [Real.exp_log (by linarith only [hz3])] at h1
    exact h1
  have hzbig : 100000000 * Real.log q ≤ z := by
    nlinarith only [hzsq, hlogzsq, hsqL, hsqLpos, hsqLbig]
  have hz0' : (0 : ℝ) < z := by linarith only [hz3]
  have hsqz : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0'.le
  have hsqzbig : 10000 * Real.sqrt (Real.log q) ≤ Real.sqrt z := by
    have h1 : Real.sqrt (100000000 * Real.log q) ≤ Real.sqrt z := Real.sqrt_le_sqrt hzbig
    have h2 : Real.sqrt (100000000 * Real.log q) = 10000 * Real.sqrt (Real.log q) := by
      rw [show (100000000 : ℝ) * Real.log q = 10000 ^ 2 * Real.log q by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10000)]
    linarith only [h1, h2]
  -- the window `[q^250, q^500]`
  have hq250 : Real.exp (250 * Real.log q) = (q : ℝ) ^ (250 : ℕ) := by
    rw [show (250 : ℝ) * Real.log q = ((250 : ℕ) : ℝ) * Real.log q by norm_num,
      Real.exp_nat_mul, Real.exp_log hqR0]
  have hq500 : Real.exp (500 * Real.log q) = (q : ℝ) ^ (500 : ℕ) := by
    rw [show (500 : ℝ) * Real.log q = ((500 : ℕ) : ℝ) * Real.log q by norm_num,
      Real.exp_nat_mul, Real.exp_log hqR0]
  have hx250 : Real.exp (250 * Real.log q) ≤ (x : ℝ) := by rw [hq250]; exact hx
  have hXbig : (375000000 : ℝ) ≤ (x : ℝ) := by
    have h := Real.add_one_le_exp (250 * Real.log q)
    linarith only [h, hx250, hLhuge]
  have hXpos : (0 : ℝ) < (x : ℝ) := by linarith only [hXbig]
  have hX3 : (3 : ℝ) ≤ (x : ℝ) := by linarith only [hXbig]
  have hlogX : 250 * Real.log q ≤ Real.log (x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (250 * Real.log q)) hx250
    rwa [Real.log_exp] at h
  have hwinX : Real.log (x : ℝ) ≤ 500 * Real.log q := by
    have h := Real.log_le_log hXpos hx'
    rw [← hq500, Real.log_exp] at h
    exact h
  have hzX : z ≤ (x : ℝ) := by
    have hsq3 : (1 : ℝ) ≤ (hbZ q η : ℝ) ^ 2 := by nlinarith only [hZ2]
    have h1 : (hbZ q η : ℝ) ≤ (hbZ q η : ℝ) ^ 3 := by nlinarith only [hsq3, hZ2]
    have h2 : (hbZ q η : ℝ) ^ 3 ≤ (x : ℝ) := hzx
    rw [hzdef]; linarith only [h1, h2]
  -- the four binders of `hb_L2_at_split_point_charTrio`
  obtain ⟨S, hS, htail⟩ := logChiSum_tail_at_window hR hx
  have hcorr := hcorr_at_split hR hz3 hzX hS
  have hkill := chiOne_kill_at_hb_point hR hz3 hXpos.le hwinX
  rw [← hecdef] at hkill
  obtain ⟨Ek, hEkdef⟩ : ∃ Ek : ℝ, Ek = Real.exp 250 * ((1 - β₀) * (2 * Real.log q) ^ 2
      + (2 + ec * (2 * Real.log q / Real.sqrt (n9Ell q η)))) / Real.log z := ⟨_, rfl⟩
  rw [← hEkdef] at hkill
  have hseg := hb_hseg_closed χ hR.sq hqpos hz3 hzX (segC_spec.2 q hqpos hz3 hzX) hkill
  have hP := merC_spec.2 z hz3
  rw [hfl] at hcorr hseg
  -- the two shapes of the target
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.log (n9Ell q η) / Real.sqrt (n9Ell q η) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 1 / Real.sqrt (Real.log q) := ⟨_, rfl⟩
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hB0 : (0 : ℝ) < B := by rw [hBdef]; positivity
  have hBsmall : B ≤ 1 / 1224 := by
    rw [hBdef, div_le_div_iff₀ hsqLpos (by norm_num)]; linarith only [hsqLbig]
  have hsqzpos : (0 : ℝ) < Real.sqrt z := Real.sqrt_pos.mpr hz0'
  have hLsq : Real.sqrt (Real.log q) ≤ Real.log q := by
    nlinarith only [hsqL, hsqLbig, hsqLpos]
  -- `A ≤ 4/(e^{600}·ec²)` — the eighth power in `n9E0` paying the master constant
  have hA4 : A * (Real.exp 600 * ec ^ 2) ≤ 4 := by
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt (Real.sqrt (n9Ell q η)) := ⟨_, rfl⟩
    have hr0 : (0 : ℝ) < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hEsqrt
    have hrsq : r ^ 2 = Real.sqrt (n9Ell q η) := by
      rw [hrdef]; exact Real.sq_sqrt hEsqrt.le
    have hlogsplit : Real.log (n9Ell q η) ≤ 4 * r := by
      have h1 : Real.log (Real.sqrt (n9Ell q η)) ≤ 2 * r := by
        rw [hrdef]; exact n9_log_le_two_sqrt hEsqrt
      have h2 : Real.log (Real.sqrt (n9Ell q η)) = Real.log (n9Ell q η) / 2 :=
        Real.log_sqrt hEpos.le
      linarith only [h1, h2]
    have hrbig : Real.exp 600 * ec ^ 2 ≤ r := by
      have h1 : (Real.exp 300 * ec) ^ 4 ≤ Real.sqrt (n9Ell q η) := by
        refine Real.le_sqrt_of_sq_le ?_
        calc ((Real.exp 300 * ec) ^ 4) ^ 2 = (Real.exp 300 * ec) ^ 8 := by ring
          _ ≤ n9Ell q η := hEec
      rw [hrdef]
      refine Real.le_sqrt_of_sq_le ?_
      have h3 : (Real.exp 600 * ec ^ 2) ^ 2 = (Real.exp 300 * ec) ^ 4 := by
        rw [show Real.exp 600 = Real.exp 300 * Real.exp 300 by
          rw [← Real.exp_add]; norm_num]
        ring
      rw [h3]; exact h1
    have hAle : A ≤ 4 / r := by
      rw [hAdef, div_le_div_iff₀ hEsqrt hr0]
      nlinarith only [hlogsplit, hrsq, hr0]
    have hrpos : (0 : ℝ) < Real.exp 600 * ec ^ 2 := by positivity
    calc A * (Real.exp 600 * ec ^ 2) ≤ (4 / r) * r := by
          refine mul_le_mul hAle hrbig hrpos.le (by positivity)
      _ = 4 := by field_simp
  have he250 : (0 : ℝ) < Real.exp 250 := Real.exp_pos _
  -- reciprocal-scale facts (`B·√L = 1`, `B·L = √L`)
  have hBsqLeq : B * Real.sqrt (Real.log q) = 1 := by
    rw [hBdef]; field_simp
  have hBLeq : B * Real.log q = Real.sqrt (Real.log q) := by
    rw [hBdef, div_mul_eq_mul_div, one_mul, eq_comm, eq_div_iff (ne_of_gt hsqLpos)]
    nlinarith only [hsqL]
  have hBz : 100000000 * Real.sqrt (Real.log q) ≤ B * z := by
    have h1 : B * (100000000 * Real.log q) ≤ B * z :=
      mul_le_mul_of_nonneg_left hzbig hB0.le
    have h2 : B * (100000000 * Real.log q) = 100000000 * (B * Real.log q) := by ring
    linarith only [h1, h2, hBLeq]
  have hBzbig : (100000000 : ℝ) ≤ B * z := by linarith only [hBz, hsqLbig]
  have hBsqz : (10000 : ℝ) ≤ B * Real.sqrt z := by
    have h1 : B * (10000 * Real.sqrt (Real.log q)) ≤ B * Real.sqrt z :=
      mul_le_mul_of_nonneg_left hsqzbig hB0.le
    have h2 : B * (10000 * Real.sqrt (Real.log q)) = 10000 * (B * Real.sqrt (Real.log q)) := by
      ring
    linarith only [h1, h2, hBsqLeq]
  have hBlogz : (25000 : ℝ) ≤ B * Real.log z := by
    have h1 : B * (25000 * Real.sqrt (Real.log q)) ≤ B * Real.log z :=
      mul_le_mul_of_nonneg_left hlogzsq hB0.le
    have h2 : B * (25000 * Real.sqrt (Real.log q)) = 25000 * (B * Real.sqrt (Real.log q)) := by
      ring
    linarith only [h1, h2, hBsqLeq]
  -- `A·log z ≥ 5000·(L/√ℓ′)`, the shape every `1/log z` row is priced against
  have hlogEpos : (0 : ℝ) < Real.log (n9Ell q η) := by linarith only [hlogE]
  have hU0 : (0 : ℝ) ≤ Real.log q / Real.sqrt (n9Ell q η) := by positivity
  have hAlogz : 5000 * (Real.log q / Real.sqrt (n9Ell q η)) ≤ A * Real.log z := by
    have h1 : A * (5000 * Real.log q / Real.log (n9Ell q η)) ≤ A * Real.log z :=
      mul_le_mul_of_nonneg_left hlogz hA0
    have h2 : A * (5000 * Real.log q / Real.log (n9Ell q η))
        = 5000 * (Real.log q / Real.sqrt (n9Ell q η)) := by
      rw [hAdef]; field_simp
    linarith only [h1, h2]
  have hSQbig : (1000 : ℝ) ≤ Real.sqrt (n9Ell q η) := by
    rw [show (1000 : ℝ) = Real.sqrt (1000 ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1000)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith only [hPbig])
  have hUbig : (100 : ℝ) ≤ Real.log q / Real.sqrt (n9Ell q η) := by
    rw [le_div_iff₀ hEsqrt]
    nlinarith only [hEsq, hPsmall, hEsqrt, hSQbig]
  -- the rows, atom by atom
  have c1 : 2 / z ≤ B / 8 := by
    rw [div_le_div_iff₀ hz0' (by norm_num : (0 : ℝ) < 8)]; linarith only [hBzbig]
  have c2 : 10 / Real.sqrt z ≤ B / 8 := by
    rw [div_le_div_iff₀ hsqzpos (by norm_num : (0 : ℝ) < 8)]; linarith only [hBsqz]
  have c4 : 30 / Real.sqrt z ≤ B / 8 := by
    rw [div_le_div_iff₀ hsqzpos (by norm_num : (0 : ℝ) < 8)]; linarith only [hBsqz]
  have c11 : 64 / z ≤ B / 8 := by
    rw [div_le_div_iff₀ hz0' (by norm_num : (0 : ℝ) < 8)]; linarith only [hBzbig]
  have c6 : Real.log q / Real.log z / z ≤ B / 8 := by
    have h1 : Real.log q / Real.log z ≤ Real.sqrt (Real.log q) / 25000 := by
      rw [div_le_div_iff₀ hlogzpos (by norm_num : (0 : ℝ) < 25000)]
      nlinarith only [hlogzsq, hsqL, hsqLpos, hL]
    have h2 : Real.log q / Real.log z / z ≤ Real.sqrt (Real.log q) / 25000 / z := by
      rw [div_le_div_iff₀ hz0' hz0']
      nlinarith only [h1, hz0']
    have h3 : Real.sqrt (Real.log q) / 25000 / z ≤ B / 8 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
      nlinarith only [hBz, hsqLpos]
    linarith only [h2, h3]
  have c10 : 2 * (Real.log q / Real.log z) / z ≤ B / 8 := by
    have heq : 2 * (Real.log q / Real.log z) / z = 2 * (Real.log q / Real.log z / z) := by ring
    rw [heq]
    have h1 : Real.log q / Real.log z ≤ Real.sqrt (Real.log q) / 25000 := by
      rw [div_le_div_iff₀ hlogzpos (by norm_num : (0 : ℝ) < 25000)]
      nlinarith only [hlogzsq, hsqL, hsqLpos, hL]
    have h2 : Real.log q / Real.log z / z ≤ Real.sqrt (Real.log q) / 25000 / z := by
      rw [div_le_div_iff₀ hz0' hz0']
      nlinarith only [h1, hz0']
    have h3 : 2 * (Real.sqrt (Real.log q) / 25000 / z) ≤ B / 8 := by
      rw [div_div, show (2 : ℝ) * (Real.sqrt (Real.log q) / (25000 * z))
        = 2 * Real.sqrt (Real.log q) / (25000 * z) by ring,
        div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
      nlinarith only [hBz, hsqLpos]
    have h0 : (0 : ℝ) ≤ Real.log q / Real.log z / z := by positivity
    linarith only [h2, h3, h0]
  have c7 : 100 / Real.sqrt (Real.log (x : ℝ)) ≤ 7 * B := by
    have hlogXpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith only [hlogX, hL]
    have hsqXpos : (0 : ℝ) < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.mpr hlogXpos
    have hsqX : 15 * Real.sqrt (Real.log q) ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h1 : Real.sqrt (225 * Real.log q) ≤ Real.sqrt (Real.log (x : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith only [hlogX, hL])
      have h2 : Real.sqrt (225 * Real.log q) = 15 * Real.sqrt (Real.log q) := by
        rw [show (225 : ℝ) * Real.log q = 15 ^ 2 * Real.log q by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 15)]
      linarith only [h1, h2]
    have hBsqX : (15 : ℝ) ≤ B * Real.sqrt (Real.log (x : ℝ)) := by
      have h1 : B * (15 * Real.sqrt (Real.log q)) ≤ B * Real.sqrt (Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqX hB0.le
      have h2 : B * (15 * Real.sqrt (Real.log q)) = 15 * (B * Real.sqrt (Real.log q)) := by ring
      linarith only [h1, h2, hBsqLeq]
    rw [div_le_iff₀ hsqXpos]
    nlinarith only [hBsqX, hsqXpos]
  have hlogLnn : (0 : ℝ) ≤ Real.log (Real.log q) := Real.log_nonneg (by linarith only [hLhuge])
  have hηe : Real.exp 300 * Real.log q ^ 3 ≤ η := by
    have h1 : Real.exp (300 + 3 * Real.log (Real.log q)) ≤ Real.exp (Real.log η) :=
      Real.exp_le_exp.mpr (by linarith only [h16L, hEllLogη, hlogLnn])
    rw [Real.exp_log hηpos] at h1
    have h2 : Real.exp (300 + 3 * Real.log (Real.log q)) = Real.exp 300 * Real.log q ^ 3 := by
      rw [Real.exp_add, show (3 : ℝ) * Real.log (Real.log q)
        = ((3 : ℕ) : ℝ) * Real.log (Real.log q) by norm_num, Real.exp_nat_mul, Real.exp_log hL]
    linarith only [h1, h2]
  have he300 : (51 : ℝ) ≤ Real.exp 300 := by
    have := Real.add_one_le_exp (300 : ℝ); linarith only [this]
  have c8 : 500 * (1 + 2 * Real.log (η * Real.log q)) / η ≤ B / 8 := by
    have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
      Real.log_mul (ne_of_gt hηpos) hLne
    have hlogη : Real.log η ≤ Real.log q := by
      have h := hR.ηq
      have h2 := Real.add_one_le_exp (401 : ℝ)
      rcases le_or_gt 0 (Real.log η) with h3 | h3
      · nlinarith only [h, h2, h3]
      · linarith only [h3, hL]
    have hlogL : Real.log (Real.log q) ≤ Real.log q := by
      linarith only [Real.log_le_sub_one_of_pos hL]
    have hnum : 1 + 2 * Real.log (η * Real.log q) ≤ 5 * Real.log q := by
      rw [hsplit]; linarith only [hlogη, hlogL, hLhuge]
    have hBη : Real.log q ^ 2 * Real.sqrt (Real.log q) ≤ B * η := by
      have h1 : B * (Real.exp 300 * Real.log q ^ 3) ≤ B * η :=
        mul_le_mul_of_nonneg_left hηe hB0.le
      have h2 : B * (Real.exp 300 * Real.log q ^ 3)
          = Real.exp 300 * Real.log q ^ 2 * (B * Real.log q) := by ring
      have h3 : Real.exp 300 * Real.log q ^ 2 * (B * Real.log q)
          = Real.exp 300 * Real.log q ^ 2 * Real.sqrt (Real.log q) := by rw [hBLeq]
      have h4 : Real.log q ^ 2 * Real.sqrt (Real.log q)
          ≤ Real.exp 300 * Real.log q ^ 2 * Real.sqrt (Real.log q) := by
        have hnn : (0 : ℝ) ≤ Real.log q ^ 2 * Real.sqrt (Real.log q) := by positivity
        nlinarith only [he300, hnn]
      linarith only [h1, h2, h3, h4]
    rw [div_le_div_iff₀ hηpos (by norm_num : (0 : ℝ) < 8)]
    nlinarith only [hnum, hBη, hsqLbig, hLhuge, hsqLpos, hL]
  have c5 : 4 * (segC / Real.log z) + 8 * (merC / Real.log z) ≤ A / 1000 := by
    have hmer := merC_spec.1
    have hsegc := segC_spec.1
    have hSsq : merC + segC ≤ 2 * Real.sqrt (n9Ell q η) := by
      linarith only [hSlog, hlogEsq]
    have hkey : 100000 * (merC + segC) ≤ A * Real.log z := by
      have h2 : 20 * (merC + segC) ≤ Real.log q / Real.sqrt (n9Ell q η) := by
        rw [le_div_iff₀ hEsqrt]
        nlinarith only [hSsq, hEsq, hPsmall, hEsqrt]
      linarith only [h2, hAlogz]
    have h1 : segC / Real.log z ≤ A / 100000 := by
      rw [div_le_div_iff₀ hlogzpos (by norm_num : (0 : ℝ) < 100000)]
      nlinarith only [hkey, hmer, hsegc]
    have h2 : merC / Real.log z ≤ A / 100000 := by
      rw [div_le_div_iff₀ hlogzpos (by norm_num : (0 : ℝ) < 100000)]
      nlinarith only [hkey, hmer, hsegc]
    linarith only [h1, h2, hA0]
  have c3 : Ek ≤ (Real.exp 250 * ec / 1200) * A + B / 4 := by
    have hbeta : 1 - β₀ = 1 / (η * Real.log q) := by rw [hηL, one_div_one_div]
    have hEk3 : Ek = Real.exp 250 * 4 * (Real.log q / η) / Real.log z
        + Real.exp 250 * 2 / Real.log z
        + Real.exp 250 * 2 * ec * (Real.log q / Real.sqrt (n9Ell q η)) / Real.log z := by
      rw [hEkdef, hbeta]
      field_simp
      ring
    have p1 : Real.exp 250 * 4 * (Real.log q / η) / Real.log z ≤ B / 4 := by
      have hfrac : Real.log q / η ≤ 1 / (Real.exp 300 * Real.log q ^ 2) := by
        rw [div_le_div_iff₀ hηpos (by positivity)]
        nlinarith only [hηe, hL]
      have hnum : Real.exp 250 * 4 * (Real.log q / η) ≤ 1 := by
        have h1 : Real.exp 250 * 4 * (Real.log q / η)
            ≤ Real.exp 250 * 4 * (1 / (Real.exp 300 * Real.log q ^ 2)) := by
          have h0 : (0 : ℝ) ≤ Real.exp 250 * 4 := by positivity
          nlinarith only [hfrac, h0]
        have h2 : Real.exp 250 * 4 * (1 / (Real.exp 300 * Real.log q ^ 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]
          have h3 : Real.exp 250 * Real.exp 50 = Real.exp 300 := by
            rw [← Real.exp_add]; norm_num
          have h4 : (51 : ℝ) ≤ Real.exp 50 := by
            have := Real.add_one_le_exp (50 : ℝ); linarith only [this]
          have hL2 : (2250000000000 : ℝ) ≤ Real.log q ^ 2 := by nlinarith only [hLhuge]
          have h5 : (4 : ℝ) ≤ Real.exp 50 * Real.log q ^ 2 := by nlinarith only [h4, hL2]
          nlinarith only [h3, h5, he250]
        linarith only [h1, h2]
      rw [div_le_div_iff₀ hlogzpos (by norm_num : (0 : ℝ) < 4)]
      nlinarith only [hnum, hBlogz]
    have p2 : Real.exp 250 * 2 / Real.log z ≤ (Real.exp 250 * ec / 2400) * A := by
      rw [div_le_iff₀ hlogzpos]
      have hAL : (500000 : ℝ) ≤ A * Real.log z := by linarith only [hAlogz, hUbig]
      have hAlz : (4800 : ℝ) ≤ ec * (A * Real.log z) := by nlinarith only [hAL, hec]
      have hmul2 : Real.exp 250 * 4800 ≤ Real.exp 250 * (ec * (A * Real.log z)) :=
        mul_le_mul_of_nonneg_left hAlz he250.le
      linarith only [hmul2]
    have p3 : Real.exp 250 * 2 * ec * (Real.log q / Real.sqrt (n9Ell q η)) / Real.log z
        ≤ (Real.exp 250 * ec / 2400) * A := by
      rw [div_le_iff₀ hlogzpos]
      have hmul : (Real.exp 250 * ec / 2400) * (5000 * (Real.log q / Real.sqrt (n9Ell q η)))
          ≤ (Real.exp 250 * ec / 2400) * (A * Real.log z) :=
        mul_le_mul_of_nonneg_left hAlogz (by positivity)
      have hnn : (0 : ℝ) ≤ Real.exp 250 * ec * (Real.log q / Real.sqrt (n9Ell q η)) := by
        positivity
      linarith only [hmul, hnn]
    have hsum : (Real.exp 250 * ec / 2400) * A + (Real.exp 250 * ec / 2400) * A
        = (Real.exp 250 * ec / 1200) * A := by ring
    linarith only [hEk3, p1, p2, p3, hsum]
  -- the master constant, and the two closings
  have hAle1 : A ≤ 1 := by
    have h2 : (1 : ℝ) ≤ Real.exp 600 := by
      have := Real.add_one_le_exp (600 : ℝ); linarith only [this]
    have hec2 : (200000000 : ℝ) ≤ ec ^ 2 := by nlinarith only [hec]
    have hbig : (200000000 : ℝ) ≤ Real.exp 600 * ec ^ 2 := by nlinarith only [h2, hec2]
    nlinarith only [hA4, hbig, hA0]
  have hAsmall : (Real.exp 250 * ec / 300) * A ≤ 1 / 2 := by
    have h1 : Real.exp 600 = Real.exp 250 * Real.exp 350 := by
      rw [← Real.exp_add]; norm_num
    have h2 : (1 : ℝ) ≤ Real.exp 350 := by
      have := Real.add_one_le_exp (350 : ℝ); linarith only [this]
    have hprod : (Real.exp 250 * ec * A) * (Real.exp 350 * ec) ≤ 4 := by
      have heq : A * (Real.exp 600 * ec ^ 2)
          = (Real.exp 250 * ec * A) * (Real.exp 350 * ec) := by rw [h1]; ring
      linarith only [hA4, heq]
    have hpos : (0 : ℝ) ≤ Real.exp 250 * ec * A := by positivity
    have hbig : (14402 : ℝ) ≤ Real.exp 350 * ec := by nlinarith only [h2, hec]
    nlinarith only [hprod, hpos, hbig]
  have hsmall : 4 * ((2 / z + 10 / Real.sqrt z)
        + (Ek + 30 / Real.sqrt z + segC / Real.log z + Real.log q / Real.log z / z)
        + 100 / Real.sqrt (Real.log (x : ℝ))
        + 500 * (1 + 2 * Real.log (η * Real.log q)) / η)
      + 8 * (merC / Real.log z) + 2 * (64 / z) ≤ 1 := by
    linarith only [c1, c2, c3, c4, c5, c6, c7, c8, c11, hAsmall, hBsmall, hAle1, hB0]
  obtain ⟨δ, hδeq, hδle⟩ := hb_L2_at_split_point_charTrio (α := 4) (x := (x : ℝ)) χ hR.sq hqpos
    (by norm_num) (by norm_num) hR.β1 hL hR.ηdef hz32 (by exact_mod_cast hz4) hX3 hwinX
    (by linarith only [hηnum]) hm1 htail hseg hcorr hP hsmall
  rw [hzdef] at hδeq
  refine ⟨δ, hδeq, ?_⟩
  refine le_trans hδle ?_
  rw [← hAdef, ← hBdef, n9K2, ← hecdef]
  have hc1 : Real.exp 250 * ec / 300 + 1 / 1000 ≤ Real.exp 260 * ec := by
    have h10 : (11 : ℝ) ≤ Real.exp 10 := by
      have := Real.add_one_le_exp (10 : ℝ); linarith only [this]
    have heq : Real.exp 260 = Real.exp 250 * Real.exp 10 := by
      rw [← Real.exp_add]; norm_num
    have h1 : (1 : ℝ) ≤ Real.exp 250 := by
      have := Real.add_one_le_exp (250 : ℝ); linarith only [this]
    have h0 : (0 : ℝ) ≤ Real.exp 250 * ec := by positivity
    have hprod : 11 * (Real.exp 250 * ec) ≤ Real.exp 10 * (Real.exp 250 * ec) := by
      nlinarith only [h10, h0]
    have heq2 : Real.exp 10 * (Real.exp 250 * ec) = Real.exp 260 * ec := by rw [heq]; ring
    have hbig : (14402 : ℝ) ≤ Real.exp 250 * ec := by nlinarith only [h1, hec]
    linarith only [hprod, heq2, hbig]
  have hc2 : (32 : ℝ) ≤ Real.exp 260 * ec := by
    have h1 : (1 : ℝ) ≤ Real.exp 260 := by
      have := Real.add_one_le_exp (260 : ℝ); linarith only [this]
    nlinarith only [h1, hec]
  have hcA : (Real.exp 250 * ec / 300) * A + A / 1000 ≤ Real.exp 260 * ec * A := by
    nlinarith only [hA0, hc1]
  have hcB : 32 * B ≤ Real.exp 260 * ec * B := by nlinarith only [hB0, hc2]
  linarith only [c1, c2, c3, c4, c5, c6, c7, c8, c10, c11, hcA, hcB]

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
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < ε * Real.log 2 := mul_pos hε hlog2
  set g : ℝ := 1 + (ε * Real.log 2)⁻¹ with hg
  set P₀ : ℕ := ⌈(2 : ℝ) ^ ε⁻¹⌉₊ with hP₀
  have hg1 : (1 : ℝ) ≤ g := by rw [hg]; have := (inv_pos.mpr hKpos).le; linarith
  have hgpos : (0 : ℝ) < g := by rw [hg]; have := inv_pos.mpr hKpos; linarith
  -- the PRINTED constant dominates the landed witness `g ^ P₀`
  have h3ε : (1 : ℝ) ≤ 3 / ε := by rw [le_div_iff₀ hε]; linarith
  have hgle : g ≤ 3 / ε := by
    have hl2 := Real.log_two_gt_d9
    have hinv : (ε * Real.log 2)⁻¹ ≤ 2 / ε := by
      rw [inv_eq_one_div, div_le_div_iff₀ hKpos hε]
      nlinarith only [hl2, hε]
    have h1 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    have h2 : (3 : ℝ) / ε = 1 / ε + 2 / ε := by ring
    rw [hg]; linarith only [hinv, h1, h2]
  have hP₀le : (P₀ : ℝ) ≤ (2 : ℝ) ^ (1 / ε) + 1 := by
    rw [hP₀, one_div]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg (by norm_num) _))
  have hconst : g ^ P₀ ≤ (3 / ε) ^ ((2 : ℝ) ^ (1 / ε) + 1) := by
    have h1 : g ^ P₀ ≤ (3 / ε) ^ P₀ := pow_le_pow_left₀ hgpos.le hgle P₀
    have h2 : ((3 : ℝ) / ε) ^ P₀ = (3 / ε) ^ ((P₀ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    rw [h2] at h1
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le h3ε hP₀le)
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn_eq : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
    have h1 : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
    calc (n : ℝ)
        = ((∏ p ∈ n.primeFactors, p ^ (n.factorization p) : ℕ) : ℝ) := by rw [← h1]
      _ = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by push_cast; rfl
  have hq : ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε)
      = (n : ℝ) ^ ε := by
    rw [hn_eq, ← Real.finsetProd_rpow n.primeFactors
        (fun p => (p : ℝ) ^ (n.factorization p)) (fun p _ => by positivity) ε]
    apply Finset.prod_congr rfl
    intro p _
    rw [← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul (by positivity)]
  have hfactor : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1)
        ≤ (if p < P₀ then g else 1) * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hlt : p < P₀
    · rw [if_pos hlt, hg]; exact Salt.Maynard.tau_factor_small hε hp2
    · rw [if_neg hlt, one_mul]
      exact Salt.Maynard.tau_factor_large
        (Salt.Maynard.tau_threshold hε (hP₀ ▸ not_lt.mp hlt))
  have hprodc : ∏ p ∈ n.primeFactors, (if p < P₀ then g else 1 : ℝ) ≤ g ^ P₀ := by
    have hrw : ∏ p ∈ n.primeFactors, (if p < P₀ then g else 1 : ℝ)
        = ∏ _p ∈ n.primeFactors.filter (· < P₀), g :=
      (Finset.prod_filter (· < P₀) (fun _ => (g : ℝ))).symm
    rw [hrw, Finset.prod_const]
    apply pow_le_pow_right₀ hg1
    calc (n.primeFactors.filter (· < P₀)).card
        ≤ (Finset.range P₀).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          exact Finset.mem_range.mpr hp.2
      _ = P₀ := Finset.card_range P₀
  have hnε : (0 : ℝ) ≤ (n : ℝ) ^ ε := Real.rpow_nonneg (by positivity) _
  rw [Nat.card_divisors hn0]
  push_cast
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          (if p < P₀ then g else 1) * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, (if p < P₀ then g else 1))
          * ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        Finset.prod_mul_distrib
    _ ≤ g ^ P₀ * (n : ℝ) ^ ε := by
        rw [hq]; exact mul_le_mul_of_nonneg_right hprodc hnε
    _ ≤ (3 / ε) ^ ((2 : ℝ) ^ (1 / ε) + 1) * (n : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right hconst hnε

/-- `t·e^{−a·t} ≤ 1/a` on the non-negatives — the elementary decay every ledger row below
uses to beat a polynomial factor against an exponential one. -/
private lemma n9_exp_lin {a t : ℝ} (ha : 0 < a) (_ht : 0 ≤ t) :
    t * Real.exp (-(a * t)) ≤ 1 / a := by
  have he : a * t ≤ Real.exp (a * t) := by
    have h := Real.add_one_le_exp (a * t); linarith only [h]
  have hcomm : t * a = a * t := mul_comm t a
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) ha]
  linarith only [he, hcomm]

/-- **THE LEDGER'S KILL STEP.**  At `t ≥ 3·10⁶` a rate `a ≥ 1/10` beats any offset `c` up to
`a·t/4`: `t·e^{c − a·t} ≤ 1`.  Every row of the Lemma-4 and p.200 ledgers below is one
instance of this, with `t` either `log ℓ′` or `log L`. -/
private lemma n9_kill {t a c : ℝ} (ha : 1 / 10 ≤ a) (ht : 3000000 ≤ t)
    (hc : c ≤ a * t / 4) : t * Real.exp (c - a * t) ≤ 1 := by
  have hapos : (0 : ℝ) < a := by linarith only [ha]
  have ht0 : (0 : ℝ) ≤ t := by linarith only [ht]
  have hat : (150000 : ℝ) ≤ a * t / 2 := by nlinarith only [ha, ht]
  have hlin : t * Real.exp (-(a / 4 * t)) ≤ 4 / a := by
    have h := n9_exp_lin (a := a / 4) (t := t) (by linarith only [hapos]) ht0
    rw [one_div_div] at h
    exact h
  have hsplit : Real.exp (c - a * t) ≤ Real.exp (-(a / 4 * t)) * Real.exp (-(a * t / 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hc])
  have hsmall : Real.exp (-(a * t / 2)) ≤ 1 / 40 := by
    have h1 : Real.exp (150000 : ℝ) ≤ Real.exp (a * t / 2) := Real.exp_le_exp.mpr hat
    have h2 : (150001 : ℝ) ≤ Real.exp (150000 : ℝ) := by
      have h := Real.add_one_le_exp (150000 : ℝ); linarith only [h]
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith only [h1, h2]
  have h4a : 4 / a ≤ 40 := by rw [div_le_iff₀ hapos]; linarith only [ha]
  calc t * Real.exp (c - a * t)
      ≤ t * (Real.exp (-(a / 4 * t)) * Real.exp (-(a * t / 2))) :=
        mul_le_mul_of_nonneg_left hsplit ht0
    _ = t * Real.exp (-(a / 4 * t)) * Real.exp (-(a * t / 2)) := by ring
    _ ≤ (4 / a) * (1 / 40) :=
        mul_le_mul hlin hsmall (Real.exp_pos _).le (by positivity)
    _ ≤ 1 := by linarith only [h4a]

/-- **The `m2` row of the Lemma-4 ledger, as pure arithmetic.**  `e^{2510 z₀}` against the
pretense bound: the `L/η` half is killed by `η ≥ L^{13}`, the constant half by `L ≥ 100·ℓ′`, and
the `1/√ℓ′` half by `ℓ′ ≥ (e^{300}(802+4·n9Cs))^8` — the eighth power of `n9E0`. -/
private lemma n9_l4_m2_core {s Lg ηv ec : ℝ}
    (hs : 3000000 ≤ s) (hLg : 100 * Real.exp s ≤ Lg)
    (hη : Real.exp (13 * s) ≤ ηv) (_hηpos : 0 < ηv)
    (hec1 : 1 ≤ ec) (hecs : 2400 + 8 * Real.log ec ≤ s) :
    Real.exp (251 / 1000 * s) * (Real.exp 251
        * (2 * Lg / ηv + 1 + ec * Lg / Real.exp (s / 2))) * (s / 10000)
      ≤ 16000 * Lg := by
  have hs0 : (0 : ℝ) < s := by linarith only [hs]
  have hes : (0 : ℝ) < Real.exp s := Real.exp_pos _
  have hLg0 : (0 : ℝ) < Lg := by linarith only [hLg, hes]
  -- row 1: the `L/η` half
  have hk1 : s * Real.exp (251 - 12749 / 1000 * s) ≤ 1 :=
    n9_kill (by norm_num) hs (by linarith only [hs])
  have hr1 : Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000) * (2 * Lg / ηv)
      ≤ 5300 * Lg := by
    have hinv : ηv⁻¹ ≤ (Real.exp (13 * s))⁻¹ := by
      have h := one_div_le_one_div_of_le (Real.exp_pos (13 * s)) hη
      rwa [one_div, one_div] at h
    have h3 : 2 * Lg / ηv ≤ 2 * Lg * Real.exp (-(13 * s)) := by
      rw [div_eq_mul_inv, Real.exp_neg]
      exact mul_le_mul_of_nonneg_left hinv (by linarith only [hLg0])
    have hpos : (0 : ℝ) ≤ Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000) := by
      positivity
    have h4 := mul_le_mul_of_nonneg_left h3 hpos
    have hexp3 : Real.exp (251 / 1000 * s) * Real.exp 251 * Real.exp (-(13 * s))
        = Real.exp (251 - 12749 / 1000 * s) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h5 : Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000)
          * (2 * Lg * Real.exp (-(13 * s)))
        = 2 * Lg / 10000 * (s * Real.exp (251 - 12749 / 1000 * s)) := by
      rw [← hexp3]; ring
    rw [h5] at h4
    have h6 : 2 * Lg / 10000 * (s * Real.exp (251 - 12749 / 1000 * s)) ≤ 2 * Lg / 10000 * 1 :=
      mul_le_mul_of_nonneg_left hk1 (by positivity)
    linarith only [h4, h6, hLg0]
  -- row 2: the constant half
  have hk2 : s * Real.exp (251 - 749 / 1000 * s) ≤ 1 :=
    n9_kill (by norm_num) hs (by linarith only [hs])
  have hr2 : Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000) * 1 ≤ 5300 * Lg := by
    have hexp2 : Real.exp (251 - 749 / 1000 * s) * Real.exp s
        = Real.exp (251 / 1000 * s) * Real.exp 251 := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000) * 1
        = s * Real.exp (251 - 749 / 1000 * s) * Real.exp s / 10000 := by
      rw [← hexp2]; ring
    have h2 := mul_le_mul_of_nonneg_right hk2 hes.le
    rw [h1]
    linarith only [h2, hLg, hes, hLg0]
  -- row 3: the `1/√ℓ′` half
  have hecpos : (0 : ℝ) < ec := by linarith only [hec1]
  have hk3 : s * Real.exp (0 - 124 / 1000 * s) ≤ 1 :=
    n9_kill (by norm_num) hs (by linarith only [hs])
  have hr3 : Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000)
        * (ec * Lg / Real.exp (s / 2)) ≤ 5300 * Lg := by
    have hec2 : ec ≤ Real.exp ((s - 2400) / 8) := by
      calc ec = Real.exp (Real.log ec) := (Real.exp_log hecpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hecs])
    have hdiv : ec * Lg / Real.exp (s / 2) = ec * Lg * Real.exp (-(s / 2)) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    have hstep : ec * Lg * Real.exp (-(s / 2))
        ≤ Real.exp ((s - 2400) / 8) * Lg * Real.exp (-(s / 2)) := by
      have := mul_le_mul_of_nonneg_right hec2 (le_of_lt hLg0)
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    have hpos : (0 : ℝ) ≤ Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000) := by
      positivity
    have h4 := mul_le_mul_of_nonneg_left hstep hpos
    have hexpid : Real.exp (251 / 1000 * s) * Real.exp 251 * Real.exp ((s - 2400) / 8)
          * Real.exp (-(s / 2))
        = Real.exp (0 - 124 / 1000 * s) * Real.exp (-49) := by
      simp only [← Real.exp_add]; congr 1; ring
    have h5 : Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000)
          * (Real.exp ((s - 2400) / 8) * Lg * Real.exp (-(s / 2)))
        = Lg / 10000 * (s * Real.exp (0 - 124 / 1000 * s)) * Real.exp (-49) := by
      linear_combination (s * Lg / 10000) * hexpid
    have he49 : Real.exp (-49 : ℝ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; norm_num
    have h6 : Lg / 10000 * (s * Real.exp (0 - 124 / 1000 * s)) * Real.exp (-49)
        ≤ Lg / 10000 * 1 * 1 := by
      refine mul_le_mul ?_ he49 (Real.exp_pos _).le (by positivity)
      exact mul_le_mul_of_nonneg_left hk3 (by positivity)
    rw [hdiv]
    rw [h5] at h4
    linarith only [h4, h6, hLg0]
  have hsplit : Real.exp (251 / 1000 * s) * (Real.exp 251
        * (2 * Lg / ηv + 1 + ec * Lg / Real.exp (s / 2))) * (s / 10000)
      = Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000) * (2 * Lg / ηv)
        + Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000) * 1
        + Real.exp (251 / 1000 * s) * Real.exp 251 * (s / 10000)
            * (ec * Lg / Real.exp (s / 2)) := by ring
  rw [hsplit]
  linarith only [hr1, hr2, hr3, hLg0]

/-- **The `m3` row of the Lemma-4 ledger, as pure arithmetic.**  The prefactor is
`exp(5·log L)`; the two decays are `z^{1/8} ≥ e^{W/8}` (and `W/8 ≥ 6·log L`) and
`x^{1/10} ≥ q^{25}`. -/
private lemma n9_l4_m3_core {s M Lg W : ℝ}
    (hs : 3000000 ≤ s) (hsM : s ≤ M) (hMexp : Real.exp M = Lg) (hW8 : 6 * M ≤ W / 8) :
    Real.exp (1004 / 10000 * s) * (502 * Lg) ^ 3 * (s / 10000)
        * (Real.exp (-(W / 8)) + Real.exp (-(25 * Lg))) ≤ 64 := by
  have hM : (3000000 : ℝ) ≤ M := le_trans hs hsM
  have hLgpos : 0 < Lg := by rw [← hMexp]; exact Real.exp_pos _
  have hMLg : M ≤ Lg := by
    rw [← hMexp]; linarith only [Real.add_one_le_exp M]
  have hexp3M : Real.exp M ^ 3 = Real.exp (3 * M) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hLg3 : (502 * Lg) ^ 3 = 126506008 * Real.exp (3 * M) := by
    rw [mul_pow, ← hMexp, hexp3M]; norm_num
  have h1 : Real.exp (1004 / 10000 * s) ≤ Real.exp M :=
    Real.exp_le_exp.mpr (by linarith only [hsM, hM])
  have h2 : s / 10000 ≤ Real.exp M / 10000 := by
    rw [hMexp]; linarith only [hsM, hMLg]
  have hA : Real.exp (1004 / 10000 * s) * (502 * Lg) ^ 3 * (s / 10000)
      ≤ Real.exp M * (126506008 * Real.exp (3 * M)) * (Real.exp M / 10000) := by
    refine mul_le_mul (mul_le_mul h1 (le_of_eq hLg3) (by positivity) (Real.exp_pos _).le) h2
      (by positivity) (by positivity)
  have hE : Real.exp M * Real.exp (3 * M) * Real.exp M = Real.exp (5 * M) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hB : Real.exp M * (126506008 * Real.exp (3 * M)) * (Real.exp M / 10000)
      = 126506008 / 10000 * Real.exp (5 * M) := by
    rw [← hE]; ring
  have hdecay : Real.exp (-(W / 8)) + Real.exp (-(25 * Lg)) ≤ 2 * Real.exp (-(6 * M)) := by
    have d1 : Real.exp (-(W / 8)) ≤ Real.exp (-(6 * M)) :=
      Real.exp_le_exp.mpr (by linarith only [hW8])
    have d2 : Real.exp (-(25 * Lg)) ≤ Real.exp (-(6 * M)) :=
      Real.exp_le_exp.mpr (by linarith only [hMLg, hM])
    linarith only [d1, d2]
  have hfin : Real.exp (5 * M) * Real.exp (-(6 * M)) = Real.exp (-M) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsmall : Real.exp (-M) ≤ 1 / 3000001 := by
    have h3 : Real.exp (3000000 : ℝ) ≤ Real.exp M := Real.exp_le_exp.mpr hM
    have h4 : (3000001 : ℝ) ≤ Real.exp (3000000 : ℝ) := by
      have h := Real.add_one_le_exp (3000000 : ℝ); linarith only [h]
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith only [h3, h4]
  calc Real.exp (1004 / 10000 * s) * (502 * Lg) ^ 3 * (s / 10000)
        * (Real.exp (-(W / 8)) + Real.exp (-(25 * Lg)))
      ≤ (126506008 / 10000 * Real.exp (5 * M)) * (2 * Real.exp (-(6 * M))) := by
        rw [← hB]
        exact mul_le_mul hA hdecay (by positivity) (by positivity)
    _ = 126506008 / 5000 * Real.exp (-M) := by rw [← hfin]; ring
    _ ≤ 64 := by
        have := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0:ℝ) ≤ 126506008 / 5000)
        linarith only [this]

/-- **The swap row of the Lemma-4 ledger, as pure arithmetic.**  `2(ω(q)+z)·Lwin²` against
`x/z₀`: every factor in sight is at most `e^L`, while `x ≥ e^{250L}`. -/
private lemma n9_l4_swap_core {L om zv Lw w0 X : ℝ}
    (hL : 1500000 ≤ L) (hw0 : 0 < w0) (hw0L : w0 ≤ L)
    (_hom : 0 ≤ om) (homle : om ≤ 2 * Real.exp L)
    (_hzv : 0 ≤ zv) (hzvle : zv ≤ Real.exp (L / 300 + 1))
    (hLw : 0 ≤ Lw) (hLwle : Lw ≤ 501 * L)
    (hX : Real.exp (250 * L) ≤ X) :
    2 * (om + zv) * Lw ^ 2 * w0 ≤ 2 ^ 37 * X := by
  have hLpos : (0 : ℝ) < L := by linarith
  have heL : (0 : ℝ) < Real.exp L := Real.exp_pos _
  have h1 : Real.exp (L / 300 + 1) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
  have hL2 : L ^ 2 ≤ 4 * Real.exp L := n9_sq_le_exp hLpos.le
  have hLe : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hbig : (6024024 : ℝ) ≤ Real.exp L := by nlinarith only [hL2, hL, hLpos]
  have hLw2 : Lw ^ 2 ≤ 251001 * L ^ 2 := by nlinarith only [hLw, hLwle, hLpos]
  have hstep1 : 2 * (om + zv) * Lw ^ 2 * w0 ≤ 6 * Real.exp L * (251001 * L ^ 2) * L :=
    mul_le_mul (mul_le_mul (by linarith) hLw2 (by positivity) (by positivity)) hw0L hw0.le
      (by positivity)
  have hstep2 : 6 * Real.exp L * (251001 * L ^ 2) * L
      ≤ 6 * Real.exp L * (251001 * (4 * Real.exp L)) * Real.exp L :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hLe hLpos.le
      (by positivity)
  have hstep3 : 6 * Real.exp L * (251001 * (4 * Real.exp L)) * Real.exp L
      ≤ Real.exp L * Real.exp L * Real.exp L * Real.exp L := by
    have h := mul_le_mul_of_nonneg_right hbig
      (by positivity : (0 : ℝ) ≤ Real.exp L * Real.exp L * Real.exp L)
    linarith only [h]
  have hstep4 : Real.exp L * Real.exp L * Real.exp L * Real.exp L ≤ Real.exp (250 * L) := by
    have h4 : Real.exp L * Real.exp L * Real.exp L * Real.exp L = Real.exp (4 * L) := by
      simp only [← Real.exp_add]; congr 1; ring
    rw [h4]
    exact Real.exp_le_exp.mpr (by linarith)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  linarith

/-- **The star row of the Lemma-4 ledger, as pure arithmetic.**  The divisor constant's double
exponential `e^{e^{3P/20}}` and the window factor `x^{2ε} = e^{0.501·W}` are both eaten by the
single sieve gain `z^{-1} = e^{-W}`, because `W ≥ 10⁶·e^P/P` at the operating point. -/
private lemma n9_l4_star_core {L P W w0 X Cc Lw t tl : ℝ}
    (_hP : 3000000 ≤ P) (hL : 1500000 ≤ L)
    (hw0 : 0 < w0) (hw0L : w0 ≤ L) (hWL : W ≤ L / 300)
    (hquart : 1004004 * L ^ 4 ≤ Real.exp (W / 5))
    (hGW : 2 * Real.exp (3 / 20 * P) ≤ W / 5)
    (hC : 0 ≤ Cc) (hCle : Cc ≤ Real.exp (Real.exp (3 / 20 * P)))
    (h0t : 0 ≤ t) (ht : t ≤ Real.exp (501 / 2000 * W))
    (hLw : 0 ≤ Lw) (hLwle : Lw ≤ 501 * L)
    (hX : Real.exp (250 * L) ≤ X)
    (htl : 0 ≤ tl)
    (htle : tl ≤ 2 * X * Real.exp (-W) + 2 * X * Real.exp (-(125 * L))) :
    2 * (Cc * t * Lw) ^ 2 * tl * w0 ≤ 2 ^ 37 * X := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hWpos : (0 : ℝ) < W := by
    have h := Real.exp_pos (3 / 20 * P); linarith
  have hCsq : Cc ^ 2 ≤ Real.exp (W / 5) := by
    have h1 : Cc ^ 2 ≤ Real.exp (Real.exp (3 / 20 * P)) ^ 2 := pow_le_pow_left₀ hC hCle 2
    have h2 : Real.exp (Real.exp (3 / 20 * P)) ^ 2
        = Real.exp (2 * Real.exp (3 / 20 * P)) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [h2] at h1
    exact le_trans h1 (Real.exp_le_exp.mpr hGW)
  have htsq : t ^ 2 ≤ Real.exp (501 / 1000 * W) := by
    have h1 : t ^ 2 ≤ Real.exp (501 / 2000 * W) ^ 2 := pow_le_pow_left₀ h0t ht 2
    have h2 : Real.exp (501 / 2000 * W) ^ 2 = Real.exp (501 / 1000 * W) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [h2] at h1
    exact h1
  have hLw4 : Lw ^ 2 * w0 ≤ Real.exp (W / 5) := by
    have h1 : Lw ^ 2 ≤ 251001 * L ^ 2 := by nlinarith only [hLw, hLwle, hLpos]
    have h2 : Lw ^ 2 * w0 ≤ 251001 * L ^ 2 * L := mul_le_mul h1 hw0L hw0.le (by positivity)
    have hL3 : (0 : ℝ) ≤ L ^ 3 := by positivity
    have h3 : 251001 * L ^ 2 * L ≤ 1004004 * L ^ 4 := by nlinarith only [hL, hL3]
    linarith
  have key : Cc ^ 2 * t ^ 2 * (Lw ^ 2 * w0) ≤ Real.exp (901 / 1000 * W) := by
    have h1 : Cc ^ 2 * t ^ 2 * (Lw ^ 2 * w0)
        ≤ Real.exp (W / 5) * Real.exp (501 / 1000 * W) * Real.exp (W / 5) :=
      mul_le_mul (mul_le_mul hCsq htsq (by positivity) (Real.exp_pos _).le) hLw4
        (by positivity) (by positivity)
    have h2 : Real.exp (W / 5) * Real.exp (501 / 1000 * W) * Real.exp (W / 5)
        = Real.exp (901 / 1000 * W) := by
      simp only [← Real.exp_add]; congr 1; ring
    linarith [h1, h2]
  have htl4 : tl ≤ 4 * X * Real.exp (-W) := by
    have h1 : Real.exp (-(125 * L)) ≤ Real.exp (-W) := Real.exp_le_exp.mpr (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * X)
    linarith [htle, h2]
  have hfin : 2 * (Cc * t * Lw) ^ 2 * tl * w0
      ≤ 2 * Real.exp (901 / 1000 * W) * (4 * X * Real.exp (-W)) := by
    have heq : 2 * (Cc * t * Lw) ^ 2 * tl * w0
        = 2 * (Cc ^ 2 * t ^ 2 * (Lw ^ 2 * w0)) * tl := by ring
    rw [heq]
    exact mul_le_mul (by linarith [key]) htl4 htl (by positivity)
  have hlast : 2 * Real.exp (901 / 1000 * W) * (4 * X * Real.exp (-W)) ≤ 8 * X := by
    have h1 : Real.exp (901 / 1000 * W) * Real.exp (-W) = Real.exp (-(99 / 1000 * W)) := by
      simp only [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(99 / 1000 * W)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    calc 2 * Real.exp (901 / 1000 * W) * (4 * X * Real.exp (-W))
        = 8 * X * (Real.exp (901 / 1000 * W) * Real.exp (-W)) := by ring
      _ = 8 * X * Real.exp (-(99 / 1000 * W)) := by rw [h1]
      _ ≤ 8 * X * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 * X := by ring
  linarith [hfin, hlast, hXpos]

set_option maxHeartbeats 4000000 in
-- The ledger is five rows over one shared ~120-fact regime context (the window, the `z`
-- witness, `P = log ℓ′`, the printed divisor constant); each row is a `mul_le_mul` chain into a
-- pure-real core, and the terminal `simp only [lemma4Err, add_mul]` distributes a five-summand
-- product.  The elaborator needs the room for that one declaration.
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
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, hPbig, hPsmall, hlog4qpos, hW2L, -⟩ := n9_num_facts hR
  obtain ⟨-, -, hEllge, -, hPleL⟩ := n9_z_regime hR
  obtain ⟨hz0pos, hz0ge, hWbig, hWle, hlogzge, hlogzle⟩ := n9_scale hR
  obtain ⟨hz2, hz100, hz8, hzx, -, -, -, -, -, -, -⟩ := hbZ_packet hR hx hx'
  have hEllpos : (0 : ℝ) < n9Ell q η := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hLne : Real.log q ≠ 0 := ne_of_gt hL
  have hηne : η ≠ 0 := ne_of_gt hηpos
  have hw0ne : hbZ0 q η ≠ 0 := ne_of_gt hz0pos
  -- `P := log ℓ′`, the ledger's currency
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Real.log (n9Ell q η) := ⟨_, rfl⟩
  have hexpP : Real.exp P = n9Ell q η := by rw [hPdef]; exact Real.exp_log hEllpos
  have hPge : (3000000 : ℝ) ≤ P := by
    have h := Real.log_le_log (Real.exp_pos (3 * 10 ^ 6 : ℝ)) hEllge
    rw [Real.log_exp] at h
    rw [hPdef]; linarith
  have hPpos : (0 : ℝ) < P := by linarith
  have hw0eq : hbZ0 q η = P / 10000 := by
    rw [hPdef]; simp only [hbZ0, hbZ0A]; ring
  have hPleL' : P ≤ Real.log (Real.log q) := by rw [hPdef]; exact hPleL
  have hlogLpos : (0 : ℝ) < Real.log (Real.log q) := Real.log_pos (by linarith)
  have hw0L : hbZ0 q η ≤ Real.log q := by
    have h1 : Real.log (Real.log q) ≤ Real.log q := by
      have := Real.log_le_sub_one_of_pos hL; linarith
    rw [hw0eq]; linarith
  -- `W := L/z₀`, kept opaque
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Real.log q / hbZ0 q η := ⟨_, rfl⟩
  rw [← hWdef] at hWbig hWle hlogzge hlogzle
  have hWpos : (0 : ℝ) < W := by
    have h : (0 : ℝ) < 10000 * Real.exp (10 ^ 6 : ℝ) := by positivity
    linarith
  have hWge1 : (1 : ℝ) ≤ W := by
    have h := Real.add_one_le_exp (10 ^ 6 : ℝ); linarith
  have hw0W : hbZ0 q η * W = Real.log q := by rw [hWdef]; field_simp
  have hWeq : W = 10000 * Real.log q / P := by rw [hWdef, hw0eq]; field_simp
  -- the window `[q^250, q^500]`
  have hq250 : Real.exp (250 * Real.log q) = (q : ℝ) ^ (250 : ℕ) := by
    rw [show (250 : ℝ) * Real.log q = ((250 : ℕ) : ℝ) * Real.log q by norm_num,
      Real.exp_nat_mul, Real.exp_log hqpos]
  have hq500 : Real.exp (500 * Real.log q) = (q : ℝ) ^ (500 : ℕ) := by
    rw [show (500 : ℝ) * Real.log q = ((500 : ℕ) : ℝ) * Real.log q by norm_num,
      Real.exp_nat_mul, Real.exp_log hqpos]
  have hx250 : Real.exp (250 * Real.log q) ≤ (x : ℝ) := by rw [hq250]; exact hx
  have hx500 : (x : ℝ) ≤ Real.exp (500 * Real.log q) := by rw [hq500]; exact hx'
  have hXpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hx250
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have h := Real.add_one_le_exp (250 * Real.log q); linarith
  have hlogX : 250 * Real.log q ≤ Real.log (x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (250 * Real.log q)) hx250
    rwa [Real.log_exp] at h
  have hlogXpos : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have hLwinLe : Real.log (2 * (x : ℝ) + 2) ≤ 501 * Real.log q := by
    have hexpL : Real.log q + 1 ≤ Real.exp (Real.log q) := Real.add_one_le_exp _
    have h4 : (4 : ℝ) ≤ Real.exp (Real.log q) := by linarith
    have h2 : (4 : ℝ) * (x : ℝ) ≤ Real.exp (Real.log q) * Real.exp (500 * Real.log q) :=
      mul_le_mul h4 hx500 (by linarith) (by positivity)
    have h3 : Real.exp (Real.log q) * Real.exp (500 * Real.log q)
        = Real.exp (501 * Real.log q) := by rw [← Real.exp_add]; congr 1; ring
    have hb : 2 * (x : ℝ) + 2 ≤ Real.exp (501 * Real.log q) := by linarith
    have h := Real.log_le_log (by positivity) hb
    rwa [Real.log_exp] at h
  have hLwinGe : 250 * Real.log q ≤ Real.log (2 * (x : ℝ) + 2) := by
    have h1 : Real.exp (250 * Real.log q) ≤ 2 * (x : ℝ) + 2 := by linarith
    have h := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h
  have hLwinNn : (0 : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) := by linarith
  -- the `z` witness
  have hZ2 : (2 : ℝ) ≤ (hbZ q η : ℝ) := by exact_mod_cast hz2
  have hZpos : (0 : ℝ) < (hbZ q η : ℝ) := by linarith
  have hlogZpos : (0 : ℝ) < Real.log (hbZ q η : ℝ) := by linarith
  have hZge : Real.exp W ≤ (hbZ q η : ℝ) := by
    have h := Real.exp_le_exp.mpr hlogzge
    rwa [Real.exp_log hZpos] at h
  have hZle : (hbZ q η : ℝ) ≤ Real.exp (Real.log q / 300 + 1) := by
    have h := Real.exp_le_exp.mpr (le_trans hlogzle (by linarith : W + 1 ≤ Real.log q / 300 + 1))
    rwa [Real.exp_log hZpos] at h
  have hz0zx : z0 (hbZ q η) x = Real.log (2 * (x : ℝ) + 2) / Real.log (hbZ q η : ℝ) := rfl
  have hzzpos : (0 : ℝ) < z0 (hbZ q η) x := by
    rw [hz0zx]; exact div_pos (by linarith) hlogZpos
  have hzzlo : hbZ0 q η / 64 ≤ z0 (hbZ q η) x := by
    rw [hz0zx, div_le_div_iff₀ (by norm_num) hlogZpos]
    have h1 : Real.log (hbZ q η : ℝ) ≤ 2 * W := by linarith
    have h2 : hbZ0 q η * Real.log (hbZ q η : ℝ) ≤ hbZ0 q η * (2 * W) :=
      mul_le_mul_of_nonneg_left h1 hz0pos.le
    linarith
  have hzzhi : z0 (hbZ q η) x ≤ 501 * hbZ0 q η := by
    rw [hz0zx, div_le_iff₀ hlogZpos]
    have h2 : 501 * hbZ0 q η * W ≤ 501 * hbZ0 q η * Real.log (hbZ q η : ℝ) :=
      mul_le_mul_of_nonneg_left hlogzge (by positivity)
    linarith
  -- ω(q) ≤ q + 1
  have hom : ((q.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.exp (Real.log q) := by
    have hsub : q.primeFactors ⊆ Finset.range (q + 1) := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hp.2.2) hp.2.1))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    have hc : ((q.primeFactors.card : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hcard
    rw [Real.exp_log hqpos]; linarith
  -- the divisor constant, printed
  obtain ⟨ε, hεdef⟩ : ∃ e : ℝ, e = 1 / (2000 * hbZ0 q η) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]; linarith
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = (3 / ε) ^ ((2 : ℝ) ^ (1 / ε) + 1) := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hCdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hCtau : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
    rw [hCdef]; exact card_divisors_le_rpow_explicit hεpos hε1
  -- the ledger's numerals
  have hLg : 100 * Real.exp P ≤ Real.log q := by rw [hexpP]; linarith
  have hEllLogη : n9Ell q η ≤ Real.log η := by
    have hinv : 0 ≤ Real.log (1 / dhC) :=
      Real.log_nonneg (by rw [le_div_iff₀ dh_spec.1]; linarith [dh_spec.2.1])
    have hlog4q : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
    have hLle : Real.log q ≤ Real.log (4 * (q : ℝ)) + 2 := by
      have h : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hlogLle : Real.log (Real.log q) ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      Real.log_le_log hL hLle
    have hXnn : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) := Real.log_nonneg (by linarith)
    have hdk : dhK = 14 := rfl
    have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
      Real.log_mul hηne hLne
    simp only [n9Ell, hdk, hsplit]
    linarith
  have hηexp : Real.exp (13 * P) ≤ η := by
    have hsq := n9_sq_le_exp hPpos.le
    have h13 : 13 * P ≤ Real.exp P := by nlinarith only [hsq, hPge, hPpos]
    rw [hexpP] at h13
    have h3 := Real.exp_le_exp.mpr (show 13 * P ≤ Real.log η by linarith)
    rwa [Real.exp_log hηpos] at h3
  have hn9Cs : (3400 : ℝ) ≤ n9Cs := by
    have h := invSqC_spec.1
    simp only [n9Cs, dhB]
    nlinarith only [h]
  have hec1 : (1 : ℝ) ≤ 802 + 4 * n9Cs := by linarith
  have hecpos : (0 : ℝ) < 802 + 4 * n9Cs := by linarith
  have hecs : 2400 + 8 * Real.log (802 + 4 * n9Cs) ≤ P := by
    have h1 : (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 ≤ n9Ell q η := by
      have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
      have ha : (0 : ℝ) < Real.exp (3 * 10 ^ 6 : ℝ) := Real.exp_pos _
      have hn : (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 ≤ n9E0 := by
        simp only [n9E0]; linarith
      linarith [hR.ellBig]
    have h2 : Real.log ((Real.exp 300 * (802 + 4 * n9Cs)) ^ 8) ≤ P := by
      rw [hPdef]; exact Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_mul (ne_of_gt (Real.exp_pos 300)) (ne_of_gt hecpos),
      Real.log_exp] at h2
    push_cast at h2
    linarith
  -- ROW A: the swap
  have rowA : 2 * ((q.primeFactors.card : ℝ) + (hbZ q η : ℝ)) * Lwin x ^ 2 * hbZ0 q η
      ≤ 2 ^ 37 * (x : ℝ) := by
    exact n9_l4_swap_core hLhuge hz0pos hw0L (by positivity) hom hZpos.le hZle
      hLwinNn hLwinLe hx250
  -- ROW M1: the master's leading term
  have rowM1 : L2cCmain * ((x : ℝ) / z0 (hbZ q η) x) * hbZ0 q η ≤ 2 ^ 37 * (x : ℝ) := by
    simp only [L2cCmain]
    have h1 : (x : ℝ) / z0 (hbZ q η) x * hbZ0 q η ≤ 64 * (x : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hzzpos]
      nlinarith only [hzzlo, hXpos, hz0pos]
    linarith
  -- ROW M2: the pretense term
  have hPS := pretenseSum_at_hb_point hR hx'
  have hPS0 : (0 : ℝ) ≤ PretenseSum χ (2 * x + 2) := pretenseSum_nonneg χ _
  have hsqrtEll : Real.sqrt (n9Ell q η) = Real.exp (P / 2) := by
    rw [← hexpP, show Real.exp P = Real.exp (P / 2) * Real.exp (P / 2) by
      rw [← Real.exp_add]; ring_nf]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  have hbeta : 1 - β₀ = 1 / (η * Real.log q) := by rw [hηL, one_div_one_div]
  have hEne : Real.exp (P / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hPB : PretenseSum χ (2 * x + 2)
      ≤ Real.exp 251 * (2 * Real.log q / η + 1
          + (802 + 4 * n9Cs) * Real.log q / Real.exp (P / 2)) := by
    refine le_trans hPS (le_of_eq ?_)
    rw [hsqrtEll, hbeta]
    field_simp
    ring
  have hcore2 := n9_l4_m2_core (s := P) (Lg := Real.log q) (ηv := η) (ec := 802 + 4 * n9Cs)
    hPge hLg hηexp hηpos hec1 hecs
  have hexp5 : Real.exp (5 * z0 (hbZ q η) x) ≤ Real.exp (251 / 1000 * P) := by
    refine Real.exp_le_exp.mpr ?_
    have h : z0 (hbZ q η) x ≤ 501 * hbZ0 q η := hzzhi
    rw [hw0eq] at h
    linarith
  have rowM2 : L2cCmain * ((x : ℝ) / Real.log (x : ℝ)) * Real.exp (5 * z0 (hbZ q η) x)
      * PretenseSum χ (2 * x + 2) * hbZ0 q η ≤ 2 ^ 37 * (x : ℝ) := by
    simp only [L2cCmain]
    have hnn : (0 : ℝ) ≤ Real.exp (5 * z0 (hbZ q η) x) * PretenseSum χ (2 * x + 2)
        * hbZ0 q η :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le hPS0) hz0pos.le
    have h1 : Real.exp (5 * z0 (hbZ q η) x) * PretenseSum χ (2 * x + 2) * hbZ0 q η
        ≤ 16000 * Real.log q := by
      have hA : Real.exp (5 * z0 (hbZ q η) x) * PretenseSum χ (2 * x + 2)
          ≤ Real.exp (251 / 1000 * P) * (Real.exp 251 * (2 * Real.log q / η + 1
              + (802 + 4 * n9Cs) * Real.log q / Real.exp (P / 2))) :=
        mul_le_mul hexp5 hPB hPS0 (Real.exp_pos _).le
      have hB := mul_le_mul_of_nonneg_right hA hz0pos.le
      rw [hw0eq] at hB ⊢
      linarith [hcore2, hB]
    have h2 : (x : ℝ) / Real.log (x : ℝ) ≤ (x : ℝ) / (250 * Real.log q) := by
      rw [div_le_div_iff₀ hlogXpos (by linarith : (0 : ℝ) < 250 * Real.log q)]
      nlinarith only [hlogX, hXpos]
    calc 2 ^ 31 * ((x : ℝ) / Real.log (x : ℝ)) * Real.exp (5 * z0 (hbZ q η) x)
            * PretenseSum χ (2 * x + 2) * hbZ0 q η
        = (2 ^ 31 * ((x : ℝ) / Real.log (x : ℝ)))
            * (Real.exp (5 * z0 (hbZ q η) x) * PretenseSum χ (2 * x + 2) * hbZ0 q η) := by
          ring
      _ ≤ (2 ^ 31 * ((x : ℝ) / (250 * Real.log q))) * (16000 * Real.log q) :=
          mul_le_mul (by linarith) h1 hnn (by positivity)
      _ = 2 ^ 37 * (x : ℝ) := by field_simp; ring
  -- ROW M3: the master's tail
  have hMexp : Real.exp (Real.log (Real.log q)) = Real.log q := Real.exp_log hL
  have hlogLsq : Real.log (Real.log q) ^ 2 ≤ 4 * Real.log q := by
    have h1 := n9_log_le_two_sqrt hL
    have h2 : Real.sqrt (Real.log q) ^ 2 = Real.log q := Real.sq_sqrt hL.le
    nlinarith only [h1, h2, hlogLpos, Real.sqrt_nonneg (Real.log q)]
  have hW8 : 6 * Real.log (Real.log q) ≤ W / 8 := by
    have hkey : 48 * Real.log (Real.log q) * P ≤ 10000 * Real.log q := by
      nlinarith only [hlogLsq, hPleL', hlogLpos, hPpos]
    rw [hWeq, div_div, le_div_iff₀ (by positivity)]
    linarith
  have hcore3 := n9_l4_m3_core (s := P) (M := Real.log (Real.log q)) (Lg := Real.log q)
    (W := W) hPge hPleL' hMexp hW8
  have hexp2 : Real.exp (2 * z0 (hbZ q η) x) ≤ Real.exp (1004 / 10000 * P) := by
    refine Real.exp_le_exp.mpr ?_
    have h : z0 (hbZ q η) x ≤ 501 * hbZ0 q η := hzzhi
    rw [hw0eq] at h
    linarith
  have hterm3 : (x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)
      ≤ (x : ℝ) * (Real.exp (-(W / 8)) + Real.exp (-(25 * Real.log q))) := by
    have hA : (x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) ≤ (x : ℝ) * Real.exp (-(W / 8)) := by
      have hZ8 : Real.exp (W / 8) ≤ (hbZ q η : ℝ) ^ (1 / 8 : ℝ) := by
        rw [Real.rpow_def_of_pos hZpos]
        exact Real.exp_le_exp.mpr (by linarith)
      have h1 : (x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) ≤ (x : ℝ) / Real.exp (W / 8) := by
        rw [div_le_div_iff₀ (by positivity) (Real.exp_pos _)]
        nlinarith only [hZ8, hXpos, Real.exp_pos (W / 8)]
      have h2 : (x : ℝ) / Real.exp (W / 8) = (x : ℝ) * Real.exp (-(W / 8)) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      linarith
    have hB : (x : ℝ) ^ ((9 : ℝ) / 10) ≤ (x : ℝ) * Real.exp (-(25 * Real.log q)) := by
      rw [Real.rpow_def_of_pos hXpos]
      have h2 : Real.exp (Real.log (x : ℝ) * (9 / 10))
          ≤ Real.exp (Real.log (x : ℝ) - 25 * Real.log q) :=
        Real.exp_le_exp.mpr (by linarith)
      have h3 : Real.exp (Real.log (x : ℝ) - 25 * Real.log q)
          = (x : ℝ) * Real.exp (-(25 * Real.log q)) := by
        rw [Real.exp_sub, Real.exp_log hXpos, Real.exp_neg, div_eq_mul_inv]
      linarith
    linarith
  have hLwin3 : Lwin x ^ 3 ≤ (502 * Real.log q) ^ 3 :=
    pow_le_pow_left₀ hLwinNn (by linarith) 3
  have rowM3 : L2cCmain * Real.exp (2 * z0 (hbZ q η) x)
      * ((x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3
      * hbZ0 q η ≤ 2 ^ 37 * (x : ℝ) := by
    simp only [L2cCmain]
    have hT0 : (0 : ℝ) ≤ (x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10) := by
      positivity
    have hA : Real.exp (2 * z0 (hbZ q η) x)
          * ((x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10)) * Lwin x ^ 3
        ≤ Real.exp (1004 / 10000 * P)
            * ((x : ℝ) * (Real.exp (-(W / 8)) + Real.exp (-(25 * Real.log q))))
            * (502 * Real.log q) ^ 3 :=
      mul_le_mul (mul_le_mul hexp2 hterm3 hT0 (Real.exp_pos _).le) hLwin3 (by positivity)
        (by positivity)
    calc 2 ^ 31 * Real.exp (2 * z0 (hbZ q η) x)
            * ((x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10))
            * Lwin x ^ 3 * hbZ0 q η
        = 2 ^ 31 * (Real.exp (2 * z0 (hbZ q η) x)
            * ((x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10))
            * Lwin x ^ 3 * hbZ0 q η) := by ring
      _ ≤ 2 ^ 31 * ((x : ℝ) * 64) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc Real.exp (2 * z0 (hbZ q η) x)
                  * ((x : ℝ) / (hbZ q η : ℝ) ^ (1 / 8 : ℝ) + (x : ℝ) ^ ((9 : ℝ) / 10))
                  * Lwin x ^ 3 * hbZ0 q η
              ≤ (Real.exp (1004 / 10000 * P)
                  * ((x : ℝ) * (Real.exp (-(W / 8)) + Real.exp (-(25 * Real.log q))))
                  * (502 * Real.log q) ^ 3) * hbZ0 q η :=
                mul_le_mul_of_nonneg_right hA hz0pos.le
            _ = (x : ℝ) * (Real.exp (1004 / 10000 * P) * (502 * Real.log q) ^ 3 * (P / 10000)
                  * (Real.exp (-(W / 8)) + Real.exp (-(25 * Real.log q)))) := by
                rw [hw0eq]; ring
            _ ≤ (x : ℝ) * 64 := mul_le_mul_of_nonneg_left hcore3 hXpos.le
      _ = 2 ^ 37 * (x : ℝ) := by ring
  -- ROW S: the star term
  have hεval : ε = 5 / P := by rw [hεdef, hw0eq]; field_simp; norm_num
  have hεinv : 1 / ε = P / 5 := by rw [hεval, one_div_div]
  have hε3 : 3 / ε = 3 * P / 5 := by rw [hεval]; field_simp
  have hbase : (0 : ℝ) < 3 / ε := by positivity
  have hlogC : Real.log C = ((2 : ℝ) ^ (1 / ε) + 1) * Real.log (3 / ε) := by
    rw [hCdef, Real.log_rpow hbase]
  have h2pow : (2 : ℝ) ^ (1 / ε) ≤ Real.exp (P / 7) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hεinv]
    refine Real.exp_le_exp.mpr ?_
    have hl2 := Real.log_two_lt_d9
    nlinarith only [hl2, hPpos]
  have hlog3ε : Real.log (3 / ε) ≤ P := by
    rw [hε3]
    have h1 : Real.log (3 * P / 5) ≤ 3 * P / 5 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hlog3εnn : 0 ≤ Real.log (3 / ε) := by
    rw [hε3]; exact Real.log_nonneg (by linarith)
  have hlogCle : Real.log C ≤ Real.exp (3 / 20 * P) := by
    have h1 : ((2 : ℝ) ^ (1 / ε) + 1) * Real.log (3 / ε) ≤ (Real.exp (P / 7) + 1) * P :=
      mul_le_mul (by linarith) hlog3ε hlog3εnn (by positivity)
    have hone : (1 : ℝ) ≤ Real.exp (P / 7) := by
      have h := Real.add_one_le_exp (P / 7); linarith
    have h2 : (Real.exp (P / 7) + 1) * P ≤ 2 * P * Real.exp (P / 7) := by
      nlinarith only [hone, hPpos]
    have hkey : 2 * P ≤ Real.exp (P / 140) := by
      have h := n9_sq_le_exp (t := P / 140) (by linarith)
      nlinarith only [h, hPge]
    have h3 : 2 * P * Real.exp (P / 7) ≤ Real.exp (3 / 20 * P) := by
      calc 2 * P * Real.exp (P / 7) ≤ Real.exp (P / 140) * Real.exp (P / 7) :=
            mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
        _ = Real.exp (3 / 20 * P) := by
            rw [← Real.exp_add]; congr 1; ring
    linarith [hlogC]
  have hCle : C ≤ Real.exp (Real.exp (3 / 20 * P)) := by
    have h := Real.exp_le_exp.mpr hlogCle
    rwa [Real.exp_log hCpos] at h
  have hWlo : 1000000 * Real.exp P / P ≤ W := by
    rw [hWeq, div_le_div_iff₀ hPpos hPpos]
    nlinarith only [hLg, hPpos]
  have hGW : 2 * Real.exp (3 / 20 * P) ≤ W / 5 := by
    have hb : (17 / 20 * P) ^ 2 ≤ 4 * Real.exp (17 / 20 * P) := n9_sq_le_exp (by linarith)
    have h2P : 2 * P ≤ 200000 * Real.exp (17 / 20 * P) := by nlinarith only [hb, hPge, hPpos]
    have hGP : 2 * P * Real.exp (3 / 20 * P) ≤ 200000 * Real.exp P := by
      calc 2 * P * Real.exp (3 / 20 * P)
          ≤ (200000 * Real.exp (17 / 20 * P)) * Real.exp (3 / 20 * P) :=
            mul_le_mul_of_nonneg_right h2P (Real.exp_pos _).le
        _ = 200000 * Real.exp P := by
            rw [mul_assoc, ← Real.exp_add, show 17 / 20 * P + 3 / 20 * P = P by ring]
    have hstep : 2 * Real.exp (3 / 20 * P) ≤ 200000 * Real.exp P / P := by
      rw [le_div_iff₀ hPpos]; linarith
    have heq : 1000000 * Real.exp P / P / 5 = 200000 * Real.exp P / P := by ring
    linarith
  have hquart : 1004004 * Real.log q ^ 4 ≤ Real.exp (W / 5) := by
    have hL4 : Real.exp (4 * Real.log (Real.log q)) = Real.log q ^ 4 := by
      rw [show (4 : ℝ) * Real.log (Real.log q) = ((4 : ℕ) : ℝ) * Real.log (Real.log q) by
        norm_num, Real.exp_nat_mul, Real.exp_log hL]
    have hc : (1004004 : ℝ) ≤ Real.exp 1004004 := by
      have h := Real.add_one_le_exp (1004004 : ℝ); linarith
    have h3 : (1000001 : ℝ) ≤ Real.exp (10 ^ 6 : ℝ) := by
      have h := Real.add_one_le_exp (10 ^ 6 : ℝ); linarith
    have hle : 1004004 + 4 * Real.log (Real.log q) ≤ W / 5 := by
      have h1 : 48 * Real.log (Real.log q) ≤ W := by linarith
      linarith
    calc 1004004 * Real.log q ^ 4
        = 1004004 * Real.exp (4 * Real.log (Real.log q)) := by rw [hL4]
      _ ≤ Real.exp 1004004 * Real.exp (4 * Real.log (Real.log q)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = Real.exp (1004004 + 4 * Real.log (Real.log q)) := by rw [← Real.exp_add]
      _ ≤ Real.exp (W / 5) := Real.exp_le_exp.mpr hle
  have htbound : (2 * (x : ℝ) + 2) ^ ε ≤ Real.exp (501 / 2000 * W) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : Real.log (2 * (x : ℝ) + 2) * ε ≤ (501 * Real.log q) * ε :=
      mul_le_mul_of_nonneg_right hLwinLe hεpos.le
    have h2 : (501 * Real.log q) * ε = 501 / 2000 * W := by
      rw [hεdef, hWdef]; field_simp
    linarith
  have htnn : (0 : ℝ) ≤ (2 * (x : ℝ) + 2) ^ ε := by positivity
  have htl : (0 : ℝ) ≤ 2 * (x : ℝ) / (hbZ q η : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ) := by positivity
  have htlle : 2 * (x : ℝ) / (hbZ q η : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)
      ≤ 2 * (x : ℝ) * Real.exp (-W) + 2 * (x : ℝ) * Real.exp (-(125 * Real.log q)) := by
    have hA : 2 * (x : ℝ) / (hbZ q η : ℝ) ≤ 2 * (x : ℝ) * Real.exp (-W) := by
      have h1 : 2 * (x : ℝ) / (hbZ q η : ℝ) ≤ 2 * (x : ℝ) / Real.exp W := by
        rw [div_le_div_iff₀ hZpos (Real.exp_pos _)]
        nlinarith only [hZge, hXpos, Real.exp_pos W]
      have h2 : 2 * (x : ℝ) / Real.exp W = 2 * (x : ℝ) * Real.exp (-W) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      linarith
    have hB : (Nat.sqrt (2 * x + 2) : ℝ) ≤ 2 * (x : ℝ) * Real.exp (-(125 * Real.log q)) := by
      have hBnn : (0 : ℝ) ≤ 2 * (x : ℝ) * Real.exp (-(125 * Real.log q)) := by positivity
      have hs2 : ((Nat.sqrt (2 * x + 2) : ℕ) : ℝ) ^ 2 ≤ 4 * (x : ℝ) := by
        have h := Nat.sqrt_le' (2 * x + 2)
        have hc : ((Nat.sqrt (2 * x + 2) : ℕ) : ℝ) ^ 2 ≤ ((2 * x + 2 : ℕ) : ℝ) := by
          exact_mod_cast h
        push_cast at hc
        linarith
      have he : Real.exp (-(125 * Real.log q)) ^ 2 = Real.exp (-(250 * Real.log q)) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have h1 : Real.exp (250 * Real.log q) * Real.exp (-(250 * Real.log q)) = 1 := by
        rw [← Real.exp_add]; simp
      have hkey : 1 ≤ (x : ℝ) * Real.exp (-(250 * Real.log q)) := by
        have h2 := mul_le_mul_of_nonneg_right hx250
          (Real.exp_pos (-(250 * Real.log q))).le
        rw [h1] at h2
        linarith
      have hexpand : (2 * (x : ℝ) * Real.exp (-(125 * Real.log q))) ^ 2
          = 4 * (x : ℝ) * ((x : ℝ) * Real.exp (-(250 * Real.log q))) := by
        rw [mul_pow, mul_pow, he]; ring
      have hBsq : 4 * (x : ℝ) ≤ (2 * (x : ℝ) * Real.exp (-(125 * Real.log q))) ^ 2 := by
        rw [hexpand]; nlinarith only [hkey, hXpos]
      have hfin : ((Nat.sqrt (2 * x + 2) : ℕ) : ℝ) ^ 2
          ≤ (2 * (x : ℝ) * Real.exp (-(125 * Real.log q))) ^ 2 := by linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) hBnn hfin
    linarith
  have rowS : 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
      * (2 * (x : ℝ) / (hbZ q η : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) * hbZ0 q η
      ≤ 2 ^ 37 * (x : ℝ) := by
    exact n9_l4_star_core hPge hLhuge hz0pos hw0L hWle hquart hGW hCpos.le hCle
      htnn htbound hLwinNn hLwinLe hx250 htl htlle
  -- the ledger, summed
  refine le_trans (hb_lemma4_l2cWindow χ hR.sq (Nat.pos_of_ne_zero (NeZero.ne q)) hεpos hCpos
    hCtau hz100 hz8 hzx) ?_
  rw [le_div_iff₀ hz0pos]
  simp only [lemma4Err, add_mul]
  refine le_trans (add_le_add (add_le_add rowA
    (add_le_add (add_le_add rowM1 rowM2) rowM3)) rowS) ?_
  nlinarith [hXpos]

/-- **The p.200 constant** (a ceiling in the N7 constants). -/
noncomputable def n9K3 (Cerr CA CA' CC : ℝ) : ℝ :=
  Real.exp 300 * (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr)

/-- `C(4) = 2`: the product over the odd prime factors of `4` is empty. -/
private lemma n9_calpha_four : hbCalpha 4 = 2 := by
  have h4 : (4 : ℕ).primeFactors = {2} := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_pow 2 (by norm_num),
      Nat.Prime.primeFactors Nat.prime_two]
  simp [hbCalpha, h4, Finset.filter_singleton]

/-- **A NUMERAL LOWER BOUND ON THE TWIN SINGULAR SERIES** — the corpus carries only
`twinSingularSeries_pos` and `twinSingularSeries_lt_two` (`HardyLittlewood/Frame.lean:103,107`),
and Theorem 1 CANNOT convert Lemma 4's ABSOLUTE error `2^40·x/z₀` into a relative error against
`x·𝔖·C(4)` without one.  `log(1 − (p−1)^{−2}) ≥ −8/p²` (`abs_log_twinFactor_le`) and the tail
`tsum_tail_inv_sq_le` at `K = 8`, `N = 2` give `∑' log ≥ −4`, so `Π₂ = exp(∑' log) ≥ e^{−4}`
and `𝔖 = 2Π₂ ≥ 2/56 = 1/28` (`exp 4 ≤ 2.7182818286^4 ≤ 56`). -/
private lemma n9_singular_ge : (1 : ℝ) / 28 ≤ Salt.HardyLittlewood.twinSingularSeries := by
  have hnonpos : ∀ p : Salt.TwinBar.PrimesGt2,
      Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) ≤ 0 := by
    intro p
    have h := Salt.TwinBar.twinC2_factor_pos p
    have hnn : (0 : ℝ) ≤ ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹ := by positivity
    exact Real.log_nonpos h.le (by linarith only [hnn])
  have hbnd : ∀ p : Salt.TwinBar.PrimesGt2,
      -Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) ≤ 8 / (((p : ℕ)) : ℝ) ^ 2 := by
    intro p
    have h := abs_log_twinFactor_le p
    rwa [abs_of_nonpos (hnonpos p)] at h
  have htail := tsum_tail_inv_sq_le (ι := Salt.TwinBar.PrimesGt2)
    (fun p => (p : ℕ)) Subtype.val_injective
    (fun p => -Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹))
    (K := 8) (by norm_num) (N := 2) (by norm_num) (fun p => p.2.2) hbnd
  rw [tsum_neg] at htail
  have hexp : Salt.TwinBar.twinC2
      = Real.exp (∑' p : Salt.TwinBar.PrimesGt2,
          Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹)) := by
    rw [Salt.TwinBar.twinC2]
    exact (Real.rexp_tsum_eq_tprod Salt.TwinBar.twinC2_factor_pos
      Salt.TwinBar.twinC2_log_summable).symm
  have hge : Real.exp (-4 : ℝ) ≤ Salt.TwinBar.twinC2 := by
    rw [hexp]
    refine Real.exp_le_exp.mpr ?_
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2] at htail
    linarith only [htail]
  have he1 := Real.exp_one_lt_d9
  have hpos1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h4eq : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h4le : Real.exp (4 : ℝ) ≤ 56 := by
    have hp : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hpos1.le he1.le 4
    rw [h4eq]
    nlinarith only [hp]
  have h4pos : (0 : ℝ) < Real.exp (4 : ℝ) := Real.exp_pos _
  have hinv : (1 : ℝ) / 56 ≤ Real.exp (-4 : ℝ) := by
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by norm_num) h4pos]
    linarith only [h4le]
  have hpi : Salt.HardyLittlewood.twinSingularSeries = 2 * Salt.TwinBar.twinC2 := rfl
  rw [hpi]
  linarith only [hge, hinv]
set_option maxHeartbeats 2000000 in
-- The p.200 sandwich composed with `(L2)`, `(L1)` and the FL/sieve-error rows: one ledger
-- over a context of ~120 facts, with four opaque N7 constants carried symbolically.
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
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, hPbig, hPsmall, hlog4qpos, hW2L, -⟩ := n9_num_facts hR
  obtain ⟨hz0pos, hz0ge, hWbig, hWle, hlogzge, hlogzle⟩ := n9_scale hR
  obtain ⟨hz2, -, -, -, hzt, h32, -, hD, hlev, -, hLam⟩ := hbZ_packet hR hx hx'
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  have hqpos : 0 < q := by omega
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith only [hqR]
  have hLne : Real.log q ≠ 0 := ne_of_gt hL
  have hηne : η ≠ 0 := ne_of_gt hηpos
  -- `ℓ′` and the opaque constants
  have hEpos : (0 : ℝ) < n9Ell q η := by linarith only [hPbig]
  have hEsqrt : (0 : ℝ) < Real.sqrt (n9Ell q η) := Real.sqrt_pos.mpr hEpos
  have hEsq : Real.sqrt (n9Ell q η) ^ 2 = n9Ell q η := Real.sq_sqrt hEpos.le
  have hEsq1 : (1 : ℝ) ≤ Real.sqrt (n9Ell q η) := by nlinarith only [hEsq, hEsqrt, hPbig]
  have hn9Cs : (3400 : ℝ) ≤ n9Cs := by
    have h := invSqC_spec.1
    simp only [n9Cs, dhB]
    nlinarith only [h]
  obtain ⟨ec, hecdef⟩ : ∃ ec : ℝ, ec = 802 + 4 * n9Cs := ⟨_, rfl⟩
  have hec : (14402 : ℝ) ≤ ec := by rw [hecdef]; linarith only [hn9Cs]
  have hec0 : (0 : ℝ) < ec := by linarith only [hec]
  have hEec : (Real.exp 300 * ec) ^ 8 ≤ n9Ell q η := by
    have ha : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    have hc : (0 : ℝ) < Real.exp (3 * 10 ^ 6 : ℝ) := Real.exp_pos _
    have h := hR.ellBig
    simp only [n9E0, ← hecdef] at h
    linarith only [h, ha, hc]
  have hEecbig : 300 * ec ≤ n9Ell q η := by
    have h1 : (301 : ℝ) ≤ Real.exp 300 := by
      have := Real.add_one_le_exp (300 : ℝ); linarith only [this]
    have hX1 : (1 : ℝ) ≤ Real.exp 300 * ec := by nlinarith only [h1, hec]
    have hX8 : (Real.exp 300 * ec) ^ 1 ≤ (Real.exp 300 * ec) ^ 8 :=
      pow_le_pow_right₀ hX1 (by norm_num)
    rw [pow_one] at hX8
    have h2 : 300 * ec ≤ Real.exp 300 * ec := by nlinarith only [h1, hec0]
    linarith only [h2, hX8, hEec]
  -- `ℓ′ ≤ log η`, hence `η` beats every opaque constant
  have hEllLogη : n9Ell q η ≤ Real.log η := by
    have hinv : 0 ≤ Real.log (1 / dhC) :=
      Real.log_nonneg (by rw [le_div_iff₀ dh_spec.1]; linarith [dh_spec.2.1])
    have hLle : Real.log q ≤ Real.log (4 * (q : ℝ)) + 2 := by
      have h : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
        Real.log_le_log hqR0 (by linarith only [hqR0])
      linarith only [h]
    have hlogLle : Real.log (Real.log q) ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      Real.log_le_log hL hLle
    have hXnn : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      Real.log_nonneg (by linarith only [hlog4qpos])
    have hdk : dhK = 14 := rfl
    have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
      Real.log_mul hηne hLne
    simp only [n9Ell, hdk, hsplit]
    linarith only [hinv, hlogLle, hXnn]
  have hηell : n9Ell q η ≤ η := by
    have h1 : Real.exp (n9Ell q η) ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr hEllLogη
    rw [Real.exp_log hηpos] at h1
    have h2 := Real.add_one_le_exp (n9Ell q η)
    linarith only [h1, h2]
  have hηbig2 : (3000001 : ℝ) ≤ η := by linarith only [hηell, hPbig]
  -- the split point and its logarithm
  have hZ2 : (2 : ℝ) ≤ (hbZ q η : ℝ) := by exact_mod_cast hz2
  have hZpos : (0 : ℝ) < (hbZ q η : ℝ) := by linarith only [hZ2]
  have hlogZpos : (0 : ℝ) < Real.log (hbZ q η : ℝ) := Real.log_pos (by linarith only [hZ2])
  have hsqL : Real.sqrt (Real.log q) ^ 2 = Real.log q := Real.sq_sqrt hL.le
  have hsqLpos : (0 : ℝ) < Real.sqrt (Real.log q) := Real.sqrt_pos.mpr hL
  have hsqLbig : (1224 : ℝ) ≤ Real.sqrt (Real.log q) := by
    rw [show (1224 : ℝ) = Real.sqrt (1224 ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1224)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith only [hLhuge])
  have hEsqL : 10 * Real.sqrt (n9Ell q η) ≤ Real.sqrt (Real.log q) := by
    have h1 : Real.sqrt (100 * n9Ell q η) ≤ Real.sqrt (Real.log q) :=
      Real.sqrt_le_sqrt (by linarith only [hPsmall])
    have h2 : Real.sqrt (100 * n9Ell q η) = 10 * Real.sqrt (n9Ell q η) := by
      rw [show (100 : ℝ) * n9Ell q η = 10 ^ 2 * n9Ell q η by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]
    linarith only [h1, h2]
  have hlogE : (14 : ℝ) ≤ Real.log (n9Ell q η) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3000001) hPbig
    have h2 : (14 : ℝ) ≤ Real.log 3000001 := by
      rw [show (14 : ℝ) = Real.log (Real.exp 14) by rw [Real.log_exp]]
      refine Real.log_le_log (Real.exp_pos _) ?_
      have he : Real.exp 14 = Real.exp 1 ^ 14 := by
        rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      have h1 := Real.exp_one_lt_d9
      have h3 : Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt h1) 14
      rw [he]; norm_num at h3 ⊢; linarith only [h3]
    linarith only [h, h2]
  have hlogEsq : Real.log (n9Ell q η) ≤ 2 * Real.sqrt (n9Ell q η) :=
    n9_log_le_two_sqrt hEpos
  have hlogZ25 : 25000 * Real.sqrt (Real.log q) ≤ Real.log (hbZ q η : ℝ) := by
    have hz0small : hbZ0 q η ≤ Real.log q / 10000 := by
      have hz0eq : hbZ0 q η = 1 / 10000 * Real.log (n9Ell q η) := by
        simp only [hbZ0, hbZ0A]
      have hle : Real.log (n9Ell q η) ≤ Real.log q := by
        have h1 : Real.log (n9Ell q η) ≤ n9Ell q η := by
          linarith only [Real.log_le_sub_one_of_pos hEpos]
        linarith only [h1, hPsmall, hL]
      rw [hz0eq]; linarith only [hle]
    have hWeq : Real.log q / hbZ0 q η = 10000 * Real.log q / Real.log (n9Ell q η) := by
      have hz0 : hbZ0 q η = 1 / 10000 * Real.log (n9Ell q η) := by
        simp only [hbZ0, hbZ0A]
      rw [hz0]
      have hPpos : (0 : ℝ) < Real.log (n9Ell q η) := by linarith only [hlogE]
      field_simp
    have h1 : 25000 * Real.sqrt (Real.log q) ≤ 10000 * Real.log q / Real.log (n9Ell q η) := by
      rw [le_div_iff₀ (by linarith only [hlogE])]
      nlinarith only [hlogEsq, hEsqL, hsqL, hsqLpos, hEsqrt, hL]
    rw [hWeq] at hlogzge
    linarith only [h1, hlogzge]
  have hlogZL : Real.log (hbZ q η : ℝ) ≤ Real.log q := by
    have h1 : Real.log q / hbZ0 q η ≤ Real.log q / 300 := hWle
    linarith only [hlogzle, h1, hLhuge]
  -- `κ ≥ 0` and `(P, 4) = 1`
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hκ : 0 ≤ hbKappaN9 χ x (hbZ q η) := by
    have htail : 0 < hbKappaTail χ 4 := by
      rw [hbKappaTail, ← Real.rexp_tsum_eq_tprod
        (fun p => hbWfac_pos χ 4 (three_le_of_primesGt2 p)) (hbWfac_log_summable χ 4)]
      exact Real.exp_pos _
    have hp1 : (0 : ℝ) ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ 4), (1 - 2 / (p : ℝ)) := by
      refine Finset.prod_nonneg (fun p hp => ?_)
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      obtain ⟨⟨hprime, -, -⟩, hnd⟩ := hp
      have hne2 : p ≠ 2 := by rintro rfl; exact hnd (by norm_num)
      have hp3n : 3 ≤ p := by have := hprime.two_le; omega
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3n
      have h2p : 2 / (p : ℝ) ≤ 2 / 3 := by
        rw [div_le_div_iff₀ (by linarith only [hp3]) (by norm_num)]; linarith only [hp3]
      linarith only [h2p]
    have hp2 : (0 : ℝ) ≤ ∏ p ∈ (4 : ℕ).primeFactors,
        (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2 :=
      Finset.prod_nonneg (fun p _ => sq_nonneg _)
    simp only [hbKappaN9, hbKappa]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx0
      (sq_nonneg (hbL1 χ ((hbZ q η : ℝ) - 1)))) hp1) hp2) htail.le
  have hPα : Nat.Coprime (hbDataN8 χ hR.sq hz2 x).P 4 := by
    have hPodd := (hbDataN8 χ hR.sq hz2 x).P_odd
    have hPsf := (hbDataN8 χ hR.sq hz2 x).P_squarefree
    have h2 : ¬ (2 ∣ (hbDataN8 χ hR.sq hz2 x).P) := by
      intro hdvd
      exact hPodd 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd, hPsf.ne_zero⟩) rfl
    have hcop2 : Nat.Coprime (hbDataN8 χ hR.sq hz2 x).P 2 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 hcop2
  -- the two p.200 sides
  have hlev' : levelE (Lam4 (1 / 4) ((hbZ q η : ℕ) : ℝ)) ≤ hbS q η := by linarith only [hlev]
  have hL3 : (3 : ℝ) ≤ Real.log q := by linarith only [hLhuge]
  obtain ⟨C₀, Afun, A'fun, hL5⟩ := hN7 q χ hR.sq hz2 x
  have hup := hb_p200_upper χ hR.sq hz2 (lam := 1 / 4) (sRatio := hbS q η) (L := Real.log q)
    (by norm_num) (by norm_num) hzt hlev' hL3 hD hPα hκ hL5
  have hlo := hb_p200_lower χ hR.sq hz2 (lam := 1 / 4) (sRatio := hbS q η) (L := Real.log q)
    (by norm_num) (by norm_num) hzt hlev' hL3 hD hPα hκ hL5
  -- `κ·W` from `(L2)`
  obtain ⟨δ, hδeq, hδle⟩ := hb_L2_at_hb_point hR hx hx'
  have hS1W : hbS1 χ 4 ((hbZ q η : ℝ) - 1) = W (hbDataN8 χ hR.sq hz2 x).sieve :=
    hbS1_eq_W χ hR.sq hz2 x (by norm_num) (fun p hp hpd => by
      have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by norm_num at hpd ⊢; exact hpd)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2)
  rw [hS1W] at hδeq
  -- the target scale
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ,
      T = (x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4 := ⟨_, rfl⟩
  have hxbig : (375000000 : ℝ) ≤ (x : ℝ) := by
    have hq250 : Real.exp (250 * Real.log q) = (q : ℝ) ^ (250 : ℕ) := by
      rw [show (250 : ℝ) * Real.log q = ((250 : ℕ) : ℝ) * Real.log q by norm_num,
        Real.exp_nat_mul, Real.exp_log hqR0]
    have h := Real.add_one_le_exp (250 * Real.log q)
    rw [hq250] at h
    linarith only [h, hx, hLhuge]
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith only [hxbig]
  have hT14 : (x : ℝ) / 14 ≤ T := by
    rw [hTdef, n9_calpha_four]
    nlinarith only [n9_singular_ge, hxpos]
  have hTpos : (0 : ℝ) < T := by linarith only [hT14, hxpos]
  have hP2pos : (0 : ℝ) < (η * Real.log q) ^ 2 := by positivity
  have hKWP2 : hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve
      * (η * Real.log q) ^ 2 = (1 + δ) * T := by
    rw [hδeq, ← hTdef]
    field_simp
  -- `|δ| ≤ n9K2 (SA + SB)`
  obtain ⟨SA, hSAdef⟩ : ∃ SA : ℝ,
      SA = Real.log (n9Ell q η) / Real.sqrt (n9Ell q η) := ⟨_, rfl⟩
  obtain ⟨SB, hSBdef⟩ : ∃ SB : ℝ, SB = 1 / Real.sqrt (Real.log q) := ⟨_, rfl⟩
  obtain ⟨SC, hSCdef⟩ : ∃ SC : ℝ, SC = 1 / η := ⟨_, rfl⟩
  obtain ⟨SD, hSDdef⟩ : ∃ SD : ℝ, SD = Real.exp (-Real.log 4 * hbS q η) := ⟨_, rfl⟩
  have hSA0 : (0 : ℝ) ≤ SA := by rw [hSAdef]; positivity
  have hSB0 : (0 : ℝ) < SB := by rw [hSBdef]; positivity
  have hSC0 : (0 : ℝ) < SC := by rw [hSCdef]; positivity
  have hSD0 : (0 : ℝ) < SD := by rw [hSDdef]; exact Real.exp_pos _
  rw [← hSAdef, ← hSBdef] at hδle
  have hδsmall : |δ| ≤ n9K2 * (SA + SB) := hδle
  -- the `(L1)` window on `LL`
  obtain ⟨u, hudef⟩ : ∃ u : ℝ,
      u = (1606 + 8 * n9Cs) / (η * Real.sqrt (n9Ell q η)) := ⟨_, rfl⟩
  have hu0 : (0 : ℝ) ≤ u := by
    rw [hudef]; positivity
  have huP2 : u * (η * Real.log q)
      = (1606 + 8 * n9Cs) * (Real.log q / Real.sqrt (n9Ell q η)) := by
    rw [hudef]; field_simp
  have huSC : u ≤ 3 * ec * SC := by
    have h1 : 3 * ec * SC = (2406 + 12 * n9Cs) / η := by
      rw [hSCdef, hecdef]; field_simp; ring
    rw [hudef, h1, div_le_div_iff₀ (by positivity) hηpos]
    have hprod : (0 : ℝ) ≤ (2406 + 12 * n9Cs) * η * (Real.sqrt (n9Ell q η) - 1) :=
      mul_nonneg (mul_nonneg (by linarith only [hn9Cs]) hηpos.le) (by linarith only [hEsq1])
    nlinarith only [hprod, hn9Cs, hηpos]
  have husmall : u ≤ 1 / 100 := by
    have hstep : (100 : ℝ) * (1606 + 8 * n9Cs) ≤ η * Real.sqrt (n9Ell q η) := by
      have h1 : n9Ell q η ≤ η * Real.sqrt (n9Ell q η) := by
        nlinarith only [hηell, hEsq1, hEpos, hηpos]
      have h2 : (100 : ℝ) * (1606 + 8 * n9Cs) ≤ 300 * ec := by
        rw [hecdef]; linarith only [hn9Cs]
      linarith only [h1, h2, hEecbig]
    rw [hudef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hstep]
  have hLLhi : hbLL χ ≤ (1 + u) * (η * Real.log q) := by
    have h := hb_L1_upper_at_hb_point hR
    rw [show (1 + u) * (η * Real.log q) = η * Real.log q + u * (η * Real.log q) by ring, huP2]
    exact h
  have hLLlo : (1 - u) * (η * Real.log q) ≤ hbLL χ := by
    have h := hb_L1_lower_at_hb_point hR
    rw [show (1 - u) * (η * Real.log q) = η * Real.log q - u * (η * Real.log q) by ring, huP2]
    exact h
  have hηLpos : (0 : ℝ) < η * Real.log q := by positivity
  have hLL0 : (0 : ℝ) ≤ hbLL χ := by nlinarith only [hLLlo, husmall, hu0, hηLpos]
  have hLLsq_hi : hbLL χ ^ 2 ≤ (1 + 3 * u) * (η * Real.log q) ^ 2 := by
    have h1 : hbLL χ ^ 2 ≤ ((1 + u) * (η * Real.log q)) ^ 2 :=
      pow_le_pow_left₀ hLL0 hLLhi 2
    have h2 : ((1 + u) * (η * Real.log q)) ^ 2 = (1 + 2 * u + u ^ 2) * (η * Real.log q) ^ 2 := by
      ring
    have h3 : (0 : ℝ) ≤ (η * Real.log q) ^ 2 := sq_nonneg _
    have h4 : u ^ 2 ≤ u := by nlinarith only [hu0, husmall]
    have h5 : (0 : ℝ) ≤ (u - u ^ 2) * (η * Real.log q) ^ 2 :=
      mul_nonneg (by linarith only [h4]) h3
    nlinarith only [h1, h2, h5]
  have hLLsq_lo : (1 - 2 * u) * (η * Real.log q) ^ 2 ≤ hbLL χ ^ 2 := by
    have h0 : (0 : ℝ) ≤ (1 - u) * (η * Real.log q) := by
      nlinarith only [hu0, husmall, hηLpos]
    have h1 : ((1 - u) * (η * Real.log q)) ^ 2 ≤ hbLL χ ^ 2 :=
      pow_le_pow_left₀ h0 hLLlo 2
    have h2 : ((1 - u) * (η * Real.log q)) ^ 2 = (1 - 2 * u + u ^ 2) * (η * Real.log q) ^ 2 := by
      ring
    have h3 : (0 : ℝ) ≤ (η * Real.log q) ^ 2 := sq_nonneg _
    nlinarith only [h1, h2, h3, sq_nonneg u]
  have hB3 : Real.log q + |hbLL χ| ≤ 3 * (η * Real.log q) := by
    rw [abs_of_nonneg hLL0]
    nlinarith only [hLLhi, husmall, hu0, hL, hηbig2, hηLpos]
  -- the FL factor
  obtain ⟨FC, hFCdef⟩ : ∃ FC : ℝ,
      FC = flConst (1 / 4 : ℝ) (Lam4 (1 / 4) ((hbZ q η : ℕ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (-flRate (1 / 4 : ℝ) * hbS q η) := ⟨_, rfl⟩
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hflRate : flRate (1 / 4 : ℝ) = Real.log 4 := by
    rw [flRate, show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]; ring
  have hESD : E = SD := by rw [hEdef, hSDdef, hflRate]
  have hside : (1 / 4 : ℝ) * Real.exp (1 + 1 / 4) < 1 := by
    have hlog2 := Real.log_two_gt_d9
    have h5 : Real.exp (1 + 1 / 4 : ℝ) < Real.exp (Real.log 4) :=
      Real.exp_lt_exp.mpr (by rw [hlog4]; linarith only [hlog2])
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h5
    linarith only [h5]
  have hFC0 : 0 < FC := by rw [hFCdef]; exact flConst_pos (by norm_num) hside
  have hFCle : FC ≤ 14 * Real.exp 31 := by rw [hFCdef]; exact flConst_quarter_le hLam
  have hE0 : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have hFCE : FC * E ≤ 14 * Real.exp 31 * SD := by
    rw [← hESD]; nlinarith only [hFCle, hE0]
  have hbSbig : (99 : ℝ) ≤ hbS q η := by
    have h1 : 297 * Real.log (hbZ q η : ℝ) ≤ Real.log q := by
      have h2 : Real.log q / hbZ0 q η ≤ Real.log q / 300 := hWle
      linarith only [hlogzle, h2, hLhuge]
    rw [hbS, le_div_iff₀ (by positivity)]
    linarith only [h1]
  have hFCE1 : FC * E ≤ 1 := by
    have hl2 := Real.log_two_gt_d9
    have hEsm : E ≤ Real.exp (-137) := by
      rw [hEdef, hflRate]
      refine Real.exp_le_exp.mpr ?_
      nlinarith only [hl2, hbSbig, hlog4]
    have h14 : (14 : ℝ) ≤ Real.exp 4 := by
      have h1 := Real.exp_one_gt_d9
      have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      have h3 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 4
      rw [h2]; norm_num at h3 ⊢; linarith only [h3]
    have hFC35 : FC ≤ Real.exp 35 := by
      have h2 : Real.exp 4 * Real.exp 31 = Real.exp 35 := by rw [← Real.exp_add]; norm_num
      nlinarith only [hFCle, h14, h2, Real.exp_pos (31 : ℝ)]
    have h3 : Real.exp 35 * Real.exp (-137 : ℝ) = Real.exp (-102) := by
      rw [← Real.exp_add]; norm_num
    have h4 : Real.exp (-102 : ℝ) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    nlinarith only [hFC35, hEsm, hFC0, hE0, h3, h4]
  -- the sieve error
  have hCC : (0 : ℝ) ≤ CC := by
    have h := hL5.C₀_le
    have hpos : (0 : ℝ) < (Real.log q + |hbLL χ|) * Real.log q := by
      have h2 := abs_nonneg (hbLL χ); nlinarith only [h2, hL3]
    nlinarith only [h, abs_nonneg C₀, hpos]
  have hn8C60 : (0 : ℝ) ≤ n8C6 CA CA' CC := by
    have h1 := hL5.CA_nonneg
    have h2 := hL5.CA'_nonneg
    simp only [n8C6]
    positivity
  have hCerr0 : (0 : ℝ) ≤ Cerr := hL5.Cerr_nonneg
  have hmert : mertens2C ≤ 18 := by
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    have hll : -Real.log (Real.log 2) ≤ 1 / 2 := by
      have h1 : Real.log (1 / Real.log 2) ≤ 1 / Real.log 2 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (1 / Real.log 2) = -Real.log (Real.log 2) := by
        rw [one_div, Real.log_inv]
      have h3 : 1 / Real.log 2 ≤ 1.443 := by
        rw [div_le_iff₀ (by linarith only [hl2])]; linarith only [hl2]
      linarith only [h1, h2, h3]
    have h4 : 2 * (Real.log 4 + 4) / Real.log 2 ≤ 15.8 := by
      rw [div_le_iff₀ (by linarith only [hl2])]
      nlinarith only [hl2, hl2', hlog4]
    simp only [mertens2C]
    linarith only [hll, h4]
  have hz10 : Real.log q ^ 10 ≤ (hbZ q η : ℝ) := by
    have h20 : (Real.log (hbZ q η : ℝ) / 20) ^ 20 ≤ (hbZ q η : ℝ) := by
      have h1 : Real.log (hbZ q η : ℝ) / 20 ≤ Real.exp (Real.log (hbZ q η : ℝ) / 20) := by
        linarith only [Real.add_one_le_exp (Real.log (hbZ q η : ℝ) / 20)]
      have h2 : (Real.log (hbZ q η : ℝ) / 20) ^ 20
          ≤ (Real.exp (Real.log (hbZ q η : ℝ) / 20)) ^ 20 :=
        pow_le_pow_left₀ (by positivity) h1 20
      have h3 : (Real.exp (Real.log (hbZ q η : ℝ) / 20)) ^ 20 = (hbZ q η : ℝ) := by
        rw [← Real.exp_nat_mul,
          show ((20 : ℕ) : ℝ) * (Real.log (hbZ q η : ℝ) / 20) = Real.log (hbZ q η : ℝ) by
            push_cast; ring, Real.exp_log hZpos]
      linarith only [h2, h3]
    have h4 : (1250 * Real.sqrt (Real.log q)) ^ 20 ≤ (Real.log (hbZ q η : ℝ) / 20) ^ 20 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hlogZ25]) 20
    have h5 : (1250 * Real.sqrt (Real.log q)) ^ 20 = 1250 ^ 20 * Real.log q ^ 10 := by
      rw [mul_pow]
      congr 1
      rw [show (20 : ℕ) = 2 * 10 by norm_num, pow_mul, hsqL]
    have h6 : Real.log q ^ 10 ≤ 1250 ^ 20 * Real.log q ^ 10 := by
      nlinarith only [pow_nonneg hL.le 10]
    linarith only [h20, h4, h5, h6]
  have hErr : Cerr * (x : ℝ) * Real.log q ^ 4 / (hbZ q η : ℝ)
        * n8ErrSum (hbDataN8 χ hR.sq hz2 x).P
      ≤ T * (Cerr * Real.exp 300 * SB) := by
    have hPz : ∀ p ∈ (hbDataN8 χ hR.sq hz2 x).P.primeFactors, p ≤ hbZ q η := by
      intro p hp
      have h := (hbDataN8 χ hR.sq hz2 x).P_lt_z p hp
      have h2 : (p : ℝ) < ((hbZ q η : ℕ) : ℝ) := h
      exact_mod_cast le_of_lt (by exact_mod_cast h2)
    have hn8E := n8ErrSum_le _ (hbDataN8 χ hR.sq hz2 x).P_squarefree hz2 hPz
    have hexp4m : Real.exp (4 * mertens2C) ≤ Real.exp 72 :=
      Real.exp_le_exp.mpr (by linarith only [hmert])
    have hn8E' : n8ErrSum (hbDataN8 χ hR.sq hz2 x).P
        ≤ Real.exp 72 * Real.log q ^ 4 := by
      have h1 : Real.log (hbZ q η : ℝ) ^ 4 ≤ Real.log q ^ 4 :=
        pow_le_pow_left₀ hlogZpos.le hlogZL 4
      nlinarith only [hn8E, hexp4m, h1, Real.exp_pos (4 * mertens2C), pow_nonneg hlogZpos.le 4,
        Real.exp_pos (72 : ℝ)]
    have hfac : (0 : ℝ) ≤ Cerr * (x : ℝ) * Real.log q ^ 4 / (hbZ q η : ℝ) := by positivity
    have hstep : Cerr * (x : ℝ) * Real.log q ^ 4 / (hbZ q η : ℝ)
          * n8ErrSum (hbDataN8 χ hR.sq hz2 x).P
        ≤ Cerr * (x : ℝ) * Real.log q ^ 4 / (hbZ q η : ℝ) * (Real.exp 72 * Real.log q ^ 4) :=
      mul_le_mul_of_nonneg_left hn8E' hfac
    have hSBL10 : Real.log q ^ 9 ≤ SB * Real.log q ^ 10 := by
      have h1 : SB * Real.log q ^ 10 = Real.log q ^ 10 / Real.sqrt (Real.log q) := by
        rw [hSBdef]; ring
      rw [h1, le_div_iff₀ hsqLpos]
      have hLsq : Real.sqrt (Real.log q) ≤ Real.log q := by
        nlinarith only [hsqL, hsqLbig, hsqLpos]
      nlinarith only [hLsq, pow_nonneg hL.le 9]
    have he72 : (1 : ℝ) ≤ Real.exp 72 := by
      have := Real.add_one_le_exp (72 : ℝ); linarith only [this]
    have he300 : (10 ^ 12 : ℝ) ≤ Real.exp 300 := by
      have he10 : (11 : ℝ) ≤ Real.exp 10 := by
        have := Real.add_one_le_exp (10 : ℝ); linarith only [this]
      have h1 : Real.exp 300 = (Real.exp 10) ^ 30 := by
        rw [show (300 : ℝ) = ((30 : ℕ) : ℝ) * 10 by norm_num, Real.exp_nat_mul]
      have h2 : (11 : ℝ) ^ 30 ≤ (Real.exp 10) ^ 30 := pow_le_pow_left₀ (by norm_num) he10 30
      rw [h1]; norm_num at h2 ⊢; linarith only [h2]
    have he72' : (14 : ℝ) * Real.exp 72 ≤ Real.exp 300 * Real.log q := by
      have h1 : Real.exp 72 ≤ Real.exp 300 := Real.exp_le_exp.mpr (by norm_num)
      nlinarith only [h1, hLhuge, Real.exp_pos (72 : ℝ), Real.exp_pos (300 : ℝ)]
    have hcore : Cerr * (x : ℝ) * Real.log q ^ 4 / (hbZ q η : ℝ) * (Real.exp 72 * Real.log q ^ 4)
        ≤ T * (Cerr * Real.exp 300 * SB) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hZpos]
      have hkey : Real.exp 72 * Real.log q ^ 8 * 14 ≤ Real.exp 300 * SB * Real.log q ^ 10 := by
        have h1 : Real.exp 300 * SB * Real.log q ^ 10 ≥ Real.exp 300 * Real.log q ^ 9 := by
          nlinarith only [hSBL10, Real.exp_pos (300 : ℝ)]
        have h2 : Real.exp 72 * Real.log q ^ 8 * 14 ≤ Real.exp 300 * Real.log q ^ 9 := by
          have h3 : Real.log q ^ 9 = Real.log q ^ 8 * Real.log q := by ring
          nlinarith only [he72', h3, pow_nonneg hL.le 8, Real.exp_pos (72 : ℝ)]
        linarith only [h1, h2]
      have hT' : (x : ℝ) / 14 ≤ T := hT14
      have hCx : (0 : ℝ) ≤ Cerr * (x : ℝ) / 14 := by positivity
      have hA : Cerr * (x : ℝ) * Real.log q ^ 4 * (Real.exp 72 * Real.log q ^ 4)
          = (Cerr * (x : ℝ) / 14) * (14 * Real.exp 72 * Real.log q ^ 8) := by ring
      have hB : (Cerr * (x : ℝ) / 14) * (14 * Real.exp 72 * Real.log q ^ 8)
          ≤ (Cerr * (x : ℝ) / 14) * (Real.exp 300 * SB * Real.log q ^ 10) :=
        mul_le_mul_of_nonneg_left (by linarith only [hkey]) hCx
      have hC2 : (Cerr * (x : ℝ) / 14) * (Real.exp 300 * SB * Real.log q ^ 10)
          ≤ (Cerr * (x : ℝ) / 14) * (Real.exp 300 * SB * (hbZ q η : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCx
        exact mul_le_mul_of_nonneg_left hz10 (by positivity)
      have hD2 : (Cerr * (x : ℝ) / 14) * (Real.exp 300 * SB * (hbZ q η : ℝ))
          ≤ T * (Cerr * Real.exp 300 * SB) * (hbZ q η : ℝ) := by
        have h1 : Cerr * (x : ℝ) / 14 ≤ Cerr * T := by
          nlinarith only [hT', hCerr0, hxpos]
        have h2 : (0 : ℝ) ≤ Real.exp 300 * SB * (hbZ q η : ℝ) := by positivity
        nlinarith only [h1, h2]
      linarith only [hA, hB, hC2, hD2]
    linarith only [hstep, hcore]
  -- the master constant's four coefficient rows
  have he10 : (11 : ℝ) ≤ Real.exp 10 := by
    have := Real.add_one_le_exp (10 : ℝ); linarith only [this]
  have he300b : (10 ^ 12 : ℝ) ≤ Real.exp 300 := by
    have h1 : Real.exp 300 = (Real.exp 10) ^ 30 := by
      rw [show (300 : ℝ) = ((30 : ℕ) : ℝ) * 10 by norm_num, Real.exp_nat_mul]
    have h2 : (11 : ℝ) ^ 30 ≤ (Real.exp 10) ^ 30 := pow_le_pow_left₀ (by norm_num) he10 30
    rw [h1]; norm_num at h2 ⊢; linarith only [h2]
  have he40 : (14641 : ℝ) ≤ Real.exp 40 := by
    have h1 : Real.exp 40 = (Real.exp 10) ^ 4 := by
      rw [show (40 : ℝ) = ((4 : ℕ) : ℝ) * 10 by norm_num, Real.exp_nat_mul]
    have h2 : (11 : ℝ) ^ 4 ≤ (Real.exp 10) ^ 4 := pow_le_pow_left₀ (by norm_num) he10 4
    rw [h1]; norm_num at h2 ⊢; linarith only [h2]
  have he260 : Real.exp 260 * Real.exp 40 = Real.exp 300 := by rw [← Real.exp_add]; norm_num
  have he260p : (0 : ℝ) < Real.exp 260 := Real.exp_pos _
  have hKey : 9 * Real.exp 260 * ec ≤ Real.exp 300 * (1 + n9Cs) := by
    rw [← he260, hecdef]
    have h1 : (0 : ℝ) ≤ (Real.exp 40 - 14641) * (1 + n9Cs) := by
      nlinarith only [he40, hn9Cs]
    nlinarith only [h1, he260p, hn9Cs]
  have hK3big : Real.exp 300 * (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr)
      ≥ Real.exp 300 * (1 + n9Cs) + Real.exp 300 * (1 + n9Cs) * n8C6 CA CA' CC
        + Real.exp 300 * Cerr := by
    have h1 : (0 : ℝ) < Real.exp 300 * (1 + n9Cs) := by
      have := Real.exp_pos (300 : ℝ); nlinarith only [this, hn9Cs]
    have h2 : (0 : ℝ) ≤ Cerr * n9Cs := mul_nonneg hCerr0 (by linarith only [hn9Cs])
    have h3 : (0 : ℝ) < Real.exp 300 := Real.exp_pos _
    nlinarith only [h1, h2, h3]
  have hK3A : (9 + 9 * n8C6 CA CA' CC) * (Real.exp 260 * ec) ≤ n9K3 Cerr CA CA' CC := by
    simp only [n9K3]
    have h1 : 9 * n8C6 CA CA' CC * (Real.exp 260 * ec)
        ≤ Real.exp 300 * (1 + n9Cs) * n8C6 CA CA' CC := by
      nlinarith only [hKey, hn8C60]
    nlinarith only [hKey, h1, hK3big, hCerr0, Real.exp_pos (300 : ℝ)]
  have hK3C : 18 * ec + 9 * n8C6 CA CA' CC ≤ n9K3 Cerr CA CA' CC := by
    simp only [n9K3]
    have he260' : (2 : ℝ) ≤ Real.exp 260 := by
      have := Real.add_one_le_exp (260 : ℝ); linarith only [this]
    have h1 : (18 : ℝ) * ec ≤ Real.exp 300 * (1 + n9Cs) := by
      nlinarith only [hKey, he260', hec0]
    have hbase : (9 : ℝ) ≤ Real.exp 300 * (1 + n9Cs) := by
      nlinarith only [he300b, hn9Cs]
    have h2 : (9 : ℝ) * n8C6 CA CA' CC ≤ Real.exp 300 * (1 + n9Cs) * n8C6 CA CA' CC := by
      nlinarith only [hbase, hn8C60]
    have hp1 : (0 : ℝ) ≤ Real.exp 300 * (1 + n9Cs) := by
      have := Real.exp_pos (300 : ℝ); nlinarith only [this, hn9Cs]
    have hp3 : (0 : ℝ) ≤ Real.exp 300 * Cerr := mul_nonneg (Real.exp_pos _).le hCerr0
    linarith only [h1, h2, hK3big, hp3, hp1]
  have hK3D : 14 * Real.exp 31 ≤ n9K3 Cerr CA CA' CC := by
    simp only [n9K3]
    have h1 : Real.exp 31 ≤ Real.exp 300 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : (14 : ℝ) * Real.exp 300 ≤ Real.exp 300 * (1 + n9Cs) := by
      nlinarith only [hn9Cs, Real.exp_pos (300 : ℝ)]
    have hp1 : (0 : ℝ) ≤ Real.exp 300 * (1 + n9Cs) := by
      have := Real.exp_pos (300 : ℝ); nlinarith only [this, hn9Cs]
    have hp2 : (0 : ℝ) ≤ Real.exp 300 * (1 + n9Cs) * n8C6 CA CA' CC := mul_nonneg hp1 hn8C60
    have hp3 : (0 : ℝ) ≤ Real.exp 300 * Cerr := mul_nonneg (Real.exp_pos _).le hCerr0
    linarith only [h1, h2, hK3big, hp2, hp3]
  have hK3E : Cerr * Real.exp 300 ≤ n9K3 Cerr CA CA' CC := by
    simp only [n9K3]
    have hp1 : (0 : ℝ) ≤ Real.exp 300 * (1 + n9Cs) := by
      have := Real.exp_pos (300 : ℝ); nlinarith only [this, hn9Cs]
    have hp2 : (0 : ℝ) ≤ Real.exp 300 * (1 + n9Cs) * n8C6 CA CA' CC := mul_nonneg hp1 hn8C60
    linarith only [hK3big, hp1, hp2]
  -- the sieve/`W` positivity and the two brackets
  have hWpos : 0 < W (hbDataN8 χ hR.sq hz2 x).sieve := W_pos _
  have hKW0 : 0 ≤ hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve :=
    mul_nonneg hκ hWpos.le
  have hδ1 : 0 ≤ 1 + δ := by
    have h0 : (0 : ℝ) ≤ hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve
        * (η * Real.log q) ^ 2 := mul_nonneg hKW0 hP2pos.le
    rw [hKWP2] at h0
    nlinarith only [h0, hTpos]
  have hSCP2 : SC * (η * Real.log q) ^ 2 = η * Real.log q ^ 2 := by
    rw [hSCdef]; field_simp
  have hSC1 : SC ≤ 1 := by
    rw [hSCdef, div_le_one hηpos]; linarith only [hηbig2]
  have hn8SC : n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q
      ≤ 3 * (n8C6 CA CA' CC) * SC * (η * Real.log q) ^ 2 := by
    have h2 : n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q
        ≤ n8C6 CA CA' CC * (3 * (η * Real.log q)) * Real.log q := by
      have h := mul_le_mul_of_nonneg_left hB3 hn8C60
      nlinarith only [h, hL]
    have h4 : 3 * (n8C6 CA CA' CC) * SC * (η * Real.log q) ^ 2
        = n8C6 CA CA' CC * (3 * (η * Real.log q)) * Real.log q := by
      rw [show 3 * (n8C6 CA CA' CC) * SC * (η * Real.log q) ^ 2
        = 3 * (n8C6 CA CA' CC) * (SC * (η * Real.log q) ^ 2) by ring, hSCP2]
      ring
    linarith only [h2, h4]
  have hbrkU : hbLL χ ^ 2 + n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q
      ≤ (1 + (3 * u + 3 * (n8C6 CA CA' CC) * SC)) * (η * Real.log q) ^ 2 := by
    nlinarith only [hLLsq_hi, hn8SC, hSCP2]
  have hbrkL : (1 - (2 * u + FC * E + 6 * (n8C6 CA CA' CC) * SC)) * (η * Real.log q) ^ 2
      ≤ hbLL χ ^ 2 * (1 - FC * E)
        - n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q * (1 + FC * E) := by
    have hFE0 : (0 : ℝ) ≤ FC * E := by positivity
    have h1 : (1 - 2 * u) * (η * Real.log q) ^ 2 * (1 - FC * E) ≤ hbLL χ ^ 2 * (1 - FC * E) :=
      mul_le_mul_of_nonneg_right hLLsq_lo (by linarith only [hFCE1])
    have h2 : n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q * (1 + FC * E)
        ≤ 3 * (n8C6 CA CA' CC) * SC * (η * Real.log q) ^ 2 * 2 := by
      have h3 : (0 : ℝ) ≤ n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q := by
        have := abs_nonneg (hbLL χ); positivity
      nlinarith only [hn8SC, hFCE1, hFE0, h3]
    have h5 : (0 : ℝ) ≤ u * (FC * E) * (η * Real.log q) ^ 2 :=
      mul_nonneg (mul_nonneg hu0 hFE0) hP2pos.le
    nlinarith only [h1, h2, h5, hFE0, hP2pos, hFCE1]
  -- the ledger, in `T`-units
  rw [← hFCdef, ← hEdef] at hup hlo
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 1 / 4 * FC * E := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 3 * u + 3 * (n8C6 CA CA' CC) * SC := ⟨_, rfl⟩
  obtain ⟨cl, hcldef⟩ : ∃ cl : ℝ, cl = 2 * u + FC * E + 6 * (n8C6 CA CA' CC) * SC := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = n9K3 Cerr CA CA' CC * (SA + SB + SC + SD) := ⟨_, rfl⟩
  rw [← hadef] at hup
  have hd0 : (0 : ℝ) ≤ |δ| := abs_nonneg δ
  have hdub : δ ≤ |δ| := le_abs_self δ
  have hdlb : -|δ| ≤ δ := neg_abs_le δ
  have hSCn : (0 : ℝ) ≤ SC := hSC0.le
  have hecSC : (0 : ℝ) ≤ ec * SC := mul_nonneg hec0.le hSCn
  have hn8SCn : (0 : ℝ) ≤ n8C6 CA CA' CC * SC := mul_nonneg hn8C60 hSCn
  have ha0 : (0 : ℝ) ≤ a := by rw [hadef]; positivity
  have ha1 : a ≤ 1 / 4 := by rw [hadef]; nlinarith only [hFCE1, hFC0, hE0]
  have hb0 : (0 : ℝ) ≤ b := by
    rw [hbdef]; have := hSC0.le; positivity
  have hcl0 : (0 : ℝ) ≤ cl := by
    rw [hcldef]; have := hSC0.le; have := (mul_pos hFC0 hE0).le; positivity
  have hK3AB : (9 + 9 * n8C6 CA CA' CC) * (Real.exp 260 * ec) + Cerr * Real.exp 300
      ≤ n9K3 Cerr CA CA' CC := by
    simp only [n9K3]
    have h1 : 9 * n8C6 CA CA' CC * (Real.exp 260 * ec)
        ≤ Real.exp 300 * (1 + n9Cs) * n8C6 CA CA' CC := by
      nlinarith only [hKey, hn8C60]
    nlinarith only [hKey, h1, hK3big, hCerr0, Real.exp_pos (300 : ℝ)]
  have e1 : (9 + 9 * n8C6 CA CA' CC) * (Real.exp 260 * ec) * SA
      ≤ n9K3 Cerr CA CA' CC * SA := mul_le_mul_of_nonneg_right hK3A hSA0
  have e2 : ((9 + 9 * n8C6 CA CA' CC) * (Real.exp 260 * ec) + Cerr * Real.exp 300) * SB
      ≤ n9K3 Cerr CA CA' CC * SB := mul_le_mul_of_nonneg_right hK3AB hSB0.le
  have e3 : (18 * ec + 9 * n8C6 CA CA' CC) * SC ≤ n9K3 Cerr CA CA' CC * SC :=
    mul_le_mul_of_nonneg_right hK3C hSC0.le
  have e4 : (14 * Real.exp 31) * SD ≤ n9K3 Cerr CA CA' CC * SD :=
    mul_le_mul_of_nonneg_right hK3D hSD0.le
  have hδec2 : |δ| ≤ Real.exp 260 * ec * (SA + SB) := by
    have hn9K2ec : n9K2 = Real.exp 260 * ec := by rw [n9K2, hecdef]
    rw [← hn9K2ec]; exact hδsmall
  have hbsmall : b ≤ 1 + 3 * n8C6 CA CA' CC := by
    rw [hbdef]
    nlinarith only [husmall, hu0, hSC1, hn8C60, hSC0]
  have hclsmall : cl ≤ 2 + 6 * n8C6 CA CA' CC := by
    rw [hcldef]
    nlinarith only [husmall, hu0, hSC1, hn8C60, hSC0, hFCE1]
  have ht1 : 2 * a ≤ 14 * Real.exp 31 * SD := by
    rw [hadef]; nlinarith only [hFCE, hSD0, Real.exp_pos (31 : ℝ)]
  have ht2 : 2 * b ≤ (18 * ec + 9 * n8C6 CA CA' CC) * SC := by
    rw [hbdef]; nlinarith only [huSC, hn8SCn, hecSC]
  have ht2' : cl ≤ (18 * ec + 9 * n8C6 CA CA' CC) * SC + 14 * Real.exp 31 * SD := by
    rw [hcldef]; nlinarith only [huSC, hn8SCn, hecSC, hFCE]
  have ht3 : 2 * |δ| + 2 * b * |δ|
      ≤ (9 + 9 * n8C6 CA CA' CC) * (Real.exp 260 * ec) * (SA + SB) := by
    have h1 : 2 * |δ| + 2 * b * |δ| ≤ (4 + 6 * n8C6 CA CA' CC) * |δ| := by
      nlinarith only [hbsmall, hd0, hn8C60]
    have h2 : (4 + 6 * n8C6 CA CA' CC) * |δ|
        ≤ (4 + 6 * n8C6 CA CA' CC) * (Real.exp 260 * ec * (SA + SB)) := by
      nlinarith only [hδec2, hn8C60]
    have h3 : (0 : ℝ) ≤ Real.exp 260 * ec * (SA + SB) := by
      have := hSB0.le; positivity
    nlinarith only [h1, h2, h3, hn8C60]
  have ht4 : (3 + 6 * n8C6 CA CA' CC) * |δ|
      ≤ (9 + 9 * n8C6 CA CA' CC) * (Real.exp 260 * ec) * (SA + SB) := by
    have h2 : (3 + 6 * n8C6 CA CA' CC) * |δ|
        ≤ (3 + 6 * n8C6 CA CA' CC) * (Real.exp 260 * ec * (SA + SB)) := by
      nlinarith only [hδec2, hn8C60]
    have h3 : (0 : ℝ) ≤ Real.exp 260 * ec * (SA + SB) := by
      have := hSB0.le; positivity
    nlinarith only [h2, h3, hn8C60]
  have hMbound : 2 * a + 2 * b + 2 * |δ| + 2 * b * |δ| + Cerr * Real.exp 300 * SB ≤ M := by
    rw [hMdef]; linarith only [ht1, ht2, ht3, e1, e2, e3, e4]
  have hMbound2 : cl + (3 + 6 * n8C6 CA CA' CC) * |δ| + Cerr * Real.exp 300 * SB ≤ M := by
    rw [hMdef]; linarith only [ht2', ht4, e1, e2, e3, e4]
  -- the two sides
  have hupperT : S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x) ≤ (1 + M) * T := by
    have hs1 : hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve * (1 + a)
          * (hbLL χ ^ 2 + n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q)
        ≤ hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve * (1 + a)
          * ((1 + b) * (η * Real.log q) ^ 2) := by
      refine mul_le_mul_of_nonneg_left (by rw [hbdef]; exact hbrkU) ?_
      exact mul_nonneg hKW0 (by linarith only [ha0])
    have hs2 : hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve * (1 + a)
          * ((1 + b) * (η * Real.log q) ^ 2) = (1 + a) * (1 + b) * ((1 + δ) * T) := by
      rw [← hKWP2]; ring
    have halg : (1 + a) * (1 + b) * (1 + δ)
        ≤ 1 + 2 * a + 2 * b + 2 * |δ| + 2 * b * |δ| := by
      have s1 : (1 + a) * (1 + b) ≤ 1 + 2 * a + 2 * b := by nlinarith only [ha0, ha1, hb0]
      have s2 : (1 + a) * (1 + b) * (1 + δ) ≤ (1 + 2 * a + 2 * b) * (1 + δ) :=
        mul_le_mul_of_nonneg_right s1 hδ1
      have s3 : (1 + 2 * a + 2 * b) * (1 + δ) ≤ (1 + 2 * a + 2 * b) * (1 + |δ|) :=
        mul_le_mul_of_nonneg_left (by linarith only [hdub]) (by linarith only [ha0, hb0])
      have s5 : 2 * a * |δ| ≤ |δ| := by nlinarith only [ha1, ha0, hd0]
      nlinarith only [s2, s3, s5]
    have hs3 : (1 + a) * (1 + b) * ((1 + δ) * T) ≤ (1 + 2 * a + 2 * b + 2 * |δ|
        + 2 * b * |δ|) * T := by
      have h1 : (1 + a) * (1 + b) * ((1 + δ) * T) = ((1 + a) * (1 + b) * (1 + δ)) * T := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right halg hTpos.le
    have hs4 : (1 + 2 * a + 2 * b + 2 * |δ| + 2 * b * |δ|) * T + T * (Cerr * Real.exp 300 * SB)
        ≤ (1 + M) * T := by nlinarith only [hMbound, hTpos]
    linarith only [hup, hs1, hs2, hs3, hs4, hErr]
  have hlowerT : (1 - M) * T ≤ S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x) := by
    have hs1 : hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve
          * ((1 - cl) * (η * Real.log q) ^ 2)
        ≤ hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve
          * (hbLL χ ^ 2 * (1 - FC * E)
            - n8C6 CA CA' CC * (Real.log q + |hbLL χ|) * Real.log q * (1 + FC * E)) :=
      mul_le_mul_of_nonneg_left (by rw [hcldef]; exact hbrkL) hKW0
    have hs2 : hbKappaN9 χ x (hbZ q η) * W (hbDataN8 χ hR.sq hz2 x).sieve
          * ((1 - cl) * (η * Real.log q) ^ 2) = (1 - cl) * ((1 + δ) * T) := by
      rw [← hKWP2]; ring
    have halg2 : 1 - cl - (3 + 6 * n8C6 CA CA' CC) * |δ| ≤ (1 - cl) * (1 + δ) := by
      have s1 : (1 - cl) * (1 + δ) = 1 + δ - cl * (1 + δ) := by ring
      have s2 : cl * (1 + δ) ≤ cl * (1 + |δ|) :=
        mul_le_mul_of_nonneg_left (by linarith only [hdub]) hcl0
      have s3 : cl * (1 + |δ|) ≤ cl + (2 + 6 * n8C6 CA CA' CC) * |δ| := by
        nlinarith only [hclsmall, hd0, hcl0, hn8C60]
      linarith only [s1, s2, s3, hdlb]
    have hs3 : (1 - cl - (3 + 6 * n8C6 CA CA' CC) * |δ|) * T ≤ (1 - cl) * ((1 + δ) * T) := by
      have h1 : (1 - cl) * ((1 + δ) * T) = ((1 - cl) * (1 + δ)) * T := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right halg2 hTpos.le
    have hs4 : (1 - M) * T
        ≤ (1 - cl - (3 + 6 * n8C6 CA CA' CC) * |δ|) * T - T * (Cerr * Real.exp 300 * SB) := by
      nlinarith only [hMbound2, hTpos]
    linarith only [hlo, hs1, hs2, hs3, hs4, hErr]
  -- the relative form
  refine ⟨S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x) / T - 1, ?_, ?_⟩
  · rw [← hTdef]; field_simp; ring
  · have hid : S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x) / T - 1
        = (S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x) - T) / T := by field_simp
    rw [hid, abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos, abs_le]
    rw [hSAdef, hSBdef, hSCdef, hSDdef] at hMdef
    constructor
    · rw [← hMdef]; linarith only [hlowerT]
    · rw [← hMdef]; linarith only [hupperT]

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
  obtain ⟨hqR, hL, hβpos, hηL, hηpos, hηbig, hβhalf⟩ := n9_regime_facts hR
  obtain ⟨-, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  have hq2 : 2 ≤ q := by exact_mod_cast hqR
  -- `ℓ′` and its log
  have hE0 : Real.exp (3 * 10 ^ 6) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    simp only [n9E0]; linarith
  have hEll : Real.exp (3 * 10 ^ 6) ≤ n9Ell q η := le_trans hE0 hR.ellBig
  have hEllpos : 0 < n9Ell q η := lt_of_lt_of_le (Real.exp_pos _) hEll
  have hPlog : (3 : ℝ) * 10 ^ 6 ≤ Real.log (n9Ell q η) := by
    have h := Real.log_le_log (Real.exp_pos (3 * 10 ^ 6 : ℝ)) hEll
    rwa [Real.log_exp] at h
  have hPpos : 0 < Real.log (n9Ell q η) := by linarith only [hPlog]
  have hPne : Real.log (n9Ell q η) ≠ 0 := ne_of_gt hPpos
  have hLbig : 100 * Real.exp (3 * 10 ^ 6) ≤ Real.log q := by linarith only [hEll, hPsmall]
  have hEllleL : n9Ell q η ≤ Real.log q := by linarith only [hPsmall, hL]
  have hPleL : Real.log (n9Ell q η) ≤ Real.log (Real.log q) :=
    Real.log_le_log hEllpos hEllleL
  have hULog : (3 * 10 ^ 6 : ℝ) ≤ Real.log (Real.log q) := by
    have hexppos : (0 : ℝ) < Real.exp (3 * 10 ^ 6 : ℝ) := Real.exp_pos _
    have h := Real.log_le_log hexppos
      (by linarith only [hLbig, hexppos] : Real.exp (3 * 10 ^ 6 : ℝ) ≤ Real.log q)
    rwa [Real.log_exp] at h
  -- `t^4 ≤ e^t` for `t ≥ 3·10⁶`, used at `t = log ℓ′` and `t = log L`
  have hsqexp : ∀ t : ℝ, (3 * 10 ^ 6 : ℝ) ≤ t → t ^ 4 ≤ Real.exp t := by
    intro t ht
    have h1 : t / 5 + 1 ≤ Real.exp (t / 5) := Real.add_one_le_exp _
    have h2 : Real.exp (t / 5) ^ 5 = Real.exp t := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 : (t / 5) ^ 5 ≤ Real.exp (t / 5) ^ 5 :=
      pow_le_pow_left₀ (by linarith only [ht]) (by linarith only [h1]) 5
    rw [h2] at h3
    have h5 : (t / 5) ^ 5 = t ^ 4 * t / 3125 := by ring
    have h4 : t ^ 4 * 3125 ≤ t ^ 4 * t :=
      mul_le_mul_of_nonneg_left (by linarith only [ht]) (by positivity)
    rw [h5] at h3
    linarith only [h3, h4]
  -- SHAPE (i): `log ℓ′/√ℓ′ ≤ 1/log ℓ′`
  have hP4 : Real.log (n9Ell q η) ^ 4 ≤ n9Ell q η := by
    have h := hsqexp (Real.log (n9Ell q η)) hPlog
    rwa [Real.exp_log hEllpos] at h
  have hsqrtpos : 0 < Real.sqrt (n9Ell q η) := Real.sqrt_pos.mpr hEllpos
  have hsqrtge : Real.log (n9Ell q η) ^ 2 ≤ Real.sqrt (n9Ell q η) := by
    have hstep : (Real.log (n9Ell q η) ^ 2) ^ 2 ≤ n9Ell q η := by
      rw [show (Real.log (n9Ell q η) ^ 2) ^ 2 = Real.log (n9Ell q η) ^ 4 by ring]
      exact hP4
    have h := Real.sqrt_le_sqrt hstep
    rwa [Real.sqrt_sq (by positivity)] at h
  have hshapeA : Real.log (n9Ell q η) / Real.sqrt (n9Ell q η)
      ≤ 1 / Real.log (n9Ell q η) := by
    rw [div_le_div_iff₀ hsqrtpos hPpos]
    nlinarith only [hsqrtge]
  -- SHAPE (ii): `1/√L ≤ 1/log ℓ′`
  have hL4pow : Real.log (Real.log q) ^ 4 ≤ Real.log q := by
    have h := hsqexp (Real.log (Real.log q)) hULog
    rwa [Real.exp_log hL] at h
  have hPsq : Real.log (n9Ell q η) ^ 2 ≤ Real.log q := by
    have h1 : Real.log (n9Ell q η) ^ 2 ≤ Real.log (Real.log q) ^ 2 := by
      nlinarith only [hPleL, hPpos]
    have h2 : Real.log (Real.log q) ^ 2 ≤ Real.log (Real.log q) ^ 4 := by
      have hu : (1 : ℝ) ≤ Real.log (Real.log q) := by linarith only [hULog]
      exact pow_le_pow_right₀ hu (by norm_num)
    linarith only [h1, h2, hL4pow]
  have hshapeB : 1 / Real.sqrt (Real.log q) ≤ 1 / Real.log (n9Ell q η) := by
    have hsq : Real.log (n9Ell q η) ≤ Real.sqrt (Real.log q) := by
      have h := Real.sqrt_le_sqrt hPsq
      rwa [Real.sqrt_sq hPpos.le] at h
    have hspos : 0 < Real.sqrt (Real.log q) := Real.sqrt_pos.mpr hL
    rw [div_le_div_iff₀ hspos hPpos]
    linarith only [hsq]
  -- SHAPE (iii): `1/η ≤ 1/log ℓ′`, through `ℓ′ ≤ log η` (the `−13·log log q` of `n9Ell`)
  have hEllLogη : n9Ell q η ≤ Real.log η := by
    have hL4q : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
      Real.log_le_log (by linarith only [hL, hqR]) (by linarith only [hqR])
    have hlogLle : Real.log (Real.log q) ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      Real.log_le_log hL (by linarith only [hL4q])
    have hXnn : 0 ≤ Real.log (Real.log (4 * (q : ℝ)) + 2) :=
      Real.log_nonneg (by linarith only [hWpos])
    have hdhCpos := dh_spec.1
    have hdhC1 := dh_spec.2.1
    have hinv : 0 ≤ Real.log (1 / dhC) :=
      Real.log_nonneg (by rw [le_div_iff₀ hdhCpos]; linarith)
    have hsplit : Real.log (η * Real.log q) = Real.log η + Real.log (Real.log q) :=
      Real.log_mul (ne_of_gt hηpos) (ne_of_gt hL)
    have hdk : dhK = 14 := rfl
    simp only [n9Ell, hdk, hsplit]
    linarith only [hlogLle, hXnn, hinv]
  have hshapeC : 1 / η ≤ 1 / Real.log (n9Ell q η) := by
    have h1 : Real.log (n9Ell q η) ≤ n9Ell q η := by
      have h := Real.log_le_sub_one_of_pos hEllpos; linarith only [h]
    have h2 : Real.log η ≤ η := by
      have h := Real.log_le_sub_one_of_pos hηpos; linarith only [h]
    rw [div_le_div_iff₀ hηpos hPpos]
    linarith only [h1, h2, hEllLogη]
  -- SHAPE (iv): the FL term, through `hbS ≥ log ℓ′/30300`
  have hz0 : hbZ0 q η = 1 / 10000 * Real.log (n9Ell q η) := by simp only [hbZ0, hbZ0A]
  have hz0pos : 0 < hbZ0 q η := by rw [hz0]; linarith only [hPpos]
  obtain ⟨hzlo, hzhi⟩ := hbZ_bounds q η hz0pos
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith only [hqR]
  have hrp : (q : ℝ) ^ (1 / hbZ0 q η) = Real.exp (Real.log q / hbZ0 q η) := by
    rw [Real.rpow_def_of_pos hqpos, mul_one_div]
  have hWpos2 : 0 < Real.log q / hbZ0 q η := div_pos hL hz0pos
  have hzge : Real.exp (Real.log q / hbZ0 q η) ≤ (hbZ q η : ℝ) := by rw [← hrp]; exact hzlo
  have hzpos : (0 : ℝ) < (hbZ q η : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hzge
  have hzhi' : (hbZ q η : ℝ) < Real.exp (Real.log q / hbZ0 q η) + 1 := by
    rw [← hrp]; exact hzhi
  have hzle : (hbZ q η : ℝ) ≤ Real.exp (Real.log q / hbZ0 q η + 1) := by
    have hE : (1 : ℝ) ≤ Real.exp (Real.log q / hbZ0 q η) := by
      have h := Real.add_one_le_exp (Real.log q / hbZ0 q η)
      linarith only [h, hWpos2]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ); linarith only [h]
    rw [Real.exp_add]
    nlinarith only [hzhi', hE, he1]
  have hlogzle : Real.log (hbZ q η : ℝ) ≤ Real.log q / hbZ0 q η + 1 := by
    have h := Real.log_le_log hzpos hzle
    rwa [Real.log_exp] at h
  have hlogzge : Real.log q / hbZ0 q η ≤ Real.log (hbZ q η : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hzge
    rwa [Real.log_exp] at h
  have hlogzpos : 0 < Real.log (hbZ q η : ℝ) := lt_of_lt_of_le hWpos2 hlogzge
  have hWP : (Real.log q / hbZ0 q η) * Real.log (n9Ell q η) = 10000 * Real.log q := by
    rw [hz0]; field_simp
  have hPleLq : Real.log (n9Ell q η) ≤ Real.log q := by
    have h := Real.log_le_sub_one_of_pos hL
    linarith only [hPleL, h]
  have hSlow : Real.log (n9Ell q η) / 30300 ≤ hbS q η := by
    rw [hbS, div_le_div_iff₀ (by norm_num) (by linarith only [hlogzpos])]
    have h2 : Real.log (n9Ell q η) * (3 * Real.log (hbZ q η : ℝ))
        ≤ Real.log (n9Ell q η) * (3 * (Real.log q / hbZ0 q η + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlogzle]) hPpos.le
    have h3 : Real.log (n9Ell q η) * (3 * (Real.log q / hbZ0 q η + 1))
        = 3 * ((Real.log q / hbZ0 q η) * Real.log (n9Ell q η))
          + 3 * Real.log (n9Ell q η) := by ring
    linarith only [h2, h3, hWP, hPleLq, hL]
  have hlog4ge : (1 : ℝ) ≤ Real.log 4 := by
    have he := Real.exp_one_lt_d9
    have h := Real.log_le_log (Real.exp_pos 1) (by linarith only [he] : Real.exp 1 ≤ (4 : ℝ))
    rwa [Real.log_exp] at h
  have hSpos : 0 < hbS q η := by linarith only [hSlow, hPpos]
  have hshapeD : Real.exp (-(Real.log 4) * hbS q η) ≤ 30300 / Real.log (n9Ell q η) := by
    have hexpo : Real.log (n9Ell q η) / 30300 ≤ Real.log 4 * hbS q η := by
      nlinarith only [hSlow, hlog4ge, hSpos]
    have hE := Real.exp_le_exp.mpr hexpo
    have hlow := Real.add_one_le_exp (Real.log (n9Ell q η) / 30300)
    have hge : Real.log (n9Ell q η) / 30300 ≤ Real.exp (Real.log 4 * hbS q η) := by
      linarith only [hE, hlow]
    have hpos : 0 < Real.exp (Real.log 4 * hbS q η) := Real.exp_pos _
    have hneg : Real.exp (-(Real.log 4) * hbS q η)
        = (Real.exp (Real.log 4 * hbS q η))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hneg, inv_eq_one_div, div_le_div_iff₀ hpos hPpos]
    linarith only [hge]
  -- the constants: N7's signs, `n9K3 ≥ e^{300}`, and `n9K = 2^40·10⁴·n9K3`
  have hzz : 2 ≤ hbZ q η := (hbZ_packet hR hx hx').1
  obtain ⟨C₀, A, A', hL5⟩ := hN7 q χ hR.sq hzz x
  have hCerr : 0 ≤ Cerr := hL5.Cerr_nonneg
  have hCA : 0 ≤ CA := hL5.CA_nonneg
  have hCA' : 0 ≤ CA' := hL5.CA'_nonneg
  have hCC : 0 ≤ CC := by
    rcases le_or_gt 0 CC with h | h
    · exact h
    · exfalso
      have hden : 0 < (Real.log q + |hbLL χ|) * Real.log q :=
        mul_pos (by linarith only [hL, abs_nonneg (hbLL χ)]) hL
      have hneg := mul_neg_of_neg_of_pos h hden
      have hab := hL5.C₀_le
      have habs : (0 : ℝ) ≤ |C₀| := abs_nonneg _
      nlinarith only [hab, habs, hneg]
  have hn8C6 : 0 ≤ n8C6 CA CA' CC := by
    have h1 : (0 : ℝ) ≤ 64 * CA' := by linarith only [hCA']
    have h2 : (0 : ℝ) ≤ (128 * CA) ^ 2 := sq_nonneg _
    simp only [n8C6]; linarith only [h1, h2, hCC]
  have hCsnn : (0 : ℝ) ≤ n9Cs := by
    have hA := invSqC_spec.1
    have hprod : (0 : ℝ) ≤ invSqC * (dhB ^ 2 + dhB) :=
      mul_nonneg hA.le (by rw [show dhB = 680 from rfl]; norm_num)
    simp only [n9Cs]; linarith only [hprod]
  have hK300 : Real.exp 300 ≤ n9K3 Cerr CA CA' CC := by
    have h1 : (1 : ℝ) ≤ 1 + n9Cs := by linarith only [hCsnn]
    have h2 : (1 : ℝ) ≤ 1 + n8C6 CA CA' CC + Cerr := by linarith only [hn8C6, hCerr]
    have h3 : (0 : ℝ) < Real.exp 300 := Real.exp_pos _
    have hab : (1 : ℝ) ≤ (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr) := by
      nlinarith only [h1, h2]
    simp only [n9K3]
    calc Real.exp 300 = Real.exp 300 * 1 := by ring
      _ ≤ Real.exp 300 * ((1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr)) :=
        mul_le_mul_of_nonneg_left hab h3.le
      _ = Real.exp 300 * (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr) := by ring
  have hK3pos : 0 < n9K3 Cerr CA CA' CC := by
    have h := Real.exp_pos (300 : ℝ); linarith only [h, hK300]
  have hn9Keq : n9K Cerr CA CA' CC = 2 ^ 40 * 10 ^ 4 * n9K3 Cerr CA CA' CC := by
    simp only [n9K, n9K3, hbZ0A]; ring
  -- the two inputs and the main term
  obtain ⟨δ₃, heq3, hδ3⟩ := hb_S3_at_hb_point hR hx hx' hN7
  have hL4err := hb_lemma4_at_hb_point hR hx hx'
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hq250 : (1 : ℝ) ≤ (q : ℝ) ^ 250 := one_le_pow₀ (by linarith only [hqR])
    linarith only [hx, hq250]
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hxpos
  set M : ℝ := (x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4 with hMdef
  have hMlow : (x : ℝ) / 14 ≤ M := by
    rw [hMdef, n9_calpha_four]
    nlinarith only [n9_singular_ge, hxpos]
  have hMpos : 0 < M := by linarith only [hMlow, hxpos]
  refine ⟨δ₃ + (S1 (Finset.Ioc x (2 * x))
      - S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)) / M, ?_, ?_⟩
  · have hMne : M ≠ 0 := ne_of_gt hMpos
    have hexpand : (1 + (δ₃ + (S1 (Finset.Ioc x (2 * x))
          - S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)) / M)) * M
        = (1 + δ₃) * M + (S1 (Finset.Ioc x (2 * x))
          - S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)) := by
      field_simp; ring
    rw [hexpand, ← heq3]; ring
  · have hEM : |(S1 (Finset.Ioc x (2 * x))
        - S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)) / M|
        ≤ (2 ^ 40 * (x : ℝ) / hbZ0 q η) / M := by
      rw [abs_div, abs_of_pos hMpos, div_le_div_iff₀ hMpos hMpos]
      exact mul_le_mul_of_nonneg_right hL4err hMpos.le
    have hnum : (0 : ℝ) ≤ 2 ^ 40 * (x : ℝ) / hbZ0 q η :=
      div_nonneg (by positivity) hz0pos.le
    have hterm : (2 ^ 40 * (x : ℝ) / hbZ0 q η) / M
        ≤ 14 * 2 ^ 40 * 10 ^ 4 / Real.log (n9Ell q η) := by
      have h1 : (2 ^ 40 * (x : ℝ) / hbZ0 q η) / M
          ≤ (2 ^ 40 * (x : ℝ) / hbZ0 q η) / ((x : ℝ) / 14) := by
        rw [div_le_div_iff₀ hMpos (by positivity)]
        exact mul_le_mul_of_nonneg_left hMlow hnum
      have h2 : (2 ^ 40 * (x : ℝ) / hbZ0 q η) / ((x : ℝ) / 14)
          = 14 * 2 ^ 40 * 10 ^ 4 / Real.log (n9Ell q η) := by
        rw [hz0]; field_simp; ring
      linarith only [h1, h2]
    have hshapes : Real.log (n9Ell q η) / Real.sqrt (n9Ell q η)
          + 1 / Real.sqrt (Real.log q) + 1 / η
          + Real.exp (-(Real.log 4) * hbS q η)
        ≤ 30303 / Real.log (n9Ell q η) := by
      have h : (1 : ℝ) / Real.log (n9Ell q η) + 1 / Real.log (n9Ell q η)
          + 1 / Real.log (n9Ell q η) + 30300 / Real.log (n9Ell q η)
          = 30303 / Real.log (n9Ell q η) := by ring
      linarith only [hshapeA, hshapeB, hshapeC, hshapeD, h]
    have hδ3' : |δ₃| ≤ n9K3 Cerr CA CA' CC * (30303 / Real.log (n9Ell q η)) :=
      le_trans hδ3 (mul_le_mul_of_nonneg_left hshapes hK3pos.le)
    have hfinal : n9K3 Cerr CA CA' CC * (30303 / Real.log (n9Ell q η))
        + 14 * 2 ^ 40 * 10 ^ 4 / Real.log (n9Ell q η)
        ≤ 2 ^ 40 * 10 ^ 4 * n9K3 Cerr CA CA' CC / Real.log (n9Ell q η) := by
      have hexp300 : (22801 : ℝ) ≤ Real.exp 300 := by
        have h1 : (151 : ℝ) ≤ Real.exp 150 := by
          have h := Real.add_one_le_exp (150 : ℝ); linarith only [h]
        have h2 : Real.exp 150 * Real.exp 150 = Real.exp 300 := by
          rw [← Real.exp_add]; norm_num
        nlinarith only [h1, h2]
      have hK : (22801 : ℝ) ≤ n9K3 Cerr CA CA' CC := by linarith only [hexp300, hK300]
      have hnum2 : n9K3 Cerr CA CA' CC * 30303 + 14 * 2 ^ 40 * 10 ^ 4
          ≤ 2 ^ 40 * 10 ^ 4 * n9K3 Cerr CA CA' CC := by linarith only [hK]
      rw [show n9K3 Cerr CA CA' CC * (30303 / Real.log (n9Ell q η))
          = n9K3 Cerr CA CA' CC * 30303 / Real.log (n9Ell q η) by ring, ← add_div,
        div_le_div_iff₀ hPpos hPpos]
      exact mul_le_mul_of_nonneg_right hnum2 hPpos.le
    rw [hn9Keq]
    calc |δ₃ + (S1 (Finset.Ioc x (2 * x))
            - S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)) / M|
        ≤ |δ₃| + |(S1 (Finset.Ioc x (2 * x))
            - S3 χ (hbZ q η) (l2cWindow χ (hbZ q η) x)) / M| := abs_add_le _ _
      _ ≤ n9K3 Cerr CA CA' CC * (30303 / Real.log (n9Ell q η))
            + 14 * 2 ^ 40 * 10 ^ 4 / Real.log (n9Ell q η) := by
          linarith only [hδ3', hEM, hterm]
      _ ≤ 2 ^ 40 * 10 ^ 4 * n9K3 Cerr CA CA' CC / Real.log (n9Ell q η) := hfinal

/-! ## §6 — THE DOOR AND THE CROWN FAMILY (N10 reduced, N11 closed, N12 parametrised) -/

/-- **The lower half of Theorem 1, as the door reads it.**  Class **A**, cap 60.
Consumer: `crown_handover`. -/
theorem hb_theorem1_lower [NeZero q] {χ : DirichletCharacter ℂ q} {β₀ η : ℝ}
    (hR : N9Regime q χ β₀ η) {x : ℕ} (hx : (q : ℝ) ^ 250 ≤ x) (hx' : (x : ℝ) ≤ (q : ℝ) ^ 500)
    {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC)
    (hK : 2 * n9K Cerr CA CA' CC ≤ Real.log (n9Ell q η)) :
    (x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4 / 2
      ≤ S1 (Finset.Ioc x (2 * x)) := by
  obtain ⟨δ, heq, hδ⟩ := hb_theorem1 hR hx hx' hN7
  obtain ⟨hqR, hLhuge, hPbig, hPsmall, hWpos, hW2L, hCR⟩ := n9_num_facts hR
  have hlogpos : 0 < Real.log (n9Ell q η) := Real.log_pos (by linarith only [hPbig])
  have hK2 : n9K Cerr CA CA' CC / Real.log (n9Ell q η) ≤ 1 / 2 := by
    rw [div_le_iff₀ hlogpos]
    linarith only [hK]
  have hδ2 : |δ| ≤ 1 / 2 := le_trans hδ hK2
  have hlow : (1 : ℝ) / 2 ≤ 1 + δ := by
    have h := (abs_le.mp hδ2).1
    linarith only [h]
  have hM : (0 : ℝ) ≤ (x : ℝ) * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4 := by
    have h1 := Salt.HardyLittlewood.twinSingularSeries_pos
    have h2 : hbCalpha 4 = 2 := n9_calpha_four
    rw [h2]
    positivity
  rw [heq]
  have hstep := mul_le_mul_of_nonneg_right hlow hM
  linarith only [hstep]

/-- **The fulcrum quality at POLYLOG strength `k`**: infinitely many real primitive `χ` with a
zero `ρ` inside `‖1 − ρ‖ ≤ 1/(C·(log q)^k)`.  At `k = 1` this is `FulcrumQualityMin C`
(`fulcrumQualityPoly_one_iff`).  The landed engine fires at `k = 30 = dhK + 16` (findings 2, 4). -/
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
`k = 30` (`dhK = 14` from the contract, `16` from the tail's crude count — finding 4).  **The
Captain's ruling (2026-09-04 12:39): the campaign's crown is the `k = 1` member — HB's exactly —
reached through Arm B (D–H re-proved at `k ≤ 1` AND a log-free near-1 density, the next design
block); this file lands `k = 30` as the INTERMEDIATE member.** -/
def HeathBrownDichotomyPoly (k : ℝ) : Prop :=
  TwinPrimeConjecture ∨ NoSiegelZerosPoly k

/-- Class **A**, cap 30: `Real.rpow_one`. -/
theorem fulcrumQualityPoly_one_iff (C : ℝ) : FulcrumQualityPoly C 1 ↔ FulcrumQualityMin C := by
  simp only [FulcrumQualityPoly, FulcrumQualityMin, Real.rpow_one]

/-- Class **A**, cap 30: `Real.rpow_one`. -/
theorem noSiegelZerosPoly_one_iff : NoSiegelZerosPoly 1 ↔ NoSiegelZeros := by
  simp only [NoSiegelZerosPoly, NoSiegelZeros, Real.rpow_one]

/-- **The frozen crown IS the `k = 1` member** — the sentence made a theorem (the verdict's K12
note).  Class **A**, cap 20: `or_congr Iff.rfl noSiegelZerosPoly_one_iff`.
Consumer: the crown ruling (Arm B's target). -/
theorem heathBrownDichotomyPoly_one_iff : HeathBrownDichotomyPoly 1 ↔ HeathBrownDichotomy := by
  simp only [HeathBrownDichotomyPoly, HeathBrownDichotomy]
  exact or_congr Iff.rfl noSiegelZerosPoly_one_iff

/-- **A non-trivial Dirichlet character has modulus `≥ 3`** (the verdict's A9): mod `1` and
mod `2` the only character is `1` (`(ZMod 2)ˣ` is trivial).  Class **A**, cap 30.
Consumer: `noSiegelZerosPoly_mono` (`log q ≥ 1`). -/
theorem three_le_of_ne_one [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : 3 ≤ q := by
  rcases Nat.lt_or_ge q 3 with hlt | hge
  swap
  · exact hge
  exfalso
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply hne
  refine MulChar.ext fun a => ?_
  have hu : (a : ZMod q) = 1 := by
    have h2 : q = 1 ∨ q = 2 := by omega
    rcases h2 with h | h <;> subst h <;> revert a <;> decide
  rw [hu]
  simp

/-- **The family is monotone in `k`**: `c/(log q)^{k′} ≤ c/(log q)^k` for `k ≤ k′` once
`log q ≥ 1`.  This is the theorem behind "`Poly 14` is weaker than the frozen crown" (with
`noSiegelZerosPoly_one_iff` at `k = 1`).  Class **A**, cap 40: `three_le_of_ne_one`,
`Real.rpow_le_rpow_of_exponent_le`, `div_le_div_of_nonneg_left`.
Consumer: the crown ruling. -/
theorem noSiegelZerosPoly_mono {k k' : ℝ} (hk : 1 ≤ k) (hkk' : k ≤ k')
    (h : NoSiegelZerosPoly k) : NoSiegelZerosPoly k' := by
  have _hk := hk
  obtain ⟨c, hc, hprop⟩ := h
  refine ⟨c, hc, ?_⟩
  intro q _ χ hq1 hprim hsq hne β hβ hβ1
  have h3 : (3 : ℕ) ≤ q := three_le_of_ne_one χ hne
  have h3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h3
  have he : Real.exp 1 ≤ (q : ℝ) := by
    have h9 := Real.exp_one_lt_d9
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log q := by
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hmono : Real.log q ^ k ≤ Real.log q ^ k' :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hkk'
  have hpk : (0 : ℝ) < Real.log q ^ k := Real.rpow_pos_of_pos (by linarith) k
  have hpk' : (0 : ℝ) < Real.log q ^ k' := Real.rpow_pos_of_pos (by linarith) k'
  have hdiv : c / Real.log q ^ k' ≤ c / Real.log q ^ k := by
    rw [div_le_div_iff₀ hpk' hpk]
    exact mul_le_mul_of_nonneg_left hmono hc.le
  have hmain := hprop q χ hq1 hprim hsq hne β hβ hβ1
  linarith

/-- **The `¬F` horn at strength `k`** — the mirror of `not_fulcrum_implies_noSiegelZeros`.
Class **B**, cap 300.  Red-first: `¬F` gives `Q` with every `q > Q` at quality worse than
`1/(C(log q)^k)`, i.e. `1 − β > 1/(C(log q)^k)`; for `q ≤ Q` finitely many characters, each with
finitely many real zeros below `1` (`boxZeros χ (1/2) 1 0` is a `Finset`, `L(1,χ) ≠ 0`), take the
minimum gap — the compactness gadget's own argument (`Salt/Fulcrum/Gadget.lean`) at `(log q)^k`
in place of `log q`.  Consumer: `fulcrum_dichotomy_poly`. -/
theorem not_fulcrumPoly_implies_noSiegelZerosPoly {C k : ℝ} (hC : 0 < C) (hk : 1 ≤ k)
    (hnF : ¬ FulcrumQualityPoly C k) : NoSiegelZerosPoly k := by
  have hnF' : ∃ Q : ℕ, ¬ ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      Q < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
      DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 : ℂ) - ρ‖ * (C * Real.log q ^ k) ≤ 1 := by
    by_contra hcon
    exact hnF fun Q => not_not.mp fun h => hcon ⟨Q, h⟩
  obtain ⟨Q, hQ0⟩ := hnF'
  obtain ⟨c₀, hc₀, hiso⟩ := Salt.Fulcrum.siegel_zeros_isolated_below Q
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hm : (0 : ℝ) < Real.log 2 ^ k := Real.rpow_pos_of_pos hl2 k
  refine ⟨min (c₀ * Real.log 2 ^ k) (1 / C), lt_min (mul_pos hc₀ hm) (by positivity), ?_⟩
  intro q _ χ hq1 hprim hsq hne β hβ hβ1
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hlq : (0 : ℝ) < Real.log q := Real.log_pos (by linarith)
  have hlq2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hpk : (0 : ℝ) < Real.log q ^ k := Real.rpow_pos_of_pos hlq k
  have hmk : Real.log 2 ^ k ≤ Real.log q ^ k :=
    Real.rpow_le_rpow hl2.le hlq2 (by linarith)
  rcases le_or_gt q Q with hle | hgt
  · have hb := hiso q χ hle hprim hsq hne β hβ hβ1
    have hcle : min (c₀ * Real.log 2 ^ k) (1 / C) ≤ c₀ * Real.log 2 ^ k := min_le_left _ _
    have hstep : min (c₀ * Real.log 2 ^ k) (1 / C) / Real.log q ^ k ≤ c₀ := by
      rw [div_le_iff₀ hpk]
      have hh : c₀ * Real.log 2 ^ k ≤ c₀ * Real.log q ^ k :=
        mul_le_mul_of_nonneg_left hmk hc₀.le
      linarith
    linarith
  · have hkey : 1 < ‖(1 : ℂ) - (β : ℂ)‖ * (C * Real.log q ^ k) := by
      rcases le_or_gt (‖(1 : ℂ) - (β : ℂ)‖ * (C * Real.log q ^ k)) 1 with hcon | hgt2
      · exact absurd ⟨q, ‹NeZero q›, χ, (β : ℂ), hgt, hprim, hsq, hne, hβ, hcon⟩ hQ0
      · exact hgt2
    have hnorm : ‖(1 : ℂ) - (β : ℂ)‖ = 1 - β := by
      rw [show (1 : ℂ) - (β : ℂ) = ((1 - β : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hnorm] at hkey
    have hcle : min (c₀ * Real.log 2 ^ k) (1 / C) ≤ 1 / C := min_le_right _ _
    have hfin : min (c₀ * Real.log 2 ^ k) (1 / C) / Real.log q ^ k ≤ 1 - β := by
      rw [div_le_iff₀ hpk]
      have h3 : 1 / C ≤ (1 - β) * Real.log q ^ k := by
        rw [div_le_iff₀ hC]
        have heq : (1 - β) * Real.log q ^ k * C = (1 - β) * (C * Real.log q ^ k) := by ring
        rw [heq]
        linarith only [hkey]
      linarith only [hcle, h3]
    linarith

/-- **THE DICHOTOMY AT STRENGTH `k`.**  Class **A**, cap 30 (`by_cases`, as `fulcrum_dichotomy`).
Consumer: `heathBrownDichotomyPoly_of_N7`. -/
theorem fulcrum_dichotomy_poly {C k : ℝ} (hC : 0 < C) (hk : 1 ≤ k)
    (hEngine : FulcrumQualityPoly C k → TwinPrimeConjecture) :
    HeathBrownDichotomyPoly k := by
  by_cases hF : FulcrumQualityPoly C k
  · exact Or.inl (hEngine hF)
  · exact Or.inr (not_fulcrumPoly_implies_noSiegelZerosPoly hC hk hF)

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
  classical
  have _hχ := hχ
  have _hsq := hsq
  have _hlo := hlo
  have hmemZ : ∀ b : ℝ, DirichletCharacter.LFunction χ (b : ℂ) = 0 → β ≤ b → b ≤ 1 →
      (b : ℂ) ∈ Salt.SW.boxZeros χ β 1 0 := by
    intro b hb hlo' hhi'
    rw [Salt.SW.mem_boxZeros hne]
    exact ⟨hb, by simpa using hlo', by simpa using hhi', by simp⟩
  set S : Finset ℝ := (Salt.SW.boxZeros χ β 1 0).image Complex.re with hSdef
  have hβS : β ∈ S := Finset.mem_image.mpr ⟨(β : ℂ), hmemZ β hβ le_rfl hhi.le, by simp⟩
  have hSne : S.Nonempty := ⟨β, hβS⟩
  obtain ⟨ρ, hρmem, hρre⟩ := Finset.mem_image.mp (S.max'_mem hSne)
  rw [Salt.SW.mem_boxZeros hne] at hρmem
  obtain ⟨hz, hlo2, hhi2, him2⟩ := hρmem
  have him0 : ρ.im = 0 := abs_eq_zero.mp (le_antisymm him2 (abs_nonneg _))
  have hcoe : ((ρ.re : ℝ) : ℂ) = ρ := by apply Complex.ext <;> simp [him0]
  have hzero : DirichletCharacter.LFunction χ ((S.max' hSne : ℝ) : ℂ) = 0 := by
    rw [← hρre, hcoe]; exact hz
  have hge : β ≤ S.max' hSne := S.le_max' β hβS
  have hle1 : S.max' hSne ≤ 1 := by rw [← hρre]; exact hhi2
  have hlt : S.max' hSne < 1 := by
    rcases lt_or_eq_of_le hle1 with h | h
    · exact h
    · exfalso
      rw [h] at hzero
      exact (DirichletCharacter.LFunction_apply_one_ne_zero hne) (by simpa using hzero)
  refine ⟨S.max' hSne, hzero, hge, hlt, ?_⟩
  intro b' hb' hb'1
  rcases le_or_gt b' β with h | h
  · linarith
  · exact S.le_max' b' (Finset.mem_image.mpr ⟨(b' : ℂ), hmemZ b' hb' h.le hb'1.le, by simp⟩)

/-- **The crown's quality constant — HB's `C⁽¹⁾ = exp exp{2A/(𝔖C(α))}` (p.223), in this file's
currency**: `1 − β₀ ≤ 1/(n9Cq·(log q)^{30})` puts `ℓ′ ≥ n9E0 + e^{2·n9K} + 1 + 16·log L` (so
`ellBig`, `ellL` and `hK` hold): `ηL = 1/(1−β₀) ≥ C·L^{30}` gives `log(ηL) ≥ log C + 30·log L`,
and `14·log(log 4q + 2) ≤ 14·log L + 8.6` at `L ≥ 4`, so `ℓ′ ≥ log C − log(1/dhC) − 8.6 + 16·log L`;
the `/dhC` here cancels the `−log(1/dhC)` exactly, and `16·log log(4q) ≤ 16·log L + 22/L`
(the verdict's U1 gave `14`; finding 4's `ellL` adds `16`). -/
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
the quality at `k = 30` (`n9Cq`'s docstring: `ellBig` and `ellL` both); `x := q^250`;
`hb_theorem1_lower` with `hK` from the quality; then `x𝔖C(4)/2 > 4√(2x+2)·log³(2x+2)` at
`x ≥ q^250`.  Consumer: `hEngine_poly_of_N7`. -/
theorem crown_handover {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC)
    (hF : FulcrumQualityPoly (n9Cq Cerr CA CA' CC) 30) :
    ∀ N : ℕ, ∃ x : ℕ, N ≤ x ∧
      4 * Real.sqrt (2 * (x : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) ^ 3
        < S1 (Finset.Ioc x (2 * x)) := by
  classical
  -- N7's signs, read once at a harmless instance, and `n9K ≥ 10`
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨C₀, A, A', hL5⟩ := hN7 3 (1 : DirichletCharacter ℂ 3) (one_pow 2) (le_refl 2) 0
  have hl3 : (0 : ℝ) < Real.log ((3 : ℕ) : ℝ) := by
    have h : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h]; exact Real.log_pos (by norm_num)
  have hCerr : 0 ≤ Cerr := hL5.Cerr_nonneg
  have hCA : 0 ≤ CA := hL5.CA_nonneg
  have hCA' : 0 ≤ CA' := hL5.CA'_nonneg
  have hCC : 0 ≤ CC := by
    rcases le_or_gt 0 CC with h | h
    · exact h
    · exfalso
      have hden : 0 < (Real.log ((3 : ℕ) : ℝ) + |hbLL (1 : DirichletCharacter ℂ 3)|)
          * Real.log ((3 : ℕ) : ℝ) :=
        mul_pos (by linarith only [hl3, abs_nonneg (hbLL (1 : DirichletCharacter ℂ 3))]) hl3
      have hneg := mul_neg_of_neg_of_pos h hden
      have hab := hL5.C₀_le
      have habs : (0 : ℝ) ≤ |C₀| := abs_nonneg _
      nlinarith only [hab, habs, hneg]
  have hn8C6 : 0 ≤ n8C6 CA CA' CC := by
    have h1 : (0 : ℝ) ≤ 64 * CA' := by linarith only [hCA']
    have h2 : (0 : ℝ) ≤ (128 * CA) ^ 2 := sq_nonneg _
    simp only [n8C6]; linarith only [h1, h2, hCC]
  have hCsnn : (0 : ℝ) ≤ n9Cs := by
    have hA := invSqC_spec.1
    have hprod : (0 : ℝ) ≤ invSqC * (dhB ^ 2 + dhB) :=
      mul_nonneg hA.le (by rw [show dhB = 680 from rfl]; norm_num)
    simp only [n9Cs]; linarith only [hprod]
  have hexp300ge : (1 : ℝ) ≤ Real.exp 300 := Real.one_le_exp (by norm_num)
  have hKbig : (10 : ℝ) ≤ n9K Cerr CA CA' CC := by
    have h1 : (1 : ℝ) ≤ 1 + n9Cs := by linarith only [hCsnn]
    have h2 : (1 : ℝ) ≤ 1 + n8C6 CA CA' CC + Cerr := by linarith only [hn8C6, hCerr]
    have hab : (1 : ℝ) ≤ (1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr) := by
      nlinarith only [h1, h2]
    have hprod : (1 : ℝ) ≤ Real.exp 300 * ((1 + n9Cs) * (1 + n8C6 CA CA' CC + Cerr)) := by
      nlinarith only [hab, hexp300ge]
    simp only [n9K, hbZ0A]
    nlinarith only [hprod]
  have hKnn : (0 : ℝ) ≤ n9K Cerr CA CA' CC := by linarith only [hKbig]
  have hexp2K : (20 : ℝ) ≤ Real.exp (2 * n9K Cerr CA CA' CC) := by
    have h := Real.add_one_le_exp (2 * n9K Cerr CA CA' CC)
    linarith only [h, hKbig]
  -- `n9Cq` is astronomically above the ZFR threshold
  have hE0pos : (3000001 : ℝ) ≤ n9E0 := by
    have ha : (0 : ℝ) ≤ (Real.exp 300 * (802 + 4 * n9Cs)) ^ 8 := by positivity
    have hb : (0 : ℝ) < Real.exp (merC + segC) := Real.exp_pos _
    have hc := Real.add_one_le_exp (3 * 10 ^ 6 : ℝ)
    simp only [n9E0]; linarith
  have hexp20 : (253696 : ℝ) ≤ Real.exp (20 : ℝ) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ); linarith only [h]
    have h2 : Real.exp 1 ^ 20 = Real.exp 20 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 : (2 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) h1 20
    rw [← h2]; nlinarith only [h3]
  have hdCpos := dh_spec.1
  have hdC1 := dh_spec.2.1
  have hCqpos : 0 < n9Cq Cerr CA CA' CC := by
    simp only [n9Cq]; exact div_pos (Real.exp_pos _) hdCpos
  have hCqbig : (253696 : ℝ) ≤ n9Cq Cerr CA CA' CC := by
    have hnum : Real.exp (20 : ℝ)
        ≤ Real.exp (n9E0 + Real.exp (2 * n9K Cerr CA CA' CC) + 10) :=
      Real.exp_le_exp.mpr (by linarith only [hE0pos, hexp2K])
    simp only [n9Cq]
    rw [le_div_iff₀ hdCpos]
    nlinarith only [hnum, hexp20, hdCpos, hdC1]
  have hCc0 : (2 : ℝ) ≤ n9Cq Cerr CA CA' CC * (1 / 126848) := by
    linarith only [hCqbig]
  -- Siegel, INEFFECTIVE, fixed BEFORE the modulus is chosen
  obtain ⟨CS, hCSpos, hSiegel⟩ := Salt.SW.siegel_theorem (Real.exp (-402)) (Real.exp_pos _)
  intro N
  set T : ℝ := Real.exp 401 * (2 * |Real.log CS| + 2) + 10 ^ 8 with hTdef
  obtain ⟨q, hq0, χ, ρ, hQq, hprim, hsq, hne, hzero, hball⟩ :=
    hF (max N ⌈Real.exp T⌉₊)
  haveI := hq0
  have hqN : N ≤ q := le_of_lt (lt_of_le_of_lt (le_max_left N _) hQq)
  have hqceil : ⌈Real.exp T⌉₊ < q := lt_of_le_of_lt (le_max_right N _) hQq
  have hqexp : Real.exp T < (q : ℝ) := by
    have h1 : ((⌈Real.exp T⌉₊ : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hqceil
    have h2 : Real.exp T ≤ ((⌈Real.exp T⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith only [h1, h2]
  have hLT : T < Real.log q := by
    have h := Real.log_lt_log (Real.exp_pos T) hqexp
    rwa [Real.log_exp] at h
  have hTbig : (10 ^ 8 : ℝ) ≤ T := by
    have h : (0 : ℝ) ≤ Real.exp 401 * (2 * |Real.log CS| + 2) := by positivity
    rw [hTdef]; linarith only [h]
  have hLpos : 0 < Real.log q := by linarith only [hLT, hTbig]
  have hLhuge : (10 ^ 8 : ℝ) ≤ Real.log q := by linarith only [hLT, hTbig]
  have hq3 : 3 ≤ q := three_le_of_ne_one χ hne
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith only [hqR]
  -- the fulcrum ball at exponent `1` follows from the one at exponent `30`
  have hL1 : (1 : ℝ) ≤ Real.log q := by linarith only [hLhuge]
  have hmono30 : Real.log q ≤ Real.log q ^ (30 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 : ℝ) ≤ 30)
    rwa [Real.rpow_one] at h
  have hnn : (0 : ℝ) ≤ ‖(1 : ℂ) - ρ‖ := norm_nonneg _
  have hball1 : ‖(1 : ℂ) - ρ‖ * (n9Cq Cerr CA CA' CC * Real.log q) ≤ 1 := by
    have hstep : ‖(1 : ℂ) - ρ‖ * (n9Cq Cerr CA CA' CC * Real.log q)
        ≤ ‖(1 : ℂ) - ρ‖ * (n9Cq Cerr CA CA' CC * Real.log q ^ (30 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hnn
      nlinarith only [hmono30, hCqpos]
    linarith only [hstep, hball]
  obtain ⟨him0, hre12, hre1⟩ := Salt.Fulcrum.fulcrum_zero_real (n9Cq Cerr CA CA' CC)
    (1 / 126848) (by norm_num) (by norm_num) hCc0
    Salt.Fulcrum.zero_free_region_all_numeral hq3 hprim hne hzero hball1
  have hcoe : ((ρ.re : ℝ) : ℂ) = ρ := by apply Complex.ext <;> simp [him0]
  have hzβ : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by rw [hcoe]; exact hzero
  obtain ⟨β₀, hz0, hββ0, hβ01, hmax⟩ := beta0_max_of_zero hprim hsq hne hzβ hre12 hre1
  have hnormβ : ‖(1 : ℂ) - ρ‖ = 1 - ρ.re := by
    have he : (1 : ℂ) - ρ = ((1 - ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him0]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hre1])]
  have hβpos : 0 < 1 - β₀ := by linarith only [hβ01]
  have hrpos : (0 : ℝ) < n9Cq Cerr CA CA' CC * Real.log q ^ (30 : ℝ) :=
    mul_pos hCqpos (Real.rpow_pos_of_pos hLpos 30)
  have hqual : (1 - β₀) * (n9Cq Cerr CA CA' CC * Real.log q ^ (30 : ℝ)) ≤ 1 := by
    rw [hnormβ] at hball
    have hstep : (1 - β₀) * (n9Cq Cerr CA CA' CC * Real.log q ^ (30 : ℝ))
        ≤ (1 - ρ.re) * (n9Cq Cerr CA CA' CC * Real.log q ^ (30 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hββ0]) hrpos.le
    linarith only [hstep, hball]
  -- the operating point
  set η : ℝ := 1 / ((1 - β₀) * Real.log q) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hηL : η * Real.log q = 1 / (1 - β₀) := by rw [hηdef]; field_simp
  have hηLge : n9Cq Cerr CA CA' CC * Real.log q ^ (30 : ℝ) ≤ η * Real.log q := by
    rw [hηL, le_div_iff₀ hβpos]
    linarith only [hqual]
  -- `ℓ′ ≥ n9E0 + e^{2·n9K} − 4 + 16·log L`
  have hlogCq : Real.log (n9Cq Cerr CA CA' CC)
      = n9E0 + Real.exp (2 * n9K Cerr CA CA' CC) + 10 + Real.log (1 / dhC) := by
    simp only [n9Cq]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hdCpos), Real.log_exp,
      one_div, Real.log_inv]
    ring
  have hlogηL : Real.log (n9Cq Cerr CA CA' CC) + 30 * Real.log (Real.log q)
      ≤ Real.log (η * Real.log q) := by
    have h1 : Real.log (n9Cq Cerr CA CA' CC * Real.log q ^ (30 : ℝ))
        ≤ Real.log (η * Real.log q) := Real.log_le_log hrpos hηLge
    rw [Real.log_mul (ne_of_gt hCqpos) (ne_of_gt (Real.rpow_pos_of_pos hLpos 30)),
      Real.log_rpow hLpos] at h1
    linarith only [h1]
  have hlogLnn : 0 ≤ Real.log (Real.log q) := Real.log_nonneg hL1
  have hlogL1 : (1 : ℝ) ≤ Real.log (Real.log q) := by
    have he := Real.exp_one_lt_d9
    have h := Real.log_le_log (Real.exp_pos 1)
      (by linarith only [he, hLhuge] : Real.exp 1 ≤ Real.log q)
    rwa [Real.log_exp] at h
  have hlog4qle : Real.log (4 * (q : ℝ)) ≤ 3 + Real.log q := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hqpos)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h]
  have hlog4qpos : 0 < Real.log (4 * (q : ℝ)) := by
    have h : Real.log q ≤ Real.log (4 * (q : ℝ)) :=
      Real.log_le_log hqpos (by linarith only [hqpos])
    linarith only [h, hLpos]
  have hlog2L : Real.log (2 * Real.log q) = Real.log 2 + Real.log (Real.log q) :=
    Real.log_mul (by norm_num) (ne_of_gt hLpos)
  have hl2 := Real.log_two_lt_d9
  have hA2 : Real.log (Real.log (4 * (q : ℝ)) + 2) ≤ 1 + Real.log (Real.log q) := by
    have h1 : Real.log (4 * (q : ℝ)) + 2 ≤ 2 * Real.log q := by linarith only [hlog4qle, hLhuge]
    have h2 : Real.log (Real.log (4 * (q : ℝ)) + 2) ≤ Real.log (2 * Real.log q) :=
      Real.log_le_log (by linarith only [hlog4qpos]) h1
    linarith only [h2, hlog2L, hl2]
  have hA3 : Real.log (Real.log (4 * (q : ℝ))) ≤ 1 + Real.log (Real.log q) := by
    have h1 : Real.log (4 * (q : ℝ)) ≤ 2 * Real.log q := by linarith only [hlog4qle, hLhuge]
    have h2 : Real.log (Real.log (4 * (q : ℝ))) ≤ Real.log (2 * Real.log q) :=
      Real.log_le_log hlog4qpos h1
    linarith only [h2, hlog2L, hl2]
  have hEllge : n9E0 + Real.exp (2 * n9K Cerr CA CA' CC) - 4 + 16 * Real.log (Real.log q)
      ≤ n9Ell q η := by
    simp only [n9Ell, show dhK = 14 from rfl]
    linarith only [hlogηL, hlogCq, hA2]
  have hellBig : n9E0 ≤ n9Ell q η := by linarith only [hEllge, hexp2K, hlogLnn]
  have hellL : n9E0 + 16 * Real.log (Real.log (4 * (q : ℝ))) ≤ n9Ell q η := by
    linarith only [hEllge, hexp2K, hA3]
  have hEllexp : Real.exp (2 * n9K Cerr CA CA' CC) ≤ n9Ell q η := by
    linarith only [hEllge, hE0pos, hlogLnn]
  have hK : 2 * n9K Cerr CA CA' CC ≤ Real.log (n9Ell q η) := by
    have h := Real.log_le_log (Real.exp_pos (2 * n9K Cerr CA CA' CC)) hEllexp
    rwa [Real.log_exp] at h
  -- `ηq` from Siegel, at `ε = e^{−402}`
  have hβ0S : β₀ ≤ 1 - CS / (q : ℝ) ^ (Real.exp (-402)) := hSiegel q χ hprim hsq hne hz0 hβ01
  have hrp : (0 : ℝ) < (q : ℝ) ^ (Real.exp (-402)) := Real.rpow_pos_of_pos hqpos _
  have hηub : η ≤ (q : ℝ) ^ (Real.exp (-402)) / (CS * Real.log q) := by
    rw [hηdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have hlow : CS / (q : ℝ) ^ (Real.exp (-402)) ≤ 1 - β₀ := by linarith only [hβ0S]
    rw [div_le_iff₀ hrp] at hlow
    nlinarith only [hlow, hLpos, hrp, hCSpos, hβpos]
  have hlogη : Real.log η
      ≤ Real.exp (-402) * Real.log q - Real.log CS - Real.log (Real.log q) := by
    have h := Real.log_le_log hηpos hηub
    rw [Real.log_div (ne_of_gt hrp) (by positivity), Real.log_rpow hqpos,
      Real.log_mul (ne_of_gt hCSpos) (ne_of_gt hLpos)] at h
    linarith only [h]
  have hηq : Real.exp 401 * Real.log η ≤ Real.log q := by
    have h401 : (0 : ℝ) < Real.exp 401 := Real.exp_pos _
    have hprod : Real.exp 401 * Real.exp (-402 : ℝ) = Real.exp (-1 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ); linarith only [h]
    have hem1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
      linarith only [he2]
    have hstep : Real.exp 401 * Real.log η
        ≤ Real.exp 401 * (Real.exp (-402) * Real.log q - Real.log CS
            - Real.log (Real.log q)) := mul_le_mul_of_nonneg_left hlogη h401.le
    have hCSabs : -Real.log CS ≤ |Real.log CS| := neg_le_abs _
    have hTle : Real.exp 401 * (2 * |Real.log CS|) ≤ Real.log q := by
      have h : (0 : ℝ) ≤ Real.exp 401 * 2 := by positivity
      rw [hTdef] at hLT
      nlinarith only [hLT, h, hCSabs, abs_nonneg (Real.log CS)]
    have hexpand : Real.exp 401 * (Real.exp (-402) * Real.log q - Real.log CS
          - Real.log (Real.log q))
        = Real.exp (-1 : ℝ) * Real.log q + Real.exp 401 * (-Real.log CS)
          - Real.exp 401 * Real.log (Real.log q) := by
      rw [← hprod]; ring
    have hpart1 : Real.exp (-1 : ℝ) * Real.log q ≤ Real.log q / 2 := by
      nlinarith only [hem1, hLpos]
    have hpart2 : Real.exp 401 * (-Real.log CS) ≤ Real.log q / 2 := by
      nlinarith only [hCSabs, hTle, h401]
    have hpart3 : 0 ≤ Real.exp 401 * Real.log (Real.log q) := by positivity
    linarith only [hstep, hexpand, hpart1, hpart2, hpart3]
  -- the regime, and Theorem 1's lower half at `x = q^250`
  have hR : N9Regime q χ β₀ η :=
    { prim := hprim, sq := hsq, ne := hne, zero := hz0, β1 := hβ01, ηdef := hηdef,
      ηmax := hmax, ηq := hηq, ellBig := hellBig, ellL := hellL }
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by linarith only [hqR]
  have hxcast : (((q ^ 250 : ℕ)) : ℝ) = (q : ℝ) ^ 250 := by push_cast; ring
  have hxlo : (q : ℝ) ^ 250 ≤ (((q ^ 250 : ℕ)) : ℝ) := by rw [hxcast]
  have hxhi : (((q ^ 250 : ℕ)) : ℝ) ≤ (q : ℝ) ^ 500 := by
    rw [hxcast]; exact pow_le_pow_right₀ hq1R (by norm_num)
  refine ⟨q ^ 250, ?_, ?_⟩
  · calc N ≤ q := hqN
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 250 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlow := hb_theorem1_lower hR hxlo hxhi hN7 hK
  -- the crude tail is beaten at `x = q^250`
  set X : ℝ := (((q ^ 250 : ℕ)) : ℝ) with hXdef
  have hXeq : X = (q : ℝ) ^ 250 := hxcast
  have hXpos : 0 < X := by rw [hXeq]; positivity
  have hX1 : (1 : ℝ) ≤ X := by rw [hXeq]; exact one_le_pow₀ hq1R
  have hu : Real.log X = 250 * Real.log q := by
    rw [hXeq, Real.log_pow]; push_cast; ring
  have hubig : (10 ^ 10 : ℝ) ≤ Real.log X := by rw [hu]; linarith only [hLhuge]
  have hXexp : Real.exp (Real.log X) = X := Real.exp_log hXpos
  have hsqrt4 : Real.sqrt (4 * X) = 2 * Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hs1 : Real.sqrt (2 * X + 2) ≤ 2 * Real.sqrt X := by
    rw [← hsqrt4]
    exact Real.sqrt_le_sqrt (by linarith only [hX1])
  have hlogw : Real.log (2 * X + 2) ≤ 2 * Real.log X := by
    have h1 : Real.log (2 * X + 2) ≤ Real.log (4 * X) :=
      Real.log_le_log (by linarith only [hXpos]) (by linarith only [hX1])
    have h2 : Real.log (4 * X) = Real.log 4 + Real.log X :=
      Real.log_mul (by norm_num) (ne_of_gt hXpos)
    have h3 : Real.log (4 : ℝ) ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith only [h]
    linarith only [h1, h2, h3, hubig]
  have hlogwnn : 0 ≤ Real.log (2 * X + 2) :=
    Real.log_nonneg (by linarith only [hX1])
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hsqrtXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXpos.le
  -- `1792·(log X)³ < √X`
  have hpow8 : (Real.log X / 8 + 1) ^ 8 ≤ X := by
    have h1 : Real.log X / 8 + 1 ≤ Real.exp (Real.log X / 8) := Real.add_one_le_exp _
    have h2 : Real.exp (Real.log X / 8) ^ 8 = X := by
      rw [← Real.exp_nat_mul, show ((8 : ℕ) : ℝ) * (Real.log X / 8) = Real.log X by
        push_cast; ring, hXexp]
    have h3 : (Real.log X / 8 + 1) ^ 8 ≤ Real.exp (Real.log X / 8) ^ 8 :=
      pow_le_pow_left₀ (by linarith only [hubig]) h1 8
    linarith only [h2, h3]
  have hcube : (1792 * Real.log X ^ 3 + 1) ^ 2 ≤ X := by
    have hu0 : (0 : ℝ) < Real.log X := by linarith only [hubig]
    have hu1 : (1 : ℝ) ≤ Real.log X := by linarith only [hubig]
    have hA : (1792 * Real.log X ^ 3 + 1) ^ 2 ≤ 3214849 * Real.log X ^ 6 := by
      have h36 : Real.log X ^ 3 ≤ Real.log X ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
      have h06 : (1 : ℝ) ≤ Real.log X ^ 6 := one_le_pow₀ hu1
      nlinarith only [h36, h06]
    have hB : (3214849 : ℝ) * Real.log X ^ 6 ≤ (Real.log X / 8 + 1) ^ 8 := by
      have h1 : (Real.log X / 8) ^ 8 ≤ (Real.log X / 8 + 1) ^ 8 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hu0]) 8
      have h2 : (Real.log X / 8) ^ 8 = Real.log X ^ 8 / 16777216 := by ring
      have h4 : Real.log X ^ 8 = Real.log X ^ 6 * Real.log X ^ 2 := by ring
      have h5 : (10 : ℝ) ^ 20 ≤ Real.log X ^ 2 := by nlinarith only [hubig, hu0]
      have h6 : (0 : ℝ) ≤ Real.log X ^ 6 := by positivity
      have h3 : (3214849 : ℝ) * Real.log X ^ 6 ≤ Real.log X ^ 8 / 16777216 := by
        rw [h4, le_div_iff₀ (by norm_num)]
        nlinarith only [h5, h6]
      linarith only [h1, h2, h3]
    linarith only [hA, hB, hpow8]
  have hsqrtgt : 1792 * Real.log X ^ 3 < Real.sqrt X := by
    have h1 : Real.sqrt ((1792 * Real.log X ^ 3 + 1) ^ 2) ≤ Real.sqrt X :=
      Real.sqrt_le_sqrt hcube
    rw [Real.sqrt_sq (by positivity)] at h1
    linarith only [h1]
  have hSS := n9_singular_ge
  have hkey : 4 * Real.sqrt (2 * X + 2) * Real.log (2 * X + 2) ^ 3 < X / 28 := by
    have hstep1 : 4 * Real.sqrt (2 * X + 2) * Real.log (2 * X + 2) ^ 3
        ≤ 4 * (2 * Real.sqrt X) * (2 * Real.log X) ^ 3 := by
      have hc1 : Real.log (2 * X + 2) ^ 3 ≤ (2 * Real.log X) ^ 3 :=
        pow_le_pow_left₀ hlogwnn hlogw 3
      have hc2 : (0 : ℝ) ≤ 4 * Real.sqrt (2 * X + 2) := by positivity
      have hc3 : 4 * Real.sqrt (2 * X + 2) ≤ 4 * (2 * Real.sqrt X) := by
        linarith only [hs1]
      have hc4 : (0 : ℝ) ≤ (2 * Real.log X) ^ 3 := by positivity
      nlinarith only [hc1, hc2, hc3, hc4]
    have hstep2 : 4 * (2 * Real.sqrt X) * (2 * Real.log X) ^ 3
        = 64 * (Real.sqrt X * Real.log X ^ 3) := by ring
    have hstep3 : 64 * (Real.sqrt X * Real.log X ^ 3)
        < 64 * (Real.sqrt X * (Real.sqrt X / 1792)) := by
      have h : Real.log X ^ 3 < Real.sqrt X / 1792 := by linarith only [hsqrtgt]
      nlinarith only [h, hsqrtXpos]
    have hstep4 : 64 * (Real.sqrt X * (Real.sqrt X / 1792)) ≤ X / 28 := by
      nlinarith only [hsqrtXsq]
    linarith only [hstep1, hstep2, hstep3, hstep4]
  have hM : X / 28 ≤ X * Salt.HardyLittlewood.twinSingularSeries * hbCalpha 4 / 2 := by
    rw [n9_calpha_four]
    nlinarith only [hSS, hXpos]
  linarith only [hkey, hM, hlow]

/-- **THE ENGINE AT STRENGTH `30`, CONDITIONAL ON N7.**  Class **A**, cap 40:
`twinPrimeConjecture_of_frequently_S1 (crown_handover hN7 hF)`.  Consumer:
`heathBrownDichotomyPoly_of_N7`. -/
theorem hEngine_poly_of_N7 {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    FulcrumQualityPoly (n9Cq Cerr CA CA' CC) 30 → TwinPrimeConjecture := by
  exact fun hF => twinPrimeConjecture_of_frequently_S1 (crown_handover hN7 hF)

/-- **THE INTERMEDIATE CROWN, AT THE STRENGTH THE LANDED SUPPLY REACHES, CONDITIONAL ON N7:
`TPC ∨ NoSiegelZerosPoly 30`.**  Stated at the LITERAL `30` (= `dhK + 16`: the contract's `14`
plus the tail's crude-count price, finding 4), not at a def (the verdict's U4: a headline whose
exponent is a mutable `def` in the same file would silently re-anchor).  The frozen crown is the
`k = 1` member (`heathBrownDichotomyPoly_one_iff`); reaching it is Arm B — a D–H contract at
`k ≤ 1` (HB's Jutila form) AND a log-free density on the near-1 strip — by the Captain's ruling.
Class **A**, cap 20.  Consumer: none yet — the intermediate crown row. -/
theorem heathBrownDichotomyPoly_of_N7 {Cerr CA CA' CC : ℝ} (hN7 : N7Exit Cerr CA CA' CC) :
    HeathBrownDichotomyPoly 30 := by
  have hCq : 0 < n9Cq Cerr CA CA' CC := by
    simp only [n9Cq]
    exact div_pos (Real.exp_pos _) dh_spec.1
  exact fulcrum_dichotomy_poly hCq (by norm_num) (hEngine_poly_of_N7 hN7)

end Salt.HB
