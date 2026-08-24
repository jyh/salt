/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Exit
import Salt.MR.DoorFloor1500
import Salt.MR.MRTProp24
import Salt.MR.RHSGrade
import Salt.MR.NonPret

/-!
# The MRT port (item 15) — the landed nodes

Design block: `seat/briefs/2026-08-24-item15-mrt-port-DESIGN-BLOCK-v6.md`.  This file
consolidates the port's first four Lean nodes, dispatched from the frozen executor brief
of 2026-08-24 and landed at salt `b85006f4` as four separate modules; merged here and
rooted under the maestro's approval so that the full build and the axiom audit can see
them.  *An unrooted module is invisible to every instrument.*

| node | declaration |
|---|---|
| **N1** | `regime_headroom_at_socket` |
| **N2** | `mrtQuality_lower_of_pointwise` |
| **N3** | `lam_eq_lamCoeff_of_prime`, `pretDistSq_lam_eq_lamCoeff` |
| **N4** | `mrtCompMultDatum_lamCoeff` |

⛔ **SCOPE, stated once for the whole file.**  These four close **named residuals** of the
port's design block.  **They do NOT compose to the door**, and none of them discharges
`MRTUniformityXi`.  The port's open gaps at the time of landing are the design block's
G1 (`mrtQuality` has no producer), G3 (the L¹ twin of the unit-cell bridge) and G4 (the
floor/socket datum mismatch); N2 in particular is **true but inert** until a floor
uniform in `(t, q, χ)` exists to feed it — see its own section below.

The per-node docstrings that follow are those of the four original modules, carried over
unchanged.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla

/-!
## N1 — Tao's W-headroom, transported to the split road's exit socket

Item 15 (the MRT port), design block v6 §4, node **N1**.

`m4_exit_socket_split` (`M4Exit.lean:487`) hands the split road a regime together with
the `¬ logChowla2Fails` implication, but the headroom conjunct it carries is the
head's TOWER endpoint law
(`50 ≤ loglog H₋ → loglog H₊ ≤ (loglog H₋)^5`) — passed through unused.  The
`B₅ = 12` W-headroom chain (`DoorFloor1500.lean:75`/`:90`) is stated at a regime and
is therefore free to be fired at the socket's regime; this file does exactly that,
trading the tower conjunct for

`(log H₊)^{1500} ≤ log (x / (2ω))`.

## What is NEW here, and what is not

📌 `regime_head_W_headroom_1500` (`DoorFloor1500.lean:221`) ALREADY carries the same
inequality — but at a **different regime supplier** (`chowlaRegime_exists_param_head_gJoin`,
with an `H0door δ₀` floor conjunct and no failure implication).  N1's content is the
**transport to the socket's regime**, which additionally carries the
`¬ logChowla2Fails` implication; nothing about the inequality itself is re-proved.

## The floor slot stays open

The socket has already spent its `extraFloor` slot at `0` (`M4Exit.lean:500`), so its
`U1floor` binder is the LAST floor slot on this road.  The three floor demands this
proof needs are therefore joined into that one slot,

`U1floor := max extraFloor (max ⌈Real.exp 36000000⌉₊ (epsFloor ε))`,

and the caller's own `extraFloor` is re-exposed as a binder of the conclusion.  Pinning
it here would strand every downstream consumer.

`⌈Real.exp 36000000⌉₊` is a SHAPE, never evaluated — no closed numeral of that size is
formed, exactly as `DoorFloor.lean:40` records of its own `exp(9·10³⁸)`.  The `hbig`
arm is pure `Nat.le_ceil` / `Real.log_exp` / `Real.log_le_log` monotonicity.

## Measured strength

The conclusion is the **ℕ-power** form `(Real.log R.Hhi) ^ (1500 : ℕ)`.  It does **not**
deliver Tao arXiv:1509.05422v2 Prop. 2.4's `rpow` binder `W ≤ (log X)^{1/125}`; the
passage between the two is a separate, NOT-dispatchable step (v6 §4's exclusion list).
`B₅`'s live value is `12`; the `(log H)^5` forms elsewhere in the corpus are the
RETIRED `B₅ = 5` and are not cited here.
-/



/-- **N1 — the socket, re-served with Tao's W-headroom at `B₅ = 12`.**  The split road's
exit socket (`m4_exit_socket_split`), with its unused tower conjunct traded for the
`1500`-headroom inequality `(log H₊)^{1500} ≤ log X_min`.  The caller's floor slot is
kept OPEN (`∀ extraFloor`); the three internal floor demands ride in the socket's own
last slot. -/
theorem regime_headroom_at_socket :
    ∃ (ε : ℚ) (δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (extraFloor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (Real.log (R.Hhi : ℝ)) ^ (1500 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) ∧
          ((∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
              NearRatTight (arcDen 12 H) H α →
                (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ₀ * (H : ℝ)) →
            ¬ logChowla2Fails R.eps R.x R.ω)
    := by
  obtain ⟨ε, δ₀, hε, hδ₀, hsock⟩ := m4_exit_socket_split
  refine ⟨ε, δ₀, hε, hδ₀, ?_⟩
  intro extraFloor g
  -- the socket's `U1floor` is the LAST floor slot: join all three demands into it
  obtain ⟨R, hReps, hU1, hRg, -, hR⟩ :=
    hsock (max extraFloor (max ⌈Real.exp 36000000⌉₊ (epsFloor ε))) g
  have hextra : extraFloor ≤ R.Hlo := le_trans (le_max_left _ _) hU1
  have hceil : ⌈Real.exp 36000000⌉₊ ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hU1
  have hepsF : epsFloor ε ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hU1
  -- the `hbig` arm: `exp 36000000 ≤ H₊` through the ceiling, then `log`-monotonicity
  have hbig : (36000000 : ℝ) ≤ Real.log (R.Hhi : ℝ) := by
    have hcast : ((⌈Real.exp (36000000 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (R.Hhi : ℝ) := by
      exact_mod_cast le_trans hceil R.hHlohi
    have hle : Real.exp (36000000 : ℝ) ≤ (R.Hhi : ℝ) := le_trans (Nat.le_ceil _) hcast
    have hlog := Real.log_le_log (Real.exp_pos _) hle
    rwa [Real.log_exp] at hlog
  -- the `heps` arm composes only after `rw [hReps]` (`DoorFloor1500.lean:234-236`)
  have hepsHhi : epsFloor R.eps ≤ R.Hhi := by
    rw [hReps]
    exact le_trans hepsF R.hHlohi
  refine ⟨R, hReps, hextra, hRg, ?_, hR⟩
  exact regime_W_headroom_of_floor_1500 R
    (regime_hthr_of_scale_1500 R hbig (heps_arm_of_epsFloor hepsHhi))

/-!
## A pointwise floor transports to `mrtQuality`

`mrtQuality g X Q` (`Salt/MR/MRTProp24.lean:187-189`) is the infimum of
`pretDistSq g (chiTwist χ t) X` over the **triple** `(t, q, χ)` cut out by
`|t| ≤ X ∧ 1 ≤ q ∧ (q : ℝ) ≤ Q`.  This file records the `le_csInf` half of that
transport: a floor holding **pointwise, uniformly over the whole index set** is a
floor on the infimum.

⛔ **Both guards are load-bearing.**  `hX : 0 ≤ X` and `hQ : (1 : ℝ) ≤ Q` are what
make the index set nonempty, via the triple `(t, q, χ) = (0, 1, 1)`: `hX` is spent
on `|0| ≤ X` and `hQ` on `((1 : ℕ) : ℝ) ≤ Q`.  Drop either one and the set can be
empty; `Real.sInf ∅ = 0` in mathlib, so the pointwise hypothesis becomes vacuous and
**any `c > 0` refutes the conclusion** — the statement would be FALSE, not merely
unproved.  The witness character is mathlib's `(1 : DirichletCharacter ℂ 1)`; it is
**not** `chiPrin` (`Salt/MR/ChiFloor.lean:188`), which is `ℕ → ℂ` — the character
already applied and coerced — and cannot inhabit the `χ` binder.

The corpus's own landed instance of exactly this move is `mrtM_nonneg`
(`Salt/MR/MRTPropA3.lean:2595`), which likewise spends its `hX` on the nonemptiness
witness; this proof is modelled on it.

⚠️ **Scope.**  This closes the `le_csInf` half only; the **index-uniformity** half is
supplied *up to a threshold hypothesis*, and the precise state of that is below.

⛔ **CORRECTION (2026-08-24, same day this landed).**  An earlier version of this
paragraph read "the landed twisted floors — **e.g.** `chi_floor_all_unconditional_twisted`
… are **not** uniform in the `(t, q, χ)` this lemma quantifies over.  The lemma is
therefore **true but inert**."  **The `e.g.` was doing work it had not earned: one
family member's non-uniformity was generalised to the family, and
`capFreeFloor_all_chi_vt` was never looked at.**  Corrected:

* `chi_floor_all_unconditional_twisted` (`Salt/MR/ChiLLower.lean:720-728`) really does
  carry `((2 * orderOf χ : ℕ) : ℝ) ^ 2` in a denominator and subtract `primeDivSum q X`
  — that half was true, and is why it cannot feed this lemma.
* But `capFreeFloor_all_chi_vt` (`Salt/MR/VkMidSharp.lean:460`) binds `∃ K` **outside**
  `∀ (q) [NeZero q] (χ) (X)`, so its floor value is uniform in `q` and `χ`; and
  `CapFreeFloor` (`Salt/MR/CapFreeArm.lean:111-113`) is stated over the box `|v| ≤ X`,
  which is this lemma's `|t| ≤ X`.  The two objects meet definitionally, by
  `pretDistSq_lam_chi_twist` (`Salt/MR/ChiFloor.lean:208`) composed with this file's own
  `pretDistSq_lam_eq_lamCoeff`.

⛔ **THE RESIDUAL, STATED SO IT IS NOT MISTAKEN FOR CLOSURE.**  That floor is gated by a
**per-`q` threshold hypothesis** (`VkMidSharp.lean:463-468`), which this lemma's `∀ q ≤ Q`
needs discharged at *every* `q`.  A `q ≤ Q`-shaped discharge of it was **NOT FOUND UNDER
THREE ARMS**; the nearest landed instrument, `pieceFloor_vt_threshold_of_loglog`
(`Salt/MR/RbdSupply.lean:496`), does exactly this job but at the arc-denominator cap
`(q:ℝ) ≤ arcDen 12 H` and at the datum `pieceDatum χ 𝒥 Pseq Qseq`, not at `lamChi χ`.
⇒ **Read this as: the index-uniformity half is supplied MODULO a named, absent,
arithmetic-only uniformisation — never as "G1 is closed".**  Nothing here is built.
-/


/-- **A pointwise floor over the whole index set is a floor on `mrtQuality`.**
`c ≤ pretDistSq g (chiTwist χ t) X` for every admissible triple `(t, q, χ)` gives
`c ≤ mrtQuality g X Q`, by `le_csInf` with the `(0, 1, 1)` nonemptiness witness.
`hX` and `hQ` are exactly what that witness costs — see the module docstring. -/
theorem mrtQuality_lower_of_pointwise {g : ℕ → ℂ} {X Q c : ℝ}
    (hX : 0 ≤ X) (hQ : (1 : ℝ) ≤ Q)
    (h : ∀ (t : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q),
        |t| ≤ X → 1 ≤ q → (q : ℝ) ≤ Q → c ≤ pretDistSq g (chiTwist χ t) X) :
    c ≤ mrtQuality g X Q := by
  unfold mrtQuality
  refine le_csInf ⟨pretDistSq g (chiTwist (1 : DirichletCharacter ℂ 1) 0) X,
    ⟨0, 1, (1 : DirichletCharacter ℂ 1), by simpa using hX, le_refl 1,
      by simpa using hQ, rfl⟩⟩ ?_
  rintro b ⟨t, q, χ, ht, hq, hqQ, rfl⟩
  exact h t q χ ht hq hqQ

/-!
## Item 15, node N3 — the `lam` / `lamCoeff` bridge for `pretDistSq`

The MRT port (arXiv:1503.05121, Thm 1.7 / Prop 2.4) states its pretentious
distance at the honest Liouville coefficient `lamCoeff`, while this corpus's
non-pretentiousness stone S5 (`Salt/MR/NonPret.lean`) states it at `lam`, the
**constant `−1`**.  This module is the sanctioned bridge between the two.

## Why the bridge is legitimate — and why it is NOT a crossing

⚠️ The corpus carries a standing warning at ~15 sites (e.g. `M4Close.lean:590`,
"the two must never be crossed") against conflating `lam` with the true Liouville
function: `lam = fun _ => −1` (`NonPret.lean:48`) and `lamCoeff = λ`
(`M4Window.lean:74`) agree **only on primes** and differ everywhere else — most
visibly at `1`, where `λ(1) = 1 ≠ −1`.  Any statement summing over ALL `m`
(`sum_lam_residue_eq` vs `sum_liou_residue_eq`) genuinely must not cross them.

`pretDistSq` is not such a statement.  It sums over
`(Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime` — **primes only** (`Dist.lean:59-61`)
— and `pretDistSq_congr_primes` (`RHSGrade.lean:137-141`) reads its left datum at
primes and nowhere else.  So on this one object the two spellings are
interchangeable, and the exchange is a theorem rather than a confusion.

## Structure

* `lam_eq_lamCoeff_of_prime` — the pointwise fact: `lam p = lamCoeff p` for prime
  `p`, discharged by `lamCoeff_eq_liouvilleC` (`M4Exit.lean:99`, `rfl`) together
  with `liouvilleC_prime` (`M4Residue.lean:109`).  `pretDistSq_congr_primes`
  alone has nothing to feed it; this is the missing half.
* `pretDistSq_lam_eq_lamCoeff` — **the node**: the two distances are equal.
-/


/-- **The two λ-spellings agree at primes.**  `lam` is the constant `−1`
(`NonPret.lean:48`) and `lamCoeff` is the honest Liouville function
(`M4Window.lean:74`); at a prime `p` we have `Ω(p) = 1`, so `λ(p) = −1` and the
two coincide.  They do NOT coincide off the primes — see the module docstring. -/
theorem lam_eq_lamCoeff_of_prime {p : ℕ} (hp : p.Prime) : lam p = lamCoeff p := by
  have hlam : lam p = -1 := rfl
  have hliou : lamCoeff p = -1 := by
    rw [lamCoeff_eq_liouvilleC]
    exact liouvilleC_prime hp
  rw [hlam, hliou]

/-- **N3 — the `lam`/`lamCoeff` bridge for the pretentious distance.**
`𝔻(lam, g; X)² = 𝔻(lamCoeff, g; X)²`.  Legitimate because `pretDistSq` reads its
left datum only at primes (`Dist.lean:59-61`), where the constant `−1` and the
Liouville function agree.  This lets the S5 non-pretentiousness stone (stated at
`lam`) and the MRT port (stated at `lamCoeff`) meet on the same object. -/
theorem pretDistSq_lam_eq_lamCoeff (g : ℕ → ℂ) (X : ℝ) :
    pretDistSq lam g X = pretDistSq lamCoeff g X :=
  pretDistSq_congr_primes (fun _ hp => lam_eq_lamCoeff_of_prime hp) X

/-!
## N4 — `lamCoeff` inhabits MRT's 1-bounded completely multiplicative datum

Item 15, node N4 of the MRT port (design block
`seat/briefs/2026-08-24-item15-mrt-port-DESIGN-BLOCK-v6.md`, §4).  One theorem:
the Liouville coefficient sequence `lamCoeff` (`M4Window.lean:73`) satisfies
`MrtCompMultDatum` (`MRTProp24.lean:195-201`), the structure that packages MRT's
"1-bounded completely multiplicative" hypothesis.

All three fields come off the `liouvilleC` arm of the corpus, transported by the
spelling bridge `lamCoeff_eq_liouvilleC` (`M4Exit.lean:99`, which is `rfl`):

| field | discharged by |
|---|---|
| `map_one : g 1 = 1` | `liouvilleC_one` (`M4Residue.lean:96`) |
| `map_mul : ∀ m n, m ≠ 0 → n ≠ 0 → g (m*n) = g m * g n` | `liouvilleC_mul` (`M4Residue.lean:103`) |
| `norm_le_one : ∀ n, ‖g n‖ ≤ 1` | `liouvilleC_norm_le_one` (`M4Residue.lean:121`) |

`liouvilleC_mul` is the **unconditional** form `liouvilleC (m*n) = liouvilleC m *
liouvilleC n`, with no `m ≠ 0` / `n ≠ 0` side conditions at all — strictly
stronger than the field asks for.  The two hypothesis binders are therefore
consumed and discarded (`fun m n _ _ => …`); stronger discharges weaker.

⚠️ **Statement-level caution, recorded not acted on** (flagged to the helm in the
design block, §4, N4).  `MrtCompMultDatum` encodes **complete** multiplicativity —
that is Proposition 2.4's hypothesis (p. 10).  MRT **Theorem 1.7** (p. 6) asks only
for a 1-bounded **multiplicative** function.  Using this structure for a Theorem 1.7
port therefore **over-assumes**.  `lamCoeff` satisfies the stronger form, so this
node is true as stated and this file builds it exactly as stated; restating the
structure at the weaker hypothesis is a Fable/human-tier statement change.

⛔ This node closes a residual.  It does **not** compose to the door.
-/


/-- **N4.**  The Liouville coefficient sequence is a 1-bounded completely
multiplicative datum in MRT's sense.

Proof: `lamCoeff = liouvilleC` definitionally (`lamCoeff_eq_liouvilleC`, `rfl`),
then the three landed `liouvilleC` facts.  `liouvilleC_mul` carries no
nonvanishing hypotheses, so the structure's `m ≠ 0` / `n ≠ 0` binders are
consumed unused. -/
theorem mrtCompMultDatum_lamCoeff : MrtCompMultDatum lamCoeff := by
  rw [lamCoeff_eq_liouvilleC]
  exact
    { map_one := liouvilleC_one
      map_mul := fun m n _ _ => liouvilleC_mul m n
      norm_le_one := liouvilleC_norm_le_one }

end Salt.MR
