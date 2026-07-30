/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ParsevalStone
import Salt.MR.M4Close
import Salt.MR.M4ArithRho
import Salt.MR.S11ExitL2
import Salt.Entropy.Chowla.GoldbachEnergyN0

/-!
# ⟦THE L² RESTRUCTURE⟧ stone 7 — THE ROAD-SIDE RE-PLUMB (`M4DoorL2`)

Source: `docs/exploration/l2-restructure-freeze-0730.md` (freeze v1, 2026-07-30 12:45 PDT),
stone 7 — "the exit/close re-plumb (the new three-summand grade line; `M4DoorGates`
UNCHANGED)"; and the two refuter returns in `docs/blueprints/flags.md`, ⟦REF-L2-STONE⟧
(2026-07-30 12:58 PDT) and ⟦REF-L2-ARITH⟧ (13:04 PDT), whose **A1 THE BINDER SPLIT** this
file bakes in (§2).

## What this file does

Bank A landed the three pieces of the `L²` door supply and left the fuse open, because the
import direction forbade closing it in either supplier's own file:

* `parseval_insert_budget_door` (`M4ParsevalStone.lean:341`) — the insert budget at the
  door's gates, `|Ξ|`-FREE;
* `sum_bigXi_norm_windowExpSum_sq_le_parseval` / `…_twelve` /
  `mrtUniformityXiL2_of_absWindowSqBound` / `l2_budget_line` (`M4Window` §5) — the
  `Ξ_H`-summed arc adapter, whose insert budget is the NAMED hypothesis `hins`;
* `MRTUniformityXiL2` (`MRTDoor.lean:187`) — the `Ξ`-summed `L²` door predicate.

`M4Window` is UPSTREAM of `M4ParsevalStone`, so the adapter cannot cite the stone.  This
file imports both, and §1 discharges `hins` from the stone — the mechanical fuse W3's report
promised, made byte-exact by the `…_parseval` spelling (`(1/H²)` outside the `ξ`-sum,
integrand the *difference of two window sums*).

## THE ROAD SIDE, and what the `L²` route DELETES

`M4Close.m4_hbd_of_live` (`:464`) is the landed `L¹` door chain.  Its second step is the
Cauchy–Schwarz descent `∫‖·‖ ≤ √(∫‖·‖²)` — and that step is **DELETED** here: the road's
socket `M4Close.M4SievedDoorSq` (`:368`) is natively `L²`, so the `L²` door reads it with no
`√` at all.  That is why the socket's `Braw` ceiling relaxes by a full square
(⟦REF-L2-ARITH⟧: "the socket's ceiling stops being squared").

`M4Close.M4DoorGates` (`:403`) is consumed **UNCHANGED**, per the freeze — it is exactly the
gate list `parseval_insert_budget_door` asks for, field for field, including the `24·Cg/δ`
`M`-gate.  `M4Close.M4GradeGateSplit` (`:674`) is likewise UNTOUCHED; §3 mints a NEW gate
`M4GradeGateL2` beside it, because the `L²` budget line has no `√` and its target is `c₀ε`
rather than `δ₀`.

⟦ADDITIVE⟧ Not one landed declaration is touched anywhere in this file.

## The budget line (the freeze's, verbatim)

    2·K·Braw + δ/2 + 8·2^k/x  <  c₀·ε        (c₀ = cD3/(16·C))

`K = |Ξ_H|` multiplies the SQUARED-scale socket grade ONLY; the glue `δ` — the one summand
the spine's `hMδ` reads — is `K`-FREE.  `l2_budget_line` (`M4Window.lean:635`) is the
identity that turns the adapter's own right-hand side `K·(2·Bsieve) + 2·Binsert` into it, at
`Binsert := δ/4 + 4·2^k/x`, and §1 fires exactly that.

## ⟦A1 — THE MANDATORY BINDER SPLIT⟧ (§2)

⟦REF-L2-ARITH⟧, verbatim: *the socket's ceiling conjunct instantiates at
`δ_sock = √(c₀ε/4K) = 9.97e-85`; the spine's `hMδ` reads the glue `δ₀' = 1.19e-6` — 79
ORDERS apart, both free (`δ₀` `∀`-bound at all three landed sites).  **UNIFIED: `b = 324.18`
and the compose FAILS — the freeze's own fallback number arriving as a plumbing bug.***

The two thresholds are therefore TWO DISTINCT PARAMETERS in every statement of §2, and they
are never unified.  §2 also certifies the mechanism in the kernel:
`m4_doorL2_binder_floor_split` — the split `M`-floor is `96·Cg/(c₀ε)`, **`K`-FREE**;
`m4_doorL2_binder_floor_unified` — the unified `M`-floor obeys `2304·K/(c₀ε) ≤ floor²`, i.e.
its SQUARE carries `K` linearly.  That single `√K` is the 324-vs-65 gap.

## The four log scales

Untouched: `log H` (the socket/strata scale), `log ω` (the door's cover count, inside
`M4DoorGates` only), `log x` (the outer scale, only through `2^k/x`) and `log log H` (the
band floor).  Nothing in this file forms a new one.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE COMPOSITION: the road's `L²` socket ⟹ the `Ξ`-summed `L²` door

Every gate named, none smuggled:

* `M4DoorGates Cg R M k δ` — the door-glue bundle, UNCHANGED (M4-8's own list).  `Cg` is the
  constant `parseval_insert_budget_door` opens (`card_blockfree_le`'s, through
  `m4_door_sieve_mass`), so the `M`-gate `24·Cg/δ ≤ M` is a legal argument.
* `hfloor : H₀ ≤ R.Hlo` — the arc floor, produced from `ε` alone BEFORE the regime
  (`bigXiArcTight_twelve` through `nearRatTight_of_bigXiArcTight`; the non-vacuity discipline
  of `M4Window` §4/§5 verbatim).
* `hsock : M4SievedDoorSq R M Braw` — the road's per-`α` `L²` socket, at the band transport
  (the ⟦A2-5⟧ binder, supplied by `m4_bandTransport`).  NO Cauchy–Schwarz descent is applied
  to it.
* `hXi` — the `|Ξ_H| ≤ K` count, consumed ONCE and against the sieved leg only.
* `hK0 : 0 ≤ K`, `hceil : Braw H ≤ Bceil` — the `H`-uniform ceiling that makes the door's
  grade `H`-free (`MRTUniformityXiL2`'s `ρ` is a constant). -/

/-- **THE `L²` DOOR SUPPLY** (`m4_doorL2_supply`) — ⟦THE L² RESTRUCTURE⟧ stone 7's
composition.

From the road's per-`α` `L²` socket at every tight-major `α`, the door-glue gate bundle and
the large-spectrum count, the `Ξ`-summed `L²` door holds at the freeze's budget line

    ρ  =  2·K·Bceil + δ/2 + 8·2^k/x .

Where each summand comes from: `2·K·Bceil` is the socket leg (the count `K` times the
`(a+b)²` factor `2` times the socket's `H`-uniform grade — and **no `√`**, the `L¹→L²`
descent of `m4_hbd_of_live` is deleted); `δ/2 + 8·2^k/x` is `2·Binsert` at the Parseval
stone's insert budget `Binsert = δ/4 + 4·2^k/x`, paid ONCE for the whole of `Ξ_H` because
the sieve insert is `α`-INDEPENDENT.  `l2_budget_line` is the identity that assembles them.

`hins` — the adapter's one open hypothesis after bank A — is discharged HERE from
`parseval_insert_budget_door`, at the same `Cg` the gate bundle carries. -/
theorem m4_doorL2_supply :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (Braw : ℕ → ℝ) (K Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) →
            0 ≤ K →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
              MRTUniformityXiL2 R (2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, hCg, hpars⟩ := parseval_insert_budget_door
  refine ⟨Cg, hCg, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := nearRatTight_of_bigXiArcTight bigXiArcTight_twelve heps
  refine ⟨H₀, ?_⟩
  intro R hReps hfloor Braw K Bceil δ M k hgates hBraw0 hsock hXi hK0 hceil
  -- ⟦the arc supply, transported to the regime's own `ε`⟧
  have harc : ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H → ∀ ξ ∈ bigXi R.eps H,
      NearRatTight (arcDen 12 H) H (-(ξ.val : ℝ) / (H : ℝ)) := by
    intro H _ hH ξ hξ
    rw [hReps] at hξ
    exact hH₀ H hH ξ hξ
  -- ⟦the door's own scales, off the regime — the same four lines `m4_hbd_of_live` runs⟧
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ 3072 * M := by
    have := hgates.hM
    omega
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦THE FUSE⟧ the adapter's `hins`, discharged from the Parseval stone.
  have hins : ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXi R.eps H,
        ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
                (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω)
        ≤ δ / 4 + 4 * 2 ^ k / (R.x : ℝ) := by
    intro H _ hlo hhi
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (3072 * M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  -- ⟦the adapter⟧ arc + socket + count + the fused insert budget.
  have hkey := sum_bigXi_norm_windowExpSum_sq_le_parseval R
    (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    Braw K (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) hfloor harc hBraw0 (hsock m4_bandTransport)
    hXi hins
  -- ⟦the budget line⟧ and the `H`-uniform ceiling on the socket leg.
  intro H _ hlo hhi
  have h := hkey H hlo hhi
  rw [l2_budget_line K (Braw H) δ (R.x : ℝ) k] at h
  have hmono : 2 * K * Braw H ≤ 2 * K * Bceil :=
    mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
  linarith

/-- **THE `L²` DOOR SUPPLY AT THE IMPROVED COUNT** (`m4_doorL2_supply_500`) — `§1`'s
composition with the `|Ξ_H| ≤ K` gate discharged from `bigXi_bounded_500`
(`GoldbachEnergyN0.lean:866`, the N0-RETHREAD payoff: **the constant IS IN THE STATEMENT**,
`32·K_lcm·(2^35)²/ε¹⁰`, against the landed chain's three nested `∃`s).

⟦WHICH COUNT, AND WHY⟧  The improved bound is pinned at `ε = 1/500`, so it fits exactly when
the regime's own `ε` is that numeral — which is the ⟦EXPOSE-CERT⟧ pin (`eps_admissible`,
`ConstantsExposed.lean`).  At any other `ε` the landed `bigXi_bounded`
(`GoldbachEnergyFinal.lean:502`) supplies the gate instead, and §1's `hXi` slot takes it
unchanged.  The `2 ≤ H` side condition of the improved bound is free from the regime
(`two_le_regime_Hlo`).

`K_Ξ` is exported as a named constant so the b-floor ledger can read it: it is the ONLY place
`K` enters the `L²` route, and (⟦REF-L2-ARITH⟧ A5) it enters the `Braw` side ONLY — the
glue `δ` of the budget line is `K`-free, so N0's 316.6 bits buy zero on the `b`-floor and
317 on the socket ceiling. -/
theorem m4_doorL2_supply_500 :
    ∃ (Cg KXi : ℝ), 1 ≤ Cg ∧ 0 < KXi ∧ ∃ H₀ : ℕ,
      ∀ (R : ChowlaRegime), R.eps = 1 / 500 → H₀ ≤ R.Hlo →
        ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
          M4DoorGates Cg R M k δ →
          (∀ H : ℕ, 0 ≤ Braw H) →
          M4SievedDoorSq R M Braw →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            MRTUniformityXiL2 R (2 * KXi * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ)) := by
  obtain ⟨Cg, hCg, hsup⟩ := m4_doorL2_supply
  obtain ⟨Klcm, hKlcm, _, hcount⟩ := bigXi_bounded_500
  obtain ⟨H₀, hH₀⟩ := hsup (1 / 500) (by norm_num)
  refine ⟨Cg, 32 * Klcm * ((2 : ℝ) ^ 35) ^ 2 / (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10, hCg, ?_, H₀, ?_⟩
  · have h500 : (0 : ℝ) < (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10 := by norm_num
    positivity
  intro R hReps hfloor Braw Bceil δ M k hgates hBraw0 hsock hceil
  refine hH₀ R hReps hfloor Braw _ Bceil δ M k hgates hBraw0 hsock ?_ ?_ hceil
  · intro H _ hlo _
    have h2 : 2 ≤ H := le_trans (two_le_regime_Hlo R) hlo
    have := hcount H h2
    rwa [hReps]
  · have h500 : (0 : ℝ) < (((1 : ℚ) / 500 : ℚ) : ℝ) ^ 10 := by norm_num
    positivity

/-! ## §2 — ⟦A1 THE BINDER SPLIT⟧ (stone 7's load-bearing byte)

⟦REF-L2-ARITH, verbatim⟧: *the socket's ceiling conjunct instantiates at
`δ_sock = √(c₀ε/4K) = 9.97e-85`; the spine's `hMδ` reads the glue `δ₀' = 1.19e-6` — 79
ORDERS apart, both free (`δ₀` `∀`-bound at all three landed sites).  **UNIFIED: `b = 324.18`
and the compose FAILS — the freeze's own fallback number arriving as a plumbing bug.***

The three landed sites at which the socket's `δ₀` is `∀`-bound, and therefore free to be
instantiated at `δ_sock` independently of anything the spine does:
`M4SocketFused.m4_socket_discharged_fused` (`:113`), `M4CapWire` (`:566`),
`RamErrWS.m4_socket_discharged_capwired_ws` (`:489`) — and their hoisted twins in
`S11Hoist.lean` (`:127`, `:192`).  In each, `δ₀` enters the statement only through
`0 < δ₀`, through `doorRhoOfDelta δ₀` and through the ceiling conjunct
`96(1+2π)²·strataResidual H²·(108/5·RSanDoorRho (doorRhoOfDelta δ₀) H) ≤ δ₀²`.  Nothing ties
it to the door glue's `δ`; unifying them is a plumbing choice, not a constraint. -/

/-- **⟦A1, THE SOCKET SIDE⟧** (`m4_doorL2_socket_ceiling_at_sock`) — the terminals' ceiling
conjunct, read at `δ_sock` and at `δ_sock` ONLY.  This is `m4_arith_rs_ceiling_met_of_delta`
fired at the socket's own threshold: the `ρ` the terminals are instantiated at is
`doorRhoOfDelta δ_sock` (`M4ArithRho.lean:578`), NOT `doorRhoOfDelta δ₀'`.

Nothing here mentions the glue `δ₀'`.  That absence IS the amendment. -/
theorem m4_doorL2_socket_ceiling_at_sock {δsock : ℝ} (hδ : δsock ≠ 0) {H : ℕ}
    (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho (doorRhoOfDelta δsock) H)
      ≤ δsock ^ 2 :=
  m4_arith_rs_ceiling_met_of_delta hδ hL0 hlam

/-- **⟦A1, THE GLUE SIDE — THE SPLIT `M`-FLOOR IS `K`-FREE⟧**
(`m4_doorL2_binder_floor_split`).

With the binders SPLIT, the only threshold the spine's `hMδ` (`M4DoorGates.hMδ`,
`24·Cg/δ ≤ M`) ever reads is the glue `δ₀' = c₀ε/4`, and the resulting `M`-floor is

    24·Cg/δ₀'  =  96·Cg/(c₀ε) ,

in which `K` DOES NOT OCCUR.  (⟦REF-L2-ARITH⟧ A5: "K IS ABSENT FROM δ₀' — N0's 316.6 bits
buy ZERO on the b-floor, 317 on the Braw side only" — no double-count.)  At the certified
numerals this is `b = 65.125`, i.e. `m = 66`, against the ceiling `m ≤ 86`. -/
theorem m4_doorL2_binder_floor_split {Cg c₀ε : ℝ} (hc : c₀ε ≠ 0) :
    24 * Cg / (c₀ε / 4) = 96 * Cg / c₀ε := by
  field_simp
  ring

/-- **⟦A1, THE COUNTERFACTUAL — UNIFYING THE BINDERS PUTS `√K` IN THE `M`-FLOOR⟧**
(`m4_doorL2_binder_floor_unified`).

If the two thresholds are UNIFIED, the spine's `hMδ` reads the *socket's* threshold `δ_sock`,
whose price is `δ_sock² ≤ c₀ε/(4K)` (the socket ceiling `Braw ≤ c₀ε/(4K)` delivered at the
`≤ δ₀²` shape the terminals carry).  Then the `M`-floor obeys

    2304·K/(c₀ε)  ≤  (24·Cg/δ_sock)² ,

i.e. its SQUARE carries `K` LINEARLY, so the floor itself carries `√K` — against the split
floor `96·Cg/(c₀ε)`, in which `K` does not occur at all.  That single `√K` is the whole of
⟦REF-L2-ARITH⟧'s "unified ⟹ `b = 324` and the compose fails": at the landed `K ≈ 1.04e162`,
`√K` alone is 269 bits, and 65 + 269 overshoots the ceiling `m ≤ 86` by two hundred bits.

Only `1 ≤ Cg` is used on the constant — the weakest fact the door glue exports — so the
blow-up is not an artefact of any numeral. -/
theorem m4_doorL2_binder_floor_unified {Cg K c₀ε δsock : ℝ}
    (hCg : 1 ≤ Cg) (hK : 0 < K) (hc : 0 < c₀ε) (hδpos : 0 < δsock)
    (hprice : δsock ^ 2 ≤ c₀ε / (4 * K)) :
    2304 * K / c₀ε ≤ (24 * Cg / δsock) ^ 2 := by
  have hδ2 : (0 : ℝ) < δsock ^ 2 := by positivity
  have h4K : (0 : ℝ) < 4 * K := by linarith
  rw [le_div_iff₀ h4K] at hprice
  have hCg2 : (1 : ℝ) ≤ Cg ^ 2 := by nlinarith
  have hexp : (24 * Cg / δsock) ^ 2 = 576 * Cg ^ 2 / δsock ^ 2 := by
    field_simp
    ring
  rw [hexp, div_le_div_iff₀ hc hδ2]
  nlinarith [hprice, hc, hCg2, mul_le_mul_of_nonneg_right hCg2 hc.le]

/-- **⟦A1 — THE BINDER SPLIT, AS THE ROAD'S GRADE/BUDGET LEMMA⟧**
(`m4_doorL2_grade_split`).

The road's grade gate at **TWO NAMED THRESHOLDS**, which are two distinct parameters of this
statement and are never unified:

* `δ_sock` — the SOCKET-CEILING side.  It is the `∀`-bound `δ₀` of the terminals' ceiling
  conjunct (`m4_doorL2_socket_ceiling_at_sock`; the `ρ`-page's `doorRhoOfDelta δ_sock`), and
  it is read at the `√(c₀ε/(4K))`-genre threshold `hsockprice : δ_sock² ≤ c₀ε/(4K)`.  It is
  SYMBOLIC here — a parameter, never a numeral.
* `δ₀'` — the GLUE/`hMδ` side, the SPINE's own constant, read at `hspine : δ₀' ≤ c₀ε/4`.
  This is the only threshold `M4DoorGates.hMδ` ever sees.

⟦REF-L2-ARITH's A1, verbatim⟧: *"the socket's ceiling conjunct instantiates at
`δ_sock = √(c₀ε/4K) = 9.97e-85`; the spine's `hMδ` reads the glue `δ₀' = 1.19e-6` — 79
ORDERS apart, both free (`δ₀` `∀`-bound at all three landed sites).  **UNIFIED: `b = 324.18`
and the compose FAILS — the freeze's own fallback number arriving as a plumbing bug.**"*

THE SHARES (⟦REF-L2-ARITH⟧'s table, `1/2 + 1/8 + 1/8`): the socket leg takes `c₀ε/2`, the
glue `c₀ε/8`, the endpoint `c₀ε/8` — total `3c₀ε/4`, so the budget line closes STRICTLY with
a quarter of `c₀ε` to spare.  `l2_budget_line` (`M4Window.lean:635`) is what put the three
summands in this shape. -/
theorem m4_doorL2_grade_split {R : ChowlaRegime} {c₀ε K δ δsock δ₀' : ℝ} {Braw : ℕ → ℝ}
    {k : ℕ} (hc : 0 < c₀ε) (hK : 0 < K)
    -- ⟦THE SOCKET-CEILING SIDE — at `δ_sock`, and at `δ_sock` only⟧
    (hsock : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ δsock ^ 2)
    (hsockprice : δsock ^ 2 ≤ c₀ε / (4 * K))
    -- ⟦THE GLUE / `hMδ` SIDE — at the SPINE's `δ₀'`, and at `δ₀'` only⟧
    (hglue : δ ≤ δ₀') (hspine : δ₀' ≤ c₀ε / 4)
    -- ⟦the endpoint share⟧
    (hend : 8 * 2 ^ k / (R.x : ℝ) ≤ c₀ε / 8) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      2 * K * Braw H + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) < c₀ε := by
  intro H hlo hhi
  have hKne : K ≠ 0 := ne_of_gt hK
  have h2K : (0 : ℝ) < 2 * K := by linarith
  have hb : Braw H ≤ c₀ε / (4 * K) := le_trans (hsock H hlo hhi) hsockprice
  have hmul : 2 * K * Braw H ≤ 2 * K * (c₀ε / (4 * K)) :=
    mul_le_mul_of_nonneg_left hb h2K.le
  have heq : 2 * K * (c₀ε / (4 * K)) = c₀ε / 2 := by
    field_simp
    ring
  have h1 : 2 * K * Braw H ≤ c₀ε / 2 := by rw [heq] at hmul; exact hmul
  have h2 : δ / 2 ≤ c₀ε / 8 := by linarith
  linarith

/-! ## §3 — THE GRADE LINE TWIN: the `L²` replacement of the three-summand `L¹` gate

`M4Close.M4GradeGateSplit` (`:674`) reads

    √(Braw H) + δ/4 + 4·2^k/x  ≤  δ₀ .

Two things change on the `L²` route, and only these two:

1. **the `√` is GONE** — the Cauchy–Schwarz descent of `m4_hbd_of_live` (`:494`) is DELETED,
   because the socket is natively `L²` and the door is now read at the squared scale;
2. **the target is `c₀ε`, strictly** — the collision `contradiction_of_mrtDoorXiL2`
   (`MRTDoor.lean:225`) is `K`-free and asks for `ρ < c₀·ε` directly, so no `δ₀` and no
   `mrtDeliveredGrade` sits in between.

The three summands are otherwise THE SAME three, at the same places, with the same meanings.
`M4GradeGateSplit` is UNTOUCHED; this is a new name beside it. -/

/-- **THE `L²` GRADE GATE** (`M4GradeGateL2`) — the road-side successor of
`M4Close.M4GradeGateSplit` for ⟦THE L² RESTRUCTURE⟧: the freeze's budget line

    2·K·Braw H + δ/2 + 8·2^k/x  <  c₀·ε

at every window length in the regime's range.  `K` multiplies the socket grade ONLY; the
glue `δ` is `K`-FREE — that is the entire content of the restructure, and it is visible in
the statement.  Strict, because the seam it feeds (`contradiction_of_mrtDoorXiL2`) is. -/
def M4GradeGateL2 (R : ChowlaRegime) (c₀ε K δ : ℝ) (Braw : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
    2 * K * Braw H + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) < c₀ε

/-- **THE `L²` GRADE GATE, DISCHARGED FROM ⟦A1⟧** (`m4_gradeGateL2_of_binder_split`) — the
twin of `M4Close.m4_gradeGate_of_pricing_split` (`:686`) at the split binders.

Note what is NOT spent: no `m4Saving`, no `sqrt_m4Saving_le_delivered`, no `2 ≤ C` halving —
and, unlike the `L¹` twin, **no `Real.sqrt` at all**.  The socket ceiling is read directly at
`δ_sock²`, one full square cheaper than the `L¹` route's `(δ₀/2)²` (⟦REF-L2-ARITH⟧: "the
socket's ceiling stops being squared", the new ceiling `c₀ε/(4K) = δ₀_old/2`). -/
theorem m4_gradeGateL2_of_binder_split {R : ChowlaRegime} {c₀ε K δ δsock δ₀' : ℝ}
    {Braw : ℕ → ℝ} {k : ℕ} (hc : 0 < c₀ε) (hK : 0 < K)
    (hsock : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ δsock ^ 2)
    (hsockprice : δsock ^ 2 ≤ c₀ε / (4 * K))
    (hglue : δ ≤ δ₀') (hspine : δ₀' ≤ c₀ε / 4)
    (hend : 8 * 2 ^ k / (R.x : ℝ) ≤ c₀ε / 8) :
    M4GradeGateL2 R c₀ε K δ Braw k :=
  m4_doorL2_grade_split hc hK hsock hsockprice hglue hspine hend

/-- **THE GATE AT THE `H`-UNIFORM CEILING** (`m4_gradeGateL2_const`) — the door's grade `ρ`
is `H`-FREE (`MRTUniformityXiL2` takes a constant), so the gate is read once, at the
regime's own `H₋`.  `R.hHlohi` is the regime's non-vacuity field; nothing is assumed. -/
theorem m4_gradeGateL2_const {R : ChowlaRegime} {c₀ε K δ Bceil : ℝ} {k : ℕ}
    (hgate : M4GradeGateL2 R c₀ε K δ (fun _ => Bceil) k) :
    2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) < c₀ε :=
  hgate R.Hlo le_rfl R.hHlohi

/-! ## §4 — THE END-TO-END CHECK: the door-to-head seam

This section states the seam at the FREEZE's own budget line, `ρ < c₀·ε`, abstracted over the
head as `M4DoorL2HeadDemand`.  The shape is read off the landed pieces, not guessed:
`log_chowla_two_shell_xi_sq` (`Theorem23Shell.lean:361`, W1) consumes `MRTUniformityXiL2 R ρ`
together with `hbudget2 : ρ < c₀·ε` and nothing else about the door;
`contradiction_of_mrtDoorXiL2` (`MRTDoor.lean:225`) is `K`-free.  So the head's whole
door-facing surface is exactly the pair (door predicate, strict budget) — which is what §1
and §3 deliver.

⟦STATUS OF THE SIBLING⟧  W4's spine-side twins (`spine_False_core_xi_sq`,
`log_chowla_two_budget_head_g_sq(_count)` in `SpineFinal`, and the exit twins
`m4_exit_socket_split_sq(_arc)` in `S11ExitL2`) LANDED while this stone was in flight, so §5
below closes the loop against them for real, at their own threshold `δ₀ = c₀ε/4` (the head
took the freeze's `1/4` share into its constant; `δ₀ < c₀ε` and the two sections agree).
§4 is kept as the head-agnostic statement of the seam.

⟦THE SIX-STRUCTURE RESIDUE⟧  The S11 checklist's frames stay CARRIED: this file closes the
door-to-head seam, not the socket's own supply.  `M4SievedDoorSq` remains a hypothesis here
exactly as it is in `M4Close.m4_door_contradiction_of_live_split`, and the terminals'
band/cap/arith frames are untouched. -/

/-- **THE HEAD'S DOOR-FACING DEMAND** (`M4DoorL2HeadDemand`) — the shape the `L²` spine head
(freeze stone 4, sibling W4) presents to the road: a `Ξ`-summed `L²` door at ANY grade `ρ`
strictly under `c₀·ε` refutes the log-Chowla-2 failure branch.

`K`-FREE by construction — no `|Ξ_H| ≤ K` hypothesis appears, because the summed door already
carries the total over `Ξ_H` (`contradiction_of_mrtDoorXiL2`). -/
def M4DoorL2HeadDemand (R : ChowlaRegime) (c₀ε : ℝ) : Prop :=
  ∀ ρ : ℝ, MRTUniformityXiL2 R ρ → ρ < c₀ε → ¬ logChowla2Fails R.eps R.x R.ω

/-- **THE DOOR-TO-HEAD SEAM, VERIFIED** (`m4_doorL2_feeds_head`) — §1's door supply plus §3's
grade gate meet `M4DoorL2HeadDemand` with nothing left over.

⟦THE REGISTER⟧, and it is the landed `L¹` one with exactly two edits:

* `M4DoorGates Cg R M k δ` — UNCHANGED (M4-8's own list, `doorCount_gates` still the witness
  at `k := doorCount R.ω`);
* `0 ≤ Braw H` — UNCHANGED;
* `M4SievedDoorSq R M Braw` — UNCHANGED (the socket, at the band transport);
* `M4GradeGateL2 …` — REPLACES `M4GradeGateSplit`: the `√` deleted, the target `c₀ε`;
* `hXi`/`hK0`/`hceil` — NEW, and they are the count's only appearance on the whole route.

The proof is one application of the head's demand to §1's supply and §3's budget: that is
the seam, and it is the entire content of this theorem. -/
theorem m4_doorL2_feeds_head :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (Braw : ℕ → ℝ) (K Bceil c₀ε δ : ℝ) (M k : ℕ),
            M4DoorL2HeadDemand R c₀ε →
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) →
            0 ≤ K →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            M4GradeGateL2 R c₀ε K δ (fun _ => Bceil) k →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hsup⟩ := m4_doorL2_supply
  refine ⟨Cg, hCg, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := hsup eps heps
  refine ⟨H₀, ?_⟩
  intro R hReps hfloor Braw K Bceil c₀ε δ M k hhead hgates hBraw0 hsock hXi hK0 hceil hgate
  exact hhead _ (hH₀ R hReps hfloor Braw K Bceil δ M k hgates hBraw0 hsock hXi hK0 hceil)
    (m4_gradeGateL2_const hgate)

/-- **THE SEAM AT ⟦A1⟧, END TO END** (`m4_doorL2_feeds_head_split`) — the same seam with the
grade gate discharged from the SPLIT binders, so that the two thresholds `δ_sock` and `δ₀'`
appear as two distinct parameters of the top-level statement and the compose is closed
against them.

This is the theorem the `b`-floor ledger reads: `δ₀'` (and only `δ₀'`) meets
`M4DoorGates.hMδ`'s `24·Cg/δ ≤ M`, while `δ_sock` (and only `δ_sock`) meets the socket's
ceiling.  Unify them and `m4_doorL2_binder_floor_unified` says the `M`-floor picks up `√K`
— ⟦REF-L2-ARITH⟧'s "unified ⟹ `b = 324` and the compose fails". -/
theorem m4_doorL2_feeds_head_split :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (eps : ℚ), 0 < eps → ∃ H₀ : ℕ,
        ∀ (R : ChowlaRegime), R.eps = eps → H₀ ≤ R.Hlo →
          ∀ (Braw : ℕ → ℝ) (K c₀ε δ δsock δ₀' : ℝ) (M k : ℕ),
            M4DoorL2HeadDemand R c₀ε →
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
              ((bigXi R.eps H).card : ℝ) ≤ K) →
            0 < c₀ε → 0 < K →
            -- ⟦the socket-ceiling side — `δ_sock`⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ δsock ^ 2) →
            δsock ^ 2 ≤ c₀ε / (4 * K) →
            -- ⟦the glue / `hMδ` side — the spine's `δ₀'`⟧
            δ ≤ δ₀' → δ₀' ≤ c₀ε / 4 →
            -- ⟦the endpoint share⟧
            8 * 2 ^ k / (R.x : ℝ) ≤ c₀ε / 8 →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hseam⟩ := m4_doorL2_feeds_head
  refine ⟨Cg, hCg, ?_⟩
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := hseam eps heps
  refine ⟨H₀, ?_⟩
  intro R hReps hfloor Braw K c₀ε δ δsock δ₀' M k hhead hgates hBraw0 hsock hXi hc hK
    hceil hsockprice hglue hspine hend
  refine hH₀ R hReps hfloor Braw K (δsock ^ 2) c₀ε δ M k hhead hgates hBraw0 hsock hXi
    hK.le hceil ?_
  exact m4_gradeGateL2_of_binder_split (δsock := δsock) (δ₀' := δ₀') hc hK
    (fun _ _ _ => le_rfl) hsockprice hglue hspine hend

/-! ## §5 — THE LOOP CLOSED AGAINST THE LANDED HEAD

W4's `m4_exit_socket_split_sq_arc` (`S11ExitL2.lean:121`) is the road's handoff: it has
already absorbed the arc floor (`sum_bigXi_norm_windowExpSum_sq_le_twelve`, `B₅ = 12`,
unconditional) and the large-spectrum count (`log_chowla_two_budget_head_g_sq_count`'s
exported gate) into the regime, and it leaves open exactly four slots — `hsplit`, `hB0`,
`hsock`, `hins`, plus the budget `hρ`.

Three of those are the road's own data; the fourth, `hins`, is the Parseval stone's, and it
is the ONLY thing standing between bank A and a closed loop.  §5 supplies all four at the
road's actual coefficient sequence and hands the budget line over.

⟦THE SPELLING⟧  W4's `hins` slot is the `e`-spelling (`(1/H²)` INSIDE the `ξ`-sum, integrand
a window sum of the difference SEQUENCE); the Parseval stone's exit is the difference
spelling (`(1/H²)` OUTSIDE, integrand a DIFFERENCE OF TWO window sums).
`sum_bigXi_insert_spelling_eq` identifies them — the same identification
`sum_bigXi_norm_windowExpSum_sq_le_parseval` performs internally, here as a standalone stone
so the plug is byte-exact in both directions.  No new analysis.

⟦THE SIX-STRUCTURE RESIDUE, CARRIED⟧  What §5 does NOT close, and does not try to: the
socket's own supply.  `M4SievedDoorSq R M Braw` stays a hypothesis exactly as it is in
`M4Close.m4_door_contradiction_of_live_split`, and the terminals' band/cap/arith frames (the
S11 checklist) are untouched. -/

/-- **THE TWO INSERT SPELLINGS, IDENTIFIED** (`sum_bigXi_insert_spelling_eq`) — the `e`-form
of the insert energy (`M4Window`'s adapter and `S11ExitL2`'s `hins` slot) and the
difference-form (`parseval_insert_budget_door`'s exit) are the same real number.

`absWindowSum` is additive in its coefficient sequence (`absWindowSum_add_coeff`), so the
window sum of `λ − a` IS the difference of the window sums; `Finset.mul_sum` moves the
`(1/H²)` across the `ξ`-sum.  Analysis content: none. -/
theorem sum_bigXi_insert_spelling_eq (R : ChowlaRegime) (a : ℕ → ℂ) (H : ℕ) [NeZero H] :
    (∑ ξ ∈ bigXi R.eps H, (1 / (H : ℝ) ^ 2) *
        ∫ n, ‖absWindowSum (fun m => lamCoeff m - a m) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
          ∂(logMeasure R.x R.ω))
      = (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ bigXi R.eps H,
          ∫ n, ‖absWindowSum lamCoeff H n (-(ξ.val : ℝ) / (H : ℝ))
              - absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
            ∂(logMeasure R.x R.ω) := by
  have hsub : ∀ (n : ℕ) (α : ℝ),
      absWindowSum (fun m => lamCoeff m - a m) H n α
        = absWindowSum lamCoeff H n α - absWindowSum a H n α := by
    intro n α
    have h := absWindowSum_add_coeff a (fun m => lamCoeff m - a m) H n α
    have hfun : (fun m => a m + (lamCoeff m - a m)) = lamCoeff := funext fun m => by ring
    rw [hfun] at h
    rw [h]
    ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hsub]

/-- **THE LOOP, CLOSED** (`m4_doorL2_close_split_sq`) — ⟦THE L² RESTRUCTURE⟧'s door-to-head
seam, wired end to end against the landed `L²` head.

`ε`, the large-spectrum count `K` and the head's `K`-FREE threshold `δ₀` are fixed FIRST;
then for every extra floor / outer-scale demand there is a regime at which log-Chowla-2 does
not fail, conditional on exactly ⟦THE `L²` REGISTER⟧:

* `M4DoorGates Cg R M k δ` — M4-8's own list, **UNCHANGED** (`doorCount_gates` is still the
  witness at `k := doorCount R.ω`).  `Cg` is `parseval_insert_budget_door`'s opened constant.
* `0 ≤ Braw H` — UNCHANGED.
* `M4SievedDoorSq R M Braw` — UNCHANGED: the road's per-`α` `L²` socket at the band transport
  (⟦A2-5⟧).  This is the six-structure residue, carried, not closed.
* `Braw H ≤ Bceil` — NEW: the `H`-uniform ceiling that makes the door's grade `H`-free.
* `2·K·Bceil + δ/2 + 8·2^k/x ≤ δ₀` — **the freeze's budget line**, the `L²` successor of
  `M4GradeGateSplit`.  `K` multiplies the socket leg only; the glue `δ` is `K`-FREE.

⟦WHAT IS GONE relative to `m4_door_contradiction_of_live_split`⟧: the Cauchy–Schwarz descent
(`m4_hbd_of_live`'s `integral_logMeasure_le_sqrt_of_sq` step) and with it the `√` on the
socket grade — the socket's ceiling relaxes by a full square.

⟦A1⟧: the `δ` of `M4DoorGates.hMδ` here is the GLUE threshold `δ₀'`; the socket's ceiling
`Bceil` is priced at `δ_sock` (§2), and the two are never unified.  `m4_gradeGateL2_of_binder_split`
supplies the budget line from that split; `m4_doorL2_binder_floor_unified` says what happens
if they are not split. -/
theorem m4_doorL2_close_split_sq :
    ∃ (Cg : ℝ) (ε : ℚ) (K δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < K ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
            Real.log (Real.log (R.Hhi : ℝ))
              ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ ((9 : ℝ) / 2)) ∧
          ∀ (Braw : ℕ → ℝ) (Bceil δ : ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Braw H) →
            M4SievedDoorSq R M Braw →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ Bceil) →
            2 * K * Bceil + δ / 2 + 8 * 2 ^ k / (R.x : ℝ) ≤ δ₀ →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hpars⟩ := parseval_insert_budget_door
  obtain ⟨ε, K, δ₀, hε, hK, hδ₀, hexit⟩ := m4_exit_socket_split_sq_arc
  refine ⟨Cg, ε, K, δ₀, hCg, hε, hK, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hRtow, hR⟩ := hexit U1floor g
  refine ⟨R, hReps, hU1, hRg, hRtow, ?_⟩
  intro Braw Bceil δ M k hgates hBraw0 hsock hceil hbudget
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ 3072 * M := by
    have := hgates.hM
    omega
  have hHx : ∀ H : ℕ, H ≤ R.Hhi → H + 1 ≤ R.x := by
    intro H hhi
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  refine hR (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    (fun m => lamCoeff m - memSCoeff (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 2 liouvilleC m)
    Braw (δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) (fun m => by ring) hBraw0
    (hsock m4_bandTransport) ?_ ?_
  · -- ⟦THE FUSE⟧ the insert budget, from the Parseval stone, in W4's own spelling
    intro H _ hlo hhi
    rw [sum_bigXi_insert_spelling_eq R
      (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H]
    simp only [lamCoeff_eq_liouvilleC]
    exact hpars (Adoor M) (3072 * M) M 2 R.x R.ω H k liouvilleC δ (bigXi R.eps H)
      liouvilleC_norm_le_one hA hG hgates.hM hgates.hδ hgates.hMδ R.hx R.hω R.hωx
      hgates.hlogω (hHx H hhi) (hgates.hreach H hlo hhi) hgates.hpow hgates.hcount
      (hgates.hblocks H hlo hhi)
  · -- ⟦the budget line⟧ `l2_budget_line`, then the `H`-uniform ceiling on the socket leg
    intro H hlo hhi
    rw [l2_budget_line K (Braw H) δ (R.x : ℝ) k]
    have hmono : 2 * K * Braw H ≤ 2 * K * Bceil :=
      mul_le_mul_of_nonneg_left (hceil H hlo hhi) (by linarith)
    linarith

end Salt.MR

end
