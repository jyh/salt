/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.XCeil
import Salt.MR.S15SelLinear

/-!
# `KLever` — ⟦THE RAISED LEVER, THE `g`-RIDER, AND THE RE-CUT BASE-SCALE CAP⟧

⟦CAP-RECUT, 2026-08-02⟧  `XCeil` closed the `x`-window line and CAP-SCOPE ruled the verdict:
`S16BaseScaleCap96_L_gk` is **false at the flat terminal's own regime** when the lever is pinned
at `K = 32000000`, because the socket pins the base scale AT the endpoint and the Toll's landed
LOWER bound forces `loglog(endpoint) ≈ 10^{1.76·10^{95}}` against a cap RHS of `10^{9.6·10^6}`.
The Fable ruling is the composite **iii-B + iii-A**: re-cut the cap onto its ENDPOINT form (a
theorem, modulo a `g`-rider), move the door-vs-endpoint numeral into the consumer as an explicit
hypothesis, and RAISE THE LEVER so that the numeral is true.  This file is that repair's
arithmetic core.

## §1 — the dial

`kcap` is a **named design constant** (`:= 4`) and `KlevF A := ⌈kcap·e^{1.6A}⌉₊`.  Two budgets
meet at this dial and neither is comfortable:

* **the supply side** — the register hosts any `Klev ≤ 170000000·flatDoorM A`
  (`S15SelLinear.s15_sel''_L_gk_witness_flat`), i.e. `Klev ≲ 547.8·e^{1.6A}`.  At `kcap = 4`
  the margin is `137×`.
* **the demand side** — the cap numeral needs `kcap·log 2 > 2`, i.e. `kcap > 2.885`.  At
  `kcap = 4` the margin is `4·log 2/2 = 1.386×`.

The demand margin is the tight one: **one bad constant away**.  That is why the dial has a name
instead of being a numeral spelled inline.

## §2 — the `g`-rider

`XCeil.chowlaRegimeFlat_exists_param_head_ceiling` exports
`log R.x ≤ max ((31/ε)·H₊) (log (g H₊ ω))` — the outer-scale enlargement `x ↦ max x (g H₊ ω)`
means a caller who picks a huge `g` picks a huge outer scale, and no export can prevent it.
`chowlaRegimeFlat_exists_param_head_gceil` is the rider: a caller whose `g` obeys
`log (g H₊ ω) ≤ (31/ε)·H₊` gets the clean ceiling `log R.x ≤ (31/ε)·H₊`.

⟦THE HONEST COEFFICIENT⟧  The builder's own outer scale is
`log x ≤ (30/ε)·log H₊ + 2·log(P+1)`, and at the flat instantiation `P = 4^⌊ε²H₊⌋` the
`P`-term dominates: `log x ≈ 2·log 4·ε²·H₊ = 1.386·ε²·H₊`.  The rider's budget is
`31·H₊/ε`.  The ratio of admissible to constructed is therefore `31/(1.386·ε³) = 22.4/ε³`,
which at the terminal's `ε ≤ 1/500` is `≥ 2.8·10^9` — **nine orders in the coefficient**, not
four.  (The `4`-orders reading in the 0802 dossier addendum was a coefficient-only estimate; the
byte-read of `xceil_flat_P`/`xceil_flat_step` gives the figure above.)  Either way the builder's
own `x` sits far inside the rider, so the rider costs the terminal nothing it does not already
have — it is a constraint on the CALLER's `g`, and it must be stated.

## §3 — the re-cut cap

`S16BaseScaleCapEnd_L_gk R M` is the ENDPOINT form:

  `loglog(A + s) ≤ log H₊ + log(1/ε) + 5`   for every socket block.

It carries NO `K` — that is the whole point of the re-cut.  It is a THEOREM off the `x`-ceiling
(`s16_baseScaleCapEnd_L_of_xceil`), which is exactly the intermediate line of
`XCeil.s16_baseScaleCap96_L_of_xceil` with the lever's numeral peeled off.  What the lever then
has to buy is the single numeral

  `9.60000096·(log H₊ + log(1/ε) + 5) ≤ log 𝒫₂`,  `log 𝒫₂ = 3·2^{48+K}·M²·log 2`,

and `s16_baseScaleCap96_L_of_end` states it as an explicit hypothesis of the cap's consumer —
⟦iii-A⟧ in one lemma.

## §4 — the numeral, at the raised lever

`klevF_capNumeral` is the discharge's arithmetic.  Write `t := e^{1.6A}`.  From the terminal's
exported endpoint ceiling `loglog H₊ ≤ 2t`:

  LHS `≤ 9.60000096·(e^{2t} + 12) ≤ 19.2·e^{2t}`,
  RHS `≥ 2^{KlevF A}·log 2 ≥ e^{4t·log 2}·0.6931 = 0.6931·e^{2t}·e^{0.7724t}`,

and `e^{0.7724t} ≥ 0.7724·t ≥ 0.7724·10^{17}` closes it with room to spare.  The comparison
that matters is in the EXPONENT: `2t` (demand) against `kcap·log 2·t = 2.7724·t` (supply).
Everything else is slack.

`s16_baseScaleCap96_L_at_klevF` is the landing: at `K = KlevF A`, on the `x`-ceiling and the
endpoint ceiling, ⟦ITEM 3⟧ **is a theorem**.

## §5 — what is NOT here

The ~25 signature weakenings `hK : K ≤ 170000000 ⇝ K ≤ 170000000·M` along the L chain
(P2(b) of the CAP-RECUT brief) are NOT in this file; `calFrameK_doorH1_at_L_gk_kwide` below is
their ROOT (the `kwide` hop, deleted), and the flags entry names the chain.  The v4 terminal is
COMPOSE-2's.
-/

namespace Salt.Entropy.Chowla

/-! ## §2 — the `g`-rider on the flat builder's outer-scale ceiling -/

/-- **⟦THE `g`-RIDER⟧** (`chowlaRegimeFlat_exists_param_head_gceil`).
`XCeil.chowlaRegimeFlat_exists_param_head_ceiling` exports the ceiling in the `max` form
`log R.x ≤ max ((31/ε)·H₊) (log (g H₊ ω))`, because the outer-scale enlargement is
`x ↦ max x (g H₊ ω)`.  A caller whose `g` obeys the rider `log (g H₊ ω) ≤ (31/ε)·H₊` collapses
the `max` and gets the clean endpoint-only ceiling — the hypothesis
`XCeil.s16_baseScaleCap96_L_of_xceil` and `KLever.s16_baseScaleCapEnd_L_of_xceil` read.

The rider is a constraint on the CALLER, not on the builder: the builder's own `x` satisfies
`log x ≈ 1.386·ε²·H₊`, some `22.4/ε³ ≥ 2.8·10^9` times inside the rider's budget at
`ε ≤ 1/500`. -/
theorem chowlaRegimeFlat_exists_param_head_gceil (A : ℝ) (hA : 26 ≤ A) (eps : ℚ)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ Hhi ω : ℕ, Real.log ((g Hhi ω : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * (Hhi : ℝ)) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  obtain ⟨R, hReps, hRA, hRHlo, hRg, hRcap, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_head_ceiling A hA eps heps heps1 Hlo₀ g
  refine ⟨R, hReps, hRA, hRHlo, hRg, hRcap, hRwid, ?_⟩
  refine le_trans hRx ?_
  exact max_le (le_refl _) (hg R.Hhi R.ω)

end Salt.Entropy.Chowla

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — ⟦THE DIAL⟧ `kcap` and `KlevF` -/

/-- **⟦THE LEVER'S DESIGN CONSTANT⟧** (`kcap`).  The coefficient of the raised lever
`KlevF A = ⌈kcap·e^{1.6A}⌉₊`.

**Budget: `kcap ≤ 547`.**  The `M`-selection register hosts any `Klev ≤ 170000000·flatDoorM A`
(`S15SelLinear.s15_sel''_L_gk_witness_flat`), and `flatDoorM A = ⌊e^{1.6A}/310301⌋`, so the
register's own ceiling is `≈ 547.85·e^{1.6A}`.  At `kcap = 4` the supply margin is `137×`.

**Floor: `kcap·log 2 > 2`, i.e. `kcap > 2.885`.**  The cap numeral compares
`loglog H₊ ≤ 2·e^{1.6A}` (demand) against `K·log 2 ≈ kcap·log 2·e^{1.6A}` (supply); at
`kcap = 4` the demand-side coefficient margin is `4·log 2/2 = 1.386×`.

The floor is the tight side — ONE bad constant away — which is why this is a named dial and not
an inline numeral. -/
def kcap : ℕ := 4

/-- **⟦THE RAISED LEVER⟧** (`KlevF`).  `KlevF A = ⌈kcap·e^{1.6A}⌉₊`, the lever at the flat
design point.  Replaces the pinned `K = 32000000`, whose cap conditional CAP-SCOPE proved
vacuous at the flat regime. -/
noncomputable def KlevF (A : ℝ) : ℕ := ⌈(kcap : ℝ) * Real.exp (1.6 * A)⌉₊

/-- `e^{1.6A} = e^{3.2A/2}` — the bridge to `S15SelLinear`'s spelling of the design point. -/
theorem exp_sixteen_eq (A : ℝ) : Real.exp (1.6 * A) = Real.exp (3.2 * A / 2) := by
  congr 1
  ring

/-- The lever is at least `kcap·e^{1.6A}` (the ceiling's defining property). -/
theorem KlevF_ge (A : ℝ) : (kcap : ℝ) * Real.exp (3.2 * A / 2) ≤ ((KlevF A : ℕ) : ℝ) := by
  rw [KlevF, ← exp_sixteen_eq]
  exact Nat.le_ceil _

/-- The lever is at most `kcap·e^{1.6A} + 1`. -/
theorem KlevF_lt (A : ℝ) :
    ((KlevF A : ℕ) : ℝ) < (kcap : ℝ) * Real.exp (3.2 * A / 2) + 1 := by
  rw [KlevF, ← exp_sixteen_eq]
  exact Nat.ceil_lt_add_one (by positivity)

/-- **⟦THE LEVER IS ADMISSIBLE⟧** (`KlevF_le_wideCeiling`).  `KlevF A ≤ 170000000·flatDoorM A`
at every `A ≥ 26` — the WIDE ceiling the linear door and the `M`-selection register both carry
(`DoorLinear.calFrameK_satisfiable_doorL_gk`, `S15SelLinear.s15_sel''_L_gk_witness_flat`).

The accounting: `flatDoorM A ≥ e^{1.6A}/310301 − 1` and `170000000/310301 ≥ 547`, so the
register hosts `547·e^{1.6A}` while the lever asks for `4·e^{1.6A} + 1` — a `137×` margin,
uniform in `A`. -/
theorem KlevF_le_wideCeiling {A : ℝ} (hA : 26 ≤ A) :
    KlevF A ≤ 170000000 * flatDoorM A := by
  have ht : (10 : ℝ) ^ 17 ≤ Real.exp (3.2 * A / 2) := flat_exp_half_ge hA
  have hMge : Real.exp (3.2 * A / 2) / 310301 - 1 ≤ ((flatDoorM A : ℕ) : ℝ) :=
    flatDoorM_ge A
  have hlt := KlevF_lt A
  have hkc : ((kcap : ℕ) : ℝ) = 4 := by rw [kcap]; norm_num
  rw [hkc] at hlt
  -- work in the rescaled variable `u = e^{1.6A}/310301`
  set u : ℝ := Real.exp (3.2 * A / 2) / 310301 with hudef
  have htu : Real.exp (3.2 * A / 2) = 310301 * u := by
    rw [hudef]; field_simp
  have hu : (100000 : ℝ) ≤ u := by
    rw [hudef, le_div_iff₀ (by norm_num : (0 : ℝ) < 310301)]
    nlinarith [ht]
  have hreal : ((KlevF A : ℕ) : ℝ) ≤ ((170000000 * flatDoorM A : ℕ) : ℝ) := by
    have hcast : ((170000000 * flatDoorM A : ℕ) : ℝ)
        = 170000000 * ((flatDoorM A : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    rw [htu] at hlt
    linarith [hMge, hlt, hu]
  exact_mod_cast hreal

/-! ## §3 — ⟦THE RE-CUT⟧ the base-scale cap in ENDPOINT form -/

/-- **⟦ITEM 3, RE-CUT ONTO THE ENDPOINT⟧** (`S16BaseScaleCapEnd_L_gk`).  The base-scale cap
with the lever's numeral peeled off: the socket's block scale `A + s` is capped by the
REGIME's own endpoint, not by `𝒫₂`.

It carries no `K` and no `M`-dependence beyond the socket's own — which is why it is a theorem
(off the outer-scale ceiling) where the `K`-shaped `S16BaseScaleCap96_L_gk` is not. -/
def S16BaseScaleCapEnd_L_gk (R : ChowlaRegime) (M : ℕ) : Prop :=
  ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
    Real.log (Real.log (((A + s : ℕ)) : ℝ))
      ≤ Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5

/-- **⟦THE ENDPOINT FORM IS A THEOREM⟧** (`s16_baseScaleCapEnd_L_of_xceil`), modulo the
`g`-rider that `XCeil` §2 names and `chowlaRegimeFlat_exists_param_head_gceil` discharges.

This is exactly the intermediate line of `XCeil.s16_baseScaleCap96_L_of_xceil`: the socket puts
`A + s ≤ 3·R.x` (`RegisterSupply.s16_baseScaleCap96_L_of_xwindow`'s reduction), the ceiling puts
`log(3x) ≤ (32/ε)·H₊`, hence `loglog(3x) ≤ log H₊ + log(1/ε) + log 32 ≤ log H₊ + log(1/ε) + 5`.
No lever appears anywhere. -/
theorem s16_baseScaleCapEnd_L_of_xceil {R : ChowlaRegime} {M : ℕ}
    (hx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) :
    S16BaseScaleCapEnd_L_gk R M := by
  have hHhiN : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhiN
  have hHhipos : (0 : ℝ) < ((R.Hhi : ℕ) : ℝ) := by linarith
  have hepsR : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have h2q : (2 : ℚ) * R.eps ≤ 1 := by linarith [R.heps1]
  have h2r : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by exact_mod_cast h2q
  have hupos : (0 : ℝ) < 1 / (R.eps : ℝ) := div_pos one_pos hepsR
  have hu2 : (2 : ℝ) ≤ 1 / (R.eps : ℝ) := by rw [le_div_iff₀ hepsR]; linarith
  have hx2 : (2 : ℝ) ≤ ((R.x : ℕ) : ℝ) := by exact_mod_cast R.hx
  have hxpos : (0 : ℝ) < ((R.x : ℕ) : ℝ) := by linarith
  have hbig : (2 : ℝ) * 4000000 ≤ 1 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) :=
    mul_le_mul hu2 hHhiR (by norm_num) (le_of_lt hupos)
  -- `loglog(3x) ≤ log H₊ + log(1/ε) + 5` (XCeil's intermediate line)
  have hbr31 : (31 : ℝ) / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)
      = 31 * (1 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) := by ring
  have hbr32 : (32 : ℝ) / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)
      = 32 * (1 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) := by ring
  have hlog3 : Real.log 3 ≤ 2 := by
    have h : Real.log (3 : ℝ) ≤ Real.log ((2 : ℝ) ^ (2 : ℕ)) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith [Real.log_two_lt_d9]
  have hstep : Real.log (3 * ((R.x : ℕ) : ℝ)) ≤ 32 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)]
    linarith [hx, hbig, hlog3, hbr31, hbr32]
  have hlogpos : (1 : ℝ) < Real.log (3 * ((R.x : ℕ) : ℝ)) := by
    have h1 : Real.exp 1 < 3 * ((R.x : ℕ) : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.log (Real.exp 1) < Real.log (3 * ((R.x : ℕ) : ℝ)) :=
      Real.log_lt_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hll : Real.log (Real.log (3 * ((R.x : ℕ) : ℝ)))
      ≤ Real.log (32 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) :=
    Real.log_le_log (by linarith) hstep
  have heq : Real.log (32 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
      = Real.log 32 + Real.log (1 / (R.eps : ℝ)) + Real.log ((R.Hhi : ℕ) : ℝ) := by
    rw [hbr32, Real.log_mul (by norm_num)
        (mul_ne_zero (ne_of_gt hupos) (ne_of_gt hHhipos)),
      Real.log_mul (ne_of_gt hupos) (ne_of_gt hHhipos)]
    ring
  have hlog32 : Real.log 32 ≤ 5 := by
    have h : Real.log ((32 : ℝ)) = Real.log ((2 : ℝ) ^ (5 : ℕ)) := by norm_num
    rw [h, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hcap3x : Real.log (Real.log (3 * ((R.x : ℕ) : ℝ)))
      ≤ Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5 := by
    linarith [hll, heq.le, heq.ge, hlog32]
  -- the socket's own step `A + s ≤ 3·R.x`
  intro H L q j A s hb
  have h2 : H ≤ R.Hhi := hb.2.1
  have h3 : L ≤ H := hb.2.2.1
  have h8 : 0 < A := hb.2.2.2.2.2.2.2.1
  have h12 : (A : ℝ) ≤ 2 * (R.x : ℝ) := hb.2.2.2.2.2.2.2.2.2.2.2.1
  have h13 : s ≤ L := hb.2.2.2.2.2.2.2.2.2.2.2.2
  have hω : 0 < R.ω := lt_of_lt_of_le (by norm_num) R.hω
  have hhead : R.Hhi * R.ω ≤ R.x := (Nat.le_div_iff_mul_le hω).mp R.hheadroom
  have hsHhi : (s : ℝ) ≤ (R.Hhi : ℝ) := by
    have hs : s ≤ R.Hhi := le_trans h13 (le_trans h3 h2)
    exact_mod_cast hs
  have hHhile : (R.Hhi : ℝ) ≤ (R.x : ℝ) := by
    have hstep2 : R.Hhi ≤ R.x := le_trans (Nat.le_mul_of_pos_right _ hω) hhead
    exact_mod_cast hstep2
  have hsum : (((A + s : ℕ)) : ℝ) ≤ 3 * (R.x : ℝ) := by push_cast; linarith
  have hA1 : (1 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have : 1 ≤ A + s := by omega
    exact_mod_cast this
  have hlogA0 : (0 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_nonneg hA1
  have hRnn : (0 : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5 := by
    have h1 : (0 : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) := Real.log_nonneg (by linarith)
    have h2' : (0 : ℝ) ≤ Real.log (1 / (R.eps : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  by_cases hsmall : Real.log (((A + s : ℕ)) : ℝ) ≤ 1
  · have hle0 : Real.log (Real.log (((A + s : ℕ)) : ℝ)) ≤ 0 :=
      Real.log_nonpos hlogA0 hsmall
    linarith
  · have hbigA : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith [not_le.mp hsmall]
    have hApos : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by linarith
    have hstepA : Real.log (((A + s : ℕ)) : ℝ) ≤ Real.log (3 * ((R.x : ℕ) : ℝ)) :=
      Real.log_le_log hApos hsum
    have hllA : Real.log (Real.log (((A + s : ℕ)) : ℝ))
        ≤ Real.log (Real.log (3 * ((R.x : ℕ) : ℝ))) :=
      Real.log_le_log (by linarith) hstepA
    linarith

/-- **⟦iii-A IN ONE LEMMA⟧** (`s16_baseScaleCap96_L_of_end`).  The door-vs-endpoint numeral,
stated EXPLICITLY: the `K`-shaped cap follows from the `K`-free endpoint cap plus the single
inequality

  `9.60000096·(log H₊ + log(1/ε) + 5) ≤ log 𝒫₂`.

Every consumer of `S16BaseScaleCap96_L_gk` — `s16_capGate_supply_L_gk` and, through it,
`s16_budget_field_L_gk_96` — is served by this without any edit to its own statement. -/
theorem s16_baseScaleCap96_L_of_end (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    (hend : S16BaseScaleCapEnd_L_gk R M)
    (hnum : 9.60000096 * (Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5)
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) :
    S16BaseScaleCap96_L_gk K R M := by
  intro H L q j A s hb
  have h := hend H L q j A s hb
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 9.60000096)]
  nlinarith [h, hnum]

/-! ## §4 — ⟦THE NUMERAL AT THE RAISED LEVER⟧ -/

/-- **⟦THE NUMERAL⟧** (`klevF_capNumeral`).  At `K = KlevF A` the door-vs-endpoint numeral is a
THEOREM, on the terminal's own exported endpoint ceiling `loglog H₊ ≤ 2·e^{1.6A}` and its own
`ε ≥ 1/500`.

The comparison is in the exponent: with `t := e^{1.6A} ≥ 10^{17}`,

  demand  `9.60000096·(log H₊ + log(1/ε) + 5) ≤ 9.6·(e^{2t} + 12) ≤ 19.2·e^{2t}`
  supply  `log 𝒫₂ ≥ 2^{KlevF A}·log 2 ≥ 0.6931·e^{4t·log 2} = 0.6931·e^{2t}·e^{0.7724·t}`

so the whole question is `2 < kcap·log 2 = 2.7724` — the `1.386×` coefficient margin the dial's
docstring names — and the residual factor `e^{0.7724·t} ≥ 0.7724·10^{17}` is pure slack. -/
theorem klevF_capNumeral {A : ℝ} (hA : 26 ≤ A) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (heps500 : (1 : ℚ) / 500 ≤ R.eps)
    (hHhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    9.60000096 * (Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5)
      ≤ Real.log ((calP (AdoorL M) (s13GK (KlevF A) M) 2 : ℕ) : ℝ) := by
  set t : ℝ := Real.exp (3.2 * A / 2) with htdef
  have ht17 : (10 : ℝ) ^ 17 ≤ t := flat_exp_half_ge hA
  have ht0 : (0 : ℝ) < t := by nlinarith [ht17]
  have htbig : (100000000 : ℝ) ≤ t := by nlinarith [ht17]
  -- ⟦THE DEMAND SIDE⟧
  have hHhiN : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhiN
  have hepsR : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hupos : (0 : ℝ) < 1 / (R.eps : ℝ) := div_pos one_pos hepsR
  have h5q : (1 : ℚ) ≤ 500 * R.eps := by linarith
  have h5r : (1 : ℝ) ≤ 500 * (R.eps : ℝ) := by exact_mod_cast h5q
  have hinv500 : 1 / (R.eps : ℝ) ≤ 500 := by rw [div_le_iff₀ hepsR]; linarith
  have hinvle : Real.log (1 / (R.eps : ℝ)) ≤ 7 := by
    have h : Real.log (1 / (R.eps : ℝ)) ≤ Real.log ((2 : ℝ) ^ (9 : ℕ)) := by
      refine Real.log_le_log hupos ?_
      rw [show ((2 : ℝ) ^ (9 : ℕ)) = 512 by norm_num]
      linarith
    rw [Real.log_pow] at h
    push_cast at h
    linarith [Real.log_two_lt_d9]
  have hlogHhipos : (0 : ℝ) < Real.log ((R.Hhi : ℕ) : ℝ) := by
    have h : Real.log 1 < Real.log ((R.Hhi : ℕ) : ℝ) :=
      Real.log_lt_log one_pos (by linarith)
    simpa using h
  have hlogHhi_le : Real.log ((R.Hhi : ℕ) : ℝ) ≤ Real.exp (2 * t) := by
    calc Real.log ((R.Hhi : ℕ) : ℝ)
        = Real.exp (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) := (Real.exp_log hlogHhipos).symm
      _ ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr hHhi
  have hexp2t : (2 : ℝ) * t + 1 ≤ Real.exp (2 * t) := Real.add_one_le_exp (2 * t)
  have hexp2t_big : (100 : ℝ) ≤ Real.exp (2 * t) := by linarith [htbig, hexp2t]
  -- ⟦THE SUPPLY SIDE⟧ `log 𝒫₂ = 4·(AdoorL M · 𝒢K)·log 2 ≥ 2^K·log 2`
  have hlog2lo : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hAd : 1 ≤ AdoorL M := one_le_AdoorL hM
  have hnat : 2 ^ (KlevF A) ≤ 4 * (AdoorL M * s13GK (KlevF A) M) := by
    have h1 : 2 ^ (KlevF A) ≤ s13GK (KlevF A) M := by
      rw [s13GK]
      calc 2 ^ (KlevF A) ≤ 3072 * 2 ^ (KlevF A) := Nat.le_mul_of_pos_left _ (by norm_num)
        _ ≤ 3072 * 2 ^ (KlevF A) * M := Nat.le_mul_of_pos_right _ (by omega)
    calc 2 ^ (KlevF A) ≤ s13GK (KlevF A) M := h1
      _ ≤ AdoorL M * s13GK (KlevF A) M := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ 4 * (AdoorL M * s13GK (KlevF A) M) := Nat.le_mul_of_pos_left _ (by norm_num)
  have hnatR : (2 : ℝ) ^ (KlevF A) ≤ ((4 * (AdoorL M * s13GK (KlevF A) M) : ℕ) : ℝ) := by
    have h : ((2 ^ (KlevF A) : ℕ) : ℝ) ≤ ((4 * (AdoorL M * s13GK (KlevF A) M) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa using h
  have h2K : (2 : ℝ) ^ (KlevF A) = Real.exp (((KlevF A : ℕ) : ℝ) * Real.log 2) := by
    conv_rhs => rw [← Real.log_pow]
    exact (Real.exp_log (by positivity)).symm
  have hKge : (4 : ℝ) * t ≤ ((KlevF A : ℕ) : ℝ) := by
    have h := KlevF_ge A
    have hkc : ((kcap : ℕ) : ℝ) = 4 := by rw [kcap]; norm_num
    rw [hkc, ← htdef] at h
    exact h
  have hKlog : 2 * t + 0.7724 * t ≤ ((KlevF A : ℕ) : ℝ) * Real.log 2 := by
    nlinarith [hKge, hlog2lo, ht0]
  have hsplit : Real.exp (2 * t + 0.7724 * t) = Real.exp (2 * t) * Real.exp (0.7724 * t) :=
    Real.exp_add _ _
  have hexpres : (100 : ℝ) ≤ Real.exp (0.7724 * t) := by
    have h := Real.add_one_le_exp (0.7724 * t)
    nlinarith [h, htbig]
  have hpow_lo : (69 : ℝ) * Real.exp (2 * t) ≤ (2 : ℝ) ^ (KlevF A) * Real.log 2 := by
    have hchain : Real.exp (2 * t) * Real.exp (0.7724 * t) ≤ (2 : ℝ) ^ (KlevF A) := by
      rw [h2K, ← hsplit]
      exact Real.exp_le_exp.mpr hKlog
    have hexp2pos : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
    have hmul : Real.exp (2 * t) * 100 ≤ Real.exp (2 * t) * Real.exp (0.7724 * t) :=
      mul_le_mul_of_nonneg_left hexpres (le_of_lt hexp2pos)
    have hstep1 : (100 : ℝ) * Real.exp (2 * t) ≤ (2 : ℝ) ^ (KlevF A) := by
      linarith [hchain, hmul]
    have h2Knn : (0 : ℝ) ≤ (2 : ℝ) ^ (KlevF A) := by positivity
    have hstep2 : 100 * Real.exp (2 * t) * 0.6931 ≤ (2 : ℝ) ^ (KlevF A) * Real.log 2 :=
      mul_le_mul hstep1 hlog2lo (by norm_num) h2Knn
    linarith [hstep2, hexp2pos]
  -- ⟦THE CLOSE⟧
  rw [s16_logP2]
  have hcast : ((4 * (AdoorL M * s13GK (KlevF A) M) : ℕ) : ℝ) * Real.log 2
      ≥ (2 : ℝ) ^ (KlevF A) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hnatR (by linarith)
  linarith [hlogHhi_le, hinvle, hpow_lo, hcast, hexp2t_big]

/-- **⟦THE DISCHARGE⟧** (`s16_baseScaleCap96_L_at_klevF`) — ⟦ITEM 3⟧ AT THE RAISED LEVER IS A
THEOREM.  On the two ceilings the flat builder exports (the outer-scale ceiling of `XCeil` §2,
under the `g`-rider; and the endpoint ceiling `loglog H₊ ≤ 2·e^{1.6A}` the flat width law
gives), plus the terminal's own `ε ≥ 1/500`, the base-scale cap holds at `K = KlevF A`.

This is what CAP-SCOPE's verdict asked for: the cap is FALSE at `K = 32000000` and TRUE at
`K = KlevF A`, and the two are separated by exactly the coefficient comparison
`2 < kcap·log 2`. -/
theorem s16_baseScaleCap96_L_at_klevF {A : ℝ} (hA : 26 ≤ A) {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) (heps500 : (1 : ℚ) / 500 ≤ R.eps)
    (hx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
    (hHhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S16BaseScaleCap96_L_gk (KlevF A) R M :=
  s16_baseScaleCap96_L_of_end (KlevF A) (s16_baseScaleCapEnd_L_of_xceil hx)
    (klevF_capNumeral hA hM heps500 hHhi)

/-! ## §4b — ⟦THE CAP GATE ON THE RE-CUT ROUTE⟧ -/

/-- **⟦THE CAP GATE, ENDPOINT-ROUTED⟧** (`s16_capGate_supply_L_gk_end`) — the additive twin of
`S13CapGateLinear.s16_capGate_supply_L_gk` whose base-scale input is the `K`-FREE endpoint cap
plus the explicit door-vs-endpoint numeral.  Statement otherwise verbatim; the landed original
is untouched and remains every current consumer's route. -/
theorem s16_capGate_supply_L_gk_end (K : ℕ) {Cq cs T₀ Kq Ks C : ℝ} {R : ChowlaRegime} {M : ℕ}
    {epsf : ℕ → ℝ}
    (hM : 1 ≤ M) (hfl : loglogFloor50 ≤ R.Hlo) (hcs : Real.exp (-100) ≤ cs)
    (hblk : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s)
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hεr : ∀ A : ℕ, theta293 - 1 / 500 ≤ epsf A)
    (hend : S16BaseScaleCapEnd_L_gk R M)
    (hnum : 9.60000096 * (Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5)
      ≤ Real.log ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ))
    (hcof : S16CofactorSupply_L_gk K Cq R M) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGatePerBlock_L_gk K Cq cs T₀ Kq Ks C M (A + s) q P Q H (2 * T)
            Rrad Rbd CR EP2 (epsf (A + s)) :=
  s16_capGate_supply_L_gk K hM hfl hcs hblk hT₀ hKq hKs hC0 hC hεr
    (s16_baseScaleCap96_L_of_end K hend hnum) hcof

/-- **⟦THE CAP GATE AT THE RAISED LEVER⟧** (`s16_capGate_supply_L_gk_klevF`) — the same gate at
`K = KlevF A`, with BOTH cap inputs discharged from the flat builder's two exported ceilings.
This is the ingredient the v4 terminal reads in place of the (vacuous) `K = 32000000` route. -/
theorem s16_capGate_supply_L_gk_klevF {A : ℝ} (hA : 26 ≤ A)
    {Cq cs T₀ Kq Ks C : ℝ} {R : ChowlaRegime} {M : ℕ} {epsf : ℕ → ℝ}
    (hM : 1 ≤ M) (hfl : loglogFloor50 ≤ R.Hlo) (hcs : Real.exp (-100) ≤ cs)
    (hblk : ∀ H L q j A' s : ℕ, SocketBaseL R M H L q j A' s →
      s13BlockFloor_L_gk (KlevF A) M ≤ A' + s)
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) (hC0 : 0 < C) (hC : Real.log C ≤ 40)
    (hεr : ∀ A' : ℕ, theta293 - 1 / 500 ≤ epsf A')
    (heps500 : (1 : ℚ) / 500 ≤ R.eps)
    (hx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
    (hHhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2))
    (hcof : S16CofactorSupply_L_gk (KlevF A) Cq R M) :
    ∀ H L q j A' s : ℕ, SocketBaseL R M H L q j A' s →
      ∀ T : ℝ, (((A' + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A' + s : ℕ)) : ℝ) → TannGate (((A' + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGatePerBlock_L_gk (KlevF A) Cq cs T₀ Kq Ks C M (A' + s) q P Q H (2 * T)
            Rrad Rbd CR EP2 (epsf (A' + s)) :=
  s16_capGate_supply_L_gk (KlevF A) hM hfl hcs hblk hT₀ hKq hKs hC0 hC hεr
    (s16_baseScaleCap96_L_at_klevF hA hM heps500 hx hHhi) hcof

/-! ## §5 — ⟦THE `kwide` HOP, DELETED⟧ — the root lives in `ThmA2Linear` beside its original;
here is only its flat-design-point specialization. -/

/-- The wide frame at the flat design point, at the RAISED lever — the exact instance the v4
terminal reads. -/
theorem calFrameK_doorH1_at_L_gk_flat {A : ℝ} (hA : 26 ≤ A) (Xd : ℕ)
    (hXd : calQK (AdoorL (flatDoorM A)) (s13GK (KlevF A) (flatDoorM A)) (flatDoorM A) 2 ≤ Xd) :
    CalFrameK (1 / 12) (H1doorL (flatDoorM A)) (AdoorL (flatDoorM A))
      (s13GK (KlevF A) (flatDoorM A)) (flatDoorM A) 2 Xd :=
  calFrameK_doorH1_at_L_gk_kwide (KlevF A) (flatDoorM A) Xd (flatDoorM_one_le hA)
    (KlevF_le_wideCeiling hA) hXd

end Salt.MR
