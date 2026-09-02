/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalExitH
import Salt.MR.S16ProducersH
import Salt.MR.S16FlatTerminalLinearLH

/-!
# ⟦THE SEAM, CLOSED BY CONSTRUCTION⟧ — wave H1's acceptance integration

Waves P (`#18`) and X (`#19`) both landed green, both fully audited, and **did not compose at
`h ≥ 2`**: P's own `s15ArmH_log_le` demanded the `h = 1` pin `1/838400 ≤ δ₀` while X's exit can
only export `1/(838400·h²) ≤ δ₀` — and X's is FORCED (the head takes `δ₀ = cD3/(16C)·ε/4` with
`C ≤ 6.55·h` and `ε = 1/(500·h)`, so `δ₀ ≍ h⁻²`).  Both numerals sat in HYPOTHESES of
conditional statements, so **no gate in this repository could see it**: the kernel checks
theorems, not that they compose.

This file is the check that CAN see it, and it is the wave's acceptance item.  §1 is the
integration `example` at a SYMBOLIC `h ≥ 2`: it takes the exit's own exported `δ₀`-pin and feeds
it, unmodified, to the respelled arm estimate.  If either side's numeral drifts again, THIS FILE
STOPS COMPILING — the seam is closed by construction, not by inspection.

§2 is the selector layer's `h`-handle: wave H1 generalised
`s15_sel''_L_gk_witness_flat_bumped_win` (and the four lemmas beneath it) over a shift scale
`c`, so the `h`-twin is the instance `c := h`; this wrapper names it for wave H2 rather than
making every consumer re-derive `h ≤ 1096` from `hh7`.

§3 is wave H2b's acceptance: the flat-linear terminal `logChowla2_witnessed_scale_flat_LH` fired
at a CONCRETE `h = 2`, reading its `Kc ≤ 2^539` out of the theorem's own conjunct rather than
assuming it, plus the two new defs' `h = 1` twin laws.

⛔ **WHAT §3 DELIBERATELY DOES NOT CLAIM.**  `S16BandLaneCBoundedL K → S16BandLaneCBoundedLH 2 K`
is NOT asserted anywhere, and is not true in general: the rider's socket sits in HYPOTHESIS
position, so the inflated form is the STRONGER Prop and the implication runs the other way.  A
consumer at `h ≥ 2` must be handed the `LH` rider; the `h = 1` twin law is the only bridge, and
it is an `↔` at `h = 1` only.

Nothing here bears on twin primes: every object is conditional exactly where its `h = 1` twin is.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE INTEGRATION CHECK, AT A SYMBOLIC `h ≥ 2` -/

/-- **⟦THE SEAM CLOSES⟧** — the acceptance integration of wave H1.

At a symbolic `h ≥ 2` the exit register `m4_second_road_L2_H_gk_flatRoot_L_exit` exports
`1/(838400·h²) ≤ δ₀`, and `s15ArmH_log_le` — respelled in place by word 2 — DEMANDS exactly
that.  The `have` below is the composition: the pin travels from producer to consumer with no
adapter, no `le_trans`, no numeral in between.

⛔ Before word 2 this `example` did not elaborate at any `h ≥ 2`, and NOTHING in the repository
reported that: both statements were green, audited and merged.  The `h = 1` instantiation cannot
discriminate it either — at `h = 1` the two pins are the same numeral. -/
example (h : ℕ) (hh2 : 2 ≤ h) (hh7 : Real.log (h : ℝ) ≤ 7) (K : ℕ) (A₀ : ℝ) (hA₀ : 162 ≤ A₀)
    {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) : True := by
  have hh : 0 < h := by omega
  obtain ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hKbb, hδ₀, hεpin, hδpin, hβ,
    hA162, hA₀A, hAge, hCapLe, hmain⟩ :=
      m4_second_road_L2_H_gk_flatRoot_L_exit h hh hh7 K A₀ hA₀
  -- ⟦THE SEAM⟧ the exit's own `δ₀`-pin AND its own count constant `Kb`, handed straight to the
  -- arm estimate at shift `h`.  ⭐ Wave H2a word 1(e) STRENGTHENED this check: `Kc ≤ 2^539` used
  -- to be a free hypothesis of the example; it is now OBTAINED from the exit, so the seam is
  -- verified on the constant the road actually carries rather than on an assumed one.
  have _harm := s15ArmH_log_le hh hh7 hδ₀ hδpin hKb hKbb (Hhi := Hhi) (ω := ω) hHhi hΛ
  -- and the `Cg` cap that H1 word 1 restored is exported too, so the selector's bump is reachable
  have _hcap : Cg ≤ 2 * 10 ^ 12 := hCgle
  trivial

/-! ## §2 — THE SELECTOR LAYER'S `h`-HANDLE -/

/-- **⟦THE BUMPED WINDOWED SELECTOR AT SHIFT `h`⟧** (`s15_sel''_L_gk_witness_flat_bumped_win_h`)
— `FlatFloorBump.s15_sel''_L_gk_witness_flat_bumped_win` at `c := h`.

Wave H1 did not build four separate `h`-twins of the selector layer: it threaded ONE shift scale
`c` through `s15_sel''_L_witness_flat`, `s15_sel''_L_gk_witness_flat`, `flat_blk_line_gk`,
`s15_sel''_L_witness_flat_charge`, `s15_sel''_L_witness_flat_wide`,
`s15_sel''_L_gk_witness_flat_wide`, `flatDoorM_bfloor_bump` and the two bumped selectors, so the
landed lane is `c = 1` and the `h` lane is `c = h`.  The shift enters in exactly three places —
the `ε`-floor as `c` (`1/(2^9·c) ≤ R.eps`), the `δ₀`-pin as `c²`, and the `ρ`-charge as
`2·log c` — and every margin is stated at `c ≤ 1096`.  ⭐ The `Cg` bump is re-routed through
`flatDoorM_ge_pow355` (`2^355 ≈ 7.3·10^106`) because the landed `flatDoorM_ge_bfloorConst`
(`4.02432·10^19`, ZERO slack) cannot carry the `c²`; at `c ≤ 1096` the demand is
`4.84·10^25` and it clears by 81 orders. -/
theorem s15_sel''_L_gk_witness_flat_bumped_win_h {A : ℝ} (hA : 162 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {h : ℕ} (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7)
    {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / (838400 * (h : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hCg : Cg ≤ 2 * 10 ^ 12) (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (h : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) :=
  s15_sel''_L_gk_witness_flat_bumped_win (c := h) hA Klev hKle hh
    (h_le_1096_of_hh7 hh hh7) hh7 hδ hδb hK hKb hCt hCtb hCg hMfl hx0win heps hlo hhi

/-! ## §3 — WAVE H2b's ACCEPTANCE: THE FLAT-LINEAR TERMINAL AT A CONCRETE `h = 2` -/

/-- **⟦THE `h` TERMINAL FIRES AT `h = 2`⟧** — wave H2b's acceptance item.

The three hops are conditional statements whose shift is symbolic; an `example` at a CONCRETE
`h = 2` is what checks that the chain's numerals actually admit a shift, rather than merely
type-checking at a variable that no consumer instantiates.  Two things are read at the object:
the `ε` pin `1/(500·2) ≤ ε` and the count ceiling **`Kc ≤ 2^539`, OBTAINED from the theorem's
own conjunct** — at `h = 1` that ceiling is an ASSUMED rider of the landed terminal, and on the
`h` lane it is a fact, because the shift forced the count to be computed. -/
example (hband : S16BandLaneCBoundedLH 2 32000000) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) : True := by
  have hcast : (((2 : ℕ)) : ℝ) = 2 := by norm_num
  have hh7 : Real.log (((2 : ℕ)) : ℝ) ≤ 7 := by
    rw [hcast]; linarith [Real.log_two_lt_d9]
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hopq, Mfl, _hε, _hCg, _hKc, _hδ₀, _hCt, _hMfl1,
    _hCgle, hεpin, hδpin, _hMflb, hKcb, _hβ, _hA26, _hA₀A, _hAge, _hcensus, _hbody⟩ :=
    logChowla2_witnessed_scale_flat_LH 2 (by norm_num) hh7 hband A₀ hA₀
  -- ⟦THE COUNT CEILING IS A FACT HERE, NOT A RIDER⟧
  have _hKb : Kc ≤ 2 ^ 539 := hKcb
  -- ⟦THE TWO PINS AT h = 2, read as the theorem states them⟧
  have _heps : 1 / (500 * ((2 : ℕ) : ℚ)) ≤ ε := hεpin
  have _hδ : 1 / (838400 * (((2 : ℕ)) : ℝ) ^ 2) ≤ δ₀ := hδpin
  trivial

/-- **⟦THE `h = 1` INSTANCE TAKES THE LANDED RIDER⟧** — the spot-check word 10 asks for.  A
caller who holds the LANDED `S16BandLaneCBoundedL 32000000` can enter the `h` terminal at
`h = 1` through the twin law, and gets back the landed `ε`/`δ₀` pins (`1/500`, `1/838400`). -/
example (hband : S16BandLaneCBoundedL 32000000) (A₀ : ℝ) (hA₀ : 162 ≤ A₀) : True := by
  have hh7 : Real.log (((1 : ℕ)) : ℝ) ≤ 7 := by norm_num
  obtain ⟨ε, Cg, Kc, δ₀, Ct, A, β, x₀, Hopq, Mfl, _hε, _hCg, _hKc, _hδ₀, _hCt, _hMfl1,
    _hCgle, hεpin, _hδpin, _hMflb, _hKcb, _hβ, _hA26, _hA₀A, _hAge, _hcensus, _hbody⟩ :=
    logChowla2_witnessed_scale_flat_LH 1 (by norm_num) hh7
      ((s16BandLaneCBoundedLH_one_iff 32000000).mpr hband) A₀ hA₀
  have _heps : 1 / 500 ≤ ε := by
    have := hεpin; norm_num at this; linarith
  trivial

/-- The band-lane rider at `h = 1` IS the landed rider. -/
example (K : ℕ) : S16BandLaneCBoundedLH 1 K ↔ S16BandLaneCBoundedL K :=
  s16BandLaneCBoundedLH_one_iff K

/-- The crossing rider at `h = 1` IS the landed crossing rider. -/
example (K : ℕ) (R : ChowlaRegime) (M : ℕ) :
    S15CrossingBound_LH_gk 1 K R M ↔ S15CrossingBound_L_gk K R M :=
  s15CrossingBound_LH_gk_one_iff K R M

end Salt.MR

end
