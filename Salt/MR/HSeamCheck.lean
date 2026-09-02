/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S16FlatTerminalExitH
import Salt.MR.S16ProducersH

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
    {Kc : ℝ} (hKc : 0 < Kc) (hKcb : Kc ≤ 2 ^ 539) {Hhi ω : ℕ} (hHhi : 4000000 ≤ Hhi)
    (hΛ : 50 ≤ Real.log (Real.log ((Hhi : ℕ) : ℝ))) : True := by
  have hh : 0 < h := by omega
  obtain ⟨Cg, ε, Kb, δ₀, A, β, Hcap, Hopq, hCg, hCgle, hε, hKb, hδ₀, hεpin, hδpin, hβ,
    hA162, hA₀A, hAge, hCapLe, hmain⟩ :=
      m4_second_road_L2_H_gk_flatRoot_L_exit h hh K A₀ hA₀
  -- ⟦THE SEAM⟧ the exit's own `δ₀`-pin, handed straight to the arm estimate at shift `h`
  have _harm := s15ArmH_log_le hh hh7 hδ₀ hδpin hKc hKcb (Hhi := Hhi) (ω := ω) hHhi hΛ
  -- and the `Cg` cap that word 1 restored is exported too, so the selector's bump is reachable
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

end Salt.MR

end
