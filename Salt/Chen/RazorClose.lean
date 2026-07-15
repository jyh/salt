/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.CbarCert

/-!
# SW4 — the razor assembly: `hledger` at the certified constants

Design: `docs/blueprints/chen.md` (the SW4 PRE-DESIGN row + THE H-GLUE discharge map) and
`docs/blueprints/flags.md` (`2026-07-14 ★★ THE END-TO-END RE-GATE`, `FPC`, `A2W`).  This file is
the **numeric close of the entire Chen arc**: it discharges the last conjunct of the
`chen_of_hypotheses` package (`Salt/Chen/Assembly.lean`),

  `hledger : 0 < mainA1 − mainA2/2 − mainA3/2 − Real.log x · x/(z−1)/2`,

at the certified per-carrier constants, so the H-glue can hand `hledger_at_certs`'s output straight
to `chen_positivity`.

## The honest stack (the re-gate's Row-B factor trace, at the certified constants)

All three carriers are normalised by the shared F6 carrier constant `X_W = Π₂ x/(4 log z)`
(equivalently `X_W = totalMass · W(twinA1Sieve) = Λmass · V(z)`, the Mertens-3rd value the H-glue
supplies).  Normalising the landed carrier bounds by `X_W`:

* **A₁** `mainA1/X_W ≥ 9779/10000 − (ε-slack + BV strip)`.
  Certified value: `fchain N s ≥ 9779/10000` on `[3.9992, 4]` (`SuperClose.fchain_A1_final`),
  fed through `TwinSharp.twin_A1_lower_B`.  Honest number `0.9779` (Row-A) / `0.9777` (Row-B, after
  the ε·CsharpB·e²·hBJS slack).
* **A₂** `½·mainA2/X_W ≤ ½·(3 + Cmass)·(log 6 / 4) + (O(1/log z) error)`.
  From `A2Weighted.A2grid_sharp_le` at the mass budget `Cmass` (frozen `Cmass ≤ 43/75`,
  `SuperClose.massSum_le_A2_final`; the sharp `≈ 0.56309`, `A2Weighted.massSum_le_A2_sharp`, only
  improves the margin), fed through `TwinA2.twin_A2_upper`.  With `log 6 ≤ 17917596/10⁷`
  (`LogToolkit.log_two_le + log_three_le`) this is `≤ 0.800319` (frozen) / `≤ 0.798028` (sharp).
* **A₃** `½·mainA3/X_W ≤ ½·c̄·(3/8)·(243/100) + (O(1/log z) error)`.
  The re-gate's `½·(log x · tripleSum/totalMass)·(W_y/W_z)·Fchain_switch`: the count
  `log x · tripleSum/totalMass → c̄` (`CountFinal.tripleSum_le_cbar_final`,
  `CbarCert.cbar_lt : c̄ < 363084/10⁶`), the W-ratio `W_y/W_z = 3/8` (`WRatioSharp.W_ratio_upper`),
  the switch value `Fchain_switch ≤ 243/100` (`FchainPoint.Fchain_switch_le`), fed through
  `SwitchSieve.mainA3_of_hBVswitch` / `SwitchBlocks.mainA3_of_block_remainders`.  Value
  `< 0.165430`.
* **strip** `Real.log x · x/(z−1)/(2 X_W) → 0` (it is `x^{7/8} log x`-scale against the
  `x/log x`-scale `X_W`; `x ≳ e^{100}` already kills it, per the re-gate).

Certified scalar margin (`razor_scalar_margin`):
`0.9779 − 0.800319 − 0.165430 = 0.012151 ≥ 1/100 > 0` (frozen; sharp gives `+0.01444`).  Any of the
per-carrier slacks + the strip are `O(1/log z)`, so at a large enough operating threshold `x₀` their
bundle `E` is `≤ 1/200 < 1/100 ≤ M`, and the razor is strictly positive.

## What is SW4 vs. what is the H-glue

SW4 owns the **numeric arithmetic** — the certified scalar margin (genuinely consuming `cbar_lt` and
the `LogToolkit` log sandwiches) and its lift to the razor.  The **normalisation chain** — pinning
`totalMass·W(twinA1Sieve) = X_W = Π₂ x/(4 log z)` (Mertens 3rd) and discharging the per-carrier
normalised bounds (`hmA1`/`hmA2`/`hmA3`/`hstrip`) + the error-bundle threshold (`hE`, i.e. `x ≥ x₀`)
from the landed carrier lemmas — is the H-glue's `GLU-1/GLU-2` job (it aligns the shared `X_W`
across carriers and fixes `x₀`).  `razor_of_normalized` is the general symbolic razor at that
boundary;
`hledger_at_certs` is it, specialised to the certified constants.

No `sorry`, no `native_decide`, no new axioms.  `razor_scalar_margin` consumes `cbar_lt`
(`CbarCert`), `log_two_le`/`log_three_le` (`LogToolkit`) and `cbar` (`SwitchConstant`) only.
-/

namespace Salt.Chen

open Real

/-! ## Part A — the certified scalar margin (the numeric heart)

The pure real-number inequality `0 < 9779/10000 − ½·(3+43/75)·(log 6/4) − ½·c̄·(3/8)·(243/100)`,
proved from the landed value certs.  This is where SW4's numeric content lives: it genuinely
consumes `cbar_lt` (the 600-panel switch-constant certificate) and the `LogToolkit` Taylor log
sandwiches. -/

/-- **`log 6 ≤ 17917596/10⁷`** — from `log 6 = log 2 + log 3` and the `LogToolkit` sandwiches
`log 2 ≤ 6931472/10⁷`, `log 3 ≤ 10986124/10⁷`.  True value `1.79175947…`. -/
theorem log_six_le : Real.log 6 ≤ 17917596 / 10000000 := by
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h6]; linarith [log_two_le, log_three_le]

/-- **The certified scalar razor margin.**  At the frozen A₂ mass budget `43/75`, the razor's
normalised constant stack is bounded below by `1/100`:

  `1/100 ≤ 9779/10000 − ½·(3 + 43/75)·(log 6/4) − ½·c̄·(3/8)·(243/100)`.

The three carriers' certified values enter literally: `9779/10000` (A₁ `fchain`), `(3+43/75)·log6/4`
(A₂ grid mass·`(log 6)/4`), and `c̄·(3/8)·(243/100)` (A₃ count·W-ratio·switch-`Fchain`).  Upper
bounding `log 6` (`log_six_le`) and `c̄` (`cbar_lt`) — both increasing the subtracted terms — gives
the lower bound `0.012151 ≥ 1/100` (frozen; the sharp A₂ mass `≈ 0.56309` only widens it to
`0.01444`). -/
theorem razor_scalar_margin :
    (1 : ℝ) / 100
      ≤ 9779 / 10000 - (3 + 43 / 75) * (Real.log 6 / 4) / 2
          - cbar * (3 / 8) * (243 / 100) / 2 := by
  have hlog6 : Real.log 6 ≤ 17917596 / 10000000 := log_six_le
  have hcbar : cbar ≤ 363084 / 1000000 := le_of_lt cbar_lt
  nlinarith [hlog6, hcbar, cbar_pos]

/-! ## Part B — the symbolic razor at named normalised bounds (FLOOR A)

Given the three carriers and the strip normalised against a common positive `X_W`, with the
normalised numeric margin strictly exceeding the total normalised error, the razor is positive.
Pure algebra — the boundary between SW4 and the H-glue. -/

/-- **`razor_of_normalized` — the composed symbolic razor.**  With a shared positive normalisation
`XW`, per-carrier normalised bounds

  `XW·(a1lo − e1) ≤ mainA1`,  `mainA2 ≤ XW·(a2hi + e2)`,  `mainA3 ≤ XW·(a3hi + e3)`,
  `S ≤ XW·e4`,

and the margin condition `e1 + e2/2 + e3/2 + e4/2 < a1lo − a2hi/2 − a3hi/2`, the razor
`mainA1 − mainA2/2 − mainA3/2 − S/2` is strictly positive.  `S` is the strip carrier. -/
theorem razor_of_normalized {XW mainA1 mainA2 mainA3 S a1lo a2hi a3hi e1 e2 e3 e4 : ℝ}
    (hXW : 0 < XW)
    (hmargin : e1 + e2 / 2 + e3 / 2 + e4 / 2 < a1lo - a2hi / 2 - a3hi / 2)
    (hmA1 : XW * (a1lo - e1) ≤ mainA1)
    (hmA2 : mainA2 ≤ XW * (a2hi + e2))
    (hmA3 : mainA3 ≤ XW * (a3hi + e3))
    (hstrip : S ≤ XW * e4) :
    0 < mainA1 - mainA2 / 2 - mainA3 / 2 - S / 2 := by
  -- the normalised gap is strictly positive
  have hD : 0 < (a1lo - a2hi / 2 - a3hi / 2) - (e1 + e2 / 2 + e3 / 2 + e4 / 2) := by linarith
  have hpos : 0 < XW * ((a1lo - a2hi / 2 - a3hi / 2) - (e1 + e2 / 2 + e3 / 2 + e4 / 2)) :=
    mul_pos hXW hD
  -- expand the gap into the four carrier pieces
  have hexpand : XW * ((a1lo - a2hi / 2 - a3hi / 2) - (e1 + e2 / 2 + e3 / 2 + e4 / 2))
      = XW * (a1lo - e1) - XW * (a2hi + e2) / 2 - XW * (a3hi + e3) / 2 - XW * e4 / 2 := by ring
  rw [hexpand] at hpos
  -- the carrier bounds dominate the gap termwise
  linarith [hmA1, hmA2, hmA3, hstrip, hpos]

/-! ## Part C — `hledger_at_certs`: the FULL close (H-package-compatible)

The symbolic razor specialised to the certified constants.  The conclusion is *exactly* the
`hledger` conjunct of `chen_of_hypotheses` (`Salt/Chen/Assembly.lean`). -/

/-- **`hledger_at_certs` — the razor at the certified constants (the SW4 endpoint).**  For any
shared positive normalisation `XW = X_W`, given the per-carrier normalised certified bounds

* `XW·(9779/10000 − e1) ≤ mainA1`   (A₁ `fchain` cert, minus its ε/BV slack `e1`),
* `mainA2 ≤ XW·((3 + 43/75)·(log 6/4) + e2)`   (A₂ grid at the frozen mass, `+ O(1/log z)` `e2`),
* `mainA3 ≤ XW·(c̄·(3/8)·(243/100) + e3)`   (A₃ count·W-ratio·switch, `+` its `O(1/log z)` `e3`),
* `Real.log x · x/(z−1) ≤ XW·e4`   (the negligible prime-power strip),

and the error-bundle threshold `e1 + e2/2 + e3/2 + e4/2 ≤ 1/200` (the honest home of the operating
threshold `x ≥ x₀`: all four errors are `O(1/log z)`, so the bundle is `≤ 1/200` beyond some `x₀`),
the ledger closes:

  `0 < mainA1 − mainA2/2 − mainA3/2 − Real.log x · x/(z−1)/2`.

The certified scalar margin `razor_scalar_margin` (`≥ 1/100`, genuinely consuming `cbar_lt` and the
`LogToolkit` log sandwiches) beats the `1/200` error bundle with `1/100 > 1/200` to spare. -/
theorem hledger_at_certs {x z : ℕ} {XW mainA1 mainA2 mainA3 e1 e2 e3 e4 : ℝ}
    (hXW : 0 < XW)
    (hE : e1 + e2 / 2 + e3 / 2 + e4 / 2 ≤ 1 / 200)
    (hmA1 : XW * (9779 / 10000 - e1) ≤ mainA1)
    (hmA2 : mainA2 ≤ XW * ((3 + 43 / 75) * (Real.log 6 / 4) + e2))
    (hmA3 : mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100) + e3))
    (hstrip : Real.log x * (x : ℝ) / ((z : ℝ) - 1) ≤ XW * e4) :
    0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2 := by
  refine razor_of_normalized (a1lo := 9779 / 10000)
    (a2hi := (3 + 43 / 75) * (Real.log 6 / 4)) (a3hi := cbar * (3 / 8) * (243 / 100))
    hXW ?_ hmA1 hmA2 hmA3 hstrip
  -- the error bundle (≤ 1/200) is below the certified margin (≥ 1/100)
  have hM := razor_scalar_margin
  linarith [hE, hM]

end Salt.Chen
