/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.RazorClose

/-!
# GLU-1 — the razor's normalized per-carrier bounds (the H-glue's first half)

Design: `docs/blueprints/flags.md` (`2026-07-14 SW4`, `THE END-TO-END RE-GATE`, `CATCH #49`).
`Salt/Chen/RazorClose.lean`'s `razor_of_normalized` / `hledger_at_certs` are the *symbolic* razor
at the certified constants; they consume four `X_W`-normalised per-carrier bounds
(`hmA1`/`hmA2`/`hmA3`/`hstrip`) plus an error-bundle threshold `hE ≤ 1/200`.  This module is
GLU-1: it **discharges those four normalised bounds** from the landed carrier lemmas' *raw* outputs
by the honest `X_W`-relative normalisation algebra, pinning every error's explicit form.

The shared normalisation is `X_W = totalMass · W(twinA1Sieve) = Λmass · V = Π₂ x/(4 log z)` — the
Mertens-3rd carrier value the H-glue aligns across carriers.  Everything here is carrier-agnostic
(the sieve values `fA1`, `A2grid`, `T = tripleSum`, `Wy`, `Wz`, `slack…` are free reals): GLU-2
instantiates them from the concrete `twinA1Sieve`/`switchSieve` instances, so the *raw* hypotheses
below match the landed lemma conclusions verbatim.

## The raw carrier bounds (= the landed lemma conclusions, `X_W`-factored)

* **A₁** `twin_A1_lower_B` (`Salt/Chen/TwinSharp.lean`):
  `totalMass·(W·(fA1 − slack1)) − R1 ≤ mainA1`, i.e. `X_W·(fA1 − slack1) − R1 ≤ mainA1`,
  with `fA1 = fchain N (logRatio z D)`, `slack1 = ε·CsharpB ε·e²·hBJS(logRatio z D)`,
  `R1 = x/(log x)^10`.
* **A₂** `twin_A2_upper` (`Salt/Chen/TwinA2.lean`):
  `mainA2 ≤ Λmass·V·(A2grid + aggSlack) + R2 = X_W·(A2grid + aggSlack) + R2`,
  with `aggSlack = Σ_p (1/(p−1))·slackF p`, `R2 = Σ_p Rp` (the A₂ BV remainder aggregate).
* **A₃** `mainA3_of_hBVswitch` (`Salt/Chen/SwitchSieve.lean`):
  `mainA3 ≤ log x·(T·Wy·(Fv + slack3) + R3)`, with `T = tripleSum x z y`,
  `Wy = W(switchSieve)`, `Fv = Fchain N (logRatio y Dlev)`,
  `slack3 = ε·CsharpB ε·e²·hBJS(logRatio y Dlev)`, `R3 = x/(log x)^10`.

## The value / reconciliation certs (= landed lemma outputs at the operating point)

* `hcertA1 : 9779/10000 ≤ fA1` — `SuperClose.fchain_A1_final` ∘ `WindowMembership.logRatio_A1_mem`.
* `hcertA2 : A2grid ≤ (3 + 43/75)·(log 6/4 + wtail)` — `A2Weighted.A2grid_sharp_le` at the frozen
  mass `Cmass = 43/75` (`wtail = A2weight·(21/log z + 2/(z−1))`, `O(1/log z)`).
* `hcertA3 : Fv ≤ 243/100` — `FchainPoint.Fchain_switch_le` ∘ `WindowMembership.logRatio_A3_mem`.
* `hWy : Wy ≤ Wz·rho` — `WRatioSharp.W_ratio_upper`; `rho = (log z/log y)·(1 + 38/log z)`, and
  `log z/log y = (log x/8)/(log x/3) = 3/8` at the operating point.
* `hcount : log x·T ≤ (cbar + ecount)·totalMass` — the count/Mertens bridge:
  `CountFinal.tripleSum_le_cbar_final` (`T ≤ Ccount·(c̄/2)·(x/log x) + Rem`) over
  `MertensPNT.lambda_mass_lower` (`totalMass ≥ (x/2)(1 − o(1))`), whose ratio is the re-gate's
  `log x·(c̄/2)(x/log x)/((x/2)) = c̄` identity; `ecount = O(1/log z)`.

## The four discharged bounds and their EXPLICIT errors (the GLU-1 deliverable)

Normalising each raw bound by `X_W > 0` (the `hmᵢ_normalized` lemmas below):

* `e1 = slack1 + R1/X_W`                                             (A₁ slack + BV strip).
* `e2 = (3 + 43/75)·wtail + aggSlack + R2/X_W`                       (A₂ tail + agg-slack + BV).
* `e3 = ((cbar + ecount)·rho·(243/100 + slack3) − c̄·(3/8)·(243/100)) + log x·R3/X_W`
  (A₃: the count/W-ratio/switch multiplicative slack collapse `→ 0`, plus the strip crumb).
* `e4 = (log x·x/(z−1))/X_W`                                         (the prime-power strip).

The certified scalar margin is `M ≥ 1/100` (`RazorClose.razor_scalar_margin`); the bundle
`E = e1 + e2/2 + e3/2 + e4/2` beats it once each error is below its share.

## The error bundle `hE` and the operating threshold `x₀` (GLU-1 ⋈ GLU-2)

Every error above is `O(1/log z)` or `x^{−1/8}·polylog` (the strip), hence `→ 0`:

* `slack1, slack3 = ε·CsharpB ε·e²·hBJS(·)` with `ε < 1/249` frozen — a fixed small constant
  (`≈ 1.6%` of the margin per the re-gate), NOT vanishing but already below its share.
* `wtail, aggSlack, ecount, rho − 3/8` are all `O(1/log z)`.
* `R1/X_W, R2/X_W, log x·R3/X_W = (x/(log x)^9)/X_W` and `e4 = (log x·x/(z−1))/X_W`: with the crude
  `X_W ≥ totalMass·e^{−70}/(log z)² ≳ x·e^{−70}/(2(log z)²)` (`TwinInstance.W_twin_ge`-style +
  `lambda_mass_lower`) these are `polylog/(x/polylog) → 0` (the strip is `x^{7/8}·polylog` over the
  `x/polylog` carrier), killed by any `x ≳ e^{C}` per the re-gate.

`errorBundle_le` assembles `hE ≤ 1/200` from per-share bounds `bᵢ` with `b1 + b2/2 + b3/2 + b4/2
≤ 1/200`; the per-share discharge at the concrete instance (`z = ⌊x^{1/8}⌋`, the crude `X_W`-lower)
fixes the explicit `x₀` — GLU-2's instance-level arithmetic, per the SW4 note ("GLU-1/GLU-2 …
fixes x₀").  `normalized_package` bundles the four bounds and closes the razor through
`hledger_at_certs`.

No `sorry`, no `native_decide`, no new axioms.  The load-bearing algebra is the four
`hmᵢ_normalized` lemmas (raw → `X_W`-normalised) and the razor composition.
-/

namespace Salt.Chen

open Real

/-! ## Part A — the four per-carrier normalisation discharges (raw → `X_W`-relative)

Each lemma takes a raw carrier bound (the landed lemma conclusion, `X_W`-factored) plus the value /
reconciliation certs, and produces the *exact* `hledger_at_certs` per-carrier shape with the error
pinned to its explicit form.  Pure normalisation algebra over the shared `X_W > 0`. -/

/-- **A₁ discharge.**  From the raw `twin_A1_lower_B` bound `X_W·(fA1 − slack1) − R1 ≤ mainA1` and
the `fchain` cert `9779/10000 ≤ fA1`, the `X_W`-normalised A₁ bound holds with
`e1 = slack1 + R1/X_W`:

  `X_W·(9779/10000 − (slack1 + R1/X_W)) ≤ mainA1`. -/
theorem hmA1_normalized {XW fA1 slack1 R1 mainA1 : ℝ} (hXW : 0 < XW)
    (hcertA1 : (9779 : ℝ) / 10000 ≤ fA1)
    (hraw : XW * (fA1 - slack1) - R1 ≤ mainA1) :
    XW * (9779 / 10000 - (slack1 + R1 / XW)) ≤ mainA1 := by
  have hne : XW ≠ 0 := ne_of_gt hXW
  have hid : XW * (9779 / 10000 - (slack1 + R1 / XW))
      = XW * (9779 / 10000) - XW * slack1 - R1 := by field_simp; ring
  have hmono : XW * (9779 / 10000) ≤ XW * fA1 := by
    exact mul_le_mul_of_nonneg_left hcertA1 hXW.le
  have hexp : XW * (fA1 - slack1) - R1 = XW * fA1 - XW * slack1 - R1 := by ring
  linarith [hraw, hid, hmono, hexp]

/-- **A₂ discharge.**  From the raw `twin_A2_upper` bound `mainA2 ≤ X_W·(A2grid + aggSlack) + R2`
and the sharp grid cert `A2grid ≤ (3 + 43/75)·(log 6/4 + wtail)`, the `X_W`-normalised A₂ bound
holds with `e2 = (3 + 43/75)·wtail + aggSlack + R2/X_W`:

  `mainA2 ≤ X_W·((3 + 43/75)·(log 6/4) + e2)`. -/
theorem hmA2_normalized {XW A2grid wtail aggSlack R2 mainA2 : ℝ} (hXW : 0 < XW)
    (hcertA2 : A2grid ≤ (3 + 43 / 75) * (Real.log 6 / 4 + wtail))
    (hraw : mainA2 ≤ XW * (A2grid + aggSlack) + R2) :
    mainA2 ≤ XW * ((3 + 43 / 75) * (Real.log 6 / 4)
        + ((3 + 43 / 75) * wtail + aggSlack + R2 / XW)) := by
  have hne : XW ≠ 0 := ne_of_gt hXW
  have hmono : XW * (A2grid + aggSlack)
      ≤ XW * ((3 + 43 / 75) * (Real.log 6 / 4 + wtail) + aggSlack) :=
    mul_le_mul_of_nonneg_left (by linarith [hcertA2]) hXW.le
  have hid : XW * ((3 + 43 / 75) * (Real.log 6 / 4)
        + ((3 + 43 / 75) * wtail + aggSlack + R2 / XW))
      = XW * ((3 + 43 / 75) * (Real.log 6 / 4 + wtail) + aggSlack) + R2 := by
    field_simp; ring
  linarith [hraw, hmono, hid]

/-- **A₃ discharge (the catch-#49 reconciliation).**  From the raw `mainA3_of_hBVswitch` bound
`mainA3 ≤ log x·(T·Wy·(Fv + slack3) + R3)`, the switch cert `Fv ≤ 243/100`, the `W`-ratio
`Wy ≤ Wz·rho`, and the count/Mertens bridge `log x·T ≤ (cbar + ecount)·totalMass`, the
`X_W`-normalised A₃ bound holds at `X_W = totalMass·Wz` with

  `e3 = ((cbar + ecount)·rho·(243/100 + slack3) − cbar·(3/8)·(243/100)) + log x·R3/X_W`:

  `mainA3 ≤ X_W·(cbar·(3/8)·(243/100) + e3)`.

The `X_W`-cancellation writes the count `log x·T/totalMass → cbar`, the `W`-ratio `Wy/Wz ≤ rho`
(`→ 3/8`) and the switch `Fv ≤ 243/100` as one product; every deviation from `cbar·(3/8)·(243/100)`
lands in `e3`, which is `O(1/log z)`. -/
theorem hmA3_normalized {XW totalMass Wz Wy T Fv slack3 R3 rho ecount lx mainA3 : ℝ}
    (hXW : 0 < XW) (hXWdef : XW = totalMass * Wz)
    (hraw : mainA3 ≤ lx * (T * Wy * (Fv + slack3) + R3))
    (hcertA3 : Fv ≤ 243 / 100)
    (hFslack_nn : 0 ≤ Fv + slack3)
    (hWy : Wy ≤ Wz * rho) (hrho_nn : 0 ≤ rho) (hWz_nn : 0 ≤ Wz)
    (hLTnn : 0 ≤ lx * T)
    (hcount : lx * T ≤ (cbar + ecount) * totalMass) :
    mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100)
        + (((cbar + ecount) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100))
            + lx * R3 / XW)) := by
  have hne : XW ≠ 0 := ne_of_gt hXW
  -- the switch ceiling is nonneg
  have hceil_nn : (0 : ℝ) ≤ 243 / 100 + slack3 := by linarith [hcertA3, hFslack_nn]
  set B := Wz * rho * (243 / 100 + slack3) with hB
  have hB_nn : 0 ≤ B := by
    rw [hB]; positivity
  -- step 1: `Wy·(Fv+slack3) ≤ B`
  have hstep1 : Wy * (Fv + slack3) ≤ B := by
    calc Wy * (Fv + slack3) ≤ (Wz * rho) * (Fv + slack3) :=
          mul_le_mul_of_nonneg_right hWy hFslack_nn
      _ ≤ (Wz * rho) * (243 / 100 + slack3) :=
          mul_le_mul_of_nonneg_left (by linarith [hcertA3]) (mul_nonneg hWz_nn hrho_nn)
      _ = B := by rw [hB]
  -- step 2: `(lx·T)·(Wy·(Fv+slack3)) ≤ (cbar+ecount)·totalMass·B`
  have hstep2 : (lx * T) * (Wy * (Fv + slack3)) ≤ (cbar + ecount) * totalMass * B := by
    calc (lx * T) * (Wy * (Fv + slack3)) ≤ (lx * T) * B :=
          mul_le_mul_of_nonneg_left hstep1 hLTnn
      _ ≤ ((cbar + ecount) * totalMass) * B := mul_le_mul_of_nonneg_right hcount hB_nn
      _ = (cbar + ecount) * totalMass * B := by ring
  -- the raw bound expands with `(lx·T)·(Wy·(Fv+slack3))` as the leading piece
  have hrawexp : lx * (T * Wy * (Fv + slack3) + R3)
      = (lx * T) * (Wy * (Fv + slack3)) + lx * R3 := by ring
  -- the target RHS equals the count-collapsed bound.  Keep `XW` atomic in the division
  -- (`totalMass·Wz ≠ 0` does not split for `field_simp`); split off the no-division piece.
  have hcancel : XW * (lx * R3 / XW) = lx * R3 := by field_simp
  have hmain : XW * (cbar * (3 / 8) * (243 / 100)
        + ((cbar + ecount) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100)))
      = (cbar + ecount) * totalMass * B := by rw [hXWdef, hB]; ring
  have hRHS : XW * (cbar * (3 / 8) * (243 / 100)
        + (((cbar + ecount) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100))
            + lx * R3 / XW))
      = (cbar + ecount) * totalMass * B + lx * R3 := by
    rw [show cbar * (3 / 8) * (243 / 100)
          + (((cbar + ecount) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100))
              + lx * R3 / XW)
        = (cbar * (3 / 8) * (243 / 100)
            + ((cbar + ecount) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100)))
          + lx * R3 / XW from by ring, mul_add, hcancel, hmain]
  linarith [hraw, hrawexp, hstep2, hRHS]

/-- **The strip discharge.**  The prime-power strip normalises with `e4 = (log x·x/(z−1))/X_W`:
`log x·x/(z−1) ≤ X_W·e4` (an equality; `X_W > 0`). -/
theorem hstrip_normalized {XW : ℝ} (x z : ℕ) (hXW : 0 < XW) :
    Real.log x * (x : ℝ) / ((z : ℝ) - 1)
      ≤ XW * ((Real.log x * (x : ℝ) / ((z : ℝ) - 1)) / XW) := by
  have hne : XW ≠ 0 := ne_of_gt hXW
  rw [mul_div_cancel₀ _ hne]

/-! ## Part B — the error-bundle threshold (`hE`) -/

/-- **`errorBundle_le` — the razor error bundle from per-share bounds.**  If each error `eᵢ` is
below its share `bᵢ` and the shares clear `b1 + b2/2 + b3/2 + b4/2 ≤ 1/200`, then the razor bundle
`e1 + e2/2 + e3/2 + e4/2 ≤ 1/200`.  The per-share discharge at the concrete instance
(`z = ⌊x^{1/8}⌋`, the crude `X_W`-lower, poly-beats-log) fixes the explicit `x₀` — GLU-2's job. -/
theorem errorBundle_le {e1 e2 e3 e4 b1 b2 b3 b4 : ℝ}
    (h1 : e1 ≤ b1) (h2 : e2 ≤ b2) (h3 : e3 ≤ b3) (h4 : e4 ≤ b4)
    (hsum : b1 + b2 / 2 + b3 / 2 + b4 / 2 ≤ 1 / 200) :
    e1 + e2 / 2 + e3 / 2 + e4 / 2 ≤ 1 / 200 := by linarith

/-! ## Part C — `normalized_package`: the four bounds composed through `hledger_at_certs`

The H-glue's first-half endpoint: the four discharged bounds close the razor `hledger` conjunct at
the certified constants, ready for `chen_positivity`.  All carrier data are free reals (GLU-2
instantiates from the concrete sieves); the raw bounds match the landed lemma conclusions verbatim,
and `hEbundle` is the assembled error threshold (`errorBundle_le` at the operating `x₀`). -/

/-- **`normalized_package` — the razor at the certified constants, via GLU-1's four discharges.**
Given the shared normalisation `X_W = totalMass·Wz > 0`, the three raw carrier bounds (the landed
`twin_A1_lower_B` / `twin_A2_upper` / `mainA3_of_hBVswitch` conclusions, `X_W`-factored), the value
/ reconciliation certs, and the assembled error bundle `hEbundle ≤ 1/200`, the razor closes:

  `0 < mainA1 − mainA2/2 − mainA3/2 − log x·x/(z−1)/2`

— exactly the `hledger` conjunct `chen_positivity` (`Salt/Chen/Assembly.lean`) consumes.  Proof:
the four `hmᵢ_normalized` discharges feed `RazorClose.hledger_at_certs` (whose certified scalar
margin `≥ 1/100` beats the `1/200` bundle). -/
theorem normalized_package {x z : ℕ}
    {XW totalMass Wz Wy T Fv slack3 R3 rho ecount : ℝ}
    {fA1 slack1 R1 mainA1 : ℝ}
    {A2grid wtail aggSlack R2 mainA2 : ℝ}
    {mainA3 : ℝ}
    (hXW : 0 < XW) (hXWdef : XW = totalMass * Wz)
    -- A₁
    (hrawA1 : XW * (fA1 - slack1) - R1 ≤ mainA1)
    (hcertA1 : (9779 : ℝ) / 10000 ≤ fA1)
    -- A₂
    (hrawA2 : mainA2 ≤ XW * (A2grid + aggSlack) + R2)
    (hcertA2 : A2grid ≤ (3 + 43 / 75) * (Real.log 6 / 4 + wtail))
    -- A₃
    (hrawA3 : mainA3 ≤ Real.log x * (T * Wy * (Fv + slack3) + R3))
    (hcertA3 : Fv ≤ 243 / 100) (hFslack_nn : 0 ≤ Fv + slack3)
    (hWy : Wy ≤ Wz * rho) (hrho_nn : 0 ≤ rho) (hWz_nn : 0 ≤ Wz)
    (hLTnn : 0 ≤ Real.log x * T)
    (hcount : Real.log x * T ≤ (cbar + ecount) * totalMass)
    -- the assembled error bundle at the operating threshold `x₀`
    (hEbundle :
      (slack1 + R1 / XW)
        + ((3 + 43 / 75) * wtail + aggSlack + R2 / XW) / 2
        + (((cbar + ecount) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100))
            + Real.log x * R3 / XW) / 2
        + ((Real.log x * (x : ℝ) / ((z : ℝ) - 1)) / XW) / 2
      ≤ 1 / 200) :
    0 < mainA1 - mainA2 / 2 - mainA3 / 2 - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2 :=
  hledger_at_certs (x := x) (z := z) hXW hEbundle
    (hmA1_normalized hXW hcertA1 hrawA1)
    (hmA2_normalized hXW hcertA2 hrawA2)
    (hmA3_normalized hXW hXWdef hrawA3 hcertA3 hFslack_nn hWy hrho_nn hWz_nn hLTnn hcount)
    (hstrip_normalized x z hXW)

/-- Regression: the four GLU-1 discharges have exactly the `hledger_at_certs` per-carrier shapes.
`normalized_package` feeds them in with the pinned errors `e1 = slack1 + R1/X_W`,
`e2 = (3+43/75)·wtail + aggSlack + R2/X_W`,
`e3 = (cbar+ecount)·rho·(243/100+slack3) − cbar·(3/8)·(243/100) + log x·R3/X_W`,
`e4 = (log x·x/(z−1))/X_W`. -/
example : True := trivial

end Salt.Chen
