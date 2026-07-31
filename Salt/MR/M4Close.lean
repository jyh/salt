/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Exit
import Salt.MR.M4Door
import Salt.MR.M4MeanSq
import Salt.MR.M4Quality
import Salt.MR.M4Chars

/-!
# M4-7 — THE ARITHMETIC CLOSE (`M4Close`)

Source: `docs/exploration/s9-freeze-0726.md` ⟦AMENDMENT B⟧ row `M4-7` (:282) — "the
arithmetic close ⟹ `≪ HX/(dW^{1/4})`"; `docs/blueprints/flags.md` ⟦THE OVERNIGHT TRIO⟧ (the
A2-5 socket) and the M4-8 entry (the `24C/δ` gate, the four log scales).

The row composes the landed M4 tower into `M4Exit.m4_exit_socket`'s ONE open binder `hbd`,
and then fires the exit: `m4_door_contradiction_of_live` is the M4/S9 chain end to end.

## THE CHAIN, as it is actually landed here

```
   ∫‖Σ_{n<m≤n+H} λ(m)e(αm)‖ dμ                                    (the door's carrier)
     ≤ ∫‖Σ 1_𝒮(m)λ(m)e(αm)‖ dμ + δ/4·H + 4·2^k·H/x               (M4-8, CONSUMED)
     ≤ √(∫‖Σ 1_𝒮 λ e(α·)‖² dμ) + δ/4·H + 4·2^k·H/x               (§1, THE L²→L¹ STEP)
     ≤ (√(Braw H) + δ/4 + 4·2^k/x)·H                              (the socket, §4)
     ≤ mrtDeliveredGrade C H · H                                  (§3, THE MARGIN)
```

and `mrtDeliveredGrade C H · H` is byte-exactly `m4_exit_socket`'s `hbd`.

## ⟦THE SOCKET⟧ — what remains, named once (`M4SievedDoorSq`)

The one open obligation is the **mean square of the sieved λ-window sum at the door**:

```
∫ ‖Σ_{n<m≤n+H} 1_𝒮(m)λ(m)e(αm)‖² ∂(logMeasure R.x R.ω)  ≤  Braw H · H²
```

at every tight-major `α` (`NearRatTight (arcDen 12 H) H α`).  It is stated at the `L²`
level, not the `L¹` level, **because that is what the mean-square tower natively produces**:
`thm_a2'`'s carrier is `(1/X)∫_X^{2X}‖(1/h)·shortSum‖²dx`, a mean SQUARE.  §1 discharges the
Cauchy–Schwarz step once and for all, so the supplier never has to meet an `L¹` target.

Its supplier is the residue/character/Abel/dyadic chain, all of whose *stones* are landed
(`M4Chars`, `M4Residue`, `M4Abel`, `M4Dyadic`, `M4MeanSq`, `M4Quality`); what is NOT landed
is the plumbing between them — see ⟦THE FIVE OPEN BRIDGES⟧ below, which is this row's
report, not its silence.

## ⟦THE A2-5 SOCKET⟧ — `hlive`, carried

`M4MeanSq`'s header: the `𝒮_K`↔seam-datum identification cannot be derived inside the
corpus, and the WHOLE remaining band gap is the live-range agreement `hlive`
(`m4_t0band_of_live`).  It is named here (`M4LiveAgree`), bundled at the shape the whole
chain reads (`M4BandTransport`), and **discharged at that shape** (`m4_bandTransport`, from
`m4_t0band_of_live`): what the A2-5 seam still owes is the agreement at the row's own datum,
per instance, which is exactly the premise `M4LiveAgree` of the transport.  The socket
`M4SievedDoorSq` takes the transport as its own premise, so the binder is visible in the
wave's exit and is never unfolded.

## ⟦THE FIVE OPEN BRIDGES⟧ (the socket's supplier — this row's STOP list)

Each is > ~60 lines of genuinely new bridging (not consumption), hence out of this row's
budget by the brief's own rule.  Stated precisely so the next wave can dispatch them:

1. **the residue-class split of the window sum at a tight-major `α`** — `α = a/q + θ`,
   `e(αm) = e(am/q)e(θm)`, `e(am/q)` constant on classes mod `q`; the triangle inequality
   over the `q` classes.  §6 below lands the *character* half of this bridge at the honest
   sum-side datum (`sum_liou_modEq_residue_eq`, `inv_totient_sum_le`); what is still missing
   is the *window* partition and the constancy of the rational phase.
2. **the Abel drift kill inside the door window** — `M4Abel.norm_phase_sum_arcDen_drift` is
   landed for `∑_{M<m≤N} eR(θm)A(m)`; the bridge is `absWindowSum`'s own phase
   (`Complex.exp (2πiα·)`) to `eR`, and the partial-sum family `S(K)`, `K ≤ n+H`, which
   makes the mean-square obligation UNIFORM over sub-window lengths.
3. **the `d₀`-dilation transport into the door window** — `M4Residue.residue_split_dilate_door`
   + `M4Dyadic.sum_window_dilate` are landed; the bridge is the door window's image under
   `n ↦ n/d₀` and the trivial branch below `trivThresh H d₀ W` (`M4MeanSq.m4_trivial_branch`,
   landed) as a case split.
4. **the sum→integral bridge** — the mean square lives on `∫_X^{2X}·dx`, the door on a
   discrete harmonic sum.  The exact identity is available: for `x ∈ [n, n+1)` the window
   `(x, x+H]` contains exactly `{n+1,…,n+H}`, so `‖shortSum a s₀ x H‖` is constant on unit
   intervals and the discrete square-sum IS the integral.  Landing it costs interval
   additivity + integrability of a piecewise-constant integrand.
5. **the outer dyadic cover at the door** — `M4Dyadic.dyadCover_total_le(_logPow)` is landed
   for a `Finset` cover; the bridge is the harmonic weight `1/n ≍ 1/X′` on a block
   (`M4Dyadic.sum_div_dyadPart_le`, landed) meeting `logMeasure`'s normaliser `Z`.

## Conventions

* **`W` is H-scale.**  `m4W H = (log H)^{12}` and `arcDen 12 H = (log H)^{12}` are the SAME
  object in two spellings (`arcDen_twelve_eq_m4W`) — the fourth glyph of M4-8's ⟦FOUR LOG
  SCALES⟧ pin is `log ω`, and it appears here only inside M4-8's own gate list.
* **Every constant symbolic.**  `Cg` (the door glue's), `C` (`C_MRT`), `δ`, `Braw` are all
  parameters; the only numerals formed are the mean square's own five (`m4RawMS`, byte-copied
  from `m4_meansq_per_chi_gen`'s conclusion).
* **The gates ride in a bundle** (`M4DoorGates`), so the wave's exit displays the
  remaining-obligations register as a single structure.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE `L²→L¹` STEP (Cauchy–Schwarz on the door's measure)

The freeze's trap: "the Cauchy–Schwarz `L²→L¹` carries a `√` of the measure's mass".  The
door's measure is a PROBABILITY measure (`logMeasure` is `Z`-normalised), so the mass is `1`
and the step is exactly `‖f‖₁ ≤ ‖f‖₂` — but only after the normaliser has been cancelled
honestly, which is what `sum_harmonic_cauchy_schwarz` does. -/

/-- **Cauchy–Schwarz against the harmonic weight.**  `(∑ f(n)/n)² ≤ (∑ 1/n)·(∑ f(n)²/n)` on
the door window.  No hypothesis at all: the weight `1/n` is nonnegative for every `n : ℕ`
(including `n = 0`, where it is `0`), and the split is `f·w = √w·(f√w)`. -/
theorem sum_harmonic_cauchy_schwarz (x ω : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹) ^ 2
      ≤ (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n ^ 2 * (n : ℝ)⁻¹ := by
  have hw : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ)⁻¹ := fun n => by positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ioc (x / ω) x)
    (fun n => Real.sqrt ((n : ℝ)⁻¹)) (fun n => f n * Real.sqrt ((n : ℝ)⁻¹))
  have e1 : ∀ n : ℕ,
      Real.sqrt ((n : ℝ)⁻¹) * (f n * Real.sqrt ((n : ℝ)⁻¹)) = f n * (n : ℝ)⁻¹ := by
    intro n
    have hsq : Real.sqrt ((n : ℝ)⁻¹) * Real.sqrt ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ :=
      Real.mul_self_sqrt (hw n)
    calc Real.sqrt ((n : ℝ)⁻¹) * (f n * Real.sqrt ((n : ℝ)⁻¹))
        = f n * (Real.sqrt ((n : ℝ)⁻¹) * Real.sqrt ((n : ℝ)⁻¹)) := by ring
      _ = f n * (n : ℝ)⁻¹ := by rw [hsq]
  have e2 : ∀ n : ℕ, Real.sqrt ((n : ℝ)⁻¹) ^ 2 = (n : ℝ)⁻¹ := fun n => Real.sq_sqrt (hw n)
  have e3 : ∀ n : ℕ, (f n * Real.sqrt ((n : ℝ)⁻¹)) ^ 2 = f n ^ 2 * (n : ℝ)⁻¹ := by
    intro n
    rw [mul_pow, Real.sq_sqrt (hw n)]
  simp only [e1, e2, e3] at hcs
  exact hcs

/-- **THE `L²→L¹` STEP AT THE DOOR.**  `∫ f dμ ≤ √(∫ f² dμ)` for a nonnegative `f` — the
Cauchy–Schwarz inequality with the `Z`-normalisation cancelled exactly (`Z⁻²·Z = Z⁻¹`), so no
factor of the measure's mass survives.  Proved through `ShiftCorr.integral_logMeasure_eq`, so
no integrability side condition is incurred. -/
theorem integral_logMeasure_le_sqrt {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    (∫ n, f n ∂(logMeasure x ω)) ≤ Real.sqrt (∫ n, f n ^ 2 ∂(logMeasure x ω)) := by
  have hZ0 : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := door_norm_pos hx hω
  have hS1 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ :=
    Finset.sum_nonneg fun n _ => mul_nonneg (hf n) (by positivity)
  rw [integral_logMeasure_eq, integral_logMeasure_eq]
  have hL0 : (0 : ℝ) ≤ (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
      * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ :=
    mul_nonneg (by positivity) hS1
  have hcs := sum_harmonic_cauchy_schwarz x ω f
  have hkey : ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
        * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹) ^ 2
      ≤ (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n ^ 2 * (n : ℝ)⁻¹ := by
    have hexp : ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹) ^ 2
        = ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹) ^ 2
            * (∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹) ^ 2 := by ring
    have hmul := mul_le_mul_of_nonneg_left hcs
      (by positivity : (0 : ℝ) ≤ ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹) ^ 2)
    have hcancel : ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹) ^ 2
          * ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
              * ∑ n ∈ Finset.Ioc (x / ω) x, f n ^ 2 * (n : ℝ)⁻¹)
        = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
            * ∑ n ∈ Finset.Ioc (x / ω) x, f n ^ 2 * (n : ℝ)⁻¹ := by
      field_simp
    rw [hexp]
    calc ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹) ^ 2
            * (∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹) ^ 2
        ≤ ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹) ^ 2
            * ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
                * ∑ n ∈ Finset.Ioc (x / ω) x, f n ^ 2 * (n : ℝ)⁻¹) := hmul
      _ = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
            * ∑ n ∈ Finset.Ioc (x / ω) x, f n ^ 2 * (n : ℝ)⁻¹ := hcancel
  calc (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹
      = Real.sqrt (((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹) ^ 2) := (Real.sqrt_sq hL0).symm
    _ ≤ Real.sqrt ((∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n ^ 2 * (n : ℝ)⁻¹) := Real.sqrt_le_sqrt hkey

/-- **The `L²→L¹` step against a supplied mean-square bound** — the shape the close consumes:
the socket delivers `∫ f² ≤ B`, and the door's `L¹` norm is `≤ √B`. -/
theorem integral_logMeasure_le_sqrt_of_sq {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) {f : ℕ → ℝ}
    {B : ℝ} (hf : ∀ n, 0 ≤ f n) (hB : (∫ n, f n ^ 2 ∂(logMeasure x ω)) ≤ B) :
    (∫ n, f n ∂(logMeasure x ω)) ≤ Real.sqrt B :=
  le_trans (integral_logMeasure_le_sqrt hx hω hf) (Real.sqrt_le_sqrt hB)

/-! ## §2 — THE PRICING: the five raw summands

`m4_meansq_per_chi_gen`'s conclusion is a sum of five terms, byte-copied below.  The row's
"arithmetic close" is the statement that they are all below one grade; the only DERIVED step
is the first (the quality demand cashed through `m4_exit_decay_of_quality`), the other four
are the freeze's own door gates, carried in-statement (law #253). -/

/-- **THE FIVE RAW SUMMANDS**, byte-verbatim from `M4MeanSq.m4_meansq_per_chi_gen`'s
right-hand side: the quality term, the level-1 term, the `(log X)^{−1/500}` term, the
`(log X)^{−43/45}` ball term, and `C₅/h`. -/
def m4RawMS (C₁' M₀ : ℝ) (M : ℕ) (X h : ℝ) : ℝ :=
  8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1 M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- **THE `W`-SAVING** the quality demand buys: `W^{−5/2}` at `W = m4W H = (log H)^{12}`.
This is the target the five summands are priced against. -/
def m4Saving (H : ℕ) : ℝ := (m4W H) ^ (-(5 : ℝ) / 2)

/-- `arcDen 12 H` (the arc's denominator cap, an `rpow`) and `m4W H` (the quality's modulus
cap, an `npow`) are the SAME object.  One glyph, pinned once — the M4-8 ⟦FOUR LOG SCALES⟧
discipline applied to the two `log H`-scale objects of this row. -/
theorem arcDen_twelve_eq_m4W (H : ℕ) : arcDen 12 H = m4W H := by
  unfold arcDen m4W
  rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The saving in one log scale: `m4Saving H = (log H)^{−30}`. -/
theorem m4Saving_eq {H : ℕ} (hL : 0 ≤ Real.log (H : ℝ)) :
    m4Saving H = Real.log (H : ℝ) ^ (-(30 : ℝ)) := by
  unfold m4Saving m4W
  rw [← Real.rpow_natCast (Real.log (H : ℝ)) 12, ← Real.rpow_mul hL]
  norm_num

/-- **The half-power of the saving** — what the `L²→L¹` step actually spends:
`√(m4Saving H) = (log H)^{−15}`. -/
theorem sqrt_m4Saving {H : ℕ} (hL : 0 ≤ Real.log (H : ℝ)) :
    Real.sqrt (m4Saving H) = Real.log (H : ℝ) ^ (-(15 : ℝ)) := by
  rw [m4Saving_eq hL, Real.sqrt_eq_rpow, ← Real.rpow_mul hL]
  norm_num

/-- **PRICING SUMMAND 1 — the quality term.**  The demand `M₀ ≥ (5e/2)·log W` turns
`exp(−M₀/e)` into `W^{−5/2}` (`m4_exit_decay_of_quality`; the `e`s cancel exactly, and the
direction is `W^{−5/2}`, never `W^{5/2}`). -/
theorem m4_quality_summand_le {C₁' M₀ W : ℝ} (hW : 1 ≤ W) (hM : m4Demand W ≤ M₀) :
    8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) ≤ 8448 * C₁' ^ 2 * W ^ (-(5 : ℝ) / 2) :=
  mul_le_mul_of_nonneg_left (m4_exit_decay_of_quality hW hM) (by positivity)

/-- **THE ARITHMETIC CLOSE OF THE MEAN SQUARE.**  Under the quality demand and the four door
gates, the five raw summands are below one grade `G`.  Each gate is IN-STATEMENT and reads
against `G/5`: the row never chooses a numeral, it displays the split. -/
theorem m4_rawMS_le {C₁' M₀ W X h G : ℝ} {M : ℕ} (hW : 1 ≤ W) (hM : m4Demand W ≤ M₀)
    (g1 : 8448 * C₁' ^ 2 * W ^ (-(5 : ℝ) / 2) ≤ G / 5)
    (g2 : 1787702400 * a2Level1 M ≤ G / 5)
    (g3 : 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) ≤ G / 5)
    (g4 : 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) ≤ G / 5)
    (g5 : 6315000 / h ≤ G / 5) :
    m4RawMS C₁' M₀ M X h ≤ G := by
  have h1 := m4_quality_summand_le (C₁' := C₁') hW hM
  unfold m4RawMS
  linarith

/-- The close at the door's own cap `W = m4W H`, priced against the saving: the five gates
read against `m4Saving H/5`, and the quality demand is the door's `30e·loglog H`
(`m4Demand_door`). -/
theorem m4_rawMS_le_saving {C₁' M₀ X h : ℝ} {M H : ℕ} (hW : 1 ≤ m4W H)
    (hM : m4Demand (m4W H) ≤ M₀)
    (g1 : 8448 * C₁' ^ 2 * (m4W H) ^ (-(5 : ℝ) / 2) ≤ m4Saving H / 5)
    (g2 : 1787702400 * a2Level1 M ≤ m4Saving H / 5)
    (g3 : 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) ≤ m4Saving H / 5)
    (g4 : 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
      ≤ m4Saving H / 5)
    (g5 : 6315000 / h ≤ m4Saving H / 5) :
    m4RawMS C₁' M₀ M X h ≤ m4Saving H :=
  m4_rawMS_le hW hM g1 g2 g3 g4 g5

/-! ## §3 — THE MARGIN: the saving beats the door's delivered grade

The freeze's trivial-bound margin, as arithmetic.  The `L²→L¹` step spends half the saving's
exponent (`W^{−5/2} ↦ W^{−5/4} = (log H)^{−15}`), and the door asks only for
`mrtDeliveredGrade C H = C(log H)^{−11/4}loglog H`.  The exponent gap `15 − 11/4` is the
margin, and it is enormous — which is why every constant may stay symbolic. -/

/-- **The regime clears the margin's floor.**  `e ≤ log R.Hlo`, from `hHlo_floor`
(`4·10⁶ ≤ R.Hlo`) alone — never from a numeral chosen to fit.  (`exp(e) < exp 3 < 21`.) -/
theorem exp_one_le_log_regime_Hlo (R : ChowlaRegime) : Real.exp 1 ≤ Real.log (R.Hlo : ℝ) := by
  have h4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hmono : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by linarith)
  have hexp3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have h21 : Real.exp 3 ≤ 21 := by
    rw [hexp3]
    nlinarith
  rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (R.Hlo : ℝ))]
  linarith

/-- The floor transfers up the window range: `e ≤ log H` for every `H ≥ R.Hlo`. -/
theorem exp_one_le_log_of_regime_le (R : ChowlaRegime) {H : ℕ} (h : R.Hlo ≤ H) :
    Real.exp 1 ≤ Real.log (H : ℝ) := by
  have h0 : (0 : ℝ) < (R.Hlo : ℝ) := by
    have := two_le_regime_Hlo R
    exact_mod_cast (by omega : 0 < R.Hlo)
  refine le_trans (exp_one_le_log_regime_Hlo R) (Real.log_le_log h0 ?_)
  exact_mod_cast h

/-- **THE MARGIN.**  `√(m4Saving H) ≤ mrtDeliveredGrade C H` for every `C ≥ 1` past the
floor `e ≤ log H`: the half-power saving `(log H)^{−15}` is under the delivered grade
`C(log H)^{−11/4}loglog H` because `−15 ≤ −11/4`, `loglog H ≥ 1` and `C ≥ 1`.

This is the freeze's "trivial-bound margin", and it is where the row's whole slack lives. -/
theorem sqrt_m4Saving_le_delivered {C : ℝ} {H : ℕ} (hC : 1 ≤ C)
    (hL : Real.exp 1 ≤ Real.log (H : ℝ)) :
    Real.sqrt (m4Saving H) ≤ mrtDeliveredGrade C H := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hL1 : (1 : ℝ) ≤ Real.log (H : ℝ) := le_trans he.le hL
  have hL0 : (0 : ℝ) ≤ Real.log (H : ℝ) := by linarith
  have hll : (1 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at h
  have hstep : Real.log (H : ℝ) ^ (-(15 : ℝ)) ≤ Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hpos : (0 : ℝ) < Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hCA : Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) ≤ C * Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) :=
    le_mul_of_one_le_left hpos.le hC
  have hCA0 : (0 : ℝ) ≤ C * Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) :=
    mul_nonneg (by linarith) hpos.le
  have hCAll : C * Real.log (H : ℝ) ^ (-(11 / 4 : ℝ))
      ≤ C * Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) * Real.log (Real.log (H : ℝ)) :=
    le_mul_of_one_le_right hCA0 hll
  rw [sqrt_m4Saving hL0, mrtDeliveredGrade]
  linarith

/-! ## §4 — THE SOCKET AND THE DOOR CLOSE -/

/-- **⟦THE A2-5 SOCKET⟧, named.**  The live-range agreement `X < n ≤ N` between the row's
coefficient sequence and the seam coefficient — the ONE binder the A2-5/Route-III
identification owes (`M4MeanSq`'s header; flags, ⟦THE OVERNIGHT TRIO⟧).  Never unfolded
below. -/
def M4LiveAgree {q : ℕ} (χ : DirichletCharacter ℂ q) (t₀ X : ℝ) (N : ℕ) (a : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, X < (n : ℝ) → n ≤ N → a n = seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀ n

/-- **THE BAND TRANSPORT**, at the shape the whole mean-square chain reads: any coefficient
sequence agreeing with the seam coefficient on the live range inherits the band datum's
`T₀`-band bound. -/
def M4BandTransport : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t₀ X : ℝ) (N : ℕ) (a : ℕ → ℂ) (B : ℝ),
    M4LiveAgree χ t₀ X N a →
    (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (m4BandDatum χ t₀ X) (seamS0 N X) t‖ ^ 2) ≤ B →
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ B

/-- The transport is LANDED (`M4MeanSq.m4_t0band_of_live`): `dpolyA` never reads the
coefficient off `seamS0 N X`.  What the A2-5 seam still owes is `M4LiveAgree` at the row's
own datum — the premise, per instance. -/
theorem m4_bandTransport : M4BandTransport :=
  fun _ χ _ _ _ _ _ hlive hb => m4_t0band_of_live χ hlive hb

/-- **THE M4-7 SOCKET** — the mean square of the SIEVED λ-window sum on the door's measure,
at every tight-major frequency, with the band transport (hence `hlive`) as its own premise.

`L²`, not `L¹`: this is the level the mean-square tower natively produces, and §1 discharges
the Cauchy–Schwarz descent once.  See ⟦THE FIVE OPEN BRIDGES⟧ in the module header for the
supplier's remaining plumbing. -/
def M4SievedDoorSq (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen 12 H) H α →
        (∫ n, ‖absWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
              (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n α‖ ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (H : ℝ) ^ 2

/-- **THE SOCKET IS INHABITED** (the anti-vacuity duty — M4-1's lesson, and M4-8's
`doorCount_gates`).  At the TRIVIAL grade `Braw ≡ 1` the socket holds outright: the window
carries `H` terms of modulus `≤ 1`, and the door's measure is a probability measure.  So the
socket's hypothesis list is not satisfiable-by-nobody; ALL of its content is the grade, and
none of it is the shape.  (At `Braw ≡ 1` the grade gate `M4GradeGate` of course fails —
`√1 = 1` is nowhere near `mrtDeliveredGrade C H`; that failure is exactly the analytic gap
the five open bridges close.) -/
theorem m4_sievedDoorSq_trivial (R : ChowlaRegime) (M : ℕ) :
    M4SievedDoorSq R M (fun _ => 1) := by
  intro _ H _ _ _ α _
  refine integral_logMeasure_le_of_le R.hx R.hω (fun n => ?_)
  have h := norm_absWindowSum_le
    (a := memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
    (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) H n α
  have h0 := norm_nonneg (absWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
    (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n α)
  nlinarith

/-- **THE DOOR-DATA GATE BUNDLE** — M4-8's own hypothesis list, at the regime, uniform over
the window range.  `Cg` is the door glue's single opened constant; the `M`-gate is the
`24·Cg/δ` of M4-8 (the `8C/δ` of the freeze at the per-block grade `δ/3`, i.e. the `log ω`
absorption already applied).

`2 ≤ x`, `2 ≤ ω`, `ω ≤ x` are NOT here: the regime supplies them (`R.hx`, `R.hω`, `R.hωx`),
and so is `H + 1 ≤ x` (from `R.hheadroom`).  The witness for `hreach`/`hcount` at
`k := doorCount R.ω` is `M4Door.doorCount_gates`. -/
structure M4DoorGates (Cg : ℝ) (R : ChowlaRegime) (M k : ℕ) (δ : ℝ) : Prop where
  /-- the K-family's re-pin parameter is a genuine modulus -/
  hM : 1 ≤ M
  /-- the door grade is positive -/
  hδ : 0 < δ
  /-- the `M`-gate, after M4-8's `log ω` absorption -/
  hMδ : 24 * Cg / δ ≤ (M : ℝ)
  /-- the absorption's floor: `log ω ≥ 4` (where the cover/normaliser ratio is `< 3`) -/
  hlogω : 4 ≤ Real.log (R.ω : ℝ)
  /-- the geometric gate for the endpoint sum -/
  hpow : 2 ^ (k + 1) ≤ R.x
  /-- the cover count, IN-STATEMENT (law #253) -/
  hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2
  /-- the ladder exhausts the door window, at every window length in range -/
  hreach : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → doorLadder R.x H k ≤ R.x / R.ω
  /-- HS-3's analytic bundle, one per block, at every window length in range -/
  hblocks : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
    SieveBlockGate (Adoor M) (3072 * M) M 2 (doorLadder R.x H (i + 1))

/-- **THE GRADE GATE** — the row's own budget line: the socket's `L²` grade (after the
`√`), the door's sieve grade `δ/4` and the door's endpoint grade `4·2^k/x` together fit under
`mrtDeliveredGrade C H`. -/
def M4GradeGate (R : ChowlaRegime) (C δ : ℝ) (Braw : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
    Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade C H

/-- **THE GRADE GATE, DISCHARGED FROM THE PRICING.**  If the socket's grade is below the
saving (§2) then the `√`-half of the budget is paid by §3's margin at `C/2`, and the caller
is left with the door's own two terms against the other half.  `C ≥ 2` is the halving; both
halves are `mrtDeliveredGrade (C/2)`, which is exactly `mrtDeliveredGrade C/2` because the
grade is LINEAR in `C`. -/
theorem m4_gradeGate_of_pricing {R : ChowlaRegime} {C δ : ℝ} {Braw : ℕ → ℝ} {k : ℕ}
    (hC : 2 ≤ C)
    (hBraw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ m4Saving H)
    (hrest : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) :
    M4GradeGate R C δ Braw k := by
  intro H hlo hhi
  have hLexp : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have hsq : Real.sqrt (Braw H) ≤ Real.sqrt (m4Saving H) :=
    Real.sqrt_le_sqrt (hBraw H hlo hhi)
  have hmargin : Real.sqrt (m4Saving H) ≤ mrtDeliveredGrade (C / 2) H :=
    sqrt_m4Saving_le_delivered (by linarith) hLexp
  have hhalf : mrtDeliveredGrade (C / 2) H + mrtDeliveredGrade (C / 2) H
      = mrtDeliveredGrade C H := by
    unfold mrtDeliveredGrade
    ring
  have hr := hrest H hlo hhi
  linarith

/-- **THE M4-7 DELIVERABLE — `m4_hbd_of_live`.**  The `hbd` socket of
`M4Exit.m4_exit_socket`, byte-plug-compatible, from

* the door-data gate bundle `M4DoorGates` (M4-8's own list, at the regime),
* the grade gate `M4GradeGate` (the row's budget line, §3-dischargeable),
* the M4-7 socket `M4SievedDoorSq` (the sieved mean square at the door), whose own premise
  is the band transport — the ⟦A2-5⟧ binder, supplied here by `m4_bandTransport`.

The door glue's constant `Cg` is opened ONCE, at the head of the statement
(`SieveGlue`'s ⟦ONE CONSTANT⟧ discipline), so the `M`-gate `24·Cg/δ ≤ M` is a legal
argument. -/
theorem m4_hbd_of_live :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (C δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
        M4SievedDoorSq R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ mrtDeliveredGrade C H * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R C δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ 3072 * M := by
    have := hgates.hM
    omega
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed⟧
  have hglueH := hglue (Adoor M) (3072 * M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
            (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ mrtDeliveredGrade C H * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-! ## §5 — THE WAVE'S EXIT

`m4_exit_socket` (M4-9) closes everything on the door path except its single `hbd` binder;
§4 supplies that binder.  Composing them is the M4/S9 chain end to end. -/

/-- **THE WAVE'S EXIT — `m4_door_contradiction_of_live`.**

`m4_exit_socket ∘ m4_hbd_of_live`: `ε` and `δ₀` are fixed first (the budget head's own honest
choice), then for every `C_MRT ≥ 0` and every extra floor / outer-scale demand there is a
regime `R` at which **log-Chowla-2 does not fail**, conditional on exactly this register:

* `M4DoorGates Cg R M k δ` — M4-8's door-glue list (the `24Cg/δ` `M`-gate, `log ω ≥ 4`, the
  ladder's three gates, HS-3 per block).  Owed by the regime/door numerology;
  `doorCount_gates` is the witness at `k := doorCount R.ω`.
* `0 ≤ Braw H` — the socket's grade is a grade.  Owed by the supplier.
* `M4GradeGate R C δ Braw k` — the budget line.  Owed to `m4_gradeGate_of_pricing` (§3)
  plus the pricing (§2).
* `M4SievedDoorSq R M Braw` — THE SOCKET: the sieved λ mean square at the door, at every
  tight-major `α`, given the band transport (⟦A2-5⟧).  Owed by ⟦THE FIVE OPEN BRIDGES⟧
  (module header).

Nothing else is open on the M4 road: `mrtUniformityXi_of_absWindowBound_twelve` (the arc),
`log_chowla_two_budget_head_g` (the head), `contradiction_of_mrtDoorXi` (the collision) and
`m4_door_glue` (the sieve insert) are all landed and consumed. -/
theorem m4_door_contradiction_of_live :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
            M4SievedDoorSq R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, _, _, _, hR⟩ := hexit C hC U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R C δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **The exit's collision form.**  With the failure branch assumed at the exit's regime the
chain closes to `False` — `m4_exit_socket_False` composed with the same supply. -/
theorem m4_door_False_of_live :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
            M4SievedDoorSq R M Braw →
              logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_False
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hexit C hC U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock hfail =>
    hR (hhbd R C δ Braw M k hgates hBraw0 hgrade hsock) hfail⟩

/-! ## §6 — SUPPLIER STONES: the character leg at the SUM-SIDE datum

Not consumed by the exit above — these are the first half of ⟦OPEN BRIDGE 1⟧, landed here
because the gap is a datum gap, not an analytic one.

`M4Chars`' decomposition is stated at `lam` (`sum_lam_residue_eq`,
`norm_sum_lam_modEq_residue_le`), and `lam = fun _ => −1` is the PRETENTIOUS datum, correct
only at primes (the ⟦lam collision⟧, flags 2026-07-28 06:46).  The sum side of the M4 chain
sums over INTEGERS, so it must be `liouvilleC`; and at `w := liouvilleC` the per-`χ` object of
`M4Chars.sum_weight_residue_eq` is `liouChi χ` **on the nose** (`liouChi` is by definition
`liouvilleC·χ̄`).  So the honest decomposition is one instantiation away, and it is taken
here once. -/

/-- **THE M4-3 DECOMPOSITION AT THE SUM-SIDE DATUM.**  For `b₀` a unit of `ZMod q`,

`∑_{m ∈ S, m ≡ b₀} λ(m) = (1/φ(q))·∑_χ χ(b₀)·∑_{m ∈ S} liouChi χ m`,

with `λ = liouvilleC` the honest Liouville function and `liouChi χ = λ·χ̄` the row's own
datum.  (`M4Chars.sum_lam_residue_eq` is the same statement at the pretentious `lam`; the two
must never be crossed.) -/
theorem sum_liou_residue_eq {q : ℕ} [NeZero q] {b₀ : ZMod q} (hb : IsUnit b₀) (S : Finset ℕ) :
    ∑ m ∈ S.filter (fun m => ((m : ℕ) : ZMod q) = b₀), liouvilleC m
      = (q.totient : ℂ)⁻¹
          * ∑ χ : DirichletCharacter ℂ q, χ b₀ * ∑ m ∈ S, liouChi χ m := by
  rw [sum_weight_residue_eq hb liouvilleC S]
  congr 1

/-- The same with the residue test written in `ℕ` — the shape the residue split
(`M4Residue.residue_split_dilate_door`) hands over. -/
theorem sum_liou_modEq_residue_eq {q : ℕ} [NeZero q] {b : ℕ} (hcop : Nat.Coprime q b)
    (S : Finset ℕ) :
    ∑ m ∈ S.filter (fun m => m ≡ b [MOD q]), liouvilleC m
      = (q.totient : ℂ)⁻¹
          * ∑ χ : DirichletCharacter ℂ q,
              χ ((b : ℕ) : ZMod q) * ∑ m ∈ S, liouChi χ m := by
  have hfil : S.filter (fun m => m ≡ b [MOD q])
      = S.filter (fun m => ((m : ℕ) : ZMod q) = ((b : ℕ) : ZMod q)) :=
    Finset.filter_congr fun m _ => (ZMod.natCast_eq_natCast_iff m b q).symm
  rw [hfil, sum_liou_residue_eq (isUnit_natCast_of_coprime hcop) S]

/-- **The trivial bound on the decomposition, at the sum-side datum.**  The coefficient
`χ(b₀)` is unimodular, so the class sum is at most the `χ`-average of the `liouChi` sums. -/
theorem norm_sum_liou_modEq_residue_le {q : ℕ} [NeZero q] {b : ℕ} (hcop : Nat.Coprime q b)
    (S : Finset ℕ) :
    ‖∑ m ∈ S.filter (fun m => m ≡ b [MOD q]), liouvilleC m‖
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖∑ m ∈ S, liouChi χ m‖ := by
  rw [sum_liou_modEq_residue_eq hcop S, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [norm_mul, norm_chi_of_isUnit (isUnit_natCast_of_coprime hcop) χ, one_mul]

/-- **THE `χ`-COUNT.**  `#{χ mod q} = φ(q)`, read off the orthogonality relation itself at
`a = b = 1` (every term is `χ(1)·conj χ(1) = 1`).  This is the identity that makes the
`1/φ(q)` of the decomposition cancel against the `χ`-sum — no character-group theory is
invoked, only `sum_chi_mul_conj_chi`. -/
theorem card_dirichletCharacter_eq_totient (q : ℕ) [NeZero q] :
    (Fintype.card (DirichletCharacter ℂ q) : ℂ) = (q.totient : ℂ) := by
  calc (Fintype.card (DirichletCharacter ℂ q) : ℂ)
      = ∑ _χ : DirichletCharacter ℂ q, (1 : ℂ) := by simp
    _ = ∑ χ : DirichletCharacter ℂ q, χ 1 * (starRingEnd ℂ) (χ 1) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [MulChar.map_one, map_one, mul_one]
    _ = (q.totient : ℂ) := by
        rw [sum_chi_mul_conj_chi (isUnit_one) (1 : ZMod q), if_pos rfl]

/-- **THE UNIFORMITY STEP.**  A bound `B` holding UNIFORMLY over `χ` survives the
`(1/φ(q))·∑_χ` of the decomposition unchanged: the count cancels the divisor exactly.  This
is why the M4 road needs `χ`-uniform quality (`M4Quality.m4_quality_of_joint`) and not a
per-`χ` one. -/
theorem inv_totient_sum_le {q : ℕ} [NeZero q] {F : DirichletCharacter ℂ q → ℝ} {B : ℝ}
    (hF : ∀ χ, F χ ≤ B) :
    (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, F χ ≤ B := by
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = (q.totient : ℝ) := by
    exact_mod_cast card_dirichletCharacter_eq_totient q
  have hsum : ∑ χ : DirichletCharacter ℂ q, F χ ≤ (q.totient : ℝ) * B := by
    have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (DirichletCharacter ℂ q)) F B
      (fun χ _ => hF χ)
    rw [Finset.card_univ, nsmul_eq_mul, hcard] at h
    exact h
  have hφ : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q
  calc (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, F χ
      ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B := by field_simp

/-! ## §7 — ⟦THE SPLIT TWINS⟧ (second-road freeze v2, wave ①)

The family's contract is `M4Exit` §7 — read it there once.  In one line: the door integral is
consumed at the head's own CONSTANT `δ₀`, so `mrtDeliveredGrade` and the `C_MRT` binder both
disappear, and the budget line becomes a plain three-summand inequality against `δ₀`.

Everything above in this file is byte-untouched, `M4DoorGates` included: the split twins
consume the bundle unchanged, and post-split its `hMδ` field reads `24·Cg/δ ≤ M` at a
constant-scale `δ` — the freeze's "defused at the constant", by design. -/

/-- **THE GRADE GATE, SPLIT** (`M4GradeGateSplit`) — the twin of `M4GradeGate` (:425) at the
constant grade.  The three summands are the SAME three (the socket's `L²` grade after the
`√`, the door's sieve grade `δ/4`, the door's endpoint grade `4·2^k/x`); only the target
moves, from `mrtDeliveredGrade C H` to `δ₀`.

`C` is gone from the parameter list — that is the ⟦C-BINDER⟧ rule of `M4Exit` §7, and `δ₀`
takes its slot so the two Props stay positionally parallel. -/
def M4GradeGateSplit (R : ChowlaRegime) (δ₀ δ : ℝ) (Braw : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
    Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀

/-- **THE SPLIT GATE, DISCHARGED FROM THE PRICING** (`m4_gradeGate_of_pricing_split`) — the
twin of `m4_gradeGate_of_pricing` (:434).

The pricing is read DIRECTLY against the constant: `Braw H ≤ (δ₀/2)²` pays the `√`-half by
`Real.sqrt_sq`, and the caller meets the door's own two terms against the other half.  No
`m4Saving`, no `sqrt_m4Saving_le_delivered`, no `2 ≤ C` halving — the halving here is
arithmetic on a numeral, and the `15 − 11/4` exponent gap is never spent because there is no
exponent to spend it on. -/
theorem m4_gradeGate_of_pricing_split {R : ChowlaRegime} {δ₀ δ : ℝ} {Braw : ℕ → ℝ} {k : ℕ}
    (hδ₀ : 0 ≤ δ₀)
    (hBraw : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ (δ₀ / 2) ^ 2)
    (hrest : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) :
    M4GradeGateSplit R δ₀ δ Braw k := by
  intro H hlo hhi
  have hhalf : (0 : ℝ) ≤ δ₀ / 2 := by linarith
  have hsq : Real.sqrt (Braw H) ≤ δ₀ / 2 := by
    calc Real.sqrt (Braw H) ≤ Real.sqrt ((δ₀ / 2) ^ 2) := Real.sqrt_le_sqrt (hBraw H hlo hhi)
      _ = δ₀ / 2 := Real.sqrt_sq hhalf
  have hr := hrest H hlo hhi
  linarith

/-- **THE M4-7 DELIVERABLE, SPLIT** (`m4_hbd_of_live_split`) — the twin of `m4_hbd_of_live`
(:464), byte-plug-compatible with `M4Exit.m4_exit_socket_split`'s single open binder.

The proof is the landed one with its final `calc` step re-targeted: the door glue, the
socket, §1's `L²→L¹` descent and the `√`-split are all identical, and the last line reads the
split gate into `δ₀ * H` where the original read `mrtDeliveredGrade C H * H`.

Binder-list diff against the original: `C : ℝ` is GONE; `δ₀ : ℝ` takes its place and the
grade gate is `M4GradeGateSplit`.  `Cg` — the door glue's ONE opened constant — is
unchanged. -/
theorem m4_hbd_of_live_split :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (δ₀ δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGateSplit R δ₀ δ Braw k →
        M4SievedDoorSq R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ δ₀ * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R δ₀ δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ 3072 * M := by
    have := hgates.hM
    omega
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed⟧
  have hglueH := hglue (Adoor M) (3072 * M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
      (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the SPLIT budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
            (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ δ₀ * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-- **THE WAVE'S EXIT, SPLIT** (`m4_door_contradiction_of_live_split`) — the twin of
`m4_door_contradiction_of_live` (:537): `m4_exit_socket_split ∘ m4_hbd_of_live_split`.

⟦THE REGISTER, split form⟧ is the landed one with `C` deleted and the budget line re-cut:

* `M4DoorGates Cg R M k δ` — UNCHANGED (M4-8's own list; `doorCount_gates` is still the
  witness at `k := doorCount R.ω`);
* `0 ≤ Braw H` — UNCHANGED;
* `M4GradeGateSplit R δ₀ δ Braw k` — the budget line at the constant grade;
* `M4SievedDoorSq R M Braw` — UNCHANGED (the socket, at the band transport).

The conclusion `¬ logChowla2Fails R.eps R.x R.ω` is byte-identical to the landed one. -/
theorem m4_door_contradiction_of_live_split :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4SievedDoorSq R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_split
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  -- the socket's tower-law conjunct (⟦THE NAMED AMENDMENT⟧) is not consumed at this stage
  obtain ⟨R, hReps, hU1, hRg, -, hR⟩ := hexit U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R δ₀ δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-! ## §GK — the G-lever twin

The additive `_gk` family at `G := s13GK K M = 3072·2^K·M` (`GLever`).  Every declaration
below is its landed sibling with `(K : ℕ)` inserted as the FIRST binder and every literal
`3072 * M` rewritten to `s13GK K M`; nothing else moves.

The door datum genuinely changes here — `calP (Adoor M) (s13GK K M) 2` and
`calQK (Adoor M) (s13GK K M) M 2` are strictly larger than at the landed base, so the sieve
set `𝒮` moves and these cannot be transports.  What does NOT move: `a2Level1 M` (LEVEL 1 IS
K-INVARIANT, `calP_gk_one_eq`), `M4GradeGate`/`M4GradeGateSplit` (no `G` in sight),
`m4Saving`, `mrtDeliveredGrade`, and the whole `M4Exit` socket chain.

The door glue `m4_door_glue_liouville` is `(A,G)`-ABSTRACT — its only demand on the base is
`1 ≤ G`, discharged at the lever by `one_le_s13GK`.  That single line is the entire proof
diff across §GK. -/

set_option linter.unusedVariables false in
/-- **`m4RawMS` AT THE LEVER.**  The five raw summands do not read `G` at all: the level-1
summand is `a2Level1 M`, which is K-INVARIANT.  The twin exists for uniformity of the
family's shape (`K` first, everywhere), and is definitionally the landed constant. -/
def m4RawMS_gk (K : ℕ) (C₁' M₀ : ℝ) (M : ℕ) (X h : ℝ) : ℝ :=
  8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1 M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- **THE ARITHMETIC CLOSE OF THE MEAN SQUARE, AT THE LEVER.**  `m4_rawMS_le` (:249)
verbatim. -/
theorem m4_rawMS_le_gk (K : ℕ) {C₁' M₀ W X h G : ℝ} {M : ℕ} (hW : 1 ≤ W)
    (hM : m4Demand W ≤ M₀)
    (g1 : 8448 * C₁' ^ 2 * W ^ (-(5 : ℝ) / 2) ≤ G / 5)
    (g2 : 1787702400 * a2Level1 M ≤ G / 5)
    (g3 : 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) ≤ G / 5)
    (g4 : 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) ≤ G / 5)
    (g5 : 6315000 / h ≤ G / 5) :
    m4RawMS_gk K C₁' M₀ M X h ≤ G := by
  have h1 := m4_quality_summand_le (C₁' := C₁') hW hM
  unfold m4RawMS_gk
  linarith

/-- The lever's close at the door's own cap `W = m4W H` — `m4_rawMS_le_saving` (:264). -/
theorem m4_rawMS_le_saving_gk (K : ℕ) {C₁' M₀ X h : ℝ} {M H : ℕ} (hW : 1 ≤ m4W H)
    (hM : m4Demand (m4W H) ≤ M₀)
    (g1 : 8448 * C₁' ^ 2 * (m4W H) ^ (-(5 : ℝ) / 2) ≤ m4Saving H / 5)
    (g2 : 1787702400 * a2Level1 M ≤ m4Saving H / 5)
    (g3 : 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) ≤ m4Saving H / 5)
    (g4 : 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
      ≤ m4Saving H / 5)
    (g5 : 6315000 / h ≤ m4Saving H / 5) :
    m4RawMS_gk K C₁' M₀ M X h ≤ m4Saving H :=
  m4_rawMS_le_gk K hW hM g1 g2 g3 g4 g5

/-- **THE M4-7 SOCKET AT THE LEVER** — `M4SievedDoorSq` (:368) at `G := s13GK K M`.  The
sieve set moves with `K`; the shape does not. -/
def M4SievedDoorSq_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (Braw : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
      NearRatTight (arcDen 12 H) H α →
        (∫ n, ‖absWindowSum (memSCoeff (calP (Adoor M) (s13GK K M))
              (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H n α‖ ^ 2
            ∂(logMeasure R.x R.ω))
          ≤ Braw H * (H : ℝ) ^ 2

/-- **THE LEVER'S SOCKET IS INHABITED** — `m4_sievedDoorSq_trivial` (:384) verbatim: the
1-boundedness of `memSCoeff` is `G`-uniform. -/
theorem m4_sievedDoorSq_trivial_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) :
    M4SievedDoorSq_gk K R M (fun _ => 1) := by
  intro _ H _ _ _ α _
  refine integral_logMeasure_le_of_le R.hx R.hω (fun n => ?_)
  have h := norm_absWindowSum_le
    (a := memSCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC)
    (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) H n α
  have h0 := norm_nonneg (absWindowSum (memSCoeff (calP (Adoor M) (s13GK K M))
    (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H n α)
  nlinarith

/-- **THE DOOR-DATA GATE BUNDLE AT THE LEVER** — `M4DoorGates` (:403) with the per-block
`SieveBlockGate` read at `G := s13GK K M`. -/
structure M4DoorGates_gk (K : ℕ) (Cg : ℝ) (R : ChowlaRegime) (M k : ℕ) (δ : ℝ) : Prop where
  /-- the K-family's re-pin parameter is a genuine modulus -/
  hM : 1 ≤ M
  /-- the door grade is positive -/
  hδ : 0 < δ
  /-- the `M`-gate, after M4-8's `log ω` absorption -/
  hMδ : 24 * Cg / δ ≤ (M : ℝ)
  /-- the absorption's floor: `log ω ≥ 4` (where the cover/normaliser ratio is `< 3`) -/
  hlogω : 4 ≤ Real.log (R.ω : ℝ)
  /-- the geometric gate for the endpoint sum -/
  hpow : 2 ^ (k + 1) ≤ R.x
  /-- the cover count, IN-STATEMENT (law #253) -/
  hcount : (k : ℝ) ≤ Real.log (R.ω : ℝ) / Real.log 2 + 2
  /-- the ladder exhausts the door window, at every window length in range -/
  hreach : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → doorLadder R.x H k ≤ R.x / R.ω
  /-- HS-3's analytic bundle, one per block, at every window length in range -/
  hblocks : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
    SieveBlockGate (Adoor M) (s13GK K M) M 2 (doorLadder R.x H (i + 1))

/-- **THE M4-7 DELIVERABLE AT THE LEVER** — `m4_hbd_of_live` (:464).  The one proof diff:
`1 ≤ s13GK K M` comes from `one_le_s13GK` where the landed line used `omega`. -/
theorem m4_hbd_of_live_gk (K : ℕ) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (C δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
        M4SievedDoorSq_gk K R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ mrtDeliveredGrade C H * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R C δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed at the lever's base⟧
  have hglueH := hglue (Adoor M) (s13GK K M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (Adoor M) (s13GK K M))
      (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (Adoor M) (s13GK K M))
            (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ mrtDeliveredGrade C H * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-- **THE WAVE'S EXIT AT THE LEVER** — `m4_door_contradiction_of_live` (:537). -/
theorem m4_door_contradiction_of_live_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
            M4SievedDoorSq_gk K R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_gk K
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, _, _, _, hR⟩ := hexit C hC U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R C δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **The lever's exit, collision form** — `m4_door_False_of_live` (:555). -/
theorem m4_door_False_of_live_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
            M4SievedDoorSq_gk K R M Braw →
              logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_gk K
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_False
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hexit C hC U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock hfail =>
    hR (hhbd R C δ Braw M k hgates hBraw0 hgrade hsock) hfail⟩

/-- **THE M4-7 DELIVERABLE, SPLIT, AT THE LEVER** — `m4_hbd_of_live_split` (:710). -/
theorem m4_hbd_of_live_split_gk (K : ℕ) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (δ₀ δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
        M4GradeGateSplit R δ₀ δ Braw k →
        M4SievedDoorSq_gk K R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ δ₀ * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R δ₀ δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ Adoor M := by
    have h := Adoor_ge M
    omega
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed at the lever's base⟧
  have hglueH := hglue (Adoor M) (s13GK K M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (Adoor M) (s13GK K M))
      (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the SPLIT budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (Adoor M) (s13GK K M))
            (calQK (Adoor M) (s13GK K M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ δ₀ * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-- **THE WAVE'S EXIT, SPLIT, AT THE LEVER** — `m4_door_contradiction_of_live_split`
(:771). -/
theorem m4_door_contradiction_of_live_split_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4SievedDoorSq_gk K R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_split_gk K
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, -, hR⟩ := hexit U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R δ₀ δ Braw M k hgates hBraw0 hgrade hsock)⟩

-- #audit (temporary)

end Salt.MR

end
