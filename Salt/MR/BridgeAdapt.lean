/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.JointHead
import Salt.MR.WindowBridge

/-!
# BRIDGE-ADAPT — the gate-(c) chaining and the `hgrade` absorption (A-6)

The two remaining pre-assembly stones of the `HCENTER` ladder
(`docs/exploration/hsup-design.md`, the ⟦HCENTER FREEZE⟧ + ⟦AMENDMENT V2⟧ blocks):

* **STONE I — the gate-(c) chaining.**  `crossKer` (`JointHead.lean:76`) is descended onto
  the window-mass product `S₋·S₊` that `window_bridge` (`WindowBridge.lean:322`) evaluates,
  and the composed page is carried down to the exact per-`(α,β)` shape `sigma_wiring`'s
  `hbridge` integral consumes (`crossKer ≤ Kα·(1/σ)`, `σ = β+1/L`).  The `σ`-reparametrization
  and the `hbridge` adapter itself land here too; the ONE named residual is the concrete
  `Fbound` (SupF's SF-2/SF-3, on HOLD) — see the residual record at the end of §4.
* **STONE II — A-6 `hgrade`** (freeze ruling 2, V2 repair 3): the `∀ε ∃X₀(ε)` absorption of
  `loglog X` into `(log X)^ε`, at the pinned `ε = 1/1000`.

## The composed page (worked before Lean; the honest exponents at the corners)

Write `a := c₀−α−β` (the kernel's Poisson line), `L := log X`, `c₀ = 1+1/L`, `σ := β+1/L`.

**Gate (c), the kernel leg.**  Both window legs are bounded in `t` by their coefficient
masses (`norm_windowSum_le_mass`, constant in `t` — this is what `crossKer_le_mass_kernel`
does), leaving the kernel's own `L¹` mass.  Two faces are supplied:

* the **crude (Lorentzian) face** `kernel_L1_mass`: `∫‖hatKernel X h a (·−t₀)‖ ≤
  (X+h)^a·(2(X+h)/h)·(π/a) = B(a)·(π/a)`, `B(a) := 2(X+h)^{a+1}/h`  — this is the
  `B(a)`-form the `JointHead` residual record's gate (c) names;
* the **sharp face** `kernel_L1_mass_sharp` (`crossKer_le_amp_sharp` below): the same mass
  with `√L → log L` at the pin.

*Finding, recorded.*  The S-ladder route of the residual record (`mixed_weight_cs` ∘
`lorentz_compare` ∘ `k4_plan_le_diag_sharp`) reaches `B(a)·(π/a²)·√((c₀−β)(c₀+β))·S₋·S₊`,
which at `a, c₀∓β ≍ 1` is the SAME grade as the pointwise-mass route used here — because
`k4_plan_le_diag_sharp`'s diagonal `(π/c)·S²` is exactly `S²·∫(c²+τ²)⁻¹`, i.e. the `L²`
route gains nothing once the legs are read at their masses.  The pointwise route is taken:
it is shorter, it needs no `MemLp` plumbing, and it admits the SHARP kernel face (which the
Lorentzian S-ladder cannot use, `k4_plan_le_diag_sharp` being tied to the `1/(c²+τ²)`
weight).

**The amplitude at the pin** (`h = X·L^{−1/2}`, `c₀ = 1+1/L`):
`B(a) = 2(X+h)^{2+1/L−α−β}/h ≍ 2e·X·√L·X^{−α}·X^{−β}` — the `X^{−β}` is the whole point:
`window_bridge`'s honest product carries `X^{+β}` and **the two cancel**
(`amp_beta_cancel`: `(X+h)^{a+1}·X^β ≤ (X+h)^{2+1/L}·(X+h)^{−α}`, exactly).  Hence

  `crossKer α β ≤ C·((X+h)^{2+1/L}/h)·(X+h)^{−α}·y^{−2β}·min(L,1/σ)²`,  `C = 4π·9e(log 4+4)²`

(`crossKer_bridge_pinned`), and with `min(L,1/σ)² ≤ L·(1/σ)`, `y^{−2β} ≤ 1`:

  **`crossKer α β ≤ Kα·(1/σ)`,  `Kα := C·L·((X+h)^{2+1/L}/h)·(X+h)^{−α}`**

(`crossKer_sigma_bound`).  At the pin `Kα ≍ C·e·X·L^{3/2}·(X+h)^{−α}`, so
`∫₀^η Kα dα ≤ Kα(0)/log(X+h) ≍ X·√L` and `Agrade = (1/π)·L·∫₀^η Kα ≍ X·L^{3/2}` — the
refuter's predicted landing, i.e. the ledger's own PRE-EXISTING kernel-mass residual
(`kernel_mass_ledger`'s crude `X·√L` times the `L` the σ-cutoff returns), NOT worse.  The
sharp kernel face improves the `√L` to `log L` (`Agrade ≍ X·L·log L`) at no cost; both are
supplied, the consumer picks.

## The `σ` reparametrization and the `hbridge` adapter (§4)

`σ = β + 1/L` has Jacobian `1`, so `∫₀^η F(β+1/L) dβ = ∫_{1/L}^{η+1/L} F(σ) dσ`
(`sigma_reparam`), and `1/L ≤ η` plus `F ≥ 0` on the overshoot extends the upper limit to
`2η` (`sigma_reparam_le`) — the "σ = 2η scale-mismatch" of `supf-design.md`, closed.
`bridge_adapter` then produces `sigma_wiring`'s `hbridge` binder VERBATIM from
(i) the pointwise `crossKer ≤ Kα/σ` of §3 and (ii) a domination `supF α β ≤ Fbound(β+1/L)`.
`sigma_wiring_of_crossKer` chains it into `sigma_wiring`.  The residual is exactly the
concrete `Fbound` — see §4's record.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §1 — the gate-(c) descent: `crossKer` onto the window masses -/

/-- **Gate (c), step 1 — the pointwise-mass descent (`crossKer_le_mass_kernel`).**  Each
window leg of `crossKer` is bounded in `t` by its coefficient mass at its own line
(`norm_windowSum_le_mass`, valid at BOTH `c₀∓β` — the low leg's `c₀−β < 1` costs nothing),
constant in `t`, so the `t`-integral collapses onto the kernel's own `L¹` mass:

  `crossKer α β ≤ S₋·S₊·∫_t ‖hatKernel X h (c₀−α−β) (t−t₀)‖ dt`.

This is the step `window_bridge` is waiting for: its `S₋·S₊` is exactly this product. -/
theorem crossKer_le_mass_kernel {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    crossKer g X h y c₀ t₀ α β
      ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * ∫ t : ℝ, ‖hatKernel X h (c₀ - α - β) (t - t₀)‖ := by
  set Mm := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β) with hMm
  set Mp := ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
    ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β) with hMp
  have hMm0 : 0 ≤ Mm := Finset.sum_nonneg (fun n _ => by positivity)
  have hker : Integrable (fun t : ℝ => Mm * Mp * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) :=
    (((integrable_hatKernel hX hh hc).comp_sub_right t₀).norm).const_mul (Mm * Mp)
  have hint := crossKer_integrand_integrable (g := g) (X := X) (h := h) (y := y)
    (c₀ := c₀) (t₀ := t₀) (α := α) (β := β) hX hh hc
  unfold crossKer
  refine le_trans (integral_mono hint hker (fun t => ?_)) ?_
  · have hbm : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖ ≤ Mm := by
      rw [hMm]
      exact norm_windowSum_le_mass g X y (c₀ - β)
        (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp])
    have hbp : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mp := by
      rw [hMp]
      exact norm_windowSum_le_mass g X y (c₀ + β)
        (by rw [show (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp])
    have hstep : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
          * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Mm * Mp :=
      mul_le_mul hbm hbp (norm_nonneg _) hMm0
    exact mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  · rw [MeasureTheory.integral_const_mul]

/-- The `t₀`-shift is invisible to the full-line kernel mass (translation invariance). -/
theorem kernel_mass_shift (X h c t₀ : ℝ) :
    (∫ t : ℝ, ‖hatKernel X h c (t - t₀)‖) = ∫ t : ℝ, ‖hatKernel X h c t‖ :=
  integral_sub_right_eq_self (fun t : ℝ => ‖hatKernel X h c t‖) t₀

/-! ## §2 — the two kernel-amplitude faces -/

/-- **Gate (c) — the `B(a)`-form (`crossKer_le_amp`).**  The crude (Lorentzian) kernel face
`kernel_L1_mass` composed with the mass descent:

  `crossKer α β ≤ S₋·S₊·(X+h)^a·(2(X+h)/h)·(π/a)`,  `a = c₀−α−β`,

i.e. `crossKer ≤ B(a)·(π/a)·S₋·S₊` with `B(a) = 2(X+h)^{a+1}/h` — the amplitude the
`JointHead` residual record's gate (c) names (its extra `√((c₀−β)(c₀+β))/a` is the S-ladder
route's; at `a, c₀∓β ≍ 1` the two agree in grade). -/
theorem crossKer_le_amp {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    crossKer g X h y c₀ t₀ α β
      ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * ((X + h) ^ (c₀ - α - β) * (2 * (X + h) / h) * (Real.pi / (c₀ - α - β))) := by
  refine le_trans (crossKer_le_mass_kernel hX hh hc) ?_
  refine mul_le_mul_of_nonneg_left (kernel_L1_mass (t₀ := t₀) hX hh hc) ?_
  exact mul_nonneg (window_mass_nonneg g X y (c₀ - β)) (window_mass_nonneg g X y (c₀ + β))

/-- **Gate (c) — the SHARP face (`crossKer_le_amp_sharp`).**  The same descent against the
`Tsplit`-sharp kernel mass (`kernel_L1_mass_sharp`): for any split height `T > 0`,

  `crossKer α β ≤ S₋·S₊·(X+h)^a·(4·arsinh(T/a) + 4(X+h)/(hT))`.

At the pin `h = X·L^{−1/2}`, `T = L⁴`, `a ≍ 1` the bracket is `Θ(log L)` where the crude
face has `Θ(√L)` — the `√L → log L` sharpening, now available to `crossKer`'s consumer. -/
theorem crossKer_le_amp_sharp {g : ℕ → ℂ} {X h y c₀ t₀ α β T : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (hT : 0 < T) :
    crossKer g X h y c₀ t₀ α β
      ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
          * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
            ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
          * ((X + h) ^ (c₀ - α - β)
              * (4 * Real.arsinh (T / (c₀ - α - β)) + 4 * (X + h) / (h * T))) := by
  refine le_trans (crossKer_le_mass_kernel hX hh hc) ?_
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · rw [kernel_mass_shift]
    exact kernel_L1_mass_sharp hX hh hc hT
  · exact mul_nonneg (window_mass_nonneg g X y (c₀ - β)) (window_mass_nonneg g X y (c₀ + β))

/-! ## §3 — the composed page: the `X^β` cancellation and the `1/σ` shape -/

/-- **The `X^β` cancellation (`amp_beta_cancel`), exactly.**  The kernel amplitude's
`(X+h)^{a+1}` (with `a = c₀−α−β`, `c₀ = 1+1/L`) absorbs `window_bridge`'s `X^{β}` with
nothing left over beyond the `α`-decay:

  `(X+h)^{c₀−α−β+1}·X^β ≤ (X+h)^{2+1/L}·(X+h)^{−α}`.

The one inequality used is `X^β ≤ (X+h)^β` (`β ≥ 0`, `h > 0`) — the honest shape of the
freeze's "the `X^β` CANCELS". -/
theorem amp_beta_cancel {X h L c₀ α β : ℝ} (hX : 1 ≤ X) (hh : 0 < h)
    (hc₀ : c₀ = 1 + 1 / L) (hβ0 : 0 ≤ β) :
    (X + h) ^ (c₀ - α - β + 1) * X ^ β ≤ (X + h) ^ (2 + 1 / L) * (X + h) ^ (-α) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hsplit : (X + h) ^ (c₀ - α - β + 1)
      = (X + h) ^ (2 + 1 / L) * (X + h) ^ (-α) * (X + h) ^ (-β) := by
    rw [← Real.rpow_add hXh0, ← Real.rpow_add hXh0, hc₀]
    congr 1
    ring
  have hXβ : X ^ β ≤ (X + h) ^ β := Real.rpow_le_rpow hX0.le (by linarith) hβ0
  have hneg0 : (0 : ℝ) < (X + h) ^ (-β) := Real.rpow_pos_of_pos hXh0 _
  have hcancel : (X + h) ^ (-β) * X ^ β ≤ 1 := by
    have hkey : (X + h) ^ (-β) * (X + h) ^ β = 1 := by
      rw [← Real.rpow_add hXh0]
      simp
    calc (X + h) ^ (-β) * X ^ β ≤ (X + h) ^ (-β) * (X + h) ^ β :=
          mul_le_mul_of_nonneg_left hXβ hneg0.le
      _ = 1 := hkey
  have hbase0 : (0 : ℝ) ≤ (X + h) ^ (2 + 1 / L) * (X + h) ^ (-α) :=
    mul_nonneg (Real.rpow_nonneg hXh0.le _) (Real.rpow_nonneg hXh0.le _)
  calc (X + h) ^ (c₀ - α - β + 1) * X ^ β
      = ((X + h) ^ (2 + 1 / L) * (X + h) ^ (-α)) * ((X + h) ^ (-β) * X ^ β) := by
        rw [hsplit]; ring
    _ ≤ ((X + h) ^ (2 + 1 / L) * (X + h) ^ (-α)) * 1 :=
        mul_le_mul_of_nonneg_left hcancel hbase0
    _ = (X + h) ^ (2 + 1 / L) * (X + h) ^ (-α) := by ring

/-- **A-5 ∘ gate (c) — the pinned composed page (`crossKer_bridge_pinned`).**  The landed
`window_bridge` product substituted into the `B(a)`-form:

  `crossKer α β ≤ (2(X+h)^{c₀−α−β+1}/h)·(π/(c₀−α−β))·(710·X^β·y^{−2β}·min(L,1/σ)²)`,

`710 = 9e(log 4+4)²`, at the pinned home `c₀ = 1+1/L`, `L = log X`, `σ = β+1/L`.  Both sharp
Mertens factors are carried (V2 repair 1); the datum gate is `window_bridge`'s (`g`
1-bounded at primes). -/
theorem crossKer_bridge_pinned (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ α β σ : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 2) (hσ : σ = β + 1 / L) :
    crossKer g X h y c₀ t₀ α β
      ≤ (2 * (X + h) ^ (c₀ - α - β + 1) / h) * (Real.pi / (c₀ - α - β))
          * (9 * Real.exp 1 * (Real.log 4 + 4) ^ 2
              * (X ^ β * y ^ (-(2 * β))) * min L (1 / σ) ^ 2) := by
  have hX : (1 : ℝ) ≤ X := le_trans hy hyX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hc : (0 : ℝ) < c₀ - α - β := by rw [hc₀]; linarith
  -- the amplitude, in the `2(X+h)^{a+1}/h · π/a` normal form
  have hamp : (X + h) ^ (c₀ - α - β) * (2 * (X + h) / h) * (Real.pi / (c₀ - α - β))
      = (2 * (X + h) ^ (c₀ - α - β + 1) / h) * (Real.pi / (c₀ - α - β)) := by
    rw [Real.rpow_add hXh0, Real.rpow_one]
    field_simp
  have hamp0 : (0 : ℝ) ≤ (2 * (X + h) ^ (c₀ - α - β + 1) / h) * (Real.pi / (c₀ - α - β)) := by
    have h1 : (0 : ℝ) ≤ 2 * (X + h) ^ (c₀ - α - β + 1) / h :=
      div_nonneg (by positivity) hh.le
    have h2 : (0 : ℝ) ≤ Real.pi / (c₀ - α - β) := div_nonneg Real.pi_pos.le hc.le
    exact mul_nonneg h1 h2
  refine le_trans (crossKer_le_amp (g := g) (y := y) (t₀ := t₀) hX hh hc) ?_
  rw [hamp, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hamp0
  exact window_bridge g hg hL hL3 hy hyX hc₀ hβ0 (by linarith) hσ

/-- **THE EXIT — the per-`(α,β)` `1/σ` shape (`crossKer_sigma_bound`).**  The composed page
of `crossKer_bridge_pinned` collapsed to the form `sigma_wiring`'s `hbridge` integral
consumes:

  `crossKer α β ≤ Kα·(1/σ)`,  `Kα = 4π·9e(log 4+4)²·L·((X+h)^{2+1/L}/h)·(X+h)^{−α}`.

Three absorptions, each exact: `amp_beta_cancel` (the `X^β` cancellation), `π/a ≤ 2π` (from
`a = c₀−α−β ≥ 1/2`), `y^{−2β} ≤ 1`, and `min(L,1/σ)² ≤ L·(1/σ)` (the second `min` factor is
spent on the `L` the σ-cutoff returns).  At the pin `h = X·L^{−1/2}` this is
`Kα ≍ C·X·L^{3/2}·(X+h)^{−α}`, whence `Agrade ≍ X·L^{3/2}` — the ledger's pre-existing
kernel-mass residual, not a new one. -/
theorem crossKer_sigma_bound (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ α β σ : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 2) (hσ : σ = β + 1 / L) :
    crossKer g X h y c₀ t₀ α β
      ≤ (4 * Real.pi * (9 * Real.exp 1 * (Real.log 4 + 4) ^ 2) * L
          * ((X + h) ^ (2 + 1 / L) / h) * (X + h) ^ (-α)) * (1 / σ) := by
  have hX : (1 : ℝ) ≤ X := le_trans hy hyX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hc : (0 : ℝ) < c₀ - α - β := by rw [hc₀]; linarith
  have hchalf : (1 : ℝ) / 2 ≤ c₀ - α - β := by rw [hc₀]; linarith
  have hσ0 : (0 : ℝ) < σ := by rw [hσ]; linarith
  set A : ℝ := 9 * Real.exp 1 * (Real.log 4 + 4) ^ 2 with hA
  have hA0 : (0 : ℝ) ≤ A := by
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hA]; positivity
  refine le_trans (crossKer_bridge_pinned g hg hL hL3 hy hyX hc₀ hh hα0 hβ0 hαβ hσ) ?_
  -- (1) the `π/a ≤ 2π` step
  have hpi : Real.pi / (c₀ - α - β) ≤ 2 * Real.pi := by
    rw [div_le_iff₀ hc]
    nlinarith [Real.pi_pos]
  -- (2) the `y^{−2β} ≤ 1` step
  have hyβ : y ^ (-(2 * β)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  -- (3) the `min² ≤ L·(1/σ)` step
  have hminL : min L (1 / σ) ≤ L := min_le_left _ _
  have hminσ : min L (1 / σ) ≤ 1 / σ := min_le_right _ _
  have hmin0 : (0 : ℝ) ≤ min L (1 / σ) := le_min hL0.le (by positivity)
  have hminsq : min L (1 / σ) ^ 2 ≤ L * (1 / σ) := by
    calc min L (1 / σ) ^ 2 = min L (1 / σ) * min L (1 / σ) := by ring
      _ ≤ L * (1 / σ) := mul_le_mul hminL hminσ hmin0 hL0.le
  -- (4) the amplitude with the `X^β` cancelled
  have hcancel := amp_beta_cancel (X := X) (h := h) (L := L) (c₀ := c₀) (α := α) (β := β)
    hX hh hc₀ hβ0
  have hXβ0 : (0 : ℝ) ≤ X ^ β := Real.rpow_nonneg hX0.le _
  have hyβ0 : (0 : ℝ) ≤ y ^ (-(2 * β)) := Real.rpow_nonneg hy0.le _
  have hbase0 : (0 : ℝ) ≤ (X + h) ^ (2 + 1 / L) * (X + h) ^ (-α) :=
    mul_nonneg (Real.rpow_nonneg hXh0.le _) (Real.rpow_nonneg hXh0.le _)
  have hamp0 : (0 : ℝ) ≤ (X + h) ^ (c₀ - α - β + 1) := Real.rpow_nonneg hXh0.le _
  -- assemble: regroup, then bound factor by factor
  have hstep1 : (2 * (X + h) ^ (c₀ - α - β + 1) / h) * (Real.pi / (c₀ - α - β))
        * (A * (X ^ β * y ^ (-(2 * β))) * min L (1 / σ) ^ 2)
      ≤ (2 / h) * ((X + h) ^ (c₀ - α - β + 1) * X ^ β) * (2 * Real.pi) * A * 1 * (L * (1 / σ)) := by
    have e1 : (2 * (X + h) ^ (c₀ - α - β + 1) / h) * (Real.pi / (c₀ - α - β))
          * (A * (X ^ β * y ^ (-(2 * β))) * min L (1 / σ) ^ 2)
        = (2 / h) * ((X + h) ^ (c₀ - α - β + 1) * X ^ β) * (Real.pi / (c₀ - α - β)) * A
            * (y ^ (-(2 * β))) * (min L (1 / σ) ^ 2) := by
      field_simp
    rw [e1]
    have h2h0 : (0 : ℝ) ≤ 2 / h := by positivity
    have hprod0 : (0 : ℝ) ≤ (X + h) ^ (c₀ - α - β + 1) * X ^ β := mul_nonneg hamp0 hXβ0
    have hminsq0 : (0 : ℝ) ≤ min L (1 / σ) ^ 2 := sq_nonneg _
    have hbase : (0 : ℝ) ≤ (2 / h) * ((X + h) ^ (c₀ - α - β + 1) * X ^ β) :=
      mul_nonneg h2h0 hprod0
    have hpi0 : (0 : ℝ) ≤ Real.pi / (c₀ - α - β) := div_nonneg Real.pi_pos.le hc.le
    gcongr
  refine le_trans hstep1 ?_
  have hfin : (2 / h) * ((X + h) ^ (c₀ - α - β + 1) * X ^ β)
      ≤ (2 / h) * ((X + h) ^ (2 + 1 / L) * (X + h) ^ (-α)) :=
    mul_le_mul_of_nonneg_left hcancel (by positivity)
  have hrest0 : (0 : ℝ) ≤ (2 * Real.pi) * A * 1 * (L * (1 / σ)) := by
    have : (0 : ℝ) ≤ L * (1 / σ) := by positivity
    have hpi0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    nlinarith [mul_nonneg hpi0 hA0]
  calc (2 / h) * ((X + h) ^ (c₀ - α - β + 1) * X ^ β) * (2 * Real.pi) * A * 1 * (L * (1 / σ))
      = ((2 / h) * ((X + h) ^ (c₀ - α - β + 1) * X ^ β))
          * ((2 * Real.pi) * A * 1 * (L * (1 / σ))) := by
        ring
    _ ≤ ((2 / h) * ((X + h) ^ (2 + 1 / L) * (X + h) ^ (-α)))
          * ((2 * Real.pi) * A * 1 * (L * (1 / σ))) := mul_le_mul_of_nonneg_right hfin hrest0
    _ = (4 * Real.pi * A * L * ((X + h) ^ (2 + 1 / L) / h) * (X + h) ^ (-α)) * (1 / σ) := by
        field_simp
        ring

/-! ## §4 — the `σ` reparametrization and the `hbridge` adapter -/

/-- **The `σ = β + 1/L` reparametrization (Jacobian `1`).**  `∫₀^η F(β+1/L) dβ =
`∫_{1/L}^{η+1/L} F(σ) dσ` — the honest change of variables (a pure translation). -/
theorem sigma_reparam (F : ℝ → ℝ) (L η : ℝ) :
    (∫ β in (0 : ℝ)..η, F (β + 1 / L)) = ∫ σ in (1 / L)..(η + 1 / L), F σ := by
  rw [intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := η) F (1 / L)]
  norm_num

/-- **The upper-limit extension (the "σ = 2η scale-mismatch", closed).**  With `1/L ≤ η` the
reparametrized range `[1/L, η+1/L]` sits inside `[1/L, 2η]`, so a NONNEGATIVE integrand
extends upward:

  `∫₀^η F(β+1/L) dβ ≤ ∫_{1/L}^{2η} F(σ) dσ`. -/
theorem sigma_reparam_le {F : ℝ → ℝ} {L η : ℝ} (hL0 : 0 < L) (hη : 1 / L ≤ η)
    (hFnn : ∀ σ ∈ Ioc (1 / L) (2 * η), 0 ≤ F σ)
    (hI : IntervalIntegrable F volume (1 / L) (2 * η)) :
    (∫ β in (0 : ℝ)..η, F (β + 1 / L)) ≤ ∫ σ in (1 / L)..(2 * η), F σ := by
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hη0 : (0 : ℝ) < η := lt_of_lt_of_le hLinv hη
  rw [sigma_reparam F L η]
  refine intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith) ?_ hI
  rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with σ hσ
  exact hFnn σ hσ

/-- **THE `hbridge` ADAPTER (`bridge_adapter`).**  `sigma_wiring`'s `hbridge` binder
(`JointHead.lean:277`) produced VERBATIM from the two honest inputs:

* `hcross` — the per-`(α,β)` pointwise bound `crossKer α β ≤ Kα·(1/σ)` (§3's exit
  `crossKer_sigma_bound`, at the pinned home);
* `hFdom` — the domination `supF α β ≤ Fbound(β+1/L)` of the `𝒮·𝓛` sup by the σ-parametrized
  `Fbound` that `sigma_wiring`'s `hpret`/`htriv` are stated for.

Everything else is plumbing: nonnegativity of `crossKer` (`crossKer_nonneg`), the
translation `sigma_reparam`, and the upper-limit extension `sigma_reparam_le`.  The
integrability sockets are the house's conditional-assembly form (cf. `joint_cs_factoring`). -/
theorem bridge_adapter {g : ℕ → ℂ} {X h y c₀ t₀ L η Kα α : ℝ} {supF : ℝ → ℝ → ℝ}
    {Fbound : ℝ → ℝ}
    (hL0 : 0 < L) (hη : 1 / L ≤ η) (hKα0 : 0 ≤ Kα)
    (hsup0 : ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ supF α β)
    (hcross : ∀ β ∈ Icc (0 : ℝ) η,
        crossKer g X h y c₀ t₀ α β ≤ Kα * (1 / (β + 1 / L)))
    (hFdom : ∀ β ∈ Icc (0 : ℝ) η, supF α β ≤ Fbound (β + 1 / L))
    (hFnn : ∀ σ ∈ Icc (1 / L) (2 * η), 0 ≤ Fbound σ)
    (hIβ : IntervalIntegrable (fun β => supF α β * crossKer g X h y c₀ t₀ α β) volume 0 η)
    (hIshift : IntervalIntegrable
        (fun β => Kα * (Fbound (β + 1 / L) / (β + 1 / L))) volume 0 η)
    (hIσ : IntervalIntegrable (fun σ => Fbound σ / σ) volume (1 / L) (2 * η)) :
    (∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
      ≤ Kα * ∫ σ in (1 / L)..(2 * η), Fbound σ / σ := by
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hη0 : (0 : ℝ) < η := lt_of_lt_of_le hLinv hη
  -- STEP 1 — the pointwise bound on `[0, η]`
  have hpt : ∀ β ∈ Icc (0 : ℝ) η,
      supF α β * crossKer g X h y c₀ t₀ α β ≤ Kα * (Fbound (β + 1 / L) / (β + 1 / L)) := by
    intro β hβ
    obtain ⟨hβ0, hβη⟩ := hβ
    have hσ0 : (0 : ℝ) < β + 1 / L := by linarith
    have hFβ : (0 : ℝ) ≤ Fbound (β + 1 / L) := by
      refine hFnn (β + 1 / L) ⟨by linarith, by linarith⟩
    have hs0 : (0 : ℝ) ≤ supF α β := hsup0 β ⟨hβ0, hβη⟩
    have hKσ : (0 : ℝ) ≤ Kα * (1 / (β + 1 / L)) := by positivity
    calc supF α β * crossKer g X h y c₀ t₀ α β
        ≤ supF α β * (Kα * (1 / (β + 1 / L))) :=
          mul_le_mul_of_nonneg_left (hcross β ⟨hβ0, hβη⟩) hs0
      _ ≤ Fbound (β + 1 / L) * (Kα * (1 / (β + 1 / L))) :=
          mul_le_mul_of_nonneg_right (hFdom β ⟨hβ0, hβη⟩) hKσ
      _ = Kα * (Fbound (β + 1 / L) / (β + 1 / L)) := by
          rw [div_eq_mul_inv, one_div]; ring
  -- STEP 2 — integrate the pointwise bound
  have hmono : (∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
      ≤ ∫ β in (0 : ℝ)..η, Kα * (Fbound (β + 1 / L) / (β + 1 / L)) :=
    intervalIntegral.integral_mono_on hη0.le hIβ hIshift hpt
  refine le_trans hmono ?_
  -- STEP 3 — pull `Kα` out, reparametrize, extend the upper limit
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ hKα0
  refine sigma_reparam_le (F := fun σ => Fbound σ / σ) hL0 hη (fun σ hσ => ?_) hIσ
  exact div_nonneg (hFnn σ ⟨hσ.1.le, hσ.2⟩) (by linarith [hσ.1])

/-- **The chained σ-cutoff (`sigma_wiring_of_crossKer`).**  `bridge_adapter` composed with
`sigma_wiring`: the `(1+M)e^{−M}L` grade for the per-`α` `β`-integral, now reachable from the
POINTWISE `crossKer ≤ Kα/σ` page of §3 rather than from an abstract `hbridge`. -/
theorem sigma_wiring_of_crossKer {g : ℕ → ℂ} {X h y c₀ t₀ L η M Kα α : ℝ}
    {supF : ℝ → ℝ → ℝ} {Fbound : ℝ → ℝ}
    (hL : 3 ≤ L) (hM : 0 ≤ M) (hlo : 1 / L ≤ 2 * η) (hη : 1 / L ≤ η) (hKα0 : 0 ≤ Kα)
    (hint : IntervalIntegrable (fun σ => Fbound σ / σ) volume (1 / L) (2 * η))
    (hpret : ∀ σ ∈ Icc (1 / L) (2 * η), Fbound σ ≤ Real.exp (-M) * L)
    (htriv : ∀ σ ∈ Icc (1 / L) (2 * η), Fbound σ ≤ 1 / σ)
    (hsup0 : ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ supF α β)
    (hcross : ∀ β ∈ Icc (0 : ℝ) η,
        crossKer g X h y c₀ t₀ α β ≤ Kα * (1 / (β + 1 / L)))
    (hFdom : ∀ β ∈ Icc (0 : ℝ) η, supF α β ≤ Fbound (β + 1 / L))
    (hFnn : ∀ σ ∈ Icc (1 / L) (2 * η), 0 ≤ Fbound σ)
    (hIβ : IntervalIntegrable (fun β => supF α β * crossKer g X h y c₀ t₀ α β) volume 0 η)
    (hIshift : IntervalIntegrable
        (fun β => Kα * (Fbound (β + 1 / L) / (β + 1 / L))) volume 0 η) :
    (∫ β in (0 : ℝ)..η, supF α β * crossKer g X h y c₀ t₀ α β)
      ≤ Kα * ((1 + M) * Real.exp (-M) * L) :=
  sigma_wiring hL hM hlo hKα0 hint hpret htriv
    (bridge_adapter (by linarith) hη hKα0 hsup0 hcross hFdom hFnn hIβ hIshift hint)

/-! ### RESIDUAL RECORD (§4) — what the adapter still waits for

`bridge_adapter`/`sigma_wiring_of_crossKer` close the WIRING of the `hbridge` residual
recorded at `JointHead.lean:598-650`: its items 1 (the parameter relations `c₀ = 1+1/L`,
`L = log X`) and 2 (the `σ ⇄ [1/L, 2η]` range) are now discharged — item 1 by
`WindowBridge`'s pinned hypotheses flowing through `crossKer_bridge_pinned`, item 2 by
`sigma_reparam`/`sigma_reparam_le` under the explicit gate `1/L ≤ η`.

**The ONE remaining input is the record's item 3, unchanged: a CONCRETE `Fbound`.**  The
adapter consumes it as `hFdom : supF α β ≤ Fbound (β + 1/L)` together with `sigma_wiring`'s
own `hpret`/`htriv` for that same `Fbound`; supplying it is SupF's pending pretentious
residual (`docs/exploration/supf-design.md`, SF-2/SF-3, on HOLD — `head_pin_bound` lands the
pin `σ = 1/L`, the `loglog X − M(t)` evaluation is available only at the principal datum).
Nothing in this file assumes it; nothing in this file weakens it.

The `hIshift` socket is pure plumbing (interval-integrability of the translated integrand);
it is a hypothesis rather than a derivation only because `IntervalIntegrable.comp_add_right`
carries an autoparam side goal that a general `Fbound` cannot discharge — with any concrete
`Fbound` it follows from `hint` by `comp_add_right` + `mono_set`. -/

/-! ## §5 — A-6: the `hgrade` absorption `loglog X ≤ (log X)^ε`

The freeze's ruling 2 (V2 repair 3): the supplier states `S0` with a `+ε` slot, the sharp
kernel's `loglog X` deficit absorbed as `(log X)^{−1/(64e)+ε}`.  The quantifier order is
`∀ε ∃X₀(ε)`, and the pin is `ε := 1/1000`.

**The price tag (recorded, per the V2 amendment).**  The witness produced below is
`X₀(C,ε) = exp((max 1 (2C/ε))^{2/ε})`, i.e. `X₀(ε) ≍ exp(C^{1/ε})` — at `ε = 1/1000` this is
the campaign's dominant threshold.  It is EXISTENTIAL-HARMLESS (no landed statement's
constant depends on it; the `∃X₀` is the whole interface), and **Route D** (sharp truncation
+ a `Λ`-mean-value stone, `[C, 400-700]`) is the priced effective alternative should the
threshold ever need to be a number.

**The ε-caps** (both satisfied with room by `ε = 1/1000 = 0.001`): `1/(192e) = 0.00184` is
the critical-path cap (keeps the ball leg off the critical path); `1/(64e) − 1/500 = 0.00375`
is the hard door wall.  `0.001 < 0.00184 < 0.00375`.

The elementary page is `Real.log_le_rpow_div` (`log t ≤ t^ε/ε`) applied at `ε/2`, the
leftover `2C/ε` swallowed by the second half-power — no `isLittleO` extraction is needed
(the corpus precedent `logpow4_le_sqrt_eventually` routes through `Filter.Eventually`; the
direct route here is shorter AND effective, which is strictly more than the interface asks). -/

/-- **A-6 — the general absorption stone (`loglog_absorb`).**  For every constant `C ≥ 0` and
every `ε > 0` there is a threshold `X₀` beyond which the `loglog` is swallowed by an
arbitrarily small power of the log:

  `∀ X ≥ X₀,  1 ≤ log X  ∧  C·log(log X) ≤ (log X)^ε`.

Witness: `X₀ = exp((max 1 (2C/ε))^{2/ε})`.  Route: `log t ≤ t^{ε/2}/(ε/2)` at `t = log X`,
then `2C/ε ≤ t^{ε/2}` by the choice of `X₀`, and `t^{ε/2}·t^{ε/2} = t^ε`. -/
theorem loglog_absorb {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      1 ≤ Real.log X ∧ C * Real.log (Real.log X) ≤ Real.log X ^ ε := by
  set B : ℝ := max 1 (2 * C / ε) with hB
  have hB1 : (1 : ℝ) ≤ B := by rw [hB]; exact le_max_left _ _
  have hB0 : (0 : ℝ) < B := by linarith
  have hBr : 2 * C / ε ≤ B := by rw [hB]; exact le_max_right _ _
  set T : ℝ := B ^ (2 / ε) with hT
  have hT1 : (1 : ℝ) ≤ T := by rw [hT]; exact Real.one_le_rpow hB1 (by positivity)
  refine ⟨Real.exp T, Real.exp_pos T, fun X hX => ?_⟩
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos T) hX
  have hlogT : T ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos T) hX
    rwa [Real.log_exp] at hmono
  have hlog1 : (1 : ℝ) ≤ Real.log X := le_trans hT1 hlogT
  refine ⟨hlog1, ?_⟩
  have ht0 : (0 : ℝ) < Real.log X := by linarith
  -- step 1: the elementary page at the half-power
  have hstep1 : Real.log (Real.log X) ≤ Real.log X ^ (ε / 2) / (ε / 2) :=
    Real.log_le_rpow_div ht0.le (by linarith)
  -- step 2: the constant is below the half-power
  have hTpow : T ^ (ε / 2) = B := by
    rw [hT, ← Real.rpow_mul hB0.le, show 2 / ε * (ε / 2) = 1 from by field_simp,
      Real.rpow_one]
  have hpow : B ≤ Real.log X ^ (ε / 2) := by
    have hmono : T ^ (ε / 2) ≤ Real.log X ^ (ε / 2) :=
      Real.rpow_le_rpow (by linarith) hlogT (by linarith)
    rwa [hTpow] at hmono
  have h2Cε : 2 * C / ε ≤ Real.log X ^ (ε / 2) := le_trans hBr hpow
  -- step 3: assemble
  have hhalf0 : (0 : ℝ) ≤ Real.log X ^ (ε / 2) := Real.rpow_nonneg ht0.le _
  have hsq : Real.log X ^ (ε / 2) * Real.log X ^ (ε / 2) = Real.log X ^ ε := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  have hC1 : C * Real.log (Real.log X) ≤ C * (Real.log X ^ (ε / 2) / (ε / 2)) :=
    mul_le_mul_of_nonneg_left hstep1 hC
  have heq : C * (Real.log X ^ (ε / 2) / (ε / 2)) = (2 * C / ε) * Real.log X ^ (ε / 2) := by
    field_simp
  have hfin : (2 * C / ε) * Real.log X ^ (ε / 2)
      ≤ Real.log X ^ (ε / 2) * Real.log X ^ (ε / 2) :=
    mul_le_mul_of_nonneg_right h2Cε hhalf0
  rw [heq] at hC1
  linarith [hsq ▸ hfin]

/-- **A-6 — the consumer-shaped corollary (`loglog_absorb_pow`).**  The `C`-absorption in the
shape the supplier's head actually carries: for every `C ≥ 0`, `ε > 0` and every exponent
`a`,

  `C·loglog X·(log X)^{−a} ≤ (log X)^{−a+ε}`  for `X ≥ X₀(C,ε)`.

(The `a`-slot is free: the two sides differ by the factor `(log X)^{−a} > 0`.)  This is the
form the `T1_decay_conditional_final` head consumes when the sharp kernel's `loglog X`
deficit is absorbed into the exponent. -/
theorem loglog_absorb_pow {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (a : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      C * Real.log (Real.log X) * Real.log X ^ (-a) ≤ Real.log X ^ (-a + ε) := by
  obtain ⟨X₀, hX₀0, hX₀⟩ := loglog_absorb hC hε
  refine ⟨X₀, hX₀0, fun X hX => ?_⟩
  obtain ⟨hlog1, hmain⟩ := hX₀ X hX
  have ht0 : (0 : ℝ) < Real.log X := by linarith
  have hsplit : Real.log X ^ (-a + ε) = Real.log X ^ (-a) * Real.log X ^ ε :=
    Real.rpow_add ht0 _ _
  rw [hsplit]
  calc C * Real.log (Real.log X) * Real.log X ^ (-a)
      = Real.log X ^ (-a) * (C * Real.log (Real.log X)) := by ring
    _ ≤ Real.log X ^ (-a) * Real.log X ^ ε :=
        mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg ht0.le _)

/-- **A-6 at the PIN `ε = 1/1000`** (V2 repair 3).  The instance the `HCENTER` supplier
cites; `1/1000` sits below both caps (`1/(192e) ≈ 0.00184`, `1/(64e) − 1/500 ≈ 0.00375`). -/
theorem loglog_le_log_rpow_pin :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      1 ≤ Real.log X ∧ Real.log (Real.log X) ≤ Real.log X ^ ((1 : ℝ) / 1000) := by
  obtain ⟨X₀, hX₀0, hX₀⟩ := loglog_absorb (C := 1) (ε := (1 : ℝ) / 1000)
    (by norm_num) (by norm_num)
  refine ⟨X₀, hX₀0, fun X hX => ?_⟩
  obtain ⟨hlog1, hmain⟩ := hX₀ X hX
  exact ⟨hlog1, by linarith⟩

/-- **A-6 at the pin, consumer shape.**  `C·loglog X·(log X)^{−a} ≤ (log X)^{−a+1/1000}`
eventually, for every `C ≥ 0` and every `a`. -/
theorem loglog_absorb_pow_pin {C : ℝ} (hC : 0 ≤ C) (a : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      C * Real.log (Real.log X) * Real.log X ^ (-a)
        ≤ Real.log X ^ (-a + (1 : ℝ) / 1000) :=
  loglog_absorb_pow hC (by norm_num) a

end Salt.MR
