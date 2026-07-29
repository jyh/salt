/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetGradedBalance
import Salt.MR.PinFamily2

/-!
# USetGradedPrice — the PRICING RECONCILIATION of the graded `hU` (ROUTE G, stone G1b-PRICE)

`USetGradedBalance` (G1b) supplies the graded `hU` row STRUCTURALLY, with the two grade
budgets `KS` and `R̄` as binders.  Pricing them is what this file does — and doing it forced
the three-slot reconciliation ⟦G1b⟧'s own Zeno note names:

1. the SUPPLY delivers `cofactorRbd` — the `q = 1/2` fused bound (`CofactorSupply`), whose far
   arm is `farErr`'s `√(log W)` denominator;
2. the CERTIFICATE that closes the far arm (`PinFamily.farErr34_local_closes`) lives at the
   `q = 3/4` denominator (`Transfer34.farErr34`) AND at the R2 truncation height `T*₂`, not at
   `CofactorLocal`'s `T*(M, log M)`;
3. both landed pricing stones (`Transfer34.Rbd34_grade_priced`,
   `USetResiduals.Rbd_grade_priced`) still write the AMBIENT `(Dmax + 1)` slot.

The reconciliation is §1: the localized dichotomy re-taken at the `T*₂` window, so that CASE B
hands back the radius `T*₂(M, log M)` — which is EXACTLY `farErr34_local_closes`' `Rmax` slot.
Then §2 prices the fused bound at the ratified numerals, and §4 spends it on the graded row.

## ⚑ THE WINDOW-ALIGNMENT VERDICT (the honest finding of this wave) ⚑

The dichotomy's split window must (a) CONTAIN every window the CASE-A floor is consumed on,
and (b) BE the radius CASE B reports.  The two demands pull against each other, and the
numbers decide:

* `log T*(Y, log Y) = 4·loglog Y + log Y/(4·loglog Y)` — an `L/(4 log L)` scale
  (`CofactorLocal.log_Tstar_self`);
* `log T*₂(Y, log Y) = L^{2/5} + L^{3/5}` (`PinFamily.log_Tstar2_self`).

At the family gate `L = 32768` these are `≈ 796` against `≈ 576`, and the gap only widens:
**`T*₂ < T*` throughout the live range.**  So splitting at `T*₂` — which (b) forces, since
`farErr34` at `Rmax = T*(M)` diverges like `L^{1/4}/log L` against `(log W)^{3/4}` — makes the
split window SMALLER than the windows the LANDED CASE-A supply
(`CofactorSupply.caseA_partial_supply_slice`, whose `hMwin` is at `T*(k, log k)`) consumes.
The floor arm therefore cannot be fed from the landed CASE-A page.

The aligned CASE-A page is the `y₂` one: `PinFamily2`'s `rhs_grade_at_scale_trunc2` /
`rhs_grade_at_scale_closed_star2` consume their far kernel at `T := T*₂(k, log k)`
(`hKf`/`hgate` there), and their exit constant is `caseAS2` (`PinFamily2` §5).  But that chain
is the BALL arm's shape — the minimality floor `hmin` at the fixed exponent `c = 1/(2e)` — not
CASE A's `c`-generic WINDOW-FLOOR shape; `PinFamily2`'s own residual list says so in as many
words (residuals 2 and 3: "the free-`c` width layer at `y₂`" and "`caseA_rhs_socket2`").

So this file carries the CASE-A page as ONE named socket, `CaseASocket2` (§1), and discharges
everything else.  That is `hRHS_socket_star2`'s posture, deliberately: a socket whose shape is
exactly what the missing `y₂` window-floor chain will produce, never a hypothesis that hides a
divergence.  **The `q = 1/2` alternative is NOT available: carrying
`cofactorRbd … (T*(M, log M)) ≤ C·(log X)^{−ρ}` as a hypothesis would be a silent vacuity —
`CofactorLocal.farErr_local_window_ge` refutes it.**

## The stones

* **§1 (P-1)** `Tstar2_window_mono`, `pocket_transport_pin2` (the dichotomy at the `y₂`
  window), `damped_partial_transfer_34` (CASE B at `q = 3/4`, the pocket's cap consumed
  DIRECTLY at `P/32`), `cofactorRbd34loc` + `cofactor_Rbd34_local`, and
  `tL_supply_discharged34_local` — `CofactorLocal`'s L-2/L-3 at the repaired arm.
* **§2 (P-2)** `caseAS2_arm_priced`, `Rbd34loc_uniform` (the worst corner, `T*₂` slot
  included), `gradeCR2` and `Rbd34loc_grade_priced` — `R̄₃₄ ≤ C_R₂·(log X)^{−ρ₂₉₃}` with
  `C_R₂` EXPLICIT.
* **§3 (P-3)** `thinBundleG_at_pin` — the graded thinness bundle at the §8.3 pin.
* **§4 (P-4)** `hUG34_supplied`, `hUG34_priced` — the graded row with `hU` discharged at the
  REPAIRED far arm and its balance priced.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §8.3 pp. 27–29;
`docs/exploration/hsup-design.md` ⟦V6a⟧/⟦V6b⟧/⟦V7⟧ (R1+R2+R3).
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open Finset MeasureTheory

/-! ## §1 (P-1) — the LOCALIZED dichotomy at the `y₂` truncation height -/

/-- `exp 32768 ≤ exp(exp 165)`: the `q = 3/4` conversion threshold clears the R2 family gate,
so a single hypothesis `ballQuarterThreshold ≤ k₀` feeds BOTH the pocket's `P/32` conversion
(`Transfer34.far_transfer_sup_34_of_pocket_cap`) and the `T*₂` monotonicity
(`PinFamily2.Tstar2_mono`).  The numeral leg is the `exp 12` one (`131072 ≤ e^{12}`, the
⟦V7⟧ trap: `e^{11}` does NOT clear `2^{17}`). -/
lemma pin2Gate_le_ballQuarterThreshold : pin2Gate ≤ ballQuarterThreshold := by
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h12 : Real.exp 12 = Real.exp 1 ^ (12 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpw := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he 12
  have hbig : (131072 : ℝ) ≤ Real.exp 12 := by
    rw [h12]; norm_num at hpw ⊢; linarith
  have h165 : Real.exp 12 ≤ Real.exp 165 := Real.exp_le_exp.mpr (by norm_num)
  unfold pin2Gate ballQuarterThreshold
  exact Real.exp_le_exp.mpr (by linarith)

/-- **The `y₂` split window dominates every consumed `y₂` window.**  `k ↦ T*₂(k, log k)` climbs
across the co-factor window (`PinFamily2.Tstar2_mono`), so the ONE window
`|v − t| ≤ T*₂(M, log M)` contains every `|v − t| ≤ T*₂(k, log k)`, `k ∈ [k₀, M]`.  Twin of
`CofactorLocal.Tstar_window_mono`, at the R2 height and with the R2 family gate. -/
lemma Tstar2_window_mono {k₀ M k : ℕ} (hk₀pin : pin2Gate ≤ (k₀ : ℝ))
    (hk1 : k₀ ≤ k) (hk2 : k ≤ M) :
    Tstar2 (k : ℝ) (Real.log (k : ℝ)) ≤ Tstar2 (M : ℝ) (Real.log (M : ℝ)) := by
  have hk₀k : ((k₀ : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk1
  have hkM : ((k : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hk2
  exact Tstar2_mono (le_trans hk₀pin hk₀k) hkM

/-- **THE CASE-A SOCKET AT `y₂`** (`CaseASocket2`).  The conclusion of the `y₂` twin of
`CofactorSupply.caseA_partial_supply_slice`: the damped datum's twisted partial sums are
linear with the R2 CASE-A constant `caseAS2` (`PinFamily2` §5), under the window floor stated
on the `T*₂`-windows.

This is the ONE page this file does not own — see the module docstring's window-alignment
verdict.  It is stated (law #253) rather than assumed off-stage, and its shape is fixed by
what `PinFamily2`'s `y₂` machinery consumes: the far kernel at `T := T*₂(k, log k)`, so the
floor binder is at `|v − t| ≤ T*₂(k, log k)`; and the exit constant is `caseAS2`, whose only
difference from `caseAS` is `farCStar ↝ farCStar2`. -/
def CaseASocket2 (g : ℕ → ℂ) (P Q : ℕ) (c Cb X θ : ℝ) (k₀ M : ℕ) (t : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
      cofactorMfl X θ (k₀ : ℝ)
        ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ)) →
    ∀ k : ℕ, k₀ ≤ k → k ≤ M →
      ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
        ≤ caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) * (k : ℝ)

/-- **P-1a — THE LOCALIZED POCKET TRANSPORT AT `y₂`** (`pocket_transport_pin2`).  At a FIXED
damping parameter `x ∈ [0,1]`: either the CASE-A window floor holds at `cofactorMfl X θ k₀` on
every `T*₂`-window, or the CASE-B pocket exists at `x` — **with its centre inside the `y₂`
truncation window**, `|t − t₁'| ≤ T*₂(M, log M)`.

Twin of `CofactorLocal.pocket_transport_local`, with two changes:

1. the `by_cases` window is `|v − t| ≤ T*₂(M, log M)` (R2's height) in place of
   `T*(M, log M)`, and the ¬-branch moves between windows by `Tstar2_window_mono`;
2. the pocket branch reports its cap in the SHARP form `𝔻² ≤ (1/32 − θ)loglog X` and stops
   there — the `∀ y, 𝔻² ≤ P(y)/8` leg of the landed dichotomy is GONE, because
   `Transfer34.far_transfer_sup_34_of_pocket_cap` consumes the cap directly at the `P/32`
   convention.  With it goes the loglog descent gate `hll`: at `q = 3/4` the descent is
   charged inside the transfer, at its own explicit gate.

The single contour gate `hTM : |t| + T*₂(M, log M) ≤ 3X` still supplies the collision's box
binder `|t₁'| ≤ 3X`, exactly as in the landed twin. -/
theorem pocket_transport_pin2 {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {k₀ M : ℕ} {X θ t x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀pin : pin2Gate ≤ (k₀ : ℝ)) (hMX : (M : ℝ) ≤ X)
    (hTM : |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X) :
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar2 (k : ℝ) (Real.log (k : ℝ)) →
        cofactorMfl X θ (k₀ : ℝ)
          ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ))
      ∨ (∃ t₁' : ℝ, |t - t₁'| ≤ Tstar2 (M : ℝ) (Real.log (M : ℝ)) ∧ |t₁'| ≤ 3 * X ∧
          pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
            ≤ (1 / 32 - θ) * Real.log (Real.log X)) := by
  classical
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  have hEll : ∀ n : ℕ, ‖ellLin (gxDatum g P Q x) n‖ ≤ 1 := ellLin_norm_le_one _ hgx
  by_cases hpocket : ∃ v : ℝ, |v - t| ≤ Tstar2 (M : ℝ) (Real.log (M : ℝ)) ∧
      pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) X
        ≤ (1 / 32 - θ) * Real.log (Real.log X)
  · -- the pocket arm: the RADIUS comes with the pocket
    right
    obtain ⟨v, hvwin, hv⟩ := hpocket
    have hvabs : |v| ≤ 3 * X := by
      have h1 : |v| ≤ |v - t| + |t| := by
        have := abs_add_le (v - t) t
        simpa using this
      linarith
    refine ⟨v, ?_, hvabs, hv⟩
    rw [abs_sub_comm]
    exact hvwin
  · -- the floor arm: the descent is PRICED, and the window is the `y₂` one
    left
    simp only [not_exists, not_and, not_le] at hpocket
    intro k hk1 hk2 v hv
    have hcw : ∀ n : ℕ, ‖costwist v n‖ ≤ 1 := fun n => le_of_eq (costwist_norm v n)
    have hvwin : |v - t| ≤ Tstar2 (M : ℝ) (Real.log (M : ℝ)) :=
      le_trans hv (Tstar2_window_mono hk₀pin hk1 hk2)
    have hXbig := hpocket v hvwin
    have hkM : ((k : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hk2
    have hkX : ⌊((k : ℕ) : ℝ)⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono (le_trans hkM hMX)
    have htail := pretDistSq_tail_le (f := ellLin (gxDatum g P Q x)) (g := costwist v)
      hEll hcw hkX
    have hSk : Salt.Mertens.SPartial ((k₀ : ℕ) : ℝ) ≤ Salt.Mertens.SPartial ((k : ℕ) : ℝ) := by
      refine SPartial_mono_floor ?_
      rw [Nat.floor_natCast, Nat.floor_natCast]
      exact hk1
    unfold cofactorMfl
    linarith

/-- **P-1b — CASE B AT `q = 3/4`, at the damped co-factor datum**
(`damped_partial_transfer_34`).  `CofactorBall.damped_partial_transfer` with
`far_transfer_sup` replaced by `Transfer34.far_transfer_sup_34_of_pocket_cap`: the window
binders and the datum split are byte-identical (the same `ramRdampCoeff` support page), and
the ONLY change is which transfer prices the far arm — hence which cap the pocket must
supply.  The landed twin asks for `∀ y ∈ [k₀,M], 𝔻² ≤ P(y)/8`; this one asks for the pocket's
OWN cap `𝔻²(ℓ(g_x), p^{it₁'}; X) ≤ (1/32 − θ)loglog X` plus the two conversion gates
(`ballQuarterThreshold ≤ k₀`, the loglog descent charge `hgate`), and pays `farSupS34`. -/
theorem damped_partial_transfer_34 {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    {H : ℝ} {N Xn P Q j M k₀ : ℕ} {x t t₁' Rmax R X θ : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀th : ballQuarterThreshold ≤ (k₀ : ℝ)) (hMN : M ≤ N)
    (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j) (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1)
    (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1)) (hMX : (M : ℝ) ≤ X)
    (hgate : 18 + Real.log (Real.log X) - Real.log (Real.log (k₀ : ℝ))
      ≤ 32 * θ * Real.log (Real.log X))
    (hcap : pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
      ≤ (1 / 32 - θ) * Real.log (Real.log X))
    (hR0 : 0 < R) (hRle : R ≤ 1 + |t - t₁'|) (hRmax : |t - t₁'| ≤ Rmax) :
    ∀ m : ℕ, m ≤ M →
      ‖spolyA (ramRdampCoeff H N Xn P Q j (ellLin g) x) t m‖
        ≤ farSupS34 (k₀ : ℝ) (M : ℝ) Rmax R * (m : ℝ) := by
  have hMk : (M : ℝ) ≤ 2 * (k₀ : ℝ) := by linarith
  have hMtop2 : (M : ℝ) ≤ 2 * ramRbot H Xn j := by linarith
  refine far_transfer_sup_34_of_pocket_cap (f := ellLin (gxDatum g P Q x)) hMk (ellLin_one _)
    (ellLin_mul_coprime_all _)
    (fun n => ellLin_norm_le_one _ (fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp) n)
    ?_ ?_ hk₀th hMX hgate hcap hR0 hRle hRmax
  · -- `hsupp`: below the cut the window indicator is off
    intro n hn
    have hlt : (n : ℝ) < ramRbot H Xn j := by
      have : (n : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hn
      linarith
    rw [ramRdampCoeff, if_neg (notMem_ramRrange_of_lt hlt)]
  · -- `hDatum`: inside the window the coefficient IS `ℓ(g_x)`
    intro n hn1 hn2
    have hmem : n ∈ ramRrange H N Xn j := by
      have hnk : (k₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn2
      rw [ramRrange, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hn2 hMN⟩, ?_, ?_⟩
      · have : ramRbot H Xn j ≤ (n : ℝ) := by linarith
        rwa [ramRbot] at this
      · have : (n : ℝ) ≤ 2 * ramRbot H Xn j := le_trans hnM hMtop2
        rw [ramRbot] at this
        linarith
    rw [ramRdampCoeff_ellLin, if_pos hmem]

/-- **THE FUSED `Rbd` AT THE REPAIRED ARM** (`cofactorRbd34loc`).  `CofactorSupply.cofactorRbd`
with BOTH arms moved to the R2/R3 pins: the CASE-A arm at `caseAS2` (`farCStar2`, the `y₂`
far constant) and the CASE-B arm at `farSupS34` (the `(log W)^{3/4}` denominator).  A NEW
definition — `cofactorRbd` and `Transfer34.cofactorRbd34` are untouched. -/
def cofactorRbd34loc (c Cb X θ W Y Rmax R : ℝ) : ℝ :=
  3 * max (2 * caseAS2 c Cb (cofactorMfl X θ W) W) (farSupS34 W Y Rmax R)

lemma cofactorRbd34loc_nonneg {c Cb X θ W Y Rmax R : ℝ} (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hW : 1 ≤ W) : 0 ≤ cofactorRbd34loc c Cb X θ W Y Rmax R := by
  have h1 : (0 : ℝ) ≤ 2 * caseAS2 c Cb (cofactorMfl X θ W) W := by
    have := caseAS2_nonneg (c := c) (Cb := Cb) (M := cofactorMfl X θ W) (W := W) hc1 hCb0 hW
    linarith
  have h2 : 2 * caseAS2 c Cb (cofactorMfl X θ W) W
      ≤ max (2 * caseAS2 c Cb (cofactorMfl X θ W) W) (farSupS34 W Y Rmax R) := le_max_left _ _
  unfold cofactorRbd34loc
  linarith

/-- **P-1c — THE CO-FACTOR `Rbd` AT THE REPAIRED FAR ARM** (`cofactor_Rbd34_local`).
`CofactorLocal.cofactor_Rbd_local` re-instantiated at

  `Rmax := T*₂(M, log M)`  (in place of `T*(M, log M)`),  `Rbd := cofactorRbd34loc`,

i.e. the per-`t` co-factor bound whose far arm is EXACTLY the one
`PinFamily.farErr34_local_closes` certifies.

**THE HYPOTHESIS DIFF versus `cofactor_Rbd_local`.**

*Removed.*  `X₀ ≤ k₀` (`caseA_partial_supply_slice`'s threshold), the `c`-contract's `0 < c`
and `c ≤ 1/e`, `ShortIntervalDatum Cb`, `e^{64} ≤ k₀`, `ballMertensThreshold ≤ k₀`, and the
loglog descent gate `hll` — every one of them was consumed by a page this stone no longer
runs (the landed CASE-A slice, and the `P/8` conversion).  What is left of the `c`-data is
`2c < 1`, which `caseAS2_nonneg` needs.

*Added.*  `ballQuarterThreshold ≤ k₀` (the `P/32` conversion's threshold, which by
`pin2Gate_le_ballQuarterThreshold` also supplies the R2 family gate), the conversion's own
loglog charge `hgate`, and the CASE-A socket `CaseASocket2`.

*Replaced.*  The contour gate at the R2 height: `|t| + T*₂(M, log M) ≤ 3X`.

*Kept verbatim.*  The collision inputs at the global scale (`collisionGate X 25 C` included),
the seven window-geometry binders, `M ≤ X`, the far-leg LOWER gate `0 < R`, `R ≤ |t − t₁|`,
and the half-open endpoint charge `hend`. -/
theorem cofactor_Rbd34_local :
    ∃ C : ℝ,
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ) (N Xn P Q j M k₀ : ℕ) (c Cb X θ t t₁ R : ℝ),
        2 * c < 1 → 0 ≤ Cb →
        -- the conversion threshold (it also supplies the R2 family gate)
        ballQuarterThreshold ≤ (k₀ : ℝ) →
        -- the co-factor window geometry
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        -- the transport gates, at the R2 height
        (M : ℝ) ≤ X →
        |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X →
        18 + Real.log (Real.log X) - Real.log (Real.log (k₀ : ℝ))
          ≤ 32 * θ * Real.log (Real.log X) →
        -- the collision inputs, at the GLOBAL scale
        Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 0 < θ → θ ≤ 1 / 32 →
        P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C →
        -- the far leg — the LOWER gate only
        0 < R → R ≤ |t - t₁| →
        -- the CASE-A page, as a socket (see the module docstring)
        CaseASocket2 g P Q c Cb X θ k₀ M t →
        -- the half-open endpoint charge
        2 / ramRbot H Xn j
          ≤ cofactorRbd34loc c Cb X θ (k₀ : ℝ) (M : ℝ)
              (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R / 3 →
        ‖ramR H N Xn P Q j (ellLin g) t‖
          ≤ cofactorRbd34loc c Cb X θ (k₀ : ℝ) (M : ℝ)
              (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R := by
  obtain ⟨C, hC⟩ := pocket_collision_window
  refine ⟨C, ?_⟩
  intro g hg H N Xn P Q j M k₀ c Cb X θ t t₁ R hc1 hCb0 hk₀th hMN hk₀lo hk₀hi hbot hlow
    hhigh hMtop hMX hTM hgate32 hX hLX hθ0 hθ32 hPlow hQhigh hPQ ht₁ hrow hgate hR0 hfar
    hA2 hend
  have hk₀3R : (3 : ℝ) ≤ (k₀ : ℝ) := le_trans three_le_ballQuarterThreshold hk₀th
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by linarith
  have hk₀pin : pin2Gate ≤ (k₀ : ℝ) := le_trans pin2Gate_le_ballQuarterThreshold hk₀th
  set S : ℝ := max (2 * caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ))
    (farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R) with hS
  have hSA : 2 * caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) ≤ S := le_max_left _ _
  have hSB : farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R ≤ S :=
    le_max_right _ _
  have hRbdS : cofactorRbd34loc c Cb X θ (k₀ : ℝ) (M : ℝ)
      (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R = 3 * S := rfl
  have hendS : 2 / ramRbot H Xn j ≤ S := by
    rw [hRbdS] at hend; linarith
  rw [hRbdS]
  refine ramR_abel_sup (fun n => ellLin_norm_le_one g hg n) hbot hlow hhigh hMtop hendS ?_
  intro m hm
  refine spolyA_ramRcoeff_le_of_damp ?_
  intro x hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases pocket_transport_pin2 hg P Q hx.1 hx.2 hk₀pin hMX hTM with hA | hB
  · -- CASE A at this `x` — the socket, at the `y₂` window floor
    have hk₀M : k₀ ≤ M := by
      have hk₀MR : (k₀ : ℝ) ≤ (M : ℝ) := by linarith
      exact_mod_cast hk₀MR
    have hS0 : (0 : ℝ) ≤ caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) :=
      caseAS2_nonneg hc1 hCb0 hk₀1
    have hbd := caseA_damped_partial (g := g) (H := H) (N := N) (Xn := Xn) (P := P) (Q := Q)
      (j := j) (M := M) (k₀ := k₀) (x := x) (t := t) hS0 hMN hk₀M hk₀lo hk₀hi hhigh
      (hA2 x hx.1 hx.2 hA) m hm
    have hmul : 2 * caseAS2 c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) * (m : ℝ) ≤ S * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hSA hm0
    linarith
  · -- CASE B at this `x` — the radius arrives WITH the pocket, at the R2 height
    obtain ⟨t₁', hRmax, ht₁'abs, hpock⟩ := hB
    have hcoll := hC g hg P Q X x θ t₁ t₁' hX hLX hθ0 hθ32 hx.1 hx.2 hPlow hQhigh hPQ ht₁
      ht₁'abs hrow hpock hgate
    have hRle : R ≤ 1 + |t - t₁'| := by
      have := pocket_far_from_ball hcoll hfar
      linarith
    have hbd := damped_partial_transfer_34 hg hx.1 hx.2 hk₀th hMN hk₀lo hk₀hi hhigh hMX
      hgate32 hpock hR0 hRle hRmax m hm
    have hmul : farSupS34 (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R * (m : ℝ)
        ≤ S * (m : ℝ) := mul_le_mul_of_nonneg_right hSB hm0
    linarith

/-- **P-1d — THE `𝒯_L` EXIT AT THE REPAIRED ARM** (`tL_supply_discharged34_local`).
`CofactorLocal.tL_supply_discharged_local` with its co-factor supply taken from
`cofactor_Rbd34_local`:

  `Σ_{t∈𝒯_L} ‖Q_{j,H}·R_{j,H}‖² ≤ 54·C_q·(cofactorRbd34loc … T*₂(M, log M) R)²·(H/j)²`.

The per-`t` bundle is the localized one at the R2 height — `R ≤ |t − t₁|` and
`|t| + T*₂(M, log M) ≤ 3Xg`.  `Dmax` does not occur; neither does `T*`. -/
theorem tL_supply_discharged34_local :
    ∃ Cq cq T₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q j N Xn M k₀ : ℕ) (cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      H ≤ (j : ℝ) →
      -- U-8's own window
      ∀ (T V L δ' : ℝ) (𝒯 : Finset ℝ), WellSpaced 𝒯 →
      (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) → T₀ ≤ T → 1 < T →
      3 ≤ ramQbase H P j → (ramQbase H P j : ℝ) ≤ T →
      30 ≤ Real.log T / Real.log (ramQbase H P j) →
      5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
      Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L →
      Real.log (ramQbase H P j) ≤ L → Real.log V ≤ 100 * Real.log L →
      420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cq * (Real.log (ramQbase H P j)) ^ 2 →
      -- U-7's own gates (all `t`-free), at the REPAIRED arm
      ∀ (c Cb Xg θ t₁ R : ℝ),
        2 * c < 1 → 0 ≤ Cb → ballQuarterThreshold ≤ (k₀ : ℝ) →
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        (M : ℝ) ≤ Xg →
        18 + Real.log (Real.log Xg) - Real.log (Real.log (k₀ : ℝ))
          ≤ 32 * θ * Real.log (Real.log Xg) →
        Real.exp 1 ≤ Xg → Real.exp 1 ≤ Real.log Xg → 0 < θ → θ ≤ 1 / 32 →
        P83 Xg θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 Xg → P ≤ Q → |t₁| ≤ Xg →
        pretDistSq (ellLin g) (costwist t₁) Xg ≤ (1 / 16) * Real.log (Real.log Xg) →
        collisionGate Xg 25 C → 0 < R →
        (∀ t : ℝ, CaseASocket2 g P Q c Cb Xg θ k₀ M t) →
        2 / ramRbot H Xn j
          ≤ cofactorRbd34loc c Cb Xg θ (k₀ : ℝ) (M : ℝ)
              (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R / 3 →
        -- the per-`t` gates on the `𝒯_L` branch
        (∀ t ∈ tLset H P Q j cf δ' 𝒯, R ≤ |t - t₁| ∧
          |t| + Tstar2 (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * Xg) →
        ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xn P Q (ellLin g) cf j t‖ ^ 2
          ≤ 54 * Cq * cofactorRbd34loc c Cb Xg θ (k₀ : ℝ) (M : ℝ)
                (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R ^ 2
              * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, htL⟩ := tL_main_sumsq
  obtain ⟨C, hRbd⟩ := cofactor_Rbd34_local
  refine ⟨Cq, cq, T₀, C, hCq, hcq, hT₀, ?_⟩
  intro g hg H hH P Q j N Xn M k₀ cf hcf1 hHj T V L δ' 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5
    hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill c Cb Xg θ t₁ R hc1 hCb0 hk₀th hMN hk₀lo hk₀hi
    hbot hlow hhigh hMtop hMX hgate32 hX hLX hθ0 hθ32 hPlow hQhigh hPQ ht₁ hrow hgate hR0
    hA2 hend hper
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by
    have := le_trans three_le_ballQuarterThreshold hk₀th
    linarith
  refine htL H hH P Q j N Xn cf (ellLin g) hcf1 hHj T V L δ'
    (cofactorRbd34loc c Cb Xg θ (k₀ : ℝ) (M : ℝ) (Tstar2 (M : ℝ) (Real.log (M : ℝ))) R)
    𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5 hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill
    (cofactorRbd34loc_nonneg hc1 hCb0 hk₀1) ?_
  intro t ht
  obtain ⟨hfar, hTM⟩ := hper t ht
  exact hRbd g hg H N Xn P Q j M k₀ c Cb Xg θ t t₁ R hc1 hCb0 hk₀th hMN hk₀lo hk₀hi hbot
    hlow hhigh hMtop hMX hTM hgate32 hX hLX hθ0 hθ32 hPlow hQhigh hPQ ht₁ hrow hgate hR0
    hfar (hA2 t) hend

/-! ## §2 (P-2) — the repaired arm, PRICED at the ratified numerals

`USetResiduals` §2/§3 re-run at `cofactorRbd34loc`.  Two of the three pages are untouched:
the CASE-A grade page (`caseAS_arm_priced`) and the far arm's MAIN term (`farMain_priced`).
Only the GS-7.1 error moves, and it moves onto `PinFamily.farErr34_local_closes_of_gate` —
the certificate that CLOSES, rather than the `q = 1/2` one that
`CofactorLocal.farErr_local_window_ge` refutes. -/

/-- **The `y₂` CASE-A arm, PRICED.**  `caseAS2` differs from `caseAS` by exactly one summand
(`farCStar2` in place of `farCStar`), so `USetResiduals.caseAS_arm_priced` carries the whole
page and the R2 constant enters additively:

  `caseAS2 (1/e) Cb (cofactorMfl X θ₂₉₃ W) W
     ≤ (C₁(1/e,Cb)·e^{13} + 2·C_far* + 2·C_far*₂ + 8)·(log X)^{−ρ₂₉₃}`.

The extra `2·C_far*₂` is `logW_rpow_le` at the shifted scale, exactly as the landed
`farCStar` term: the exponent `1/(32e)` is the same at both pins (`rho293_le_far`). -/
theorem caseAS2_arm_priced {X W Cb : ℝ} (hCb0 : 0 ≤ Cb) (hW2 : 2 ≤ W) (hWX : W ≤ X)
    (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log W) :
    caseAS2 (1 / Real.exp 1) Cb (cofactorMfl X theta293 W) W
      ≤ (gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 + 2 * farCStar + 2 * farCStar2 + 8)
        * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log (Real.log X) := by
    have h := Real.log_le_log (Real.exp_pos 2) hlX
    rwa [Real.log_exp] at h
  have hhalf : 1 / 2 * Real.log X ≤ Real.log W := by
    have h1 : (1 : ℝ) / Real.log (Real.log X) ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
    nlinarith
  have hfar1 : (1 : ℝ) / (32 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.exp_one_gt_d9]
  have hW0 : (0 : ℝ) < Real.log W := by
    have := Real.log_pos (show (1 : ℝ) < W by linarith)
    linarith
  have hu0 : (0 : ℝ) ≤ Real.log W ^ (-(1 / (32 * Real.exp 1))) := Real.rpow_nonneg hW0.le _
  -- the landed CASE-A page
  have hA := caseAS_arm_priced (X := X) (W := W) (Cb := Cb) hCb0 hW2 hWX hlX hgate
  -- the R2 far constant, at the shifted scale
  have hB : farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))
      ≤ farCStar2 * (2 * (Real.log X) ^ (-rho293)) :=
    mul_le_mul_of_nonneg_left (logW_rpow_le hL1 hhalf rho293_le_far hfar1) farCStar2_nonneg
  have hdrop : (0 : ℝ) ≤ farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1))) :=
    mul_nonneg farCStar_nonneg hu0
  have hsplit : caseAS2 (1 / Real.exp 1) Cb (cofactorMfl X theta293 W) W
      = caseAS (1 / Real.exp 1) Cb (cofactorMfl X theta293 W) W
        + (farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))
          - farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))) := by
    unfold caseAS2 caseAS
    ring
  rw [hsplit]
  linarith

/-- **`caseAS2` is antitone in BOTH slots** — the `caseAS_anti` page at the R2 far constant.
Nothing moves but the numeral: the grade factor falls with the floor, and both far numerals
fall with the scale. -/
lemma caseAS2_anti {c Cb M M' W W' : ℝ} (hc0 : 0 < c) (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hM : M' ≤ M) (hW1 : 1 < W') (hW : W' ≤ W) :
    caseAS2 c Cb M W ≤ caseAS2 c Cb M' W' := by
  have hC0 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hlW' : (0 : ℝ) < Real.log W' := Real.log_pos hW1
  have hlW : Real.log W' ≤ Real.log W := Real.log_le_log (by linarith) hW
  have hcM : c * M' ≤ c * M := mul_le_mul_of_nonneg_left hM (le_of_lt hc0)
  have h1 : Real.exp (-c * M) ≤ Real.exp (-c * M') := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.log W ^ (-(1 / (32 * Real.exp 1)))
      ≤ Real.log W' ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_le_rpow_of_nonpos hlW' hlW (neg_nonpos.mpr (by positivity))
  have h3 : Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.log W' ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_nonpos hlW' hlW (by norm_num)
  have hA : gradeAbsConstC c Cb * Real.exp (-c * M)
      ≤ gradeAbsConstC c Cb * Real.exp (-c * M') := mul_le_mul_of_nonneg_left h1 hC0
  have hB : farCStar2 * Real.log W ^ (-(1 / (32 * Real.exp 1)))
      ≤ farCStar2 * Real.log W' ^ (-(1 / (32 * Real.exp 1))) :=
    mul_le_mul_of_nonneg_left h2 farCStar2_nonneg
  unfold caseAS2
  linarith

/-- **`farErr34` is antitone in the window bottom and monotone in the top AND the radius.**
`USetPrice.farErr_le` at the `3/4` denominator, with the `Rmax` slot moving too — the graded
route needs that, because its `Rmax = T*₂(M_j, log M_j)` is `j`-dependent (the flat route's
`Dmax + 1` is not).  The `rpow` denominator is why `0 < log W'` is in-statement: unlike
`√(log W)` it has no free sign (⟦V7⟧'s trap). -/
lemma farErr34_le {W W' Y Y' Rmax Rmax' : ℝ} (hW1 : 1 < W') (hW : W' ≤ W)
    (hRmax : 0 ≤ Rmax) (hRR : Rmax ≤ Rmax') (hY : 1 ≤ Y) (hYY : Y ≤ Y') :
    farErr34 W Y Rmax ≤ farErr34 W' Y' Rmax' := by
  have hlW' : (0 : ℝ) < Real.log W' := Real.log_pos hW1
  have hlW : Real.log W' ≤ Real.log W := Real.log_le_log (by linarith) hW
  have hs' : (0 : ℝ) < (Real.log W') ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hlW' _
  have hs : (Real.log W') ^ ((3 : ℝ) / 4) ≤ (Real.log W) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hlW'.le hlW (by norm_num)
  have hlY : (0 : ℝ) ≤ Real.log Y := Real.log_nonneg hY
  have hlYY : Real.log Y ≤ Real.log Y' := Real.log_le_log (by linarith) hYY
  have hin0 : (0 : ℝ) < 3 + Rmax * (1 + Real.log Y) := by nlinarith
  have hnum : Real.log (3 + Rmax * (1 + Real.log Y))
      ≤ Real.log (3 + Rmax' * (1 + Real.log Y')) := by
    refine Real.log_le_log hin0 ?_
    nlinarith
  have hC := ballSupC34_pos
  have htop : 4 * ballSupC34 * (1 + Real.log (3 + Rmax * (1 + Real.log Y)))
      ≤ 4 * ballSupC34 * (1 + Real.log (3 + Rmax' * (1 + Real.log Y'))) := by nlinarith
  have htop0 : (0 : ℝ) ≤ 4 * ballSupC34 * (1 + Real.log (3 + Rmax' * (1 + Real.log Y'))) := by
    have h1 : (1 : ℝ) ≤ 3 + Rmax' * (1 + Real.log Y') := by nlinarith
    have := Real.log_nonneg h1
    nlinarith
  unfold farErr34
  exact div_le_div₀ htop0 htop hs' hs

/-- `farSupS34` inherits the three monotonicities (the radius pin `R` is the ball removal's
own datum and does not move with the block). -/
lemma farSupS34_le {W W' Y Y' Rmax Rmax' R : ℝ} (hW1 : 1 < W') (hW : W' ≤ W)
    (hRmax : 0 ≤ Rmax) (hRR : Rmax ≤ Rmax') (hY : 1 ≤ Y) (hYY : Y ≤ Y') :
    farSupS34 W Y Rmax R ≤ farSupS34 W' Y' Rmax' R := by
  have h := farErr34_le (W := W) (W' := W') (Y := Y) (Y' := Y') (Rmax := Rmax) (Rmax' := Rmax')
    hW1 hW hRmax hRR hY hYY
  unfold farSupS34
  linarith

/-- **P-2a (the monotone step) — `cofactorRbd34loc` at the worst corner.**  The twin of
`USetPrice.cofactorRbd_le_of_worst` at the repaired arm, with the extra `Rmax`-monotonicity
the localized route needs. -/
theorem cofactorRbd34loc_le_of_worst {c Cb X θ W W' Y Y' Rmax Rmax' R : ℝ}
    (hc0 : 0 < c) (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb)
    (hW1 : 1 < W') (hW : W' ≤ W) (hRmax : 0 ≤ Rmax) (hRR : Rmax ≤ Rmax')
    (hY : 1 ≤ Y) (hYY : Y ≤ Y') :
    cofactorRbd34loc c Cb X θ W Y Rmax R ≤ cofactorRbd34loc c Cb X θ W' Y' Rmax' R := by
  have hmfl : cofactorMfl X θ W' ≤ cofactorMfl X θ W := cofactorMfl_mono X θ hW
  have h1 : 2 * caseAS2 c Cb (cofactorMfl X θ W) W
      ≤ 2 * caseAS2 c Cb (cofactorMfl X θ W') W' := by
    have := caseAS2_anti (c := c) (Cb := Cb) (M := cofactorMfl X θ W)
      (M' := cofactorMfl X θ W') (W := W) (W' := W') hc0 hc1 hCb0 hmfl hW1 hW
    linarith
  have h2 : farSupS34 W Y Rmax R ≤ farSupS34 W' Y' Rmax' R :=
    farSupS34_le hW1 hW hRmax hRR hY hYY
  have hmax := max_le_max h1 h2
  unfold cofactorRbd34loc
  linarith

/-- **P-2b — THE UNIFORM `R̄` AT THE REPAIRED ARM** (`Rbd34loc_uniform`), in the graded row's
`hRbdU` shape.  The worst corner is the MIXED one, exactly as in the flat file: `kmin` for the
descent anchor (worst at the largest `j`), `Ymax` for the window top (worst at the smallest
`j`).  The third slot moves WITH the top — `T*₂(M_j) ≤ T*₂(Ymax)` by `PinFamily2.Tstar2_mono`,
whose gate `pin2Gate ≤ M_j` is the family gate the whole R2 layer runs on. -/
theorem Rbd34loc_uniform (H : ℝ) (P Q : ℕ) (Mt kk : ℕ → ℕ)
    (c Cb X θ Rrad kmin Ymax : ℝ)
    (hc0 : 0 < c) (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb) (hkmin : 1 < kmin)
    (hMtpin : ∀ j ∈ ramI H P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ))
    (hkk : ∀ j ∈ ramI H P Q, kmin ≤ ((kk j : ℕ) : ℝ))
    (hMt1 : ∀ j ∈ ramI H P Q, 1 ≤ ((Mt j : ℕ) : ℝ))
    (hMt : ∀ j ∈ ramI H P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) :
    ∀ j ∈ ramI H P Q,
      cofactorRbd34loc c Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
          (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad
        ≤ cofactorRbd34loc c Cb X θ kmin Ymax (Tstar2 Ymax (Real.log Ymax)) Rrad := by
  intro j hj
  have hMt0 : (0 : ℝ) < ((Mt j : ℕ) : ℝ) :=
    lt_of_lt_of_le pin2Gate_pos (hMtpin j hj)
  have hRmax0 : (0 : ℝ) ≤ Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) :=
    (Tstar2_pos hMt0).le
  have hRR : Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))
      ≤ Tstar2 Ymax (Real.log Ymax) :=
    Tstar2_mono (hMtpin j hj) (hMt j hj)
  exact cofactorRbd34loc_le_of_worst hc0 hc1 hCb0 hkmin (hkk j hj) hRmax0 hRR (hMt1 j hj)
    (hMt j hj)

/-- **THE EXPLICIT `C_R` AT THE REPAIRED ARM** (`gradeCR2`).  `USetResiduals.gradeCR` with the
R2 far constant added: `C_R₂(Cb) = 6·(C₁(1/e,Cb)·e^{13} + 2·C_far* + 2·C_far*₂ + 8) + 12`.
Carried, never set to `1` (⟦V5f⟧'s silent-vacuity catch). -/
def gradeCR2 (Cb : ℝ) : ℝ :=
  6 * (gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 + 2 * farCStar + 2 * farCStar2 + 8) + 12

lemma one_lt_gradeCR2 {Cb : ℝ} (hCb0 : 0 ≤ Cb) : 1 < gradeCR2 Cb := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := gradeAbsConstC_nonneg hc1 hCb0
  have h3 : (0 : ℝ) < Real.exp 13 := Real.exp_pos _
  have h4 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 := mul_nonneg h1 h3.le
  unfold gradeCR2
  linarith [farCStar_nonneg, farCStar2_nonneg]

/-- **P-2c — `R̄₃₄ ≤ C_R₂·(log X)^{−ρ₂₉₃}` AT THE REPAIRED ARM** (`Rbd34loc_grade_priced`).
The three pages, at the pin `c = 1/e`, `θ = θ₂₉₃`:

* CASE A at `caseAS2_arm_priced` (the landed grade page plus the R2 far numeral);
* the far arm's MAIN term at `USetResiduals.farMain_priced` (`2√2/Rrad ≤ 3(log X)^{−ρ}`, at
  the LOWER radius pin `seamRad X ≤ Rrad` — ⟦V6a⟧'s silent-vacuity catch, law #253);
* the far arm's GS-7.1 error at `PinFamily.farErr34_local_closes_of_gate` — **the certificate
  that closes**, at `Rmax = T*₂(Ymax, log Ymax)` and the window geometry `log Ymax ≤ 2 log kmin`
  (i.e. `kmin ≤ Ymax ≤ kmin²`, which the co-factor window's own `k₀ ≤ M ≤ 2k₀` gives).

`hXY : log X ≤ log Ymax` is what turns the certificate's `(log Ymax)^{−ρ}` into the exit's
`(log X)^{−ρ}`; `hthr` is §5's explicit threshold (`3/20 − ρ₂₉₃ > 0`,
`PinFamily.three_twentieths_gap`), a THRESHOLD and not an obstruction. -/
theorem Rbd34loc_grade_priced {X Cb kmin Ymax Rrad : ℝ}
    (hCb0 : 0 ≤ Cb) (hk2 : 2 ≤ kmin) (hkX : kmin ≤ X) (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin)
    (hRlow : seamRad X ≤ Rrad)
    (hY : pin2Gate ≤ Ymax) (hWY : Real.log Ymax ≤ 2 * Real.log kmin)
    (hXY : Real.log X ≤ Real.log Ymax)
    (hthr : 32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) :
    cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
        (Tstar2 Ymax (Real.log Ymax)) Rrad
      ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hpow0 : (0 : ℝ) ≤ (Real.log X) ^ (-rho293) := Real.rpow_nonneg hL0.le _
  have hρ0 : (0 : ℝ) ≤ rho293 := by
    have hθ : theta293 = 1 / (32 * (3 * Real.exp 1 + 1)) := rfl
    have hθ0 : (0 : ℝ) < theta293 := by
      rw [hθ]; positivity
    have hρ : rho293 = 3 * theta293 := rfl
    rw [hρ]; linarith
  set CA : ℝ := gradeAbsConstC (1 / Real.exp 1) Cb * Real.exp 13 + 2 * farCStar
    + 2 * farCStar2 + 8 with hCA
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hCA0 : (0 : ℝ) ≤ CA := by
    have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / Real.exp 1) Cb := gradeAbsConstC_nonneg hc1 hCb0
    have h3 : (0 : ℝ) < Real.exp 13 := Real.exp_pos _
    rw [hCA]
    nlinarith [farCStar_nonneg, farCStar2_nonneg]
  -- the CASE-A arm
  have hA := caseAS2_arm_priced (X := X) (W := kmin) (Cb := Cb) hCb0 hk2 hkX hlX hgate
  -- the far arm: the main term at the radius pin, the error at the CERTIFICATE
  have hclose := farErr34_local_closes_of_gate (W := kmin) hY hWY hthr
  have htrans : (Real.log Ymax) ^ (-rho293) ≤ (Real.log X) ^ (-rho293) :=
    rpow_neg_le_rpow_neg_of_le hL0 hXY hρ0
  have hB : farSupS34 kmin Ymax (Tstar2 Ymax (Real.log Ymax)) Rrad
      ≤ 4 * (Real.log X) ^ (-rho293) := by
    have hm := farMain_priced (X := X) (Rrad := Rrad) hL1 hRlow
    unfold farSupS34
    linarith
  have hmax : max (2 * caseAS2 (1 / Real.exp 1) Cb (cofactorMfl X theta293 kmin) kmin)
      (farSupS34 kmin Ymax (Tstar2 Ymax (Real.log Ymax)) Rrad)
        ≤ (2 * CA + 4) * (Real.log X) ^ (-rho293) := by
    refine max_le ?_ ?_
    · nlinarith [hA]
    · nlinarith [hB]
  have hCRval : gradeCR2 Cb = 3 * (2 * CA + 4) := by rw [gradeCR2, hCA]; ring
  unfold cofactorRbd34loc
  rw [hCRval]
  nlinarith [hmax]

/-- **P-2d — the same, with the threshold DISCHARGED** (`Rbd34loc_grade_closes`).
`PinFamily.farErr34_local_closes`' explicit `Y₀` carried through: past it, the repaired
co-factor bound meets the graded balance's `hRgrade` slot with `C_R₂` explicit and NO
remaining far-arm hypothesis.  This is the inequality ⟦V6a⟧ proved impossible at the old pin
and ⟦V6b⟧'s R1 alone left divergent. -/
theorem Rbd34loc_grade_closes :
    ∃ Y₀ : ℝ, pin2Gate ≤ Y₀ ∧
      ∀ (X Cb kmin Ymax Rrad : ℝ), 0 ≤ Cb → 2 ≤ kmin → kmin ≤ X →
        Real.exp 2 ≤ Real.log X →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        seamRad X ≤ Rrad → Y₀ ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
            (Tstar2 Ymax (Real.log Ymax)) Rrad
          ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) := by
  obtain ⟨hgap, -⟩ := three_twentieths_gap
  have hC0 : (0 : ℝ) < ballSupC34 := ballSupC34_pos
  set ε : ℝ := (3 : ℝ) / 20 - rho293 with hε
  set A : ℝ := 32 * ballSupC34 with hA
  have hA0 : (0 : ℝ) < A := by rw [hA]; linarith
  refine ⟨max pin2Gate (Real.exp (A ^ (1 / ε))), le_max_left _ _, ?_⟩
  intro X Cb kmin Ymax Rrad hCb0 hk2 hkX hlX hgate hRlow hY hWY hXY
  have hYg : pin2Gate ≤ Ymax := le_trans (le_max_left _ _) hY
  have hYe : Real.exp (A ^ (1 / ε)) ≤ Ymax := le_trans (le_max_right _ _) hY
  obtain ⟨hY0, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hYg rfl
  have hL0 : (0 : ℝ) < Real.log Ymax := by linarith
  have hthr : A ^ (1 / ε) ≤ Real.log Ymax := by
    have h := Real.log_le_log (Real.exp_pos _) hYe
    rwa [Real.log_exp] at h
  have hgateA : A ≤ (Real.log Ymax) ^ ε := by
    have h1 : (A ^ (1 / ε)) ^ ε ≤ (Real.log Ymax) ^ ε :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA0.le _) hthr hgap.le
    have h2 : (A ^ (1 / ε)) ^ ε = A := by
      rw [← Real.rpow_mul hA0.le, one_div, inv_mul_cancel₀ (ne_of_gt hgap), Real.rpow_one]
    linarith [h2.symm.le, h2.le]
  exact Rbd34loc_grade_priced hCb0 hk2 hkX hlX hgate hRlow hYg hWY hXY
    (by rw [hA] at hgateA; exact hgateA)

/-! ## §3 (P-3) — the graded thinness bundle at the §8.3 pin

`USetGradedBalance.thinBundleG` is `|I_J|·(840·V_J²·e^{2(log T/log P_J)loglog T})`.  At the
pin the two `J`-dependent factors are priced by pages that already exist: the block count by
`USetPrice.ramI_card_le_pin` and the level by `USetGradedThin.gradeV_sq_le_rpow`.  That is the
bridge G1b's Zeno #2 names — 40 lines, and the only reason it is not inside `USetGradedThin`
is that the graded bundle is defined one file later. -/

/-- **P-3 — THE GRADED BUNDLE AT THE PIN** (`thinBundleG_at_pin`).  At `H_Jb = H₈₃ X θ₂₉₃`,
`Q_Jb ≤ Q₈₃ X` and any level with `V_J² ≤ X^ε`:

  `thinBundleG T V_J H_Jb P_Jb Q_Jb ≤ 2(log X)^{1+θ₂₉₃}·840·X^ε·e^{2(log T/log P_Jb)loglog T}`.

The `T`-power leg `T^{2α}` is NOT here (it factors out of the bundle by construction, which is
what lets `thin_sqrt_kill` apply verbatim), and neither is the `1/loglog X` gain of the card
page — the block leg has `(log X)^{−2θ}` of spare and does not need it. -/
theorem thinBundleG_at_pin (X T VJ ε : ℝ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (Jb : ℕ)
    (hHpin : Hseq Jb = H83 X theta293) (hQ0 : 0 < Qseq Jb)
    (hQpin : ((Qseq Jb : ℕ) : ℝ) ≤ Q83 X) (hLe : Real.exp 1 ≤ Real.log X)
    (hVJ : VJ ^ 2 ≤ X ^ ε) :
    thinBundleG T VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
      ≤ 2 * (Real.log X) ^ (1 + theta293)
        * (840 * X ^ ε
            * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log T))) := by
  have hcard : ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ)
      ≤ 2 * (Real.log X) ^ (1 + theta293) := by
    rw [hHpin]
    exact ramI_card_le_pin X (Pseq Jb) (Qseq Jb) hQ0 hQpin hLe
  have hcard0 : (0 : ℝ) ≤ ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ) := Nat.cast_nonneg _
  have hexp0 : (0 : ℝ) < Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
      * Real.log (Real.log T)) := Real.exp_pos _
  have hinner : 840 * VJ ^ 2
        * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ)) * Real.log (Real.log T))
      ≤ 840 * X ^ ε
        * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
            * Real.log (Real.log T)) := by
    have h1 : 840 * VJ ^ 2 ≤ 840 * X ^ ε := by linarith
    exact mul_le_mul_of_nonneg_right h1 hexp0.le
  have hinner0 : (0 : ℝ) ≤ 840 * VJ ^ 2
      * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ)) * Real.log (Real.log T)) := by
    positivity
  have hLX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hLe
  rw [thinBundleG]
  exact mul_le_mul hcard hinner hinner0
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hLX0.le _))

/-- **P-3 (the level at the pin).**  The same, at the CONCRETE graded level
`V_J = Q_Jb^{α_Jb}` that `USetGradedThin.usetG_thin_Q` supplies: the `X^ε` comes from
`gradeV_sq_le_rpow`, whose gates are `α_Jb ≤ 1`, `Q_Jb ≤ Q₈₃ X` and `2/ε ≤ loglog X`. -/
theorem thinBundleG_at_pin_Q (X T ε : ℝ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb : ℕ)
    (hX1 : 1 < X) (hε : 0 < ε) (hHpin : Hseq Jb = H83 X theta293) (hQ0 : 0 < Qseq Jb)
    (hQpin : ((Qseq Jb : ℕ) : ℝ) ≤ Q83 X) (hLe : Real.exp 1 ≤ Real.log X)
    (hLL : 2 / ε ≤ Real.log (Real.log X))
    (hα0 : 0 ≤ αseq Jb) (hα1 : αseq Jb ≤ 1) :
    thinBundleG T (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) (Hseq Jb) (Pseq Jb) (Qseq Jb)
      ≤ 2 * (Real.log X) ^ (1 + theta293)
        * (840 * X ^ ε
            * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log T))) := by
  exact thinBundleG_at_pin X T _ ε Pseq Qseq Hseq Jb hHpin hQ0 hQpin hLe
    (gradeV_sq_le_rpow hX1 hQ0 hα0 hα1 hε hQpin hLL)

/-! ## §4 (P-4) — the graded `hU`, SUPPLIED AND PRICED AT THE REPAIRED ARM

`USetGradedBalance` §4/§5 re-run with the `𝒯_L` feed taken from §1 instead of from
`CofactorLocal.tL_supply_discharged_local`.  The `𝒯_S` side does not move at all: the graded
thinness feed `TSG_feed_of_thin` is reused VERBATIM (it knows nothing about the co-factor
arm).  What moves is exactly the co-factor slot — and it moves onto the arm §2 prices. -/

/-- **THE PER-BLOCK `𝒯_L` GATE BUNDLE AT THE REPAIRED ARM** (`TLBlockGates34`).
`USetGradedBalance.TLBlockGatesLoc` with four changes, each the removal or replacement of a
gate whose consumer moved:

* `X₀ ≤ k₀`, `e^{64} ≤ k₀`, `ballMertensThreshold ≤ k₀` → the single
  `ballQuarterThreshold ≤ k₀` (the `P/32` conversion's threshold, which by
  `pin2Gate_le_ballQuarterThreshold` also supplies the R2 family gate);
* the loglog descent gate `(1/32−θ)loglog Xg ≤ (1/16)loglog k₀` → the conversion's own charge
  `18 + loglog Xg − loglog k₀ ≤ 32θ·loglog Xg` (`Transfer34`'s T-1 page, the SHARP
  convention);
* `0 ≤ cofactorMfl Xg θ k₀` is GONE (its consumer was the landed CASE-A slice's `hM0`; the
  socket owns the floor now);
* the endpoint charge is read at `cofactorRbd34loc … (T*₂(M_j, log M_j))`.

Everything else is byte-identical: the block base, the `X₀` law `hκ30`, the kill gate, the two
roundings of the co-factor length, `M_j ≤ N`, `M_j ≤ Xg`. -/
def TLBlockGates34 (cq H : ℝ) (P N Xn : ℕ) (Mt kk : ℕ → ℕ)
    (T L c Cb Xg θ Rrad : ℝ) (j : ℕ) : Prop :=
  H ≤ (j : ℝ) ∧ 3 ≤ ramQbase H P j ∧ (ramQbase H P j : ℝ) ≤ T ∧
  30 ≤ Real.log T / Real.log (ramQbase H P j) ∧
  Real.log (ramQbase H P j) ≤ L ∧
  420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (ramQbase H P j)) ^ 2 ∧
  ballQuarterThreshold ≤ ((kk j : ℕ) : ℝ) ∧
  Mt j ≤ N ∧ ((kk j : ℕ) : ℝ) < ramRbot H Xn j ∧ ramRbot H Xn j ≤ ((kk j : ℕ) : ℝ) + 1 ∧
  1 < ramRbot H Xn j ∧ ramRbot H Xn j - 1 ≤ ((Mt j : ℕ) : ℝ) ∧
  ((Mt j : ℕ) : ℝ) ≤ 2 * (ramRbot H Xn j - 1) ∧ 2 * ramRbot H Xn j < ((Mt j : ℕ) : ℝ) + 3 ∧
  ((Mt j : ℕ) : ℝ) ≤ Xg ∧
  18 + Real.log (Real.log Xg) - Real.log (Real.log ((kk j : ℕ) : ℝ))
    ≤ 32 * θ * Real.log (Real.log Xg) ∧
  2 / ramRbot H Xn j
    ≤ cofactorRbd34loc c Cb Xg θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
        (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3

/-- **P-4a — THE GRADED `hU` SUPPLY AT THE REPAIRED ARM** (`hUG34_supplied`).
`USetGradedBalance.hUG_supplied` with its `𝒯_L` feed taken from §1:

  `∫_{(Ann∖ball)∩𝒰G} ‖spoly N a‖² ≤ 4|I|·(|I|·KS + 54·C_q·R̄²·H²/(⌊H log P⌋−1)) + 2E`,
  `R̄ ≥ cofactorRbd34loc cg Cb X θ k₀(j) M(j) (T*₂(M(j), log M(j))) Rrad`.

The `𝒯_S` half is verbatim (`TSG_feed_of_thin`), `TannGate X Tann` rides in-statement (it is
what supplies `hκ30` through `USetPins.kappa30_of_TannGate`), and the far-leg geometry is
DERIVED exactly as in the landed twin: `Rrad ≤ seamRad X` plus `t ∉ ball` gives CASE B's
radius input.  The contour box is the R2 one, `|t| + T*₂(M_j, log M_j) ≤ 3X`. -/
theorem hUG34_supplied :
    ∃ Cq cq T₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq Ms Mt kk : ℕ → ℕ)
        (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E : ℝ),
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        -- the graded partition's non-degeneracy pins (the `G0` empty-block trap)
        1 ≤ Jb → Jb ≤ Jset → 2 ≤ Hseq Jb → 0 ≤ αseq Jb →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ Tann →
        -- `Vthin`: the graded thinness level and its α-gate
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
        αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        -- `Vsplit`: the `𝒯_S ∥ 𝒯_L` level at `δ'`
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        -- U-7's `t`-free gates, at the REPAIRED arm (no `ShortIntervalDatum`, no `c`-contract)
        2 * cg < 1 → 0 ≤ Cb →
        0 < θ → θ ≤ 1 / 32 → P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X →
        (∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, CaseASocket2 g P Q cg Cb X θ (kk j) (Mt j) t) →
        (∀ j ∈ ramI H P Q, 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
            * (∑ m ∈ Finset.Icc 1 (Ms j),
                ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2) ≤ KS) →
        (∀ j ∈ ramI H P Q,
          cofactorRbd34loc cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
        (∫ t in (-Tann)..Tann, ‖ramErr H N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        (∫ t in (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset,
            ‖spoly N a t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbar ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cq, cq, T₀, C, hCq, hcq, hT₀, hTL⟩ := tL_supply_discharged34_local
  refine ⟨Cq, cq, T₀, C, hCq, hcq, hT₀, ?_⟩
  intro g fb a cf hg hfb1 hcf1 H hH N Xd P Q Jset Jb Pseq Qseq Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η cg Cb θ Rrad KS Rbar E
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hH2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hc1 hCb0 hθ0 hθ32 hPlow hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad
    hblk hbox hA2 hKS hRbdU hj₀ herr
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hκ30 : 30 ≤ Real.log Tann / Real.log (Qseq Jb) :=
    kappa30_of_TannGate X Tann (Qseq Jb) hQ1 hQpin hTgate
  have hRsub : (seamAnn X Tann \ seamBall X t₁) ⊆ Set.Icc (-Tann) Tann :=
    fun _ ht => seamAnn_subset_Icc X Tann ht.1
  -- the `𝒯_S` feed at the GRADED thinness — VERBATIM
  have hTSfeed := TSG_feed_of_thin fb hfb1 Pseq Qseq Hseq αseq Jset Jb hJb1 hJbJ hH2 hα0
    Tann VJ hT1 hP3 hPQ hQT hκ30 hLL5 hVJ η X hα hη2 hTX
    (seamAnn X Tann \ seamBall X t₁) hRsub H N Xd P Q (ellLin g) cf δ' Ms hMs hbudget
  -- the `𝒯_L` feed at the REPAIRED supply
  have hTLj : ∀ j ∈ ramI H P Q, ∀ 𝒯 : Finset ℝ, WellSpaced 𝒯 →
      (↑𝒯 : Set ℝ) ⊆ (seamAnn X Tann \ seamBall X t₁) ∩ UsetG fb Pseq Qseq Hseq αseq Jset →
      (∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xd P Q (ellLin g) cf j t‖ ^ 2)
        ≤ 54 * Cq * cofactorRbd34loc cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
            (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ^ 2
            * (H / (j : ℝ)) ^ 2 := by
    intro j hj 𝒯 hws h𝒯A
    obtain ⟨hHj, hB3, hBT, hκ30j, hWL, hkill, hk₀th, hMN, hk₀lo, hk₀hi, hbot, hlow, hhigh,
      hMtop, hMX, hgate32, hend⟩ := hblk j hj
    refine hTL g hg H hH P Q j N Xd (Mt j) (kk j) cf hcf1 hHj Tann V L δ' 𝒯 hws
      (fun t ht => hRsub (h𝒯A (Finset.mem_coe.mpr ht)).1) hT₀T hT1 hB3 hBT hκ30j hLL5 hV1 hVδ
      hTLle hlogT1 hLe hWL hlogV hkill cg Cb X θ t₁ Rrad hc1 hCb0 hk₀th hMN hk₀lo hk₀hi
      hbot hlow hhigh hMtop hMX hgate32 hXe hLXe hθ0 hθ32 hPlow hQhigh hPQ83 ht₁ hrow hcoll
      hR0 (hA2 j hj) hend ?_
    intro t ht
    have ht𝒯 : t ∈ 𝒯 := tLset_subset H P Q j cf δ' 𝒯 ht
    have htA := h𝒯A (Finset.mem_coe.mpr ht𝒯)
    have hTabs : |t| ≤ Tann := htA.1.1.2
    have hnot : ¬ (|t - t₁| ≤ seamRad X) := htA.1.2
    exact ⟨le_trans hRrad (le_of_lt (not_le.mp hnot)), hbox j hj t hTabs⟩
  refine hUG_exit_of_branches H N Xd P Q a (ellLin g) cf fb Pseq Qseq Hseq αseq Jset
    X Tann t₁ E hTann0 herr δ'
    (fun j => 5128 * δ' ^ 2 * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
      * ∑ m ∈ Finset.Icc 1 (Ms j), ‖ramRcoeff H N Xd P Q j (ellLin g) m‖ ^ 2 / (m : ℝ) ^ 2)
    (fun j => 54 * Cq * cofactorRbd34loc cg Cb X θ ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
      (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ^ 2 * (H / (j : ℝ)) ^ 2)
    KS Cq Rbar (le_of_lt hCq) hj₀ (fun j hj 𝒯 hws h𝒯A => hTSfeed j hj 𝒯 hws h𝒯A) hTLj hKS ?_
  intro j hj
  obtain ⟨-, -, -, -, -, -, hk₀th, -, -, -, -, -, -, -, -, -, -⟩ := hblk j hj
  have hk₀1 : (1 : ℝ) ≤ ((kk j : ℕ) : ℝ) := by
    have := le_trans three_le_ballQuarterThreshold hk₀th
    linarith
  exact tL_block_weight Cq H _ Rbar j (le_of_lt hCq)
    (cofactorRbd34loc_nonneg hc1 hCb0 hk₀1) (hRbdU j hj)

/-- **P-4b — THE GRADED STATION PRIZE** (`hUG34_fully_priced`).  The graded seam row at the
§8.3 pins `H := H₈₃ X θ₂₉₃`, `θ := θ₂₉₃`, `c := 1/e`, with **all four grade slots discharged**
— and, unlike the flat `USetPrice.hU_fully_priced`, the co-factor grade `R̄` DISCHARGED TOO:

* `hKS` by `USetPrice.KS_supplied` at `KS = 20512·δ'²(1 + log 2Tann)`;
* `hRbdU` by §2's `Rbd34loc_uniform` at the mixed worst corner `(kmin, Ymax)`;
* `hRgrade` by §2's `Rbd34loc_grade_priced` at `C_R₂ = gradeCR2 Cb` — **this is what the
  repair buys**: the flat file must CARRY `R̄ ≤ C_R(log X)^{−ρ}` as a hypothesis, and at the
  `q = 1/2` localized arm that hypothesis is refuted (`CofactorLocal.farErr_local_window_ge`);
* `hmain`/`hrem` by `USetPrice.balance_priced_main` / `rem_priced`, both predicate-blind and
  reused VERBATIM (the graded exit has the flat exit's shape — that is the whole content of
  G1b's predicate-blindness census).

The exit is `USetGradedBalance.hUG_balance`'s, hence `hUG_balance_beats_door`'s input: the
door's floor `c₀ ≥ 1/500` at the ratified margin `1.7067×`.

**The radius pin rides in BOTH directions** (law #253, ⟦V6a⟧'s silent-vacuity catch):
`Rrad ≤ seamRad X` is what turns `t ∉ ball` into CASE B's far leg, and `seamRad X ≤ Rrad` is
what `USetResiduals.farMain_priced` needs; asking only one of them would make the priced arm
vacuous. -/
theorem hUG34_fully_priced :
    ∃ Cq cq T₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧
      ∀ (g fb a cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖fb n‖ ≤ 1) →
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q Jset Jb : ℕ) (Pseq Qseq m₀ Ms Mt kk : ℕ → ℕ) (Hseq αseq : ℕ → ℝ),
      ∀ (X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        1 < (Qseq Jb : ℝ) → Real.log (Qseq Jb) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        1 ≤ Jb → Jb ≤ Jset → 2 ≤ Hseq Jb → 0 ≤ αseq Jb →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ Tann →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
        αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η)
            ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C → 0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
          CaseASocket2 g P Q (1 / Real.exp 1) Cb X theta293 (kk j) (Mt j) t) →
        -- the block-range data: the mixed worst corner, and the window's own geometry
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        -- the two block gates and Lemma 12's rows
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        -- the graded row's own frame
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG fb Pseq Qseq Hseq αseq Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, C, hCq, hcq, hT₀, hsup⟩ := hUG34_supplied
  refine ⟨Cq, cq, T₀, C, hCq, hcq, hT₀, ?_⟩
  intro g fb a cf hg hfb1 hcf1 N Xd P Q Jset Jb Pseq Qseq m₀ Ms Mt kk Hseq αseq
    X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hA2 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hlog2T : (0 : ℝ) ≤ 1 + Real.log (2 * Tann) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * Tann by linarith)
    linarith
  have hKS0 : (0 : ℝ) ≤ 20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)) :=
    mul_nonneg (by positivity) hlog2T
  have hkmin1 : (1 : ℝ) < kmin := by linarith
  have hMt1 : ∀ j ∈ ramI (H83 X theta293) P Q, (1 : ℝ) ≤ ((Mt j : ℕ) : ℝ) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ pin2Gate := Real.one_le_exp (by norm_num)
    exact le_trans h1 (hMtpin j hj)
  have hRbar0 : (0 : ℝ) ≤ cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
      (Tstar2 Ymax (Real.log Ymax)) Rrad :=
    cofactorRbd34loc_nonneg hc1 hCb0 (le_of_lt hkmin1)
  -- §1 of `USetPrice`: the `𝒯_S` slot
  have hKSb := KS_supplied (H83 X theta293) N Xd P Q g hg m₀ Ms Tann δ' (le_of_lt hT1)
    hm₀2 hm₀ hMs hMs4
  -- §2: the co-factor slot at the worst corner, and ITS GRADE
  have hRb := Rbd34loc_uniform (H83 X theta293) P Q Mt kk (1 / Real.exp 1) Cb X theta293
    Rrad kmin Ymax hc0 hc1 hCb0 hkmin1 hMtpin hkk hMt1 hMt
  have hRgrade := Rbd34loc_grade_priced (X := X) (Cb := Cb) (kmin := kmin) (Ymax := Ymax)
    (Rrad := Rrad) hCb0 hk2 hkX hlX2 hgateW hRlow hYpin hWY hXY hthr
  -- the floor page
  have hfl := floor_pin X P hL4 hPlow
  -- §4a: the graded `𝒰` integral at the repaired arm
  have hU := hsup g fb a cf hg hfb1 hcf1 (H83 X theta293) hH2 N Xd P Q Jset Jb Pseq Qseq
    Ms Mt kk Hseq αseq X Tann t₁ δ' V VJ L η (1 / Real.exp 1) Cb theta293 Rrad
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
    (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
      (Tstar2 Ymax (Real.log Ymax)) Rrad) E
    hX0 hXe hLXe hTgate hT1 hTX hQ1 hQpin hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 hJbJ hHb2 hα0 hP3 hPQ hQT hVJ hα hη2 hMs hbudget hV1 hVδ hlogV
    hc1 hCb0 theta293_pos (le_of_lt theta293_lt_one_div_32) hPlow hQhigh hPQ83 ht₁ hrow
    hcoll hR0 hRrad hblk hbox hA2 hKSb hRb hfl.1 herr
  -- §3 of `USetPrice`: the two balance binders, predicate-blind and verbatim
  have hmain := balance_priced_main X (H83 X theta293) Cq (gradeCR2 Cb)
    (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann)))
    (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
      (Tstar2 Ymax (Real.log Ymax)) Rrad) P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    (le_of_lt hCq) hKS0 hRbar0 hRgrade hKSgate hCqgate
  have hrem := rem_priced X Tann (H83 X theta293) ε EP2 E hL1 hX0 (by linarith)
    (le_of_eq hHeq.symm) habs hEP2 hErow
  have hbal := hUG_balance a fb N Pseq Qseq Hseq αseq Jset X Tann t₁ ε _ _ hε0 hL1 hX0
    hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG a N fb Pseq Qseq Hseq αseq Jset X Tann t₁ S _ hL0.le
    (by linarith) hX0 hXN hN2 hsupp hSup hbal

end Salt.MR
