/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.DispersionClose
import Salt.Maynard.Level
import Salt.Maynard.EHConsume

/-!
# V4 + V5 — the ψ→π bridge and the `HasLevel (1/2)` target

Design: `docs/blueprints/bv.md`, nodes `V4.1`/`V4.2` (the ψ→θ→π conversion) and
`V5.1` (`hasLevel_half_of_siegelWalfisz`). The last substantive node of the `bv`
rung.

## What is landed here (structural glue, sorry-free)

`hasLevel_half_of_siegelWalfisz_of_bridge` reduces the frozen target
`SiegelWalfisz → HasLevel (1/2)` to a **single** explicit conversion hypothesis
`PsiToPiTransfer`, discharging everything *around* the discretized-Abel core:

* the **range bridge** `(x : ℝ) ^ (1/2 : ℝ) = Real.sqrt x` (`Real.sqrt_eq_rpow`),
  aligning `HasLevel`'s `⌊x^{1/2}/(log x)^B⌋₊` modulus range with the
  ψ-keystone's `⌊√x/(log x)^B⌋₊`;
* the **small-`x` absorption** (`sum_maxDiscrepancy_crude` + a finite-range
  constant), lifting the conversion's *eventual* (`∀ᶠ x`) output to the
  `∀ x ≥ 2` shape `HasLevel` demands — the exact pattern of
  `Salt/BV/Dispersion.lean`'s keystone small-`x` tail, now for the π-form
  carrier via the landed trivial bound `Salt.Maynard.maxDiscrepancy_le_trivial`;
* the `∀A ∃B ∃C` **packaging** and the `max C Csm` constant.

## The single deferred step: `PsiToPiTransfer` (the discretized Abel, node V4)

`PsiToPiTransfer` takes the landed ψ-form BV dispersion family
(`psi_BV_of_siegelWalfisz'`: for each saving `A`, a haircut `B` and constant `C`
with `∑_{q ≤ √x/(log x)^B} dispDisc y q ≤ C·x/(log x)^A` for *every* `y ≤ x`,
the q-range fixed `x`-based) and returns the π-form BV dispersion family
(`∑_{q ≤ √x/(log x)^B} maxDiscrepancy x q ≤ C·x/(log x)^A`, eventually in `x`).

This is exactly the θ→π partial summation of node V4.2 on a polylog net of
scales, whose faithful formalization is deferred (PB-floor). The mechanism, as
clarified during this landing (see `docs/blueprints/flags.md`, the V4/V5 entry):

1. **θ-skip.** `maxDiscrepancy x q = sup'_a |π(x;q,a) − π(x)/φq|` is π-form
   directly (`primesCount`); there is no θ-carrier in `Salt/Maynard`, so the
   conversion goes ψ→π in one step. The prime-power correction `ψ − θ` is
   `O(√x·log²x)` (by *size*, not by absence — prime powers `p^k ≤ x`, `k ≥ 2`
   DO occur in `(√x, x]`, e.g. `2^6 = 64 ≤ 100`), absorbed below `x/(log x)^A`.

2. **Difference against `q = 1`.** Abel-expanding both `π(x;q,a)` and
   `π(x)/φq = π(x;1,0)/φq` and subtracting, the main terms cancel *identically*
   — `E_π(x;q,a)` is expressed purely through the ψ-discrepancies
   `ψ(t;q,a) − ψ(t)/φq` at scales `t`, with NO PNT-style reconstruction of
   `π(x)` needed. Here `ψ(t;q,a) − ψ(t)/φq = E_ψ(t;q,a) + (ψ(t,χ₀) − ψ(t))/φq`,
   the first `≤ dispDisc t q`, the second `≤ ω(q)·log t/φq`
   (`norm_psiChi_one_sub_psiTot_le`).

3. **Fixed-`x` q-range at each net point.** The keystone's crucial shape —
   the sum over the *`x`-based* range `q ≤ ⌊√x/(log x)^B⌋`, uniform over the
   scale `y ≤ x` — lets one apply `∑_q dispDisc(t_i) ≤ C·x/(log x)^A` at each
   net point `t_i ∈ [√x, x]` (there is no `√t`-based range shrinkage). The
   net has `≤ log₂ x` points; the Abel kernel `∫_√x^x dt/(t log²t) ≤ 2/log x`
   weights them, giving `≤ 2C·x/(log x)^{A+1}` — a power-of-log saving.

4. **Crude within-shell increments + tiny scales.** `max_{t∈shell}|E| ≤
   |E(t_i)| + [ψ-increment] + width/φq`, with `∑_q max_a[increment]
   ≤ log x·(width·log x + Q)` via the trivial interval count `width/q + 1`
   (NO Brun–Titchmarsh); tiny scales `t ≤ √x` use `|E(t)| ≤ 3t` trivially.

Discharging `PsiToPiTransfer` upgrades `hasLevel_half_of_siegelWalfisz_of_bridge`
to the frozen `hasLevel_half_of_siegelWalfisz : SiegelWalfisz → HasLevel (1/2)`.
-/

namespace Salt.BV

open Finset Filter Salt.LS Salt.Maynard
open scoped BigOperators

/-! ## The π-form crude bound (small-`x` absorber) -/

/-- **Crude π-discrepancy sum bound.** Over the haircut range, the summed
`maxDiscrepancy` is `≤ Q·(x+1)` where `Q = ⌊√x/(log x)^B⌋₊`: each
`maxDiscrepancy x q ≤ x/φq + 1 ≤ x + 1` (`maxDiscrepancy_le_trivial`, `φq ≥ 1`),
and there are `Q` moduli. The π-form analogue of `Salt/BV/Dispersion.lean`'s
`dispDisc_crude`; feeds the finite small-`x` constant in the target. -/
lemma sum_maxDiscrepancy_crude (x : ℕ) (B : ℝ) :
    ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, maxDiscrepancy x q
      ≤ (⌊Real.sqrt x / (Real.log x) ^ B⌋₊ : ℝ) * ((x : ℝ) + 1) := by
  set Q := ⌊Real.sqrt x / (Real.log x) ^ B⌋₊ with hQ
  calc ∑ q ∈ Finset.Icc 1 Q, maxDiscrepancy x q
      ≤ ∑ _q ∈ Finset.Icc 1 Q, ((x : ℝ) + 1) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [Finset.mem_Icc] at hq
        have hqpos : 0 < q := by omega
        have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqpos
        have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
          have : 1 ≤ q.totient := Nat.totient_pos.mpr hqpos
          exact_mod_cast this
        calc maxDiscrepancy x q ≤ (x : ℝ) / (q.totient : ℝ) + 1 := maxDiscrepancy_le_trivial x q
          _ ≤ (x : ℝ) + 1 := by
              have hxdiv : (x : ℝ) / (q.totient : ℝ) ≤ (x : ℝ) :=
                div_le_self (by positivity) hφ1
              linarith
    _ = (Q : ℝ) * ((x : ℝ) + 1) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast [Nat.add_sub_cancel]; ring

/-! ## The deferred ψ→π conversion (node V4) -/

/-- **The ψ→π transfer (node V4 — the discretized-Abel core, deferred).**
Transfers the ψ-form BV dispersion family (`psi_BV_of_siegelWalfisz'`'s shape,
the hypothesis) into the π-form BV dispersion family (eventual in `x`, the
conclusion), preserving the haircut range `⌊√x/(log x)^B⌋₊`. This is exactly the
θ→π partial summation on a polylog net of scales; see the module docstring and
`docs/blueprints/flags.md` for the mechanism. -/
def PsiToPiTransfer : Prop :=
  (∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ x y : ℕ, 2 ≤ x → y ≤ x →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, dispDisc y q
        ≤ C * x / (Real.log x) ^ A) →
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
    ∀ᶠ x : ℕ in atTop,
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, maxDiscrepancy x q
        ≤ C * x / (Real.log x) ^ A

/-! ## V5 — the `HasLevel (1/2)` target (PB-floor form) -/

/-- **V5.1 (PB-floor) — `HasLevel (1/2)` from Siegel–Walfisz modulo the ψ→π
bridge.** Given the named gate `SiegelWalfisz` and the deferred conversion
`PsiToPiTransfer` (node V4, the discretized Abel), the frozen level-of-
distribution target `HasLevel (1/2)` holds.

The ψ-keystone `psi_BV_of_siegelWalfisz'` feeds `PsiToPiTransfer` to produce the
π-form dispersion family (eventual in `x`); this file then discharges the
structural remainder — the `(x)^{1/2} = √x` range bridge, the small-`x`
absorption via `sum_maxDiscrepancy_crude`, and the `∀A ∃B ∃C` packaging — to
land the exact `HasLevel (1/2)` shape. Discharging `PsiToPiTransfer` yields the
frozen `hasLevel_half_of_siegelWalfisz : SiegelWalfisz → HasLevel (1/2)`. -/
theorem hasLevel_half_of_siegelWalfisz_of_bridge
    (hSW : SiegelWalfisz) (hT : PsiToPiTransfer) :
    HasLevel (1 / 2) := by
  -- the π-form dispersion family, eventual in `x`, from the transfer applied
  -- to the landed ψ-keystone.
  have hpi := hT (psi_BV_of_siegelWalfisz' hSW)
  intro A hA
  obtain ⟨B, C, hB, hC, hev⟩ := hpi A hA
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  -- finite small-`x` constant (mirrors the Dispersion keystone's tail).
  set Csm : ℝ := ∑ x' ∈ Finset.Icc 2 x₀,
      (⌊Real.sqrt x' / (Real.log x') ^ B⌋₊ : ℝ) * ((x' : ℝ) + 1) * (Real.log x') ^ A / x'
    with hCsmdef
  have hterm_nn : ∀ x' ∈ Finset.Icc 2 x₀,
      0 ≤ (⌊Real.sqrt x' / (Real.log x') ^ B⌋₊ : ℝ) * ((x' : ℝ) + 1) * (Real.log x') ^ A / x' := by
    intro x' _
    have hlog : (0 : ℝ) ≤ Real.log x' := Real.log_natCast_nonneg x'
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Real.rpow_nonneg hlog A))
      (by positivity)
  have hCsm0 : 0 ≤ Csm := Finset.sum_nonneg hterm_nn
  refine ⟨B, max C Csm, hB, fun x hx => ?_⟩
  -- range bridge: `(x)^{1/2} → √x`.
  rw [show ((x : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt x from (Real.sqrt_eq_rpow x).symm]
  -- real facts at `x ≥ 2`.
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hLpos A
  set t : ℝ := (x : ℝ) / (Real.log x) ^ A with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  -- rewrite the RHS as `max C Csm * t`.
  rw [show max C Csm * (x : ℝ) / (Real.log x) ^ A = max C Csm * t by rw [htdef]; ring]
  by_cases hxx : x₀ ≤ x
  · -- eventual regime: the transfer's bound, then `C ≤ max C Csm`.
    have hbound := hx₀ x hxx
    calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, maxDiscrepancy x q
        ≤ C * x / (Real.log x) ^ A := hbound
      _ = C * t := by rw [htdef]; ring
      _ ≤ max C Csm * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
  · -- small-`x` regime: crude bound absorbed into `Csm`.
    have hxmem : x ∈ Finset.Icc 2 x₀ := Finset.mem_Icc.mpr ⟨hx, by omega⟩
    have hsingle :
        (⌊Real.sqrt x / (Real.log x) ^ B⌋₊ : ℝ) * ((x : ℝ) + 1) * (Real.log x) ^ A / x ≤ Csm := by
      rw [hCsmdef]
      exact Finset.single_le_sum hterm_nn hxmem
    calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, maxDiscrepancy x q
        ≤ (⌊Real.sqrt x / (Real.log x) ^ B⌋₊ : ℝ) * ((x : ℝ) + 1) := sum_maxDiscrepancy_crude x B
      _ = ((⌊Real.sqrt x / (Real.log x) ^ B⌋₊ : ℝ) * ((x : ℝ) + 1) * (Real.log x) ^ A / x) * t := by
          rw [htdef]; field_simp
      _ ≤ Csm * t := mul_le_mul_of_nonneg_right hsingle ht0
      _ ≤ max C Csm * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht0

end Salt.BV
