/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.PsiToPi

/-!
# V4-core — the discretized-Abel ψ→π transfer (`PsiToPiCore` reduction)

Design: `docs/blueprints/bv.md`, node `V4` (the θ→π partial summation) and
`docs/blueprints/flags.md` (the V4/V5 entry, mechanism). This module discharges
the *plumbing* around the genuinely-analytic Abel core and isolates that core as
a single, precisely-stated hypothesis `PsiToPiCore`.

## What is landed here (sorry-free, complete)

* `sum_omega_mul_le` — the **gate-free conversion sum**: the `ω(q)·L/φq` gap
  (dispDisc's mean is `psiChi χ₀/φq`, the transfer needs the `psiTot/φq` mean;
  the gap is `norm_psiChi_one_sub_psiTot_le`'s `ω(q)·L`) summed over the haircut
  range is polylog — `∑_{q≤Q} ω(q)·L/φq ≤ (logb 2 Q)·L·4(1+log Q)` — via
  `primeFactors_card_le_logb` (`ω(q) ≤ logb 2 Q`) and `sum_inv_totient_le`
  (`∑ 1/φq ≤ 4(1+log Q)`). No Siegel–Walfisz gate appears. This is a complete
  sub-lemma of the deferred core.

* `psiToPiTransfer_of_core` — the **complete reduction** of `PsiToPiTransfer` to
  the single hypothesis `PsiToPiCore`. Given the ψ-family (`psi_BV_of_siegelWalfisz'`'s
  shape), this discharges — sorry-free — the entire assembly *around* the Abel
  core: the `∀A ∃B ∃C` packaging, the haircut inflation `B := B' + A` (with the
  ψ-family carried to the smaller range by monotonicity, absorbing the
  prime-power `x/L^B` term), the scale-uniform `M`-instantiation of the ψ-bound,
  the polylog conversion absorption (via `absorb_nat`, `√x·(1+log x)³ = o(x/L^A)`),
  and the constant `C := 5 + 2C'`.

## The single deferred piece: `PsiToPiCore`

`PsiToPiCore` isolates *exactly* the discretized-Abel analytic content: per `x`,
given a scale-uniform bound `M` on the ψ-form q-sum (`∀ y ≤ x, ∑_q dispDisc y q ≤ M`
— precisely what the ψ-keystone delivers at each `x`), the π-form q-sum is
controlled by

  `∑_q maxDiscrepancy x q ≤ √x·(1+log x)³  +  2·M  +  4·x/(log x)^B`.

The three summands are, respectively: the **polylog conversion** (`ω(q)L/φq` gap,
bounded here by `sum_omega_mul_le`, ≤ `√x·(1+log x)³`); the **main Abel term**
(`Σ_q Σ_n w_n dispDisc(n) q` with telescoping weights `Σ_n w_n = 1/log 2 < 2`,
swapped `Σ_q` inside and bounded by `2M` since `Σ_q dispDisc(n) q ≤ M` uniformly
in the scale `n`); and the **prime-power correction** (`ψ−θ` on the dyadic net,
`~ Q·√x`, ≤ `4x/L^B` after the haircut). Its faithful proof needs
`Finset.sum_Ioc_by_parts` (the log-weighted Abel identity for `primesCount`, cf.
`Salt/BV/TypeI.lean`'s `abel_log_char_le` precedent) and a `ψ(t)−θ(t) = O(√t·log²t)`
Chebyshev bound absent from mathlib — deferred (PB-floor). See
`docs/blueprints/flags.md`, the V4-core entry.

Discharging `PsiToPiCore` (via `psiToPiTransfer_of_core`) yields the frozen
`PsiToPiTransfer`, upgrading `hasLevel_half_of_siegelWalfisz_of_bridge` and
`bounded_gaps_of_siegelWalfisz_of_bridge` to their unconditional forms.
-/

namespace Salt.BV

open Finset Filter Salt.LS Salt.Maynard
open scoped BigOperators

/-! ## The gate-free conversion sum (complete) -/

/-- **Gate-free conversion sum.** The `ω(q)·L/φq` mean-reconciliation gap
(`dispDisc`'s mean is `psiChi χ₀/φq`; the π-transfer wants `psiTot/φq`, the gap
`≤ ω(q)·L` by `norm_psiChi_one_sub_psiTot_le`) summed over the haircut range is
polylog: `∑_{q≤Q} ω(q)·L/φq ≤ (logb 2 Q)·L·4(1+log Q)`. No Siegel–Walfisz gate
appears (`ω(q) ≤ logb 2 Q` is `primeFactors_card_le_logb`; `∑ 1/φq ≤ 4(1+log Q)`
is `sum_inv_totient_le`). -/
lemma sum_omega_mul_le {Q : ℕ} (hQ : 1 ≤ Q) {L : ℝ} (hL : 0 ≤ L) :
    ∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ) * L / (q.totient : ℝ)
      ≤ Real.logb 2 Q * L * (4 * (1 + Real.log Q)) := by
  have hlogbnn : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) (by exact_mod_cast hQ)
  have hstep : ∀ q ∈ Finset.Icc 1 Q,
      (q.primeFactors.card : ℝ) * L / (q.totient : ℝ)
        ≤ Real.logb 2 Q * L * (1 / (q.totient : ℝ)) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hq1 : 1 ≤ q := hq.1
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hω : (q.primeFactors.card : ℝ) ≤ Real.logb 2 Q := by
      calc (q.primeFactors.card : ℝ) ≤ Real.logb 2 q := primeFactors_card_le_logb hq1
        _ ≤ Real.logb 2 Q :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hq1) (by exact_mod_cast hq.2)
    have hLφ : (0 : ℝ) ≤ L / (q.totient : ℝ) := div_nonneg hL hφpos.le
    rw [mul_div_assoc]
    calc (q.primeFactors.card : ℝ) * (L / (q.totient : ℝ))
        ≤ Real.logb 2 Q * (L / (q.totient : ℝ)) := mul_le_mul_of_nonneg_right hω hLφ
      _ = Real.logb 2 Q * L * (1 / (q.totient : ℝ)) := by ring
  calc ∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ) * L / (q.totient : ℝ)
      ≤ ∑ q ∈ Finset.Icc 1 Q, Real.logb 2 Q * L * (1 / (q.totient : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = Real.logb 2 Q * L * ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ Real.logb 2 Q * L * (4 * (1 + Real.log Q)) :=
        mul_le_mul_of_nonneg_left (sum_inv_totient_le Q hQ) (by positivity)

/-! ## The discretized-Abel core (single deferred hypothesis) -/

/-- **The discretized-Abel core (node V4, deferred).** The genuine analytic heart
of the ψ→π transfer, isolated as a single hypothesis. For each `x ≥ 2` and each
haircut `B`, given a *scale-uniform* bound `M` on the ψ-form q-sum
(`∀ y ≤ x, ∑_q dispDisc y q ≤ M` — exactly what the ψ-keystone delivers), the
π-form q-sum is controlled by the polylog conversion `√x·(1+log x)³`, the main
Abel term `2·M`, and the prime-power correction `4·x/(log x)^B`. See the module
docstring and `docs/blueprints/flags.md` for the mechanism (`Finset.sum_Ioc_by_parts`
on the log-weighted counting sum + a `ψ−θ = O(√x·log²x)` Chebyshev bound). -/
def PsiToPiCore : Prop :=
  ∀ (x : ℕ) (B M : ℝ), 2 ≤ x → 0 ≤ B → 0 ≤ M →
    (∀ y : ℕ, y ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, dispDisc y q ≤ M) →
    ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, maxDiscrepancy x q
      ≤ (x : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log x) ^ (3 : ℝ) + 2 * M + 4 * x / (Real.log x) ^ B

/-! ## The complete reduction -/

/-- **`PsiToPiTransfer` from the Abel core (complete, sorry-free).** The full
assembly around `PsiToPiCore`: extract the ψ-family at saving `A + 1`, inflate the
haircut to `B := B' + A` (carrying the ψ-bound to the smaller range by
monotonicity, which tames the prime-power `x/L^B` term), instantiate the
scale-uniform `M := C'·x/(log x)^{A+1}`, apply the core, and absorb the polylog
conversion `√x·(1+log x)³ = o(x/(log x)^A)` via `absorb_nat`. Constant
`C := 5 + 2C'`. -/
theorem psiToPiTransfer_of_core (hCore : PsiToPiCore) : PsiToPiTransfer := by
  intro hψ A hA
  obtain ⟨B', C', hB', hC', hψb⟩ := hψ (A + 1) (by linarith)
  refine ⟨B' + A, 5 + 2 * C', add_nonneg hB' hA.le, by positivity, ?_⟩
  filter_upwards [absorb_nat (θ := (1 / 2 : ℝ)) (k := (3 : ℝ)) (A := A) (M := (1 : ℝ))
        (by norm_num) (by norm_num) (by norm_num),
      eventually_ge_atTop 3] with x habs hx3
  have hx2 : 2 ≤ x := by omega
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      _ ≤ (x : ℝ) := hx3R
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hLApos : (0 : ℝ) < (Real.log x) ^ A := Real.rpow_pos_of_pos hLpos A
  have hLA1pos : (0 : ℝ) < (Real.log x) ^ (A + 1) := Real.rpow_pos_of_pos hLpos (A + 1)
  -- the scale-uniform bound `M`
  have hM0 : 0 ≤ C' * (x : ℝ) / (Real.log x) ^ (A + 1) :=
    div_nonneg (mul_nonneg hC' hxpos.le) hLA1pos.le
  -- the ψ-family carried to the inflated (smaller) range `√x/L^{B'+A}`
  have hBmono : Real.sqrt x / (Real.log x) ^ (B' + A) ≤ Real.sqrt x / (Real.log x) ^ B' :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hLpos B')
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hsub : Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (B' + A)⌋₊
      ⊆ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B'⌋₊ :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_floor hBmono)
  have hyp : ∀ y : ℕ, y ≤ x →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (B' + A)⌋₊, dispDisc y q
        ≤ C' * (x : ℝ) / (Real.log x) ^ (A + 1) := by
    intro y hyx
    calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (B' + A)⌋₊, dispDisc y q
        ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B'⌋₊, dispDisc y q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => dispDisc_nonneg y q)
      _ ≤ C' * (x : ℝ) / (Real.log x) ^ (A + 1) := hψb x y hx2 hyx
  -- apply the Abel core
  have hcore := hCore x (B' + A) (C' * (x : ℝ) / (Real.log x) ^ (A + 1))
    hx2 (add_nonneg hB' hA.le) hM0 hyp
  refine le_trans hcore ?_
  -- bound the three summands by multiples of `x/(log x)^A`
  rw [one_mul] at habs
  have hLexp1 : (Real.log x) ^ A ≤ (Real.log x) ^ (A + 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLexp2 : (Real.log x) ^ A ≤ (Real.log x) ^ (B' + A) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h2M : 2 * (C' * (x : ℝ) / (Real.log x) ^ (A + 1))
      ≤ 2 * (C' * (x : ℝ) / (Real.log x) ^ A) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (mul_nonneg hC' hxpos.le) hLApos hLexp1) (by norm_num)
  have h4 : 4 * (x : ℝ) / (Real.log x) ^ (B' + A) ≤ 4 * (x : ℝ) / (Real.log x) ^ A :=
    div_le_div_of_nonneg_left (by positivity) hLApos hLexp2
  calc (x : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log x) ^ (3 : ℝ)
          + 2 * (C' * (x : ℝ) / (Real.log x) ^ (A + 1))
          + 4 * (x : ℝ) / (Real.log x) ^ (B' + A)
      ≤ (x : ℝ) / (Real.log x) ^ A + 2 * (C' * (x : ℝ) / (Real.log x) ^ A)
          + 4 * (x : ℝ) / (Real.log x) ^ A :=
        add_le_add (add_le_add habs h2M) h4
    _ = (5 + 2 * C') * (x : ℝ) / (Real.log x) ^ A := by
        field_simp
        ring

end Salt.BV
