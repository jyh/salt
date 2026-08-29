/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The joint-invariance estimate (Chowla / entropy-decrement spine, wave II, node D-d)

The approximate translation invariance of the log-sampled window laws (Tao
arXiv:1509.05422v2 §3, the load-bearing MI-gain step of Lemma 3.1).  The shifted window
`X_H^{(j)} n := liouvilleWindow H (n + j·H)` samples the SAME `n`'s Liouville
values on the block `(n + jH, n + jH + H]`; under `logMeasure x ω` its law barely
moves, because the log-sampling weight `1/n` telescopes: the pushforward laws of
the joint variable `(X_H^{(j)}, Y_H)` and `(X_H, Y_H)` differ in `ℓ¹` by at most
`2 A_j / Σ` (`A_j = ∑_{x/ω < m ≤ x/ω + jH} 1/m`, `Σ = ∑_{x/ω < n ≤ x} 1/n`).

Exports:
* `liouvilleWindowShift` (+ `FiniteRange`/measurability): the shifted window.
-/
import Mathlib
import Salt.Entropy.Basic
import Salt.Entropy.Chowla.Windows
import Salt.Entropy.Chowla.PrimeWindow
import Salt.Entropy.Chowla.Fannes

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### The shifted window `X_H^{(j)}` -/

/-- The shifted Liouville window `X_H^{(j)} n := liouvilleWindow H (n + j·H)`: the
    length-`H` window of Liouville values starting just above `n + jH`.  At `j = 0`
    it is `liouvilleWindow H`. -/
def liouvilleWindowShift (H j : ℕ) (n : ℕ) : Fin H → ℤ := liouvilleWindow H (n + j * H)

@[simp] lemma liouvilleWindowShift_zero (H : ℕ) :
    liouvilleWindowShift H 0 = liouvilleWindow H := by
  funext n; simp [liouvilleWindowShift]

@[simp] lemma liouvilleWindowShift_apply (H j n : ℕ) (i : Fin H) :
    liouvilleWindowShift H j n i = ArithmeticFunction.liouville (n + j * H + i + 1) := rfl

/-- The shifted window lands in the same `{-1, 1}^H` product Finset. -/
lemma liouvilleWindowShift_mem_piFinset (H j n : ℕ) :
    liouvilleWindowShift H j n ∈ Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ)) :=
  liouvilleWindow_mem_piFinset H (n + j * H)

/-- The shifted window has finite range (contained in `{-1, 1}^H`). -/
instance instFiniteRangeShift (H j : ℕ) : FiniteRange (liouvilleWindowShift H j) :=
  finiteRange_of_finset (liouvilleWindowShift H j)
    (Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ)))
    (fun n => liouvilleWindowShift_mem_piFinset H j n)

/-- The shifted window is measurable (its domain `ℕ` is discrete/countable). -/
lemma measurable_liouvilleWindowShift (H j : ℕ) : Measurable (liouvilleWindowShift H j) :=
  measurable_of_countable _

/-! ### The arithmetic kernel: the log-sampling mass a shift moves -/

/-- **The arithmetic kernel of D-d** (wave-II gate, Charge 2 — the machine-checked
    form of the verified `2·A_j/Σ ≤ 8·j·H·ω/x`).  Under `logMeasure x ω` the total
    normalized `ℓ¹` mass that a shift by `t` (`= j·H`) can move is at most `8·t·ω/x`:
    the left-edge sum `A_t = ∑_{x/ω < m ≤ x/ω + t} 1/m` telescopes the shifted vs
    unshifted laws, and `A_t ≤ t·(2ω/x)` (each `1/m ≤ 2ω/x`, `t` terms) while the
    normalizer `Σ = ∑_{x/ω < n ≤ x} 1/n ≥ 1/2` (`logMeasure_norm_ge_half`, `ω ≥ 2`).
    So `2·A_t/Σ ≤ 4·A_t ≤ 8·t·ω/x`.  This is the quantity discharged `≤ exp(-1)` and
    fed to the Fannes bound `entropy_sub_le_of_l1` by the D-d headline. -/
theorem harmonic_shift_l1_le {x ω t : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) :
    2 * (∑ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹)
        / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ 8 * t * ω / x := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hω0 : (0 : ℝ) < ω := by exact_mod_cast (show 0 < ω by omega)
  set Sden : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hSdef
  set A : ℝ := ∑ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹ with hAdef
  -- normalizer floor `Σ ≥ 1/2`
  have hωR : (2 : ℝ) ≤ ω := by exact_mod_cast hω
  have hinv : (1 : ℝ) / ω ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hωR
  have hShalf : (1 : ℝ) / 2 ≤ Sden := by
    have h := logMeasure_norm_ge_half hx hω hωx
    rw [hSdef]; linarith
  have hSpos : (0 : ℝ) < Sden := by linarith
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun m _ => by positivity)
  -- termwise bound `1/m ≤ 2ω/x`
  have hterm : ∀ m ∈ Finset.Ioc (x / ω) (x / ω + t), (m : ℝ)⁻¹ ≤ 2 * ω / x := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    obtain ⟨hlo, _hhi⟩ := hm
    have hm1 : x / ω + 1 ≤ m := hlo
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hlo
    have hxlt : x < ω * m := by
      have hdm : ω * (x / ω) + x % ω = x := Nat.div_add_mod x ω
      have hmod : x % ω < ω := Nat.mod_lt x (by omega)
      have hml : ω * (x / ω + 1) ≤ ω * m := Nat.mul_le_mul (le_refl ω) hm1
      have he : ω * (x / ω + 1) = ω * (x / ω) + ω := by ring
      -- `x = ω*(x/ω) + x%ω < ω*(x/ω) + ω = ω*(x/ω+1) ≤ ω*m`
      calc x = ω * (x / ω) + x % ω := hdm.symm
        _ < ω * (x / ω) + ω := by omega
        _ = ω * (x / ω + 1) := he.symm
        _ ≤ ω * m := hml
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hmne : (m : ℝ) ≠ 0 := hmR.ne'
    have hxltR : (x : ℝ) < ω * m := by exact_mod_cast hxlt
    rw [le_div_iff₀ hx0]
    have hle : (m : ℝ)⁻¹ * x ≤ (m : ℝ)⁻¹ * (ω * m) :=
      mul_le_mul_of_nonneg_left hxltR.le (by positivity)
    have hcancel : (m : ℝ)⁻¹ * (ω * m) = ω := by
      rw [mul_comm (ω : ℝ) m, ← mul_assoc, inv_mul_cancel₀ hmne, one_mul]
    rw [hcancel] at hle
    linarith [hle, hω0]
  -- `A ≤ t · (2ω/x)`
  have hAle : A ≤ (t : ℝ) * (2 * (ω : ℝ) / (x : ℝ)) := by
    calc A ≤ ∑ _m ∈ Finset.Ioc (x / ω) (x / ω + t), (2 * (ω : ℝ) / (x : ℝ)) :=
            Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (x / ω) (x / ω + t)).card : ℝ) * (2 * (ω : ℝ) / (x : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (t : ℝ) * (2 * (ω : ℝ) / (x : ℝ)) := by
            rw [Nat.card_Ioc, show x / ω + t - x / ω = t from by omega]
  -- combine: `2A/Σ ≤ 4A ≤ 8tω/x`
  have hstep : 2 * A / Sden ≤ 4 * A := by
    rw [div_le_iff₀ hSpos]
    nlinarith [mul_nonneg hA0 (show (0 : ℝ) ≤ 2 * Sden - 1 by linarith)]
  have hfin : 4 * A ≤ 8 * (t : ℝ) * (ω : ℝ) / (x : ℝ) := by
    have h4 : 4 * A ≤ 4 * ((t : ℝ) * (2 * (ω : ℝ) / (x : ℝ))) := by linarith [hAle]
    have heq : 4 * ((t : ℝ) * (2 * (ω : ℝ) / (x : ℝ)))
        = 8 * (t : ℝ) * (ω : ℝ) / (x : ℝ) := by ring
    linarith [h4, heq.le]
  linarith [hstep, hfin]

end Salt.Entropy.Chowla
