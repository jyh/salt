/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.MomentOrbit
import Salt.Weil.NewtonBridge
import Salt.Weil.LocalFactor
import Mathlib

/-!
# Weil track, node W2T6.IND — the Theorem 6 induction (the η-ladder synthesis)

Blueprint: `docs/exploration/w2t6-design.md` §5 (the IND node). This is the final synthesis of
the η ladder. It glues the four landed inputs into Harcos Theorem 6:
```
  kloostermanMoment a b n = − localPowerSum (kloosterman a b).re p n   (n ≥ 1, ab ≠ 0).
```

The assembly, following the H3 friction recipe:

* **The bridge** (`cCoeff_eq_cCoeffN`). `MomentOrbit`'s `cCoeff` (via `irredMonicOfDeg`) and
  `NewtonBridge`'s `cCoeffN` (via `irredMonicOfDegN`) are the *same* object: both filter
  `Irreducible` over the `tuplePoly` image, and their membership lemmas have identical RHS, so
  the underlying Finsets are `Finset.ext`-equal and the coefficient sums coincide.

* **The `c`-recurrence** (inside `cCoeffN_eq_neg_localPowerSum`). At `n = m + 3` the Newton
  identity `newton_bridge` has `aCoeff a b (m+3) = 0` (`T5_ad`) on the left, and on the right the
  `Icc 1 (m+3)` sum keeps only `j ∈ {m+1, m+2, m+3}` — the others die by `T5_ad` on `a_{n-j}`.
  With `a₀ = 1`, `a₁ = S`, `a₂ = p` this gives `c_{m+3} = −S·c_{m+2} − p·c_{m+1}`, the
  *same* three-term recurrence as `−localPowerSum` (`localPowerSum_rec`).

* **The seeds.** `c₁ = a₁ = S = −P₁` and `c₂ = 2p − S² = −P₂`, from `newton_bridge`
  at `n = 1, 2`. A two-step strong induction forces `c_n = −P_n` for all `n ≥ 1`.

**Where `ab ≠ 0` enters.** Only through `T5_a2`/`T5_ad` in the recurrence extraction — `H1`
(`kloostermanMoment_eq_cCoeff`) and Newton (`newton_bridge`) are both hypothesis-free in `a, b`.
The realness `kloosterman a b = ((kloosterman a b).re : ℂ)` rides on `kloosterman_im`.
-/

namespace Salt.Weil

open scoped BigOperators
open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ### The bridge: `cCoeff = cCoeffN` -/

/-- `MomentOrbit`'s `irredMonicOfDeg` and `NewtonBridge`'s `irredMonicOfDegN` are the same Finset:
their membership predicates are literally `Monic ∧ natDegree = d ∧ Irreducible`. -/
theorem irredMonicOfDeg_eq_irredMonicOfDegN (d : ℕ) :
    irredMonicOfDeg p d = irredMonicOfDegN p d := by
  ext k
  simp only [mem_irredMonicOfDeg, mem_irredMonicOfDegN]

/-- **The coordination bridge.** The two coefficient sums coincide term by term. -/
theorem cCoeff_eq_cCoeffN (a b : ZMod p) (n : ℕ) : cCoeff a b n = cCoeffN a b n := by
  unfold cCoeff cCoeffN
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [irredMonicOfDeg_eq_irredMonicOfDegN]

/-- `S(a, b; p)` is real: `kloosterman a b = ((kloosterman a b).re : ℂ)`, via `kloosterman_im`. -/
private theorem kloosterman_eq_ofReal (a b : ZMod p) :
    kloosterman a b = ((kloosterman a b).re : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simp [kloosterman_im a b]

/-! ### The induction: `c_n = −P_n` -/

/-- **The η-ladder induction.** For all `n ≥ 1`, `cCoeffN a b n = − localPowerSum S p n` with
`S = (kloosterman a b).re`. Two-step strong induction: seeds `c₁, c₂` from `newton_bridge` at
`n = 1, 2`; step `c_{m+3} = −S·c_{m+2} − p·c_{m+1}` from `newton_bridge` at `n = m+3` after
killing the `aCoeff`-vanishing tail (`T5_ad`) and reading off `a₀, a₁, a₂`. -/
theorem cCoeffN_eq_neg_localPowerSum (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ n, 1 ≤ n → cCoeffN a b n = -localPowerSum (kloosterman a b).re p n := by
  have hreal := kloosterman_eq_ofReal a b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | _ | _ | m
    · exact absurd hn (by omega)
    · -- n = 1 : c₁ = a₁ = S = −P₁
      have h1 := newton_bridge a b 1 (by omega)
      rw [Finset.Icc_self, Finset.sum_singleton] at h1
      simp only [show (1 : ℕ) - 1 = 0 from rfl, T5_a0, T5_a1, Nat.cast_one, one_mul] at h1
      rw [localPowerSum_one, ← h1, neg_neg]; exact hreal
    · -- n = 2 : c₂ = 2p − S² = −P₂
      have hc1 := ih 1 (by omega) (by omega)
      have h2 := newton_bridge a b 2 (by omega)
      rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from by decide,
        Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)] at h2
      simp only [show (2 : ℕ) - 1 = 1 from rfl, show (2 : ℕ) - 2 = 0 from rfl,
        T5_a0, T5_a1, T5_a2 a b ha hb] at h2
      have hP2 : localPowerSum (kloosterman a b).re p 2
          = -((kloosterman a b).re : ℂ) * localPowerSum (kloosterman a b).re p 1
            - (p : ℂ) * localPowerSum (kloosterman a b).re p 0 := localPowerSum_rec _ p 0
      rw [localPowerSum_zero, localPowerSum_one] at hP2
      rw [localPowerSum_one] at hc1
      push_cast at h2
      rw [hP2]
      linear_combination -h2 - ((kloosterman a b).re : ℂ) * hc1 - (cCoeffN a b 1) * hreal
    · -- n = m + 3 : the three-term recurrence
      have hi1 := ih (m + 1) (by omega) (by omega)
      have hi2 := ih (m + 2) (by omega) (by omega)
      have hN := newton_bridge a b (m + 3) (by omega)
      rw [T5_ad a b ha (by omega : 3 ≤ m + 3), mul_zero] at hN
      have htail : (∑ j ∈ Finset.Icc 1 m, aCoeff a b (m + 3 - j) * cCoeffN a b j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [T5_ad a b ha (by omega : 3 ≤ m + 3 - j), zero_mul]
      have hpeel1 : (∑ j ∈ Finset.Icc 1 (m + 3), aCoeff a b (m + 3 - j) * cCoeffN a b j)
          = (∑ j ∈ Finset.Icc 1 (m + 2), aCoeff a b (m + 3 - j) * cCoeffN a b j)
            + aCoeff a b (m + 3 - (m + 3)) * cCoeffN a b (m + 3) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hpeel2 : (∑ j ∈ Finset.Icc 1 (m + 2), aCoeff a b (m + 3 - j) * cCoeffN a b j)
          = (∑ j ∈ Finset.Icc 1 (m + 1), aCoeff a b (m + 3 - j) * cCoeffN a b j)
            + aCoeff a b (m + 3 - (m + 2)) * cCoeffN a b (m + 2) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hpeel3 : (∑ j ∈ Finset.Icc 1 (m + 1), aCoeff a b (m + 3 - j) * cCoeffN a b j)
          = (∑ j ∈ Finset.Icc 1 m, aCoeff a b (m + 3 - j) * cCoeffN a b j)
            + aCoeff a b (m + 3 - (m + 1)) * cCoeffN a b (m + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      rw [hpeel1, hpeel2, hpeel3, htail] at hN
      simp only [show m + 3 - (m + 1) = 2 from by omega, show m + 3 - (m + 2) = 1 from by omega,
        show m + 3 - (m + 3) = 0 from by omega, T5_a0, T5_a1, T5_a2 a b ha hb] at hN
      have hrec : cCoeffN a b (m + 3)
          = -((kloosterman a b).re : ℂ) * cCoeffN a b (m + 2)
            - (p : ℂ) * cCoeffN a b (m + 1) := by
        linear_combination -hN - (cCoeffN a b (m + 2)) * hreal
      have hP3 : localPowerSum (kloosterman a b).re p (m + 3)
          = -((kloosterman a b).re : ℂ) * localPowerSum (kloosterman a b).re p (m + 2)
            - (p : ℂ) * localPowerSum (kloosterman a b).re p (m + 1) :=
        localPowerSum_rec _ p (m + 1)
      rw [hrec, hi2, hi1, hP3]; ring

/-! ### The headline: Theorem 6 -/

/-- **Harcos Theorem 6.** For `ab ≠ 0` and `n ≥ 1`, the twisted Kloosterman moment over
`𝔽_{p^n}` is minus the `n`-th local power sum: `M_n(a, b) = −(αⁿ + βⁿ)` with `α, β` the
reciprocal roots of `1 + S·T + p·T²`, `S = (kloosterman a b).re`. This is `H1`
(`kloostermanMoment_eq_cCoeff`) composed with `cCoeff = cCoeffN` and the η-ladder induction. -/
theorem kloostermanMoment_eq_neg_localPowerSum (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    kloostermanMoment a b n = -localPowerSum (kloosterman a b).re p n := by
  rw [kloostermanMoment_eq_cCoeff a b (by omega : n ≠ 0), cCoeff_eq_cCoeffN]
  exact cCoeffN_eq_neg_localPowerSum a b ha hb n hn

end Salt.Weil
