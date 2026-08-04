/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.TwistedMertens
import Salt.SW.BCSup

/-!
# HB 1983, Lemma 3 — the remainder discharged (node N4a, closing wave)

`Salt/HB/TwistedMertens.lean` landed `hb_lemma3_final` with three carried items beyond the
transfer-side data: `hrem` (the partial fraction's analytic remainder *difference*, Davenport
ch. 12 (17)), and the two export defects `hβZ`/`hmβ` and `hmz`.  All three are discharged here
by one call to `Salt.SW.LFunction_partialFraction_remainder_diff`:

* `hrem` — the Cauchy/Schwarz difference bound off the (already landed, see the `hsup` verdict
  in `Salt/SW/BCSup.lean`) S2-Z3c sup estimate, at the explicit rate
  `Rrem = 1600·log(80√f(1+log f))·(σ′−σ)`.  At HB's operating points `σ = 1+L^{−1}`,
  `σ′ = 1+aL^{−1}` this is `O(a)`, which is what (4.2)'s optimization prices.
* `hβZ`, `hmβ` — the converse membership of the exported zero set.
* `hmz` — `m = zeroMult` on `Z`, at equality.

What remains in `hb_lemma3_unconditional` is exactly the **transfer-side and F-side** data:
`hsq`, `hA`, `hres`, `hcoef` (N3's, unchanged), the operating-point arithmetic, and the two
Deuring–Heilbronn inputs `hfloor`/`hSinv` that the F-side artillery supplies (`hSinv` is priced
unconditionally by `Salt.HB.invSq_sum_split_le`, whose own hypotheses `hzero`/`hmz` this
theorem's exports now meet).  No analytic input is carried.
-/

namespace Salt.HB

open Complex Metric DirichletCharacter Set

/-- **HB Lemma 3 with the remainder discharged.**  For a primitive real character `χ` mod
`f ≥ 2` with a zero `β₀ ∈ (1/2, 1)` of `L(·,χ)`, the `t₀ = 0` partial fraction supplies a zero
set `Z` with multiplicities `m` such that `β₀ ∈ Z`, `m β₀ ≥ 1`, every `ρ ∈ Z` is a zero of
`L(·,χ)`, and `m = zeroMult` on `Z` — and, given only the F-side repulsion data
(`hfloor`, `hSinv`) and N3's transfer-side data (`hres`, `hcoef`), HB (3.3) holds at the rate
`hbCoreRate σ σ′ Sinv Rrem` with the **explicit** remainder

    Rrem = 1600·log(80√f(1+log f))·(σ′ − σ).

This is `hb_lemma3_final` with its `hrem`, `hβZ`, `hmβ` and (via the exported `m = zeroMult`)
`hmz` all supplied. -/
theorem hb_lemma3_unconditional {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (hsq : χ ^ 2 = 1)
    {A : Finset ℕ} (hA : CoprimeSupport f A) (x : ℝ) (N : ℕ) (Cmain z0 Aexp junk : ℝ)
    {σ σ' β₀ r0 Sinv : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hlt : σ ≤ σ') (hσ'2 : σ' ≤ 2)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hr0 : 0 < r0) (hσr : σ - 1 ≤ r0 / 2) (hσ'r : σ' - 1 ≤ r0 / 2) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖) →
        (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        (overshootMajorant χ A
          ≤ Cmain * (x / z0)
            + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N + junk) →
        0 ≤ Cmain * (x / Real.log x) * Real.exp (Aexp * z0) →
        S2 χ A - S1 A
          ≤ Cmain * (x / z0)
            + Cmain * (x / Real.log x) * Real.exp (Aexp * z0)
              * ((N : ℝ) ^ (σ - 1) * ((1 - β₀) / (σ - 1) ^ 2
                  + hbCoreRate σ σ' Sinv
                      (1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) * (σ' - σ))) / 2)
            + junk) := by
  classical
  obtain ⟨Z, m, hmemZ, hconv, hmult, hdiff⟩ :=
    Salt.SW.LFunction_partialFraction_remainder_diff χ hχ hf
  -- `β₀` lies in the disk, hence in `Z` with multiplicity `≥ 1`
  have hβball : ((β₀ : ℝ) : ℂ) ∈ ball (2 : ℂ) (3 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hcast : (((β₀ : ℝ) : ℂ) - 2) = ((β₀ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  obtain ⟨hβZ, hmβ⟩ := hconv ((β₀ : ℝ) : ℂ) hβball hβ0
  refine ⟨Z, m, hβZ, hmβ, fun ρ hρ => (hmemZ ρ hρ).2, fun ρ hρ => le_of_eq ?_, ?_⟩
  · exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (hmult ρ hρ)
  · intro hfloor hSinv hres hcoef
    have hσ'1 : 1 ≤ σ' := by linarith
    have hrem := hdiff σ σ' (by linarith) hσ2 hσ'1 hσ'2
    have habs : |σ - σ'| = σ' - σ := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [habs] at hrem
    exact hb_lemma3_final χ hsq hA x N Cmain z0 Aexp junk hσ1 hσ2 hlt hσ'2 hβ1 hβZ hmβ
      hr0 hσr hσ'r hfloor hSinv hrem hres hcoef

end Salt.HB
