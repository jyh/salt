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

## The `Rrem` absorption (§2 below)

`Rrem` reaches the consumer as a *separate additive term* inside `hbCoreRate`.  At HB's
operating points `σ = 1 + L^{−1}`, `σ′ = 1 + aL^{−1}` with `a = (log η)^{1/2}` it is
`CR·(a−1)/L`, and the campaign's two conventions — `CR ≤ 800·L` (the `L`-vs-`f` convention:
`L ≥ 2·log(80√f(1+log f))`) and `log η ≤ L` — turn it into `≤ 800·L(log η)^{−1/2}`, the *same*
shape as the rest of the rate.  So it absorbs into the constant:

    hbCoreRate  ≤  2 + (802 + 4Cs)·L·(log η)^{−1/2},

i.e. HB's `K = 2 + 4Cs` grows to `K = 802 + 4Cs` and downstream consumers see **one** constant.
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

/-! ## §2 — the `Rrem` absorption: one rate constant, `K = 802 + 4Cs` -/

/-- **The remainder absorbed into the rate constant.**  At HB's optimum
`σ = 1 + L^{−1}`, `σ′ = 1 + (log η)^{1/2}L^{−1}`, a remainder of the *Lipschitz* shape
`Rrem = CR·(σ′−σ)` costs `CR·(√ℓ−1)/L ≤ 800(√ℓ−1) ≤ 800·√ℓ = 800·ℓ/√ℓ ≤ 800·L/√ℓ`, using
`CR ≤ 800·L` and `ℓ ≤ L`.  That is the *same* `L(log η)^{−1/2}` shape as the two error terms
of (4.2), so it merges with them:

    hbCoreRate  ≤  2 + (802 + 4Cs)·L·(log η)^{−1/2}.

This is `hbCoreRate_at_hb_optimum` with its `+ Rrem` swallowed — HB's `K = 2 + 4Cs` becomes
`K = 802 + 4Cs`, and the rate SHAPE is unchanged. -/
theorem hbCoreRate_at_hb_optimum_absorbed {Lp ell Sinv Cs CR : ℝ}
    (hell : 1 ≤ ell) (hellL : ell ≤ Lp) (hCs : 0 ≤ Cs)
    (hSinv : Sinv ≤ Cs * (Lp ^ 2 / ell)) (hCR : CR ≤ 800 * Lp) :
    hbCoreRate (1 + 1 / Lp) (1 + Real.sqrt ell / Lp) Sinv
        (CR * ((1 + Real.sqrt ell / Lp) - (1 + 1 / Lp)))
      ≤ 2 + (802 + 4 * Cs) * (Lp / Real.sqrt ell) := by
  have hell0 : (0 : ℝ) < ell := lt_of_lt_of_le zero_lt_one hell
  have hL : (0 : ℝ) < Lp := lt_of_lt_of_le hell0 hellL
  have hLne : Lp ≠ 0 := ne_of_gt hL
  have hs : (0 : ℝ) < Real.sqrt ell := Real.sqrt_pos.mpr hell0
  have hsne : Real.sqrt ell ≠ 0 := ne_of_gt hs
  have hs1 : (1 : ℝ) ≤ Real.sqrt ell := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hell
  have hmul : Real.sqrt ell * Real.sqrt ell = ell := Real.mul_self_sqrt hell0.le
  -- the base rate, with the remainder still riding additively
  have hbase := hbCoreRate_at_hb_optimum (Sinv := Sinv)
    (Rrem := CR * ((1 + Real.sqrt ell / Lp) - (1 + 1 / Lp))) hL hell hCs hSinv
  -- the absorption itself
  have hstep : (1 + Real.sqrt ell / Lp) - (1 + 1 / Lp) = (Real.sqrt ell - 1) / Lp := by ring
  have hnn : (0 : ℝ) ≤ (Real.sqrt ell - 1) / Lp := div_nonneg (by linarith) hL.le
  have h1 : CR * ((Real.sqrt ell - 1) / Lp) ≤ 800 * Lp * ((Real.sqrt ell - 1) / Lp) :=
    mul_le_mul_of_nonneg_right hCR hnn
  have h2 : 800 * Lp * ((Real.sqrt ell - 1) / Lp) = 800 * (Real.sqrt ell - 1) := by
    field_simp
  have h3 : Real.sqrt ell ≤ Lp / Real.sqrt ell := by
    have hd : Lp / Real.sqrt ell - Real.sqrt ell = (Lp - ell) / Real.sqrt ell := by
      field_simp
      nlinarith [hmul]
    have hpos : (0 : ℝ) ≤ (Lp - ell) / Real.sqrt ell := div_nonneg (by linarith) hs.le
    linarith
  have habs : CR * ((1 + Real.sqrt ell / Lp) - (1 + 1 / Lp)) ≤ 800 * (Lp / Real.sqrt ell) := by
    rw [hstep]; linarith
  have hring : 2 + 800 * (Lp / Real.sqrt ell) + (2 + 4 * Cs) * (Lp / Real.sqrt ell)
      = 2 + (802 + 4 * Cs) * (Lp / Real.sqrt ell) := by ring
  linarith

/-- **HB 1983, LEMMA 3 — UNCONDITIONAL, AT THE OPERATING POINT, WITH ONE CONSTANT.**
`hb_lemma3_unconditional` fired at `σ = 1 + L^{−1}`, `σ′ = 1 + (log η)^{1/2}L^{−1}` and the
remainder absorbed: the consumer sees the pole term `(1−β₀)L²` and a single rate

    2 + K·L·(log η)^{−1/2},    K = 802 + 4Cs,

with **no `Rrem` in the statement**.  The two campaign conventions enter as the named
hypotheses `hCR` (`L ≥ 2·log(80√f(1+log f))`, the `L`-vs-`f` convention) and `hellL`
(`log η ≤ L`); `hSinvC` is the F-side repulsion pricing `Sinv ≤ Cs·L²(log η)^{−1}` that
`invSq_sum_split_le` supplies.  The operating-point arithmetic of
`hb_lemma3_unconditional` (`1 < σ ≤ 2`, `σ ≤ σ′ ≤ 2`) is discharged here from `1 ≤ ℓ ≤ L`. -/
theorem hb_lemma3_unconditional_absorbed {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (hsq : χ ^ 2 = 1)
    {A : Finset ℕ} (hA : CoprimeSupport f A) (x : ℝ) (N : ℕ) (Cmain z0 Aexp junk : ℝ)
    {β₀ r0 Sinv Cs Lp ell : ℝ}
    (hell : 1 ≤ ell) (hellL : ell ≤ Lp) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * (Lp ^ 2 / ell))
    (hCR : 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ 800 * Lp)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hr0 : 0 < r0) (hσr : 1 / Lp ≤ r0 / 2) (hσ'r : Real.sqrt ell / Lp ≤ r0 / 2) :
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
              * ((N : ℝ) ^ (1 / Lp) * ((1 - β₀) * Lp ^ 2
                  + (2 + (802 + 4 * Cs) * (Lp / Real.sqrt ell))) / 2)
            + junk) := by
  have hell0 : (0 : ℝ) < ell := lt_of_lt_of_le zero_lt_one hell
  have hL : (0 : ℝ) < Lp := lt_of_lt_of_le hell0 hellL
  have hLne : Lp ≠ 0 := ne_of_gt hL
  have hL1 : (1 : ℝ) ≤ Lp := le_trans hell hellL
  have hs : (0 : ℝ) < Real.sqrt ell := Real.sqrt_pos.mpr hell0
  have hs1 : (1 : ℝ) ≤ Real.sqrt ell := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hell
  have hmul : Real.sqrt ell * Real.sqrt ell = ell := Real.mul_self_sqrt hell0.le
  have hsle : Real.sqrt ell ≤ Lp := le_trans (by nlinarith [hmul]) hellL
  have hinv0 : (0 : ℝ) < 1 / Lp := by positivity
  have hinv1 : 1 / Lp ≤ 1 := (div_le_one hL).mpr hL1
  -- the operating-point arithmetic
  have hσ1 : (1 : ℝ) < 1 + 1 / Lp := by linarith
  have hσ2 : 1 + 1 / Lp ≤ 2 := by linarith
  have hlt : 1 + 1 / Lp ≤ 1 + Real.sqrt ell / Lp := by
    have := (div_le_div_iff_of_pos_right hL).mpr hs1
    linarith
  have hσ'2 : 1 + Real.sqrt ell / Lp ≤ 2 := by
    have := (div_le_one hL).mpr hsle
    linarith
  obtain ⟨Z, m, hβZ, hmβ, hzero, hmz, hbody⟩ :=
    hb_lemma3_unconditional χ hχ hf hsq hA x N Cmain z0 Aexp junk
      (σ := 1 + 1 / Lp) (σ' := 1 + Real.sqrt ell / Lp) (β₀ := β₀) (r0 := r0) (Sinv := Sinv)
      hσ1 hσ2 hlt hσ'2 hβlo hβ1 hβ0 hr0 (by linarith) (by linarith)
  refine ⟨Z, m, hβZ, hmβ, hzero, hmz, ?_⟩
  intro hfloor hSinv hres hcoef
  have hmain := hbody hfloor hSinv hres hcoef
  have hrate := hbCoreRate_at_hb_optimum_absorbed (Sinv := Sinv) (Cs := Cs)
    (CR := 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f))) hell hellL hCs hSinvC hCR
  have hexp : (1 + 1 / Lp) - 1 = 1 / Lp := by ring
  have hNn : (0 : ℝ) ≤ (N : ℝ) ^ (1 / Lp : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hstep : (N : ℝ) ^ ((1 + 1 / Lp) - 1) * ((1 - β₀) / ((1 + 1 / Lp) - 1) ^ 2
        + hbCoreRate (1 + 1 / Lp) (1 + Real.sqrt ell / Lp) Sinv
            (1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f))
              * ((1 + Real.sqrt ell / Lp) - (1 + 1 / Lp)))) / 2
      ≤ (N : ℝ) ^ (1 / Lp) * ((1 - β₀) * Lp ^ 2
          + (2 + (802 + 4 * Cs) * (Lp / Real.sqrt ell))) / 2 := by
    rw [hexp]
    have hpole : (1 - β₀) / (1 / Lp : ℝ) ^ 2 = (1 - β₀) * Lp ^ 2 := by field_simp
    rw [hpole]
    nlinarith [mul_le_mul_of_nonneg_left hrate hNn]
  have hmono := mul_le_mul_of_nonneg_left hstep hcoef
  linarith

end Salt.HB
