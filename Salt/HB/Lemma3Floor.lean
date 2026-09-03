/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma3Uncond
import Salt.HB.HSigmaComp
import Salt.SW.TauExt

/-!
# HB Lemma 3 at the repulsion floor — the N3 JOIN of the fulcrum campaign

`hb_lemma3_unconditional_absorbed` with its floor antecedent discharged from a
`repulsionCeiling` hypothesis, the mirror of `HSigmaComp`.  A join is not the engine;
nothing here bears on twin primes.

## The two sides

* the **demand**, `Salt.HB.hb_lemma3_unconditional_absorbed`
  (`Salt/HB/Lemma3Uncond.lean:213`), which delivers HB Lemma 3's rate only behind the
  distance floor `∀ ρ ∈ Z.erase β₀, r0 ≤ ‖ρ − 1‖` together with the three `r0`-binders
  `hr0 : 0 < r0`, `hσr : 1/Lp ≤ r0/2`, `hσ'r : √ell/Lp ≤ r0/2`;
* the **supply**, `Salt.HB.one_sub_ceiling_le_dist_one`
  (`Salt/HB/PretenseSumProof.lean:312`): a zero capped by the Deuring–Heilbronn
  `Salt.SW.repulsionCeiling b c k Q u` sits at distance at least
  `(log(1/u) − log(1/c) − k·log(log Q + 2))/(b·log Q)` from `1`.

Instantiating `r0` at that floor joins them, exactly as
`hb_L1_one_sided_at_repulsion_floor` (`Salt/HB/HSigmaComp.lean:170`) does for the `(L1)`
twin.  Here `Lp := L` and `ell := log η`.

## The one difference from the `(L1)` template

`(L1)` needs `√ℓ/(2L) ≤ r0/2`; N3 needs `√ℓ/L ≤ r0/2` — a factor `2` more demanding.  So
the quadratic step `sqrt_quad_of_threshold` (`HSigmaComp` §1) is applied here with
`B := 2·b·log Q / L` rather than `b·log Q / L`, and `hlarge` is the threshold in that `B`.
The third binder `1/L ≤ r0/2` is then free: `1 ≤ √(log η)` (from `hell`) makes it the
`√ℓ ↦ 1` specialization of the same inequality.

## ⛔ SCOPE FENCE — what this file does NOT certify

* `hceil` is an **interface, not a theorem proved here**: it is the tall-box shape the
  TAU-EXT artillery supplies — at the `|γ| ≤ 1` range Lemma 3 actually needs, by
  `Salt.SW.boxZeros_re_le_unit_box` (`Salt/SW/TauExt.lean:340`, this file's import); at
  EF height, by `Salt.SW.boxZeros_re_le_at_efHeight` (`Salt/SW/TBalTall.lean:2231`, NOT
  imported here).  Nothing about the door, `q`-freeness, or the tall re-thread is settled
  here, and no `hceil` is *produced* — it is consumed.
* the **`Sinv` antecedent is deliberately still carried**.  The error sum
  `∑_{ρ ≠ β₀} m_ρ/‖ρ − 1‖² ≤ Sinv` is priced by `Salt.HB.invSq_sum_split_le`
  (`Salt/HB/TwistedMertens.lean:597`), and that composition is **out of scope for this
  file**: only the *floor* antecedent is discharged.
* as with `HSigmaComp`, the largeness hypothesis `hlarge` is genuine — the obligation is a
  quadratic in `√(log η)` and is false for small `η`.  No vacuity check is re-run here; the
  `(L1)` witness (`hsigma_largeness_satisfiable`) is at the strictly weaker `B`.
-/

namespace Salt.HB

open Finset ArithmeticFunction
open scoped ArithmeticFunction
open Salt.SW

/-! ## §1 — the three `r0`-binders from the floor -/

/-- **The N3 analogue of `repulsion_floor_gives_hsigma`.**  The repulsion floor

    r₀ = (log(1/u) − log(1/c) − k·log(log Q + 2)) / (b·log Q)

supplies **all three** `r0`-binders of `hb_lemma3_unconditional_absorbed` at `Lp = L`,
`ell = log η`: `0 < r0`, `1/L ≤ r0/2` and `√(log η)/L ≤ r0/2`.

With `u = 1 − β₀` and `η = ((1−β₀)L)^{−1}` one has `1/u = η·L`, so
`log(1/u) = log η + log L` and the binding obligation `√ℓ/L ≤ r0/2` reads

    (2·b·log Q/L)·√(log η)  ≤  log η + log L − log(1/c) − k·log(log Q + 2),

a **quadratic in `√(log η)`** — `sqrt_quad_of_threshold` with `B = 2·b·log Q/L` and `D` the
deficit `log(1/c) + k·log(log Q + 2) − log L`.  The `2` in `B` is the whole difference from
the `(L1)` twin, whose demand is `√ℓ/(2L) ≤ r0/2`.

The other two binders fall out of the same inequality: `1 ≤ √(log η)` turns it into
`B ≤ ℓ − D`, which is both `1/L ≤ r0/2` and (with `B > 0`) the positivity `0 < r0`. -/
lemma repulsion_floor_gives_lemma3_binders
    {b c k Q u η L β₀ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hQ : 1 < Q) (hβ1 : β₀ < 1)
    (hη : η = 1 / ((1 - β₀) * L)) (hu : u = 1 - β₀)
    (hell : 1 ≤ Real.log η)
    (hD : 0 ≤ Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
    (hlarge : (2 * b * Real.log Q / L
        + (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
            / (2 * b * Real.log Q / L)) ^ 2 ≤ Real.log η) :
    0 < (Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))
          / (b * Real.log Q) ∧
      1 / L
        ≤ ((Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))
            / (b * Real.log Q)) / 2 ∧
      Real.sqrt (Real.log η) / L
        ≤ ((Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))
            / (b * Real.log Q)) / 2 := by
  have hβ0 : (0 : ℝ) < 1 - β₀ := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL
  have hηpos : 0 < η := by rw [hη]; positivity
  -- `1/u = η·L`, hence `log(1/u) = log η + log L`
  have hlogu : Real.log (1 / u) = Real.log η + Real.log L := by
    have h1 : 1 / u = η * L := by rw [hu, hη]; field_simp
    rw [h1, Real.log_mul (ne_of_gt hηpos) hLne]
  have hlq : 0 < Real.log Q := Real.log_pos hQ
  have hBpos : 0 < 2 * b * Real.log Q / L := by positivity
  -- the quadratic step, at the N3 constant `B = 2·b·log Q/L`
  have hkey := sqrt_quad_of_threshold hBpos hD hlarge
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.log η) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hell
  have hBs : 2 * b * Real.log Q / L * 1
      ≤ 2 * b * Real.log Q / L * Real.sqrt (Real.log η) :=
    mul_le_mul_of_nonneg_left hs1 hBpos.le
  -- `B ≤ ℓ − D`, the common parent of all three binders
  have hBle : 2 * b * Real.log Q / L
      ≤ Real.log η + Real.log L - Real.log (1 / c)
        - k * Real.log (Real.log Q + 2) := by linarith
  have hnum : 0 < Real.log η + Real.log L - Real.log (1 / c)
      - k * Real.log (Real.log Q + 2) := lt_of_lt_of_le hBpos hBle
  refine ⟨?_, ?_, ?_⟩
  · rw [hlogu]
    exact div_pos hnum (by positivity)
  · rw [hlogu, div_div, div_le_div_iff₀ hL (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hBle hL.le
    have heq : 2 * b * Real.log Q / L * L = b * Real.log Q * 2 := by field_simp
    rw [heq] at hmul
    linarith
  · rw [hlogu, div_div, div_le_div_iff₀ hL (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right
      (show 2 * b * Real.log Q / L * Real.sqrt (Real.log η)
          ≤ Real.log η + Real.log L - Real.log (1 / c)
            - k * Real.log (Real.log Q + 2) by linarith) hL.le
    have heq : 2 * b * Real.log Q / L * Real.sqrt (Real.log η) * L
        = Real.sqrt (Real.log η) * (b * Real.log Q * 2) := by field_simp
    rw [heq] at hmul
    exact hmul

/-! ## §2 — the join -/

/-- **HB LEMMA 3 AT THE REPULSION FLOOR — the `hfloor` antecedent DISCHARGED.**

`hb_lemma3_unconditional_absorbed` delivers its rate only behind three antecedents, one of
which is the distance floor `∀ ρ ∈ Z.erase β₀, r0 ≤ ‖ρ − 1‖`.  Instantiating `r0` at the
Deuring–Heilbronn repulsion floor, `one_sub_ceiling_le_dist_one` discharges that antecedent
from the ceiling hypothesis `hceil` — the tall-box interface, consumed not proved — and
`repulsion_floor_gives_lemma3_binders` supplies the three `r0`-binders.

What is left in the conclusion is the `Sinv` error-sum antecedent (deliberately still
carried: it is priced by `invSq_sum_split_le`, out of scope here) together with N3's own
transfer-side `hres`/`hcoef`.

As in the `(L1)` twin, `Q` is *free*: no relation between `Q` and `L = log q` is assumed,
so the join is base-agnostic; the base enters only through `hlarge`, where the ratio
`log Q/L` scales `b`.

⛔ This discharges the FLOOR antecedent only; see the file header's scope fence. -/
theorem hb_lemma3_at_repulsion_floor {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (hsq : χ ^ 2 = 1)
    {A : Finset ℕ} (hA : CoprimeSupport f A) (x : ℝ) (N : ℕ) (Cmain z0 Aexp junk : ℝ)
    {β₀ Sinv Cs L η b c k Q u : ℝ}
    (hLpos : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hell : 1 ≤ Real.log η) (hηq : Real.log η ≤ L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * (L ^ 2 / Real.log η))
    (hCR : 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ 800 * L)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hb : 0 < b) (hQ : 1 < Q) (hu : u = 1 - β₀)
    (hD : 0 ≤ Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
    (hlarge : (2 * b * Real.log Q / L
        + (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
            / (2 * b * Real.log Q / L)) ^ 2 ≤ Real.log η)
    (hceil : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) →
        ρ.re ≤ repulsionCeiling b c k Q u) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        (overshootMajorant χ A
          ≤ Cmain * (x / z0)
            + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N + junk) →
        0 ≤ Cmain * (x / Real.log x) * Real.exp (Aexp * z0) →
        S2 χ A - S1 A
          ≤ Cmain * (x / z0)
            + Cmain * (x / Real.log x) * Real.exp (Aexp * z0)
              * ((N : ℝ) ^ (1 / L) * ((1 - β₀) * L ^ 2
                  + (2 + (802 + 4 * Cs) * (L / Real.sqrt (Real.log η)))) / 2)
            + junk) := by
  obtain ⟨hr0, hσr, hσ'r⟩ :=
    repulsion_floor_gives_lemma3_binders hb hLpos hQ hβ1 hη hu hell hD hlarge
  obtain ⟨Z, m, hβZ, hmβ, hzero, hmz, hbody⟩ :=
    hb_lemma3_unconditional_absorbed χ hχ hf hsq hA x N Cmain z0 Aexp junk
      (Lp := L) (ell := Real.log η) (β₀ := β₀) (Sinv := Sinv) (Cs := Cs)
      hell hηq hCs hSinvC hCR hβlo hβ1 hβ0 hr0 hσr hσ'r
  refine ⟨Z, m, hβZ, hmβ, hzero, hmz, fun hSinv hres hcoef =>
    hbody (fun ρ hρ => ?_) hSinv hres hcoef⟩
  exact one_sub_ceiling_le_dist_one
    (hceil ρ (hzero ρ (Finset.mem_of_mem_erase hρ)) (Finset.ne_of_mem_erase hρ))

end Salt.HB
