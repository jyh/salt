/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7L

/-!
# HSIGMA-COMP — the repulsion floor discharges `hb_L1_one_sided`'s `hσ'r`

Two landed statements had never been composed in Lean:

* the **supply**, `Salt.HB.one_sub_ceiling_le_dist_one` (`Salt/HB/PretenseSumProof.lean:312`):
  a zero capped by the Deuring–Heilbronn `Salt.SW.repulsionCeiling b c k Q u` is at distance
  at least `(log(1/u) − log(1/c) − k·log(log Q + 2))/(b·log Q)` from `1`;
* the **demand**, `Salt.HB.hb_L1_one_sided` (`Salt/HB/Lemma7L.lean:231`), whose two
  `r0`-binders are `hr0 : 0 < r0` and `hσ'r : √(log η)/(2L) ≤ r0/2`, and whose conclusion
  carries the antecedent `∀ ρ ∈ Z.erase β₀, r0 ≤ ‖ρ − 1‖`.

This file instantiates `r0` at the repulsion floor and kernel-checks the join.

## ⛔ SCOPE FENCE — what this file does NOT certify

It certifies the **`hσ'r` obligation only**.  There is a *second, independent* demand on
`log η` from the Range-A EF ledger (`efEnvelope_le_ledger_sharp`,
`Salt/HB/Lemma7EF.lean:2624-2632`, inside the byte-fixed window at `:2844`), which contributes
a `5b/s·log L` term that is **entirely `k`-independent**.  Nothing here certifies the door,
`q`-freeness, or the full threshold: this is **one of two conjoined obligations**.

## What lands

* `sqrt_quad_of_threshold` — the quadratic step.  `B·√ℓ + D ≤ ℓ` as soon as `ℓ` clears the
  explicit threshold `(B + D/B)²`.  This is the whole mathematical content: with
  `u = 1 − β₀ = (ηL)^{−1}` one has `log(1/u) = log η + log L`, so `hσ'r` becomes a
  **quadratic in `√(log η)`**, satisfiable only above a threshold.
* `repulsion_floor_gives_hsigma` — the composition.  Supplies **both** of `hb_L1_one_sided`'s
  `r0`-binders (`0 < r0` and `hσ'r`) from the repulsion floor, under an explicit largeness
  bound on `log η`.
* `hb_L1_one_sided_at_repulsion_floor` — the end-to-end wiring: `(L1)` with the `hfloor`
  antecedent **discharged**, off a ceiling hypothesis quantified over the zeros of `L(·,χ)`.
* `hsigma_largeness_satisfiable` — the vacuity check, kernel-checked.  `hb_L1_one_sided`
  carries `hηq : log η ≤ L` while the largeness bound needs `log η ≳ 4.6·10⁵`; together these
  force `L ≳ 4.6·10⁵`, i.e. `q ≳ e^{460000}`.  That is **consistent, not contradictory** — a
  witness at `b = 680`, `k = 14`, `log(1/c) = 90`, `Q = e^{10⁶}`, `L = 10⁶`, `log η = 5·10⁵`
  satisfies every arithmetic binder simultaneously.

## The threshold, and what moves it

At `Q` with `log Q = L` the composed demand reads

    b·√ℓ  ≤  ℓ + log L − log(1/c) − k·log(log Q + 2),      ℓ = log η,

so `b` enters through `b²` and `log(1/c)` enters **additively**.  That is the arithmetic the
demand-side trace (`docs/exploration/n4-n8-obligation-trace-0806.md`, §5) did by hand; it is
here in the kernel.
-/

namespace Salt.HB

/-! ## §1 — the quadratic step -/

/-- **The quadratic step.**  For `B > 0` and `D ≥ 0`, the inequality `B·√ℓ + D ≤ ℓ` — a
quadratic in `√ℓ` — holds as soon as `ℓ` clears the explicit threshold `(B + D/B)²`.

The threshold is sharp to within `(D/B)²`: at `s = B + D/B` the quadratic
`s² − B·s − D` equals exactly `(D/B)²`, and its true root is `(B + √(B² + 4D))/2`. -/
lemma sqrt_quad_of_threshold {B D ell : ℝ} (hB : 0 < B) (hD : 0 ≤ D)
    (hthr : (B + D / B) ^ 2 ≤ ell) :
    B * Real.sqrt ell + D ≤ ell := by
  have hd0 : (0 : ℝ) ≤ D / B := div_nonneg hD hB.le
  have ht0 : (0 : ℝ) < B + D / B := by linarith
  have hell0 : (0 : ℝ) ≤ ell := le_trans (sq_nonneg _) hthr
  have hs : B + D / B ≤ Real.sqrt ell := by
    have h := Real.sqrt_le_sqrt hthr
    rwa [Real.sqrt_sq ht0.le] at h
  have hsq : Real.sqrt ell ^ 2 = ell := Real.sq_sqrt hell0
  have hDB : D / B * B = D := by field_simp
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by positivity : (0 : ℝ) ≤ Real.sqrt ell + D / B),
    sq_nonneg (D / B)]

/-! ## §2 — the composition -/

open Salt.SW in
/-- **HSIGMA-COMP.**  The repulsion floor

    r₀ = (log(1/u) − log(1/c) − k·log(log Q + 2)) / (b·log Q)

— the quantity `one_sub_ceiling_le_dist_one` produces from `repulsionCeiling b c k Q u` —
supplies **both** `r0`-binders of `hb_L1_one_sided`: `hr0 : 0 < r0` and
`hσ'r : √(log η)/(2L) ≤ r0/2`.

The mathematical content is `hσ'r`.  With `u = 1 − β₀` and `η = ((1−β₀)L)^{−1}` one has
`1/u = η·L`, hence `log(1/u) = log η + log L`, and the obligation becomes

    (b·log Q/L)·√(log η)  ≤  log η + log L − log(1/c) − k·log(log Q + 2),

a **quadratic in `√(log η)`**.  It is therefore *false for small `η`* and the lemma must — and
does — carry a largeness hypothesis, exactly as `hb_L1_one_sided` already carries
`hell : 1 ≤ log η`.  `hlarge` is that hypothesis, in the explicit threshold form of
`sqrt_quad_of_threshold` with `B = b·log Q/L` and `D` the deficit
`log(1/c) + k·log(log Q + 2) − log L`.

⛔ This discharges the `hσ'r` obligation ONLY.  See the file header's scope fence. -/
lemma repulsion_floor_gives_hsigma
    {b c k Q u η L β₀ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hQ : 1 < Q) (hβ1 : β₀ < 1)
    (hη : η = 1 / ((1 - β₀) * L)) (hu : u = 1 - β₀)
    (hD : 0 ≤ Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
    (hlarge : (b * Real.log Q / L
        + (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
            / (b * Real.log Q / L)) ^ 2 ≤ Real.log η) :
    0 < (Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))
          / (b * Real.log Q) ∧
      Real.sqrt (Real.log η) / (2 * L)
        ≤ ((Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2))
            / (b * Real.log Q)) / 2 := by
  have hβ0 : (0 : ℝ) < 1 - β₀ := by linarith
  have hne : (1 : ℝ) - β₀ ≠ 0 := ne_of_gt hβ0
  have hLne : L ≠ 0 := ne_of_gt hL
  have hηpos : 0 < η := by rw [hη]; positivity
  -- `1/u = η·L`, hence `log(1/u) = log η + log L`
  have hlogu : Real.log (1 / u) = Real.log η + Real.log L := by
    have h1 : 1 / u = η * L := by rw [hu, hη]; field_simp
    rw [h1, Real.log_mul (ne_of_gt hηpos) hLne]
  have hlq : 0 < Real.log Q := Real.log_pos hQ
  have hBpos : 0 < b * Real.log Q / L := by positivity
  -- the quadratic step
  have hkey := sqrt_quad_of_threshold hBpos hD hlarge
  have hkey2 : b * Real.log Q / L * Real.sqrt (Real.log η)
      ≤ Real.log η + Real.log L - Real.log (1 / c)
        - k * Real.log (Real.log Q + 2) := by linarith
  -- positivity of the floor: `ℓ − D ≥ B² + D + (D/B)² > 0`
  have hd0 : (0 : ℝ) ≤ (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
      / (b * Real.log Q / L) := div_nonneg hD hBpos.le
  have hDB : (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
      / (b * Real.log Q / L) * (b * Real.log Q / L)
      = Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L := by
    field_simp
  have hnum : 0 < Real.log η + Real.log L - Real.log (1 / c)
      - k * Real.log (Real.log Q + 2) := by
    nlinarith [hlarge, hDB, mul_pos hBpos hBpos, mul_nonneg hBpos.le hd0, sq_nonneg
      ((Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
        / (b * Real.log Q / L))]
  constructor
  · rw [hlogu]
    exact div_pos hnum (by positivity)
  · rw [hlogu, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hkey2 (by positivity : (0 : ℝ) ≤ 2 * L)
    have heq : b * Real.log Q / L * Real.sqrt (Real.log η) * (2 * L)
        = Real.sqrt (Real.log η) * (b * Real.log Q * 2) := by field_simp
    rw [heq] at hmul
    exact hmul

/-! ## §3 — the end-to-end wiring -/

open Salt.SW in
/-- **`(L1)` at the repulsion floor — the `hfloor` antecedent DISCHARGED.**

`hb_L1_one_sided` delivers its rate only behind two antecedents, one of which is the distance
floor `∀ ρ ∈ Z.erase β₀, r0 ≤ ‖ρ − 1‖`.  Instantiating `r0` at the repulsion floor,
`one_sub_ceiling_le_dist_one` discharges that antecedent from a `repulsionCeiling` hypothesis
quantified over the zeros of `L(·,χ)` (the shape `Salt.SW.boxZeros_re_le_unit_box` and
`Salt.SW.boxZeros_re_le_at_efHeight` produce), and `repulsion_floor_gives_hsigma` supplies the
two `r0`-binders.  What is left is the `(4.1)` error-sum antecedent alone.

Note the `Q` is *free*: no relation between `Q` and `L = log q` is assumed here, so the lemma
is base-agnostic.  The base enters only through `hlarge`, where the ratio `log Q/L` scales `b`.

⛔ This is the `hσ'r` obligation only; see the file header's scope fence. -/
theorem hb_L1_one_sided_at_repulsion_floor {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f)
    {β₀ Sinv Cs L η b c k Q u : ℝ}
    (hLpos : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hell : 1 ≤ Real.log η) (hηq : Real.log η ≤ L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * ((2 * L) ^ 2 / Real.log η))
    (hCR : Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ L)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hb : 0 < b) (hQ : 1 < Q) (hu : u = 1 - β₀)
    (hD : 0 ≤ Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
    (hlarge : (b * Real.log Q / L
        + (Real.log (1 / c) + k * Real.log (Real.log Q + 2) - Real.log L)
            / (b * Real.log Q / L)) ^ 2 ≤ Real.log η)
    (hceil : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) →
        ρ.re ≤ repulsionCeiling b c k Q u) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        (-logDeriv (DirichletCharacter.LFunction χ) (1 : ℂ)).re
          ≤ -((Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) * (η * L))
            + (1604 + 2 * (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) + 8 * Cs)
                * (L / Real.sqrt (Real.log η))) := by
  obtain ⟨hr0, hσ'r⟩ := repulsion_floor_gives_hsigma hb hLpos hQ hβ1 hη hu hD hlarge
  obtain ⟨Z, m, hβZ, hmβ, hzero, hmz, hbody⟩ :=
    hb_L1_one_sided χ hχ hf hLpos hη hell hηq hCs hSinvC hCR hβlo hβ1 hβ0 hr0 hσ'r
  refine ⟨Z, m, hβZ, hmβ, hzero, hmz, fun hSinv => hbody (fun ρ hρ => ?_) hSinv⟩
  exact one_sub_ceiling_le_dist_one
    (hceil ρ (hzero ρ (Finset.mem_of_mem_erase hρ)) (Finset.ne_of_mem_erase hρ))

/-! ## §4 — the vacuity check -/

/-- **NOT VACUOUS.**  `hb_L1_one_sided` carries `hηq : log η ≤ L`, while the largeness bound
of `repulsion_floor_gives_hsigma` needs `log η ≳ b² ≈ 4.6·10⁵`.  Together these force
`L ≳ 4.6·10⁵`, i.e. `q ≳ e^{460000}` — a *large-`q`* regime, not a contradiction.  Both are
hypotheses, and this theorem exhibits a simultaneous witness at the post-TAU-SHARP parameters

    b = 680,  k = 14,  log(1/c) = 90,  Q = e^{10⁶},  L = 10⁶,  log η = 5·10⁵,

so `q`-largeness is the only price.  (The `β₀` is then pinned by `η = ((1−β₀)L)^{−1}`, and it
lands in `(1/2, 1)` with room to spare.) -/
theorem hsigma_largeness_satisfiable :
    ∃ β₀ η : ℝ,
      1 / 2 < β₀ ∧ β₀ < 1 ∧
      η = 1 / ((1 - β₀) * (10 : ℝ) ^ 6) ∧
      1 ≤ Real.log η ∧ Real.log η ≤ (10 : ℝ) ^ 6 ∧
      0 ≤ Real.log (1 / Real.exp (-90))
            + 14 * Real.log (Real.log (Real.exp ((10 : ℝ) ^ 6)) + 2)
            - Real.log ((10 : ℝ) ^ 6) ∧
      (680 * Real.log (Real.exp ((10 : ℝ) ^ 6)) / (10 : ℝ) ^ 6
          + (Real.log (1 / Real.exp (-90))
              + 14 * Real.log (Real.log (Real.exp ((10 : ℝ) ^ 6)) + 2)
              - Real.log ((10 : ℝ) ^ 6)) / (680 * Real.log (Real.exp ((10 : ℝ) ^ 6))
                / (10 : ℝ) ^ 6)) ^ 2
        ≤ Real.log η := by
  set η : ℝ := Real.exp (5 * 10 ^ 5) with hηdef
  have hηpos : 0 < η := Real.exp_pos _
  have hlogη : Real.log η = 5 * 10 ^ 5 := by rw [hηdef, Real.log_exp]
  -- `η ≥ 1 + 5·10⁵`, so `η·10⁶ > 2`
  have hηbig : (5 : ℝ) * 10 ^ 5 + 1 ≤ η := by rw [hηdef]; exact Real.add_one_le_exp _
  have hprod : (2 : ℝ) < η * 10 ^ 6 := by nlinarith
  have hsmall : 1 / (η * (10 : ℝ) ^ 6) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hpos : 0 < 1 / (η * (10 : ℝ) ^ 6) := by positivity
  refine ⟨1 - 1 / (η * (10 : ℝ) ^ 6), η, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (1 : ℝ) - (1 - 1 / (η * (10 : ℝ) ^ 6)) = 1 / (η * (10 : ℝ) ^ 6) := by ring
    rw [h]; field_simp
  · rw [hlogη]; norm_num
  · rw [hlogη]; norm_num
  -- the deficit `D` is nonnegative: `log(10⁶) ≤ log(10⁶+2) ≤ 14·log(10⁶+2)`
  · rw [Real.log_exp, one_div, Real.log_inv, Real.log_exp]
    have h1 : Real.log ((10 : ℝ) ^ 6) ≤ Real.log ((10 : ℝ) ^ 6 + 2) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log ((10 : ℝ) ^ 6 + 2) := Real.log_nonneg (by norm_num)
    linarith
  -- the largeness bound: `D ≤ 370 ≤ 680`, so `(680 + D/680)² ≤ 681² ≤ 5·10⁵`
  · rw [Real.log_exp, one_div, Real.log_inv, Real.log_exp, hlogη]
    have h1 : Real.log ((10 : ℝ) ^ 6) ≤ Real.log ((10 : ℝ) ^ 6 + 2) :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log ((10 : ℝ) ^ 6 + 2) := Real.log_nonneg (by norm_num)
    have h3 : Real.log ((10 : ℝ) ^ 6 + 2) ≤ 20 * Real.log 2 := by
      have hle : Real.log ((10 : ℝ) ^ 6 + 2) ≤ Real.log ((2 : ℝ) ^ 20) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rwa [Real.log_pow, Nat.cast_ofNat] at hle
    have h4 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have h5 : (0 : ℝ) ≤ Real.log ((10 : ℝ) ^ 6) := Real.log_nonneg (by norm_num)
    have hB : (680 : ℝ) * ((10 : ℝ) ^ 6) / (10 : ℝ) ^ 6 = 680 := by norm_num
    rw [hB]
    have hquad : ∀ D : ℝ, 0 ≤ D → D ≤ 680 → (680 + D / 680) ^ 2 ≤ 5 * 10 ^ 5 := by
      intro D hD0 hD1
      have he : D / 680 ≤ 1 := by rw [div_le_one (by norm_num)]; exact hD1
      have he0 : (0 : ℝ) ≤ D / 680 := by positivity
      nlinarith [he, he0, mul_nonneg he0 (by linarith : (0 : ℝ) ≤ 1 - D / 680)]
    exact hquad _ (by linarith) (by linarith)

end Salt.HB
