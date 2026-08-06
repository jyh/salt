/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7Prod
import Salt.HardyLittlewood.Frame

/-!
# HB 1983, Lemma 7 — node N4b, wave **W4**, part γ: **the assembly to `(L2)`**

Heath-Brown pp.207–210, the closing paragraph.  W3 evaluated `log F`; this file runs HB's
`(4.4)+(4.5)+(4.6)` and produces the design freeze's second object,

    (L2)   κ S₁  =  {1 + δ} · x · 𝔖 · C(α) · (m·ηL)^{−2},   |δ| explicitly bounded,

at `m = 1` (design v3 **D11**: `hm1` rides — the `F`-side cancellation is valid at no other
multiplicity).

## The chain, and what is *proved* versus what *rides*

* `(4.6)` `∏_{p<z}(1−1/p)² = {1+O(z₀/L)}e^{−2γ₀}(log z)^{−2}` — **proved**
  (`hb_mertens_third_real`; `Salt.Mertens.mertens_third_log` + the `⌊·⌋ → ℝ` re-indexing,
  no new analytic input).
* `F² = e^{2γ₀}(log z)²(ηL)^{−2}{1+O(Δ)}` — **proved** (`sq_eq_exp_mul_one_add`), as an
  explicit `Real.exp` bound off `Real.abs_exp_sub_one_le`, never an informal absorption.
* `log F = log log z − log(ηL) + γ₀ + O(Δ)` — **proved in wave 3**
  (`hb_logF_at_split_point`).
* `(4.4)`, the finite-product rearrangement of `κS₁` — **named binder** `hrear`: the sieve
  side (`G(p)`, `ρ₁`, `C(α)`) has no corpus definition yet; see the `W4.5` note below.
* `(4.5)` `𝔖(z,χ) = {1+O(z^{−1})}𝔖` — **named binder** `hsing`, stated against the corpus's
  *own* `𝔖` (`Salt.HardyLittlewood.twinSingularSeries`).

Nothing is hidden inside an `O(·)`: `hrear` and `hsing` each come with an explicit numeric bound
(`a1`, `a2`) on their `{1+ε}` factor, and the conclusion's `δ` is bounded by

    |δ| ≤ 4·Δ + 8·E_P + 2·a1 + 2·a2                                        (`hb_L2_core`)

with `Δ` W3's total and `E_P` the `(4.6)` error.  At HB's operating point
(`Δ ≍ z₀(log η)^{−1/2}`, `E_P ≍ z₀/L`, `a1 ≍ z₀/z`, `a2 ≍ z^{−1}`) this is HB's
`{1 + O(z₀(log η)^{−1/2})}`, with `K₄ = 4`.

## The `W4.5` stone (recorded, not owed here)

`κ` — HB's sieve normalisation — has no corpus definition, so `(4.4)` cannot be *proved* at the
bytes: it is a statement about `ρ₁`, `G(p)` and `C(α)`, none of which exist yet.  `S₁` **is**
defined here (`hbS1`, HB p.207 exactly), so `(L2)` is stated about the honest object
`κ · S₁`, and the residue is precisely: *define `κ`, `G`, `C(α)` and prove `hrear`.*  That is the
`W4.5` stone for the N5/N6 consumer wiring.

## Binders (all named, nothing silent)

`hz` (`3 ≤ z`), `hα` (`(α:ℝ) < z` — HB's "assuming `z > α`", consumed by `(4.4)`'s provider),
`hηL`/`hβ₀1`/`hL`/`hη` (the `η` package), `hX`/`hwin` (the split point and the **upper** window
edge), `hηlarge` (`500 ≤ η`, W3's addition), `hm1` (D11), `hsmall` (the exponentiation guard
`4Δ + 8E_P + 2a2 ≤ 1`, HB's own side condition), plus W3's three rows `htail`/`hseg`/`hcorr`.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set MeasureTheory
open Salt.SW
open scoped Topology

namespace Salt.HB

/-! ## §1 — the exponentiation guard and the multiplicative error algebra -/

/-- `exp(2 log u) = u²`. -/
lemma exp_two_mul_log {u : ℝ} (hu : 0 < u) : Real.exp (2 * Real.log u) = u ^ 2 := by
  rw [show (2 : ℝ) * Real.log u = Real.log u + Real.log u by ring, Real.exp_add,
    Real.exp_log hu, sq]

/-- **The `F²` step, as an explicit `Real.exp` bound.**  Design v3 forbids an informal
`O`-absorption here: from `|log F − A| ≤ Δ` and the guard `2Δ ≤ 1`,

    F² = e^{2A}·(1 + ε),   |ε| ≤ 4Δ,

the `ε`-bound being mathlib's `|e^w − 1| ≤ 2|w|` at `|w| ≤ 1`. -/
lemma sq_eq_exp_mul_one_add {F A Δ : ℝ} (hF : 0 < F) (h : |Real.log F - A| ≤ Δ)
    (hΔ : 2 * Δ ≤ 1) :
    ∃ ε : ℝ, F ^ 2 = Real.exp (2 * A) * (1 + ε) ∧ |ε| ≤ 4 * Δ := by
  have habs := abs_nonneg (Real.log F - A)
  have hw : |2 * (Real.log F - A)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  refine ⟨Real.exp (2 * (Real.log F - A)) - 1, ?_, ?_⟩
  · rw [show (1 : ℝ) + (Real.exp (2 * (Real.log F - A)) - 1)
        = Real.exp (2 * (Real.log F - A)) by ring, ← Real.exp_add,
      show 2 * A + 2 * (Real.log F - A) = 2 * Real.log F by ring, exp_two_mul_log hF]
  · have hb := Real.abs_exp_sub_one_le hw
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hb
    linarith

/-- Two-factor multiplicative error algebra: `|(1+a)(1+b) − 1| ≤ |a| + 2|b|` for `|a| ≤ 1`. -/
lemma abs_one_add_mul_sub_one_le {a b : ℝ} (ha : |a| ≤ 1) :
    |(1 + a) * (1 + b) - 1| ≤ |a| + 2 * |b| := by
  rw [show (1 + a) * (1 + b) - 1 = a + b + a * b by ring]
  calc |a + b + a * b| ≤ |a + b| + |a * b| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |a| * |b| := by
        rw [abs_mul]; exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ |a| + 2 * |b| := by nlinarith [abs_nonneg b, abs_nonneg a]

/-! ## §2 — `(4.6)`: Mertens' third theorem re-indexed to a real cutoff -/

/-- HB's `(4.6)` product `∏_{p ≤ z}(1 − 1/p)`, at a **real** cutoff `z` (read as `p ≤ ⌊z⌋`). -/
noncomputable def primeProdBelow (z : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

lemma primeProdBelow_pos {z : ℝ} : 0 < primeProdBelow z := by
  refine Finset.prod_pos (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have h1 : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff_of_pos_left one_pos (by linarith) (by norm_num)]; linarith
  linarith

/-- **`(4.6)`, re-indexed to a real cutoff** (the freeze's "`mertens_third` is `∃C` and
`ℕ`-indexed — W4 owes the re-indexing"):

    |log ∏_{p ≤ z}(1 − 1/p) + log log z + γ₀|  ≤  C / log z    for `z ≥ 3`,

with `C = 2C₀ + 1` where `C₀ = 14` is `Salt.Mertens.mertens_third_log`'s constant. -/
theorem hb_mertens_third_real :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 3 ≤ z →
      |Real.log (primeProdBelow z) + Real.log (Real.log z) + Real.eulerMascheroniConstant|
        ≤ C / Real.log z := by
  obtain ⟨C₀, hC₀, h⟩ := Salt.Mertens.mertens_third_log
  refine ⟨2 * C₀ + 1, by linarith, fun z hz => ?_⟩
  have hn3 : 3 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have hnR : (3 : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hn3
  have hnz : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzn : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  have hn0 : (0 : ℝ) < (⌊z⌋₊ : ℝ) := by linarith
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
  have hlogn1 : (1 : ℝ) < Real.log (⌊z⌋₊ : ℝ) :=
    lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hnR)
  have hlogz1 : (1 : ℝ) < Real.log z := lt_of_lt_of_le hlogn1 (Real.log_le_log hn0 hnz)
  -- the ℕ-indexed statement at `n = ⌊z⌋`
  have hkey := h ⌊z⌋₊ hn3
  have hPeq : primeProdBelow z
      = ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := rfl
  rw [← hPeq] at hkey
  -- the iterated-log bridge
  have hbridge := abs_log_log_floor_sub_le hz
  -- `log z ≤ 2 log ⌊z⌋` (i.e. `z ≤ ⌊z⌋²`)
  have hsq : z ≤ (⌊z⌋₊ : ℝ) ^ 2 := by nlinarith
  have hdouble : Real.log z ≤ 2 * Real.log (⌊z⌋₊ : ℝ) := by
    have := Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hratio : C₀ / Real.log (⌊z⌋₊ : ℝ) ≤ 2 * C₀ / Real.log z := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  -- compose
  have htri : |Real.log (primeProdBelow z) + Real.log (Real.log z)
        + Real.eulerMascheroniConstant|
      ≤ |Real.log (primeProdBelow z) + Real.log (Real.log (⌊z⌋₊ : ℝ))
          + Real.eulerMascheroniConstant|
        + |Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ))| := by
    have := abs_add_le (Real.log (primeProdBelow z) + Real.log (Real.log (⌊z⌋₊ : ℝ))
        + Real.eulerMascheroniConstant)
      (Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ)))
    calc |Real.log (primeProdBelow z) + Real.log (Real.log z)
            + Real.eulerMascheroniConstant|
        = |(Real.log (primeProdBelow z) + Real.log (Real.log (⌊z⌋₊ : ℝ))
              + Real.eulerMascheroniConstant)
            + (Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ)))| := by ring_nf
      _ ≤ _ := this
  have hfin : (2 * C₀ + 1) / Real.log z = 2 * C₀ / Real.log z + 1 / Real.log z := by ring
  rw [hfin]
  linarith

/-! ## §3 — HB's sieve product `S₁` (p.207) -/

/-- **HB's `S₁`** (p.207): `∏_{p < z, χ_ℝ(p) = 1, p ∤ α} (p−1)(p−2)/(p(p+1))`, the second
form of `∏(1 − G(p)/p)` over the same range. -/
noncomputable def hbS1 {q : ℕ} (χ : DirichletCharacter ℂ q) (α : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ Salt.TwinBar.chiRe χ p = 1 ∧ ¬ (p ∣ α)),
    ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) + 1))

/-! ## §4 — the assembly `(L2)` -/

/-- **`(L2)` — the core assembly.**  HB pp.207–210, `(4.4)+(4.5)+(4.6)` composed with W3's
`log F`.  All four `{1+ε}` factors carry explicit numeric bounds, and the `F²`/`P²` steps are
honest `Real.exp` bounds:

    κS₁ = (1 + δ)·x·𝔖·C(α)/(ηL)²,     |δ| ≤ 4Δ + 8E_P + 2a₁ + 2a₂.

`Δ` is W3's `log F` error, `E_P` is `(4.6)`'s, `a₁` is `(4.4)`'s rearrangement error and `a₂` is
`(4.5)`'s.  `hsmall : 4Δ + 8E_P + 2a₂ ≤ 1` is HB's own side condition, here in the exact form the
exponentiation needs. -/
theorem hb_L2_core {q : ℕ} (χ : DirichletCharacter ℂ q)
    {L η z x Calpha Sing Singz kS1 Delta EP a1 a2 e1 e2 : ℝ}
    (hηL : 0 < η * L)
    (hF : |Real.log (hbF χ z)
        - (Real.log (Real.log z) - Real.log (η * L) + Real.eulerMascheroniConstant)| ≤ Delta)
    (hP : |Real.log (primeProdBelow z) + Real.log (Real.log z)
        + Real.eulerMascheroniConstant| ≤ EP)
    (hrear : kS1 = (1 + e1) * (x * Calpha * hbF χ z ^ 2 * primeProdBelow z ^ 2 * Singz))
    (hsing : Singz = (1 + e2) * Sing)
    (he1 : |e1| ≤ a1) (he2 : |e2| ≤ a2)
    (hsmall : 4 * Delta + 8 * EP + 2 * a2 ≤ 1) :
    ∃ δ : ℝ, kS1 = (1 + δ) * (x * Sing * Calpha / (η * L) ^ 2)
      ∧ |δ| ≤ 4 * Delta + 8 * EP + 2 * a1 + 2 * a2 := by
  have hΔ0 : 0 ≤ Delta := le_trans (abs_nonneg _) hF
  have hEP0 : 0 ≤ EP := le_trans (abs_nonneg _) hP
  have ha10 : 0 ≤ a1 := le_trans (abs_nonneg _) he1
  have ha20 : 0 ≤ a2 := le_trans (abs_nonneg _) he2
  -- the two exponentiations
  obtain ⟨ε₀, hFsq, hε₀⟩ := sq_eq_exp_mul_one_add (hbF_pos χ z) hF (by linarith)
  have hPform : |Real.log (primeProdBelow z)
      - (-(Real.log (Real.log z)) - Real.eulerMascheroniConstant)| ≤ EP := by
    rw [show Real.log (primeProdBelow z)
        - (-(Real.log (Real.log z)) - Real.eulerMascheroniConstant)
      = Real.log (primeProdBelow z) + Real.log (Real.log z)
        + Real.eulerMascheroniConstant by ring]
    exact hP
  obtain ⟨ε₃, hPsq, hε₃⟩ :=
    sq_eq_exp_mul_one_add (primeProdBelow_pos (z := z)) hPform (by linarith)
  -- the two exponentials multiply to `(ηL)^{−2}`
  have hexp : Real.exp (2 * (Real.log (Real.log z) - Real.log (η * L)
        + Real.eulerMascheroniConstant))
      * Real.exp (2 * (-(Real.log (Real.log z)) - Real.eulerMascheroniConstant))
      = ((η * L) ^ 2)⁻¹ := by
    rw [← Real.exp_add,
      show 2 * (Real.log (Real.log z) - Real.log (η * L) + Real.eulerMascheroniConstant)
          + 2 * (-(Real.log (Real.log z)) - Real.eulerMascheroniConstant)
        = -(2 * Real.log (η * L)) by ring, Real.exp_neg, exp_two_mul_log hηL]
  -- the multiplicative bookkeeping
  set u1 : ℝ := (1 + ε₀) * (1 + ε₃) - 1 with hu1
  set u2 : ℝ := (1 + u1) * (1 + e2) - 1 with hu2
  set u3 : ℝ := (1 + u2) * (1 + e1) - 1 with hu3
  have hb1 : |u1| ≤ |ε₀| + 2 * |ε₃| := by
    rw [hu1]; exact abs_one_add_mul_sub_one_le (by linarith)
  have hb1' : |u1| ≤ 4 * Delta + 8 * EP := by linarith
  have hb2 : |u2| ≤ |u1| + 2 * |e2| := by
    rw [hu2]; exact abs_one_add_mul_sub_one_le (by linarith)
  have hb2' : |u2| ≤ 4 * Delta + 8 * EP + 2 * a2 := by linarith
  have hb3 : |u3| ≤ |u2| + 2 * |e1| := by
    rw [hu3]; exact abs_one_add_mul_sub_one_le (by linarith)
  have hb3' : |u3| ≤ 4 * Delta + 8 * EP + 2 * a1 + 2 * a2 := by linarith
  refine ⟨u3, ?_, hb3'⟩
  have hfactor : (1 : ℝ) + u3 = (1 + e1) * ((1 + e2) * ((1 + ε₀) * (1 + ε₃))) := by
    rw [hu3, hu2, hu1]; ring
  rw [hrear, hsing, hFsq, hPsq, hfactor, div_eq_mul_inv, ← hexp]
  ring

/-! ## §5 — `(L2)` at the split point: W3 fired inside -/

/-- **`(L2)` AT THE MULTIPLICATIVE MANDATE** — the closing statement of HB Lemma 7's `κS₁`
half, with W3's `log F` computation fired inside, so that every binder of the block is visible
in one place.

    κ·S₁  =  (1 + δ) · x · 𝔖 · C(α) / (ηL)²,

    |δ| ≤ 4·(Ecorr + Eseg + Etail + 500(1 + 2 log ηL)/η) + 8·E_P + 2·a₁ + 2·a₂.

`𝔖` is the corpus's own Hardy–Littlewood constant, `S₁` HB's product (`hbS1`), and the two
sieve-side rows `hrear` (`(4.4)`) and `hsing` (`(4.5)`) ride as **named binders with explicit
bounds** — the `W4.5` residue, whose discharge needs `κ`, `G(p)` and `C(α)` as definitions.

`hm1` is design v3 **D11**; `hα` is HB's "assuming `z > α`" (consumed by `hrear`'s provider);
`hwin` is the window's **upper** edge, spent inside W3. -/
theorem hb_L2_at_split_point {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {α : ℕ} {β₀ L η z x X Calpha Singz kappa Ecorr Eseg Etail EP a1 a2 e1 e2 : ℝ}
    {Stail : ℂ}
    (hβ₀1 : β₀ < 1) (hL : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hz : 3 ≤ z) (hα : (α : ℝ) < z)
    (hX : 3 ≤ X) (hwin : Real.log X ≤ 500 * L) (hηlarge : 500 ≤ η)
    (hm1 : zeroMult χ (β₀ : ℂ) = 1)
    (htail : ‖Stail + ((zeroMult χ (β₀ : ℂ) : ℕ) : ℂ)
        * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖ ≤ Etail)
    (hseg : |(logChiSum χ z X).re
        - (Real.log (Real.log z) - Real.log (Real.log X))| ≤ Eseg)
    (hcorr : |Real.log (hbF χ z) - ((logChiSum χ z X).re + Stail.re)| ≤ Ecorr)
    (hP : |Real.log (primeProdBelow z) + Real.log (Real.log z)
        + Real.eulerMascheroniConstant| ≤ EP)
    (hrear : kappa * hbS1 χ α z
      = (1 + e1) * (x * Calpha * hbF χ z ^ 2 * primeProdBelow z ^ 2 * Singz))
    (hsing : Singz = (1 + e2) * Salt.HardyLittlewood.twinSingularSeries)
    (he1 : |e1| ≤ a1) (he2 : |e2| ≤ a2)
    (hsmall : 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
        + 8 * EP + 2 * a2 ≤ 1) :
    ∃ δ : ℝ,
      kappa * hbS1 χ α z
        = (1 + δ) * (x * Salt.HardyLittlewood.twinSingularSeries * Calpha / (η * L) ^ 2)
      ∧ |δ| ≤ 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
          + 8 * EP + 2 * a1 + 2 * a2 := by
  have _hα := hα
  have _hz := hz
  -- `ηL = (1−β₀)^{−1} > 0`
  have hηL : 0 < η * L := by
    rw [hη]
    have : 0 < 1 - β₀ := by linarith
    rw [div_mul_eq_mul_div, one_mul, div_eq_mul_inv]
    positivity
  -- W3's deliverable, instantiated at `logF := log F`
  have hF := hb_logF_at_split_point χ (β₀ := β₀) (L := L) (η := η) (z := z) (X := X)
    (logF := Real.log (hbF χ z)) hβ₀1 hL hη hX hwin hηlarge hm1 htail hseg hcorr
  exact hb_L2_core χ hηL hF hP hrear hsing he1 he2 hsmall

end Salt.HB
