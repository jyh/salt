/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ChiLLower
import Salt.SW.SiegelFinal

/-!
# ROUTE A, the Siegel arm — the real-character exceptional gap (`SiegelArm`)

`ChiLLower.lean` closes ROUTE A unconditionally for every character, but with a floor whose
H2 (bounded-band) branch is only a CONSTANT at a REAL nonprincipal `χ`
(`chi_floor_all_unconditional`), while `χ² ≠ 1` gets the growing
`(1/4)loglog X − O(log q)` (`chi_floor_all_nonreal`) and `χ₀` gets `loglog X − O(1)`
(`chi_floor_all_principal`).  This file closes that last gap.

## The S-1 verdict (the landed Siegel arc, read end to end)

The question was whether the SW rung's Siegel family supplies the `L(1,χ)` lower bound that a
real-χ region transport needs.  It does NOT, and the reason is structural:

* `Salt.SW.siegel_theorem` (`SiegelClose.lean:841`) is UNCONDITIONAL and ε-quantified, but it
  is the ZERO-FREE form `β ≤ 1 − C/q^ε`; it says nothing about `‖L(s,χ)‖` anywhere.
* `Salt.SW.siegel_L_one_exceptional` (`SiegelFinal.lean:324`) and its sharpened sibling
  `Salt.SW.siegel_L_one_lower_near` (`SiegelClose.lean:582`) ARE `L(1,χ)`-lower bounds, but
  both carry the *fixed exceptional data* `(q₁, χ₁, β₁)` as hypotheses and require the target
  `χ` to be DISTINCT from `χ₁` — they live strictly inside the exceptional branch of
  `Salt.SW.siegel_dichotomy`.
* `Salt.SW.L1_lower_siegel` (`DHCore.lean:808`) is effective, but it needs a real zero `β₀` of
  `L(·,χ)` ITSELF together with the deep-regime guard `N^{1−β₀} ≤ e` — it bites only when `χ`
  already has a Siegel zero.

So the composition FAILS in the no-exceptional-zero branch: there the corpus has no `L(1,χ)`
lower bound at all.  An unconditional uniform-in-`q` `L(1,χ) ≫_ε q^{−ε}` is a genuine port
(Landau's hyperbola argument, or the class-number bound `L(1,χ) ≫ q^{−1/2}`), in neither
mathlib nor Salt.  **That port is NOT what the growing floor needs, however** — see below.

## What the growing floor actually needs (and what is landed here)

The consumer is `chi_floor_all_of_Llower` (`ChiFloorLow.lean:262`): a lower bound
`−B ≤ log‖L(1 + 1/log X − it, χ)‖` on the bounded band, with `B` allowed to be ANY expression.
The floor it returns is `loglog X − B − CH2`, so the floor GROWS as soon as `B` is
`X`-INDEPENDENT.  And an `X`-independent `B` is available for EVERY nonprincipal character,
real or not, with no Siegel input whatsoever:

`L(·,χ)` is entire for `χ ≠ 1` and NONVANISHING on the closed half-plane `Re s ≥ 1`
(mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re` at the `χ ≠ 1` branch — the
Dirichlet-grade nonvanishing, which already contains the hard real-character case at `s = 1`).
The bridge points `1 + 1/log X − it` with `X ≥ e`, `|t| ≤ 1` all lie in the COMPACT box
`[1,2] × [−1,1]`, so `‖L(·,χ)‖` attains a positive minimum there.  That minimum is the whole
`B`.  The `χ₀` case is the same statement with the ζ-pole patch supplying the minimum
(`Salt.MR.zeta_lower_small_t`), and there the constant is EXPLICIT: `δ/q`.

The price is exactly the Siegel price, and it is confined to ONE binder: the compact minimum
is produced by the extreme-value theorem, so `B` is a per-character existential with no
control in `q`.  Uniformity in `q` — which the door's `M(g;X,W) = inf_{q ≤ W, χ, t}` shape
wants at `W = (loglog x)⁵` — is precisely what the ineffective Siegel constant buys and what
this file does not claim.  Stated as a scope line: this file makes the floor GROW for every
fixed character; making the growth uniform over `q ≤ W` still needs the `L(1,χ) ≫_ε q^{−ε}`
port plus an explicit region transport.

## Contents

* `LFunction_band_lower` (S-2a) — the compact-min bound for `χ ≠ 1`: a positive `m` with
  `m ≤ ‖L((1+d) − it, χ)‖` on `d ∈ [0,1]`, `|t| ≤ 1`.
* `LFunction_band_lower_principal` (S-2b) — the same for `χ₀`, EXPLICIT: `δ/q`, from
  `zeta_lower_small_t` and the Euler-factor bound `∏_{p|q}‖1 − p^{−s}‖ ≥ 1/q`.
* `chi_Llower_band` (S-2) — the two joined in the exact hypothesis shape of
  `chi_floor_all_of_Llower`: `∃ B, ∀ X ≥ e, ∀ |t| ≤ 1, −B ≤ log‖L(1 + 1/log X − it, χ)‖`,
  with `B` independent of `X` and `t`.
* `chi_floor_all_complete` / `chi_floor_all_complete_twisted` (S-3) — the unified floor: for
  EVERY `q`, EVERY `χ` (principal, real nonprincipal, non-real alike) and EVERY `t`, the
  bounded-band branch is `loglog X − B_χ − CH2` with `B_χ` independent of `X`.  This is the
  first statement in the campaign whose χ-quality floor TENDS TO INFINITY at a real
  nonprincipal character.

Section 6 then supplies the UNIFORM arm — the same floor with the constant EXPLICIT in `q`,
conditional on the one input the SW arc does not deliver (a lower bound for `(L(1,χ)).re`):

* `zeta_upper_band` — the absolute `Z ≥ 1` with `‖ζ((1+d)+iτ)‖ ≤ Z/|τ|` on the band box (the
  compact-max companion of `zeta_lower_small_t`).
* `LFunctionTrivChar_norm_le` — `‖L(s,χ₀)‖ ≤ q‖ζ(s)‖`; `norm_deriv_LFunction_ball_le` — the
  Cauchy bound `‖L'‖ ≤ 8·diskConst q` on the excursion ball `‖z−2‖ ≤ 9/8`.
* `LFunction_lower_of_L1` — the mean-value excursion from `s = 1`.
* `chi_Llower_real_far` — 3-4-1 at a REAL `χ` with the ζ-pole factor priced by the DISTANCE
  `2|t|` instead of by `1 + log X`; this is the single step `chi_Llower_341` could not take.
* `chi_Llower_real_of_L1` (S-2 uniform) / `chi_floor_real_of_L1` (S-3 uniform) — the two
  branches joined at `δ = L₁/(32·diskConst q)`, and the resulting floor
  `(1/4)loglog X − O(log q) − O(log(1/L₁))`, byte-matching `chi_floor_all_nonreal`'s shape.
* `exists_L1_lower` — the `L₁` slot is INHABITED at every real nonprincipal `χ`
  (`Salt.SW.LFunction_apply_one_pos`), ineffectively; Siegel is exactly what makes the
  inhabitant uniform in `q`.
-/

namespace Salt.MR

open Complex DirichletCharacter Salt.SW

/-! ## 1. The bounded-band box -/

/-- The compact box `[1,2] × [−1,1]` that contains every bridge point `1 + 1/log X − it`
(`X ≥ e`, `|t| ≤ 1`). -/
private def bandBox : Set ℂ := {z : ℂ | (1 ≤ z.re ∧ z.re ≤ 2) ∧ |z.im| ≤ 1}

private lemma bandBox_isCompact : IsCompact bandBox := by
  have heq : bandBox = ({z : ℂ | 1 ≤ z.re} ∩ {z : ℂ | z.re ≤ 2}) ∩ {z : ℂ | |z.im| ≤ 1} := by
    ext z
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have hclosed : IsClosed bandBox := by
    rw [heq]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_le Complex.continuous_im.abs continuous_const)
  have hsub : bandBox ⊆ Metric.closedBall (0 : ℂ) 3 := by
    intro z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ 2 := by rw [abs_of_pos (by linarith : (0 : ℝ) < z.re)]; exact h2
    linarith
  exact (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset hclosed hsub

private lemma bandBox_nonempty : bandBox.Nonempty := by
  refine ⟨(1 : ℂ), ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [Complex.one_re]
  · rw [Complex.one_re]; norm_num
  · rw [Complex.one_im, abs_zero]; norm_num

private lemma bandBox_re {d t : ℝ} :
    (((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I).re = 1 + d := by simp

private lemma bandBox_im {d t : ℝ} :
    (((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I).im = -t := by simp

private lemma bandBox_mem {d t : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht : |t| ≤ 1) :
    ((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I ∈ bandBox := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [bandBox_re]; linarith
  · rw [bandBox_re]; linarith
  · rw [bandBox_im, abs_neg]; exact ht

private lemma bandBox_mem_add {d τ : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hτ : |τ| ≤ 1) :
    ((1 + d : ℝ) : ℂ) + (τ : ℝ) * Complex.I ∈ bandBox := by
  have hre : (((1 + d : ℝ) : ℂ) + (τ : ℝ) * Complex.I).re = 1 + d := by simp
  have him : (((1 + d : ℝ) : ℂ) + (τ : ℝ) * Complex.I).im = τ := by simp
  exact ⟨⟨by rw [hre]; linarith, by rw [hre]; linarith⟩, by rw [him]; exact hτ⟩

/-! ## 2. S-2a — the compact minimum at a nonprincipal character -/

/-- **S-2a — the bounded-band `L`-lower bound for every NONPRINCIPAL character.**  For `χ ≠ 1`
there is `m > 0` with `m ≤ ‖L((1+d) − it, χ)‖` for all `d ∈ [0,1]` and `|t| ≤ 1`.

No Siegel input, no zero-free region: `L(·,χ)` is entire (`differentiable_LFunction`) and
nonvanishing on `Re s ≥ 1` (`LFunction_ne_zero_of_one_le_re` at the `χ ≠ 1` branch — the
statement that already contains the hard real-character case at `s = 1`), so the extreme-value
theorem on the compact box `[1,2] × [−1,1]` furnishes the minimum.  `m` is NOT effective in
`q`: that, and only that, is where Siegel's ineffective constant would enter. -/
theorem LFunction_band_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ d t : ℝ, 0 ≤ d → d ≤ 1 → |t| ≤ 1 →
      m ≤ ‖LFunction χ (((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  have hcont : ContinuousOn (fun z => ‖LFunction χ z‖) bandBox :=
    ((differentiable_LFunction hχ1).continuous.norm).continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := bandBox_isCompact.exists_isMinOn bandBox_nonempty hcont
  refine ⟨‖LFunction χ z₀‖,
    norm_pos_iff.mpr (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hz₀.1.1), ?_⟩
  intro d t hd0 hd1 ht
  exact isMinOn_iff.mp hmin _ (bandBox_mem hd0 hd1 ht)

/-! ## 3. S-2b — the principal character, with an EXPLICIT constant -/

/-- The Euler-factor product of `L(·,χ₀)` is bounded BELOW by `1/q` on `Re s ≥ 1`.  Each factor
obeys `‖1 − p^{−s}‖ ≥ 1 − p^{−Re s} ≥ 1 − 1/p ≥ 1/p` (`p ≥ 2`), and
`∏_{p|q} 1/p = 1/∏_{p|q} p ≥ 1/q`. -/
lemma eulerFactor_prod_lower (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 ≤ s.re) :
    1 / (q : ℝ) ≤ ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  rw [norm_prod]
  have hstep : ∀ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hcp : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / (p : ℝ) := by
      rw [norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
      have h1 : ((p : ℝ)) ^ (-s.re) ≤ ((p : ℝ)) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have h2 : ((p : ℝ)) ^ (-1 : ℝ) = 1 / (p : ℝ) := by
        rw [Real.rpow_neg_one, one_div]
      linarith [h1, h2.le, h2.symm.le]
    have hlow : (1 : ℝ) - ‖(p : ℂ) ^ (-s)‖ ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
      rwa [norm_one] at h
    have hhalf : (1 : ℝ) / (p : ℝ) ≤ 1 - 1 / (p : ℝ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ))]
      have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      nlinarith
    linarith
  have hnn : ∀ p ∈ q.primeFactors, (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    positivity
  have hcmp : ∏ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ)
      ≤ ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ :=
    Finset.prod_le_prod hnn hstep
  have hprodpos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have hpos : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast hpos
  have heq : ∏ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ)
      = 1 / ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    simp [one_div, Finset.prod_inv_distrib]
  have hle : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  have hfin : 1 / (q : ℝ) ≤ ∏ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ) := by
    rw [heq]
    exact one_div_le_one_div_of_le hprodpos hle
  linarith

/-- **S-2b — the bounded-band `L`-lower bound at the PRINCIPAL character, EXPLICIT.**  For
`d ∈ (0,1]` and `|t| ≤ 1`, `δ/q ≤ ‖L((1+d) − it, χ₀)‖` with `δ` the absolute constant of
`Salt.MR.zeta_lower_small_t`.  The pole of `ζ` only helps: `L(s,χ₀) = ∏_{p|q}(1−p^{−s})·ζ(s)`,
the ζ-factor is bounded below by `δ` on the whole box (`zeta_lower_small_t`, height `≤ 3`), and
the Euler product costs at most `q` (`eulerFactor_prod_lower`).  Unlike S-2a this constant is
uniform in `q` up to the explicit `1/q`. -/
theorem LFunction_band_lower_principal (q : ℕ) [NeZero q] :
    ∃ m : ℝ, 0 < m ∧ ∀ d t : ℝ, 0 < d → d ≤ 1 → |t| ≤ 1 →
      m / (q : ℝ) ≤ ‖LFunction (1 : DirichletCharacter ℂ q)
        (((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨δ, hδ, hsmall⟩ := zeta_lower_small_t
  refine ⟨δ, hδ, ?_⟩
  intro d t hd0 hd1 ht
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  set s : ℂ := ((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1 + d := by rw [hsdef]; exact bandBox_re
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hsre
    linarith
  have hz : δ ≤ ‖riemannZeta s‖ := by
    have h := hsmall d (-t) hd0.le hd1 (by rw [abs_neg]; linarith) (fun hc => absurd hc.1 hd0.ne')
    have hpt : ((1 + d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = s := by
      rw [hsdef]; push_cast; ring
    rwa [hpt] at h
  have hprod : 1 / (q : ℝ) ≤ ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ :=
    eulerFactor_prod_lower q (by rw [hsre]; linarith)
  have hfac : LFunction (1 : DirichletCharacter ℂ q) s
      = (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
    LFunctionTrivChar_eq_mul_riemannZeta hs1
  rw [hfac, norm_mul]
  have hmul : (1 / (q : ℝ)) * δ
      ≤ ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖ :=
    mul_le_mul hprod hz hδ.le (norm_nonneg _)
  have hdiv : δ / (q : ℝ) = (1 / (q : ℝ)) * δ := by field_simp
  linarith [hdiv.le, hdiv.symm.le, hmul]

/-! ## 4. S-2 — the joined band bound, in the consumer's hypothesis shape -/

/-- **S-2 — the bounded-band `L`-lower bound for EVERY character, `X`-INDEPENDENT.**  For every
`q ≠ 0` and every `χ mod q` there is a constant `B` — depending on `q` and `χ` only — with

  `−B ≤ log‖L(1 + 1/log X − it, χ)‖`   for every `X ≥ e` and every `|t| ≤ 1`.

This is EXACTLY the hypothesis shape of `chi_floor_all_of_Llower` (`ChiFloorLow.lean:262`),
with a `B` that does not grow with `X` — which is what turns the H2 floor `loglog X − B − CH2`
from a constant into an unbounded function of `X`.  Nonprincipal: `LFunction_band_lower`
(`B = −log m`, ineffective in `q`).  Principal: `LFunction_band_lower_principal`
(`B = log q − log δ`, explicit). -/
theorem chi_Llower_band {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ B : ℝ, ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 →
      -B ≤ Real.log ‖DirichletCharacter.LFunction χ
            (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  have hband : ∃ m : ℝ, 0 < m ∧ ∀ d t : ℝ, 0 < d → d ≤ 1 → |t| ≤ 1 →
      m ≤ ‖LFunction χ (((1 + d : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
    by_cases hχ1 : χ = 1
    · obtain ⟨m, hm, hbnd⟩ := LFunction_band_lower_principal q
      have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      refine ⟨m / (q : ℝ), by positivity, ?_⟩
      intro d t hd0 hd1 ht
      rw [hχ1]
      exact hbnd d t hd0 hd1 ht
    · obtain ⟨m, hm, hbnd⟩ := LFunction_band_lower χ hχ1
      exact ⟨m, hm, fun d t hd0 hd1 ht => hbnd d t hd0.le hd1 ht⟩
  obtain ⟨m, hm, hbnd⟩ := hband
  refine ⟨-Real.log m, ?_⟩
  intro X t hX ht
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  rw [neg_neg]
  exact Real.log_le_log hm (hbnd (1 / Real.log X) t hd0 hd1 ht)

/-! ## 5. S-3 — the unified ROUTE-A floor -/

/-- **S-3 — THE UNIFIED ROUTE-A χ-QUALITY FLOOR, GROWING AT EVERY CHARACTER.**  There are
constants `CH1`, `CH2` (uniform in everything) such that for every `q ≠ 0` and every `χ mod q`
there is a constant `B` — independent of `X` and `t` — with: for every `X ≥ e` and EVERY real
`t`,

  `min( loglog X − B − CH2,`
  `     [loglog X − (3/4)loglog(|kt|+3) − 5·logloglog(|kt|+16) − CH1 − ∑_{p|q,p≤X}1/p]/k² )`
  `  ≤ 𝔻(λ·χ̄, n^{it}; X)²`     (`k = 2·orderOf χ`).

Both branches now TEND TO INFINITY with `X`, at every character: principal, real
nonprincipal, and non-real alike.  This closes the gap left by
`chi_floor_all_unconditional` (whose bounded-band branch was a constant) and strictly
improves `chi_floor_all_nonreal` (whose branch grew like `(1/4)loglog X`) at fixed `χ`.

The Siegel obstruction has NOT been dissolved — it has been confined to one binder: `B` is
supplied by the extreme-value theorem at a nonprincipal `χ` (`LFunction_band_lower`), so it
carries no control in `q`.  A floor uniform over `q ≤ W` with `W → ∞` still needs the
ineffective `L(1,χ) ≫_ε q^{−ε}` together with an explicit region transport; see this file's
S-1 verdict. -/
theorem chi_floor_all_complete :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), ∃ B : ℝ,
      ∀ (X t : ℝ), Real.exp 1 ≤ X →
        min (Real.log (Real.log X) - B - CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_of_Llower
  refine ⟨CH1, CH2, ?_⟩
  intro q _ χ
  obtain ⟨B, hB⟩ := chi_Llower_band χ
  refine ⟨B, ?_⟩
  intro X t hX
  refine hC q χ X t B hX (fun hkt => hB X t hX ?_)
  have hord : 0 < orderOf χ := MulChar.orderOf_pos χ
  have hk2 : (2 : ℝ) ≤ ((2 * orderOf χ : ℕ) : ℝ) := by
    have h2 : 2 ≤ 2 * orderOf χ := by omega
    exact_mod_cast h2
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((2 * orderOf χ : ℕ) : ℝ))] at hkt
  nlinarith [abs_nonneg t]

/-- **S-3 (MRT shape) — the unified growing floor on `𝔻(λ, χ·n^{it}; X)²`**, the object the
quality infimum `M(λ; X, W)` ranges over.  One rewrite through `pretDistSq_lam_chi_twist`. -/
theorem chi_floor_all_complete_twisted :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), ∃ B : ℝ,
      ∀ (X t : ℝ), Real.exp 1 ≤ X →
        min (Real.log (Real.log X) - B - CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq lam (fun n => χ (n : ZMod q) * costwist t n) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_complete
  refine ⟨CH1, CH2, ?_⟩
  intro q _ χ
  obtain ⟨B, hB⟩ := hC q χ
  refine ⟨B, ?_⟩
  intro X t hX
  rw [pretDistSq_lam_chi_twist χ t X]
  exact hB X t hX

/-! ## 6. The UNIFORM arm — the region transport from a named `L(1,χ)` lower bound

Sections 2–5 make the floor grow at every FIXED character; the door's
`M(g;X,W) = inf_{q ≤ W, χ, t}` wants growth uniform over `q ≤ W`, and for that the constant
must be explicit in `q`.  This section supplies the transport that does it, taking the
`L(1,χ)` lower bound as a NAMED hypothesis — the classical Siegel statement, which per this
file's S-1 verdict is exactly the piece the landed SW arc does not deliver unconditionally.
The transport itself is unconditional and fully explicit.

Geometry (the reason there are two branches): at a REAL `χ` the 3-4-1 device puts the
PRINCIPAL character at height `2t`, so its ζ-pole is at `t = 0` — the device degrades exactly
at the centre of the band, and the `L(1,χ)` bound is what covers the centre.
* `|t|` LARGE (`> δ`): 3-4-1, with the pole factor bounded `X`-independently by
  `q·Z/(2|t|)` (`zeta_upper_band` + `LFunctionTrivChar_norm_le`) instead of by the trivial
  `1 + log X` — this is the ONLY change from `chi_Llower_341`, and it is what keeps the
  `loglog X` coefficient at `3/4` rather than `1`.
* `|t|` SMALL (`≤ δ`): the Cauchy/mean-value excursion from `s = 1`, with
  `δ = L₁/(32·diskConst q)` and the matching gate `32·diskConst q/L₁ ≤ log X` (which is what
  puts the bridge point `1 + 1/log X − it` inside the excursion radius).
-/

/-- **The ζ-upper companion of `zeta_lower_small_t`.**  There is an ABSOLUTE constant `Z ≥ 1`
with `‖ζ((1+d) + iτ)‖ ≤ Z/|τ|` for every `d ∈ [0,1]` and `0 < |τ| ≤ 1`: the entire
`Zc = (s−1)ζ` has a compact maximum on the band box, and `‖s − 1‖ ≥ |τ|`.  `Z` is independent
of `q` and of `X` — the whole point, since it is the pole factor's price in the real-χ
3-4-1. -/
theorem zeta_upper_band :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ d τ : ℝ, 0 ≤ d → d ≤ 1 → |τ| ≤ 1 → 0 < |τ| →
      ‖riemannZeta (((1 + d : ℝ) : ℂ) + (τ : ℝ) * Complex.I)‖ ≤ Z / |τ| := by
  have hcont : ContinuousOn (fun z => ‖Zc z‖) bandBox :=
    (Zc_differentiable.continuous.norm).continuousOn
  obtain ⟨z₀, -, hmax⟩ := bandBox_isCompact.exists_isMaxOn bandBox_nonempty hcont
  refine ⟨max ‖Zc z₀‖ 1, le_max_right _ _, ?_⟩
  intro d τ hd0 hd1 hτ1 hτ0
  set s : ℂ := ((1 + d : ℝ) : ℂ) + (τ : ℝ) * Complex.I with hsdef
  have hsim : s.im = τ := by rw [hsdef]; simp
  have hs1 : s ≠ 1 := by
    intro h
    have hτz : τ = 0 := by rw [← hsim, h, Complex.one_im]
    rw [hτz, abs_zero] at hτ0
    exact lt_irrefl 0 hτ0
  have hmem : s ∈ bandBox := bandBox_mem_add hd0 hd1 hτ1
  have hle : ‖Zc s‖ ≤ ‖Zc z₀‖ := isMaxOn_iff.mp hmax s hmem
  have heq : ‖Zc s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by rw [Zc_eq_of_ne hs1, norm_mul]
  have him : |τ| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, hsim, Complex.one_im, sub_zero] at h
    exact h
  rw [le_div_iff₀ hτ0]
  have hstep : ‖riemannZeta s‖ * |τ| ≤ ‖riemannZeta s‖ * ‖s - 1‖ :=
    mul_le_mul_of_nonneg_left him (norm_nonneg _)
  have hZ : ‖Zc s‖ ≤ max ‖Zc z₀‖ 1 := le_trans hle (le_max_left _ _)
  nlinarith [hstep, hZ, heq.symm.le, heq.le]

/-- **The principal-character upper bound in terms of ζ.**  For `Re s ≥ 0` and `s ≠ 1`,
`‖L(s,χ₀)‖ ≤ q·‖ζ(s)‖`: the Euler correction `∏_{p|q}(1 − p^{−s})` has every factor of norm
`≤ 2 ≤ p`, and `∏_{p|q} p ≤ q`. -/
lemma LFunctionTrivChar_norm_le (q : ℕ) [NeZero q] {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s ≠ 1) :
    ‖LFunction (1 : DirichletCharacter ℂ q) s‖ ≤ (q : ℝ) * ‖riemannZeta s‖ := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hfac : LFunction (1 : DirichletCharacter ℂ q) s
      = (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
    LFunctionTrivChar_eq_mul_riemannZeta hs1
  rw [hfac, norm_mul]
  have hprod : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ (q : ℝ) := by
    rw [norm_prod]
    have hstep : ∀ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hcp : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [norm_natCast_cpow_of_pos hpp.pos]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpp.one_le)
          (by rw [Complex.neg_re]; linarith)
      calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [norm_one]; linarith
        _ ≤ (p : ℝ) := by linarith
    calc ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖
        ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hstep
      _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (q : ℝ) := by exact_mod_cast Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)

/-- **The Cauchy derivative bound on the excursion ball.**  For `ψ ≠ 1` mod `N` and any `z`
with `‖z − 2‖ ≤ 9/8`, `‖L'(z,ψ)‖ ≤ 8·diskConst N`.  The radius-`1/8` sphere about `z` stays
inside `ball 2 (3/2)` (`1/8 + 9/8 = 5/4 < 3/2`), where `Salt.SW.norm_LFunction_ball_le`
applies.  This is `Salt.SW.norm_deriv_LFunction_imprim_le` with the real point `σ ∈ [7/8,1]`
replaced by an arbitrary point of the excursion ball — the same radius, the same constant. -/
lemma norm_deriv_LFunction_ball_le {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ1 : ψ ≠ 1) {z : ℂ} (hz : ‖z - 2‖ ≤ 9 / 8) :
    ‖deriv (LFunction ψ) z‖ ≤ 8 * diskConst N := by
  have hsphere : ∀ w ∈ Metric.sphere z (1 / 8), ‖LFunction ψ w‖ ≤ diskConst N := by
    intro w hw
    rw [Metric.mem_sphere, Complex.dist_eq] at hw
    have hwball : w ∈ Metric.ball (2 : ℂ) (3 / 2) := by
      rw [Metric.mem_ball, Complex.dist_eq]
      calc ‖w - 2‖ = ‖(w - z) + (z - 2)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - 2‖ := norm_add_le _ _
        _ ≤ 1 / 8 + 9 / 8 := by rw [hw]; linarith
        _ < 3 / 2 := by norm_num
    exact norm_LFunction_ball_le ψ hψ1 hwball
  have hdcc : DiffContOnCl ℂ (LFunction ψ) (Metric.ball z (1 / 8)) :=
    (differentiable_LFunction hψ1).diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 8) hdcc hsphere
  calc ‖deriv (LFunction ψ) z‖ ≤ diskConst N / (1 / 8) := hcauchy
    _ = 8 * diskConst N := by ring

/-- **The excursion from `s = 1` (the small-`|t|` transport).**  If `L₁ ≤ (L(1,χ)).re` and the
point `s` lies in the excursion ball `‖s − 2‖ ≤ 9/8` at distance
`‖s − 1‖ ≤ L₁/(2·8·diskConst q)` from `1`, then `L₁/2 ≤ ‖L(s,χ)‖`.  Mean value on the convex
ball with the Cauchy bound `norm_deriv_LFunction_ball_le`, against
`‖L(1,χ)‖ ≥ (L(1,χ)).re ≥ L₁`. -/
lemma LFunction_lower_of_L1 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    {L₁ : ℝ} (hL1 : L₁ ≤ (LFunction χ 1).re) {s : ℂ} (hs2 : ‖s - 2‖ ≤ 9 / 8)
    (hclose : (8 * diskConst q) * ‖s - 1‖ ≤ L₁ / 2) :
    L₁ / 2 ≤ ‖LFunction χ s‖ := by
  have hconv : Convex ℝ (Metric.closedBall (2 : ℂ) (9 / 8)) := convex_closedBall _ _
  have hmem1 : (1 : ℂ) ∈ Metric.closedBall (2 : ℂ) (9 / 8) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, show (1 : ℂ) - 2 = -1 by ring, norm_neg, norm_one]
    norm_num
  have hmems : s ∈ Metric.closedBall (2 : ℂ) (9 / 8) := by
    rw [Metric.mem_closedBall, Complex.dist_eq]; exact hs2
  have hbound : ∀ z ∈ Metric.closedBall (2 : ℂ) (9 / 8),
      ‖fderiv ℂ (LFunction χ) z‖ ≤ 8 * diskConst q := by
    intro z hz
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    rw [← norm_deriv_eq_norm_fderiv]
    exact norm_deriv_LFunction_ball_le χ hχ1 hz
  have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (differentiable_LFunction hχ1) z) hbound hmem1 hmems
  have hre : L₁ ≤ ‖LFunction χ 1‖ := le_trans hL1 (Complex.re_le_norm _)
  have htri : ‖LFunction χ 1‖ - ‖LFunction χ s‖ ≤ ‖LFunction χ s - LFunction χ 1‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  linarith

/-- **The far branch — 3-4-1 with the pole factor priced by DISTANCE, not by `log X`.**  For a
REAL character (`χ² = 1`), `X ≥ e`, `0 < |t| ≤ 1/2`,

  `−[2log4 + (3/4)log(1+log X) + (1/4)log(q·Z/(2|t|))] ≤ log‖L(1 + 1/log X − it, χ)‖`.

Identical to `chi_Llower_341` except at ONE step: there the factor `L(v+2it,χ²)` was bounded
by Pólya–Vinogradov (legal only for `χ² ≠ 1`); here `χ² = χ₀` carries the ζ-pole, and it is
bounded instead by `q·‖ζ‖ ≤ q·Z/(2|t|)` — `X`-independent, and finite precisely because
`t ≠ 0`.  The `loglog X` coefficient therefore stays at `3/4`, so the floor this buys still
grows like `(1/4)loglog X`. -/
theorem chi_Llower_real_far :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 / 2 → 0 < |t| →
        -(2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
            + (1 / 4) * Real.log ((q : ℝ) * Z / (2 * |t|)))
          ≤ Real.log ‖DirichletCharacter.LFunction χ
              (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨Z, hZ1, hZ⟩ := zeta_upper_band
  refine ⟨Z, hZ1, ?_⟩
  intro q _ χ hsq X t hX ht ht0
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  have hu1 : (1 : ℝ) < 1 + 1 / Real.log X := by linarith
  have hu2 : 1 + 1 / Real.log X ≤ 2 := by linarith
  have hlog4 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have h341 := LFunction_341_horiz χ (u := 1 + 1 / Real.log X) (t := -t) hu1 hu2
  rw [hsq] at h341
  have hpt : ((1 + 1 / Real.log X : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I := by push_cast; ring
  rw [hpt] at h341
  -- the three `Re = 2` anchors
  have a0 : -Real.log 4 ≤ Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((2 : ℝ) : ℂ)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by norm_num))
  have a1 : -Real.log 4
      ≤ Real.log ‖LFunction χ (((2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by simp))
  have a2 : -Real.log 4
      ≤ Real.log ‖LFunction (1 : DirichletCharacter ℂ q)
          (((2 : ℝ) : ℂ) + 2 * ((-t : ℝ) : ℂ) * I)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by simp))
  -- the principal-character cost at `v = u`
  have hb0 : Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((1 + 1 / Real.log X : ℝ) : ℂ)‖
      ≤ Real.log (1 + Real.log X) := by
    have hne1 : (((1 + 1 / Real.log X : ℝ) : ℂ)) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [Complex.ofReal_re, Complex.one_re] at this
      linarith
    have hpos : (0 : ℝ) < ‖LFunction (1 : DirichletCharacter ℂ q)
        (((1 + 1 / Real.log X : ℝ) : ℂ))‖ := by
      rw [norm_pos_iff]
      exact LFunction_ne_zero_of_one_le_re _ (Or.inr hne1) (by simp; linarith)
    refine Real.log_le_log hpos ?_
    have hbnd := LFunction_one_real_upper (q := q) (u := 1 + 1 / Real.log X) hu1
    have heq : (1 : ℝ) + 1 / ((1 + 1 / Real.log X) - 1) = 1 + Real.log X := by
      rw [show (1 + 1 / Real.log X) - 1 = 1 / Real.log X by ring, one_div_one_div]
    linarith [hbnd, heq.symm.le, heq.le]
  -- the pole factor at `v = u`, priced by the DISTANCE `2|t|` (X-independent)
  have hp2 : (((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by push_cast; ring
  have hs2re : (((1 + 1 / Real.log X : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I).re
      = 1 + 1 / Real.log X := by simp
  have hs2ne : (((1 + 1 / Real.log X : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hs2re, Complex.one_re] at this
    linarith
  have habs2 : |(-2 * t)| = 2 * |t| := by
    rw [abs_mul, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0)]; norm_num
  have hb2 : Real.log ‖LFunction (1 : DirichletCharacter ℂ q)
        ((((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I)‖
      ≤ Real.log ((q : ℝ) * Z / (2 * |t|)) := by
    rw [hp2]
    have hzet : ‖riemannZeta (((1 + 1 / Real.log X : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖
        ≤ Z / (2 * |t|) := by
      have h := hZ (1 / Real.log X) (-2 * t) hd0.le hd1 (by rw [habs2]; linarith)
        (by rw [habs2]; linarith)
      rwa [habs2] at h
    have hL2 : ‖LFunction (1 : DirichletCharacter ℂ q)
        (((1 + 1 / Real.log X : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖
        ≤ (q : ℝ) * ‖riemannZeta (((1 + 1 / Real.log X : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖ :=
      LFunctionTrivChar_norm_le q (by rw [hs2re]; linarith) hs2ne
    have hpos : (0 : ℝ) < ‖LFunction (1 : DirichletCharacter ℂ q)
        (((1 + 1 / Real.log X : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖ := by
      rw [norm_pos_iff]
      exact LFunction_ne_zero_of_one_le_re _ (Or.inr hs2ne) (by rw [hs2re]; linarith)
    refine Real.log_le_log hpos ?_
    have hstep : (q : ℝ) * ‖riemannZeta (((1 + 1 / Real.log X : ℝ) : ℂ)
        + ((-2 * t : ℝ) : ℂ) * I)‖ ≤ (q : ℝ) * (Z / (2 * |t|)) :=
      mul_le_mul_of_nonneg_left hzet (by linarith)
    have heq : (q : ℝ) * (Z / (2 * |t|)) = (q : ℝ) * Z / (2 * |t|) := by ring
    linarith [hL2, hstep, heq.le, heq.symm.le]
  linarith [h341, a0, a1, a2, hb0, hb2]

/-- **S-2 (uniform) — the real-χ band bound from a named `L(1,χ)` lower bound.**  Let `χ` be a
real nonprincipal character mod `q`, let `0 < L₁ ≤ 1` be ANY lower bound for `(L(1,χ)).re`,
and let `X` satisfy the gate `32·diskConst q/L₁ ≤ log X`.  Then for every `|t| ≤ 1/2`,

  `−[log 2 − log L₁ + 2log4 + (3/4)log(1+log X) + (1/4)log(16·q·Z·diskConst q/L₁)]`
  `  ≤ log‖L(1 + 1/log X − it, χ)‖`.

Everything on the left is EXPLICIT in `q`, `L₁` and `X` (`Z` is one absolute constant), and
the only `X`-growing term is `(3/4)log(1+log X)`.  The two branches meet at
`δ = L₁/(32·diskConst q)`: below it the excursion from `s = 1` (`LFunction_lower_of_L1`),
above it the pole-distance 3-4-1 (`chi_Llower_real_far`).  Feed this to
`chi_floor_all_of_Llower` and Siegel's `L(1,χ) ≫_ε q^{−ε}` turns it into a floor uniform over
`q ≤ W`; that `L(1,χ)` bound is the ONLY missing input. -/
theorem chi_Llower_real_of_L1 :
    ∃ Z : ℝ, 1 ≤ Z ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t L₁ : ℝ, Real.exp 1 ≤ X → |t| ≤ 1 / 2 → 0 < L₁ → L₁ ≤ 1 →
        L₁ ≤ (DirichletCharacter.LFunction χ 1).re →
        32 * diskConst q / L₁ ≤ Real.log X →
          -(Real.log 2 - Real.log L₁
              + (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
                + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / L₁)))
            ≤ Real.log ‖DirichletCharacter.LFunction χ
                (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  obtain ⟨Z, hZ1, hfar⟩ := chi_Llower_real_far
  refine ⟨Z, hZ1, ?_⟩
  intro q _ χ hχ1 hsq X t L₁ hX ht hL1pos hL1le hL1 hgate
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
  have hD1 : (1 : ℝ) ≤ diskConst q := one_le_diskConst
  have hDpos : (0 : ℝ) < diskConst q := by linarith
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  set δ : ℝ := L₁ / (32 * diskConst q) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδsmall : δ ≤ 1 / 32 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the gate puts `1/log X` below `δ`
  have hdδ : 1 / Real.log X ≤ δ := by
    rw [hδdef, div_le_div_iff₀ hlogXpos (by positivity)]
    rw [div_le_iff₀ hL1pos] at hgate
    nlinarith
  -- the two nonnegative pieces of `B`
  have hNnn : (0 : ℝ) ≤ Real.log 2 - Real.log L₁ := by
    have h1 : Real.log L₁ ≤ 0 := Real.log_nonpos hL1pos.le hL1le
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hqZ : (0 : ℝ) ≤ (q : ℝ) * Z := mul_nonneg (by linarith) (by linarith)
  have hqZD : (1 : ℝ) ≤ (q : ℝ) * Z * diskConst q := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) * Z := by nlinarith
    nlinarith [h1]
  have hbig1 : (1 : ℝ) ≤ 16 * (q : ℝ) * Z * diskConst q / L₁ := by
    rw [le_div_iff₀ hL1pos]
    linarith [hqZD]
  have hFnn : (0 : ℝ) ≤ 2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
      + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / L₁) := by
    have h1 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log (1 + Real.log X) := Real.log_nonneg (by linarith)
    have h3 : (0 : ℝ) ≤ Real.log (16 * (q : ℝ) * Z * diskConst q / L₁) :=
      Real.log_nonneg hbig1
    linarith
  by_cases htsmall : |t| ≤ δ
  · -- the excursion branch
    set s : ℂ := ((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I with hsdef
    have hsre : s.re = 1 + 1 / Real.log X := by rw [hsdef]; exact bandBox_re
    have hsim : s.im = -t := by rw [hsdef]; exact bandBox_im
    have hs1 : ‖s - 1‖ ≤ 1 / Real.log X + |t| := by
      have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
      rw [Complex.sub_re, hsre, Complex.one_re, Complex.sub_im, hsim, Complex.one_im,
        sub_zero, abs_neg] at h
      have habs : |1 + 1 / Real.log X - 1| = 1 / Real.log X := by
        rw [show 1 + 1 / Real.log X - 1 = 1 / Real.log X by ring, abs_of_pos hd0]
      linarith [h, habs.le, habs.symm.le]
    have hs2 : ‖s - 2‖ ≤ 9 / 8 := by
      have h := Complex.norm_le_abs_re_add_abs_im (s - 2)
      have hre2 : (s - 2).re = 1 + 1 / Real.log X - 2 := by rw [Complex.sub_re, hsre]; norm_num
      have him2 : (s - 2).im = -t := by rw [Complex.sub_im, hsim]; norm_num
      rw [hre2, him2, abs_neg] at h
      have habs : |1 + 1 / Real.log X - 2| = 1 - 1 / Real.log X := by
        rw [abs_of_nonpos (by linarith [hd0, hdδ, hδsmall])]; ring
      rw [habs] at h
      linarith [hdδ, hδsmall, htsmall]
    have hclose : (8 * diskConst q) * ‖s - 1‖ ≤ L₁ / 2 := by
      have hsum : ‖s - 1‖ ≤ 2 * δ := by linarith [hs1, hdδ, htsmall]
      have h2δ : (8 * diskConst q) * (2 * δ) = L₁ / 2 := by
        rw [hδdef]; field_simp; ring
      nlinarith [hsum, hDpos]
    have hlow : L₁ / 2 ≤ ‖LFunction χ s‖ := LFunction_lower_of_L1 χ hχ1 hL1 hs2 hclose
    have hlog : Real.log (L₁ / 2) ≤ Real.log ‖LFunction χ s‖ :=
      Real.log_le_log (by positivity) hlow
    have heq : Real.log (L₁ / 2) = Real.log L₁ - Real.log 2 :=
      Real.log_div (ne_of_gt hL1pos) (by norm_num)
    rw [heq] at hlog
    linarith [hlog, hFnn]
  · -- the pole-distance branch
    have ht0 : 0 < |t| := lt_of_lt_of_le hδpos (le_of_lt (not_le.mp htsmall))
    have hfar' := hfar q χ hsq X t hX ht ht0
    have hmono : Real.log ((q : ℝ) * Z / (2 * |t|))
        ≤ Real.log (16 * (q : ℝ) * Z * diskConst q / L₁) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_div_iff₀ (by positivity) hL1pos]
      have htδ : δ ≤ |t| := le_of_lt (not_le.mp htsmall)
      rw [hδdef, div_le_iff₀ (by positivity)] at htδ
      linarith [mul_le_mul_of_nonneg_left htδ hqZ]
    linarith [hfar', hmono, hNnn]

/-- **S-3 (uniform) — the real-χ floor with EXPLICIT `q`-dependence.**  For every real
nonprincipal `χ mod q`, every lower bound `0 < L₁ ≤ 1` for `(L(1,χ)).re`, every `X ≥ e` past
the gate `32·diskConst q/L₁ ≤ log X`, and EVERY real `t`, the bounded-band branch of the
ROUTE-A floor is

  `loglog X − (3/4)log(1+log X) − [log 2 − log L₁ + 2log4 + (1/4)log(16 q Z diskConst q/L₁)]`
  `  − CH2`,

i.e. `(1/4)loglog X − O(log q) − O(log(1/L₁))`, exactly the shape
`chi_floor_all_nonreal` has at `χ² ≠ 1`.  With Siegel's `L(1,χ) ≫_ε q^{−ε}` in the `L₁` slot
the debit is `O(ε log q)` and the floor is uniform over `q ≤ W` — this is the door's shape,
and the `L₁` slot is the ONLY thing between the campaign and it. -/
theorem chi_floor_real_of_L1 :
    ∃ CH1 CH2 Z : ℝ, 1 ≤ Z ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t L₁ : ℝ, Real.exp 1 ≤ X → 0 < L₁ → L₁ ≤ 1 →
        L₁ ≤ (DirichletCharacter.LFunction χ 1).re →
        32 * diskConst q / L₁ ≤ Real.log X →
          min (Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
                - (Real.log 2 - Real.log L₁ + 2 * Real.log 4
                  + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / L₁)) - CH2)
              ((Real.log (Real.log X)
                  - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                  - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                  - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
            ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_of_Llower
  obtain ⟨Z, hZ1, hL⟩ := chi_Llower_real_of_L1
  refine ⟨CH1, CH2, Z, hZ1, ?_⟩
  intro q _ χ hχ1 hsq X t L₁ hX hL1pos hL1le hL1 hgate
  have hB := hC q χ X t (Real.log 2 - Real.log L₁
      + (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / L₁))) hX (fun hkt => ?_)
  · have heq : Real.log (Real.log X)
        - (Real.log 2 - Real.log L₁
            + (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
              + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / L₁))) - CH2
        = Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
            - (Real.log 2 - Real.log L₁ + 2 * Real.log 4
              + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / L₁)) - CH2 := by ring
    rw [← heq]
    exact hB
  · have hord : 0 < orderOf χ := MulChar.orderOf_pos χ
    have hk2 : (2 : ℝ) ≤ ((2 * orderOf χ : ℕ) : ℝ) := by
      have h2 : 2 ≤ 2 * orderOf χ := by omega
      exact_mod_cast h2
    have ht1 : |t| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((2 * orderOf χ : ℕ) : ℝ))] at hkt
      nlinarith [abs_nonneg t]
    exact hL q χ hχ1 hsq X t L₁ hX ht1 hL1pos hL1le hL1 hgate

/-- **The `L₁` slot is inhabited at every real nonprincipal character.**  `L(1,χ)` is a
POSITIVE real for `χ ≠ 1`, `χ² = 1` (`Salt.SW.LFunction_apply_one_pos`), so
`L₁ = min 1 (L(1,χ)).re` satisfies every hypothesis of `chi_floor_real_of_L1`.  What this
does NOT give — and what Siegel's theorem is — is a `q`-uniform choice: `L₁` here is produced
character by character, exactly like the compact minimum of §2.  Composing this with
`chi_floor_real_of_L1` reproves §5's per-character growing floor through the explicit route;
composing an ineffective `L(1,χ) ≫_ε q^{−ε}` with it instead gives the door's uniform one. -/
theorem exists_L1_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hsq : χ ^ 2 = 1) :
    ∃ L₁ : ℝ, 0 < L₁ ∧ L₁ ≤ 1 ∧ L₁ ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hre : 0 < (LFunction χ 1).re :=
    (Complex.pos_iff.mp (Salt.SW.LFunction_apply_one_pos hχ1 hsq)).1
  exact ⟨min 1 ((LFunction χ 1).re), lt_min one_pos hre, min_le_left _ _, min_le_right _ _⟩

end Salt.MR
