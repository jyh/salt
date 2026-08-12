/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.LeastK

/-!
# COMPREHENSIBILITY CERTIFICATE — THE WALL (the twin bar, and the least `k`)

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable), row 11.
Landed theorems certified, all three in one file because they are one story:
* `Salt.TwinBar.twin_bar` (`Salt/TwinBar/Impossibility.lean:173`)
* `Salt.TwinBar.no_twin_weight` (`Salt/TwinBar/Impossibility.lean:276`)
* `Salt.TwinBar.least_k_theorem` (`Salt/TwinBar/LeastK.lean:127`)

## WHAT THEY SAY, in one sentence each
* **`twin_bar`** — for every continuous weight on the triangle, the two Selberg
  contractions sum to at most `2·log 2` times its `L²` mass.
* **`no_twin_weight`** — since `2·log 2 < 2`, **no** continuous weight of positive
  mass can make that sum exceed **twice** its mass. The twin gate is unreachable
  at `k = 2`.
* **`least_k_theorem`** — the gate stays unreachable at `k = 3` and `k = 4`, and at
  `k = 5` an explicit rational weight `F★` crosses it. So `5` is the least `k`.

## THE VOCABULARY, UNFOLDED (rule 1) — all from `Salt/TwinBar/Defs.lean`
Every name below is replaced by its definition in the `k = 2` certificates, so
`cert_twin_bar` and `cert_no_twin_weight` mention **no corpus-internal definition
at all** — only `∫`, `^`, `+`, `<`, `≤` and `Real.log`.

* `R₂` — the closed triangle `{(t₁,t₂) | 0 ≤ t₁, 0 ≤ t₂, t₁ + t₂ ≤ 1}` (`:52`).
* `I₂ F` — the **`L²` mass**, `∫₀¹ (∫₀^{1−t₂} (F t₁ t₂)² dt₁) dt₂` (`:39`).
* `J₁ F` — the **first contraction**: integrate `F` along `t₁`, square, integrate
  along `t₂` (`:43`). `J₂ F` is the same with the roles swapped (`:47`).
* `Function.uncurry F` is `fun p => F p.1 p.2`, so the continuity hypothesis is
  written here in that plain form.

## THE MECHANISM, in one line (why `twin_bar` is true)
Two per-slice Cauchy–Schwarz estimates against the weights `w₁ = 1 − t₂ + t₁` and
`w₂ = 1 − t₁ + t₂`, one Tonelli swap on the triangle, and the pointwise identity
`w₁ + w₂ ≡ 2`. The `log 2` is the slice integral `∫₀^{1−t₂} dt₁ / w₁`.

## DIRECTION (rule 3)
`cert_twin_bar` and `cert_no_twin_weight` are the **same propositions** as the
landed theorems with every definition unfolded, proved by `exact`. **No generality
is traded.** `cert_least_k` is likewise the same proposition, proved by `exact`.

## ⭐⭐ THE CARRIER ASYMMETRY — READ THIS BEFORE QUOTING `cert_least_k`
**This is rule 2's UPWARD direction, and it is the one a reader of this claim is
most likely to get wrong.** The plain-English sentence *"the least `k` with
`M_k > 2` is 5"* is **more than the theorem says**, because its two halves live in
**different carriers**:

* the three **no-go** conjuncts (`k = 2,3,4`) are about **continuous real weights**
  on the real simplices — a statement about an uncountable function class;
* the `k = 5` conjunct is an **exact rational certificate**: one explicit
  polynomial `F★`, evaluated in `ℚ` bilinear Dirichlet arithmetic, giving
  `M₅ = 191881/95820 ≈ 2.00251`.

**The single-object bracket that would unify them** — a Dirichlet real-integral
bridge, plus the `2 < M₅ ≤ (5/4)·log 5` upper bracket — **is REGISTERED DEBT and is
not part of this theorem.** What is certified is exactly the honest asymmetric
pair. This certificate states the asymmetry rather than smoothing it, because a
certificate that read as a single-object claim would be the readable form claiming
more than the formal one.

## RULE 1, WHERE IT IS APPLIED BY DOCSTRING RATHER THAN BY UNFOLDING
`cert_least_k`'s `k = 3` and `k = 4` conjuncts keep their names `I₃/J₁₃/J₂₃/J₃₃`,
`I₄/J₁₄/…`, `R₃`, `R₄`. **They are the identical construction at higher arity** —
`I_k` is the `L²` mass over the `k`-simplex, `J_mk` integrates `F` along the `m`-th
coordinate, squares, and integrates over the rest — and unfolding them produces
fifteen nested integrals with no gain in comprehensibility. *The `k = 2` case IS
unfolded, completely, in `cert_no_twin_weight` directly above; a reader who wants
the shape reads it there and transposes.* **This is a deliberate application of
rule 1's second clause ("or the cert explains it in its docstring header"), and it
is declared rather than silent.**

## RULE 6 WITNESSES
* `cert_twin_bar` carries hypotheses ⇒ **NON-DEGENERACY witness**, below.
  ⛔ The degenerate witness this rejects is `F ≡ 0`: continuous, satisfies the
  hypothesis, and makes the bound read `0 ≤ 0` — the 8/12 amendment's own case.
  The witness used is `F ≡ 1`, where `I₂ = 1/2 > 0` and the bound reads
  `2/3 ≤ log 2 ≈ 0.6931` — **non-vacuous AND near-sharp, a 3.9 % margin**, so the
  witness shows the theorem has real content at the point it is instantiated.
* `cert_no_twin_weight` and `cert_least_k` are **hypothesis-free** ⇒ **EXEMPT**
  (a closed false proposition cannot be proved at all).

## AXIOMS
`[propext, Classical.choice, Quot.sound]` — the standard three; verified at landing.
-/

namespace Salt.Certs

open Salt.TwinBar Salt.Twelve

/-- **THE `k = 2` BAR, in primitive vocabulary.** For every weight `F` continuous
on the triangle `{0 ≤ t₁, 0 ≤ t₂, t₁ + t₂ ≤ 1}`:

> the first contraction plus the second is at most `2·log 2` times the `L²` mass.

Every corpus definition is unfolded; nothing but `∫`, `^`, `+`, `≤` and `Real.log`
appears. Direction: **the same proposition** as `Salt.TwinBar.twin_bar`. -/
theorem cert_twin_bar (F : ℝ → ℝ → ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
            {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) :
    (∫ t₂ in (0:ℝ)..1, (∫ t₁ in (0:ℝ)..(1 - t₂), F t₁ t₂) ^ 2)
      + (∫ t₁ in (0:ℝ)..1, (∫ t₂ in (0:ℝ)..(1 - t₁), F t₁ t₂) ^ 2)
      ≤ 2 * Real.log 2 * (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (F t₁ t₂) ^ 2) :=
  twin_bar F hF

/-- **THE HEADLINE, in primitive vocabulary.** There is **no** weight `F`
continuous on the triangle with positive `L²` mass whose two contractions sum to
more than **twice** that mass.

*Why `2` and not `2·log 2`: `2·log 2 ≈ 1.386 < 2`, so the bar sits strictly below
the twin gate and the gap is what makes the impossibility strict.*

Direction: **the same proposition** as `Salt.TwinBar.no_twin_weight`.
Rule 6: **hypothesis-free ⇒ EXEMPT.** -/
theorem cert_no_twin_weight :
    ¬ ∃ F : ℝ → ℝ → ℝ,
        ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ∧
        0 < (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (F t₁ t₂) ^ 2) ∧
        2 * (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (F t₁ t₂) ^ 2)
          < (∫ t₂ in (0:ℝ)..1, (∫ t₁ in (0:ℝ)..(1 - t₂), F t₁ t₂) ^ 2)
            + (∫ t₁ in (0:ℝ)..1, (∫ t₂ in (0:ℝ)..(1 - t₁), F t₁ t₂) ^ 2) :=
  no_twin_weight

/-- **THE LEAST-`k` THEOREM.** The twin gate is uncrossable by continuous weights
at `k = 2, 3, 4`, and the explicit rational `F★` crosses it at `k = 5`.

⭐ **THE TWO HALVES LIVE IN DIFFERENT CARRIERS — see the module docstring.** The
no-gos are about continuous real weights; the `k = 5` conjunct is an exact `ℚ`
certificate at one explicit polynomial. The unifying single-object bracket is
registered debt, not part of this statement.

Direction: **the same proposition** as `Salt.TwinBar.least_k_theorem`.
Rule 6: **hypothesis-free ⇒ EXEMPT.** -/
theorem cert_least_k :
    (¬ ∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ ∧
        0 < I₂ F ∧ 2 * I₂ F < J₁ F + J₂ F)
    ∧ (¬ ∃ F : ℝ → ℝ → ℝ → ℝ, ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) R₃ ∧
        0 < I₃ F ∧ 2 * I₃ F < J₁₃ F + J₂₃ F + J₃₃ F)
    ∧ (¬ ∃ F : ℝ → ℝ → ℝ → ℝ → ℝ,
        ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2) R₄ ∧
        0 < I₄ F ∧ 2 * I₄ F < J₁₄ F + J₂₄ F + J₃₄ F + J₄₄ F)
    ∧ 2 < (∑ m : Fin 5, Jcal m Fstar) / Ical Fstar :=
  least_k_theorem

/-! ### The rule-6 witness for `cert_twin_bar` — the three carriers at `F ≡ 1` -/

/-- `I₂ 1 = 1/2` — the area of the triangle. -/
theorem cert_twin_bar_mass_at_one :
    (∫ t₂ in (0:ℝ)..1, ∫ _t₁ in (0:ℝ)..(1 - t₂), ((1:ℝ)) ^ 2) = 1 / 2 := by
  simp only [one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id)]
  simp [integral_id]
  norm_num

/-- `∫₀¹ (1 − t)² dt = 1/3`, by the reflection `t ↦ 1 − t`. Both contractions of
the constant weight reduce to this integral. -/
theorem cert_twin_bar_contraction_integral :
    (∫ t in (0:ℝ)..1, (1 - t) ^ 2) = 1 / 3 := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
    (fun u : ℝ => u ^ 2) 1
  simp only [sub_zero, sub_self] at h
  rw [h, integral_pow]
  norm_num

/-- ⭐ **THE RULE-6 WITNESS, KIND: NON-DEGENERACY.** At the constant weight
`F ≡ 1` the hypotheses of `cert_twin_bar` hold (a constant is continuous), the
mass is **positive** — `1/2`, not `0` — and the bar reads

> `1/3 + 1/3 = 2/3  ≤  2·log 2·(1/2) = log 2 ≈ 0.6931`

⛔ **The degenerate witness this exists to reject is `F ≡ 0`**: also continuous,
also satisfies every hypothesis, and makes the bound read `0 ≤ 0` — true, and
saying nothing about the theorem. *This witness instead pins the bar within
**3.9 %** of equality, so it certifies that the inequality is doing work exactly
where it is instantiated.* -/
theorem cert_twin_bar_witness :
    ContinuousOn (fun _p : ℝ × ℝ => ((1:ℝ))) {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ∧
      0 < (∫ t₂ in (0:ℝ)..1, ∫ _t₁ in (0:ℝ)..(1 - t₂), ((1:ℝ)) ^ 2) ∧
      (∫ t₂ in (0:ℝ)..1, (∫ _t₁ in (0:ℝ)..(1 - t₂), (1:ℝ)) ^ 2)
        + (∫ t₁ in (0:ℝ)..1, (∫ _t₂ in (0:ℝ)..(1 - t₁), (1:ℝ)) ^ 2) = 2 / 3 ∧
      2 * Real.log 2 * (∫ t₂ in (0:ℝ)..1, ∫ _t₁ in (0:ℝ)..(1 - t₂), ((1:ℝ)) ^ 2)
        = Real.log 2 := by
  refine ⟨continuousOn_const, ?_, ?_, ?_⟩
  · rw [cert_twin_bar_mass_at_one]; norm_num
  · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    rw [cert_twin_bar_contraction_integral]; norm_num
  · rw [cert_twin_bar_mass_at_one]; ring

#print axioms cert_twin_bar
#print axioms cert_no_twin_weight
#print axioms cert_least_k
#print axioms cert_twin_bar_witness

end Salt.Certs
