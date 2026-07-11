/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# L9.1 — Vaughan's identity

Design: `docs/blueprints/largesieve.md`, node `L9.1` and the W6 section.

Vaughan's identity, stated as an exact finite-sum identity for the von Mangoldt
function `Λ = ArithmeticFunction.vonMangoldt`, using the Möbius function
`μ = ArithmeticFunction.moebius` (ℤ-valued, cast to ℝ). For truncation
parameters `U, V ≥ 1` and `n > V`:

  `Λ n = (∑_{d ∣ n, d ≤ U} μ d · log(n/d))`
       `− (∑_{d ∣ n, d ≤ U} ∑_{c ∣ (n/d), c ≤ V} μ d · Λ c)`
       `+ (∑_{d ∣ n, d > U} ∑_{c ∣ (n/d), c > V} μ d · Λ c)`.

Representation choice: the middle and right "pairs `(d, c)` with `d·c ∣ n`" are
rendered as the nested divisor sums `∑_{d ∣ n} ∑_{c ∣ (n/d)}` (equivalent to
`d·c ∣ n`), which keeps every piece a plain `Finset.sum` over divisor sets and
matches the base identity `Λ = μ * log` and the log expansion
`log m = ∑_{c ∣ m} Λ c` on the nose.

Route: **direct double-counting**, not convolution algebra on truncated
arithmetic functions — with the sole exception of the "degenerate" sum
`T := ∑_{d ∣ n} μ d · ∑_{c ∣ (n/d), c ≤ V} Λ c`, whose vanishing (the `n > V`
guard doing its work) is cleanest as the single convolution identity
`μ * (Λ_{≤V} * ζ) = Λ_{≤V}` evaluated at `n`, where `Λ_{≤V}` is `Λ` truncated to
`≤ V` (`vmLE`). Everything else is `Finset` filter-splitting.

The proof needs only two mathlib inputs: `moebius_mul_log_eq_vonMangoldt`
(`↑μ * log = Λ`, Dirichlet convolution) and `vonMangoldt_sum`
(`∑_{c ∣ m} Λ c = log m`), plus `coe_moebius_mul_coe_zeta` (`↑μ * ζ = 1`) for the
guard term.

Also provides `vaughan_sum`, the linear-functional version: the identity summed
against an arbitrary weight `f : ℕ → ℂ` over `n ∈ Ioc V x`, which the Type I/II
reduction (L9.2–L9.4) consumes.
-/

namespace Salt.LS

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Split a real sum over a divisor-like set into its `≤ P` and `> P` parts. Used
both for the inner `c`-split (`P = V`) and the outer `d`-split (`P = U`). -/
private theorem sum_le_add_lt (P : ℕ) (s : Finset ℕ) (g : ℕ → ℝ) :
    (∑ c ∈ s.filter (· ≤ P), g c) + (∑ c ∈ s.filter (P < ·), g c) = ∑ c ∈ s, g c := by
  have h : s.filter (P < ·) = s.filter (fun c => ¬ c ≤ P) :=
    Finset.filter_congr (fun c _ => by rw [not_le])
  rw [h, Finset.sum_filter_add_sum_filter_not]

/-- The von Mangoldt function truncated to arguments `≤ V`, bundled as an
`ArithmeticFunction ℝ` so its convolution with `μ` and `ζ` is available. -/
private noncomputable def vmLE (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun c => if c ≤ V then Λ c else 0, by simp⟩

@[simp] private theorem vmLE_apply (V c : ℕ) : vmLE V c = if c ≤ V then Λ c else 0 := rfl

/-- Key convolution identity: `μ * (Λ_{≤V} * ζ) = Λ_{≤V}`, since `μ * ζ = 1`. -/
private theorem mu_mul_vmLE_mul_zeta (V : ℕ) :
    (μ : ArithmeticFunction ℝ) * (vmLE V * ζ) = vmLE V := by
  rw [← mul_assoc, mul_comm (μ : ArithmeticFunction ℝ) (vmLE V), mul_assoc,
      coe_moebius_mul_coe_zeta, mul_one]

/-- The guard term vanishes: for `n > V`,
`∑_{d ∣ n} μ d · ∑_{c ∣ (n/d), c ≤ V} Λ c = 0`. This is `(μ * (Λ_{≤V} * ζ)) n =
Λ_{≤V} n = 0`, the `n > V` guard killing the truncated `Λ`. -/
private theorem Tall_eq_zero {n : ℕ} (V : ℕ) (hn : V < n) :
    (∑ d ∈ n.divisors, (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (· ≤ V), Λ c) = 0 := by
  have hconv : (∑ d ∈ n.divisors, (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (· ≤ V), Λ c)
      = ((μ : ArithmeticFunction ℝ) * (vmLE V * ζ)) n := by
    rw [mul_apply,
        Nat.sum_divisorsAntidiagonal
          (fun a b => (μ : ArithmeticFunction ℝ) a * (vmLE V * ζ) b)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [coe_mul_zeta_apply, intCoe_apply, Finset.sum_filter]
    simp only [vmLE_apply]
  rw [hconv, mu_mul_vmLE_mul_zeta, vmLE_apply, if_neg (by omega)]

/-- **L9.1 — Vaughan's identity** (exact finite-sum form). For truncation
parameters `U, V ≥ 1` and `n > V`, the von Mangoldt function decomposes into the
piece-1 divisor sum (a "Type I" term), minus the `≤U × ≤V` piece, plus the
`>U × >V` piece (the "Type II" bilinear term). The pairs `(d, c)` with `d·c ∣ n`
are the nested divisor sums `∑_{d ∣ n} ∑_{c ∣ (n/d)}`. -/
theorem vaughan {U V : ℕ} (_hU : 1 ≤ U) (_hV : 1 ≤ V) {n : ℕ} (hn : V < n) :
    Λ n
      = (∑ d ∈ n.divisors.filter (· ≤ U), (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ))
      - (∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V),
            (μ d : ℝ) * Λ c)
      + (∑ d ∈ n.divisors.filter (U < ·), ∑ c ∈ (n / d).divisors.filter (V < ·),
            (μ d : ℝ) * Λ c) := by
  -- The full double sum `∑_{d ∣ n} μ d · ∑_{c ∣ (n/d)} Λ c` equals `Λ n`
  -- (base identity `Λ = μ * log`, then `log(n/d) = ∑_{c ∣ (n/d)} Λ c`).
  have hfull : Λ n = ∑ d ∈ n.divisors, (μ d : ℝ) * ∑ c ∈ (n / d).divisors, Λ c := by
    conv_lhs => rw [← moebius_mul_log_eq_vonMangoldt, mul_apply]
    rw [Nat.sum_divisorsAntidiagonal
          (fun a b => (μ : ArithmeticFunction ℝ) a * ArithmeticFunction.log b)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [intCoe_apply, ArithmeticFunction.log_apply, ← ArithmeticFunction.vonMangoldt_sum]
  -- The `c ≤ V` guard term vanishes.
  have hTall : (∑ d ∈ n.divisors, (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (· ≤ V), Λ c) = 0 :=
    Tall_eq_zero V hn
  -- Piece 1 with each `log(n/d)` expanded to `∑_{c ∣ (n/d)} Λ c`.
  have hP1 : (∑ d ∈ n.divisors.filter (· ≤ U), (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ))
      = ∑ d ∈ n.divisors.filter (· ≤ U), (μ d : ℝ) * ∑ c ∈ (n / d).divisors, Λ c := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← ArithmeticFunction.vonMangoldt_sum]
  -- Pieces 2 and 3: factor `μ d` out of the inner sum.
  have hP2 : (∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V),
              (μ d : ℝ) * Λ c)
      = ∑ d ∈ n.divisors.filter (· ≤ U),
          (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (· ≤ V), Λ c := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
  have hP3 : (∑ d ∈ n.divisors.filter (U < ·), ∑ c ∈ (n / d).divisors.filter (V < ·),
              (μ d : ℝ) * Λ c)
      = ∑ d ∈ n.divisors.filter (U < ·),
          (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (V < ·), Λ c := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
  rw [hP1, hP2, hP3]
  -- Combine `piece1 − piece2` into `∑_{d ∣ n, d ≤ U} μ d · ∑_{c ∣ (n/d), c > V} Λ c`.
  have hbody : ∀ d ∈ n.divisors.filter (· ≤ U),
      (μ d : ℝ) * (∑ c ∈ (n / d).divisors, Λ c)
        - (μ d : ℝ) * (∑ c ∈ (n / d).divisors.filter (· ≤ V), Λ c)
      = (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (V < ·), Λ c := by
    intro d _
    rw [← mul_sub]
    congr 1
    rw [← sum_le_add_lt V ((n / d).divisors) (fun c => Λ c)]
    ring
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hbody,
      sum_le_add_lt U n.divisors
        (fun d => (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (V < ·), Λ c)]
  -- Now the goal is `Λ n = ∑_{d ∣ n} μ d · ∑_{c ∣ (n/d), c > V} Λ c`; split the full
  -- sum into `≤ V` (which is `0` by `hTall`) plus `> V`.
  rw [hfull]
  have hsplit : ∀ d ∈ n.divisors,
      (μ d : ℝ) * ∑ c ∈ (n / d).divisors, Λ c
      = (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (· ≤ V), Λ c
        + (μ d : ℝ) * ∑ c ∈ (n / d).divisors.filter (V < ·), Λ c := by
    intro d _
    rw [← mul_add, sum_le_add_lt V ((n / d).divisors) (fun c => Λ c)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hTall, zero_add]

/-- **L9.1, summed form.** The linear-functional version: Vaughan's identity
weighted by an arbitrary `f : ℕ → ℂ` and summed over `n ∈ Ioc V x`. The three
pieces become three outer sums (Type I term, minus `≤U × ≤V`, plus `>U × >V`),
ready for the Type I/II reduction. -/
theorem vaughan_sum {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc V x, (Λ n : ℂ) * f n)
      = (∑ n ∈ Finset.Ioc V x,
          ((∑ d ∈ n.divisors.filter (· ≤ U),
              (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) * f n)
      - (∑ n ∈ Finset.Ioc V x,
          ((∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V),
              (μ d : ℝ) * Λ c : ℝ) : ℂ) * f n)
      + (∑ n ∈ Finset.Ioc V x,
          ((∑ d ∈ n.divisors.filter (U < ·), ∑ c ∈ (n / d).divisors.filter (V < ·),
              (μ d : ℝ) * Λ c : ℝ) : ℂ) * f n) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn' : V < n := (Finset.mem_Ioc.mp hn).1
  rw [vaughan hU hV hn']
  push_cast
  ring

end Salt.LS
