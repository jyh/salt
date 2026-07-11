/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Vaughan
import Salt.LS.PsiDefs

/-!
# L9.2–L9.4 — the Type I / Type II reduction of Vaughan's identity

Design: `docs/blueprints/largesieve.md`, nodes `L9.2`, `L9.3`, `L9.4` and the
W6 section. Consumes `vaughan_sum` (`Salt/LS/Vaughan.lean`) and `psiChi`
(`Salt/LS/PsiDefs.lean`).

The three pieces of `vaughan_sum` (`Σ₁ − Σ₂ + Σ₃`, each a divisor sum over
`n ∈ Ioc V x` weighted by `f : ℕ → ℂ`) are rearranged into the two structured
shapes the future Bombieri–Vinogradov dispersion step consumes.  The common
engine is `reindex_core`: for a divisor predicate `P`,

  `∑_{n ∈ Ioc V x} ∑_{d ∣ n, P d} F n d
     = ∑_{d ∈ Icc 1 x, P d} ∑_{m : V < d·m ≤ x} F (d·m) d`,

a pure `Finset` double-counting reindex (`sum_comm'` to swap `n ↔ d`, then a
per-`d` bijection `n ↔ d·m` via `sum_nbij'`).  Every reindexed piece has FREE
ranges in the two variables — no more `n.divisors` — which is exactly the
form dispersion needs.

* **L9.2 (Type I).**
  - `typeI_one_eq` (`Σ₁`): `∑_{d ≤ U} μ(d) ∑_m (log m) f(dm)`.  Coefficient
    `μ(d)` bounded by `1` (mathlib `abs_moebius_le_one`).
  - `typeI_two_eq` (`Σ₂`): the `(d ≤ U, c ≤ V)` double sum collapses via
    `t := d·c` to `∑_{t} a(t) ∑_m f(tm)` with
    `a(t) = ∑_{d ∣ t, d ≤ U, t/d ≤ V} μ(d) Λ(t/d)` (`typeICoeff`).  The
    collapse is arithmetic-function associativity
    `μ_{≤U} * (Λ_{≤V} * ζ) = (μ_{≤U} * Λ_{≤V}) * ζ` (`sigma2_inner`).
    Coefficient bound `|a(t)| ≤ log t` (`abs_typeICoeff_le`) and support
    `t > U·V → a(t) = 0` (`typeICoeff_eq_zero`), so `|a(t)| ≤ log(U·V)`.

* **L9.3 (Type II bilinear).** `Σ₃` is genuinely bilinear.  Note the landed
  `vaughan`'s `Σ₃` is the `d·c ∣ n` form (a residual `e = n/(d·c)` is present,
  NOT `n = d·c`), so the faithful Type II packaging groups `μ(d)` against the
  full quotient `m = n/d`, with the `> V` von-Mangoldt data folded into the
  `m`-coefficient `b(m) = ∑_{c ∣ m, c > V} Λ(c)` (`typeIIData`):
  `Σ₃ = ∑_{d > U} μ(d) ∑_m b(m) f(dm)` (`typeII_eq`).  Both coefficients
  explicit: `|μ(d)| ≤ 1` and `0 ≤ b(m) ≤ log m` (`typeIIData_nonneg`,
  `typeIIData_le_log`).  DEVIATION from the node prose: that prose assumed
  `Σ₃ = ∑_{d,c} μ(d) Λ(c) f(dc)` (i.e. `n = d·c`), which does NOT hold for the
  landed `vaughan` — its `Σ₃` carries a residual `e = n/(d·c)` — so `Λ(c)` is
  replaced by the ℓ²-controllable `b(m)`; the bilinear structure and free
  ranges (the property dispersion needs) are fully preserved.

* **L9.4 (AP / character reduction).** `tail_decomp` is the general-`f`
  assembly `∑_{n ∈ Ioc V x} Λ(n) f(n) = TypeI₁ − TypeI₂ + TypeII`; specialising
  `f := χ(·)` and splitting `psiChi` at `V` gives `psiChi_sub_head_eq`, with
  the crude head bound `‖head‖ ≤ V·log V` (`norm_head_le`).  Multiplicativity
  `χ(dm) = χ(d)·χ(m)` is `chi_cast_mul`.

Integrability/measurability: none — everything is a finite `Finset` sum.
-/

namespace Salt.LS

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## The reindexing engine -/

/-- **Core reindex.** Swap `∑_{n ∈ Ioc V x} ∑_{d ∣ n, P d}` into
`∑_{d ∈ Icc 1 x, P d} ∑_{m : V < d·m ≤ x}`, substituting `n = d·m`.  Pure
`Finset` double counting: `sum_comm'` swaps the order of summation, then a
per-`d` bijection `n ↔ d·m` (`sum_nbij'`) frees the inner range. -/
private theorem reindex_core {V x : ℕ} (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc V x, ∑ d ∈ n.divisors.filter P, F n d)
      = ∑ d ∈ (Finset.Icc 1 x).filter P,
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x), F (d * m) d := by
  have hcomm : (∑ n ∈ Finset.Ioc V x, ∑ d ∈ n.divisors.filter P, F n d)
      = ∑ d ∈ (Finset.Icc 1 x).filter P,
          ∑ n ∈ (Finset.Ioc V x).filter (d ∣ ·), F n d := by
    apply Finset.sum_comm'
    intro n d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hVn, hnx⟩, ⟨hdvd, _hn0⟩, hP⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdx : d ≤ x := le_trans (Nat.le_of_dvd (by omega) hdvd) hnx
      exact ⟨⟨⟨hVn, hnx⟩, hdvd⟩, ⟨⟨hdpos, hdx⟩, hP⟩⟩
    · rintro ⟨⟨⟨hVn, hnx⟩, hdvd⟩, ⟨_hd, hP⟩⟩
      exact ⟨⟨hVn, hnx⟩, ⟨hdvd, by omega⟩, hP⟩
  rw [hcomm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd1 : 0 < d := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1; omega
  refine Finset.sum_nbij' (fun n => n / d) (fun m => d * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hVn, hnx⟩, hdvd⟩ := hn
    have hdn : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd1; omega
    · exact le_trans (Nat.div_le_self n d) hnx
    · rw [hdn]; exact hVn
    · rw [hdn]; exact hnx
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨_hm1, _hmx⟩, hV, hx⟩ := hm
    exact ⟨⟨hV, hx⟩, Dvd.intro m rfl⟩
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _hm
    exact Nat.mul_div_cancel_left m hd1
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- The `P = True` specialisation of `reindex_core`: reindex over all divisors. -/
private theorem reindex_core_all {V x : ℕ} (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc V x, ∑ d ∈ n.divisors, F n d)
      = ∑ d ∈ Finset.Icc 1 x,
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x), F (d * m) d := by
  simpa only [Finset.filter_true] using reindex_core (fun _ => True) F

/-! ## Coefficient data and bounds -/

/-- `|μ n|` as a real number is bounded by `1`. -/
private theorem abs_moebius_real_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast abs_moebius_le_one

/-- Type I outer coefficient (`Σ₂`, `t = d·c` collapse):
`a(t) = ∑_{d ∣ t, d ≤ U, t/d ≤ V} μ(d) Λ(t/d)`. -/
noncomputable def typeICoeff (U V t : ℕ) : ℝ :=
  ∑ d ∈ t.divisors.filter (fun d => d ≤ U ∧ t / d ≤ V), (μ d : ℝ) * Λ (t / d)

/-- Type II inner coefficient (`Σ₃`): `b(m) = ∑_{c ∣ m, c > V} Λ(c)`. -/
noncomputable def typeIIData (V m : ℕ) : ℝ :=
  ∑ c ∈ m.divisors.filter (V < ·), Λ c

/-- The `Σ₂` coefficient is bounded: `|a(t)| ≤ log t`.  (Via `|μ| ≤ 1`,
`Λ ≥ 0`, extend the filtered divisor sum to all divisors, then
`∑_{d ∣ t} Λ(t/d) = ∑_{c ∣ t} Λ(c) = log t`.) -/
theorem abs_typeICoeff_le (U V t : ℕ) : |typeICoeff U V t| ≤ Real.log t := by
  rw [typeICoeff]
  calc |∑ d ∈ t.divisors.filter (fun d => d ≤ U ∧ t / d ≤ V), (μ d : ℝ) * Λ (t / d)|
      ≤ ∑ d ∈ t.divisors.filter (fun d => d ≤ U ∧ t / d ≤ V), |(μ d : ℝ) * Λ (t / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ t.divisors.filter (fun d => d ≤ U ∧ t / d ≤ V), Λ (t / d) := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        calc |(μ d : ℝ)| * Λ (t / d) ≤ 1 * Λ (t / d) :=
              mul_le_mul_of_nonneg_right (abs_moebius_real_le_one d) vonMangoldt_nonneg
          _ = Λ (t / d) := one_mul _
    _ ≤ ∑ d ∈ t.divisors, Λ (t / d) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => vonMangoldt_nonneg)
    _ = ∑ c ∈ t.divisors, Λ c := Nat.sum_div_divisors t Λ
    _ = Real.log t := vonMangoldt_sum

/-- The `Σ₂` coefficient vanishes past `U·V`: if `U·V < t` then `a(t) = 0`.
Combined with `abs_typeICoeff_le` this gives `|a(t)| ≤ log(U·V)` on the support. -/
theorem typeICoeff_eq_zero {U V t : ℕ} (h : U * V < t) : typeICoeff U V t = 0 := by
  rw [typeICoeff]
  apply Finset.sum_eq_zero
  intro d hd
  exfalso
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdvd, _⟩, hdU, htV⟩ := hd
  have ht : d * (t / d) = t := Nat.mul_div_cancel' hdvd
  have : t ≤ U * V := by
    calc t = d * (t / d) := ht.symm
      _ ≤ U * V := Nat.mul_le_mul hdU htV
  omega

/-- The `Σ₃` coefficient is nonnegative. -/
theorem typeIIData_nonneg (V m : ℕ) : 0 ≤ typeIIData V m :=
  Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)

/-- The `Σ₃` coefficient is bounded: `b(m) ≤ log m`. -/
theorem typeIIData_le_log (V m : ℕ) : typeIIData V m ≤ Real.log m := by
  rw [typeIIData]
  calc ∑ c ∈ m.divisors.filter (V < ·), Λ c
      ≤ ∑ c ∈ m.divisors, Λ c :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => vonMangoldt_nonneg)
    _ = Real.log m := vonMangoldt_sum

/-! ## `Σ₂`: the `t = d·c` collapse via arithmetic-function associativity -/

/-- `μ` truncated to `≤ U`, as an `ArithmeticFunction ℝ`. -/
private noncomputable def muTr (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ≤ U then (μ d : ℝ) else 0, by simp⟩

@[simp] private theorem muTr_apply (U d : ℕ) : muTr U d = if d ≤ U then (μ d : ℝ) else 0 := rfl

/-- `Λ` truncated to `≤ V`, as an `ArithmeticFunction ℝ`. -/
private noncomputable def vmTr (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun c => if c ≤ V then Λ c else 0, by simp⟩

@[simp] private theorem vmTr_apply (V c : ℕ) : vmTr V c = if c ≤ V then Λ c else 0 := rfl

/-- `(Λ_{≤V} * ζ) m = ∑_{c ∣ m, c ≤ V} Λ(c)`. -/
private theorem vmTr_mul_zeta_apply (V m : ℕ) :
    (vmTr V * ζ) m = ∑ c ∈ m.divisors.filter (· ≤ V), Λ c := by
  rw [coe_mul_zeta_apply, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun c _ => rfl)

/-- `a(t) = (μ_{≤U} * Λ_{≤V}) t`: the explicit filtered coefficient equals the
convolution. -/
private theorem typeICoeff_eq (U V t : ℕ) : typeICoeff U V t = (muTr U * vmTr V) t := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => muTr U a * vmTr V b),
    typeICoeff, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [muTr_apply, vmTr_apply]
  split_ifs with h1 h2 h2 <;> simp_all

/-- `(μ_{≤U} * (Λ_{≤V} * ζ)) n` equals the raw `Σ₂` inner double sum. -/
private theorem muTr_vmTr_zeta_apply (U V n : ℕ) :
    (muTr U * (vmTr V * ζ)) n
      = ∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V),
          (μ d : ℝ) * Λ c := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => muTr U a * (vmTr V * ζ) b),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [muTr_apply, vmTr_mul_zeta_apply]
  split_ifs with h
  · rw [Finset.mul_sum]
  · rw [zero_mul]

/-- **Stage 1 of `Σ₂`.** The `(d ≤ U, c ≤ V)` double sum collapses (via
associativity `μ_{≤U} * (Λ_{≤V} * ζ) = (μ_{≤U} * Λ_{≤V}) * ζ`) to a single
divisor sum of the coefficient `a(t)`. -/
private theorem sigma2_inner (U V n : ℕ) :
    (∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V), (μ d : ℝ) * Λ c)
      = ∑ t ∈ n.divisors, typeICoeff U V t := by
  rw [← muTr_vmTr_zeta_apply, ← mul_assoc, coe_mul_zeta_apply]
  exact Finset.sum_congr rfl (fun t _ => (typeICoeff_eq U V t).symm)

/-! ## L9.2 / L9.3 — the identity theorems -/

/-- **L9.2 (Type I, `Σ₁`).**  The piece-1 sum of `vaughan_sum` rearranges to
`∑_{d ≤ U} μ(d) ∑_m (log m) f(dm)` with `n = d·m`, free ranges in `d` and `m`. -/
theorem typeI_one_eq {U V x : ℕ} (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc V x,
        ((∑ d ∈ n.divisors.filter (· ≤ U),
            (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) * f n)
      = ∑ d ∈ (Finset.Icc 1 x).filter (· ≤ U), (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (Real.log ((m : ℕ) : ℝ) : ℂ) * f (d * m) := by
  have step : (∑ n ∈ Finset.Ioc V x,
        ((∑ d ∈ n.divisors.filter (· ≤ U),
            (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) * f n)
      = ∑ n ∈ Finset.Ioc V x, ∑ d ∈ n.divisors.filter (· ≤ U),
          (((μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) * f n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [step, reindex_core (· ≤ U)
      (fun n d => (((μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) * f n)]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hd1 : 0 < d := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1; omega
  rw [Nat.mul_div_cancel_left m hd1]
  push_cast
  ring

/-- **L9.2 (Type I, `Σ₂`).**  The piece-2 double sum collapses via `t = d·c` to
`∑_t a(t) ∑_m f(tm)` with `a(t) = typeICoeff U V t`, `n = t·m`. -/
theorem typeI_two_eq {U V x : ℕ} (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc V x,
        ((∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V),
            (μ d : ℝ) * Λ c : ℝ) : ℂ) * f n)
      = ∑ t ∈ Finset.Icc 1 x, (typeICoeff U V t : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < t * m ∧ t * m ≤ x), f (t * m) := by
  have step : (∑ n ∈ Finset.Ioc V x,
        ((∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V),
            (μ d : ℝ) * Λ c : ℝ) : ℂ) * f n)
      = ∑ n ∈ Finset.Ioc V x, ∑ t ∈ n.divisors, (typeICoeff U V t : ℂ) * f n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [sigma2_inner, Complex.ofReal_sum, Finset.sum_mul]
  rw [step, reindex_core_all (fun n t => (typeICoeff U V t : ℂ) * f n)]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.mul_sum]

/-- **L9.3 (Type II bilinear).**  The piece-3 sum is bilinear: `μ(d)` against the
full quotient `m = n/d`, with the `> V` von-Mangoldt data folded into the
`m`-coefficient `b(m) = typeIIData V m`.  Free ranges in `d` (`> U`) and `m`. -/
theorem typeII_eq {U V x : ℕ} (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc V x,
        ((∑ d ∈ n.divisors.filter (U < ·), ∑ c ∈ (n / d).divisors.filter (V < ·),
            (μ d : ℝ) * Λ c : ℝ) : ℂ) * f n)
      = ∑ d ∈ Finset.Ioc U x, (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (typeIIData V m : ℂ) * f (d * m) := by
  have step : (∑ n ∈ Finset.Ioc V x,
        ((∑ d ∈ n.divisors.filter (U < ·), ∑ c ∈ (n / d).divisors.filter (V < ·),
            (μ d : ℝ) * Λ c : ℝ) : ℂ) * f n)
      = ∑ n ∈ Finset.Ioc V x, ∑ d ∈ n.divisors.filter (U < ·),
          (((μ d : ℝ) * typeIIData V (n / d) : ℝ) : ℂ) * f n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have hc : (∑ c ∈ (n / d).divisors.filter (V < ·), (μ d : ℝ) * Λ c)
        = (μ d : ℝ) * typeIIData V (n / d) := by
      rw [typeIIData, Finset.mul_sum]
    rw [hc]
  rw [step, reindex_core (U < ·) (fun n d => (((μ d : ℝ) * typeIIData V (n / d) : ℝ) : ℂ) * f n)]
  have hrange : (Finset.Icc 1 x).filter (U < ·) = Finset.Ioc U x := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hrange]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hd1 : 0 < d := by
    have := (Finset.mem_Ioc.mp hd).1; omega
  rw [Nat.mul_div_cancel_left m hd1]
  push_cast
  ring

/-! ## L9.4 — the AP / character reduction -/

/-- **L9.4 (general `f`).**  The tail sum `∑_{V < n ≤ x} Λ(n) f(n)` decomposes
into `TypeI₁ − TypeI₂ + TypeII`. -/
theorem tail_decomp {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc V x, (Λ n : ℂ) * f n)
      = (∑ d ∈ (Finset.Icc 1 x).filter (· ≤ U), (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (Real.log ((m : ℕ) : ℝ) : ℂ) * f (d * m))
      - (∑ t ∈ Finset.Icc 1 x, (typeICoeff U V t : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < t * m ∧ t * m ≤ x), f (t * m))
      + (∑ d ∈ Finset.Ioc U x, (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (typeIIData V m : ℂ) * f (d * m)) := by
  rw [vaughan_sum hU hV x f, typeI_one_eq, typeI_two_eq, typeII_eq]

/-- Multiplicativity of the character weight: `χ(d·m) = χ(d)·χ(m)`. -/
theorem chi_cast_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (d m : ℕ) :
    χ ((d * m : ℕ) : ZMod q) = χ (d : ZMod q) * χ (m : ZMod q) := by
  rw [Nat.cast_mul, map_mul]

/-- `psiChi x χ` splits at `V` into a head (`n ≤ V`) and tail (`V < n ≤ x`). -/
theorem psiChi_eq_head_add_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {V x : ℕ}
    (hVx : V ≤ x) :
    psiChi x χ = (∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod q))
      + (∑ n ∈ Finset.Ioc V x, (Λ n : ℂ) * χ (n : ZMod q)) := by
  rw [psiChi]
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hIccV : Finset.Icc 1 V = Finset.Ioc 0 V := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, hIccV, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le V) hVx]

/-- The head `∑_{n ≤ V} Λ(n) χ(n)` is crudely bounded by `V·log V`. -/
theorem norm_head_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {V : ℕ} :
    ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod q)‖ ≤ (V : ℝ) * Real.log V := by
  calc ‖∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Icc 1 V, ‖(Λ n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 V, Real.log V := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        simp only [Finset.mem_Icc] at hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        calc Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n * 1 :=
              mul_le_mul_of_nonneg_left (χ.norm_le_one _) vonMangoldt_nonneg
          _ = Λ n := mul_one _
          _ ≤ Real.log n := vonMangoldt_le_log
          _ ≤ Real.log V := Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    _ = (V : ℝ) * Real.log V := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast [Nat.add_sub_cancel]
        ring

/-- **L9.4 (character form).**  `psiChi x χ` minus the head equals the Type I / II
decomposition with weight `f := χ(·)`.  The character-sum interface the future
Bombieri–Vinogradov dispersion step consumes. -/
theorem psiChi_sub_head_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) {x : ℕ} (hVx : V ≤ x) :
    psiChi x χ - (∑ n ∈ Finset.Icc 1 V, (Λ n : ℂ) * χ (n : ZMod q))
      = (∑ d ∈ (Finset.Icc 1 x).filter (· ≤ U), (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (Real.log ((m : ℕ) : ℝ) : ℂ) * χ ((d * m : ℕ) : ZMod q))
      - (∑ t ∈ Finset.Icc 1 x, (typeICoeff U V t : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < t * m ∧ t * m ≤ x), χ ((t * m : ℕ) : ZMod q))
      + (∑ d ∈ Finset.Ioc U x, (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 x).filter (fun m => V < d * m ∧ d * m ≤ x),
            (typeIIData V m : ℂ) * χ ((d * m : ℕ) : ZMod q)) := by
  rw [psiChi_eq_head_add_tail χ hVx, add_sub_cancel_left,
    tail_decomp hU hV x (fun n => χ (n : ZMod q))]

end Salt.LS
