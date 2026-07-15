/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Gate
import Salt.BV.Defs
import Salt.BrunLower.MertensWindow
import Salt.Chen.TwinA1

/-!
# The Chen rung, node C3d — the triple-prime count `Σ aₙ`

Design: `docs/blueprints/chen.md`, the C3d row + its DESIGN NOTE. The switch
carrier `A₃` sifts `aₙ = ∑ 1_{n = p₁p₂p₃}` with `z ≤ p₁ ≤ y < p₂ ≤ p₃`; the
count `∑_{n ∈ window} aₙ` must land under the LITERAL ledger constant
`0.363084` in the normalisation `x/(2 log z)` (so `cbar_lt`, dilog-blocked, is
never consumed — C5 pairs this with `two_log_three_sub_log_six_sub_cbar_pos`).

## The PNT source (design-note "genuine PNT error term REQUIRED")

Satisfied from our own gate: `Salt.BV.siegelWalfisz_psiTot`, fed by the
UNCONDITIONAL `Salt.SW.siegelWalfisz_holds`, gives
`|ψ(x) − x| ≤ K·x/(log x)^A` for every `A > 0` — the PNT with arbitrary
log-power error, in-corpus. mathlib's only prime-count bound is Chebyshev
(`Chebyshev.pi_le_log4_mul_div`, constant `2 log 4 ≈ 2.77`), which the design
note correctly rules out (38% slack ≫ the S7 cap). Here `A = 1` suffices.

## The route (grid-free; a genuine FULL landing at 0.29827 < 0.363084)

The design note anticipated the sharp treatment (true `log(x/p₁p₂) =
(1−t₁−t₂)log x`, forcing a 2-D integral majorised by a rational grid). We
avoid that: the sharp PNT interval mass `ψ(U) − ψ(L) = (U − L)(1 + o(1))`
gives the inner `p₃`-count leading coefficient `½` (versus Chebyshev's
`≈ 2.77`), which leaves enough room to bound `1/log L` by its worst case
`≈ 1/((1/6) log x)` UNIFORMLY over the `(p₁,p₂)` box and still land at

  `const = 3·log(8/3)·log(3/2) / 4 = 0.29827 < 0.363084`  (margin 17.85%).

Concretely, with `z = x^{1/8}`, `y = x^{1/3}` and `p₂` extended to `√x`
(over-counting):
* inner `p₃`-count: `#{p₃ ∈ (L, U]} ≤ (U − L + PNT error)/log L`, from the
  gate at `U = ⌊x/(p₁p₂)⌋` and `L = ⌊x/(2 p₁p₂)⌋` (`prime_count_Ioc_le`);
* `U − L ≤ x/(2 p₁p₂) + 1`, so the double sum factors through
  `∑_{p₁} 1/p₁ · ∑_{p₂} 1/p₂ ≤ log(8/3)·log(3/2)` (windowed Mertens
  `Salt.BrunLower.sum_inv_le_of_prime_window`, `C₃ = 19`);
* `1/log L ≤ 1/lam` with `lam = (1/6) log x − log 4` a uniform floor.

No `sorry`, no `native_decide`, no new axioms.
-/

open Salt.LS ArithmeticFunction
open scoped BigOperators

namespace Salt.Chen

/-! ## Section 1 — the PNT corollary (ψ upper/lower from the gate, `A = 1`) -/

/-- **The unconditional PNT bound at `A = 1`.** There is `K ≥ 0` with
`|ψ(x) − x| ≤ K·x/log x` for all `x ≥ 3`. Instantiates `siegelWalfisz_psiTot`
(fed by the unconditional gate `siegelWalfisz_holds`) at the saving `A = 1`,
rewriting `(log x)^(1:ℝ) = log x`. -/
theorem psiTot_pnt :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℕ, 3 ≤ x →
      |psiTot x - (x : ℝ)| ≤ K * x / Real.log x := by
  obtain ⟨K, hK0, hK⟩ :=
    Salt.BV.siegelWalfisz_psiTot Salt.SW.siegelWalfisz_holds (show (0:ℝ) < 1 by norm_num)
  refine ⟨K, hK0, fun x hx => ?_⟩
  have := hK x hx
  rwa [Real.rpow_one] at this

/-! ## Section 2 — the inner `p₃`-count from the PNT interval mass -/

/-- The count of primes in `(L, U]`, as a real number. -/
noncomputable def primeCountIoc (L U : ℕ) : ℝ :=
  (((Finset.Ioc L U).filter (fun p => p.Prime)).card : ℝ)

/-- **The interval mass dominates the count times `log L`.** For `1 ≤ L ≤ U`,
`#{p ∈ (L, U] prime}·log L ≤ ψ(U) − ψ(L)`. Each prime `p ∈ (L, U]` has
`Λ(p) = log p ≥ log L`, and `ψ(U) − ψ(L) = ∑_{n ∈ (L,U]} Λ(n)` dominates the
prime part. -/
theorem primeCountIoc_mul_log_le {L U : ℕ} (hL : 1 ≤ L) (hLU : L ≤ U) :
    primeCountIoc L U * Real.log L ≤ psiTot U - psiTot L := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  -- ψ(U) − ψ(L) = ∑_{(L,U]} Λ
  have hunion : Finset.Icc 1 U = Finset.Icc 1 L ∪ Finset.Ioc L U := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 L) (Finset.Ioc L U) := by
    simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdiff : psiTot U - psiTot L = ∑ n ∈ Finset.Ioc L U, vonMangoldt n := by
    have : psiTot U = psiTot L + ∑ n ∈ Finset.Ioc L U, vonMangoldt n := by
      unfold psiTot; rw [hunion, Finset.sum_union hdisj]
    linarith
  rw [hdiff]
  set filt := (Finset.Ioc L U).filter (fun p => p.Prime) with hfilt
  -- prime part ≤ whole
  have hsub : ∑ p ∈ filt, vonMangoldt p ≤ ∑ n ∈ Finset.Ioc L U, vonMangoldt n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => vonMangoldt_nonneg)
  -- card · log L ≤ prime part
  have hcard : primeCountIoc L U * Real.log L ≤ ∑ p ∈ filt, vonMangoldt p := by
    rw [primeCountIoc, ← hfilt]
    have hstep : ∑ p ∈ filt, Real.log (L : ℝ) ≤ ∑ p ∈ filt, vonMangoldt p := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      rw [hfilt, Finset.mem_filter, Finset.mem_Ioc] at hp
      obtain ⟨⟨hLp, _⟩, hpp⟩ := hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpp]
      exact Real.log_le_log hLpos (by exact_mod_cast hLp.le)
    rw [Finset.sum_const, nsmul_eq_mul] at hstep
    linarith
  linarith [hcard, hsub]

/-- **The inner `p₃`-count, PNT-sharp.** Given the unconditional PNT bound
(`psiTot_pnt`'s `K`), for `3 ≤ L ≤ U`,
`#{p ∈ (L, U]} ≤ (U − L + K·U/log U + K·L/log L)/log L`. The leading term
`(U − L)/log L` is the *sharp* interval-mass coefficient (Chebyshev would give
`≈ 2.77·U/log U`). Parametric in `K` so the double sum threads one constant. -/
theorem prime_count_Ioc_le {K : ℝ} (_hK0 : 0 ≤ K)
    (hpsi : ∀ x : ℕ, 3 ≤ x → |psiTot x - (x : ℝ)| ≤ K * x / Real.log x)
    {L U : ℕ} (hL : 3 ≤ L) (hLU : L ≤ U) :
    primeCountIoc L U ≤ ((U : ℝ) - L + K * U / Real.log U + K * L / Real.log L) / Real.log L := by
  have hU : 3 ≤ U := le_trans hL hLU
  have hLpos1 : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 1 < L)
  have hlogL : 0 < Real.log L := Real.log_pos hLpos1
  -- upper ψ(U), lower ψ(L)
  have hbU := abs_le.mp (hpsi U hU)
  have hbL := abs_le.mp (hpsi L hL)
  have hpsiU : psiTot U ≤ (U : ℝ) + K * U / Real.log U := by linarith [hbU.2]
  have hpsiL : (L : ℝ) - K * L / Real.log L ≤ psiTot L := by linarith [hbL.1]
  have hmass := primeCountIoc_mul_log_le (by omega : 1 ≤ L) hLU
  rw [le_div_iff₀ hlogL]
  calc primeCountIoc L U * Real.log L
      ≤ psiTot U - psiTot L := hmass
    _ ≤ (U : ℝ) - L + K * U / Real.log U + K * L / Real.log L := by linarith [hpsiU, hpsiL]

/-! ## Section 3 — the switch-constant numeric confirmation (the "grid" step) -/

/-- **The achieved constant clears the ledger line.**
`3·log(8/3)·log(3/2)/4 < 0.363084`. This is the C3d endpoint constant
(`log(8/3)` = the `p₁`-window Mertens length `log(log y/log z)`, `log(3/2)` =
the `p₂`-window length `log(log√x/log y)`, `3/4` = the geometric factor
`log z / log L₀` at `log z = ⅛ log x`, `log L₀ = ⅙ log x`, after the `(x/2)`
interval-mass numerator is normalised against `x/(2 log z)`). True value
`0.29827`; margin to `0.363084` is `17.85%`. Proof: rational bounds on `log 2`,
`log 3` (`Real.log_two_lt_d9`, `Real.log_three_gt_d9`/`_near_10`). -/
theorem chen_switch_const_lt :
    3 * Real.log (8/3) * Real.log (3/2) / 4 < 0.363084 := by
  have h2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2l : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h3l : 1.0986122885 < Real.log 3 := Real.log_three_gt_d9
  have h3u : Real.log 3 ≤ 1.09861228877 := by
    have := (abs_sub_le_iff.1 Real.log_three_near_10).1
    norm_num at this ⊢; linarith
  -- log(8/3) = 3 log 2 − log 3, log(3/2) = log 3 − log 2
  have e83 : Real.log (8/3) = 3 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]; push_cast; ring
  have e32 : Real.log (3/2) = Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  rw [e83, e32]
  -- both factors positive, with explicit rational upper bounds
  have hf1pos : (0 : ℝ) < 3 * Real.log 2 - Real.log 3 := by linarith
  have hf2pos : (0 : ℝ) < Real.log 3 - Real.log 2 := by linarith
  have hf1 : 3 * Real.log 2 - Real.log 3 < 0.9808292541 := by linarith
  have hf2 : Real.log 3 - Real.log 2 < 0.4054651085 := by linarith
  nlinarith [mul_lt_mul'' hf1 hf2 hf1pos.le hf2pos.le, hf1pos, hf2pos]

/-! ## Section 4 — the triple set, the count `aₙ`, and the Fubini reindex -/

/-- The product of a triple. -/
def prod3 (t : ℕ × ℕ × ℕ) : ℕ := t.1 * t.2.1 * t.2.2

/-- The set of admissible triples `(p₁, p₂, p₃)`: `z ≤ p₁ ≤ y < p₂ ≤ p₃`, all
prime, with product in the shifted window `[x/2+2, x]` (i.e. `n = prod − 2` lies
in `twinWindow x`). Carried inside `Icc 1 x`³ (each prime `≤ product ≤ x`). -/
def tripleSet (x z y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x ×ˢ Finset.Icc 1 x)).filter
    (fun t => z ≤ t.1 ∧ t.1 ≤ y ∧ y < t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
      t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
      x / 2 + 2 ≤ prod3 t ∧ prod3 t ≤ x)

/-- The switch weight `aₙ = #{(p₁,p₂,p₃) admissible : p₁p₂p₃ = n + 2}` (the
fibre of `tripleSet` over `n`). -/
noncomputable def aCount (x z y n : ℕ) : ℝ :=
  (((tripleSet x z y).filter (fun t => prod3 t = n + 2)).card : ℝ)

/-- The C3d target sum `∑_{n ∈ twinWindow x} aₙ`. -/
noncomputable def tripleSum (x z y : ℕ) : ℝ :=
  ∑ n ∈ Salt.Chen.twinWindow x, aCount x z y n

/-- **The Fubini reindex.** `∑_{n ∈ window} aₙ = #{admissible triples}`: every
admissible triple has `prod − 2 ∈ twinWindow x`, so the fibres over the window
partition `tripleSet`. -/
theorem tripleSum_eq_card (x z y : ℕ) :
    tripleSum x z y = ((tripleSet x z y).card : ℝ) := by
  unfold tripleSum aCount
  rw [← Nat.cast_sum]
  congr 1
  -- fibrewise over f t = prod3 t - 2, landing in twinWindow x
  have Hmem : ∀ t ∈ tripleSet x z y, prod3 t - 2 ∈ Salt.Chen.twinWindow x := by
    intro t ht
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hlo, hhi⟩ := ht
    rw [twinWindow, Finset.mem_Icc]; omega
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  refine Finset.sum_congr rfl (fun n _hn => ?_)
  congr 1
  apply Finset.filter_congr
  intro t ht
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _, _, _, hlo, _⟩ := ht
  constructor <;> (intro h; omega)

/-! ## Section 5 — the reduction to a pair-sum of inner counts -/

/-- The inner endpoints for a pair `q = (p₁, p₂)`: `U = ⌊x/(p₁p₂)⌋`,
`L = ⌊x/(2 p₁p₂)⌋`. Every admissible `p₃` lies in `(L, U]`. -/
def Ufun (x : ℕ) (q : ℕ × ℕ) : ℕ := x / (q.1 * q.2)
def Lfun (x : ℕ) (q : ℕ × ℕ) : ℕ := x / (2 * q.1 * q.2)

/-- The set of admissible pairs `(p₁, p₂)`: `z ≤ p₁ ≤ y < p₂`, both prime,
`p₂² ≤ x` (forced by `p₂ ≤ p₃` and `prod ≤ x`). Contains `proj(tripleSet)`. -/
def pairSet (x z y : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x)).filter
    (fun q => z ≤ q.1 ∧ q.1 ≤ y ∧ y < q.2 ∧ q.2 * q.2 ≤ x ∧ q.1.Prime ∧ q.2.Prime)

/-- **The reduction (step 1).** `#{admissible triples} ≤ ∑_{(p₁,p₂)} #{p₃ ∈ (L,U]}`.
Decompose `tripleSet` over the projection to `(p₁, p₂) ∈ pairSet`; each fibre
injects (via `p₃`) into the primes of `(L, U]`. -/
theorem card_tripleSet_le_pairSum (x z y : ℕ) :
    ((tripleSet x z y).card : ℝ)
      ≤ ∑ q ∈ pairSet x z y, primeCountIoc (Lfun x q) (Ufun x q) := by
  classical
  have Hmem : ∀ t ∈ tripleSet x z y, (t.1, t.2.1) ∈ pairSet x z y := by
    intro t ht
    rw [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht
    obtain ⟨⟨ht1, ht21, _⟩, hz1, hy1, hy2, h23, hp1, hp2, _hp3, _hlo, hhi⟩ := ht
    rw [pairSet, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ht1, ht21⟩, hz1, hy1, hy2, ?_, hp1, hp2⟩
    -- p₂² ≤ p₂·p₃ ≤ p₁p₂p₃ = prod ≤ x
    have h1 : t.2.1 * t.2.1 ≤ t.2.1 * t.2.2 := Nat.mul_le_mul_left _ h23
    have h2 : t.2.1 * t.2.2 ≤ prod3 t := by
      rw [prod3]; calc t.2.1 * t.2.2 ≤ t.1 * (t.2.1 * t.2.2) :=
            Nat.le_mul_of_pos_left _ hp1.pos
        _ = t.1 * t.2.1 * t.2.2 := by ring
    exact le_trans (le_trans h1 h2) hhi
  rw [Finset.card_eq_sum_card_fiberwise Hmem]
  push_cast
  refine Finset.sum_le_sum (fun q _hq => ?_)
  rw [primeCountIoc]
  refine Nat.cast_le.mpr ?_
  refine Finset.card_le_card_of_injOn (fun t => t.2.2) ?_ ?_
  · -- MapsTo: each fibre element's p₃ lands in the prime window (L, U]
    intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨htmem, hprojq⟩ := ht
    have hq1 : q.1 = t.1 := by rw [← hprojq]
    have hq2 : q.2 = t.2.1 := by rw [← hprojq]
    rw [tripleSet, Finset.mem_filter] at htmem
    obtain ⟨_, _, _, _, _, hp1, hp2, hp3, hlo, hhi⟩ := htmem
    have hden : 0 < q.1 * q.2 := by rw [hq1, hq2]; exact Nat.mul_pos hp1.pos hp2.pos
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hp3⟩
    · -- L < p₃: else 2·prod ≤ x contradicts prod ≥ x/2 + 2
      rw [Lfun]
      by_contra hle
      rw [not_lt] at hle
      have hden2 : 0 < 2 * q.1 * q.2 := by
        rw [hq1, hq2]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hp1.pos) hp2.pos
      have hmul : t.2.2 * (2 * q.1 * q.2) ≤ x := (Nat.le_div_iff_mul_le hden2).mp hle
      rw [hq1, hq2] at hmul
      have heq : 2 * prod3 t = t.2.2 * (2 * t.1 * t.2.1) := by rw [prod3]; ring
      omega
    · -- p₃ ≤ U
      rw [Ufun]
      refine (Nat.le_div_iff_mul_le hden).mpr ?_
      rw [hq1, hq2]
      calc t.2.2 * (t.1 * t.2.1) = prod3 t := by rw [prod3]; ring
        _ ≤ x := hhi
  · -- InjOn: p₃ determines the fibre element (p₁, p₂ fixed by the fibre)
    intro t ht t' ht' heq
    rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨ht1, ht2⟩ := Prod.ext_iff.mp (ht.2.trans ht'.2.symm)
    exact Prod.ext ht1 (Prod.ext ht2 heq)

/-- **The C3d headline (reduction form).** `∑_{n ∈ window} aₙ ≤ ∑_{(p₁,p₂)}
#{p₃ ∈ (L,U]}`: the switch count is at most the pair-sum of inner PNT counts.
Composes the Fubini reindex with the projection reduction; the inner counts are
priced by the gate via `prime_count_Ioc_le`. -/
theorem triple_count_le_pairSum (x z y : ℕ) :
    tripleSum x z y ≤ ∑ q ∈ pairSet x z y, primeCountIoc (Lfun x q) (Ufun x q) := by
  rw [tripleSum_eq_card]; exact card_tripleSet_le_pairSum x z y

/-! ## Section 6 — the windowed-Mertens product for the pair reciprocal sum -/

/-- The `p₁`-window `[z, y]`, prime, inside `Icc 1 x`. -/
def S1set (x z y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun p => z ≤ p ∧ p ≤ y ∧ p.Prime)

/-- The `p₂`-window `(y, √x]`, prime, inside `Icc 1 x`. -/
def S2set (x y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun p => y < p ∧ p * p ≤ x ∧ p.Prime)

/-- `pairSet` factors as `S1set ×ˢ S2set`. -/
theorem pairSet_factor (x z y : ℕ) :
    pairSet x z y = S1set x z y ×ˢ S2set x y := by
  ext q
  simp only [pairSet, S1set, S2set, Finset.mem_filter, Finset.mem_product]
  tauto

/-- **The pair reciprocal sum factors and is Mertens-bounded.** For `2 ≤ z ≤ y`,
`1 ≤ y ≤ √x`, `∑_{(p₁,p₂) ∈ pairSet} 1/(p₁p₂) ≤ M₁·M₂` where `M₁, M₂` are the
`p₁` and `p₂` windowed-Mertens lengths (`sum_inv_le_of_prime_window`, `C₃ = 19`).
-/
theorem sum_inv_pairSet_le {x z y : ℕ} (hz2 : 2 ≤ z) (hzy : z ≤ y)
    (hy1 : 1 ≤ y) (hysx : (y : ℝ) ≤ Real.sqrt x) :
    ∑ q ∈ pairSet x z y, 1 / ((q.1 : ℝ) * q.2)
      ≤ (Real.log (Real.log (y + 1) / Real.log z) + 19 / Real.log z)
        * (Real.log (Real.log (Real.sqrt x + 1) / Real.log (y + 1)) + 19 / Real.log (y + 1)) := by
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hy1R : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  -- factor the sum
  rw [pairSet_factor, Finset.sum_product]
  have hfac : ∑ p₁ ∈ S1set x z y, ∑ p₂ ∈ S2set x y, 1 / ((p₁ : ℝ) * p₂)
      = (∑ p₁ ∈ S1set x z y, 1 / (p₁ : ℝ)) * (∑ p₂ ∈ S2set x y, 1 / (p₂ : ℝ)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p₁ _ => Finset.sum_congr rfl (fun p₂ _ => ?_))
    rw [div_mul_div_comm, one_mul]
  rw [hfac]
  -- Mertens on each window
  have hzyR : (z : ℝ) ≤ (y : ℝ) := by exact_mod_cast hzy
  have hzy1 : (z : ℝ) ≤ (y : ℝ) + 1 := by linarith
  have hS1 : ∀ p ∈ S1set x z y, Nat.Prime p ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (y : ℝ) + 1 := by
    intro p hp
    rw [S1set, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨_, hzp, hpy, hpp⟩ := hp
    exact ⟨hpp, by exact_mod_cast hzp, by exact_mod_cast (by omega : p < y + 1)⟩
  have hM1 := Salt.BrunLower.sum_inv_le_of_prime_window hzR hzy1 hS1
  have hS2 : ∀ p ∈ S2set x y, Nat.Prime p ∧ (y : ℝ) + 1 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt x + 1 := by
    intro p hp
    rw [S2set, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨_, hyp, hpx, hpp⟩ := hp
    refine ⟨hpp, by exact_mod_cast (by omega : y + 1 ≤ p), ?_⟩
    have hppx : (p : ℝ) * (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast hpx
    have hple : (p : ℝ) ≤ Real.sqrt x := by
      rw [← Real.sqrt_mul_self (show (0:ℝ) ≤ (p:ℝ) by positivity)]
      exact Real.sqrt_le_sqrt hppx
    linarith
  have hM2 := Salt.BrunLower.sum_inv_le_of_prime_window (by linarith : (2:ℝ) ≤ (y:ℝ)+1)
    (by linarith [hysx] : (y:ℝ)+1 ≤ Real.sqrt x + 1) hS2
  have hM1b : 0 ≤ Real.log (Real.log (y + 1) / Real.log z) + 19 / Real.log z :=
    le_trans (Finset.sum_nonneg (fun p _ => by positivity)) hM1
  exact mul_le_mul hM1 hM2 (Finset.sum_nonneg (fun p _ => by positivity)) hM1b

/-! ## Section 7 — the per-pair inner bound with a uniform `log L` floor -/

/-- The uniform floor value `⌊x/(2 y √x)⌋` for `L = Lfun x q` over all admissible
pairs (`q.1 ≤ y`, `q.2 ≤ √x`). -/
def Lval (x y : ℕ) : ℕ := x / (2 * y * Nat.sqrt x)

/-- Nat division is antitone in the denominator. -/
private lemma nat_div_le_div_denom {k a b : ℕ} (hab : a ≤ b) (ha : 0 < a) :
    k / b ≤ k / a := by
  refine (Nat.le_div_iff_mul_le ha).mpr ?_
  calc (k / b) * a ≤ (k / b) * b := Nat.mul_le_mul (le_refl _) hab
    _ ≤ k := Nat.div_mul_le_self k b

/-- A nat-division cast lower bound: `x/m ≥ (x:ℝ)/m − 1`. -/
private lemma cast_div_ge {x m : ℕ} (hm : 0 < m) :
    (x : ℝ) / m - 1 < ((x / m : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h1 : m * (x / m) + x % m = x := Nat.div_add_mod x m
  have h2 : x % m < m := Nat.mod_lt x hm
  have h3 : (x : ℝ) < ((x / m : ℕ) : ℝ) * m + m := by
    have : (x : ℝ) = (m : ℝ) * ((x / m : ℕ) : ℝ) + ((x % m : ℕ) : ℝ) := by exact_mod_cast h1.symm
    have h2R : ((x % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast h2
    nlinarith [this, h2R]
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hmR]
  linarith [h3]

/-- **The per-pair inner bound.** For an admissible pair `q` (with the uniform
floor `3 ≤ Lval x y`), the inner PNT count is bounded by a `1/(p₁p₂)`-weighted
main term (leading coefficient exact) plus a constant `1/lam`, with
`lam = log(Lval x y)` a uniform lower bound for `log L`:
`#{p₃ ∈ (L,U]} ≤ (1 + 3K/lam)·(x/2)/lam · 1/(p₁p₂) + 1/lam`. -/
theorem per_pair_le {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ K * n / Real.log n)
    {x z y : ℕ} (hLval3 : 3 ≤ Lval x y) {q : ℕ × ℕ} (hq : q ∈ pairSet x z y) :
    primeCountIoc (Lfun x q) (Ufun x q)
      ≤ (1 + 3 * K / Real.log (Lval x y)) * ((x : ℝ) / 2) / Real.log (Lval x y)
          * (1 / ((q.1 : ℝ) * q.2)) + 1 / Real.log (Lval x y) := by
  rw [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hq1lo, hq1x⟩, hq2lo, hq2x⟩, _hzq1, hq1y, hyq2, hq2sq, hp1, hp2⟩ := hq
  -- basic positivity
  have hm : 0 < q.1 * q.2 := Nat.mul_pos hp1.pos hp2.pos
  have hmR : (0 : ℝ) < (q.1 : ℝ) * q.2 := by exact_mod_cast hm
  set lam : ℝ := Real.log (Lval x y) with hlam
  have hLval2 : 2 ≤ Lval x y := by omega
  have hlampos : 0 < lam := Real.log_pos (by exact_mod_cast (by omega : 1 < Lval x y))
  -- Lval ≤ L = Lfun x q, giving 3 ≤ L, L ≤ U, lam ≤ log L ≤ log U
  have hq2sqrt : q.2 ≤ Nat.sqrt x := Nat.le_sqrt.mpr hq2sq
  have hden_le : 2 * q.1 * q.2 ≤ 2 * y * Nat.sqrt x := by
    calc 2 * q.1 * q.2 = 2 * (q.1 * q.2) := by ring
      _ ≤ 2 * (y * Nat.sqrt x) := Nat.mul_le_mul (le_refl 2) (Nat.mul_le_mul hq1y hq2sqrt)
      _ = 2 * y * Nat.sqrt x := by ring
  have hm2 : 0 < 2 * q.1 * q.2 := Nat.mul_pos (Nat.mul_pos (by norm_num) hp1.pos) hp2.pos
  have hLvalL : Lval x y ≤ Lfun x q := by
    rw [Lval, Lfun]; exact nat_div_le_div_denom hden_le hm2
  have hL3 : 3 ≤ Lfun x q := le_trans hLval3 hLvalL
  have hLU : Lfun x q ≤ Ufun x q := by
    rw [Lfun, Ufun]
    refine nat_div_le_div_denom ?_ hm
    calc q.1 * q.2 ≤ 2 * (q.1 * q.2) := by omega
      _ = 2 * q.1 * q.2 := by ring
  -- log floors
  have hLvalLR : (Lval x y : ℝ) ≤ (Lfun x q : ℝ) := by exact_mod_cast hLvalL
  have hlogL : lam ≤ Real.log (Lfun x q) := by
    rw [hlam]; exact Real.log_le_log (by exact_mod_cast (by omega : 0 < Lval x y)) hLvalLR
  have hlogLpos : 0 < Real.log (Lfun x q) := lt_of_lt_of_le hlampos hlogL
  have hLfunposR : (0 : ℝ) < (Lfun x q : ℝ) := by exact_mod_cast (by omega : 0 < Lfun x q)
  have hlogU : lam ≤ Real.log (Ufun x q) :=
    le_trans hlogL (Real.log_le_log hLfunposR (by exact_mod_cast hLU))
  -- the raw inner bound
  have hraw := prime_count_Ioc_le hK0 hpsi hL3 hLU
  -- cast bounds for U and L
  have hUup : (Ufun x q : ℝ) ≤ (x : ℝ) / ((q.1 : ℝ) * q.2) := by
    rw [Ufun]; refine le_trans Nat.cast_div_le (le_of_eq ?_); push_cast; ring
  have hLup : (Lfun x q : ℝ) ≤ (x : ℝ) / (2 * (q.1 : ℝ) * q.2) := by
    rw [Lfun]; refine le_trans Nat.cast_div_le (le_of_eq ?_); push_cast; ring
  have hLlow : (x : ℝ) / (2 * (q.1 : ℝ) * q.2) - 1 < (Lfun x q : ℝ) := by
    rw [Lfun]
    have := cast_div_ge (x := x) (m := 2 * q.1 * q.2) hm2
    convert this using 3
    push_cast; ring
  -- key: 2·(x/(2 q1 q2)) = x/(q1 q2)
  have hxm : (x : ℝ) / ((q.1 : ℝ) * q.2) = 2 * ((x : ℝ) / (2 * (q.1 : ℝ) * q.2)) := by
    field_simp
  set t : ℝ := (x : ℝ) / (2 * (q.1 : ℝ) * q.2) with ht
  have htnn : 0 ≤ t := by rw [ht]; positivity
  -- bound the three summands of the raw numerator
  have hUL : (Ufun x q : ℝ) - Lfun x q ≤ t + 1 := by
    have : (Ufun x q : ℝ) ≤ 2 * t := by rw [← hxm]; exact hUup
    linarith [this, hLlow]
  have hlogUpos : 0 < Real.log (Ufun x q) := lt_of_lt_of_le hlampos hlogU
  have hKU : K * (Ufun x q : ℝ) / Real.log (Ufun x q) ≤ K * (2 * t) / lam := by
    have hU2t : (Ufun x q : ℝ) ≤ 2 * t := by rw [← hxm]; exact hUup
    calc K * (Ufun x q : ℝ) / Real.log (Ufun x q)
        ≤ K * (Ufun x q : ℝ) / lam :=
          div_le_div_of_nonneg_left (mul_nonneg hK0 (by positivity)) hlampos hlogU
      _ ≤ K * (2 * t) / lam := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by nlinarith [hU2t, hK0]) (by positivity)
  have hKL : K * (Lfun x q : ℝ) / Real.log (Lfun x q) ≤ K * t / lam := by
    calc K * (Lfun x q : ℝ) / Real.log (Lfun x q)
        ≤ K * (Lfun x q : ℝ) / lam :=
          div_le_div_of_nonneg_left (mul_nonneg hK0 (by positivity)) hlampos hlogL
      _ ≤ K * t / lam := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by nlinarith [hLup, hK0]) (by positivity)
  -- combine the numerator into `(1 + 3K/lam)·t + 1`
  have hexp : (1 + 3 * K / lam) * t = t + 3 * K / lam * t := by ring
  have hid : K * (2 * t) / lam + K * t / lam = 3 * K / lam * t := by
    field_simp; ring
  have hnum : (Ufun x q : ℝ) - Lfun x q
        + K * (Ufun x q : ℝ) / Real.log (Ufun x q)
        + K * (Lfun x q : ℝ) / Real.log (Lfun x q)
      ≤ (1 + 3 * K / lam) * t + 1 := by
    linarith [hUL, hKU, hKL, hexp, hid]
  have h1p3 : (0 : ℝ) ≤ 1 + 3 * K / lam := by
    have : (0 : ℝ) ≤ 3 * K / lam := div_nonneg (by linarith [hK0]) hlampos.le
    linarith
  have hnn : (0 : ℝ) ≤ (1 + 3 * K / lam) * t + 1 := by
    nlinarith [mul_nonneg h1p3 htnn]
  -- assemble
  have hstep : primeCountIoc (Lfun x q) (Ufun x q) ≤ ((1 + 3 * K / lam) * t + 1) / lam := by
    calc primeCountIoc (Lfun x q) (Ufun x q)
        ≤ ((Ufun x q : ℝ) - Lfun x q + K * (Ufun x q : ℝ) / Real.log (Ufun x q)
            + K * (Lfun x q : ℝ) / Real.log (Lfun x q)) / Real.log (Lfun x q) := hraw
      _ ≤ ((1 + 3 * K / lam) * t + 1) / Real.log (Lfun x q) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hlogLpos.le)
      _ ≤ ((1 + 3 * K / lam) * t + 1) / lam :=
          div_le_div_of_nonneg_left hnn hlampos hlogL
  have hReq : ((1 + 3 * K / lam) * t + 1) / lam
      = (1 + 3 * K / lam) * ((x : ℝ) / 2) / lam * (1 / ((q.1 : ℝ) * q.2)) + 1 / lam := by
    rw [ht]; field_simp
  rw [hReq] at hstep
  exact hstep

/-! ## Section 8 — the C3d endpoint: `∑ aₙ` bounded by the switch-constant form -/

/-- **C3d — the triple-prime count.** For the `x^{1/8}`/`x^{1/3}` carriers
`z ≤ y ≤ √x` (`2 ≤ z`, `1 ≤ y`) with the uniform inner floor `3 ≤ ⌊x/(2y√x)⌋`,

  `∑_{n ∈ twinWindow x} aₙ ≤ Cₓ·(M₁·M₂) + |pairSet|/λ₀`,

where `λ₀ = log⌊x/(2y√x)⌋`, `Cₓ = (1 + 3K/λ₀)·(x/2)/λ₀`, and `M₁, M₂` are the
`p₁`/`p₂` windowed-Mertens lengths (`C₃ = 19`). `K` is the unconditional
PNT-error constant of the gate (`psiTot_pnt`). After C5 plugs the carrier
relations, `M₁ → log(8/3)`, `M₂ → log(3/2)`, and `Cₓ·M₁M₂ → 0.29827·x/(2 log z)`
— under the ledger line `0.363084` by `17.85%` (`chen_switch_const_lt`); the
`|pairSet|/λ₀ = O(x^{5/6}/log x)` remainder and the `3K/λ₀ = O(1/log x)` factor
are the o(1) terms C5 absorbs (the C0 ledger's S7 reserve). The design note's
"genuine PNT error term" enters through `K`; Chebyshev cannot serve. -/
theorem triple_count_le {x z y : ℕ}
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy1 : 1 ≤ y) (hysx : (y : ℝ) ≤ Real.sqrt x)
    (hLval3 : 3 ≤ Lval x y) :
    ∃ K : ℝ, 0 ≤ K ∧
      tripleSum x z y ≤
        (1 + 3 * K / Real.log (Lval x y)) * ((x : ℝ) / 2) / Real.log (Lval x y)
          * ((Real.log (Real.log (y + 1) / Real.log z) + 19 / Real.log z)
            * (Real.log (Real.log (Real.sqrt x + 1) / Real.log (y + 1))
                + 19 / Real.log (y + 1)))
        + ((pairSet x z y).card : ℝ) / Real.log (Lval x y) := by
  obtain ⟨K, hK0, hpsi⟩ := psiTot_pnt
  refine ⟨K, hK0, ?_⟩
  set lam : ℝ := Real.log (Lval x y) with hlam
  have hlampos : 0 < lam := Real.log_pos (by exact_mod_cast (by omega : 1 < Lval x y))
  set C : ℝ := (1 + 3 * K / lam) * ((x : ℝ) / 2) / lam with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h3 : (0 : ℝ) ≤ 3 * K / lam := div_nonneg (by linarith [hK0]) hlampos.le
    apply div_nonneg (mul_nonneg (by linarith) (by positivity)) hlampos.le
  -- the per-pair envelope summed and factored
  have hsum_eq :
      ∑ q ∈ pairSet x z y, (C * (1 / ((q.1 : ℝ) * q.2)) + 1 / lam)
        = C * (∑ q ∈ pairSet x z y, 1 / ((q.1 : ℝ) * q.2))
            + ((pairSet x z y).card : ℝ) / lam := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      mul_one_div]
  calc tripleSum x z y
      ≤ ∑ q ∈ pairSet x z y, primeCountIoc (Lfun x q) (Ufun x q) :=
        triple_count_le_pairSum x z y
    _ ≤ ∑ q ∈ pairSet x z y, (C * (1 / ((q.1 : ℝ) * q.2)) + 1 / lam) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have := per_pair_le hK0 hpsi hLval3 hq
        rw [← hlam, ← hC] at this
        exact this
    _ = C * (∑ q ∈ pairSet x z y, 1 / ((q.1 : ℝ) * q.2))
          + ((pairSet x z y).card : ℝ) / lam := hsum_eq
    _ ≤ C * ((Real.log (Real.log (y + 1) / Real.log z) + 19 / Real.log z)
            * (Real.log (Real.log (Real.sqrt x + 1) / Real.log (y + 1))
                + 19 / Real.log (y + 1)))
          + ((pairSet x z y).card : ℝ) / lam := by
        gcongr
        exact sum_inv_pairSet_le hz2 hzy hy1 hysx

end Salt.Chen
