/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.BilinearLS
import Salt.BV.DivisorSum
import Salt.LS.TypeSums

/-!
# V2b — the Type II bilinear estimate (fixed cutoff `y`)

Design: `docs/blueprints/bv.md`, node `V2b` (CORRECTED form; the `max_y` is STRUCK
per the "6th correction" — we work at a FIXED cutoff `y`, `∀ y ≤ x`; V3.1/V4 handle
scales).  This file lands the per-`(D,F)`-dyadic-block bound `typeII_block_le`
(the core: one clean `bilinear_LS_shell` application), together with the carrier
`typeII`, its dyadic-in-`d` decomposition into blocks (`typeII_le_sum_blocks`), and
the two mechanisms that feed the block bound.

## The carrier

`typeII U V y χ` is the Type II summand of `psiChi_sub_head_eq` at `x := y`
(`Salt/LS/TypeSums.lean`): `∑_{d ∈ Ioc U y} μ(d) ∑_{m : V < d·m ≤ y} b(V,m)·χ(d·m)`
with `b(V,m) = typeIIData V m = ∑_{c ∣ m, c > V} Λ(c)`.

## The reindex mechanism (the load-bearing insight)

The Vaughan LOWER guard `V < d·m` is **free**: `typeIIData V m = 0` whenever `m ≤ V`
(`typeIIData_eq_zero_of_le`), and a term with `d·m ≤ V` has `m ≤ d·m ≤ V`, so it
already vanishes.  Hence the inner `m`-range collapses from
`(Icc 1 y).filter (V < d·m ∧ d·m ≤ y)` to `(Icc 1 y).filter (d·m ≤ y)`
(`inner_dropguard`), which — for `d > D` — equals `(Icc 1 (y/D)).filter (d·m ≤ y)`
(the b-side range `H := y/D`).  This is exactly `bilinear_LS_shell`'s cutoff shape
`m·n ≤ Y` with `Y := y`.

## The per-block bound

For a dyadic `d`-block `Ioc D (2D)` and a conductor block `Icc F (2F)`, we apply
`bilinear_LS_shell` at `Q := 2F`, `M := 2D`, `H := y/D`, `Y := y`, with
`a d = μ(d)·1_{(D,2D]}` (`‖a‖₂² ≤ D`) and `b m = typeIIData V m`
(`‖b‖₂² ≤ (y/D)·(log x)²` via `sum_log_sq_le`).  The `(1/φf)` LHS weight is reached
by `(1/φf) ≤ (1/F)·(f/φf)` on `f ≥ F` (the BDH-assembly weight collapse), NOT the
naive `≤ f/φf` (which loses a factor `Q`).

The outer double-dyadic assembly (sum over `d`-blocks `D = U·2^j` and conductor
blocks `F = 2^i`, the four `√(a+b) ≤ √a + √b` regime totals, and the diagonal term
killed by the `f > (log x)^C` cutoff) is deferred to V3.1 — see
`docs/blueprints/flags.md` (node `V2b`).

Only `[propext, Classical.choice, Quot.sound]` are used (via `bilinear_LS_shell`).
-/

namespace Salt.BV

open Finset Salt.LS ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

/-! ## The carrier and its dyadic-in-`d` blocks -/

/-- The Type II piece (`Σ₃` of Vaughan), character-twisted, cut off at `y`.
Matches the `TypeII` summand of `psiChi_sub_head_eq` with `x := y`. -/
noncomputable def typeII (U V y : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ d ∈ Finset.Ioc U y, (μ d : ℂ) *
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y),
      (typeIIData V m : ℂ) * χ ((d * m : ℕ) : ZMod q)

/-- A single dyadic `d`-block of the Type II carrier: the `d`-sum restricted to
`Ioc D (2D)` (with the same inner `m`-sum as `typeII`). -/
noncomputable def typeIIBlock (V y D : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), (μ d : ℂ) *
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y),
      (typeIIData V m : ℂ) * χ ((d * m : ℕ) : ZMod q)

/-! ## The reindex mechanism: the lower Vaughan guard is free -/

/-- `typeIIData V m = 0` whenever `m ≤ V`: every divisor `c` of `m` has `c ≤ m ≤ V`,
so the `V < c` filter is empty. -/
theorem typeIIData_eq_zero_of_le {V m : ℕ} (h : m ≤ V) : typeIIData V m = 0 := by
  rw [typeIIData]
  apply Finset.sum_eq_zero
  intro c hc
  exfalso
  rw [Finset.mem_filter, Nat.mem_divisors] at hc
  obtain ⟨⟨hcdvd, hm0⟩, hVc⟩ := hc
  have hcm : c ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hcdvd
  omega

/-- **Guard drop.** For `d ≥ 1`, the inner `m`-sum with the coupled guard
`V < d·m ∧ d·m ≤ y` equals the one with only `d·m ≤ y`: the extra terms
(`d·m ≤ V`) have `m ≤ d·m ≤ V`, so `typeIIData V m = 0`. -/
theorem inner_dropguard (V y d : ℕ) (hd : 1 ≤ d) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y),
        (typeIIData V m : ℂ) * χ ((d * m : ℕ) : ZMod q)
      = ∑ m ∈ (Finset.Icc 1 y).filter (fun m => d * m ≤ y),
        (typeIIData V m : ℂ) * χ ((d * m : ℕ) : ZMod q) := by
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.2⟩
  · intro m hm hm'
    rw [Finset.mem_filter] at hm hm'
    -- `m ∈ filter (d*m ≤ y)` but `m ∉ filter (V < d*m ∧ d*m ≤ y)`; since `d*m ≤ y`,
    -- the failure is `¬ (V < d*m)`, i.e. `d*m ≤ V`, whence `m ≤ V`.
    have hdmy : d * m ≤ y := hm.2
    have hnV : ¬ (V < d * m) := by
      intro hV
      exact hm' ⟨hm.1, hV, hdmy⟩
    have hmV : m ≤ V := le_trans (Nat.le_mul_of_pos_left m hd) (by omega)
    rw [typeIIData_eq_zero_of_le hmV]
    simp

/-- For `D < d` (and `1 ≤ D`), the `b`-side range collapses: `{m ∈ Icc 1 y : d·m ≤ y}`
equals `{m ∈ Icc 1 (y/D) : d·m ≤ y}` (any `m` with `d·m ≤ y` and `d > D` has
`m ≤ y/d ≤ y/D`). -/
private lemma mset_eq (y D d : ℕ) (hDd : D < d) (hD : 1 ≤ D) :
    (Finset.Icc 1 y).filter (fun m => d * m ≤ y)
      = (Finset.Icc 1 (y / D)).filter (fun m => d * m ≤ y) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm1, _hmy⟩, hdmy⟩
    refine ⟨⟨hm1, ?_⟩, hdmy⟩
    have h1 : m ≤ y / d :=
      (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by rw [Nat.mul_comm]; exact hdmy)
    have h2 : y / d ≤ y / D := Nat.div_le_div_left (le_of_lt hDd) hD
    omega
  · rintro ⟨⟨hm1, hmyD⟩, hdmy⟩
    exact ⟨⟨hm1, le_trans hmyD (Nat.div_le_self y D)⟩, hdmy⟩

/-- **The bilinear identity.** The dyadic `d`-block `typeIIBlock V y D χ` is exactly the
`bilinear_LS_shell` inner sum with `M := 2D`, `H := y/D`, `Y := y`,
`a d = μ(d)·1_{(D,2D]}`, `b m = typeIIData V m`.  This is the reindex the shell consumes:
guard-drop (`inner_dropguard`), b-range collapse (`mset_eq`), and the `1_{(D,2D]}`
extension of the `d`-sum to `Icc 1 (2D)`. -/
private lemma typeIIBlock_eq (V y D : ℕ) (hD : 1 ≤ D) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    typeIIBlock V y D χ
      = ∑ d ∈ Finset.Icc 1 (2 * D),
          ∑ m ∈ (Finset.Icc 1 (y / D)).filter (fun m => d * m ≤ y),
            (if D < d then (μ d : ℂ) else 0) * (typeIIData V m : ℂ) * χ ((d * m : ℕ) : ZMod q) := by
  rw [typeIIBlock]
  symm
  have hsub : Finset.Ioc D (2 * D) ⊆ Finset.Icc 1 (2 * D) := by
    intro d hd; rw [Finset.mem_Ioc] at hd; rw [Finset.mem_Icc]; omega
  have hzero : ∀ d ∈ Finset.Icc 1 (2 * D), d ∉ Finset.Ioc D (2 * D) →
      ∑ m ∈ (Finset.Icc 1 (y / D)).filter (fun m => d * m ≤ y),
          (if D < d then (μ d : ℂ) else 0) * (typeIIData V m : ℂ) * χ ((d * m : ℕ) : ZMod q)
        = 0 := by
    intro d hdI hdO
    rw [Finset.mem_Icc] at hdI; rw [Finset.mem_Ioc] at hdO
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg (by omega : ¬ D < d)]; ring
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hDd : D < d := (Finset.mem_Ioc.mp hd).1
  have hd1 : 1 ≤ d := by omega
  rw [inner_dropguard V y d hd1 χ, mset_eq y D d hDd hD, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [if_pos hDd]; ring

/-! ## The coefficient masses -/

/-- **`a`-side mass.** `∑_{d ∈ Icc 1 (2D)} ‖μ(d)·1_{(D,2D]}‖² ≤ D` (`|μ| ≤ 1`, support
`Ioc D (2D)` of size `D`). -/
private lemma aMass_le (D : ℕ) :
    ∑ d ∈ Finset.Icc 1 (2 * D), ‖(if D < d then (μ d : ℂ) else 0)‖ ^ 2 ≤ (D : ℝ) := by
  calc ∑ d ∈ Finset.Icc 1 (2 * D), ‖(if D < d then (μ d : ℂ) else 0)‖ ^ 2
      ≤ ∑ d ∈ Finset.Icc 1 (2 * D), (if D < d then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro d _
        by_cases h : D < d
        · rw [if_pos h, if_pos h]
          have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
          exact pow_le_one₀ (norm_nonneg _) hμ
        · rw [if_neg h, if_neg h, norm_zero]; norm_num
    _ = (((Finset.Icc 1 (2 * D)).filter (fun d => D < d)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ = (D : ℝ) := by
        have hset : (Finset.Icc 1 (2 * D)).filter (fun d => D < d) = Finset.Ioc D (2 * D) := by
          ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
        rw [hset, Nat.card_Ioc]
        congr 1; omega

/-- **`b`-side mass.** `∑_{m ∈ Icc 1 k} ‖typeIIData V m‖² ≤ k·(1 + log x)²`
(`0 ≤ typeIIData ≤ log m`, then `sum_log_sq_le` and `log k ≤ log x`). -/
private lemma bMass_le (V k x : ℕ) (hk : 1 ≤ k) (hkx : k ≤ x) :
    ∑ m ∈ Finset.Icc 1 k, ‖(typeIIData V m : ℂ)‖ ^ 2 ≤ (k : ℝ) * (1 + Real.log x) ^ 2 := by
  have hstep : ∑ m ∈ Finset.Icc 1 k, ‖(typeIIData V m : ℂ)‖ ^ 2
      ≤ ∑ m ∈ Finset.Icc 1 k, (Real.log m) ^ 2 := by
    apply Finset.sum_le_sum
    intro m _
    have hnn : 0 ≤ typeIIData V m := typeIIData_nonneg V m
    have hle : typeIIData V m ≤ Real.log m := typeIIData_le_log V m
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact pow_le_pow_left₀ hnn hle 2
  refine le_trans hstep (le_trans (sum_log_sq_le k hk) ?_)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hkR
  have hlogkx : Real.log k ≤ Real.log x :=
    Real.log_le_log (by linarith) (by exact_mod_cast hkx)
  have hsq : (Real.log k) ^ 2 ≤ (1 + Real.log x) ^ 2 := pow_le_pow_left₀ hlogk (by linarith) 2
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-! ## The per-`(D,F)`-block bound -/

/-- `typeIIBlock` vanishes when `y < D`: every `d > D > y` forces the inner `m`-sum
(`d·m ≥ d > y`) to be empty. -/
private lemma typeIIBlock_eq_zero_of_lt {V y D : ℕ} (hyD : y < D) {q : ℕ}
    (χ : DirichletCharacter ℂ q) : typeIIBlock V y D χ = 0 := by
  rw [typeIIBlock]
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_Ioc] at hd
  have hempty : (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro m hm
    rw [Finset.mem_Icc] at hm
    rintro ⟨-, hdmy⟩
    have : y < d * m := lt_of_lt_of_le (by omega : y < d) (Nat.le_mul_of_pos_right d (by omega))
    omega
  rw [hempty, Finset.sum_empty, mul_zero]

/-- The per-`(D,F)`-block bound value: the `bilinear_LS_shell` output at `Q := 2F`,
`M := 2D`, `H := y/D`, with the coefficient masses substituted (it is `V`-free — the
`b`-mass `(y/D)(log x)²` does not see `V`).  The outer dyadic assembly (V3.1) sums
`blockBound x y (U·2^j) (2^i)` over `j`, `i`. -/
noncomputable def blockBound (x y D F : ℕ) : ℝ :=
  (1 / (F : ℝ)) * (2 * (1 + Real.log (x : ℝ))
      * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((2 * D : ℕ) : ℝ) + 1))
      * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((y / D : ℕ) : ℝ) + 1))
      * Real.sqrt ((D : ℝ))
      * (Real.sqrt (((y / D : ℕ) : ℝ)) * (1 + Real.log (x : ℝ))))

lemma blockBound_nonneg (x y D F : ℕ) : 0 ≤ blockBound x y D F := by
  rw [blockBound]; positivity

open Classical in
/-- **V2b — the per-`(D,F)` block bound.**  For a dyadic `d`-block `Ioc D (2D)` and a
conductor block `Icc F (2F)` (with `1 ≤ D`, `1 ≤ F`, `y ≤ x`),
```
∑_{f ∈ Icc F (2F)} (1/φf) ∑_{χ prim mod f} ‖typeIIBlock V y D χ‖ ≤ blockBound x y D F,
```
where `blockBound = (1/F)·2(1+log x)·√((2F)²+13(2D+1))·√((2F)²+13(y/D+1))·√D·(√(y/D)·(1+log x))`.
One `bilinear_LS_shell` application at `Q := 2F`, `M := 2D`, `H := y/D`, `Y := y`,
`a d = μ(d)·1_{(D,2D]}` (`‖a‖₂² ≤ D`), `b m = typeIIData V m` (`‖b‖₂² ≤ (y/D)(1+log x)²`);
the `(1/φf)` weight is reached by `(1/φf) ≤ (1/F)(f/φf)` on `f ≥ F`. -/
theorem typeII_block_le (V x y D F : ℕ) (hyx : y ≤ x) (hD : 1 ≤ D) (hF : 1 ≤ F) :
    ∑ f ∈ Finset.Icc F (2 * F), (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          ‖typeIIBlock V y D χ‖
      ≤ blockBound x y D F := by
  classical
  have hlogx0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hFR : (0 : ℝ) < (F : ℝ) := by exact_mod_cast (by omega : 0 < F)
  set RHS := blockBound x y D F with hRHSdef
  have hRHSnn : 0 ≤ RHS := by rw [hRHSdef]; exact blockBound_nonneg x y D F
  -- Degenerate case: `y < D` ⇒ every block sum vanishes.
  rcases lt_or_ge y D with hyD | hDy
  · have : ∑ f ∈ Finset.Icc F (2 * F), (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          ‖typeIIBlock V y D χ‖ = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      rw [mul_eq_zero]; right
      apply Finset.sum_eq_zero
      intro χ _
      rw [typeIIBlock_eq_zero_of_lt hyD χ, norm_zero]
    rw [this]; exact hRHSnn
  -- Main case: `D ≤ y`, so `H := y/D ≥ 1`.
  have hHpos : 0 < y / D := (Nat.one_le_div_iff (by omega : 0 < D)).mpr hDy
  -- The bilinear sieve at `Q := 2F`, `M := 2D`, `H := y/D`, `Y := y`.
  have hbil := bilinear_LS_shell (M := 2 * D) (H := y / D) (Q := 2 * F)
    (by omega : 2 ≤ 2 * F) hHpos
    (fun d => if D < d then (μ d : ℂ) else 0) (fun m => (typeIIData V m : ℂ)) y
  -- Rewrite the block norms into the bilinear inner shape.
  have hEqLHS : ∑ f ∈ Finset.Icc 1 (2 * F), ((f : ℝ) / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          ‖typeIIBlock V y D χ‖
      = ∑ f ∈ Finset.Icc 1 (2 * F), ((f : ℝ) / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 (2 * D),
              ∑ n ∈ (Finset.Icc 1 (y / D)).filter (fun n => m * n ≤ y),
                (if D < m then (μ m : ℂ) else 0) * (typeIIData V n : ℂ)
                  * χ ((m * n : ℕ) : ZMod f)‖ := by
    refine Finset.sum_congr rfl (fun f _ => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [typeIIBlock_eq V y D hD χ]
  -- The RHS of `bilinear_LS_shell`, bounded via the masses and `log (y/D) ≤ log x`.
  have hMassBound : 2 * (1 + Real.log ((y / D : ℕ) : ℝ))
        * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((2 * D : ℕ) : ℝ) + 1))
        * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((y / D : ℕ) : ℝ) + 1))
        * Real.sqrt (∑ m ∈ Finset.Icc 1 (2 * D), ‖(if D < m then (μ m : ℂ) else 0)‖ ^ 2)
        * Real.sqrt (∑ n ∈ Finset.Icc 1 (y / D), ‖(typeIIData V n : ℂ)‖ ^ 2)
      ≤ 2 * (1 + Real.log (x : ℝ))
        * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((2 * D : ℕ) : ℝ) + 1))
        * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((y / D : ℕ) : ℝ) + 1))
        * Real.sqrt ((D : ℝ))
        * (Real.sqrt (((y / D : ℕ) : ℝ)) * (1 + Real.log (x : ℝ))) := by
    have hlogyDx : Real.log ((y / D : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by exact_mod_cast hHpos)
        (by exact_mod_cast (le_trans (Nat.div_le_self y D) hyx))
    have hSaLe : Real.sqrt (∑ m ∈ Finset.Icc 1 (2 * D), ‖(if D < m then (μ m : ℂ) else 0)‖ ^ 2)
        ≤ Real.sqrt (D : ℝ) := Real.sqrt_le_sqrt (aMass_le D)
    have hSbLe : Real.sqrt (∑ n ∈ Finset.Icc 1 (y / D), ‖(typeIIData V n : ℂ)‖ ^ 2)
        ≤ Real.sqrt (((y / D : ℕ) : ℝ)) * (1 + Real.log (x : ℝ)) := by
      refine le_trans (Real.sqrt_le_sqrt
        (bMass_le V (y / D) x hHpos (le_trans (Nat.div_le_self y D) hyx))) ?_
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    gcongr
  -- Assemble.
  calc ∑ f ∈ Finset.Icc F (2 * F), (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeIIBlock V y D χ‖
      ≤ ∑ f ∈ Finset.Icc F (2 * F), (1 / (F : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeIIBlock V y D χ‖) := by
        refine Finset.sum_le_sum (fun f hf => ?_)
        rw [Finset.mem_Icc] at hf
        have hf1 : 1 ≤ f := by omega
        have hfF : F ≤ f := hf.1
        have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr hf1
        have hsumnn : 0 ≤ ∑ χ ∈ Finset.univ.filter
            (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive), ‖typeIIBlock V y D χ‖ :=
          Finset.sum_nonneg (fun χ _ => norm_nonneg _)
        have hweight : (1 / (f.totient : ℝ)) ≤ (1 / (F : ℝ)) * ((f : ℝ) / (f.totient : ℝ)) := by
          have hfFR : (F : ℝ) ≤ (f : ℝ) := by exact_mod_cast hfF
          have hge1 : (1 : ℝ) ≤ (f : ℝ) / (F : ℝ) := (one_le_div hFR).mpr hfFR
          calc (1 / (f.totient : ℝ)) = 1 * (1 / (f.totient : ℝ)) := by ring
            _ ≤ ((f : ℝ) / (F : ℝ)) * (1 / (f.totient : ℝ)) :=
                mul_le_mul_of_nonneg_right hge1 (by positivity)
            _ = (1 / (F : ℝ)) * ((f : ℝ) / (f.totient : ℝ)) := by ring
        calc (1 / (f.totient : ℝ)) * (∑ χ ∈ _, ‖typeIIBlock V y D χ‖)
            ≤ ((1 / (F : ℝ)) * ((f : ℝ) / (f.totient : ℝ))) * (∑ χ ∈ _, ‖typeIIBlock V y D χ‖) :=
              mul_le_mul_of_nonneg_right hweight hsumnn
          _ = (1 / (F : ℝ)) * (((f : ℝ) / (f.totient : ℝ)) * (∑ χ ∈ _, ‖typeIIBlock V y D χ‖)) := by
              ring
    _ = (1 / (F : ℝ)) * ∑ f ∈ Finset.Icc F (2 * F), (((f : ℝ) / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeIIBlock V y D χ‖) := by rw [Finset.mul_sum]
    _ ≤ (1 / (F : ℝ)) * ∑ f ∈ Finset.Icc 1 (2 * F), (((f : ℝ) / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeIIBlock V y D χ‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro f hf; rw [Finset.mem_Icc] at hf ⊢; omega
        · intro f _ _
          exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => norm_nonneg _))
    _ = (1 / (F : ℝ)) * ∑ f ∈ Finset.Icc 1 (2 * F), (((f : ℝ) / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖∑ m ∈ Finset.Icc 1 (2 * D),
              ∑ n ∈ (Finset.Icc 1 (y / D)).filter (fun n => m * n ≤ y),
                (if D < m then (μ m : ℂ) else 0) * (typeIIData V n : ℂ)
                  * χ ((m * n : ℕ) : ZMod f)‖) := by rw [hEqLHS]
    _ ≤ (1 / (F : ℝ)) * (2 * (1 + Real.log ((y / D : ℕ) : ℝ))
          * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((2 * D : ℕ) : ℝ) + 1))
          * Real.sqrt (((2 * F : ℕ) : ℝ) ^ 2 + 13 * (((y / D : ℕ) : ℝ) + 1))
          * Real.sqrt (∑ m ∈ Finset.Icc 1 (2 * D), ‖(if D < m then (μ m : ℂ) else 0)‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 (y / D), ‖(typeIIData V n : ℂ)‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hbil
    _ ≤ RHS := by
        rw [hRHSdef, blockBound]
        apply mul_le_mul_of_nonneg_left hMassBound (by positivity)

/-! ## The dyadic-in-`d` decomposition of the carrier -/

/-- Dyadic partition of a `d`-sum over `Ioc U (U·2^J)` into the `J` consecutive
blocks `Ioc (U·2^j) (U·2^{j+1})` (telescoping via `sum_Ioc_consecutive`). -/
private lemma dyadic_d_partition (U : ℕ) (g : ℕ → ℂ) (J : ℕ) :
    ∑ d ∈ Finset.Ioc U (U * 2 ^ J), g d
      = ∑ j ∈ Finset.range J, ∑ d ∈ Finset.Ioc (U * 2 ^ j) (U * 2 ^ (j + 1)), g d := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hab : U * 2 ^ J ≤ U * 2 ^ (J + 1) :=
        Nat.mul_le_mul_left U (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))
      have hUb : U ≤ U * 2 ^ J := Nat.le_mul_of_pos_right U (by positivity)
      exact (Finset.sum_Ioc_consecutive g hUb hab).symm

/-- **Dyadic-in-`d` decomposition.**  For `1 ≤ U` and `y ≤ U·2^J`, the Type II carrier
is the sum of its `J` dyadic `d`-blocks (the `d > y` tail is empty), so its norm is
`≤ ∑_{j<J} ‖typeIIBlock V y (U·2^j) χ‖`.  This feeds the outer dyadic assembly (V3.1). -/
theorem typeII_le_sum_blocks (U V y : ℕ) (J : ℕ) (hJ : y ≤ U * 2 ^ J)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖typeII U V y χ‖ ≤ ∑ j ∈ Finset.range J, ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
  have hExt : typeII U V y χ = ∑ j ∈ Finset.range J, typeIIBlock V y (U * 2 ^ j) χ := by
    rw [typeII]
    -- (1) extend `Ioc U y` to `Ioc U (U·2^J)` (the `d > y` tail is empty)
    rw [Finset.sum_subset (s₁ := Finset.Ioc U y) (s₂ := Finset.Ioc U (U * 2 ^ J))]
    · -- (2) dyadic partition, then (3) each block is `typeIIBlock`
      rw [dyadic_d_partition U _ J]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [typeIIBlock]
      have hpow : U * 2 ^ (j + 1) = 2 * (U * 2 ^ j) := by rw [pow_succ]; ring
      rw [hpow]
    · intro d hd; rw [Finset.mem_Ioc] at hd ⊢; exact ⟨hd.1, le_trans hd.2 hJ⟩
    · intro d hdBig hdSmall
      rw [Finset.mem_Ioc] at hdBig
      simp only [Finset.mem_Ioc, not_and, not_le] at hdSmall
      have hyd : y < d := hdSmall hdBig.1
      have hempty : (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m hm
        rw [Finset.mem_Icc] at hm
        rintro ⟨-, hdmy⟩
        have : y < d * m := lt_of_lt_of_le hyd (Nat.le_mul_of_pos_right d (by omega))
        omega
      rw [hempty, Finset.sum_empty, mul_zero]
  rw [hExt]
  exact norm_sum_le _ _

/-! ## The assembly reduction: LHS ≤ the double block-sum -/

open Classical in
/-- **V2b assembly reduction.**  The full `(1/φf)`-weighted, primitive-character `L¹`
Type II discrepancy over any conductor set `S ⊆ Icc 1 Q` (with `f ≥ 2`) is bounded by the
double dyadic block-sum: over `d`-blocks `D = U·2^j` (`j < J`, `y ≤ U·2^J`) and conductor
blocks `F = 2^i` (`i ≤ log₂(Q-1)`).  This performs all of the character-theoretic and
`Finset` work — the `d`-decomposition (`typeII_le_sum_blocks`), the sum swap, and the
BDH-style conductor fibering by `Nat.log 2 (f-1)` (each fibre `⊆ Icc (2^i) (2^{i+1})`,
closed by `typeII_block_le`).  What remains for `typeII_disc_le` is the PURELY REAL
geometric double sum of `blockBound` (the four `√(a+b) ≤ √a+√b` regimes + the diagonal
term killed by the `f > (log x)^C` cutoff) — see `docs/blueprints/flags.md` (node `V2b`). -/
theorem typeII_disc_reduce (U V x y Q : ℕ) (hU : 1 ≤ U) (hyx : y ≤ x)
    (J : ℕ) (hJ : y ≤ U * 2 ^ J) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q) (hS2 : ∀ f ∈ S, 2 ≤ f) :
    ∑ f ∈ S, (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          ‖typeII U V y χ‖
      ≤ ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (Nat.log 2 (Q - 1) + 1),
          blockBound x y (U * 2 ^ j) (2 ^ i) := by
  classical
  set I := Nat.log 2 (Q - 1) with hIdef
  calc ∑ f ∈ S, (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeII U V y χ‖
      ≤ ∑ f ∈ S, (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ∑ j ∈ Finset.range J, ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
        refine Finset.sum_le_sum (fun f _ => ?_)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => ?_)) (by positivity)
        exact typeII_le_sum_blocks U V y J hJ χ
    _ = ∑ j ∈ Finset.range J, ∑ f ∈ S, (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (I + 1),
          blockBound x y (U * 2 ^ j) (2 ^ i) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        -- Conductor fibering by `i = Nat.log 2 (f-1)`.
        have hmaps : ∀ f ∈ S, Nat.log 2 (f - 1) ∈ Finset.range (I + 1) := by
          intro f hf
          have hfIcc := hS hf; rw [Finset.mem_Icc] at hfIcc
          rw [Finset.mem_range]
          have hmono : Nat.log 2 (f - 1) ≤ Nat.log 2 (Q - 1) := Nat.log_mono_right (by omega)
          omega
        rw [← Finset.sum_fiberwise_of_maps_to hmaps
          (fun f => (1 / (f.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
              ‖typeIIBlock V y (U * 2 ^ j) χ‖)]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hUj : 1 ≤ U * 2 ^ j := by
          have h2j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
          calc 1 = 1 * 1 := by ring
            _ ≤ U * 2 ^ j := Nat.mul_le_mul hU h2j
        have hFi : 1 ≤ 2 ^ i := Nat.one_le_two_pow
        calc ∑ f ∈ S.filter (fun f => Nat.log 2 (f - 1) = i),
                (1 / (f.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
                    ‖typeIIBlock V y (U * 2 ^ j) χ‖
            ≤ ∑ f ∈ Finset.Icc (2 ^ i) (2 * 2 ^ i),
                (1 / (f.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
                    ‖typeIIBlock V y (U * 2 ^ j) χ‖ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro f hf
                rw [Finset.mem_filter] at hf
                obtain ⟨hfS, hflog⟩ := hf
                have hf2 := hS2 f hfS
                rw [Finset.mem_Icc]
                refine ⟨?_, ?_⟩
                · have hle := Nat.pow_log_le_self 2 (show f - 1 ≠ 0 by omega)
                  rw [hflog] at hle; omega
                · have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (f - 1)
                  rw [hflog, pow_succ] at hlt; omega
              · intro f _ _
                exact mul_nonneg (by positivity)
                  (Finset.sum_nonneg (fun χ _ => norm_nonneg _))
          _ ≤ blockBound x y (U * 2 ^ j) (2 ^ i) :=
              typeII_block_le V x y (U * 2 ^ j) (2 ^ i) hyx hUj hFi

end Salt.BV
