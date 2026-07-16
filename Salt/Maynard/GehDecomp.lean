/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehMulti

/-!
# The GEH door — the Type-II dyadic decomposition supplier (node S2-B3-DECOMP)

Design freeze: `docs/exploration/s2-b3-design.md`, RE-CUT block (2026-07-17); the
multiblock consumer is `Salt/Maynard/GehMulti.lean`
(`pieceObligationU_of_GEH_multiblock`).  This file supplies the *analytic content*
of the Type-II piece `vP3`: the pointwise **dyadic partition** of the bilinear
form into Dirichlet-convolution block pairs, the coefficient (`CoeffAt`) bounds,
the block count, and the `seqDiscrepancy` subadditivity engine (`hdecomp`).

## What is delivered (all sorry-free, honest)

* `seqDiscrepancy_sum_le` — the `Finset`-sum subadditivity of `seqDiscrepancy`
  (the `hdecomp` engine; `GehMulti` only had the two-term `seqDiscrepancy_add_le`).
* `dyadic_cover` — the disjoint dyadic interval cover `∑_a 1_{(2^a c, 2^{a+1} c]}
  = 1_{(c, 2^W c]}`.
* `vP3_eq_dyadicPartition` — **the pointwise partition identity**: for `n ≤ x`,
  `vP3 (cbrt x) (cbrt x) n = ∑_{a < dCount x} dconv (muBlock a x) (typeIIData (cbrt x)) n`.
  The `μ`-side is split dyadically (`d ∈ (2^a⌊x^{1/3}⌋, 2^{a+1}⌊x^{1/3}⌋]`); the
  `typeIIData` co-divisor side is the full complementary factor.
* `hdecomp_dyadic` — the block subadditivity (`vP3` ≤ block-sum discrepancy),
  from the identity + `seqDiscrepancy_sum_le` + `seqDiscrepancy_congr_Icc`.
* `coeffAt_muBlock` — the `μ`-side `CoeffAt` (exponent `k = 0`, unconditional).
* `tiiBlock` / `tiiBlock_support` / `abs_tiiBlock_le` — the dyadically-localised
  `typeIIData` block matching `GehSW`'s `SWAt` family, with its support and its
  `τ·log`-bound *under the operating scale* `2·N_b x ≤ x`.
* `blockCount_le` — `dCount x ≤ (2/log 2) · log x` (the `hcount` polylog input,
  `p = 1`).

## The seam blocking the final door assembly (FLAG — house re-plumb)

`pieceObligationU_of_GEH_multiblock` cannot be instantiated for `vP3` as its
interface stands, for a **structural** reason (not a mere spelling mismatch):

* `hwin` demands *every* block satisfy `N_i M_i ≤ x ≤ 4 N_i M_i`, i.e.
  `N_i M_i ∈ [x/4, x]`, so each block's convolution support `(N_i M_i, 4 N_i M_i]`
  lies in `(x/4, 4x]`.  But `vP3 (cbrt x) (cbrt x)` is supported on
  `n > (⌊x^{1/3}⌋)^2 ≈ x^{2/3}` (it needs `d, c > x^{1/3}` with `dc ∣ n`), and
  `x^{2/3} < x/4` for `x > 64`.  So the window-blocks **cannot cover** the range
  `n ∈ (x^{2/3}, x/4]` where `vP3` is genuinely nonzero: no single-scale dyadic
  family both (a) partitions `vP3` over `[1, x]` and (b) meets `hwin`.  The two
  hypotheses are jointly unsatisfiable for `vP3`.  The classical fix is an outer
  `O(log x)` dyadic split of the `n`-range with the window taken at the *local*
  scale — which the current combinator (single scale `x` in both the modulus
  range `x^θ/log^B` and the bound `C x/log^A`) does not expose.
* Secondary: the dyadic `typeIIData` block's `CoeffAt` (`abs_tiiBlock_le`) holds
  only under `2·N_b x ≤ x`, not unconditionally in `x` (at small `x` a fixed
  large-index block overruns `x` and `log x` under-covers `log m`); and the
  `μ`-side is `CoeffAt` at `k = 0` while the `typeIIData` side needs `k = 1`, so
  the combinator's shared-`k` `hα`/`hβ` also needs widening.  These are downstream
  of the fatal `hwin` issue.

The honest partition + coefficient package below is exactly what an `n`-dyadic
re-plumb of the combinator would consume.
-/

open Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

/-- Dyadic block count on the `μ`-side: `2^(dCount x) > x`, so the blocks
`(2^a⌊x^{1/3}⌋, 2^{a+1}⌊x^{1/3}⌋]`, `a < dCount x`, cover every divisor `d ≤ x`. -/
def dCount (x : ℕ) : ℕ := Nat.log 2 x + 1

/-- The `a`-th dyadic scale: `N_a x = 2^a · ⌊x^{1/3}⌋`. -/
noncomputable def nScale (a x : ℕ) : ℕ := 2 ^ a * cbrt x

/-- The `a`-th `μ`-side dyadic block coefficient: `μ(d)` restricted to the block
`d ∈ (N_a x, 2 N_a x]`.  `CoeffAt`-admissible at exponent `k = 0`. -/
noncomputable def muBlock (a x d : ℕ) : ℝ :=
  if d ∈ Finset.Ioc (nScale a x) (2 * nScale a x) then (μ d : ℝ) else 0

/-- **`seqDiscrepancy` is `Finset`-sum subadditive.**  The discrepancy of a finite
sum of weights is at most the sum of the discrepancies — the iterated
`seqDiscrepancy_add_le` the `hdecomp` slot needs. -/
theorem seqDiscrepancy_sum_le {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ) (x q : ℕ) :
    seqDiscrepancy (fun n => ∑ i ∈ s, g i n) x q ≤ ∑ i ∈ s, seqDiscrepancy (g i) x q := by
  induction s using Finset.cons_induction with
  | empty => simp [seqDiscrepancy_const_zero]
  | cons a s ha ih =>
    have hfun : (fun n => ∑ i ∈ Finset.cons a s ha, g i n)
        = (fun n => g a n + ∑ i ∈ s, g i n) := by funext n; rw [Finset.sum_cons]
    rw [hfun, Finset.sum_cons]
    exact (seqDiscrepancy_add_le (g a) (fun n => ∑ i ∈ s, g i n) x q).trans
      (add_le_add le_rfl ih)

/-- **`seqDiscrepancy` congruence on the cutoff window.**  The discrepancy at
cutoff `y` depends on the weight only through its values on `[1, y]`. -/
theorem seqDiscrepancy_congr_Icc {f g : ℕ → ℝ} {y : ℕ} (q : ℕ)
    (h : ∀ n ∈ Finset.Icc 1 y, f n = g n) :
    seqDiscrepancy f y q = seqDiscrepancy g y q := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; simp [seqDiscrepancy]
  rw [seqDiscrepancy_eq f y q hq, seqDiscrepancy_eq g y q hq]
  refine congrArg (Finset.sup' _ _) (funext fun a => ?_)
  have hA : (∑ n ∈ Finset.Icc 1 y, if n % q = a then f n else 0)
      = ∑ n ∈ Finset.Icc 1 y, if n % q = a then g n else 0 :=
    Finset.sum_congr rfl (fun n hn => by rw [h n hn])
  have hM : (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0)
      = ∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then g n else 0 :=
    Finset.sum_congr rfl (fun n hn => by rw [h n hn])
  rw [hA, hM]

/-- **Disjoint dyadic interval cover.**  The intervals `(2^a c, 2^{a+1} c]`,
`a < W`, partition `(c, 2^W c]`: summing their indicators gives `1_{(c, 2^W c]}`. -/
theorem dyadic_cover (c d W : ℕ) :
    ∑ a ∈ Finset.range W,
        (if d ∈ Finset.Ioc (2 ^ a * c) (2 * (2 ^ a * c)) then (1 : ℝ) else 0)
      = if (c < d ∧ d ≤ 2 ^ W * c) then (1 : ℝ) else 0 := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : (2 : ℕ) ^ (W + 1) * c = 2 * (2 ^ W * c) := by rw [pow_succ]; ring
    have ht : c ≤ 2 ^ W * c := Nat.le_mul_of_pos_left c (by positivity)
    rw [h2]
    simp only [Finset.mem_Ioc]
    clear h2 ih
    revert ht
    generalize 2 ^ W * c = t
    intro ht
    split_ifs with hA hB hC <;> first | (exfalso; omega) | norm_num

/-- **The dyadic blocks reconstruct the `μ`-restriction.**  For `d ≤ x`, summing
the `μ`-side dyadic blocks recovers `vaughanA₃ (cbrt x) d = μ(d)·1_{cbrt x < d}` —
the disjoint cover (`dyadic_cover`) with the top interval reaching past `x`. -/
theorem sum_muBlock_eq {x d : ℕ} (hx : 1 ≤ x) (hd : d ≤ x) :
    ∑ a ∈ Finset.range (dCount x), muBlock a x d = vaughanA₃ (cbrt x) d := by
  have hc1 : 1 ≤ cbrt x := by
    rw [cbrt]; apply Nat.le_floor; rw [Nat.cast_one]
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := by rw [Real.one_rpow]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)
  have hrw : ∀ a, muBlock a x d
      = (if d ∈ Finset.Ioc (2 ^ a * cbrt x) (2 * (2 ^ a * cbrt x)) then (1 : ℝ) else 0)
          * (μ d : ℝ) := by
    intro a; simp only [muBlock, nScale]; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun a _ => hrw a), ← Finset.sum_mul,
    dyadic_cover (cbrt x) d (dCount x)]
  have hupper : d ≤ 2 ^ (dCount x) * cbrt x := by
    have hlt : x < 2 ^ (dCount x) := by
      unfold dCount; exact Nat.lt_pow_succ_log_self (by norm_num) x
    calc d ≤ x := hd
      _ ≤ 2 ^ (dCount x) := le_of_lt hlt
      _ ≤ 2 ^ (dCount x) * cbrt x := Nat.le_mul_of_pos_right _ (by omega)
  unfold vaughanA₃
  by_cases hlt : cbrt x < d
  · rw [if_pos ⟨hlt, hupper⟩, if_pos hlt, one_mul]
  · rw [if_neg (fun hh => hlt hh.1), if_neg hlt, zero_mul]

/-- **The pointwise dyadic partition of the Type-II piece.**  For `n ≤ x`, the
bilinear form `vP3` factors as a sum of Dirichlet-convolution block pairs — the
`μ`-side split dyadically, the `typeIIData` co-divisor side full.  The top
dyadic interval reaches past `x ≥ n ≥ d`, so every divisor `d > cbrt x` is
captured exactly once. -/
theorem vP3_eq_dyadicPartition {x : ℕ} (hx : 1 ≤ x) {n : ℕ} (hn : n ≤ x) :
    vP3 (cbrt x) (cbrt x) n
      = ∑ a ∈ Finset.range (dCount x), dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n := by
  rw [vP3_eq_dconv]
  unfold dconv
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd' := Nat.mem_divisors.mp hd
  have hdx : d ≤ x := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hd'.2) hd'.1) hn
  rw [← Finset.sum_mul, sum_muBlock_eq hx hdx]

/-- **The Type-II block subadditivity (`hdecomp`).**  The `y`-cutoff discrepancy
of `vP3` is bounded by the sum of the dyadic blocks' discrepancies — from the
pointwise partition (valid on `[1, y] ⊆ [1, x]`) and `seqDiscrepancy_sum_le`. -/
theorem hdecomp_dyadic {x : ℕ} (hx : 1 ≤ x) (y q : ℕ) (hyx : y ≤ x) :
    seqDiscrepancy (fun n => vP3 (cbrt x) (cbrt x) n) y q
      ≤ ∑ a ∈ Finset.range (dCount x),
          seqDiscrepancy (fun n => dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n) y q := by
  have hcongr : ∀ n ∈ Finset.Icc 1 y,
      vP3 (cbrt x) (cbrt x) n
        = ∑ a ∈ Finset.range (dCount x),
            dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact vP3_eq_dyadicPartition hx (le_trans hn.2 hyx)
  calc seqDiscrepancy (fun n => vP3 (cbrt x) (cbrt x) n) y q
      = seqDiscrepancy (fun n => ∑ a ∈ Finset.range (dCount x),
          dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n) y q :=
        seqDiscrepancy_congr_Icc q hcongr
    _ ≤ _ := seqDiscrepancy_sum_le (Finset.range (dCount x))
        (fun a n => dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n) y q

/-- **The `μ`-side `CoeffAt`** (exponent `k = 0`, unconditional in `x`).  Support
in the dyadic block by construction; `|μ(d)| ≤ 1 = τ(d)^0 (log x)^0`. -/
theorem coeffAt_muBlock (a : ℕ) : CoeffAt (muBlock a) (nScale a) 0 := by
  intro x n
  refine ⟨fun h => ?_, ?_⟩
  · simp only [muBlock] at h
    by_contra hmem
    rw [if_neg hmem] at h
    exact h rfl
  · simp only [muBlock, pow_zero, one_mul]
    split_ifs with hmem
    · exact_mod_cast abs_moebius_le_one
    · rw [abs_zero]; exact zero_le_one

/-- The `b`-th Type-II dyadic block, matching `GehSW`'s `SWAt` family
`β x m = 1_{Ioc (M x) (2 M x)}(m) · typeIIData (V x) m` at `M = nScale b`,
`V = cbrt`. -/
noncomputable def tiiBlock (b x m : ℕ) : ℝ :=
  if m ∈ Finset.Ioc (nScale b x) (2 * nScale b x) then Salt.LS.typeIIData (cbrt x) m else 0

/-- The Type-II block is supported on its dyadic interval (`CoeffAt` support). -/
theorem tiiBlock_support (b x m : ℕ) (h : tiiBlock b x m ≠ 0) :
    m ∈ Finset.Ioc (nScale b x) (2 * nScale b x) := by
  simp only [tiiBlock] at h
  by_contra hmem
  rw [if_neg hmem] at h
  exact h rfl

/-- **The Type-II block coefficient bound** (`CoeffAt` bound at `k = 1`) *under
the operating scale* `2·N_b x ≤ x`: `|β_b x m| ≤ τ(m)·log x`.  On support
`m ≤ 2 N_b x ≤ x`, so `typeIIData ≤ log m ≤ log x ≤ τ(m)·log x`.  (Unconditional
`CoeffAt` at a fixed `b` fails at small `x`; see the module FLAG.) -/
theorem abs_tiiBlock_le {b x m : ℕ} (hscale : 2 * nScale b x ≤ x) (hx : 2 ≤ x) :
    |tiiBlock b x m| ≤ (m.divisors.card : ℝ) ^ 1 * Real.log x ^ 1 := by
  simp only [tiiBlock, pow_one]
  split_ifs with hmem
  · rw [abs_of_nonneg (Salt.LS.typeIIData_nonneg _ _)]
    have hmpos : 1 ≤ m := by have := (Finset.mem_Ioc.mp hmem).1; omega
    have hmx : m ≤ x := le_trans (Finset.mem_Ioc.mp hmem).2 hscale
    have hlogx0 : (0 : ℝ) ≤ Real.log x :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
    have hcard1 : (1 : ℝ) ≤ (m.divisors.card : ℝ) := by
      have : 0 < m.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      exact_mod_cast this
    calc Salt.LS.typeIIData (cbrt x) m ≤ Real.log m := Salt.LS.typeIIData_le_log _ _
      _ ≤ Real.log x := Real.log_le_log (by exact_mod_cast hmpos) (by exact_mod_cast hmx)
      _ ≤ (m.divisors.card : ℝ) * Real.log x := le_mul_of_one_le_left hlogx0 hcard1
  · rw [abs_zero]; positivity

/-- **The block count is polylog** (`hcount` with `p = 1`):
`dCount x ≤ (2/log 2)·log x` for `x ≥ 2`. -/
theorem blockCount_le {x : ℕ} (hx : 2 ≤ x) :
    (dCount x : ℝ) ≤ (2 / Real.log 2) * Real.log x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hkey : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
    have h1 : (2 : ℕ) ^ (Nat.log 2 x) ≤ x := Nat.pow_log_le_self 2 (by omega)
    have h2 : Real.log (((2 : ℕ) : ℝ) ^ (Nat.log 2 x)) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by exact_mod_cast h1)
    rwa [Real.log_pow, Nat.cast_ofNat] at h2
  have hL2 : (Nat.log 2 x : ℝ) ≤ Real.log x / Real.log 2 := (le_div_iff₀ hlog2).mpr hkey
  have h1 : (1 : ℝ) ≤ Real.log x / Real.log 2 := (le_div_iff₀ hlog2).mpr (by linarith)
  have hrhs : (2 / Real.log 2) * Real.log x
      = Real.log x / Real.log 2 + Real.log x / Real.log 2 := by field_simp; ring
  unfold dCount
  push_cast
  rw [hrhs]
  linarith
